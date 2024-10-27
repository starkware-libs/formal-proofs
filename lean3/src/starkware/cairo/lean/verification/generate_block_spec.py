import dataclasses
from typing import Dict, List, Optional, Union

from starkware.cairo.lang.compiler.ast.cairo_types import TypeFelt
from starkware.cairo.lang.compiler.ast.expr import Expression
from starkware.cairo.lean.verification.expr_to_lean import (
    LEAN_HINT_VAR_PREFIX,
    LeanDescContext,
    LeanExprSimplifier,
    count_div_ops,
    is_ap_ref,
    is_fp_ref,
    to_lean_description,
    to_lean_description_aux,
    to_lean_paren_description_aux,
)
from starkware.cairo.lean.verification.generate_rc import SpecRCSteps
from starkware.cairo.lean.verification.generate_soundness import (
    LEAN_CODE_INDENT,
    gen_implicit_args,
    mk_lean_auto_spec_name,
    mk_lean_user_spec_name,
)
from starkware.cairo.lean.verification.lean_processed_info import (
    LEAN_IGNORE_CONSTS,
    LEAN_RETURN_VAR_PREFIX,
    LeanFunctionInfo,
    LeanProgramInfo,
    get_instr_trace_count,
)
from starkware.cairo.lean.verification.lean_raw_info import (
    LeanPreprocessedAssertEq,
    LeanPreprocessedCodeElement,
    LeanPreprocessedCompoundAssertEq,
    LeanPreprocessedConst,
    LeanPreprocessedFuncCall,
    LeanPreprocessedIf,
    LeanPreprocessedJumpToLabelInstruction,
    LeanPreprocessedReference,
    LeanPreprocessedReturn,
    LeanPreprocessedTailCall,
    LeanPreprocessedTempVar,
    LeanPreprocessedWithAsserts,
)
from starkware.cairo.lean.verification.rebinding import (
    add_name_sub,
    inc_name_sub,
    name_with_sub,
    next_name_with_sub,
)
from starkware.cairo.lean.verification.type_to_lean import create_arg_defs, get_lean_type


@dataclasses.dataclass
class LeanTraceCount:
    """
    Collects information about the trace count along an execution path.
    """

    # Length of trace required to execute the instructions.
    count: int = 0
    # Number of function/block calls in the execution.
    calls: int = 0


@dataclasses.dataclass
class LeanSpecBlockGenerator:
    """
    This class generates the list of specifications for a single (sub-)block of code
    in a Cairo function. A block is a section of the code for which a separate
    auto-specification definition is generated. A sub-block is part of such a block,
    which is handled similarly to a block except that that its generated specifications
    are included as part of the specifications of a larger block. For example,
    the two branches of a if-then-else are separate sub-blocks, but will be included
    in the same specification definition.
    """

    func: LeanFunctionInfo
    lean_info: LeanProgramInfo
    simplifier: LeanExprSimplifier
    # The start of the block processed here.
    spec_start_lean_desc: int
    # Current position in the spec generation.
    lean_desc_num: int

    # Tracking objects inherited from a parent block.

    name_sub: Dict[str, int]
    trace_count: LeanTraceCount
    rc_steps: Optional[SpecRCSteps]
    # Number of function calls in the function up to this point.
    num_func_calls: int
    # Local Cairo variables indexed by their offset from fp.
    lvars: Dict[int, str] = dataclasses.field(default_factory=lambda: {})

    # Context information updated per instruction processed.

    # Context information needed when generating Lean expression from Cairo expressions.
    desc_ctx: LeanDescContext = dataclasses.field(init=False)
    # Prefix for extra variables created for division.
    div_var_basename: str = "δ0_"

    # Indentation prefix.
    prefix: str = ""
    # The claims asserted by the spec.
    asserts: List[str] = dataclasses.field(default_factory=lambda: [])

    def __post_init__(self):
        # When this block is called recursively as a sub-block of a larger block,
        # it inherits the following tracking objects from the parent block. However,
        # changes it applies to these objects should not affect the parent block
        # (for example, if this is just one branch of two taken by the main block).
        # Therefore, the inherited objects are duplicated here.
        self.rc_steps = self.rc_steps.branch() if self.rc_steps is not None else None
        self.name_sub = self.name_sub.copy()
        self.trace_count = dataclasses.replace(self.trace_count)

        # Initialize cached values.
        self.lvars = self.func.local_var_names()

        self.desc_ctx = LeanDescContext(
            simplifier=self.simplifier,
            cairo_type=TypeFelt(),  # Placeholder, may be replaced below.
            struct_defs=self.func.struct_defs,
            identifiers=self.func.identifiers,
            func_scope=self.func.func_scope,
            open_namespaces=self.func.open_namespaces,
            div_var_basename=self.div_var_basename,
            div_var_startnum=0,
            local_vars=self.lvars,
            name_sub=self.name_sub,
            prefix=self.prefix,
            hint_vars=[],
        )

    def indent(self):
        self.prefix += " " * LEAN_CODE_INDENT

    def outdent(self):
        self.prefix = self.prefix[:-LEAN_CODE_INDENT]

    def mk_block_specs(self) -> List[str]:
        """
        This is the main function of this object, generating the properties asserted
        by the specification of this block.
        """
        while self.lean_desc_num < len(self.func.lean_desc):

            # Prepare the processing of the next instruction.
            instr = self.func.lean_desc[self.lean_desc_num]
            self.set_context_for_instruction(instr)

            if (
                self.spec_start_lean_desc < self.lean_desc_num
                and self.lean_desc_num in self.func.join_points
            ):
                # Reached an independent block. This terminates the block spec generation.
                self.mk_call_next_block_spec()
                return self.asserts

            self.trace_count.count += get_instr_trace_count(instr)
            self.mk_instr_specs(instr)

            if (
                isinstance(instr, LeanPreprocessedReturn)
                or isinstance(instr, LeanPreprocessedTailCall)
                # An if statement (or conditional jump) terminates the block because the remaining
                # instructions in the block are handled recursively in the two branches of
                # the if-then-else.
                or isinstance(instr, LeanPreprocessedIf)
                or (
                    isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
                    and instr.condition is not None
                )
            ):
                return self.asserts

            # Advance to the next instruction.
            if isinstance(instr, LeanPreprocessedJumpToLabelInstruction):
                self.lean_desc_num = self.func.label_dict[instr.label_name]
            else:
                self.lean_desc_num += 1

        raise Exception("Expected a return to end the block.")

    def set_context_for_instruction(self, instr: LeanPreprocessedCodeElement):
        """
        Set the context for processing the next instruction.
        """
        self.simplifier.set_instr(instr)
        self.div_var_basename = "δ{}_".format(self.lean_desc_num)
        self.desc_ctx = dataclasses.replace(
            self.desc_ctx,
            div_var_basename=self.div_var_basename,
            prefix=self.prefix,
            hint_vars=instr.get_hint_vars()
            if isinstance(instr, LeanPreprocessedWithAsserts)
            else [],
        )

    def mk_call_next_block_spec(self):
        """
        Generates the asserted specifications when arriving at an independent block
        (which has a separate spec definition).
        """
        auto_spec_name = (
            mk_lean_auto_spec_name(self.func.name, self.func.open_namespaces)
            + "_block"
            + str(self.lean_desc_num)
        )
        self.trace_count.calls += 1
        trace_var = add_name_sub("κ", self.trace_count.calls)
        args = [trace_var] + self.get_block_spec_arg_names(self.lean_desc_num, self.name_sub)
        block_spec = f"∃ ({trace_var} : ℕ), {auto_spec_name} mem {' '.join(args)}"
        self.add_assert(block_spec)
        self.add_trace_count_assert()

    def mk_instr_specs(self, instr: LeanPreprocessedCodeElement):

        if isinstance(instr, LeanPreprocessedWithAsserts):
            for hint in instr.get_hint_vars():
                lean_type = get_lean_type(
                    hint.resolved_type, self.func.func_scope, self.func.open_namespaces
                )
                name = next_name_with_sub(hint.identifier.identifier.name, self.name_sub)
                self.add_assert(f"∃ {LEAN_HINT_VAR_PREFIX}{name} : {lean_type},")

        if isinstance(instr, LeanPreprocessedAssertEq) or isinstance(
            instr, LeanPreprocessedCompoundAssertEq
        ):
            self.mk_assert_specs(instr)
        elif (isinstance(instr, LeanPreprocessedReference) and not instr.asserts) or isinstance(
            instr, LeanPreprocessedTempVar
        ):
            self.mk_var_specs(instr)
        elif isinstance(instr, LeanPreprocessedConst):
            self.mk_const_specs(instr)
        elif isinstance(instr, LeanPreprocessedFuncCall):
            self.mk_func_call_specs(instr)
        elif isinstance(instr, LeanPreprocessedIf):
            self.mk_if_specs(instr)
        elif (
            isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
            and instr.condition is not None
        ):
            self.mk_cond_jmp_specs(instr)
        elif isinstance(instr, LeanPreprocessedReturn):
            self.mk_return_specs(instr)

    def mk_assert_specs(
        self,
        instr: Union[LeanPreprocessedAssertEq, LeanPreprocessedCompoundAssertEq],
    ):
        """
        Creates the specs both for a simple and a compound assert.
        """
        self.append_div_var_asserts([instr.lhs, instr.rhs])
        self.desc_ctx = dataclasses.replace(
            self.desc_ctx,
            div_var_startnum=0,
            cairo_type=instr.resolved_type
            if isinstance(instr, LeanPreprocessedCompoundAssertEq)
            else TypeFelt(),
        )
        # Simplifier ends up adding rhs asserts first.
        rhs, self.desc_ctx.div_var_startnum = to_lean_description_aux(
            expr=instr.rhs,
            context=self.desc_ctx,
        )
        lhs, self.desc_ctx.div_var_startnum = to_lean_description_aux(
            expr=instr.lhs,
            context=self.desc_ctx,
        )
        self.add_assert(f"{lhs} = {rhs}")
        if self.rc_steps is not None:
            for rc_spec in self.rc_steps.get_assert_rc_spec(instr.lhs, instr.rhs, self.desc_ctx):
                self.add_assert(rc_spec)

    def mk_var_specs(self, instr: Union[LeanPreprocessedReference, LeanPreprocessedTempVar]):
        base_name = instr.identifier.identifier.name
        lean_type = get_lean_type(
            instr.resolved_type, self.func.func_scope, self.func.open_namespaces
        )
        name = next_name_with_sub(base_name, self.name_sub)
        if is_fp_ref(instr.expr) or is_ap_ref(instr.expr) or instr.expr is None:
            self.add_assert(f"∃ {name} : {lean_type},")
        else:
            self.append_div_var_asserts([instr.expr])
            self.desc_ctx = dataclasses.replace(
                self.desc_ctx,
                div_var_startnum=0,
                cairo_type=instr.resolved_type,
            )
            self.add_assert(
                "∃ {} : {}, {} = {}".format(
                    name,
                    lean_type,
                    name,
                    to_lean_description(expr=instr.expr, context=self.desc_ctx),
                ),
            )
        if self.rc_steps is not None:
            self.rc_steps.add_step_from_var(base_name, instr.expr, self.name_sub)
            for rc_spec in self.rc_steps.get_var_rc_spec(
                name=name, expr=instr.expr, desc_ctx=self.desc_ctx
            ):
                self.add_assert(rc_spec)
        inc_name_sub(base_name, self.name_sub)

    def mk_const_specs(self, instr: LeanPreprocessedConst):
        """
        Generates the specs for a constant local to the function, which is currently
        handled as a variable with a constant value.
        """
        name = str(instr.name[-1:])
        if name not in LEAN_IGNORE_CONSTS:
            self.add_assert("∃ {} : F, {} = {}".format(name, name, instr.val))

    def mk_func_call_specs(self, instr: LeanPreprocessedFuncCall):
        spec_name = mk_lean_user_spec_name(instr.name, self.func.open_namespaces)
        fn = self.lean_info.function_dict[instr.name]
        # Create the variables needed for the default division values (if any).
        self.append_div_var_asserts(instr.func_args)
        # First generate the call arguments, only then the return variables,
        # as implicit arguments need to have a higher subscript on the return variable.
        call_args = gen_implicit_args(fn, len(instr.func_args), self.name_sub)
        arg_descs = []
        self.desc_ctx = dataclasses.replace(
            self.desc_ctx,
            div_var_startnum=0,
            cairo_type=None,
        )
        self.trace_count.calls += 1
        trace_var = add_name_sub("κ", self.trace_count.calls)
        for arg in instr.func_args:
            call_arg, self.desc_ctx.div_var_startnum = to_lean_paren_description_aux(
                expr=arg,
                context=self.desc_ctx,
            )
            arg_descs.append(call_arg)
        call_args += " ".join(arg_descs)

        if isinstance(instr, LeanPreprocessedTailCall):
            # The return variables of the tail call are the same as those of the calling
            # function.
            ret_vars_str = " ".join(self.func.get_ret_arg_names())
            self.add_assert(
                f"∃ ({trace_var} : ℕ), {spec_name} mem {trace_var} {call_args} {ret_vars_str}"
            )
            self.add_trace_count_assert()
            return

        ret_vars = [
            inc_name_sub(fn.arg_names[j], self.name_sub) for j in range(fn.num_implicit_args)
        ]
        num_returns = fn.num_returns
        if num_returns == len(instr.ret_vars):
            for pos, ret_var in enumerate(instr.ret_vars):
                if ret_var == "_":
                    ret_vars.append(f"ret{self.num_func_calls}_{pos}")
                else:
                    ret_vars.append(inc_name_sub(ret_var, self.name_sub))
        else:
            ret_vars += [f"ret{self.num_func_calls}_{j}" for j in range(num_returns)]
        if len(ret_vars) > 0:
            ret_defs = create_arg_defs(fn.add_types_to_ret_names(ret_vars))
            self.add_assert(
                "∃ ({} : ℕ) {}, {} mem {} {} {}".format(
                    trace_var,
                    " ".join(ret_defs),
                    spec_name,
                    trace_var,
                    call_args,
                    " ".join(ret_vars),
                ),
            )
        else:
            self.add_assert(f"∃ ({trace_var} : ℕ), {spec_name} mem {trace_var} {call_args}")
        self.num_func_calls += 1

    def mk_if_specs(self, instr: LeanPreprocessedIf):
        """
        Adds the specifications for both branches of the if-then-else. This includes
        the code inside the if-then-else blocks and all code that follows the if-then-else,
        which usually is handled by a separate spec block definition.
        """
        assert instr.jump_instr is not None, "Jump instruction missing in if block."
        self.desc_ctx = dataclasses.replace(
            self.desc_ctx,
            div_var_startnum=0,
            cairo_type=None,
        )
        self.append_div_var_asserts([instr.expr_a, instr.expr_b])
        expr_a, self.desc_ctx.div_var_startnum = to_lean_description_aux(
            expr=instr.expr_a,
            context=self.desc_ctx,
        )
        expr_b, self.desc_ctx.div_var_startnum = to_lean_description_aux(
            expr=instr.expr_b,
            context=self.desc_ctx,
        )
        self.mk_cond_branch_specs(
            expr_a=expr_a,
            expr_b=expr_b,
            cond_eq=instr.cond_eq,
            neg_lean_desc_num=self.func.label_dict[instr.jump_instr.label_name],
        )

    def mk_cond_jmp_specs(self, instr: LeanPreprocessedJumpToLabelInstruction):
        name = "anon_cond"
        self.add_assert(f"∃ {name} : F,")
        self.mk_cond_branch_specs(
            expr_a=name,
            expr_b="0",
            cond_eq=True,
            neg_lean_desc_num=self.func.label_dict[instr.label_name],
        )

    def mk_cond_branch_specs(self, expr_a: str, expr_b: str, cond_eq: bool, neg_lean_desc_num: int):
        cond_pos = f"{expr_a} = {expr_b}"
        cond_neg = f"{expr_a} ≠ {expr_b}"
        pos_ctx = LeanSpecBlockGenerator(
            func=self.func,
            lean_info=self.lean_info,
            simplifier=self.simplifier,
            spec_start_lean_desc=self.spec_start_lean_desc,
            lean_desc_num=self.lean_desc_num + 1,
            name_sub=self.name_sub,
            trace_count=self.trace_count,
            rc_steps=self.rc_steps,
            num_func_calls=self.num_func_calls,
            prefix=self.prefix,
        )
        pos_ctx.indent()
        pos_asserts_aux = pos_ctx.mk_block_specs()
        if pos_asserts_aux:
            pos_asserts = [cond_pos + " ∧\n  " + self.prefix] + pos_asserts_aux
        else:
            pos_asserts = [cond_pos]

        neg_asserts = [cond_neg]
        if neg_lean_desc_num > self.lean_desc_num:
            neg_ctx = LeanSpecBlockGenerator(
                func=self.func,
                lean_info=self.lean_info,
                simplifier=self.simplifier,
                spec_start_lean_desc=self.spec_start_lean_desc,
                lean_desc_num=neg_lean_desc_num,
                name_sub=self.name_sub,
                trace_count=self.trace_count,
                rc_steps=self.rc_steps,
                num_func_calls=self.num_func_calls,
                prefix=self.prefix,
            )
            neg_ctx.indent()
            neg_asserts_aux = neg_ctx.mk_block_specs()
            if neg_asserts_aux:
                neg_asserts = [cond_neg + " ∧\n  " + self.prefix] + neg_asserts_aux

        disj_asserts = (
            ["(("] + pos_asserts + [") ∨\n" + self.prefix + " ("] + neg_asserts + ["))"]
            if cond_eq
            else ["(("] + neg_asserts + [") ∨\n" + self.prefix + " ("] + pos_asserts + ["))"]
        )
        self.append_asserts(disj_asserts)

    def mk_return_specs(self, instr: LeanPreprocessedReturn):
        self.add_trace_count_assert()
        for name in self.func.get_implicit_arg_names():
            self.add_assert(
                f"{LEAN_RETURN_VAR_PREFIX}{name} = {name_with_sub(name, self.name_sub)}",
            )
        self.append_div_var_asserts(instr.ret_arg_exprs)
        self.desc_ctx.div_var_startnum = 0
        for j in range(self.func.num_returns):
            self.desc_ctx = dataclasses.replace(
                self.desc_ctx,
                cairo_type=self.func.ret_arg_types[j],
            )
            rhs, self.desc_ctx.div_var_startnum = to_lean_description_aux(
                expr=instr.ret_arg_exprs[j],
                context=self.desc_ctx,
            )
            self.add_assert(f"{self.func.ret_arg_names[j]} = {rhs}")
        if not self.asserts or self.asserts[-1].rstrip()[-1] == ",":
            self.add_assert("true")

    def add_trace_count_assert(self):
        """
        Adds the assertion bounding the trace count at this point.
        """
        if self.trace_count.count == 0 and self.trace_count.calls == 0:
            return
        if 0 < self.trace_count.calls:
            trace_count_assert = (
                " + ".join([add_name_sub("κ", i + 1) for i in range(0, self.trace_count.calls)])
                + (" + " + str(self.trace_count.count) if 0 < self.trace_count.count else "")
                + " ≤ κ"
            )
        else:
            trace_count_assert = f"{self.trace_count.count} ≤ κ"
        self.add_assert(trace_count_assert)

    def append_div_var_asserts(self, exprs: List[Expression]):
        """
        Asserts the existence of default values for the division symbols in
        exprs, if there are any.
        """
        num_divs = sum([count_div_ops(expr, self.simplifier) for expr in exprs], 0)
        if num_divs != 0:
            varnames = ["{}{}".format(self.div_var_basename, i) for i in range(num_divs)]
            self.add_assert("∃ {} : F,".format(" ".join(varnames)))

    def add_assert(self, assertstr: str):
        if len(self.asserts) == 0:
            self.asserts.append(assertstr)
        elif self.asserts[-1].rstrip()[-1] == ",":
            self.asserts.append("\n" + self.prefix + assertstr)
        else:
            self.asserts.append(" ∧\n" + self.prefix + assertstr)

    def append_asserts(self, to_append: List[str]):
        """
        Appends the given asserts to the existing asserts, adding
        a conjuction if needed.
        """
        if len(self.asserts) == 0:
            self.asserts += to_append
        elif self.asserts[-1].rstrip()[-1] == ",":
            self.asserts += ["\n" + self.prefix] + to_append
        else:
            self.asserts += [" ∧\n" + self.prefix] + to_append

    # Auxiliary generation functions.

    def get_block_spec_args(self, block_desc_num: int) -> Dict[str, str]:
        assert block_desc_num in self.func.block_list
        arg_types = self.func.block_list[block_desc_num].get_args_with_type()
        arg_types.update(self.func.get_ret_args_with_type())
        return arg_types

    def get_block_spec_arg_names(
        self,
        block_desc_num: int,
        name_sub: Optional[Dict[str, int]],
    ) -> List[str]:
        """
        Returns the list of names of arguments of a block (without types). When
        a list of subscripts is provided, those subscripts are used for the variables.
        """
        base_names = list(self.get_block_spec_args(block_desc_num))
        return (
            [name_with_sub(name, name_sub) for name in base_names]
            if name_sub is not None
            else base_names
        )
