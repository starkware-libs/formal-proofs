import dataclasses
from typing import Dict, List, Optional, Set, Tuple

from starkware.cairo.lang.compiler.ast.expr import (
    ExprCast,
    ExprDeref,
    Expression,
    ExprIdentifier,
    ExprNeg,
    ExprOperator,
    ExprParentheses,
    ExprPow,
    ExprTuple,
)
from starkware.cairo.lang.compiler.ast.expr_func_call import ExprFuncCall
from starkware.cairo.lean.verification.expr_to_lean import (
    LeanDescContext,
    get_const,
    to_lean_description,
)
from starkware.cairo.lean.verification.rc_builtin import RCBuiltin
from starkware.cairo.lean.verification.rebinding import add_name_sub, get_next_name_sub

# The RC steps track not only the steps being made, but also the name used
# at every step. There is no requirement that all steps be made using the same name.
# However, no splitting sequences are currently supported.
# All steps in the proof can now be carried out with the sequences of steps which
# do not necessarily need to be performed on the same name.


@dataclasses.dataclass
class RCStep:
    base_name: str
    sub: int  # Name subscript.
    step: str  # Size of step (may be a number or a Lean variable name).
    # The rewrites for the ap offset of function calls which do not have
    # an rc argument and take place between this step and the next step.
    next_ap_rws: List[str] = dataclasses.field(default_factory=lambda: [])

    def get_name(self) -> str:
        """
        Returns the full name (with subscript) of the variable which is
        the result of this step.
        """
        return add_name_sub(self.base_name, self.sub)

    def copy(self):
        """
        Returns a copy of this object, so that any editing of this object
        has no effect on the copy.
        """
        return RCStep(self.base_name, self.sub, self.step, self.next_ap_rws.copy())


@dataclasses.dataclass
class RCSteps:
    rc_builtin: RCBuiltin
    # All variable names used for the builtin pointer.
    names: Set[str] = dataclasses.field(default_factory=lambda: set())
    steps: List[RCStep] = dataclasses.field(default_factory=lambda: [])

    def __post_init__(self):
        self.names.add(self.rc_builtin.arg_name)
        self.steps = [RCStep(base_name=self.rc_builtin.arg_name, sub=0, step="0")]

    def copy_from(self, rc):
        """
        Copies the values from 'rc' to this object
        """
        self.names = rc.names.copy()
        self.steps = [step.copy() for step in rc.steps]

    def active(self):
        """
        Returns True if the object represents the built-in steps of a function
        which uses that built-in (otherwise, the built-in is not used in the function)
        """
        return len(self.names) > 0

    def is_rc_ptr_name(self, name: str) -> bool:
        """
        Checks whether this name is one of the names used as an rc pointer in
        the current execution sequence.
        """
        return name in self.names

    def is_rc_ptr_expr(self, e: Expression) -> bool:
        if isinstance(e, ExprCast):
            return self.is_rc_ptr_expr(e.expr)
        elif isinstance(e, ExprParentheses):
            return self.is_rc_ptr_expr(e.val)
        elif isinstance(e, ExprIdentifier):
            return self.is_rc_ptr_name(e.name)
        else:
            return False

    def get_rc_ptr_name(self, e: Expression) -> Optional[str]:
        """
        If the expression is <rc ptr>, returns the name of the pointer.
        """
        if isinstance(e, ExprCast):
            return self.get_rc_ptr_name(e.expr)
        elif isinstance(e, ExprParentheses):
            return self.get_rc_ptr_name(e.val)
        elif isinstance(e, ExprIdentifier):
            return e.name if self.is_rc_ptr_name(e.name) else None
        else:
            return None

    def get_rc_step_name(self, e: Expression) -> Optional[str]:
        """
        If the expression is <rc ptr> or <rc ptr> + c, returns the name <rc ptr>
        """
        name = self.get_rc_ptr_name(e)
        if name != None:
            return name

        if isinstance(e, ExprCast):
            return self.get_rc_step_name(e.expr)
        elif isinstance(e, ExprParentheses):
            return self.get_rc_step_name(e.val)
        elif isinstance(e, ExprOperator):
            if e.op != "+" and e.op != "-":
                return None
            if get_const(e.a) != None:
                return self.get_rc_ptr_name(e.b)
            elif get_const(e.b) != None:
                return self.get_rc_ptr_name(e.a)
            else:
                return None
        else:
            return None

    def get_rc_check_name(self, expr: Expression) -> Optional[str]:
        """
        If the expression is [<rc ptr>] or [<rc ptr> + c], returns the name <rc ptr>
        """
        if isinstance(expr, ExprCast):
            return self.get_rc_check_name(expr.expr)
        elif isinstance(expr, ExprParentheses):
            return self.get_rc_check_name(expr.val)
        elif isinstance(expr, ExprDeref):
            return self.get_rc_step_name(expr.addr)
        else:
            return None

    def get_rc_step_size(self, e: Expression, allow_zero: bool = True) -> Optional[int]:
        """
        If the expression is <rc ptr> + c, returns the value of c.
        If allow_zero it true, 0 is returned for an expression <rc ptr>.
        Otherwise, None is returned in this case.
        """
        if isinstance(e, ExprCast):
            return self.get_rc_step_size(e.expr)
        elif isinstance(e, ExprParentheses):
            return self.get_rc_step_size(e.val)
        elif isinstance(e, ExprOperator):
            if e.op != "+" and e.op != "-":
                return None
            if self.is_rc_ptr_expr(e.a):
                rc_const = get_const(e.b)
                return None if rc_const is None else (rc_const if e.op == "+" else -rc_const)
            elif self.is_rc_ptr_expr(e.b):
                rc_const = get_const(e.a)
                return None if rc_const is None else (rc_const if e.op == "+" else -rc_const)
            else:
                return None
        elif allow_zero and self.is_rc_ptr_expr(e):
            return 0
        else:
            return None

    def get_rc_step(self, e: Expression, allow_zero: bool) -> Optional[str]:
        """
        If the expression is <rc ptr> + c, returns the string str(c).
        If allow_zero is True the this returns "0" if the expression is <rc ptr>.
        """
        c = self.get_rc_step_size(e, allow_zero)
        return str(c) if c is not None else None

    def get_rc_check_offset(self, e: Expression) -> Optional[int]:
        """
        If e is an expression [<rc ptr> + c], this function returns c and
        otherwise, None.
        """
        if isinstance(e, ExprCast):
            return self.get_rc_check_offset(e.expr)
        elif isinstance(e, ExprParentheses):
            return self.get_rc_check_offset(e.val)
        elif isinstance(e, ExprDeref):
            return 0 if self.is_rc_ptr_expr(e.addr) else self.get_rc_step_size(e.addr)
        else:
            return None

    def get_rc_check_name_and_offset(
        self,
        expr: Expression,
    ) -> Tuple[Optional[str], Optional[int]]:
        """
        If expr is an expression [<rc ptr> + c], this function returns the name of the rc pointer
        and the offset c. Otherwise, (None, None) is returned.
        The rc pointer name is returned with the appropriate rebinding index and this index
        is adjusted so that the offset is positive.
        """
        if isinstance(expr, ExprCast):
            return self.get_rc_check_name_and_offset(expr.expr)
        elif isinstance(expr, ExprParentheses):
            return self.get_rc_check_name_and_offset(expr.val)
        elif isinstance(expr, ExprDeref):
            name = self.get_rc_step_name(expr.addr)
            offset = self.get_rc_step_size(expr.addr, True)
            if name is None or offset is None:
                return (None, None)
            for step in reversed(self.steps):
                if 0 <= offset:
                    return add_name_sub(name, step.sub), offset
                if not step.step.isdigit():
                    # This step is not of a known integer size, but of variable size
                    # (such as a range checked function call).
                    break
                offset += int(step.step)
            raise Exception(
                "Range check backward offset points before initial range check pointer."
            )
        else:
            return (None, None)

    def get_rc_checks(self, expr: Expression) -> List[Tuple[Expression, str, int]]:
        """
        Returns the list of range check expressions which appear inside the expression.
        Any sub-expression of the form [<rc ptr> + c] is a range check expression.
        The function returns a list of these sub-expressions.
        The function returns a list of tuples, with each tuple holding the expression,
        range check pointer name and the offset c.
        When the rc expression is wrapped by a cast or parentheses, the outer expression
        (with the cast or parentheses) is returned.
        """
        rc_name, rc_offset = self.get_rc_check_name_and_offset(expr)
        if rc_name is not None and rc_offset is not None:
            return [(expr, rc_name, rc_offset)]

        if isinstance(expr, ExprNeg):
            return self.get_rc_checks(expr.val)
        if isinstance(expr, ExprOperator) or isinstance(expr, ExprPow):
            return self.get_rc_checks(expr.a) + self.get_rc_checks(expr.b)
        if isinstance(expr, ExprFuncCall):
            rc_checks: List[Tuple[Expression, str, int]] = []
            for arg in expr.rvalue.arguments.args:
                rc_checks += self.get_rc_checks(arg.expr)
            return rc_checks
        if isinstance(expr, ExprTuple):
            rc_checks = []
            for arg in expr.members.args:
                rc_checks += self.get_rc_checks(arg.expr)
        return []

    # Step addition functions.

    def add_step_from_var(self, base_name: str, expr: Expression, name_sub: Dict[str, int]) -> bool:
        """
        Adds an rc pointer step for a variable assignment of the form:
        let <base_name> = <rc ptr> + c
          or
        tempvar <base name> = <rc ptr> + c
        where <rc ptr> is the rc pointer of the previous step.
        The new pointer is assigned to the variable with the given base_name.
        It is assumed that the subscript of 'base_name' in 'name_sub' has not
        yet been advanced to reflect this assignment. This function does not
        advance the subscript either.
        Returns True if an rc step was added.
        """
        step = self.get_rc_step(expr, True)
        if step is None:
            return False
        prev_name = self.get_rc_step_name(expr)
        # Currently we do not support splitting of the steps into multiple chains.
        if self.steps[-1].base_name != prev_name:
            return False
        self.names.add(base_name)
        self.steps.append(RCStep(base_name, get_next_name_sub(base_name, name_sub), step))
        return True

    def add_func_step(self, called_rc_builtin: RCBuiltin, step_id: str) -> bool:
        """
        Adds the step implied by a call to a function, if the function takes
        an rc pointer as an implicit argument.
        """
        prev_step = self.steps[-1]
        # Requires that the last range check pointer has the same name as
        # the range check pointer argument of the called function.
        if called_rc_builtin.arg_name != prev_step.base_name:
            return False

        self.steps.append(RCStep(prev_step.base_name, prev_step.sub + 1, f"rc_m{step_id}"))
        return True

    # Application of the built-in property to variables and expressions.

    def get_assert_rc_check(
        self,
        lhs: Expression,
        rhs: Expression,
    ) -> List[Tuple[Expression, str, int]]:
        """
        Returns a list of expressions range checked by an assert. For each
        expression, the list contains a tuple (checked_expr, rc_check_name, rc_check_offset)
        which holds the expression that was range checked, the rc variable (with
        rebinding subscript) that range checked it and the range check offset.
        If the assert is of the form:
        <checked_expr> = [<rc_check_name> + <rc_check_offset>]
          or
        [<rc_check_name> + <rc_check_offset>] = <checked_expr>
        the <checked_expr> is returned as the expression that was ranged checked.
        In other cases the expression [<rc_check_name> + <rc_check_offset>] is returned.
        """
        if not self.active():
            return []

        rhs_checks = self.get_rc_checks(rhs)
        lhs_checks = self.get_rc_checks(lhs)
        if len(rhs_checks) == 0 and len(lhs_checks) == 1:
            rc_expr, rc_check_name, rc_check_offset = lhs_checks[0]
            if rc_expr == lhs:
                return [(rhs, rc_check_name, rc_check_offset)]

        if len(lhs_checks) == 0 and len(rhs_checks) == 1:
            rc_expr, rc_check_name, rc_check_offset = rhs_checks[0]
            if rc_expr == rhs:
                return [(lhs, rc_check_name, rc_check_offset)]

        return lhs_checks + rhs_checks


@dataclasses.dataclass
class SpecRCSteps(RCSteps):
    """
    Extends the range check step tracking class to generate the specifications
    implied by the use of the range check pointer in asserts and variable
    assignments.
    """

    def branch(self):
        """
        Returns a new SpecRCSteps object with copies of the sets and lists.
        This should be called before entering a branch, so that
        steps added in the branch are only added to the copy object and not
        the original SpecRCSteps object (which can then be used as the starting
        point for the next branch)
        """
        rc = SpecRCSteps(self.rc_builtin)
        rc.copy_from(self)
        return rc

    def get_assert_rc_spec(
        self, lhs: Expression, rhs: Expression, desc_ctx: LeanDescContext
    ) -> List[str]:
        """
        Returns a list of 'is_range_checked <expr>' specifications for expressions
        inside an assert <lhs> = <rhs>.
        """
        return [
            f"is_range_checked (rc_bound F) ({to_lean_description(expr=expr, context=desc_ctx)})"
            for expr, _, _ in self.get_assert_rc_check(lhs, rhs)
        ]

    def get_var_rc_spec(self, name: str, expr: Expression, desc_ctx: LeanDescContext) -> List[str]:
        """
        Returns a list of 'is_range_checked <expr>' specifications for expressions
        in a variable assignment:
        let <name> = <expr>
          or
        tempvar <name> = <expr>
        If <expr> is [<range check ptr> + c], the range checked expression is
        the variable name.
        """
        return [
            f"is_range_checked (rc_bound F) {expr_desc}"
            for expr_desc in [
                name
                if rc_expr == expr
                else f"({to_lean_description(expr=rc_expr, context=desc_ctx)})"
                for rc_expr, _, _ in self.get_rc_checks(expr)
            ]
        ]


@dataclasses.dataclass
class SoundnessRCSteps(RCSteps):
    """
    Extends the range check step tracking class to generate the code needed
    in the automatic soundness proof to prove the properties implied by
    the use of the range check built-in.
    """

    bounds: List[str] = dataclasses.field(default_factory=lambda: [])
    # All rewrites which apply to the range check pointers.
    rc_rw: List[str] = dataclasses.field(default_factory=lambda: [])

    def __post_init__(self):
        super().__post_init__()
        self.rc_rw.append("hin_" + self.steps[0].get_name())

    def copy_from(self, rc):
        """
        Copies the values from 'rc' to this object
        """
        super().copy_from(rc)
        self.bounds = rc.bounds.copy()
        self.rc_rw = rc.rc_rw.copy()

    def branch(self):
        """
        Returns a new SoundnessRCSteps object with copies of the sets and lists.
        This should be called before entering a branch, so that
        steps added in the branch are only added to the copy object and not
        the original SoundnessRCSteps object (which can then be used as the starting
        point for the next branch)
        """
        rc = SoundnessRCSteps(self.rc_builtin)
        rc.copy_from(self)
        return rc

    def get_all_ap_rw(self) -> List[str]:
        """
        Returns all the ap rewrites of all steps, in reverse order (last step
        first).
        """
        return [ap_rw for step in reversed(self.steps) for ap_rw in reversed(step.next_ap_rws)]

    def get_ap_rw_after(self, step_name: str) -> List[str]:
        """
        Returns the list of all ap rewrites which apply after the step with the given
        name. The rewrites are returned in reverse order (last step first).
        """
        ap_rw = []
        for step in reversed(self.steps):
            ap_rw += list(reversed(step.next_ap_rws))
            if step.get_name() == step_name:
                break

        return ap_rw

    def get_last_htv(self) -> Optional[str]:
        """
        Returns the last htv_<rc pointer> rewrite. This provides the last memory
        location to which the rc pointer was copied so far.
        """
        htv = filter(lambda s: s.startswith("htv_"), reversed(self.rc_rw))
        return next(htv, None)

    def gen_rc_rw_ref_to_in_arg(self, n: int):
        """
        returns the list of range check point rewrites, which rewrites
        an expression mem _ + c referring to the n'th range check pointer
        to an expression mem (σ.fp - _) + c_1 + ... which represents the
        same pointer, but with reference to the input rc pointer as input argument
        to the function.
        The input range check pointer is considered to have index 0.
        """
        rc_rw = []
        if len(self.steps) < n + 1:
            raise Exception("fewer range check steps than expected")

        if n >= 1:
            rc_rw += ["←htv_" + self.steps[n].get_name()] + list(
                reversed(["hl_{}".format(self.steps[i].get_name()) for i in range(1, n + 1)])
            )
        rc_rw += ["hin_" + self.steps[0].get_name()]
        return rc_rw

    def gen_rc_rw_in_arg_to_ptr(self, n: int):
        """
        returns the list of range check point rewrites, which rewrites
        an expression mem (σ.fp - _) + c_1 + ... into the name of
        the n'th range check pointer (the pointer after the n'th step). The original
        expression represents the range check pointer relative to a reference
        to the input range check point mem (σ.fp + _)
        """
        if len(self.steps) < n + 1:
            raise Exception("fewer range check steps than expected")

        rc_rw = ["←hin_" + self.steps[0].get_name()]
        if n >= 1:
            rc_rw += ["←hl_{}".format(self.steps[i].get_name()) for i in range(1, n + 1)]
        return rc_rw

    def gen_rc_rw_mem_to_in(self) -> Tuple[List[str], List[str]]:
        """
        Returns, in the first list, the list of range check pointer rewrites,
        which will rewrite the last memory cell assigned to a range check pointer,
        to an expression mem (σ.fp + c) + c_1 + ... which represents the same rc pointer
        relative to the the input rc pointer argument of the function.
        The second list returned consists of the ap rewrites which bridge the gap
        between the last base ap pointer so far (after all function calls so far)
        and the base ap pointer of the last range check pointer. This list mat be
        empty.
        """
        rc_rw = self.rc_rw
        # Find the position of last "htv_*" "hbtv_*" in rc_rw. An "hbtv_" rewrite
        # indicates that we are applying a final block under special conditions
        # (add_block_step() determines when to create such a rewrite).
        for i, rw in enumerate(reversed(self.rc_rw)):
            if "htv_" in rw or "hbtv_" in rw:
                if i != 0:
                    rc_rw = self.rc_rw[:-i]
                break
        else:
            # No range check pointer assigned a memory cell except the first one,
            # so the list of rewrites is empty, and we need the full list of
            # ap steps.
            return ([], self.get_all_ap_rw())
        return (
            ["←" + rc_rw[-1]] + list(filter(lambda x: "hl_" in x or "hin_" in x, reversed(rc_rw))),
            self.get_ap_rw_after(rc_rw[-1][len("htv_") :]),
        )

    def add_rc_rw_to_in(self, at_expr: str) -> List[str]:
        """
        Generates proof lines that rewrite the latest memory in which the
        range-check pointer is stored into an equivalent expression relative
        to the input range check pointer. If at_expr is not empty, this is the
        expression to which the rewrites are applied.
        """
        rc_rw, ap_rw = self.gen_rc_rw_mem_to_in()
        proof_lines = []
        rw_at = f" at {at_expr}" if at_expr else ""

        if ap_rw:
            proof_lines.append(
                f'  try {{ simp only [{" ,".join(ap_rw)}]{rw_at} }}, try {{ arith_simps }},'
            )
        if rc_rw:
            proof_lines.append(f'  rw [{", ".join(rc_rw)}]{rw_at},')

        return proof_lines

    def gen_rc_rw_to_last_var(self) -> List[str]:
        """
        returns the list of range check pointer rewrites, going backwards from
        the last rewrite (which represents the current range check pointer)
        to the last "htv_*" rewrite, that is, the last rewrite which associates
        a range check pointer which a memory cell (something of the
        form range_check_ptr = mem _). If there is no such rewrite, this returns
        the full list of rewrites, which begins with hin_*
        This sequence of rewrites rewrites the current range check
        pointer variable into a memory reference + const(s)
        """
        rc_rw = self.rc_rw
        # Find the position of last "htv_*" in rc_rw.
        for i, rw in enumerate(reversed(self.rc_rw)):
            if "htv_" in rw:
                rc_rw = self.rc_rw[-(i + 1) :]
                break
        return list(reversed(rc_rw))

    def add_rc_var_step(
        self, var_name: str, expr: Expression, is_temp_var: bool, name_sub: Dict[str, int]
    ) -> List[str]:
        """
        When called on a variable assignment, checks whether this assignment
        is a step for the current range check pointer. If it is, this function
        adds this step to the list of steps and returns the lines that should be
        added to the final proof. If this variable assignment is not a step,
        this function returns an empty list of proof lines.
        This should be called for every variable assignment (such as
        let x = <expr> or tempvar x = <expr>).
        """
        if not self.active() or not self.add_step_from_var(var_name, expr, name_sub):
            return []
        prev_name = self.steps[-2].get_name()
        new_name = self.steps[-1].get_name()
        # add the variable to the list of rewrites
        self.rc_rw.append("hl_" + new_name)
        # if this is a tempvar, also need to add the rewrite to memory
        if is_temp_var:
            self.rc_rw.append("htv_" + new_name)
        return [
            f"have rc_h_{new_name} := range_checked_offset' rc_h_{prev_name},",
            f"have rc_h_{new_name}' := range_checked_add_right rc_h_{new_name},"
            f"try {{ norm_cast at rc_h_{new_name}' }},",
        ]

    def add_rc_call_arg_var(self, called_rc_builtin: RCBuiltin) -> List[str]:
        """
        Checks whether the called function has a range check pointer argument. If yes,
        and if the last range check pointer before the call was not assigned a memory cell
        (that is, it was created by a 'let') then such a cell is now assigned to it
        by the function call. We here add an 'htv_*' rewrite for it, which binds
        range check pointer name to a reference on the stack.
        The function updates the rc rewrites stored and returns the lines that need to
        be added to the main soundness proof.
        If there is no need to define the variable, this function returns an empty list.
        TO DO: this does not check that the rc argument of the called function is
        the same as the last rc pointer before the call.
        """
        # We assume the function call rc step was not added, so the last step
        # is the input to the function.
        # If the input range check pointer is in memory, there is nothing to do.
        if len(self.steps) < 2 or ("htv_" + self.steps[-1].get_name()) in self.rc_rw:
            return []

        rc_name = self.steps[-1].get_name()
        proof_lines = [
            f"have htv_{rc_name}: {rc_name} = _,",
            # Hack: currently, we assume that the assembly assert which sets the rc pointer
            # argument to the function is in the same position as the argument position.
            # This holds in standard cases, but is not necessarily true if the rc pointer
            # is not the first implicit argument.
            f"{{ apply eq.symm, apply eq.trans arg{called_rc_builtin.arg_index},",
            f'  simp only [{", ".join(self.gen_rc_rw_to_last_var())}]; arith_simps; refl }},',
        ]
        self.rc_rw.append(f"htv_{rc_name}")
        return proof_lines

    def add_called_func_step(
        self, called_rc_builtin: Optional[RCBuiltin], ap_rw: str, step_id: int
    ) -> List[str]:
        """
        Should be called for every function call. When both the calling and
        the called function use the range check pointer, this adds the range check
        pointer step implied by the function call. It returns the lines which need to
        be added to the main soundness proof in this case. If the call does not add
        an rc step, [] is returned. However, it will record the called function ap offset
        if that offset is a constant.
        """
        if not self.active():
            return []
        if called_rc_builtin is None:
            if ap_rw:
                self.steps[-1].next_ap_rws.append(ap_rw)
            return []
        if not self.add_func_step(called_rc_builtin, str(step_id)):
            return []

        rc_name = self.steps[-1].get_name()
        self.bounds.append(f"rc_mle{step_id}")
        self.rc_rw.append(f"hl_{rc_name}")
        return [
            f"rcases h_call{step_id} "
            f"with ⟨rc_m{step_id}, rc_mle{step_id}, hl_{rc_name}, h_call{step_id}⟩,"
        ]

    def add_block_step(
        self,
        called_rc_builtin: Optional[RCBuiltin],
        block_suffix: str,
        ap_rewrites: List[str],
    ) -> List[str]:
        if not self.active():
            return []
        if called_rc_builtin is None:
            return []
        if not self.add_func_step(called_rc_builtin, block_suffix):
            return []

        rc_name = self.steps[-1].get_name()

        lines = [
            f"rcases h{block_suffix} "
            f"with ⟨rc_m{block_suffix}, rc_m_le{block_suffix}, hblk_{rc_name}, h{block_suffix}⟩,",
        ]

        # The rewrite "hblk_<rc pointer>" is the rc hypothesis of a block.
        # We need to rewrite the last htv_ variable (if any) to use the
        # same ap as the rc hypothesis of the block. Because of previous
        # rewrites, this will be the 'oldest' ap which can be reached by
        # ap rewrites (if teh function has a constant ap offset, this mean
        # the initial σ.ap).
        # Since we may also need the original version of the htv_ rewrite,
        # we create a new copy of it, with a new name.
        htv = self.get_last_htv()
        if ap_rewrites and htv is not None:
            htv_name = htv[len("htv_") :]
            lines.append(f"have hbtv_{htv_name} := htv_{htv_name},")
            lines.append(f'try {{ simp only [{" ,".join(ap_rewrites)}] at hbtv_{htv_name} }},')
            lines.append(f"try {{ arith_simps at hbtv_{htv_name} }},")
            self.rc_rw.append(f"hbtv_{htv_name}")

        self.bounds.append(f"rc_m_le{block_suffix}")
        self.rc_rw.append(f"hblk_{rc_name}")

        lines += self.add_rc_rw_to_in(f"h{block_suffix}")

        return lines

    def is_rc_ret_var(self, ret_var) -> bool:
        """
        Returns true if the given variable name is the next variable name to
        be assigned to the range check variable after a function call.
        It is assumed that the range check step associated with the function
        call was already added to the range check steps, if the function
        call indeed has a range check argument.
        """
        return self.active() and ret_var == self.steps[-1].get_name()

    def add_rc_ret_var(self, ret_var, ret_var_rw):
        """
        If ret_var (a return variable for a function call) is the variable
        of the last step, add its rewrite (which rewrite the variable name to
        its memory allocation) to the list of range check rewrites.
        """
        if self.active() and ret_var == self.steps[-1].get_name():
            self.rc_rw.append(ret_var_rw)

    def add_rw_call_range_check(
        self,
        called_rc_builtin: Optional[RCBuiltin],
        step_id: int,
        added_rc_call_arg_var: bool,
        arg_rw: List[str],
    ) -> List[str]:
        """
        This function adds the rewrites that convert the range check step and
        range check hypothesis of the called function into the variables and
        memory references of the calling function.
        Returns the lines that should be added to the soundness proof.
        """
        if not self.active() or called_rc_builtin is None:
            return []
        proof_lines = []
        # Lean variable name of the called function output rc pointer.
        rc_out_name = self.steps[-1].get_name()

        # Convert the rc step in the specification of the called function into a step
        # of the calling function pointers. The 'arg_rw' rewrites are needed only when
        # the rc pointer is copied to the arguments of the called function without
        # increasing it. It is applied optionally, as we don't know whether copying
        # was needed (it may already have been at the right place) and instead of
        # trying to guess which assert (if any) copied the range check pointer,
        # we simply apply optionally all the rewrites that copy function arguments.
        # Only the one that applies will match.
        if not added_rc_call_arg_var and arg_rw:
            proof_lines.append(f'try {{ simp only [{" ,".join(arg_rw)}] at hl_{rc_out_name} }},')

        rc_rw = ["←htv_" + rc_out_name]
        if len(self.steps) > 2:
            ap_rw = list(reversed(self.steps[-2].next_ap_rws))
            rc_rw += ["←htv_" + self.steps[-2].get_name()]
        else:
            ap_rw = list(reversed(self.steps[0].next_ap_rws))
            rc_rw += ["←hin_" + self.steps[0].get_name()]
        if 0 < len(ap_rw):
            proof_lines.append(
                f'try {{ rw [{", ".join(ap_rw)}] at hl_{rc_out_name} }}, '
                + f"try {{ arith_simps at hl_{rc_out_name} }},"
            )
        proof_lines.append(f'rw [{", ".join(rc_rw)}] at hl_{rc_out_name},')

        # Rewrite the range_checked hypothesis of the called function.

        # Apply optionally all the rewrites that copy function arguments.
        # Only the one that applies will match.
        if not added_rc_call_arg_var and arg_rw:
            proof_lines.append(f'try {{ simp only [{" ,".join(arg_rw)}] at h_call{step_id} }},')

        # To rewrite the call, we need the rewrites up to the input rc pointer
        # of the function call (the last rc pointer is now the output rc pointer).
        if 0 < len(ap_rw):
            proof_lines.append(
                f'try {{ rw [{", ".join(ap_rw)}] at h_call{step_id} }}, '
                + f"try {{ arith_simps at h_call{step_id} }},"
            )
        call_rw = self.gen_rc_rw_ref_to_in_arg(len(self.steps) - 2)
        proof_lines.append(f'rw [{", ".join(call_rw)}] at h_call{step_id},')

        return proof_lines

    def add_sub_call_rc_final(
        self, called_rc_builtin: Optional[RCBuiltin], step_id: int, is_tail_call: bool
    ) -> List[str]:
        """
        Generates the rc part of the final proof for handling the rc of a called function.
        """
        if not self.active() or called_rc_builtin is None:
            return []
        proof_lines = []
        # Lean variable names of the called function input an output rc pointers.
        rc_in_name = self.steps[-2].get_name()
        rc_out_name = self.steps[-1].get_name()

        proof_lines.append(f"have rc_h_{rc_out_name} := range_checked_offset' rc_h_{rc_in_name},")
        proof_lines.append(
            f"have rc_h_{rc_out_name}' := range_checked_add_right rc_h_{rc_out_name}, "
            f"try {{ norm_cast at rc_h_{rc_out_name}' }},"
        )
        proof_lines.append(f"have spec{step_id} := h_call{step_id} rc_h_{rc_in_name}',")

        # Previously we rewrote the sub-function specification to something
        # we can prove in the calling function. Now it is time to reverse that rewrite.
        rc_spec_rw = self.gen_rc_rw_in_arg_to_ptr(len(self.steps) - 2)
        # And we also need to rewrite the return reference of the called function to
        # a range check pointer (unless it is a tail function call, in which case
        # the return reference is immediately also a return reference of the calling
        # function).
        if not is_tail_call:
            rc_spec_rw += [f"←htv_{rc_out_name}"]

        proof_lines.append(f'rw [{", ".join(rc_spec_rw)}] at spec{step_id},')
        proof_lines.append(f"try {{ dsimp at spec{step_id}, arith_simps at spec{step_id} }},")
        proof_lines.append(f"use_only [spec{step_id}],")

        return proof_lines

    def add_block_rc_final(
        self,
        called_rc_builtin: Optional[RCBuiltin],
        block_suffix: str,
    ) -> List[str]:
        """
        Generates the rc part of the final proof for handling the rc assumption
        of a block specification.
        """
        if not self.active() or called_rc_builtin is None:
            return []
        proof_lines = []
        # Lean variable names of the called function input an output rc pointers.
        rc_in_name = self.steps[-2].get_name()
        rc_out_name = self.steps[-1].get_name()

        proof_lines.append(f"have rc_h_{rc_out_name} := range_checked_offset' rc_h_{rc_in_name},")
        proof_lines.append(
            f"have rc_h_{rc_out_name}' := range_checked_add_right rc_h_{rc_out_name}, "
            f"try {{ norm_cast at rc_h_{rc_out_name}' }},"
        )
        proof_lines.append(f"have h{block_suffix}' := h{block_suffix} rc_h_{rc_in_name}',")

        # Previously we rewrote the block specification to something
        # we can prove in the calling function. Now it is time to reverse that rewrite.
        rc_block_rw = self.gen_rc_rw_in_arg_to_ptr(len(self.steps) - 2)

        proof_lines.append(f"try {{ rw [{', '.join(rc_block_rw)}] at h{block_suffix}' }},")
        proof_lines.append(f"try {{ dsimp at h{block_suffix}, arith_simps at h{block_suffix}' }},")
        proof_lines.append(f"have h{block_suffix} := h{block_suffix}',")

        return proof_lines

    def add_assert_range_checked(
        self,
        lhs: Expression,
        rhs: Expression,
        assert_rw: str,
    ) -> List[str]:
        """
        When called on an assert which implies one or more range checks this returns
        the lines that need to be added to the final proof to prove the asserted
        range checked property.
        This should be called on every assert. When the assert does not imply
        a range check, this returns an empty list of lines to add to the proof.
        """
        proof_lines = []
        for checked_expr, rc_check_name, rc_check_offset in self.get_assert_rc_check(lhs, rhs):
            proof_lines.append(
                f"cases rc_h_{rc_check_name}' ({str(rc_check_offset)}) "
                "(by norm_num1) with n hn, arith_simps at hn,"
            )

            # Only rewrites between pointer names (not memory assignments).
            rc_rw = list(filter(lambda x: "htv_" not in x, self.rc_rw))
            if checked_expr == lhs:
                rc_rw.append(assert_rw)
            elif checked_expr == rhs:
                assert_rw += ".symm"
                rc_rw.append(assert_rw)
            rc_rw.reverse()
            proof_lines.append(
                f'use_only [n], {{ simp only [{", ".join(rc_rw)}], arith_simps, exact hn }},'
            )

        return proof_lines

    def add_var_range_checked(self, expr: Expression, var_rw: str) -> List[str]:
        """
        When called on a variable assignment which implies range checking
        (something like 'let a = [range_check_ptr + 2]') where 'expr' is
        the expression assigned to the variable, this function returns
        the lines that should be added to the soundness proof to prove
        the range check proeprty for this variable.
        This should be called on every variable assignment. It returns an
        empty list when the variable assignment does not imply range checking.
        """
        proof_lines = []
        for checked_expr, rc_check_name, rc_check_offset in self.get_rc_checks(expr):
            proof_lines.append(
                f"cases rc_h_{rc_check_name}' ({rc_check_offset}) "
                "(by norm_num1) with n hn, arith_simps at hn,"
            )

            # Only rewrites between pointer names (not memory assignments).
            rc_rw = list(filter(lambda x: "htv_" not in x, self.rc_rw))
            if expr == checked_expr:
                rc_rw.append(var_rw)
            rc_rw.reverse()
            proof_lines.append(
                f'use_only [n], {{ simp only [{", ".join(rc_rw)}], arith_simps, exact hn }},'
            )

        return proof_lines

    def add_rc_condition_proof(
        self,
        rewrites: List[str],
    ) -> List[str]:
        """
        If the Cairo function uses the range check pointer, this generates the range check condition
        of the function, that is, that m memory cells beginning with the input range check
        pointer are range checked.
        The lines generated by this proof should be added at the end of the main proof.
        """
        if not self.active():
            return []

        proof_lines = []
        proof_lines.append("-- range check condition")

        # add two zeros at the end of the sum because we want to apply first
        # range_checked_offset' and then range_checked_add_right to
        # the resulting range_checked expressions and this means that in
        # the last steps we need two extra zeros to ensure there is still
        # a sum where the lemmas expect it.
        m_expr = "+".join([s.step for s in self.steps[1:]] + ["0", "0"])
        proof_lines.append(f"use_only ({m_expr}), split,")
        # Proof that m <= k.
        proof_lines.append(f'linarith [{", ".join(self.bounds)}],')
        proof_lines.append("split,")
        # Proof that rc_out = rc_in + m.
        # First, rewrite with the return value and the last htv_
        # simplify and rewrite the return value for the rc pointer.

        # If there the return has asserts which copy the return values to
        # the end of the function stack, the assert for the rc pointer has
        # to be included in the rewrites. Since there may be no need to copy
        # some of the return values (including the range check pointer) we
        # do not know which rewrite to apply. Therefore, we apply them all
        # optionally.
        # An "hblk_" rewrite is similar to an "hret" rewrite but is used when
        # a sub-block sets the return arguments.
        ret_rw = list(filter(lambda x: x.startswith("hret") or x.startswith("hblk"), rewrites))

        proof_lines.append(
            "{ arith_simps,"
            + ("" if not ret_rw else f' try {{ simp only [{" ,".join(ret_rw)}] }},')
        )

        proof_lines += self.add_rc_rw_to_in("")

        first_rc_name = self.steps[0].get_name()
        proof_lines.append("  try { arith_simps, refl <|> norm_cast }, try { refl } },")
        proof_lines.append(
            f"intro rc_h_{first_rc_name}, repeat {{ rw [add_assoc] at rc_h_{first_rc_name} }},"
        )
        proof_lines.append(
            f"have rc_h_{first_rc_name}' := range_checked_add_right rc_h_{first_rc_name},"
        )

        return proof_lines
