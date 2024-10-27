import dataclasses
from typing import Dict, List, Optional, Tuple, Union

from starkware.cairo.lang.compiler.ast.cairo_types import CairoType, TypeFelt
from starkware.cairo.lang.compiler.ast.expr import Expression, ExprHint
from starkware.cairo.lang.compiler.instruction import Register
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.expr_to_lean import (
    LEAN_HINT_VAR_PREFIX,
    LeanDescContext,
    LeanExprSimplifier,
    get_ap_ref_offset,
    get_fp_ref_offset,
    get_reversed_add_exprs,
    is_ap_ref,
    rec_get_const_div_inv,
    to_lean_description_aux,
    to_lean_paren_description_aux,
)
from starkware.cairo.lean.verification.generate_rc import SoundnessRCSteps
from starkware.cairo.lean.verification.lean_assembly_info import LeanAssemblyInfo
from starkware.cairo.lean.verification.lean_file_names import (
    LeanFileNames,
    mk_lean_core_import_path,
    mk_lean_dependency_soundness_import_path,
    mk_lean_rel_import_path,
)
from starkware.cairo.lean.verification.lean_instruction_builder import (
    LeanCodeAssertEq,
    LeanCodeElement,
)
from starkware.cairo.lean.verification.lean_processed_info import (
    LeanBlockInfo,
    LeanFunctionInfo,
    LeanProgramInfo,
)
from starkware.cairo.lean.verification.lean_raw_info import (
    LeanPreprocessedAddAp,
    LeanPreprocessedAssertEq,
    LeanPreprocessedCodeElement,
    LeanPreprocessedCompoundAssertEq,
    LeanPreprocessedConst,
    LeanPreprocessedFuncCall,
    LeanPreprocessedIf,
    LeanPreprocessedJumpToLabelInstruction,
    LeanPreprocessedNop,
    LeanPreprocessedReference,
    LeanPreprocessedReturn,
    LeanPreprocessedTailCall,
    LeanPreprocessedTempVar,
    LeanPreprocessedTempVarAlloc,
    LeanPreprocessedWithAsserts,
)
from starkware.cairo.lean.verification.rebinding import (
    inc_name_sub,
    name_with_sub,
    next_name_with_sub,
)
from starkware.cairo.lean.verification.scope_to_lean import get_name_in_open_scopes
from starkware.cairo.lean.verification.type_to_lean import (
    create_arg_defs,
    get_lean_type,
    get_lean_type_cast,
)
from starkware.cairo.lean.verification.var_info import LeanMemVarInfo, LeanRefVarInfo, LeanVarInfo

LEAN_CODE_INDENT = 2


@dataclasses.dataclass
class LeanGenContext:
    """
    This class stores the context information for the automatic soundness
    theorem generation process.
    """

    func: LeanFunctionInfo
    lean_info: LeanProgramInfo
    assembly_info: LeanAssemblyInfo
    lean_code: List[LeanCodeElement]

    simplifier: LeanExprSimplifier

    lvars: Dict[int, str]

    # Start of block.
    start_lean_desc_num: int
    start_pc_offset: int

    # The following lists are inherited from the previous block and then extended
    # inside the block. They are used to generate the proof for this block. This means
    # that if the execution can arrive at this block from multiple previous
    # blocks, the following fields should be initialized by lists which are common
    # to all previous blocks. For 'rewrites', for example, we can use hin_args. Currently,
    # The beginning of the 'rewrites' list is the hin_args list. This is for the input
    # arguments to the function. This can be extended to apply per block.
    # Currently, the proof generation process can go through the same block several times
    # and re-initializes the lists below every time it goes through the block.
    rc_steps: Optional[SoundnessRCSteps] = None
    name_sub: Dict[str, int] = dataclasses.field(default_factory=lambda: {})
    rewrites: List[str] = dataclasses.field(default_factory=lambda: [])
    rewrite_types: Dict[str, Tuple[CairoType, str]] = dataclasses.field(default_factory=lambda: {})
    ap_rewrites: List[str] = dataclasses.field(default_factory=lambda: [])

    # Current processing position.

    lean_desc_num: int = 0
    lean_code_elt_num: int = 0
    pc_offset: int = 0

    # Context information for generating Lean expressions from Cairo expressions.
    desc_ctx: LeanDescContext = dataclasses.field(init=False)

    # The part of the proof constructed in the current block.
    prefix: str = ""
    statement: List[str] = dataclasses.field(default_factory=lambda: [])
    proof_intro: List[str] = dataclasses.field(default_factory=lambda: [])
    main_proof: List[str] = dataclasses.field(default_factory=lambda: [])
    final_proof: List[str] = dataclasses.field(default_factory=lambda: [])

    # The complete proof suffix beginning at this block and ending at a return.

    # The final proof parts constructed by previous blocks: since these belong
    # at the end, they have to be accumulated and added at the end of the proof.
    final_proof_prefix: List[List[str]] = dataclasses.field(default_factory=lambda: [])
    proof: List[str] = dataclasses.field(default_factory=lambda: [])

    def __post_init__(self):
        self.lean_desc_num = self.start_lean_desc_num
        self.pc_offset = self.start_pc_offset
        self.lean_code_elt_num = self.get_lean_code_elt_num_by_pc_offset(self.pc_offset)

        self.desc_ctx = LeanDescContext(
            simplifier=self.simplifier,
            cairo_type=None,
            struct_defs=self.func.struct_defs,
            identifiers=self.lean_info.identifiers,
            func_scope=self.func.func_scope,
            open_namespaces=self.func.open_namespaces,
            div_var_basename=self.div_var_basename,
            local_vars=self.lvars,
            name_sub=self.name_sub,
            prefix=self.prefix,
        )

        self.set_instr_context()

    @property
    def file_scope(self) -> ScopedName:
        """
        Returns the top namespace opened in the soundness file, which is the
        namespace corresponding to the cairo file in which the function is
        defines.
        """
        return self.func.func_scope[:-1]

    @property
    def block_info(self) -> LeanBlockInfo:
        if self.start_lean_desc_num not in self.func.block_list:
            raise Exception("No block info for context.")
        return self.func.block_list[self.start_lean_desc_num]

    @property
    def block_name_suffix(self) -> str:
        return mk_block_name_suffix(self)

    @property
    def auto_spec_name(self) -> str:
        """
        The name of the automatic specification as it should be referred to when generating
        the auto soundness proof, and, therefore, relative to the open namespaces.
        """
        return (
            mk_lean_auto_spec_name(
                self.func.name,
                self.lean_info.open_namespaces,
            )
            + self.block_name_suffix
        )

    @property
    def auto_soundness_theorem_name(self) -> str:
        """
        The name of the auto soundness theorem as it should be used when generating
        the theorem, and, therefore, relative to the namespace wherein this is generated.
        """
        return (
            mk_lean_auto_soundness_name(
                self.func.name,
                [self.func.func_scope[:-1]],
            )
            + self.block_name_suffix
        )

    @property
    def user_soundness_theorem_name(self) -> str:
        """
        The name of the user soundness theorem as it should be referred to when generating
        the auto soundness proof, and, therefore, relative to the open namespaces.
        """
        return mk_lean_user_soundness_name(self.func.name, self.lean_info.open_namespaces)

    @property
    def div_var_basename(self) -> str:
        return "δ{}_".format(self.pc_offset)

    @property
    def is_main_theorem(self) -> bool:
        return self.start_lean_desc_num == 0

    @property
    def at_return(self) -> bool:
        return isinstance(
            self.func.lean_desc[self.lean_desc_num], LeanPreprocessedReturn
        ) or isinstance(self.func.lean_desc[self.lean_desc_num], LeanPreprocessedTailCall)

    @property
    def has_independent_ap(self) -> bool:
        return not self.func.has_const_ap_offset and not self.is_main_theorem

    def indent(self):
        self.prefix += " " * LEAN_CODE_INDENT
        self.desc_ctx.prefix = self.prefix

    def outdent(self):
        self.prefix = self.prefix[:-LEAN_CODE_INDENT]
        self.desc_ctx.prefix = self.prefix

    def get_lean_code_elt_num_by_pc(self, pc):
        """
        Returns the lean code pc (relative to the current function) for
        the given lean instruction pc (relative to the full code).
        Can be used for jmp destination addresses, for example.
        """
        return self.assembly_info.pc_lookup[pc] - self.assembly_info.pc_lookup[self.func.start_pc]

    def get_lean_code_elt_num_by_pc_offset(self, pc_offset):
        """
        Returns the lean code pc (relative to the current function) for
        the given lean instruction pc (relative to the current function).
        Can be used for jmp destination addresses, for example.
        """
        return (
            self.assembly_info.pc_lookup[self.func.start_pc + pc_offset]
            - self.assembly_info.pc_lookup[self.func.start_pc]
        )

    def reset_pointers(self):
        self.lean_desc_num = self.start_lean_desc_num
        self.pc_offset = self.start_pc_offset
        self.lean_code_elt_num = self.get_lean_code_elt_num_by_pc_offset(self.pc_offset)
        self.set_instr_context()

    def skip_asserts(self) -> Tuple[int, int]:
        """
        Returns the pc offset and lean code position after skipping all asserts
        generated for the current instruction (under the assumption that the
        current pc offset and lean code position are at the beginning of the code
        for the current instruction).
        This does not change the pointer on the context object.
        """
        instr = self.func.lean_desc[self.lean_desc_num]
        if isinstance(instr, LeanPreprocessedAssertEq):
            return (
                self.pc_offset + len(self.lean_code[self.lean_code_elt_num].code),
                self.lean_code_elt_num + 1,
            )
        if isinstance(instr, LeanPreprocessedWithAsserts):
            pc_offset = self.pc_offset
            lean_code_elt_num = self.lean_code_elt_num
            for _ in instr.asserts:
                pc_offset += len(self.lean_code[lean_code_elt_num].code)
                lean_code_elt_num += 1
            return (pc_offset, lean_code_elt_num)

        return (self.pc_offset, self.lean_code_elt_num)

    def next_instr(self):
        """
        Advance the counters as a result of executing the current instruction.
        This should not be called for branching instructions (conditional
        jumps) and does not change the counters when called for such an instruction.
        This also does not advance the counters for a return, as a return
        terminates the processing of the function.
        """
        instr = self.func.lean_desc[self.lean_desc_num]
        # Conditional jumps and the return are not handled here.
        if (
            isinstance(instr, LeanPreprocessedIf)
            or (
                isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
                and instr.condition is not None
            )
            or isinstance(instr, LeanPreprocessedReturn)
        ):
            return

        if isinstance(instr, LeanPreprocessedNop) or isinstance(instr, LeanPreprocessedConst):
            self.lean_desc_num += 1
            self.set_instr_context()
            return

        if isinstance(instr, LeanPreprocessedJumpToLabelInstruction) and instr.condition is None:
            self.pc_offset += instr.offset
            self.lean_code_elt_num = self.get_lean_code_elt_num_by_pc(instr.pc_dest)
            self.lean_desc_num = self.func.label_dict[instr.label_name]
        elif isinstance(instr, LeanPreprocessedAddAp):
            self.pc_offset += 2
            self.lean_code_elt_num += 1
            self.lean_desc_num += 1
        elif isinstance(instr, LeanPreprocessedAssertEq) or isinstance(
            instr, LeanPreprocessedWithAsserts
        ):
            self.pc_offset, self.lean_code_elt_num = self.skip_asserts()
            self.lean_desc_num += 1
            if isinstance(instr, LeanPreprocessedFuncCall) or (
                isinstance(instr, LeanPreprocessedTempVar) and instr.add_ap_instr is not None
            ):
                # In addition to the asserts that prepare the instruction, we have an additional
                # instruction: the call instruction or the 'ap += c' allocating the temp var.
                self.pc_offset += len(self.lean_code[self.lean_code_elt_num].code)
                self.lean_code_elt_num += 1

        self.set_instr_context()

    def add_intro(self, line: str):
        self.proof_intro.append(self.prefix + line)

    def concat_intro(self, lines: List[str]):
        self.proof_intro += lines

    def add_main(self, line: str):
        self.main_proof.append(self.prefix + line)

    def concat_main(self, lines: List[str]):
        self.main_proof += lines

    def add_final(self, line: str):
        self.final_proof.append(line)

    def concat_final(self, lines: List[str]):
        self.final_proof += lines

    def reset_context(
        self,
        rc_steps: Optional[SoundnessRCSteps],
        name_sub: Dict[str, int],
        rewrites: List[str],
        rewrite_types: Dict[str, Tuple[CairoType, str]],
        ap_rewrites: List[str],
    ):
        """
        Resets the context, so that it can be used again. Resets the state pointers
        to the beginning of the block. Clears the proofs. Sets the rewrites and
        rc_steps to a copy of the values provided.
        """
        self.reset_pointers()

        self.rc_steps = rc_steps.branch() if rc_steps is not None else None
        self.name_sub = name_sub.copy()
        self.rewrites = rewrites.copy()
        self.rewrite_types = rewrite_types.copy()
        self.ap_rewrites = ap_rewrites.copy()

        self.statement = []
        self.proof_intro = []
        self.main_proof = []
        self.final_proof = []

        self.reset_desc_context()

    def reset_desc_context(self):
        self.desc_ctx.name_sub = self.name_sub
        self.desc_ctx.prefix = self.prefix

    def set_instr_context(self):
        """
        Set those parts of the context which depend on the current instruction.
        """
        self.set_instr_simplifier()
        self.set_instr_desc_ctx()

    def set_instr_simplifier(self):
        """
        Sets the simplifier to simplify expressions of the current instruction.
        """
        instr = self.func.lean_desc[self.lean_desc_num]
        self.simplifier.set_instr(instr)

    def set_instr_desc_ctx(self):
        """
        Set those parts of the description context that depend on the current
        instruction.
        """
        instr = self.func.lean_desc[self.lean_desc_num]
        self.desc_ctx.div_var_basename = self.div_var_basename
        self.desc_ctx.div_var_startnum = 0
        self.desc_ctx.hint_vars = (
            instr.get_hint_vars() if isinstance(instr, LeanPreprocessedWithAsserts) else []
        )
        self.desc_ctx.prefix = self.prefix


@dataclasses.dataclass
class LeanBranchCond:
    # A name indicating the type of the branch (such as "if" or "jnz", for example).
    # Currently this is only used to generate comments in the Lean code.
    name: str
    cond_var: str
    # The two expressions in the condition. If this is None, the condition
    # is [ap] != 0 or [ap] = 0.
    exprs: Optional[Tuple[str, str]]
    # Is the condition an equal or a not-equal. In the spec, the condition
    # (equal or not-equal as specified in the Cairo code) appears first and its negation appears
    # second. In the assembly code, the jump is always to the not-equal branch.
    is_eq: bool
    # Assert rewrites which apply to the condition.
    assert_rw: List[str]


@dataclasses.dataclass
class LeanSoundnessGen:

    func: LeanFunctionInfo
    lean_info: LeanProgramInfo
    assembly_info: LeanAssemblyInfo

    blocks_by_lean_desc_num: Dict[int, LeanGenContext] = dataclasses.field(
        default_factory=lambda: {}
    )

    def new_block_ctx(
        self, ctx: LeanGenContext, start_lean_desc_num: int, start_pc_offset: int
    ) -> LeanGenContext:
        """
        Generates a new context object which inherits the function's properties from
        the previous context and starts at the given position.
        """
        return LeanGenContext(
            # Fields that depend only on the function, not the block.
            func=ctx.func,
            lean_info=ctx.lean_info,
            assembly_info=ctx.assembly_info,
            lean_code=ctx.lean_code,
            simplifier=LeanExprSimplifier(ctx.lean_info.preprocessor),
            lvars=ctx.lvars,
            rc_steps=ctx.rc_steps.branch() if ctx.rc_steps is not None else None,
            # Start position.
            start_lean_desc_num=start_lean_desc_num,
            start_pc_offset=start_pc_offset,
            prefix=ctx.prefix,
        )

    def next_ctxs(
        self, ctx: LeanGenContext
    ) -> Tuple[Optional[LeanGenContext], Optional[LeanGenContext]]:
        """
        Returns the context to use after processing the current instruction.
        This may be the same context as the one for the current instruction
        (in which case the pointers on the context are advanced) or it may be one
        or two new contexts for the one block following the instruction or the two
        blocks following a branch instruction.
        If the processing reached a return, the pointers are not advanced and
        two Nones are returned.
        If the contexts already exist in the block table, they are returned
        and otherwise they are created and added to the block table.
        """
        if ctx.at_return:
            return (None, None)

        instr = ctx.func.lean_desc[ctx.lean_desc_num]

        if isinstance(instr, LeanPreprocessedIf) or (
            isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
            and instr.condition is not None
        ):
            jump_instr = instr.jump_instr if isinstance(instr, LeanPreprocessedIf) else instr
            assert jump_instr is not None, "If statement without a jump instruction."
            # Skip the asserts to the position of the conditional jump.
            pc_offset, _ = ctx.skip_asserts()

            if ctx.lean_desc_num + 1 in self.blocks_by_lean_desc_num:
                ctx_pos = self.blocks_by_lean_desc_num[ctx.lean_desc_num + 1]
            else:
                ctx_pos = self.new_block_ctx(ctx, ctx.lean_desc_num + 1, pc_offset + 2)
                self.blocks_by_lean_desc_num[ctx_pos.lean_desc_num] = ctx_pos

            if ctx.func.label_dict[jump_instr.label_name] in self.blocks_by_lean_desc_num:
                ctx_neg = self.blocks_by_lean_desc_num[ctx.func.label_dict[jump_instr.label_name]]
            else:
                ctx_neg = self.new_block_ctx(
                    ctx, ctx.func.label_dict[jump_instr.label_name], pc_offset + jump_instr.offset
                )
                self.blocks_by_lean_desc_num[ctx_neg.lean_desc_num] = ctx_neg

            return (ctx_pos, ctx_neg)

        if isinstance(instr, LeanPreprocessedJumpToLabelInstruction) and instr.condition is None:

            if self.func.label_dict[instr.label_name] in self.blocks_by_lean_desc_num:
                return (self.blocks_by_lean_desc_num[self.func.label_dict[instr.label_name]], None)

            ctx_jmp = self.new_block_ctx(
                ctx, self.func.label_dict[instr.label_name], ctx.pc_offset + instr.offset
            )
            self.blocks_by_lean_desc_num[ctx_jmp.lean_desc_num] = ctx_jmp

            return (ctx_jmp, None)

        # Non-branching instructions: advance the pointer.
        ctx.next_instr()
        if ctx.lean_desc_num in self.func.labels_by_lean_desc_num:
            # A labeled instruction: start new block.
            if ctx.lean_desc_num in self.blocks_by_lean_desc_num:
                return (self.blocks_by_lean_desc_num[ctx.lean_desc_num], None)

            ctx = self.new_block_ctx(ctx, ctx.lean_desc_num, ctx.pc_offset)
            self.blocks_by_lean_desc_num[ctx.lean_desc_num] = ctx
        return (ctx, None)

    def gen_blocks(self, ctx: Optional[LeanGenContext] = None):
        """
        Generates the context blocks beginning with the given context. If no
        context is given, generates the context blocks beginning at the beginning
        of the function.
        """
        if ctx is None:
            ctx = self.get_start_ctx()

        if ctx.func.has_loop:
            return

        if ctx.at_return:
            ctx.reset_pointers()
            return

        ctx_pos, ctx_neg = self.next_ctxs(ctx)
        if ctx_pos is not None:
            self.gen_blocks(ctx_pos)
        if ctx_neg is not None:
            self.gen_blocks(ctx_neg)

        if ctx_pos != ctx:
            ctx.reset_pointers()

    def get_start_ctx(self) -> LeanGenContext:
        """
        Generates the context which begins at the start of the function.
        """
        if 0 in self.blocks_by_lean_desc_num:
            return self.blocks_by_lean_desc_num[0]

        lean_start_pc = self.assembly_info.pc_lookup[self.func.start_pc]
        lean_end_pc = self.assembly_info.pc_lookup[self.func.end_pc]
        ctx = LeanGenContext(
            func=self.func,
            lean_info=self.lean_info,
            assembly_info=self.assembly_info,
            lean_code=self.assembly_info.lean_code[lean_start_pc:lean_end_pc],
            simplifier=LeanExprSimplifier(self.lean_info.preprocessor),
            lvars=self.func.local_var_names(),
            start_lean_desc_num=0,
            start_pc_offset=0,
            name_sub={name: 0 for name in self.func.arg_names},
            rc_steps=SoundnessRCSteps(rc_builtin=self.func.rc)
            if self.func.rc is not None
            else None,
            rewrites=["add_neg_eq_sub"],
        )

        self.blocks_by_lean_desc_num[0] = ctx
        return ctx

    def gen_func_proofs(self) -> List[str]:
        """
        Generates the proofs for the automatic specs of all blocks.
        """
        proof = []
        for join_point in sorted(self.func.join_points, reverse=True):
            if join_point not in self.blocks_by_lean_desc_num:
                raise Exception("No generation context for join point.")
            ctx = self.blocks_by_lean_desc_num[join_point]
            proof += self.gen_block_proof(ctx) + [""]

        proof += self.gen_block_proof(self.get_start_ctx())

        return proof

    def gen_block_proof(self, ctx: LeanGenContext) -> List[str]:
        """
        Generates the full proof for a single block. Such a proof is an
        independent lemma.
        """
        ctx.reset_context(
            rc_steps=SoundnessRCSteps(rc_builtin=self.func.rc)
            if self.func.rc is not None
            else None,
            name_sub={name: 0 for name in ctx.block_info.get_arg_names()},
            rewrites=["add_neg_eq_sub"] + get_block_hin_args(ctx),
            rewrite_types=get_block_hin_arg_types(ctx),
            ap_rewrites=[],
        )
        self.mk_auto_soundness_block_statement(ctx)
        ctx.indent()
        mk_auto_soundness_block_proof_intro(ctx)
        mk_auto_soundness_block_final_proof_intro(ctx)

        proof = self.gen_proof(ctx) if not ctx.func.has_loop else ["sorry"]
        return ctx.statement + ["begin"] + proof + ["end"]

    def gen_proof(self, ctx: LeanGenContext) -> List[str]:
        """
        Continue generating the proof at the block whose context is given.
        """
        ctx_pos, ctx_neg, cond = mk_auto_soundness_theorem_block(self, ctx)

        if ctx_pos is None:
            # Reached a return statement. Generate the final part of the proof.
            mk_auto_soundness_block_proof_finish(ctx)
            return (
                ctx.proof_intro + ctx.main_proof + [ctx.prefix + line for line in ctx.final_proof]
            )

        ctx_pos.reset_context(
            ctx.rc_steps, ctx.name_sub, ctx.rewrites, ctx.rewrite_types, ctx.ap_rewrites
        )
        ctx_pos.prefix = ctx.prefix
        ctx_pos.final_proof = ctx.final_proof.copy()

        if ctx_neg is not None:
            ctx_pos.indent()
        if cond is not None:
            mk_if_branch_intro(ctx=ctx_pos, cond=cond, is_pos=True)
        pos_proof = (
            mk_block_apply_proof(ctx, ctx_pos)
            if ctx_pos.start_lean_desc_num in ctx.func.join_points
            else self.gen_proof(ctx_pos)
        )

        if ctx_neg is None or ctx_neg == ctx:
            return ctx.proof_intro + ctx.main_proof + pos_proof

        ctx_neg.reset_context(
            ctx.rc_steps, ctx.name_sub, ctx.rewrites, ctx.rewrite_types, ctx.ap_rewrites
        )
        ctx_neg.prefix = ctx.prefix
        ctx_neg.final_proof = ctx.final_proof.copy()
        ctx_neg.indent()
        if cond is not None:
            mk_if_branch_intro(ctx=ctx_neg, cond=cond, is_pos=False)
        neg_proof = (
            mk_block_apply_proof(ctx, ctx_neg)
            if ctx_neg.start_lean_desc_num in ctx.func.join_points
            else self.gen_proof(ctx_neg)
        )
        return (
            ctx.proof_intro
            + ctx.main_proof
            + [ctx.prefix + "{"]
            + pos_proof
            + [ctx.prefix + "},"]
            + [ctx.prefix + "{"]
            + neg_proof
            + [ctx.prefix + "}"]
        )

    def gen_induction_hypothesis_arg(self) -> List[str]:
        """
        Generates the induction hypothesis argument, to be used when passing the
        induction hypothesis of a recursive function into a block.
        This is very similar to the main theorem statement.
        """
        # The induction hypothesis is based on the statement of the main theorem.
        ctx = self.get_start_ctx()
        lines = ["(νih : ∀ (σ : register_state F)"]
        lines += [
            "     " + line for line in self.gen_auto_soundness_block_statement_args(ctx, True)
        ]
        lines[-1] += ","
        lines += [
            "     " + line for line in self.gen_auto_soundness_block_statement_conclusion(ctx, True)
        ]
        lines[-1] += ")"

        return lines

    def mk_auto_soundness_block_statement(self, ctx: LeanGenContext):
        ctx.statement.append(f"theorem {ctx.auto_soundness_theorem_name}")

        # The arguments of the statement.
        ctx.statement += self.gen_auto_soundness_block_statement_args(ctx, False)

        # Conclusion.
        ctx.statement.append("    -- conclusion")
        ctx.statement += self.gen_auto_soundness_block_statement_conclusion(ctx, False)

    def gen_auto_soundness_block_statement_args(
        self, ctx: LeanGenContext, is_induction_hypothesis: bool
    ) -> List[str]:
        """
        Generates the arguments of the statement. This can also generate a version of
        the arguments used in the induction hypothesis (when the function is recursive).
        """
        lines = []

        # Do we need an independent ap variable?
        if ctx.has_independent_ap and not is_induction_hypothesis:
            lines.append("    -- An independent ap variable.")
            lines.append("    (ap : F)")
        # Function arguments.
        arg_defs = get_soundness_func_block_arg_defs(ctx)
        if arg_defs:
            if not is_induction_hypothesis:
                lines.append("    -- arguments")
            lines.append("    " + " ".join(arg_defs))
        # Code in memory.
        if not is_induction_hypothesis:
            lines.append("    -- code is in memory at σ.pc")
        lines.append(
            "    (h_mem : mem_at mem {} σ.pc)".format(
                mk_lean_code_def_name(ctx.func.name, ctx.lean_info.open_namespaces)
            )
        )
        # Code of dependencies in memory.
        if len(ctx.func.call_dependencies) != 0:
            if not is_induction_hypothesis:
                lines.append("    -- all dependencies are in memory")
            for dep_name, dep_offset in get_dependencies(ctx):
                d_code_name = mk_lean_code_def_name(dep_name, ctx.lean_info.open_namespaces)
                d_id = ctx.lean_info.function_dict[dep_name].id
                d_start_pc = ctx.func.start_pc - dep_offset
                offset_str = f" - {d_start_pc}" if 0 <= d_start_pc else f" + {-d_start_pc}"
                lines.append(
                    "    (h_mem_{} : mem_at mem {} (σ.pc {}))".format(d_id, d_code_name, offset_str)
                )

        # Input arguments offsets.
        if not is_induction_hypothesis:
            lines.append("    -- input arguments on the stack")
        for name, var_info in ctx.block_info.arg_info.items():
            cast_sep = " " if var_info.cast else ""
            lines.append(
                f"    (hin_{name} : {name} = "
                f"{var_info.cast}{cast_sep}{mk_hin_arg_expr(ctx, var_info)})"
            )
        if not ctx.is_main_theorem:
            lines.append("    (νbound : ℕ)")
            if ctx.func.is_recursive:
                lines += ["    " + line for line in self.gen_induction_hypothesis_arg()]

        return lines

    def gen_auto_soundness_block_statement_conclusion(
        self, ctx: LeanGenContext, is_induction_hypothesis: bool
    ) -> List[str]:
        """
        Generates the conclusion of the statement. This can also generate a version of
        the conclusion used in the induction hypothesis (when the function is recursive).
        """
        lines = []

        has_const_ap_offset = ctx.func.has_const_ap_offset
        ap_offset = ctx.block_info.flow_at_start.ap_tracking.offset

        args = " ".join(ctx.block_info.get_arg_names())
        ret_offsets_etc = get_auto_soundness_ret_types_offsets_and_casts(
            ctx.func, ctx.lean_info, " "
        )
        ret_vals = [f"({cast}mem (τ.ap - {-offset}))" for _, offset, cast in ret_offsets_etc]
        full_args = (" " + args if args else "") + (" " + " ".join(ret_vals) if ret_vals else "")

        spec_name = (
            mk_lean_user_spec_name(ctx.func.name, ctx.lean_info.open_namespaces)
            if ctx.is_main_theorem
            else ctx.auto_spec_name
        )

        f_props = (
            "τ.ap = σ.ap + {} ∧".format(ctx.func.get_total_ap_offset())
            if has_const_ap_offset
            else ""
        )

        if ctx.is_main_theorem:
            if not is_induction_hypothesis:
                lines.append("  : ensures_ret mem σ (λ κ τ,")
            else:
                lines.append("    ensuresb_ret νbound mem σ (λ κ τ,")
        else:
            lines.append("  : ensuresb_ret νbound mem")
            start_ap = (
                "ap"
                if ctx.has_independent_ap
                else "σ.ap" + (f" + {ap_offset}" if ap_offset else "")
            )
            lines.append(
                f"    {{pc := σ.pc + {ctx.start_pc_offset}, ap := {start_ap}, fp := σ.fp}}"
            )
            lines.append("    (λ κ τ,")

        if f_props:
            if ctx.func.has_range_check():
                lines.append("      " + f_props.strip())
            else:
                lines[-1] += " " + f_props

        end_op = "" if is_induction_hypothesis else " :="

        if ctx.func.rc is not None:
            rc_var_info = ctx.block_info.get_arg_info_by_name(ctx.func.rc.arg_name)
            if (
                rc_var_info is None
                or not isinstance(rc_var_info, LeanMemVarInfo)
                or rc_var_info.offset is None
            ):
                raise Exception("Failed to find rc variable offset in block variables.")
            _, rc_ret_offset, _ = ret_offsets_etc[ctx.func.rc.arg_index]
            lines.append(
                "      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ "
                f"({mk_hin_arg_expr(ctx, rc_var_info)}) (mem $ τ.ap - {-rc_ret_offset})",
            )
            lines.append(f"        ({spec_name} mem κ{full_args})){end_op}")
        else:
            lines[-1] += f" {spec_name} mem κ{full_args}){end_op}"

        return lines


def get_dependencies(ctx: LeanGenContext) -> List[Tuple[str, int]]:
    """
    Returns the list of dependencies of the function. Each dependency is
    described by a tuple <name, pc offset>. The list is sorted by the pc offset.
    """
    return sorted(
        [
            (dep_name, ctx.lean_info.function_dict[dep_name].start_pc)
            for dep_name in ctx.func.call_dependencies
        ],
        key=lambda p: p[1],
    )


def get_dep_args(ctx: LeanGenContext) -> List[str]:
    """
    Returns the sorted list of dependency arguments.
    """
    return [
        f"h_mem_{ctx.lean_info.function_dict[dep_name].id}" for dep_name, _ in get_dependencies(ctx)
    ]


def get_hin_args(ctx: LeanGenContext) -> List[str]:
    offsets_etc = get_auto_soundness_arg_types_offsets_and_casts(ctx.func, ctx.lean_info, "")
    return [f"hin_{name}" for name, _ in offsets_etc.items()]


def get_block_hin_args(ctx: LeanGenContext) -> List[str]:
    return [f"hin_{name}" for name in ctx.block_info.arg_info]


def get_hin_arg_types(ctx: LeanGenContext) -> Dict[str, Tuple[CairoType, str]]:
    """
    The type and cast for the input arguments which are not of type F.
    """
    types = {}
    offsets_etc = get_auto_soundness_arg_types_offsets_and_casts(ctx.func, ctx.lean_info, "")
    for name, (arg_type, _, cast) in offsets_etc.items():
        if not isinstance(arg_type, TypeFelt):
            types[f"hin_{name}"] = (arg_type, cast)
    return types


def get_block_hin_arg_types(ctx: LeanGenContext) -> Dict[str, Tuple[CairoType, str]]:
    """
    The type and cast for the block input arguments which are not of type F.
    """

    types = {}
    for name, var_info in ctx.block_info.arg_info.items():
        if not isinstance(var_info.cairo_type, TypeFelt):
            types[f"hin_{name}"] = (var_info.cairo_type, var_info.cast)
    return types


def mk_hin_arg_expr(ctx: LeanGenContext, var_info: LeanVarInfo) -> str:
    """
    Returns the Lean expression defining an input variable in terms of offsets
    from the register pointers (fp and ap).
    """
    if isinstance(var_info, LeanMemVarInfo):
        reg_str = (
            "σ.fp"
            if var_info.reg == Register.FP
            else ("σ.ap" if ctx.func.has_const_ap_offset else "ap")
        )
        offset = var_info.offset
        if var_info.reg == Register.AP and ctx.func.has_const_ap_offset:
            offset += ctx.block_info.flow_at_start.ap_tracking.offset
        return (
            f"mem {reg_str}"
            if offset == 0
            else (f"mem ({reg_str} - {-offset})" if offset < 0 else f"mem ({reg_str} + {offset})")
        )
    if isinstance(var_info, LeanRefVarInfo):
        return "({})".format(
            var_info.lean_expr
            if ctx.func.has_const_ap_offset
            else var_info.lean_expr.replace("σ.ap", "ap")
        )

    raise Exception("Verification block: unsupported variable type.")


def mk_auto_soundness_block_proof_intro(ctx: LeanGenContext):
    """
    Generates the first part of the soundness proof, which is still independent
    of the instructions of the function, but depends on the inputs and on
    general properties of the function (for example, whether it is recursive).
    """
    if ctx.is_main_theorem:
        ctx.add_intro("apply ensures_of_ensuresb, intro νbound,")
    if ctx.func.is_recursive and ctx.is_main_theorem:
        # Assume inductively that the theorem spec holds for shorter execution traces.
        theorem_arglist = " ".join(
            ["σ"] + ctx.func.arg_names + ["h_mem"] + get_dep_args(ctx) + get_hin_args(ctx)
        )
        ctx.add_intro("revert " + theorem_arglist + ",")
        ctx.add_intro("induction νbound with νbound νih,")
        ctx.add_intro("{ intros, intros n nlt, apply absurd nlt (nat.not_lt_zero _) },")
        ctx.add_intro("intros " + theorem_arglist + ",")
        ctx.add_intro("dsimp at νih,")

    ctx.add_intro("have h_mem_rec := h_mem,")

    # Unpack the memory.
    code_length = ctx.func.end_pc - ctx.func.start_pc
    pc_hyps = map(lambda i: "hpc" + str(i), range(code_length))
    ctx.add_intro(
        "unpack_memory {} at h_mem with ⟨{}⟩,".format(
            mk_lean_code_def_name(ctx.func.name, ctx.lean_info.open_namespaces), ", ".join(pc_hyps)
        )
    )


# Names for definitions and theorems.


def mk_lean_code_def_name(fn_name: str, namespaces: List[ScopedName]):
    prefix = "code_"
    return get_name_in_open_scopes(ScopedName.from_string(fn_name), namespaces, prefix)


def mk_lean_auto_spec_name(fn_name: str, namespaces: List[ScopedName]):
    prefix = "auto_spec_"
    return get_name_in_open_scopes(ScopedName.from_string(fn_name), namespaces, prefix)


def mk_lean_user_spec_name(fn_name: str, namespaces: List[ScopedName]):
    prefix = "spec_"
    return get_name_in_open_scopes(ScopedName.from_string(fn_name), namespaces, prefix)


def mk_lean_user_soundness_name(fn_name: str, namespaces: List[ScopedName]):
    prefix = "sound_"
    return get_name_in_open_scopes(ScopedName.from_string(fn_name), namespaces, prefix)


def mk_lean_auto_soundness_name(fn_name: str, namespaces: List[ScopedName]):
    prefix = "auto_sound_"
    return get_name_in_open_scopes(ScopedName.from_string(fn_name), namespaces, prefix)


def mk_block_name_suffix(ctx: LeanGenContext) -> str:
    return f"_block{ctx.start_lean_desc_num}" if not ctx.is_main_theorem else ""


@dataclasses.dataclass
class LeanExprSimps:
    """
    An auxiliary class to store rewrites which are needed as a result of transformations
    applied to expressions by the compiler's simplifier.
    """

    # Rewrites needed for division by a constant.
    const_div_rw: List[str] = dataclasses.field(default_factory=lambda: [])
    # Rewrites for x + y -> y + x (when x is a constant)
    add_comm: List[str] = dataclasses.field(default_factory=lambda: [])

    def is_empty(self) -> bool:
        return len(self.const_div_rw) == 0 and len(self.add_comm) == 0


# The procedures that do all the real work.

# Code definition.


def mk_lean_function_code_def(func_name: str, main_scope: ScopedName, code: List[str], out):
    print(
        "def {} : list F := [".format(mk_lean_code_def_name(func_name, [main_scope])),
        file=out,
    )
    print("  " + ",\n  ".join(code), file=out)
    print("]", file=out)


def add_proof_line(proof: List[str], prefix: str, line: str):
    proof.append(prefix + line)


def gen_implicit_args(func: LeanFunctionInfo, num_expl_args: int, name_sub: Dict[str, int]) -> str:
    implicit_args = " ".join(
        ["{}".format(name_with_sub(a, name_sub)) for a in func.arg_names[: func.num_implicit_args]]
    )
    if func.num_implicit_args > 0 and num_expl_args > 0:
        implicit_args += " "
    return implicit_args


def create_local(
    ctx: LeanGenContext, instr: LeanPreprocessedReference
) -> Tuple[str, CairoType, str]:
    name = inc_name_sub(instr.identifier.identifier.name, ctx.name_sub)
    cast = get_lean_type_cast(
        instr.resolved_type, ctx.func.func_scope, ctx.func.open_namespaces, ""
    )
    offset = get_fp_ref_offset(instr.expr)

    if offset == 0:
        ctx.add_main(
            "generalize' lc_{}_rev: {}mem σ.fp = {},".format(name, cast + " " if cast else "", name)
        )
    else:
        ctx.add_main(
            "generalize' lc_{}_rev: {}mem (σ.fp + {}) = {},".format(
                name, cast + " " if cast else "", offset, name
            ),
        )
    ctx.add_main(f"have lc_{name} := lc_{name}_rev.symm, clear lc_{name}_rev,")
    ctx.add_final(f"use_only [{name}],")
    return (f"lc_{name}", instr.resolved_type, cast)


def copy_local(
    ctx: LeanGenContext, instr: LeanPreprocessedReference, cp_rewrites: List[str]
) -> Tuple[str, CairoType, str]:

    # The local variable was already declared, so we do not need to advance the subscript.
    name = name_with_sub(instr.identifier.identifier.name, ctx.name_sub)
    cast = get_lean_type_cast(
        instr.resolved_type, ctx.func.func_scope, ctx.func.open_namespaces, ""
    )
    offset = get_fp_ref_offset(instr.expr)

    # The local variable was already declared, here we only copy its value.
    if offset == 0:
        ctx.add_main(
            "have lc_{}: {} = {}mem σ.fp, {{".format(name, name, cast + " " if cast else "")
        )
    else:
        ctx.add_main(
            "have lc_{}: {} = {}mem (σ.fp + {}), {{".format(
                name, name, cast + " " if cast else "", offset
            )
        )

    assert_simp = gen_assert_simp(
        ctx=ctx,
        var_rw=[f"htv_{name}"],
        assert_rw=cp_rewrites,
        is_struct=not isinstance(instr.resolved_type, TypeFelt),
    )
    assert_simp[-1] += " },"
    ctx.indent()
    for line in assert_simp:
        ctx.add_main(line)
    ctx.outdent()
    ctx.add_main("clear {},".format(" ".join(cp_rewrites)))

    return (f"lc_{name}", instr.resolved_type, cast)


def create_var(
    ctx: LeanGenContext, instr: Union[LeanPreprocessedReference, LeanPreprocessedTempVar]
) -> Tuple[str, CairoType, str]:
    base_name = instr.identifier.identifier.name
    lean_type = get_lean_type(
        instr.resolved_type, ctx.func.func_scope, ctx.lean_info.open_namespaces
    )
    cast = get_lean_type_cast(
        instr.resolved_type, ctx.func.func_scope, ctx.func.open_namespaces, ""
    )
    # Use the next name, but do not advance the subscript in 'name_sub' yet.
    name = next_name_with_sub(base_name, ctx.name_sub)
    ctx.desc_ctx.cairo_type = instr.resolved_type
    lean_expr, ctx.desc_ctx.div_var_startnum = to_lean_description_aux(
        expr=instr.expr,
        context=ctx.desc_ctx,
    )
    div_var_names = [
        ctx.div_var_basename + str(div_num) for div_num in range(ctx.desc_ctx.div_var_startnum)
    ]
    ctx.add_main(f"generalize' hl_rev_{name}: ({lean_expr} : {lean_type}) = {name},")
    ctx.add_main(f"have hl_{name} := hl_rev_{name}.symm, clear hl_rev_{name},")

    var_rw = f"hl_{name}"
    # if this variable assignment advances the rc pointer, store this step and
    # add the relevant lines to the final proof.
    if ctx.rc_steps is not None:
        ctx.concat_final(
            ctx.rc_steps.add_rc_var_step(
                base_name, instr.expr, isinstance(instr, LeanPreprocessedTempVar), ctx.name_sub
            )
        )
    if div_var_names:
        ctx.add_final("use_only [{}],".format(", ".join(div_var_names)))
    ctx.add_final("use_only [{}, hl_{}],".format(name, name))
    inc_name_sub(base_name, ctx.name_sub)
    return (var_rw, instr.resolved_type, cast)


def is_alloc_tempvar(instr: LeanPreprocessedCodeElement) -> bool:
    """
    Checks whether this is as a special case of a tempvar definition, without initial
    assignment of value:

    tempvar x

    The only thing the assembly code does here is advance the ap to allocate
    the memory for this variable.
    """
    if not isinstance(instr, LeanPreprocessedTempVar):
        return False
    return instr.add_ap_instr is not None and len(instr.asserts) == 0


def alloc_var(
    ctx: LeanGenContext,
    instr: Union[LeanPreprocessedTempVarAlloc, LeanPreprocessedReference],
) -> Tuple[str, CairoType, str]:
    """
    To be called when a tempvar is created but not assigned a value or when a references
    is initialized to an offset from the ap (such as let a = [ap + 3]). This 'allocates'
    the variable by defining it as an offset from the current ap (for a tempvar this offset is 0).
    The variable is not assigned any value.
    """
    name_prefix = LEAN_HINT_VAR_PREFIX if isinstance(instr.expr, ExprHint) else ""
    base_name = name_prefix + instr.identifier.identifier.name
    offset = get_ap_ref_offset(instr.expr) if isinstance(instr, LeanPreprocessedReference) else 0
    if offset is None:
        raise Exception("Unexpected expression when allocating ap variable.")
    # Use the next name, advancing the subscript.
    name = inc_name_sub(base_name, ctx.name_sub)
    cast = get_lean_type_cast(
        instr.resolved_type, ctx.func.func_scope, ctx.lean_info.open_namespaces, ""
    )
    ctx.add_main("apply of_register_state,")
    ctx.add_main(f"intros regstate_{name} regstateeq_{name},")
    ctx.add_main(
        "generalize' hl_rev_{}: {}mem {}regstate_{}.ap{} = {},".format(
            name,
            cast + " " if cast else "",
            "(" if offset != 0 else "",
            name,
            " + " + str(offset) + ")" if offset != 0 else "",
            name,
        ),
    )
    ctx.add_main(f"have hl_{name} := hl_rev_{name}.symm,")
    ctx.add_main(f"rw [regstateeq_{name}] at hl_{name}, try {{ dsimp at hl_{name} }},")

    var_rw = f"hl_{name}"
    ctx.add_final(f"use_only [{name}],")
    return (var_rw, instr.resolved_type, cast)


def need_ret_var(
    ctx: LeanGenContext,
    ret_var_base: str,
    is_tail_call: bool,
) -> bool:
    """
    Returns true if there is need to create a variable for the given return
    argument. Currently, this is always required if the function call is not
    a tail call. When the call is a tail call, this is only required for
    the range check argument (if any).
    """
    return not is_tail_call or (
        ctx.rc_steps is not None
        and ctx.rc_steps.is_rc_ret_var(next_name_with_sub(ret_var_base, ctx.name_sub))
    )


def create_ret_var(
    ctx: LeanGenContext,
    offset: int,
    cast: str,
    ret_var_base: str,
    is_explicit: bool,
    is_tail_call: bool,
    pc_offset: int,
) -> str:
    ret_var = inc_name_sub(ret_var_base, ctx.name_sub)
    ctx.add_main(
        "generalize' hr_rev_{}: {}mem (ap{} - {}) = {},".format(
            ret_var, cast + " " if cast else "", pc_offset, -offset, ret_var
        ),
    )
    if is_explicit:
        ctx.add_main(f"simp only [hr_rev_{ret_var}] at h_call{pc_offset},")
    ctx.add_main(f"have htv_{ret_var} := hr_rev_{ret_var}.symm, clear hr_rev_{ret_var},")
    if ctx.rc_steps is not None:
        ctx.rc_steps.add_rc_ret_var(ret_var, f"htv_{ret_var}")
    if not is_tail_call:
        ctx.add_final(f"use_only [{ret_var}],")

    return f"htv_{ret_var}"


def get_casts_for_rewrites(
    func: LeanFunctionInfo,
    rewrites: List[str],
    rewrite_types: Dict[str, Tuple[CairoType, str]],
) -> List[str]:
    """
    Retruns the list of casts which have to be simplified after rewriting with
    the given rewrites.
    """
    types = [
        rw_type for rw, (rw_type, cast) in rewrite_types.items() if rw in rewrites and 0 < len(cast)
    ]
    return func.struct_defs.get_lean_type_cast_rec(
        scope=func.func_scope, cairo_types=types, open_namespaces=func.open_namespaces
    )


def get_offsets_for_rewrites(
    func: LeanFunctionInfo, rewrites: List[str], rewrite_types: Dict[str, Tuple[CairoType, str]]
) -> List[str]:
    """
    Retruns the list of offset definitions which have to be simplified after rewriting
    with the given rewrites.
    """
    rw_simp_offsets = []
    for rw in rewrites:
        if not rw in rewrite_types:
            continue  # Simple F type.
        rw_type, _ = rewrite_types[rw]
        rw_offsets = func.struct_defs.get_struct_offset_def_names(rw_type, func.open_namespaces)
        for rw_offset in rw_offsets:
            if not rw_offset in rw_simp_offsets:
                rw_simp_offsets.append(rw_offset)
    return rw_simp_offsets


def add_additional_type_casts(
    func: LeanFunctionInfo,
    rw_casts: List[str],
    additional_types: List[CairoType],
) -> List[str]:
    """
    Adds the casts for the types in additional_types to the casts already in rw_casts.
    """
    additional_casts = func.struct_defs.get_lean_type_cast_rec(
        scope=func.func_scope, cairo_types=additional_types, open_namespaces=func.open_namespaces
    )
    for cast in additional_casts:
        if cast not in rw_casts:
            rw_casts.append(cast)

    return rw_casts


def add_additional_member_offsets(
    func: LeanFunctionInfo, mem_offsets: List[str], additional_types: List[CairoType]
) -> List[str]:
    """
    Adds to mem_offsets the offsets of the members of the types in additional_types,
    if they are structure types.
    """
    for cairo_type in additional_types:
        offsets = func.struct_defs.get_struct_offset_def_names(cairo_type, func.open_namespaces)
        for offset in offsets:
            if not offset in mem_offsets:
                mem_offsets.append(offset)
    return mem_offsets


# Code generation for the automatic soundness proof blocks.


def gen_assert_simp(
    ctx: LeanGenContext,
    var_rw: List[str],
    assert_rw: List[str],
    is_struct: bool,
    additional_types: List[CairoType] = [],
) -> List[str]:
    """
    Generates the Lean code to simplify an assert. Variations of this
    code can also be used to handle the copying of the arguments of a function
    before calling it and the copying of the return values before returning them.
    """
    rw_casts = get_casts_for_rewrites(ctx.func, var_rw, ctx.rewrite_types)
    add_additional_type_casts(ctx.func, rw_casts, additional_types)

    lines: List[str] = ["try { ext } ; {"] if is_struct else []
    prefix = "  " if is_struct else ""

    lines.append(prefix + f'try {{ simp only [{", ".join(var_rw)}] }},')
    if rw_casts:
        lines.append(prefix + f'try {{ dsimp [{", ".join(rw_casts)}] }},')
    if assert_rw:
        lines.append(
            prefix + f'try {{ arith_simps }}, try {{ simp only [{", ".join(assert_rw)}] }},'
        )
    if ctx.ap_rewrites:
        lines.append(prefix + f'try {{ simp only [{", ".join(ctx.ap_rewrites)}] }},')
    lines.append(
        prefix
        + "try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },"
    )
    if is_struct:
        lines[-1] += "},"

    return lines


def gen_tempvar_assignment(
    ctx: LeanGenContext,
    var_size: int,
    var_rw: str,
    assert_rw: List[str],
    expr_simps: LeanExprSimps,
) -> List[str]:

    lines: List[str] = []
    mem_rws = assert_rw[-var_size:]
    other_assert_rw = assert_rw[:-var_size]

    if 1 < var_size:
        lines.append("ext,")
    for mem_pos in range(var_size):
        lines += gen_tempvar_mem_assignment(
            ctx=ctx,
            var_size=var_size,
            var_rw=var_rw,
            mem_rw=mem_rws[mem_pos],
            assert_rw=other_assert_rw,
            expr_simps=expr_simps,
        )
    if 1 < var_size:
        lines[-1] += " },"

    return lines


def gen_tempvar_mem_assignment(
    ctx: LeanGenContext,
    var_size: int,
    var_rw: str,
    mem_rw: str,
    assert_rw: List[str],
    expr_simps: LeanExprSimps,
) -> List[str]:
    """
    This function generates the proof for a single memory assignment in the assignment
    of a tempvar. When the tempvar is a structure or a tuple, this will be called multiple
    times, once for each field (including fields of sub-structures).
    mem_rw should be the final assert that places the value in the memory.
    """
    lines: List[str] = []
    lines.append(
        "{}apply eq.symm, apply eq.trans {},".format(
            "{ try { arith_simps }, " if var_size > 1 else "", mem_rw
        )
    )
    lines += gen_expr_simps(simps=expr_simps, at_var=var_rw, indent=LEAN_CODE_INDENT)
    # Always called with is_struct False, as this is called once for every field in a structure.
    assert_simp = gen_assert_simp(
        ctx=ctx, var_rw=ctx.rewrites + [var_rw], assert_rw=assert_rw, is_struct=False
    )
    assert_simp[-1] += " },"
    for line in assert_simp:
        lines.append("  " + line)

    return lines


def add_rc_call_arg_var(ctx: LeanGenContext, called_func: LeanFunctionInfo) -> bool:
    """
    Checks whether the called function has a range check pointer argument. If yes,
    and if the last range check pointer before the call was not assigned a memory cell
    (that is, it was created by a 'let') then such a cell is now assigned to it
    by the function call. We here add an 'htv_*' rewrite for it, which binds
    a range check pointer name to a reference on the stack.
    """
    if ctx.rc_steps is None or called_func.rc is None:
        return False

    proof_lines = ctx.rc_steps.add_rc_call_arg_var(called_func.rc)
    if len(proof_lines) == 0:
        return False

    for line in proof_lines:
        ctx.add_main(line)
    ctx.rewrites.append(ctx.rc_steps.rc_rw[-1])
    return True


def add_called_func_rc(
    ctx: LeanGenContext,
    called_func: LeanFunctionInfo,
    ap_rw: str,
    pc_offset: int,
):
    """
    If a called function uses the range check built-in, we here add to
    the calling function's proof the elements which allow the proof
    to connect the range check properties of the calling and called function.
    """
    if ctx.rc_steps is None:
        return

    proof_lines = ctx.rc_steps.add_called_func_step(called_func.rc, ap_rw, pc_offset)
    if len(proof_lines) == 0:
        return

    for line in proof_lines:
        ctx.add_main(line)

def add_block_rc(
    ctx: LeanGenContext,
):
    """
    If a called function uses the range check built-in, we here add to
    the calling function's proof the elements which allow the proof
    to connect the range check properties of the calling and called function.
    """
    if ctx.rc_steps is None:
        return

    proof_lines = ctx.rc_steps.add_block_step(
        called_rc_builtin=ctx.func.rc,
        block_suffix=ctx.block_name_suffix,
        ap_rewrites=ctx.ap_rewrites,
    )
    if len(proof_lines) == 0:
        return

    for line in proof_lines:
        ctx.add_main(line)

    ctx.rewrites.append(ctx.rc_steps.rc_rw[-1])


def add_rw_call_range_check(
    ctx: LeanGenContext,
    called_func: LeanFunctionInfo,
    pc_offset: int,
    added_rc_call_arg_var: bool,
    arg_rw: List[str],
):
    """
    This function adds the rewrites that convert the range check step and
    range check hypothesis of the called function into the variables and
    memory references of the calling function.
    """
    if ctx.rc_steps is None:
        return

    proof_lines = ctx.rc_steps.add_rw_call_range_check(
        called_func.rc, pc_offset, added_rc_call_arg_var, arg_rw
    )
    # The list of proof lines is empty if the called function has no rc.
    for line in proof_lines:
        ctx.add_main(line)


def add_sub_call_rc_final(
    ctx: LeanGenContext,
    called_func: LeanFunctionInfo,
    pc_offset: int,
    is_tail_call: bool,
):
    """
    Generates the rc part of the final proof for handling the rc of a called function.
    """
    if ctx.rc_steps is not None:
        ctx.concat_final(
            ctx.rc_steps.add_sub_call_rc_final(called_func.rc, pc_offset, is_tail_call)
        )


def add_assert_range_checked(
    ctx: LeanGenContext,
    lhs: Expression,
    rhs: Expression,
    assert_rw: str,
):
    """
    When called on an assert which asserts the range checked property
    (that is, something like 'assert a = [range_check_ptr + 2]') this function
    adds the proof lines which prove the range checked property.
    Should be called on every assert.
    """
    if ctx.rc_steps is not None:
        ctx.concat_final(ctx.rc_steps.add_assert_range_checked(lhs, rhs, assert_rw))


def add_var_range_checked(ctx: LeanGenContext, expr: Expression, var_rw: str):
    """
    When called on a variable assignment which implies the range checked property
    (that is, something like 'let a = [range_check_ptr + 2]') this function
    adds the proof lines which prove the range checked property.
    Should be called on every variable assignment.
    """
    if ctx.rc_steps is not None:
        ctx.concat_final(ctx.rc_steps.add_var_range_checked(expr, var_rw))


def add_rc_condition_proof(ctx: LeanGenContext):
    """
    If the Cairo function uses the range check pointer, this generates
    the range check condition of the function, that is,
    that m memory cells beginning with the input range check pointer are range checked.
    This should be called at the end of the main proof.
    """
    if ctx.rc_steps is not None:
        for line in ctx.rc_steps.add_rc_condition_proof(ctx.rewrites):
            ctx.add_main(line)


def prepare_expr_simps(
    simps: LeanExprSimps,
    ctx: LeanGenContext,
    expr: Expression,
    div_to_field: bool,  # If division, is the constant in the division in the Field or in ℤ?
):
    simps.const_div_rw += prepare_const_divs(ctx=ctx, expr=expr, to_field=div_to_field)
    simps.add_comm += add_comm_rewrites(ctx=ctx, expr=expr)


def apply_expr_simps(simps: LeanExprSimps, ctx: LeanGenContext):
    for line in gen_expr_simps(simps):
        ctx.add_main(line)


def gen_expr_simps(
    simps: LeanExprSimps, at_var: Optional[str] = None, indent: int = 0
) -> List[str]:
    lines = []
    simp_at = f" at {at_var}" if at_var is not None else ""
    if 0 < len(simps.const_div_rw):
        lines.append(
            " " * indent + f'try {{ simp only [{", ".join(simps.const_div_rw)}]{simp_at} }},'
        )
    if 0 < len(simps.add_comm):
        lines.append(" " * indent + f'try {{ simp only [{", ".join(simps.add_comm)}]{simp_at} }},')

    return lines


def prepare_const_divs(
    ctx: LeanGenContext,
    expr: Expression,
    to_field: bool,  # Is the constant in the division in the Field or in ℤ?
) -> List[str]:
    """
    If the given expression contains division(s) by a constant, this function
    adds to the main proof the hypotheses needed to handle these constant divisions.
    The function returns the names of these hypotheses.
    """
    hyp_basename = "h_" + ctx.div_var_basename + "c"
    const_div_rw = []
    for index, (const_expr, div_const, is_full_expr) in enumerate(
        rec_get_const_div_inv(expr, ctx.desc_ctx)
    ):
        hyp_name = f"{hyp_basename}{index}"
        if is_full_expr:
            ctx.add_main(f"have {hyp_name} : ({const_expr} : F) = ({div_const} : ℤ),")
            ctx.add_main("{ apply PRIME.div_eq_const,")
            ctx.indent()
            ctx.add_main(
                "{ apply PRIME.cast_ne_zero, norm_num1, rw [PRIME], "
                + "try { simp_int_casts }, norm_num1 },"
            )
            simp_consts = ["PRIME"]
            ctx.add_main(f'rw [{", ".join(simp_consts)}], try {{ simp_int_casts }}, norm_num1 }},')
            ctx.outdent()
        else:
            f_to_z_name = hyp_name + "_fz"
            if to_field:
                const_div_rw.append(f_to_z_name)
            ctx.add_main(
                f"have {hyp_name} : ∀ x : F, x / ({const_expr} : ℤ) = x * ({div_const} : ℤ),"
            )
            ctx.add_main(
                "{ intro x,  apply div_eq_mul_inv', "
                + "apply PRIME.int_cast_mul_eq_one, rw [PRIME], "
                + "try { simp_int_casts }, norm_num1 },"
            )
            if to_field:
                ctx.add_main(
                    f"have {f_to_z_name} : ∀ x : F, x / {const_expr} = x / ({const_expr} : ℤ), "
                    + "{ intro x, norm_cast }, "
                )
        const_div_rw.append(hyp_name)
    return const_div_rw


def add_comm_rewrites(ctx: LeanGenContext, expr: Expression) -> List[str]:
    return [
        "add_comm " + a_expr + " " + b_expr
        for a_expr, b_expr in get_reversed_add_exprs(expr=expr, simplifier=ctx.simplifier)
    ]


def process_assert_block(
    ctx: LeanGenContext,
    asserts: List[Union[LeanPreprocessedAssertEq, LeanPreprocessedTempVarAlloc]],
    temp_name_prefix: str,
) -> Tuple[List[str], List[str], List[str]]:
    count = 0
    temp_rewrites = []
    temp_names = []
    div_var_names = []
    div_var_num = 0
    pc_offset = ctx.pc_offset
    for count in range(0, len(asserts)):
        code_elt = ctx.lean_code[ctx.lean_code_elt_num + count]
        an_assert = asserts[count]
        if isinstance(an_assert, LeanPreprocessedTempVarAlloc):
            mk_auto_soundness_alloc_tempvar(ctx, an_assert)
            continue
        assert isinstance(code_elt, LeanCodeAssertEq)
        instr_length = len(code_elt.code)
        temp_name = (temp_name_prefix + "{}").format(count)

        if instr_length == 1:
            ctx.add_main(f"step_assert_eq hpc{pc_offset} with {temp_name},")
        else:
            ctx.add_main(
                "step_assert_eq hpc{} hpc{} with {},".format(pc_offset, pc_offset + 1, temp_name),
            )

        if code_elt.inv_transformed and not code_elt.is_add:
            div_var_name = f"{ctx.div_var_basename}{div_var_num}"
            ctx.add_main(
                "cases exists_eq_ddiv_of_eq_mul {} with {} {}',".format(
                    temp_name, div_var_name, temp_name
                ),
            )
            div_var_names.append(div_var_name)
            div_var_num += 1
        if code_elt.inv_transformed:
            if code_elt.is_add:
                prf = f"(eq_sub_of_eq_add {temp_name})"
            else:
                prf = f"{temp_name}'"
        else:
            prf = f"{temp_name}"
        if code_elt.reversed:
            prf += ".symm"
        temp_rewrites.append(prf)
        temp_names.append(temp_name)
        pc_offset += instr_length

    return temp_rewrites, temp_names, div_var_names


def mk_if_branch_intro(
    ctx: LeanGenContext,
    cond: LeanBranchCond,
    is_pos: bool,
):
    """
    Generates the introduction to the proof of one of the branches following
    a conditional jump instruction (if or jnz).
    The arguments provide information about the condition leading to this branch
    and whether the context given is for the positive or negative branch.
    """
    ctx.add_intro(f'-- {cond.name}: {"positive" if is_pos else "negative"} branch')
    if cond.exprs is None:
        # The condition is [ap] != 0 or [ap] == 0.
        ctx.add_intro(f"rw ←regstateapeq_{cond.cond_var} at {cond.cond_var},"),
    elif cond.assert_rw:
        ctx.add_intro(f'have {cond.cond_var} := cond_aux{"1" if is_pos else "2"} htest hcond,')
        ctx.add_intro(f"try {{ arith_simps at {cond.cond_var} }},")
        ctx.add_intro("clear htest hcond,")
    else:
        ctx.add_intro(
            f"have {cond.cond_var} : "
            f'{cond.exprs[0]} {"=" if is_pos else "≠"} {cond.exprs[1]}, {{'
        )
        assert_simp = gen_assert_simp(
            ctx=ctx, var_rw=ctx.rewrites, assert_rw=["hcond"], is_struct=False
        )
        ctx.indent()
        if not is_pos:
            ctx.add_intro("try { simp only [ne.def] },")
        for line in assert_simp:
            ctx.add_intro(line)
        ctx.outdent()
        ctx.add_intro("},")
        ctx.add_intro(
            f"try {{ dsimp at {cond.cond_var} }}, try {{ arith_simps at {cond.cond_var} }},"
        )
        ctx.add_intro("clear hcond,")

    ctx.add_final("left," if is_pos == cond.is_eq else "right,")
    ctx.add_final(f"use_only [{cond.cond_var}],")


def mk_auto_soundness_theorem_block(
    lean_gen: LeanSoundnessGen, ctx: LeanGenContext
) -> Tuple[Optional[LeanGenContext], Optional[LeanGenContext], Optional[LeanBranchCond]]:
    """
    Generates the code for a block of code which begins at the current position
    of the generation context. Returns the contexts at the end of this block
    (both contexts are None if the block ends with a return, and the second context
    is None if the block does not end with a conditional branch). If the block ends
    with a conditional jump, the last return value provides information about
    this conditional jump.
    """

    cond: Optional[LeanBranchCond] = None
    # Context of the positive branch (if branching) or of the next instruction
    # (if no branching). May be the same as ctx.
    ctx_pos: Optional[LeanGenContext] = ctx
    ctx_neg: Optional[LeanGenContext] = None

    # Quits the loop once the next block is reached or a return is reached.
    while ctx_pos == ctx:
        instr = ctx.func.lean_desc[ctx.lean_desc_num]

        if isinstance(instr, LeanPreprocessedJumpToLabelInstruction) and instr.condition is None:
            mk_auto_soundness_jmp(ctx)
        elif isinstance(instr, LeanPreprocessedIf):
            cond = mk_auto_soundness_if(ctx, instr)
        elif (
            isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
            and instr.condition is not None
        ):
            cond = mk_auto_soundness_jnz(ctx)
        elif isinstance(instr, LeanPreprocessedReturn):
            mk_auto_soundness_return(ctx, instr)
        else:
            mk_auto_soundness_step_instr(ctx)

        ctx_pos, ctx_neg = lean_gen.next_ctxs(ctx)

    return ctx_pos, ctx_neg, cond


def mk_auto_soundness_jmp(ctx: LeanGenContext):
    ctx.add_main("-- jump statement")
    ctx.add_main("step_jump_imm hpc{} hpc{},".format(ctx.pc_offset, ctx.pc_offset + 1))


def mk_auto_soundness_if(ctx: LeanGenContext, instr: LeanPreprocessedIf) -> LeanBranchCond:
    ctx.add_main("-- if statement")
    ctx.desc_ctx.cairo_type = TypeFelt()
    expr_a, ctx.desc_ctx.div_var_startnum = to_lean_description_aux(
        expr=instr.expr_a, context=ctx.desc_ctx
    )
    expr_b, ctx.desc_ctx.div_var_startnum = to_lean_description_aux(
        expr=instr.expr_b,
        context=ctx.desc_ctx,
    )

    temp_rewrites, temp_names, div_var_names = process_assert_block(
        ctx=ctx, asserts=instr.asserts, temp_name_prefix="temp"
    )

    # Prepare the conditional jump.
    if temp_rewrites:
        ctx.add_main("have htest: _ = {} - {}, {{".format(expr_a, expr_b))
        ctx.add_main("  apply eq.trans {},".format(temp_rewrites[-1]))
        assert_simp = gen_assert_simp(
            ctx=ctx, var_rw=ctx.rewrites, assert_rw=temp_rewrites[:-1], is_struct=False
        )
        for line in assert_simp[:-1]:
            ctx.add_main("  " + line)
        ctx.add_main("  " + assert_simp[-1] + " },")
        ctx.add_main("clear {},".format(" ".join(temp_names)))
    pc_offset, _ = ctx.skip_asserts()
    ctx.add_main(
        "step_jnz hpc{} hpc{} with {} {},".format(pc_offset, pc_offset + 1, "hcond", "hcond"),
    )

    if ctx.desc_ctx.div_var_startnum > 0:
        ctx.add_final("use_only [{}],".format(", ".join(div_var_names)))

    # Branch.

    return LeanBranchCond(
        name="if",
        cond_var=f"a{ctx.pc_offset}",
        exprs=(expr_a, expr_b),
        is_eq=instr.cond_eq,
        assert_rw=temp_rewrites,
    )


def mk_auto_soundness_jnz(ctx: LeanGenContext) -> LeanBranchCond:
    cond_var = f"a{ctx.pc_offset}"
    ctx.add_main("-- jnz")
    # The trick to infer the ap value at proof time.
    ctx.add_main("apply of_register_state,")
    ctx.add_main(f"intros regstate{ctx.pc_offset} regstate{ctx.pc_offset}eq,")
    ctx.add_main(
        "have regstateapeq_{} := congr_arg register_state.ap regstate{}eq,".format(
            cond_var, ctx.pc_offset
        ),
    )
    ctx.add_main(f"try {{ dsimp at regstateapeq_{cond_var} }},")
    ctx.add_final(f"use_only (mem regstate{ctx.pc_offset}.ap),")

    ctx.add_main(
        "step_jnz hpc{} hpc{} with {} {},".format(
            ctx.pc_offset, ctx.pc_offset + 1, cond_var, cond_var
        ),
    )

    # Branch.

    return LeanBranchCond(
        name="jnz",
        cond_var=cond_var,
        exprs=None,
        # In the spec, equality is the first case.
        is_eq=True,
        assert_rw=[],
    )


def mk_auto_soundness_return(ctx: LeanGenContext, instr: LeanPreprocessedReturn):
    ctx.add_main("-- return")
    temp_rewrites, temp_names, _ = process_assert_block(
        ctx=ctx, asserts=instr.asserts, temp_name_prefix="hret"
    )
    pc_offset, _ = ctx.skip_asserts()
    ctx.add_main(f"step_ret hpc{pc_offset},")
    # Prove the trace count assertion.
    ctx.add_final("try { split, linarith },")
    assert_simp = gen_assert_simp(
        ctx=ctx,
        var_rw=ctx.rewrites,
        assert_rw=temp_rewrites,
        is_struct=False,
        additional_types=ctx.func.ret_arg_types,
    )
    ctx.rewrites.extend(temp_rewrites)
    ctx.add_final(f"try {{ ensures_simps; {assert_simp[0]} }},")
    ctx.concat_final(assert_simp[1:])


def mk_auto_soundness_add_ap(ctx: LeanGenContext, instr: LeanPreprocessedAddAp):
    ctx.add_main(f"-- ap += {instr.step}")
    ctx.add_main(f"step_advance_ap hpc{ctx.pc_offset} hpc{ctx.pc_offset + 1},")


def mk_auto_soundness_const(ctx: LeanGenContext, instr: LeanPreprocessedConst):
    name = str(instr.name[-1:])
    if name != "SIZEOF_LOCALS":
        ctx.add_main("-- const")
        ctx.add_main(f"set! {name} := ({instr.val} : F) with hc_{name},")
        ctx.rewrites += [f"hc_{name}"]
        ctx.add_final(f"use [{name}, hc_{name}],")


def mk_auto_soundness_assert(
    ctx: LeanGenContext,
    instr: Union[LeanPreprocessedAssertEq, LeanPreprocessedCompoundAssertEq],
):
    """
    This function generates the code both for simple and compound asserts.
    """
    if isinstance(instr, LeanPreprocessedCompoundAssertEq):
        ctx.add_main("-- compound assert eq")
        asserts = instr.asserts
    else:
        ctx.add_main("-- assert eq")
        asserts = [instr]

    ctx.desc_ctx.cairo_type = (
        instr.resolved_type if isinstance(instr, LeanPreprocessedCompoundAssertEq) else TypeFelt()
    )

    # Simplifier processes rhs first.
    rhs, ctx.desc_ctx.div_var_startnum = to_lean_description_aux(
        expr=instr.rhs,
        context=ctx.desc_ctx,
    )
    lhs, ctx.desc_ctx.div_var_startnum = to_lean_description_aux(
        expr=instr.lhs,
        context=ctx.desc_ctx,
    )
    expr_simps = LeanExprSimps()
    prepare_expr_simps(simps=expr_simps, ctx=ctx, expr=instr.rhs, div_to_field=False)
    prepare_expr_simps(simps=expr_simps, ctx=ctx, expr=instr.lhs, div_to_field=False)
    temp_rewrites, temp_names, div_var_names = process_assert_block(
        ctx=ctx, asserts=asserts, temp_name_prefix="temp"
    )
    ctx.add_main(f"have a{ctx.pc_offset}: {lhs} = {rhs}, {{")
    ctx.indent()
    apply_expr_simps(simps=expr_simps, ctx=ctx)

    is_struct = isinstance(instr, LeanPreprocessedCompoundAssertEq) and not isinstance(
        instr.resolved_type, TypeFelt
    )
    if is_struct:
        # The lhs is always a simple expression, so no need for the assert_eq_reduction.
        assert_simp = gen_assert_simp(
            ctx=ctx, var_rw=ctx.rewrites, assert_rw=temp_rewrites, is_struct=is_struct
        )
    else:
        # if the goal is `c = d`, the last of the sequence of asserted equations is of the form
        # `a = b`, where `a` should turn into `c` by rewriting, and `b` should turn into `d`.
        # The lemma `assert_reduction` turns the goal into `a = c ∧ d = b`.
        ctx.add_main(f"apply assert_eq_reduction {temp_rewrites[-1]},")
        assert_simp = gen_assert_simp(
            ctx=ctx, var_rw=ctx.rewrites, assert_rw=temp_rewrites[:-1], is_struct=is_struct
        )

    for line in assert_simp:
        ctx.add_main(line)

    if is_struct:
        ctx.outdent()

    ctx.outdent()
    ctx.add_main("},")

    if not is_struct:
        ctx.add_main(
            f"try {{ dsimp at a{ctx.pc_offset} }}, try {{ arith_simps at a{ctx.pc_offset} }},"
        )
    ctx.add_main(f'clear {" ".join(temp_names)},')
    # Establish the assertion in the final proof.
    if div_var_names:
        ctx.add_final(f'use_only [{", ".join(div_var_names)}],')
    # The result is lhs = rhs.
    ctx.add_final(f"use_only [a{ctx.pc_offset}],")
    # Add range check proof, if needed.
    add_assert_range_checked(
        ctx=ctx, lhs=instr.lhs, rhs=instr.rhs, assert_rw="a{}".format(ctx.pc_offset)
    )


def mk_auto_soundness_ref(ctx: LeanGenContext, instr: LeanPreprocessedReference):
    if instr.is_local_var:
        ctx.add_main("-- local var")
        if instr.asserts:
            temp_rewrites, temp_names, _ = process_assert_block(
                ctx=ctx, asserts=instr.asserts, temp_name_prefix="temp"
            )
            var_rw, var_type, var_cast = copy_local(ctx, instr, temp_rewrites)
        else:
            var_rw, var_type, var_cast = create_local(ctx, instr)
    elif is_ap_ref(instr.expr):
        ctx.add_main("-- let (ap reference)")
        var_rw, var_type, var_cast = alloc_var(ctx, instr)
    else:
        ctx.add_main("-- let")
        var_rw, var_type, var_cast = create_var(ctx, instr)
        expr_simps = LeanExprSimps()
        prepare_expr_simps(simps=expr_simps, ctx=ctx, expr=instr.expr, div_to_field=False)
        if not expr_simps.is_empty():
            # We need to simplify the rewrite which we will use for simplifying other expressions,
            # but keep the original unchanged, as it is needed to solve the corresponding expression
            # in the spec. Therefore, we create a copy of the rewrite before simplifying.
            orig_var_rw = var_rw
            var_rw += "'"
            ctx.add_main(f"have {var_rw} := {orig_var_rw},")
            for line in gen_expr_simps(expr_simps, var_rw):
                ctx.add_main(line)
        ctx.add_main(f"try {{ dsimp at {var_rw} }}, try {{ arith_simps at {var_rw} }},")

    ctx.rewrites.append(var_rw)
    if not isinstance(var_type, TypeFelt):
        ctx.rewrite_types[var_rw] = (var_type, var_cast)
    # Add range check proof if needed.
    add_var_range_checked(ctx=ctx, expr=instr.expr, var_rw=var_rw)


def mk_auto_soundness_alloc_tempvar(ctx: LeanGenContext, instr: LeanPreprocessedTempVarAlloc):
    """
    Generates the code for a tempvar instruction that only allocates the memory
    for the variable but does not assign it a value.
    """
    ctx.add_main("-- tempvar")
    var_rw, var_type, var_cast = alloc_var(ctx, instr)
    ctx.rewrites += [var_rw]
    if not isinstance(var_type, TypeFelt):
        ctx.rewrite_types[var_rw] = (var_type, var_cast)
    # Process the embedded ap += c instruction.
    if instr.add_ap_instr is not None:
        mk_auto_soundness_add_ap(ctx, instr.add_ap_instr)


def mk_auto_soundness_tempvar(ctx: LeanGenContext, instr: LeanPreprocessedTempVar):
    """
    Generates the code for a tempvar instruction where the instruction also assigns
    the variable a value.
    """
    ctx.add_main("-- tempvar")
    base_name = instr.identifier.identifier.name
    temp_rewrites, temp_names, _ = process_assert_block(
        ctx=ctx,
        asserts=instr.asserts,
        temp_name_prefix="tv_" + base_name,
    )
    var_rw, var_type, var_cast = create_var(ctx, instr)
    if not isinstance(var_type, TypeFelt):
        ctx.rewrite_types[var_rw] = (var_type, var_cast)
    name = name_with_sub(base_name, ctx.name_sub)
    ctx.add_main(f'have htv_{name}: {name} = {var_cast  + " mem " if var_cast else ""}_, {{')
    # Division by a constant.
    # We rewrite the variable rw from division to multiplication. This should
    # happen inside the proof of htv_* as outside of this proof we want to keep
    # the original variable rw (with division).
    ctx.indent()
    expr_simps = LeanExprSimps()
    prepare_expr_simps(simps=expr_simps, ctx=ctx, expr=instr.expr, div_to_field=False)
    ctx.outdent()
    assert_simp = gen_tempvar_assignment(
        ctx=ctx,
        var_size=ctx.func.struct_defs.get_type_size(var_type),
        var_rw=var_rw,
        assert_rw=temp_rewrites,
        expr_simps=expr_simps,
    )
    ctx.indent()
    for line in assert_simp:
        ctx.add_main(line)
    ctx.outdent()

    ctx.add_main(f'clear {" ".join(temp_names)},')
    ctx.add_main(f"try {{ dsimp at {var_rw} }}, try {{ arith_simps at {var_rw} }},")
    ctx.rewrites += [var_rw, f"htv_{name}"]
    if not isinstance(var_type, TypeFelt):
        ctx.rewrite_types[var_rw] = (var_type, var_cast)
    # Add range check proof, if needed.
    add_var_range_checked(ctx=ctx, expr=instr.expr, var_rw=var_rw)


def mk_auto_soundness_call(ctx: LeanGenContext, instr: LeanPreprocessedFuncCall):
    is_tail_call = isinstance(instr, LeanPreprocessedTailCall)
    ctx.add_main(
        "-- {}{}function call".format(
            "tail " if is_tail_call else "", "recursive " if ctx.func.name == instr.name else ""
        )
    )
    temp_rewrites, temp_names, div_var_names = process_assert_block(
        ctx=ctx, asserts=instr.asserts, temp_name_prefix="arg"
    )
    pc_offset, _ = ctx.skip_asserts()

    function_dict = ctx.lean_info.function_dict
    fn = function_dict[instr.name]
    # Prepare range check pointer (if used).
    added_rc_call_arg_var = add_rc_call_arg_var(ctx=ctx, called_func=fn)

    # Execute the call.
    # The arguments to the theorem are: `mem`, the register, the arguments,
    # the fact that the code is in memory, the fact that its dependencies are in memory,
    # and the fact that the arguments are in the right place.
    # Only `mem` and the arguments are given; the rest are underscores.
    call_soundness_thm = mk_lean_auto_soundness_name(instr.name, ctx.lean_info.open_namespaces)
    call_args = gen_implicit_args(fn, len(instr.func_args), ctx.name_sub)
    arg_descs = []
    expr_simps = LeanExprSimps()
    for arg, arg_type in zip(instr.func_args, list(fn.arg_cairo_types.values())):
        ctx.desc_ctx.cairo_type = arg_type
        call_arg, ctx.desc_ctx.div_var_startnum = to_lean_paren_description_aux(
            expr=arg,
            context=ctx.desc_ctx,
        )
        # Prepare handling of arguments with division by a constant.
        prepare_expr_simps(simps=expr_simps, ctx=ctx, expr=arg, div_to_field=True)
        arg_descs.append(call_arg)
    call_args += " ".join(arg_descs)
    call_dependencies = fn.call_dependencies
    underscores = " ".join(
        ["_"] * (fn.num_implicit_args + len(instr.func_args) + 1 + len(call_dependencies))
    )

    if instr.name != ctx.func.name:
        ctx.add_main(
            "step_sub hpc{} ({} mem _ {} {}),".format(
                pc_offset, call_soundness_thm, call_args, underscores
            ),
        )
    else:
        # Use the inductive hypothesis for the recursive call.
        ctx.add_main(f"step_rec_sub hpc{pc_offset} (νih _ {call_args} {underscores}),")
    pc_offset += 1

    # The function is in memory at the right place.
    if instr.name != ctx.func.name:
        ctx.add_main(f"{{ rw hpc{pc_offset}, norm_num2, exact h_mem_{fn.id} }},")
    else:
        # Recursive call needs stronger version of `norm_num`.
        ctx.add_main(f"{{ rw hpc{pc_offset}, norm_num, exact h_mem_rec }},")
    # Its dependencies are in memory.
    dep_list = [(dep_name, function_dict[dep_name].start_pc) for dep_name in call_dependencies]
    dep_list.sort(key=lambda p: p[1])
    for d in dep_list:
        d_id = function_dict[d[0]].id
        ctx.add_main(f"{{ rw hpc{pc_offset}, norm_num2, exact h_mem_{d_id} }},")
    # The arguments are in the right place.
    for _, type in fn.get_args_with_type(with_ret=False).items():
        assert_simp = gen_assert_simp(
            ctx=ctx,
            var_rw=ctx.rewrites,
            assert_rw=temp_rewrites,
            is_struct=(type != "F"),
        )
        ctx.add_main("{ " + " ".join(gen_expr_simps(expr_simps) + [assert_simp[0]]))
        assert_simp[-1] += " },"
        ctx.indent()
        for line in assert_simp[1:]:
            ctx.add_main(line)
        ctx.outdent()
    pc_offset += 1
    # Introduce the new specification and ap into the context.
    ctx.add_main(f"intros κ_call{pc_offset} ap{pc_offset} h_call{pc_offset},")

    ap_rw = ""
    if fn.has_const_ap_offset:
        ctx.add_main(
            f"rcases h_call{pc_offset} with ⟨h_call{pc_offset}_ap_offset, h_call{pc_offset}⟩,"
        )
        ap_rw = f"h_call{pc_offset}_ap_offset"
        ctx.ap_rewrites.append(ap_rw)

    # if the specification is `rc_ensures`, handle it
    add_called_func_rc(ctx=ctx, called_func=fn, ap_rw=ap_rw, pc_offset=pc_offset)
    # The div variables appear before the return variables.
    if div_var_names:
        ctx.add_final(f'use_only [{", ".join(div_var_names)}],')

    # The κ for this function call.
    ctx.add_final(f"use_only [κ_call{pc_offset}],")

    if is_tail_call:
        # This is immediately also a return.
        ctx.add_main(f"step_ret hpc{pc_offset},")

    # Calculate the offsets and casts of the return variables.
    offsets_etc = get_auto_soundness_ret_types_offsets_and_casts(fn, ctx.lean_info, "")

    # Create the implicit return variables.
    if fn.num_implicit_args > 0:
        for pos, ret_var in enumerate(fn.arg_names[: fn.num_implicit_args]):
            if not need_ret_var(ctx, ret_var, is_tail_call):
                continue
            var_type, offset, cast = offsets_etc[pos]
            ret_var_rw = create_ret_var(
                ctx=ctx,
                offset=offset,
                cast=cast,
                ret_var_base=ret_var,
                is_explicit=False,
                is_tail_call=is_tail_call,
                pc_offset=pc_offset,
            )
            ctx.rewrites.append(ret_var_rw)
            if not isinstance(var_type, TypeFelt):
                ctx.rewrite_types[ret_var_rw] = (var_type, cast)
    # Create the return variables.
    if fn.num_returns == len(instr.ret_vars):
        for pos, ret_var in enumerate(instr.ret_vars):
            if not need_ret_var(ctx, ret_var, is_tail_call):
                continue

            var_type, offset, cast = offsets_etc[pos + fn.num_implicit_args]

            if ret_var == "_":
                ctx.add_final(
                    "use_only [({}mem (ap{} - {}))],".format(
                        cast + " " if cast else "", pc_offset, -offset
                    )
                )
                continue

            ret_var_rw = create_ret_var(
                ctx=ctx,
                offset=offset,
                cast=cast,
                ret_var_base=ret_var,
                is_explicit=True,
                is_tail_call=is_tail_call,
                pc_offset=pc_offset,
            )
            ctx.rewrites.append(ret_var_rw)
            if not isinstance(var_type, TypeFelt):
                ctx.rewrite_types[ret_var_rw] = (var_type, cast)
    elif not is_tail_call:
        # Instantiate the return positions in the final proof.
        for pos in range(fn.num_returns):
            var_type, offset, cast = offsets_etc[pos + fn.num_implicit_args]
            ctx.add_final(
                "use_only [({}mem (ap{} - {}))],".format(
                    cast + " " if cast else "", pc_offset, -offset
                )
            )

    # Establish the function call specification in the final proof.
    if not fn.has_range_check():
        # Simplify constants, if any.
        ctx.add_final(f"try {{ dsimp at h_call{pc_offset}, arith_simps at h_call{pc_offset} }},")
        # Need the 'try' here because sometimes the goal is solved by a previous simplification.
        ctx.add_final("try {{ use_only [h_call{}] }},".format(pc_offset))
        if is_tail_call:
            ctx.add_final("try { linarith },")
    else:
        add_rw_call_range_check(
            ctx=ctx,
            called_func=fn,
            pc_offset=pc_offset,
            added_rc_call_arg_var=added_rc_call_arg_var,
            arg_rw=temp_names,
        )
        add_sub_call_rc_final(
            ctx=ctx, called_func=fn, pc_offset=pc_offset, is_tail_call=is_tail_call
        )
        if is_tail_call:
            ctx.add_final("try { linarith },")

    # Clean up.
    ctx.add_main(f'clear {" ".join(temp_names)},')


def mk_auto_soundness_step_instr(ctx: LeanGenContext):
    """
    Adds the part of the proof which corresponds to a single Cairo instruction after
    which the PC pointer moves to the next instruction (that is, not a jump or
    a return).
    """
    instr = ctx.func.lean_desc[ctx.lean_desc_num]
    if isinstance(instr, LeanPreprocessedNop):
        return
    if isinstance(instr, LeanPreprocessedAddAp):
        mk_auto_soundness_add_ap(ctx, instr)
    elif isinstance(instr, LeanPreprocessedConst):
        mk_auto_soundness_const(ctx, instr)
    elif isinstance(instr, LeanPreprocessedAssertEq) or isinstance(
        instr, LeanPreprocessedCompoundAssertEq
    ):
        mk_auto_soundness_assert(ctx, instr)
    elif isinstance(instr, LeanPreprocessedReference):
        mk_auto_soundness_ref(ctx, instr)
    elif isinstance(instr, LeanPreprocessedTempVar) and is_alloc_tempvar(instr):
        mk_auto_soundness_alloc_tempvar(ctx, instr)
    elif isinstance(instr, LeanPreprocessedTempVar):
        mk_auto_soundness_tempvar(ctx, instr)
    elif isinstance(instr, LeanPreprocessedFuncCall):
        mk_auto_soundness_call(ctx, instr)
    else:
        raise Exception("mk_auto_soundness_step_instr: not handled yet")


def mk_block_apply_proof(from_ctx: LeanGenContext, ctx: LeanGenContext) -> List[str]:
    """
    Generates the part of the proof that applies the proof of the block ctx
    as the end of the proof which flows from from_ctx.
    """
    if from_ctx.ap_rewrites:
        ctx.add_main(
            f'try {{ simp only [{", ".join(from_ctx.ap_rewrites)}] }},' "try { arith_simps },"
        )
    # For each argumment name, find the corresponding variable (with subscript)
    # and the corresponding rewrite.
    args = []
    # The expression to use when applying the block.
    apply_arg_h = []
    # Simplification to apply after applying the block for _ arguments (in order).
    simp_arg_h = []
    for name in ctx.block_info.get_arg_names():
        rebound = name_with_sub(name, from_ctx.name_sub)
        args.append(rebound)

        if ctx.block_info.is_let_arg(name):
            apply_arg_h.append("_")
            # Full simplification (using all rewrites) is required in this case.
            simp_arg_h.append("")
            continue

        if f"hin_{rebound}" in from_ctx.rewrites:
            simp_h = f"hin_{rebound}"
        elif f"htv_{rebound}" in from_ctx.rewrites:
            simp_h = f"htv_{rebound}"
        elif f"lc_{rebound}" in from_ctx.rewrites:
            simp_h = f"lc_{rebound}"
        elif f"hl_{rebound}" in from_ctx.rewrites:
            simp_h = f"hl_{rebound}"
        else:
            raise Exception("Failed to find rewrite for block soundness application.")
        if ctx.block_info.is_ap_arg(name) and (
            not ctx.func.has_const_ap_offset or from_ctx.ap_rewrites
        ):
            apply_arg_h.append("_")
            simp_arg_h.append(simp_h)
        else:
            apply_arg_h.append(simp_h)
    mem_h = ["h_mem_rec"] + get_dep_args(from_ctx)

    ctx.add_main("-- Use the block soundness theorem.")

    ctx.add_main(
        "apply ensuresb_ret_trans ({} mem σ{}{}{}{} νbound{}),".format(
            ctx.auto_soundness_theorem_name,
            " _" if not ctx.func.has_const_ap_offset else "",
            " " + " ".join(args) if args else "",
            " " + " ".join(mem_h),
            " " + " ".join(apply_arg_h) if apply_arg_h else "",
            " " + "νih" if ctx.func.is_recursive else "",
        )
    )
    if simp_arg_h:
        ctx.add_main("rotate,")
        ap_simp = (
            f' try {{ simp only [{" ,".join(from_ctx.ap_rewrites)}] }},'
            if from_ctx.ap_rewrites
            else ""
        )
        for simp_h in simp_arg_h:
            if simp_h:
                # This is a simple ap argument simplification.
                ctx.add_main(
                    f"{{ simp only [{simp_h}],{ap_simp} try {{ arith_simps }}, try {{ refl }} }},"
                )
            else:
                # Full rewrite required.
                h_simps = gen_assert_simp(
                    ctx=from_ctx, var_rw=from_ctx.rewrites, assert_rw=[], is_struct=False
                )
                h_simps[-1] += " },"
                ctx.add_main("{ " + h_simps[0])
                ctx.indent()
                for line in h_simps[1:]:
                    ctx.add_main(line)
                ctx.outdent()

    ctx.add_main(f"intros κ{ctx.block_name_suffix} τ, try {{ arith_simps }},")
    h_block = "h" + ctx.block_name_suffix
    if not ctx.func.has_const_ap_offset:
        ctx.add_main(f"intro {h_block},")
    else:
        ctx.add_main(f"rintros ⟨apeq, {h_block}⟩,")
        ctx.add_main("use_only [apeq],")

    add_block_rc(ctx)
    add_rc_condition_proof(ctx)

    if ctx.rc_steps is not None:
        ctx.concat_final(ctx.rc_steps.add_block_rc_final(ctx.func.rc, ctx.block_name_suffix))
    ctx.add_final(f"use_only[κ{ctx.block_name_suffix}],")
    ctx.add_final(f"use [{h_block}],")
    ctx.add_final("try { linarith }")

    return ctx.proof_intro + ctx.main_proof + [ctx.prefix + line for line in ctx.final_proof]


def mk_auto_soundness_block_proof_finish(ctx: LeanGenContext):
    ctx.add_main("-- finish")
    ctx.add_main("step_done, use_only [rfl, rfl],")

    if ctx.func.has_const_ap_offset:
        if len(ctx.ap_rewrites) == 0:
            ctx.add_main("split, refl,")
        else:
            ctx.add_main("split,")
            ctx.add_main(f'{{ try {{ simp only [{" ,".join(ctx.ap_rewrites)}] }},')
            ctx.indent()
            ctx.add_main("try { arith_simps }, try { refl } },")
            ctx.outdent()

    # If the function uses the range check built-in, prove the range_checked
    # condition for the function.
    add_rc_condition_proof(ctx)


def mk_auto_soundness_block_final_proof_intro(ctx: LeanGenContext):
    """
    Generates the beginning of the final proof. Should be called on teh first
    block in the proof before generating any of the proof.
    """
    ctx.add_final("-- Final Proof")
    mk_simplify_to_auto(ctx)


def mk_simplify_to_auto(ctx: LeanGenContext):
    if ctx.is_main_theorem:
        # In this case we first need to reduce the user specification to the automatic
        # specification.
        ctx.add_final("-- user-provided reduction")
        underscores = "".join([" _"] * (ctx.func.num_returns + ctx.func.num_implicit_args))
        args = " ".join(ctx.func.arg_names)
        ctx.add_final(f"suffices auto_spec: {ctx.auto_spec_name} mem _ {args}{underscores},")
        ctx.add_final(f"{{ apply {ctx.user_soundness_theorem_name}, apply auto_spec }},")
        ctx.add_final("-- prove the auto generated assertion")

    ctx.add_final(f"dsimp [{ctx.auto_spec_name}],")
    ctx.add_final("try { norm_num1 }, try { arith_simps },")


def get_soundness_func_arg_defs(func: LeanFunctionInfo) -> List[str]:
    arg_types = func.get_args_with_type(with_ret=False)
    return create_arg_defs(arg_types)


def get_soundness_func_block_arg_defs(ctx: LeanGenContext) -> List[str]:
    arg_types = ctx.block_info.get_args_with_type()
    return create_arg_defs(arg_types)


def get_auto_soundness_arg_types_offsets_and_casts(
    func: LeanFunctionInfo,
    lean_info: LeanProgramInfo,
    cast_end_separator: str = "",
) -> Dict[str, Tuple[CairoType, int, str]]:
    """
    Returns a dictionary mapping each input argument of the function (both
    implicit and explicit) to its resolved type, its offset from fp and the cast
    it requires.
    """
    end_offset = -2
    explicit_offsets_etc = lean_info.struct_defs.get_arg_types_offsets_and_casts(
        func.func_scope, func.args_struct, end_offset, lean_info.open_namespaces, cast_end_separator
    )
    if len(explicit_offsets_etc) > 0:
        _, end_offset, _ = next(iter(explicit_offsets_etc.values()))
    offsets_etc = lean_info.struct_defs.get_arg_types_offsets_and_casts(
        func.func_scope,
        func.implicit_args_struct,
        end_offset,
        lean_info.open_namespaces,
        cast_end_separator,
    )
    offsets_etc.update(explicit_offsets_etc)

    return offsets_etc


def get_auto_soundness_ret_types_offsets_and_casts(
    func: LeanFunctionInfo,
    lean_info: LeanProgramInfo,
    cast_end_separator: str = "",
) -> List[Tuple[CairoType, int, str]]:
    end_offset = 0
    explicit_offsets_etc = lean_info.struct_defs.get_offsets_and_casts_by_types(
        func.func_scope,
        func.ret_arg_types,
        end_offset,
        lean_info.open_namespaces,
        cast_end_separator,
    )
    if len(explicit_offsets_etc) > 0:
        _, end_offset, _ = explicit_offsets_etc[0]
    implicit_offsets_etc = lean_info.struct_defs.get_arg_types_offsets_and_casts(
        func.func_scope,
        func.implicit_args_struct,
        end_offset,
        lean_info.open_namespaces,
        cast_end_separator,
    )
    return list(implicit_offsets_etc.values()) + explicit_offsets_etc


def get_auto_soundness_ret_vals(
    func: LeanFunctionInfo,
    lean_info: LeanProgramInfo,
) -> List[str]:
    ret_vals = []
    for _, offset, cast in get_auto_soundness_ret_types_offsets_and_casts(func, lean_info, " "):
        ret_vals.append(f"({cast}mem (τ.ap - {-offset}))")
    return ret_vals


def mk_lean_function_auto_soundness_theorem(
    func: LeanFunctionInfo,
    lean_info: LeanProgramInfo,
    assembly_info: LeanAssemblyInfo,
    out,
):
    soundness_gen = LeanSoundnessGen(func=func, lean_info=lean_info, assembly_info=assembly_info)
    soundness_gen.gen_blocks()
    proofs = soundness_gen.gen_func_proofs()

    for line in proofs:
        print(line, file=out)


# These functions generate the relevant files.

# Code file.


def mk_lean_code_file(
    file_names: LeanFileNames, lean_info: LeanProgramInfo, assembly_info: LeanAssemblyInfo
):

    out = open(file_names.code_filename, "w")
    lean_code = [code_line for code_elt in assembly_info.lean_code for code_line in code_elt.code]

    print("/-", file=out)
    print("File: {}.lean".format(file_names.code_base_filename), file=out)
    print(file=out)
    print("Autogenerated file.", file=out)
    print("-/", file=out)
    print("import " + mk_lean_core_import_path("hoare"), file=out)
    print(file=out)
    print("variables {F : Type} [field F] [decidable_eq F]", file=out)
    print(file=out)
    for func in lean_info.all_funcs:
        print("/- function {} code definition -/".format(func.name), file=out)
        print(file=out)
        mk_lean_function_code_def(
            func.name, lean_info.main_scope, lean_code[func.start_pc : func.end_pc], out
        )
        print(file=out)

    out.close()


# Autogenerated soundness proofs.


def mk_lean_soundness(
    file_names: LeanFileNames,
    soundness_select: Optional[List[str]],
    lean_info: LeanProgramInfo,
    assembly_info: LeanAssemblyInfo,
) -> List[str]:
    """
    Creates the soundness files for all functions and returns the paths (relative to
    the current working directory) of the files created.
    """

    soundness_files = []

    for func in lean_info.all_funcs:
        if soundness_select is not None and not any(s in func.name for s in soundness_select):
            continue
        filename_with_path = file_names.soundness_filename(func.name)
        out = open(filename_with_path, "w")
        soundness_files.append(filename_with_path)

        mk_lean_soundness_file(
            func=func,
            file_names=file_names,
            lean_info=lean_info,
            assembly_info=assembly_info,
            out=out,
        )
        out.close()

    return soundness_files


def make_top_dependencies(func: LeanFunctionInfo, lean_info: LeanProgramInfo):
    dependencies = func.call_dependencies.copy()
    for dep in func.call_dependencies:
        dependencies.difference_update(lean_info.function_dict[dep].call_dependencies)
    return dependencies


def make_dependency_import(func: LeanFunctionInfo, lean_info: LeanProgramInfo) -> List[str]:
    lines = []
    top_dependencies = make_top_dependencies(func, lean_info)
    for dep in top_dependencies:
        dep_scope = ScopedName.from_string(dep)
        lines.append(
            f"import {mk_lean_dependency_soundness_import_path(lean_info.main_scope, dep_scope)}"
        )

    return lines


def mk_lean_soundness_file(
    func: LeanFunctionInfo,
    file_names: LeanFileNames,
    lean_info: LeanProgramInfo,
    assembly_info: LeanAssemblyInfo,
    out,
):

    make_top_dependencies(func, lean_info)

    print("/-", file=out)
    print("File: {}.lean".format(file_names.soundness_base_filename(func.name)), file=out)
    print("", file=out)
    print("Autogenerated file.", file=out)
    print("-/", file=out)
    print("import " + mk_lean_core_import_path("hoare"), file=out)
    print(
        "import {}".format(
            mk_lean_rel_import_path(
                import_file=file_names.code_filename,
                from_file=file_names.soundness_filename(func.name),
            )
        ),
        file=out,
    )
    print(
        "import {}".format(
            mk_lean_rel_import_path(
                import_file=file_names.spec_filename,
                from_file=file_names.soundness_filename(func.name),
            )
        ),
        file=out,
    )

    for line in make_dependency_import(func, lean_info):
        print(line, file=out)

    print("open tactic", file=out)
    print(file=out)
    for open_scope in func.open_namespaces:
        print(f"open {str(open_scope)}", file=out)
    print(file=out)
    print("variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]", file=out)
    print("variable  mem : F → F", file=out)
    print("variable  σ : register_state F", file=out)
    print(file=out)

    print("/- {} autogenerated soundness theorem -/".format(func.name), file=out)
    print(file=out)
    mk_lean_function_auto_soundness_theorem(
        func=func, lean_info=lean_info, assembly_info=assembly_info, out=out
    )
    print(file=out)
