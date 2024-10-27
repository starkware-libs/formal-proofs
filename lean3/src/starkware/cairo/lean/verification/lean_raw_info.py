import dataclasses
from typing import Dict, List, Optional, Set, Tuple, Union

from starkware.cairo.lang.compiler.ast.cairo_types import CairoType, TypeFelt
from starkware.cairo.lang.compiler.ast.expr import (
    ExprCast,
    ExprConst,
    Expression,
    ExprHint,
    ExprTuple,
)
from starkware.cairo.lang.compiler.ast.types import TypedIdentifier
from starkware.cairo.lang.compiler.error_handling import Location
from starkware.cairo.lang.compiler.identifier_definition import StructDefinition
from starkware.cairo.lang.compiler.preprocessor.auxiliary_info_collector import (
    AuxiliaryInfoCollector,
)
from starkware.cairo.lang.compiler.preprocessor.flow import FlowTrackingData
from starkware.cairo.lang.compiler.preprocessor.preprocessor import Preprocessor
from starkware.cairo.lang.compiler.preprocessor.reg_tracking import (
    RegChange,
    RegChangeUnconstrained,
)
from starkware.cairo.lang.compiler.scoped_name import ScopedName

# Information for the preprocessor to store.


@dataclasses.dataclass
class LeanPreprocessedCodeElement:
    accessible_scopes: List[ScopedName]
    flow_tracking_data: FlowTrackingData

    def get_exprs(self) -> List[Expression]:
        return []


@dataclasses.dataclass
class LeanPreprocessedAssertEq(LeanPreprocessedCodeElement):
    lhs: Expression
    rhs: Expression

    def get_exprs(self) -> List[Expression]:
        return [self.lhs, self.rhs]


@dataclasses.dataclass
class LeanPreprocessedAddAp(LeanPreprocessedCodeElement):
    step: int

    def get_exprs(self) -> List[Expression]:
        return []


@dataclasses.dataclass
class LeanPreprocessedTempVarAlloc(LeanPreprocessedCodeElement):
    """
    Represents the memory allocation of a tempvar and the name (and type)
    assigned to this allocation.
    """

    identifier: TypedIdentifier
    resolved_type: CairoType
    add_ap_instr: Optional[LeanPreprocessedAddAp]
    expr: Expression

    def get_exprs(self) -> List[Expression]:
        return [self.expr] if self.expr is not None else []


@dataclasses.dataclass
class LeanPreprocessedWithAsserts(LeanPreprocessedCodeElement):
    """
    A common base class for all code elements which may be translated into
    a sequence of asserts and/or anonymous tempvar allocation (through an ap +=
    instruction) possibly in addition to the main instruction
    (such as a call or return).
    """

    asserts: List[Union[LeanPreprocessedAssertEq, LeanPreprocessedTempVarAlloc]]

    def get_hint_vars(self) -> List[LeanPreprocessedTempVarAlloc]:
        return [x for x in self.asserts if isinstance(x, LeanPreprocessedTempVarAlloc)]


@dataclasses.dataclass
class LeanPreprocessedCompoundAssertEq(LeanPreprocessedWithAsserts):
    lhs: Expression
    rhs: Expression
    resolved_type: CairoType

    def get_exprs(self) -> List[Expression]:
        return [self.lhs, self.rhs]


@dataclasses.dataclass
class LeanPreprocessedTempVar(LeanPreprocessedTempVarAlloc, LeanPreprocessedWithAsserts):
    """
    A tempvar combines the allocation of a tempvar and possibly a sequence of asserts
    that sets its initial value.
    """


@dataclasses.dataclass
class LeanPreprocessedReference(LeanPreprocessedWithAsserts):
    identifier: TypedIdentifier
    resolved_type: CairoType
    expr: Expression
    is_local_var: bool

    def get_exprs(self) -> List[Expression]:
        return [self.expr]


@dataclasses.dataclass
class LeanPreprocessedFuncCall(LeanPreprocessedWithAsserts):
    name: str
    # Explicit arguments only.
    func_args: List[Expression]
    ret_vars: List[str]

    def get_exprs(self) -> List[Expression]:
        return self.func_args


@dataclasses.dataclass
class LeanPreprocessedTailCall(LeanPreprocessedFuncCall):
    """
    This class is identical to a standard function call, but by using this
    class one indicates that the function call is a tail call.
    """


@dataclasses.dataclass
class LeanPreprocessedReturn(LeanPreprocessedWithAsserts):
    ret_arg_exprs: List[Expression]

    def get_exprs(self) -> List[Expression]:
        return self.ret_arg_exprs


@dataclasses.dataclass
class LeanPreprocessedJumpToLabelInstruction(LeanPreprocessedCodeElement):
    # If it comes from an if statement, we store this with the if statement and handle it there.
    # The (possible) condition stored here is used only if it appears in the code by itself.
    label_name: ScopedName
    offset: int
    pc_dest: int
    condition: Optional[Expression]

    def get_exprs(self) -> List[Expression]:
        return [self.condition] if self.condition is not None else []


@dataclasses.dataclass
class LeanPreprocessedIf(LeanPreprocessedWithAsserts):
    expr_a: Expression
    expr_b: Expression
    cond_eq: bool
    jump_instr: Optional[LeanPreprocessedJumpToLabelInstruction]

    def get_exprs(self) -> List[Expression]:
        return [self.expr_a, self.expr_b]


@dataclasses.dataclass
class LeanPreprocessedConst(LeanPreprocessedCodeElement):
    name: ScopedName
    val: int
    expr: Expression

    def get_exprs(self) -> List[Expression]:
        return [self.expr]


@dataclasses.dataclass
class LeanPreprocessedNop(LeanPreprocessedCodeElement):
    def get_exprs(self) -> List[Expression]:
        return []


# Information associated with each function by the preprocessor.


@dataclasses.dataclass
class LeanRawFunctionInfo:
    name: str
    id: int  # Just an identifying number.
    start_pc: int
    end_pc: int
    # The structures defining the implicit and explicit arguments.
    implicit_args_struct: StructDefinition
    args_struct: StructDefinition
    ret_type: Optional[CairoType]
    call_dependencies: Set[str]
    total_ap_change: RegChange = RegChangeUnconstrained()
    is_recursive: bool = False
    lean_desc: List[LeanPreprocessedCodeElement] = dataclasses.field(default_factory=lambda: [])
    label_dict: Dict[ScopedName, int] = dataclasses.field(default_factory=lambda: {})

    # Used internally, when gathering information in the preprocessor.
    current_instr: Optional[LeanPreprocessedCodeElement] = None

    def reset_upon_retry(self):
        """
        Resets those parts of the function information which have to be collected again
        in case the preprocessor retries to process the function.
        """
        self.call_dependencies = set()
        self.is_recursive = False
        self.lean_desc = []
        self.label_dict = {}
        self.current_instr = None


# Information from the preprocessor.


@dataclasses.dataclass
class LeanRawProgramInfo(AuxiliaryInfoCollector):
    """
    Stores information needed for Lean verification, generated during the preprocessing phase.
    """

    prime: int
    preprocessor: Preprocessor
    function_dict: Dict[str, LeanRawFunctionInfo] = dataclasses.field(default_factory=lambda: {})
    const_expr: Dict[ScopedName, Tuple[Expression, int, List[ScopedName]]] = dataclasses.field(
        default_factory=lambda: {}
    )
    lean_temp_var_depth: int = 0

    # Used internally, when gathering information in the preprocessor.
    current_function: Optional[LeanRawFunctionInfo] = None
    labeled_jumps: Dict[int, LeanPreprocessedJumpToLabelInstruction] = dataclasses.field(
        default_factory=lambda: {}
    )

    @classmethod
    def create(cls, *args, **kwargs):
        return cls(*args, **kwargs)

    def start_function_info(
        self,
        name: str,
        start_pc: int,
        implicit_args_struct: StructDefinition,
        args_struct: StructDefinition,
        ret_type: Optional[CairoType],
    ):
        self.current_function = LeanRawFunctionInfo(
            name=name,
            id=len(self.function_dict),
            start_pc=start_pc,
            end_pc=0,
            call_dependencies=set(),
            implicit_args_struct=implicit_args_struct,
            args_struct=args_struct,
            ret_type=ret_type,
        )
        self.lean_temp_var_depth = 0

    def finish_function_info(self, end_pc: int, total_ap_change: RegChange):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        self.current_function.end_pc = end_pc
        self.current_function.total_ap_change = total_ap_change
        self.function_dict[self.current_function.name] = self.current_function
        self.current_function = None

    def start_function_retry(self):
        """
        Resets those parts of the function information which have to be collected again
        in case the preprocessor retries to process the function.
        """
        if self.current_function is None:
            return
        self.current_function.reset_upon_retry()

    def add_assert_eq(self, lhs, rhs):
        if self.current_function is None:
            return
        accessible_scopes = self.preprocessor.accessible_scopes.copy()
        if self.current_function.current_instr is None:
            self.current_function.lean_desc.append(
                LeanPreprocessedAssertEq(
                    accessible_scopes=accessible_scopes,
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    lhs=lhs,
                    rhs=rhs,
                )
            )
        elif (
            isinstance(self.current_function.current_instr, LeanPreprocessedCompoundAssertEq)
            or isinstance(self.current_function.current_instr, LeanPreprocessedTempVar)
            or isinstance(self.current_function.current_instr, LeanPreprocessedFuncCall)
            or isinstance(self.current_function.current_instr, LeanPreprocessedTailCall)
            or isinstance(self.current_function.current_instr, LeanPreprocessedReturn)
            or isinstance(self.current_function.current_instr, LeanPreprocessedIf)
        ):
            self.current_function.current_instr.asserts.append(
                LeanPreprocessedAssertEq(
                    accessible_scopes=accessible_scopes,
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    lhs=lhs,
                    rhs=rhs,
                )
            )

    def start_compound_assert_eq(self, lhs, rhs, resolved_type):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        self.current_function.current_instr = LeanPreprocessedCompoundAssertEq(
            accessible_scopes=self.preprocessor.accessible_scopes.copy(),
            flow_tracking_data=self.preprocessor.flow_tracking.data,
            lhs=lhs,
            rhs=rhs,
            resolved_type=resolved_type,
            asserts=[],
        )

    def finish_compound_assert_eq(self):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        assert (
            self.current_function.current_instr is not None
        ), "Verifier: expected an assert statement."
        self.current_function.lean_desc.append(self.current_function.current_instr)
        self.current_function.current_instr = None

    def add_reference(
        self,
        identifier: TypedIdentifier,
        resolved_type: CairoType,
        expr: Expression,
        identifier_loc: Optional[Location],
    ):
        if (
            identifier_loc != None
            and self.current_function is not None
            and self.current_function.current_instr == None
        ):
            self.current_function.lean_desc.append(
                LeanPreprocessedReference(
                    accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    identifier=identifier,
                    resolved_type=resolved_type,
                    expr=expr,
                    is_local_var=False,
                    asserts=[],
                )
            )

    def start_temp_var(
        self, identifier: TypedIdentifier, expr: Expression, identifier_loc: Optional[Location]
    ):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        # This function may be called several times when processing a tempvar
        # definition. We only want it to do anything the first time it is called.
        if identifier_loc != None:
            self.current_function.current_instr = LeanPreprocessedTempVar(
                accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                flow_tracking_data=self.preprocessor.flow_tracking.data,
                # The actual type is updated in finish_temp_var.
                identifier=identifier,
                resolved_type=TypeFelt(),
                add_ap_instr=None,  # Will be filled in later.
                expr=expr,
                asserts=[],
            )
            self.lean_temp_var_depth = 1
        elif (
            isinstance(self.current_function.current_instr, LeanPreprocessedTempVar)
            and self.lean_temp_var_depth > 0
        ):
            self.lean_temp_var_depth += 1
        elif isinstance(self.current_function.current_instr, LeanPreprocessedWithAsserts):
            if not isinstance(expr, ExprHint):
                return
            # This is a hint tempvar inside another instruction.
            self.current_function.current_instr.asserts.append(
                LeanPreprocessedTempVarAlloc(
                    accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    # The actual type is updated in finish_temp_var.
                    identifier=identifier,
                    resolved_type=TypeFelt(),
                    add_ap_instr=None,  # Will be filled in later.
                    expr=expr,
                )
            )
        else:
            raise Exception("Verifier: unexpected use of a tempvar.")

    def get_current_hint_tempvar(self) -> Optional[LeanPreprocessedTempVarAlloc]:
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        if (
            not isinstance(self.current_function.current_instr, LeanPreprocessedWithAsserts)
            or len(self.current_function.current_instr.asserts) == 0
        ):
            return None
        last_subinstr = self.current_function.current_instr.asserts[-1]
        if not isinstance(last_subinstr, LeanPreprocessedTempVarAlloc):
            return None
        return last_subinstr

    def finish_temp_var(self, resolved_type: CairoType):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        if isinstance(self.current_function.current_instr, LeanPreprocessedTempVar):
            self.lean_temp_var_depth -= 1
            if self.lean_temp_var_depth != 0:
                return
            self.current_function.current_instr.resolved_type = resolved_type
            self.current_function.lean_desc.append(self.current_function.current_instr)
            self.current_function.current_instr = None
        elif isinstance(self.current_function.current_instr, LeanPreprocessedWithAsserts):
            last_subinstr = self.get_current_hint_tempvar()
            if last_subinstr is None:
                # This is not a hint tempvar (but a temporary one, inside a compound expression).
                return
            last_subinstr.resolved_type = resolved_type
        else:
            raise Exception("Verifier: unexpected use of a tempvar.")

    def start_func_call(self, name, args):
        assert self.current_function is not None, "Verifier: expected to be inside a function."

        if self.current_function.name == name:
            self.current_function.is_recursive = True
        else:
            self.current_function.call_dependencies.add(name)
        # The current instruction may have already been set to a tail call.
        if self.current_function.current_instr is None:
            self.current_function.current_instr = LeanPreprocessedFuncCall(
                accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                flow_tracking_data=self.preprocessor.flow_tracking.data,
                name=name,
                func_args=args,
                ret_vars=[],
                asserts=[],
            )
        elif isinstance(self.current_function.current_instr, LeanPreprocessedTailCall):
            self.current_function.current_instr.name = name

    def finish_func_call(self):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        assert (
            self.current_function.current_instr is not None
        ), "Verifier: expected a function call statement."
        # If this takes place inside a tail call, we need to wait with closing
        # the handling of this function call until finish_tail_call is called
        # (as the 'return' part of the tail call still needs to be added).
        if not isinstance(self.current_function.current_instr, LeanPreprocessedTailCall):
            self.current_function.lean_desc.append(self.current_function.current_instr)
            self.current_function.current_instr = None

    def start_tail_call(self, args):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        # The name is not known when this called. It will later be set when
        # start_func_call is called for this function call.
        self.current_function.current_instr = LeanPreprocessedTailCall(
            accessible_scopes=self.preprocessor.accessible_scopes.copy(),
            flow_tracking_data=self.preprocessor.flow_tracking.data,
            name="",
            func_args=args,
            ret_vars=[],
            asserts=[],
        )
        # Remaining setup will take place when start_func_call is called.

    def finish_tail_call(self):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        assert (
            self.current_function.current_instr is not None
        ), "Verifier: expected a function call statement."
        self.current_function.lean_desc.append(self.current_function.current_instr)
        self.current_function.current_instr = None

    def add_func_ret_vars(self, ret_vars: List[str]):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        if self.current_function is not None and isinstance(
            self.current_function.lean_desc[-1], LeanPreprocessedFuncCall
        ):
            self.current_function.lean_desc[-1].ret_vars.extend(ret_vars)

    def start_return(self):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        self.current_function.current_instr = LeanPreprocessedReturn(
            accessible_scopes=self.preprocessor.accessible_scopes.copy(),
            flow_tracking_data=self.preprocessor.flow_tracking.data,
            asserts=[],
            ret_arg_exprs=[],
        )

    def finish_return(self, expr: Expression):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        assert isinstance(
            self.current_function.current_instr, LeanPreprocessedReturn
        ), "Verifier: expected to be at a return statement."
        self.current_function.lean_desc.append(self.current_function.current_instr)
        if isinstance(expr, ExprTuple):
            self.current_function.current_instr.ret_arg_exprs = [
                arg.expr for arg in expr.members.args
            ]
        else:
            self.current_function.current_instr.ret_arg_exprs = [expr]
        self.current_function.current_instr = None

    def record_label(self, label_full_name):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        self.current_function.label_dict[label_full_name] = len(self.current_function.lean_desc)

    def record_jump_to_labeled_instruction(self, label_name, condition, current_pc, pc_dest=None):
        # When this is called, the pc of the label may or may not be known (if it is not known,
        # this will be called later again).
        offset = pc_dest - current_pc if pc_dest is not None else None

        if current_pc not in self.labeled_jumps:
            assert self.current_function is not None, "Verifier: expected to be inside a function."
            jump_instr = LeanPreprocessedJumpToLabelInstruction(
                accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                flow_tracking_data=self.preprocessor.flow_tracking.data,
                label_name=label_name,
                offset=offset,
                pc_dest=pc_dest,
                condition=condition,
            )
            self.labeled_jumps[current_pc] = jump_instr
            current_instr = self.current_function.current_instr
            if not current_instr:
                self.current_function.lean_desc.append(jump_instr)
            elif isinstance(current_instr, LeanPreprocessedIf):
                current_instr.jump_instr = jump_instr
            else:
                raise Exception("Unexpected jump")
        else:
            self.labeled_jumps[current_pc].offset = offset
            self.labeled_jumps[current_pc].pc_dest = pc_dest

    def start_if(self, expr_a, expr_b, cond_eq):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        self.current_function.current_instr = LeanPreprocessedIf(
            accessible_scopes=self.preprocessor.accessible_scopes.copy(),
            flow_tracking_data=self.preprocessor.flow_tracking.data,
            expr_a=expr_a,
            expr_b=expr_b,
            cond_eq=cond_eq,
            asserts=[],
            jump_instr=None,
        )

    def end_if(self):
        assert self.current_function is not None, "Verifier: expected to be inside a function."
        assert (
            self.current_function.current_instr is not None
        ), "Verifier: expected to be at end of if block."
        self.current_function.lean_desc.append(self.current_function.current_instr)
        self.current_function.current_instr = None

    def get_const(self, e: Expression) -> Optional[int]:
        if isinstance(e, ExprCast):
            return self.get_const(e.expr)
        elif isinstance(e, ExprConst):
            return e.val
        else:
            return None

    def add_add_ap(self, expr: Expression):
        if self.current_function is None:
            return
        c = self.get_const(expr)
        if c is None:
            raise Exception("Non-integer value for ap +=")
        if self.current_function.current_instr is None:
            self.current_function.lean_desc.append(
                LeanPreprocessedAddAp(
                    accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    step=c,
                )
            )
        elif isinstance(self.current_function.current_instr, LeanPreprocessedTempVar):
            self.current_function.current_instr.add_ap_instr = LeanPreprocessedAddAp(
                accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                flow_tracking_data=self.preprocessor.flow_tracking.data,
                step=c,
            )
        elif isinstance(self.current_function.current_instr, LeanPreprocessedWithAsserts):
            if isinstance(self.current_function.current_instr, LeanPreprocessedTempVar):
                self.current_function.current_instr.add_ap_instr = LeanPreprocessedAddAp(
                    accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    step=c,
                )
            else:
                tempvar_instr = self.get_current_hint_tempvar()
                if tempvar_instr is None:
                    raise Exception("Unexpected ap +=")
                tempvar_instr.add_ap_instr = LeanPreprocessedAddAp(
                    accessible_scopes=self.preprocessor.accessible_scopes.copy(),
                    flow_tracking_data=self.preprocessor.flow_tracking.data,
                    step=c,
                )
        else:
            raise Exception("Unexpected ap +=")

    def add_const(self, name: ScopedName, expr: Expression, val: int):
        accessible_scopes = self.preprocessor.accessible_scopes.copy()
        self.const_expr[name] = (expr, val, accessible_scopes)
        if self.current_function is None:
            return
        self.current_function.lean_desc.append(
            LeanPreprocessedConst(
                accessible_scopes=accessible_scopes,
                flow_tracking_data=self.preprocessor.flow_tracking.data,
                name=name,
                val=val,
                expr=expr,
            )
        )
