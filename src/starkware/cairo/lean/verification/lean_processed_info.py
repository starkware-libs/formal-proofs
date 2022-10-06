import dataclasses
from dataclasses import InitVar
from typing import Dict, List, Optional, Set, Tuple

from starkware.cairo.lang.compiler.ast.cairo_types import CairoType, TypeTuple
from starkware.cairo.lang.compiler.ast.expr import Expression
from starkware.cairo.lang.compiler.identifier_definition import (
    ReferenceDefinition,
    StructDefinition,
)
from starkware.cairo.lang.compiler.identifier_manager import IdentifierManager
from starkware.cairo.lang.compiler.instruction import Register
from starkware.cairo.lang.compiler.preprocessor.flow import (
    FlowTrackingDataActual,
    FlowTrackingDataUnreachable,
    LostReferenceError,
    MissingReferenceError,
    ReferenceManager,
)
from starkware.cairo.lang.compiler.preprocessor.preprocessor import Preprocessor
from starkware.cairo.lang.compiler.preprocessor.reg_tracking import RegChangeKnown
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.expr_to_lean import (
    LeanDescContext,
    get_expr_identifier_full_names,
    get_fp_ref_offset,
    get_reg_ref,
    is_fp_ref,
    to_lean_description,
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
    LeanRawFunctionInfo,
    LeanRawProgramInfo,
)
from starkware.cairo.lean.verification.rc_builtin import RCBuiltin, init_rc_on_func
from starkware.cairo.lean.verification.type_to_lean import (
    LeanStructDefs,
    extract_embedded_struct_type_names,
    get_lean_type,
    get_lean_type_cast,
)
from starkware.cairo.lean.verification.var_info import LeanMemVarInfo, LeanRefVarInfo, LeanVarInfo


@dataclasses.dataclass
class LeanBlockInfo:
    flow_at_start: FlowTrackingDataActual
    label: ScopedName = ScopedName()
    arg_info: Dict[str, LeanVarInfo] = dataclasses.field(default_factory=lambda: {})
    flows_to: List[int] = dataclasses.field(default_factory=lambda: [])
    flows_from: List[int] = dataclasses.field(default_factory=lambda: [])

    def add_var_info(
        self,
        func_scope: ScopedName,
        open_namespaces: List[ScopedName],
        func_args: List[str],
        identifiers: IdentifierManager,
        references: ReferenceManager,
        desc_ctx: LeanDescContext,
    ):
        """
        Using the flow information for the beginning of the block, this function
        generates the variable information for all variables defined at the beginning
        of the block.
        """
        arg_info: Dict[str, LeanVarInfo] = {}
        for scoped_name in self.flow_at_start.reference_ids:
            if str(scoped_name[-1:]).startswith("__temp"):
                continue
            id_def = identifiers.get_by_full_name(scoped_name)
            assert isinstance(id_def, ReferenceDefinition), "Expected a reference definition."
            try:
                ref = self.flow_at_start.evaluate_reference(references, scoped_name)
            except MissingReferenceError:
                continue
            except LostReferenceError:
                continue
            reg_and_offset = get_reg_ref(ref)
            if reg_and_offset is None:
                # Expressions which are not an offset from a register are 'let' expressions.
                lean_expr = to_lean_description(
                    expr=ref,
                    context=dataclasses.replace(desc_ctx, cairo_type=id_def.cairo_type),
                )
                arg_info[str(scoped_name[-1:])] = LeanRefVarInfo(
                    cairo_type=id_def.cairo_type,
                    lean_type=get_lean_type(id_def.cairo_type, func_scope, open_namespaces),
                    cast=get_lean_type_cast(id_def.cairo_type, func_scope, open_namespaces, ""),
                    lean_expr=lean_expr,
                )
            else:
                reg, offset = reg_and_offset
                arg_info[str(scoped_name[-1:])] = LeanMemVarInfo(
                    cairo_type=id_def.cairo_type,
                    lean_type=get_lean_type(id_def.cairo_type, func_scope, open_namespaces),
                    cast=get_lean_type_cast(id_def.cairo_type, func_scope, open_namespaces, ""),
                    reg=reg,
                    offset=offset,
                )

        # Reorder the arguments so that the function arguments appear in the order
        # in which they appear in the function definition.
        for name in func_args:
            if name in arg_info:
                self.arg_info[name] = arg_info[name]
        for name, info in arg_info.items():
            self.arg_info[name] = info

    def get_arg_names(self) -> List[str]:
        return list(self.arg_info)

    def get_args_with_type(self) -> Dict[str, str]:
        """
        Returns a dictionary mapping the names of the block arguments to
        their types (in order).
        """
        return {name: var_info.lean_type for name, var_info in self.arg_info.items()}

    def get_arg_info_by_name(self, name: str) -> Optional[LeanVarInfo]:
        return self.arg_info[name] if name in self.arg_info else None

    def is_ap_arg(self, name: str) -> bool:
        if name not in self.arg_info:
            return False

        var_info = self.arg_info[name]
        return isinstance(var_info, LeanMemVarInfo) and var_info.reg == Register.AP

    def is_let_arg(self, name: str) -> bool:
        return name in self.arg_info and isinstance(self.arg_info[name], LeanRefVarInfo)


LEAN_RETURN_VAR_PREFIX = "ρ_"


@dataclasses.dataclass
class LeanFunctionInfo(LeanRawFunctionInfo):
    identifiers: IdentifierManager = dataclasses.field(default_factory=lambda: IdentifierManager())
    num_implicit_args: int = 0
    # All arguments, with the implicit arguments first.
    arg_names: List[str] = dataclasses.field(default_factory=lambda: [])
    ret_arg_names: List[str] = dataclasses.field(default_factory=lambda: [])
    ret_arg_types: List[CairoType] = dataclasses.field(default_factory=lambda: [])
    locals_by_offset: Dict[int, LeanPreprocessedReference] = dataclasses.field(
        default_factory=lambda: {}
    )
    labels_by_lean_desc_num: Dict[int, ScopedName] = dataclasses.field(default_factory=lambda: {})
    # The structure definitions, shared with all other functions.
    struct_defs: LeanStructDefs = dataclasses.field(default_factory=lambda: LeanStructDefs())
    # All constant definitions, shared with all other functions.
    const_expr: Dict[ScopedName, Tuple[Expression, int, List[ScopedName]]] = dataclasses.field(
        default_factory=lambda: {}
    )

    # Full names of constants referred to in this function which are not defined
    # within the scope of the function.
    external_consts: List[ScopedName] = dataclasses.field(default_factory=lambda: [])
    # The namespaces external to the function which the definitions used by the function
    # belong to. This does not include the namespace of the function itself or
    # the file it belongs to.
    imported_namespaces: Set[ScopedName] = dataclasses.field(default_factory=lambda: set())
    # The namespaces open in the generated Lean code.
    open_namespaces: List[ScopedName] = dataclasses.field(default_factory=lambda: [])

    # Object to handle the range check built-in.
    rc: Optional[RCBuiltin] = None
    # Block information.
    block_list: Dict[int, LeanBlockInfo] = dataclasses.field(default_factory=lambda: {})
    dependency_order: List[int] = dataclasses.field(default_factory=lambda: [])
    join_points: List[int] = dataclasses.field(default_factory=lambda: [])
    has_loop: bool = False

    def __post_init__(self):
        self.num_implicit_args = len(self.implicit_args_struct.members)
        # Relies on order remaining the same; guaranteed from Python 3.7 on
        # implicit arguments first.
        self.arg_names = list(self.implicit_args_struct.members) + list(self.args_struct.members)
        self.set_ret_args()
        self.rc = init_rc_on_func(self.arg_names)
        self.find_local_vars()
        self.prepare_local_vars()
        self.prepare_local_ret_vars()
        self.create_labels_by_lean_desc_num()
        self.collect_external_consts()
        self.add_to_struct_defs()
        self.set_imported_namespaces()
        self.set_open_namespaces()
        self.add_tuple_structs()

    @property
    def func_scope(self) -> ScopedName:
        return ScopedName.from_string(self.name)

    @property
    def has_const_ap_offset(self) -> bool:
        return isinstance(self.total_ap_change, RegChangeKnown)

    def get_total_ap_offset(self) -> int:
        return (
            self.total_ap_change.value if isinstance(self.total_ap_change, RegChangeKnown) else -1
        )

    def get_implicit_arg_names(self) -> List[str]:
        return list(self.implicit_args_struct.members)

    @property
    def arg_cairo_types(self) -> Dict[str, CairoType]:
        """
        The list of explicit arguments with their Cairo types.
        """
        return {name: member.cairo_type for name, member in self.args_struct.members.items()}

    @property
    def arg_lean_types(self) -> Dict[str, str]:
        """
        The list of explicit arguments with their Lean types.
        """
        return {
            name: get_lean_type(member.cairo_type, self.func_scope, self.open_namespaces)
            for name, member in self.args_struct.members.items()
        }

    @property
    def implicit_arg_lean_types(self) -> Dict[str, str]:
        """
        The list of implicit arguments with their Lean types.
        """
        return {
            name: get_lean_type(member.cairo_type, self.func_scope, self.open_namespaces)
            for name, member in self.implicit_args_struct.members.items()
        }

    def get_args_with_type(self, with_ret: bool) -> Dict[str, str]:
        """
        Returns a dictionary mapping the names of the function arguments to
        their types (in order). If with_ret is True, the return arguments are
        also included.
        """
        arg_types = dict(self.implicit_arg_lean_types)
        arg_types.update(self.arg_lean_types)
        if with_ret:
            arg_types.update(self.get_ret_args_with_type())
        return arg_types

    @property
    def num_returns(self) -> int:
        """
        Number of explicit return values.
        """
        return len(self.ret_arg_types)

    def get_ret_lean_types(self) -> List[str]:
        """
        Get the list of Lean types of the explicit return values.
        """
        return [
            get_lean_type(cairo_type, self.func_scope, self.open_namespaces)
            for cairo_type in self.ret_arg_types
        ]

    def get_ret_arg_names(self) -> List[str]:
        return [
            LEAN_RETURN_VAR_PREFIX + name for name in self.implicit_arg_lean_types
        ] + self.ret_arg_names

    def get_ret_args_with_type(self) -> Dict[str, str]:
        """
        Returns a dictionary mapping the names of the return arguments to
        their types (in order). This includes both the implicit and the explicit
        return arguments.
        """
        arg_types = {
            LEAN_RETURN_VAR_PREFIX + name: lean_type
            for name, lean_type in self.implicit_arg_lean_types.items()
        }
        explicit_ret_types = self.get_ret_lean_types()
        arg_types.update(
            {self.ret_arg_names[i]: lean_type for i, lean_type in enumerate(explicit_ret_types)}
        )
        return arg_types

    def add_types_to_ret_names(self, ret_names: List[str]) -> Dict[str, str]:
        """
        Returns the given return names (such as the names assigned to the return values
        by a calling function) aligned with the types of the corresponding return
        values.
        """
        ret_types = list(self.implicit_arg_lean_types.values()) + self.get_ret_lean_types()
        return {name: lean_type for name, lean_type in zip(ret_names, ret_types)}

    def local_var_names(self) -> Dict[int, str]:
        return {offset: i.identifier.identifier.name for offset, i in self.locals_by_offset.items()}

    def has_range_check(self) -> bool:
        return self.rc is not None

    # From here: processed information initialization functions.

    def set_ret_args(self):
        if self.ret_type is None:
            return
        if isinstance(self.ret_type, TypeTuple):
            for indx, member in enumerate(self.ret_type.members):
                self.ret_arg_names.append(
                    LEAN_RETURN_VAR_PREFIX + (member.name if member.name is not None else str(indx))
                )
                self.ret_arg_types.append(member.typ)
        else:
            self.ret_arg_names.append("ρ")
            self.ret_arg_types.append(self.ret_type)

    def find_local_vars(self):
        for inst in self.lean_desc:
            if not isinstance(inst, LeanPreprocessedReference):
                continue
            inst.is_local_var = is_fp_ref(inst.expr)
            if inst.is_local_var:
                ref_offset = get_fp_ref_offset(inst.expr)
                if ref_offset is not None:
                    self.locals_by_offset[ref_offset] = inst

    def prepare_local_vars(self):
        """
        Reorders the Lean description so that the reference to a local variable
        appears before the assert that defines it (if any) and not after
        """
        reordered = []
        for pos, inst in enumerate(self.lean_desc):
            reordered.append(inst)
            if pos == 0 or not isinstance(inst, LeanPreprocessedReference):
                continue
            prev = self.lean_desc[pos - 1]
            if not isinstance(prev, LeanPreprocessedCompoundAssertEq):
                continue
            if is_fp_ref(inst.expr) and inst.expr.format() == prev.lhs.format():
                reordered[-2] = inst
                reordered[-1] = prev

        self.lean_desc = reordered

    def prepare_local_ret_vars(self):
        """
        Explicit return values which are immediately assigned to a local variable
        are replaced by the local variable and the reference for this variable
        is assigned the assert which copies the value.
        """

        last_called = None
        lvars = self.local_var_names()
        new_lean_desc: List[LeanPreprocessedCodeElement] = []

        for inst in self.lean_desc:

            if isinstance(inst, LeanPreprocessedFuncCall):
                last_called = inst
            elif last_called is not None:
                if isinstance(inst, LeanPreprocessedCompoundAssertEq) and is_fp_ref(inst.lhs):
                    local = to_lean_description(expr=inst.lhs, local_vars=lvars)
                    desc = to_lean_description(expr=inst.rhs, local_vars=lvars)
                    prev = new_lean_desc[-1]
                    if (
                        desc in last_called.ret_vars
                        and isinstance(prev, LeanPreprocessedReference)
                        and prev.is_local_var
                        and prev.identifier.identifier.name == local
                    ):
                        # Replace the return variable with the local variable.
                        last_called.ret_vars = [
                            local if x == desc else x for x in last_called.ret_vars
                        ]
                        # Transfer the assert to the reference.
                        prev.asserts = inst.asserts
                        # Don't add the assert (the required steps belong to the reference now)
                        # insert a 'nop' instruction instead (we do not want to change the relative
                        # position of instructions).
                        inst = LeanPreprocessedNop([], FlowTrackingDataUnreachable())
                    else:
                        last_called = None
                elif not isinstance(inst, LeanPreprocessedReference) or not inst.is_local_var:
                    last_called = None

            new_lean_desc.append(inst)

        self.lean_desc = new_lean_desc

    def create_labels_by_lean_desc_num(self):
        self.labels_by_lean_desc_num = {num: label for label, num in self.label_dict.items()}

    def collect_external_consts(self):
        """
        Finds all consts referred to by this function which are defined outside
        of it.
        """
        for instr in self.lean_desc:
            for expr in instr.get_exprs():
                self.external_consts += [
                    name
                    for name in get_expr_identifier_full_names(
                        expr, self.identifiers, instr.accessible_scopes
                    )
                    if not name in self.external_consts and not name.startswith(self.func_scope)
                ]

        # Add the constants used in the definitions of these constants.
        sub_consts: List[ScopedName] = []
        for const_name in self.external_consts:
            const_sub_consts = get_sub_consts(
                const_name=const_name,
                const_expr=self.const_expr,
                identifiers=self.identifiers,
            )
            sub_consts = const_sub_consts + [
                name for name in sub_consts if name not in const_sub_consts
            ]

        self.external_consts = sub_consts + [
            name for name in self.external_consts if name not in sub_consts
        ]

    def get_all_types_used(self) -> List[CairoType]:
        """
        Return the list of all types used in this function. Some may be duplicates.
        """
        types = (
            [member.cairo_type for member in self.implicit_args_struct.members.values()]
            + [member.cairo_type for member in self.args_struct.members.values()]
            + self.ret_arg_types
        )

        for instr in self.lean_desc:
            if isinstance(instr, LeanPreprocessedReference) or isinstance(
                instr, LeanPreprocessedTempVarAlloc
            ):
                types.append(instr.resolved_type)

        return types

    def get_referred_structs(self) -> List[ScopedName]:
        """
        Return the scoped names of all structure definitions used by the function.
        """
        struct_names: List[ScopedName] = []

        for type in self.get_all_types_used():
            names = extract_embedded_struct_type_names(type)
            for name in names:
                if name not in struct_names:
                    struct_names.append(name)

        return struct_names

    def add_tuple_structs(self):
        for type in self.get_all_types_used():
            if isinstance(type, TypeTuple):
                self.struct_defs.add_tuple_struct(
                    tuple=type, func_scope=self.func_scope, open_namespaces=self.open_namespaces
                )

    def add_to_struct_defs(self):
        """
        This function adds the structure definitions used by the arguments and variables
        of this function to the list of structure definitions which needs to be generated.
        """
        for struct_name in self.get_referred_structs():
            self.struct_defs.try_add_by_name(struct_name)
        self.struct_defs.add_sub_structs()

    def set_imported_namespaces(self):

        no_import_scope = self.func_scope[:-1]

        self.imported_namespaces = set(
            name[:-1]
            for name in filter(lambda x: not x.startswith(no_import_scope), self.external_consts)
        )
        self.imported_namespaces = self.imported_namespaces.union(
            name[:-1]
            for name in filter(
                lambda x: not x.startswith(no_import_scope),
                self.struct_defs.get_sub_structs(self.get_referred_structs()),
            )
        )
        self.imported_namespaces = self.imported_namespaces.union(
            func_dep[:-1]
            for func_dep in filter(
                lambda x: not x.startswith(no_import_scope),
                [ScopedName.from_string(dep) for dep in self.call_dependencies],
            )
        )

    def set_open_namespaces(self):
        self.open_namespaces = [self.func_scope[:-1]] + list(self.imported_namespaces)


LEAN_IGNORE_CONSTS = ["SIZEOF_LOCALS"]


@dataclasses.dataclass
class LeanProgramInfo:
    """
    Stores information needed for Lean verification, generated during the preprocessing phase.
    """

    prime: int
    main_scope: ScopedName
    preprocessor: Preprocessor
    identifiers: IdentifierManager
    reference_manager: ReferenceManager
    function_dict: Dict[str, LeanFunctionInfo] = dataclasses.field(default_factory=lambda: {})
    # Structures referred to in the functions.
    struct_defs: LeanStructDefs = dataclasses.field(default_factory=lambda: LeanStructDefs())
    # Constant definitions.
    const_expr: Dict[ScopedName, Tuple[Expression, int, List[ScopedName]]] = dataclasses.field(
        default_factory=lambda: {}
    )
    imported_scopes: Set[ScopedName] = dataclasses.field(default_factory=lambda: set())
    program_info: InitVar[LeanRawProgramInfo] = None
    func_select: InitVar[Optional[List[str]]] = None

    def __post_init__(self, program_info: LeanRawProgramInfo, func_select: Optional[List[str]]):
        self.struct_defs.set_identifiers(self.identifiers)
        self.const_expr = program_info.const_expr
        self.preprocess_program_info(program_info, func_select)

    @property
    def all_funcs(self) -> List[LeanFunctionInfo]:
        return list(self.function_dict.values())

    @property
    def main_scope_funcs(self) -> List[LeanFunctionInfo]:
        """
        Returns the list of functions which are defined in the main scope.
        """
        return list(
            filter(
                lambda fn: fn.func_scope.startswith(self.main_scope), self.function_dict.values()
            )
        )

    @property
    def non_main_scope_funcs(self) -> List[LeanFunctionInfo]:
        """
        Returns the list of functions which are not defined in the main scope.
        """
        return list(
            filter(
                lambda fn: not fn.func_scope.startswith(self.main_scope),
                self.function_dict.values(),
            )
        )

    def is_in_func_scope(self, name: ScopedName) -> bool:
        """
        Returns true if the given name is inside the scope of one of the functions
        (this means it is defined inside the function).
        """
        return any(name.startswith(func.func_scope) for func in self.all_funcs)

    @property
    def main_scope_consts(
        self,
    ) -> Dict[ScopedName, List[Tuple[str, Expression, List[ScopedName]]]]:
        """
        Returns the constant definitions which are defined in the main scope or in a sub-scope
        of the main scope (for example, inside a function defined in the main scope).
        The definitions are returned sorted by scope.
        """
        all_consts = self.get_const_defs_by_namespace()
        return {
            scope: all_consts[scope]
            for scope in filter(lambda scope: scope.startswith(self.main_scope), all_consts.keys())
        }

    @property
    def non_main_scope_consts(
        self,
    ) -> Dict[ScopedName, List[Tuple[str, Expression, List[ScopedName]]]]:
        """
        Returns the constant definitions which are defined outside the main scope
        (that is, also not in a sub-scopes of the main scope). These are the constants
        that need to be imported. Constants defined inside functions outside of the main
        scope are excluded.
        """
        all_consts = self.get_const_defs_by_namespace()
        return {
            scope: all_consts[scope]
            for scope in filter(
                lambda scope: not scope.startswith(self.main_scope)
                and not self.is_in_func_scope(scope),
                all_consts.keys(),
            )
        }

    def get_const_defs_by_namespace(
        self,
    ) -> Dict[ScopedName, List[Tuple[str, Expression, List[ScopedName]]]]:
        """
        Returns the constants sorted by their namespace (prefix of their scoped
        name).
        """
        by_namespace: Dict[ScopedName, List[Tuple[str, Expression, List[ScopedName]]]] = {}
        for name, (expr, _, accessible_scopes) in self.const_expr.items():
            if str(name[-1:]) in LEAN_IGNORE_CONSTS:
                continue
            if name[:-1] in by_namespace:
                by_namespace[name[:-1]].append((str(name[-1:]), expr, accessible_scopes))
            else:
                by_namespace[name[:-1]] = [(str(name[-1:]), expr, accessible_scopes)]
        return by_namespace

    @property
    def main_scope_structs(self) -> Dict[ScopedName, List[StructDefinition]]:
        """
        Returns the structure definitions which are defined in the main scope or in a sub-scope
        of the main scope (for example, inside a function defined in the main scope).
        The definitions are returned sorted by scope.
        """
        all_structs = self.get_structs_by_namespace()
        return {
            scope: all_structs[scope]
            for scope in filter(lambda scope: scope.startswith(self.main_scope), all_structs.keys())
        }

    @property
    def non_main_scope_structs(self) -> Dict[ScopedName, List[StructDefinition]]:
        """
        Returns the structure definitions which are defined outside the main scope
        (that is, also not in a subs-scope of the main scope). These are the structure
        definitions that need to be imported. Structures defined inside functions outside
        of the main scope are excluded.
        """
        all_structs = self.get_structs_by_namespace()
        return {
            scope: all_structs[scope]
            for scope in filter(
                lambda scope: not scope.startswith(self.main_scope)
                and not self.is_in_func_scope(scope),
                all_structs.keys(),
            )
        }

    def get_structs_by_namespace(self) -> Dict[ScopedName, List[StructDefinition]]:
        return self.struct_defs.get_structs_by_namespace()

    @property
    def open_namespaces(self) -> List[ScopedName]:
        """
        List of all namespaces which are opened in the Lean files generated.
        """
        return [self.main_scope] + list(self.imported_scopes)

    # From here: initialization functions.

    def preprocess_program_info(
        self,
        program_info: LeanRawProgramInfo,
        func_select: Optional[List[str]],
    ):
        dep_sorted_function_dict = topo_sort_funcs_by_deps(program_info.function_dict)
        if func_select is not None:
            dep_sorted_function_dict = self.select_funcs_with_dependencies(
                func_select,
                dep_sorted_function_dict,
            )

        for name, func in dep_sorted_function_dict.items():
            self.function_dict[name] = LeanFunctionInfo(
                name=func.name,
                id=func.id,
                start_pc=func.start_pc,
                end_pc=func.end_pc,
                implicit_args_struct=func.implicit_args_struct,
                args_struct=func.args_struct,
                ret_type=func.ret_type,
                ret_arg_names=[],
                ret_arg_types=[],
                call_dependencies=func.call_dependencies,
                total_ap_change=func.total_ap_change,
                is_recursive=func.is_recursive,
                lean_desc=func.lean_desc,
                label_dict=func.label_dict,
                identifiers=self.identifiers,
                struct_defs=self.struct_defs,
                const_expr=self.const_expr,
            )
        self.reset_main_scope(self.main_scope)

    def select_funcs_with_dependencies(
        self, func_select: List[str], dep_sorted_function_dict: Dict[str, LeanRawFunctionInfo]
    ) -> Dict[str, LeanRawFunctionInfo]:
        """
        Extracts out of a list of functions, already sorted by dependency, the functions
        that appear in the selection list, together with the functions they depend on.
        """
        selected_function_dict = dict(
            filter(lambda item: item[0] in func_select, dep_sorted_function_dict.items())
        )
        deps: Set[str] = set()
        for func in selected_function_dict.values():
            deps = deps.union(func.call_dependencies)
        return dict(
            filter(
                lambda item: item[0] in func_select + list(deps),
                dep_sorted_function_dict.items(),
            )
        )

    def reset_main_scope(self, main_scope: ScopedName):
        self.main_scope = main_scope
        self.set_imported_scopes()

    def set_imported_scopes(self):
        self.imported_scopes = set()
        for func in self.main_scope_funcs:
            self.imported_scopes = self.imported_scopes.union(func.imported_namespaces)

        self.imported_scopes = self.imported_scopes.union(
            set(
                sub_struct[:-1]
                for sub_struct in filter(
                    lambda x: not x.startswith(self.main_scope),
                    self.struct_defs.get_sub_structs(list(self.main_scope_structs.keys())),
                )
            )
        )

        for scope, consts in self.main_scope_consts.items():
            for name, _, _ in consts:
                self.imported_scopes = self.imported_scopes.union(
                    sub_const[:-1]
                    for sub_const in filter(
                        lambda x: not x.startswith(self.main_scope),
                        get_sub_consts(
                            const_name=scope + ScopedName.from_string(name),
                            const_expr=self.const_expr,
                            identifiers=self.identifiers,
                        ),
                    )
                )


def topo_sort_funcs_by_deps(
    raw_funcs: Dict[str, LeanRawFunctionInfo]
) -> Dict[str, LeanRawFunctionInfo]:
    """
    Sorts the functions topologically relative to their dependencies (function
    follows all functions it depends on). Duplicates each function entry and
    adds the indirect dependencies to it.
    """
    sorted_funcs: Dict[str, LeanRawFunctionInfo] = {}
    for name, _ in raw_funcs.items():
        topo_sort_func_deps(name, raw_funcs=raw_funcs, sorted_funcs=sorted_funcs)

    return sorted_funcs


def topo_sort_func_deps(
    name: str,
    raw_funcs: Dict[str, LeanRawFunctionInfo],
    sorted_funcs: Dict[str, LeanRawFunctionInfo],
):
    if name in sorted_funcs:
        return

    func = dataclasses.replace(
        raw_funcs[name], call_dependencies=set(raw_funcs[name].call_dependencies)
    )

    for dep in raw_funcs[name].call_dependencies:
        topo_sort_func_deps(dep, raw_funcs=raw_funcs, sorted_funcs=sorted_funcs)
        func.call_dependencies = func.call_dependencies.union(sorted_funcs[dep].call_dependencies)

    sorted_funcs[name] = func



def get_sub_consts(
    const_name: ScopedName,
    const_expr: Dict[ScopedName, Tuple[Expression, int, List[ScopedName]]],
    identifiers: IdentifierManager,
) -> List[ScopedName]:
    """
    Returns the full name of all constants used in the definition of the given constant.
    The returned set is topologically sorted.
    """
    if const_name not in const_expr:
        return []

    expr, _, accessible_scopes = const_expr[const_name]
    sub_consts = get_expr_identifier_full_names(expr, identifiers, accessible_scopes)

    for sub_const in sub_consts:
        const_sub_consts = get_sub_consts(
            const_name=sub_const, const_expr=const_expr, identifiers=identifiers
        )
        sub_consts = const_sub_consts + [
            name for name in sub_consts if name not in const_sub_consts
        ]

    return sub_consts


def get_instr_trace_count(instr: LeanPreprocessedCodeElement) -> int:
    """
    Returns the length of the trace required for the execution of this instruction.
    These may be compound instructions, compiled into more than one machine instruction.
    """
    if isinstance(instr, LeanPreprocessedAddAp):
        return 1
    if isinstance(instr, LeanPreprocessedAssertEq):
        return 1
    if isinstance(instr, LeanPreprocessedConst) or isinstance(instr, LeanPreprocessedNop):
        return 0

    count = 0

    if isinstance(instr, LeanPreprocessedWithAsserts):
        # We only count here the asserts/ap+= associated with the instruction, while
        # the count for the instruction itself is added below.
        count += len(
            [
                asrt
                for asrt in instr.asserts
                if isinstance(asrt, LeanPreprocessedAssertEq)
                or (
                    isinstance(asrt, LeanPreprocessedTempVarAlloc) and asrt.add_ap_instr is not None
                )
            ]
        )

    if isinstance(instr, LeanPreprocessedCompoundAssertEq) or isinstance(
        instr, LeanPreprocessedReference
    ):
        return count
    if isinstance(instr, LeanPreprocessedTempVar):
        return count + (1 if instr.add_ap_instr else 0)
    if isinstance(instr, LeanPreprocessedFuncCall):
        # A tail call is a call together with a return and therefore adds 2 to the count.
        return count + (2 if isinstance(instr, LeanPreprocessedTailCall) else 1)
    if isinstance(instr, LeanPreprocessedIf):
        return count + 1
    if isinstance(instr, LeanPreprocessedJumpToLabelInstruction):
        return count + 1
    if isinstance(instr, LeanPreprocessedReturn):
        return count + 1

    raise Exception("Could not determine trace count of instruction.")
