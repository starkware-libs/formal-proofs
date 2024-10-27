import dataclasses
from typing import Dict, List, Optional, Tuple

from starkware.cairo.lang.compiler.ast.cairo_types import (
    CairoType,
    TypeFelt,
    TypePointer,
    TypeStruct,
    TypeTuple,
)
from starkware.cairo.lang.compiler.identifier_definition import (
    DefinitionError,
    MemberDefinition,
    StructDefinition,
)
from starkware.cairo.lang.compiler.identifier_manager import (
    IdentifierManager,
    MissingIdentifierError,
)
from starkware.cairo.lang.compiler.identifier_utils import get_struct_definition
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.scope_to_lean import get_name_in_open_scopes

LEAN_STRUCT_PTR_PREFIX = "π_"
LEAN_CAST_PREFIX = "cast_"
LEAN_STRUCT_OFFSET_PREFIX = "φ_"


def extract_embedded_struct_type_names(type: CairoType) -> List[ScopedName]:
    """
    Returns the full names of the top-level structure(s) which are embedded inside
    the given type. Sub-structures of these structures are not returned.
    """
    if isinstance(type, TypeStruct):
        return [type.scope]
    if isinstance(type, TypePointer):
        return extract_embedded_struct_type_names(type.pointee)
    if isinstance(type, TypeTuple):
        names: List[ScopedName] = []
        for member in type.members:
            names += extract_embedded_struct_type_names(member.typ)
        return names
    return []


def get_lean_type(
    cairo_type: CairoType,
    scope: ScopedName,
    open_namespaces: List[ScopedName],
) -> str:
    """
    Given a CairoType object, this function returns the corresponding
    Lean type. For types which are not built-in types, the type name is given
    relative to the list of open namespaces.
    The scope is the scope in which the type is used.
    """
    if isinstance(cairo_type, TypeFelt):
        return "F"
    if isinstance(cairo_type, TypeStruct):
        return get_name_in_open_scopes(cairo_type.scope, open_namespaces) + " F"
    if isinstance(cairo_type, TypePointer):
        if isinstance(cairo_type.pointee, TypeStruct):
            return (
                get_name_in_open_scopes(
                    cairo_type.pointee.scope, open_namespaces, LEAN_STRUCT_PTR_PREFIX
                )
                + " F"
            )
        return "F"  # Other pointers are, for now, just F.

    if isinstance(cairo_type, TypeTuple):
        # Assumes the tuple can only be defined in the scope (function) that uses it.
        return (
            get_name_in_open_scopes(
                scope + ScopedName.from_string(mk_tuple_name(cairo_type, open_namespaces)),
                open_namespaces,
            )
            + " F"
        )

    raise Exception("Verifier: unsupported type.")


def get_lean_type_cast(
    cairo_type: CairoType,
    scope: Optional[ScopedName],
    open_namespaces: List[ScopedName],
    end_separator: str = "",
) -> str:
    """
    Given a CairoType object, this function returns the Lean cast function
    for this type (this is the function that casts a memory pointer to this type).
    The cairo type is expected to be fully resolved.
    The scope is the scope in which the cast is used.
    When no cast is necessary, this function returns an empty string.
    The cast function name is given relative to the longest open namespace which is
    a prefix of the type scope.
    If the cast function is not empty, the end separator is concatenated at the end.
    """
    if isinstance(cairo_type, TypeFelt):
        return ""
    if isinstance(cairo_type, TypeStruct):
        return (
            get_name_in_open_scopes(cairo_type.scope, open_namespaces, LEAN_CAST_PREFIX)
            + end_separator
        )
    if isinstance(cairo_type, TypePointer):
        if isinstance(cairo_type.pointee, TypeStruct):
            return (
                get_name_in_open_scopes(
                    cairo_type.pointee.scope,
                    open_namespaces,
                    LEAN_CAST_PREFIX + LEAN_STRUCT_PTR_PREFIX,
                )
                + end_separator
            )
        return ""  # Other pointers are, for now, just F.
    if isinstance(cairo_type, TypeTuple):
        if scope is None:
            raise Exception("Verifier: cannot cast tuple without scope.")
        return (
            get_name_in_open_scopes(
                scope + ScopedName.from_string(mk_tuple_name(cairo_type, open_namespaces)),
                open_namespaces,
                LEAN_CAST_PREFIX,
            )
            + end_separator
        )

    raise Exception("Verifier: unsupported type.")


def mk_tuple_name(tuple: TypeTuple, open_namespaces: List[ScopedName]) -> str:
    type_str = "τ"  # Every tuple type name begins with the symbol.

    end_char = "ₑ"  # Character indicating the end of a member.

    subscript_trans = "".maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

    for indx, member in enumerate(tuple.members):
        if member.name is not None:
            type_str += member.name
        type_str += str(indx).translate(subscript_trans)
        type_str += mk_type_name(member.typ, open_namespaces)
        type_str += end_char

    return type_str


def mk_type_name(type: CairoType, open_namespaces: List[ScopedName]) -> str:
    """
    Returns a string which is a valid Lean identifier and which uniquely identifies
    the given type. Structure names may be given relative to the open namespaces.
    """
    sep_char = "ₛ"  # Separator between strings in a scoped name.
    pointer_char = "π"  # Prefix character to indicate a pointer type.
    if isinstance(type, TypeTuple):
        return mk_tuple_name(type, open_namespaces)
    elif isinstance(type, TypeStruct):
        return get_name_in_open_scopes(type.scope, open_namespaces).replace(".", sep_char)
    elif isinstance(type, TypePointer):
        return pointer_char + mk_type_name(type.pointee, open_namespaces)
    elif isinstance(type, TypeFelt):
        return ""

    raise Exception("Cannot create name for unsupported type.")


def create_arg_defs(typed_args: Dict[str, str]) -> List[str]:
    """
    Given a list of argument names and their types, this function returns
    the Lean definition for these arguments with the given types. The order
    of the arguments is preserved and the consecutive arguments of the same
    type are grouped together.
    """
    defs = []
    prev_type = None
    names = []
    for name, arg_type in typed_args.items():
        if arg_type == prev_type:
            names.append(name)
        else:
            if len(names) > 0:
                defs.append(f'({" ".join(names)} : {prev_type})')
            names = [name]
            prev_type = arg_type

    if len(names) > 0:
        defs.append(f'({" ".join(names)} : {prev_type})')

    return defs


@dataclasses.dataclass
class LeanStructDefs:
    """
    This class collects structure definitions used in the Cairo code and can then
    be used to generate the Lean definitions of the corresponding Lean structures.
    """

    identifiers: IdentifierManager = dataclasses.field(default_factory=lambda: IdentifierManager())
    names: Dict[ScopedName, StructDefinition] = dataclasses.field(default_factory=lambda: {})
    unique_tuple_names: Dict[str, List[ScopedName]] = dataclasses.field(default_factory=lambda: {})

    def set_identifiers(self, identifiers: IdentifierManager):
        self.identifiers = identifiers

    def try_get_struct_definition(self, name: ScopedName) -> Optional[StructDefinition]:
        """
        Return the structure definition if the name refers to a structure and otherwise
        return None.
        """
        try:
            return get_struct_definition(name, self.identifiers)
        except MissingIdentifierError:
            return None
        except DefinitionError:
            return None

    def try_add_by_name(self, name: ScopedName) -> bool:
        """
        Adds the name to the list of structures if the name is indeed that of
        of a structure definition. Returns True if added and False if not.
        """
        if name in self.names:
            return True
        struct_def = self.try_get_struct_definition(name)
        if struct_def is not None:
            self.names[name] = struct_def
            return True
        return False

    def try_add_by_type(self, cairo_type: CairoType) -> bool:
        """
        If the cairo type is a structure type or a pointer to structure type,
        adds the structure to the list of structures stored on this object.
        Returns True if added and False if not.
        """
        if isinstance(cairo_type, TypeFelt):
            return False
        if isinstance(cairo_type, TypeStruct):
            return self.try_add_by_name(cairo_type.scope)
        if isinstance(cairo_type, TypePointer):
            # Add the structure, if needed.
            return self.try_add_by_type(cairo_type.pointee)
        return False

    def try_add_members(self, args_struct: StructDefinition):
        """
        Tries to add the types of the members of the structure
        """
        for member in args_struct.members.values():
            self.try_add_by_type(member.cairo_type)

    def add_sub_structs(self):
        """
        Adds all structure definitions embedded inside structure definitions already stored
        in the table. The resulting table is topologically sorted so that sub-structures
        appear before the structures that use them.
        """
        top_structs = self.names
        self.names = {}
        # First add the sub-structures.
        for struct_def in self.names.values():
            self.try_add_members(struct_def)
        # Add back the remaining structures.
        self.names.update(top_structs)

        if len(top_structs) < len(self.names):
            self.add_sub_structs()

    def add_tuple_struct(
        self, tuple: TypeTuple, func_scope: ScopedName, open_namespaces: List[ScopedName]
    ):
        """
        Adds the structure definition for the given tuple. The scope of the function in
        which the tuple is defined and the namespaces which are open in the context of this
        function should be provided.
        """
        # Unique name (independent of context)
        unique_name = mk_tuple_name(tuple, [])
        # Shorter name, but in scope.
        name = func_scope + ScopedName.from_string(mk_tuple_name(tuple, open_namespaces))
        if name in self.names:
            return
        members = {}
        offset = 0
        for indx, member in enumerate(tuple.members):
            member_name = member.name if member.name is not None else "μ" + str(indx)
            members[member_name] = MemberDefinition(offset=offset, cairo_type=member.typ)
            if isinstance(member.typ, TypeTuple):
                self.add_tuple_struct(
                    tuple=member.typ,
                    func_scope=func_scope,
                    open_namespaces=open_namespaces,
                )
            offset += self.get_type_size(member.typ)

        self.names[name] = StructDefinition(
            full_name=name,
            members=members,
            size=offset,
        )

        if unique_name in self.unique_tuple_names:
            self.unique_tuple_names[unique_name].append(name)
        else:
            self.unique_tuple_names[unique_name] = [name]

    def get_struct_by_resolved_type(self, cairo_type: CairoType) -> Optional[StructDefinition]:
        if not isinstance(cairo_type, TypeStruct) or not cairo_type.scope in self.names:
            return None
        return self.names[cairo_type.scope]

    def get_member_type(self, resolved_type: CairoType, member_name: str) -> CairoType:
        if (
            not isinstance(resolved_type, TypeStruct)
            # or not resolved_type.is_fully_resolved
            or not resolved_type.scope in self.names
            or not member_name in self.names[resolved_type.scope].members
        ):
            raise Exception("Cannot determine member type.")
        return self.names[resolved_type.scope].members[member_name].cairo_type

    def get_structs_by_namespace(self) -> Dict[ScopedName, List[StructDefinition]]:
        """
        Returns the structures sorted by their namespace (prefix of their scoped
        name).
        """
        by_namespace: Dict[ScopedName, List[StructDefinition]] = {}
        for name, struct_def in self.names.items():
            if name[:-1] in by_namespace:
                by_namespace[name[:-1]].append(struct_def)
            else:
                by_namespace[name[:-1]] = [struct_def]
        return by_namespace

    def get_type_size(self, resolved_type: CairoType) -> int:
        """
        Given a type, this function returns the size of that type. The type should be
        fully resolved.
        """
        if isinstance(resolved_type, TypeStruct):
            # if not resolved_type.is_fully_resolved or resolved_type.scope not in self.names:
            if resolved_type.scope not in self.names:
                raise Exception("Failed to determine size of structure type.")
            return self.names[resolved_type.scope].size

        if isinstance(resolved_type, TypeTuple):
            unique_name = mk_tuple_name(resolved_type, [])
            if unique_name not in self.unique_tuple_names:
                raise Exception("Failed to determine size of a tuple type.")
            # All structure definitions for the same tuple have the same size.
            return self.names[self.unique_tuple_names[unique_name][0]].size

        return 1

    def get_arg_types_offsets_and_casts(
        self,
        func_scope: ScopedName,
        args_struct: StructDefinition,
        end_offset: int,
        open_namespaces: List[ScopedName],
        cast_end_separator: str,
    ) -> Dict[str, Tuple[CairoType, int, str]]:
        """
        Given a structure describing the arguments of a function, this function
        returns the offsets of the arguments (based on their type) and the cast
        function needed to cast to their type from a field element pointer.
        The offsets are given relative to the provided end offset (which is
        the offset after the last argument).
        """
        offsets_and_casts = {}
        for name, member in reversed(list(args_struct.members.items())):
            end_offset -= self.get_type_size(member.cairo_type)
            cast = get_lean_type_cast(
                member.cairo_type, func_scope, open_namespaces, cast_end_separator
            )
            offsets_and_casts[name] = (member.cairo_type, end_offset, cast)

        return {
            name: offset_and_cast
            for name, offset_and_cast in reversed(list(offsets_and_casts.items()))
        }

    def get_offsets_and_casts_by_types(
        self,
        scope: ScopedName,
        types: List[CairoType],
        end_offset: int,
        open_namespaces: List[ScopedName],
        cast_end_separator: str,
    ) -> List[Tuple[CairoType, int, str]]:
        """
        Returns the sequence of offsets corresponding to a sequence of arguments
        whose types are given and the casts needed to convert them from the field
        pointer. The tuples returned also store the cairo type.
        The offsets are relative to the end offset, which is the offset after
        the last argument.
        """
        offsets_etc = []
        for cairo_type in reversed(types):
            end_offset -= self.get_type_size(cairo_type)
            cast = get_lean_type_cast(cairo_type, scope, open_namespaces, cast_end_separator)
            offsets_etc.append((cairo_type, end_offset, cast))

        return list(reversed(offsets_etc))

    def get_struct_offset_def_names(
        self,
        cairo_type: CairoType,
        open_namespaces: List[ScopedName],
    ) -> List[str]:
        """
        Returns the names of the member offset definitions, if the given type is
        the fully resolved name of a structure or pointer to a structure.
        The names are given relative to the given open namespaces (relative to
        the longest namespace which is a prefix of each name).
        """
        if isinstance(cairo_type, TypePointer):
            return self.get_struct_offset_def_names(cairo_type.pointee, open_namespaces)
        if not isinstance(cairo_type, TypeStruct):
            return []
        if not cairo_type.scope in self.names:
            return []
        offset_name = get_name_in_open_scopes(
            cairo_type.scope, open_namespaces, LEAN_STRUCT_OFFSET_PREFIX
        )
        return [
            offset_name + "." + member_name for member_name in self.names[cairo_type.scope].members
        ]

    def get_rec_types(
        self,
        cairo_type: CairoType,
    ) -> List[CairoType]:
        """
        Given a Cairo type, this function returns a list consisting of the type
        itself (if it is a structure or pointer to a structure) and the types
        embedded inside it. If the type is not a structure (or pointer to
        a structure), this function returns an empty list.
        The returned list may contain duplicate types.
        """
        rec_types: List[CairoType] = [cairo_type]
        if isinstance(cairo_type, TypePointer):
            pointee_types = self.get_rec_types(cairo_type.pointee)
            return rec_types + pointee_types[1:] if 0 < len(pointee_types) else []
        if not isinstance(cairo_type, TypeStruct):
            return []
        if not cairo_type.scope in self.names:
            return []
        for member in self.names[cairo_type.scope].members.values():
            rec_types += self.get_rec_types(member.cairo_type)
        return rec_types

    def get_sub_structs_of_type(self, cairo_type: CairoType) -> List[ScopedName]:
        """
        Returns the names of all structures which are embedded in the given type.
        If the type itself is a structure, it is included. If the type is not a structure
        and does not embed structures, an empty list is returned.
        """

        if isinstance(cairo_type, TypePointer):
            return self.get_sub_structs_of_type(cairo_type.pointee)
        if not isinstance(cairo_type, TypeStruct):
            return []
        if not cairo_type.scope in self.names:
            return []

        struct_names: List[ScopedName] = [cairo_type.scope]
        for member in self.names[cairo_type.scope].members.values():
            struct_names += [
                name
                for name in self.get_sub_structs_of_type(member.cairo_type)
                if name not in struct_names
            ]
        return struct_names

    def get_sub_structs(self, names: List[ScopedName]) -> List[ScopedName]:
        """
        Given the fully resolved names of some structures, returns those names
        which are stored in this object, together with the names of their sub-structures.
        """
        struct_names: List[ScopedName] = []
        for name in names:
            if name not in self.names:
                continue
            struct_names.append(name)
            for member in self.names[name].members.values():
                struct_names += [
                    name
                    for name in self.get_sub_structs_of_type(member.cairo_type)
                    if name not in struct_names
                ]
        return struct_names

    def get_lean_type_cast_rec(
        self,
        scope: ScopedName,
        cairo_types: List[CairoType],
        open_namespaces: List[ScopedName],
        end_separator: str = "",
    ) -> List[str]:
        """
        Returns the Lean casts for all structures in the input types, including the casts for
        sub-structures.
        """
        all_casts: List[str] = []
        for type in cairo_types:
            for rec_type in self.get_rec_types(type):
                cast = get_lean_type_cast(
                    scope=scope,
                    cairo_type=rec_type,
                    open_namespaces=open_namespaces,
                    end_separator=end_separator,
                )
                if 0 < len(cast) and not cast in all_casts:
                    all_casts.append(cast)

        return all_casts
