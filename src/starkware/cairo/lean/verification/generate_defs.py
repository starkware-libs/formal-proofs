import re
from typing import List, Optional, Tuple

from starkware.cairo.lang.compiler.ast.cairo_types import TypeFelt
from starkware.cairo.lang.compiler.ast.expr import Expression
from starkware.cairo.lang.compiler.identifier_definition import StructDefinition
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.expr_to_lean import (
    LeanDescContext,
    LeanExprSimplifier,
    to_lean_description,
)
from starkware.cairo.lean.verification.generate_prelude import find_prelude_end
from starkware.cairo.lean.verification.lean_processed_info import LeanProgramInfo
from starkware.cairo.lean.verification.scope_to_lean import get_name_in_scope
from starkware.cairo.lean.verification.type_to_lean import (
    LEAN_CAST_PREFIX,
    LEAN_STRUCT_OFFSET_PREFIX,
    LEAN_STRUCT_PTR_PREFIX,
    get_lean_type,
    get_lean_type_cast,
)


def add_lean_defs_to_file(lines: List[str], lean_info: LeanProgramInfo) -> List[str]:
    """
    Adds all the Lean definitions needed (based on lean_info) to the lines of a file.
    Existing definitions with the same type and name are replaced by the new definitions.
    Other existing definitions are left unchanged.
    """
    main_consts = lean_info.main_scope_consts
    main_defs = lean_info.main_scope_structs

    all_namespaces = list(set(main_consts).union(set(main_defs)))
    # We want the main namespace to be first (if there are any definitions
    # in the namespace).
    if lean_info.main_scope in all_namespaces:
        pos = all_namespaces.index(lean_info.main_scope)
        all_namespaces = [lean_info.main_scope] + all_namespaces[:pos] + all_namespaces[pos + 1 :]

    simplifier = LeanExprSimplifier(lean_info.preprocessor)
    # The context used in generating the constants, so the type is TypeFelt.
    desc_ctx = LeanDescContext(
        simplifier=simplifier,
        cairo_type=TypeFelt(),
        struct_defs=lean_info.struct_defs,
        identifiers=lean_info.identifiers,
        func_scope=None,
        open_namespaces=[],  # Will be updated below.
    )
    after = 0
    for namespace in all_namespaces:
        namespace_defs = []
        open_namespaces = lean_info.open_namespaces + [namespace]
        desc_ctx.open_namespaces = open_namespaces
        if namespace in main_consts:
            const_defs = main_consts[namespace]
            for (name, expr, accessible_scopes) in const_defs:
                simplifier.set_no_flow(accessible_scopes)
                namespace_defs += [gen_const_def(name, expr, desc_ctx)]
        if namespace in main_defs:
            struct_defs = main_defs[namespace]
            for struct_def in struct_defs:
                namespace_defs += gen_lean_struct(struct_def, namespace, open_namespaces)

        lines, _, after = add_defs_to_namespace(lean_info, lines, namespace_defs, namespace, after)
    return lines


def def_section_start_str(lean_info: LeanProgramInfo, namespace: ScopedName) -> str:
    is_main_scope = str(namespace) == str(lean_info.main_scope)
    return (
        "-- Main scope definitions."
        if is_main_scope
        else "namespace " + str(get_name_in_scope(namespace, lean_info.main_scope))
    )


def def_section_end_str(lean_info: LeanProgramInfo, namespace: ScopedName) -> str:
    is_main_scope = str(namespace) == str(lean_info.main_scope)
    return (
        "-- End of main scope definitions."
        if is_main_scope
        else "end " + str(get_name_in_scope(namespace, lean_info.main_scope))
    )


def add_defs_to_namespace(
    lean_info: LeanProgramInfo,
    lines: List[str],
    defs: List[List[str]],
    namespace: ScopedName,
    after: int,
) -> Tuple[List[str], int, int]:
    """
    Adds the definitions to the definition section of the given namespace and
    return the new set of lines and the position (start and end) of the definition
    section in the new set of lines. If the section is not found, it will be
    inserted at position 'after'.
    """
    start, end = get_namespace_def_pos(lean_info, lines, namespace, after)
    if start != end:
        defs = update_namespace_defs(split_defs_in_namespace(lines[start + 1 : end - 1]), defs)
    new_lines = [""] if 0 < start and lines[start - 1] and not lines[start - 1].isspace() else []
    new_lines += [def_section_start_str(lean_info, namespace), ""]
    for def_lines in defs:
        new_lines += def_lines
    new_lines += ["", def_section_end_str(lean_info, namespace)]
    if end < len(lines) and lines[end] and not lines[end].isspace():
        new_lines += [""]
    return (lines[:start] + new_lines + lines[end:], start, start + len(new_lines))


def get_namespace_def_pos(
    lean_info: LeanProgramInfo,
    lines: List[str],
    namespace: ScopedName,
    after: int,
) -> Tuple[int, int]:
    """
    Returns the start and end line number of the definitions for the namespace.
    If the namespace definition section is not found, the numbers returned indicate where
    it should be inserted. This will be not before 'after' and not before
    the file prelude (if found).
    """
    start_str = def_section_start_str(lean_info, namespace)
    end_str = def_section_end_str(lean_info, namespace)
    for start, line in enumerate(lines):
        if line.startswith(start_str):
            for end in range(start + 1, len(lines)):
                if lines[end].startswith(end_str):
                    return (start, end + 1)
            else:
                return (start, len(lines))

    after = max(after, find_prelude_end(lines))
    return (after, after)


LEAN_DEF_ATTR_PREFIXES = ("reducible", "ext", "derive decidable_eq")
LEAN_DEF_PREFIXES = ("def", "structure", "instance", "attribute")


def strip_def_attr(line: str) -> str:
    """
    Checks whether the given line begins with a valid attribute assignment @[...],
    and if it does, strips that attribute assignment and returns the stripped line.
    Otherwise, returns the original line.
    """
    match = re.match(r"\s*@\[(.*)\]", line)
    if match is None:
        return line
    attr_list = match.group(1)
    attrs = re.split(r",[\s]*", attr_list.strip())
    if all(attr in LEAN_DEF_ATTR_PREFIXES for attr in attrs):
        return line[match.end(0) :]
    return line


def is_lean_def_first_line(line: str) -> bool:
    """
    Checks whether the given line is the first line of a Lean definition.
    Attribute assignments (attribute [<attributes>] <name>) are seen as separate
    definitions.
    """
    if not line or line.isspace():
        return False
    line = strip_def_attr(line)
    tokens = re.split(r"[:\s]+", line.strip())
    return tokens[0] in LEAN_DEF_PREFIXES


def get_def_type_and_name(lean_def: List[str]) -> Optional[Tuple[str, str]]:
    if len(lean_def) == 0:
        return None
    line = strip_def_attr(lean_def[0])
    tokens = re.split(r"[:\s]+", line.strip())
    if len(tokens) < 2:
        return None
    if tokens[0] in LEAN_DEF_PREFIXES:
        return (tokens[0], tokens[1])
    return None


def split_defs_in_namespace(lines: List[str]) -> List[List[str]]:
    """
    Splits the lines into separate definitions, each definition consisting of
    one or more lines.
    A definition is recognized as beginning with "def <name>", "structure <name>" or
    "instance <name>" and ending with a blank line or a new definition
    """
    defs: List[List[str]] = []
    next_def: List[str] = []
    for line in lines:
        if not line or line.isspace():
            if len(next_def) > 0:
                defs.append(next_def)
                next_def = []
            continue
        if is_lean_def_first_line(line):
            if len(next_def) > 0:
                defs.append(next_def)
            next_def = [line]
        else:
            next_def.append(line)
    if len(next_def) > 0:
        defs.append(next_def)
    return defs


def update_namespace_defs(old_defs: List[List[str]], new_defs: List[List[str]]) -> List[List[str]]:
    """
    Modifies the old definitions with the new definitions and returns the new set
    of definitions. A new definition replaces an old definition if they have
    the same name. New definitions which do not replace old definitions are
    inserted at the earliest possible position, but not before the position at
    which the previous definition was added.
    """
    next_insert_pos = 0
    for new_def in new_defs:
        if not new_def:
            continue
        type_and_name = get_def_type_and_name(new_def)
        if type_and_name is None:
            raise Exception("Cannot find type or name of definition.")
        old_def_pos = next(
            filter(
                lambda old_def: type_and_name == get_def_type_and_name(old_def[1]),
                enumerate(old_defs),
            ),
            (-1, []),
        )[0]
        if old_def_pos >= next_insert_pos:
            old_defs = old_defs[:old_def_pos] + [new_def] + old_defs[old_def_pos + 1 :]
            next_insert_pos = old_def_pos + 1
        elif old_def_pos >= 0:
            old_defs = (
                old_defs[:old_def_pos]
                + old_defs[old_def_pos + 1 : next_insert_pos]
                + [new_def]
                + old_defs[next_insert_pos:]
            )
            next_insert_pos += 1
        else:
            old_defs = old_defs[:next_insert_pos] + [new_def] + old_defs[next_insert_pos:]
            next_insert_pos += 1

    return old_defs


def gen_const_def(name: str, expr: Expression, desc_ctx: LeanDescContext) -> List[str]:
    """
    Returns a Lean const definition, consisting of one or more lines,
    together providing a Lean const definition based on the expression defining
    the constant (rather than its integer value). The returned
    definitions are relative to the namespace in the context.
    """
    lean_desc = to_lean_description(expr=expr, context=desc_ctx)
    return [f"@[reducible] def {name} := {lean_desc}"]


def gen_lean_struct(
    struct_def: StructDefinition,
    namespace: ScopedName,
    open_namespaces: List[ScopedName],
) -> List[List[str]]:
    """
    Returns a list of Lean definitions, each consisting of one or more lines,
    together providing the Lean definition to support the given Cairo structure
    (including auxiliary definitions, such as the offset object). The returned
    definitions are relative to the given namespace and may assume a list of
    open namespaces.
    """
    member_defs = [
        f"( {name} : {get_lean_type(member.cairo_type, namespace, open_namespaces)} )"
        for name, member in struct_def.members.items()
    ]
    member_casts = [
        (name, get_lean_type_cast(member.cairo_type, namespace, open_namespaces, " "))
        for name, member in struct_def.members.items()
    ]

    struct_name = get_name_in_scope(struct_def.full_name, namespace)
    ptr_name = get_name_in_scope(struct_def.full_name, namespace, LEAN_STRUCT_PTR_PREFIX)
    offset_name = get_name_in_scope(struct_def.full_name, namespace, LEAN_STRUCT_OFFSET_PREFIX)
    cast_name = get_name_in_scope(struct_def.full_name, namespace, LEAN_CAST_PREFIX)
    ptr_cast_name = get_name_in_scope(
        struct_def.full_name, namespace, LEAN_CAST_PREFIX + LEAN_STRUCT_PTR_PREFIX
    )

    struct_defs = [
        # The structure itself.
        [f"@[ext] structure {struct_name} (F : Type) :=", "  " + " ".join(member_defs)],
        # A pointer to the structure.
        [f"@[ext] structure {ptr_name} (F : Type) :=", "  ( σ_ptr : F ) " + " ".join(member_defs)],
    ]

    # Add the offset definition.
    struct_defs += [
        [f"@[reducible] def {offset_name}.{name} := {member.offset}"]
        for name, member in struct_def.members.items()
    ]
    struct_defs += [[f"@[reducible] def {offset_name}.SIZE := {struct_def.size}"]]

    struct_defs += [
        # The cast functions.
        [
            f"@[reducible] def {cast_name} (mem : F → F) (p : F) : {struct_name} F := {{",
            "  "
            + ",\n  ".join(
                [f"{m} := {m_cast}mem (p + {offset_name}.{m})" for m, m_cast in member_casts]
            )
            + "\n}",
        ],
        [
            f"@[reducible] def {ptr_cast_name} (mem : F → F) (p : F) : {ptr_name} F := {{",
            "  σ_ptr := mem p,\n  "
            + ",\n  ".join(
                [f"{m} := {m_cast}mem ((mem p) + {offset_name}.{m})" for m, m_cast in member_casts]
            )
            + "\n}",
        ],
        # Coercion back to pointer.
        [f"instance {ptr_name}_to_F : has_coe ({ptr_name} F) F := ⟨λ s, s.σ_ptr⟩"],
    ]

    return struct_defs
