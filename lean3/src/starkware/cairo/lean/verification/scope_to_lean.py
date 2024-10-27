from typing import List, Optional

from starkware.cairo.lang.compiler.scoped_name import ScopedName


def lean_scoped_name(name: ScopedName, prefix: str = "") -> ScopedName:
    """
    Fixes the names in a scoped name such that they are all valid Lean identifiers
    (no leading _, for example). If 'prefix' is not an empty string, it is added
    as a prefix to the last name in the scopded name.
    """
    if len(name) == 0:
        return ScopedName()

    lean_path = [("σ" + s if s[0] == "_" else s) for s in name.path]
    if prefix:
        lean_path[-1] = prefix + lean_path[-1]
    return ScopedName(tuple(lean_path))


def get_name_in_scope(
    name: ScopedName, scope: Optional[ScopedName] = None, prefix: str = ""
) -> str:
    """
    If 'scope' is a prefix of 'name', this returns the name as should be used
    within the scope (that is, without the scope part). The name returned is
    the lean name (after fixing the names which are not valid Lean names).
    If 'prefix' is not an empty string, it is added as a prefix to the last name
    in the scoped name.
    """
    if len(name) == 0:
        return ""

    scoped_name = name[len(scope) :] if scope is not None and name.startswith(scope) else name
    if len(scoped_name) == 0:
        scoped_name = scoped_name[-1:]
    return str(lean_scoped_name(scoped_name, prefix))


def get_name_in_open_scopes(
    name: ScopedName, open_scopes: List[ScopedName], prefix: str = ""
) -> str:
    """
    Same as get_name_in_scope(), but tries out all the given scopes as prefix scopes.
    If there are multiple prefixes possible, the longest prefix is used.
    """
    if len(name) == 0:
        return ""
    for scope in sorted(open_scopes, key=len, reverse=True):
        if name.startswith(scope):
            return str(get_name_in_scope(name, scope, prefix))

    return str(lean_scoped_name(name, prefix))
