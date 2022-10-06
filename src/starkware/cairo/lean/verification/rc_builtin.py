import dataclasses
from typing import List, Optional


@dataclasses.dataclass
class RCBuiltin:
    """
    Stores general information for this builtin for a specific function (for which
    it is initialized). Such information includes the index of the (implicit) argument
    to the function which is a pointer for this builtin and the name of this
    argument.
    """

    # The position in the argument list (of the function this object belongs to)
    # of the range check pointer (implicit) argument.
    arg_index: int
    arg_name: str


# Functions to construct the RCBuiltin.


def is_implicit_rc_ptr(name: str) -> bool:
    """
    Checks whether the name can be the implicit rc pointer argument of a function.
    """
    return name in ["range_check_ptr"]


def implicit_rc_ptr_index(names: List[str]) -> int:
    """
    Returns the first position in the list where the string is the name
    of of an rc pointer.
    """
    for i, n in enumerate(names):
        if is_implicit_rc_ptr(n):
            return i
    return -1


def init_rc_on_func(func_arg_names: List[str]) -> Optional[RCBuiltin]:
    """
    Checks whether the given function has an argument for this builtin and,
    if yes, constructs the RCBuiltin object for it and returns it.
    """
    arg_index = implicit_rc_ptr_index(func_arg_names)
    if arg_index < 0:
        return None

    return RCBuiltin(arg_index=arg_index, arg_name=func_arg_names[arg_index])
