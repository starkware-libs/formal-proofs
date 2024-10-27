from typing import Dict


def add_name_sub(name: str, sub: int) -> str:
    """
    Add a subscript to a name.
    """
    if max(sub, 0) == 0:
        return name
    subscript_trans = "".maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
    return name + str(sub).translate(subscript_trans)


def get_name_sub(name: str, name_sub: Dict[str, int]) -> int:
    return name_sub[name] if name in name_sub else 0


def get_next_name_sub(name: str, name_sub: Dict[str, int]) -> int:
    return name_sub[name] + 1 if name in name_sub else 0


def name_with_sub(name: str, name_sub: Dict[str, int]) -> str:
    return add_name_sub(name, name_sub[name] if name in name_sub else 0)


def prev_name_with_sub(name: str, name_sub: Dict[str, int]) -> str:
    return add_name_sub(name, name_sub[name] - 1 if name in name_sub else 0)


def next_name_with_sub(name: str, name_sub: Dict[str, int]) -> str:
    return add_name_sub(name, name_sub[name] + 1 if name in name_sub else 0)


def inc_name_sub(name: str, name_sub: Dict[str, int]) -> str:
    """
    Increment the subscript for the given name. Return the name with
    the new subscript.
    """
    name_sub[name] = name_sub[name] + 1 if name in name_sub else 0
    return name_with_sub(name, name_sub)
