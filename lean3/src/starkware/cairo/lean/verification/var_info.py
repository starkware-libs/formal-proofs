import dataclasses

from starkware.cairo.lang.compiler.ast.cairo_types import CairoType
from starkware.cairo.lang.compiler.instruction import Register


@dataclasses.dataclass
class LeanVarInfo:
    """
    Stores information about a variable. This variable may be a function
    argument, a return argument or any variable created inside a function.
    """

    cairo_type: CairoType
    lean_type: str
    cast: str


@dataclasses.dataclass
class LeanRefVarInfo(LeanVarInfo):
    """
    Stores information about a reference (e.g. 'let x = a + b').
    """

    lean_expr: str


@dataclasses.dataclass
class LeanMemVarInfo(LeanVarInfo):
    """
    Stores information about a variable allocated in memory (either fp or ap based).
    """

    # AP or FP based variable (sometimes we only know this later)
    reg: Register
    # When this is a AP based variable, the offset is relative to the AP at
    # the relevant context.
    offset: int
