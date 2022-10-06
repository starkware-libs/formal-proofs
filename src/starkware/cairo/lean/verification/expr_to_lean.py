import dataclasses
from typing import Dict, List, Optional, Tuple

from starkware.cairo.lang.compiler.ast.cairo_types import (
    CairoType,
    TypeFelt,
    TypePointer,
    TypeStruct,
)
from starkware.cairo.lang.compiler.ast.expr import (
    ArgList,
    ExprAddressOf,
    ExprAssignment,
    ExprCast,
    ExprConst,
    ExprDeref,
    ExprDot,
    Expression,
    ExprHint,
    ExprIdentifier,
    ExprNeg,
    ExprOperator,
    ExprParentheses,
    ExprPow,
    ExprReg,
    ExprSubscript,
    ExprTuple,
)
from starkware.cairo.lang.compiler.ast.expr_func_call import ExprFuncCall
from starkware.cairo.lang.compiler.identifier_definition import (
    MemberDefinition,
    ReferenceDefinition,
)
from starkware.cairo.lang.compiler.identifier_manager import IdentifierManager
from starkware.cairo.lang.compiler.instruction import Register
from starkware.cairo.lang.compiler.preprocessor.flow import (
    FlowTrackingData,
    FlowTrackingDataUnreachable,
)
from starkware.cairo.lang.compiler.preprocessor.preprocessor import Preprocessor
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.lean_raw_info import (
    LeanPreprocessedCodeElement,
    LeanPreprocessedTempVarAlloc,
)
from starkware.cairo.lean.verification.rebinding import name_with_sub
from starkware.cairo.lean.verification.type_to_lean import LeanStructDefs, get_lean_type_cast

LEAN_HINT_VAR_PREFIX = "ιχ"


@dataclasses.dataclass
class LeanExprSimplifier:
    """
    An expression simplifier based on the simplification performed by the preprocessor.
    This allows us to perform partial expression simplifications. For example,
    when analyzing a division operator, we need to determine whether this is simplified
    to division by a constant.
    """

    preprocessor: Preprocessor
    accessible_scopes: List[ScopedName] = dataclasses.field(default_factory=lambda: [])
    flow_tracking_data: FlowTrackingData = FlowTrackingDataUnreachable()

    def set_instr(self, instr: LeanPreprocessedCodeElement):
        self.accessible_scopes = instr.accessible_scopes
        self.flow_tracking_data = instr.flow_tracking_data

    def set_no_flow(self, accessible_scopes: List[ScopedName]):
        """
        Sets the simplifier when the context is not inside a function.
        """
        self.accessible_scopes = accessible_scopes
        self.flow_tracking_data = FlowTrackingDataUnreachable()

    def visit(self, expr: Expression):
        self.preprocessor.accessible_scopes = self.accessible_scopes
        self.preprocessor.flow_tracking.data = self.flow_tracking_data
        simp, _ = self.preprocessor.simplify_expr(expr)
        return simp


@dataclasses.dataclass
class LeanDescContext:
    """
    Context information to allow the proper generation of the Lean description corresponding
    to an expression.
    This information includes:
    simplifier: the expression simplifier, set to the scope and flow of the current instruction.
    cairo_type: the type of the expression. This is optional, as it is only needed in some
        cases and is not always available.
    struct_defs: available structure definitions.
    identifiers: the identifier manager.
    func_scope: the scope of the function in which this expression appears. This may be None
        for expressions which are not inside a function context.
    open_namespaces: the open namespaces relative to which the description should be generated.
    div_var_basename, div_var_startnum: the prefix and index to use for the temporary variables
        used in division expressions.
    local_vars: the table of local variables of the current function.
    name_sub: the table of rebinding subscripts at the current instruction.
    prefix: An optional prefix to add before every line of the description. If this is None,
        the expression is generated on a single line. Otherwise (even if the prefix is the
        empty string), large expressions (such as structure) may be split over multiple lines.
    hint_vars: hints which may appear inside the current expression.
    """

    simplifier: Optional[LeanExprSimplifier]
    cairo_type: Optional[CairoType]
    struct_defs: LeanStructDefs
    identifiers: IdentifierManager
    func_scope: Optional[ScopedName]
    open_namespaces: List[ScopedName]
    div_var_basename: str = "δ0_"
    div_var_startnum: int = 0
    local_vars: Dict[int, str] = dataclasses.field(default_factory=lambda: {})
    name_sub: Dict[str, int] = dataclasses.field(default_factory=lambda: {})
    prefix: Optional[str] = None
    hint_vars: List[LeanPreprocessedTempVarAlloc] = dataclasses.field(default_factory=lambda: [])


def get_const_div_inv(
    expr: Expression, simplifier: Optional[LeanExprSimplifier]
) -> Optional[Tuple[int, bool]]:
    """
    If the given expression is a division by constant expression, and the simplifier
    is provided, this function returns the inverse of that constant. If the whole expression
    simplifies to a constant, the constant it is simplified into is returned.
    To distinguish between these two cases, a second argument is returned, which is
    True when the whole expression simplifies into a constant.
    Otherwise, None is returned.
    """
    if not isinstance(expr, ExprOperator) or not expr.op == "/" or simplifier is None:
        return None
    s_expr = simplifier.visit(expr)
    if isinstance(s_expr, ExprConst):
        return (s_expr.val, True)
    if isinstance(s_expr, ExprOperator) and s_expr.op == "*" and isinstance(s_expr.b, ExprConst):
        return (s_expr.b.val, False)
    return None


def rec_get_const_div_inv(
    expr: Expression, desc_ctx: LeanDescContext
) -> List[Tuple[str, int, bool]]:
    """
    Recursively gets all division by constant inverse values. This includes both
    the cases where only the divisor is a constant and cases where the whole division
    expression is a constant. Returns a list of triples where the last element in the
    triple is True if the whole division operation is a constant and False if only
    the divisor is a constant. The first element in each triple is the Lean representation
    of the constant expression: either the full expression, if it is a constant or just
    the divisor. This expression is not simplified. The second element of the triple
    is the constant to which the expression is equal (if the full expression is a constant)
    or the inverse of the constant (if only the divisor is a constant).
    """
    if isinstance(expr, ExprNeg):
        return rec_get_const_div_inv(expr.val, desc_ctx)
    if isinstance(expr, ExprCast):
        return rec_get_const_div_inv(expr.expr, desc_ctx)
    if isinstance(expr, ExprOperator):
        inv = rec_get_const_div_inv(expr.a, desc_ctx)
        const_inv = get_const_div_inv(expr, desc_ctx.simplifier)
        if const_inv is not None:
            the_const, is_full_expr = const_inv
            if is_full_expr:
                return inv + [
                    (to_lean_description(expr, context=desc_ctx), the_const, is_full_expr)
                ]
            return inv + [(to_lean_description(expr.b), the_const, is_full_expr)]
        return inv + rec_get_const_div_inv(expr.b, desc_ctx)
    if isinstance(expr, ExprPow):
        return rec_get_const_div_inv(expr.a, desc_ctx) + rec_get_const_div_inv(expr.b, desc_ctx)
    if isinstance(expr, ExprParentheses):
        return rec_get_const_div_inv(expr.val, desc_ctx)
    if isinstance(expr, ExprFuncCall):
        inv = []
        for arg in expr.rvalue.arguments.args:
            inv += rec_get_const_div_inv(arg.expr, desc_ctx)
        return inv
    if isinstance(expr, ExprDeref):
        return rec_get_const_div_inv(expr.addr, desc_ctx)
    return []


def count_div_ops(expr: Expression, simplifier: LeanExprSimplifier):
    """
    Counts the number of non-constant division operations in an expression.
    """
    if isinstance(expr, ExprConst):
        return 0
    if isinstance(expr, ExprNeg) or isinstance(expr, ExprParentheses):
        return count_div_ops(expr.val, simplifier)
    if isinstance(expr, ExprCast):
        return count_div_ops(expr.expr, simplifier)
    if isinstance(expr, ExprIdentifier):
        return 0
    if isinstance(expr, ExprOperator):
        return (
            count_div_ops(expr.a, simplifier)
            + count_div_ops(expr.b, simplifier)
            + (1 if (expr.op == "/" and get_const_div_inv(expr, simplifier) is None) else 0)
        )
    if isinstance(expr, ExprPow):
        return count_div_ops(expr.a, simplifier) + count_div_ops(expr.b, simplifier)
    if isinstance(expr, ExprParentheses):
        return count_div_ops(expr.val, simplifier)
    if isinstance(expr, ExprFuncCall):
        return sum([count_div_ops(arg.expr, simplifier) for arg in expr.rvalue.arguments.args])
    if isinstance(expr, ExprDeref):
        return count_div_ops(expr.addr, simplifier)
    return 0


def get_reversed_add_exprs(
    expr: Expression,
    simplifier: LeanExprSimplifier,
) -> List[Tuple[str, str]]:
    """
    Finds all sub-expressions on the expression which are an additional operation
    which is reversed (a + b -> b + a) by the simplifier. The function returns
    a list of the pairs of Lean expressions of the operands (a, b) in these expressions.
    """
    if isinstance(expr, ExprNeg) or isinstance(expr, ExprParentheses):
        return get_reversed_add_exprs(expr.val, simplifier)
    if isinstance(expr, ExprCast):
        return get_reversed_add_exprs(expr.expr, simplifier)
    if isinstance(expr, ExprPow):
        return get_reversed_add_exprs(expr.a, simplifier) + get_reversed_add_exprs(
            expr.b, simplifier
        )
    if isinstance(expr, ExprFuncCall):
        rev: List[Tuple[str, str]] = []
        for arg in expr.rvalue.arguments.args:
            rev += get_reversed_add_exprs(arg.expr, simplifier)
        return rev
    if isinstance(expr, ExprDeref):
        return get_reversed_add_exprs(expr.addr, simplifier)
    if isinstance(expr, ExprOperator):
        rev = []
        if expr.op == "+":
            a_expr = simplifier.visit(expr.a)
            b_expr = simplifier.visit(expr.b)
            if isinstance(a_expr, ExprConst) and not isinstance(b_expr, ExprConst):
                rev.append((to_lean_description(expr.a), to_lean_description(expr.b)))
        rev += get_reversed_add_exprs(expr.a, simplifier) + get_reversed_add_exprs(
            expr.b, simplifier
        )
        return rev

    return []


def to_lean_description(
    expr: Expression,
    local_vars: Dict[int, str] = {},
    context: Optional[LeanDescContext] = None,
) -> str:
    """
    Converts an expression to a Lean description. Takes a base name for variables that represent
    default division values.
    """
    result, _ = to_lean_description_aux(expr=expr, local_vars=local_vars, context=context)
    return result


def to_lean_description_aux(
    expr: Expression,
    local_vars: Dict[int, str] = {},
    context: Optional[LeanDescContext] = None,
) -> Tuple[str, int]:
    """
    Converts an expression to a Lean description. Returns a string containing the Lean
    expression and the updated division variable counter.
    """
    div_var_startnum = context.div_var_startnum if context is not None else 0
    if len(local_vars) == 0 and context is not None:
        local_vars = context.local_vars
    if isinstance(expr, ExprConst):
        return str(expr.val) if 0 <= expr.val else f"({str(expr.val)})", div_var_startnum
    if isinstance(expr, ExprNeg):
        result, new_div_var_startnum = to_lean_description_aux(expr.val, local_vars, context)
        return f"(-{result})", new_div_var_startnum
    if isinstance(expr, ExprCast):
        return to_lean_description_aux(expr.expr, local_vars, context)
    if isinstance(expr, ExprIdentifier):
        name_sub = context.name_sub if context is not None else {}
        return name_with_sub(expr.name, name_sub), div_var_startnum
    if isinstance(expr, ExprOperator):
        op1, new_div_var_startnum = to_lean_description_aux(expr.a, local_vars, context)
        simplifier = context.simplifier if context is not None else None
        div_var_basename = context.div_var_basename if context is not None else "δ_"
        is_ddiv = expr.op == "/" and get_const_div_inv(expr, simplifier) is None
        if is_ddiv:
            div_var_name = f"{div_var_basename}{new_div_var_startnum}"
            new_div_var_startnum += 1
        if context is not None:
            context.div_var_startnum = new_div_var_startnum
        op2, new_div_var_startnum = to_lean_description_aux(
            expr.b,
            local_vars,
            context,
        )
        if is_ddiv:
            return f"ddiv {op1} {op2} {div_var_name}", new_div_var_startnum
        if expr.op == "/":
            div_simp = get_const_div_inv(expr, simplifier)
            if div_simp is not None and div_simp[1]:
                return f"({op1} : ℤ) / ({op2} : ℤ)", new_div_var_startnum
            return f"{op1} / ({op2} : ℤ)", new_div_var_startnum
        return f"{op1} {expr.op} {op2}", new_div_var_startnum
    if isinstance(expr, ExprPow):
        op1, new_div_var_startnum = to_lean_description_aux(expr.a, local_vars, context)
        if context is not None:
            context.div_var_startnum = new_div_var_startnum
        op2, new_div_var_startnum = to_lean_description_aux(
            expr.b,
            local_vars,
            context,
        )
        return f"{op1} ^ {op2}", new_div_var_startnum
    if isinstance(expr, ExprParentheses):
        result, new_div_var_startnum = to_lean_description_aux(expr.val, local_vars, context)
        return f"({result})", new_div_var_startnum
    if isinstance(expr, ExprFuncCall):
        assert (
            context is None
            or context.cairo_type is None
            or (
                isinstance(context.cairo_type, TypeStruct)
                and expr.rvalue.func_ident.name == str(context.cairo_type.scope[-1:])
            )
        ), "Function call name does not match type."
        return to_obj_constructor(
            args=expr.rvalue.arguments,
            local_vars=local_vars,
            context=context,
        )

    if isinstance(expr, ExprTuple):
        return to_obj_constructor(
            args=expr.members,
            local_vars=local_vars,
            context=context,
        )
    if isinstance(expr, ExprDeref):
        reg_and_offset = get_reg_offset(expr.addr)
        if reg_and_offset is not None:
            reg, offset = reg_and_offset
            if reg == Register.FP and offset in local_vars:
                return local_vars[offset], div_var_startnum
            return (
                "mem (σ.{}{})".format(
                    "fp" if reg == Register.FP else "ap",
                    "" if offset == 0 else (f" + {offset}" if 0 < offset else f" - {-offset}"),
                ),
                div_var_startnum,
            )

        result, new_div_var_startnum = to_lean_description_aux(expr.addr, local_vars, context)
        return f"mem ({result})", new_div_var_startnum
    if isinstance(expr, ExprReg):
        return "σ.fp" if expr.reg == Register.FP else "σ.ap", div_var_startnum
    if isinstance(expr, ExprAddressOf):
        if isinstance(expr.expr, ExprSubscript):
            inner, _, new_div_var_startnum = to_lean_subscript_inner_desc_and_cast(
                expr=expr.expr,
                local_vars=local_vars,
                context=context,
            )
            return inner, new_div_var_startnum

        sub_expr, new_div_var_startnum = to_lean_description_aux(expr.expr, local_vars, context)
        if sub_expr.startswith("mem ("):
            addr_prefix = "mem ("
            addr_suffix = ")"
        elif sub_expr.startswith("mem "):
            addr_prefix = "mem "
            addr_suffix = ""
        else:
            raise Exception("Cannot determine address expression.")

        if addr_suffix:
            addr_expr = sub_expr[len(addr_prefix) : -len(addr_suffix)]
        else:
            addr_expr = sub_expr[len(addr_prefix) :]
        return addr_expr, new_div_var_startnum

    if isinstance(expr, ExprSubscript):
        inner, cast, new_div_var_startnum = to_lean_subscript_inner_desc_and_cast(
            expr=expr,
            local_vars=local_vars,
            context=context,
        )

        lean_expr = f"{cast} (mem ({inner}))" if cast else f"mem ({inner})"
        return lean_expr, new_div_var_startnum

    if isinstance(expr, ExprDot):
        base_expr, new_div_var_startnum = to_lean_description_aux(expr.expr, local_vars, context)
        return f"({base_expr}).{expr.member.name}", new_div_var_startnum

    if isinstance(expr, ExprHint):
        if context is not None:
            for hint_var in context.hint_vars:
                if hint_var.expr == expr:
                    return (
                        LEAN_HINT_VAR_PREFIX + hint_var.identifier.identifier.name,
                        div_var_startnum,
                    )
        raise Exception("Failed to resolve hint variable.")

    raise Exception("Unsupported expression type.")


def to_lean_paren_description(
    expr: Expression,
    local_vars: Dict[int, str] = {},
    context: Optional[LeanDescContext] = None,
) -> str:
    """
    Same as to_lean_description, but insert parentheses when needed.
    """
    result, _ = to_lean_paren_description_aux(expr, local_vars, context)
    return result


def to_lean_paren_description_aux(
    expr: Expression,
    local_vars: Dict[int, str] = {},
    context: Optional[LeanDescContext] = None,
) -> Tuple[str, int]:
    """
    Same as to_lean_description_aux, but insert parentheses when needed.
    """
    if (
        isinstance(expr, ExprOperator)
        or isinstance(expr, ExprAddressOf)
        or isinstance(expr, ExprSubscript)
    ):
        result, div_var_startnum = to_lean_description_aux(
            expr,
            local_vars,
            context=context,
        )
        return f"({result})", div_var_startnum
    else:
        return to_lean_description_aux(expr, local_vars, context)


def to_lean_subscript_inner_desc_and_cast(
    expr: ExprSubscript,
    local_vars: Dict[int, str],
    context: Optional[LeanDescContext],
) -> Tuple[str, str, int]:
    base_expr, new_div_var_startnum = to_lean_description_aux(expr.expr, local_vars, context)
    if context is not None:
        cairo_type = get_expr_type(expr.expr, context)
        context.div_var_startnum = new_div_var_startnum
    else:
        cairo_type = TypeFelt()
    mem_offset, new_div_var_startnum = to_lean_description_aux(
        expr.offset,
        local_vars,
        context,
    )

    if (
        context is not None
        and isinstance(cairo_type, TypePointer)
        and isinstance(cairo_type.pointee, TypeStruct)
    ):
        size = context.struct_defs.get_type_size(cairo_type.pointee)
        cast = get_lean_type_cast(
            cairo_type.pointee,
            context.func_scope if context is not None else None,
            context.open_namespaces if context is not None else [],
        )
        return f"{base_expr} + {size} * {mem_offset}", cast, new_div_var_startnum

    return f"{base_expr} + {mem_offset}", "", new_div_var_startnum


def to_obj_constructor(
    args: ArgList,
    local_vars: Dict[int, str],
    context: Optional[LeanDescContext],
) -> Tuple[str, int]:
    """
    Returns the Lean object constructor with the field assignments given by the args.
    If the args are all keyword arguments, the context is optional. If some are positional
    arguments, the context must be provided to allow the function to determine the type
    of the object being constructed.
    If the context prefix is not None, the object constructor is split over multiple
    lines (one per member) and the prefix is added before each line (except
    the first one).
    """
    fields, div_var_startnum = gen_obj_positional_fields(
        args=args,
        local_vars=local_vars,
        context=context,
    )
    if context is not None:
        context.div_var_startnum = div_var_startnum
    keyword_fields, div_var_startnum = gen_obj_keyword_fields(
        args=args,
        local_vars=local_vars,
        context=context,
    )

    fields += keyword_fields

    if context is None or context.prefix is None:
        return "{ " + ", ".join(fields) + " }", div_var_startnum

    return (
        "{\n"
        + ",\n".join([context.prefix + "  " + field for field in fields])
        + "\n"
        + context.prefix
        + "}",
        div_var_startnum,
    )


def gen_obj_positional_fields(
    args: ArgList,
    local_vars: Dict[int, str],
    context: Optional[LeanDescContext],
) -> Tuple[List[str], int]:
    """
    Returns a list with the assignments for the positional fields in an object
    constructor. Since the names of the positional fields are not provided, this
    function uses the type provided by the context to determine the field.
    """
    div_var_startnum = context.div_var_startnum if context is not None else 0
    if context is None or context.cairo_type is None:
        return [], div_var_startnum
    struct_def = context.struct_defs.get_struct_by_resolved_type(context.cairo_type)
    if struct_def is None:
        return [], div_var_startnum

    fields: List[str] = []

    for arg_num, (name, member) in enumerate(struct_def.members.items()):
        if args.args[arg_num].identifier is not None:
            # End of positional arguments.
            return fields, div_var_startnum
        if context is not None:
            context.div_var_startnum = div_var_startnum
        field, div_var_startnum = gen_obj_field_assignment(
            name=name,
            member=member,
            arg=args.args[arg_num],
            local_vars=local_vars,
            context=context,
        )
        fields.append(field)

    return fields, div_var_startnum


def gen_obj_keyword_fields(
    args: ArgList,
    local_vars: Dict[int, str],
    context: Optional[LeanDescContext],
) -> Tuple[List[str], int]:
    """
    Returns a list with the assignments for the keyword fields in an object
    constructor.
    """
    # The use of the structure definition is optional.
    struct_def = (
        None
        if context is None or context.cairo_type is None
        else context.struct_defs.get_struct_by_resolved_type(context.cairo_type)
    )

    div_var_startnum = context.div_var_startnum if context is not None else 0
    fields = []

    for arg in args.args:
        if arg.identifier is None:
            continue
        name = arg.identifier.name
        if struct_def is not None and name in struct_def.members:
            member: Optional[MemberDefinition] = struct_def.members[name]
        else:
            member = None
        if context is not None:
            context.div_var_startnum = div_var_startnum
        field, div_var_startnum = gen_obj_field_assignment(
            name=name,
            member=member,
            arg=arg,
            local_vars=local_vars,
            context=context,
        )
        fields.append(field)
    return fields, div_var_startnum


def gen_obj_field_assignment(
    name: str,
    member: Optional[MemberDefinition],
    arg: ExprAssignment,
    local_vars: Dict[int, str],
    context: Optional[LeanDescContext],
) -> Tuple[str, int]:
    """
    Generates the assignment for a single field in an object constructor.
    """
    arg_context = None
    if context is not None and member is not None:
        if isinstance(member.cairo_type, TypeStruct):
            arg_context = dataclasses.replace(context, cairo_type=member.cairo_type, prefix=None)
        else:
            arg_context = dataclasses.replace(context, cairo_type=TypeFelt, prefix=None)
    lean_expr, div_var_startnum = to_lean_description_aux(arg.expr, local_vars, arg_context)
    return f"{name} := {lean_expr}", div_var_startnum


def get_reg_offset(expr: Expression) -> Optional[Tuple[Register, int]]:
    """
    If this expression represents an offset from fp or ap, return the register
    from which the offset is and the offset.
    Otherwise, returns None.
    """
    if isinstance(expr, ExprCast):
        return get_reg_offset(expr.expr)
    if isinstance(expr, ExprReg):
        return (expr.reg, 0) if expr.reg == Register.FP or expr.reg == Register.AP else None
    if isinstance(expr, ExprOperator):
        if expr.op not in ["+", "-"]:
            return None
        reg_and_offset = get_reg_offset(expr.a)
        if reg_and_offset is not None and isinstance(expr.b, ExprConst):
            reg, offset = reg_and_offset
            return reg, offset + (expr.b.val if expr.op == "+" else -expr.b.val)
        reg_and_offset = get_reg_offset(expr.b)
        if reg_and_offset is not None and isinstance(expr.a, ExprConst):
            reg, offset = reg_and_offset
            return reg, offset + (expr.a.val if expr.op == "+" else -expr.a.val)
    return None


def get_reg_ref(expr: Expression) -> Optional[Tuple[Register, int]]:
    if isinstance(expr, ExprCast):
        return get_reg_ref(expr.expr)
    elif isinstance(expr, ExprDeref):
        return get_reg_offset(expr.addr)
    return None


def get_all_reg_refs(expr: Expression) -> List[Tuple[Register, int]]:
    """
    Returns all the refrences to a register + offset in the given expression.
    """
    if isinstance(expr, ExprConst):
        return []
    if isinstance(expr, ExprNeg):
        return get_all_reg_refs(expr.val)
    if isinstance(expr, ExprCast):
        return get_all_reg_refs(expr.expr)
    if isinstance(expr, ExprIdentifier):
        return []
    if isinstance(expr, ExprOperator):
        return get_all_reg_refs(expr.a) + get_all_reg_refs(expr.b)
    if isinstance(expr, ExprPow):
        return get_all_reg_refs(expr.a) + get_all_reg_refs(expr.b)
    if isinstance(expr, ExprParentheses):
        return get_all_reg_refs(expr.val)
    if isinstance(expr, ExprFuncCall):
        return []
    if isinstance(expr, ExprDeref):
        reg_offset = get_reg_offset(expr.addr)
        return [] if reg_offset is None else [reg_offset]

    raise Exception("Cannot extract register references from expression.")


def is_fp_ref(expr: Expression) -> bool:
    """
    Returns true if the given expression is of the form [fp + c]
    """
    if isinstance(expr, ExprCast):
        return is_fp_ref(expr.expr)
    elif isinstance(expr, ExprDeref):
        return get_fp_offset(expr.addr) != None
    return False


def get_fp_ref_offset(expr: Expression) -> Optional[int]:
    """
    Returns the offset from fp if the given expression is [fp + c]
    """
    if isinstance(expr, ExprCast):
        return get_fp_ref_offset(expr.expr)
    elif isinstance(expr, ExprDeref):
        return get_fp_offset(expr.addr)
    return None


def get_fp_offset(expr: Expression) -> Optional[int]:
    """
    If this expression represents an offset from fp, return this offset.
    Otherwise, return None
    """
    reg_and_offset = get_reg_offset(expr)
    if reg_and_offset is None:
        return None
    reg, offset = reg_and_offset
    return None if reg != Register.FP else offset


def is_ap_ref(expr: Expression) -> bool:
    """
    Returns true if the given expression is of the form [ap + c]
    """
    if isinstance(expr, ExprCast):
        return is_ap_ref(expr.expr)
    elif isinstance(expr, ExprDeref):
        return get_ap_offset(expr.addr) != None
    return False


def get_ap_ref_offset(expr: Expression) -> Optional[int]:
    """
    Returns the offset from ap if the given expression is [ap + c]
    """
    if isinstance(expr, ExprCast):
        return get_ap_ref_offset(expr.expr)
    elif isinstance(expr, ExprDeref):
        return get_ap_offset(expr.addr)
    return None


def get_ap_offset(expr: Expression) -> Optional[int]:
    """
    If this expression represents an offset from ap, returns this offset.
    Otherwise, returns None.
    """
    reg_and_offset = get_reg_offset(expr)
    if reg_and_offset is None:
        return None
    reg, offset = reg_and_offset
    return None if reg != Register.AP else offset


def get_const(expr: Expression) -> Optional[int]:
    if isinstance(expr, ExprCast):
        return get_const(expr.expr)
    elif isinstance(expr, ExprConst):
        return expr.val
    else:
        return None


def get_expr_identifiers(expr: Expression) -> List[ExprIdentifier]:
    """
    Returns all the ExprIdentifier nodes in an expression.
    """
    if isinstance(expr, ExprCast):
        return get_expr_identifiers(expr.expr)
    if isinstance(expr, ExprConst):
        return []
    if isinstance(expr, ExprNeg):
        return get_expr_identifiers(expr.val)
    if isinstance(expr, ExprIdentifier):
        return [expr]
    if isinstance(expr, ExprOperator):
        return get_expr_identifiers(expr.a) + get_expr_identifiers(expr.b)
    if isinstance(expr, ExprPow):
        return get_expr_identifiers(expr.a) + get_expr_identifiers(expr.b)
    if isinstance(expr, ExprParentheses):
        return get_expr_identifiers(expr.val)
    if isinstance(expr, ExprFuncCall):
        exprs: List[ExprIdentifier] = []
        for arg in expr.rvalue.arguments.args:
            exprs += get_expr_identifiers(arg.expr)
        return exprs
    if isinstance(expr, ExprTuple):
        exprs = []
        for arg in expr.members.args:
            exprs += get_expr_identifiers(arg.expr)
        return exprs
    if isinstance(expr, ExprDeref):
        return get_expr_identifiers(expr.addr)
    if isinstance(expr, ExprReg):
        return []
    if isinstance(expr, ExprAddressOf):
        return get_expr_identifiers(expr.expr)
    if isinstance(expr, ExprSubscript):
        return get_expr_identifiers(expr.expr)
    if isinstance(expr, ExprDot):
        return get_expr_identifiers(expr.expr)
    if isinstance(expr, ExprHint):
        return []

    raise Exception("Cannot determine type of expression.")


def get_expr_identifier_full_names(
    expr: Expression,
    identifiers: IdentifierManager,
    accessible_scopes: List[ScopedName],
) -> List[ScopedName]:

    full_names = []
    for identifier in get_expr_identifiers(expr):
        name = identifiers.search(
            accessible_scopes, ScopedName.from_string(identifier.name)
        ).canonical_name
        if name not in full_names:
            full_names.append(name)
    return full_names


def get_expr_type(expr: Expression, context: LeanDescContext) -> CairoType:
    """
    Returns the Cairo type of the expression.
    """
    if isinstance(expr, ExprCast):
        return expr.dest_type
    if isinstance(expr, ExprConst):
        return TypeFelt()
    if isinstance(expr, ExprNeg):
        return get_expr_type(expr.val, context)
    if isinstance(expr, ExprIdentifier):
        id_def = context.identifiers.get_by_full_name(
            (context.func_scope if context.func_scope is not None else ScopedName())
            + ScopedName.from_string(expr.name)
        )
        if id_def is None or not isinstance(id_def, ReferenceDefinition):
            raise Exception("Cannot determine type of unknown/non-reference identifier.")
        return id_def.cairo_type
    if isinstance(expr, ExprOperator):
        type_a = get_expr_type(expr.a, context)
        type_b = get_expr_type(expr.b, context)
        if isinstance(type_a, TypePointer):
            return type_a
        if isinstance(type_b, TypePointer):
            return type_b
        return TypeFelt()
    if isinstance(expr, ExprPow):
        return TypeFelt()
    if isinstance(expr, ExprParentheses):
        return get_expr_type(expr.val, context)
    if isinstance(expr, ExprFuncCall):
        raise Exception("Determining the type of an ExprFuncCall expression not yet supported.")
    if isinstance(expr, ExprTuple):
        raise Exception("Determining the type of an ExprTuple expression not yet supported.")
    if isinstance(expr, ExprDeref):
        return TypeFelt()
    if isinstance(expr, ExprReg):
        return TypeFelt()
    if isinstance(expr, ExprAddressOf):
        return TypePointer(get_expr_type(expr.expr, context))
    if isinstance(expr, ExprSubscript):
        base_type = get_expr_type(expr.expr, context)
        return base_type.pointee if isinstance(base_type, TypePointer) else base_type
    if isinstance(expr, ExprDot):
        struct_type = get_expr_type(expr.expr, context)
        if isinstance(struct_type, TypePointer):
            struct_type = struct_type.pointee
        if not isinstance(struct_type, TypeStruct):
            raise Exception("Dot expression applied to a non-structure type.")
        return context.struct_defs.get_member_type(struct_type, expr.member.name)

    raise Exception("Cannot determine type of expression.")
