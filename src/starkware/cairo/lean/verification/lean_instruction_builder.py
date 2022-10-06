import dataclasses
from typing import List, cast

from starkware.cairo.lang.compiler.ast.expr import ExprConst, ExprDeref
from starkware.cairo.lang.compiler.ast.instructions import (
    AddApInstruction,
    AssertEqInstruction,
    CallInstruction,
    InstructionAst,
    JnzInstruction,
    JumpInstruction,
    RetInstruction,
)
from starkware.cairo.lang.compiler.error_handling import LocationError
from starkware.cairo.lang.compiler.instruction import Instruction, Register
from starkware.cairo.lang.compiler.instruction_builder import (
    InstructionBuilderError,
    _apply_inverse_syntactic_sugar,
    _parse_dereference,
    _parse_register_offset,
    _parse_res,
)

# Lean description of code elements.


@dataclasses.dataclass
class LeanCodeElement:
    code: List[str]

    def get_code(self):
        return self.code


@dataclasses.dataclass
class LeanCodeAssertEq(LeanCodeElement):
    lhs: str
    rhs: str
    inv_transformed: bool
    is_add: bool
    reversed: bool


@dataclasses.dataclass
class LeanCodeReturn(LeanCodeElement):
    pass


# The instruction builder.


class LeanInstructionBuilderError(LocationError):
    pass


def build_lean_instruction(instruction: InstructionAst) -> LeanCodeElement:
    if isinstance(instruction.body, AssertEqInstruction):
        return _build_lean_assert_eq_instruction(instruction)
    elif isinstance(instruction.body, JumpInstruction):
        return _build_lean_jump_instruction(instruction)
    elif isinstance(instruction.body, JnzInstruction):
        return _build_lean_jnz_instruction(instruction)
    elif isinstance(instruction.body, CallInstruction):
        return _build_lean_call_instruction(instruction)
    elif isinstance(instruction.body, RetInstruction):
        return _build_lean_ret_instruction(instruction)
    elif isinstance(instruction.body, AddApInstruction):
        return _build_lean_addap_instruction(instruction)
    else:
        raise LeanInstructionBuilderError(
            f"Instructions of type {type(instruction.body).__name__} are not implemented.",
            location=instruction.body.location,
        )


def _build_lean_assert_eq_instruction(instruction_ast: InstructionAst) -> LeanCodeAssertEq:
    """
    Builds an Instruction object from the AST object, assuming the instruction is of type AssertEq.
    If a = b is not a valid Cairo instruction, it will try to write it as b = a. For example,
    "[[ap]] = [fp]" is supported even though its operands are reversed in the bytecode.
    """
    try:
        # First try to parse the instruction in its the original form.
        return _build_lean_assert_eq_instruction_inner(instruction_ast, reversed=False)
    except InstructionBuilderError as exc_:
        # Store the exception in case the second attempt fails as well.
        exc = exc_

    try:
        # If it fails, try to parse it as b = a instead of a = b.
        instruction_body: AssertEqInstruction = cast(AssertEqInstruction, instruction_ast.body)
        return _build_lean_assert_eq_instruction_inner(
            dataclasses.replace(
                instruction_ast,
                body=dataclasses.replace(
                    instruction_body, a=instruction_body.b, b=instruction_body.a
                ),
            ),
            reversed=True,
        )
    except Exception:
        # If both fail, raise the exception thrown by parsing the original form.
        raise exc from None


def reg_offset_lean(reg: Register, off: int):
    if reg is Register.AP:
        if off == 0:
            return "[ap]"
        else:
            return "[ap+ " + str(off) + "]"
    else:
        if off == 0:
            return "[fp]"
        else:
            return "[fp+ " + str(off) + "]"


def op0_part_lean(reg: Register, off: int):
    return "op0:='op0" + reg_offset_lean(reg, off) + ", "


def dst_part_lean(reg: Register, off: int):
    return "'dst" + reg_offset_lean(reg, off)


def op1_part_lean(op1_addr: Instruction.Op1Addr, off: int):
    if op1_addr is Instruction.Op1Addr.IMM:
        return "'op1[imm]"
    elif op1_addr is Instruction.Op1Addr.AP:
        if off == 0:
            return "'op1[ap]"
        else:
            return "'op1[ap+ " + str(off) + "]"
    elif op1_addr is Instruction.Op1Addr.FP:
        if off == 0:
            return "'op1[fp]"
        else:
            return "'op1[fp+ " + str(off) + "]"
    elif off == 0:
        return "'op1[op0]"
    else:
        return "'op1[op0+ " + str(off) + "]"


def _build_lean_assert_eq_instruction_inner(
    instruction_ast: InstructionAst, reversed: bool
) -> LeanCodeAssertEq:
    """
    Builds an Instruction object from the AST object, assuming the instruction is of type AssertEq.
    """
    old_instruction_body: AssertEqInstruction = cast(AssertEqInstruction, instruction_ast.body)

    instruction_body = _apply_inverse_syntactic_sugar(old_instruction_body)
    inv_transformed = instruction_body != old_instruction_body

    dst_expr = _parse_dereference(instruction_body.a)
    dst_register, off0 = _parse_register_offset(dst_expr)

    res_desc = _parse_res(instruction_body.b)

    op0_part = (
        ""
        if res_desc.res is Instruction.Res.OP1 and res_desc.op1_addr != Instruction.Op1Addr.OP0
        else op0_part_lean(res_desc.op0_register, res_desc.off1)
    )
    dst_part = dst_part_lean(dst_register, off0)
    op1_part = op1_part_lean(res_desc.op1_addr, res_desc.off2)
    is_add = False
    if res_desc.res is Instruction.Res.OP1:
        res_part = "'res[" + op1_part + "]"
    elif res_desc.res is Instruction.Res.ADD:
        res_part = "'res[op0+ " + op1_part + "]"
        is_add = True
    elif res_desc.res is Instruction.Res.MUL:
        res_part = "'res[op0* " + op1_part + "]"
    else:
        LeanInstructionBuilderError(f"Unexpected result type.", location=instruction_body.location)

    ap_part = ";ap++" if instruction_ast.inc_ap else ""

    imm_part = [str(res_desc.imm)] if res_desc.op1_addr is Instruction.Op1Addr.IMM else []

    code = [
        "'assert_eq[" + op0_part + dst_part + " === " + res_part + ap_part + "].to_nat"
    ] + imm_part

    return LeanCodeAssertEq(
        code=code, lhs="", rhs="", inv_transformed=inv_transformed, is_add=is_add, reversed=reversed
    )


def _build_lean_jump_instruction(instruction_ast: InstructionAst) -> LeanCodeElement:
    """
    Builds an Instruction object from the AST object, assuming the instruction is a JumpInstruction.
    """
    instruction_body: JumpInstruction = cast(JumpInstruction, instruction_ast.body)

    res_desc = _parse_res(instruction_body.val)

    instr_part = "'jmp_rel" if instruction_body.relative else "'jmp_abs"
    op0_part = (
        ""
        if res_desc.res is Instruction.Res.OP1
        else op0_part_lean(res_desc.op0_register, res_desc.off1)
    )
    op1_part = op1_part_lean(res_desc.op1_addr, res_desc.off2)
    if res_desc.res is Instruction.Res.OP1:
        res_part = "[" + op1_part
    elif res_desc.res is Instruction.Res.ADD:
        res_part = "[+" + op0_part + ", " + op1_part
    elif res_desc.res is Instruction.Res.MUL:
        res_part = "[*" + op0_part + ", " + op1_part
    else:
        LeanInstructionBuilderError(f"Unexpected result type.", location=instruction_body.location)

    ap_part = ";ap++" if instruction_ast.inc_ap else ""

    imm_part = (
        ["'[#nz " + str(res_desc.imm) + "]"] if res_desc.op1_addr is Instruction.Op1Addr.IMM else []
    )

    code = [instr_part + res_part + ap_part + "].to_nat"] + imm_part
    return LeanCodeElement(code=code)


def _build_lean_jnz_instruction(instruction_ast: InstructionAst) -> LeanCodeElement:
    """
    Builds an Instruction object from the AST object, assuming the instruction is a JnzInstruction.
    """
    instruction_body: JnzInstruction = cast(JnzInstruction, instruction_ast.body)

    cond_addr = _parse_dereference(instruction_body.condition)
    dst_register, off0 = _parse_register_offset(cond_addr)

    jump_offset = instruction_body.jump_offset
    if isinstance(jump_offset, ExprDeref):
        op1_reg, off2 = _parse_register_offset(jump_offset.addr)
        imm = None
        op1_addr = Instruction.Op1Addr.FP if op1_reg is Register.FP else Instruction.Op1Addr.AP
    elif isinstance(jump_offset, ExprConst):
        off2 = 1
        imm = jump_offset.val
        op1_addr = Instruction.Op1Addr.IMM
    else:
        raise LeanInstructionBuilderError(
            "Invalid expression for jmp offset.", location=jump_offset.location
        )

    dst_part = dst_part_lean(dst_register, off0)
    op1_part = op1_part_lean(op1_addr, off2)
    ap_part = ";ap++" if instruction_ast.inc_ap else ""
    imm_part = [] if imm is None else [str(imm)]

    code = ["'jnz_rel[" + op1_part + ", " + dst_part + ap_part + "].to_nat"] + imm_part
    return LeanCodeElement(code=code)


def _build_lean_call_instruction(instruction_ast: InstructionAst) -> LeanCodeElement:
    """
    Builds an Instruction object from the AST object, assuming the instruction is a CallInstruction.
    """
    instruction_body: CallInstruction = cast(CallInstruction, instruction_ast.body)

    val = instruction_body.val
    if isinstance(val, ExprDeref):
        op1_reg, off2 = _parse_register_offset(val.addr)
        imm = None
        op1_addr = Instruction.Op1Addr.FP if op1_reg is Register.FP else Instruction.Op1Addr.AP
    elif isinstance(val, ExprConst):
        off2 = 1
        imm = val.val
        op1_addr = Instruction.Op1Addr.IMM
    else:
        raise LeanInstructionBuilderError("Invalid offset for call.", location=val.location)

    if instruction_ast.inc_ap:
        raise LeanInstructionBuilderError(
            "ap++ may not be used with the call opcode.", location=instruction_ast.location
        )

    instr_part = "'call_rel[" if instruction_body.relative else "'call_abs"
    op1_part = op1_part_lean(op1_addr, off2)
    imm_part = [] if imm is None else [str(imm)]

    code = [instr_part + op1_part + "].to_nat"] + imm_part
    return LeanCodeElement(code=code)


def _build_lean_ret_instruction(instruction_ast: InstructionAst) -> LeanCodeElement:
    """
    Builds an Instruction object from the AST object, assuming the instruction is a RetInstruction.
    """

    code = ["'ret[].to_nat"]
    return LeanCodeReturn(code=code)


def _build_lean_addap_instruction(instruction_ast: InstructionAst) -> LeanCodeElement:
    """
    Builds an Instruction object from the AST object, assuming the instruction is an
    AddApInstruction.
    """
    instruction_body: AddApInstruction = cast(AddApInstruction, instruction_ast.body)

    res_desc = _parse_res(instruction_body.expr)

    op0_part = (
        ""
        if res_desc.res is Instruction.Res.OP1
        else (op0_part_lean(res_desc.op0_register, res_desc.off1))
    )
    op1_part = op1_part_lean(res_desc.op1_addr, res_desc.off2)
    if res_desc.res is Instruction.Res.OP1:
        res_part = "'res[" + op1_part + "]"
    elif res_desc.res is Instruction.Res.ADD:
        res_part = "'res[op0+ " + op1_part + "]"
    elif res_desc.res is Instruction.Res.MUL:
        res_part = "'res[op0* " + op1_part + "]"
    else:
        LeanInstructionBuilderError(f"Unexpected result type.", location=instruction_body.location)

    imm_part = [str(res_desc.imm)] if res_desc.op1_addr is Instruction.Op1Addr.IMM else []

    code = ["'ap+=[" + op0_part + res_part + "].to_nat"] + imm_part
    return LeanCodeElement(code=code)
