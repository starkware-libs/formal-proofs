/-
Cairo machine instructions.
-/
import Verification.Semantics.Util

@[ext]
structure Instruction where
  offDst : Bitvec 16
  offOp0 : Bitvec 16
  offOp1 : Bitvec 16
  flags : Bitvec 15
  deriving DecidableEq

-- flag bits

-- mathport name: exprDST_REG
notation "DST_REG" => 0

-- mathport name: exprOP0_REG
notation "OP0_REG" => 1

-- mathport name: exprOP1_IMM
notation "OP1_IMM" => 2

-- mathport name: exprOP1_FP
notation "OP1_FP" => 3

-- mathport name: exprOP1_AP
notation "OP1_AP" => 4

-- mathport name: exprRES_ADD
notation "RES_ADD" => 5

-- mathport name: exprRES_MUL
notation "RES_MUL" => 6

-- mathport name: exprPC_JUMP_ABS
notation "PC_JUMP_ABS" => 7

-- mathport name: exprPC_JUMP_REL
notation "PC_JUMP_REL" => 8

-- mathport name: exprPC_JNZ
notation "PC_JNZ" => 9

-- mathport name: exprAP_ADD
notation "AP_ADD" => 10

-- mathport name: exprAP_ADD1
notation "AP_ADD1" => 11

-- mathport name: exprOPCODE_CALL
notation "OPCODE_CALL" => 12

-- mathport name: exprOPCODE_RET
notation "OPCODE_RET" => 13

-- mathport name: exprOPCODE_ASSERT_EQ
notation "OPCODE_ASSERT_EQ" => 14

namespace Instruction

variable (i : Instruction)

def dstReg := i.flags.get DST_REG
def op0Reg := i.flags.get OP0_REG
def op1Imm := i.flags.get OP1_IMM

-- op1 src
def op1Fp := i.flags.get OP1_FP

-- op1 src
def op1Ap := i.flags.get OP1_AP

-- op1 src
def resAdd := i.flags.get RES_ADD

-- res logic
def resMul := i.flags.get RES_MUL

-- res logic
def pcJumpAbs := i.flags.get PC_JUMP_ABS

-- pc update
def pcJumpRel := i.flags.get PC_JUMP_REL

-- pc update
def pcJnz := i.flags.get PC_JNZ

-- pc update
def apAdd := i.flags.get AP_ADD

-- ap update
def apAdd1 := i.flags.get AP_ADD1

-- ap update
def opcodeCall := i.flags.get OPCODE_CALL

-- opcode
def opcodeRet := i.flags.get OPCODE_RET

-- opcode
def opcodeAssertEq := i.flags.get OPCODE_ASSERT_EQ

-- opcode
def toNat (inst : Instruction) : ℕ :=
  inst.offDst.toNatr + 2 ^ 16 * inst.offOp0.toNatr + 2 ^ 32 * inst.offOp1.toNatr +
    2 ^ 48 * inst.flags.toNatr

end Instruction