/-
Cairo machine instructions.
-/
import Verification.Semantics.Util

@[ext]
structure Instruction where
  offDst : BitVec 16
  offOp0 : BitVec 16
  offOp1 : BitVec 16
  -- flags
  dstReg : Bool
  op0Reg : Bool
  op1Imm : Bool
  op1Fp : Bool
  op1Ap : Bool
  resAdd : Bool
  resMul : Bool
  pcJumpAbs : Bool
  pcJumpRel : Bool
  pcJnz : Bool
  apAdd : Bool
  apAdd1 : Bool
  opcodeCall : Bool
  opcodeRet : Bool
  opcodeAssertEq : Bool
  deriving DecidableEq

-- flag bits
notation "DST_REG" => 0
notation "OP0_REG" => 1
notation "OP1_IMM" => 2
notation "OP1_FP" => 3
notation "OP1_AP" => 4
notation "RES_ADD" => 5
notation "RES_MUL" => 6
notation "PC_JUMP_ABS" => 7
notation "PC_JUMP_REL" => 8
notation "PC_JNZ" => 9
notation "AP_ADD" => 10
notation "AP_ADD1" => 11
notation "OPCODE_CALL" => 12
notation "OPCODE_RET" => 13
notation "OPCODE_ASSERT_EQ" => 14

namespace Instruction

variable (i : Instruction)

def flags (inst : Instruction) : BitVec 15 := BitVec.ofBoolListLE [inst.dstReg, inst.op0Reg, inst.op1Imm,
      inst.op1Fp, inst.op1Ap, inst.resAdd, inst.resMul, inst.pcJumpAbs,
      inst.pcJumpRel, inst.pcJnz, inst.apAdd, inst.apAdd1, inst.opcodeCall,
      inst.opcodeRet, inst.opcodeAssertEq]

def toNat (inst : Instruction) : ℕ :=
  inst.offDst.toNat + 2 ^ 16 * inst.offOp0.toNat + 2 ^ 32 * inst.offOp1.toNat +
    2 ^ 48 * inst.flags.toNat

theorem dstReg_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.dstReg = i2.dstReg := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 0) h
    simp at h'; exact h'

theorem op0Reg_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.op0Reg = i2.op0Reg := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 1) h
    simp at h'; exact h'

theorem op1Imm_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.op1Imm = i2.op1Imm := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 2) h
    simp at h'; exact h'

theorem op1Fp_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.op1Fp = i2.op1Fp := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 3) h
    simp at h'; exact h'

theorem op1Ap_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.op1Ap = i2.op1Ap := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 4) h
    simp at h'; exact h'

theorem resAdd_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.resAdd = i2.resAdd := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 5) h
    simp at h'; exact h'

theorem resMul_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.resMul = i2.resMul := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 6) h
    simp at h'; exact h'

theorem pcJumpAbs_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.pcJumpAbs = i2.pcJumpAbs := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 7) h
    simp at h'; exact h'

theorem pcJumpRel_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.pcJumpRel = i2.pcJumpRel := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 8) h
    simp at h'; exact h'

theorem pcJnz_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.pcJnz = i2.pcJnz := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 9) h
    simp at h'; exact h'

theorem apAdd_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.apAdd = i2.apAdd := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 10) h
    simp at h'; exact h'

theorem apAdd1_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.apAdd1 = i2.apAdd1 := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 11) h
    simp at h'; exact h'

theorem opcodeCall_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.opcodeCall = i2.opcodeCall := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 12) h
    simp at h'; exact h'

theorem opcodeRet_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.opcodeRet = i2.opcodeRet := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 13) h
    simp at h'; exact h'

theorem opcodeAssertEq_eq_of_flags_eq {i1 i2 : Instruction} (h : i1.flags = i2.flags) :
    i1.opcodeAssertEq = i2.opcodeAssertEq := by
    rw [flags, flags] at h
    have h' := congrArg (fun fs => BitVec.getLsbD fs 14) h
    simp at h'; exact h'

end Instruction
