/-
This is a variant of the semantic lemmas in `assembly.lean` that interprets instructions
according to the virtual machine.
-/
import Verification.Semantics.Vm
import Verification.Semantics.Assembly

def Instr.VmNextState (PRIME : Int) (i : Instr) (mem : Mrel → Mrel) (s t : VmRegisterState) :=
  i.toInstruction.VmNextState PRIME mem s t

/-- Lifts the `next_state` vm semantics from machine instructions to assembly instructions. -/

def intClip' (x : Int) : Int :=
  natClip x - 2 ^ 15

theorem intClip'_eq {x : Int} (h₁ : -2 ^ 15 ≤ x) (h₂ : x < 2 ^ 15) : intClip' x = x := by
  have h : (x + 2 ^ 15).toNat ≤ 2 ^ 16 - 1 := by
    rw [Int.toNat_le, Int.ofNat_sub]
    apply Int.le_sub_one_of_lt
    apply lt_of_lt_of_le (add_lt_add_right h₂ _)
    norm_num; norm_num
  rw [intClip', natClip, Nat.mod_eq_of_lt]
  have h' : x = ((x + 2 ^ 15).toNat : ℤ) - 2 ^ 15 := by
    apply eq_sub_of_add_eq;
    rw [Int.toNat_of_nonneg]; linarith
  conv =>
    rhs
    rw [h']
  apply Nat.lt_of_succ_le
  convert Nat.succ_le_succ h using 1

@[simp] theorem clip_checked' (x : Int) (h₁ : -2 ^ 15 ≤ x) (h₂ : x < 2 ^ 15) :
    intClip' (@checked x h₁ h₂) = x :=
  intClip'_eq h₁ h₂

/-
VM semantics of the assembly language.
-/

section
open Mrel
variable (PRIME : Int)
variable (mem : Mrel → Mrel)
variable (s t : VmRegisterState)
variable (op0 : Op0Spec) (res : ResSpec) (dst : DstSpec) (ap_update : Bool)

@[simp] def vmBumpAp : Bool → Int
  | true => s.ap + 1
  | false => s.ap

@[simp] def vmComputeOp0 : Op0Spec → Mrel
  | Op0Spec.ap_plus i => mem (exec (s.ap + intClip' i))
  | Op0Spec.fp_plus i => mem (exec (s.fp + intClip' i))

@[simp] def vmComputeOp1 : Op1Spec → Mrel
  | Op1Spec.mem_op0_plus i => mem (vmComputeOp0 mem s op0 + val (intClip' i))
  | Op1Spec.mem_pc_plus i => mem (prog (s.pc + intClip' i))
  | Op1Spec.mem_fp_plus i => mem (exec (s.fp + intClip' i))
  | Op1Spec.mem_ap_plus i => mem (exec (s.ap + intClip' i))

@[simp] def vmComputeDst : DstSpec → Mrel
  | DstSpec.mem_ap_plus i => mem (exec s.ap + intClip' i)
  | DstSpec.mem_fp_plus i => mem (exec s.fp + intClip' i)

@[simp] def vmComputeRes : ResSpec → Mrel
  | ResSpec.op1 o1 => vmComputeOp1 mem s op0 o1
  | ResSpec.op0_plus_op1 o1 => vmComputeOp0 mem s op0 + vmComputeOp1 mem s op0 o1
  | ResSpec.op0_times_op1 o1 => vmComputeOp0 mem s op0 * vmComputeOp1 mem s op0 o1

@[simp] def vmBumpPc : Bool → Int
  | false => s.pc + 1
  | true => s.pc + 2

@[simp] def vmJumpPc : Bool → Mrel → Int
  | false, a => s.pc + a.toInt
  | true, a => a.toInt

/- Characterize one-step behavior of the assembly instructions.  -/

theorem vm_instruction_op0_eq (i : Instruction) (op0 : Op0Spec)
      (h : i.op0Reg = op0.op0Reg)
      (h' : i.offOp0.toNatr = natClip op0.offOp0) :
    i.vmOp0 mem s = vmComputeOp0 mem s op0 := by
  cases op0 <;> (simp [Instruction.vmOp0, h, h', Bitvec.toBiased16, intClip']; rfl)

theorem vm_instruction_op1_eq (i : Instruction) (op0 : Op0Spec) (op1 : Op1Spec)
      (h : i.vmOp0 mem s = vmComputeOp0 mem s op0)
      (h' : i.offOp1.toNatr = natClip op1.op1)  :
    (match op1.op1Imm, op1.op1Fp, op1.op1Ap with
      | false, false, false => some (mem (i.vmOp0 mem s + i.offOp1.toBiased16))
      |  true, false, false => some (mem (prog (s.pc + i.offOp1.toBiased16)))
      | false,  true, false => some (mem (exec (s.fp + i.offOp1.toBiased16)))
      | false, false,  true => some (mem (exec (s.ap + i.offOp1.toBiased16)))
      | _, _, _ => none)
    = some (vmComputeOp1 mem s op0 op1) := by
  cases op1 <;> simp [h, h', -vmComputeOp0, Bitvec.toBiased16, intClip']

theorem vm_instruction_res_aux_eq (i : Instruction) (op0 : Op0Spec) (res : ResSpec)
      (hop0: i.vmOp0 mem s = vmComputeOp0 mem s op0)
      (hop1: i.vmOp1 mem s = some (vmComputeOp1 mem s op0 (res.toOp1))) :
    (match i.vmOp1 mem s, res.resAdd, res.resMul with
      | some op1, false, false => some op1
      | some op1, true, false  => some (i.vmOp0 mem s + op1)
      | some op1, false, true  => some (i.vmOp0 mem s * op1)
      | _, _, _ => none)
    = some (vmComputeRes mem s op0 res) := by
  rw [hop1]; cases res <;> simp [hop0]

theorem vm_instruction_dst_eq (i : Instruction) (dst : DstSpec)
      (h : i.dstReg = dst.dstReg)
      (h' : i.offDst.toNatr = natClip dst.offDst) :
    i.vmDst mem s = vmComputeDst mem s dst := by
  cases dst <;> simp [Instruction.vmDst, h, h', Bitvec.toBiased16, intClip']

theorem vmNextState_assert_eq :
    (assertEqInstr op0 res dst ap_update).VmNextState PRIME mem s t ↔
      t.pc = vmBumpPc s res.toOp1.op1Imm ∧
        t.ap = vmBumpAp s ap_update ∧
          t.fp = s.fp ∧ Mrel.Equiv PRIME (vmComputeDst mem s dst) (vmComputeRes mem s op0 res) := by
  let instr := (assertEqInstr op0 res dst ap_update).toInstruction
  have hop0 : instr.vmOp0 mem s = vmComputeOp0 mem s op0 := by
    apply vm_instruction_op0_eq <;> simp [assertEqInstr]
  have hop1 : instr.vmOp1 mem s = vmComputeOp1 mem s op0 res.toOp1 := by
    apply vm_instruction_op1_eq (h := hop0); simp [assertEqInstr]
  have hres : instr.vmRes mem s = some (vmComputeRes mem s op0 res) := by
    apply vm_instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  have hdst : instr.vmDst mem s = vmComputeDst mem s dst := by
    apply vm_instruction_dst_eq <;> simp [assertEqInstr]
  apply and_congr
  . show s.pc + instr.vmSize = _ ↔ _
    simp [Instruction.size, assertEqInstr, -ResSpec.toOp1]
    cases ResSpec.toOp1 res <;>
      simp only [cond_true, cond_false, Nat.cast_zero, Nat.cast_one, zero_add] <;> exact comm
  apply and_congr
  . simp [assertEqInstr, Mrel.Agrees]
    cases ap_update <;> simp <;> exact comm
  apply and_congr
  .  simp [assertEqInstr, Mrel.Agrees]; exact comm
  show Mrel.Agrees PRIME (instr.vmRes mem s) (instr.vmDst mem s) ↔ _
  simp only [hres, hdst, Mrel.Agrees]
  constructor <;> apply Mrel.Equiv.symm

theorem vmNextState_jump (jump_abs : Bool) :
    (jumpInstr jump_abs op0 res ap_update).VmNextState PRIME mem s t ↔
      t.pc = vmJumpPc s jump_abs (vmComputeRes mem s op0 res) ∧
        t.ap = vmBumpAp s ap_update ∧ t.fp = s.fp := by
  let instr := (jumpInstr jump_abs op0 res ap_update).toInstruction
  simp only [Instr.VmNextState, Instruction.NextState]
  have hop0 : instr.vmOp0 mem s = vmComputeOp0 mem s op0 := by
    apply vm_instruction_op0_eq <;> simp [jumpInstr]
  have hop1 : instr.vmOp1 mem s = vmComputeOp1 mem s op0 res.toOp1 := by
    apply vm_instruction_op1_eq (h := hop0); simp [jumpInstr]
  have hres : instr.vmRes mem s = some (vmComputeRes mem s op0 res) := by
    cases jump_abs <;> apply vm_instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  apply and_congr
  . cases jump_abs
    . show Option.Agrees
        (match instr.vmRes mem s with
          | some res => some (s.pc + toInt res)
          | none => none) t.pc ↔ t.pc = vmJumpPc s false (vmComputeRes mem s op0 res)
      simp only [hres, Mrel.Agrees]; exact comm
    . simp [Instruction.vmNextPc, jumpInstr]
      show Option.Agrees ((instr.vmRes mem s).map Mrel.toInt) _ ↔ t.pc = (vmComputeRes mem s op0 res).toInt
      simp only [hres, Mrel.Agrees]; exact comm
  apply and_congr
  . simp [Instruction.vmNextAp, Instruction.vmNextApAux, Option.Agrees]
    cases ap_update <;> simp <;> exact comm
  simp [Instruction.vmNextFp, Instruction.VmAsserts, jumpInstr, Option.Agrees]; exact comm

theorem vmNextState_jnz (op1 : Op1Spec) :
    (jnzInstr op0 op1 dst ap_update).VmNextState PRIME mem s t ↔
      (t.pc =
          if vmComputeDst mem s dst = 0 then vmBumpPc s op1.op1Imm
          else s.pc + (vmComputeOp1 mem s op0 op1).toInt) ∧
        t.ap = vmBumpAp s ap_update ∧ t.fp = s.fp := by
  let instr := (jnzInstr op0 op1 dst ap_update).toInstruction
  have hop0 : instr.vmOp0 mem s = vmComputeOp0 mem s op0 := by
    apply vm_instruction_op0_eq <;> simp [jnzInstr]
  have hop1 : instr.vmOp1 mem s = vmComputeOp1 mem s op0 op1 := by
    apply vm_instruction_op1_eq (h := hop0); simp [jnzInstr]
  have hdst : instr.vmDst mem s = vmComputeDst mem s dst := by
    apply vm_instruction_dst_eq <;> simp [jnzInstr]
  have hsize : s.pc + instr.vmSize = vmBumpPc s op1.op1Imm := by
    cases ap_update <;> simp [Instruction.vmSize, jnzInstr] <;> cases op1 <;> simp
  apply and_congr
  . show Option.Agrees (if instr.vmDst mem s = 0 then some (s.pc + instr.vmSize) else
                          match instr.vmOp1 mem s with
                           | some op1 => some (s.pc + toInt op1)
                           | none => none) _ ↔ _
    simp only [hop1, hdst, hsize, Option.Agrees]; split_ifs <;> (simp [*]; exact comm)
  apply and_congr
  . simp [Instruction.vmNextAp, Instruction.vmNextApAux, Mrel.Agrees]
    cases ap_update <;> simp <;> exact comm
  simp [Instruction.vmNextFp, Instruction.VmAsserts, jnzInstr, Mrel.Agrees]; exact comm
