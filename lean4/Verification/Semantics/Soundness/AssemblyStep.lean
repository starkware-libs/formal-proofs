/-
This file proves theorems characterizing the next state for each assembly language instruction,
by unfolding it to the machine instruction and unraveling the CPU semantics.
-/
import Verification.Semantics.Cpu
import Verification.Semantics.Assembly

/-- Lifts the `next_state` semantics from machine instructions to assembly instructions. -/

def Instr.NextState {F : Type _} [Field F] [DecidableEq F] (i : Instr) (mem : F → F)
    (s t : RegisterState F) :=
  i.toInstruction.NextState mem s t

/- Functions for clipping natural numbers and integers to the right range.  -/

section
variable {F : Type _} [Field F]

def intClip (x : Int) : F := natClip x - 2 ^ 15

theorem intClip_eq {x : Int} (h₁ : -2 ^ 15 ≤ x) (h₂ : x < 2 ^ 15) : (intClip x : F) = x := by
  have h : (x + 2 ^ 15).toNat ≤ 2 ^ 16 - 1 := by
    rw [Int.toNat_le, Int.ofNat_sub]
    apply Int.le_sub_one_of_lt
    apply lt_of_lt_of_le (add_lt_add_right h₂ _)
    norm_num; norm_num
  rw [intClip, natClip, Nat.mod_eq_of_lt]
  have h' : x = ((x + 2 ^ 15).toNat : ℤ) - 2 ^ 15 := by
    apply eq_sub_of_add_eq;
    rw [Int.toNat_of_nonneg]; linarith
  . conv => rhs; rw [h']; simp
  . apply Nat.lt_of_succ_le
    convert Nat.succ_le_succ h using 1

theorem intClip_eq' (x : Int) : intClip x = ((natClip x - 2 ^ 15 : Int) : F) := by simp [intClip]

@[simp] theorem Int.zero_clip : intClip 0 = (0 : F) := by rw [intClip_eq] <;> norm_num

@[simp] theorem clip_checked (x : Int) (h₁ : -2 ^ 15 ≤ x) (h₂ : x < 2 ^ 15) :
    (intClip (@checked x h₁ h₂) : F) = ↑x :=
  intClip_eq h₁ h₂

theorem neg_checked_hyps {x : Int} (h₁ : -2 ^ 15 < x) (h₂ : x < 2 ^ 15) :
  -2 ^ 15 ≤ -x ∧ -x < 2 ^ 15 := by
  simp only [neg_le_neg_iff]
  exact ⟨le_of_lt h₂, neg_lt_neg h₁⟩

theorem neg_checked_eq (x : Int) (h₁ : -(2 ^ 15) ≤ x) (h₂ : x < 2 ^ 15)
  (h₃ : x ≠ - (2 ^ 15)) :
  -(@checked x h₁ h₂) = @checked (-x)
    (neg_checked_hyps (lt_of_le_of_ne h₁ h₃.symm) h₂).1
    (neg_checked_hyps (lt_of_le_of_ne h₁ h₃.symm) h₂).2 := by rfl

theorem neg_clip_checked (x : Int) (h₁ : -2 ^ 15 ≤ x) (h₂ : x < 2 ^ 15) :
    x ≠ - (2 ^ 15) →
    (intClip (-@checked x h₁ h₂) : F) = ↑(-x) := by
  intro hx
  rw [neg_checked_eq, clip_checked]
  exact hx

end

/- Semantics of the assembly language.  -/

section
variable {F : Type _} [Field F]
variable (mem : F → F)
variable (s t : RegisterState F)
variable (op0 : Op0Spec) (res : ResSpec) (dst : DstSpec) (ap_update : Bool)

@[simp] def bumpAp : Bool → F
  | true => s.ap + 1
  | false => s.ap

@[simp] def computeOp0 : Op0Spec → F
  | Op0Spec.ap_plus i => mem (s.ap + intClip i)
  | Op0Spec.fp_plus i => mem (s.fp + intClip i)

@[simp] def computeOp1 : Op1Spec → F
  | Op1Spec.mem_op0_plus i => mem (computeOp0 mem s op0 + intClip i)
  | Op1Spec.mem_pc_plus i => mem (s.pc + intClip i)
  | Op1Spec.mem_fp_plus i => mem (s.fp + intClip i)
  | Op1Spec.mem_ap_plus i => mem (s.ap + intClip i)

@[simp] def computeDst : DstSpec → F
  | DstSpec.mem_ap_plus i => mem (s.ap + intClip i)
  | DstSpec.mem_fp_plus i => mem (s.fp + intClip i)

@[simp] def computeRes : ResSpec → F
  | ResSpec.op1 o1 => computeOp1 mem s op0 o1
  | ResSpec.op0_plus_op1 o1 => computeOp0 mem s op0 + computeOp1 mem s op0 o1
  | ResSpec.op0_times_op1 o1 => computeOp0 mem s op0 * computeOp1 mem s op0 o1

@[simp] def bumpPc : Bool → F
  | false => s.pc + 1
  | true => s.pc + 2

@[simp] def jumpPc : Bool → F → F
  | false, i => s.pc + i
  | true, i => i

/- Characterize one-step behavior of the assembly instructions.  -/

theorem instruction_op0_eq (i : Instruction) (op0 : Op0Spec)
      (h : i.op0Reg = op0.op0Reg)
      (h' : i.offOp0.toNatr = natClip op0.offOp0) :
    i.op0 mem s = computeOp0 mem s op0 := by
  cases op0 <;> simp [Instruction.op0, h, h', Bitvec.toBiased16, intClip]

theorem instruction_op1_eq (i : Instruction) (op0 : Op0Spec) (op1 : Op1Spec)
      (h : i.op0 mem s = computeOp0 mem s op0)
      (h' : i.offOp1.toNatr = natClip op1.op1)  :
    (match op1.op1Imm, op1.op1Fp, op1.op1Ap with
      | false, false, false => some (mem (i.op0 mem s + i.offOp1.toBiased16))
      |  true, false, false => some (mem (s.pc + i.offOp1.toBiased16))
      | false,  true, false => some (mem (s.fp + i.offOp1.toBiased16))
      | false, false,  true => some (mem (s.ap + i.offOp1.toBiased16))
      | _, _, _ => none)
    = some (computeOp1 mem s op0 op1) := by
  cases op1 <;> simp [h, h', -computeOp0, Bitvec.toBiased16, intClip]

theorem instruction_res_aux_eq (i : Instruction) (op0 : Op0Spec) (res : ResSpec)
      (hop0: i.op0 mem s = computeOp0 mem s op0)
      (hop1: i.op1 mem s = some (computeOp1 mem s op0 (res.toOp1))) :
    (match i.op1 mem s, res.resAdd, res.resMul with
      | some op1, false, false => some op1
      | some op1, true, false  => some (i.op0 mem s + op1)
      | some op1, false, true  => some (i.op0 mem s * op1)
      | _, _, _ => none)
    = some (computeRes mem s op0 res) := by
  rw [hop1]; cases res <;> simp [hop0]

theorem instruction_dst_eq (i : Instruction) (dst : DstSpec)
      (h : i.dstReg = dst.dstReg)
      (h' : i.offDst.toNatr = natClip dst.offDst) :
    i.dst mem s = computeDst mem s dst := by
  cases dst <;> simp [Instruction.dst, h, h', Bitvec.toBiased16, intClip]

variable [DecidableEq F]

theorem nextState_assert_eq :
    (assertEqInstr op0 res dst ap_update).NextState mem s t ↔
      t.pc = bumpPc s res.toOp1.op1Imm ∧
        t.ap = bumpAp s ap_update ∧ t.fp = s.fp ∧
        computeDst mem s dst = computeRes mem s op0 res := by
  let instr := (assertEqInstr op0 res dst ap_update).toInstruction
  have hop0 : instr.op0 mem s = computeOp0 mem s op0 := by
    apply instruction_op0_eq <;> simp [assertEqInstr]
  have hop1 : instr.op1 mem s = computeOp1 mem s op0 res.toOp1 := by
    apply instruction_op1_eq (h := hop0); simp [assertEqInstr]
  have hres : instr.res mem s = some (computeRes mem s op0 res) := by
    apply instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  have hdst : instr.dst mem s = computeDst mem s dst := by
    apply instruction_dst_eq <;> simp [assertEqInstr]
  apply and_congr
  . show s.pc + instr.size = _ ↔ _
    simp [Instruction.size, assertEqInstr, -ResSpec.toOp1]
    have : (1 : F) + 1 = 2 := by norm_num
    cases ResSpec.toOp1 res <;>
      simp only [cond_true, cond_false, Nat.cast_zero, Nat.cast_one, zero_add, this] <;> exact comm
  apply and_congr
  . simp [Instruction.nextAp, Instruction.nextApAux, assertEqInstr, Option.Agrees]
    cases ap_update <;> simp <;> exact comm
  apply and_congr
  .  simp [Instruction.nextFp, assertEqInstr, Option.Agrees]; exact comm
  show Option.Agrees (instr.res mem s) (instr.dst mem s) ↔ _
  simp only [hres, hdst, Option.Agrees]; exact comm

theorem nextState_jump (jump_abs : Bool) :
    (jumpInstr jump_abs op0 res ap_update).NextState mem s t ↔
      t.pc = jumpPc s jump_abs (computeRes mem s op0 res) ∧
        t.ap = bumpAp s ap_update ∧ t.fp = s.fp := by
  let instr := (jumpInstr jump_abs op0 res ap_update).toInstruction
  simp only [Instr.NextState, Instruction.NextState]
  have hop0 : instr.op0 mem s = computeOp0 mem s op0 := by
    apply instruction_op0_eq <;> simp [jumpInstr]
  have hop1 : instr.op1 mem s = computeOp1 mem s op0 res.toOp1 := by
    apply instruction_op1_eq (h := hop0); simp [jumpInstr]
  have hres : instr.res mem s = some (computeRes mem s op0 res) := by
    cases jump_abs <;> apply instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  apply and_congr
  . cases jump_abs
    . show Option.Agrees (match instr.res mem s with
                            | some res => some (s.pc + res)
                            | none => none) _ ↔ t.pc = s.pc + computeRes mem s op0 res
      simp only [hres, Option.Agrees]; exact comm
    . show Option.Agrees (instr.res mem s) _ ↔ t.pc = computeRes mem s op0 res
      simp only [hres, Option.Agrees]; exact comm
  apply and_congr
  . simp [Instruction.nextAp, Instruction.nextApAux, Option.Agrees]
    cases ap_update <;> simp <;> exact comm
  simp [Instruction.nextFp, Instruction.Asserts, jumpInstr, Option.Agrees]; exact comm

theorem nextState_jnz (op1 : Op1Spec) :
    (jnzInstr op0 op1 dst ap_update).NextState mem s t ↔
      (t.pc =
          if computeDst mem s dst = 0 then bumpPc s op1.op1Imm
          else s.pc + computeOp1 mem s op0 op1) ∧
        t.ap = bumpAp s ap_update ∧ t.fp = s.fp := by
  let instr := (jnzInstr op0 op1 dst ap_update).toInstruction
  have hop0 : instr.op0 mem s = computeOp0 mem s op0 := by
    apply instruction_op0_eq <;> simp [jnzInstr]
  have hop1 : instr.op1 mem s = computeOp1 mem s op0 op1 := by
    apply instruction_op1_eq (h := hop0); simp [jnzInstr]
  have hdst : instr.dst mem s = computeDst mem s dst := by
    apply instruction_dst_eq <;> simp [jnzInstr]
  have hsize : s.pc + instr.size = bumpPc s op1.op1Imm := by
    have : (1 : F) + 1 = 2 := by norm_num
    cases ap_update <;> simp [Instruction.size, jnzInstr] <;> cases op1 <;> simp [this]
  apply and_congr
  . show Option.Agrees (if instr.dst mem s = 0 then some (s.pc + instr.size) else
                          match instr.op1 mem s with
                           | some op1 => some (s.pc + op1)
                           | none => none) _ ↔ _
    simp only [hop1, hdst, hsize, Option.Agrees]; split_ifs <;> (simp [*]; exact comm)
  apply and_congr
  . simp [Instruction.nextAp, Instruction.nextApAux, Option.Agrees]
    cases ap_update <;> simp <;> exact comm
  simp [Instruction.nextFp, Instruction.Asserts, jnzInstr, Option.Agrees]; exact comm

theorem nextState_call (call_abs : Bool) :
    (callInstr call_abs res).NextState mem s t ↔
      t.pc = jumpPc s call_abs (computeRes mem s (Op0Spec.ap_plus 1) res) ∧
      t.ap = s.ap + 2 ∧
      t.fp = s.ap + 2 ∧
      mem (s.ap + 1) = bumpPc s res.toOp1.op1Imm ∧
      mem s.ap = s.fp := by
  let instr := (callInstr call_abs res).toInstruction
  simp only [Instr.NextState, Instruction.NextState]
  have hop0 : instr.op0 mem s = computeOp0 mem s (Op0Spec.ap_plus 1) := by
    apply instruction_op0_eq <;> simp [callInstr]
  have hop1 : instr.op1 mem s = computeOp1 mem s (Op0Spec.ap_plus 1) res.toOp1 := by
    apply instruction_op1_eq (h := hop0); simp [callInstr]
  have hres : instr.res mem s = some (computeRes mem s (Op0Spec.ap_plus 1) res) := by
    cases call_abs <;> apply instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  have hdst : instr.dst mem s = mem s.ap := by
    simp [callInstr, Instruction.dst, Bitvec.toBiased16, intClip, natClip]
    rw [Int.emod_eq_of_lt] <;> simp
  have hsize : s.pc + instr.size = bumpPc s res.toOp1.op1Imm := by
    simp [Instruction.nextPc, callInstr, Option.Agrees, Instruction.size, -ResSpec.toOp1]
    have : (1 : F) + 1 = 2 := by norm_num
    cases ResSpec.toOp1 res <;>
      simp only [cond_true, cond_false, Nat.cast_zero, Nat.cast_one, add_right_inj, zero_add, this]
  apply and_congr
  . cases call_abs
    . show Option.Agrees
        (match instr.res mem s with
          | some res => some (s.pc + res)
          | none => none) _ ↔ t.pc = s.pc + computeRes mem s (Op0Spec.ap_plus 1) res
      simp only [hres, Option.Agrees]; exact comm
    . show Option.Agrees (instr.res mem s) _ ↔ t.pc = computeRes mem s (Op0Spec.ap_plus 1) res
      simp only [hres, Option.Agrees]; exact comm
  apply and_congr
  . simp [Instruction.nextAp, Instruction.nextApAux, Option.Agrees]
    cases ap_update <;> exact comm
  apply and_congr
  . simp [Instruction.nextFp, Instruction.Asserts, callInstr, Option.Agrees]; exact comm
  show instr.op0 mem s = s.pc + instr.size ∧ instr.dst mem s = s.fp ↔ _
  simp only [hsize, hdst, hop0, intClip_eq, computeOp0, Int.cast_one]

theorem nextState_ret :
    retInstr.NextState mem s t ↔ t.pc = mem (s.fp + -1) ∧ t.ap = s.ap ∧ t.fp = mem (s.fp - 2) := by
  simp [Instr.NextState, retInstr, Instruction.NextState, Option.Agrees, Instruction.nextPc,
    Instruction.size, Instruction.nextFp, Instruction.nextAp, Instruction.Asserts, Instruction.dst,
    Instruction.nextApAux, Instruction.res, Instruction.resAux, Instruction.op1]
  rw [Bitvec.toBiased16, Instr.offOp1_toInstruction]; dsimp
  rw [Bitvec.toBiased16, Instr.offDst_toInstruction]; dsimp
  rw [← intClip_eq', ← intClip_eq', intClip_eq, intClip_eq, sub_eq_add_neg] <;> norm_num
  repeat' apply and_congr; exact comm
  exact comm

theorem nextState_advance_ap :
    (advanceApInstr op0 res).NextState mem s t ↔
      t.pc = bumpPc s res.toOp1.op1Imm ∧ t.ap = s.ap + computeRes mem s op0 res ∧ t.fp = s.fp := by
  let instr := (advanceApInstr op0 res).toInstruction
  have hop0 : instr.op0 mem s = computeOp0 mem s op0 := by
    apply instruction_op0_eq <;> simp [advanceApInstr]
  have hop1 : instr.op1 mem s = computeOp1 mem s op0 res.toOp1 := by
    apply instruction_op1_eq (h := hop0); simp [advanceApInstr]
  have hres : instr.res mem s = some (computeRes mem s op0 res) := by
    apply instruction_res_aux_eq (hop0 := hop0) (hop1 := hop1)
  apply and_congr
  . show s.pc + instr.size = _ ↔ _
    simp [Instruction.size, advanceApInstr, -ResSpec.toOp1]
    have : (1 : F) + 1 = 2 := by norm_num
    cases ResSpec.toOp1 res <;>
      simp only [cond_true, cond_false, Nat.cast_zero, Nat.cast_one, zero_add, this] <;> exact comm
  apply and_congr
  . show Option.Agrees (match instr.res mem s with
                          | some res => some (s.ap + res)
                          | none => none ) _ ↔ _
    simp only [hres, Option.Agrees]; exact comm
  simp [Instruction.nextFp, Instruction.Asserts, advanceApInstr, Option.Agrees]; exact comm
