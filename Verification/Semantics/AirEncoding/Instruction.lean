/-
Theorem 1 in Section 9.4 of the whitepaper, dealing with the encoding of an instruction as a field
element.
-/
import Verification.Semantics.Util
import Verification.Semantics.Cpu
import Verification.Semantics.AirEncoding.Constraints

open scoped BigOperators

/-
Note: this is needed for the `Classical.some`, but we can possibly remove it
based on the data from the range_check, if we assume `F` has decidable equality.
-/
noncomputable section

/- The tilde encoding of bit vectors.  -/
namespace BitVec

variable {n : ℕ} (b : BitVec n)

def tilde (i : Fin (n + 1)) : ℕ :=
  ∑ j in i.revPerm.range, (2 ^ ((Fin.castSucc (Fin.revPerm j)) - i : ℕ) * (b.getLsbD (Fin.revPerm j)).toNat)

@[simp]
theorem tilde_last : b.tilde (Fin.last n) = 0 := by
  rw [tilde, Fin.revPerm_last, Fin.sum_range_zero]

theorem tilde_succ (i : Fin n) : b.tilde (Fin.castSucc i) = 2 * b.tilde i.succ + (b.getLsbD i).toNat := by
  rw [tilde, tilde, Fin.revPerm_castSucc, Fin.sum_range_succ, Finset.mul_sum, add_comm, Fin.revPerm_revPerm,
    Nat.sub_self, pow_zero, one_mul, ← Fin.castSucc_revPerm]
  congr 1
  apply Finset.sum_congr rfl
  intro j; rw [Fin.mem_range, Fin.castSucc_lt_castSucc_iff]; intro hj
  rw [← mul_assoc, ← pow_succ', Fin.val_succ, Nat.sub_succ, Fin.coe_castSucc, Fin.coe_castSucc];
  congr; symm; apply Nat.succ_pred_eq_of_pos
  apply Nat.sub_pos_of_lt
  rwa [← Fin.lt_iff_val_lt_val, ← Fin.revPerm_lt_revPerm, Fin.revPerm_revPerm]

theorem tilde_spec {α : Type _} [Semiring α] (f : Fin (n + 1) → α) (h0 : f (Fin.last n) = 0)
    (hsucc : ∀ i : Fin n, f (Fin.castSucc i) = 2 * f i.succ + (b.getLsbD i).toNat) :
    ∀ i : Fin (n + 1), f i = b.tilde i := by
  intro i
  rw [← Fin.revPerm_revPerm i]
  generalize (Fin.revPerm i) = j
  induction' j using Fin.inductionOn with i ih
  · rw [Fin.revPerm_zero, h0, tilde_last, Nat.cast_zero]
  rw [← Fin.castSucc_revPerm, tilde_succ, hsucc, ← Fin.revPerm_castSucc, ih]
  simp only [Bool.toNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem tilde_spec_nat (f : Fin (n + 1) → ℕ) (h0 : f (Fin.last n) = 0)
    (hsucc : ∀ i : Fin n, f (Fin.castSucc i) = 2 * f i.succ + (b.getLsbD i).toNat) : f = b.tilde := by
  ext n
  rw [tilde_spec b f h0]; simp; exact hsucc

theorem tilde_zero_eq : b.tilde 0 = b.toNat := by
  rw [BitVec.toNat, tilde, Fin.revPerm_zero, Fin.range_last, Fin.val_zero]
  induction' n with n ih
  · simp
  rw [Fin.sum_univ_castSucc]
  simp
  simp at ih
  let b' : BitVec n := BitVec.ofFnLE fun i : Fin n => b.getLsbD i.succ
  have hb : b = b'.concat (b.getLsbD 0) := by
    dsimp [b']
    apply BitVec.eq_of_getLsbD_eq
    apply Fin.cases
    . rw [Fin.val_zero, getLsbD_concat_zero]
    . intro i
      rw [Fin.val_succ, getLsbD_concat_succ, getLsbD_ofFnLE]
  conv =>
    rhs
    rw [hb, BitVec.toNat_concat, Bool.toNat, ←ih b']
  dsimp [b']
  congr
  rw [mul_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_assoc]
  congr 1
  . rw [←pow_succ', ← Nat.sub_add_comm (Nat.succ_le_of_lt i.isLt), Nat.succ_sub_succ]
  congr 1
  have : n - (↑i + 1) < n := by
    cases n
    . apply i.elim0
    rw [Nat.succ_sub_succ]
    apply lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
  have : n - (↑i + 1) = Fin.mk _ this := rfl
  rw [this, getLsbD_ofFnLE]; dsimp
  congr
  omega

def fromTilde (f : Fin (n + 1) → ℕ) : BitVec n :=
  BitVec.ofFnLE fun i : Fin n => (Bool.ofNat <| f (Fin.castSucc i) - 2 * f i.succ)

theorem fromTilde_tilde : fromTilde b.tilde = b := by
  dsimp [fromTilde]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [getLsbD_ofFnLE, tilde_succ, add_comm, Nat.add_sub_cancel, Bool.ofNat_toNat]

theorem tilde_zero_inj {b1 b2 : BitVec n} (h : b1.tilde 0 = b2.tilde 0) : b1 = b2 := by
  rw [tilde_zero_eq, tilde_zero_eq] at h
  exact toNat_inj h

end BitVec

/-
Converting an instruction to a natural number.

This is only needed for the uniqueness theorem below, which may not be necessary for the
correctness proof.
-/
namespace Instruction

theorem toNat_le (inst : Instruction) : inst.toNat < 2 ^ 63 :=
  calc
    inst.toNat ≤ 2 ^ 16 - 1 + 2 ^ 16 * (2 ^ 16 - 1) + 2 ^ 32 * (2 ^ 16 - 1) + 2 ^ 48 * (2 ^ 15 - 1) := by
      apply add_le_add
      apply add_le_add
      apply add_le_add
      apply inst.offDst.toNat_le
      apply Nat.mul_le_mul_left
      apply inst.offOp0.toNat_le
      apply Nat.mul_le_mul_left
      apply inst.offOp1.toNat_le
      apply Nat.mul_le_mul_left
      apply BitVec.toNat_le
    _ = 2 ^ 63 - 1 := by norm_num
    _ < 2 ^ 63 := by norm_num


theorem toNat_eq (inst : Instruction) : inst.toNat = inst.offDst.toNat +
  2 ^ 16 * (inst.offOp0.toNat + 2 ^ 16 * (inst.offOp1.toNat + 2 ^ 16 * inst.flags.toNat)) :=
  by rw [Instruction.toNat]; ring

theorem toNat_inj {i1 i2 : Instruction} (h : i1.toNat = i2.toNat) : i1 = i2 := by
  have nez : 2 ^ 16 ≠ 0 := by norm_num
  rw [toNat_eq, toNat_eq] at h
  have h1 : i1.offDst.toNat = i2.offDst.toNat :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offDst.isLt] at this
    rwa [Nat.mod_eq_of_lt i2.offDst.isLt] at this
  rw [h1, add_right_inj, mul_right_inj' nez] at h
  have h2 : i1.offOp0.toNat = i2.offOp0.toNat :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offOp0.isLt] at this
    rwa [Nat.mod_eq_of_lt i2.offOp0.isLt] at this
  rw [h2, add_right_inj, mul_right_inj' nez] at h
  have h3 : i1.offOp1.toNat = i2.offOp1.toNat :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offOp1.isLt] at this
    rwa [Nat.mod_eq_of_lt i2.offOp1.isLt] at this
  rw [h3, add_right_inj, mul_right_inj' nez] at h
  have h' := BitVec.toNat_inj h
  apply
    Instruction.ext (BitVec.toNat_inj h1) (BitVec.toNat_inj h2) (BitVec.toNat_inj h3)
      (dstReg_eq_of_flags_eq h')
      (op0Reg_eq_of_flags_eq h')
      (op1Imm_eq_of_flags_eq h')
      (op1Fp_eq_of_flags_eq h')
      (op1Ap_eq_of_flags_eq h')
      (resAdd_eq_of_flags_eq h')
      (resMul_eq_of_flags_eq h')
      (pcJumpAbs_eq_of_flags_eq h')
      (pcJumpRel_eq_of_flags_eq h')
      (pcJnz_eq_of_flags_eq h')
      (apAdd_eq_of_flags_eq h')
      (apAdd1_eq_of_flags_eq h')
      (opcodeCall_eq_of_flags_eq h')
      (opcodeRet_eq_of_flags_eq h')
      (opcodeAssertEq_eq_of_flags_eq h')

end Instruction

/- Theorem 1.  -/
section TheoremOne

variable {F : Type _} [Field F]

-- the data
variable {inst offOp0_tilde offOp1_tilde offDst_tilde : F}
  {f_tilde : TildeType F}

-- the constraints
variable
  (h_instruction :
    inst = offDst_tilde + 2 ^ 16 * offOp0_tilde + 2 ^ 32 * offOp1_tilde + 2 ^ 48 * f_tilde 0)
  (h_bit : ∀ i : Fin 15, f_tilde.toF i * (f_tilde.toF i - 1) = 0)
  (h_last_value : f_tilde 15 = 0)
  (offOp0_in_range : ∃ j : ℕ, j < 2 ^ 16 ∧ offOp0_tilde = ↑j)
  (offOp1_in_range : ∃ j : ℕ, j < 2 ^ 16 ∧ offOp1_tilde = ↑j)
  (offDst_in_range : ∃ j : ℕ, j < 2 ^ 16 ∧ offDst_tilde = ↑j)

-- recovering the instruction
def offOp0Nat := Classical.choose offOp0_in_range

theorem offOp0_lt : @offOp0Nat F _ _ offOp0_in_range < 2 ^ 16 :=
  (Classical.choose_spec offOp0_in_range).left

theorem offOp0_eq : offOp0_tilde = ↑(@offOp0Nat F _ _ offOp0_in_range) :=
  (Classical.choose_spec offOp0_in_range).right

def offOp1Nat := Classical.choose offOp1_in_range

theorem offOp1_lt : @offOp1Nat F _ _ offOp1_in_range < 2 ^ 16 :=
  (Classical.choose_spec offOp1_in_range).left

theorem offOp1_eq : offOp1_tilde = ↑(@offOp1Nat F _ _ offOp1_in_range) :=
  (Classical.choose_spec offOp1_in_range).right

def offDstNat := Classical.choose offDst_in_range

theorem offDst_lt : @offDstNat F _ _ offDst_in_range < 2 ^ 16 :=
  (Classical.choose_spec offDst_in_range).left

theorem offDst_eq : offDst_tilde = ↑(@offDstNat F _ _ offDst_in_range) :=
  (Classical.choose_spec offDst_in_range).right

include h_bit in
theorem exists_bool_f_tilde_eq (i : Fin 15) : ∃ b : Bool, f_tilde.toF i = ↑b.toNat := by
  cases' eq_zero_or_eq_zero_of_mul_eq_zero (h_bit i) with h h
  · use false; rw [h]; simp only [Bool.toNat, Bool.cond_false, Nat.cast_zero]
  use true; rw [eq_of_sub_eq_zero h]; exact Nat.cast_one.symm

def flagVec : BitVec 15 := BitVec.ofFnLE fun i => Classical.choose (exists_bool_f_tilde_eq h_bit i)

theorem flagVec_spec (i : Fin 15) : ↑((flagVec h_bit).getLsbD i).toNat = f_tilde.toF i := by
rw [flagVec, BitVec.getLsbD_ofFnLE, ← Classical.choose_spec (exists_bool_f_tilde_eq h_bit i)]

include h_last_value in
theorem f_tilde_eq : ∀ (i : Fin (15 + 1)), f_tilde i = (flagVec h_bit).tilde i := by
  apply BitVec.tilde_spec _ _ h_last_value
  intro i
  rw [add_comm (2 * f_tilde _)]
  apply eq_add_of_sub_eq
  symm; apply flagVec_spec

def theInstruction : Instruction where
  offDst := BitVec.ofNat 16 (offDstNat offDst_in_range)
  offOp0 := BitVec.ofNat 16 (offOp0Nat offOp0_in_range)
  offOp1 := BitVec.ofNat 16 (offOp1Nat offOp1_in_range)
  dstReg := (Classical.choose (exists_bool_f_tilde_eq h_bit 0))
  op0Reg := (Classical.choose (exists_bool_f_tilde_eq h_bit 1))
  op1Imm := (Classical.choose (exists_bool_f_tilde_eq h_bit 2))
  op1Fp  := (Classical.choose (exists_bool_f_tilde_eq h_bit 3))
  op1Ap  := (Classical.choose (exists_bool_f_tilde_eq h_bit 4))
  resAdd := (Classical.choose (exists_bool_f_tilde_eq h_bit 5))
  resMul := (Classical.choose (exists_bool_f_tilde_eq h_bit 6))
  pcJumpAbs  := (Classical.choose (exists_bool_f_tilde_eq h_bit 7))
  pcJumpRel  := (Classical.choose (exists_bool_f_tilde_eq h_bit 8))
  pcJnz  := (Classical.choose (exists_bool_f_tilde_eq h_bit 9))
  apAdd  := (Classical.choose (exists_bool_f_tilde_eq h_bit 10))
  apAdd1 := (Classical.choose (exists_bool_f_tilde_eq h_bit 11))
  opcodeCall := (Classical.choose (exists_bool_f_tilde_eq h_bit 12))
  opcodeRet  := (Classical.choose (exists_bool_f_tilde_eq h_bit 13))
  opcodeAssertEq := (Classical.choose (exists_bool_f_tilde_eq h_bit 14))

theorem theInstruction_flags_eq : (theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).flags =
      flagVec h_bit := by
  rw [flagVec, theInstruction, Instruction.flags, BitVec.ofFnLE]; symm
  convert BitVec.ofBoolListLE_cast _ _ rfl _ <;> simp [Fin.foldr_succ]

/- The main theorem: -/
include h_instruction h_last_value in
theorem inst_eq :
  inst = (theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).toNat := by
  rw [h_instruction, Instruction.toNat, theInstruction_flags_eq, theInstruction]
  simp only [Fin.isValue, BitVec.toNat_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  have := f_tilde_eq h_bit h_last_value 0
  rw [Nat.mod_eq_of_lt (offOp0_lt offOp0_in_range),
    Nat.mod_eq_of_lt (offOp1_lt offOp1_in_range), Nat.mod_eq_of_lt (offDst_lt offDst_in_range),
    ← offOp0_eq offOp0_in_range, ← offOp1_eq offOp1_in_range, ← offDst_eq offDst_in_range,
    this, BitVec.tilde_zero_eq]
  norm_num

theorem offDst_tilde_eq :
  offDst_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offDst.toNat := by
  dsimp [theInstruction]
  trans
  apply offDst_eq offDst_in_range
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (offDst_lt offDst_in_range)]

theorem offOp0_tilde_eq :
  offOp0_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offOp0.toNat := by
  dsimp [theInstruction]
  trans
  apply offOp0_eq offOp0_in_range
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (offOp0_lt offOp0_in_range)]

theorem offOp1_tilde_eq :
  offOp1_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offOp1.toNat := by
  dsimp [theInstruction]
  trans
  apply @offOp1_eq F _ _ offOp1_in_range
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (offOp1_lt offOp1_in_range)]

theorem f_tilde_toF_eq :
  ∀ i, f_tilde.toF i =
      ↑((theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).flags.getLsbD i).toNat := by
  intro i
  rw [theInstruction_flags_eq, flagVec_spec h_bit]

section Uniqueness

variable (char_ge : CharGe263 F)

include char_ge

theorem inst_unique (i1 i2 : Instruction) (h : (i1.toNat : F) = i2.toNat) : i1 = i2 := by
  have h1 : i1.toNat < ringChar F := lt_of_lt_of_le i1.toNat_le char_ge.h
  have h2 : i2.toNat < ringChar F := lt_of_lt_of_le i2.toNat_le char_ge.h
  have : i1.toNat = i2.toNat := Nat.cast_inj_of_lt_char h1 h2 h
  exact Instruction.toNat_inj this

include h_instruction h_last_value

theorem inst_unique' (i : Instruction) (h : inst = i.toNat) :
    i = theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range := by
  apply inst_unique char_ge
  rw [← h]; apply inst_eq; apply h_instruction
  exact h_last_value

end Uniqueness

end TheoremOne
