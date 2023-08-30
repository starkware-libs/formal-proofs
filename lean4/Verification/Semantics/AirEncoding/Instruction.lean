/-
Theorem 1 in Section 9.4 of the whitepaper, dealing with the encoding of an instruction as a field
element.

TODO(Jeremy): Although `Fin.rev` still exists, Mathlib now favors `Fin.revPerm`, and e.g.
`Fin.rev_rev` has been renamed to `Fin.revPerm_revPerm`.
-/
import Verification.Semantics.Util
import Verification.Semantics.Cpu
import Verification.Semantics.AirEncoding.Constraints

open scoped BigOperators

/-
Note: this is needed for the `classical.some`, but we can possibly remove it
based on the data from the range_check, if we assume `F` has decidable equality.
-/
noncomputable section

/- The tilde encoding of bit vectors.  -/
namespace Bitvec

variable {n : ℕ} (b : Bitvec n)

def tilde (i : Fin (n + 1)) : ℕ :=
  ∑ j in i.revPerm.range, (2 ^ ((Fin.castSucc (Fin.revPerm j)) - i : ℕ) * (b.get (Fin.revPerm j)).toNat)

@[simp]
theorem tilde_last : b.tilde (Fin.last n) = 0 := by
  rw [tilde, Fin.revPerm_last, Fin.sum_range_zero]

theorem tilde_succ (i : Fin n) : b.tilde (Fin.castSucc i) = 2 * b.tilde i.succ + (b.get i).toNat := by
  rw [tilde, tilde, Fin.rev_castSucc, Fin.sum_range_succ, Finset.mul_sum, add_comm, Fin.revPerm_revPerm,
    Nat.sub_self, pow_zero, one_mul, ← Fin.castSucc_revPerm]
  congr 1
  apply Finset.sum_congr rfl
  intro j; rw [Fin.mem_range, Fin.castSucc_lt_castSucc_iff]; intro hj
  rw [← mul_assoc, ← pow_succ, Fin.val_succ, Nat.sub_succ, Fin.coe_castSucc, Fin.coe_castSucc];
  congr; symm; apply Nat.succ_pred_eq_of_pos
  apply Nat.sub_pos_of_lt
  rwa [← Fin.lt_iff_val_lt_val, ← Fin.revPerm_lt_revPerm, Fin.revPerm_revPerm]

section

variable {α : Type _} [Semiring α]

theorem tilde_spec (f : Fin (n + 1) → α) (h0 : f (Fin.last n) = 0)
    (hsucc : ∀ i : Fin n, f (Fin.castSucc i) = 2 * f i.succ + (b.get i).toNat) :
    ∀ i : Fin (n + 1), f i = b.tilde i := by
  intro i
  rw [← Fin.revPerm_revPerm i]
  generalize (Fin.revPerm i) = j
  induction' j using Fin.inductionOn with i ih
  · rw [Fin.revPerm_zero, h0, tilde_last, Nat.cast_zero]
  rw [← Fin.castSucc_revPerm, tilde_succ, hsucc, ← Fin.rev_castSucc, ih]
  simp only [Bool.toNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

end

theorem tilde_spec_nat (f : Fin (n + 1) → ℕ) (h0 : f (Fin.last n) = 0)
    (hsucc : ∀ i : Fin n, f (Fin.castSucc i) = 2 * f i.succ + (b.get i).toNat) : f = b.tilde := by
  ext n
  rw [tilde_spec b f h0]; simp; exact hsucc

theorem tilde_zero_eq : b.tilde 0 = b.toNatr := by
  rw [Bitvec.toNatr, tilde, Fin.revPerm_zero, Fin.range_last, Fin.val_zero]
  induction' n with n ih
  · rw [Vector.eq_nil b]; rfl
  rw [Fin.sum_univ_castSucc]
  conv =>
    rhs
    rw [← Vector.cons_head_tail b]
  rw [Vector.reverse_cons, Bitvec.toNat_append, ← ih (Vector.tail b)]
  congr
  · rw [mul_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp; rw [← mul_assoc, ← pow_succ, Fin.rev_castSucc]
    congr
    apply tsub_eq_of_eq_add_rev
    rw [add_comm, add_assoc, add_comm 1, Nat.sub_add_cancel]
    exact j.2
  rw [Bitvec.singleton_toNat]; simp

def fromTilde (f : Fin (n + 1) → ℕ) : Bitvec n :=
  Vector.ofFn fun i : Fin n => Bool.ofNat <| f (Fin.castSucc i) - 2 * f i.succ

theorem fromTilde_tilde : fromTilde b.tilde = b := by
  ext i; dsimp [fromTilde]
  rw [Vector.get_ofFn, tilde_succ, add_comm, Nat.add_sub_cancel, Bool.ofNat_toNat]

theorem tilde_zero_inj {b1 b2 : Bitvec n} (h : b1.tilde 0 = b2.tilde 0) : b1 = b2 := by
  rw [tilde_zero_eq, tilde_zero_eq] at h
  have := toNat_inj h
  have h' := congr_arg Vector.reverse this
  rwa [Vector.reverse_reverse, Vector.reverse_reverse] at h'

end Bitvec

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
      apply inst.offDst.toNatr_le
      apply Nat.mul_le_mul_left
      apply inst.offOp0.toNatr_le
      apply Nat.mul_le_mul_left
      apply inst.offOp1.toNatr_le
      apply Nat.mul_le_mul_left
      apply Bitvec.toNatr_le
    _ = 2 ^ 63 - 1 := by norm_num
    _ < 2 ^ 63 := by norm_num


theorem toNat_eq (inst : Instruction) : inst.toNat = inst.offDst.toNatr +
  2 ^ 16 * (inst.offOp0.toNatr + 2 ^ 16 * (inst.offOp1.toNatr + 2 ^ 16 * inst.flags.toNatr)) :=
  by rw [Instruction.toNat]; ring

theorem toNat_inj {i1 i2 : Instruction} (h : i1.toNat = i2.toNat) : i1 = i2 := by
  have nez : 2 ^ 16 ≠ 0; norm_num
  rw [toNat_eq, toNat_eq] at h
  have h1 : i1.offDst.toNatr = i2.offDst.toNatr :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offDst.toNatr_lt] at this
    rwa [Nat.mod_eq_of_lt i2.offDst.toNatr_lt] at this
  rw [h1, add_right_inj, mul_right_inj' nez] at h
  have h2 : i1.offOp0.toNatr = i2.offOp0.toNatr :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offOp0.toNatr_lt] at this
    rwa [Nat.mod_eq_of_lt i2.offOp0.toNatr_lt] at this
  rw [h2, add_right_inj, mul_right_inj' nez] at h
  have h3 : i1.offOp1.toNatr = i2.offOp1.toNatr :=
    by
    have := congr_arg (fun i => i % 2 ^ 16) h; dsimp at this
    simp [Nat.add_mul_mod_self_left] at this
    rw [Nat.mod_eq_of_lt i1.offOp1.toNatr_lt] at this
    rwa [Nat.mod_eq_of_lt i2.offOp1.toNatr_lt] at this
  rw [h3, add_right_inj, mul_right_inj' nez] at h
  apply
    Instruction.ext _ _ (Bitvec.toNatr_inj h1) (Bitvec.toNatr_inj h2) (Bitvec.toNatr_inj h3)
      (Bitvec.toNatr_inj h)

end Instruction

/- Theorem 1.  -/
section TheoremOne

variable {F : Type _} [Field F]

-- so far, this is not used: [fintype F]
variable (char_ge : ringChar F ≥ 2 ^ 63)

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

section

theorem exists_bool_f_tilde_eq (i : Fin 15) : ∃ b : Bool, f_tilde.toF i = ↑b.toNat := by
  cases' eq_zero_or_eq_zero_of_mul_eq_zero (h_bit i) with h h
  · use false; rw [h]; simp only [Bool.toNat, Bool.cond_false, Nat.cast_zero]
  use true; rw [eq_of_sub_eq_zero h]; exact Nat.cast_one.symm

end

def flagVec : Bitvec 15 := Vector.ofFn fun i => Classical.choose (exists_bool_f_tilde_eq h_bit i)

theorem flagVec_spec (i : Fin 15) : ↑((flagVec h_bit).get i).toNat = f_tilde.toF i := by
  rw [flagVec, Vector.get_ofFn, ← Classical.choose_spec (exists_bool_f_tilde_eq h_bit i)]

section

theorem f_tilde_eq : ∀ (i : Fin (15 + 1)), f_tilde i = (flagVec h_bit).tilde i := by
  apply Bitvec.tilde_spec _ _ h_last_value
  intro i
  rw [add_comm (2 * f_tilde _)]
  apply eq_add_of_sub_eq
  symm; apply flagVec_spec

end

def theInstruction : Instruction where
  offDst := Bitvec.ofNatr 16 (offDstNat offDst_in_range)
  offOp0 := Bitvec.ofNatr 16 (offOp0Nat offOp0_in_range)
  offOp1 := Bitvec.ofNatr 16 (offOp1Nat offOp1_in_range)
  flags := flagVec h_bit

/- The main theorem: -/
section

--include h_instruction h_last_value

theorem inst_eq :
  inst = (theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).toNat := by
  rw [h_instruction, theInstruction, Instruction.toNat]
  simp [Bitvec.toNatr_ofNatr]
  have := f_tilde_eq h_bit h_last_value 0
  rw [Nat.mod_eq_of_lt (offOp0_lt offOp0_in_range),
    Nat.mod_eq_of_lt (offOp1_lt offOp1_in_range), Nat.mod_eq_of_lt (offDst_lt offDst_in_range),
    ← offOp0_eq offOp0_in_range, ← offOp1_eq offOp1_in_range, ← offDst_eq offDst_in_range,
    this, Bitvec.tilde_zero_eq]

end

theorem offDst_tilde_eq :
  offDst_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offDst.toNatr := by
  dsimp [theInstruction]
  trans
  apply offDst_eq offDst_in_range
  rw [Bitvec.toNatr_ofNatr, Nat.mod_eq_of_lt (offDst_lt offDst_in_range)]

theorem offOp0_tilde_eq :
  offOp0_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offOp0.toNatr := by
  dsimp [theInstruction]
  trans
  apply offOp0_eq offOp0_in_range
  rw [Bitvec.toNatr_ofNatr, Nat.mod_eq_of_lt (offOp0_lt offOp0_in_range)]

theorem offOp1_tilde_eq :
  offOp1_tilde = ↑(theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).offOp1.toNatr := by
  dsimp [theInstruction]
  trans
  apply @offOp1_eq F _ _ offOp1_in_range
  rw [Bitvec.toNatr_ofNatr, Nat.mod_eq_of_lt (offOp1_lt offOp1_in_range)]

theorem f_tilde_toF_eq :
  ∀ i, f_tilde.toF i =
      ↑((theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).flags.get i).toNat := by
  intro i
  dsimp [theInstruction]
  symm
  apply flagVec_spec

section Uniqueness

variable (char_ge : CharGe263 F)

theorem inst_unique (i1 i2 : Instruction) (h : (i1.toNat : F) = i2.toNat) : i1 = i2 := by
  have h1 : i1.toNat < ringChar F := lt_of_lt_of_le i1.toNat_le char_ge.h
  have h2 : i2.toNat < ringChar F := lt_of_lt_of_le i2.toNat_le char_ge.h
  have : i1.toNat = i2.toNat := Nat.cast_inj_of_lt_char h1 h2 h
  exact Instruction.toNat_inj this

theorem inst_unique' (i : Instruction) (h : inst = i.toNat) :
    i = theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range := by
  apply inst_unique char_ge
  rw [← h]; apply inst_eq; apply h_instruction
  exact h_last_value

end Uniqueness

end TheoremOne