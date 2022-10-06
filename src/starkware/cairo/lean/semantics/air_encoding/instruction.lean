/-
Theorem 1 in Section 9.4 of the whitepaper, dealing with the encoding of an instruction as a field
element.
-/
import starkware.cairo.lean.semantics.cpu
import starkware.cairo.lean.semantics.air_encoding.constraints

open_locale big_operators

/-
Note: this is needed for the `classical.some`, but we can possibly remove it
based on the data from the range_check, if we assume `F` has decidable equality.
-/
noncomputable theory

/-
The tilde encoding of bit vectors.
-/

namespace bitvec

variables {n : ℕ} (b : bitvec n)

def tilde (i : fin (n + 1)) : ℕ :=
∑ j in i.rev.range, 2^(j.rev.cast_succ - i : ℕ) * (b.nth j.rev).to_nat

@[simp] theorem tilde_last : b.tilde (fin.last n) = 0 :=
by rw [tilde, fin.rev_last, fin.sum_range_zero]

theorem tilde_succ (i : fin n) :
  b.tilde i.cast_succ = 2 * b.tilde i.succ + (b.nth i).to_nat :=
begin
  rw [tilde, tilde, fin.rev_cast_succ, fin.sum_range_succ, finset.mul_sum,
      add_comm, fin.rev_rev, nat.sub_self, pow_zero, one_mul, ←fin.cast_succ_rev],
  congr' 1,
  apply finset.sum_congr rfl,
  intro j, rw [fin.mem_range, fin.cast_succ_lt_cast_succ_iff], intro hj,
  rw [←mul_assoc, ←pow_succ, fin.coe_succ, nat.sub_succ, fin.coe_cast_succ, fin.coe_cast_succ], congr, symmetry, apply nat.succ_pred_eq_of_pos,
  apply nat.sub_pos_of_lt,
  rwa [←fin.lt_iff_coe_lt_coe, ←fin.rev_lt_rev_iff, fin.rev_rev]
end

section

variables {α : Type*} [semiring α]

theorem tilde_spec (f : fin (n + 1) → α)
    (h0 : f (fin.last n) = 0)
    (hsucc : ∀ i : fin n, f i.cast_succ = 2 * f i.succ + (b.nth i).to_nat) :
  f = λ i, b.tilde i :=
begin
  ext i, rw ←fin.rev_rev i,
  generalize : i.rev = j,
  apply fin.induction_on j,
  { rw [fin.rev_zero, h0, tilde_last, nat.cast_zero] },
  intros i ih,
  rw [←fin.cast_succ_rev, tilde_succ, hsucc, ←fin.rev_cast_succ, ih],
  simp
end

end

theorem tilde_spec_nat (f : fin (n + 1) → ℕ)
    (h0 : f (fin.last n) = 0)
    (hsucc : ∀ i : fin n, f i.cast_succ = 2 * f i.succ + (b.nth i).to_nat) :
  f = b.tilde :=
by { rw (tilde_spec b f h0); simp, exact hsucc }

theorem tilde_zero_eq : b.tilde 0 = b.to_natr :=
begin
  rw [bitvec.to_natr, tilde, fin.rev_zero, fin.range_last, fin.coe_zero],
  induction n with n ih,
  { rw [vector.eq_nil b], refl },
  rw [fin.sum_univ_cast_succ],
  conv { to_rhs, rw ←vector.cons_head_tail b },
  rw [vector.reverse_cons, bitvec.to_nat_append, ←ih (vector.tail b)],
  congr,
  { rw [mul_comm, finset.mul_sum],
    apply finset.sum_congr rfl,
    intros j _,
    simp, rw [←mul_assoc, ←pow_succ, fin.rev_cast_succ],
    congr,
    apply tsub_eq_of_eq_add_rev,
    rw [add_comm, add_assoc, add_comm 1, nat.sub_add_cancel],
    exact j.2, },
  rw [bitvec.singleton_to_nat], simp
end

def from_tilde (f : fin (n+1) → ℕ) : bitvec n :=
vector.of_fn (λ i : fin n, bool.of_nat $
  (f i.cast_succ - 2 * f i.succ))

theorem from_tilde_tilde : from_tilde b.tilde = b :=
begin
  ext i, dsimp [from_tilde],
  rw [vector.nth_of_fn, tilde_succ, add_comm, nat.add_sub_cancel, bool.of_nat_to_nat]
end

theorem tilde_zero_inj {b1 b2 : bitvec n} (h : b1.tilde 0 = b2.tilde 0) : b1 = b2 :=
begin
  rw [tilde_zero_eq, tilde_zero_eq] at h,
  have := to_nat_inj h,
  have h' := congr_arg vector.reverse this,
  rwa [vector.reverse_reverse, vector.reverse_reverse] at h'
end

end bitvec

/-
Converting an instruction to a natural number.

This is only needed for the uniqueness theorem below, which may not be necessary for the
correctness proof.
-/

namespace instruction

theorem to_nat_le (inst : instruction) : inst.to_nat < 2^63 :=
calc
  inst.to_nat ≤ (2^16 - 1) + 2^16 * (2^16 - 1) + 2^32 * (2^16 - 1) + 2^48 * (2^15 - 1) :
    begin
      apply add_le_add,
      apply add_le_add,
      apply add_le_add,
      apply inst.off_dst.to_natr_le,
      apply nat.mul_le_mul_left,
      apply inst.off_op0.to_natr_le,
      apply nat.mul_le_mul_left,
      apply inst.off_op1.to_natr_le,
      apply nat.mul_le_mul_left,
      apply bitvec.to_natr_le
    end
  ... = 2^63 - 1 : by norm_num
  ... < 2^63     : by norm_num

theorem to_nat_eq (inst : instruction) :
  inst.to_nat = inst.off_dst.to_natr + 2^16 * (inst.off_op0.to_natr +
    2^16 * (inst.off_op1.to_natr + 2^16 * inst.flags.to_natr)) :=
by { rw [instruction.to_nat], ring }

theorem to_nat_inj {i1 i2 : instruction} (h : i1.to_nat = i2.to_nat) : i1 = i2 :=
begin
  have nez : 2^16 ≠ 0, norm_num,
  rw [to_nat_eq, to_nat_eq] at h,
  have h1 : i1.off_dst.to_natr = i2.off_dst.to_natr,
  { have := congr_arg (λ i, i % 2^16) h, dsimp at this,
    simp [nat.add_mul_mod_self_left] at this,
    rw [nat.mod_eq_of_lt i1.off_dst.to_natr_lt] at this,
    rwa [nat.mod_eq_of_lt i2.off_dst.to_natr_lt] at this },
  rw [h1, add_right_inj, mul_right_inj' nez] at h,
  have h2 : i1.off_op0.to_natr = i2.off_op0.to_natr,
  { have := congr_arg (λ i, i % 2^16) h, dsimp at this,
    simp [nat.add_mul_mod_self_left] at this,
    rw [nat.mod_eq_of_lt i1.off_op0.to_natr_lt] at this,
    rwa [nat.mod_eq_of_lt i2.off_op0.to_natr_lt] at this },
  rw [h2, add_right_inj, mul_right_inj' nez] at h,
  have h3 : i1.off_op1.to_natr = i2.off_op1.to_natr,
  { have := congr_arg (λ i, i % 2^16) h, dsimp at this,
    simp [nat.add_mul_mod_self_left] at this,
    rw [nat.mod_eq_of_lt i1.off_op1.to_natr_lt] at this,
    rwa [nat.mod_eq_of_lt i2.off_op1.to_natr_lt] at this },
  rw [h3, add_right_inj, mul_right_inj' nez] at h,
  apply instruction.ext _ _ (bitvec.to_natr_inj h1) (bitvec.to_natr_inj h2)
      (bitvec.to_natr_inj h3) (bitvec.to_natr_inj h)
end

end instruction

/-
Theorem 1.
-/

section theorem_one

variables {F : Type*} [field F]
-- so far, this is not used: [fintype F]
variable  (char_ge: ring_char F ≥ 2^63)

/- the data -/

variables {inst
           off_op0_tilde
           off_op1_tilde
           off_dst_tilde : F }

variable  {f_tilde : tilde_type F}

/- the constraints -/

variable  h_instruction : inst = off_dst_tilde + 2^16 * off_op0_tilde + 2^32 * off_op1_tilde +
                                   2^48 * f_tilde 0

variable  h_bit : ∀ i : fin 15, f_tilde.to_f i * (f_tilde.to_f i - 1) = 0

variable  h_last_value : f_tilde ⟨15, by norm_num⟩ = 0

variable  off_op0_in_range : ∃ j : ℕ, j < 2^16 ∧ off_op0_tilde = ↑j

variable  off_op1_in_range : ∃ j : ℕ, j < 2^16 ∧ off_op1_tilde = ↑j

variable  off_dst_in_range  : ∃ j : ℕ, j < 2^16 ∧ off_dst_tilde = ↑j

/- recovering the instruction -/

def off_op0_nat := classical.some off_op0_in_range

theorem off_op0_lt : @off_op0_nat F _ _ off_op0_in_range < 2^16 :=
(classical.some_spec off_op0_in_range).left

theorem off_op0_eq : off_op0_tilde = ↑(@off_op0_nat F _ _ off_op0_in_range) :=
(classical.some_spec off_op0_in_range).right

def off_op1_nat := classical.some off_op1_in_range

theorem off_op1_lt : @off_op1_nat F _ _ off_op1_in_range < 2^16 :=
(classical.some_spec off_op1_in_range).left

theorem off_op1_eq : off_op1_tilde = ↑(@off_op1_nat F _ _ off_op1_in_range) :=
(classical.some_spec off_op1_in_range).right

def off_dst_nat := classical.some off_dst_in_range

theorem off_dst_lt : @off_dst_nat F _ _ off_dst_in_range < 2^16 :=
(classical.some_spec off_dst_in_range).left

theorem off_dst_eq : off_dst_tilde = ↑(@off_dst_nat F _ _ off_dst_in_range) :=
(classical.some_spec off_dst_in_range).right

section

include h_bit

theorem exists_bool_f_tilde_eq (i : fin 15) :
  ∃ b : bool, f_tilde.to_f i = ↑(b.to_nat) :=
begin
  cases eq_zero_or_eq_zero_of_mul_eq_zero (h_bit i) with h h,
  { use ff, rw [h], simp only [bool.to_nat, bool.cond_ff, nat.cast_zero]},
  use tt, rw [eq_of_sub_eq_zero h], exact nat.cast_one.symm
end

end

def flag_vec : bitvec 15 := vector.of_fn $ λ i, classical.some (exists_bool_f_tilde_eq h_bit i)

theorem flag_vec_spec (i : fin 15) : ↑((flag_vec h_bit).nth i).to_nat = f_tilde.to_f i :=
by rw [flag_vec, vector.nth_of_fn, ←classical.some_spec (exists_bool_f_tilde_eq h_bit i)]

section
include h_bit h_last_value

theorem f_tilde_eq : f_tilde = λ i, (flag_vec h_bit).tilde i :=
begin
  apply bitvec.tilde_spec _ _ h_last_value,
  intro i,
  rw add_comm (2 * f_tilde _),
  apply eq_add_of_sub_eq,
  symmetry, apply flag_vec_spec
end
end

def the_instruction : instruction :=
{ off_dst := bitvec.of_natr 16 (off_dst_nat off_dst_in_range),
  off_op0 := bitvec.of_natr 16 (off_op0_nat off_op0_in_range),
  off_op1 := bitvec.of_natr 16 (off_op1_nat off_op1_in_range),
  flags   := flag_vec h_bit }

/-
The main theorem:
-/

section
include h_instruction h_last_value

theorem inst_eq : inst = (the_instruction h_bit off_op0_in_range
                        off_op1_in_range off_dst_in_range).to_nat :=
begin
  rw [h_instruction, the_instruction, instruction.to_nat],
  simp [bitvec.to_natr_of_natr],
  have := congr_fun (f_tilde_eq h_bit h_last_value) 0,
  dsimp at this,
  rw [nat.mod_eq_of_lt (off_op0_lt off_op0_in_range),
         nat.mod_eq_of_lt (off_op1_lt off_op1_in_range),
         nat.mod_eq_of_lt (off_dst_lt off_dst_in_range),
         ←off_op0_eq off_op0_in_range,
         ←off_op1_eq off_op1_in_range,
         ←off_dst_eq off_dst_in_range,
         this, bitvec.tilde_zero_eq]
end
end

theorem off_dst_tilde_eq : off_dst_tilde =
  ↑(the_instruction h_bit off_op0_in_range off_op1_in_range off_dst_in_range).off_dst.to_natr :=
begin
  dsimp [the_instruction],
  transitivity,
  apply (off_dst_eq off_dst_in_range),
  rw [bitvec.to_natr_of_natr, nat.mod_eq_of_lt (off_dst_lt off_dst_in_range)]
end

theorem off_op0_tilde_eq : off_op0_tilde =
  ↑(the_instruction h_bit off_op0_in_range  off_op1_in_range off_dst_in_range).off_op0.to_natr :=
begin
  dsimp [the_instruction],
  transitivity,
  apply (off_op0_eq off_op0_in_range),
  rw [bitvec.to_natr_of_natr, nat.mod_eq_of_lt (off_op0_lt off_op0_in_range)]
end

theorem off_op1_tilde_eq : off_op1_tilde =
  ↑(the_instruction h_bit off_op0_in_range off_op1_in_range off_dst_in_range).off_op1.to_natr :=
begin
  dsimp [the_instruction],
  transitivity,
  apply (@off_op1_eq F _ _ off_op1_in_range),
  rw [bitvec.to_natr_of_natr, nat.mod_eq_of_lt (off_op1_lt off_op1_in_range)]
end

theorem f_tilde_to_f_eq : ∀ i, f_tilde.to_f i =
  ↑((the_instruction h_bit off_op0_in_range off_op1_in_range
      off_dst_in_range).flags.nth i).to_nat :=
begin
  intro i,
  dsimp [the_instruction],
  symmetry,
  apply flag_vec_spec
end

section uniqueness
include char_ge

theorem inst_unique (i1 i2 : instruction) (h : (i1.to_nat : F) = i2.to_nat) :
  i1 = i2 :=
begin
  have h1 : i1.to_nat < ring_char F, from lt_of_lt_of_le i1.to_nat_le char_ge,
  have h2 : i2.to_nat < ring_char F, from lt_of_lt_of_le i2.to_nat_le char_ge,
  have : i1.to_nat = i2.to_nat, from nat.cast_inj_of_lt_char h1 h2 h,
  exact instruction.to_nat_inj this
end

include h_instruction h_last_value

theorem inst_unique' (i : instruction) (h : inst = i.to_nat) :
  i = the_instruction h_bit off_op0_in_range off_op1_in_range off_dst_in_range :=
begin
  apply inst_unique char_ge,
  rw ←h, apply inst_eq, apply h_instruction, apply h_last_value
end
end uniqueness

end theorem_one
