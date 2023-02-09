/-
Range check constraints.
-/
import starkware.cairo.lean.semantics.air_encoding.memory

noncomputable theory
open_locale big_operators

/- trace data -/

variables {F : Type*} [field F]

variables {n : ℕ} {a a' p : fin (n + 1) → F}

variables {z : F}

variables {rc_min rc_max : ℕ}

variable  {T : ℕ}

variables {off_op0_tilde
           off_op1_tilde
           off_dst_tilde
           rc16_vals       : fin T → F}

variables {embed_off_op0
           embed_off_op1
           embed_off_dst
           embed_rc16_vals : fin T → fin (n + 1)}

/- constraints -/

variable h_continuity :
  ∀ i : fin n, (a' i.succ - a' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0

variable h_initial : (z - a' 0) * p 0 = z - a 0

variable h_cumulative : ∀ i : fin n, (z - a' i.succ) * p i.succ = (z - a i.succ) * p i.cast_succ

variable h_final : p (fin.last n) = 1

variable h_rc_min : a' 0 = rc_min

variable h_rc_max : a' (fin.last n) = rc_max

variable h_embed_op0 : ∀ i, a (embed_off_op0 i) = off_op0_tilde i

variable h_embed_op1 : ∀ i, a (embed_off_op1 i) = off_op1_tilde i

variable h_embed_dst : ∀ i, a (embed_off_dst i) = off_dst_tilde i

variable h_embed_rc : ∀ i, a (embed_rc16_vals i) = rc16_vals i

variable h_n_lt : n < ring_char F

variable h_rc_lt : rc_max < 2^16

variable h_rc_le : rc_min ≤ rc_max

variable h_ring_char_gt : 2^16 < ring_char F

section
include h_continuity h_rc_min

lemma rc_a'_eq (j : fin (n + 1)) : a' j = ↑(rc_min + a'_nat_offset a' j) :=
by rw [a'_nat_offset_spec h_continuity j, h_rc_min, nat.cast_add]

include h_rc_max h_rc_le h_rc_lt h_n_lt h_ring_char_gt

lemma rc_nat_offset_eq : rc_min + a'_nat_offset a' (fin.last n) = rc_max :=
begin
  have h₀ : (↑rc_min : F) + ↑(a'_nat_offset a' (fin.last n)) = ↑rc_min + ↑(rc_max - rc_min),
  { rw [←nat.cast_add, ←nat.cast_add, ←rc_a'_eq h_continuity h_rc_min, h_rc_max,
         nat.add_sub_of_le h_rc_le] },
  have h₁ : a'_nat_offset a' (fin.last n) < ring_char F :=
    lt_of_le_of_lt (a'_nat_offset_le _) h_n_lt,
  have h₂ : rc_max - rc_min < ring_char F :=
    lt_of_le_of_lt tsub_le_self (lt_trans h_rc_lt h_ring_char_gt),
  have := add_left_cancel h₀,
  rw nat.cast_inj_of_lt_char h₁ h₂ this,
  apply nat.add_sub_of_le h_rc_le
end

lemma rc_nat_offset_le (j : fin (n + 1)): rc_min + a'_nat_offset a' j ≤ rc_max :=
begin
  rw ←rc_nat_offset_eq h_continuity h_rc_min h_rc_max h_n_lt h_rc_lt h_rc_le h_ring_char_gt,
  apply add_le_add_left,
  apply monotone_a'_nat_offset,
  apply fin.le_last
end

end

section

variable [fintype F]

def bad_set_3 (a a' : fin (n + 1) → F) : finset F :=
polynomial_aux.exceptional_set a a'

theorem card_bad_set_3_le : (bad_set_3 a a').card ≤ n + 1 :=
by { transitivity, apply polynomial_aux.card_exceptional_set_le, simp }

theorem bad_set_3_spec {z : F}
    (h₁ : z ∉ bad_set_3 a a')
    (h₂ : ∏ i : fin (n + 1), (z - a i) = ∏ i, (z - a' i)) :
  ∀ i, ∃ j, a i = a' j :=
exceptional_set_spec _ _ h₁ h₂

theorem bad_set_3_spec' {z : F}
    (h₁ : z ∉ bad_set_3 a a')
    (h₂ : ∏ i : fin (n + 1), (z - a i) = ∏ i, (z - a' i)) :
  ∀ i, ∃ j, a' i = a j:=
exceptional_set_spec' _ _ h₁ h₂

end

section permutation

include h_initial h_cumulative

lemma rc_permutation_aux (j : fin (n + 1)) :
  ∏ i in fin.range j.succ, (z - a i) = (∏ i in fin.range j.succ, (z - a' i)) * p j :=
begin
  apply fin.induction_on j,
  { rw [←fin.one_eq_succ_zero, fin.prod_range_one, fin.prod_range_one, h_initial] },
  intros j ih,
  rw [fin.prod_range_succ, fin.prod_range_succ, ←fin.succ_cast_succ, ih, ←mul_assoc],
  conv { to_rhs, rw [mul_right_comm, h_cumulative, mul_right_comm] }
end

include h_final

lemma rc_permutation_prod_eq : ∏ i, (z - a i) = ∏ i, (z - a' i) :=
by rw [←fin.range_last, ←fin.succ_last, rc_permutation_aux h_initial h_cumulative, h_final, mul_one]

end permutation

variable [fintype F]

variable hprob₃ : z ∉ bad_set_3 a a'

lemma rc_permutation : ∀ i, ∃ j, a i = a' j :=
λ i, bad_set_3_spec hprob₃ (rc_permutation_prod_eq h_initial h_cumulative h_final) i

include h_continuity h_initial h_cumulative h_final hprob₃
include h_rc_min h_rc_max h_rc_le h_rc_lt h_n_lt h_ring_char_gt

section
include h_embed_op0

theorem off_op0_in_range (i : fin T) : ∃ k : ℕ, k < 2^16 ∧ off_op0_tilde i = ↑k :=
begin
  rcases (rc_permutation h_initial h_cumulative h_final hprob₃ (embed_off_op0 i)) with ⟨j, hj⟩,
  have : a' j = a' 0 + a'_nat_offset a' j := a'_nat_offset_spec h_continuity _,
  rw [this, h_embed_op0, h_rc_min, ←nat.cast_add] at hj,
  use [rc_min + a'_nat_offset a' j],
  split,
  { apply lt_of_le_of_lt _ h_rc_lt,
    apply rc_nat_offset_le h_continuity h_rc_min h_rc_max h_n_lt h_rc_lt h_rc_le h_ring_char_gt },
  exact hj
end
end

theorem off_op1_in_range (i : fin T) : ∃ k : ℕ, k < 2^16 ∧ off_op1_tilde i = ↑k :=
off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min
  h_rc_max h_embed_op1 h_n_lt h_rc_lt h_rc_le h_ring_char_gt hprob₃ i

theorem off_dst_in_range (i : fin T) : ∃ k : ℕ, k < 2^16 ∧ off_dst_tilde i = ↑k :=
off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min
  h_rc_max h_embed_dst h_n_lt h_rc_lt h_rc_le h_ring_char_gt hprob₃ i

theorem rc16_vals_in_range (i : fin T) : ∃ k : ℕ, k < 2^16 ∧ rc16_vals i = ↑k :=
off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min
  h_rc_max h_embed_rc h_n_lt h_rc_lt h_rc_le h_ring_char_gt hprob₃ i