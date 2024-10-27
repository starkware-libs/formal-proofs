/-
Range check constraints.
-/
import Verification.Semantics.AirEncoding.Memory

-- trace data
variable {F : Type _} [Field F] {n : ℕ} {a a' p : Fin (n + 1) → F} {z : F} {rc_min rc_max : ℕ} {T : ℕ}
  {off_op0_tilde off_op1_tilde off_dst_tilde rc16_vals : Fin T → F}
  {embed_off_op0 embed_off_op1 embed_off_dst embed_rc16_vals : Fin T → Fin (n + 1)}

-- constraints
variable
  (h_continuity : ∀ i : Fin n, (a' i.succ - a' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)
  (h_initial : (z - a' 0) * p 0 = z - a 0)
  (h_cumulative : ∀ i : Fin n, (z - a' i.succ) * p i.succ = (z - a i.succ) * p (Fin.castSucc i))
  (h_final : p (Fin.last n) = 1)
  (h_rc_min : a' 0 = rc_min)
  (h_rc_max : a' (Fin.last n) = rc_max)
  (h_embed_op0 : ∀ i, a (embed_off_op0 i) = off_op0_tilde i)
  (h_embed_op1 : ∀ i, a (embed_off_op1 i) = off_op1_tilde i)
  (h_embed_dst : ∀ i, a (embed_off_dst i) = off_dst_tilde i)
  (h_embed_rc : ∀ i, a (embed_rc16_vals i) = rc16_vals i)
  (h_n_lt : n < ringChar F)
  (h_rc_lt : rc_max < 2 ^ 16)
  (h_rc_le : rc_min ≤ rc_max)
  (h_ring_char_gt : 2 ^ 16 < ringChar F)

section

include h_continuity h_rc_min

theorem rc_a'_eq (j : Fin (n + 1)) : a' j = ↑(rc_min + a'NatOffset a' j) := by
  rw [a'NatOffset_spec h_continuity j, h_rc_min, Nat.cast_add]

include h_rc_max h_rc_le h_rc_lt h_n_lt h_ring_char_gt

theorem rc_nat_offset_eq : rc_min + a'NatOffset a' (Fin.last n) = rc_max := by
  have h₀ : (↑rc_min : F) + ↑(a'NatOffset a' (Fin.last n)) = ↑rc_min + ↑(rc_max - rc_min) := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← rc_a'_eq h_continuity h_rc_min, h_rc_max,
      Nat.add_sub_of_le h_rc_le]
  have h₁ : a'NatOffset a' (Fin.last n) < ringChar F := lt_of_le_of_lt (a'NatOffset_le _) h_n_lt
  have h₂ : rc_max - rc_min < ringChar F :=
    lt_of_le_of_lt tsub_le_self (lt_trans h_rc_lt h_ring_char_gt)
  have := add_left_cancel h₀
  rw [Nat.cast_inj_of_lt_char h₁ h₂ this]
  apply Nat.add_sub_of_le h_rc_le

theorem rc_nat_offset_le (j : Fin (n + 1)) : rc_min + a'NatOffset a' j ≤ rc_max :=
  by
  rw [← rc_nat_offset_eq h_continuity h_rc_min h_rc_max h_n_lt h_rc_lt h_rc_le h_ring_char_gt]
  apply add_le_add_left
  apply monotone_a'NatOffset
  apply Fin.le_last

end

section

variable [Fintype F]

noncomputable def badSet3 (a a' : Fin (n + 1) → F) : Finset F :=
  PolynomialAux.exceptionalSet a a'

theorem card_badSet3_le : (badSet3 a a').card ≤ n + 1 := by
  trans; apply PolynomialAux.card_exceptionalSet_le; simp

theorem badSet3_spec {z : F} (h₁ : z ∉ badSet3 a a')
    (h₂ : (∏ i : Fin (n + 1), (z - a i)) = (∏ i, (z - a' i))) : ∀ i, ∃ j, a i = a' j :=
  exceptionalSet_spec _ _ h₁ h₂

theorem badSet3_spec' {z : F} (h₁ : z ∉ badSet3 a a')
    (h₂ : (∏ i : Fin (n + 1), (z - a i)) = (∏ i, (z - a' i))) : ∀ i, ∃ j, a' i = a j :=
  exceptionalSet_spec' _ _ h₁ h₂

end

section permutation

include h_initial h_cumulative

theorem rc_permutation_aux (j : Fin (n + 1)) :
  (∏ i in Fin.range j.succ, (z - a i)) = (∏ i in Fin.range j.succ, (z - a' i)) * p j := by
  induction' j using Fin.inductionOn with j ih
  · rw [← Fin.one_eq_succ_zero, Fin.prod_range_one, Fin.prod_range_one, h_initial]
  rw [Fin.prod_range_succ, Fin.prod_range_succ, ← Fin.succ_castSucc, ih, ← mul_assoc]
  conv =>
    rhs
    rw [mul_right_comm, h_cumulative, mul_right_comm]

include h_final

theorem rc_permutation_prod_eq : (∏ i, (z - a i)) = (∏ i, (z - a' i)) := by
  rw [← Fin.range_last, ← Fin.succ_last, rc_permutation_aux h_initial h_cumulative,
    h_final, mul_one]

end permutation

variable [Fintype F] (hprob₃ : z ∉ badSet3 a a')

include h_initial h_cumulative h_final hprob₃

theorem rc_permutation : ∀ i, ∃ j, a i = a' j := fun i =>
  badSet3_spec hprob₃ (rc_permutation_prod_eq h_initial h_cumulative h_final) i

include h_continuity h_initial h_cumulative h_final h_rc_min h_rc_max h_rc_le h_rc_lt h_n_lt h_ring_char_gt

include h_embed_op0 in
theorem off_op0_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ off_op0_tilde i = ↑k := by
  rcases rc_permutation h_initial h_cumulative h_final hprob₃ (embed_off_op0 i) with ⟨j, hj⟩
  have : a' j = a' 0 + a'NatOffset a' j := a'NatOffset_spec h_continuity _
  rw [this, h_embed_op0, h_rc_min, ← Nat.cast_add] at hj
  use rc_min + a'NatOffset a' j
  constructor
  · apply lt_of_le_of_lt _ h_rc_lt
    apply rc_nat_offset_le h_continuity h_rc_min h_rc_max h_n_lt h_rc_lt h_rc_le h_ring_char_gt
  exact hj

include h_embed_op1 in
theorem off_op1_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ off_op1_tilde i = ↑k :=
  off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min h_rc_max h_embed_op1 h_n_lt
    h_rc_lt h_rc_le h_ring_char_gt hprob₃ i

include h_embed_dst in
theorem off_dst_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ off_dst_tilde i = ↑k :=
  off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min h_rc_max h_embed_dst h_n_lt
    h_rc_lt h_rc_le h_ring_char_gt hprob₃ i

include h_embed_rc in
theorem rc16_vals_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ rc16_vals i = ↑k :=
  off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min h_rc_max h_embed_rc h_n_lt
    h_rc_lt h_rc_le h_ring_char_gt hprob₃ i
