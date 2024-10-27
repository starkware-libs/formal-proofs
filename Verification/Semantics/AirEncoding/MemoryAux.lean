/-
Interpretation of memory constraints.
-/
import Verification.Semantics.Util

noncomputable section

open scoped Classical BigOperators

/- General facts about polyomials -/
namespace PolynomialAux

variable {F : Type _} [Field F] {n : Type _} [Fintype n] (a b : n → F)

open Finset Polynomial

def mprod := ((univ.val.map a).map fun r => X - C r).prod

theorem natDegree_mprod : (mprod a).natDegree = Fintype.card n := by
  rw [mprod, natDegree_multiset_prod_X_sub_C (univ.val.map a), Multiset.card_map]; rfl

theorem eq_of_mprod_eq (h : mprod a = mprod b) : univ.val.map a = univ.val.map b := by
  have : (mprod a).roots = (mprod b).roots := congr_arg _ h
  rwa [mprod, mprod, multiset_prod_x_sub_c_roots, multiset_prod_x_sub_c_roots] at this

theorem prod_eq_mprod (z : F) : ∏ i : n, (z - a i) = (mprod a).eval z := by
  rw [mprod, Polynomial.eval_multiset_prod]; simp

variable [Fintype F]

theorem card_roots_le_or_all_eq:
  card (univ.filter fun z : F => ∏ i, (z - a i) = ∏ i, (z - b i)) ≤ Fintype.card n ∨
    ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i) := by
  have h₀ : ∀ z, (∏ i, (z - a i)) - (∏ i, (z - b i)) = (mprod a - mprod b).eval z := by
    intro z; rw [mprod, Polynomial.eval_sub, Polynomial.eval_multiset_prod]; simp [prod_eq_mprod]
  by_cases h : mprod a - mprod b = 0
  · right; intro z; rw [← sub_eq_zero, h₀, h, eval_zero]
  have : (univ.filter fun z : F => (∏ i, (z - a i)) = ∏ i, (z - b i)) = (mprod a - mprod b).roots.toFinset := by
    ext z
    simp [mem_roots h, ← sub_eq_zero, h₀, eval_sub]
  left
  rw [this]
  apply (Multiset.toFinset_card_le _).trans
  apply (card_roots' _).trans
  apply (natDegree_add (mprod a) _).trans
  rw [natDegree_neg, natDegree_mprod, natDegree_mprod, max_self]

def exceptionalSet : Finset F :=
  if ∀ z, (∏ i, (z - a i)) = ∏ i, (z - b i) then ∅
  else univ.filter fun z : F => (∏ i : n, (z - a i)) = ∏ i, (z - b i)

@[simp]
theorem exception_set_eq_pos (h : ∀ z, (∏ i, (z - a i)) = ∏ i, (z - b i)) : exceptionalSet a b = ∅ := by
  rw [exceptionalSet, if_pos h]

@[simp]
theorem exception_set_eq_neg (h : ¬∀ z, (∏ i, (z - a i)) = ∏ i, (z - b i)) :
    exceptionalSet a b = univ.filter fun z : F => (∏ i : n, (z - a i)) = ∏ i, (z - b i) := by
  rw [exceptionalSet, if_neg h]

theorem card_exceptionalSet_le : card (exceptionalSet a b) ≤ Fintype.card n := by
  by_cases h : ∀ z, (∏ i, (z - a i)) = ∏ i, (z - b i) <;> simp [h]
  exact (card_roots_le_or_all_eq a b).resolve_right h

theorem all_eq_of_not_mem_exceptionalSet {z : F} (h₁ : z ∉ exceptionalSet a b)
    (h₂ : (∏ i : n, (z - a i)) = ∏ i, (z - b i)) : ∀ z, (∏ i, (z - a i)) = ∏ i, (z - b i) := by
  by_contra h
  simp [exceptionalSet, if_neg h] at h₁
  contradiction

end PolynomialAux

section

variable {F : Type _} [Field F] {n : ℕ} (a b : Fin n → F)

theorem prod_sub_eq_zero_iff (z : F) : (∏ i : Fin n, (z - a i)) = 0 ↔ ∃ j : Fin n, z = a j := by
  induction' n with n ih
  · simp
  rw [Fin.prod_univ_castSucc, mul_eq_zero, ih, Fin.exists_fin_castSucc]
  simp only [sub_eq_zero]

variable [Fintype F]

theorem exceptionalSet_spec {z : F} (h₁ : z ∉ PolynomialAux.exceptionalSet a b)
    (h₂ : (∏ i : Fin n, (z - a i)) = ∏ i, (z - b i)) : ∀ i, ∃ j, a i = b j := by
  intro i
  have : (∏ i' : Fin n, (a i - a i')) = 0 := by
    rw [prod_sub_eq_zero_iff]
    exact ⟨i, rfl⟩
  rw [PolynomialAux.all_eq_of_not_mem_exceptionalSet a b h₁ h₂] at this
  rwa [← prod_sub_eq_zero_iff]

theorem exceptionalSet_spec' {z : F} (h₁ : z ∉ PolynomialAux.exceptionalSet a b)
    (h₂ : (∏ i : Fin n, (z - a i)) = ∏ i, (z - b i)) : ∀ i, ∃ j, b i = a j := by
  intro i
  have : (∏ i' : Fin n, (b i - b i')) = 0 := by
    rw [prod_sub_eq_zero_iff]
    use i
  rw [← PolynomialAux.all_eq_of_not_mem_exceptionalSet a b h₁ h₂] at this
  rwa [← prod_sub_eq_zero_iff]

end

/-
The constraints.

Note: where the whitepaper assumes `n > 0`, we use `n + 1` instead.
-/
section Constraints

variable {F : Type _} [Field F] {n : ℕ} {a v a' v' p : Fin (n + 1) → F} {alpha z : F}

variable
  (h_continuity : ∀ i : Fin n, (a' i.succ - a' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)
  (h_single_valued :
    ∀ i : Fin n, (v' i.succ - v' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)
  (h_initial : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0))
  (h_cumulative :
    ∀ i : Fin n, (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
        (z - (a i.succ + alpha * v i.succ)) * p (Fin.castSucc i))
  (h_final : p (Fin.last n) = 1)

/- See also `hprob₁`, `hprob₂`, and `char_lt` below.  -/
def a'Step (a' : Fin (n + 1) → F) (i : Fin n) : ℕ :=
  if a' i.succ = a' (Fin.castSucc i) then 0 else 1

omit [Field F] in
theorem a'Step_of_eq (i : Fin n) (h : a' i.succ = a' (Fin.castSucc i)) : a'Step a' i = 0 := by
  rw [a'Step, if_pos h]

theorem a'Step_of_eq_add_one (i : Fin n) (h : a' i.succ = a' (Fin.castSucc i) + 1) : a'Step a' i = 1 := by
  rw [a'Step, if_neg]
  simp [h]

def a'NatOffset (a' : Fin (n + 1) → F) (i : Fin (n + 1)) : ℕ := ∑ j in Fin.range i, (a'Step a') j

section
omit [Field F]

@[simp] theorem a'NatOffset_zero : a'NatOffset a' 0 = 0 := Fin.sum_range_zero _

@[simp] theorem a'NatOffset_succ (i : Fin n) :
    a'NatOffset a' i.succ = a'NatOffset a' (Fin.castSucc i) + a'Step a' i := by
  rw [a'NatOffset, Fin.sum_range_succ _ _, add_comm]
  rfl

theorem monotone_a'NatOffset : Monotone (a'NatOffset a') := by
  intro i j ilej
  apply Finset.sum_mono_set
  apply Fin.range_subset.mpr ilej

theorem a'NatOffset_le (i : Fin (n + 1)) : a'NatOffset a' i ≤ ↑i := by
  induction' i using Fin.inductionOn with i' ih <;> simp
  apply add_le_add ih _
  by_cases h : a' i'.succ = a' (Fin.castSucc i') <;> simp [a'Step, h]

theorem a'NatOffset_le' (i : Fin (n + 1)) : a'NatOffset a' i ≤ n :=
  le_trans (monotone_a'NatOffset (Fin.le_last i)) (a'NatOffset_le _)

end

section HContinuity
include h_continuity

theorem a'_succ_eq (i : Fin n) : a' i.succ = a' (Fin.castSucc i) ∨ a' i.succ = a' (Fin.castSucc i) + 1 := by
  cases' eq_zero_or_eq_zero_of_mul_eq_zero <| h_continuity i with h h
  · left; apply eq_of_sub_eq_zero h
  right; apply eq_of_sub_eq_zero; rw [← h]; abel

theorem a'_succ_eq' (i : Fin n) : a' i.succ = a' (Fin.castSucc i) + a'Step a' i := by
  cases' a'_succ_eq h_continuity i with h h
  · simp [a'Step_of_eq _ h, h]
  simp [a'Step_of_eq_add_one _ h, h]

theorem a'NatOffset_spec (i : Fin (n + 1)) : a' i = a' 0 + a'NatOffset a' i := by
  induction' i using Fin.inductionOn with i' ih <;> simp [a'_succ_eq' h_continuity]
  rw [ih, add_assoc]

theorem nat_offset_eq (h_n_lt : n < ringChar F) {i j : Fin (n + 1)} (h : a' i = a' j) :
    a'NatOffset a' i = a'NatOffset a' j := by
  have : ↑i < ringChar F := lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) h_n_lt
  have : ↑j < ringChar F := lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) h_n_lt
  rw [a'NatOffset_spec h_continuity i, a'NatOffset_spec h_continuity j] at h
  apply Nat.cast_inj_of_lt_char _ _ (add_left_cancel h) <;>
    · apply lt_of_le_of_lt (a'NatOffset_le _); assumption

theorem a'_continuous_aux (i : Fin (n + 1)) :
    ∀ k ≤ a'NatOffset a' i, ∃ j ≤ i, a'NatOffset a' j = k := by
  induction' i using Fin.inductionOn with i' ih <;> simp
  intro k
  cases' a'_succ_eq h_continuity i' with h h
  · simp [a'Step_of_eq _ h, h]
    intro hk
    rcases ih k hk with ⟨j, hj, hj'⟩
    exact ⟨j, le_trans hj (le_of_lt (Fin.castSucc_lt_succ _)), hj'⟩
  simp [a'Step_of_eq_add_one _ h, h]
  intro hk
  cases' Nat.of_le_succ hk with hk' hk'
  · rcases ih k hk' with ⟨j, hj, hj'⟩
    exact ⟨j, le_trans hj (le_of_lt (Fin.castSucc_lt_succ _)), hj'⟩
  refine' ⟨i'.succ, le_refl _, _⟩
  rw [hk', a'NatOffset_succ, a'Step_of_eq_add_one _ h]

theorem a'_continuous (k : ℕ) (hk : k ≤ a'NatOffset a' (Fin.last n)) : ∃ j, a'NatOffset a' j = k := by
  rcases a'_continuous_aux h_continuity _ _ hk with ⟨j, _, hj⟩
  exact ⟨j, hj⟩

section SingleValued

variable
  (h_single_valued :
    ∀ i : Fin n, (v' i.succ - v' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)

include h_single_valued

omit h_continuity in
theorem a'_single_valued_aux {i : Fin n} (h : a' i.succ = a' (Fin.castSucc i)) :
    v' i.succ = v' (Fin.castSucc i) := by
  have := h_single_valued i
  simp [h] at this
  symm
  exact eq_of_sub_eq_zero this

theorem a'_single_valued_aux' (h_n_lt : n < ringChar F) (i : Fin (n + 1)) :
    ∀ j < i, a' i = a' j → v' i = v' j := by
  induction' i using Fin.inductionOn with i' ih
  · intro j hj; exfalso; apply Fin.not_lt_zero _ hj
  intro j hj a'eq
  have hj' : j ≤ (Fin.castSucc i') := Fin.le_of_lt_succ hj
  have a'eq2 : a' i'.succ = a' (Fin.castSucc i') := by
    rw [a'eq, a'NatOffset_spec h_continuity, a'NatOffset_spec h_continuity (Fin.castSucc i')]
    congr 2; apply le_antisymm (monotone_a'NatOffset <| Fin.le_of_lt_succ hj)
    rw [← nat_offset_eq h_continuity h_n_lt a'eq]
    apply monotone_a'NatOffset (le_of_lt <| Fin.castSucc_lt_succ _)
  rw [a'_single_valued_aux h_single_valued a'eq2]
  cases' lt_or_eq_of_le hj' with h h
  · exact ih j h (a'eq2.symm.trans a'eq)
  rw [h]

theorem a'_single_valued (h_n_lt : n < ringChar F) {i j : Fin (n + 1)} :
    a' i = a' j → v' i = v' j :=
  by
  have : i < j ∨ i = j ∨ j < i := trichotomous i j
  rcases this with (h | rfl | h)
  · intro h'; symm
    exact a'_single_valued_aux' h_continuity h_single_valued h_n_lt _ _ h h'.symm
  · intro; rfl
  exact a'_single_valued_aux' h_continuity h_single_valued h_n_lt _ _ h

end SingleValued

end HContinuity

section

variable [Fintype F]

def badSet1 (a v a' v' : Fin (n + 1) → F) : Finset F :=
  Finset.univ.filter fun alpha => ∃ i j, v i ≠ v' j ∧ a i + alpha * v i = a' j + alpha * v' j

@[simp]
theorem mem_badSet1 {a v a' v' : Fin (n + 1) → F} (alpha : F) :
    alpha ∈ badSet1 a v a' v' ↔ ∃ i j, v i ≠ v' j ∧ a i + alpha * v i = a' j + alpha * v' j := by
  rw [badSet1, Finset.mem_filter]; simp

theorem card_badSet1_le : (badSet1 a v a' v').card ≤ (n + 1) * (n + 1) :=
  let f := fun p : Fin (n + 1) × Fin (n + 1) => (a p.1 - a' p.2) / (v' p.2 - v p.1)
  calc
    (badSet1 a v a' v').card ≤ (Finset.image f Finset.univ).card := by
      apply Finset.card_le_card
      intro alpha
      simp
      intro i j hv ha
      use i, j
      have : v' j - v i ≠ 0 := by intro h; apply hv; symm; apply eq_of_sub_eq_zero h
      rw [div_eq_iff this, mul_sub, sub_eq_iff_eq_add, sub_add_eq_add_sub, add_comm (alpha * _),
        ← ha, add_sub_cancel_right]
    _ ≤ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).card := Finset.card_image_le
    _ = Fintype.card (Fin (n + 1) × Fin (n + 1)) := rfl
    _ = (n + 1) * (n + 1) := by simp

theorem badSet1_spec (h : alpha ∉ badSet1 a v a' v') {i j : Fin (n + 1)}
    (h' : a i + alpha * v i = a' j + alpha * v' j) : v i = v' j ∧ a i = a' j := by
  simp at h
  specialize h i j
  have : v i = v' j := by_contradiction fun h₀ => h h₀ h'
  constructor; · exact this
  rw [this] at h'
  exact add_right_cancel h'

def badSet2 (a v a' v' : Fin (n + 1) → F) (alpha : F) : Finset F :=
  PolynomialAux.exceptionalSet (fun i => a i + alpha * v i) fun i => a' i + alpha * v' i

theorem card_badSet2_le : (badSet2 a v a' v' alpha).card ≤ n + 1 := by
  trans
  apply PolynomialAux.card_exceptionalSet_le
  simp

theorem badSet2_spec {z : F} (h₁ : z ∉ badSet2 a v a' v' alpha)
    (h₂ : (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i, (z - (a' i + alpha * v' i)))) :
    ∀ i, ∃ j, a i + alpha * v i = a' j + alpha * v' j :=
  exceptionalSet_spec _ _ h₁ h₂

theorem badSet2_spec' {z : F} (h₁ : z ∉ badSet2 a v a' v' alpha)
    (h₂ : (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i, (z - (a' i + alpha * v' i)))) :
    ∀ i, ∃ j, a' i + alpha * v' i = a j + alpha * v j :=
  exceptionalSet_spec' _ _ h₁ h₂

end

section permutation
include h_initial h_cumulative

theorem permutation_aux (j : Fin (n + 1)) :
    (∏ i in Fin.range j.succ, (z - (a i + alpha * v i))) =
      (∏ i in Fin.range j.succ, (z - (a' i + alpha * v' i))) * p j := by
  induction' j using Fin.inductionOn with j ih
  · rw [← Fin.one_eq_succ_zero, Fin.prod_range_one, Fin.prod_range_one, h_initial]
  rw [Fin.prod_range_succ, Fin.prod_range_succ, ← Fin.succ_castSucc, ih, ← mul_assoc]
  conv =>
    rhs
    rw [mul_right_comm, h_cumulative, mul_right_comm]

variable (h_final : p (Fin.last n) = 1)
include h_final

theorem permutation_prod_eq : (∏ i, (z - (a i + alpha * v i))) = ∏ i, (z - (a' i + alpha * v' i)) := by
  rw [← Fin.range_last, ← Fin.succ_last, permutation_aux h_initial h_cumulative, h_final, mul_one]

end permutation

/- Put it all together!  -/
variable [Fintype F] (hprob₁ : alpha ∉ badSet1 a v a' v') (hprob₂ : z ∉ badSet2 a v a' v' alpha)

include hprob₁ hprob₂

theorem permutation
    (h : (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i)))) :
    ∀ i, ∃ j, v i = v' j ∧ a i = a' j := by
  intro i
  have : ∃ j, a i + alpha * v i = a' j + alpha * v' j := badSet2_spec hprob₂ h i
  cases' this with j hj
  use j
  show v i = v' j ∧ a i = a' j
  exact badSet1_spec hprob₁ hj

theorem permutation'
    (h : (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i)))) :
    ∀ i, ∃ j, v' i = v j ∧ a' i = a j := by
  intro i
  have := badSet2_spec' hprob₂ h i
  cases' this with j hj
  have := badSet1_spec hprob₁ hj.symm
  use j; simp [this]

include h_initial h_cumulative h_final h_continuity

theorem a_continuous : ∃ base : F, ∃ m : ℕ,
  (∀ i, ∃ k ≤ m, a i = base + k) ∧ ∀ k ≤ m, ∃ i, a i = base + k := by
  have h :
    (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i))) :=
    permutation_prod_eq h_initial h_cumulative h_final
  have perm := permutation hprob₁ hprob₂ h
  use a' 0
  use a'NatOffset a' (Fin.last n)
  constructor
  · intro i
    rcases perm i with ⟨j, _, aeq⟩
    use a'NatOffset a' j
    constructor
    · apply monotone_a'NatOffset; apply Fin.le_last
    rw [aeq]
    exact a'NatOffset_spec h_continuity j
  have perm' := permutation' hprob₁ hprob₂ h
  intro k kle
  rcases a'_continuous h_continuity k kle with ⟨j, hj⟩
  rcases perm' j with ⟨i, _, a'eq⟩
  use i
  rw [← a'eq, ← hj]
  exact a'NatOffset_spec h_continuity j

include h_single_valued

theorem a_single_valued (h_char_lt : n < ringChar F) : ∀ i i', a i = a i' → v i = v i' := by
  intro i i' aieq
  have h :
    (∏ i : Fin (n + 1), (z - (a i + alpha * v i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i))) :=
    permutation_prod_eq h_initial h_cumulative h_final
  have perm := permutation hprob₁ hprob₂ h
  rcases perm i with ⟨j, veq, aeq⟩
  rcases perm i' with ⟨j', veq', aeq'⟩
  rw [veq, veq']
  apply a'_single_valued h_continuity h_single_valued h_char_lt
  rw [← aeq, ← aeq', aieq]

end Constraints
