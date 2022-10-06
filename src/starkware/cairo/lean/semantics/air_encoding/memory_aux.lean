/-
Interpretation of memory constraints.
-/
import starkware.cairo.lean.semantics.util

noncomputable theory

open_locale classical big_operators

/-
General facts about polyomials
-/

namespace polynomial_aux

variables {F : Type*} [field F] [fintype F]
variables {n : Type*} [fintype n] (a b : n → F)

open finset polynomial

def mprod := ((univ.val.map a).map (λ r, X - C r)).prod

lemma nat_degree_mprod : (mprod a).nat_degree = fintype.card n :=
by { rw [mprod, nat_degree_multiset_prod_X_sub_C (univ.val.map a), multiset.card_map], refl }

lemma eq_of_mprod_eq (h : mprod a = mprod b) : univ.val.map a = univ.val.map b :=
begin
  have : (mprod a).roots = (mprod b).roots := congr_arg _ h,
  rwa [mprod, mprod, multiset_prod_X_sub_C_roots, multiset_prod_X_sub_C_roots] at this
end

lemma prod_eq_mprod (z : F) : ∏ i : n, (z - a i) = (mprod a).eval z :=
by { simp [mprod], refl }

theorem card_roots_le_or_all_eq [fintype F] :
  card (univ.filter (λ z : F, ∏ i, (z - a i) = ∏ i, (z - b i))) ≤ fintype.card n ∨
    ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i) :=
begin
  have h₀ : ∀ z, (∏ i, (z - a i)) - (∏ i, (z - b i)) = (mprod a - mprod b).eval z,
  { intro z, simp [mprod], refl },
  by_cases h : mprod a - mprod b = 0,
  { right, intro z, rw [←sub_eq_zero, h₀, h, eval_zero] },
  have : univ.filter (λ z : F, ∏ i, (z - a i) = ∏ i, (z - b i)) =
          (mprod a - mprod b).roots.to_finset,
  { ext z; simp [mem_roots h], rw [←sub_eq_zero, h₀, eval_sub] },
  left, rw this,
  apply (multiset.to_finset_card_le _).trans,
  apply (card_roots' _).trans,
  apply (nat_degree_add (mprod a) _).trans,
  rw [nat_degree_neg, nat_degree_mprod, nat_degree_mprod, max_self]
end

def exceptional_set : finset F :=
if ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i) then ∅ else
  univ.filter (λ z : F, ∏ i : n, (z - a i) = ∏ i, (z - b i))

@[simp] theorem exception_set_eq_pos (h : ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i)) :
  exceptional_set a b = ∅ :=
by rw [exceptional_set, if_pos h]

@[simp] theorem exception_set_eq_neg (h : ¬ ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i)) :
  exceptional_set a b = univ.filter (λ z : F, ∏ i : n, (z - a i) = ∏ i, (z - b i)) :=
by rw [exceptional_set, if_neg h]

theorem card_exceptional_set_le : card (exceptional_set a b) ≤ fintype.card n :=
begin
  by_cases h : (∀ z, ∏ i, (z - a i) = ∏ i, (z - b i)); simp [h],
  exact (card_roots_le_or_all_eq a b).resolve_right h
end

theorem all_eq_of_not_mem_exceptional_set {z : F}
    (h₁ : z ∉ exceptional_set a b)
    (h₂ : ∏ i : n, (z - a i) = ∏ i, (z - b i)) :
  ∀ z, ∏ i, (z - a i) = ∏ i, (z - b i) :=
begin
  by_contradiction h,
  simp [exceptional_set, if_neg h] at h₁,
  contradiction
end

end polynomial_aux

section

variables {F : Type*} [field F] {n : ℕ} (a b : fin n → F)

theorem prod_sub_eq_zero_iff (z : F) :
  ∏ i : fin n, (z - a i) = 0 ↔ ∃ j : fin n, z = a j :=
begin
  induction n with n ih,
  { simp },
  rw [fin.prod_univ_cast_succ, mul_eq_zero, ih, fin.exists_fin_cast_succ],
  simp only [sub_eq_zero]
end

variable [fintype F]

theorem exceptional_set_spec {z : F}
    (h₁ : z ∉ polynomial_aux.exceptional_set a b)
    (h₂ : ∏ i : fin n, (z - a i) = ∏ i, (z - b i)) :
  ∀ i, ∃ j, a i = b j :=
begin
  intro i,
  have : ∏ i' : fin n, (a i - a i') = 0,
  { rw prod_sub_eq_zero_iff, use i },
  rw polynomial_aux.all_eq_of_not_mem_exceptional_set a b h₁ h₂ at this,
  rwa ←prod_sub_eq_zero_iff
end

theorem exceptional_set_spec' {z : F}
    (h₁ : z ∉ polynomial_aux.exceptional_set a b)
    (h₂ : ∏ i : fin n, (z - a i) = ∏ i, (z - b i)) :
  ∀ i, ∃ j, b i = a j :=
begin
  intro i,
  have : ∏ i' : fin n, (b i - b i') = 0,
  { rw prod_sub_eq_zero_iff, use i },
  rw ←polynomial_aux.all_eq_of_not_mem_exceptional_set a b h₁ h₂ at this,
  rwa ←prod_sub_eq_zero_iff
end

end

/-
The constraints.

Note: where the whitepaper assumes `n > 0`, we use `n + 1` instead.
-/

section constraints

variables {F : Type*} [field F]

variables {n : ℕ} {a v a' v' p : fin (n + 1) → F}

variables {alpha z : F}

variable h_continuity :
  ∀ i : fin n, (a' i.succ - a' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0

variable h_single_valued :
  ∀ i : fin n, (v' i.succ - v' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0

variable h_initial : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0)

variable h_cumulative : ∀ i : fin n, (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
                                       (z - (a i.succ + alpha * v i.succ)) * p i.cast_succ

variable h_final : p (fin.last n) = 1

/-
See also `hprob₁`, `hprob₂`, and `char_lt` below.
-/

def a'_step (a' : fin (n + 1) → F) (i : fin n) : ℕ :=
if a' i.succ = a' i.cast_succ then 0 else 1

lemma a'_step_of_eq (i : fin n) (h : a' i.succ = a' i.cast_succ) :
  a'_step a' i = 0 :=
by rw [a'_step, if_pos h]

lemma a'_step_of_eq_add_one (i : fin n) (h : a' i.succ = a' i.cast_succ + 1) :
  a'_step a' i = 1 :=
by rw [a'_step, if_neg]; simp [h]

def a'_nat_offset (a' : fin (n + 1) → F) (i : fin (n + 1)) : ℕ :=
∑ j in fin.range i, (a'_step a') j

@[simp] lemma a'_nat_offset_zero : a'_nat_offset a' 0 = 0 := fin.sum_range_zero _

@[simp] lemma a'_nat_offset_succ (i : fin n) :
  a'_nat_offset a' i.succ = a'_nat_offset a' i.cast_succ + a'_step a' i :=
by rw [a'_nat_offset, fin.sum_range_succ _ _, add_comm]; refl

lemma monotone_a'_nat_offset : monotone (a'_nat_offset a') :=
by { intros i j ilej, apply finset.sum_mono_set, apply fin.range_subset.mpr ilej }

lemma a'_nat_offset_le (i : fin (n + 1)) : a'_nat_offset a' i ≤ ↑i :=
begin
  apply fin.induction_on i; simp,
  intros i' ih,
  apply add_le_add ih _,
  by_cases h : a' i'.succ = a' i'.cast_succ; simp [a'_step, h]
end

lemma a'_nat_offset_le' (i : fin (n + 1)) : a'_nat_offset a' i ≤ n :=
le_trans (monotone_a'_nat_offset (fin.le_last i)) (a'_nat_offset_le _)

section h_continuity
include h_continuity

lemma a'_succ_eq (i : fin n) : a' i.succ = a' i.cast_succ ∨ a' i.succ = a' i.cast_succ + 1 :=
begin
  cases (eq_zero_or_eq_zero_of_mul_eq_zero $ h_continuity i) with h h,
  { left, apply eq_of_sub_eq_zero h },
  right, apply eq_of_sub_eq_zero, rw ←h, abel
end

lemma a'_succ_eq' (i : fin n) : a' i.succ = a' i.cast_succ + a'_step a' i :=
begin
  cases (a'_succ_eq h_continuity i) with h h,
  { simp [a'_step_of_eq _ h, h] },
  simp [a'_step_of_eq_add_one _ h, h]
end

lemma a'_nat_offset_spec (i : fin (n + 1)) : a' i = a' 0 + a'_nat_offset a' i :=
begin
  apply fin.induction_on i; simp [a'_succ_eq' h_continuity],
  intros i' ih, rw [ih, add_assoc]
end

lemma nat_offset_eq (h_n_lt : n < ring_char F) {i j : fin (n + 1)} (h : a' i = a' j) :
  a'_nat_offset a' i = a'_nat_offset a' j :=
begin
  have : ↑i < ring_char F := lt_of_le_of_lt (nat.le_of_lt_succ i.property) h_n_lt,
  have : ↑j < ring_char F := lt_of_le_of_lt (nat.le_of_lt_succ j.property) h_n_lt,
  rw [a'_nat_offset_spec h_continuity i, a'_nat_offset_spec h_continuity j] at h,
  apply nat.cast_inj_of_lt_char _ _ (add_left_cancel h);
  { apply lt_of_le_of_lt (a'_nat_offset_le _), assumption }
end

lemma a'_continuous_aux (i : fin (n + 1)) :
  ∀ k ≤ a'_nat_offset a' i, ∃ j ≤ i, a'_nat_offset a' j = k :=
begin
  apply fin.induction_on i; simp,
  { use [0, le_refl _], simp },
  intros i' ih k,
  cases (a'_succ_eq h_continuity i') with h h,
  { simp [a'_step_of_eq _ h, h],
    intro hk,
    rcases ih k hk with ⟨j, hj, hj'⟩,
    exact ⟨j, le_trans hj (le_of_lt (fin.cast_succ_lt_succ _)), hj'⟩ },
   simp [a'_step_of_eq_add_one _ h, h],
   intro hk,
   cases (nat.of_le_succ hk) with hk' hk',
   { rcases ih k hk' with ⟨j, hj, hj'⟩,
     exact⟨j, le_trans hj (le_of_lt (fin.cast_succ_lt_succ _)), hj'⟩ },
   refine ⟨i'.succ, le_refl _, _⟩,
  rw [hk', a'_nat_offset_succ, a'_step_of_eq_add_one _ h]
end

lemma a'_continuous (k : ℕ) (hk : k ≤ a'_nat_offset a' (fin.last n)) :
  ∃ j, a'_nat_offset a' j = k :=
begin
  rcases a'_continuous_aux h_continuity _ _ hk with ⟨j, _, hj⟩,
  exact ⟨j, hj⟩
end

section single_valued
include h_single_valued

lemma a'_single_valued_aux {i : fin n} (h : a' i.succ = a' i.cast_succ) :
  v' i.succ = v' i.cast_succ :=
begin
  have := h_single_valued i,
  simp [h] at this,
  symmetry,
  exact eq_of_sub_eq_zero this
end

lemma a'_single_valued_aux' (h_n_lt : n < ring_char F) (i : fin (n + 1)) :
  ∀ j < i, a' i = a' j → v' i = v' j :=
begin
  apply i.induction_on,
  { intros j hj, exfalso, apply fin.not_lt_zero _ hj },
  intros i' ih j hj a'eq,
  have hj' : j ≤ i'.cast_succ := fin.le_of_lt_succ hj,
  have a'eq2 : a' i'.succ = a' i'.cast_succ,
  { rw [a'eq, a'_nat_offset_spec h_continuity, a'_nat_offset_spec h_continuity i'.cast_succ],
    congr' 2, apply le_antisymm (monotone_a'_nat_offset $ fin.le_of_lt_succ hj),
    rw ←nat_offset_eq h_continuity h_n_lt a'eq,
    apply monotone_a'_nat_offset (le_of_lt $ fin.cast_succ_lt_succ _) },
  rw [a'_single_valued_aux h_continuity h_single_valued a'eq2],
  cases (lt_or_eq_of_le hj') with h h,
  { exact ih j h (a'eq2.symm.trans a'eq) },
  rw h
end

lemma a'_single_valued (h_n_lt : n < ring_char F) {i j : fin (n + 1)} :
  a' i = a' j → v' i = v' j :=
begin
  have : i < j ∨ i = j ∨ j < i := trichotomous i j,
  rcases this with h | rfl | h,
  { intro h', symmetry,
    exact a'_single_valued_aux' h_continuity h_single_valued h_n_lt _ _ h h'.symm },
  { intro _, refl },
  exact a'_single_valued_aux' h_continuity h_single_valued h_n_lt _ _ h
end

end single_valued

end h_continuity

section

variable [fintype F]

def bad_set_1 (a v a' v' : fin (n + 1) → F) : finset F :=
finset.univ.filter (λ alpha, ∃ i j, v i ≠ v' j ∧ a i + alpha * v i = a' j + alpha * v' j)

@[simp] theorem mem_bad_set_1 {a v a' v' : fin (n + 1) → F} (alpha : F) :
  alpha ∈ bad_set_1 a v a' v' ↔ ∃ i j, v i ≠ v' j ∧ a i + alpha * v i = a' j + alpha * v' j :=
by { rw [bad_set_1, finset.mem_filter], simp }

theorem card_bad_set_1_le  : (bad_set_1 a v a' v').card ≤ (n + 1) * (n + 1) :=
let f := λ p : fin (n + 1) × fin (n + 1), (a p.1 - a' p.2) / (v' p.2 - v p.1) in
calc
    (bad_set_1 a v a' v').card ≤ (finset.image f finset.univ).card :
      begin
        apply finset.card_le_of_subset,
        intros alpha,
        simp,
        intros i j hv ha,
        use [i, j], dsimp [f],
        have : v' j - v i ≠ 0,
        { intro h, apply hv, symmetry, apply eq_of_sub_eq_zero h },
        rw [div_eq_iff this, mul_sub, sub_eq_iff_eq_add, sub_add_eq_add_sub, add_comm, ←ha,
             add_sub_cancel]
      end
    ... ≤ (finset.univ : finset (fin (n + 1) × fin (n + 1))).card : finset.card_image_le
    ... = fintype.card (fin (n + 1) × fin (n + 1))                : rfl
    ... = (n + 1) * (n + 1)                                       : by simp

theorem bad_set_1_spec (h : alpha ∉ bad_set_1 a v a' v') {i j : fin (n + 1)}
    (h' : a i + alpha * v i = a' j + alpha * v' j) :
  v i = v' j ∧ a i = a' j :=
begin
  simp at h,
  specialize h i j,
  have : v i = v' j := by_contradiction (λ h₀, h h₀ h'),
  split, { exact this },
  rw this at h',
  exact add_right_cancel h'
end

def bad_set_2 (a v a' v' : fin (n + 1) → F) (alpha : F) : finset F :=
polynomial_aux.exceptional_set (λ i, a i + alpha * v i) (λ i, a' i + alpha * v' i)

theorem card_bad_set_2_le : (bad_set_2 a v a' v' alpha).card ≤ n + 1 :=
by { transitivity, apply polynomial_aux.card_exceptional_set_le, simp }

theorem bad_set_2_spec {z : F}
    (h₁ : z ∉ bad_set_2 a v a' v' alpha)
    (h₂ : ∏ i : fin (n + 1), (z - (a i + alpha * v i)) = ∏ i, (z - (a' i + alpha * v' i))) :
  ∀ i, ∃ j, a i + alpha * v i = a' j + alpha * v' j :=
exceptional_set_spec _ _ h₁ h₂

theorem bad_set_2_spec' {z : F}
    (h₁ : z ∉ bad_set_2 a v a' v' alpha)
    (h₂ : ∏ i : fin (n + 1), (z - (a i + alpha * v i)) = ∏ i, (z - (a' i + alpha * v' i))) :
  ∀ i, ∃ j, a' i + alpha * v' i = a j + alpha * v j :=
exceptional_set_spec' _ _ h₁ h₂

end

section permutation

include h_initial h_cumulative

lemma permutation_aux (j : fin (n + 1)) :
  ∏ i in fin.range j.succ, (z - (a i + alpha * v i)) =
    (∏ i in fin.range j.succ, (z - (a' i + alpha * v' i))) * p j :=
begin
  apply fin.induction_on j,
  { rw [←fin.one_eq_succ_zero, fin.prod_range_one, fin.prod_range_one, h_initial] },
  intros j ih,
  rw [fin.prod_range_succ, fin.prod_range_succ, ←fin.succ_cast_succ, ih, ←mul_assoc],
  conv { to_rhs, rw [mul_right_comm, h_cumulative, mul_right_comm] }
end

include h_final

lemma permutation_prod_eq :
  ∏ i, (z - (a i + alpha * v i)) = ∏ i, (z - (a' i + alpha * v' i)) :=
by rw [←fin.range_last, ←fin.succ_last, permutation_aux h_initial h_cumulative,
    h_final, mul_one]

end permutation

/-
Put it all together!
-/

variable [fintype F]
variable hprob₁ : alpha ∉ bad_set_1 a v a' v'
variable hprob₂ : z ∉ bad_set_2 a v a' v' alpha

include hprob₁ hprob₂

lemma permutation (h : ∏ (i : fin (n + 1)), (z - (a i + alpha * v i)) =
                         ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i))) :
  ∀ i, ∃ j, v i = v' j ∧ a i = a' j :=
begin
  intro i,
  have : ∃ j, a i + alpha * v i = a' j + alpha * v' j := bad_set_2_spec hprob₂ h i,
  cases this with j hj,
  use j,
  show v i = v' j ∧ a i = a' j,
    from bad_set_1_spec hprob₁ hj
end

lemma permutation'  (h : ∏ (i : fin (n + 1)), (z - (a i + alpha * v i)) =
                         ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i))) :
  ∀ i, ∃ j, v' i = v j ∧ a' i = a j :=
begin
  intro i,
  have := bad_set_2_spec' hprob₂ h i,
  cases this with j hj,
  have := bad_set_1_spec hprob₁ hj.symm,
  use j, simp [this]
end

include h_continuity h_initial h_cumulative h_final

lemma a_continuous : ∃ base : F, ∃ m : ℕ,
    (∀ i, ∃ k ≤ m, a i = base + k) ∧ (∀ k ≤ m, ∃ i, a i = base + k) :=
begin
  have h : ∏ (i : fin (n + 1)), (z - (a i + alpha * v i)) =
             ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i)) :=
    permutation_prod_eq h_initial h_cumulative h_final,
  have perm := permutation hprob₁ hprob₂ h,
  use a' 0,
  use a'_nat_offset a' (fin.last n),
  split,
  { intro i,
    rcases perm i with ⟨j, veq, aeq⟩,
    use a'_nat_offset a' j,
    split,
    { apply monotone_a'_nat_offset, apply fin.le_last },
    rw aeq,
    exact a'_nat_offset_spec h_continuity j },
  have perm' := permutation' hprob₁ hprob₂ h,
  intros k kle,
  rcases a'_continuous h_continuity k kle with ⟨j, hj⟩,
  rcases perm' j with ⟨i, v'eq, a'eq⟩,
  use i,
  rw [←a'eq, ←hj],
  exact a'_nat_offset_spec h_continuity j
end

include h_single_valued

lemma a_single_valued (h_char_lt : n < ring_char F) : ∀ i i', a i = a i' → v i = v i' :=
begin
  intros i i' aieq,
  have h : ∏ (i : fin (n + 1)), (z - (a i + alpha * v i)) =
             ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i)) :=
    permutation_prod_eq h_initial h_cumulative h_final,
  have perm := permutation hprob₁ hprob₂ h,
  rcases perm i with ⟨j, veq, aeq⟩,
  rcases perm i' with ⟨j', veq', aeq'⟩,
  rw [veq, veq'],
  apply a'_single_valued h_continuity h_single_valued h_char_lt,
  rw [←aeq, ←aeq', aieq]
end

end constraints

-- #lint
