import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

variable {F : Type _} [Field F] [Fintype F] [DecidableEq F]
variable {char_F : ℕ} [h_CharP_F : CharP F char_F]

-- TODO (Yoav) : fix this later
set_option linter.unusedSectionVars false

noncomputable section
open scoped Classical BigOperators

open Polynomial

def prodF := (Finset.univ.val.map fun (r : F) => X - C r).prod
def prodF_exc (z : F) := ((Finset.univ.val.erase z).map fun r => X - C r).prod
-- This was the original definition, but it now seems that it is less convenient to use than the definition
-- using erase. We leave it here, for now, with a proof of equivalence.
def prodF_exc' (z : F) := ((Finset.univ.val.filter fun r => r ≠ z).map fun r => X - C r).prod

lemma prodF_exc_def {z : F} : prodF_exc z = prodF_exc' z := by
  unfold prodF_exc prodF_exc' ; rw [Multiset.Nodup.erase_eq_filter _] ; apply Finset.nodup

omit [Fintype F] in
lemma X_sub_C_eval {z : F} : (fun (r : F) => X - C r) z = X - C z := rfl

lemma prodF_exc_map_erase (z : F) : prodF_exc z = ((Finset.univ.val.map fun r => X - C r).erase (X - C z)).prod := by
  unfold prodF_exc ; rw [Multiset.map_erase_of_mem] ; simp

-- This lemma is for division of polynomials, not of rational functions.
lemma prodF_ex_eq' {z : F} : prodF / (X - C z) = prodF_exc z := by
  have h_in : (X - C z) ∈ Finset.univ.val.map fun r => X - C r := by simp
  unfold prodF
  simp only [←Multiset.prod_erase h_in]
  rw [←(prodF_exc_map_erase z)]
  rw [←Polynomial.divByMonic_eq_div _ (Polynomial.monic_X_sub_C z)]
  rw [Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C z)]

lemma prodF_exc_eval_eq_zero {x z : F} (h_ne : x ≠ z) : (prodF_exc z).eval x = 0 := by
  have h_in : (X - C x) ∈ (Finset.univ.val.erase z).map fun r => X - C r := by
    simp ; rw [Multiset.mem_erase_of_ne h_ne] ; simp
  unfold prodF_exc
  simp [←Multiset.prod_erase h_in]

lemma prodF_exc_eval_ne_zero {z : F} : (prodF_exc z).eval z ≠ 0 := by
  unfold prodF_exc
  rw [Polynomial.eval_multiset_prod]
  apply Multiset.prod_ne_zero
  by_contra h
  rw [Multiset.mem_map] at h
  rcases h with ⟨p, h_p_in, h_eval⟩
  rw [Multiset.mem_map] at h_p_in
  rcases h_p_in with ⟨a, h_a_in, h_a⟩
  rw [←h_a, eval_sub, eval_X, eval_C, sub_eq_zero] at h_eval
  rw [h_eval] at h_a_in
  apply Multiset.Nodup.notMem_erase _ h_a_in
  apply Finset.nodup

lemma sum_prodF_eq_zero {x : F} {m₁ m₂ : F → F} :
    (∑ z ∈ Finset.erase Finset.univ x, C (m₁ z - m₂ z) * prodF_exc z).eval x = 0 := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul]
  apply Multiset.sum_eq_zero
  intro p h_p
  rw [Multiset.mem_map] at h_p
  rcases h_p with ⟨z, h_z_in, h_p_eq⟩
  by_cases h_x_z : x = z
  · exfalso ; rw [Finset.mem_val, h_x_z] at h_z_in ; apply Finset.notMem_erase z _ h_z_in
  rw [←h_p_eq, prodF_exc_eval_eq_zero ((ne_eq _ _).mpr h_x_z), mul_zero]

lemma prodF_ex_eq {z : F} :
    (algebraMap F[X] (RatFunc F)) prodF / (algebraMap _ _) (X - C z) = (algebraMap _ _) (prodF_exc z) := by
  have h_in : (X - C z) ∈ Finset.univ.val.map fun r => X - C r := by simp
  unfold prodF
  simp only [←Multiset.prod_erase h_in]
  rw [←(prodF_exc_map_erase z)]
  simp only [map_mul]
  rw [mul_div_cancel_left₀ _ _]
  apply RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero z)

-- Lemma 4
lemma unique_decomposition {m₁ m₂ : F → F} :
  ∑ z : F, RatFunc.mk (C <| m₁ z) (X - C z) = ∑ z : F, RatFunc.mk (C <| m₂ z) (X - C z) ↔
    ∀ z : F, m₁ z = m₂ z := by
  constructor
  · intro h x

    have h_diff :
      ∑ z : F, RatFunc.mk (C <| m₁ z) (X - C z) - ∑ z : F, RatFunc.mk (C <| m₂ z) (X - C z) =
        ∑ z : F, RatFunc.mk (C (m₁ z - m₂ z)) (X - C z) := by
      rw [←Finset.sum_sub_distrib] ; congr ; apply @_root_.funext
      intro x ; simp ; ring
    have h_diff_eq_zero : ∑ z : F, RatFunc.mk (C (m₁ z - m₂ z)) (X - C z) = 0 := by
      rw [←h_diff, sub_eq_iff_eq_add, zero_add, h]
    have h_prod_sum_eq : ((algebraMap F[X] _) prodF) * ∑ z : F, RatFunc.mk (C (m₁ z - m₂ z)) (X - C z) =
        ∑ z : F, (algebraMap _ _) (C (m₁ z - m₂ z)) * (algebraMap _ _) (prodF_exc z) := by
      simp
      rw [Finset.sum_mk, Finset.sum_mk, ←Multiset.sum_map_mul_left]
      congr ;  apply @_root_.funext ; intro x
      rw [←prodF_ex_eq]
      simp [←mul_div_assoc]
      rw [mul_comm]
    have h_mul_zero :
        ∑ z : F, (algebraMap F[X] (RatFunc F)) (C (m₁ z - m₂ z)) * (algebraMap _ _) (prodF_exc z) = 0 := by
      rw [←h_prod_sum_eq, h_diff_eq_zero, mul_zero]
    -- The same, but for polynomials.
    have h_mul_poly_zero : ∑ z : F, C (m₁ z - m₂ z) * (prodF_exc z) = 0 := by
      simp only [←map_mul, ←map_sum, FaithfulSMul.algebraMap_eq_zero_iff] at h_mul_zero ; apply h_mul_zero
    have h_eval_zero : (∑ z : F, (C (m₁ z - m₂ z) * (prodF_exc z))).eval x = 0 := by
      simp only [h_mul_poly_zero] ; simp
    have h_in : x ∈ Finset.univ := by simp
    simp only [←Finset.add_sum_erase _ _ h_in] at h_eval_zero
    rw [eval_add, sum_prodF_eq_zero, add_zero, eval_mul, mul_eq_zero] at h_eval_zero
    cases' h_eval_zero with h_l h_r
    · rwa [eval_C, sub_eq_zero] at h_l
    exfalso ; apply prodF_exc_eval_ne_zero h_r
  intro h
  congr ; apply @_root_.funext
  intro x ; rw [h x]

lemma frac_sum_equiv {m : F → F} : ∑ z : F, RatFunc.mk (C <| m z) (X + C z) = ∑ z : F, RatFunc.mk (C <| m (-z)) (X + C (-z)) := by
  apply Fintype.sum_equiv (Equiv.mk (fun z => -z) (fun z => -z) (leftInverse_neg _) (rightInverse_neg _))
  simp

-- A variant of lemma 4 with X + C z instead of X - C z
lemma unique_decomposition' {m₁ m₂ : F → F} :
  ∑ z : F, RatFunc.mk (C <| m₁ z) (X + C z) = ∑ z : F, RatFunc.mk (C <| m₂ z) (X + C z) ↔
    ∀ z : F, m₁ z = m₂ z := by
  simp only [frac_sum_equiv, Polynomial.C_neg, ←sub_eq_add_neg]
  have h_m_neg : (∀ z : F, m₁ z = m₂ z) ↔ (∀ z : F, m₁ (-z) = m₂ (-z)) := by
    constructor
    · intros h z ; exact h (-z)
    intros h z ; rw [←neg_neg z] ; exact h (-z)
  simp only [h_m_neg]
  apply unique_decomposition

/-
  # Definitions and Auxiliary lemmas for lemma 5
-/

--variable {n : Type _} [Fintype n]

-- inverse image of a field element under b
def inv_b {n : Type _} [Fintype n] (b : n → F) := fun z => Finset.univ.val.filter (fun i => b i = z)
def frac_f {n : Type _} [Fintype n] (b : n → F) (m : n → F) := fun i => RatFunc.mk (C <| m i) (X + C (b i))
-- Function that maps every elements z in F to the multiset of fractions (with coefficients) for elements in b with that value.
def z_fracs {n : Type _} [Fintype n] (b : n → F) (m : n → F) := fun (z : F) => (inv_b b z).map (frac_f b m)
-- For each field element z, the sum of the coefficients for all elements in b with the value z.
def μ {n : Type _} [Fintype n] (b m : n → F) := fun z => ((inv_b b z).map m).sum
def μ' {n : Type _} [Fintype n] (b m : n → F) := fun z => ∑ i ∈ (inv_b b z).toFinset, m i

omit [Fintype F] in
lemma μ_eq {n : Type _} [Fintype n] {b m : n → F} : μ b m = μ' b m := by
  apply  @_root_.funext ; intro x
  unfold μ μ' ; rw [Finset.sum_eq_multiset_sum] ; congr ; simp
  rw [Eq.comm, Multiset.dedup_eq_self]
  apply Multiset.Nodup.filter
  apply Finset.nodup

omit [Field F] [Fintype F] in
lemma inv_b_count_ite {n : Type _} [Fintype n] {i : n} {b : n → F} {x : F} :
    Multiset.count i (inv_b b x) = if i ∈ inv_b b x then 1 else 0 := by
  by_cases h : i ∈ inv_b b x
  · simp only [eq_true h, ite_true]
    rw [Multiset.count_eq_one_of_mem _ h]
    apply Multiset.Nodup.filter
    apply Finset.nodup
  simp only [eq_false h, ite_false]
  rwa [Multiset.count_eq_zero_of_notMem]

omit [Field F]in
lemma inv_b_filter {n : Type _} [Fintype n] {i : n} {b : n → F} :
    (Finset.filter (fun (x : F) => i ∈ inv_b b x) Finset.univ) = {b i} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp [inv_b]
  intro x
  simp [inv_b]
  intro h ; rw [h]

omit [Field F] in
lemma sum_partition {n : Type _} [Fintype n] {b : n → F} : (∑ z : F, inv_b b z) = Finset.univ.val := by
  apply le_antisymm
  · rw [Multiset.le_iff_count]
    intro i
    rw [Multiset.count_sum']
    simp [inv_b_count_ite, Finset.sum_boole]
    simp [inv_b_filter, Finset.card_singleton]
  -- Same proof as above (can they be combined?)
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_sum']
  simp [inv_b_count_ite, Finset.sum_boole]
  simp [inv_b_filter]

lemma sum_map {α β : Type _} (s : Finset α) (f : n → β) (g : α → Multiset n) : ∑ x ∈ s, Multiset.map f (g x) = Multiset.map f (∑ x ∈ s, g x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ h_ni h_ind =>
    simp only [Finset.sum_insert h_ni]
    rw [Multiset.map_add, h_ind]

omit [Field F] in
lemma sum_map_F {β : Type _} (f : n → β) (g : F → Multiset n) : ∑ x : F, Multiset.map f (g x) = Multiset.map f (∑ x : F, g x) := by
  apply sum_map

lemma sum_fracs_partition {n : Type _} [Fintype n] {b m : n → F} :
    (∑ z : F, z_fracs b m z) = Finset.univ.val.map (frac_f b m) := by
  unfold z_fracs
  rw [sum_map_F (frac_f b m) (fun x => (inv_b b x))]
  rw [sum_partition]

lemma sum_frac_b_n_eq_sum_F {n : Type _} [Fintype n] {b m : n → F} :
    ∑ i : n, RatFunc.mk (C (m i)) (X + C (b i)) = (∑ z : F, z_fracs b m z).sum := by
  rw [sum_fracs_partition]
  unfold frac_f
  simp

omit [Fintype F] in
lemma RatFunc.mk_add_eq_denom {p₁ p₂ q : F[X]} : RatFunc.mk (p₁ + p₂) q = RatFunc.mk p₁ q + RatFunc.mk p₂ q := by
  simp ; ring

omit [Fintype F] in
lemma sum_frac_inv_b_eq_frac_μ {n : Type _} [Fintype n] {b m : n → F} {z : F}:
     Multiset.sum (z_fracs b m z) = RatFunc.mk (C <| (μ b m) z) (X + C z) := by
  unfold z_fracs frac_f

  have h_s (s : Multiset n) (h_s : s ≤ inv_b b z) :
      Multiset.sum (Multiset.map (fun i => RatFunc.mk (C (m i)) (X + C (b i))) s) = RatFunc.mk (C (s.map m).sum) (X + C z) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons n s h_in =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        rw [h_in (le_trans (Multiset.le_cons_self _ _) h_s)]
        rw [Multiset.of_mem_filter <| Multiset.mem_of_le h_s (Multiset.mem_cons_self _ _)]
        rw [Polynomial.C_add, RatFunc.mk_add_eq_denom]

  apply h_s (inv_b b z) (le_refl _)

lemma sum_map_count {m : Multiset F} :
    ∑ x ∈ Multiset.toFinset m, Multiset.count x m • RatFunc.mk 1 (X + C x) =
      ∑ x : F, Multiset.count x m • RatFunc.mk 1 (X + C x)  := by
  apply Finset.sum_subset
  · simp
  intros x _ h_x_n_mem
  simp only [Multiset.mem_toFinset] at h_x_n_mem
  rw [Multiset.count_eq_zero_of_notMem h_x_n_mem] ; simp

lemma count_eq_of_sum_eq {na nb : Type _} [Fintype na] [Fintype nb]
    (a : na → F)
    (b : nb → F) :
  ∀ m : nb → F,
    ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i)) →
      ∀ z, ↑(Multiset.count z (Multiset.map a Finset.univ.val)) = μ (fun i => b i) (fun i => m i) z := by

  intros m h_sums z

  rw [sum_frac_b_n_eq_sum_F, Multiset.sum_sum] at h_sums
  simp only [sum_frac_inv_b_eq_frac_μ] at h_sums

  have h_a : (fun i => RatFunc.mk 1 (X + C (a i))) = (fun z => RatFunc.mk 1 (X + C z)) ∘ a := by rfl

  rw [h_a] at h_sums ; unfold Finset.sum at h_sums
  rw [←Multiset.map_map, Finset.sum_multiset_map_count, sum_map_count] at h_sums

  apply unique_decomposition'.mp _ z
  convert h_sums
  simp only [nsmul_eq_mul, RatFunc.mk_eq_div, map_natCast, map_one, mul_div, mul_one]

lemma count_neg_eq {na : Type _} [Fintype na] {a : na → F} {z : F} :
    Multiset.count z (Multiset.map a Finset.univ.val) = Multiset.count (-z) (Multiset.map (-a) Finset.univ.val) := by
  have h_a : -a = (fun i => -i) ∘ a := by rfl
  rw [h_a, eq_comm, ←Multiset.map_map]
  apply Multiset.count_map_eq_count'
  intro a b ; simp

-- Same as count_eq_of_sum_eq, but with X - C instead of X + C
lemma count_eq_of_sum_eq' {na nb : Type _} [Fintype na] [Fintype nb]
    (a : na → F)
    (b : nb → F) :
  ∀ m : nb → F,
    ∑ i : na, RatFunc.mk 1 (X - C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X - C (b i)) →
      ∀ z, ↑(Multiset.count z (Multiset.map a Finset.univ.val)) = μ (fun i => b i) (fun i => m i) z := by
  intro m h z
  have h_μ : ∀ z, μ b m z = μ (-b) m (-z) := by
    intro z ; unfold μ inv_b ; simp
  rw [h_μ, count_neg_eq]
  apply count_eq_of_sum_eq (-a) (-b) m
  simp only [Pi.neg_apply, map_neg, ←sub_eq_add_neg]
  exact h

variable [Nonempty F]

-- The maximal count of a value in F in a multiset of values in F.
def max_count_F {na : Type _} [Fintype na] (a : na → F) : Nat :=
  Finset.max' ((Finset.univ : Finset F).val.map (fun x => Multiset.count x (Multiset.map a Finset.univ.val))).toFinset
  (by simp [←Finset.nonempty_iff_ne_empty])

lemma Multiset.map_count_neg_eq {na : Type _} [Fintype na] (a : na → F) :
    ((Finset.univ : Finset F).val.map (fun x => Multiset.count x (Multiset.map (-a) Finset.univ.val))).toFinset =
      ((Finset.univ : Finset F).val.map (fun x => Multiset.count x (Multiset.map a Finset.univ.val))).toFinset := by
  simp only [Finset.ext_iff, Multiset.mem_toFinset]
  intro n
  constructor
  all_goals
    intro h
    rw [Multiset.mem_map] at h
    rcases h with ⟨x, h_x_mem, h_x_count⟩
    rw [count_neg_eq] at h_x_count
    try simp at h_x_count
    rw [←h_x_count]
    simp

lemma max_count_F_eq_max_count_F_neg {na : Type _} [Fintype na] (a : na → F) :
    max_count_F a = max_count_F (-a) := by
  simp only [max_count_F, Multiset.map_count_neg_eq]

-- Main proof of one direction Lemma 5

lemma mem_b_of_sum_eq {na nb : Type _} [Fintype na] [Fintype nb]
    (a : na → F)
    (b : nb → F)
    (h_na_lt : max_count_F a < char_F) :
  ∀ m : nb → F,
    ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i)) →
      (∀ i, μ b m (b i) ≠ 0 ↔ ∃ j ∈ Finset.univ.val, a j = b i) := by

  intros m h_sums i
  have h_count := (count_eq_of_sum_eq a b m h_sums) (b i)

  constructor
  · intro h_μ
    rw [←Multiset.mem_map, ←Multiset.one_le_count_iff_mem]
    rw [←h_count] at h_μ
    apply @Nat.one_le_of_lt 0
    rw [←Nat.ne_zero_iff_zero_lt]
    apply ne_of_apply_ne (Nat.cast (R := F))
    convert h_μ ; simp

  intro h_j
  rw [←h_count]
  rw [ne_eq]
  rw [(charP_iff _ char_F).mp h_CharP_F]
  rw [←Multiset.mem_map, ←Multiset.one_le_count_iff_mem] at h_j
  apply Nat.not_dvd_of_pos_of_lt (lt_of_lt_of_le zero_lt_one h_j)
  apply lt_of_le_of_lt _ h_na_lt
  apply Finset.le_max'
  simp

-- Probably not used.
/-
lemma mem_b_of_sum_eq' {na nb : Type _} [Fintype na] [Fintype nb]
    (a : na → F)
    (b : nb → F) :
  ∀ m : nb → F,
    ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i)) →
      (∀ i, (Multiset.count (b i) (Multiset.map a Finset.univ.val) < char_F) →
        (μ b m (b i) ≠ 0 ↔ ∃ j ∈ Finset.univ.val, a j = b i)) := by

  intros m h_sums i h_char
  have h_count := (count_eq_of_sum_eq a b m h_sums) (b i)

  constructor
  · intro h_μ
    rw [←Multiset.mem_map, ←Multiset.one_le_count_iff_mem]
    rw [←h_count] at h_μ
    apply @Nat.one_le_of_lt 0
    rw [←Nat.ne_zero_iff_zero_lt]
    apply ne_of_apply_ne (Nat.cast (R := F))
    convert h_μ ; simp

  intro h_j
  rw [←h_count]
  rw [ne_eq]
  rw [(charP_iff _ char_F).mp h_CharP_F]
  rw [←Multiset.mem_map, ←Multiset.one_le_count_iff_mem] at h_j
  apply Nat.not_dvd_of_pos_of_lt (lt_of_lt_of_le zero_lt_one h_j)
  apply lt_of_le_of_lt _ h_char
  simp
-/

-- Lemma 5

omit [Fintype F] in
lemma eq_frac_of_set_inclusion {na nb : Type _} [Fintype na] [Fintype nb]
      (h_nb_lt : Fintype.card nb < char_F)
      (a : na → F)
      (b : nb → F) :
    Finset.univ.val.map a ⊆ Finset.univ.val.map b →
      ∃ m : nb → F,
        ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i)) := by

    let m_a := fun z : F => (Finset.univ.val.map a).count z
    let m_b := fun z : F => (Finset.univ.val.map b).count z

    intro h_subset

    let m := fun i => (m_a (b i) : F) / (m_b (b i))
    use m

    have h_a : (fun i => RatFunc.mk 1 (X + C (a i))) = (fun z => RatFunc.mk 1 (X + C z)) ∘ a := by rfl
    have h_b : (fun i => RatFunc.mk (C <| m i) (X + C (b i))) = (fun z => RatFunc.mk (C <| (m_a z : F) / (m_b z : F)) (X + C z)) ∘ b := by
      simp only [m] ; rfl
    rw [h_a, h_b] ; unfold Finset.sum
    simp only [←Multiset.map_map, Finset.sum_multiset_map_count]

    rw [←Multiset.toFinset_subset] at h_subset
    rw [Finset.sum_subset h_subset _]

    apply Finset.sum_congr rfl
    intros x h_x

    have h_one : (Multiset.count x (Multiset.map b Finset.univ.val)) • ((m_a x : F) / (m_b x : F)) = (m_a x : F) := by
      rw [←smul_div_assoc, ←smul_one_mul, Nat.smul_one_eq_cast]
      simp only [m_b]
      rw [mul_div_cancel_left₀]
      rw [ne_eq, (charP_iff _ char_F).mp h_CharP_F]
      apply Nat.not_dvd_of_pos_of_lt
      · rwa [Multiset.count_pos, ←Multiset.mem_toFinset]
      rw [Multiset.count_map]
      apply lt_of_le_of_lt (Finset.card_filter_le _ _)
      apply h_nb_lt

    conv_rhs =>
      rw [←mul_one ((m_a x : F) / (m_b x : F))]
      rw [Polynomial.C_mul, ←Polynomial.smul_eq_C_mul, Polynomial.C_1]
      rw [RatFunc.mk_smul]
      rw [←smul_assoc]
      rw [h_one]
      rw [←Nat.smul_one_eq_cast]
      rw [smul_assoc, one_smul]

    intros x _ h_x_ni
    simp only [Multiset.mem_toFinset] at h_x_ni
    rw [Multiset.count_eq_zero_of_notMem h_x_ni]
    simp

lemma set_inclusion_of {na nb : Type _} [Fintype na] [Fintype nb]
      --(h_na_lt : Fintype.card na < char_F)
      (a : na → F)
      (b : nb → F)
      (h_na_lt : max_count_F a < char_F) :
    (∃ m : nb → F,
      ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i))) →
        Finset.univ.val.map a ⊆ Finset.univ.val.map b := by

    intro h_eq
    rw [Multiset.subset_iff] ; intros z h_z
    rw [Multiset.mem_map]

    rcases h_eq with ⟨m, h_sums⟩

    rw [←Multiset.one_le_count_iff_mem] at h_z

    have h_count : (Multiset.count z (Multiset.map a Finset.univ.val) : F) ≠ 0 := by
      rw [ne_eq, (charP_iff _ char_F).mp h_CharP_F]
      apply Nat.not_dvd_of_pos_of_lt (lt_of_lt_of_le zero_lt_one h_z)
      apply lt_of_le_of_lt _ h_na_lt
      apply Finset.le_max'
      simp

    rw [count_eq_of_sum_eq a b m h_sums z] at h_count
    rw [μ_eq] at h_count

    have preimage_ne_zero := Multiset.toFinset_nonempty.mp (Finset.nonempty_of_sum_ne_zero h_count)
    rcases Multiset.exists_mem_of_ne_zero preimage_ne_zero with ⟨i, h_in_inv_b⟩

    use i
    constructor
    · simp
    unfold inv_b at h_in_inv_b
    rw [Multiset.mem_filter] at h_in_inv_b
    exact h_in_inv_b.2

lemma mem_b_of_mem_a {na nb : Type _} [Fintype na] [Fintype nb]
      (a : na → F)
      (b : nb → F)
      (i : na)
      (h_i : Multiset.count (a i) (Multiset.map a Finset.univ.val) < char_F) :
    (∃ m : nb → F,
      ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i))) →
        a i ∈ Finset.univ.val.map b := by
    intro h_eq
    rcases h_eq with ⟨m, h_sums⟩

    have h_count : (Multiset.count (a i) (Multiset.map a Finset.univ.val) : F) ≠ 0 := by
      rw [ne_eq, (charP_iff _ char_F).mp h_CharP_F]
      apply Nat.not_dvd_of_pos_of_lt _ h_i
      rw [zero_lt_iff, ←Nat.one_le_iff_ne_zero, Multiset.one_le_count_iff_mem]
      simp

    rw [count_eq_of_sum_eq a b m h_sums (a i)] at h_count
    rw [μ_eq] at h_count

    have preimage_ne_zero := Multiset.toFinset_nonempty.mp (Finset.nonempty_of_sum_ne_zero h_count)
    rcases Multiset.exists_mem_of_ne_zero preimage_ne_zero with ⟨j, h_in_inv_b⟩

    rw [Multiset.mem_map]
    use j
    constructor
    · simp
    unfold inv_b at h_in_inv_b
    rw [Multiset.mem_filter] at h_in_inv_b
    exact h_in_inv_b.2

-- Same as set_inclusion, but with X - C instead of X + C
omit [Fintype F] in
lemma eq_frac_of_set_inclusion' {na nb : Type _} [Fintype na] [Fintype nb]
      (h_nb_lt : Fintype.card nb < char_F)
      (a : na → F)
      (b : nb → F) :
    Finset.univ.val.map a ⊆ Finset.univ.val.map b →
      ∃ m : nb → F,
        ∑ i : na, RatFunc.mk 1 (X - C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X - C (b i)) := by
  simp only [sub_eq_add_neg, ←map_neg]
  simp only [←Pi.neg_apply]
  intro h_subset
  apply eq_frac_of_set_inclusion h_nb_lt (-a) (-b)

  simp only [Multiset.subset_iff, Multiset.mem_map]
  simp only [Pi.neg_apply, neg_eq_iff_eq_neg]
  simp only [Multiset.subset_iff, Multiset.mem_map] at h_subset

  intro x h_i
  exact h_subset (x := -x) h_i

-- Same as set_inclusion, but with X - C instead of X + C
lemma set_inclusion_of' {na nb : Type _} [Fintype na] [Fintype nb]
      (a : na → F)
      (b : nb → F)
      (h_na_lt : max_count_F a < char_F) :
      (∃ m : nb → F,
        ∑ i : na, RatFunc.mk 1 (X - C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X - C (b i))) →
          Finset.univ.val.map a ⊆ Finset.univ.val.map b := by
  simp only [sub_eq_add_neg, ←map_neg]
  simp only [←Pi.neg_apply]
  intro h_sum_eq
  rw [max_count_F_eq_max_count_F_neg] at h_na_lt
  have h_subset := set_inclusion_of (-a) (-b) h_na_lt h_sum_eq

  simp only [Multiset.subset_iff, Multiset.mem_map]
  simp only [Multiset.subset_iff, Multiset.mem_map] at h_subset
  simp only [Pi.neg_apply, neg_eq_iff_eq_neg] at h_subset

  intro x h_i
  replace h_subset := h_subset (x := -x)
  simp only [neg_neg] at h_subset
  exact h_subset h_i

-- Same as mem_b_of_mem_a, but with X - C instead of X + C
lemma mem_b_of_mem_a' {na nb : Type _} [Fintype na] [Fintype nb]
      (a : na → F)
      (b : nb → F)
      (i : na)
      (h_i : Multiset.count (a i) (Multiset.map a Finset.univ.val) < char_F) :
    (∃ m : nb → F,
      ∑ i : na, RatFunc.mk 1 (X - C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X - C (b i))) →
        a i ∈ Finset.univ.val.map b := by
  simp only [sub_eq_add_neg, ←map_neg]
  simp only [←Pi.neg_apply]
  intro h_sum_eq

  rw [count_neg_eq] at h_i
  have h_mem := mem_b_of_mem_a (-a) (-b) i h_i h_sum_eq
  simp only [Multiset.mem_map, Pi.neg_apply, neg_eq_iff_eq_neg, neg_neg] at h_mem
  rw [Multiset.mem_map]
  exact h_mem

lemma set_equality {na nb : Type _} [Fintype na] [Fintype nb]
      (a : na → F)
      (b : nb → F)
      (h_na_lt : max_count_F a < char_F)
      (h_nb_lt : Fintype.card nb < char_F) :
    (Finset.univ.val.map a).toFinset = (Finset.univ.val.map b).toFinset ↔
      ∃ m : nb → F,
        ∑ i : na, RatFunc.mk 1 (X + C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X + C (b i))
        ∧ ∀ i, μ b m (b i) ≠ 0 := by

  constructor
  · intro h_set_eq
    have h := (Multiset.toFinset_subset.mp (subset_of_eq h_set_eq))
    rcases (eq_frac_of_set_inclusion (h_CharP_F := h_CharP_F) h_nb_lt a b) h with ⟨m, h_m⟩
    use m, h_m
    intro i
    apply (mem_b_of_sum_eq (h_CharP_F := h_CharP_F) a b h_na_lt m h_m i).mpr
    rw [←Multiset.mem_map, ←Multiset.mem_toFinset, h_set_eq] ; simp

  intro ⟨m, h_m, h_ne_zero⟩
  apply subset_antisymm
  · rw [Multiset.toFinset_subset]
    apply (set_inclusion_of (h_CharP_F := h_CharP_F) a b h_na_lt) ⟨m, h_m⟩
  rw [Multiset.toFinset_subset, Multiset.subset_iff]
  intro z h_z
  rcases Multiset.mem_map.mp h_z with ⟨i, _, h_eq_z⟩
  rw [Multiset.mem_map, ←h_eq_z]
  rcases (mem_b_of_sum_eq (h_CharP_F := h_CharP_F) a b h_na_lt m h_m i).mp (h_ne_zero i) with ⟨j, h_j, h_eq_b_i⟩
  use j

-- Same as set_equality, but with X - C instead of X + C
lemma set_equality' {na nb : Type _} [Fintype na] [Fintype nb]
      (a : na → F)
      (b : nb → F)
      (h_na_lt : max_count_F a < char_F)
      (h_nb_lt : Fintype.card nb < char_F) :
    (Finset.univ.val.map a).toFinset = (Finset.univ.val.map b).toFinset ↔
      ∃ m : nb → F,
        ∑ i : na, RatFunc.mk 1 (X - C (a i)) = ∑ i : nb, RatFunc.mk (C <| m i) (X - C (b i))
        ∧ ∀ i, μ b m (b i) ≠ 0 := by
  rw [max_count_F_eq_max_count_F_neg] at h_na_lt
  simp only [sub_eq_add_neg, ←map_neg]
  simp only [←Pi.neg_apply]
  have h_inv_b (i : nb) : inv_b b (b i) = inv_b (-b) (-b i) := by
    unfold inv_b ; simp
  have h_μ (m : nb → F) : ∀ i, μ b m (b i) = μ (-b) m ((-b) i) := by
    intro i ; unfold μ ; simp only [h_inv_b] ; rfl
  simp only [h_μ]
  rw [←set_equality (-a) (-b) h_na_lt h_nb_lt]
  simp only [Finset.ext_iff, Multiset.mem_toFinset, Multiset.mem_map]
  simp only [Pi.neg_apply, neg_eq_iff_eq_neg]
  constructor
  · intro h x ; exact @h (-x)
  intro h x
  have h_mem := @h (-x)
  rw [neg_neg] at h_mem
  exact h_mem
