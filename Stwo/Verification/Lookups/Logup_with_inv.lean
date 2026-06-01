import Verification.Lookups.Logup

noncomputable section
open scoped Classical BigOperators

open Polynomial

variable {F : Type _} [Field F]

/-
  In this version of the logup constraints, we partition the indexes (indxsK s k)
  (the indexes in a single cumulative constraint) into sub-lists (indxsKv s v k j).

  An additional set of values is defined, and for each k and l we define constraints
  that show that the corresponding value is the multiplicative inverse of
  ∏ i ∈ (indxsKv s v k l), (z ∘  r i - f i).
  These constraints show that z does not collide with any of the values of f.
  These inverse values are then also used in the cumulative constraints.
-/

def indxsKv {t n_s n_v : Nat} (s : Fin t → Fin n_s) (v : Fin t → Fin n_v) (k : Nat) (j : Fin t) :=
  (indxsK s k).filter fun i => v i = v j

def prodKv_exc {t n_s n_v : Nat}
    (s : Fin t → Fin n_s)
    (v : Fin t → Fin n_v)
    (f z : Fin t → F)
    (k : Nat)
    (i : Fin t) :=
  (((indxsKv s v k i).erase i).map fun j => z j - f j).prod

lemma idxK_mem_k {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) :
    ∀ j : Fin (indxsK s k).length, idxK s k j ∈ indxsK s k := by
  intro j ; unfold idxK
  apply List.get_mem

lemma idxK_mem_kv {t n_s n_v : Nat} (s : Fin t → Fin n_s) (v : Fin t → Fin n_v) (k : Nat) :
    ∀ j : Fin (indxsK s k).length, idxK s k j ∈ indxsKv s v k (idxK s k j) := by
  intro j ; unfold indxsKv
  rw [List.mem_filter]
  use (idxK_mem_k s k j)
  simp

lemma prodKv_exc_mul_eq_prod {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin n_s)
      (v : Fin t → Fin n_v)
      (r : Fin t → Fin n_r)
      (z : Fin n_r → F)
      (k : Fin n_s) :
    ∀ j : Fin (indxsK s k).length,
      (prodKv_exc s v f (z ∘ r) k (idxK s k j)) * ((z ∘ r)  (idxK s k j) - f (idxK s k j)) =
        ((indxsKv s v k (idxK s k j)).map fun i => (z ∘ r) i - f i).prod := by
  intro j
  unfold prodKv_exc
  rw [←List.prod_map_erase _ (idxK_mem_kv s v k j), mul_comm]

lemma constraint_prod_eq_frac {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin n_s)
      (v : Fin t → Fin n_v)
      (r : Fin t → Fin n_r)
      (z : Fin n_r → F)
      (inv : Fin n_s → Fin n_v → F)
      (k : Fin n_s)
      (h_inv : ∀ i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0 ∧
        inv k (v (idxK s k i)) = ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod⁻¹) :
    let f_k := funK s k f
    let z_k := funK s k (z ∘ r)
    let m_k := funK s k m
    ∀ j : Fin (indxsK s k).length,
      (funK s k m j) * (prodKv_exc s v f (z ∘ r) k (idxK s k j)) * (inv k (v (idxK s k j))) = (m_k j) / (z_k j - f_k j) := by
  intro _ _ _ j
  rw [(h_inv j).2]
  rw [←prodKv_exc_mul_eq_prod f s v r z k j]
  rw [mul_inv, mul_assoc]
  conv => arg 1 ; arg 2 ; rw [←mul_assoc] ; arg 1

  have h_prod_ne_zero : (z ∘ r) (idxK s (↑k) j) - f (idxK s (↑k) j) ≠ 0
      ∧ prodKv_exc s v f (z ∘ r) k (idxK s k j) ≠ 0 := by
    rw [←mul_ne_zero_iff]
    unfold prodKv_exc
    rw [List.prod_map_erase ((fun j => (z ∘ r) j - f j)) (idxK_mem_kv s v k j)]
    apply (h_inv j).1

  rw [mul_inv_cancel₀ h_prod_ne_zero.2, one_mul]
  rw [inv_eq_one_div, mul_div, mul_one]
  rfl

lemma z_sub_f_ne_zero_iff_prod_ne_zero {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin n_s)
      (v : Fin t → Fin n_v)
      (r : Fin t → Fin n_r)
      (z : Fin n_r → F)
      (k : Fin n_s) :
    (∀ i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0) ↔
      ∀ (i : Fin (indxsK s k).length), funK s k f i ≠ funK s k (z ∘ r) i := by
  conv_lhs =>
    simp only [ne_eq] ; simp only [List.prod_eq_zero_iff, List.mem_map]
    simp only [not_exists, not_and, sub_ne_zero, ne_comm]
  unfold funK indxsKv idxK
  simp only [List.forall_mem_filter]
  constructor
  · intro h i
    apply h i ((indxsK s ↑k).get i)
    apply List.get_mem
    simp only [List.get_eq_getElem, decide_true]
  intro h i j h_mem h_eq
  rw [List.mem_iff_get] at h_mem
  rcases h_mem with ⟨n, h_n⟩
  rw [←h_n]
  exact h n

lemma z_sub_f_ne_zero_of_forall_prod_ne_zero {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F) :
    (∀ (k : Fin (n_s + 1)) i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0) →
      ∀ j, f j ≠ (z ∘ r) j := by
  intro h_ne_zero j

  have h_j_mem : j ∈ indxsK s (s j) := by
    unfold indxsK
    simp only [List.mem_filter, Finset.mem_toList, decide_true, and_true]
    use (Fintype.complete j)
  rw [List.mem_iff_get] at h_j_mem
  rcases h_j_mem with ⟨i, h_i⟩

  replace h_ne_zero := h_ne_zero (s j)
  rw [z_sub_f_ne_zero_iff_prod_ne_zero f s v r z (s j)] at h_ne_zero
  replace h_ne_zero := h_ne_zero i
  unfold funK at h_ne_zero ; rwa [h_i] at h_ne_zero

lemma z_sub_f_ne_zero_on_r_of_prod_ne_zero {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F) :
    (∀ (k : Fin (n_s + 1)) i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0) →
      ∀ (l : Fin (n_r + 1)) j, z l ≠ funK r l f j := by
  intro h_ne_zero l j
  rw [←forall_r_z r z l j, ne_comm]
  unfold funK
  apply z_sub_f_ne_zero_of_forall_prod_ne_zero f s v r z h_ne_zero

-- The cumulative constraints

def cumulativeC_kv {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (p : Nat → F)
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (k : Fin (n_s + 1)) :=
    ∑ j : Fin (indxsK s k).length,
      (funK s k m j) * (prodKv_exc s v f (z ∘ r) k (idxK s k j)) * (inv k (v (idxK s k j))) = (p k.succ - p k)

def cumulativeC_v {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (p : Nat → F)
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F) :=
    ∀ k : Fin (n_s + 1), cumulativeC_kv f m s v r p z inv k

lemma constraint_inv_as_frac {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (p : Nat → F)
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (k : Fin (n_s + 1))
      (h_inv : ∀ i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0 ∧
        inv k (v (idxK s k i)) = ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod⁻¹) :
    let f_k := funK s k f
    let z_k := funK s k (z ∘ r)
    let m_k := funK s k m
    cumulativeC_kv f m s v r p z inv k ↔
      ∑ j : Fin (indxsK s k).length, (m_k j) / (z_k j - f_k j) = (p k.succ - p k) := by
  unfold cumulativeC_kv
  simp only [constraint_prod_eq_frac f m s v r z inv k h_inv]

lemma cumulativeC_kv_iff_cumulativeC_k {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (p : Nat → F)
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (k : Fin (n_s + 1))
      (h_inv : ∀ i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0 ∧
        inv k (v (idxK s k i)) = ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod⁻¹) :
    cumulativeC_kv f m s v r p z inv k ↔ cumulativeC_k f m s r p z k := by
  simp only [constraint_inv_as_frac f m s v r p z inv k h_inv]
  have h := (z_sub_f_ne_zero_iff_prod_ne_zero f s v r z k).mp (forall_and.mp h_inv).1
  simp only [constraint_as_frac f m s r z p k h]
  rfl

lemma cumulativeC_v_iff_cumulativeC {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (p : Nat → F)
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (h_inv : ∀ (k : Fin (n_s + 1)) i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0 ∧
        inv k (v (idxK s k i)) = ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod⁻¹) :
    cumulativeC_v f m s v r p z inv ↔ cumulativeC f m s r z p := by
  unfold cumulativeC_v cumulativeC
  constructor
  · intro h_cum k
    apply (cumulativeC_kv_iff_cumulativeC_k f m s v r p z inv k (h_inv k)).mp (h_cum k)
  intro h_cum k
  apply (cumulativeC_kv_iff_cumulativeC_k f m s v r p z inv k (h_inv k)).mpr (h_cum k)

-- Zero set

variable [Fintype F]

lemma not_mem_exceptionalSet_of_inv_and_not_zero_set {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (h_z : z ∉ zero_set f m r)
      (h_prod_ne_zero : ∀ (k : Fin (n_s + 1)) i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0) :
    z ∉ exceptionalSet f m r := by
  unfold exceptionalSet

  by_cases h : ∀ (k : Fin (n_r + 1)),
        ∑ j : Fin (indxsK r ↑k).length, RatFunc.mk (C (funK r (↑k) m j)) (X - C (funK r (↑k) f j)) = 0
  · rw [if_pos h] ; apply Finset.notMem_empty
  rw [if_neg h]
  simp only [exceptionalSet_filter_or_not_and]
  simp only [Finset.filter_or, Finset.notMem_union]
  constructor
  · simp only [Finset.mem_filter, not_and, not_exists, ←ne_eq] ; intro _ k
    exact z_sub_f_ne_zero_on_r_of_prod_ne_zero f s v r z h_prod_ne_zero k
  apply h_z

def zero_set_v {t n_r : Nat} (f m : Fin t → F) (r : Fin t → Fin (n_r + 1)) : Finset (Fin (n_r + 1) → F) :=
  if ∀ k : Fin (n_r + 1), ∑ j : Fin (indxsK r k).length, (RatFunc.mk (C (funK r k m j)) (X - C (funK r k f j))) = 0
    then ∅
    else zero_set f m r

lemma not_mem_exceptionalSet_of_inv_and_not_zero_set_v {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (h_z : z ∉ zero_set_v f m r)
      (h_prod_ne_zero : ∀ (k : Fin (n_s + 1)) i, ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0) :
    z ∉ exceptionalSet f m r := by
  by_cases h : ∀ (k : Fin (n_r + 1)),
        ∑ j : Fin (indxsK r ↑k).length, RatFunc.mk (C (funK r (↑k) m j)) (X - C (funK r (↑k) f j)) = 0
  · unfold exceptionalSet
    rw [if_pos h] ; apply Finset.notMem_empty
  unfold zero_set_v at h_z
  rw [if_neg h] at h_z
  apply not_mem_exceptionalSet_of_inv_and_not_zero_set f m s v r z h_z h_prod_ne_zero

lemma card_zero_set_v_le_exists_k {t n_r : Nat}
      (f m : Fin t → F)
      (r : Fin t → Fin (n_r + 1)) :
    ∃ (k : Fin (n_r + 1)), (zero_set_v f m r).card ≤ (Fintype.card F) ^ (n_r) * ((indxsK r k).length + 1) := by
  by_cases h : ∀ (k : Fin (n_r + 1)),
        ∑ j : Fin (indxsK r ↑k).length, RatFunc.mk (C (funK r (↑k) m j)) (X - C (funK r (↑k) f j)) = 0
  · unfold zero_set_v
    rw [if_pos h, Finset.card_empty]
    use 0
    exact Nat.zero_le _
  unfold zero_set_v
  rw [if_neg h]
  simp only [not_forall, ←ne_eq] at h
  rcases h with ⟨k, h_k⟩
  use k
  apply card_zero_set_le f m r k h_k

lemma card_zero_set_v_le {t n_r : Nat}
      (f m : Fin t → F)
      (r : Fin t → Fin (n_r + 1)) :
    (zero_set_v f m r).card ≤ (Fintype.card F) ^ (n_r) * (max_pr_len r) := by
  rcases card_zero_set_v_le_exists_k f m r with ⟨k, h_card_le⟩
  apply le_trans h_card_le
  apply Nat.mul_le_mul_left
  apply Finset.le_max'
  apply Finset.mem_image_of_mem
  apply (Fintype.complete k)

-- Non-colllision constraints

-- Single non-collison constraint
def nonCollisionC_k_i {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (k : Fin (n_s + 1))
      (i : Fin (indxsK s ↑k).length)
      (inv_k_i : F) :=
  ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod * inv_k_i - 1 = 0

-- All non-collision constraints

-- This definition is slightly misleading (though correct) because the same constraint
-- appears here multiple times (because for the same k, multiple i's belong to the same product).

def nonCollisionC {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F) :=
  ∀ (k : Fin (n_s + 1)) (i : Fin (indxsK s ↑k).length), nonCollisionC_k_i f s v r z k i (inv k (v (idxK s k i)))

omit [Fintype F] in
lemma prod_ne_zero_of_nonCollision_k_i {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (k : Fin (n_s + 1))
      (i : Fin (indxsK s ↑k).length)
      (inv_k_i : F)
      (h_nonCollision : nonCollisionC_k_i f s v r z k i inv_k_i) :
    ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod ≠ 0 := by
  unfold nonCollisionC_k_i at h_nonCollision
  rw [sub_eq_zero] at h_nonCollision
  have h_ne := ne_of_eq_of_ne h_nonCollision zero_ne_one.symm
  rw [mul_ne_zero_iff] at h_ne
  exact h_ne.1

omit [Fintype F] in
lemma prod_inv_of_nonCollision_k_i {t n_s n_r n_v : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (k : Fin (n_s + 1))
      (i : Fin (indxsK s ↑k).length)
      (inv_k_i : F)
      (h_nonCollision : nonCollisionC_k_i f s v r z k i inv_k_i) :
    inv_k_i = ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ r) j - f j).prod⁻¹ := by
  rw [←mul_eq_one_iff_eq_inv₀ (prod_ne_zero_of_nonCollision_k_i f s v r z k i inv_k_i h_nonCollision)]
  unfold nonCollisionC_k_i at h_nonCollision
  rwa [sub_eq_zero, mul_comm] at h_nonCollision

lemma inclusion_of_inv_constraints_and_not_zero_set {t n_s n_r n_v : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (r : Fin t → Fin (n_r + 1))
      (z : Fin (n_r + 1) → F)
      (p : Nat → F)
      (h_use_count_lt : ∀ k, max_count_F (useK m r k f) < ringChar F)
      (h_z : z ∉ zero_set_v f m r)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (h_cumulativeC_v : cumulativeC_v f m s v r p z inv)
      (h_cyclic : p n_s.succ = p 0)
      (h_nonCollision : nonCollisionC f s v r z inv) :
    ∀ k : Fin (n_r + 1), Finset.univ.val.map (useK m r k f) ⊆ Finset.univ.val.map (yieldK m r k f) := by
  apply inclusion_of_constraints_and_not_exceptionalSet f m s r z p h_use_count_lt _ _ h_cyclic
  · apply not_mem_exceptionalSet_of_inv_and_not_zero_set_v f m s v r z h_z
    intro k i
    apply prod_ne_zero_of_nonCollision_k_i f s v r z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
  apply (cumulativeC_v_iff_cumulativeC f m s v r p z inv _).mp h_cumulativeC_v
  intro k i
  use prod_ne_zero_of_nonCollision_k_i f s v r z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
  apply prod_inv_of_nonCollision_k_i f s v r z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
