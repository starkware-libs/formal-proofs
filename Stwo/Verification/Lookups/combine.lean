import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fin.SuccPred
import Verification.Lookups.Logup
import Verification.Lookups.Logup_with_inv

noncomputable section
open scoped Classical BigOperators

open Polynomial

variable {F : Type _} [Field F]

/-
  This file handles the mapping ('combine') of the values in tuplea over F into
  values in F. These values in F are then used in the logup.

  The combination function maps [a_0, ..., a_n] → a_0 + α a_1 + ... + α^n a_n
-/

def combine {n : Nat} (α : F) (a : Fin (n + 1) → F) := ∑ i : Fin (n + 1), a i * α ^ (i : Nat)
def combine_poly {n : Nat} (a : Fin (n + 1) → F) : F[X] := ∑ i : Fin (n + 1), C (a i) * X ^ (i : Nat)

lemma combine_eq_combine_poly_eval {n : Nat} (α : F) (a : Fin (n + 1) → F) :
    combine α a = (combine_poly a).eval α := by
  unfold combine_poly combine
  simp only [Polynomial.eval_finset_sum] ; simp

lemma combine_poly_sub_eq {n : Nat} (a b : Fin (n + 1) → F) :
    (combine_poly a - combine_poly b) = ∑ i : Fin (n + 1), C ((a i) - (b i)) * X ^ (i : Nat) := by
  unfold combine_poly
  simp only [←Finset.sum_sub_distrib, ←mul_sub_right_distrib, map_sub]

lemma collision_IsRoot {n : Nat} (α : F) (a b : Fin (n + 1) → F) :
    combine α a = combine α b ↔ (combine_poly a - combine_poly b).IsRoot α := by
  simp only [combine_eq_combine_poly_eval]
  rw [←sub_eq_zero, ←Polynomial.eval_sub, iff_comm, Polynomial.IsRoot.def]

lemma coeff_eq {n : Nat} (a : Fin (n + 1) → F) (k : Fin (n + 1)) :
    (∑ i : Fin (n + 1), C (a i) * X ^ (i : Nat)).coeff k = a k := by
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  simp only [Fin.val_eq_val, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma pair_collision_poly_ne_zero {n : Nat} (a b : Fin (n + 1) → F) (h_ne : a ≠ b) :
    (combine_poly a - combine_poly b) ≠ 0 := by
  intro h_eq ; apply h_ne
  ext k
  rw [←sub_eq_zero] ; rw [←coeff_eq (fun i => a i - b i) k]
  rw [combine_poly_sub_eq] at h_eq
  rw [h_eq]
  simp only [coeff_zero]

variable [Fintype F]

lemma pair_collisions_eq_roots {n : Nat} (a b : Fin (n + 1) → F) (h_ne : a ≠ b) :
    (Finset.univ.filter fun α => combine α a = combine α b) = (combine_poly a - combine_poly b).roots.toFinset := by
  ext x
  simp only [Finset.mem_filter, collision_IsRoot, Finset.mem_univ, true_and, Multiset.mem_toFinset]
  simp only [Polynomial.mem_roots (pair_collision_poly_ne_zero a b h_ne)]

lemma pair_collision_card {n : Nat} (a b : Fin (n + 1) → F) (h_ne : a ≠ b) :
    (Finset.univ.filter fun α => combine α a = combine α b).card ≤ n := by
  rw [pair_collisions_eq_roots a b h_ne]
  apply le_trans (Multiset.toFinset_card_le _)
  apply le_trans (Polynomial.card_roots' _)
  rw [combine_poly_sub_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _
  intro i _
  apply le_trans _ (Nat.le_of_lt_succ i.isLt)
  apply Polynomial.natDegree_C_mul_X_pow_le

def badSet {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) : Finset F :=
  if Finset.image tuples use_i ⊆ Finset.image tuples yield_i
  then ∅
  else
    Finset.univ.filter fun α => ∀ u, u ∈ Finset.image tuples use_i \ Finset.image tuples yield_i →
      ∃ y, y ∈ Finset.image tuples (Finset.univ \ use_i) ∧ combine α u = combine α y

lemma badSet_subset {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (yield_i : Finset (Fin l))
      (x : Fin (n + 1) → F)
      (h_x : x ∈ Finset.image tuples use_i \ Finset.image tuples yield_i) :
    badSet tuples use_i yield_i ⊆ (Finset.image tuples (Finset.univ \ use_i)).biUnion
      (fun y => Finset.univ.filter fun α => combine α x = combine α y) := by
  unfold badSet
  by_cases h : Finset.image tuples use_i ⊆ Finset.image tuples yield_i
  · -- This case never happens, but it is easier to prove this case than to show it is impossible.
    rw [if_pos h] ; apply Finset.empty_subset
  rw [if_neg h, Finset.subset_iff]
  simp only [Finset.mem_filter]
  rintro α ⟨h_α_mem, h_α⟩
  rw [Finset.mem_biUnion]
  rcases h_α x h_x with ⟨y, h_y_in, h_y_eq⟩
  use y, h_y_in
  rw [Finset.mem_filter]
  use h_α_mem

omit [Field F] [Fintype F] in
lemma not_mem_of_eq_use_or_yield {n l: Nat}
      {tuples : Fin l → (Fin (n + 1) → F)}
      {use_i : Finset (Fin l)}
      {yield_i : Finset (Fin l)}
      -- The tuple of different relations are disjoint.
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j) :
    ∀ i j, tuples i = tuples j → i ∈ use_i → j ∉ Finset.univ \ (use_i ∪ yield_i) := by
  intro i j h_eq h_use
  by_contra h
  apply h_disjoint i _ j _ h_eq
  exact Finset.mem_union_left _ h_use
  exact (Finset.mem_sdiff.mp h).2

lemma Finset.union_sdiff_sdiff_eq_self {α : Type u_1 }  [DecidableEq α] {s t : Finset α} :
    s = (s ∪ t) \ (t \ s) := by
  rw [Finset.union_sdiff_distrib, Finset.sdiff_sdiff_self_left]
  rw[Finset.sdiff_sdiff_eq_sdiff_union (subset_refl _)]
  rw [Finset.union_eq_right (t := s).mpr Finset.sdiff_subset]
  rw [Finset.union_eq_left.mpr Finset.inter_subset_right]

omit [Field F] [Fintype F] in
lemma mem_yield_of_not_use_eq_use {n l: Nat}
      {tuples : Fin l → (Fin (n + 1) → F)}
      {use_i : Finset (Fin l)}
      {yield_i : Finset (Fin l)}
      -- The tuple of different relations are disjoint.
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j) :
    ∀ x, x ∈ Finset.image tuples use_i →
            x ∈ Finset.image tuples (Finset.univ \ use_i) →
                x ∈ Finset.image tuples yield_i := by
  simp only [Finset.mem_image]
  intro x h_use h_not_use
  have h_union : (Finset.univ \ use_i) = (Finset.univ \ (use_i ∪ yield_i)) ∪ (yield_i \ use_i) := by
    rw [←Finset.sdiff_sdiff_eq_sdiff_union (Finset.subset_univ _), ←Finset.union_sdiff_sdiff_eq_self]
  rw [h_union] at h_not_use
  rcases h_not_use with ⟨j, h_mem, h_eq⟩
  use j
  simp only [h_eq, and_true]
  apply ((Finset.mem_sdiff (t := use_i)).mp _).1
  rw [Finset.mem_union] at h_mem
  apply Or.resolve_left h_mem
  rcases h_use with ⟨i, h_i_mem, h_i_eq⟩
  apply not_mem_of_eq_use_or_yield h_disjoint i j _ h_i_mem
  simp [h_i_eq, h_eq]

lemma mem_diff_collision_card {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (yield_i : Finset (Fin l))
      -- The tuple of different relations are disjoint.
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j)
      (x : Fin (n + 1) → F)
      (h_x : x ∈ Finset.image tuples use_i \ Finset.image tuples yield_i) :
    ∀ y ∈ Finset.image tuples (Finset.univ \ use_i),
      (Finset.univ.filter fun α => combine α x = combine α y).card ≤ n := by
  intro y h_y
  have h_ne : x ≠ y := by
    by_contra h
    rw [Finset.mem_sdiff, h] at h_x
    apply h_x.2 _
    exact mem_yield_of_not_use_eq_use h_disjoint y h_x.1 h_y
  apply pair_collision_card _ _ h_ne

lemma card_badSet_le_yield {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (yield_i : Finset (Fin l))
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j) :
    (badSet tuples use_i yield_i).card ≤ (Finset.univ \ use_i).card * n := by
  unfold badSet
  by_cases h : Finset.image tuples use_i ⊆ Finset.image tuples yield_i
  · rw [if_pos h, Finset.card_empty] ; apply Nat.zero_le
  rw [Finset.subset_iff, Classical.not_forall] at h
  simp only [_root_.not_imp] at h
  rcases h with ⟨x, h_x⟩
  rw [←Finset.mem_sdiff] at h_x
  apply le_trans (Finset.card_le_card (badSet_subset tuples use_i yield_i x h_x))
  apply le_trans (Finset.card_biUnion_le_card_mul _ _ _ (mem_diff_collision_card tuples use_i yield_i h_disjoint x h_x))
  apply mul_le_mul_right'
  apply le_trans Finset.card_image_le
  simp only [le_refl]

lemma card_badSet_le {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (yield_i : Finset (Fin l))
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j) :
    (badSet tuples use_i yield_i).card ≤ l * n := by
  apply le_trans (card_badSet_le_yield tuples use_i yield_i h_disjoint)
  apply mul_le_mul_right'
  apply le_trans (Finset.card_le_card Finset.sdiff_subset)
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [le_refl]

def inclusion_of_not_badSet {n l : Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (yield_i : Finset (Fin l))
      (α : F)
      (h_inclusion : (Finset.image (combine α ∘ tuples) use_i) ⊆ Finset.image (combine α ∘ tuples) (Finset.univ \ use_i))
      (h_α : α ∉ badSet tuples use_i yield_i) :
    Finset.image tuples use_i ⊆ Finset.image tuples yield_i := by
  by_contra h
  unfold badSet at h_α
  rw [if_neg h] at h_α
  apply h_α
  simp only [Finset.mem_filter, Finset.mem_univ α, true_and]
  intro x h_x
  rw [Finset.mem_sdiff] at h_x
  have h_x_in : combine α x ∈ Finset.image (combine α) (Finset.image tuples use_i) := by
    rw [Finset.mem_image] ; use x, h_x.1
  rw [Finset.subset_iff, ←Finset.image_image] at h_inclusion
  replace h_inclusion := h_inclusion h_x_in
  rw [←Finset.image_image, Finset.mem_image] at h_inclusion
  simp only [Eq.comm] at h_inclusion
  apply h_inclusion

def to_indxs_surOn {t n_p : ℕ}
    (pr : Fin t → Fin (n_p + 1))
    (k : Fin (n_p + 1))
    (to_indxs : Fin (indxsK pr k).length → Fin t) :=
  (∀ i, to_indxs i ∈ indxsK pr k)  -- mapsOn
    ∧ (∀ j ∈ (indxsK pr k), ∃ i, to_indxs i = j) -- surOn

omit [Fintype F] in
lemma h_combine_in_use {t n_p : ℕ}
      (f : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      -- For here, assumptions about the tuples of a specific partition
      (k : Fin (n_p + 1)) -- The partition
      {tuple_len : Nat} -- The length of the tuple - 1 for this partition.
      (tuples : Fin (indxsK pr k).length → Fin (tuple_len + 1) → F) -- The values of the partition (tuples)
      (use_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'use' values
      (to_all_indxs : Fin (indxsK pr k).length → Fin t) -- mapping into the set of all indexes
      (α : F)
      (h_combine_eq : ∀ i, combine α (tuples i) = f (to_all_indxs i)) :
    ∀ x, x ∈ Finset.image tuples use_i →
      combine α x ∈ Multiset.map (fin_map f (Finset.image to_all_indxs use_i).toList) Finset.univ.val := by
  intro x h_x
  rw [Multiset.mem_map]
  rw [Finset.mem_image] at h_x
  rcases h_x with ⟨i, h_i_use, h_i_eq⟩

  have h_use_indx : ∃ j, j ∈ ((Finset.image to_all_indxs use_i).toList) ∧ f j = combine α x := by
    use to_all_indxs i
    constructor
    · rw [Finset.mem_toList, Finset.mem_image]
      use i
    rw [←h_i_eq, h_combine_eq i]

  rw [List.exists_mem_iff_getElem] at h_use_indx
  rcases h_use_indx with ⟨j, h_j_lt, h_j_eq⟩
  simp only [Fin.exists_iff]
  use j, h_j_lt
  simp [Finset.mem_val, Finset.mem_univ, fin_map, ←h_j_eq]

omit [Fintype F] in
lemma h_combine_in_complement {t n_p : ℕ}
      (f : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      -- For here, assumptions about the tuples of a specific partition
      (k : Fin (n_p + 1)) -- The partition
      {tuple_len : Nat} -- The length of the tuple - 1 for this partition.
      (tuples : Fin (indxsK pr k).length → Fin (tuple_len + 1) → F) -- The values of the partition (tuples)
      (use_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'use' values
      (to_all_indxs : Fin (indxsK pr k).length → Fin t) -- mapping into the set of all indexes
      (h_surOn : to_indxs_surOn pr k to_all_indxs)
      (α : F)
      (h_combine_eq : ∀ i, combine α (tuples i) = f (to_all_indxs i)) :
    ∀ x, x ∈ Multiset.map (fin_map f ((indxsK pr ↑k).diff (Finset.image to_all_indxs use_i).toList)) Finset.univ.val →
      ∃ i, i ∉ use_i ∧ combine α (tuples i) = x := by
  intro x h_x
  simp only [Multiset.mem_map, fin_map] at h_x
  rcases h_x with ⟨i, _, h_i_eq⟩
  have h_subset : (indxsK pr k).diff (Finset.image to_all_indxs use_i).toList ⊆ indxsK pr k := List.diff_subset _ _
  have h_mem : (((indxsK pr ↑k).diff (Finset.image to_all_indxs use_i).toList).get i) ∈ (indxsK pr k) := by
    apply h_subset ; simp
  rcases h_surOn.2 _ h_mem with ⟨j, h_j⟩
  use j
  constructor
  · simp only [List.get_eq_getElem] at h_j
    replace h_j := List.mem_of_getElem h_j.symm
    rw [List.Nodup.mem_diff_iff (indxsK_nodup _ _)] at h_j
    rw [Finset.mem_toList] at h_j
    by_contra h_mem_use_i
    apply h_j.2
    rw [Finset.mem_image]
    use j
  rw [←h_i_eq, ←h_j]
  exact h_combine_eq j

lemma tuple_inclusion_of_not_in_bad_sets {t n_s n_p : ℕ}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      --(h_use_count_lt : ∀ k, max_count_F (useK m pr k f) < ringChar F)
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      -- For here, assumptions about the tuples of a specific partition
      (k : Fin (n_p + 1)) -- The partition
      {tuple_len : Nat} -- The length of the tuple - 1 for this partition.
      (tuples : Fin (indxsK pr k).length → Fin (tuple_len + 1) → F) -- The values of the partition (tuples)
      (use_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'use' values for the relation
      (yield_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'yield' values for the relation
      (h_use_i_lt : use_i.card < ringChar F)
      (to_all_indxs : Fin (indxsK pr k).length → Fin t) -- mapping into the set of all indexes
      (h_surOn : to_indxs_surOn pr k to_all_indxs)
      (h_use_mult_one : ∀ i, i ∈ use_i → m (to_all_indxs i) = 1)
      (α : F)
      (h_combine_eq : ∀ i, combine α (tuples i) = f (to_all_indxs i))
      (h_α : α ∉ badSet tuples use_i yield_i) :
    Finset.image tuples use_i ⊆ Finset.image tuples yield_i := by
  apply inclusion_of_not_badSet tuples use_i yield_i α _ h_α
  rw [Finset.subset_iff]
  intro x h_x
  rw [←Finset.image_image, Finset.mem_image] at h_x
  rcases h_x with ⟨i, h_i_mem, h_i_eq⟩
  have h_use := h_combine_in_use f pr k tuples use_i to_all_indxs α h_combine_eq i h_i_mem
  rw [h_i_eq] at h_use

  have h_use_i : Finset.image to_all_indxs use_i ⊆ (use_indxs m pr k).toFinset := by
    rw [Finset.subset_iff]
    intro x h_x
    rw [List.mem_toFinset, use_indxs, List.mem_filter]
    rw [Finset.mem_image] at h_x
    rcases h_x with ⟨i, h_i_mem, h_i_eq⟩
    rw [←h_i_eq]
    use h_surOn.1 i
    simp [h_use_mult_one i h_i_mem]

  have h_inclusion := inclusion_of_constraints_and_not_exceptionalSet'
                        f m s pr z psum h_cumulativeC h_cyclic k
                        (Finset.image to_all_indxs use_i) h_use_i (lt_of_le_of_lt Finset.card_image_le h_use_i_lt)
                        h_z
  rw [Multiset.subset_iff] at h_inclusion

  have h_yield := h_combine_in_complement
      f pr k tuples use_i to_all_indxs h_surOn α h_combine_eq
      x (h_inclusion h_use)

  rcases h_yield with ⟨j, h_j_nin, h_j_eq⟩
  simp only [Finset.mem_image, Finset.mem_sdiff]
  use j
  simp only [Finset.mem_univ, h_j_nin, ←h_j_eq, Function.comp_apply]
  simp

/-
  Chain lookup combine bad set

  Chain lookups add yields with a multiplicity of -1 to be able to deduce that
  for each tuple, its count in the use set is the same as its count in the
  yield set. This requires a different definition of the bad set for the
  combine function, as set inclusion of the use values in the yield values
  is not sufficient for this property.
-/

def set_count {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (subset : Finset (Fin l)) (t : Fin (n + 1) → F) : Nat :=
  Multiset.count t (Multiset.map tuples subset.val)
-- Set of use values which have a larger use count than a yield count.
def set_lt_set {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (set1 set2 : Finset (Fin l)) : Finset (Fin (n + 1) → F) :=
  Finset.univ.filter fun t => set_count tuples set1 t < set_count tuples set2 t
def yield_lt_use {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) : Finset (Fin (n + 1) → F) :=
  set_lt_set tuples yield_i use_i
  -- Finset.univ.filter fun t => set_count tuples yield_i t < set_count tuples use_i t
def use_lt_yield {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) : Finset (Fin (n + 1) → F) :=
  set_lt_set tuples use_i yield_i
  --Finset.univ.filter fun t => set_count tuples use_i t < set_count tuples yield_i t

def chainBadSet {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) : Finset F :=
  if ∀ t, set_count tuples use_i t = set_count tuples yield_i t
  then ∅
  else
    Finset.univ.filter fun α =>
      (∀ u, u ∈ yield_lt_use tuples use_i yield_i →
        ∃ y, y ∈ Finset.image tuples (Finset.univ \ use_i) ∧ u ≠ y ∧ combine α u = combine α y)
      ∧
      (∀ u, u ∈ use_lt_yield tuples use_i yield_i →
        ∃ y, y ∈ Finset.image tuples (Finset.univ \ yield_i) ∧ u ≠ y ∧ combine α u = combine α y)


/-
  Cardinality of the chain bad set
-/

lemma chainBadSet_symm {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (set1 set2 : Finset (Fin l)) :
    chainBadSet tuples set1 set2 = chainBadSet tuples set2 set1 := by
  by_cases h : ∀ t, set_count tuples set2 t = set_count tuples set1 t
  · have h' := h
    simp only [Eq.comm] at h
    simp only [chainBadSet, if_pos h, if_pos h']
  have h' := h
  simp only [Eq.comm] at h
  simp only [chainBadSet, if_neg h, if_neg h']
  simp only [yield_lt_use, use_lt_yield, And.comm]

lemma chainBadSet_subset_set_lt_set {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (set1 set2 : Finset (Fin l))
      (x : Fin (n + 1) → F)
      (h_x : x ∈ set_lt_set tuples set1 set2) :
    chainBadSet tuples set1 set2 ⊆ (Finset.image tuples (Finset.univ \ set2)).biUnion
      (fun y => Finset.univ.filter fun α => x ≠ y ∧ combine α x = combine α y) := by
  unfold chainBadSet
  by_cases h : ∀ t, set_count tuples set2 t ≤ set_count tuples set1 t
  · exfalso
    rw [set_lt_set, Finset.mem_filter] at h_x
    exact (lt_iff_not_ge.mp (LT.lt.gt h_x.2)) (h x)
  have h_ne : ¬∀ (t : Fin (n + 1) → F), set_count tuples set1 t = set_count tuples set2 t := by
    simp_all only [not_forall]
    rcases h with ⟨x, h_x⟩
    replace h_x := ne_of_not_le h_x
    exact ⟨x, h_x.symm⟩
  rw [if_neg h_ne, Finset.subset_iff]
  simp only [Finset.mem_filter]
  rintro α ⟨h_α_mem, h_α⟩
  rw [Finset.mem_biUnion]
  rcases h_α.2 x h_x with ⟨y, h_y_in, h_y_eq⟩
  use y, h_y_in
  rw [Finset.mem_filter]
  exact ⟨h_α_mem, h_y_eq.1, h_y_eq.2⟩

lemma mem_collision_card {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (use_i : Finset (Fin l))
      (x : Fin (n + 1) → F) :
    ∀ y ∈ Finset.image tuples (Finset.univ \ use_i),
      (Finset.univ.filter fun α => x ≠ y ∧ combine α x = combine α y).card ≤ n := by
  intro y h_y
  by_cases h : x = y
  · simp [h]
  simp [h]
  apply pair_collision_card _ _ h

lemma card_chainBadSet_le_of_set_count_lt {n l: Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (set1 set2 : Finset (Fin l))
      (x : Fin (n + 1) → F)
      (h_lt : set_count tuples set1 x < set_count tuples set2 x):
    (chainBadSet tuples set1 set2).card ≤ (Finset.univ \ set2).card * n := by
  have h_mem_lt : x ∈ set_lt_set tuples set1 set2 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_lt⟩
  apply le_trans (Finset.card_le_card (chainBadSet_subset_set_lt_set tuples set1 set2 x h_mem_lt))
  apply le_trans (Finset.card_biUnion_le_card_mul _ _ _ (mem_collision_card tuples set2 x))
  apply mul_le_mul_right'
  apply le_trans Finset.card_image_le
  simp only [le_refl]

lemma card_chainBadSet_le_max {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) :
    (chainBadSet tuples use_i yield_i).card ≤ (max (Finset.univ \ use_i).card (Finset.univ \ yield_i).card) * n := by
  unfold chainBadSet
  by_cases h : ∀ t, set_count tuples use_i t = set_count tuples yield_i t
  · rw [if_pos h, Finset.card_empty] ; apply Nat.zero_le
  simp only [Classical.not_forall] at h
  rcases h with ⟨x, h_x⟩
  cases lt_or_gt_of_ne h_x
  case neg.intro.inl h_lt =>
    apply le_trans (card_chainBadSet_le_of_set_count_lt tuples use_i yield_i x h_lt)
    apply mul_le_mul_right'
    simp only [le_sup_right]
  case neg.intro.inr h_lt =>
    have h_le_union := card_chainBadSet_le_of_set_count_lt tuples yield_i use_i x h_lt
    simp only [chainBadSet_symm] at h_le_union
    apply le_trans h_le_union
    apply mul_le_mul_right'
    simp only [le_sup_left]

lemma card_chainBadSet_le {n l: Nat} (tuples : Fin l → (Fin (n + 1) → F)) (use_i : Finset (Fin l)) (yield_i : Finset (Fin l)) :
    (chainBadSet tuples use_i yield_i).card ≤ l * n := by
  apply le_trans (card_chainBadSet_le_max tuples use_i yield_i)
  apply mul_le_mul_right'
  simp [Finset.card_sdiff]

/-
  Equal counts when α is not in the bad set.
-/

omit [Fintype F] in
lemma exists_of_set_count_lt_set_count {n l : Nat}
      (tuples : Fin l → (Fin (n + 1) → F))
      (set1 set2 : Finset (Fin l))
      --(univ_set : Finset (Fin l)) -- All use values in the partition.
      --(h_set1 : set1 ⊆ univ_set)
      (h_set2 : set2 ⊆ Finset.univ \ set1)
      (α : F)
      (x : Fin (n + 1) → F)
      (h_count: Multiset.count (combine α x) (Multiset.map (combine α ∘ tuples) set1.val) =
        Multiset.count (combine α x) (Multiset.map (combine α ∘ tuples) set2.val)) :
    set_count tuples set2 x < set_count tuples set1 x →
      ∃ y ∈ Finset.image tuples (Finset.univ \ set1), x ≠ y ∧ combine α x = combine α y := by
  intro h_x
  rw [←Multiset.filter_add_not ((fun t => t = x) ∘ tuples) set2.val] at h_count
  rw [←Multiset.filter_add_not ((fun t => t = x) ∘ tuples) set1.val] at h_count
  simp only [Multiset.map_add, Multiset.count_add] at h_count
  simp only [←Multiset.map_map, ←Multiset.filter_map, Multiset.filter_eq', Multiset.map_replicate] at h_count
  simp only [Multiset.count_replicate_self] at h_count
  have h {a b c d : Nat} : a + b = c + d → c < a → b < d := by intro h_eq h_lt ; linarith
  have h_ne_zero := (Nat.ne_of_lt (Nat.zero_lt_of_lt (h h_count h_x))).symm
  rw [Multiset.count_ne_zero, Multiset.mem_map] at h_ne_zero
  rcases h_ne_zero with ⟨y, h_mem, h_eq⟩
  rw [Multiset.mem_map] at h_mem
  simp only [Multiset.mem_filter, Finset.mem_val] at h_mem
  rcases h_mem with ⟨i, ⟨h_i_mem, h_i_ne⟩, h_i_eq⟩
  simp [h_i_eq, ←ne_eq] at h_i_ne
  simp only [Finset.mem_image]
  replace h_i_mem : i ∈ Finset.univ \ set1 := by
    apply Finset.mem_of_subset _ h_i_mem
    --trans Finset.univ \ univ_set
    exact h_set2
    --exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h_set1
  exact ⟨y, ⟨i, h_i_mem, h_i_eq⟩, h_i_ne.symm, h_eq.symm⟩

lemma map_toList_eq_image {α : Type u_1} {β : Type u_2} [DecidableEq β]
      (s t : Finset α)
      {f : α → β}
      (h_sub : s ⊆ t)
      (h_inj : ((fun (i : {i // i ∈ t}) => f i).Injective)) :
    Multiset.map f s.toList = ↑(Finset.image f s).toList := by
  have h_inj_on : ∀ x ∈ s.val, ∀ y ∈ s.val, f x = f y → x = y := by
    intro x hx y hy hxy
    have hx' : x ∈ t := h_sub hx
    have hy' : y ∈ t := h_sub hy
    have hxy' : (fun i : {i // i ∈ t} => f i) ⟨x, hx'⟩ = (fun i : {i // i ∈ t} => f i) ⟨y, hy'⟩ := by
      simpa using hxy
    exact congrArg Subtype.val (h_inj hxy')
  have h_nodup : Multiset.Nodup (Multiset.map f s.val) := s.nodup.map_on h_inj_on
  have h_dedup : (Multiset.map f s.val).dedup = Multiset.map f s.val := h_nodup.dedup
  simp [Finset.coe_toList, Finset.image_val, h_dedup]

theorem equal_count_image_of_multiplicity_one {t n_s n_p : ℕ} [Fact (2 < ringChar F)]
      {f m : Fin t → F}
      {s : Fin t → Fin (n_s + 1)}
      {pr : Fin t → Fin (n_p + 1)}
      {z : Fin (n_p + 1) → F}
      {psum : Nat → F}
      {k : Fin (n_p + 1)}
      (use_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'use' values for the relation
      (yield_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'yield' values for the relation
      (h_use_i_lt : use_i.card < ringChar F)
      (h_yield_i_lt : yield_i.card < ringChar F)
      {to_all_indxs : Fin (indxsK pr k).length → Fin t} -- mapping into the set of all indexes
      (h_surOn : to_indxs_surOn pr k to_all_indxs)
      (h_use_mult_one : ∀ i, i ∈ use_i → m (to_all_indxs i) = 1)
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      (h_inj : (fun (i : {i // i ∈ use_i ∪ yield_i}) => to_all_indxs i).Injective)

      (h_y : ∀ i ∈ yield_i, m (to_all_indxs i) = -1)
      (x : F) :
    (∀ j ∈ (indxsK pr k).toFinset \ ((Finset.image to_all_indxs use_i) ∪ (Finset.image to_all_indxs yield_i)), x ≠ f j) →
      Multiset.count x (yield_i.toList.map fun i => f (to_all_indxs i)) =
        Multiset.count x (use_i.toList.map (fun i => f (to_all_indxs i))) := by
  intro h_disjoint
  have h_use_i : Finset.image to_all_indxs use_i ⊆ (use_indxs m pr k).toFinset := by
    rw [Finset.subset_iff]
    intro i h_i_mem
    rw [List.mem_toFinset, use_indxs, List.mem_filter]
    rcases Finset.mem_image.mp h_i_mem with ⟨i', h_i'_mem, h_i'_eq⟩
    rw [←h_i'_eq]
    use h_surOn.1 i'
    exact decide_eq_true (h_use_mult_one i' h_i'_mem)
  have h_yield_i : Finset.image to_all_indxs yield_i ⊆ (yield_indxs m pr k).toFinset := by
    rw [Finset.subset_iff]
    intro i h_i_mem
    rw [List.mem_toFinset, yield_indxs, List.mem_filter]
    rcases Finset.mem_image.mp h_i_mem with ⟨i', h_i'_mem, h_i'_eq⟩
    rw [←h_i'_eq]
    use h_surOn.1 i'
    apply decide_eq_true
    rw [h_y i' h_i'_mem]
    apply CharP.neg_one_ne_one

  have h_use_count_lt : (Finset.image to_all_indxs use_i).card < ringChar F := by
    apply lt_of_le_of_lt Finset.card_image_le h_use_i_lt
  have h_yield_count_lt : (Finset.image to_all_indxs yield_i).card < ringChar F := by
    apply lt_of_le_of_lt Finset.card_image_le h_yield_i_lt

  have h_m : (∀ i ∈ Finset.image to_all_indxs yield_i, m i = -1) := by
    intro i h_i_mem
    rw [Finset.mem_image] at h_i_mem
    rcases h_i_mem with ⟨x, h_x_mem, h_x_eq⟩
    rw [←h_x_eq]
    exact h_y x h_x_mem

  simp only [←Function.comp_def, ←List.map_map, ←Multiset.map_coe]
  simp only [
    map_toList_eq_image use_i _ Finset.subset_union_left h_inj,
    map_toList_eq_image yield_i _ Finset.subset_union_right h_inj]
  exact equal_count_of_multiplicity_one'' k _ _ h_use_i h_yield_i h_use_count_lt h_yield_count_lt h_z h_cumulativeC h_cyclic h_m h_disjoint

omit [Fintype F] in
lemma map_combine_tuples_eq {l : ℕ} {tuple_len : Nat} {tuples : Fin l → Fin (tuple_len + 1) → F} {s : Finset (Fin l)} {α : F} :
    (Multiset.map (fun i => combine α (tuples i)) ↑s.toList) = (Multiset.map (combine α ∘ tuples) s.val) := by simp

lemma exists_collision_of_count_lt {t n_p : ℕ}
      {f : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)} -- The partition
      {tuple_len : Nat} -- The length of the tuple - 1 for this partition.
      {tuples : Fin (indxsK pr k).length → Fin (tuple_len + 1) → F} -- The values of the partition (tuples)
      (set1 set2 : Finset (Fin (indxsK pr k).length))
      (h_disjoint : ∀ i ∈ set1 ∪ set2, ∀ j ∉ set1 ∪ set2, tuples i ≠ tuples j)
      (h_subset : set2 ⊆ Finset.univ \ set1)
      {to_all_indxs : Fin (indxsK pr k).length → Fin t} -- mapping into the set of all indexes
      (h_surOn : to_indxs_surOn pr k to_all_indxs)
      {α : F}
      (h_combine_eq : ∀ i, combine α (tuples i) = f (to_all_indxs i))
      {u : Fin (tuple_len + 1) → F}
      (h_count :
          (∀ j ∈ (indxsK pr k).toFinset \ ((Finset.image to_all_indxs set1) ∪ (Finset.image to_all_indxs set2)), combine α u ≠ f j) →
              (Multiset.count (combine α u) (set2.toList.map fun i => f (to_all_indxs i))) =
                Multiset.count (combine α u) (set1.toList.map (fun i => f (to_all_indxs i)))) :
    u ∈ set_lt_set tuples set2 set1 →
      ∃ y ∈ Finset.image tuples (Finset.univ \ set1), u ≠ y ∧ combine α u = combine α y := by
  intro h_u_mem
  simp only [set_lt_set, Finset.mem_filter] at h_u_mem
  have h_u_tuple_of_mem : ∃ i ∈ set1, u = tuples i := by
    have h := Multiset.mem_map.mp (Multiset.count_pos.mp (Nat.zero_lt_of_lt h_u_mem.2))
    simp only [eq_comm, Finset.mem_val] at h
    exact h
  by_contra h_no_y
  by_cases h_t_disjoint : ∀ j ∈ (indxsK pr k).toFinset \ ((Finset.image to_all_indxs set1) ∪ (Finset.image to_all_indxs set2)), combine α u ≠ f j
  · replace h_count := h_count h_t_disjoint
    simp only [←h_combine_eq, ←Multiset.map_coe] at h_count
    rw [map_combine_tuples_eq, map_combine_tuples_eq, Eq.comm] at h_count
    apply h_no_y
    exact exists_of_set_count_lt_set_count tuples set1 set2 h_subset α u h_count h_u_mem.2
  apply h_no_y
  rw [Classical.not_forall] at h_t_disjoint
  rcases h_t_disjoint with ⟨i, h_i⟩
  rw [Classical.not_imp, not_ne_iff] at h_i
  rcases h_surOn.2 i (List.mem_toFinset.mp (Finset.mem_sdiff.mp h_i.1).1) with ⟨i', h_i'⟩
  have h_i'_nin : i' ∉ set1 ∪ set2 := by
    rw [Finset.mem_sdiff] at h_i
    have h_mem := h_i.1.2
    simp only [←Finset.image_union, Finset.mem_image, not_exists, not_and'] at h_mem
    exact h_mem i' h_i'
  use tuples i'
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mem_image]
    use i'
    simp [Finset.mem_sdiff, (Finset.notMem_union.mp h_i'_nin).1]
  · rcases h_u_tuple_of_mem with ⟨u_i, h_u_i_mem, h_u_i_eq⟩
    rw [h_u_i_eq]
    apply h_disjoint _ (Finset.mem_union_left _ h_u_i_mem) _ h_i'_nin
  rw [h_combine_eq, h_i', h_i.2]

theorem equal_count_tuples_of_multiplicity_one [Fact (2 < ringChar F)] {t n_s n_p : ℕ}
      {f m : Fin t → F}
      {s : Fin t → Fin (n_s + 1)}
      {pr : Fin t → Fin (n_p + 1)}
      {z : Fin (n_p + 1) → F}
      {psum : Nat → F}
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      {k : Fin (n_p + 1)} -- The partition
      {tuple_len : Nat} -- The length of the tuple - 1 for this partition.
      {tuples : Fin (indxsK pr k).length → Fin (tuple_len + 1) → F} -- The values of the partition (tuples)
      (use_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'use' values for the relation
      (yield_i : Finset (Fin (indxsK pr k).length)) -- a subset of the tuples are 'yield' values for the relation
      (h_use_i_lt : use_i.card < ringChar F)
      (h_yield_i_lt : yield_i.card < ringChar F)
      (h_disjoint : ∀ i ∈ use_i ∪ yield_i, ∀ j ∉ use_i ∪ yield_i, tuples i ≠ tuples j)
      {to_all_indxs : Fin (indxsK pr k).length → Fin t} -- mapping into the set of all indexes
      (h_surOn : to_indxs_surOn pr k to_all_indxs)
      (h_use_mult_one : ∀ i, i ∈ use_i → m (to_all_indxs i) = 1)
      (h_inj : (fun (i : {i // i ∈ use_i ∪ yield_i}) => to_all_indxs i).Injective)
      (h_y : ∀ i ∈ yield_i, m (to_all_indxs i) = -1)
      {α : F}
      (h_combine_eq : ∀ i, combine α (tuples i) = f (to_all_indxs i))
      (h_α : α ∉ chainBadSet tuples use_i yield_i) :
    ∀ t, set_count tuples use_i t = set_count tuples yield_i t := by

  have h_yield_subset : yield_i ⊆ Finset.univ \ use_i := by
    simp [Finset.subset_sdiff, Finset.disjoint_iff_ne]
    intro i h_i
    apply not_imp_not.mpr (h_use_mult_one i)
    rw [h_y i h_i, ←ne_eq]
    apply CharP.neg_one_ne_one
  have h_use_subset : use_i ⊆ Finset.univ \ yield_i := by
    simp [Finset.subset_sdiff, Finset.disjoint_iff_ne]
    intro i h_i
    apply not_imp_not.mpr (h_y i)
    rw [h_use_mult_one i h_i, eq_comm, ←ne_eq]
    apply CharP.neg_one_ne_one
  by_contra h
  simp only [chainBadSet, if_neg h] at h_α
  apply h_α
  simp only [Finset.mem_filter, Finset.mem_univ α, true_and]
  have h_counts := equal_count_image_of_multiplicity_one
                      use_i yield_i h_use_i_lt h_yield_i_lt h_surOn h_use_mult_one h_z h_cumulativeC h_cyclic h_inj h_y
  constructor
  · intro u
    exact exists_collision_of_count_lt use_i yield_i h_disjoint h_yield_subset h_surOn h_combine_eq (h_counts (combine α u))
  intro u
  rw [Finset.union_comm] at h_disjoint
  replace h_counts := (h_counts (combine α u))
  rw [Finset.union_comm, eq_comm] at h_counts
  exact exists_collision_of_count_lt yield_i use_i h_disjoint h_use_subset h_surOn h_combine_eq h_counts
