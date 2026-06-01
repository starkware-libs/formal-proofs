import Verification.Semantics.Util
import Verification.Lookups.poles
import Mathlib.Data.Fin.SuccPred

noncomputable section
open scoped Classical BigOperators

open Polynomial

variable {F : Type _} [Field F] [Fintype F]

/-
  # The constraints as polynomials
-/

/-
  We consider all use and yield values to be provided as a single indexed list
  Fin t → F. A 'step' function s : Fin t → Fin n defines for each
  value in the indexed list the step in which it is added to the constraints.
  Each step adds a single constraint. Multiple values may be added
  in single constraint (and this number may, in principle, be zero, though
  this is not useful in practice).
  Similarly, a partition function pr : Fin t → Fin l indicates for each
  value which partition it belongs to.
-/

-- The indexes in the full list of values which belong to the k'th set.
def indxsK {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) :=
  ((Fin.fintype t).elems.toList.filter (fun i => s i = k))

lemma indxsK_nodup {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) : (indxsK s k).Nodup := by
  apply List.Nodup.filter ; apply Finset.nodup_toList

-- The indexes in the full list of values up to (and including) set k.
def cumIndxs {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) :=
  (Fin.fintype t).elems.toList.filter (fun i => s i ≤ k)

lemma cumIndxs_zero {t n_s : Nat} (s : Fin t → Fin n_s) : cumIndxs s 0 = indxsK s 0 := by
  unfold cumIndxs indxsK ; simp only [Nat.le_zero]

lemma cumIndxs_all {t n_s : Nat} (s : Fin t → Fin n_s) (h_zero_ls_n_s : 0 < n_s) :
    cumIndxs s (n_s - 1) = (Fin.fintype t).elems.toList := by
  unfold cumIndxs
  simp only [List.filter_eq_self]
  intro x _
  simp only [Nat.sub_one, Nat.le_pred_iff_lt h_zero_ls_n_s, Fin.is_lt]
  simp only [decide_true]

lemma cumIndxs_append {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (h_k : 0 < k):
    ((cumIndxs s (k - 1)) ++ (indxsK s k)).Perm (cumIndxs s k) := by
  unfold cumIndxs indxsK
  have h_eq : (fun i => decide (s i = k)) = (fun i => decide (¬ s i ≤ k - 1 ∧ s i ≤ k)) := by
    apply @_root_.funext ; intro i ; congr ; rw [and_comm, ←Nat.lt_iff_le_pred h_k, ←iff_iff_eq] ; exact eq_iff_le_not_lt
  have h_le : (fun i => decide (s i ≤ k - 1)) = (fun i => decide (s i ≤ k - 1 ∧ s i ≤ k)) := by
    apply @_root_.funext ; intro i ; congr ; rw [←iff_iff_eq, and_comm] ; apply iff_and_self.mpr
    intro h ; apply le_trans h ; exact Nat.sub_le k 1
  simp only [h_eq, h_le, Bool.decide_and, decide_not]
  simp only [←List.filter_filter]
  apply List.filter_append_perm

lemma sum_indxs_len {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) :
    (cumIndxs s k).length = ∑ l : Fin (k + 1), (indxsK s l).length := by
  induction k with
  | zero =>
    simp ; rw [cumIndxs_zero]
  | succ l h_ind =>
    rw [←Finset.sum_range (fun l => (indxsK s l).length), Finset.sum_range_succ]
    rw [Finset.sum_range (fun l => (indxsK s l).length), ←h_ind]
    rw [←List.length_append]
    have h_append := List.Perm.length_eq (cumIndxs_append s (l + 1) (Nat.zero_lt_succ l))
    rw [Nat.add_sub_cancel] at h_append
    rw [h_append]

lemma sum_indxs_len' {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (h_k : 0 < k) :
    (cumIndxs s (k - 1)).length = ∑ l : Fin k, (indxsK s l).length := by
  let k' := k - 1
  have h : k = k' + 1 := by rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt h_k)]
  rw [h, Nat.add_sub_cancel]
  exact sum_indxs_len s k'

lemma sum_all_indxs_len {t n_s : Nat} (s : Fin t → Fin n_s) (h_zero_ls_n_s : 0 < n_s) :
    ∑ l : Fin n_s, (indxsK s l).length = t := by
  rw [←sum_indxs_len' s n_s h_zero_ls_n_s]
  rw [cumIndxs_all s h_zero_ls_n_s]
  rw [Finset.length_toList]
  rw [←Finset.univ, ←Fintype.card, Fintype.card_fin t]

-- The i'th index in the partition s
def idxK {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) :=
  fun i : Fin (indxsK s k).length => (indxsK s k).get i

-- The restriction of a function to the indexes in the k'th set.
def funK {α : Type _ } {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (f : Fin t → α) :=
  fun i : Fin (indxsK s k).length => f ((indxsK s k).get i)

-- The restriction of a function to the indexes up to (and including) the k'th set.
def funCumK {α : Type _ } {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (f : Fin t → α) :=
  fun i : Fin (cumIndxs s k).length => f ((cumIndxs s k).get i)

def cumIndxs_zero_sum {α : Type _ } [AddCommMonoid α] {t n_s : Nat} (s : Fin t → Fin n_s) (f : Fin t → α) :
    ∑ i, (funCumK s 0 f) i = ∑ i, (funK s 0 f) i := by
  unfold funCumK funK ; rw [cumIndxs_zero]

lemma cumIndxs_append_sum {α : Type _ } [AddCommMonoid α] {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (h_k : 0 < k) (f : Fin t → α) :
    ∑ i, (funCumK s k f) i = ∑ i, (funCumK s (k - 1) f) i + ∑ i, (funK s k f) i := by
  unfold funCumK funK
  simp only [←List.sum_ofFn] ; simp only [List.get_eq_getElem, List.ofFn_getElem_eq_map]
  simp [←List.Perm.sum_eq (List.Perm.map f (cumIndxs_append s k h_k))]

lemma cumIndxs_sum {α : Type _ } [AddCommMonoid α] {t n_s : Nat} (s : Fin t → Fin n_s) (k : Nat) (f : Fin t → α) :
    ∑ i, (funCumK s k f) i = ∑ l : Fin (k + 1), ∑ i, (funK s l f) i := by
  induction k with
  | zero =>
    simp ; rw [cumIndxs_zero_sum]
  | succ l h_ind =>
    rw [←Finset.sum_range (fun l => ∑ i, (funK s l f) i), Finset.sum_range_succ]
    rw [Finset.sum_range (fun l => ∑ i, (funK s l f) i), ←h_ind]
    apply cumIndxs_append_sum _ _ (Nat.zero_lt_succ l)

def prodZ {n :Nat} (f z : Fin n → F) : F := ((Fin.fintype n).elems.val.map fun j => z j - f j).prod
def prodZ_exc {n : Nat} (f z : Fin n → F) (k : Fin n) : F :=
  (((Fin.fintype n).elems.val.erase k).map fun j => z j - f j).prod

omit [Fintype F] in
lemma prod_ne_zero {α : Type _} {m : Multiset α} (f z : α → F) (h : ∀ j, f j ≠ z j) :
    (m.map fun j => z j - f j).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  by_contra h_mem
  simp only [Multiset.mem_map, sub_eq_zero, Eq.comm] at h_mem
  rcases h_mem with ⟨a, h_a⟩
  exact (h a) h_a.2

omit [Fintype F] in
lemma prodZ_ne_zero {n :Nat} (f z : Fin n → F) (h : ∀ j, f j ≠ z j) : prodZ f z ≠ 0 :=
  prod_ne_zero f z h

omit [Fintype F] in
lemma prodZ_exc_ne_zero {n :Nat} (f z : Fin n → F) (k : Fin n) (h : ∀ j, f j ≠ z j) : prodZ_exc f z k ≠ 0 :=
  prod_ne_zero f z h

omit [Fintype F] in
lemma prodZ_exc_eq_prod_div {n : Nat} (f m z : Fin n → F) (h : ∀ j, f j ≠ z j) (i : Fin n) :
    prodZ f z * (m i / (z i - f i)) = (m i) * prodZ_exc f z i := by
  unfold prodZ prodZ_exc
  have h_i : i ∈ (Fin.fintype n).elems.val := Finset.mem_univ_val i
  rw [←Multiset.prod_map_erase h_i]
  rw [mul_comm (z i - f i), mul_assoc]
  rw [mul_div_cancel₀, mul_comm]
  rw [ne_eq, sub_eq_zero]
  apply (h i).symm

omit [Fintype F] in
lemma prodZ_eq_iff_frac_sum_eq {n : Nat} (f m z : Fin n → F) (h : ∀ j, f j ≠ z j) (psum : F) :
    ∑ j : Fin n, (m j) * (prodZ_exc f z j) = (prodZ f z) * psum ↔
      ∑ j : Fin n, (m j) / (z j - f j) = psum := by
  conv_rhs => rw [←mul_right_inj' (prodZ_ne_zero f z h), Finset.mul_sum]
  apply eq_iff_eq_cancel_right.mpr
  congr ; apply @_root_.funext ; intro j
  rw [prodZ_exc_eq_prod_div f m z h j]

/-
  The cumulative constraint:
    f: the use and yield values
    m: multiplicities, assumed 1 for use values and -multiplicity for yield values (≠ 1 if the field is large enough).
    s: defines the step in which each value is added to the constraints.
    pr: defines the partition to which each value belongs
    psum: the sum of fractions added up to step k.
    z: the random values used in the fractions. This is composed with pr, so the same z value is assigned to
       all values of the same partition.
-/

-- The k'th constraint
def cumulativeC_k {t n_s n_p : Nat} (f m : Fin t → F) (s : Fin t → Fin n_s) (pr : Fin t → Fin n_p) (psum : Nat → F) (z : Fin n_p → F) (k : Nat) :=
    let f_k := funK s k f
    let z_k := funK s k (z ∘ pr)
    let m_k := funK s k m
    ∑ j : Fin (indxsK s k).length, (m_k j) * (prodZ_exc f_k z_k j) = (prodZ f_k z_k) * (psum k.succ - psum k)

omit [Fintype F] in
lemma funCumK_frac {t n_s n_p : Nat} (f m : Fin t → F) (s : Fin t → Fin n_s) (pr : Fin t → Fin n_p) (z : Fin n_p → F) (k : Nat):
    (fun j => (funCumK s k m j) / (funCumK s k (z ∘ pr) j - funCumK s k f j)) =
      funCumK s k (fun j => (m j) / ((z ∘ pr) j - f j)) := by rfl

omit [Fintype F] in
lemma funK_frac {t n_s n_p : Nat} (f m : Fin t → F) (s : Fin t → Fin n_s) (pr : Fin t → Fin n_p) (z : Fin n_p → F) (k : Nat):
    (fun j => (funK s k m j) / (funK s k (z ∘ pr) j - funK s k f j)) =
      funK s k (fun j => (m j) / ((z ∘ pr) j - f j)) := by rfl

omit [Fintype F] in
lemma constraint_as_frac {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin n_s)
      (pr : Fin t → Fin n_p)
      (z : Fin n_p → F)
      (psum : Nat → F)
      (k : Nat)
      (h : ∀ (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j) :
    let f_k := funK s k f
    let z_k := funK s k (z ∘ pr)
    let m_k := funK s k m
    cumulativeC_k f m s pr psum z k ↔
      ∑ j : Fin (indxsK s k).length, (m_k j) / (z_k j - f_k j) = (psum k.succ - psum k) := by
  apply prodZ_eq_iff_frac_sum_eq (h := h)

omit [Fintype F] in
lemma frac_sum_of_constraints_to_k {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (k : Nat)
      (h : ∀ l ≤ k, ∀ (j : Fin (indxsK s l).length), funK s l f j ≠ funK s l (z ∘ pr) j)
      (h_cumulative_k : ∀ i, i ≤ k → cumulativeC_k f m s pr psum z i) :
    let f_k := funCumK s k f
    let z_k := funCumK s k (z ∘ pr)
    let m_k := funCumK s k m
    ∑ j : Fin (cumIndxs s k).length, (m_k j) / (z_k j - f_k j) = (psum k.succ - psum 0) := by
    induction k with
  | zero =>
      unfold funCumK ; rw [cumIndxs_zero]
      apply (constraint_as_frac f m s pr z psum 0 (h 0 (le_refl 0))).mp (h_cumulative_k 0 (le_refl 0))
  | succ l h_ind =>
      simp only [←Nat.lt_succ_iff] at h_ind h_cumulative_k h
      rw [Nat.forall_lt_succ] at h_cumulative_k h
      replace h_ind := h_ind h.1
      simp only [funCumK_frac]
      rw [cumIndxs_append_sum s (l + 1) (Nat.zero_lt_succ l)]
      simp only [Nat.add_one_sub_one]
      rw [←funCumK_frac, h_ind h_cumulative_k.1, ← funK_frac]
      have h_cum_last := (constraint_as_frac f m s pr z psum (l + 1) h.2).mp h_cumulative_k.2
      rw [h_cum_last]
      simp

omit [Fintype F] in
lemma frac_sum_of_constraints_fin_k {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (h : ∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j)
      (h_cumulative_k : ∀ (k : Fin (n_s + 1)), cumulativeC_k f m s pr psum z k) :
    let f_s := funCumK s n_s f
    let z_s := funCumK s n_s (z ∘ pr)
    let m_s := funCumK s n_s m
      ∑ j : Fin (cumIndxs s n_s).length, (m_s j) / (z_s j - f_s j) = (psum n_s.succ - psum 0) := by
  rw [Fin.forall_iff] at h h_cumulative_k ; simp only [Nat.lt_succ] at h h_cumulative_k
  apply frac_sum_of_constraints_to_k f m s pr z psum n_s h h_cumulative_k

-- All constraints

omit [Fintype F] in
lemma sum_all_fracs_cum {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    let f_s := funCumK s n_s f;
    let z_s := funCumK s n_s (z ∘ pr);
    let m_s := funCumK s n_s m;
    ∑ j : Fin (cumIndxs s n_s).length, m_s j / (z_s j - f_s j) =
      ∑ k : Fin (n_s + 1), ∑ j : Fin (indxsK s k).length, funK s k m j / (funK s k (z ∘ pr) j - funK s k f j) := by
  simp only [funCumK_frac f m s pr z, funK_frac f m s pr z]
  apply cumIndxs_sum

omit [Fintype F] in
lemma sum_all_fracs {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    let f_s := funCumK s n_s f;
    let z_s := funCumK s n_s (z ∘ pr);
    let m_s := funCumK s n_s m;
    ∑ j : Fin (cumIndxs s n_s).length, m_s j / (z_s j - f_s j) = ∑ j, (m j) / ((z ∘ pr) j - f j) := by
  simp only [funCumK_frac]
  have h_list_sum : Finset.univ.sum (funCumK s n_s fun j => m j / ((z ∘ pr) j - f j)) =
      (List.map (fun j => m j / ((z ∘ pr) j - f j)) Fintype.elems.toList).sum := by
    have h_true : (fun i => decide (↑(s i) ≤ n_s)) = fun _ => true := by
      apply @_root_.funext ; intro i ; apply decide_eq_true ; apply Fin.is_le
    unfold funCumK cumIndxs ; simp only [List.get_eq_getElem]
    rw [h_true, List.filter_true]
    rw [Fin.sum_univ_fun_getElem Fintype.elems.toList (fun j => m j / ((z ∘ pr) j - f j))]
  rw [h_list_sum]
  have h_sum : ∑ j, (m j) / ((z ∘ pr) j - f j) = ((Fin.fintype t).elems.toList.map (fun j => (m j) / ((z ∘ pr) j - f j))).sum := by
    simp ; rfl
  rw [←h_sum]

def cumulativeC {t n_s n_p : Nat}
    (f m : Fin t → F)
    (s : Fin t → Fin (n_s + 1))
    (pr : Fin t → Fin (n_p + 1))
    (z : Fin (n_p + 1) → F)
    (psum : Nat → F) :=
  ∀ k : Fin (n_s + 1), cumulativeC_k f m s pr psum z k

omit [Fintype F] in
lemma sum_zero_of_constraits {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (h : ∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0) :
    ∑ j, (m j) / ((z ∘ pr) j - f j) = 0 := by
  rw [←sum_all_fracs f m s pr z]
  rw [frac_sum_of_constraints_fin_k f m s pr z psum h h_cumulativeC]
  rw [h_cyclic] ; simp

/-
  Collisions between f and z
-/

omit [Field F] [Fintype F] in
lemma forall_r_z {t n_p : Nat}
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (k : Fin (n_p + 1)) :
    ∀ j, funK pr k (z ∘ pr) j = z k := by
  unfold funK indxsK
  simp only [Fin.forall_iff, List.get_eq_getElem]
  rw [←List.forall_mem_iff_getElem (p := fun x => (z ∘ pr) x = z k)]
  intro x h_x
  rw [List.mem_filter, Bool.decide_iff] at h_x
  rw [Function.comp_apply] ; congr
  apply Fin.eq_of_val_eq h_x.2

omit [Field F] [Fintype F] in
lemma forall_indxsK_ne_iff {t n_s : Nat}
      (f g : Fin t → F)
      (s : Fin t → Fin (n_s + 1)) :
    (∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k g j) ↔
      (∀ (j : Fin t), f j ≠ g j) := by
  unfold funK indxsK
  constructor
  · intro h j
    have h_in : ∀ j : Fin t, j ∈ List.filter (fun i => decide ((s i).val = (s j).val)) Fintype.elems.toList := by
      intro j ; rw [List.mem_filter, Finset.mem_toList] ; use (Fintype.complete j) ; simp
    rcases List.mem_iff_get.mp (h_in j) with ⟨i, h_i⟩
    replace h := h (s j) i
    rwa [h_i] at h
  intro h k j
  exact h ((List.filter (fun i => decide ((s i).val = k.val)) Fintype.elems.toList).get j)

omit [Field F] [Fintype F] in
lemma forall_no_z_collisions_comp {t n_s n_p : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    (∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j) ↔
      (∀ (j : Fin t), f j ≠ (z ∘ pr) j) := by
  apply forall_indxsK_ne_iff f (z ∘ pr) s

omit [Field F] [Fintype F] in
lemma forall_no_z_collisions {t n_s n_p : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    (∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j) ↔
      ∀ k j, ¬ (z k = funK pr k f j) := by
  simp only [forall_no_z_collisions_comp f s pr z, ←ne_eq]
  have h_r_z : (∀ (k : Fin (n_p + 1)) (j : Fin (indxsK pr ↑k).length), z k ≠ funK pr ↑k f j) ↔
      ∀ (k : Fin (n_p + 1)) (j : Fin (indxsK pr ↑k).length), funK pr k (z ∘ pr) j ≠ funK pr (↑k) f j := by
    simp only [forall_r_z]
  rw [h_r_z]
  rw [forall_indxsK_ne_iff (z ∘ pr) f pr]
  simp only [ne_comm]

omit [Field F] [Fintype F] in
lemma exists_no_z_collisions {t n_s n_p : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    (∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s k).length), funK s k f j ≠ funK s k (z ∘ pr) j) ↔
      ¬ ∃ k j, z k = funK pr k f j := by
  simp only [not_exists]
  apply forall_no_z_collisions

/-
  Fraction sums
-/

omit [Fintype F] in
lemma sum_all_fracs_cum_by_rel {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F) :
    let f_r := funCumK pr n_p f;
    let z_r := funCumK pr n_p (z ∘ pr);
    let m_r := funCumK pr n_p m;
    ∑ j : Fin (cumIndxs pr n_p).length, m_r j / (z_r j - f_r j) =
      ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, funK pr k m j / (z k - funK pr k f j) := by
  simp only [funCumK_frac f m pr pr z]
  have h_r_z : ∀ (k : Fin (n_p + 1)) (j : Fin (indxsK pr ↑k).length),
      funK pr k m j / (z k - funK pr k f j) = funK pr k m j / (funK pr k (z ∘ pr) j - funK pr k f j) := by
    intro k j ; rw [forall_r_z pr z k j]
  simp only [h_r_z]
  apply cumIndxs_sum

/-
  # Exceptional set
-/

def exceptionalSet {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) : Finset (Fin (n_p + 1) → F) :=
  if ∀ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) = 0
    then ∅
    else Finset.univ.filter fun z =>
      (∃ k j, z k = funK pr k f j)
        ∨ ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (funK pr k m j) / ((z k) - funK pr k f j) = 0

lemma exceptionalSet_eq_neg {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (h : ¬ ∀ k : Fin (n_p + 1),
            ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) = 0) :
    exceptionalSet f m pr = Finset.univ.filter fun (z : Fin (n_p + 1) → F) =>
      (∃ k j, z k = funK pr k f j)
        ∨ ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (funK pr k m j) / ((z k) - funK pr k f j) = 0 := by
  rw [exceptionalSet, if_neg h]

-- Translates the no collision condition in the exceptional set (which is partition-based) to the step-based
-- condition required by some lemmas.
omit [Field F] [Fintype F] in
lemma no_collisions_s_of_r {t n_s n_p : Nat}
      (f : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (h_collisions : ¬ (∃ k j, z k = funK pr k f j)) :
    ∀ (k : Fin (n_s + 1)) (j : Fin (indxsK s ↑k).length), funK s (↑k) f j ≠ funK s (↑k) (z ∘ pr) j := by
  simp only [not_exists] at h_collisions
  rwa [←forall_no_z_collisions f s pr z] at h_collisions


-- # Collision set

-- collisions at partition k

-- The set of functions where the collision is with values in the k'th partition
open Fin.NatCast in
def collision_k {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :=
  Finset.univ.filter fun (z : Fin (n_p + 1) → F) => (∃ j, z k = funK pr k f j)

-- The collision_k set is a piFinset defined by the following function
def collision_pi {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) : Fin (n_p + 1) → Finset F :=
  fun (i : Fin (n_p + 1)) => if i = k then ((indxsK pr k).map f).toFinset else Finset.univ

-- For the bound on the cardinality we actually only need inclusion ⊆ here, but we prove both directions, anyway.
omit [Field F] in
lemma collision_k_eq_pi {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) :
    collision_k f pr k = Fintype.piFinset (collision_pi f pr k) := by
  apply Finset.ext ; intro z
  rw [Fintype.mem_piFinset]
  unfold collision_k
  rw [Finset.mem_filter]
  unfold collision_pi
  constructor
  · rintro ⟨_, j, h_c⟩
    intro i
    unfold funK at h_c
    by_cases h : i = k
    · rw [if_pos h]
      simp only [h, List.mem_toFinset, List.mem_map]
      use (indxsK pr ↑k).get j
      constructor ; apply List.get_mem _ j
      rw [←h_c] ; simp
    rw [if_neg h] ; simp
  intro h_z ; simp
  have h_k := h_z k
  simp only [eq_self, ite_true, List.mem_toFinset, List.mem_map] at h_k
  rcases h_k with ⟨a, h_a_mem, h_f_a⟩
  rw [List.mem_iff_get] at h_a_mem
  unfold funK
  rcases h_a_mem with ⟨j, h_j⟩
  use j
  rwa [h_j, eq_comm]

omit [Field F] in
lemma collision_k_card {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) :
    (collision_k f pr k).card = (Fintype.card F) ^ (n_p) * (List.map f (indxsK pr k)).toFinset.card := by
  rw [collision_k_eq_pi, Fintype.card_piFinset]
  unfold collision_pi
  simp only [apply_ite, Finset.prod_ite]
  -- first product (i ≠ k)
  simp only [Finset.prod_const]
  simp only [←ne_eq, ne_comm, Finset.filter_ne _ k]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ k)]
  simp only [Finset.card_univ, Fintype.card_fin, add_tsub_cancel_right]
  -- second product (i = k)
  simp only [Finset.filter_eq']
  simp only [Finset.mem_univ, ↓reduceIte, Finset.card_singleton, pow_one]
  simp only [mul_comm]

-- All collisions

-- The set of functions where the collision is with values in any partition before the k'th.
open Fin.NatCast in
def collision_lt_k {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :=
  Finset.univ.filter fun (z : Fin (n_p + 1) → F) => (∃ k' < k, ∃ j, z k' = funK pr k' f j)

omit [Field F] in
lemma collision_k_union {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    collision_lt_k f pr (k + 1) = collision_lt_k f pr k ∪ collision_k f pr k := by
  unfold collision_lt_k collision_k
  simp only [Nat.exists_lt_succ, Finset.filter_or]

omit [Field F] in
lemma collision_le_k_card_le {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (collision_lt_k f pr (k + 1)).card ≤ ∑ i < (k + 1), (collision_k f pr i).card := by
  simp only [Finset.Iio_eq_Ico, Nat.bot_eq_zero]
  induction k with
  | zero => unfold collision_lt_k collision_k ; simp
  | succ k h_ind =>
    rw [collision_k_union]
    apply le_trans (Finset.card_union_le _ _)
    rw [Finset.sum_Ico_succ_top (by simp)]
    apply add_le_add h_ind (le_refl _)

omit [Field F] in
lemma collision_le_n_r_card_le {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (collision_lt_k f pr (n_p + 1)).card ≤ ∑ i : Fin (n_p +1), (collision_k f pr i).card := by
  apply le_trans (collision_le_k_card_le f pr n_p)
  simp only [Finset.Iio_eq_Ico, Nat.bot_eq_zero, Nat.Ico_zero_eq_range]
  simp only [←Fin.sum_univ_eq_sum_range]
  apply le_of_eq
  rfl

omit [Field F] in
lemma collision_set_eq {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (Finset.univ.filter fun (z : Fin (n_p + 1) → F) => (∃ k j, z k = funK pr k f j)) =
      collision_lt_k f pr (n_p + 1) := by
  unfold collision_lt_k
  congr ; apply @_root_.funext ; intro z
  rw [Fin.exists_iff]
  ext
  constructor
  · rintro ⟨k', h_k', j, h_eq⟩
    use k', h_k', j
    convert h_eq
    apply Nat.mod_eq_of_lt h_k'
  rintro ⟨k', h_k', j, h_eq⟩
  use k', h_k', j
  convert h_eq
  rw [eq_comm] ; apply Nat.mod_eq_of_lt h_k'

-- Main bound for the collision part of the extension set.

omit [Field F] in
lemma collision_set_card_le {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (Finset.univ.filter fun (z : Fin (n_p + 1) → F) => (∃ k j, z k = funK pr k f j)).card ≤
      (Fintype.card F) ^ (n_p) * ∑ k : Fin (n_p + 1), (List.map f (indxsK pr k)).toFinset.card := by
  rw [collision_set_eq]
  apply le_trans (collision_le_n_r_card_le f pr)
  simp only [collision_k_card f pr _]
  rw [Finset.mul_sum]

-- Slightly weaker than above, but perhaps easier to use.
omit [Field F] in
lemma collision_set_card_le' {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (Finset.univ.filter fun (z : Fin (n_p + 1) → F) => (∃ k j, z k = funK pr k f j)).card ≤
      (Fintype.card F) ^ (n_p) * ∑ k : Fin (n_p + 1), (indxsK pr k).length := by
  apply le_trans (collision_set_card_le f pr)
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro i _
  apply le_trans (List.toFinset_card_le _)
  simp [List.length_map]

-- # Rational function poles and polynomials

def prodM {n :Nat} (f : Fin n → F) : F[X] := ((Fin.fintype n).elems.val.map (fun j => (X - C (f j)))).prod
def prodM_exc {n : Nat} (f : Fin n → F) (k : Fin n) : F[X] :=
  (((Fin.fintype n).elems.val.erase k).map (fun j => (X - C (f j)))).prod

-- These are used in calculating a bound on the zero part of the exceptional set.

omit [Fintype F] in
lemma prodM_exc_map_erase {n : Nat} (f : Fin n → F) (j : Fin n) :
    prodM_exc f j = (((Fin.fintype n).elems.val.map (fun j => (X - C (f j)))).erase (X - C (f j))).prod := by
  unfold prodM_exc ; rw [Multiset.map_erase_of_mem]
  exact (Fin.fintype n).complete j

omit [Fintype F] in
lemma Polynomial.prod_ne_zero {n : Nat} {f : Fin n → F} : prodM f ≠ 0 := by
  apply Multiset.prod_ne_zero
  rw [Multiset.mem_map, not_exists]
  intro j ;  rw [not_and] ; intro _ ; rw [←ne_eq]
  apply Polynomial.X_sub_C_ne_zero

omit [Fintype F] in
lemma RatFunc.prod_ne_zero {n : Nat} {f : Fin n → F} : (algebraMap F[X] (RatFunc F)) (prodM f) ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  apply Polynomial.prod_ne_zero

omit [Fintype F] in
lemma RatFunc.X_sub_C_ne_zero {x : F} : RatFunc.X - RatFunc.C x ≠ 0 := by
  rw [←RatFunc.algebraMap_X, ←RatFunc.algebraMap_C, ←algebraMap.coe_sub]
  apply RatFunc.algebraMap_ne_zero
  apply Polynomial.X_sub_C_ne_zero

omit [Fintype F] in
lemma prod_mul_frac_eq {n : Nat} (f m : Fin n → F) (j : Fin n) :
    (algebraMap _ _) (prodM f) * RatFunc.mk (C (m j)) (X - C (f j)) = ↑(C (m j)) * ↑(prodM_exc f j) := by
  unfold prodM prodM_exc
  have h_j : j ∈ (Fin.fintype n).elems.val := Finset.mem_univ_val j
  rw [←Multiset.prod_map_erase h_j]
  rw [RatFunc.mk_eq_div]
  simp
  conv_lhs => rw [mul_comm, ←mul_assoc]
  rw [div_mul_cancel₀] ; swap ; apply RatFunc.X_sub_C_ne_zero
  rfl

omit [Fintype F] in
lemma sum_prod_mul_frac_eq {n : Nat} {f m : Fin n → F} :
    ∑ j : Fin n, (algebraMap _ _) (prodM f) * RatFunc.mk (C (m j)) (X - C (f j)) =
      ∑ j : Fin n, (algebraMap F[X] (RatFunc F)) (C (m j)) * ↑(prodM_exc f j) := by
  apply Finset.sum_congr
  rfl
  intros j _ ; apply prod_mul_frac_eq

omit [Fintype F] in
lemma sum_prod_mul_frac_eq' {n : Nat} {f m : Fin n → F} :
    ∑ j : Fin n, (algebraMap _ _) (prodM f) * RatFunc.mk (C (m j)) (X - C (f j)) =
      (algebraMap F[X] (RatFunc F)) (∑ j : Fin n, (C (m j)) * (prodM_exc f j)) := by
  rw [sum_prod_mul_frac_eq]
  simp only [RatFunc.algebraMap_C, map_sum, map_mul] ; rfl

omit [Fintype F] in
lemma RatFunc.prod_mul_cancel (x y : RatFunc F) (f : Fin nCol → F) :
    x = y ↔ (algebraMap _ _) (prodM f) * x = (algebraMap _ _) (prodM f) * y := by
  constructor
  · intro h ; exact congr_arg (fun (x : RatFunc F) => ((algebraMap _ _) (prodM f)) * x) h
  intro h
  apply mul_left_cancel₀ _ h
  apply prod_ne_zero

omit [Fintype F] in
lemma sum_frac_eq_iff_sum_prod {n : Nat} {q : F} {f m : Fin n → F} :
    ∑ j : Fin n, (RatFunc.mk (C <| m j) (X - C (f j))) = RatFunc.C q ↔
      (algebraMap _ _) (∑ j : Fin n, C (m j) * (prodM_exc f j)) = (algebraMap _ _) (prodM f) * RatFunc.C q := by
  rw [RatFunc.prod_mul_cancel _ _ f]
  rw [Finset.mul_sum, sum_prod_mul_frac_eq']

omit [Fintype F] in
lemma sum_ratFunc_iff_sum_poly {n : Nat} {q : F} {f m : Fin n → F} :
    (algebraMap _ _) (∑ j : Fin n, C (m j) * (prodM_exc f j)) = (algebraMap _ _) (prodM f) * RatFunc.C q ↔
      ∑ j : Fin n, C (m j) * (prodM_exc f j) = (prodM f) * C q := by
  simp only [←RatFunc.algebraMap_C]
  simp only [←map_mul]
  constructor
  · intro h
    apply RatFunc.algebraMap_injective
    exact h
  intro h ; rw [h]

-- This is the main lemma used below

omit [Fintype F] in
lemma sum_frac_eq_iff_sum_prod_poly_eq' {n : Nat} {q : F} {f m : Fin n → F} :
    ∑ j : Fin n, (RatFunc.mk (C <| m j) (X - C (f j))) = RatFunc.C q ↔
      ∑ j : Fin n, C (m j) * (prodM_exc f j) = (prodM f) * C q  := by
  rw [sum_frac_eq_iff_sum_prod]
  apply sum_ratFunc_iff_sum_poly


-- # Zero set

def fin_exc_k {n_p : Nat} (k : Fin (n_p + 1)) := (Fin.fintype (n_p + 1)).elems.erase k

def frac_eval_k {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) :=
  ∑ j : Fin (indxsK pr k).length, funK pr k m j / (z k - funK pr k f j)

omit [Fintype F] in
lemma frac_eval_k_add {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) :
    ∑ i : Fin (n_p + 1), ∑ j : Fin (indxsK pr i).length, funK pr i m j / (z i - funK pr i f j) =
      (∑ i ∈ fin_exc_k k, frac_eval_k f m pr z i) + frac_eval_k f m pr z k := by
  unfold fin_exc_k
  simp only [Finset.sum_erase_add _ _ (Fintype.complete k)]
  rfl

omit [Fintype F] in
lemma sum_prod_exc_eval_eq {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) :
    (∑ j : Fin (indxsK pr k).length, C (funK pr k m j) * (prodM_exc (funK pr k f) j)).eval (z k) =
      ∑ j : Fin (indxsK pr k).length, (funK pr k m j) * (prodZ_exc (funK pr k f) (funK pr k (z ∘ pr)) j) := by
  unfold prodM_exc
  simp only [eval_finset_sum, eval_mul, eval_C]
  simp only [_root_.eval_multiset_prod, Multiset.map_map, Function.comp_apply, eval_sub, eval_C, eval_X]
  unfold prodZ_exc
  simp only [forall_r_z]

omit [Fintype F] in
lemma prod_eval_eq {t n_p : Nat} (f : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) :
    (prodM (funK pr k f)).eval (z k) = prodZ (funK pr k f) (funK pr k (z ∘ pr)) := by
  unfold prodM prodZ
  simp only [_root_.eval_multiset_prod, Multiset.map_map, Function.comp_apply, eval_sub, eval_C, eval_X]
  simp only [forall_r_z]

-- If z is in the zero set then z k is a root of the following polynomial.
def z_k_poly {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) : F[X] :=
    (∑ j : Fin (indxsK pr k).length, C (funK pr k m j) * (prodM_exc (funK pr k f) j)) + (prodM (funK pr k f)) * C (∑ i ∈ fin_exc_k k, frac_eval_k f m pr z i)

omit [Fintype F] in
lemma z_k_poly_eq_on_exc {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z₁ z₂ : Fin (n_p + 1) → F)
      (k : Fin (n_p + 1))
      (h_eq_exc : ∀ i, i ≠ k → z₁ i = z₂ i) :
    z_k_poly f m pr z₁ k = z_k_poly f m pr z₂ k := by
  unfold z_k_poly
  rw [add_left_cancel_iff]
  apply congr_arg
  rw [Polynomial.C_inj]
  apply Finset.sum_congr rfl
  intro i h_i
  unfold frac_eval_k
  rw [h_eq_exc i (Finset.ne_of_mem_erase h_i)]

omit [Fintype F] in
lemma natDegree_prodM {n :Nat} (f : Fin n → F) : (prodM f).natDegree = n := by
  unfold prodM
  rw [Polynomial.natDegree_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.natDegree_X_sub_C]
  · simp ; rw [←Finset.univ, ←Finset.card_fin n] ; simp
  rw [Multiset.mem_map, not_exists]
  intro i
  rw [not_and] ; intro _ ; rw [←ne_eq] ; apply Polynomial.X_sub_C_ne_zero

omit [Fintype F] in
lemma natDegree_prodM_exc {n :Nat} (f : Fin n → F) (k : Fin n) : (prodM_exc f k).natDegree = n - 1 := by
  unfold prodM_exc
  rw [Polynomial.natDegree_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.natDegree_X_sub_C]
  · simp ; rw [Multiset.card_erase_of_mem (Fintype.complete k)] ; rw [←Finset.univ, ←Finset.card_fin n] ; simp
  rw [Multiset.mem_map, not_exists]
  intro i
  rw [not_and] ; intro _ ; rw [←ne_eq] ; apply Polynomial.X_sub_C_ne_zero

omit [Fintype F] in
lemma netDegree_sum_prodM_exc_le {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Fin (n_p + 1)) :
    (∑ j : Fin (indxsK pr k).length, C (funK pr k m j) * (prodM_exc (funK pr k f) j)).natDegree ≤ (indxsK pr k).length - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  rw [mul_comm]
  apply le_trans (Polynomial.natDegree_mul_C_le _ _)
  rw [natDegree_prodM_exc]

omit [Fintype F] in
lemma natDegree_prodM_eq_of_ne_zero {t n_p : Nat}
      (f : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Fin (n_p + 1))
      (a : F)
      (h_a : a ≠ 0) :
    ((prodM (funK pr k f)) * C a).natDegree = (indxsK pr k).length := by
  rw [Polynomial.natDegree_mul_C h_a]
  apply natDegree_prodM

omit [Fintype F] in
lemma natDegree_z_k_poly {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (z : Fin (n_p + 1) → F) (k : Fin (n_p + 1)) :
    (z_k_poly f m pr z k).natDegree ≤ (indxsK pr k).length := by
  unfold z_k_poly
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply le_trans (max_le_max (netDegree_sum_prodM_exc_le f m pr k) (Polynomial.natDegree_mul_C_le _ _))
  rw [natDegree_prodM]
  simp

omit [Fintype F] in
lemma sum_eval_exc_eq_zero_of_poly_k_eq_zero {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (k : Fin (n_p + 1))
      (h_len_ne_zero : (indxsK pr k).length ≠ 0) :
    (z_k_poly f m pr z k) = 0 → C (∑ i ∈ fin_exc_k k, frac_eval_k f m pr z i) = 0 := by
  unfold z_k_poly ; intro h
  rw [add_eq_zero_iff_eq_neg] at h
  by_contra h_ne_zero
  rw [←ne_eq, Polynomial.C_ne_zero] at h_ne_zero
  replace h := congr_arg Polynomial.natDegree h
  rw [Polynomial.natDegree_neg, natDegree_prodM_eq_of_ne_zero f pr k _ h_ne_zero] at h
  have h_exc := netDegree_sum_prodM_exc_le f m pr k
  simp only [h] at h_exc
  exact Nat.not_le_of_lt (Nat.sub_one_lt h_len_ne_zero) h_exc

omit [Fintype F] in
lemma indxs_len_ne_zero_of_fracs_ne_zero {t n_p : Nat}
      {f m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    (indxsK pr k).length ≠ 0 := by
  by_contra h_len
  rw [Finset.sum_fin_eq_sum_range] at h_frac_ne_zero
  simp only [h_len, Finset.range_zero, Finset.sum_empty] at h_frac_ne_zero
  exact h_frac_ne_zero rfl

omit [Fintype F] in
lemma poly_k_ne_zero {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (k : Fin (n_p + 1))
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    (z_k_poly f m pr z k) ≠ 0 := by
  unfold z_k_poly
  by_contra h
  have h_len_ne_zero : (indxsK pr k).length ≠ 0 := indxs_len_ne_zero_of_fracs_ne_zero h_frac_ne_zero
  simp only [sum_eval_exc_eq_zero_of_poly_k_eq_zero f m pr z k h_len_ne_zero h] at h
  rw [add_eq_zero_iff_eq_neg, neg_mul_eq_mul_neg, neg_zero, ←Polynomial.C_0] at h
  rw [←sum_frac_eq_iff_sum_prod_poly_eq', map_zero] at h
  exact h_frac_ne_zero h

-- Maps (z k) to its index in the list of roots of z_k_poly.
def z_k_root_indx {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) (z : Fin (n_p + 1) → F) :=
  (z_k_poly f m pr z k).roots.toFinset.toList.idxOf (z k)

omit [Fintype F] in
lemma z_k_root_indx_le {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) (z : Fin (n_p + 1) → F) :
    z_k_root_indx f m pr k z ≤ (indxsK pr ↑k).length := by
  apply le_trans (List.idxOf_le_length)
  rw [Finset.length_toList]
  apply le_trans (Multiset.toFinset_card_le _)
  apply le_trans (Polynomial.card_roots' _)
  exact natDegree_z_k_poly f m pr z k

omit [Fintype F] in
lemma z_k_root_indx_lt {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) (z : Fin (n_p + 1) → F) :
    z_k_root_indx f m pr k z < (indxsK pr ↑k).length + 1 := by
  rw [Nat.lt_succ]
  apply z_k_root_indx_le

omit [Fintype F] in
def z_k_root_indx_fin {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) (z : Fin (n_p + 1) → F) :
    Fin ((indxsK pr k).length + 1) :=
  ⟨z_k_root_indx f m pr k z, z_k_root_indx_lt f m pr k z⟩

def exceptionalSpace (n_p : Nat) (n : Nat) :=
  Fintype.piFinset (fun (_ : Fin n_p) => (Finset.univ : Finset F)) ×ˢ (Fin.fintype (n + 1)).elems

-- injection from the zero set to the exceptionalSpace
open Fin.NatCast in
def proj_z_k_root_indx {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) :=
  fun z => (fun (i : Fin n_p) => if i < k then (z i) else (z (i + 1)), z_k_root_indx_fin f m pr k z)

open Fin.NatCast in
lemma proj_z_k_root_into_exceptionalSpace {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) (z : Fin (n_p + 1) → F) :
    proj_z_k_root_indx f m pr k z ∈ exceptionalSpace n_p (indxsK pr ↑k).length := by
  unfold exceptionalSpace
  rw [Finset.mem_product, Fintype.mem_piFinset]
  unfold proj_z_k_root_indx
  constructor
  · intro i
    by_cases h : i < k
    · simp only [if_pos h, Finset.mem_univ]
    simp only [if_neg h, Finset.mem_univ]
  simp
  apply Finset.mem_univ (z_k_root_indx_fin f m pr k z)

def zero_set {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :=
  Finset.univ.filter fun (z : Fin (n_p + 1) → F) =>
     ¬ (∃ k j, z k = funK pr k f j)
      ∧ ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (funK pr k m j) / ((z k) - funK pr k f j) = 0

lemma eval_eq_of_zero_set {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (z_in : z ∈ zero_set f m pr) :
    ∀ (k : Fin (n_p + 1)),
      (∑ j : Fin (indxsK pr k).length, C (funK pr k m j) * (prodM_exc (funK pr k f) j)).eval (z k) =
        ((prodM (funK pr k f)).eval (z k)) * (- ∑ i ∈ fin_exc_k k, frac_eval_k f m pr z i) := by
  unfold zero_set at z_in
  rw [Finset.mem_filter] at z_in
  rcases z_in with ⟨_, h_collisions, h_sum_zero⟩
  intro k
  rw [frac_eval_k_add _ _ _ _ k] at h_sum_zero
  unfold frac_eval_k at h_sum_zero
  rw [sum_prod_exc_eval_eq, prod_eval_eq]
  rw [prodZ_eq_iff_frac_sum_eq (funK pr k f) (funK pr k m) (funK pr k (z ∘ pr))]
  · rw [← add_eq_zero_iff_eq_neg']
    simp only [forall_r_z]
    exact h_sum_zero
  simp only [not_exists] at h_collisions
  simp only [forall_r_z, ne_eq, eq_comm]
  exact h_collisions k

lemma z_k_is_root_of_mem_zero_set {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (z_in : z ∈ zero_set f m pr)
      (k : Fin (n_p + 1)) :
    (z_k_poly f m pr z k).IsRoot (z k) := by
  unfold z_k_poly ; rw [IsRoot]
  simp only [eval_add]
  conv_lhs => arg 2 ; simp only [eval_mul, eval_C]
  rw [add_eq_zero_iff_eq_neg, neg_mul_eq_mul_neg]
  exact eval_eq_of_zero_set f m pr z z_in k

lemma z_k_root_indx_inj {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z₁ z₂ : Fin (n_p + 1) → F)
      (z₁_in : z₁ ∈ zero_set f m pr)
      (z₂_in : z₂ ∈ zero_set f m pr)
      (k : Fin (n_p + 1))
      (h_eq_exc : ∀ i, i ≠ k → z₁ i = z₂ i)
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    z_k_root_indx f m pr k z₁ = z_k_root_indx f m pr k z₂ → z₁ k = z₂ k := by
  intro h ; unfold z_k_root_indx at h
  rw [z_k_poly_eq_on_exc f m pr z₁ z₂ k h_eq_exc] at h
  rw [←(List.idxOf_inj _ _).mp h] <;> rw [Finset.mem_toList, Multiset.mem_toFinset, Polynomial.mem_roots]
  · rw [←z_k_poly_eq_on_exc f m pr z₁ z₂ k h_eq_exc] ; exact z_k_is_root_of_mem_zero_set f m pr z₁ z₁_in k
  exact poly_k_ne_zero f m pr z₂ k h_frac_ne_zero
  exact z_k_is_root_of_mem_zero_set f m pr z₂ z₂_in k
  exact poly_k_ne_zero f m pr z₂ k h_frac_ne_zero

omit [Fintype F] in
theorem nat_coe_F_inj {t n_p : Nat} {pr : Fin t → Fin (n_p + 1)} {k : Fin (n_p + 1)} {a b : ℕ}
      (h_lt_char : (indxsK pr k).length < ringChar F)
      (ha : a ≤ (indxsK pr k).length)
      (hb : b ≤ (indxsK pr k).length)
      (h : (a : F) = (b : F)) :
    a = b := by
  apply Nat.cast_inj_of_lt_char _ _ h <;> apply lt_of_le_of_lt _ h_lt_char <;> assumption

omit [Fintype F] in
lemma proj_z_k_root_injOn_exc {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (z₁ z₂ : Fin (n_p + 1) → F)
      (k : Fin (n_p + 1))
      (h_proj_eq : proj_z_k_root_indx f m pr k z₁ = proj_z_k_root_indx f m pr k z₂) :
    ∀ i, i ≠ k → z₁ i = z₂ i := by
  rw [Fin.forall_iff]
  intro i h_i_lt h_ne
  unfold proj_z_k_root_indx at h_proj_eq
  rw [Prod.mk_inj] at h_proj_eq
  rw [funext_iff] at h_proj_eq
  replace h_proj_eq := h_proj_eq.1
  rw [Fin.forall_iff] at h_proj_eq
  simp only [Fin.lt_iff_val_lt_val, Fin.val_natCast] at h_proj_eq
  by_cases h : i < ↑k
  · have h_i_lt_n_r : i < n_p := by apply lt_of_lt_of_le h (Fin.is_le k)
    replace h_proj_eq := h_proj_eq i h_i_lt_n_r
    simp only [Nat.mod_eq_of_lt h_i_lt] at h_proj_eq
    simp only [if_pos h] at h_proj_eq
    rwa [Fin.natCast_eq_mk h_i_lt] at h_proj_eq
  rw [not_lt] at h
  rw [ne_eq, ←Fin.val_eq_val, Fin.val_mk, Eq.comm, ←ne_eq] at h_ne
  replace h := lt_of_le_of_ne h h_ne
  have h_i_sub_one_lt_n_r : i - 1 < n_p := by
    rw [Nat.sub_one, ←Nat.pred_succ n_p]
    exact Nat.pred_lt_pred (ne_zero_of_lt h) h_i_lt
  have h_i_sub_one_lt_succ := (lt_trans h_i_sub_one_lt_n_r (Nat.lt_add_one _))
  replace h_proj_eq := h_proj_eq (i - 1) h_i_sub_one_lt_n_r
  simp only [Nat.mod_eq_of_lt h_i_sub_one_lt_succ] at h_proj_eq
  have h_not_lt : ¬ i - 1 < ↑k := by exact not_lt_of_ge (Nat.le_pred_of_lt h)
  simp only [if_neg h_not_lt] at h_proj_eq
  simp only [Fin.add_def] at h_proj_eq
  simp only [Fin.val_natCast, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod] at h_proj_eq
  simp only [Nat.sub_one_add_one (Nat.ne_zero_of_lt h)] at h_proj_eq
  simp only [Nat.mod_eq_of_lt h_i_lt] at h_proj_eq
  exact h_proj_eq

lemma proj_z_k_root_injOn {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Fin (n_p + 1))
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    Set.InjOn (proj_z_k_root_indx f m pr k) (zero_set f m pr) := by
  unfold Set.InjOn zero_set
  intros z₁ z₁_in z₂ z₂_in h_proj_eq
  apply @_root_.funext
  intro i
  by_cases h_eq : i = k
  · rw [h_eq]
    apply z_k_root_indx_inj f m pr z₁ z₂ z₁_in z₂_in k (proj_z_k_root_injOn_exc f m pr z₁ z₂ k h_proj_eq) h_frac_ne_zero
    unfold proj_z_k_root_indx at h_proj_eq
    rw [Prod.mk_inj] at h_proj_eq
    replace h_proj_eq := h_proj_eq.2
    unfold z_k_root_indx_fin at h_proj_eq
    rw [Fin.mk_eq_mk] at h_proj_eq
    exact h_proj_eq
  exact (proj_z_k_root_injOn_exc f m pr z₁ z₂ k h_proj_eq i h_eq)

lemma card_zero_set_le_card_exceptionalSpace {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Fin (n_p + 1))
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    (zero_set f m pr).card ≤ (exceptionalSpace (F := F) n_p (indxsK pr ↑k).length).card := by
  apply Finset.card_le_card_of_injOn (proj_z_k_root_indx f m pr k)
  intro z _ ; apply proj_z_k_root_into_exceptionalSpace f m pr k z
  apply proj_z_k_root_injOn f m pr k h_frac_ne_zero

lemma card_zero_set_le {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Fin (n_p + 1))
      (h_frac_ne_zero : ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) ≠ 0) :
    -- The + 1 is not needed here, and is a result of the definition of Fin_F. This can be changed but
    -- requires some changes to other proofs.
    (zero_set f m pr).card ≤ (Fintype.card F) ^ (n_p) * ((indxsK pr k).length + 1) := by
  apply le_trans (card_zero_set_le_card_exceptionalSpace f m pr k h_frac_ne_zero)
  unfold exceptionalSpace ; rw [Finset.card_product]
  rw [Fintype.card_piFinset]
  apply Nat.mul_le_mul
  · simp only [Fin.prod_const]
    simp only [Finset.card_univ] ; rfl
  rw [←Finset.univ, Finset.card_fin ((indxsK pr ↑k).length + 1)]

lemma or_iff_or_not_and {p q : Prop} : p ∨ q ↔ p ∨ (¬p ∧ q) := by
  constructor
  · intro h
    rw [Classical.or_iff_not_imp_left] at h
    cases' Classical.em p with h_p h_p
    · left ; assumption
    right ; exact ⟨h_p, h h_p⟩
  intro h
  cases' h with h_p h_q
  · left ; assumption
  right ; exact h_q.2

omit [Fintype F] in
lemma exceptionalSet_filter_or_not_and {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (fun (z : Fin (n_p + 1) → F) => (∃ k j, z k = funK pr (↑k) f j) ∨
      ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr ↑k).length, funK pr (↑k) m j / (z k - funK pr (↑k) f j) = 0) =
    (fun (z : Fin (n_p + 1) → F) => (∃ k j, z k = funK pr (↑k) f j) ∨
      (¬ (∃ k j, z k = funK pr (↑k) f j) ∧
        ∑ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr ↑k).length, funK pr (↑k) m j / (z k - funK pr (↑k) f j) = 0)) := by
  apply _root_.funext
  intro z
  rw [or_iff_or_not_and]

-- The + 1 in ((indxsK pr k).length + 1) is not really needed (see similar comment above).
lemma card_exceptionalSet_le_sum_add_exists {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    ∃ k : Fin (n_p + 1), (exceptionalSet f m pr).card ≤
      (Fintype.card F) ^ (n_p) * ∑ i : Fin (n_p + 1), (indxsK pr i).length + (Fintype.card F) ^ (n_p) * ((indxsK pr k).length + 1) := by
  by_cases h : ∀ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) = 0
  · rw [exceptionalSet, if_pos h] ; simp
  rw [exceptionalSet, if_neg h]
  rw [not_forall] at h
  rcases h with ⟨k, h_frac_ne_zero⟩
  use k
  simp only [exceptionalSet_filter_or_not_and]
  simp only [Finset.filter_or]
  apply le_trans (Finset.card_union_le _ _)
  apply add_le_add
  exact collision_set_card_le' f pr
  apply card_zero_set_le f m pr k h_frac_ne_zero

lemma rel_lengths_nonempty {t n_p : Nat} (pr : Fin t → Fin (n_p + 1)) :
    (Finset.image (fun (k : Fin (n_p + 1)) => (indxsK pr k).length + 1) (Fin.fintype (n_p + 1)).elems).Nonempty := by
  rw [Finset.image_nonempty]
  apply Finset.univ_nonempty

def max_pr_len {t n_p : Nat} (pr : Fin t → Fin (n_p + 1)) : ℕ :=
  Finset.max' (Finset.image (fun (k : Fin (n_p + 1)) => (indxsK pr k).length + 1) (Fin.fintype (n_p + 1)).elems)
    (rel_lengths_nonempty pr)

lemma exists_k_max {t n_p : Nat} (pr : Fin t → Fin (n_p + 1)) :
    ∃ k ∈ (Fin.fintype (n_p + 1)).elems, max_pr_len pr = (indxsK pr ↑k).length + 1 := by
  unfold max_pr_len
  rw [Finset.max'_eq_sup', Finset.sup'_image, Function.id_comp]
  apply Finset.exists_mem_eq_sup' Finset.univ_nonempty

lemma card_exceptionalSet_le {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    (exceptionalSet f m pr).card ≤ Fintype.card F ^ n_p * t + Fintype.card F ^ n_p * max_pr_len pr := by
  rcases card_exceptionalSet_le_sum_add_exists f m pr with ⟨k, h_card_le⟩
  apply le_trans h_card_le
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_left
    rw [sum_all_indxs_len _ (Nat.zero_lt_succ n_p)]
  apply Nat.mul_le_mul_left
  apply Finset.le_max'
  apply Finset.mem_image_of_mem
  apply (Fintype.complete k)

lemma pole_sum_zero_of_constraints_and_not_exceptionalSet {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0) :
    ∀ k : Fin (n_p + 1), ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) = 0 := by
  by_contra h
  rw [exceptionalSet_eq_neg f m pr h] at h_z
  rw [Finset.mem_filter] at h_z
  simp only [Finset.mem_univ, true_and, not_or] at h_z
  rcases h_z with ⟨h_collisions, h_sum_zero⟩
  rw [←sum_all_fracs_cum_by_rel] at h_sum_zero
  rw [sum_all_fracs f m pr pr z] at h_sum_zero
  rw [sum_zero_of_constraits f m s pr z psum (no_collisions_s_of_r f s pr z h_collisions) h_cumulativeC h_cyclic] at h_sum_zero
  exact h_sum_zero rfl

-- # use / yield values

-- The indexes of the use values in partition k
def use_indxs {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :=
  (indxsK pr k).filter (fun i => m i = 1)
def yield_indxs {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :=
  (indxsK pr k).filter (fun i => m i ≠ 1)

omit [Fintype F] in
lemma use_indxs_nodup {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (use_indxs m pr k).Nodup := by
  apply List.Nodup.filter _ (indxsK_nodup _ _)

omit [Fintype F] in
lemma yield_indxs_nodup {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (yield_indxs m pr k).Nodup := by
  apply List.Nodup.filter _ (indxsK_nodup _ _)

omit [Fintype F] in
lemma use_indxs_subset {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (use_indxs m pr k).toFinset ⊆ (indxsK pr k).toFinset := by simp [use_indxs]

omit [Fintype F] in
lemma yield_indxs_subset {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (yield_indxs m pr k).toFinset ⊆ (indxsK pr k).toFinset := by simp [yield_indxs]

omit [Fintype F] in
lemma use_yield_indxs_disjoint {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (use_indxs m pr k).toFinset ∩ (yield_indxs m pr k).toFinset = ∅ := by
  simp only [use_indxs, yield_indxs, List.toFinset_filter, ←Finset.disjoint_iff_inter_eq_empty]
  apply Finset.disjoint_filter.mpr
  intro _ _ h_p
  simp [ne_eq, decide_not, h_p]

omit [Fintype F] in
lemma use_indxs_card {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (use_indxs m pr k).length ≤ t := by
  apply le_trans (List.length_filter_le _ _)
  apply le_trans (List.length_filter_le _ _)
  simp only [Finset.length_toList]
  apply card_finset_fin_le

omit [Fintype F] in
lemma yield_indxs_card {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    (yield_indxs m pr k).length ≤ t := by
  apply le_trans (List.length_filter_le _ _)
  apply le_trans (List.length_filter_le _ _)
  simp only [Finset.length_toList]
  apply card_finset_fin_le

omit [Fintype F] in
lemma use_yield_indxs_append {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) :
    ((use_indxs m pr k) ++ (yield_indxs m pr k)).Perm (indxsK pr k) := by
  unfold use_indxs yield_indxs
  simp only [decide_not]
  apply List.filter_append_perm

omit [Fintype F] in
lemma count_use_indx {t n_p : ℕ} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) :
    ∀ i : Fin t, Multiset.count i ↑(use_indxs m pr ↑k) = if pr i = k ∧ m i = 1 then 1 else 0 := by
  intro i ; rw [Multiset.coe_count]
  unfold use_indxs indxsK ; rw [List.filter_filter]
  by_cases h_r_m : pr i = k ∧ m i = 1
  · simp [h_r_m.1, h_r_m.2]
    apply List.count_eq_one_of_mem (Finset.nodup_toList _) _
    rw [Finset.mem_toList] ; exact Fintype.complete i
  rw [if_neg h_r_m]
  rw [List.count_eq_zero, List.mem_filter]
  intro h ; apply h_r_m
  simp only [←Bool.decide_and, decide_eq_true_eq, Fin.val_eq_val] at h
  exact h.2.symm

omit [Fintype F] in
lemma count_yield_indx {t n_p : ℕ} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Fin (n_p + 1)) :
    ∀ i : Fin t, Multiset.count i ↑(yield_indxs m pr ↑k) = if pr i = k ∧ m i ≠ 1 then 1 else 0 := by
  intro i ; rw [Multiset.coe_count]
  unfold yield_indxs indxsK ; rw [List.filter_filter]
  by_cases h_r_m : pr i = k ∧ m i ≠ 1
  · simp [h_r_m.1, h_r_m.2]
    apply List.count_eq_one_of_mem (Finset.nodup_toList _) _
    rw [Finset.mem_toList] ; exact Fintype.complete i
  rw [if_neg h_r_m]
  rw [List.count_eq_zero, List.mem_filter]
  intro h ; apply h_r_m
  simp only [←Bool.decide_and, decide_eq_true_eq, Fin.val_eq_val] at h
  exact h.2.symm


def useK {α : Type _ } {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) (f : Fin t → α) :=
  fun i : Fin (use_indxs m pr k).length => f ((use_indxs m pr k).get i)
def yieldK {α : Type _ } {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) (f : Fin t → α) :=
  fun i : Fin (yield_indxs m pr k).length => f ((yield_indxs m pr k).get i)

omit [Fintype F] in
lemma use_yield_sum {α : Type _ } [AddCommMonoid α] {t n_p : Nat} (m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) (k : Nat) (f : Fin t → α) :
    ∑ j, (funK pr k f j) = (∑ j, (useK m pr k f j)) + ∑ j, (yieldK m pr k f j) := by
  unfold funK useK yieldK
  simp only [←List.sum_ofFn] ; simp only [List.get_eq_getElem, List.ofFn_getElem_eq_map]
  simp [←List.Perm.sum_eq (List.Perm.map f (use_yield_indxs_append m pr k))]

omit [Fintype F] in
lemma pole_split {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Nat) :
  ∑ j : Fin (indxsK pr k).length, (RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) =
    ∑ j : Fin (use_indxs m pr k).length, (RatFunc.mk (C (useK m pr k m j)) (X - C (useK m pr k f j)))
      + ∑ j : Fin (yield_indxs m pr k).length, (RatFunc.mk (C (yieldK m pr k m j)) (X - C (yieldK m pr k f j))) := by
  have h_funK : (fun j => RatFunc.mk (C (funK pr k m j)) (X - C (funK pr k f j))) =
    funK pr k (fun j => RatFunc.mk (C (m j)) (X - C (f j))) := by rfl
  have h_useK : (fun j => RatFunc.mk (C (useK m pr k m j)) (X - C (useK m pr k f j))) =
    useK m pr k (fun j => RatFunc.mk (C (m j)) (X - C (f j))) := by rfl
  have h_yieldK : (fun j => RatFunc.mk (C (yieldK m pr k m j)) (X - C (yieldK m pr k f j))) =
    yieldK m pr k (fun j => RatFunc.mk (C (m j)) (X - C (f j))) := by rfl
  rw [h_funK, h_useK, h_yieldK]
  apply use_yield_sum

omit [Fintype F] in
lemma use_poles {t n_p : Nat}
      (f m : Fin t → F)
      (pr : Fin t → Fin (n_p + 1))
      (k : Nat) :
    ∑ j : Fin (use_indxs m pr k).length, (RatFunc.mk (C (useK m pr k m j)) (X - C (useK m pr k f j))) =
      ∑ j : Fin (use_indxs m pr k).length, (RatFunc.mk 1 (X - C (useK m pr k f j))) := by
  have h_use_m : ∀ j, m ((List.filter (fun i => decide (m i = 1)) (indxsK pr k)).get j) = 1 := by
    simp only [Fin.forall_iff, List.get_eq_getElem]
    rw [←List.forall_mem_iff_getElem (p := fun x => m x = 1)]
    intro i
    rw [List.mem_filter, Bool.decide_iff]
    intro h ; exact h.2
  unfold useK use_indxs
  simp only [h_use_m, Polynomial.C_1]

omit [Fintype F] in
lemma neg_frac_eq_neg_m {t n_p : Nat} (f m : Fin t → F) (pr : Fin t → Fin (n_p + 1)) :
    ∀ k i, RatFunc.mk (C (yieldK m pr (↑k) (-m) i)) (X - C (yieldK m pr (↑k) f i)) =
      - RatFunc.mk (C (yieldK m pr (↑k) m i)) (X - C (yieldK m pr (↑k) f i)) := by
  intro k i
  have h_m_neg : (yieldK m pr (↑k) (-m) i) = -(yieldK m pr (↑k) m i) := by rfl
  simp only [h_m_neg, Polynomial.C_neg]
  simp only [RatFunc.mk_eq_div, map_neg, neg_div]

lemma inclusion_of_constraints_and_not_exceptionalSet {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (h_use_count_lt : ∀ k, max_count_F (useK m pr k f) < ringChar F)
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0) :
    ∀ k : Fin (n_p + 1), Finset.univ.val.map (useK m pr k f) ⊆ Finset.univ.val.map (yieldK m pr k f) := by
  intro k
  apply (set_inclusion_of' (useK m pr k f) (yieldK m pr k f) (h_use_count_lt k))
  use (yieldK m pr k (-m))
  simp only [neg_frac_eq_neg_m, Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
  simp only [←use_poles, ←pole_split]
  apply pole_sum_zero_of_constraints_and_not_exceptionalSet f m s pr z psum h_z h_cumulativeC h_cyclic

/-
  fin_map
-/

def fin_map {α : Type _ } {t : Nat} (f : Fin t → α) (indxs : List (Fin t)) :=
  fun i : Fin indxs.length => f (indxs.get i)

lemma map_eq_indxs {t : Nat} (indxs : List (Fin t)) :
    Multiset.map (fun i : Fin indxs.length => indxs.get i) Finset.univ.val = ↑indxs := by
  rw [←List.finRange_map_get indxs]
  simp

lemma fin_map_subset {α : Type _ } {t : Nat} (f : Fin t → α) (indxs1 indxs2 : List (Fin t)) (h : indxs1 ⊆ indxs2) :
    Multiset.map (fin_map f indxs1) Finset.univ.val ⊆ Multiset.map (fin_map f indxs2) Finset.univ.val := by
  rw [Multiset.subset_iff]
  simp only [Multiset.mem_map]
  intro x h_x_mem
  rcases h_x_mem with ⟨i, h_i_mem, h_i_eq⟩
  have h_mem2 : (indxs1.get i) ∈ indxs2 := by
    apply List.subset_def.mp h (List.get_mem _ _)
  rw [List.mem_iff_get] at h_mem2
  rcases h_mem2 with ⟨j, h_j_eq⟩
  use j
  rw [fin_map] at h_i_eq
  rw [fin_map, h_j_eq, h_i_eq]
  simp

lemma fin_map_count_eq {α : Type _ } {t : Nat}
    {f : Fin t → α}
    {indxs : List (Fin t)} :
    ∀ z, Multiset.count z (Multiset.map (fin_map f indxs) Finset.univ.val) =
      Multiset.count z (indxs.map fun i => f i) := by
  intro z
  simp only [←Multiset.map_coe, Multiset.count_map]
  rw [←map_eq_indxs indxs, Multiset.filter_map]
  simp [fin_map]

lemma fin_map_count_not_diff {α : Type _ } {t : Nat}
    {f : Fin t → α}
    {indxs indxs1 indxs2 : List (Fin t)}
    (h_nodup : indxs.Nodup)
    (h_nodup2 : indxs2.Nodup)
    (h_subset2 : indxs2 ⊆ indxs) :
    ∀ z, z ∉ Multiset.map (fin_map f (indxs.diff indxs1)) Finset.univ.val →
      Multiset.count z (Multiset.map (fin_map f indxs2) Finset.univ.val) ≤
        Multiset.count z (Multiset.map (fin_map f indxs1) Finset.univ.val) := by
  intro z h_z
  simp only [fin_map_count_eq, ←Multiset.map_coe]
  simp only [Multiset.count_map]
  apply Multiset.card_le_card
  rw [Multiset.le_iff_subset _]
  · rw [Multiset.subset_iff]
    intro i h_i
    simp_all
    have h_i_mem : i ∉ indxs1 → i ∈ indxs.diff indxs1 := by
      intro h_i_nin
      rw [List.Nodup.mem_diff_iff h_nodup]
      use List.subset_def.mp h_subset2 h_i.1
    by_contra h_not
    rcases List.mem_iff_get.mp (h_i_mem h_not) with ⟨j, h_j⟩
    apply h_z j
    simp only [fin_map, h_j]
  apply Multiset.Nodup.filter _ (Multiset.coe_nodup.mpr h_nodup2)

omit [Fintype F] in
lemma use_i_subset_use {t n_p : Nat}
      {m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      (use_i : Finset (Fin t))
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset) :
    use_i.toList ⊆ use_indxs m pr ↑k := by
  rw [List.subset_def]
  intro i h_i
  rw [←List.mem_toFinset]
  rw [Finset.mem_toList] at h_i
  apply Finset.mem_of_subset h_use_i h_i

omit [Fintype F] in
lemma yield_subset_complement_use_i {t n_p : Nat}
      {m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      (use_i : Finset (Fin t))
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset) :
    yield_indxs m pr ↑k ⊆ (indxsK pr ↑k).diff use_i.toList := by
  rw [List.subset_def]
  intro i h_i
  rw [List.Nodup.mem_diff_iff (indxsK_nodup _ _)]
  use (List.mem_filter.mp h_i).1
  intro h_mem
  have h_mem_use := List.subset_def.mp (use_i_subset_use use_i h_use_i) h_mem
  simp only [use_indxs, List.mem_filter, decide_eq_true_eq] at h_mem_use
  simp [yield_indxs, List.mem_filter] at h_i
  exact h_i.2 (h_mem_use.2)

lemma inclusion_of_constraints_and_not_exceptionalSet' {t n_s n_p : Nat}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      (k : Fin (n_p + 1))
      (use_i : Finset (Fin t))
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset)
      (h_use_count_lt : use_i.card < ringChar F)
      (h_z : z ∉ exceptionalSet f m pr) :
    Finset.univ.val.map (fin_map f use_i.toList) ⊆ Finset.univ.val.map (fin_map f ((indxsK pr k).diff use_i.toList)) := by
  rw [Multiset.subset_iff] ; intros x h_x
  replace h_x : x ∈ Multiset.map (fin_map f (use_indxs m pr k)) Finset.univ.val := by
    apply Multiset.mem_of_subset _ h_x
    apply fin_map_subset
    exact use_i_subset_use use_i h_use_i
  have h_useK : fin_map f (use_indxs m pr k) = useK m pr k f := by rfl
  rw [Multiset.mem_map] at h_x
  rcases h_x with ⟨i, h_i_mem, h_i_eq⟩
  rw [h_useK] at h_i_eq

  by_contra h
  have h_count : Multiset.count (useK m pr (↑k) f i) (Multiset.map (useK m pr (↑k) f) Finset.univ.val) < ringChar F := by
    rw [h_i_eq, ←h_useK]
    apply lt_of_le_of_lt (fin_map_count_not_diff (indxsK_nodup _ _) _ _ _ h)
    · apply lt_of_le_of_lt (Multiset.count_le_card _ _)
      rw [Multiset.card_map]
      simp only [Finset.card_val, Finset.card_univ, Finset.length_toList, Fintype.card_fin]
      exact h_use_count_lt
    · apply List.Nodup.filter
      exact (indxsK_nodup _ _)
    simp only [use_indxs, List.filter_subset']
  apply h

  apply Multiset.mem_of_subset (fin_map_subset f _ _ (yield_subset_complement_use_i use_i h_use_i))
  have h_mem_yield := mem_b_of_mem_a' (useK m pr k f) (yieldK m pr k f) i h_count
  rw [h_i_eq] at h_mem_yield
  apply h_mem_yield
  use (yieldK m pr k (-m))
  simp only [neg_frac_eq_neg_m, Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
  simp only [←use_poles, ←pole_split]
  apply pole_sum_zero_of_constraints_and_not_exceptionalSet f m s pr z psum h_z h_cumulativeC h_cyclic

lemma count_eq_sum_of_constraints [DecidableEq F] {t n_s n_p : ℕ}
      {f m : Fin t → F}
      {s : Fin t → Fin (n_s + 1)}
      {pr : Fin t → Fin (n_p + 1)}
      {z : Fin (n_p + 1) → F}
      {psum : Nat → F}
      (k : Fin (n_p + 1))
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0) :
    ∀ x, ↑(Multiset.count x (Multiset.map (useK m pr (↑k) f) Finset.univ.val)) =
      μ (fun i => yieldK m pr (↑k) f i) (fun i => yieldK m pr (↑k) (-m) i) x := by
  intro x
  have h_poles := pole_sum_zero_of_constraints_and_not_exceptionalSet
      f m s pr z psum h_z h_cumulativeC h_cyclic k
  rw [pole_split, add_eq_zero_iff_eq_neg] at h_poles
  simp only [←Finset.sum_neg_distrib, ←neg_frac_eq_neg_m] at h_poles
  have h_m_one : ∀ j ∈ (use_indxs m pr (↑k)), m j = 1 := by
    intro j h_j ; unfold use_indxs at h_j
    simp [List.mem_filter] at h_j
    exact h_j.2
  have h_m_use : ∀ j, (useK m pr (↑k) m j) = 1 := by
    intro j ; unfold useK ; apply h_m_one
    apply List.get_mem
  simp only [h_m_use, Polynomial.C_1] at h_poles
  exact count_eq_of_sum_eq' _ _ _ h_poles x

omit [Fintype F] [Field F] in
lemma count_fin_map_eq_count {t : Nat} (f : Fin t → F) (indxs : List (Fin t)) :
    ∀ x, Multiset.count x (Multiset.map (fun i => fin_map f indxs i) Finset.univ.val) =
        Multiset.count x (indxs.map f) := by
  intro x
  simp only [←Multiset.map_coe, ←map_eq_indxs, fin_map]
  simp

omit [Fintype F] in
lemma count_map_useK_eq_count {t n_p : ℕ} {f m : Fin t → F}  {pr : Fin t → Fin (n_p + 1)} {k : Fin (n_p + 1)} :
    ∀ x, Multiset.count x (Multiset.map (useK m pr (↑k) f) Finset.univ.val) = Multiset.count x ((use_indxs m pr k).map f) := by
  intro x
  have h_useK : fin_map f (use_indxs m pr k) = useK m pr k f := by rfl
  rw [←h_useK]
  apply count_fin_map_eq_count

omit [Fintype F] in
lemma mem_use_i_of_not_mem_sdiff {t n_p : ℕ}
      {m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      {use_i : Finset (Fin t)}
      {yield_i : Finset (Fin t)}
      (h_yield_i : yield_i ⊆ (yield_indxs m pr k).toFinset) :
    ∀ i, i ∈ use_indxs m pr k ∧ i ∉ (indxsK pr k).toFinset \ (use_i ∪ yield_i) → i ∈ use_i := by
  intro i ⟨h_i_in, h_i_nin⟩
  have h_subset := Finset.sdiff_subset_sdiff (use_indxs_subset m pr k) (Finset.Subset.refl (use_i ∪ yield_i))
  replace h_i_nin := Finset.not_mem_subset h_subset h_i_nin
  rw [Finset.mem_sdiff, not_and] at h_i_nin
  have h := h_i_nin (List.mem_toFinset.mpr h_i_in)
  rw [Decidable.not_not, Finset.mem_union] at h
  apply Or.resolve_right h
  by_contra h_mem_y
  apply Finset.notMem_empty i
  rw [←use_yield_indxs_disjoint m pr k]
  apply Finset.mem_inter.mpr ⟨(List.mem_toFinset.mpr h_i_in), Finset.mem_of_subset h_yield_i h_mem_y⟩

omit [Fintype F] in
lemma mem_yield_i_of_not_mem_sdiff {t n_p : ℕ}
      {m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      {use_i : Finset (Fin t)}
      (yield_i : Finset (Fin t))
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset) :
    ∀ i, i ∈ yield_indxs m pr k ∧ i ∉ (indxsK pr k).toFinset \ (use_i ∪ yield_i) → i ∈ yield_i := by
  intro i ⟨h_i_in, h_i_nin⟩
  have h_subset := Finset.sdiff_subset_sdiff (yield_indxs_subset m pr k) (Finset.Subset.refl (use_i ∪ yield_i))
  replace h_i_nin := Finset.not_mem_subset h_subset h_i_nin
  rw [Finset.mem_sdiff, not_and] at h_i_nin
  have h := h_i_nin (List.mem_toFinset.mpr h_i_in)
  rw [Decidable.not_not, Finset.mem_union] at h
  apply Or.resolve_left h
  by_contra h_mem_y
  apply Finset.notMem_empty i
  rw [←use_yield_indxs_disjoint m pr k]
  apply Finset.mem_inter.mpr ⟨Finset.mem_of_subset h_use_i h_mem_y, (List.mem_toFinset.mpr h_i_in)⟩

omit [Fintype F] in
lemma count_use_eq_count_use_i_of_disjoint' {t n_p : ℕ}
      {f m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      {use_i : Finset (Fin t)}
      {yield_i : Finset (Fin t)}
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset)
      (h_yield_i : yield_i ⊆ (yield_indxs m pr k).toFinset)
      {x : F}
      (h_x_i : ∃ i ∈ use_i ∪ yield_i, x = f i)
      (h_disjoint : ∀ j ∈ (indxsK pr k).toFinset \ (use_i ∪ yield_i), x ≠ f j) :
    Multiset.count x (use_i.toList.map (fun i => f i))
      = (Multiset.count x (Multiset.map (useK m pr (↑k) f) Finset.univ.val)) := by
  rw [count_map_useK_eq_count x]
  simp only [←Multiset.map_coe, Multiset.count_map]
  apply congr_arg
  rw [Multiset.Nodup.ext _ _]
  · intro i
    simp only [Multiset.mem_filter, Multiset.mem_coe]
    rw [Finset.mem_toList, ←List.mem_toFinset]
    constructor
    · intro h_i
      exact ⟨Finset.mem_of_subset h_use_i h_i.1, h_i.2⟩
    intro h_i
    rcases h_x_i with ⟨i', h_i'_mem, h_i'_eq⟩
    have h_i_nin := h_disjoint i
    simp only [←h_i.2, ne_eq, not_true_eq_false, imp_false] at h_i_nin
    use mem_use_i_of_not_mem_sdiff h_yield_i i ⟨List.mem_toFinset.mp h_i.1 ,h_i_nin⟩
    exact h_i.2
  · apply Multiset.Nodup.filter
    simp [Finset.nodup]
  apply Multiset.Nodup.filter
  rw [Multiset.coe_nodup]
  exact use_indxs_nodup m pr k

omit [Fintype F] in
lemma filter_x_eq_filter_x_of_disjoint' {t n_p : ℕ}
      {f m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      {use_i : Finset (Fin t)}
      {yield_i : Finset (Fin t)}
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset)
      (h_yield_i : yield_i ⊆ (yield_indxs m pr k).toFinset)
      {x : F}
      (h_x_i : ∃ i ∈ use_i ∪ yield_i, x = f i)
      (h_disjoint : ∀ j ∈ (indxsK pr k).toFinset \ (use_i ∪ yield_i), x ≠ f j) :
    Multiset.filter (fun i => f i = x) (Multiset.map (yield_indxs m pr ↑k).get Finset.univ.val) =
      Multiset.filter (fun i => f i = x) ↑(yield_i.toList) := by
  rw [Multiset.Nodup.ext _ _]
  · intro i
    have : (Multiset.map (yield_indxs m pr ↑k).get Finset.univ.val) = yield_indxs m pr ↑k := by simp
    rw [this]
    suffices h : ∀ i, i ∈ (yield_indxs m pr k) → f i = x → i ∈ yield_i by
      simp only [Multiset.mem_filter, Multiset.mem_coe]
      constructor
      · intro h_i
        rw [Finset.mem_toList]
        exact ⟨h i h_i.1 h_i.2, h_i.2⟩
      rw [Finset.mem_toList, ←List.mem_toFinset]
      intro h_i
      use Finset.mem_of_subset h_yield_i h_i.1
      exact h_i.2
    intro i h_mem_y h_eq
    apply mem_yield_i_of_not_mem_sdiff _ h_use_i i
    use h_mem_y
    by_contra h
    rcases h_x_i with ⟨i', h_i'_mem, h_i'_eq⟩
    have h_i_nin := h_disjoint i h
    rw [h_eq] at h_i_nin
    simp_all
  · apply Multiset.Nodup.filter
    apply Multiset.Nodup.map _ (Finset.nodup _)
    exact List.nodup_iff_injective_get.mp (yield_indxs_nodup m pr k)
  apply Multiset.Nodup.filter
  simp only [Finset.coe_toList, Finset.nodup]

omit [Fintype F] in
lemma sum_mult_yield_eq_count_yield_i_of_disjoint' {t n_p : ℕ}
      {f m : Fin t → F}
      {pr : Fin t → Fin (n_p + 1)}
      {k : Fin (n_p + 1)}
      {use_i : Finset (Fin t)}
      {yield_i : Finset (Fin t)}
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset)
      (h_yield_i : yield_i ⊆ (yield_indxs m pr k).toFinset)
      (h_m : ∀ i ∈ yield_i, m i = -1)
      {x : F}
      (h_x_i : ∃ i ∈ use_i ∪ yield_i, x = f i)
      (h_disjoint : ∀ j ∈ (indxsK pr k).toFinset \ (use_i ∪ yield_i), x ≠ f j) :
    μ (fun i => yieldK m pr (↑k) f i) (fun i => yieldK m pr (↑k) (-m) i) x =
      ↑(Multiset.count x ↑(List.map (fun i => f i) yield_i.toList)) := by
  unfold μ yieldK inv_b
  have : (fun i => (fun i => f ((yield_indxs m pr ↑k).get i)) i = x)
                = (fun i => f i = x) ∘ (fun i => (yield_indxs m pr ↑k).get i) := by rfl
  simp only [this]
  rw [←Function.comp_def, ←Multiset.map_map, ←Multiset.filter_map]
  rw [filter_x_eq_filter_x_of_disjoint' h_use_i h_yield_i h_x_i h_disjoint]
  have h_m_filter : ∀ i ∈ (Multiset.filter (fun i => f i = x) ↑yield_i.toList), (-m) i = 1 := by
    intro i h_i
    simp only [Pi.neg_apply, neg_eq_iff_eq_neg]
    exact h_m i (Finset.mem_toList.mp (Multiset.mem_coe.mp (Multiset.mem_filter.mp h_i).1))
  simp only [Multiset.map_congr rfl h_m_filter]
  simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  simp only [←Multiset.map_coe, Multiset.count_map]
  congr
  simp only [eq_comm]

lemma equal_count_of_multiplicity_one'' {t n_s n_p : ℕ}
      {f m : Fin t → F}
      {s : Fin t → Fin (n_s + 1)}
      {pr : Fin t → Fin (n_p + 1)}
      {z : Fin (n_p + 1) → F}
      {psum : Nat → F}
      (k : Fin (n_p + 1))
      (use_i : Finset (Fin t))
      (yield_i : Finset (Fin t))
      (h_use_i : use_i ⊆ (use_indxs m pr k).toFinset)
      (h_yield_i : yield_i ⊆ (yield_indxs m pr k).toFinset)
      (h_use_count_lt : use_i.card < ringChar F)
      (h_yield_count_lt : yield_i.card < ringChar F)
      (h_z : z ∉ exceptionalSet f m pr)
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      (h_m : ∀ i ∈ yield_i, m i = -1)
      {x : F}
      (h_disjoint : ∀ i ∈ (indxsK pr k).toFinset \ (use_i ∪ yield_i), x ≠ f i) :
    Multiset.count x (yield_i.toList.map fun i => f i) =
      Multiset.count x (use_i.toList.map (fun i => f i)) := by
  by_cases h_i_in : ∃ i ∈ use_i ∪ yield_i, x = f i
  · have h_use_count := count_use_eq_count_use_i_of_disjoint' h_use_i h_yield_i h_i_in h_disjoint
    have h_sum_mult := sum_mult_yield_eq_count_yield_i_of_disjoint' h_use_i h_yield_i h_m h_i_in h_disjoint
    have h_count := count_eq_sum_of_constraints k h_z h_cumulativeC h_cyclic x
    rw [←h_use_count, h_sum_mult] at h_count
    apply Nat.cast_inj_of_lt_char _ _ h_count.symm
    all_goals apply lt_of_le_of_lt (Multiset.count_le_card x _) ; simp
    exact h_yield_count_lt
    exact h_use_count_lt
  simp only [not_exists, not_and] at h_i_in
  simp only [←Multiset.map_coe, Multiset.count_map]
  rw [Multiset.filter_eq_nil.mpr _, Multiset.filter_eq_nil.mpr _]
  all_goals
    intro i h_i
    rw [Multiset.mem_coe, Finset.mem_toList] at h_i
    apply h_i_in i
    simp [h_i]
