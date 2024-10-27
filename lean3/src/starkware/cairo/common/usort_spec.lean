/-
  Specifications file for usort_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.math_spec

open starkware.cairo.common.math
open_locale big_operators

namespace starkware.cairo.common.usort

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

instance F_inhabited : inhabited F := ⟨0⟩

-- End of automatically generated prelude.

lemma rc_mul_bound : 2 ^ 50 * (1 + rc_bound F) < PRIME :=
begin
  apply lt_of_le_of_lt _ (show 2 ^50 * (1 + 2 ^ 128) < PRIME, by { rw [PRIME], norm_num1}),
  apply nat.mul_le_mul, norm_num1, apply nat.add_le_add_left, exact (rc_bound_hyp F),
end

lemma rc_mul_n_bound {n : ℕ} (h : n < 2 ^ 50) : n * rc_bound F < PRIME :=
begin
  apply lt_of_le_of_lt _ (show 2 ^50 * 2 ^ 128 < PRIME, by { rw [PRIME], norm_num1}),
  apply nat.mul_le_mul, exact le_of_lt h, exact (rc_bound_hyp F)
end

-- Maps a pointer and a length into a list of field elements.
def array_to_list (mem : F → F) : F → ℕ → list F
| _ 0 := []
| array (n + 1) := (mem array) :: array_to_list (array + 1) n

lemma array_to_list_singleton_append (mem : F → F) (n : ℕ) (array : F) :
  array_to_list mem array (n + 1) = array_to_list mem array 1 ++ array_to_list mem (array + 1) n :=
begin
  dsimp [array_to_list], refl
end

lemma array_to_list_append (mem: F → F) (m len : ℕ) :
  ∀ array : F,
    array_to_list mem array (m + len) = array_to_list mem array m ++ array_to_list mem (array + ↑m) len :=
begin
  induction m with m ih,
  { intro array, rw [nat.cast_zero, add_zero, zero_add],
    dsimp [array_to_list], refl },
  intro array,
  rw [←nat.add_one], rw [array_to_list_singleton_append mem m array],
  rw [add_assoc, add_comm 1 len, ←add_assoc], rw [array_to_list_singleton_append mem (m + len) array],
  rw [list.append_assoc], apply (list.append_right_inj _).mpr,
  rw [add_comm m 1, nat.cast_add, ←add_assoc, nat.cast_one],
  exact ih (array + 1),
end

lemma array_to_list_mem (mem: F → F) (n : ℕ):
  ∀ (array : F) (m < n), mem (array + ↑m) ∈ array_to_list mem array n :=
begin
  induction n with n ih,
  { intros array m h_mn, exfalso, apply nat.not_lt_zero m, exact h_mn },
  intros array m h_mn, rw [array_to_list_singleton_append mem n], rw [list.mem_append],
  cases m,
  { dsimp [array_to_list], left, left, rw [nat.cast_zero, add_zero] },
  right, rw [nat.succ_eq_add_one, nat.add_comm m 1, nat.cast_add, ←add_assoc, nat.cast_one],
  exact ih (array + 1) m (nat.lt_of_succ_lt_succ h_mn),
end

lemma array_to_list_length {mem: F → F} {n : ℕ} {array : F}:
  (array_to_list mem array n).length = n :=
begin
  revert array,
  induction n with n ih,
  intro array, dsimp [array_to_list], triv,
  intro array, dsimp [array_to_list], rw [ih],
end

lemma list_count_pos_subset (l1 l2 : list F) (counts : list ℕ)
  (h_c_pos : counts.all₂ (λ m, 0 < m))
  (h_c_lt : list.forall₂ (λ (m : ℕ) (x : F), m ≤ l1.count x) counts l2) :
l2 ⊆ l1 :=
begin
  rw [list.subset_def], intros a h_a, rw [←list.one_le_count_iff_mem],
  rcases list.forall₂_iff_nth_le.mp h_c_lt with ⟨h_len, h_nth⟩,
  rcases list.mem_iff_nth_le.mp h_a with ⟨n, h_n, h_a_n⟩,
  rw [←h_a_n], apply nat.succ_le_of_lt,
  apply nat.lt_of_lt_of_le _ (h_nth n (h_len.symm ▸ h_n) h_n),
  exact list.all₂_iff_forall.mp h_c_pos (counts.nth_le n (h_len.symm ▸ h_n)) (list.nth_le_mem _ _ _),
end

lemma filter_subset_finset_eq {l1 l2 : list F} (h_sub : l2 ⊆ l1) :
  finset.filter (λ x, x ∈ l2) l1.to_finset = l2.to_finset :=
begin
  ext, rw [list.mem_to_finset], split,
  { intro h_a, exact (finset.mem_filter.mp h_a).right },
  intro h_a, apply finset.mem_filter.mpr,
  exact ⟨list.mem_to_finset.mpr (h_sub h_a), h_a⟩,
end

lemma list_count_le_subset (l1 l2 : list F) (counts : list ℕ)
  (h_sub : l2 ⊆ l1)
  (h_nodup : l2.nodup)
  (h_c : list.forall₂ (λ (m : ℕ) (x : F), m ≤ l1.count x) counts l2)
  (h_t : l1.length = counts.sum) :
∀ s, s ∈ l1 → s ∈ l2 :=
begin
  intros s h_s,
  by_contradiction h_s_n_l2,
  have h := (list.length_filter_lt_length_iff_exists (λ v, v ∈ l2) l1).mpr ⟨s, h_s, h_s_n_l2⟩,
  apply (lt_iff_not_ge _ _).mp h, rw [h_t],
  have h1 := list.forall₂_map_right_iff.mpr h_c,
  apply le_trans (list.forall₂.sum_le_sum h1),
  rw [←(list.sum_to_finset _ h_nodup)], rw [←(filter_subset_finset_eq h_sub)],
  rw [finset.sum_filter_count_eq_countp _ l1], apply le_of_eq, apply list.countp_eq_length_filter,
end

lemma list_count_eq {l1 : list F} {l2 : list F} {counts : list ℕ}
  (h_sub : l2 ⊆ l1)
  (h_nodup : l2.nodup)
  (h_c : list.forall₂ (λ (m : ℕ) (x : F), m ≤ l1.count x) counts l2)
  (h_t : l1.length = counts.sum) :
list.forall₂ (λ (m : ℕ) (x : F), m = l1.count x) counts l2 :=
begin
  rw [list.forall₂_iff_zip],
  use [list.forall₂.length_eq h_c],
  intros a b h_ab,
  by_contradiction h_ne,
  suffices h_sum_lt :
    (list.map (λ x : (ℕ × F), x.fst) (counts.zip l2)).sum <
    (list.map (λ x : (ℕ × F), list.count x.snd l1) (counts.zip l2)).sum,
  { apply not_lt_of_le _ h_sum_lt, rw [←(list.map_map (λ y : F, list.count y l1) (λ x : (ℕ × F), x.snd) _)],
    rw [←list.unzip_left], rw [←list.unzip_right], rw [list.unzip_zip (list.forall₂.length_eq h_c)], dsimp,
    rw [←h_t], rw [←(list.sum_to_finset _ h_nodup)],
    rw [←(filter_subset_finset_eq h_sub)], rw [finset.sum_filter_count_eq_countp _ l1],
    apply list.countp_le_length,
  },
  rw [list.forall₂_iff_zip, ←prod.forall'] at h_c, simp only [prod.mk.eta] at h_c,
  have h_lt := lt_of_le_of_ne (h_c.right (a,b) h_ab) h_ne,
  apply list.sum_lt_sum,
  { exact h_c.right },
  exact ⟨(a,b), h_ab, h_lt⟩,
end

-- You may change anything in this definition except the name and arguments.
def spec_verify_multiplicity (mem : F → F) (κ : ℕ) (range_check_ptr multiplicity input_len input value ρ_range_check_ptr : F) : Prop :=
  ∀ multiplicity_n ≤ rc_bound F,
    multiplicity = ↑multiplicity_n →
    multiplicity_n < κ ∧
    ∃ input_len_n < (1 + multiplicity_n) * (1 + rc_bound F),
      input_len = ↑input_len_n ∧
      multiplicity_n ≤ (array_to_list mem input input_len_n).count value

/-
-- Function: verify_multiplicity
-/

/- verify_multiplicity autogenerated specification -/

-- Do not change this definition.
def auto_spec_verify_multiplicity (mem : F → F) (κ : ℕ) (range_check_ptr multiplicity input_len input value ρ_range_check_ptr : F) : Prop :=
  ((multiplicity = 0 ∧
    ∃ (κ₁ : ℕ) (range_check_ptr₁ : F), spec_assert_nn mem κ₁ range_check_ptr input_len range_check_ptr₁ ∧
    κ₁ + 5 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr₁) ∨
   (multiplicity ≠ 0 ∧
    ∃ next_item_index : F,
    ∃ (κ₁ : ℕ) (range_check_ptr₁ : F), spec_assert_nn mem κ₁ range_check_ptr next_item_index range_check_ptr₁ ∧
    mem (input + (next_item_index)) = value ∧
    ∃ (κ₂ : ℕ), spec_verify_multiplicity mem κ₂ range_check_ptr₁ (multiplicity - 1) (input_len - next_item_index - 1) (input + ((next_item_index + 1))) value ρ_range_check_ptr ∧
    κ₁ + κ₂ + 16 ≤ κ))

/- verify_multiplicity soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_verify_multiplicity
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr multiplicity input_len input value ρ_range_check_ptr : F)
    (h_auto : auto_spec_verify_multiplicity mem κ range_check_ptr multiplicity input_len input value ρ_range_check_ptr) :
  spec_verify_multiplicity mem κ range_check_ptr multiplicity input_len input value ρ_range_check_ptr :=
begin
  intros multiplicity_n h_multiplicity_bound h_multiplicity,
  have h_lt_p : multiplicity_n < PRIME,
    { apply lt_of_le_of_lt h_multiplicity_bound, rw [PRIME], apply lt_of_le_of_lt (rc_bound_hyp F), norm_num1 },
  rcases h_auto with ⟨h_mult, _, _, ⟨iln, iln_lt, iln_eq⟩, h_k, _⟩ | ⟨h_mult, h_n_zero⟩,
  { -- If multiplicity = 0:
    have h_m_zero : multiplicity_n = 0,
    from PRIME.nat_coe_field_zero h_lt_p h_multiplicity h_mult,
    split, { rw h_m_zero, linarith [h_k] },
    use [iln], split,
    { rw [h_m_zero, add_zero, one_mul], linarith [iln_lt], },
    use [iln_eq],
    rw [h_m_zero], exact nat.zero_le _,
  },

  -- If 0 < multiplicity:
  have one_le_multiplicity_n : 1 ≤ multiplicity_n,
  { cases multiplicity_n,
    { simp [h_multiplicity] at h_mult, contradiction },
    apply nat.succ_le_succ, apply nat.zero_le },
  have multiplicity_n'_bound : multiplicity_n - 1 ≤ rc_bound F,
  { linarith [h_multiplicity_bound] },
  have multiplicity_sub_one : multiplicity - 1 = ↑(multiplicity_n - 1),
  { simp [h_multiplicity, one_le_multiplicity_n] },

  rcases h_n_zero with ⟨skip, _, _, ⟨⟨skip_n, skip_n_bound, h_skip⟩, h_val, k_rec, h_rec, h_k⟩⟩,
  rcases h_rec (multiplicity_n - 1) multiplicity_n'_bound multiplicity_sub_one with
    ⟨h_k_rec, input_len_n', input_len_n'_bound, h_input_len_n', h_rec⟩,

  split, { linarith [h_k_rec, h_k] },

  use input_len_n' + skip_n + 1, split,
  { rw [nat.add_comm 1 multiplicity_n, add_one_mul, add_assoc, add_comm skip_n 1],
    apply add_lt_add_of_lt_of_le, linarith, linarith },

  split,
  { rw [nat.cast_add, nat.cast_add, nat.cast_one, ←h_skip, ←h_input_len_n'], ring },
  rw [add_assoc, add_comm], rw [array_to_list_append mem (skip_n + 1) input_len_n' input],
  rw [list.count_append], rw [nat.cast_add, nat.cast_one, ←h_skip, ←add_assoc],
  have h_1m1 : 1 + (multiplicity_n - 1) = multiplicity_n, from nat.add_sub_of_le one_le_multiplicity_n,
  rw [←h_1m1], apply nat.add_le_add,
  { rw [list.one_le_count_iff_mem], rw [←h_val, h_skip],
    apply array_to_list_mem mem (skip_n + 1) input skip_n, exact lt_add_one skip_n,  },
  rw [add_assoc], exact h_rec,
end

/-
-- Function: verify_usort
-/

def spec_verify_usort (mem : F → F) (κ : ℕ) (range_check_ptr output input_len input total_visited multiplicities prev ρ_range_check_ptr ρ_output : F) : Prop :=
  κ < 2 ^ 50 →
    ∀ (total_visited_n : ℕ) (prev_plus_one_n : ℕ),
      total_visited_n + κ < PRIME →
      total_visited = ↑total_visited_n →
      prev + 1 = ↑prev_plus_one_n →
        ∃ (output_len_n < κ) (out_n : list ℕ) (mult_n : list ℕ) (input_len_n : ℕ),
          ρ_output = output + ↑output_len_n ∧
          out_n.length = output_len_n ∧
          mult_n.length = output_len_n ∧
          input_len = ↑input_len_n ∧
          -- Output (shifted by one) is sorted.
          out_n.map (λ v, ↑v - ↑1) = array_to_list mem output output_len_n ∧
          out_n.chain (λ m n, m < n) prev_plus_one_n ∧
          out_n.all₂ (λ v, v ≤ prev_plus_one_n + output_len_n * rc_bound F) ∧
          -- Multiplicities are correct.
          mult_n.map (λ m, ↑m) = array_to_list mem multiplicities output_len_n ∧
          mult_n.all₂ (λ m, 0 < m ∧ m ≤ rc_bound F) ∧
          list.forall₂
            (λ (m : ℕ) (x : F), m ≤ (array_to_list mem input input_len_n).count x)
            mult_n
            (array_to_list mem output output_len_n) ∧
          -- Bound on the input length.
          input_len_n = total_visited_n + mult_n.sum ∧
          mult_n.sum < κ

/- verify_usort autogenerated specification -/

-- Do not change this definition.
def auto_spec_verify_usort (mem : F → F) (κ : ℕ) (range_check_ptr output input_len input total_visited multiplicities prev ρ_range_check_ptr ρ_output : F) : Prop :=
  ((total_visited = input_len ∧
    6 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr ∧
    ρ_output = output) ∨
   (total_visited ≠ input_len ∧
    ∃ value : F,
    value = mem output ∧
    ∃ output₁ : F, output₁ = output + (1) ∧
    ∃ (κ₁ : ℕ) (range_check_ptr₁ : F), spec_assert_lt mem κ₁ range_check_ptr prev value range_check_ptr₁ ∧
    ∃ multiplicity : F,
    multiplicity = mem multiplicities ∧
    ∃ (κ₂ : ℕ) (range_check_ptr₂ : F), spec_assert_nn mem κ₂ range_check_ptr₁ (multiplicity - 1) range_check_ptr₂ ∧
    ∃ (κ₃ : ℕ) (range_check_ptr₃ : F), spec_verify_multiplicity mem κ₃ range_check_ptr₂ multiplicity input_len input value range_check_ptr₃ ∧
    ∃ (κ₄ : ℕ), spec_verify_usort mem κ₄ range_check_ptr₃ output₁ input_len input (total_visited + multiplicity) (multiplicities + (1)) value ρ_range_check_ptr ρ_output ∧
    κ₁ + κ₂ + κ₃ + κ₄ + 24 ≤ κ))

/- verify_usort soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_verify_usort
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr output input_len input total_visited multiplicities prev ρ_range_check_ptr ρ_output : F)
    (h_auto : auto_spec_verify_usort mem κ range_check_ptr output input_len input total_visited multiplicities prev ρ_range_check_ptr ρ_output) :
  spec_verify_usort mem κ range_check_ptr output input_len input total_visited multiplicities prev ρ_range_check_ptr ρ_output :=
begin
  intros h_k_bound total_visited_n prev_plus_one_n tv_k_bound h_eq_tvn h_eq_ppon,
  rcases h_auto with ⟨h_tv_eq, lt_k, _, h_out⟩ | ⟨h_tv_ne, h_cont⟩,
  { use [0],
    split, { exact lt_of_lt_of_le (show 0 < 6, by norm_num1) lt_k, },
    use [[], [], total_visited_n],
    split, { rwa [nat.cast_zero, add_zero] },
    split, { rw [list.length] },
    split, { rw [list.length] },
    split,  { rwa [←h_tv_eq], },
    split, { rw [list.map_nil _], dsimp [array_to_list], refl, },
    split, { apply list.chain.nil },
    split, { dsimp [list.all₂], triv },
    split, { rw [list.map_nil _], dsimp [array_to_list], refl, },
    split, { dsimp [list.all₂], triv },
    split, { apply list.forall₂_nil_left_iff.mpr, dsimp [array_to_list], refl },
    rw [list.sum_nil],
    split, rw [nat.add_zero],
    linarith,
  },
  rcases h_cont with ⟨value, h_value, out_tail, out_tail_eq, _, _, h_prev_lt, mult, mult_eq, _, _, mult_nn, vm_k, _, h_verify_mult, h_rec_k, h_rec, h_k⟩,
  rcases mult_nn with ⟨mult_n, h_mult_n_lt, h_mult_n_eq⟩,
  rcases h_prev_lt with ⟨pv_n, h_pv_lt, h_pv_eq⟩,

  have h_rec_k_bound : h_rec_k < 2 ^ 50, { linarith [h_k_bound, h_k] },
  have h_mult_eq : mult = ↑(mult_n + 1), { rw [nat.cast_add, nat.cast_one], exact eq_add_of_sub_eq h_mult_n_eq, },
  have h_rec_tvn_eq: total_visited + mult = ↑(total_visited_n + mult_n + 1), { rw [h_mult_eq, h_eq_tvn], norm_cast },

  have h_mult_n_bound : mult_n + 1 ≤ rc_bound F, { exact nat.add_one_le_iff.mpr h_mult_n_lt },
  rcases (h_verify_mult (mult_n + 1) h_mult_n_bound h_mult_eq) with ⟨h_vm_k, vm_iln, vm_iln_lt, vm_iln_eq, vm_mult_le⟩,

  have h_rec_tv_k_bound : total_visited_n + mult_n + 1 + h_rec_k < PRIME,
  { apply nat.lt_trans _ tv_k_bound, rw [add_assoc, add_assoc], apply nat.add_lt_add_left, linarith [h_vm_k], },

  have h_rec_ppon_eq: value + 1 = ↑(prev_plus_one_n + pv_n + 1),
  { rw [nat.cast_add, nat.cast_add, ←h_eq_ppon, h_pv_eq, nat.cast_add], ring },
  have h_rec_ppon_eq': value = ↑(prev_plus_one_n + pv_n),
  { rw [nat.cast_add, nat.cast_one] at h_rec_ppon_eq, exact add_right_cancel h_rec_ppon_eq },

  rcases (h_rec h_rec_k_bound (total_visited_n + mult_n + 1) (prev_plus_one_n + pv_n + 1) h_rec_tv_k_bound h_rec_tvn_eq h_rec_ppon_eq)
  with ⟨r_oln, r_oln_lt, r_out_n, r_mult_n, r_iln, r_oln_eq, r_out_len_eq, r_mult_len_eq, r_iln_eq, r_out_eq, r_out_sorted, r_out_all, r_mult_eq, r_mult_all, h_r_count, h_total, h_mult_sum_lt⟩,
  use [r_oln + 1],
  split, { linarith [h_k, h_rec_k] },
  use [(prev_plus_one_n + pv_n + 1)::r_out_n, (mult_n + 1)::r_mult_n, r_iln],
  split, { rw [out_tail_eq] at r_oln_eq, rwa [nat.add_comm, nat.cast_add, nat.cast_one, ←add_assoc] },
  split, { rw [list.length_cons], rw [r_out_len_eq] },
  split, { rw [list.length_cons], rw [r_mult_len_eq],  },
  split, { exact r_iln_eq },
  split,
  { rw [list.map_cons], rw [array_to_list_singleton_append], rw [r_out_eq, out_tail_eq],  dsimp [array_to_list],
    rw [←h_value], rw [h_rec_ppon_eq'], rw [nat.cast_add, add_sub_cancel] },
  split, { rw [list.chain_cons], split, { linarith }, exact r_out_sorted,  },
  split,
  { rw [list.all₂_cons], split,
    { rw [add_assoc], apply nat.add_le_add_left, apply le_trans (nat.add_one_le_iff.mpr h_pv_lt),
      apply nat.le_mul_of_pos_left, apply nat.lt_of_lt_of_le zero_lt_one, apply nat.le_add_left },
    apply list.all₂_iff_forall.mpr, intros x h_x,
    have r_out_x := (list.all₂_iff_forall.mp r_out_all x h_x),
    apply nat.le_trans r_out_x, rw [add_assoc, add_assoc], apply nat.add_le_add_left, linarith [h_pv_lt] },
  split,
  { rw [list.map_cons], rw [array_to_list_singleton_append], rw [r_mult_eq], dsimp [array_to_list], rw [←mult_eq, h_mult_eq] },
  split,
  { rw [list.all₂_cons], split,
    { simp only [nat.succ_pos', true_and, bool.of_to_bool_iff], apply nat.add_one_le_iff.mpr, exact h_mult_n_lt, },
    exact r_mult_all, },
  split,
  { rw [array_to_list_singleton_append], dsimp [array_to_list], rw [list.forall₂_cons], split,
    {
      have h_r_iln_bound : r_iln < PRIME, { rw [h_total], apply lt_trans _ h_rec_tv_k_bound, linarith [h_mult_sum_lt], },
      have h_vm_iln_bound : vm_iln < PRIME,
      { apply nat.lt_trans vm_iln_lt, refine @nat.lt_of_le_of_lt _ (2 ^ 50 * (1 + rc_bound F)) _ _ rc_mul_bound,
        apply nat.mul_le_mul_right, apply le_trans _ (le_of_lt h_k_bound), linarith [h_k, h_vm_k], },
      have h_iln_eq : r_iln = vm_iln, {
        rw [vm_iln_eq] at r_iln_eq,
        apply PRIME.nat_coe_field_inj h_r_iln_bound h_vm_iln_bound r_iln_eq.symm,
      },
      rwa [h_iln_eq, ←h_value] },
    rw [←out_tail_eq], exact h_r_count,  },
  split,
  { rw [list.sum_cons, h_total], ring },
  { rw [list.sum_cons], linarith [h_mult_sum_lt, h_vm_k] },
end

/-
-- Function: usort
-/

/- usort autogenerated specification -/

-- Do not change this definition.
def auto_spec_usort (mem : F → F) (κ : ℕ) (range_check_ptr input_len input ρ_range_check_ptr ρ_output_len ρ_output ρ_multiplicities : F) : Prop :=
  ∃ output_len : F,
  ∃ output : F,
  ∃ multiplicities : F,
  ∃ output_start : F, output_start = output ∧
  ∃ (κ₁ : ℕ) (range_check_ptr₁ output₁ : F), spec_verify_usort mem κ₁ range_check_ptr output input_len input 0 multiplicities (-1) range_check_ptr₁ output₁ ∧
  κ₁ + 14 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₁ ∧
  ρ_output_len = output₁ - output_start ∧
  ρ_output = output_start ∧
  ρ_multiplicities = multiplicities

-- You may change anything in this definition except the name and arguments.
def spec_usort (mem : F → F) (κ : ℕ) (range_check_ptr input_len input ρ_range_check_ptr ρ_output_len ρ_output ρ_multiplicities : F) : Prop :=
  κ < 2 ^ 50 →
    ∃ (output_len_n < κ) (input_len_n < κ) (out_n : list ℕ) (mult_n : list ℕ),
      out_n.length = output_len_n ∧
      mult_n.length = output_len_n ∧
      input_len = ↑input_len_n ∧
      ρ_output_len = ↑output_len_n ∧
      -- The arrays input and ρ_output have the same set of members.
      (array_to_list mem ρ_output output_len_n).to_finset = (array_to_list mem input input_len_n).to_finset ∧
      -- The natural number representatives of the output are sorted.
      out_n.map (λ v, ↑v) = array_to_list mem ρ_output output_len_n ∧
      out_n.sorted (<) ∧
      out_n.all₂ (λ v, v < PRIME) ∧
      -- Multiplicities are correct.
      mult_n.map (λ m, ↑m) = array_to_list mem ρ_multiplicities output_len_n ∧
      mult_n.all₂ (λ m, 0 < m ∧ m ≤ rc_bound F) ∧
      mult_n = (array_to_list mem ρ_output output_len_n).map (λ x : F, (array_to_list mem input input_len_n).count x)

/- usort soundness theorem -/

lemma out_n_not_zero (ln : list ℕ) : list.chain (λ (m n : ℕ), m < n) 0 ln →  list.all₂ (λ n, 0 < n) ln :=
begin
  intro h, rw [list.chain_iff_pairwise, list.pairwise_cons] at h,
  rw [list.all₂_iff_forall], exact h.1
end

lemma out_n_sorted (ln : list ℕ) : list.chain (λ (m n : ℕ), m < n) 0 ln → (list.map (λ n, n - 1) ln).sorted (<) :=
begin
  intro h, dsimp [list.sorted], rw [list.pairwise_map],
  have : ∀ m n : ℕ, m ∈ ln → n ∈ ln → (m < n → (m -1) < (n - 1)),
  { intros m n h_m h_n, apply nat.pred_lt_pred,
    exact (ne_of_lt (list.all₂_iff_forall.mp (out_n_not_zero ln h) m h_m)).symm },
  apply list.pairwise.imp_of_mem this,
  apply list.pairwise.sublist (list.tail_sublist (0 :: ln)), exact (list.chain_iff_pairwise.mp h)
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_usort
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr input_len input ρ_range_check_ptr ρ_output_len ρ_output ρ_multiplicities : F)
    (h_auto : auto_spec_usort mem κ range_check_ptr input_len input ρ_range_check_ptr ρ_output_len ρ_output ρ_multiplicities) :
  spec_usort mem κ range_check_ptr input_len input ρ_range_check_ptr ρ_output_len ρ_output ρ_multiplicities :=
begin
  intro h_k,
  rcases h_auto
  with ⟨output_len, output, multiplicities, output_s, output_s_eq, k_vu, _, vu_output, verify_usort, h_k_vu, _, ol_eq, o_eq, m_eq⟩,
  have k_uv_bound : k_vu < 2 ^ 50, { by linarith },
  have k_uv_le_p : 0 + k_vu < PRIME, { rw [zero_add], apply lt_trans k_uv_bound, rw [PRIME], norm_num1, },
  rcases (verify_usort k_uv_bound 0 0 k_uv_le_p nat.cast_zero.symm (by { rw [nat.cast_zero], norm_num1 }))
  with ⟨
    vu_oln, vu_oln_bound, vu_out_n, vu_mult_n, vu_iln, vu_out_eq, vu_out_len_eq, vu_mult_len_eq, vu_iln_eq, vu_out_n_eq,
    vu_out_n_chain, vu_out_n_bound, vu_mult_n_eq, vu_mult_n_all, vu_mult_n_forall, vu_iln_eq_sum, vu_mult_sum_bound⟩,

  rw [o_eq, output_s_eq, m_eq],
  rw [zero_add] at vu_iln_eq_sum,
  let out_n := list.map (λ n, n - 1) vu_out_n,

  have vu_out_n_pos : list.all₂ (λ n, 0 < n) vu_out_n, from out_n_not_zero vu_out_n vu_out_n_chain,
  have out_n_eq_out : list.map (λ v, ↑v) out_n = array_to_list mem output vu_oln,
  { rw [←vu_out_n_eq], dsimp [out_n], rw [list.map_map _ _ _],
    apply list.map_eq_map_iff.mpr, intros x h_x, simp,
    have : 0 < x, from list.all₂_iff_forall.mp vu_out_n_pos x h_x,
    rw nat.cast_pred this, },
  have out_n_sorted : out_n.sorted (<), from out_n_sorted vu_out_n vu_out_n_chain,
  have out_n_bound : out_n.all₂ (λ n, n < PRIME),
  { dsimp [out_n], rw [list.all₂_map_iff], apply list.all₂.imp _ vu_out_n_bound, rw [zero_add],
    intros x h_x, rw [function.comp_app], apply lt_of_le_of_lt (nat.pred_le x), apply lt_of_le_of_lt h_x,
    apply rc_mul_n_bound, linarith, },
  have h_l_sub : array_to_list mem output vu_oln ⊆ array_to_list mem input vu_iln,
  { apply list_count_pos_subset (array_to_list mem input vu_iln) (array_to_list mem output vu_oln) vu_mult_n,
    { apply list.all₂.imp _ vu_mult_n_all, intros x h_x, exact h_x.1 }, exact vu_mult_n_forall },
  have h_output_nodup : (array_to_list mem output vu_oln).nodup,
  { rw [←out_n_eq_out], apply list.nodup.map_on,
    { intros x h_x y h_y, apply PRIME.nat_coe_field_inj,
      apply (list.all₂_iff_forall.mp out_n_bound) x h_x, apply (list.all₂_iff_forall.mp out_n_bound) y h_y },
    exact list.sorted.nodup out_n_sorted },
  use vu_oln,
  split, { linarith [vu_oln_bound, h_k_vu] },
  use [vu_iln],
  split, { rw [vu_iln_eq_sum], linarith },
  use [out_n, vu_mult_n],
  split, { rwa [list.length_map _ _], },
  use [vu_mult_len_eq, vu_iln_eq],
  split, { rw [ol_eq, vu_out_eq, output_s_eq], ring, },
  split,
  { rw [list.to_finset.ext_iff], intro x, split,
    { revert x, exact list.subset_def.mp h_l_sub },
      revert x,
      apply list_count_le_subset
        (array_to_list mem input vu_iln)
        (array_to_list mem output vu_oln)
        vu_mult_n
        h_l_sub
        h_output_nodup
        vu_mult_n_forall,
      dsimp [array_to_list], rwa [array_to_list_length] },
  use [out_n_eq_out, out_n_sorted, out_n_bound, vu_mult_n_eq, vu_mult_n_all],
  rw [←list.forall₂_eq_eq_eq], rw [list.forall₂_map_right_iff],
  apply list_count_eq h_l_sub h_output_nodup vu_mult_n_forall,
  rwa [array_to_list_length],
end


end starkware.cairo.common.usort
