import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_lhs_completeness_spec
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_lhs_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
open Mrel
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

open vm_bounded_int_div_rem_known_small_lhs_code
open bounded_int_div_rem_knonw_small_lhs_completeness

variable (mem : Mrel → Mrel) (σ : VmRegisterState)


theorem complete_bounded_int_div_rem_known_small_lhs_VerifyBQ_from_spec
    -- arguments
    (range_check a b b_or_q_bound_rc_value bq q r : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_bounded_int_div_rem_known_small_lhs_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a : val a = mem (exec (σ.ap - 4)))
    (htv_b : val b = mem (exec (σ.ap - 3)))
    (htv_b_or_q_bound_rc_value : val b_or_q_bound_rc_value = mem (exec (σ.ap + 3)))
    (htv_bq : val bq = mem (exec (σ.ap + 4)))
    (htv_q : val q = mem (exec (σ.ap + 5)))
    (htv_r : val r = mem (exec (σ.ap + 6)))
    (h_spec: ∃ (ρ_q ρ_r : ℤ),
               auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 7) (range_check + 3),
    VmRangeChecked loc.rc_vals (range_check + 3) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 14, ap := (σ.ap + 7), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 7) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc ((range_check + 3) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_q, ρ_r, h_rc_b_or_q_bound_rc_value, h_α15, h_α16, h_ρ_q, h_ρ_r⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 7)) with
        | 0 => rc (range_check + 4)
        | 1 => val ρ_q
        | 2 => val ρ_r
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 3)) with
        | 0 => (↑b_or_q_bound_rc_value : ℤ)
        | _ => (0 : ℤ)

  let loc := (⟨3, exec_vals, 1, rc_vals⟩ : LocalAssignment (σ.ap + 7) (range_check + 3))

  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_of_lt mem loc (σ.ap + 6)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_pos mem loc (σ.ap + 7)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_pos mem loc (σ.ap + 8)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_pos mem loc (σ.ap + 9)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_3 := assign_rc_pos mem loc (range_check + 3)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_b_or_q_bound_rc_value
    apply VmRangeChecked_zero
  vm_step_assert_eq hmem14 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_3]
    simp only [←htv_b_or_q_bound_rc_value]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_3]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem15 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_4]
    simp only [←htv_bq]
    simp only [h_ap_minus_3]
    simp only [←htv_b]
    simp only [h_ap_plus_5]
    simp only [←htv_q]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α15]
  vm_step_assert_eq hmem16 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_minus_4]
    simp only [←htv_a]
    simp only [h_ap_plus_4]
    simp only [←htv_bq]
    simp only [h_ap_plus_6]
    simp only [←htv_r]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α16]
  --   range check return value
  vm_step_assert_eq hmem17 hmem, hmem18 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem18 hmem]
    simp only [h_ap_plus_7]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem19 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_8]
    simp only [h_ap_plus_5]
    simp only [←htv_q]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_q]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem20 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_9]
    simp only [h_ap_plus_6]
    simp only [←htv_r]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem21 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_7]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl
  done

theorem complete_bounded_int_div_rem_known_small_lhs_QIsSmall_from_spec
    -- arguments
    (range_check a b b_or_q_bound_rc_value bq q r : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_bounded_int_div_rem_known_small_lhs_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a : val a = mem (exec (σ.ap - 4)))
    (htv_b : val b = mem (exec (σ.ap - 3)))
    (htv_b_or_q_bound_rc_value : val b_or_q_bound_rc_value = mem (exec (σ.ap + 3)))
    (htv_bq : val bq = mem (exec (σ.ap + 4)))
    (htv_q : val q = mem (exec (σ.ap + 5)))
    (htv_r : val r = mem (exec (σ.ap + 6)))
    (h_spec: ∃ (ρ_q ρ_r : ℤ),
               auto_spec_bounded_int_div_rem_known_small_lhs_QIsSmall range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 7) (range_check + 3),
    VmRangeChecked loc.rc_vals (range_check + 3) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 12, ap := (σ.ap + 6), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 7) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc ((range_check + 3) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_q, ρ_r, h_α12, h_block_VerifyBQ⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 7)) with
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 3)) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨0, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 7) (range_check + 3))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_a_ap : val ↑a = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_a]
  have h_b_ap : val ↑b = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b]
  have h_b_or_q_bound_rc_value_ap : val ↑b_or_q_bound_rc_value = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), htv_b_or_q_bound_rc_value]
  have h_bq_ap : val ↑bq = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_bq]
  have h_q_ap : val ↑q = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), htv_q]
  have h_r_ap : val ↑r = Assign mem loc₀ (exec (σ.ap + 6)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 6) (by apply Int.add_lt_add_left ; norm_num1), htv_r]
  have h_VerifyBQ := complete_bounded_int_div_rem_known_small_lhs_VerifyBQ_from_spec
    (Assign mem loc₀) σ range_check a b b_or_q_bound_rc_value bq q r hmem hin_fp h_range_check_ap h_a_ap h_b_ap h_b_or_q_bound_rc_value_ap h_bq_ap h_q_ap h_r_ap ⟨ρ_q, ρ_r, h_block_VerifyBQ⟩

  have h_ap_concat : (σ.ap + 7) = (σ.ap + 7) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 3) = (range_check + 3) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_VerifyBQ with ⟨loc₁, h_rc_VerifyBQ, h_VerifyBQ⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_of_lt mem loc (σ.ap + 6)
    (by apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_VerifyBQ
  vm_step_assert_eq hmem12 hmem, hmem13 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem13 hmem]
    simp only [h_ap_plus_3]
    simp only [←htv_b_or_q_bound_rc_value]
    simp only [h_ap_plus_5]
    simp only [←htv_q]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_bound_minus_limiter_bound] at h_α12
    simp only [h_α12]
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_VerifyBQ
  done

theorem complete_bounded_int_div_rem_known_small_lhs_from_spec
    -- arguments
    (range_check a b : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_bounded_int_div_rem_known_small_lhs_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a : val a = mem (exec (σ.ap - 4)))
    (htv_b : val b = mem (exec (σ.ap - 3)))
    (h_spec: ∃ (ρ_q ρ_r : ℤ),
               auto_spec_bounded_int_div_rem_known_small_lhs range_check a b ρ_q ρ_r)
  -- conclusion
  : ∃ loc : LocalAssignment σ.ap range_check,
    VmRangeChecked loc.rc_vals range_check loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) σ (fun κ τ =>
      τ.ap = σ.ap + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_q, ρ_r, orig_range_check, h_orig_range_check, r_plus_1, b_minus_r_minus_1, bq, q, r, h_rc_q, h_rc_r, h_α2, h_α4, h_rc_b_minus_r_minus_1, q_is_small, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_q_is_small, b_or_q_bound_rc_value, h_α8, h_block_VerifyBQ⟩
    let exec_vals :=
        fun (i : ℤ) =>
          match (i - σ.ap) with
          | 0 => val r_plus_1
          | 1 => val b_minus_r_minus_1
          | 2 => val q_is_small
          | 3 => val b_or_q_bound_rc_value
          | 4 => val bq
          | 5 => val q
          | 6 => val r
          | _ => val 0

    let rc_vals :=
        fun (i : ℤ) =>
          match (i - range_check) with
          | 0 => (↑q : ℤ)
          | 1 => (↑r : ℤ)
          | 2 => (↑b_minus_r_minus_1 : ℤ)
          | _ => (0 : ℤ)

    let loc₀ := (⟨7, exec_vals, 3, rc_vals⟩ : LocalAssignment σ.ap range_check)

    have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 5)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
    have h_a_ap : val ↑a = Assign mem loc₀ (exec (σ.ap - 4)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap - 4) (by apply Int.sub_lt_self ; norm_num1), htv_a]
    have h_b_ap : val ↑b = Assign mem loc₀ (exec (σ.ap - 3)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap - 3) (by apply Int.sub_lt_self ; norm_num1), htv_b]
    have h_b_or_q_bound_rc_value_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 3)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_b_or_q_bound_rc_value_ap : val ↑b_or_q_bound_rc_value = Assign mem loc₀ (exec (σ.ap + 3)) := by
      simp only [h_b_or_q_bound_rc_value_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
    have h_bq_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 4)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_bq_ap : val ↑bq = Assign mem loc₀ (exec (σ.ap + 4)) := by
      simp only [h_bq_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
    have h_q_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 5)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_q_ap : val ↑q = Assign mem loc₀ (exec (σ.ap + 5)) := by
      simp only [h_q_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
    have h_r_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 6)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_r_ap : val ↑r = Assign mem loc₀ (exec (σ.ap + 6)) := by
      simp only [h_r_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
    have h_VerifyBQ := complete_bounded_int_div_rem_known_small_lhs_VerifyBQ_from_spec
      (Assign mem loc₀) σ range_check a b b_or_q_bound_rc_value bq q r hmem hin_fp h_range_check_ap h_a_ap h_b_ap h_b_or_q_bound_rc_value_ap h_bq_ap h_q_ap h_r_ap ⟨ρ_q, ρ_r, h_block_VerifyBQ⟩

    have h_ap_concat : (σ.ap + 7) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
    have h_rc_concat : (range_check + 3) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
    rcases h_VerifyBQ with ⟨loc₁, h_rc_VerifyBQ, h_VerifyBQ⟩

    let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

    have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
      (by apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
      (by apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
      (by apply Int.sub_lt_self ; norm_num1)
    have h_ap_plus_0 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat σ.ap
      (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
    have h_ap_plus_1 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 1)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_2 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 2)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_3 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 3)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_4 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 4)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_5 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 5)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
    have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

    use loc
    constructor
    · apply VmRangeChecked_concat
      · apply VmRangeChecked_rec
        · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
          apply h_rc_b_minus_r_minus_1
        apply VmRangeChecked_rec
        · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
          apply h_rc_r
        apply VmRangeChecked_rec
        · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
          apply h_rc_q
        apply VmRangeChecked_zero
      apply h_rc_VerifyBQ
    vm_step_assert_eq hmem0 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_5]
      simp only [h_ap_minus_5]
      simp only [←htv_range_check]
      simp only [h_rc_plus_0]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      apply Mrel.Equiv.refl_val
    vm_step_assert_eq hmem1 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_6]
      simp only [h_ap_minus_5]
      simp only [←htv_range_check]
      simp only [h_rc_plus_1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      apply Mrel.Equiv.refl_val
    vm_step_assert_eq hmem2 hmem, hmem3 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem3 hmem]
      try simp only [add_zero]
      simp only [h_ap_plus_0]
      simp only [h_ap_plus_6]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [one] at h_α2
      simp only [h_α2]
    vm_step_assert_eq hmem4 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_1]
      simp only [h_ap_minus_3]
      simp only [←htv_b]
      try simp only [add_zero]
      simp only [h_ap_plus_0]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α4
      dsimp [Mrel.Equiv]
      simp only [h_α4]
    vm_step_assert_eq hmem5 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_1]
      simp only [h_ap_minus_5]
      simp only [←htv_range_check]
      simp only [h_rc_plus_2]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      apply Mrel.Equiv.refl_val
    vm_step_jnz hmem6 hmem, hmem7 hmem
    -- q_is_small = 0
    swap
    · norm_num1
      simp only [h_ap_plus_2]
      dsimp [exec_vals]
      simp only [Int.add_comm σ.ap 2, Int.add_sub_cancel]
      ring_nf ; simp only [val.injEq, Int.reduceNeg]
      simp only [hc_q_is_small]
      simp only [not_true, false_implies]
    intro _
    vm_step_assert_eq hmem8 hmem, hmem9 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem9 hmem]
      simp only [h_ap_plus_3]
      simp only [h_ap_minus_3]
      simp only [←htv_b]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [u128_bound_minus_limiter_bound] at h_α8
      simp only [h_α8]
    vm_step_jump_imm hmem10 hmem, hmem11 hmem
    rw [assign_concat, concat_exec_num, concat_rc_num]
    simp only [Nat.cast_add]
    try simp only [Nat.cast_zero, Int.zero_add]
    try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
    try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
    norm_num1
    try simp only [←Int.add_assoc]
    apply h_VerifyBQ
  rcases h_spec with ⟨hc_q_is_small, b_or_q_bound_rc_value, h_block_QIsSmall⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - σ.ap) with
        | 0 => val r_plus_1
        | 1 => val b_minus_r_minus_1
        | 2 => val q_is_small
        | 3 => val b_or_q_bound_rc_value
        | 4 => val bq
        | 5 => val q
        | 6 => val r
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | 0 => (↑q : ℤ)
        | 1 => (↑r : ℤ)
        | 2 => (↑b_minus_r_minus_1 : ℤ)
        | _ => (0 : ℤ)

  let loc₀ := (⟨7, exec_vals, 3, rc_vals⟩ : LocalAssignment σ.ap range_check)

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
  have h_a_ap : val ↑a = Assign mem loc₀ (exec (σ.ap - 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 4) (by apply Int.sub_lt_self ; norm_num1), htv_a]
  have h_b_ap : val ↑b = Assign mem loc₀ (exec (σ.ap - 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 3) (by apply Int.sub_lt_self ; norm_num1), htv_b]
  have h_b_or_q_bound_rc_value_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_b_or_q_bound_rc_value_ap : val ↑b_or_q_bound_rc_value = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [h_b_or_q_bound_rc_value_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_bq_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 4)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_bq_ap : val ↑bq = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [h_bq_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_q_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 5)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_q_ap : val ↑q = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [h_q_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 6)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_r_ap : val ↑r = Assign mem loc₀ (exec (σ.ap + 6)) := by
    simp only [h_r_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_QIsSmall := complete_bounded_int_div_rem_known_small_lhs_QIsSmall_from_spec
    (Assign mem loc₀) σ range_check a b b_or_q_bound_rc_value bq q r hmem hin_fp h_range_check_ap h_a_ap h_b_ap h_b_or_q_bound_rc_value_ap h_bq_ap h_q_ap h_r_ap ⟨ρ_q, ρ_r, h_block_QIsSmall⟩

  have h_ap_concat : (σ.ap + 7) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 3) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_QIsSmall with ⟨loc₁, h_rc_QIsSmall, h_QIsSmall⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat σ.ap
    (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 4)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 5)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_b_minus_r_minus_1
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_r
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_q
      apply VmRangeChecked_zero
    apply h_rc_QIsSmall
  vm_step_assert_eq hmem0 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_5]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem1 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_6]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem2 hmem, hmem3 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem3 hmem]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [h_ap_plus_6]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [one] at h_α2
    simp only [h_α2]
  vm_step_assert_eq hmem4 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [h_ap_minus_3]
    simp only [←htv_b]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α4
    dsimp [Mrel.Equiv]
    simp only [h_α4]
  vm_step_assert_eq hmem5 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_2]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_jnz hmem6 hmem, hmem7 hmem
  -- q_is_small ≠ 0
  · norm_num1
    simp only [h_ap_plus_2]
    dsimp [exec_vals]
    simp only [Int.add_comm σ.ap 2, Int.add_sub_cancel]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_q_is_small
    injection h_cond
  intro _
  simp only [assign_prog, hmem7 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_QIsSmall
  done
