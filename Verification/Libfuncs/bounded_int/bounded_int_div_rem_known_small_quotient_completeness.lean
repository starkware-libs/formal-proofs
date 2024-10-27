import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_quotient_completeness_spec
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_quotient_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
open Mrel
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

open vm_bounded_int_div_rem_known_small_quotient_code
open bounded_int_div_rem_known_small_quotient_completeness

variable (mem : Mrel → Mrel) (σ : VmRegisterState)


theorem complete_bounded_int_div_rem_known_small_quotient_from_spec
    -- arguments
    (range_check a b : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_bounded_int_div_rem_known_small_quotient_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a : val a = mem (exec (σ.ap - 4)))
    (htv_b : val b = mem (exec (σ.ap - 3)))
    (h_spec: ∃ (ρ_q ρ_r : ℤ),
               auto_spec_bounded_int_div_rem_known_small_quotient range_check a b ρ_q ρ_r)
  -- conclusion
  : ∃ loc : LocalAssignment σ.ap range_check,
    VmRangeChecked loc.rc_vals range_check loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) σ (fun κ τ =>
      τ.ap = σ.ap + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_q, ρ_r, orig_range_check, h_orig_range_check, r_plus_1, b_minus_r_minus_1, bq, q, r, h_rc_q, h_rc_r, h_α2, h_α4, h_rc_b_minus_r_minus_1, b_or_q_bound_rc_value, h_α6, h_rc_b_or_q_bound_rc_value, h_α9, h_α10, h_ρ_q, h_ρ_r⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - σ.ap) with
        | 0 => val r_plus_1
        | 1 => val b_minus_r_minus_1
        | 2 => val b_or_q_bound_rc_value
        | 3 => val bq
        | 4 => val q
        | 5 => val r
        | 6 => rc (range_check + 4)
        | 7 => val ρ_q
        | 8 => val ρ_r
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | 0 => (↑q : ℤ)
        | 1 => (↑r : ℤ)
        | 2 => (↑b_minus_r_minus_1 : ℤ)
        | 3 => (↑b_or_q_bound_rc_value : ℤ)
        | _ => (0 : ℤ)

  let loc := (⟨9, exec_vals, 4, rc_vals⟩ : LocalAssignment σ.ap range_check)

  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_pos mem loc σ.ap
    (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_pos mem loc (σ.ap + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_pos mem loc (σ.ap + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_pos mem loc (σ.ap + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_pos mem loc (σ.ap + 4)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_pos mem loc (σ.ap + 5)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_pos mem loc (σ.ap + 6)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_pos mem loc (σ.ap + 7)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_pos mem loc (σ.ap + 8)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_0 := assign_rc_pos mem loc (range_check + 0)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_1 := assign_rc_pos mem loc (range_check + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_2 := assign_rc_pos mem loc (range_check + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_3 := assign_rc_pos mem loc (range_check + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_b_or_q_bound_rc_value
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_b_minus_r_minus_1
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_r
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_q
    apply VmRangeChecked_zero
  vm_step_assert_eq hmem0 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_4]
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
    simp only [h_ap_plus_5]
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
    simp only [h_ap_plus_5]
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
  vm_step_assert_eq hmem6 hmem, hmem7 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem7 hmem]
    simp only [h_ap_plus_2]
    simp only [h_ap_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_bound_minus_q_upper] at h_α6
    simp only [h_α6]
  vm_step_assert_eq hmem8 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_2]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_3]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem9 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_3]
    simp only [h_ap_minus_3]
    simp only [←htv_b]
    simp only [h_ap_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α9]
  vm_step_assert_eq hmem10 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_minus_4]
    simp only [←htv_a]
    simp only [h_ap_plus_3]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α10]
  --   range check return value
  vm_step_assert_eq hmem11 hmem, hmem12 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem12 hmem]
    simp only [h_ap_plus_6]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem13 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_7]
    simp only [h_ap_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_q]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem14 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_8]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem15 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_6]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl
  done