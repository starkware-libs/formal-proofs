import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u128.u128_sqrt_completeness_spec
import Verification.Libfuncs.u128.u128_sqrt_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
open Mrel
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

open vm_u128_sqrt_code
open u128_sqrt_completeness

variable (mem : Mrel → Mrel) (σ : VmRegisterState)


theorem complete_u128_sqrt_from_spec
    -- arguments
    (range_check value : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u128_sqrt_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 4)))
    (htv_value : val value = mem (exec (σ.ap - 3)))
    (h_spec: ∃ (ρ_root : ℤ),
               auto_spec_u128_sqrt range_check value ρ_root)
  -- conclusion
  : ∃ loc : LocalAssignment σ.ap range_check,
    VmRangeChecked loc.rc_vals range_check loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) σ (fun κ τ =>
      τ.ap = σ.ap + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 2)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_root, orig_range_check, h_orig_range_check, fixed_root, root_squared, value_minus_root_squared, root_times_two, diff, root, h_α0, h_rc_root, h_rc_fixed_root, h_α4, h_α5, h_rc_value_minus_root_squared, h_α7, h_α8, h_rc_diff, h_ρ_root⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - σ.ap) with
        | 0 => val fixed_root
        | 1 => val root_squared
        | 2 => val value_minus_root_squared
        | 3 => val root_times_two
        | 4 => val diff
        | 5 => val root
        | 6 => rc (range_check + 4)
        | 7 => val ρ_root
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | 0 => (↑root : ℤ)
        | 1 => (↑fixed_root : ℤ)
        | 2 => (↑value_minus_root_squared : ℤ)
        | 3 => (↑diff : ℤ)
        | _ => (0 : ℤ)

  let loc := (⟨8, exec_vals, 4, rc_vals⟩ : LocalAssignment σ.ap range_check)

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
      apply h_rc_diff
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_value_minus_root_squared
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_fixed_root
    apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_root
    apply VmRangeChecked_zero
  vm_step_assert_eq hmem0 hmem, hmem1 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem1 hmem]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u125_upper_fixer] at h_α0
    simp only [h_α0]
  vm_step_assert_eq hmem2 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_5]
    simp only [h_ap_minus_4]
    simp only [←htv_range_check]
    simp only [h_rc_plus_0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem3 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [h_ap_minus_4]
    simp only [←htv_range_check]
    simp only [h_rc_plus_1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem4 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α4]
  vm_step_assert_eq hmem5 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_2]
    simp only [h_ap_minus_3]
    simp only [←htv_value]
    simp only [h_ap_plus_1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α5
    dsimp [Mrel.Equiv]
    simp only [h_α5]
  vm_step_assert_eq hmem6 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_2]
    simp only [h_ap_minus_4]
    simp only [←htv_range_check]
    simp only [h_rc_plus_2]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem7 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_3]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α7]
  vm_step_assert_eq hmem8 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_4]
    simp only [h_ap_plus_3]
    simp only [h_ap_plus_2]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α8
    dsimp [Mrel.Equiv]
    simp only [h_α8]
  vm_step_assert_eq hmem9 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_4]
    simp only [h_ap_minus_4]
    simp only [←htv_range_check]
    simp only [h_rc_plus_3]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  --   range check return value
  vm_step_assert_eq hmem10 hmem, hmem11 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem11 hmem]
    simp only [h_ap_plus_6]
    simp only [h_ap_minus_4]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem12 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_7]
    simp only [h_ap_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_root]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem13 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_6]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl
  done
