import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u128.u128_overflowing_add_completeness_spec
import Verification.Libfuncs.u128.u128_overflowing_add_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
open Mrel
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

open vm_u128_overflowing_add_code
open u128_overflowing_add_completeness

variable (mem : Mrel → Mrel) (σ : VmRegisterState)


theorem complete_u128_overflowing_add_NoOverflow_from_spec
    -- arguments
    (range_check a_plus_b : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u128_overflowing_add_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a_plus_b : val a_plus_b = mem (exec (σ.ap + 1)))
    (h_spec: ∃ (ρ_branch_id ρ_a_plus_b : ℤ),
               auto_spec_u128_overflowing_add_NoOverflow range_check a_plus_b ρ_branch_id ρ_a_plus_b)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 2) (range_check + 0),
    VmRangeChecked loc.rc_vals (range_check + 0) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 8, ap := (σ.ap + 2), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 2) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_a_plus_b, h_rc_a_plus_b, h_ρ_branch_id, h_ρ_a_plus_b⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 2)) with
        | 0 => val 0
        | 1 => rc (range_check + 1)
        | 2 => val ρ_branch_id
        | 3 => val ρ_a_plus_b
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | 0 => (↑a_plus_b : ℤ)
        | _ => (0 : ℤ)

  let loc := (⟨4, exec_vals, 1, rc_vals⟩ : LocalAssignment (σ.ap + 2) (range_check + 0))

  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_pos mem loc (σ.ap + 2)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_pos mem loc (σ.ap + 3)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_pos mem loc (σ.ap + 4)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_pos mem loc (σ.ap + 5)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_0 := assign_rc_pos mem loc (range_check + 0)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_a_plus_b
    apply VmRangeChecked_zero
  vm_step_assert_eq hmem8 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [←htv_a_plus_b]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    simp only [h_rc_plus_0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_advance_ap hmem9 hmem, hmem10 hmem
  --   range check return value
  vm_step_assert_eq hmem11 hmem, hmem12 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem12 hmem]
    simp only [h_ap_plus_3]
    simp only [h_ap_minus_5]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem13 hmem, hmem14 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem14 hmem]
    simp only [h_ap_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_branch_id]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem15 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_5]
    simp only [h_ap_plus_1]
    simp only [←htv_a_plus_b]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_a_plus_b]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem16 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_3]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl

theorem complete_u128_overflowing_add_from_spec
    -- arguments
    (range_check a b : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u128_overflowing_add_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 5)))
    (htv_a : val a = mem (exec (σ.ap - 4)))
    (htv_b : val b = mem (exec (σ.ap - 3)))
    (h_spec: ∃ (ρ_branch_id ρ_a_plus_b : ℤ),
               auto_spec_u128_overflowing_add range_check a b ρ_branch_id ρ_a_plus_b)
  -- conclusion
  : ∃ loc : LocalAssignment σ.ap range_check,
    VmRangeChecked loc.rc_vals range_check loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) σ (fun κ τ =>
      τ.ap = σ.ap + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 3)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_a_plus_b, orig_range_check, h_orig_range_check, no_overflow, a_plus_b, h_a_plus_b, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_no_overflow, wrapping_a_plus_b, h_wrapping_a_plus_b, h_rc_wrapping_a_plus_b, h_ρ_branch_id, h_ρ_a_plus_b⟩
    let exec_vals :=
        fun (i : ℤ) =>
          match (i - σ.ap) with
          | 0 => val no_overflow
          | 1 => val a_plus_b
          | 2 => val wrapping_a_plus_b
          | 3 => rc (range_check + 1)
          | 4 => val ρ_branch_id
          | 5 => val ρ_a_plus_b
          | _ => val 0

    let rc_vals :=
        fun (i : ℤ) =>
          match (i - range_check) with
          | 0 => (↑wrapping_a_plus_b : ℤ)
          | _ => (0 : ℤ)

    let loc := (⟨6, exec_vals, 1, rc_vals⟩ : LocalAssignment σ.ap range_check)

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
    have h_rc_plus_0 := assign_rc_pos mem loc (range_check + 0)
      (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

    use loc
    constructor
    · apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_wrapping_a_plus_b
      apply VmRangeChecked_zero
    vm_step_assert_eq hmem0 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_1]
      simp only [h_ap_minus_4]
      simp only [←htv_a]
      simp only [h_ap_minus_3]
      simp only [←htv_b]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [h_a_plus_b]
    vm_step_jnz hmem1 hmem, hmem2 hmem
    -- no_overflow = 0
    swap
    · norm_num1
      try simp only [add_zero]
      simp only [h_ap_plus_0]
      dsimp [exec_vals]
      simp only [Int.sub_self]
      ring_nf ; simp only [val.injEq, Int.reduceNeg]
      simp only [hc_no_overflow]
      simp only [not_true, false_implies]
    intro _
    vm_step_assert_eq hmem3 hmem, hmem4 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem4 hmem]
      simp only [h_ap_plus_2]
      simp only [h_ap_plus_1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      rw [Int.eq_sub_emod_iff_add_emod_eq] at h_wrapping_a_plus_b
      dsimp [Mrel.Equiv]
      simp only [u128_limit] at h_wrapping_a_plus_b
      simp only [h_wrapping_a_plus_b]
    vm_step_assert_eq hmem5 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_2]
      simp only [h_ap_minus_5]
      simp only [←htv_range_check]
      simp only [h_rc_plus_0]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      apply Mrel.Equiv.refl_val
    vm_step_jump_imm hmem6 hmem, hmem7 hmem
    --   range check return value
    vm_step_assert_eq hmem17 hmem, hmem18 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem18 hmem]
      simp only [h_ap_plus_3]
      simp only [h_ap_minus_5]
      simp only [←htv_range_check]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      apply Mrel.Equiv.refl_rc
    vm_step_assert_eq hmem19 hmem, hmem20 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem20 hmem]
      simp only [h_ap_plus_4]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      simp only [h_ρ_branch_id]
      apply Mrel.Equiv.refl_val
    vm_step_assert_eq hmem21 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_5]
      simp only [h_ap_plus_2]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      simp only [h_ρ_a_plus_b]
      apply Mrel.Equiv.refl_val
    apply ret_returns
    apply hmem22 hmem
    constructor
    · vm_arith_simps
    simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
    simp only [add_sub_assoc] ; norm_num1
    simp only [h_ap_plus_3]
    try dsimp [exec_vals, rc_vals]
    try ring_nf
    try rfl
  rcases h_spec with ⟨hc_no_overflow, h_block_NoOverflow⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - σ.ap) with
        | 0 => val no_overflow
        | 1 => val a_plus_b
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨2, exec_vals, 0, rc_vals⟩ : LocalAssignment σ.ap range_check)

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
  have h_a_plus_b_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_a_plus_b_ap : val ↑a_plus_b = Assign mem loc₀ (exec (σ.ap + 1)) := by
    simp only [h_a_plus_b_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_NoOverflow := complete_u128_overflowing_add_NoOverflow_from_spec
    (Assign mem loc₀) σ range_check a_plus_b hmem hin_fp h_range_check_ap h_a_plus_b_ap ⟨ρ_branch_id, ρ_a_plus_b, h_block_NoOverflow⟩

  have h_ap_concat : (σ.ap + 2) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 0) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_NoOverflow with ⟨loc₁, h_rc_NoOverflow, h_NoOverflow⟩

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

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_NoOverflow
  vm_step_assert_eq hmem0 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [h_ap_minus_4]
    simp only [←htv_a]
    simp only [h_ap_minus_3]
    simp only [←htv_b]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_a_plus_b]
  vm_step_jnz hmem1 hmem, hmem2 hmem
  -- no_overflow ≠ 0
  · norm_num1
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    dsimp [exec_vals]
    simp only [Int.sub_self]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_no_overflow
    injection h_cond
  intro _
  simp only [assign_prog, hmem2 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_NoOverflow
  done
