import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u64.u64_try_from_felt252_soundness_spec
import Verification.Libfuncs.u64.u64_try_from_felt252_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u64_try_from_felt252_code

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u64_try_from_felt252_IsSmall
  -- arguments
  (range_check value : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u64_try_from_felt252_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 4))
  (htv_value : value = mem (σ.fp - 3))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 18, ap := σ.ap + 1, fp := σ.fp }
    (fun κ τ =>
    2 ≤ κ ∧ RcEnsures mem (rcBound F) 2 (mem (σ.fp - 4)) (mem (τ.ap - 3))
      (auto_spec_u64_try_from_felt252_IsSmall κ range_check value (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- range check for value
  step_assert_eq hmem18 hmem with rc_value
  -- tempvar value_upper_limit
  step_assert_eq hmem19 hmem, hmem20 hmem with tv_value_upper_limit
  mkdef hl_value_upper_limit : value_upper_limit = value + fixer_limit
  have htv_value_upper_limit : value_upper_limit = mem (σ.ap + 1) := by
    rw [hl_value_upper_limit, htv_value, fixer_limit, tv_value_upper_limit]
  -- range check for value_upper_limit
  step_assert_eq hmem21 hmem with rc_value_upper_limit
  -- return values
  step_advance_ap hmem22 hmem, hmem23 hmem
  --   range check return value
  step_assert_eq hmem24 hmem, hmem25 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 2
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem26 hmem, hmem27 hmem with ret_branch_id
  step_assert_eq hmem28 hmem with ret_value
  step_jump_imm hmem29 hmem, hmem30 hmem
  step_ret hmem37 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  rc_app rc_h_range_check 0 htv_value rc_value

  use_only value_upper_limit, hl_value_upper_limit
  rc_app rc_h_range_check 1 htv_value_upper_limit rc_value_upper_limit

  arith_simps
  use_only ret_branch_id
  rw [htv_value] ; exact ret_value
  done

theorem auto_sound_u64_try_from_felt252
  -- arguments
  (range_check value : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u64_try_from_felt252_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 4))
  (htv_value : value = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    ∃ μ ≤ κ, 2 ≤ μ ∧ RcEnsures mem (rcBound F) μ (mem (σ.fp - 4)) (mem (τ.ap - 3))
      (spec_u64_try_from_felt252 κ range_check value (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 4) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar is_small
  mkdef hl_is_small : is_small = mem σ.ap
  have htv_is_small : is_small = mem σ.ap := by
    exact hl_is_small
  -- jump to IsSmall if is_small != 0
  step_jnz hmem0 hmem, hmem1 hmem with hcond0 hcond0
  ·
    -- is_small = 0
    have a0 : is_small = 0 := by simp only [htv_is_small]; exact hcond0
    -- tempvar shifted_value
    step_assert_eq hmem2 hmem, hmem3 hmem with tv_shifted_value
    mkdef hl_shifted_value : shifted_value = value - limit
    have htv_shifted_value : shifted_value = mem (σ.ap + 1) := by
      rw [hl_shifted_value, htv_value, limit, tv_shifted_value, add_sub_cancel_right]
    -- tempvar x_part
    mkdef hl_x_part : x_part = mem (σ.ap + 4)
    have htv_x_part : x_part = mem (σ.ap + 4) := by
      exact hl_x_part
    -- tempvar x
    mkdef hl_x : x = mem (σ.ap + 2)
    have htv_x : x = mem (σ.ap + 2) := by
      exact hl_x
    -- assert
    step_assert_eq hmem4 hmem, hmem5 hmem with ha4
    have a4 : x_part = x * a_imm := by
      rw [htv_x_part, htv_x, a_imm] ; exact ha4
    -- tempvar y
    mkdef hl_y : y = mem (σ.ap + 3)
    have htv_y : y = mem (σ.ap + 3) := by
      exact hl_y
    -- assert
    step_assert_eq hmem6 hmem with ha6
    have a6 : shifted_value = x_part + y := by
      rw [htv_shifted_value, htv_x_part, htv_y] ; exact ha6
    -- range check for y
    step_assert_eq hmem7 hmem with rc_y
    -- tempvar y_fixed
    mkdef hl_y_fixed : y_fixed = mem (σ.ap + 5)
    have htv_y_fixed : y_fixed = mem (σ.ap + 5) := by
      exact hl_y_fixed
    -- assert
    step_assert_eq hmem8 hmem, hmem9 hmem with ha8
    have a8 : y_fixed = y + b_imm_fix := by
      rw [htv_y_fixed, htv_y, b_imm_fix] ; exact ha8
    -- range check for y_fixed
    step_assert_eq hmem10 hmem with rc_y_fixed
    -- range check for x
    step_assert_eq hmem11 hmem with rc_x
    -- tempvar diff
    mkdef hl_diff : diff = mem (σ.ap + 6)
    have htv_diff : diff = mem (σ.ap + 6) := by
      exact hl_diff
    -- assert
    step_assert_eq hmem12 hmem, hmem13 hmem with ha12
    have a12 : diff = x - u128_limit_minus_1 := by
      rw [htv_diff, htv_x, u128_limit_minus_1, ha12, add_sub_cancel_right]
    -- jump to Done if diff != 0
    step_jnz hmem14 hmem, hmem15 hmem with hcond14 hcond14
    ·
      -- diff = 0
      have a14 : diff = 0 := by simp only [htv_diff]; exact hcond14
      -- fail
      step_assert_eq hmem16 hmem, hmem17 hmem with ha_fail
      exfalso; apply zero_ne_one (add_left_cancel (Eq.trans _ ha_fail)); rw [add_zero]
      done
    -- diff ≠ 0
    have a14 : diff ≠ 0 := by simp only [htv_diff]; exact hcond14
    -- return values
    --   range check return value
    step_assert_eq hmem31 hmem, hmem32 hmem with ret_range_check₁
    mkdef hl_range_check₁ : range_check₁ = range_check + 3
    let htv_range_check₁ : range_check₁ = _ := by
      apply Eq.symm; apply Eq.trans ret_range_check₁
      simp only [hl_range_check₁, htv_range_check]
    step_assert_eq hmem33 hmem, hmem34 hmem with ret_branch_id
    step_assert_eq hmem35 hmem, hmem36 hmem with ret_value
    step_ret hmem37 hmem
    step_done
    use_only rfl, rfl
    -- range check condition
    use_only 3
    constructor
    norm_num1
    constructor ; norm_num1
    constructor
    · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u64_try_from_felt252 _ range_check value _ _ by
      apply sound_u64_try_from_felt252 ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only is_small
    left
    use_only a0
    use_only shifted_value, hl_shifted_value
    use_only x_part
    use_only x
    use_only a4
    use_only y
    use_only a6
    rc_app rc_h_range_check 0 htv_y rc_y

    use_only y_fixed
    use_only a8
    rc_app rc_h_range_check 1 htv_y_fixed rc_y_fixed

    rc_app rc_h_range_check 2 htv_x rc_x

    use_only diff
    use_only a12
    right
    use_only a14
    arith_simps
    exact ret_branch_id
    done
  -- is_small ≠ 0
  have a0 : is_small ≠ 0 := by simp only [htv_is_small]; exact hcond0
  arith_simps
  apply ensuresbRet_trans (auto_sound_u64_try_from_felt252_IsSmall mem σ
    range_check value
    hmem
    htv_range_check
    htv_value
    νbound)
  intros κ_IsSmall _ h_IsSmall
  rcases h_IsSmall with ⟨rc_m_le_IsSmall, hblk_range_check_ptr, h_IsSmall⟩
  -- range check condition
  use_only 2
  constructor
  apply le_trans rc_m_le_IsSmall (Nat.le_add_right _ _)
  constructor ; norm_num1
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u64_try_from_felt252 _ range_check value _ _ by
    apply sound_u64_try_from_felt252 ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only is_small
  right
  use_only a0
  use_only κ_IsSmall
  apply h_IsSmall rc_h_range_check
  done
