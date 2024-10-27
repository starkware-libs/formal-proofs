import Verification.Libfuncs.u64.u64_overflowing_add_soundness_spec
import Verification.Libfuncs.u64.u64_overflowing_add_code

namespace u64_overflowing_add_soundness
open u64_overflowing_add_code

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)

theorem auto_sound_u64_overflowing_add
  -- arguments
  (range_check a b : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u64_overflowing_add_code σ.pc)
  -- input arguments on the stack
  (_ : range_check = mem (σ.fp - 5))
  (hin_a : a = mem (σ.fp - 4))
  (hin_b : b = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    ∃ μ ≤ κ, RcEnsures mem (rcBound F) μ (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_u64_overflowing_add a b (mem (τ.ap - 2)) (mem (τ.ap - 1)))) := by
  apply ensures_of_ensuresb; intro νbound
  -- let
  -- tempvar no_overflow
  mkdef hl_no_overflow : no_overflow = mem σ.ap
  -- let
  mkdef hl_deferred_a_plus_b : deferred_a_plus_b = a + b
  -- jump to NoOverflow if no_overflow != 0
  step_jnz hmem0 hmem, hmem1 hmem with hcond0 hcond0
  · -- no_overflow = 0
    have a0 : no_overflow = 0 := by simp only [hl_no_overflow]; exact hcond0
    -- tempvar temp_a_plus_b
    step_assert_eq hmem2 hmem with tv_temp_a_plus_b
    mkdef hl_temp_a_plus_b : temp_a_plus_b = deferred_a_plus_b
    have htv_temp_a_plus_b : temp_a_plus_b = mem (σ.ap + 1) := by
      rw [hl_temp_a_plus_b, hl_deferred_a_plus_b, hin_a, hin_b]; exact tv_temp_a_plus_b.symm
    -- tempvar fixed_a_plus_b
    step_assert_eq hmem3 hmem, hmem4 hmem with tv_fixed_a_plus_b
    mkdef hl_fixed_a_plus_b : fixed_a_plus_b = temp_a_plus_b - u64Limit
    have htv_fixed_a_plus_b : fixed_a_plus_b = mem (σ.ap + 2) := by
      rw [hl_fixed_a_plus_b, htv_temp_a_plus_b]
      rw [sub_eq_iff_eq_add]
      norm_num1
      exact tv_fixed_a_plus_b
    -- range check for fixed_a_plus_b
    step_assert_eq hmem5 hmem with rc_fixed_a_plus_b
    step_jump_imm hmem6 hmem, hmem7 hmem
    -- return values
    --   range check return value
    step_assert_eq hmem19 hmem, hmem20 hmem with ret_range_check₁
    step_assert_eq hmem21 hmem, hmem22 hmem with ret_branch_id
    step_assert_eq hmem23 hmem with ret_a_plus_b
    step_ret hmem24 hmem
    step_done
    use_only rfl, rfl
    -- range check condition
    use_only (1 + 0); constructor; norm_num1
    constructor
    · arith_simps; exact ret_range_check₁
    intro rc_h_range_check
    have rc_h_range_check' := rangeChecked_add_right rc_h_range_check
    suffices auto_spec : auto_spec_u64_overflowing_add a b _ _ by
      apply sound_u64_overflowing_add; apply auto_spec
    use_only no_overflow
    use_only deferred_a_plus_b, hl_deferred_a_plus_b
    left
    use_only a0
    use_only fixed_a_plus_b, hl_temp_a_plus_b ▸ hl_fixed_a_plus_b
    rc_app rc_h_range_check' 0 htv_fixed_a_plus_b rc_fixed_a_plus_b
    simp only
    arith_simps
    use_only ret_branch_id
    exact htv_fixed_a_plus_b ▸ ret_a_plus_b
  -- no_overflow ≠ 0
  have a0 : no_overflow ≠ 0 := by simp only [hl_no_overflow]; exact hcond0
  -- tempvar temp_fixed_a_plus_b
  mkdef hl_temp_fixed_a_plus_b : temp_fixed_a_plus_b = mem (σ.ap + 1)
  -- tempvar a_plus_b
  step_assert_eq hmem8 hmem with tv_a_plus_b
  mkdef hl_a_plus_b : a_plus_b = deferred_a_plus_b
  have htv_a_plus_b : a_plus_b = mem (σ.ap + 2) := by
    rw [hl_a_plus_b, hl_deferred_a_plus_b, hin_a, hin_b]
    exact tv_a_plus_b.symm
  -- assert
  step_assert_eq hmem9 hmem, hmem10 hmem with ha9
  have a9 : temp_fixed_a_plus_b = a_plus_b + (u128Limit - u64Limit) := by
    rw [hl_temp_fixed_a_plus_b, htv_a_plus_b]
    norm_num1
    exact ha9
  -- range check for temp_fixed_a_plus_b
  step_assert_eq hmem11 hmem with rc_temp_fixed_a_plus_b
  -- return values
  --   range check return value
  step_assert_eq hmem12 hmem, hmem13 hmem with ret_range_check₁
  step_assert_eq hmem14 hmem, hmem15 hmem with ret_branch_id
  step_assert_eq hmem16 hmem with ret_a_plus_b
  step_jump_imm hmem17 hmem, hmem18 hmem
  step_ret hmem24 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  use_only (1 + 0); constructor; norm_num1
  constructor
  · arith_simps; exact ret_range_check₁
  intro rc_h_range_check
  have rc_h_range_check' := rangeChecked_add_right rc_h_range_check
  suffices auto_spec : auto_spec_u64_overflowing_add a b _ _ by
    apply sound_u64_overflowing_add; apply auto_spec
  use_only no_overflow
  use_only deferred_a_plus_b, hl_deferred_a_plus_b
  right
  use_only a0
  rw [← hl_a_plus_b, add_sub_assoc, ← a9]
  rc_app rc_h_range_check' 0 hl_temp_fixed_a_plus_b rc_temp_fixed_a_plus_b
  simp only
  arith_simps
  use_only ret_branch_id
  exact htv_a_plus_b ▸ ret_a_plus_b

end u64_overflowing_add_soundness