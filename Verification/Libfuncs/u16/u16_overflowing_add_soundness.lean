import Verification.Libfuncs.u16.u16_overflowing_add_soundness_spec
import Verification.Libfuncs.u16.u16_overflowing_add_code

namespace u16_overflowing_add_soundness
open u16_overflowing_add_code

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)

theorem auto_sound_u16_overflowing_add
  -- arguments
  (range_check_ptr a b : F)
  -- code is in memory at s.pc
  (hmem : MemAt mem u16_overflowing_add_code σ.pc)
  -- input arguments on the stack
  (_ : range_check_ptr = mem (σ.fp - 5))
  (hin_a : a = mem (σ.fp - 4))
  (hin_b : b = mem (σ.fp - 3)) :
    -- conclusion
  EnsuresRet mem σ fun κ τ =>
    ∃ μ ≤ κ, RcEnsures mem (rcBound F) μ (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_u16_overflowing_add a b (mem (τ.ap - 2)) (mem (τ.ap - 1))) := by
  apply ensures_of_ensuresb; intro νbound
  -- tempvar no_overflow
  mkdef hl_no_overflow : no_overflow = mem σ.ap
  -- let deferred_a_plus_b = a + b
  mkdef hl_deferred_a_plus_b : deferred_a_plus_b = a + b
  -- jump NoOverflow if no_overflow != 0;
  step_jnz hmem0 hmem, hmem1 hmem with hcond hcond
  · -- no_overflow == 0
    have a0 : no_overflow = 0 := by simp only [hl_no_overflow, hcond]
    -- tempvar temp_a_plus_b
    step_assert_eq hmem2 hmem with tv_temp_a_plus_b
    mkdef hl_temp_a_plus_b : temp_a_plus_b = deferred_a_plus_b
    let htv_temp_a_plus_b: temp_a_plus_b = _ := by
      apply Eq.symm; apply Eq.trans tv_temp_a_plus_b
      simp only [hl_temp_a_plus_b, hin_a, hin_b, hl_deferred_a_plus_b]
    -- tempvar a_plus_b
    step_assert_eq hmem3 hmem, hmem4 hmem with tv_fixed_a_plus_b
    mkdef hl_fixed_a_plus_b : fixed_a_plus_b = temp_a_plus_b - u16Limit
    have htv_fixed_a_plus_b: fixed_a_plus_b = mem (σ.ap + 2) := by
      simp only [hl_fixed_a_plus_b, htv_temp_a_plus_b, tv_fixed_a_plus_b]; rw [u16Limit]; arith_simps
    -- range check
    step_assert_eq hmem5 hmem with rc_check
    step_jump_imm hmem6 hmem, hmem7 hmem
    -- return range check
    step_assert_eq hmem19 hmem, hmem20 hmem with tv_range_check_ptr₁
    -- return values
    step_assert_eq hmem21 hmem, hmem22 hmem with ret_overflow
    step_assert_eq hmem23 hmem with ret_add
    step_ret hmem24 hmem
    step_done
    use_only rfl, rfl
    -- range check condition
    use_only (1 + 0)
    constructor
    · norm_num1
    constructor
    · arith_simps
      exact tv_range_check_ptr₁
    intro rc_h_range_check_ptr
    have rc_h_range_check_ptr' := rangeChecked_add_right rc_h_range_check_ptr
    suffices auto_spec: auto_spec_u16_overflowing_add a b _ _ by
      apply sound_u16_overflowing_add; apply auto_spec
    use_only no_overflow
    use_only deferred_a_plus_b, hl_deferred_a_plus_b
    left
    use_only a0
    use_only temp_a_plus_b, hl_temp_a_plus_b
    use_only fixed_a_plus_b, hl_fixed_a_plus_b
    rc_app rc_h_range_check_ptr' 0 htv_fixed_a_plus_b rc_check
    arith_simps
    use_only ret_overflow
    simp only [htv_fixed_a_plus_b]
    exact ret_add
  -- no_overflow != 0
  have a0 : no_overflow ≠ 0 := by simp only [hl_no_overflow]; exact hcond
  -- tempvar temp_fixed_a_plus_b
  mkdef hl_temp_fixed_a_plus_b : temp_fixed_a_plus_b = mem (σ.ap + 1)
  -- tempvar a_plus_b
  step_assert_eq hmem8 hmem with tv_a_plus_b
  mkdef hl_a_plus_b : a_plus_b = deferred_a_plus_b
  let htv_a_plus_b : a_plus_b = _ := by
    apply Eq.symm; apply Eq.trans tv_a_plus_b
    simp only [hl_a_plus_b, hin_a, hin_b, hl_deferred_a_plus_b]
  -- assert temp_fixed_a_plus_b = a_plus_b + limit_fixer;
  step_assert_eq hmem9 hmem, hmem10 hmem with ha9
  have a9 : temp_fixed_a_plus_b = a_plus_b + u128Limit - u16Limit := by
    rw [u128Limit, u16Limit, htv_a_plus_b, hl_temp_fixed_a_plus_b]
    simp only [ha9]; rw [add_sub_assoc]; norm_num1
    rfl
  -- range check
  step_assert_eq hmem11 hmem with rc_check
  -- return range check
  step_assert_eq hmem12 hmem, hmem13 hmem with tv_range_check_ptr₁
  -- return values
  step_assert_eq hmem14 hmem, hmem15 hmem with ret_overflow
  step_assert_eq hmem16 hmem with ret_add
  step_jump_imm hmem17 hmem, hmem18 hmem
  step_ret hmem24 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  use_only (1 + 0)
  constructor
  · norm_num1
  constructor
  · arith_simps
    exact tv_range_check_ptr₁
  intro rc_h_range_check_ptr
  have rc_h_range_check_ptr' := rangeChecked_add_right rc_h_range_check_ptr
  suffices auto_spec: auto_spec_u16_overflowing_add a b _ _ by
    apply sound_u16_overflowing_add; apply auto_spec
  use_only no_overflow
  use_only deferred_a_plus_b, hl_deferred_a_plus_b
  right
  use_only a0
  use_only temp_fixed_a_plus_b
  use_only a_plus_b, hl_a_plus_b
  use_only a9
  rc_app rc_h_range_check_ptr' 0 hl_temp_fixed_a_plus_b rc_check
  arith_simps
  use_only ret_overflow
  simp only [htv_a_plus_b]
  exact ret_add

end u16_overflowing_add_soundness
