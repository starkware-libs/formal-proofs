import Verification.Libfuncs.u64.u64_overflowing_sub_soundness_spec
import Verification.Libfuncs.u64.u64_overflowing_sub_code

namespace u64_overflowing_sub_soundness
open u64_overflowing_sub_code

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)

theorem auto_sound_u64_overflowing_sub
    -- arguments
    (range_check_ptr a b : F)
    -- code is in memory at s.pc
    (hmem : MemAt mem u64_overflowing_sub_code σ.pc)
    -- input arguments on the stack
    (_ : range_check_ptr = mem (σ.fp - 5))
    (hin_a : a = mem (σ.fp - 4))
    (hin_b : b = mem (σ.fp - 3))
    -- conclusion
  : EnsuresRet mem σ fun κ τ =>
    ∃ μ ≤ κ, RcEnsures mem (rcBound F) μ (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_u64_overflowing_sub a b (mem (τ.ap - 2)) (mem (τ.ap - 1))) := by
  apply ensures_of_ensuresb; intro νbound
  -- tempvar a_ge_b
  mkdef hl_a_ge_b : a_ge_b = mem σ.ap
  -- tempvar a_minus_b = a - b
  step_assert_eq hmem0 hmem with tv_a_minus_b
  mkdef hl_a_minus_b : a_minus_b = a - b
  have htv_a_minus_b: a_minus_b = mem (σ.ap + 1) := by
    simp only [hl_a_minus_b, hin_a, hin_b, tv_a_minus_b]; ring
  -- jump NoOverflow if a_ge_b != 0;
  step_jnz hmem1 hmem, hmem2 hmem with hcond hcond
  · -- a_ge_b == 0
    have a0 : a_ge_b = 0 := by simp only [hl_a_ge_b, hcond]
    -- tempvar fixed_a_minus_b = a_minus_b + u128Limit;
    step_assert_eq hmem3 hmem, hmem4 hmem with tv_fixed_a_minus_b
    mkdef hl_fixed_a_minus_b : fixed_a_minus_b = a_minus_b + u128Limit
    have htv_fixed_a_minus_b: fixed_a_minus_b = mem (σ.ap + 2) := by
      simp only [tv_fixed_a_minus_b, hl_fixed_a_minus_b, u128Limit, htv_a_minus_b]
      norm_num1
      rfl
    -- range_check
    step_assert_eq hmem5 hmem with range_check
    step_jump_imm hmem6 hmem, hmem7 hmem
    -- return range check
    step_assert_eq hmem18 hmem, hmem19 hmem with tv_range_check_ptr₁
    -- return values
    step_assert_eq hmem20 hmem, hmem21 hmem with ret_overflow
    step_assert_eq hmem22 hmem, hmem23 hmem with ret_sub
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
    suffices auto_spec : auto_spec_u64_overflowing_sub a b _ _ by
      apply sound_u64_overflowing_sub; apply auto_spec
    use_only a_ge_b
    use_only a_minus_b, hl_a_minus_b
    left
    use_only a0
    use_only fixed_a_minus_b, hl_fixed_a_minus_b
    -- range check
    rc_app rc_h_range_check_ptr' 0 htv_fixed_a_minus_b range_check
    arith_simps
    use_only ret_overflow
    simp only [htv_a_minus_b, u64Limit]
    exact ret_sub
  -- a_ge_b != 0
  have a0 : a_ge_b ≠ 0 := by simp only [hl_a_ge_b]; exact hcond
  -- range_check
  step_assert_eq hmem8 hmem with range_check
  step_advance_ap hmem9 hmem, hmem10 hmem
  -- return range check
  step_assert_eq hmem11 hmem, hmem12 hmem with tv_range_check_ptr₁
  -- return values
  step_assert_eq hmem13 hmem, hmem14 hmem with ret_overflow
  step_assert_eq hmem15 hmem with ret_sub
  step_jump_imm hmem16 hmem, hmem17 hmem
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
  suffices auto_spec: auto_spec_u64_overflowing_sub a b _ _ by
    apply sound_u64_overflowing_sub; apply auto_spec
  use_only a_ge_b
  use_only a_minus_b, hl_a_minus_b
  right
  use_only a0
  -- range check
  rc_app rc_h_range_check_ptr' 0 htv_a_minus_b range_check
  arith_simps
  use_only ret_overflow
  simp only [htv_a_minus_b]
  exact ret_sub

end u64_overflowing_sub_soundness
