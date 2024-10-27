import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u256.u256_sqrt_soundness_spec
import Verification.Libfuncs.u256.u256_sqrt_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u256_sqrt_code
open u256_sqrt_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u256_sqrt_Done
  -- arguments
  (range_check sqrt : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_sqrt_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_sqrt : sqrt = mem (σ.ap + 19))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 41, ap := σ.ap + 25, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ + 4 ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 5)) (mem (τ.ap - 2))
      (auto_spec_u256_sqrt_Done κ range_check sqrt (mem (τ.ap - 1)))) :=
by
  -- return values
  --   range check return value
  step_assert_eq hmem41 hmem, hmem42 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 7
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem43 hmem with ret_sqrt
  step_ret hmem44 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  arith_simps
  rw [htv_sqrt] ; exact ret_sqrt
  done

theorem auto_sound_u256_sqrt_SqrtMul2MinusRemainderGeU128
  -- arguments
  (range_check sqrt sqrt_mul_2_minus_remainder fixed_sqrt_mul_2_minus_remainder : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_sqrt_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_sqrt : sqrt = mem (σ.ap + 19))
  (htv_sqrt_mul_2_minus_remainder : sqrt_mul_2_minus_remainder = mem (σ.ap + 23))
  (htv_fixed_sqrt_mul_2_minus_remainder : fixed_sqrt_mul_2_minus_remainder = mem (σ.ap + 24))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 38, ap := σ.ap + 25, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ + 2 ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 5)) (mem (τ.ap - 2))
      (auto_spec_u256_sqrt_SqrtMul2MinusRemainderGeU128 κ range_check sqrt sqrt_mul_2_minus_remainder fixed_sqrt_mul_2_minus_remainder (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem38 hmem, hmem39 hmem with ha38
  have a38 : fixed_sqrt_mul_2_minus_remainder = sqrt_mul_2_minus_remainder - u128_limit := by
    rw [htv_fixed_sqrt_mul_2_minus_remainder, htv_sqrt_mul_2_minus_remainder, u128_limit, ha38, add_sub_cancel_right]
  -- range check for fixed_sqrt_mul_2_minus_remainder
  step_assert_eq hmem40 hmem with rc_fixed_sqrt_mul_2_minus_remainder
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_sqrt_Done mem σ
    range_check sqrt
    hmem
    htv_range_check
    htv_sqrt
    νbound)
  intros κ_Done _ h_Done
  rcases h_Done with ⟨rc_m_le_Done, hblk_range_check_ptr, h_Done⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_Done (Nat.add_le_add_left _ _) ; norm_num1
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a38
  rc_app rc_h_range_check 6 htv_fixed_sqrt_mul_2_minus_remainder rc_fixed_sqrt_mul_2_minus_remainder
  use_only κ_Done
  apply h_Done rc_h_range_check
  done

theorem auto_sound_u256_sqrt
  -- arguments
  (range_check value_low value_high : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_sqrt_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_value_low : value_low = mem (σ.fp - 4))
  (htv_value_high : value_high = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 5)) (mem (τ.ap - 2))
      (spec_u256_sqrt κ range_check value_low value_high (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 5) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar sqrt0
  mkdef hl_sqrt0 : sqrt0 = mem σ.ap
  have htv_sqrt0 : sqrt0 = mem σ.ap := by
    exact hl_sqrt0
  -- tempvar sqrt1
  mkdef hl_sqrt1 : sqrt1 = mem (σ.ap + 1)
  have htv_sqrt1 : sqrt1 = mem (σ.ap + 1) := by
    exact hl_sqrt1
  -- tempvar remainder_low
  mkdef hl_remainder_low : remainder_low = mem (σ.ap + 2)
  have htv_remainder_low : remainder_low = mem (σ.ap + 2) := by
    exact hl_remainder_low
  -- tempvar remainder_high
  mkdef hl_remainder_high : remainder_high = mem (σ.ap + 3)
  have htv_remainder_high : remainder_high = mem (σ.ap + 3) := by
    exact hl_remainder_high
  -- tempvar sqrt_mul_2_minus_remainder_ge_u128
  mkdef hl_sqrt_mul_2_minus_remainder_ge_u128 : sqrt_mul_2_minus_remainder_ge_u128 = mem (σ.ap + 4)
  have htv_sqrt_mul_2_minus_remainder_ge_u128 : sqrt_mul_2_minus_remainder_ge_u128 = mem (σ.ap + 4) := by
    exact hl_sqrt_mul_2_minus_remainder_ge_u128
  -- range check for sqrt0
  step_assert_eq hmem0 hmem with rc_sqrt0
  -- range check for sqrt1
  step_assert_eq hmem1 hmem with rc_sqrt1
  -- tempvar sqrt0_plus_sqrt1
  step_assert_eq hmem2 hmem with tv_sqrt0_plus_sqrt1
  mkdef hl_sqrt0_plus_sqrt1 : sqrt0_plus_sqrt1 = sqrt0 + sqrt1
  have htv_sqrt0_plus_sqrt1 : sqrt0_plus_sqrt1 = mem (σ.ap + 5) := by
    rw [hl_sqrt0_plus_sqrt1, htv_sqrt0, htv_sqrt1, tv_sqrt0_plus_sqrt1]
  -- tempvar a
  step_assert_eq hmem3 hmem, hmem4 hmem with tv_a
  mkdef hl_a : a = sqrt0_plus_sqrt1 + u128_bound_minus_u65_bound
  have htv_a : a = mem (σ.ap + 6) := by
    rw [hl_a, htv_sqrt0_plus_sqrt1, u128_bound_minus_u65_bound, tv_a]
  -- range check for a
  step_assert_eq hmem5 hmem with rc_a
  -- range check for remainder_low
  step_assert_eq hmem6 hmem with rc_remainder_low
  -- assert
  step_assert_eq hmem7 hmem with ha7
  have a7 : remainder_high = remainder_high * remainder_high := by
    rw [htv_remainder_high] ; exact ha7
  -- tempvar element
  step_assert_eq hmem8 hmem with tv_element
  mkdef hl_element : element = sqrt0 * sqrt0
  have htv_element : element = mem (σ.ap + 7) := by
    rw [hl_element, htv_sqrt0, tv_element]
  -- tempvar accum0
  step_assert_eq hmem9 hmem with tv_accum0
  mkdef hl_accum0 : accum0 = remainder_low + element
  have htv_accum0 : accum0 = mem (σ.ap + 8) := by
    rw [hl_accum0, htv_remainder_low, htv_element, tv_accum0]
  -- tempvar accum1
  step_assert_eq hmem10 hmem with tv_accum1
  mkdef hl_accum1 : accum1 = accum0 - value_low
  have htv_accum1 : accum1 = mem (σ.ap + 9) := by
    rw [hl_accum1, htv_accum0, htv_value_low, tv_accum1, add_sub_cancel_right]
  -- tempvar accum2
  step_assert_eq hmem11 hmem, hmem12 hmem with tv_accum2
  mkdef hl_accum2 : accum2 = accum1 / u64_limit
  have htv_accum2 : accum2 = mem (σ.ap + 10) := by
    rw [hl_accum2, htv_accum1, u64_limit, div_eq_iff_mul_eq] ; exact tv_accum2.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- tempvar temp
  step_assert_eq hmem13 hmem, hmem14 hmem with tv_temp
  mkdef hl_temp : temp = accum2 + u128_half
  have htv_temp : temp = mem (σ.ap + 11) := by
    rw [hl_temp, htv_accum2, u128_half, tv_temp]
  -- range check for temp
  step_assert_eq hmem15 hmem with rc_temp
  -- tempvar element₁
  step_assert_eq hmem16 hmem with tv_element₁
  mkdef hl_element₁ : element₁ = sqrt0 * sqrt1
  have htv_element₁ : element₁ = mem (σ.ap + 12) := by
    rw [hl_element₁, htv_sqrt0, htv_sqrt1, tv_element₁]
  -- tempvar accum3
  step_assert_eq hmem17 hmem with tv_accum3
  mkdef hl_accum3 : accum3 = accum2 + element₁
  have htv_accum3 : accum3 = mem (σ.ap + 13) := by
    rw [hl_accum3, htv_accum2, htv_element₁, tv_accum3]
  -- tempvar accum4
  step_assert_eq hmem18 hmem with tv_accum4
  mkdef hl_accum4 : accum4 = accum3 + element₁
  have htv_accum4 : accum4 = mem (σ.ap + 14) := by
    rw [hl_accum4, htv_accum3, htv_element₁, tv_accum4]
  -- tempvar accum5
  step_assert_eq hmem19 hmem, hmem20 hmem with tv_accum5
  mkdef hl_accum5 : accum5 = accum4 / u64_limit
  have htv_accum5 : accum5 = mem (σ.ap + 15) := by
    rw [hl_accum5, htv_accum4, u64_limit, div_eq_iff_mul_eq] ; exact tv_accum5.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- range check for accum5
  step_assert_eq hmem21 hmem with rc_accum5
  -- tempvar accum6
  step_assert_eq hmem22 hmem with tv_accum6
  mkdef hl_accum6 : accum6 = accum5 + remainder_high
  have htv_accum6 : accum6 = mem (σ.ap + 16) := by
    rw [hl_accum6, htv_accum5, htv_remainder_high, tv_accum6]
  -- tempvar element₂
  step_assert_eq hmem23 hmem with tv_element₂
  mkdef hl_element₂ : element₂ = sqrt1 * sqrt1
  have htv_element₂ : element₂ = mem (σ.ap + 17) := by
    rw [hl_element₂, htv_sqrt1, tv_element₂]
  -- assert
  step_assert_eq hmem24 hmem with ha24
  have a24 : value_high = accum6 + element₂ := by
    rw [htv_value_high, htv_accum6, htv_element₂] ; exact ha24
  -- tempvar shifted_sqrt1
  step_assert_eq hmem25 hmem, hmem26 hmem with tv_shifted_sqrt1
  mkdef hl_shifted_sqrt1 : shifted_sqrt1 = sqrt1 * u64_limit
  have htv_shifted_sqrt1 : shifted_sqrt1 = mem (σ.ap + 18) := by
    rw [hl_shifted_sqrt1, htv_sqrt1, u64_limit, tv_shifted_sqrt1]
  -- tempvar sqrt
  step_assert_eq hmem27 hmem with tv_sqrt
  mkdef hl_sqrt : sqrt = sqrt0 + shifted_sqrt1
  have htv_sqrt : sqrt = mem (σ.ap + 19) := by
    rw [hl_sqrt, htv_sqrt0, htv_shifted_sqrt1, tv_sqrt]
  -- tempvar shifted_remainder_high
  step_assert_eq hmem28 hmem, hmem29 hmem with tv_shifted_remainder_high
  mkdef hl_shifted_remainder_high : shifted_remainder_high = remainder_high * u128_limit
  have htv_shifted_remainder_high : shifted_remainder_high = mem (σ.ap + 20) := by
    rw [hl_shifted_remainder_high, htv_remainder_high, u128_limit, tv_shifted_remainder_high]
  -- tempvar remainder
  step_assert_eq hmem30 hmem with tv_remainder
  mkdef hl_remainder : remainder = remainder_low + shifted_remainder_high
  have htv_remainder : remainder = mem (σ.ap + 21) := by
    rw [hl_remainder, htv_remainder_low, htv_shifted_remainder_high, tv_remainder]
  -- tempvar sqrt_mul_2
  step_assert_eq hmem31 hmem with tv_sqrt_mul_2
  mkdef hl_sqrt_mul_2 : sqrt_mul_2 = sqrt + sqrt
  have htv_sqrt_mul_2 : sqrt_mul_2 = mem (σ.ap + 22) := by
    rw [hl_sqrt_mul_2, htv_sqrt, tv_sqrt_mul_2]
  -- tempvar sqrt_mul_2_minus_remainder
  step_assert_eq hmem32 hmem with tv_sqrt_mul_2_minus_remainder
  mkdef hl_sqrt_mul_2_minus_remainder : sqrt_mul_2_minus_remainder = sqrt_mul_2 - remainder
  have htv_sqrt_mul_2_minus_remainder : sqrt_mul_2_minus_remainder = mem (σ.ap + 23) := by
    rw [hl_sqrt_mul_2_minus_remainder, htv_sqrt_mul_2, htv_remainder, tv_sqrt_mul_2_minus_remainder, add_sub_cancel_right]
  -- tempvar fixed_sqrt_mul_2_minus_remainder
  mkdef hl_fixed_sqrt_mul_2_minus_remainder : fixed_sqrt_mul_2_minus_remainder = mem (σ.ap + 24)
  have htv_fixed_sqrt_mul_2_minus_remainder : fixed_sqrt_mul_2_minus_remainder = mem (σ.ap + 24) := by
    exact hl_fixed_sqrt_mul_2_minus_remainder
  -- jump to SqrtMul2MinusRemainderGeU128 if sqrt_mul_2_minus_remainder_ge_u128 != 0
  step_jnz hmem33 hmem, hmem34 hmem with hcond33 hcond33
  ·
    -- sqrt_mul_2_minus_remainder_ge_u128 = 0
    have a33 : sqrt_mul_2_minus_remainder_ge_u128 = 0 := by simp only [htv_sqrt_mul_2_minus_remainder_ge_u128]; exact hcond33
    -- range check for sqrt_mul_2_minus_remainder
    step_assert_eq hmem35 hmem with rc_sqrt_mul_2_minus_remainder
    step_jump_imm hmem36 hmem, hmem37 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_sqrt_Done mem σ
      range_check sqrt
      hmem
      htv_range_check
      htv_sqrt
      νbound)
    intros κ_Done _ h_Done
    rcases h_Done with ⟨rc_m_le_Done, hblk_range_check_ptr, h_Done⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_Done (Nat.add_le_add_left _ _) ; norm_num1
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u256_sqrt _ range_check value_low value_high _ by
      apply sound_u256_sqrt ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only sqrt0
    use_only sqrt1
    use_only remainder_low
    use_only remainder_high
    use_only sqrt_mul_2_minus_remainder_ge_u128
    rc_app rc_h_range_check 0 htv_sqrt0 rc_sqrt0
    rc_app rc_h_range_check 1 htv_sqrt1 rc_sqrt1
    use_only sqrt0_plus_sqrt1, hl_sqrt0_plus_sqrt1
    use_only a, hl_a
    rc_app rc_h_range_check 2 htv_a rc_a
    rc_app rc_h_range_check 3 htv_remainder_low rc_remainder_low
    use_only a7
    use_only element, hl_element
    use_only accum0, hl_accum0
    use_only accum1, hl_accum1
    use_only accum2, hl_accum2
    use_only temp, hl_temp
    rc_app rc_h_range_check 4 htv_temp rc_temp
    use_only element₁, hl_element₁
    use_only accum3, hl_accum3
    use_only accum4, hl_accum4
    use_only accum5, hl_accum5
    rc_app rc_h_range_check 5 htv_accum5 rc_accum5
    use_only accum6, hl_accum6
    use_only element₂, hl_element₂
    use_only a24
    use_only shifted_sqrt1, hl_shifted_sqrt1
    use_only sqrt, hl_sqrt
    use_only shifted_remainder_high, hl_shifted_remainder_high
    use_only remainder, hl_remainder
    use_only sqrt_mul_2, hl_sqrt_mul_2
    use_only sqrt_mul_2_minus_remainder, hl_sqrt_mul_2_minus_remainder
    use_only fixed_sqrt_mul_2_minus_remainder
    left
    use_only a33
    rc_app rc_h_range_check 6 htv_sqrt_mul_2_minus_remainder rc_sqrt_mul_2_minus_remainder
    use_only κ_Done
    apply h_Done rc_h_range_check
    done
  -- sqrt_mul_2_minus_remainder_ge_u128 ≠ 0
  have a33 : sqrt_mul_2_minus_remainder_ge_u128 ≠ 0 := by simp only [htv_sqrt_mul_2_minus_remainder_ge_u128]; exact hcond33
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_sqrt_SqrtMul2MinusRemainderGeU128 mem σ
    range_check sqrt sqrt_mul_2_minus_remainder fixed_sqrt_mul_2_minus_remainder
    hmem
    htv_range_check
    htv_sqrt
    htv_sqrt_mul_2_minus_remainder
    htv_fixed_sqrt_mul_2_minus_remainder
    νbound)
  intros κ_SqrtMul2MinusRemainderGeU128 _ h_SqrtMul2MinusRemainderGeU128
  rcases h_SqrtMul2MinusRemainderGeU128 with ⟨rc_m_le_SqrtMul2MinusRemainderGeU128, hblk_range_check_ptr, h_SqrtMul2MinusRemainderGeU128⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_SqrtMul2MinusRemainderGeU128 (Nat.add_le_add_left _ _) ; norm_num1
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u256_sqrt _ range_check value_low value_high _ by
    apply sound_u256_sqrt ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only sqrt0
  use_only sqrt1
  use_only remainder_low
  use_only remainder_high
  use_only sqrt_mul_2_minus_remainder_ge_u128
  rc_app rc_h_range_check 0 htv_sqrt0 rc_sqrt0
  rc_app rc_h_range_check 1 htv_sqrt1 rc_sqrt1
  use_only sqrt0_plus_sqrt1, hl_sqrt0_plus_sqrt1
  use_only a, hl_a
  rc_app rc_h_range_check 2 htv_a rc_a
  rc_app rc_h_range_check 3 htv_remainder_low rc_remainder_low
  use_only a7
  use_only element, hl_element
  use_only accum0, hl_accum0
  use_only accum1, hl_accum1
  use_only accum2, hl_accum2
  use_only temp, hl_temp
  rc_app rc_h_range_check 4 htv_temp rc_temp
  use_only element₁, hl_element₁
  use_only accum3, hl_accum3
  use_only accum4, hl_accum4
  use_only accum5, hl_accum5
  rc_app rc_h_range_check 5 htv_accum5 rc_accum5
  use_only accum6, hl_accum6
  use_only element₂, hl_element₂
  use_only a24
  use_only shifted_sqrt1, hl_shifted_sqrt1
  use_only sqrt, hl_sqrt
  use_only shifted_remainder_high, hl_shifted_remainder_high
  use_only remainder, hl_remainder
  use_only sqrt_mul_2, hl_sqrt_mul_2
  use_only sqrt_mul_2_minus_remainder, hl_sqrt_mul_2_minus_remainder
  use_only fixed_sqrt_mul_2_minus_remainder
  right
  use_only a33
  use_only κ_SqrtMul2MinusRemainderGeU128
  apply h_SqrtMul2MinusRemainderGeU128 rc_h_range_check
  done
