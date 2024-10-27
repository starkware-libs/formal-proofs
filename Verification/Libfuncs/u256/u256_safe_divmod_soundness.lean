import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u256.u256_safe_divmod_soundness_spec
import Verification.Libfuncs.u256.u256_safe_divmod_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u256_safe_divmod_code
open u256_safe_divmod_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u256_safe_divmod_MERGE
  -- arguments
  (range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 7))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 8))
  (htv_leftover : leftover = mem (σ.ap + 11))
  (htv_qd1_small : qd1_small = mem (σ.ap + 12))
  (htv_qd1_large : qd1_large = mem (σ.ap + 13))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 43, ap := σ.ap + 15, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_MERGE κ range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar qd1_small_fixed
  step_assert_eq hmem43 hmem, hmem44 hmem with tv_qd1_small_fixed
  mkdef hl_qd1_small_fixed : qd1_small_fixed = qd1_small + u128_bound_minus_u64_bound
  have htv_qd1_small_fixed : qd1_small_fixed = mem (σ.ap + 15) := by
    rw [hl_qd1_small_fixed, htv_qd1_small, u128_bound_minus_u64_bound, tv_qd1_small_fixed]
  -- range check for qd1_small_fixed
  step_assert_eq hmem45 hmem with rc_qd1_small_fixed
  -- tempvar qd1
  step_assert_eq hmem46 hmem with tv_qd1
  mkdef hl_qd1 : qd1 = qd1_small * qd1_large
  have htv_qd1 : qd1 = mem (σ.ap + 16) := by
    rw [hl_qd1, htv_qd1_small, htv_qd1_large, tv_qd1]
  -- tempvar part0₁
  step_assert_eq hmem47 hmem with tv_part0₁
  mkdef hl_part0₁ : part0₁ = leftover + q0d0_high
  have htv_part0₁ : part0₁ = mem (σ.ap + 17) := by
    rw [hl_part0₁, htv_leftover, htv_q0d0_high, tv_part0₁]
  -- tempvar part1₁
  step_assert_eq hmem48 hmem with tv_part1₁
  mkdef hl_part1₁ : part1₁ = part0₁ + remainder1
  have htv_part1₁ : part1₁ = mem (σ.ap + 18) := by
    rw [hl_part1₁, htv_part0₁, htv_remainder1, tv_part1₁]
  -- assert
  step_assert_eq hmem49 hmem with ha49
  have a49 : dividend1 = part1₁ + qd1 := by
    rw [htv_dividend1, htv_part1₁, htv_qd1] ; exact ha49
  -- return values
  --   range check return value
  step_assert_eq hmem50 hmem, hmem51 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 6
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem52 hmem with ret_quotient0
  step_assert_eq hmem53 hmem with ret_quotient1
  step_assert_eq hmem54 hmem with ret_remainder0
  step_assert_eq hmem55 hmem with ret_remainder1
  step_assert_eq hmem56 hmem with ret_quotient0₁
  step_assert_eq hmem57 hmem with ret_divisor0
  step_assert_eq hmem58 hmem with ret_q0d0_high
  step_assert_eq hmem59 hmem with ret_q0d0_low
  step_ret hmem60 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  use_only qd1_small_fixed, hl_qd1_small_fixed
  rc_app rc_h_range_check 5 htv_qd1_small_fixed rc_qd1_small_fixed
  use_only qd1, hl_qd1
  use_only part0₁, hl_part0₁
  use_only part1₁, hl_part1₁
  use_only a49
  arith_simps
  constructor ; rw [htv_quotient0] ; exact ret_quotient0
  constructor ; rw [htv_quotient1] ; exact ret_quotient1
  constructor ; rw [htv_remainder0] ; exact ret_remainder0
  constructor ; rw [htv_remainder1] ; exact ret_remainder1
  constructor ; rw [htv_quotient0] ; exact ret_quotient0₁
  constructor ; rw [htv_divisor0] ; exact ret_divisor0
  constructor ; rw [htv_q0d0_high] ; exact ret_q0d0_high
  rw [htv_q0d0_low] ; exact ret_q0d0_low
  done

theorem auto_sound_u256_safe_divmod_QUOTIENT1_LESS_THAN_DIVISOR0
  -- arguments
  (range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 7))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 8))
  (htv_leftover : leftover = mem (σ.ap + 11))
  (htv_qd1_small : qd1_small = mem (σ.ap + 12))
  (htv_qd1_large : qd1_large = mem (σ.ap + 13))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 41, ap := σ.ap + 14, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_QUOTIENT1_LESS_THAN_DIVISOR0 κ range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem41 hmem with ha41
  have a41 : qd1_small = quotient1 := by
    rw [htv_qd1_small, htv_quotient1] ; exact ha41
  -- assert
  step_assert_eq hmem42 hmem with ha42
  have a42 : qd1_large = divisor0 := by
    rw [htv_qd1_large, htv_divisor0] ; exact ha42
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_MERGE mem σ
    range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
    hmem
    htv_range_check
    htv_dividend1
    htv_divisor0
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_leftover
    htv_qd1_small
    htv_qd1_large
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a41
  use_only a42
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u256_safe_divmod_DIVISOR1_EQ_ZERO
  -- arguments
  (range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 7))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 8))
  (htv_leftover : leftover = mem (σ.ap + 11))
  (htv_qd1_small : qd1_small = mem (σ.ap + 12))
  (htv_qd1_large : qd1_large = mem (σ.ap + 13))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 33, ap := σ.ap + 12, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_DIVISOR1_EQ_ZERO κ range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem33 hmem, hmem34 hmem with ha33
  have a33 : divisor1 = zero := by
    rw [htv_divisor1, zero] ; exact ha33
  -- tempvar quotient1_less_than_divisor0
  mkdef hl_quotient1_less_than_divisor0 : quotient1_less_than_divisor0 = mem (σ.ap + 14)
  have htv_quotient1_less_than_divisor0 : quotient1_less_than_divisor0 = mem (σ.ap + 14) := by
    exact hl_quotient1_less_than_divisor0
  -- jump to QUOTIENT1_LESS_THAN_DIVISOR0 if quotient1_less_than_divisor0 != 0
  step_jnz hmem35 hmem, hmem36 hmem with hcond35 hcond35
  ·
    -- quotient1_less_than_divisor0 = 0
    have a35 : quotient1_less_than_divisor0 = 0 := by simp only [htv_quotient1_less_than_divisor0]; exact hcond35
    -- assert
    step_assert_eq hmem37 hmem with ha37
    have a37 : qd1_small = divisor0 := by
      rw [htv_qd1_small, htv_divisor0] ; exact ha37
    -- assert
    step_assert_eq hmem38 hmem with ha38
    have a38 : qd1_large = quotient1 := by
      rw [htv_qd1_large, htv_quotient1] ; exact ha38
    step_jump_imm hmem39 hmem, hmem40 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_safe_divmod_MERGE mem σ
      range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
      hmem
      htv_range_check
      htv_dividend1
      htv_divisor0
      htv_quotient0
      htv_quotient1
      htv_remainder0
      htv_remainder1
      htv_q0d0_low
      htv_q0d0_high
      htv_leftover
      htv_qd1_small
      htv_qd1_large
      νbound)
    intros κ_MERGE _ h_MERGE
    rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only a33
    use_only quotient1_less_than_divisor0
    left
    use_only a35
    use_only a37
    use_only a38
    use_only κ_MERGE
    apply h_MERGE rc_h_range_check
    done
  -- quotient1_less_than_divisor0 ≠ 0
  have a35 : quotient1_less_than_divisor0 ≠ 0 := by simp only [htv_quotient1_less_than_divisor0]; exact hcond35
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_QUOTIENT1_LESS_THAN_DIVISOR0 mem σ
    range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
    hmem
    htv_range_check
    htv_dividend1
    htv_divisor0
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_leftover
    htv_qd1_small
    htv_qd1_large
    νbound)
  intros κ_QUOTIENT1_LESS_THAN_DIVISOR0 _ h_QUOTIENT1_LESS_THAN_DIVISOR0
  rcases h_QUOTIENT1_LESS_THAN_DIVISOR0 with ⟨rc_m_le_QUOTIENT1_LESS_THAN_DIVISOR0, hblk_range_check_ptr, h_QUOTIENT1_LESS_THAN_DIVISOR0⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_QUOTIENT1_LESS_THAN_DIVISOR0 (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a33
  use_only quotient1_less_than_divisor0
  right
  use_only a35
  use_only κ_QUOTIENT1_LESS_THAN_DIVISOR0
  apply h_QUOTIENT1_LESS_THAN_DIVISOR0 rc_h_range_check
  done

theorem auto_sound_u256_safe_divmod_QUOTIENT0_LESS_THAN_DIVISOR1
  -- arguments
  (range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 7))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 8))
  (htv_leftover : leftover = mem (σ.ap + 11))
  (htv_qd1_small : qd1_small = mem (σ.ap + 12))
  (htv_qd1_large : qd1_large = mem (σ.ap + 13))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 29, ap := σ.ap + 13, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_QUOTIENT0_LESS_THAN_DIVISOR1 κ range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem29 hmem with ha29
  have a29 : qd1_small = quotient0 := by
    rw [htv_qd1_small, htv_quotient0] ; exact ha29
  -- assert
  step_assert_eq hmem30 hmem with ha30
  have a30 : qd1_large = divisor1 := by
    rw [htv_qd1_large, htv_divisor1] ; exact ha30
  step_jump_imm hmem31 hmem, hmem32 hmem
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_MERGE mem σ
    range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
    hmem
    htv_range_check
    htv_dividend1
    htv_divisor0
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_leftover
    htv_qd1_small
    htv_qd1_large
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a29
  use_only a30
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u256_safe_divmod_After
  -- arguments
  (range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend0 : dividend0 = mem (σ.fp - 6))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 16, ap := σ.ap + 7, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_After κ range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar q0d0_low
  mkdef hl_q0d0_low : q0d0_low = mem (σ.ap + 7)
  have htv_q0d0_low : q0d0_low = mem (σ.ap + 7) := by
    exact hl_q0d0_low
  -- tempvar q0d0_high
  mkdef hl_q0d0_high : q0d0_high = mem (σ.ap + 8)
  have htv_q0d0_high : q0d0_high = mem (σ.ap + 8) := by
    exact hl_q0d0_high
  -- tempvar part0
  step_assert_eq hmem16 hmem with tv_part0
  mkdef hl_part0 : part0 = q0d0_low + remainder0
  have htv_part0 : part0 = mem (σ.ap + 9) := by
    rw [hl_part0, htv_q0d0_low, htv_remainder0, tv_part0]
  -- tempvar part1
  step_assert_eq hmem17 hmem with tv_part1
  mkdef hl_part1 : part1 = part0 - dividend0
  have htv_part1 : part1 = mem (σ.ap + 10) := by
    rw [hl_part1, htv_part0, htv_dividend0, tv_part1, add_sub_cancel_right]
  -- tempvar leftover
  step_assert_eq hmem18 hmem, hmem19 hmem with tv_leftover
  mkdef hl_leftover : leftover = part1 / u128_limit
  have htv_leftover : leftover = mem (σ.ap + 11) := by
    rw [hl_leftover, htv_part1, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- assert
  step_assert_eq hmem20 hmem with ha20
  have a20 : leftover = leftover * leftover := by
    rw [htv_leftover] ; exact ha20
  -- tempvar qd1_small
  mkdef hl_qd1_small : qd1_small = mem (σ.ap + 12)
  have htv_qd1_small : qd1_small = mem (σ.ap + 12) := by
    exact hl_qd1_small
  -- tempvar qd1_large
  mkdef hl_qd1_large : qd1_large = mem (σ.ap + 13)
  have htv_qd1_large : qd1_large = mem (σ.ap + 13) := by
    exact hl_qd1_large
  -- jump to DIVISOR1_EQ_ZERO if quotient1 != 0
  step_jnz hmem21 hmem, hmem22 hmem with hcond21 hcond21
  ·
    -- quotient1 = 0
    have a21 : quotient1 = 0 := by simp only [htv_quotient1]; exact hcond21
    -- tempvar quotient0_less_than_divisor1
    mkdef hl_quotient0_less_than_divisor1 : quotient0_less_than_divisor1 = mem (σ.ap + 14)
    have htv_quotient0_less_than_divisor1 : quotient0_less_than_divisor1 = mem (σ.ap + 14) := by
      exact hl_quotient0_less_than_divisor1
    -- jump to QUOTIENT0_LESS_THAN_DIVISOR1 if quotient0_less_than_divisor1 != 0
    step_jnz hmem23 hmem, hmem24 hmem with hcond23 hcond23
    ·
      -- quotient0_less_than_divisor1 = 0
      have a23 : quotient0_less_than_divisor1 = 0 := by simp only [htv_quotient0_less_than_divisor1]; exact hcond23
      -- assert
      step_assert_eq hmem25 hmem with ha25
      have a25 : qd1_small = divisor1 := by
        rw [htv_qd1_small, htv_divisor1] ; exact ha25
      -- assert
      step_assert_eq hmem26 hmem with ha26
      have a26 : qd1_large = quotient0 := by
        rw [htv_qd1_large, htv_quotient0] ; exact ha26
      step_jump_imm hmem27 hmem, hmem28 hmem
      arith_simps
      apply ensuresbRet_trans (auto_sound_u256_safe_divmod_MERGE mem σ
        range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
        hmem
        htv_range_check
        htv_dividend1
        htv_divisor0
        htv_quotient0
        htv_quotient1
        htv_remainder0
        htv_remainder1
        htv_q0d0_low
        htv_q0d0_high
        htv_leftover
        htv_qd1_small
        htv_qd1_large
        νbound)
      intros κ_MERGE _ h_MERGE
      rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
      -- range check condition
      constructor
      apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
      constructor
      · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
      intro rc_h_range_check
      use_only q0d0_low
      use_only q0d0_high
      use_only part0, hl_part0
      use_only part1, hl_part1
      use_only leftover, hl_leftover
      use_only a20
      use_only qd1_small
      use_only qd1_large
      left
      use_only a21
      use_only quotient0_less_than_divisor1
      left
      use_only a23
      use_only a25
      use_only a26
      use_only κ_MERGE
      apply h_MERGE rc_h_range_check
      done
    -- quotient0_less_than_divisor1 ≠ 0
    have a23 : quotient0_less_than_divisor1 ≠ 0 := by simp only [htv_quotient0_less_than_divisor1]; exact hcond23
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_safe_divmod_QUOTIENT0_LESS_THAN_DIVISOR1 mem σ
      range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
      hmem
      htv_range_check
      htv_dividend1
      htv_divisor0
      htv_divisor1
      htv_quotient0
      htv_quotient1
      htv_remainder0
      htv_remainder1
      htv_q0d0_low
      htv_q0d0_high
      htv_leftover
      htv_qd1_small
      htv_qd1_large
      νbound)
    intros κ_QUOTIENT0_LESS_THAN_DIVISOR1 _ h_QUOTIENT0_LESS_THAN_DIVISOR1
    rcases h_QUOTIENT0_LESS_THAN_DIVISOR1 with ⟨rc_m_le_QUOTIENT0_LESS_THAN_DIVISOR1, hblk_range_check_ptr, h_QUOTIENT0_LESS_THAN_DIVISOR1⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_QUOTIENT0_LESS_THAN_DIVISOR1 (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only q0d0_low
    use_only q0d0_high
    use_only part0, hl_part0
    use_only part1, hl_part1
    use_only leftover, hl_leftover
    use_only a20
    use_only qd1_small
    use_only qd1_large
    left
    use_only a21
    use_only quotient0_less_than_divisor1
    right
    use_only a23
    use_only κ_QUOTIENT0_LESS_THAN_DIVISOR1
    apply h_QUOTIENT0_LESS_THAN_DIVISOR1 rc_h_range_check
    done
  -- quotient1 ≠ 0
  have a21 : quotient1 ≠ 0 := by simp only [htv_quotient1]; exact hcond21
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_DIVISOR1_EQ_ZERO mem σ
    range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large
    hmem
    htv_range_check
    htv_dividend1
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_leftover
    htv_qd1_small
    htv_qd1_large
    νbound)
  intros κ_DIVISOR1_EQ_ZERO _ h_DIVISOR1_EQ_ZERO
  rcases h_DIVISOR1_EQ_ZERO with ⟨rc_m_le_DIVISOR1_EQ_ZERO, hblk_range_check_ptr, h_DIVISOR1_EQ_ZERO⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_DIVISOR1_EQ_ZERO (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only q0d0_low
  use_only q0d0_high
  use_only part0, hl_part0
  use_only part1, hl_part1
  use_only leftover, hl_leftover
  use_only a20
  use_only qd1_small
  use_only qd1_large
  right
  use_only a21
  use_only κ_DIVISOR1_EQ_ZERO
  apply h_DIVISOR1_EQ_ZERO rc_h_range_check
  done

theorem auto_sound_u256_safe_divmod_HighDiff
  -- arguments
  (range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 diff1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend0 : dividend0 = mem (σ.fp - 6))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_remainder0 : remainder0 = mem (σ.ap + 2))
  (htv_remainder1 : remainder1 = mem (σ.ap + 3))
  (htv_diff1 : diff1 = mem (σ.ap + 4))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 13, ap := σ.ap + 6, fp := σ.fp }
    (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (auto_spec_u256_safe_divmod_HighDiff κ range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 diff1 (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  step_advance_ap hmem13 hmem, hmem14 hmem
  -- range check for diff1
  step_assert_eq hmem15 hmem with rc_diff1
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_After mem σ
    range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
    hmem
    htv_range_check
    htv_dividend0
    htv_dividend1
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    νbound)
  intros κ_After _ h_After
  rcases h_After with ⟨rc_m_le_After, hblk_range_check_ptr, h_After⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_After (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  rc_app rc_h_range_check 4 htv_diff1 rc_diff1
  use_only κ_After
  apply h_After rc_h_range_check
  done

theorem auto_sound_u256_safe_divmod
  -- arguments
  (range_check dividend0 dividend1 divisor0 divisor1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_safe_divmod_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_dividend0 : dividend0 = mem (σ.fp - 6))
  (htv_dividend1 : dividend1 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    6 ≤ κ ∧ RcEnsures mem (rcBound F) 6 (mem (σ.fp - 7)) (mem (τ.ap - 9))
      (spec_u256_safe_divmod κ range_check dividend0 dividend1 divisor0 divisor1 (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 7) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar quotient0
  mkdef hl_quotient0 : quotient0 = mem σ.ap
  have htv_quotient0 : quotient0 = mem σ.ap := by
    exact hl_quotient0
  -- tempvar quotient1
  mkdef hl_quotient1 : quotient1 = mem (σ.ap + 1)
  have htv_quotient1 : quotient1 = mem (σ.ap + 1) := by
    exact hl_quotient1
  -- tempvar remainder0
  mkdef hl_remainder0 : remainder0 = mem (σ.ap + 2)
  have htv_remainder0 : remainder0 = mem (σ.ap + 2) := by
    exact hl_remainder0
  -- tempvar remainder1
  mkdef hl_remainder1 : remainder1 = mem (σ.ap + 3)
  have htv_remainder1 : remainder1 = mem (σ.ap + 3) := by
    exact hl_remainder1
  -- range check for quotient0
  step_assert_eq hmem0 hmem with rc_quotient0
  -- range check for quotient1
  step_assert_eq hmem1 hmem with rc_quotient1
  -- range check for remainder0
  step_assert_eq hmem2 hmem with rc_remainder0
  -- range check for remainder1
  step_assert_eq hmem3 hmem with rc_remainder1
  -- tempvar diff1
  step_assert_eq hmem4 hmem with tv_diff1
  mkdef hl_diff1 : diff1 = divisor1 - remainder1
  have htv_diff1 : diff1 = mem (σ.ap + 4) := by
    rw [hl_diff1, htv_divisor1, htv_remainder1, tv_diff1, add_sub_cancel_right]
  -- tempvar diff0
  mkdef hl_diff0 : diff0 = mem (σ.ap + 5)
  have htv_diff0 : diff0 = mem (σ.ap + 5) := by
    exact hl_diff0
  -- tempvar diff0_min_1
  mkdef hl_diff0_min_1 : diff0_min_1 = mem (σ.ap + 6)
  have htv_diff0_min_1 : diff0_min_1 = mem (σ.ap + 6) := by
    exact hl_diff0_min_1
  -- jump to HighDiff if diff1 != 0
  step_jnz hmem5 hmem, hmem6 hmem with hcond5 hcond5
  ·
    -- diff1 = 0
    have a5 : diff1 = 0 := by simp only [htv_diff1]; exact hcond5
    -- assert
    step_assert_eq hmem7 hmem with ha7
    have a7 : diff0 = divisor0 - remainder0 := by
      rw [htv_diff0, htv_divisor0, htv_remainder0, ha7, add_sub_cancel_right]
    -- assert
    step_assert_eq hmem8 hmem, hmem9 hmem with ha8
    have a8 : diff0_min_1 = diff0 - one := by
      rw [htv_diff0_min_1, htv_diff0, one, ha8, add_sub_cancel_right]
    -- range check for diff0_min_1
    step_assert_eq hmem10 hmem with rc_diff0_min_1
    step_jump_imm hmem11 hmem, hmem12 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_safe_divmod_After mem σ
      range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
      hmem
      htv_range_check
      htv_dividend0
      htv_dividend1
      htv_divisor0
      htv_divisor1
      htv_quotient0
      htv_quotient1
      htv_remainder0
      htv_remainder1
      νbound)
    intros κ_After _ h_After
    rcases h_After with ⟨rc_m_le_After, hblk_range_check_ptr, h_After⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_After (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u256_safe_divmod _ range_check dividend0 dividend1 divisor0 divisor1 _ _ _ _ _ _ _ _ by
      apply sound_u256_safe_divmod ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only quotient0
    use_only quotient1
    use_only remainder0
    use_only remainder1
    rc_app rc_h_range_check 0 htv_quotient0 rc_quotient0
    rc_app rc_h_range_check 1 htv_quotient1 rc_quotient1
    rc_app rc_h_range_check 2 htv_remainder0 rc_remainder0
    rc_app rc_h_range_check 3 htv_remainder1 rc_remainder1
    use_only diff1, hl_diff1
    use_only diff0
    use_only diff0_min_1
    left
    use_only a5
    use_only a7
    use_only a8
    rc_app rc_h_range_check 4 htv_diff0_min_1 rc_diff0_min_1
    use_only κ_After
    apply h_After rc_h_range_check
    done
  -- diff1 ≠ 0
  have a5 : diff1 ≠ 0 := by simp only [htv_diff1]; exact hcond5
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_safe_divmod_HighDiff mem σ
    range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 diff1
    hmem
    htv_range_check
    htv_dividend0
    htv_dividend1
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_remainder0
    htv_remainder1
    htv_diff1
    νbound)
  intros κ_HighDiff _ h_HighDiff
  rcases h_HighDiff with ⟨rc_m_le_HighDiff, hblk_range_check_ptr, h_HighDiff⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_HighDiff (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u256_safe_divmod _ range_check dividend0 dividend1 divisor0 divisor1 _ _ _ _ _ _ _ _ by
    apply sound_u256_safe_divmod ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only quotient0
  use_only quotient1
  use_only remainder0
  use_only remainder1
  rc_app rc_h_range_check 0 htv_quotient0 rc_quotient0
  rc_app rc_h_range_check 1 htv_quotient1 rc_quotient1
  rc_app rc_h_range_check 2 htv_remainder0 rc_remainder0
  rc_app rc_h_range_check 3 htv_remainder1 rc_remainder1
  use_only diff1, hl_diff1
  use_only diff0
  use_only diff0_min_1
  right
  use_only a5
  use_only κ_HighDiff
  apply h_HighDiff rc_h_range_check
  done
