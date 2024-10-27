import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u512.u512_safe_divmod_by_u256_soundness_spec
import Verification.Libfuncs.u512.u512_safe_divmod_by_u256_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u512_safe_divmod_by_u256_code
open u512_safe_divmod_by_u256_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u512_safe_divmod_by_u256_MERGE
  -- arguments
  (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 9))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 10))
  (htv_q1d0_low : q1d0_low = mem (σ.ap + 11))
  (htv_q1d0_high : q1d0_high = mem (σ.ap + 12))
  (htv_q0d1_low : q0d1_low = mem (σ.ap + 13))
  (htv_q0d1_high : q0d1_high = mem (σ.ap + 14))
  (htv_q1d1_low : q1d1_low = mem (σ.ap + 15))
  (htv_q1d1_high : q1d1_high = mem (σ.ap + 16))
  (htv_q2d0_low : q2d0_low = mem (σ.ap + 17))
  (htv_q2d0_high : q2d0_high = mem (σ.ap + 18))
  (htv_leftover : leftover = mem (σ.ap + 34))
  (htv_qd3_small : qd3_small = mem (σ.ap + 36))
  (htv_qd3_large : qd3_large = mem (σ.ap + 37))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 67, ap := σ.ap + 39, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_MERGE κ range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar qd3_small_fixed
  step_assert_eq hmem67 hmem, hmem68 hmem with tv_qd3_small_fixed
  mkdef hl_qd3_small_fixed : qd3_small_fixed = qd3_small + u128_bound_minus_u64_bound
  have htv_qd3_small_fixed : qd3_small_fixed = mem (σ.ap + 39) := by
    rw [hl_qd3_small_fixed, htv_qd3_small, u128_bound_minus_u64_bound, tv_qd3_small_fixed]
  -- range check for qd3_small_fixed
  step_assert_eq hmem69 hmem with rc_qd3_small_fixed
  -- tempvar qd3
  step_assert_eq hmem70 hmem with tv_qd3
  mkdef hl_qd3 : qd3 = qd3_small * qd3_large
  have htv_qd3 : qd3 = mem (σ.ap + 40) := by
    rw [hl_qd3, htv_qd3_small, htv_qd3_large, tv_qd3]
  -- tempvar part0₁
  step_assert_eq hmem71 hmem with tv_part0₁
  mkdef hl_part0₁ : part0₁ = leftover + q2d0_high
  have htv_part0₁ : part0₁ = mem (σ.ap + 41) := by
    rw [hl_part0₁, htv_leftover, htv_q2d0_high, tv_part0₁]
  -- tempvar part1₁
  step_assert_eq hmem72 hmem with tv_part1₁
  mkdef hl_part1₁ : part1₁ = part0₁ + q1d1_high
  have htv_part1₁ : part1₁ = mem (σ.ap + 42) := by
    rw [hl_part1₁, htv_part0₁, htv_q1d1_high, tv_part1₁]
  -- assert
  step_assert_eq hmem73 hmem with ha73
  have a73 : dividend3 = part1₁ + qd3 := by
    rw [htv_dividend3, htv_part1₁, htv_qd3] ; exact ha73
  -- return values
  --   range check return value
  step_assert_eq hmem74 hmem, hmem75 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 12
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem76 hmem with ret_quotient0
  step_assert_eq hmem77 hmem with ret_quotient1
  step_assert_eq hmem78 hmem with ret_quotient2
  step_assert_eq hmem79 hmem with ret_quotient3
  step_assert_eq hmem80 hmem with ret_remainder0
  step_assert_eq hmem81 hmem with ret_remainder1
  step_assert_eq hmem82 hmem with ret_quotient0₁
  step_assert_eq hmem83 hmem with ret_divisor0
  step_assert_eq hmem84 hmem with ret_q0d0_high
  step_assert_eq hmem85 hmem with ret_q0d0_low
  step_assert_eq hmem86 hmem with ret_quotient0₂
  step_assert_eq hmem87 hmem with ret_divisor1
  step_assert_eq hmem88 hmem with ret_q0d1_high
  step_assert_eq hmem89 hmem with ret_q0d1_low
  step_assert_eq hmem90 hmem with ret_quotient1₁
  step_assert_eq hmem91 hmem with ret_divisor0₁
  step_assert_eq hmem92 hmem with ret_q1d0_high
  step_assert_eq hmem93 hmem with ret_q1d0_low
  step_assert_eq hmem94 hmem with ret_quotient1₂
  step_assert_eq hmem95 hmem with ret_divisor1₁
  step_assert_eq hmem96 hmem with ret_q1d1_high
  step_assert_eq hmem97 hmem with ret_q1d1_low
  step_assert_eq hmem98 hmem with ret_quotient2₁
  step_assert_eq hmem99 hmem with ret_divisor0₂
  step_assert_eq hmem100 hmem with ret_q2d0_high
  step_assert_eq hmem101 hmem with ret_q2d0_low
  step_ret hmem102 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  use_only qd3_small_fixed, hl_qd3_small_fixed
  rc_app rc_h_range_check 11 htv_qd3_small_fixed rc_qd3_small_fixed
  use_only qd3, hl_qd3
  use_only part0₁, hl_part0₁
  use_only part1₁, hl_part1₁
  use_only a73
  arith_simps
  constructor ; rw [htv_quotient0] ; exact ret_quotient0
  constructor ; rw [htv_quotient1] ; exact ret_quotient1
  constructor ; rw [htv_quotient2] ; exact ret_quotient2
  constructor ; rw [htv_quotient3] ; exact ret_quotient3
  constructor ; rw [htv_remainder0] ; exact ret_remainder0
  constructor ; rw [htv_remainder1] ; exact ret_remainder1
  constructor ; rw [htv_quotient0] ; exact ret_quotient0₁
  constructor ; rw [htv_divisor0] ; exact ret_divisor0
  constructor ; rw [htv_q0d0_high] ; exact ret_q0d0_high
  constructor ; rw [htv_q0d0_low] ; exact ret_q0d0_low
  constructor ; rw [htv_quotient0] ; exact ret_quotient0₂
  constructor ; rw [htv_divisor1] ; exact ret_divisor1
  constructor ; rw [htv_q0d1_high] ; exact ret_q0d1_high
  constructor ; rw [htv_q0d1_low] ; exact ret_q0d1_low
  constructor ; rw [htv_quotient1] ; exact ret_quotient1₁
  constructor ; rw [htv_divisor0] ; exact ret_divisor0₁
  constructor ; rw [htv_q1d0_high] ; exact ret_q1d0_high
  constructor ; rw [htv_q1d0_low] ; exact ret_q1d0_low
  constructor ; rw [htv_quotient1] ; exact ret_quotient1₂
  constructor ; rw [htv_divisor1] ; exact ret_divisor1₁
  constructor ; rw [htv_q1d1_high] ; exact ret_q1d1_high
  constructor ; rw [htv_q1d1_low] ; exact ret_q1d1_low
  constructor ; rw [htv_quotient2] ; exact ret_quotient2₁
  constructor ; rw [htv_divisor0] ; exact ret_divisor0₂
  constructor ; rw [htv_q2d0_high] ; exact ret_q2d0_high
  rw [htv_q2d0_low] ; exact ret_q2d0_low
  done

theorem auto_sound_u512_safe_divmod_by_u256_QUOTIENT3_LESS_THAN_DIVISOR0
  -- arguments
  (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 9))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 10))
  (htv_q1d0_low : q1d0_low = mem (σ.ap + 11))
  (htv_q1d0_high : q1d0_high = mem (σ.ap + 12))
  (htv_q0d1_low : q0d1_low = mem (σ.ap + 13))
  (htv_q0d1_high : q0d1_high = mem (σ.ap + 14))
  (htv_q1d1_low : q1d1_low = mem (σ.ap + 15))
  (htv_q1d1_high : q1d1_high = mem (σ.ap + 16))
  (htv_q2d0_low : q2d0_low = mem (σ.ap + 17))
  (htv_q2d0_high : q2d0_high = mem (σ.ap + 18))
  (htv_leftover : leftover = mem (σ.ap + 34))
  (htv_qd3_small : qd3_small = mem (σ.ap + 36))
  (htv_qd3_large : qd3_large = mem (σ.ap + 37))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 65, ap := σ.ap + 39, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_QUOTIENT3_LESS_THAN_DIVISOR0 κ range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem65 hmem with ha65
  have a65 : qd3_small = quotient3 := by
    rw [htv_qd3_small, htv_quotient3] ; exact ha65
  -- assert
  step_assert_eq hmem66 hmem with ha66
  have a66 : qd3_large = divisor0 := by
    rw [htv_qd3_large, htv_divisor0] ; exact ha66
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_MERGE mem σ
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large
    hmem
    htv_range_check
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_q1d0_low
    htv_q1d0_high
    htv_q0d1_low
    htv_q0d1_high
    htv_q1d1_low
    htv_q1d1_high
    htv_q2d0_low
    htv_q2d0_high
    htv_leftover
    htv_qd3_small
    htv_qd3_large
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a65
  use_only a66
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u512_safe_divmod_by_u256_DIVISOR1_EQ_ZERO
  -- arguments
  (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 9))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 10))
  (htv_q1d0_low : q1d0_low = mem (σ.ap + 11))
  (htv_q1d0_high : q1d0_high = mem (σ.ap + 12))
  (htv_q0d1_low : q0d1_low = mem (σ.ap + 13))
  (htv_q0d1_high : q0d1_high = mem (σ.ap + 14))
  (htv_q1d1_low : q1d1_low = mem (σ.ap + 15))
  (htv_q1d1_high : q1d1_high = mem (σ.ap + 16))
  (htv_q2d0_low : q2d0_low = mem (σ.ap + 17))
  (htv_q2d0_high : q2d0_high = mem (σ.ap + 18))
  (htv_leftover : leftover = mem (σ.ap + 34))
  (htv_qd3_small : qd3_small = mem (σ.ap + 36))
  (htv_qd3_large : qd3_large = mem (σ.ap + 37))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 57, ap := σ.ap + 37, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_DIVISOR1_EQ_ZERO κ range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem57 hmem, hmem58 hmem with ha57
  have a57 : divisor1 = zero := by
    rw [htv_divisor1, zero] ; exact ha57
  -- tempvar quotient3_less_than_divisor0
  mkdef hl_quotient3_less_than_divisor0 : quotient3_less_than_divisor0 = mem (σ.ap + 38)
  have htv_quotient3_less_than_divisor0 : quotient3_less_than_divisor0 = mem (σ.ap + 38) := by
    exact hl_quotient3_less_than_divisor0
  -- jump to QUOTIENT3_LESS_THAN_DIVISOR0 if quotient3_less_than_divisor0 != 0
  step_jnz hmem59 hmem, hmem60 hmem with hcond59 hcond59
  ·
    -- quotient3_less_than_divisor0 = 0
    have a59 : quotient3_less_than_divisor0 = 0 := by simp only [htv_quotient3_less_than_divisor0]; exact hcond59
    -- assert
    step_assert_eq hmem61 hmem with ha61
    have a61 : qd3_small = divisor0 := by
      rw [htv_qd3_small, htv_divisor0] ; exact ha61
    -- assert
    step_assert_eq hmem62 hmem with ha62
    have a62 : qd3_large = quotient3 := by
      rw [htv_qd3_large, htv_quotient3] ; exact ha62
    step_jump_imm hmem63 hmem, hmem64 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_MERGE mem σ
      range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large
      hmem
      htv_range_check
      htv_dividend3
      htv_divisor0
      htv_divisor1
      htv_quotient0
      htv_quotient1
      htv_quotient2
      htv_quotient3
      htv_remainder0
      htv_remainder1
      htv_q0d0_low
      htv_q0d0_high
      htv_q1d0_low
      htv_q1d0_high
      htv_q0d1_low
      htv_q0d1_high
      htv_q1d1_low
      htv_q1d1_high
      htv_q2d0_low
      htv_q2d0_high
      htv_leftover
      htv_qd3_small
      htv_qd3_large
      νbound)
    intros κ_MERGE _ h_MERGE
    rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only a57
    use_only quotient3_less_than_divisor0
    left
    use_only a59
    use_only a61
    use_only a62
    use_only κ_MERGE
    apply h_MERGE rc_h_range_check
    done
  -- quotient3_less_than_divisor0 ≠ 0
  have a59 : quotient3_less_than_divisor0 ≠ 0 := by simp only [htv_quotient3_less_than_divisor0]; exact hcond59
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_QUOTIENT3_LESS_THAN_DIVISOR0 mem σ
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large
    hmem
    htv_range_check
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_q1d0_low
    htv_q1d0_high
    htv_q0d1_low
    htv_q0d1_high
    htv_q1d1_low
    htv_q1d1_high
    htv_q2d0_low
    htv_q2d0_high
    htv_leftover
    htv_qd3_small
    htv_qd3_large
    νbound)
  intros κ_QUOTIENT3_LESS_THAN_DIVISOR0 _ h_QUOTIENT3_LESS_THAN_DIVISOR0
  rcases h_QUOTIENT3_LESS_THAN_DIVISOR0 with ⟨rc_m_le_QUOTIENT3_LESS_THAN_DIVISOR0, hblk_range_check_ptr, h_QUOTIENT3_LESS_THAN_DIVISOR0⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_QUOTIENT3_LESS_THAN_DIVISOR0 (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a57
  use_only quotient3_less_than_divisor0
  right
  use_only a59
  use_only κ_QUOTIENT3_LESS_THAN_DIVISOR0
  apply h_QUOTIENT3_LESS_THAN_DIVISOR0 rc_h_range_check
  done

theorem auto_sound_u512_safe_divmod_by_u256_QUOTIENT2_LESS_THAN_DIVISOR1
  -- arguments
  (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (htv_q0d0_low : q0d0_low = mem (σ.ap + 9))
  (htv_q0d0_high : q0d0_high = mem (σ.ap + 10))
  (htv_q1d0_low : q1d0_low = mem (σ.ap + 11))
  (htv_q1d0_high : q1d0_high = mem (σ.ap + 12))
  (htv_q0d1_low : q0d1_low = mem (σ.ap + 13))
  (htv_q0d1_high : q0d1_high = mem (σ.ap + 14))
  (htv_q1d1_low : q1d1_low = mem (σ.ap + 15))
  (htv_q1d1_high : q1d1_high = mem (σ.ap + 16))
  (htv_q2d0_low : q2d0_low = mem (σ.ap + 17))
  (htv_q2d0_high : q2d0_high = mem (σ.ap + 18))
  (htv_leftover : leftover = mem (σ.ap + 34))
  (htv_qd3_small : qd3_small = mem (σ.ap + 36))
  (htv_qd3_large : qd3_large = mem (σ.ap + 37))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 53, ap := σ.ap + 38, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_QUOTIENT2_LESS_THAN_DIVISOR1 κ range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem53 hmem with ha53
  have a53 : qd3_small = quotient2 := by
    rw [htv_qd3_small, htv_quotient2] ; exact ha53
  -- assert
  step_assert_eq hmem54 hmem with ha54
  have a54 : qd3_large = divisor1 := by
    rw [htv_qd3_large, htv_divisor1] ; exact ha54
  step_jump_imm hmem55 hmem, hmem56 hmem
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_MERGE mem σ
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large
    hmem
    htv_range_check
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_q1d0_low
    htv_q1d0_high
    htv_q0d1_low
    htv_q0d1_high
    htv_q1d1_low
    htv_q1d1_high
    htv_q2d0_low
    htv_q2d0_high
    htv_leftover
    htv_qd3_small
    htv_qd3_large
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a53
  use_only a54
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u512_safe_divmod_by_u256_After
  -- arguments
  (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend0 : dividend0 = mem (σ.fp - 8))
  (htv_dividend1 : dividend1 = mem (σ.fp - 7))
  (htv_dividend2 : dividend2 = mem (σ.fp - 6))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 18, ap := σ.ap + 19, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_After κ range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar q0d0_low
  mkdef hl_q0d0_low : q0d0_low = mem (σ.ap + 9)
  have htv_q0d0_low : q0d0_low = mem (σ.ap + 9) := by
    exact hl_q0d0_low
  -- tempvar q0d0_high
  mkdef hl_q0d0_high : q0d0_high = mem (σ.ap + 10)
  have htv_q0d0_high : q0d0_high = mem (σ.ap + 10) := by
    exact hl_q0d0_high
  -- tempvar q1d0_low
  mkdef hl_q1d0_low : q1d0_low = mem (σ.ap + 11)
  have htv_q1d0_low : q1d0_low = mem (σ.ap + 11) := by
    exact hl_q1d0_low
  -- tempvar q1d0_high
  mkdef hl_q1d0_high : q1d0_high = mem (σ.ap + 12)
  have htv_q1d0_high : q1d0_high = mem (σ.ap + 12) := by
    exact hl_q1d0_high
  -- tempvar q0d1_low
  mkdef hl_q0d1_low : q0d1_low = mem (σ.ap + 13)
  have htv_q0d1_low : q0d1_low = mem (σ.ap + 13) := by
    exact hl_q0d1_low
  -- tempvar q0d1_high
  mkdef hl_q0d1_high : q0d1_high = mem (σ.ap + 14)
  have htv_q0d1_high : q0d1_high = mem (σ.ap + 14) := by
    exact hl_q0d1_high
  -- tempvar q1d1_low
  mkdef hl_q1d1_low : q1d1_low = mem (σ.ap + 15)
  have htv_q1d1_low : q1d1_low = mem (σ.ap + 15) := by
    exact hl_q1d1_low
  -- tempvar q1d1_high
  mkdef hl_q1d1_high : q1d1_high = mem (σ.ap + 16)
  have htv_q1d1_high : q1d1_high = mem (σ.ap + 16) := by
    exact hl_q1d1_high
  -- tempvar q2d0_low
  mkdef hl_q2d0_low : q2d0_low = mem (σ.ap + 17)
  have htv_q2d0_low : q2d0_low = mem (σ.ap + 17) := by
    exact hl_q2d0_low
  -- tempvar q2d0_high
  mkdef hl_q2d0_high : q2d0_high = mem (σ.ap + 18)
  have htv_q2d0_high : q2d0_high = mem (σ.ap + 18) := by
    exact hl_q2d0_high
  -- tempvar part0
  step_assert_eq hmem18 hmem with tv_part0
  mkdef hl_part0 : part0 = q0d0_low + remainder0
  have htv_part0 : part0 = mem (σ.ap + 19) := by
    rw [hl_part0, htv_q0d0_low, htv_remainder0, tv_part0]
  -- tempvar part1
  step_assert_eq hmem19 hmem with tv_part1
  mkdef hl_part1 : part1 = part0 - dividend0
  have htv_part1 : part1 = mem (σ.ap + 20) := by
    rw [hl_part1, htv_part0, htv_dividend0, tv_part1, add_sub_cancel_right]
  -- tempvar leftover
  step_assert_eq hmem20 hmem, hmem21 hmem with tv_leftover
  mkdef hl_leftover : leftover = part1 / u128_limit
  have htv_leftover : leftover = mem (σ.ap + 21) := by
    rw [hl_leftover, htv_part1, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- assert
  step_assert_eq hmem22 hmem with ha22
  have a22 : leftover = leftover * leftover := by
    rw [htv_leftover] ; exact ha22
  -- tempvar part0₁
  step_assert_eq hmem23 hmem with tv_part0₁
  mkdef hl_part0₁ : part0₁ = leftover + q0d0_high
  have htv_part0₁ : part0₁ = mem (σ.ap + 22) := by
    rw [hl_part0₁, htv_leftover, htv_q0d0_high, tv_part0₁]
  -- tempvar part1₁
  step_assert_eq hmem24 hmem with tv_part1₁
  mkdef hl_part1₁ : part1₁ = part0₁ + q1d0_low
  have htv_part1₁ : part1₁ = mem (σ.ap + 23) := by
    rw [hl_part1₁, htv_part0₁, htv_q1d0_low, tv_part1₁]
  -- tempvar part2
  step_assert_eq hmem25 hmem with tv_part2
  mkdef hl_part2 : part2 = part1₁ + q0d1_low
  have htv_part2 : part2 = mem (σ.ap + 24) := by
    rw [hl_part2, htv_part1₁, htv_q0d1_low, tv_part2]
  -- tempvar part3
  step_assert_eq hmem26 hmem with tv_part3
  mkdef hl_part3 : part3 = part2 + remainder1
  have htv_part3 : part3 = mem (σ.ap + 25) := by
    rw [hl_part3, htv_part2, htv_remainder1, tv_part3]
  -- tempvar part4
  step_assert_eq hmem27 hmem with tv_part4
  mkdef hl_part4 : part4 = part3 - dividend1
  have htv_part4 : part4 = mem (σ.ap + 26) := by
    rw [hl_part4, htv_part3, htv_dividend1, tv_part4, add_sub_cancel_right]
  -- tempvar leftover₁
  step_assert_eq hmem28 hmem, hmem29 hmem with tv_leftover₁
  mkdef hl_leftover₁ : leftover₁ = part4 / u128_limit
  have htv_leftover₁ : leftover₁ = mem (σ.ap + 27) := by
    rw [hl_leftover₁, htv_part4, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover₁.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- range check for leftover₁
  step_assert_eq hmem30 hmem with rc_leftover₁
  -- tempvar a
  step_assert_eq hmem31 hmem, hmem32 hmem with tv_a
  mkdef hl_a : a = leftover₁ + u128_bound_minus_4
  have htv_a : a = mem (σ.ap + 28) := by
    rw [hl_a, htv_leftover₁, u128_bound_minus_4, tv_a]
  -- range check for a
  step_assert_eq hmem33 hmem with rc_a
  -- tempvar part0₂
  step_assert_eq hmem34 hmem with tv_part0₂
  mkdef hl_part0₂ : part0₂ = leftover₁ + q1d0_high
  have htv_part0₂ : part0₂ = mem (σ.ap + 29) := by
    rw [hl_part0₂, htv_leftover₁, htv_q1d0_high, tv_part0₂]
  -- tempvar part1₂
  step_assert_eq hmem35 hmem with tv_part1₂
  mkdef hl_part1₂ : part1₂ = part0₂ + q0d1_high
  have htv_part1₂ : part1₂ = mem (σ.ap + 30) := by
    rw [hl_part1₂, htv_part0₂, htv_q0d1_high, tv_part1₂]
  -- tempvar part2₁
  step_assert_eq hmem36 hmem with tv_part2₁
  mkdef hl_part2₁ : part2₁ = part1₂ + q1d1_low
  have htv_part2₁ : part2₁ = mem (σ.ap + 31) := by
    rw [hl_part2₁, htv_part1₂, htv_q1d1_low, tv_part2₁]
  -- tempvar part3₁
  step_assert_eq hmem37 hmem with tv_part3₁
  mkdef hl_part3₁ : part3₁ = part2₁ + q2d0_low
  have htv_part3₁ : part3₁ = mem (σ.ap + 32) := by
    rw [hl_part3₁, htv_part2₁, htv_q2d0_low, tv_part3₁]
  -- tempvar part4₁
  step_assert_eq hmem38 hmem with tv_part4₁
  mkdef hl_part4₁ : part4₁ = part3₁ - dividend2
  have htv_part4₁ : part4₁ = mem (σ.ap + 33) := by
    rw [hl_part4₁, htv_part3₁, htv_dividend2, tv_part4₁, add_sub_cancel_right]
  -- tempvar leftover₂
  step_assert_eq hmem39 hmem, hmem40 hmem with tv_leftover₂
  mkdef hl_leftover₂ : leftover₂ = part4₁ / u128_limit
  have htv_leftover₂ : leftover₂ = mem (σ.ap + 34) := by
    rw [hl_leftover₂, htv_part4₁, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover₂.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- range check for leftover₂
  step_assert_eq hmem41 hmem with rc_leftover₂
  -- tempvar a₁
  step_assert_eq hmem42 hmem, hmem43 hmem with tv_a₁
  mkdef hl_a₁ : a₁ = leftover₂ + u128_bound_minus_4
  have htv_a₁ : a₁ = mem (σ.ap + 35) := by
    rw [hl_a₁, htv_leftover₂, u128_bound_minus_4, tv_a₁]
  -- range check for a₁
  step_assert_eq hmem44 hmem with rc_a₁
  -- tempvar qd3_small
  mkdef hl_qd3_small : qd3_small = mem (σ.ap + 36)
  have htv_qd3_small : qd3_small = mem (σ.ap + 36) := by
    exact hl_qd3_small
  -- tempvar qd3_large
  mkdef hl_qd3_large : qd3_large = mem (σ.ap + 37)
  have htv_qd3_large : qd3_large = mem (σ.ap + 37) := by
    exact hl_qd3_large
  -- jump to DIVISOR1_EQ_ZERO if quotient3 != 0
  step_jnz hmem45 hmem, hmem46 hmem with hcond45 hcond45
  ·
    -- quotient3 = 0
    have a45 : quotient3 = 0 := by simp only [htv_quotient3]; exact hcond45
    -- tempvar quotient2_less_than_divisor1
    mkdef hl_quotient2_less_than_divisor1 : quotient2_less_than_divisor1 = mem (σ.ap + 38)
    have htv_quotient2_less_than_divisor1 : quotient2_less_than_divisor1 = mem (σ.ap + 38) := by
      exact hl_quotient2_less_than_divisor1
    -- jump to QUOTIENT2_LESS_THAN_DIVISOR1 if quotient2_less_than_divisor1 != 0
    step_jnz hmem47 hmem, hmem48 hmem with hcond47 hcond47
    ·
      -- quotient2_less_than_divisor1 = 0
      have a47 : quotient2_less_than_divisor1 = 0 := by simp only [htv_quotient2_less_than_divisor1]; exact hcond47
      -- assert
      step_assert_eq hmem49 hmem with ha49
      have a49 : qd3_small = divisor1 := by
        rw [htv_qd3_small, htv_divisor1] ; exact ha49
      -- assert
      step_assert_eq hmem50 hmem with ha50
      have a50 : qd3_large = quotient2 := by
        rw [htv_qd3_large, htv_quotient2] ; exact ha50
      step_jump_imm hmem51 hmem, hmem52 hmem
      arith_simps
      apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_MERGE mem σ
        range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large
        hmem
        htv_range_check
        htv_dividend3
        htv_divisor0
        htv_divisor1
        htv_quotient0
        htv_quotient1
        htv_quotient2
        htv_quotient3
        htv_remainder0
        htv_remainder1
        htv_q0d0_low
        htv_q0d0_high
        htv_q1d0_low
        htv_q1d0_high
        htv_q0d1_low
        htv_q0d1_high
        htv_q1d1_low
        htv_q1d1_high
        htv_q2d0_low
        htv_q2d0_high
        htv_leftover₂
        htv_qd3_small
        htv_qd3_large
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
      use_only q1d0_low
      use_only q1d0_high
      use_only q0d1_low
      use_only q0d1_high
      use_only q1d1_low
      use_only q1d1_high
      use_only q2d0_low
      use_only q2d0_high
      use_only part0, hl_part0
      use_only part1, hl_part1
      use_only leftover, hl_leftover
      use_only a22
      use_only part0₁, hl_part0₁
      use_only part1₁, hl_part1₁
      use_only part2, hl_part2
      use_only part3, hl_part3
      use_only part4, hl_part4
      use_only leftover₁, hl_leftover₁
      rc_app rc_h_range_check 7 htv_leftover₁ rc_leftover₁
      use_only a, hl_a
      rc_app rc_h_range_check 8 htv_a rc_a
      use_only part0₂, hl_part0₂
      use_only part1₂, hl_part1₂
      use_only part2₁, hl_part2₁
      use_only part3₁, hl_part3₁
      use_only part4₁, hl_part4₁
      use_only leftover₂, hl_leftover₂
      rc_app rc_h_range_check 9 htv_leftover₂ rc_leftover₂
      use_only a₁, hl_a₁
      rc_app rc_h_range_check 10 htv_a₁ rc_a₁
      use_only qd3_small
      use_only qd3_large
      left
      use_only a45
      use_only quotient2_less_than_divisor1
      left
      use_only a47
      use_only a49
      use_only a50
      use_only κ_MERGE
      apply h_MERGE rc_h_range_check
      done
    -- quotient2_less_than_divisor1 ≠ 0
    have a47 : quotient2_less_than_divisor1 ≠ 0 := by simp only [htv_quotient2_less_than_divisor1]; exact hcond47
    arith_simps
    apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_QUOTIENT2_LESS_THAN_DIVISOR1 mem σ
      range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large
      hmem
      htv_range_check
      htv_dividend3
      htv_divisor0
      htv_divisor1
      htv_quotient0
      htv_quotient1
      htv_quotient2
      htv_quotient3
      htv_remainder0
      htv_remainder1
      htv_q0d0_low
      htv_q0d0_high
      htv_q1d0_low
      htv_q1d0_high
      htv_q0d1_low
      htv_q0d1_high
      htv_q1d1_low
      htv_q1d1_high
      htv_q2d0_low
      htv_q2d0_high
      htv_leftover₂
      htv_qd3_small
      htv_qd3_large
      νbound)
    intros κ_QUOTIENT2_LESS_THAN_DIVISOR1 _ h_QUOTIENT2_LESS_THAN_DIVISOR1
    rcases h_QUOTIENT2_LESS_THAN_DIVISOR1 with ⟨rc_m_le_QUOTIENT2_LESS_THAN_DIVISOR1, hblk_range_check_ptr, h_QUOTIENT2_LESS_THAN_DIVISOR1⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_QUOTIENT2_LESS_THAN_DIVISOR1 (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only q0d0_low
    use_only q0d0_high
    use_only q1d0_low
    use_only q1d0_high
    use_only q0d1_low
    use_only q0d1_high
    use_only q1d1_low
    use_only q1d1_high
    use_only q2d0_low
    use_only q2d0_high
    use_only part0, hl_part0
    use_only part1, hl_part1
    use_only leftover, hl_leftover
    use_only a22
    use_only part0₁, hl_part0₁
    use_only part1₁, hl_part1₁
    use_only part2, hl_part2
    use_only part3, hl_part3
    use_only part4, hl_part4
    use_only leftover₁, hl_leftover₁
    rc_app rc_h_range_check 7 htv_leftover₁ rc_leftover₁
    use_only a, hl_a
    rc_app rc_h_range_check 8 htv_a rc_a
    use_only part0₂, hl_part0₂
    use_only part1₂, hl_part1₂
    use_only part2₁, hl_part2₁
    use_only part3₁, hl_part3₁
    use_only part4₁, hl_part4₁
    use_only leftover₂, hl_leftover₂
    rc_app rc_h_range_check 9 htv_leftover₂ rc_leftover₂
    use_only a₁, hl_a₁
    rc_app rc_h_range_check 10 htv_a₁ rc_a₁
    use_only qd3_small
    use_only qd3_large
    left
    use_only a45
    use_only quotient2_less_than_divisor1
    right
    use_only a47
    use_only κ_QUOTIENT2_LESS_THAN_DIVISOR1
    apply h_QUOTIENT2_LESS_THAN_DIVISOR1 rc_h_range_check
    done
  -- quotient3 ≠ 0
  have a45 : quotient3 ≠ 0 := by simp only [htv_quotient3]; exact hcond45
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_DIVISOR1_EQ_ZERO mem σ
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large
    hmem
    htv_range_check
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
    htv_remainder0
    htv_remainder1
    htv_q0d0_low
    htv_q0d0_high
    htv_q1d0_low
    htv_q1d0_high
    htv_q0d1_low
    htv_q0d1_high
    htv_q1d1_low
    htv_q1d1_high
    htv_q2d0_low
    htv_q2d0_high
    htv_leftover₂
    htv_qd3_small
    htv_qd3_large
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
  use_only q1d0_low
  use_only q1d0_high
  use_only q0d1_low
  use_only q0d1_high
  use_only q1d1_low
  use_only q1d1_high
  use_only q2d0_low
  use_only q2d0_high
  use_only part0, hl_part0
  use_only part1, hl_part1
  use_only leftover, hl_leftover
  use_only a22
  use_only part0₁, hl_part0₁
  use_only part1₁, hl_part1₁
  use_only part2, hl_part2
  use_only part3, hl_part3
  use_only part4, hl_part4
  use_only leftover₁, hl_leftover₁
  rc_app rc_h_range_check 7 htv_leftover₁ rc_leftover₁
  use_only a, hl_a
  rc_app rc_h_range_check 8 htv_a rc_a
  use_only part0₂, hl_part0₂
  use_only part1₂, hl_part1₂
  use_only part2₁, hl_part2₁
  use_only part3₁, hl_part3₁
  use_only part4₁, hl_part4₁
  use_only leftover₂, hl_leftover₂
  rc_app rc_h_range_check 9 htv_leftover₂ rc_leftover₂
  use_only a₁, hl_a₁
  rc_app rc_h_range_check 10 htv_a₁ rc_a₁
  use_only qd3_small
  use_only qd3_large
  right
  use_only a45
  use_only κ_DIVISOR1_EQ_ZERO
  apply h_DIVISOR1_EQ_ZERO rc_h_range_check
  done

theorem auto_sound_u512_safe_divmod_by_u256_HighDiff
  -- arguments
  (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 diff1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend0 : dividend0 = mem (σ.fp - 8))
  (htv_dividend1 : dividend1 = mem (σ.fp - 7))
  (htv_dividend2 : dividend2 = mem (σ.fp - 6))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  (htv_quotient0 : quotient0 = mem σ.ap)
  (htv_quotient1 : quotient1 = mem (σ.ap + 1))
  (htv_quotient2 : quotient2 = mem (σ.ap + 2))
  (htv_quotient3 : quotient3 = mem (σ.ap + 3))
  (htv_remainder0 : remainder0 = mem (σ.ap + 4))
  (htv_remainder1 : remainder1 = mem (σ.ap + 5))
  (htv_diff1 : diff1 = mem (σ.ap + 6))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 17, ap := σ.ap + 19, fp := σ.fp }
    (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (auto_spec_u512_safe_divmod_by_u256_HighDiff κ range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 diff1 (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- range check for diff1
  step_assert_eq hmem17 hmem with rc_diff1
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_After mem σ
    range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
    hmem
    htv_range_check
    htv_dividend0
    htv_dividend1
    htv_dividend2
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
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
  rc_app rc_h_range_check 6 htv_diff1 rc_diff1
  use_only κ_After
  apply h_After rc_h_range_check
  done

theorem auto_sound_u512_safe_divmod_by_u256
  -- arguments
  (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u512_safe_divmod_by_u256_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 9))
  (htv_dividend0 : dividend0 = mem (σ.fp - 8))
  (htv_dividend1 : dividend1 = mem (σ.fp - 7))
  (htv_dividend2 : dividend2 = mem (σ.fp - 6))
  (htv_dividend3 : dividend3 = mem (σ.fp - 5))
  (htv_divisor0 : divisor0 = mem (σ.fp - 4))
  (htv_divisor1 : divisor1 = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    12 ≤ κ ∧ RcEnsures mem (rcBound F) 12 (mem (σ.fp - 9)) (mem (τ.ap - 27))
      (spec_u512_safe_divmod_by_u256 κ range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 9) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar quotient0
  mkdef hl_quotient0 : quotient0 = mem σ.ap
  have htv_quotient0 : quotient0 = mem σ.ap := by
    exact hl_quotient0
  -- tempvar quotient1
  mkdef hl_quotient1 : quotient1 = mem (σ.ap + 1)
  have htv_quotient1 : quotient1 = mem (σ.ap + 1) := by
    exact hl_quotient1
  -- tempvar quotient2
  mkdef hl_quotient2 : quotient2 = mem (σ.ap + 2)
  have htv_quotient2 : quotient2 = mem (σ.ap + 2) := by
    exact hl_quotient2
  -- tempvar quotient3
  mkdef hl_quotient3 : quotient3 = mem (σ.ap + 3)
  have htv_quotient3 : quotient3 = mem (σ.ap + 3) := by
    exact hl_quotient3
  -- tempvar remainder0
  mkdef hl_remainder0 : remainder0 = mem (σ.ap + 4)
  have htv_remainder0 : remainder0 = mem (σ.ap + 4) := by
    exact hl_remainder0
  -- tempvar remainder1
  mkdef hl_remainder1 : remainder1 = mem (σ.ap + 5)
  have htv_remainder1 : remainder1 = mem (σ.ap + 5) := by
    exact hl_remainder1
  -- range check for quotient0
  step_assert_eq hmem0 hmem with rc_quotient0
  -- range check for quotient1
  step_assert_eq hmem1 hmem with rc_quotient1
  -- range check for quotient2
  step_assert_eq hmem2 hmem with rc_quotient2
  -- range check for quotient3
  step_assert_eq hmem3 hmem with rc_quotient3
  -- range check for remainder0
  step_assert_eq hmem4 hmem with rc_remainder0
  -- range check for remainder1
  step_assert_eq hmem5 hmem with rc_remainder1
  -- tempvar diff1
  step_assert_eq hmem6 hmem with tv_diff1
  mkdef hl_diff1 : diff1 = divisor1 - remainder1
  have htv_diff1 : diff1 = mem (σ.ap + 6) := by
    rw [hl_diff1, htv_divisor1, htv_remainder1, tv_diff1, add_sub_cancel_right]
  step_advance_ap hmem7 hmem, hmem8 hmem
  -- tempvar diff0
  mkdef hl_diff0 : diff0 = mem (σ.ap + 7)
  have htv_diff0 : diff0 = mem (σ.ap + 7) := by
    exact hl_diff0
  -- tempvar diff0_min_1
  mkdef hl_diff0_min_1 : diff0_min_1 = mem (σ.ap + 8)
  have htv_diff0_min_1 : diff0_min_1 = mem (σ.ap + 8) := by
    exact hl_diff0_min_1
  -- jump to HighDiff if diff1 != 0
  step_jnz hmem9 hmem, hmem10 hmem with hcond9 hcond9
  ·
    -- diff1 = 0
    have a9 : diff1 = 0 := by simp only [htv_diff1]; exact hcond9
    -- assert
    step_assert_eq hmem11 hmem with ha11
    have a11 : diff0 = divisor0 - remainder0 := by
      rw [htv_diff0, htv_divisor0, htv_remainder0, ha11, add_sub_cancel_right]
    -- assert
    step_assert_eq hmem12 hmem, hmem13 hmem with ha12
    have a12 : diff0_min_1 = diff0 - one := by
      rw [htv_diff0_min_1, htv_diff0, one, ha12, add_sub_cancel_right]
    -- range check for diff0_min_1
    step_assert_eq hmem14 hmem with rc_diff0_min_1
    step_jump_imm hmem15 hmem, hmem16 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_After mem σ
      range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
      hmem
      htv_range_check
      htv_dividend0
      htv_dividend1
      htv_dividend2
      htv_dividend3
      htv_divisor0
      htv_divisor1
      htv_quotient0
      htv_quotient1
      htv_quotient2
      htv_quotient3
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
    suffices auto_spec : auto_spec_u512_safe_divmod_by_u256 _ range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ by
      apply sound_u512_safe_divmod_by_u256 ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only quotient0
    use_only quotient1
    use_only quotient2
    use_only quotient3
    use_only remainder0
    use_only remainder1
    rc_app rc_h_range_check 0 htv_quotient0 rc_quotient0
    rc_app rc_h_range_check 1 htv_quotient1 rc_quotient1
    rc_app rc_h_range_check 2 htv_quotient2 rc_quotient2
    rc_app rc_h_range_check 3 htv_quotient3 rc_quotient3
    rc_app rc_h_range_check 4 htv_remainder0 rc_remainder0
    rc_app rc_h_range_check 5 htv_remainder1 rc_remainder1
    use_only diff1, hl_diff1
    use_only diff0
    use_only diff0_min_1
    left
    use_only a9
    use_only a11
    use_only a12
    rc_app rc_h_range_check 6 htv_diff0_min_1 rc_diff0_min_1
    use_only κ_After
    apply h_After rc_h_range_check
    done
  -- diff1 ≠ 0
  have a9 : diff1 ≠ 0 := by simp only [htv_diff1]; exact hcond9
  arith_simps
  apply ensuresbRet_trans (auto_sound_u512_safe_divmod_by_u256_HighDiff mem σ
    range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 diff1
    hmem
    htv_range_check
    htv_dividend0
    htv_dividend1
    htv_dividend2
    htv_dividend3
    htv_divisor0
    htv_divisor1
    htv_quotient0
    htv_quotient1
    htv_quotient2
    htv_quotient3
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
  suffices auto_spec : auto_spec_u512_safe_divmod_by_u256 _ range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ by
    apply sound_u512_safe_divmod_by_u256 ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only quotient0
  use_only quotient1
  use_only quotient2
  use_only quotient3
  use_only remainder0
  use_only remainder1
  rc_app rc_h_range_check 0 htv_quotient0 rc_quotient0
  rc_app rc_h_range_check 1 htv_quotient1 rc_quotient1
  rc_app rc_h_range_check 2 htv_quotient2 rc_quotient2
  rc_app rc_h_range_check 3 htv_quotient3 rc_quotient3
  rc_app rc_h_range_check 4 htv_remainder0 rc_remainder0
  rc_app rc_h_range_check 5 htv_remainder1 rc_remainder1
  use_only diff1, hl_diff1
  use_only diff0
  use_only diff0_min_1
  right
  use_only a9
  use_only κ_HighDiff
  apply h_HighDiff rc_h_range_check
  done
