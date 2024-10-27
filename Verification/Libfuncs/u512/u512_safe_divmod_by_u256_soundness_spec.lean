import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u512_safe_divmod_by_u256_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def zero : F := (0 : F) -- 0
def one : F := (1 : F) -- 1
def u128_bound_minus_4 : F := (340282366920938463463374607431768211452 : F) -- u128::MAX - 3
def u128_bound_minus_u64_bound : F := (340282366920938463444927863358058659840 : F) -- u128::MAX - u64::MAX as u128
def u128_limit : F := (340282366920938463463374607431768211456 : F) -- (BigInt::from(u128::MAX) + 1) as BigInt

theorem u128_limit_eq : u128_limit = (u128Limit : F) := by unfold u128_limit u128Limit ; norm_cast
theorem u128_bound_minus_4_eq : (u128_bound_minus_4 : F) = ↑(u128Limit - 4) := by
  unfold u128_bound_minus_4 u128Limit ; norm_num1
theorem u128_bound_minus_u64_bound_eq : (u128_bound_minus_u64_bound : F) = ↑(u128Limit - u64Limit) := by
  unfold u128_bound_minus_u64_bound u128Limit u64Limit ; norm_num1

/-
  The specification.
-/

def spec_u512_safe_divmod_by_u256 (κ : ℕ) (
    range_check
    dividend0 dividend1 dividend2 dividend3
    divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∀ n_dividend0 : ℕ, is_u128_of dividend0 n_dividend0 →
  ∀ n_dividend1 : ℕ, is_u128_of dividend1 n_dividend1 →
  ∀ n_dividend2 : ℕ, is_u128_of dividend2 n_dividend2 →
  ∀ n_dividend3 : ℕ, is_u128_of dividend3 n_dividend3 →
  ∀ n_divisor0 : ℕ,  is_u128_of divisor0 n_divisor0 →
  ∀ n_divisor1 : ℕ,  is_u128_of divisor1 n_divisor1 →
    -- Guarantee specs
    u128_mul_guarantee ρ_quotient0 divisor0 ρ_q0d0_high ρ_q0d0_low →
    u128_mul_guarantee ρ_quotient1 divisor0 ρ_q1d0_high ρ_q1d0_low →
    u128_mul_guarantee ρ_quotient0 divisor1 ρ_q0d1_high ρ_q0d1_low →
    u128_mul_guarantee ρ_quotient1 divisor1 ρ_q1d1_high ρ_q1d1_low →
    u128_mul_guarantee ρ_quotient2 divisor0 ρ_q2d0_high ρ_q2d0_low →
    ∃ n_quotient0 : ℕ, is_u128_of ρ_quotient0 n_quotient0 ∧
    ∃ n_quotient1 : ℕ, is_u128_of ρ_quotient1  n_quotient1∧
    ∃ n_quotient2 : ℕ, is_u128_of ρ_quotient2 n_quotient2 ∧
    ∃ n_quotient3 : ℕ, is_u128_of ρ_quotient3 n_quotient3 ∧
    ∃ n_remainder0 : ℕ, is_u128_of ρ_remainder0 n_remainder0 ∧
    ∃ n_remainder1 : ℕ, is_u128_of ρ_remainder1 n_remainder1 ∧
      u256_from_limbs n_remainder1 n_remainder0 < u256_from_limbs n_divisor1 n_divisor0 ∧
      u512_from_limbs n_dividend3 n_dividend2 n_dividend1 n_dividend0 =
        u512_from_limbs n_quotient3 n_quotient2 n_quotient1 n_quotient0 *
        u256_from_limbs n_divisor1 n_divisor0 +
          u256_from_limbs n_remainder1 n_remainder0

/- Automatic specifications -/

def auto_spec_u512_safe_divmod_by_u256_MERGE (κ : ℕ) (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∃ qd3_small_fixed : F, qd3_small_fixed = qd3_small + u128_bound_minus_u64_bound ∧
  IsRangeChecked (rcBound F) qd3_small_fixed ∧
  ∃ qd3 : F, qd3 = qd3_small * qd3_large ∧
  ∃ part0₁ : F, part0₁ = leftover + q2d0_high ∧
  ∃ part1₁ : F, part1₁ = part0₁ + q1d1_high ∧
  dividend3 = part1₁ + qd3 ∧
  ρ_quotient0 = quotient0 ∧
  ρ_quotient1 = quotient1 ∧
  ρ_quotient2 = quotient2 ∧
  ρ_quotient3 = quotient3 ∧
  ρ_remainder0 = remainder0 ∧
  ρ_remainder1 = remainder1 ∧
  ρ_quotient0₁ = quotient0 ∧
  ρ_divisor0 = divisor0 ∧
  ρ_q0d0_high = q0d0_high ∧
  ρ_q0d0_low = q0d0_low ∧
  ρ_quotient0₂ = quotient0 ∧
  ρ_divisor1 = divisor1 ∧
  ρ_q0d1_high = q0d1_high ∧
  ρ_q0d1_low = q0d1_low ∧
  ρ_quotient1₁ = quotient1 ∧
  ρ_divisor0₁ = divisor0 ∧
  ρ_q1d0_high = q1d0_high ∧
  ρ_q1d0_low = q1d0_low ∧
  ρ_quotient1₂ = quotient1 ∧
  ρ_divisor1₁ = divisor1 ∧
  ρ_q1d1_high = q1d1_high ∧
  ρ_q1d1_low = q1d1_low ∧
  ρ_quotient2₁ = quotient2 ∧
  ρ_divisor0₂ = divisor0 ∧
  ρ_q2d0_high = q2d0_high ∧
  ρ_q2d0_low = q2d0_low

def auto_spec_u512_safe_divmod_by_u256_QUOTIENT3_LESS_THAN_DIVISOR0 (κ : ℕ) (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  qd3_small = quotient3 ∧
  qd3_large = divisor0 ∧
  ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_MERGE κ₁
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low

def auto_spec_u512_safe_divmod_by_u256_DIVISOR1_EQ_ZERO (κ : ℕ) (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  divisor1 = zero ∧
  ∃ quotient3_less_than_divisor0 : F,
  (
    (quotient3_less_than_divisor0 = 0 ∧
      qd3_small = divisor0 ∧
      qd3_large = quotient3 ∧
      ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_MERGE κ₁
        range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
    ) ∨
    (quotient3_less_than_divisor0 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_QUOTIENT3_LESS_THAN_DIVISOR0 κ₁
        range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
    )
  )

def auto_spec_u512_safe_divmod_by_u256_QUOTIENT2_LESS_THAN_DIVISOR1 (κ : ℕ) (range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  qd3_small = quotient2 ∧
  qd3_large = divisor1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_MERGE κ₁
    range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low

def auto_spec_u512_safe_divmod_by_u256_After (κ : ℕ) (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∃ q0d0_low : F,
  ∃ q0d0_high : F,
  ∃ q1d0_low : F,
  ∃ q1d0_high : F,
  ∃ q0d1_low : F,
  ∃ q0d1_high : F,
  ∃ q1d1_low : F,
  ∃ q1d1_high : F,
  ∃ q2d0_low : F,
  ∃ q2d0_high : F,
  ∃ part0 : F, part0 = q0d0_low + remainder0 ∧
  ∃ part1 : F, part1 = part0 - dividend0 ∧
  ∃ leftover : F, leftover = part1 / u128_limit ∧
  leftover = leftover * leftover ∧
  ∃ part0₁ : F, part0₁ = leftover + q0d0_high ∧
  ∃ part1₁ : F, part1₁ = part0₁ + q1d0_low ∧
  ∃ part2 : F, part2 = part1₁ + q0d1_low ∧
  ∃ part3 : F, part3 = part2 + remainder1 ∧
  ∃ part4 : F, part4 = part3 - dividend1 ∧
  ∃ leftover₁ : F, leftover₁ = part4 / u128_limit ∧
  IsRangeChecked (rcBound F) leftover₁ ∧
  ∃ a : F, a = leftover₁ + u128_bound_minus_4 ∧
  IsRangeChecked (rcBound F) a ∧
  ∃ part0₂ : F, part0₂ = leftover₁ + q1d0_high ∧
  ∃ part1₂ : F, part1₂ = part0₂ + q0d1_high ∧
  ∃ part2₁ : F, part2₁ = part1₂ + q1d1_low ∧
  ∃ part3₁ : F, part3₁ = part2₁ + q2d0_low ∧
  ∃ part4₁ : F, part4₁ = part3₁ - dividend2 ∧
  ∃ leftover₂ : F, leftover₂ = part4₁ / u128_limit ∧
  IsRangeChecked (rcBound F) leftover₂ ∧
  ∃ a₁ : F, a₁ = leftover₂ + u128_bound_minus_4 ∧
  IsRangeChecked (rcBound F) a₁ ∧
  ∃ qd3_small : F,
  ∃ qd3_large : F,
  (
    (quotient3 = 0 ∧
      ∃ quotient2_less_than_divisor1 : F,
      (
        (quotient2_less_than_divisor1 = 0 ∧
          qd3_small = divisor1 ∧
          qd3_large = quotient2 ∧
          ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_MERGE κ₁
            range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
        ) ∨
        (quotient2_less_than_divisor1 ≠ 0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_QUOTIENT2_LESS_THAN_DIVISOR1 κ₁
            range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
        )
      )
    ) ∨
    (quotient3 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_DIVISOR1_EQ_ZERO κ₁
        range_check dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high leftover₂ qd3_small qd3_large ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
    )
  )

def auto_spec_u512_safe_divmod_by_u256_HighDiff (κ : ℕ) (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 diff1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  IsRangeChecked (rcBound F) diff1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_After κ₁
    range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low

def auto_spec_u512_safe_divmod_by_u256 (κ : ℕ) (range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ quotient0 : F,
  ∃ quotient1 : F,
  ∃ quotient2 : F,
  ∃ quotient3 : F,
  ∃ remainder0 : F,
  ∃ remainder1 : F,
  IsRangeChecked (rcBound F) quotient0 ∧
  IsRangeChecked (rcBound F) quotient1 ∧
  IsRangeChecked (rcBound F) quotient2 ∧
  IsRangeChecked (rcBound F) quotient3 ∧
  IsRangeChecked (rcBound F) remainder0 ∧
  IsRangeChecked (rcBound F) remainder1 ∧
  ∃ diff1 : F, diff1 = divisor1 - remainder1 ∧
  ∃ diff0 : F,
  ∃ diff0_min_1 : F,
  (
    (diff1 = 0 ∧
      diff0 = divisor0 - remainder0 ∧
      diff0_min_1 = diff0 - one ∧
      IsRangeChecked (rcBound F) diff0_min_1 ∧
      ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_After κ₁
        range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
    ) ∨
    (diff1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_HighDiff κ₁
        range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1 quotient0 quotient1 quotient2 quotient3 remainder0 remainder1 diff1 ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low
    )
  )

/- Manually reorganized automatic specifications. -/

def man_auto_spec_u512_safe_divmod_by_u256_After (κ : ℕ)
    (range_check
      dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      -- Function local arguments.
      quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
      -- Function return arguments.
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
       -- guarantees
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∃ (q0d0_low q0d0_high q1d0_low q1d0_high q0d1_low q0d1_high q1d1_low q1d1_high q2d0_low q2d0_high : F),
  ∃ part0 : F, part0 = q0d0_low + remainder0 ∧
  ∃ part1 : F, part1 = part0 - dividend0 ∧
  ∃ leftover : F, leftover = part1 / u128_limit ∧
  leftover = leftover * leftover ∧
  ∃ part0₁ : F, part0₁ = leftover + q0d0_high ∧
  ∃ part1₁ : F, part1₁ = part0₁ + q1d0_low ∧
  ∃ part2 : F, part2 = part1₁ + q0d1_low ∧
  ∃ part3 : F, part3 = part2 + remainder1 ∧
  ∃ part4 : F, part4 = part3 - dividend1 ∧
  ∃ leftover₁ : F, leftover₁ = part4 / u128_limit ∧
  IsRangeChecked (rcBound F) leftover₁ ∧
  ∃ a : F, a = leftover₁ + u128_bound_minus_4 ∧
  IsRangeChecked (rcBound F) a ∧
  ∃ part0₂ : F, part0₂ = leftover₁ + q1d0_high ∧
  ∃ part1₂ : F, part1₂ = part0₂ + q0d1_high ∧
  ∃ part2₁ : F, part2₁ = part1₂ + q1d1_low ∧
  ∃ part3₁ : F, part3₁ = part2₁ + q2d0_low ∧
  ∃ part4₁ : F, part4₁ = part3₁ - dividend2 ∧
  ∃ leftover₂ : F, leftover₂ = part4₁ / u128_limit ∧
  IsRangeChecked (rcBound F) leftover₂ ∧
  ∃ a₁ : F, a₁ = leftover₂ + u128_bound_minus_4 ∧
  IsRangeChecked (rcBound F) a₁ ∧
  ∃ qd3_small : F,
  ∃ qd3_large : F,
  (
    (quotient3 = 0 ∧
      ∃ quotient2_less_than_divisor1 : F,
      (
        (quotient2_less_than_divisor1 = 0 ∧
          qd3_small = divisor1 ∧
          qd3_large = quotient2
        ) ∨
        (quotient2_less_than_divisor1 ≠ 0 ∧
          qd3_small = quotient2 ∧
          qd3_large = divisor1
        )
      )
    ) ∨
    (quotient3 ≠ 0 ∧
      divisor1 = zero ∧
      ∃ quotient3_less_than_divisor0 : F,
      (
        (quotient3_less_than_divisor0 = 0 ∧
          qd3_small = divisor0 ∧
          qd3_large = quotient3
        ) ∨
        (quotient3_less_than_divisor0 ≠ 0 ∧
          qd3_small = quotient3 ∧
          qd3_large = divisor0
        )
      )
    )
  ) ∧
  ∃ (κ₁ : ℕ), auto_spec_u512_safe_divmod_by_u256_MERGE κ₁
        range_check dividend3 divisor0 divisor1
        quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
        q0d0_low q0d0_high
        q1d0_low q1d0_high
        q0d1_low q0d1_high
        q1d1_low q1d1_high
        q2d0_low q2d0_high
        leftover₂ qd3_small qd3_large
        ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
        ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
        ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
        ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
        ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
        ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low


def man_auto_spec_u512_safe_divmod_by_u256 (κ : ℕ)
    (range_check
      dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ quotient0 : F,
  ∃ quotient1 : F,
  ∃ quotient2 : F,
  ∃ quotient3 : F,
  ∃ remainder0 : F,
  ∃ remainder1 : F,
  IsRangeChecked (rcBound F) quotient0 ∧
  IsRangeChecked (rcBound F) quotient1 ∧
  IsRangeChecked (rcBound F) quotient2 ∧
  IsRangeChecked (rcBound F) quotient3 ∧
  IsRangeChecked (rcBound F) remainder0 ∧
  IsRangeChecked (rcBound F) remainder1 ∧
  ∃ diff1 : F, diff1 = divisor1 - remainder1 ∧
  ∃ diff0 : F,
  ∃ diff0_min_1 : F,
  (
    (diff1 = 0 ∧
      diff0 = divisor0 - remainder0 ∧
      diff0_min_1 = diff0 - one ∧
      IsRangeChecked (rcBound F) diff0_min_1
    ) ∨
    (diff1 ≠ 0 ∧
      IsRangeChecked (rcBound F) diff1
    )
  ) ∧
  ∃ (κ₁ : ℕ), man_auto_spec_u512_safe_divmod_by_u256_After κ₁
      range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low

/-
  # Lemmas
-/

lemma man_auto_of_auto_spec_u512_safe_divmod_by_u256_After {κ : ℕ}
    {range_check
      dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      -- Function local arguments.
      quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
      -- Function return arguments.
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
       -- guarantees
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F} :
  auto_spec_u512_safe_divmod_by_u256_After κ range_check
    dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
    quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low →
  man_auto_spec_u512_safe_divmod_by_u256_After κ range_check
    dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
    quotient0 quotient1 quotient2 quotient3 remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low := by
  intro h_auto
  rcases h_auto with ⟨q0d0_low, q0d0_high, q1d0_low, q1d0_high, q0d1_low, q0d1_high, q1d1_low, q1d1_high, q2d0_low, q2d0_high,
    part0, h_part0, part1, h_part1, leftover, h_leftover, h_leftover_eq,
    part0₁, h_part0₁, part1₁, h_part1₁, part2, h_part2, part3, h_part3, part4, h_part4, leftover₁, h_leftover₁, h_rc_leftover₁, a, h_a, h_rc_a,
    part0₂, h_part0₂, part1₂, h_part1₂, part2₁, h_part2₁, part3₁, h_part3₁, part4₁, h_part4₁, leftover₂, h_leftover₂, h_rc_leftover₂, a₁, h_a₁, h_rc_a₁,
    qd3_small, qd3_large, h_auto⟩

  use q0d0_low, q0d0_high, q1d0_low, q1d0_high, q0d1_low, q0d1_high, q1d1_low, q1d1_high, q2d0_low, q2d0_high,
    part0, h_part0, part1, h_part1, leftover, h_leftover, h_leftover_eq,
    part0₁, h_part0₁, part1₁, h_part1₁, part2, h_part2, part3, h_part3, part4, h_part4, leftover₁, h_leftover₁, h_rc_leftover₁, a, h_a, h_rc_a,
    part0₂, h_part0₂, part1₂, h_part1₂, part2₁, h_part2₁, part3₁, h_part3₁, part4₁, h_part4₁, leftover₂, h_leftover₂, h_rc_leftover₂, a₁, h_a₁, h_rc_a₁,
    qd3_small, qd3_large

  rcases h_auto with h_quotient3_eq_zero | h_quotient3_ne_zero

  rcases h_quotient3_eq_zero with ⟨h_quotient3_eq_zero, quotient2_less_than_divisor1, h_q2_lt_d1_eq_zero | h_q2_lt_d1_ne_zero⟩

  rcases h_q2_lt_d1_eq_zero with ⟨h_q2_lt_d1_eq_zero, h_qd3_small, h_qd3_large, κ₁, h_MERGE⟩
  constructor
  · left
    use h_quotient3_eq_zero, quotient2_less_than_divisor1
    left
    use h_q2_lt_d1_eq_zero, h_qd3_small, h_qd3_large
  use κ₁

  rcases h_q2_lt_d1_ne_zero with ⟨h_q2_lt_d1_ne_zero, κ₀, h_qd3_small, h_qd3_large, κ₁, h_MERGE⟩
  constructor
  · left
    use h_quotient3_eq_zero, quotient2_less_than_divisor1
    right
    use h_q2_lt_d1_ne_zero, h_qd3_small, h_qd3_large
  use κ₁

  rcases h_quotient3_ne_zero with ⟨h_quotient3_ne_zero, κ₀, h_divisor1_eq_zero, q3_lt_d0, h_q3_lt_d0_eq_zero | h_q3_lt_d0_ne_zero⟩

  rcases h_q3_lt_d0_eq_zero with ⟨h_q3_lt_d0_eq_zero, h_qd3_small, h_qd3_large, κ₁, h_MERGE⟩
  constructor
  · right
    use h_quotient3_ne_zero, h_divisor1_eq_zero, q3_lt_d0
    left
    use h_q3_lt_d0_eq_zero, h_qd3_small, h_qd3_large
  use κ₁

  rcases h_q3_lt_d0_ne_zero with ⟨h_q3_lt_d0_ne_zero, κ₀, h_qd3_small, h_qd3_large, κ₁, h_MERGE⟩
  constructor
  · right
    use h_quotient3_ne_zero, h_divisor1_eq_zero, q3_lt_d0
    right
    use h_q3_lt_d0_ne_zero, h_qd3_small, h_qd3_large
  use κ₁

lemma man_auto_of_auto_spec_u512_safe_divmod_by_u256 {κ : ℕ}
    {range_check
      dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F} :
  auto_spec_u512_safe_divmod_by_u256 κ range_check
    dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low →
  man_auto_spec_u512_safe_divmod_by_u256 κ range_check
    dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low := by

  intro h_auto
  rcases h_auto with ⟨κ, h_κ, q0, q1, q2, q3, r0, r1, h_rc_q0, h_rc_q1, h_rc_q2, h_rc_q3, h_rc_r0, h_rc_r1,
    diff1, h_diff1, diff0, diff0_min_1, h_auto⟩

  use κ, h_κ, q0, q1, q2, q3, r0, r1, h_rc_q0, h_rc_q1, h_rc_q2, h_rc_q3, h_rc_r0, h_rc_r1,
    diff1, h_diff1, diff0, diff0_min_1

  rcases h_auto with h_diff1_eq_zero|h_diff1_ne_zero

  rcases h_diff1_eq_zero with ⟨h_diff1_eq_zero, h_diff0, h_diff0_min_1, h_rc_diff0_min_1, κ₁, h_After⟩
  constructor
  · left
    use h_diff1_eq_zero, h_diff0, h_diff0_min_1
  use κ₁
  apply man_auto_of_auto_spec_u512_safe_divmod_by_u256_After h_After

  rcases h_diff1_ne_zero with ⟨h_diff1, κ₀, h_rc_diff1, κ₁, h_After⟩
  constructor
  · right
    use h_diff1
  use κ₁
  apply man_auto_of_auto_spec_u512_safe_divmod_by_u256_After h_After


lemma remainder_lt_divisor (n_dvsr0 n_dvsr1 n_r0 n_r1 : ℕ) (diff0 diff0_min_1 : F)
      (h_diff :
          (↑n_dvsr1 - ↑n_r1 : F) = 0 ∧
          diff0 = ↑n_dvsr0 - ↑n_r0 ∧
          diff0_min_1 = diff0 - one ∧
          IsRangeChecked (rcBound F) diff0_min_1
        ∨
          (↑n_dvsr1 - ↑n_r1 : F) ≠ 0 ∧
          IsRangeChecked (rcBound F) ((↑n_dvsr1 - ↑n_r1) : F))
      (h_n_dvsr0_lt : n_dvsr0 < u128Limit)
      (h_n_dvsr1_lt : n_dvsr1 < u128Limit)
      (h_n_r0_lt : n_r0 < u128Limit)
      (h_n_r1_lt : n_r1 < u128Limit) :
    u256_from_limbs n_r1 n_r0 < u256_from_limbs n_dvsr1 n_dvsr0 := by
  unfold u256_from_limbs

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  rcases h_diff with ⟨hb1, rfl, hb3, ⟨n_diff0_min_1, h_n_diff0_min_1_lt, rfl⟩⟩ | ⟨hb, ⟨n_diff, h_n_diff_lt, h_n_diff⟩⟩
  · rw [sub_eq_iff_eq_add, zero_add] at hb1
    have h_dvsr1_r1_eq : n_dvsr1 = n_r1 :=
      PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_dvsr1_lt) (lt_PRIME_of_lt_u128Limit h_n_r1_lt) hb1
    rw [h_dvsr1_r1_eq]
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, one, ←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add] at hb3
    have h_eq_n_dvsr0_eq : n_diff0_min_1 + 1 + n_r0 = n_dvsr0 := by
      apply PRIME.nat_coe_field_inj _ (lt_PRIME_of_lt_u128Limit h_n_dvsr0_lt) hb3
      apply lt_trans _ u128Limit_triple_lt_PRIME
      apply Nat.add_lt_add _ h_n_r0_lt ; apply Nat.add_lt_add (lt_of_lt_of_le h_n_diff0_min_1_lt h_rcBound) ; norm_num1
    apply Nat.add_lt_add_left _ _
    rw [←h_eq_n_dvsr0_eq] ; apply Nat.lt_add_of_pos_left
    apply lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_left _ _)
  have h_n_r1_ne_n_dvsr1 : n_r1 ≠ n_dvsr1 := by
    by_contra h ; apply hb ; rw [sub_eq_iff_eq_add, zero_add, h]
  have h_n_r1_eq_n_dvsr1 : n_dvsr1 = n_diff + n_r1 := by
    rw [sub_eq_iff_eq_add, ←Nat.cast_add] at h_n_diff
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_dvsr1_lt) _ h_n_diff
    apply lt_trans _ u128Limit_double_lt_PRIME
    apply Nat.add_lt_add (lt_of_lt_of_le h_n_diff_lt h_rcBound) h_n_r1_lt
  have h_n_r1_lt_n_dvsr1 : n_r1 < n_dvsr1 := by
    apply lt_of_le_of_ne _ h_n_r1_ne_n_dvsr1
    apply le_trans (Nat.le_add_left _ _) (le_of_eq h_n_r1_eq_n_dvsr1.symm)
  apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
  rw [←(Nat.mul_one u128Limit)] at h_n_r0_lt
  apply lt_of_lt_of_le (Nat.add_lt_add_left h_n_r0_lt _)
  rw [←Nat.left_distrib]
  apply Nat.mul_le_mul_left _ ; apply Nat.succ_le_of_lt ; exact h_n_r1_lt_n_dvsr1

lemma limb0_eq (n_q0d0_low n_r0 n_dvd0 : ℕ)
    (part0 part1 leftover: F)
    (h_part0: part0 = ↑n_q0d0_low + ↑n_r0)
    (h_part1 : part1 = part0 - ↑n_dvd0)
    (h_leftover1: leftover = part1 / u128_limit)
    (h_leftover2: leftover = leftover * leftover)
    (h_n_q0d0_low_lt: n_q0d0_low < u128Limit)
    (h_n_r0_lt: n_r0 < u128Limit)
    (h_n_dvd0_lt : n_dvd0 < u128Limit) :
  ∃ n_lo :ℕ,
    leftover = ↑n_lo ∧ (n_lo = 0 ∨ n_lo = 1) ∧ n_q0d0_low + n_r0  = n_dvd0 + n_lo * u128Limit := by
  have lo_zero_or_one : leftover = 0 ∨ leftover = 1 := by
    apply eq_zero_or_eq_one_of_mul_eq_self h_leftover2.symm
  have h_p1 := (eq_div_iff_mul_eq u128Limit_coe_ne_zero).mp h_leftover1
  cases' lo_zero_or_one with h_0 h_1
  · use_only 0 ; rw [Nat.cast_zero] ; use_only h_0 ; constructor ; left ; apply Eq.refl
    rw [zero_mul, add_zero]
    rw [←h_p1, h_0, zero_mul] at h_part1 ;
    rw [sub_eq_zero.mp h_part1.symm, ←Nat.cast_add] at h_part0
    apply PRIME.nat_coe_field_inj _ _ h_part0.symm
    apply add_lt_PRIME_of_lt h_n_q0d0_low_lt h_n_r0_lt
    apply lt_trans h_n_dvd0_lt u128Limit_lt_PRIME
  use_only 1 ; rw [Nat.cast_one] ; use_only h_1 ; constructor ; right ; apply Eq.refl
  rw [←h_p1, h_1, one_mul, eq_sub_iff_add_eq] at h_part1
  rw [←h_part1, u128_limit_eq, ←Nat.cast_add, ←Nat.cast_add, add_comm u128Limit] at h_part0
  apply PRIME.nat_coe_field_inj _ _ h_part0.symm
  apply add_lt_PRIME_of_lt h_n_q0d0_low_lt h_n_r0_lt
  apply add_lt_PRIME_of_le (le_of_lt h_n_dvd0_lt) (le_of_eq rfl)

lemma limb_1_or_2_eq (n_lo n_x0 n_x1 n_x2 n_x3 n_dvd n_lo₁ n_a : ℕ)
      (part0 part1 part2 part3 part4 : F)
      (h_part0: part0 = ↑n_lo + ↑n_x0)
      (h_part1: part1 = part0 + ↑n_x1)
      (h_part2: part2 = part1 + ↑n_x2)
      (h_part3: part3 = part2 + ↑n_x3)
      (h_part4: part4 = part3 - ↑n_dvd)
      (h_lo₁: ↑n_lo₁ = part4 / u128_limit)
      (h_n_lo₁_lt: n_lo₁ < u128Limit)
      (h_a: (n_a : F) = ↑n_lo₁ + u128_bound_minus_4)
      (h_n_a_lt: n_a < u128Limit)
      (h_n_lo_lt : n_lo < 4)
      (h_n_x0_lt : n_x0 < u128Limit)
      (h_n_x1_lt : n_x1 < u128Limit)
      (h_n_x2_lt : n_x2 < u128Limit)
      (h_n_x3_lt : n_x3 < u128Limit)
      (h_n_dvd_lt : n_dvd < u128Limit) :
    n_lo₁ < 4 ∧ n_lo + n_x0 + n_x1 + n_x2 + n_x3 = n_dvd + n_lo₁ * u128Limit := by
  have h_n_lo₁_lt : n_lo₁ < 4 := by
    have h : n_a = n_lo₁ + (u128Limit - 4) := by
      rw [u128_bound_minus_4_eq, ←Nat.cast_add] at h_a
      apply PRIME.nat_coe_field_inj (lt_trans h_n_a_lt u128Limit_lt_PRIME) _ h_a
      apply add_lt_PRIME_of_lt h_n_lo₁_lt ; norm_num1
    rw [←(Nat.add_sub_of_le (show 4 ≤ u128Limit by norm_num1)), h, add_lt_add_iff_right _] at h_n_a_lt
    apply h_n_a_lt
  constructor
  apply h_n_lo₁_lt
  have h_p4 := (eq_div_iff_mul_eq u128Limit_coe_ne_zero).mp h_lo₁
  rw [h_part0] at h_part1
  rw [h_part1] at h_part2
  rw [h_part2] at h_part3
  rw [h_part3, ←h_p4, eq_sub_iff_add_eq, u128_limit_eq, add_comm] at h_part4 ; norm_cast at h_part4
  apply PRIME.nat_coe_field_inj _ _ h_part4.symm
  apply lt_trans _
    (show u128Limit + u128Limit + u128Limit + u128Limit + u128Limit < PRIME by unfold PRIME u128Limit ; norm_num1)
  apply Nat.add_lt_add _ h_n_x3_lt
  apply Nat.add_lt_add _ h_n_x2_lt
  apply Nat.add_lt_add _ h_n_x1_lt
  apply Nat.add_lt_add _ h_n_x0_lt
  apply lt_trans h_n_lo_lt (by norm_num1)
  apply lt_trans _ (show u128Limit + 4 * u128Limit < PRIME by unfold PRIME u128Limit ; norm_num1)
  apply Nat.add_lt_add h_n_dvd_lt
  apply Nat.mul_lt_mul_of_pos_right h_n_lo₁_lt (by unfold u128Limit ; norm_num1)

-- limb 3 lemmas

lemma qd3_small_lt_u64Limit {m n_qd3_sf : ℕ}
      (h_m_lt : m < u128Limit)
      (h_n_qd3_sf_lt : n_qd3_sf < u128Limit)
      (h_qd3_sf : (n_qd3_sf : F) = ↑m + u128_bound_minus_u64_bound) :
    m < u64Limit := by
  rw [u128_bound_minus_u64_bound_eq, ←Nat.cast_add] at h_qd3_sf
  have h_qd3_sf_eq : n_qd3_sf = m + (u128Limit - u64Limit) := by
    apply PRIME.nat_coe_field_inj (lt_trans h_n_qd3_sf_lt u128Limit_lt_PRIME) _ h_qd3_sf
    apply lt_trans (Nat.add_lt_add_right h_m_lt _)
    unfold u128Limit u64Limit PRIME ; norm_num1
  rw [←(Nat.add_sub_of_le (le_of_lt u64Limit_lt_u128Limit))] at h_n_qd3_sf_lt
  rw [h_qd3_sf_eq, add_lt_add_iff_right _] at h_n_qd3_sf_lt
  exact h_n_qd3_sf_lt

lemma limb3_branch_eq { n_q2d0_high n_q1d1_high n_qd3_small n_qd3_large n_lo n_dvd3 : ℕ }
      (h : (n_dvd3 : F) = ↑(n_lo + n_q2d0_high + n_q1d1_high + n_qd3_small * n_qd3_large))
      (h_n_dvd3_lt : n_dvd3 < u128Limit)
      (h_n_q1d1_high_lt : n_q1d1_high < u128Limit)
      (h_n_q2d0_high_lt : n_q2d0_high < u128Limit)
      (h_n_lo_lt : n_lo < 4)
      (h_n_qd3_small_lt_u64 : n_qd3_small < u64Limit)
      (h_n_qd3_large_lt : n_qd3_large < u128Limit):
    n_q2d0_high + n_q1d1_high + n_qd3_small * n_qd3_large + n_lo = n_dvd3 := by
  symm ; rw [add_comm] ; simp only [←add_assoc] ; apply PRIME.nat_coe_field_inj _ _ h
  apply lt_PRIME_of_lt_u128Limit h_n_dvd3_lt
  apply lt_trans _
    (show u128Limit + u128Limit + u128Limit + u64Limit * u128Limit < PRIME by unfold PRIME ; norm_num1)
  apply Nat.add_lt_add _ (Nat.mul_lt_mul_of_le_of_lt (le_of_lt h_n_qd3_small_lt_u64) h_n_qd3_large_lt (by norm_num1))
  apply Nat.add_lt_add _ h_n_q1d1_high_lt
  apply Nat.add_lt_add (lt_trans h_n_lo_lt (by norm_num1)) h_n_q2d0_high_lt

-- Main limb 3 lemma
lemma limb3_eq (n_dvd1 n_dvd3 n_dvsr0 n_dvsr1 n_q2 n_q3 n_lo n_q1d1_high n_q2d0_high n_qd3_sf : ℕ)
  (qd3_small qd3_large qd3 part0 part1 : F)
  (h_set_qd3 :
    ((n_q3 : F) = 0 ∧
      ∃ (quotient2_less_than_divisor1 : F),
        quotient2_less_than_divisor1 = 0 ∧ qd3_small = ↑n_dvsr1 ∧ qd3_large = ↑n_q2 ∨
          quotient2_less_than_divisor1 ≠ 0 ∧ qd3_small = ↑n_q2 ∧ qd3_large = ↑n_dvsr1) ∨
    (n_q3 : F) ≠ 0 ∧
      (n_dvsr1 : F) = 0 ∧
        ∃ (quotient3_less_than_divisor0 : F),
          quotient3_less_than_divisor0 = 0 ∧ qd3_small = ↑n_dvsr0 ∧ qd3_large = ↑n_q3 ∨
            quotient3_less_than_divisor0 ≠ 0 ∧ qd3_small = ↑n_q3 ∧ qd3_large = ↑n_dvsr0)
  (h_qd3_sf : (n_qd3_sf : F) = qd3_small + u128_bound_minus_u64_bound)
  (h_n_qd3_sf_lt : n_qd3_sf < u128Limit)
  (h_qd3 : qd3 = qd3_small * qd3_large)
  (h_part0 : part0 = ↑n_lo + ↑n_q2d0_high)
  (h_part1 : part1 = part0 + ↑n_q1d1_high)
  (h_dividend : (n_dvd3 : F) = part1 + qd3)
  (h_n_dvd1_lt : n_dvd1 < u128Limit)
  (h_n_dvd3_lt : n_dvd3 < u128Limit)
  (h_n_dvsr0_lt : n_dvsr0 < u128Limit)
  (h_n_dvsr1_lt : n_dvsr1 < u128Limit)
  (h_n_q2_lt : n_q2 < u128Limit)
  (h_n_q3_lt : n_q3 < u128Limit)
  (h_n_lo_lt : n_lo < 4)
  (h_n_q1d1_high_lt : n_q1d1_high < u128Limit)
  (h_n_q2d0_high_lt : n_q2d0_high < u128Limit) :
  ∃ (n_qd3_small n_qd3_large : ℕ),
    (
      n_dvsr1 = 0 ∧ (n_qd3_small = n_dvsr0 ∧ n_qd3_large = n_q3 ∨ n_qd3_small = n_q3 ∧ n_qd3_large = n_dvsr0)
      ∨
      n_q3 = 0 ∧ (n_qd3_small = n_dvsr1 ∧ n_qd3_large = n_q2 ∨ n_qd3_small = n_q2 ∧ n_qd3_large = n_dvsr1)
    ) ∧
    n_q2d0_high + n_q1d1_high + n_qd3_small * n_qd3_large + n_lo = n_dvd3 := by
  rw [h_part0] at h_part1
  rw [h_part1, h_qd3] at h_dividend
  cases' h_set_qd3 with h_qd3_zero h_qd3_ne_zero
  · rcases h_qd3_zero with ⟨n_q3_zero, -, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
    use_only n_dvsr1, n_q2
    constructor ; right ; constructor
    · apply PRIME.nat_coe_field_zero _ rfl n_q3_zero
      apply lt_trans h_n_q3_lt (by unfold PRIME u128Limit ; norm_num1)
    left ; use rfl
    · norm_cast at h_dividend
      have h_n_dvsr1_lt_u64 : n_dvsr1 < u64Limit := qd3_small_lt_u64Limit h_n_dvsr1_lt h_n_qd3_sf_lt h_qd3_sf
      apply limb3_branch_eq h_dividend h_n_dvd3_lt h_n_q1d1_high_lt h_n_q2d0_high_lt h_n_lo_lt h_n_dvsr1_lt_u64 h_n_q2_lt
    use_only n_q2, n_dvsr1
    constructor ; right ; constructor
    · apply PRIME.nat_coe_field_zero _ rfl n_q3_zero
      apply lt_trans h_n_q3_lt (by unfold PRIME u128Limit ; norm_num1)
    right ; use rfl
    · norm_cast at h_dividend
      have h_n_q2_lt_u64 : n_q2 < u64Limit := qd3_small_lt_u64Limit h_n_q2_lt h_n_qd3_sf_lt h_qd3_sf
      apply limb3_branch_eq h_dividend h_n_dvd3_lt h_n_q1d1_high_lt h_n_q2d0_high_lt h_n_lo_lt h_n_q2_lt_u64 h_n_dvsr1_lt
  rcases h_qd3_ne_zero with ⟨-, n_dvsr1_zero, -, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  use_only n_dvsr0, n_q3
  constructor ; left ; constructor
  · apply PRIME.nat_coe_field_zero _ rfl n_dvsr1_zero
    apply lt_trans h_n_dvsr1_lt (by unfold PRIME u128Limit ; norm_num1)
  left ; use rfl
  · norm_cast at h_dividend
    have h_n_dvsr0_lt_u64 : n_dvsr0 < u64Limit := qd3_small_lt_u64Limit h_n_dvsr0_lt h_n_qd3_sf_lt h_qd3_sf
    apply limb3_branch_eq h_dividend h_n_dvd3_lt h_n_q1d1_high_lt h_n_q2d0_high_lt h_n_lo_lt h_n_dvsr0_lt_u64 h_n_q3_lt
  use_only n_q3, n_dvsr0
  constructor ; left ; constructor
  · apply PRIME.nat_coe_field_zero _ rfl n_dvsr1_zero
    apply lt_trans h_n_dvsr1_lt (by unfold PRIME u128Limit ; norm_num1)
  right ; use rfl
  · norm_cast at h_dividend
    have h_n_q3_lt_u64 : n_q3 < u64Limit := qd3_small_lt_u64Limit h_n_q3_lt h_n_qd3_sf_lt h_qd3_sf
    apply limb3_branch_eq h_dividend h_n_dvd3_lt h_n_q1d1_high_lt h_n_q2d0_high_lt h_n_lo_lt h_n_q3_lt_u64 h_n_dvsr0_lt

/-
  # Main soundness theorem
-/

set_option maxRecDepth 1024 in
theorem sound_u512_safe_divmod_by_u256
    (κ : ℕ)
    (range_check
      dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
      ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
      ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
      ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
      ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
      ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low : F)
    (h_auto : auto_spec_u512_safe_divmod_by_u256 κ
                range_check dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
                ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
                ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
                ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
                ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
                ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
                ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low) :
  spec_u512_safe_divmod_by_u256 κ range_check
    dividend0 dividend1 dividend2 dividend3 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_quotient2 ρ_quotient3 ρ_remainder0 ρ_remainder1
    ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ρ_quotient0₂ ρ_divisor1 ρ_q0d1_high ρ_q0d1_low
    ρ_quotient1₁ ρ_divisor0₁ ρ_q1d0_high ρ_q1d0_low
    ρ_quotient1₂ ρ_divisor1₁ ρ_q1d1_high ρ_q1d1_low
    ρ_quotient2₁ ρ_divisor0₂ ρ_q2d0_high ρ_q2d0_low := by

  replace h_auto := man_auto_of_auto_spec_u512_safe_divmod_by_u256 h_auto

  rintro n_dvd0 ⟨h_n_dvd0_lt, rfl⟩ n_dvd1 ⟨h_n_dvd1_lt, rfl⟩ n_dvd2 ⟨h_n_dvd2_lt, rfl⟩
    n_dvd3 ⟨h_n_dvd3_lt, rfl⟩ n_dvsr0 ⟨h_n_dvsr0_lt, rfl⟩ n_dvsr1 ⟨h_n_dvsr1_lt, rfl⟩

  rintro h_g_q0d0 h_g_q1d0 h_g_q0d1 h_g_q1d1 h_g_q2d0

  rcases h_auto with ⟨-, -, q0, q1, q2, q3, r0, r1, rc_q0, rc_q1, rc_q2, rc_q3, rc_r0, rc_r1, h_auto⟩
  rcases h_auto with ⟨_, rfl, diff0, diff0_min_1, h_auto⟩

  -- First branch
  rcases h_auto with ⟨h_d_min_r, h_auto⟩

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  rcases h_auto with ⟨-, q0d0_low, q0d0_high, q1d0_low, q1d0_high, q0d1_low, q0d1_high,
    q1d1_low, q1d1_high, q2d0_low, q2d0_high, h_auto⟩

  -- limb 0

  rcases h_auto with ⟨part0, h_part0, part1, h_part1, h_auto⟩
  rcases h_auto with ⟨leftover, h_leftover1, h_leftover2, h_auto⟩

  -- limb1

  rcases h_auto with ⟨part0₁, h_part0₁, part1₁, h_part1₁, part2, h_part2, part3, h_part3, part4, h_part4, h_auto⟩
  rcases h_auto with ⟨leftover₁, h_leftover₁, ⟨n_lo₁, h_n_lo₁_lt, rfl⟩, h_auto⟩
  replace h_n_lo₁_lt := lt_of_lt_of_le h_n_lo₁_lt h_rcBound
  rcases h_auto with ⟨a, h_a, ⟨n_a, h_n_a_lt, rfl⟩, h_auto⟩
  replace h_n_a_lt := lt_of_lt_of_le h_n_a_lt h_rcBound

  -- limb 2

  rcases h_auto with ⟨part0₂, h_part0₂, part1₂, h_part1₂, part2₁, h_part2₁, part3₁, h_part3₁, part4₁, h_part4₁, h_auto⟩
  rcases h_auto with ⟨leftover₂, h_leftover₂, ⟨n_lo₂, h_n_lo₂_lt, rfl⟩, h_auto⟩
  replace h_n_lo₂_lt := lt_of_lt_of_le h_n_lo₂_lt h_rcBound
  rcases h_auto with ⟨a₁, h_a₁, ⟨n_a₁, h_n_a₁_lt, rfl⟩, h_auto⟩
  replace h_n_a₁_lt := lt_of_lt_of_le h_n_a₁_lt h_rcBound

  -- limb 3

  -- set_qd3 are the branches that set the values of qd3_small and qd3_large
  rcases h_auto with ⟨qd3_small, qd3_large, set_qd3, h_auto⟩
  rcases h_auto with ⟨-, qd3_sf, h_qd3_sf, ⟨n_qd3_sf, h_n_qd3_sf_lt, rfl⟩, qd3, h_qd3, h_auto⟩
  replace h_n_qd3_sf_lt := lt_of_lt_of_le h_n_qd3_sf_lt h_rcBound
  rcases h_auto with ⟨part0₃, h_part0₃, part1₃, h_part1₃, h_dividend₃, h_auto⟩

  -- return arguments
  rcases h_auto with ⟨rfl, rfl, rfl, rfl, rfl, rfl, h_auto⟩
  rcases h_auto with ⟨-, -, rfl, rfl, -, -, rfl, rfl, -, -, rfl, rfl, -, -, rfl, rfl, -, -, rfl, rfl⟩

  -- Unwrap the range checks (and use them immediately)
  rcases rc_q0 with ⟨n_q0, h_n_q0_lt, rfl⟩
  replace h_n_q0_lt := lt_of_lt_of_le h_n_q0_lt h_rcBound
  use_only n_q0, ⟨h_n_q0_lt, rfl⟩
  rcases rc_q1 with ⟨n_q1, h_n_q1_lt, rfl⟩
  replace h_n_q1_lt := lt_of_lt_of_le h_n_q1_lt h_rcBound
  use_only n_q1, ⟨h_n_q1_lt, rfl⟩
  rcases rc_q2 with ⟨n_q2, h_n_q2_lt, rfl⟩
  replace h_n_q2_lt := lt_of_lt_of_le h_n_q2_lt h_rcBound
  use_only n_q2, ⟨h_n_q2_lt, rfl⟩
  rcases rc_q3 with ⟨n_q3, h_n_q3_lt, rfl⟩
  replace h_n_q3_lt := lt_of_lt_of_le h_n_q3_lt h_rcBound
  use_only n_q3, ⟨h_n_q3_lt, rfl⟩
  rcases rc_r0 with ⟨n_r0, h_n_r0_lt, rfl⟩
  replace h_n_r0_lt := lt_of_lt_of_le h_n_r0_lt h_rcBound
  use_only n_r0, ⟨h_n_r0_lt, rfl⟩
  rcases rc_r1 with ⟨n_r1, h_n_r1_lt, rfl⟩
  replace h_n_r1_lt := lt_of_lt_of_le h_n_r1_lt h_rcBound
  use_only n_r1, ⟨h_n_r1_lt, rfl⟩

  -- Unfold the u128_mul_guarantees
  rcases h_g_q0d0 ⟨h_n_q0_lt, rfl⟩ ⟨h_n_dvsr0_lt, rfl⟩ with
    ⟨n_q0d0_high, ⟨h_n_q0d0_high_lt, rfl⟩, n_q0d0_low, ⟨h_n_q0d0_low_lt, rfl⟩, h_q0d0_mul⟩
  rcases h_g_q1d0 ⟨h_n_q1_lt, rfl⟩ ⟨h_n_dvsr0_lt, rfl⟩ with
    ⟨n_q1d0_high, ⟨h_n_q1d0_high_lt, rfl⟩, n_q1d0_low, ⟨h_n_q1d0_low_lt, rfl⟩, h_q1d0_mul⟩
  rcases h_g_q0d1 ⟨h_n_q0_lt, rfl⟩ ⟨h_n_dvsr1_lt, rfl⟩ with
    ⟨n_q0d1_high, ⟨h_n_q0d1_high_lt, rfl⟩, n_q0d1_low, ⟨h_n_q0d1_low_lt, rfl⟩, h_q0d1_mul⟩
  rcases h_g_q1d1 ⟨h_n_q1_lt, rfl⟩ ⟨h_n_dvsr1_lt, rfl⟩ with
    ⟨n_q1d1_high, ⟨h_n_q1d1_high_lt, rfl⟩, n_q1d1_low, ⟨h_n_q1d1_low_lt, rfl⟩, h_q1d1_mul⟩
  rcases h_g_q2d0 ⟨h_n_q2_lt, rfl⟩ ⟨h_n_dvsr0_lt, rfl⟩ with
    ⟨n_q2d0_high, ⟨h_n_q2d0_high_lt, rfl⟩, n_q2d0_low, ⟨h_n_q2d0_low_lt, rfl⟩, h_q2d0_mul⟩
  clear h_g_q0d0 h_g_q1d0 h_g_q0d1 h_g_q1d1 h_g_q2d0

  -- remainder < divisor
  constructor
  · apply remainder_lt_divisor n_dvsr0 n_dvsr1 n_r0 n_r1 diff0 diff0_min_1 h_d_min_r
      h_n_dvsr0_lt h_n_dvsr1_lt h_n_r0_lt h_n_r1_lt

  -- limb 0
  have h_limb0 : ∃ n_lo : ℕ,
      leftover = ↑n_lo ∧ (n_lo = 0 ∨ n_lo = 1) ∧ n_q0d0_low + n_r0 = n_dvd0  + n_lo * u128Limit :=
    limb0_eq n_q0d0_low n_r0 n_dvd0 part0 part1 leftover
      h_part0 h_part1 h_leftover1 h_leftover2
      h_n_q0d0_low_lt h_n_r0_lt h_n_dvd0_lt
  rcases h_limb0 with ⟨n_lo, rfl, h_n_lo_zero_or_one, h_limb0_eq⟩
  have h_n_lo_le : n_lo ≤ 1 := by
    cases' h_n_lo_zero_or_one with h h ; rw [h] ; apply Nat.zero_le 1 ; rw [h]

  -- limb 1
  have h_limb1 : n_lo₁ < 4 ∧
      n_lo + n_q0d0_high + n_q1d0_low + n_q0d1_low + n_r1 = n_dvd1 + n_lo₁ * u128Limit :=
    limb_1_or_2_eq n_lo n_q0d0_high n_q1d0_low n_q0d1_low n_r1 n_dvd1 n_lo₁ n_a
      part0₁ part1₁ part2 part3 part4
      h_part0₁ h_part1₁ h_part2 h_part3 h_part4
      h_leftover₁ h_n_lo₁_lt
      h_a h_n_a_lt (lt_of_le_of_lt h_n_lo_le (by norm_num1))
      h_n_q0d0_high_lt h_n_q1d0_low_lt h_n_q0d1_low_lt h_n_r1_lt h_n_dvd1_lt
  rcases h_limb1 with ⟨h_n_lo₁_lt, h_limb1_eq⟩

  -- limb 2
  have h_limb2 : n_lo₂ < 4 ∧
      n_lo₁ + n_q1d0_high + n_q0d1_high + n_q1d1_low + n_q2d0_low = n_dvd2 + n_lo₂ * u128Limit :=
    limb_1_or_2_eq n_lo₁ n_q1d0_high n_q0d1_high n_q1d1_low n_q2d0_low n_dvd2 n_lo₂ n_a₁
      part0₂ part1₂ part2₁ part3₁ part4₁
      h_part0₂ h_part1₂ h_part2₁ h_part3₁ h_part4₁
      h_leftover₂ h_n_lo₂_lt
      h_a₁ h_n_a₁_lt h_n_lo₁_lt
      h_n_q1d0_high_lt h_n_q0d1_high_lt h_n_q1d1_low_lt h_n_q2d0_low_lt h_n_dvd2_lt
  rcases h_limb2 with ⟨h_n_lo₂_lt, h_limb2_eq⟩

  -- limb 3
  have h_limb3 : ∃ (n_qd3_small n_qd3_large : ℕ),
      (
        n_dvsr1 = 0 ∧ (n_qd3_small = n_dvsr0 ∧ n_qd3_large = n_q3 ∨ n_qd3_small = n_q3 ∧ n_qd3_large = n_dvsr0)
        ∨
        n_q3 = 0 ∧ (n_qd3_small = n_dvsr1 ∧ n_qd3_large = n_q2 ∨ n_qd3_small = n_q2 ∧ n_qd3_large = n_dvsr1)
      ) ∧
      n_q2d0_high + n_q1d1_high + n_qd3_small * n_qd3_large + n_lo₂ = n_dvd3 :=
    limb3_eq n_dvd1 n_dvd3 n_dvsr0 n_dvsr1 n_q2 n_q3 n_lo₂ n_q1d1_high n_q2d0_high n_qd3_sf
      qd3_small qd3_large qd3 part0₃ part1₃
      set_qd3
      h_qd3_sf h_n_qd3_sf_lt h_qd3
      h_part0₃ h_part1₃ h_dividend₃
      h_n_dvd1_lt h_n_dvd3_lt h_n_dvsr0_lt h_n_dvsr1_lt h_n_q2_lt h_n_q3_lt h_n_lo₂_lt
      h_n_q1d1_high_lt h_n_q2d0_high_lt
  rcases h_limb3 with ⟨n_qd3_small, n_qd3_large, h_qd3_set, h_limb3_eq⟩

  have h_q3_dvsr1_zero : n_q3 * n_dvsr1 = 0 := by
    rcases h_qd3_set with ⟨n_dvsr1_zero, -⟩ | ⟨n_q3_zero, -⟩
    rw [n_dvsr1_zero, mul_zero]
    rw [n_q3_zero, zero_mul]

  have h_q3_dvsr0_eq : n_q3 * n_dvsr0 + n_q2 * n_dvsr1 = n_qd3_small * n_qd3_large := by
    rcases h_qd3_set with ⟨n_dvsr1_zero, h_sl⟩ | ⟨n_q3_zero, h_sl⟩
    rw [n_dvsr1_zero, mul_zero, add_zero]
    rcases h_sl with ⟨h_s, h_l⟩ | ⟨h_s, h_l⟩
    rw [h_s, h_l, mul_comm]
    rw [h_s, h_l]
    rw [n_q3_zero, zero_mul, zero_add]
    rcases h_sl with ⟨h_s, h_l⟩ | ⟨h_s, h_l⟩
    rw [h_s, h_l, mul_comm]
    rw [h_s, h_l]

  unfold u512_from_limbs u256_from_limbs

  -- Substitute limbs for lhs of equality
  rw [add_comm (u128Limit ^ 3 * n_dvd3)]
  rw [←h_limb3_eq] ; rw [add_comm _ n_lo₂] ; rw [Nat.left_distrib (u128Limit ^ 3)]
  rw [←add_assoc] ; rw [pow_succ u128Limit 2] ; rw [mul_assoc] ; rw [←Nat.left_distrib (u128Limit ^ 2)]
  rw [mul_comm _ n_lo₂]
  rw [←h_limb2_eq]
  rw [add_comm _ (u128Limit * n_dvd1)]
  simp only [add_assoc n_lo₁ _ _]
  rw [Nat.left_distrib (u128Limit ^ 2)]
  rw [pow_succ' u128Limit 1, pow_one]
  simp only [←add_assoc]
  rw [mul_assoc] ; rw [←Nat.left_distrib u128Limit] ; rw [mul_comm _ n_lo₁]
  rw [←h_limb1_eq]
  rw [add_comm _ n_dvd0]
  simp only [←add_assoc]
  simp only [add_assoc n_lo _ _]
  rw [Nat.left_distrib u128Limit]
  simp only [←add_assoc]
  rw [mul_comm _ n_lo]
  rw [←h_limb0_eq]

  -- Rearrange rhs and substitute limb3 assumptions
  have h_q_dvsr :
    (u128Limit * u128Limit * u128Limit * n_q3 + u128Limit * u128Limit * n_q2 + u128Limit * n_q1 + n_q0) *
      (u128Limit * n_dvsr1 + n_dvsr0) =
    u128Limit * u128Limit * u128Limit * u128Limit * (n_q3 * n_dvsr1) + u128Limit * u128Limit * u128Limit * (n_q3 * n_dvsr0) +
    u128Limit * u128Limit * u128Limit * (n_q2 * n_dvsr1) + u128Limit * u128Limit * (n_q2 * n_dvsr0) +
    u128Limit * u128Limit * (n_q1 * n_dvsr1) + u128Limit * (n_q1 * n_dvsr0) +
    u128Limit * (n_q0 * n_dvsr1) + n_q0 * n_dvsr0 := by ring
  rw [h_q2d0_mul, h_q1d1_mul, h_q1d0_mul, h_q0d1_mul, h_q0d0_mul] at h_q_dvsr
  simp only [u256_from_limbs] at h_q_dvsr

  rw [h_q3_dvsr1_zero, mul_zero, zero_add] at h_q_dvsr
  rw [←Nat.left_distrib, h_q3_dvsr0_eq] at h_q_dvsr

  -- lhs and rhs are equal
  rw [h_q_dvsr]
  ring
