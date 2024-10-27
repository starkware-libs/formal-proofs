import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

namespace u256_safe_divmod_soundness

def zero : F := (0 : F) -- 0
def one : F := (1 : F) -- 1
def u128_bound_minus_u64_bound : F := (340282366920938463444927863358058659840 : F) -- u128::MAX - u64::MAX as u128
def u128_limit : F := (340282366920938463463374607431768211456 : F) -- (BigInt::from(u128::MAX) + 1) as BigInt

theorem u128_limit_eq : u128_limit = (u128Limit : F) := by unfold u128_limit u128Limit ; norm_cast


def spec_u256_safe_divmod (κ : ℕ)
    (range_check
      dividend0 dividend1 divisor0 divisor1
      ρ_quotient0 ρ_quotient1
      ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∀ n_dividend0 : Nat, is_u128_of dividend0 n_dividend0 →
  ∀ n_dividend1 : Nat, is_u128_of dividend1 n_dividend1 →
  ∀ n_divisor0  : Nat, is_u128_of divisor0 n_divisor0 →
  ∀ n_divisor1  : Nat, is_u128_of divisor1 n_divisor1 →
    u128_mul_guarantee ρ_quotient0 divisor0 ρ_q0d0_high ρ_q0d0_low →
    ∃ n_quotient0 : Nat, is_u128_of ρ_quotient0 n_quotient0 ∧
    ∃ n_quotient1 : Nat, is_u128_of ρ_quotient1 n_quotient1 ∧
    ∃ n_remainder0 : Nat, is_u128_of ρ_remainder0 n_remainder0 ∧
    ∃ n_remainder1 : Nat, is_u128_of ρ_remainder1 n_remainder1 ∧
      u256_from_limbs n_remainder1 n_remainder0 < u256_from_limbs n_divisor1 n_divisor0 ∧
      u256_from_limbs n_dividend1 n_dividend0 =
        u256_from_limbs n_quotient1 n_quotient0 * u256_from_limbs n_divisor1 n_divisor0 +
          u256_from_limbs n_remainder1 n_remainder0

def auto_spec_u256_safe_divmod_MERGE (κ : ℕ) (range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∃ qd1_small_fixed : F, qd1_small_fixed = qd1_small + u128_bound_minus_u64_bound ∧
  IsRangeChecked (rcBound F) qd1_small_fixed ∧
  ∃ qd1 : F, qd1 = qd1_small * qd1_large ∧
  ∃ part0₁ : F, part0₁ = leftover + q0d0_high ∧
  ∃ part1₁ : F, part1₁ = part0₁ + remainder1 ∧
  dividend1 = part1₁ + qd1 ∧
  ρ_quotient0 = quotient0 ∧
  ρ_quotient1 = quotient1 ∧
  ρ_remainder0 = remainder0 ∧
  ρ_remainder1 = remainder1 ∧
  ρ_quotient0₁ = quotient0 ∧
  ρ_divisor0 = divisor0 ∧
  ρ_q0d0_high = q0d0_high ∧
  ρ_q0d0_low = q0d0_low

def auto_spec_u256_safe_divmod_QUOTIENT1_LESS_THAN_DIVISOR0 (κ : ℕ) (range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  qd1_small = quotient1 ∧
  qd1_large = divisor0 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_MERGE κ₁
    range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low

def auto_spec_u256_safe_divmod_DIVISOR1_EQ_ZERO (κ : ℕ) (range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  divisor1 = zero ∧
  ∃ quotient1_less_than_divisor0 : F,
  (
    (quotient1_less_than_divisor0 = 0 ∧
      qd1_small = divisor0 ∧
      qd1_large = quotient1 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_MERGE κ₁
        range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ) ∨
    (quotient1_less_than_divisor0 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_QUOTIENT1_LESS_THAN_DIVISOR0 κ₁
        range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    )
  )

def auto_spec_u256_safe_divmod_QUOTIENT0_LESS_THAN_DIVISOR1 (κ : ℕ) (range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  qd1_small = quotient0 ∧
  qd1_large = divisor1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_MERGE κ₁
    range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low

def auto_spec_u256_safe_divmod_After (κ : ℕ) (range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∃ q0d0_low : F,
  ∃ q0d0_high : F,
  ∃ part0 : F, part0 = q0d0_low + remainder0 ∧
  ∃ part1 : F, part1 = part0 - dividend0 ∧
  ∃ leftover : F, leftover = part1 / u128_limit ∧
  leftover = leftover * leftover ∧
  ∃ qd1_small : F,
  ∃ qd1_large : F,
  (
    (quotient1 = 0 ∧
      ∃ quotient0_less_than_divisor1 : F,
      (
        (quotient0_less_than_divisor1 = 0 ∧
          qd1_small = divisor1 ∧
          qd1_large = quotient0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_MERGE κ₁
            range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
        ) ∨
        (quotient0_less_than_divisor1 ≠ 0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_QUOTIENT0_LESS_THAN_DIVISOR1 κ₁
            range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
        )
      )
    ) ∨
    (quotient1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_DIVISOR1_EQ_ZERO κ₁
        range_check dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 q0d0_low q0d0_high leftover qd1_small qd1_large ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    )
  )

def auto_spec_u256_safe_divmod_HighDiff (κ : ℕ) (range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 diff1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  IsRangeChecked (rcBound F) diff1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_After κ₁
    range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low

def auto_spec_u256_safe_divmod (κ : ℕ) (range_check dividend0 dividend1 divisor0 divisor1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ quotient0 : F,
  ∃ quotient1 : F,
  ∃ remainder0 : F,
  ∃ remainder1 : F,
  IsRangeChecked (rcBound F) quotient0 ∧
  IsRangeChecked (rcBound F) quotient1 ∧
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
      ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_After κ₁
        range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    ) ∨
    (diff1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_safe_divmod_HighDiff κ₁
        range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1 diff1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low
    )
  )

/-
  # Modified versions of the automatic specificationa.
-/

def man_auto_spec_u256_safe_divmod_merge (dividend1 quotient0 quotient1 remainder0 remainder1
    leftover q0d0_high q0d0_low qd1_small qd1_large
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  IsRangeChecked (rcBound F) (qd1_small + u128_bound_minus_u64_bound) ∧
  dividend1 = leftover + q0d0_high + remainder1 + qd1_small * qd1_large ∧
  ρ_quotient0 = quotient0 ∧
  ρ_quotient1 = quotient1 ∧
  ρ_remainder0 = remainder0 ∧
  ρ_remainder1 = remainder1 ∧
  ρ_q0d0_high = q0d0_high ∧
  ρ_q0d0_low = q0d0_low

def man_auto_spec_u256_safe_divmod_after (range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1
    remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∃ q0d0_high q0d0_low leftover,
    (leftover = 0 ∨ leftover = 1) ∧
    u128Limit * leftover + dividend0 = q0d0_low + remainder0 ∧
  ∃ qd1_small qd1_large : F,
    ((quotient1 = 0 ∧
      ((qd1_large = quotient0 ∧ qd1_small = divisor1) ∨
       (qd1_large = divisor1 ∧ qd1_small = quotient0))) ∨
     ((divisor1 = 0 ∧
       ((qd1_large = quotient1 ∧ qd1_small = divisor0) ∨
       (qd1_large = divisor0 ∧ qd1_small = quotient1))))) ∧
      man_auto_spec_u256_safe_divmod_merge dividend1 quotient0 quotient1 remainder0 remainder1
        leftover q0d0_high q0d0_low qd1_small qd1_large
        ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low

def man_auto_spec_u256_safe_divmod (range_check dividend0 dividend1 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low : F) : Prop :=
  ∃ quotient0 quotient1 remainder0 remainder1,
  IsRangeChecked (rcBound F) quotient0 ∧
  IsRangeChecked (rcBound F) quotient1 ∧
  IsRangeChecked (rcBound F) remainder0 ∧
  IsRangeChecked (rcBound F) remainder1 ∧
  ((divisor1 = remainder1 ∧ IsRangeChecked (rcBound F) (divisor0 - remainder0 - 1)) ∨
   (divisor1 ≠ remainder1 ∧ IsRangeChecked (rcBound F) (divisor1 - remainder1))) ∧
  man_auto_spec_u256_safe_divmod_after range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low

/-
  The following lemmas show that the auto specs imply the modified auto specs.
-/

lemma man_auto_of_auto_spec_u256_safe_divmod_merge {κ : ℕ}
    {range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1
      q0d0_low q0d0_high leftover qd1_small qd1_large
      ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F} :
  auto_spec_u256_safe_divmod_MERGE κ range_check dividend1 divisor0 quotient0 quotient1 remainder0 remainder1
    q0d0_low q0d0_high leftover qd1_small qd1_large
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low →
  man_auto_spec_u256_safe_divmod_merge dividend1 quotient0 quotient1 remainder0 remainder1
    leftover q0d0_high q0d0_low qd1_small qd1_large
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low := by
  intro h_auto
  rcases h_auto with ⟨qd1_small_fixed, h_qd1_small_fixed, h_rc_qd1_small_fixed, h_auto⟩
  rw [h_qd1_small_fixed] at h_rc_qd1_small_fixed
  use h_rc_qd1_small_fixed
  rcases h_auto with ⟨qd1, h_qd1, part0, h_part0, part1, h_part1, h_dividend1, h_auto⟩
  constructor
  · rw [h_dividend1, h_part1, h_part0, h_qd1]
  rcases h_auto with ⟨h_q0, h_q1, h_r0, h_r1, -, -, h_q0d0_high, h_q0d0_low⟩
  use h_q0

lemma man_auto_of_auto_spec_u256_safe_divmod_after {κ : ℕ}
    {range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
      ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F} :
  auto_spec_u256_safe_divmod_After κ range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low →
  man_auto_spec_u256_safe_divmod_after range_check dividend0 dividend1 divisor0 divisor1 quotient0 quotient1 remainder0 remainder1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low := by
  intro h_auto
  rcases h_auto with ⟨q0d0_low, q0d0_high, part0, h_part0, part1, h_part1, leftover, h_leftover, h_leftover_eq, qd1_small, qd1_large, h_auto⟩

  use q0d0_high, q0d0_low, leftover
  constructor
  · by_cases h_0 : leftover = 0
    · left ; assumption
    right
    rw [(div_self (Ne.symm h_0).symm).symm]
    apply (eq_div_iff_mul_eq (Ne.symm h_0).symm).mpr
    exact h_leftover_eq.symm
  constructor
  · rw [eq_div_iff_mul_eq _, h_part1, h_part0, eq_sub_iff_add_eq, mul_comm, u128_limit_eq] at h_leftover
    apply h_leftover
    rw [u128_limit_eq]
    apply PRIME.nat_cast_ne_zero ; norm_num1 ; rw [PRIME] ; norm_num1
  use qd1_small, qd1_large

  rcases h_auto with h_q1_eq_zero|h_q1_ne_zero
  rcases h_q1_eq_zero with ⟨h_q1_eq_zero, quotient0_less_than_divisor1, h_eq_zero|h_ne_zero⟩
  rcases h_eq_zero with ⟨h_eq_zero, h_qd1_small, h_qd1_large, κ₁, h_Merge⟩
  · constructor
    · left
      use h_q1_eq_zero
      left
      use h_qd1_large
    apply man_auto_of_auto_spec_u256_safe_divmod_merge h_Merge
  rcases h_ne_zero with ⟨h_ne_zero, κ₁, h_qd1_small, h_qd1_large, κ₁, h_Merge⟩
  · constructor
    · left
      use h_q1_eq_zero
      right
      use h_qd1_large
    apply man_auto_of_auto_spec_u256_safe_divmod_merge h_Merge
  rcases h_q1_ne_zero with ⟨h_q1_ne_zero, κ₁, h_d1_eq_zero, quotient1_less_than_divisor0, h_q1_lt_d0_eq_zero|h_q1_lt_d0_ne_zero⟩

  · rcases h_q1_lt_d0_eq_zero with ⟨h_q1_lt_d0_eq_zero, h_qd1_small, h_qd1_large, κ₁, h_Merge⟩
    constructor
    · right
      use h_d1_eq_zero
      left
      use h_qd1_large
    apply man_auto_of_auto_spec_u256_safe_divmod_merge h_Merge

  rcases h_q1_lt_d0_ne_zero with ⟨h_q1_lt_d0_ne_zero, κ₁, h_qd1_small, h_qd1_large, κ₁', h_Merge⟩
  constructor
  · right
    use h_d1_eq_zero
    right
    use h_qd1_large
  apply man_auto_of_auto_spec_u256_safe_divmod_merge h_Merge

lemma man_auto_of_auto_spec_u256_safe_divmod {κ : ℕ}
    {range_check
      dividend0 dividend1 divisor0 divisor1
      ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1
      ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F} :
  auto_spec_u256_safe_divmod κ range_check dividend0 dividend1 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low →
  man_auto_spec_u256_safe_divmod range_check dividend0 dividend1 divisor0 divisor1
    ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_q0d0_high ρ_q0d0_low := by
  intro h_auto
  rcases h_auto with ⟨-, -, q0, q1, r0, r1, h_rc_q0, h_rc_q1, h_rc_r0, h_rc_r1, diff1, h_diff1, diff0, diff0_min_1, h_diff1_eq_zero|h_diff1_ne_zero⟩
  use q0, q1, r0, r1, h_rc_q0, h_rc_q1, h_rc_r0, h_rc_r1
  · rcases h_diff1_eq_zero with ⟨h_diff1_eq_zero, h_diff0, h_diff_min_1, h_rc_diff_min_1, κ₁, h_After⟩
    constructor
    · left
      rw [h_diff1_eq_zero] at h_diff1
      use (eq_of_sub_eq_zero h_diff1.symm)
      rw [h_diff_min_1, h_diff0, one] at h_rc_diff_min_1
      apply h_rc_diff_min_1
    apply man_auto_of_auto_spec_u256_safe_divmod_after h_After
  rcases h_diff1_ne_zero with ⟨h_diff1_ne_zero, κ₁, h_rc_diff1, κ₁', h_After⟩
  use q0, q1, r0, r1, h_rc_q0, h_rc_q1, h_rc_r0, h_rc_r1
  constructor
  · right
    rw [h_diff1, sub_ne_zero] at h_diff1_ne_zero
    use h_diff1_ne_zero
    rw [h_diff1] at h_rc_diff1
    apply h_rc_diff1
  apply man_auto_of_auto_spec_u256_safe_divmod_after h_After

theorem sound_u256_safe_divmod
    (κ : ℕ)
    (range_check dividend0 dividend1 divisor0 divisor1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low : F)
    (h_auto : auto_spec_u256_safe_divmod κ range_check dividend0 dividend1 divisor0 divisor1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low) :
  spec_u256_safe_divmod κ range_check dividend0 dividend1 divisor0 divisor1 ρ_quotient0 ρ_quotient1 ρ_remainder0 ρ_remainder1 ρ_quotient0₁ ρ_divisor0 ρ_q0d0_high ρ_q0d0_low := by

  replace h_auto := man_auto_of_auto_spec_u256_safe_divmod h_auto

  rintro
    n_dividend0 ⟨n_dividend0_lt, dividend0_eq⟩
    n_dividend1 ⟨n_dividend1_lt, dividend1_eq⟩
    n_divisor0  ⟨n_divisor0_lt, divisor0_eq⟩
    n_divisor1  ⟨n_divisor1_lt, divisor1_eq⟩
    hmul_guarantee

  rcases h_auto with ⟨quotient0, quotient1, remainder0, remainder1,
    ⟨n_quotient0, n_quotient0_lt, quotient0_eq⟩,
    ⟨n_quotient1, n_quotient1_lt, quotient1_eq⟩,
    ⟨n_remainder0, n_remainder0_lt, remainder0_eq⟩,
    ⟨n_remainder1, n_remainder1_lt, remainder1_eq⟩,
    hdisj, hjoin⟩
  have h_remainder_lt_divisor : u256_from_limbs n_remainder1 n_remainder0 <
      u256_from_limbs n_divisor1 n_divisor0 := by
    rcases hdisj with ⟨heq, ⟨n, n_lt, diff_eq⟩⟩ | ⟨hne, ⟨n, n_lt, diff_eq⟩⟩
    . have heq' : n_divisor1 = n_remainder1 := by
        apply @PRIME.nat_coe_field_inj F
        . exact n_divisor1_lt.trans u128Limit_lt_PRIME
        . exact n_remainder1_lt.trans rcBound_lt_PRIME
        . rw [←divisor1_eq, ←remainder1_eq, heq]
      have hlt : n_divisor0 = n_remainder0 + (n + 1) := by
        apply @PRIME.nat_coe_field_inj F
        . exact n_divisor0_lt.trans u128Limit_lt_PRIME
        . apply lt_of_lt_of_le (Nat.add_lt_add_right n_remainder0_lt _)
          apply le_trans (add_le_add (rcBound_hyp F)
            (Nat.add_le_add_right ((le_of_lt n_lt).trans (rcBound_hyp F)) 1))
          rw [PRIME]; norm_num1
        . rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ←divisor0_eq, ←remainder0_eq, ←diff_eq]
          abel
      have : n_remainder0 < n_divisor0 := by
        rw [hlt]; apply lt_add_of_pos_right; apply Nat.succ_pos
      unfold u256_from_limbs
      rw [heq']
      apply add_lt_add_left this
    . have : n_divisor1 = n_remainder1 + n := by
        apply @PRIME.nat_coe_field_inj F
        . exact n_divisor1_lt.trans u128Limit_lt_PRIME
        . apply lt_of_lt_of_le (add_lt_add (lt_of_lt_of_le n_remainder1_lt (rcBound_hyp F))
            (n_lt.trans (rcBound_hyp F)))
          rw [PRIME]; norm_num1
        . rw [Nat.cast_add, ←diff_eq, divisor1_eq, remainder1_eq]
          abel
      have : n_remainder1 < n_divisor1 := by
        apply lt_of_le_of_ne
        . rw [this]; apply Nat.le_add_right
        . intro hh
          apply hne
          rw [divisor1_eq, remainder1_eq, hh]
      unfold u256_from_limbs
      apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
      apply lt_of_lt_of_le (add_lt_add_left (lt_of_lt_of_le n_remainder0_lt (rcBound_hyp F)) _)
      rw [←u128Limit_eq_pow]
      conv => { lhs; congr; rfl; rw [←mul_one u128Limit] }
      rw [←mul_add]
      apply Nat.mul_le_mul_left
      exact this
  rcases hjoin with ⟨q0d0_high, q0d0_low, leftover, hleftover, hleftover',
    qd1_small, qd1_large, hjoin_disj, hmerge⟩
  rcases hmerge with ⟨⟨n_qd1_aux, n_qd1_aux_lt, qd1_aux_eq⟩, hdividend1,
    ρ_quotient0_eq, ρ_quotient1_eq, ρ_remainder0_eq, ρ_remainder1_eq, ρ_q0d0_high_eq,
    ρ_q0d0_low_eq⟩
  have n_quotient0_lt' : n_quotient0 < u128Limit := by
    rw [u128Limit_eq_pow]; exact lt_of_lt_of_le n_quotient0_lt (rcBound_hyp F)
  have n_divisor0_lt' : n_divisor0 < u128Limit := by
    rw [u128Limit_eq_pow]; exact lt_of_lt_of_le n_divisor0_lt (rcBound_hyp F)
  rcases hmul_guarantee ⟨n_quotient0_lt', ρ_quotient0_eq.trans quotient0_eq⟩
      ⟨n_divisor0_lt', divisor0_eq⟩
    with ⟨n_upper, ⟨n_upper_lt, ρ_q0d0_high_eq'⟩,
          n_lower, ⟨n_lower_lt, ρ_q0d0_low_eq'⟩, n_quotient0_n_divisor0_eq⟩
  have main_eq : u256_from_limbs n_dividend1 n_dividend0 =
  u256_from_limbs n_quotient1 n_quotient0 * u256_from_limbs n_divisor1 n_divisor0 +
    u256_from_limbs n_remainder1 n_remainder0 := by
    unfold u256_from_limbs
    rcases hjoin_disj with ⟨quotient1_eq_0, hdisj'⟩ | ⟨divisor1_eq_0, hdisj'⟩
    . have ⟨hprod_eq, hprod_le⟩ :
        qd1_small * qd1_large = quotient0 * divisor1 ∧ n_quotient0 * n_divisor1 ≤ 2^64 * 2^128 := by
          rcases hdisj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          . have : n_divisor1 + (2^128 - 2^64) = n_qd1_aux := by
              apply @PRIME.nat_coe_field_inj F
              . apply lt_of_lt_of_le (add_lt_add_right (n_divisor1_lt) _)
                rw [PRIME]; norm_num1
              . exact n_qd1_aux_lt.trans rcBound_lt_PRIME
              . rw [Nat.cast_add, ←qd1_aux_eq, h2, divisor1_eq, u128_bound_minus_u64_bound]
                -- simp only [Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat]
                norm_num1; rfl
            constructor
            . rw [h1, h2, mul_comm]
            . rw [mul_comm]
              apply Nat.mul_le_mul
              rw [eq_tsub_of_add_eq this, tsub_le_iff_left]
              apply (le_of_lt n_qd1_aux_lt).trans (rcBound_hyp F)
              apply (le_of_lt n_quotient0_lt).trans (rcBound_hyp F)
          . have : n_quotient0 + (2^128 - 2^64) = n_qd1_aux := by
              apply @PRIME.nat_coe_field_inj F
              . apply lt_of_lt_of_le
                  (add_lt_add_right (lt_of_lt_of_le n_quotient0_lt (rcBound_hyp F)) _)
                rw [PRIME]; norm_num1
              . exact n_qd1_aux_lt.trans rcBound_lt_PRIME
              . rw [Nat.cast_add, ←qd1_aux_eq, h2, quotient0_eq, u128_bound_minus_u64_bound]
                -- simp only [Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat]
                norm_num1; rfl
            constructor
            . rw [h1, h2, mul_comm]
            . apply Nat.mul_le_mul
              rw [eq_tsub_of_add_eq this, tsub_le_iff_left]
              apply (le_of_lt n_qd1_aux_lt).trans (rcBound_hyp F)
              apply (le_of_lt n_divisor1_lt).trans (rcBound_hyp F)
      have : n_quotient1 = 0 :=
        PRIME.nat_coe_field_zero (n_quotient1_lt.trans rcBound_lt_PRIME) quotient1_eq quotient1_eq_0
      rw [this, mul_zero, zero_add]
      rw [hprod_eq] at hdividend1
      rcases hleftover with hleftover0 | hleftover1
      . rw [hleftover0, mul_zero, zero_add] at hleftover'
        have h_dividend0 : n_dividend0 = n_lower + n_remainder0 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend0_lt.trans u128Limit_lt_PRIME
          . apply (add_lt_add n_lower_lt (lt_of_lt_of_le n_remainder0_lt (rcBound_hyp F))).trans
            rw [PRIME]; norm_num1
          . rw [←dividend0_eq, hleftover', ←ρ_q0d0_low_eq, ρ_q0d0_low_eq', remainder0_eq,
              Nat.cast_add]
        rw [hleftover0, zero_add] at hdividend1
        have h_dividend1 : n_dividend1 = n_upper + n_remainder1 + n_quotient0 * n_divisor1 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend1_lt.trans u128Limit_lt_PRIME
          . apply @lt_of_le_of_lt _ _ _ (2^128 + 2^128 + 2^64 * 2^128)
            apply add_le_add
            apply le_of_lt (add_lt_add n_upper_lt (lt_of_lt_of_le n_remainder1_lt (rcBound_hyp F)))
            exact hprod_le
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, ←dividend1_eq, hdividend1,
              ←ρ_q0d0_high_eq, ρ_q0d0_high_eq', remainder1_eq, quotient0_eq, divisor1_eq]
        rw [h_dividend0, h_dividend1, mul_add n_quotient0,
          n_quotient0_n_divisor0_eq, u256_from_limbs]; ring
      . rw [hleftover1, mul_one] at hleftover'
        have h_dividend0 : u128Limit + n_dividend0 = n_lower + n_remainder0 := by
          apply @PRIME.nat_coe_field_inj F
          . apply lt_of_le_of_lt (add_le_add_left (le_of_lt n_dividend0_lt) _)
            rw [PRIME]; norm_num1
          . apply lt_trans (add_lt_add n_lower_lt (lt_of_lt_of_le n_remainder0_lt (rcBound_hyp F)))
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, ←ρ_q0d0_low_eq', ρ_q0d0_low_eq, ←remainder0_eq,
              ←hleftover', dividend0_eq, u128Limit]
        rw [hleftover1] at hdividend1
        have h_dividend1 : n_dividend1 = 1 + n_upper + n_remainder1 + n_quotient0 * n_divisor1 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend1_lt.trans u128Limit_lt_PRIME
          . apply @lt_of_le_of_lt _ _ _ (1 + 2^128 + 2^128 + 2^64 * 2^128)
            apply add_le_add _ hprod_le
            apply add_le_add _ ((le_of_lt n_remainder1_lt).trans (rcBound_hyp F))
            apply add_le_add_left (le_of_lt n_upper_lt)
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_mul, ←dividend1_eq,
              hdividend1, ←ρ_q0d0_high_eq, ρ_q0d0_high_eq', remainder1_eq, quotient0_eq,
              divisor1_eq]
        rw [h_dividend1, mul_add n_quotient0, add_assoc, add_assoc, mul_add,
          mul_one, add_comm, ← add_assoc, add_comm n_dividend0, h_dividend0,
          n_quotient0_n_divisor0_eq, u256_from_limbs]; ring
    . have ⟨hprod_eq, hprod_le⟩ :
        qd1_small * qd1_large = quotient1 * divisor0 ∧ n_quotient1 * n_divisor0 ≤ 2^64 * 2^128 := by
          rcases hdisj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          . have : n_divisor0 + (2^128 - 2^64) = n_qd1_aux := by
              apply @PRIME.nat_coe_field_inj F
              . apply lt_of_lt_of_le (add_lt_add_right (n_divisor0_lt) _)
                rw [PRIME]; norm_num1
              . exact n_qd1_aux_lt.trans rcBound_lt_PRIME
              . rw [Nat.cast_add, ←qd1_aux_eq, h2, divisor0_eq, u128_bound_minus_u64_bound]
                -- simp only [Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat]
                norm_num1; rfl
            constructor
            . rw [h1, h2, mul_comm]
            . rw [mul_comm]
              apply Nat.mul_le_mul
              rw [eq_tsub_of_add_eq this, tsub_le_iff_left]
              apply (le_of_lt n_qd1_aux_lt).trans (rcBound_hyp F)
              apply (le_of_lt n_quotient1_lt).trans (rcBound_hyp F)
          . have : n_quotient1 + (2^128 - 2^64) = n_qd1_aux := by
              apply @PRIME.nat_coe_field_inj F
              . apply lt_of_lt_of_le
                  (add_lt_add_right (lt_of_lt_of_le  n_quotient1_lt (rcBound_hyp F)) _)
                rw [PRIME]; norm_num1
              . exact n_qd1_aux_lt.trans rcBound_lt_PRIME
              . rw [Nat.cast_add, ←qd1_aux_eq, h2, quotient1_eq, u128_bound_minus_u64_bound]
                -- simp only [Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat]
                norm_num1; rfl
            constructor
            . rw [h1, h2, mul_comm]
            . apply Nat.mul_le_mul
              rw [eq_tsub_of_add_eq this, tsub_le_iff_left]
              apply (le_of_lt n_qd1_aux_lt).trans (rcBound_hyp F)
              apply (le_of_lt n_divisor0_lt).trans (rcBound_hyp F)
      have : n_divisor1 = 0 :=
        PRIME.nat_coe_field_zero (n_divisor1_lt.trans u128Limit_lt_PRIME) divisor1_eq divisor1_eq_0
      rw [this, mul_zero, zero_add]
      rw [hprod_eq] at hdividend1
      rcases hleftover with hleftover0 | hleftover1
      . rw [hleftover0, mul_zero, zero_add] at hleftover'
        have h_dividend0 : n_dividend0 = n_lower + n_remainder0 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend0_lt.trans u128Limit_lt_PRIME
          . apply (add_lt_add n_lower_lt (lt_of_lt_of_le n_remainder0_lt (rcBound_hyp F))).trans
            rw [PRIME]; norm_num1
          . rw [←dividend0_eq, hleftover', ←ρ_q0d0_low_eq, ρ_q0d0_low_eq', remainder0_eq,
              Nat.cast_add]
        rw [hleftover0, zero_add] at hdividend1
        have h_dividend1 : n_dividend1 = n_upper + n_remainder1 + n_quotient1 * n_divisor0 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend1_lt.trans u128Limit_lt_PRIME
          . apply @lt_of_le_of_lt _ _ _ (2^128 + 2^128 + 2^64 * 2^128)
            apply add_le_add
            apply le_of_lt (add_lt_add n_upper_lt (lt_of_lt_of_le n_remainder1_lt (rcBound_hyp F)))
            exact hprod_le
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, ←dividend1_eq, hdividend1,
              ←ρ_q0d0_high_eq, ρ_q0d0_high_eq', remainder1_eq, quotient1_eq, divisor0_eq]
        rw [h_dividend0, h_dividend1, add_mul,
          n_quotient0_n_divisor0_eq, u256_from_limbs]; ring
      . rw [hleftover1, mul_one] at hleftover'
        have h_dividend0 : u128Limit + n_dividend0 = n_lower + n_remainder0 := by
          apply @PRIME.nat_coe_field_inj F
          . apply lt_of_le_of_lt (add_le_add_left (le_of_lt n_dividend0_lt) _)
            rw [PRIME]; norm_num1
          . apply (lt_trans (add_lt_add n_lower_lt (lt_of_lt_of_le n_remainder0_lt (rcBound_hyp F))))
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, ←ρ_q0d0_low_eq', ρ_q0d0_low_eq, ←remainder0_eq,
              ←hleftover', dividend0_eq, u128Limit]
        rw [hleftover1] at hdividend1
        have h_dividend1 : n_dividend1 = 1 + n_upper + n_remainder1 + n_quotient1 * n_divisor0 := by
          apply @PRIME.nat_coe_field_inj F
          . exact n_dividend1_lt.trans u128Limit_lt_PRIME
          . apply @lt_of_le_of_lt _ _ _ (1 + 2^128 + 2^128 + 2^64 * 2^128)
            apply add_le_add _ hprod_le
            apply add_le_add _ ((le_of_lt n_remainder1_lt).trans (rcBound_hyp F))
            apply add_le_add_left (le_of_lt n_upper_lt)
            rw [PRIME]; norm_num1
          . rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_mul, ←dividend1_eq, hdividend1,
              ←ρ_q0d0_high_eq, ρ_q0d0_high_eq', remainder1_eq, quotient1_eq, divisor0_eq]
        rw [h_dividend1, add_mul, add_assoc, add_assoc, mul_add,
          mul_one, add_comm, ← add_assoc, add_comm n_dividend0, h_dividend0,
          n_quotient0_n_divisor0_eq, u256_from_limbs]; ring
  have n_quotient0_lt' := Trans.trans n_quotient0_lt (rcBound_hyp F)
  have n_quotient1_lt' := Trans.trans n_quotient1_lt (rcBound_hyp F)
  have n_remainder0_lt' := Trans.trans n_remainder0_lt (rcBound_hyp F)
  have n_remainder1_lt' := Trans.trans n_remainder1_lt (rcBound_hyp F)
  use_only n_quotient0, ⟨n_quotient0_lt', ρ_quotient0_eq.trans quotient0_eq⟩
  use_only n_quotient1, ⟨n_quotient1_lt', ρ_quotient1_eq.trans quotient1_eq⟩
  use_only n_remainder0, ⟨n_remainder0_lt', ρ_remainder0_eq.trans remainder0_eq⟩
  use_only n_remainder1, ⟨n_remainder1_lt', ρ_remainder1_eq.trans remainder1_eq⟩
  use_only h_remainder_lt_divisor
  exact main_eq
