import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u256_guarantee_inv_mod_n_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def zero : F := (0 : F) -- 0
def one : F := (1 : F) -- 1
def u128_bound_minus_u65_bound : F := (340282366920938463426481119284349108224 : F) -- BigInt::from(2).pow(128) - BigInt::from(2).pow(65)
def u128_bound_minus_i16_upper_bound : F := (340282366920938463463374607431768178688 : F) -- u128::MAX - i16::MAX as u128
def i16_lower_bound : F := (-32768 : F) -- i16::MIN
def u128_limit : F := (340282366920938463463374607431768211456 : F) -- (BigInt::from(u128::MAX) + 1) as BigInt
def u64_limit : F := (18446744073709551616 : F) -- (BigInt::from(u64::MAX) + 1) as BigInt

theorem u128_limit_eq : u128_limit = (u128Limit : F) := by unfold u128_limit u128Limit ; norm_cast
theorem i16_lower_bound_eq : i16_lower_bound = (i16Min : F) := by unfold i16_lower_bound i16Min ; norm_cast
theorem u128_bound_minus_i16_upper_bound_eq : u128_bound_minus_i16_upper_bound = ((u128Max : ℤ) - i16Max : F) := by
  unfold u128_bound_minus_i16_upper_bound u128Max i16Max ; rw [←Int.cast_sub] ; norm_num1
theorem u_128_bound_plus_sub_i16_bounds : (i16_lower_bound : F) + u128_bound_minus_i16_upper_bound = ↑((u128Limit - 2 * u8Limit) : ℕ) := by
  unfold i16_lower_bound u128_bound_minus_i16_upper_bound u128Limit u8Limit ; norm_num1
theorem u8_limit_minus_i16Min_eq : (u8Limit : ℤ) - i16Min = (u16Limit :ℤ) := by
  unfold u8Limit i16Min u16Limit ; norm_num1
theorem u128_bound_minus_u65_bound_eq : (u128_bound_minus_u65_bound : F) = ↑(u128Limit - u65Limit) := by
  unfold u128_bound_minus_u65_bound u128Limit u65Limit ; norm_num1
theorem u65Limit_mul_u128Limit_add_u128Limit_lt_PRIME : u65Limit * u128Limit + u128Limit < PRIME := by
  unfold u128Limit u65Limit PRIME; norm_num1

def spec_u256_guarantee_inv_mod_n (κ : ℕ) (range_check b0 b1 n0 n1
    ρ_branch_id
    ρ_r0 ρ_r1
    ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
    ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
    ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
    ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
    ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
    ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
    ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
    ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∀ n_b0 : ℕ, is_u128_of b0 n_b0 →
  ∀ n_b1 : ℕ, is_u128_of b1 n_b1 →
  ∀ n_n0 : ℕ, is_u128_of n0 n_n0 →
  ∀ n_n1 : ℕ, is_u128_of n1 n_n1 →
    (-- Inverse exists
      ρ_branch_id = 0 ∧ (
        -- Guarantee specs
        u128_mul_guarantee ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low →
        u128_mul_guarantee ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low →
        u128_mul_guarantee ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low →
        u128_mul_guarantee ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low →
        u128_mul_guarantee ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low →
        u128_mul_guarantee ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low →
        u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
        u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
          ∃ n_r0 : ℕ, is_u128_of ρ_r0 n_r0 ∧
          ∃ n_r1 : ℕ, is_u128_of ρ_r1 n_r1 ∧
          u256_from_limbs n_r1 n_r0 < u256_from_limbs n_n1 n_n0 ∧
          -- r * b ≡ 1 mod n
          u256_from_limbs n_r1 n_r0 * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0])
    ) ∨ (
      -- n = 1
      ρ_branch_id = 1 ∧ u256_from_limbs n_n1 n_n0 = 1
    ) ∨ (-- No inverse exists.
      ρ_branch_id = 1 ∧ (
        u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
        u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
          -- ¬ ∃ r, r * b ≡ 1 mod n
          ¬ ∃ r, r * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0])
    )

def auto_spec_u256_guarantee_inv_mod_n_Done (κ : ℕ) (range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ρ_branch_id = 0 ∧
  ρ_r0 = r0 ∧
  ρ_r1 = r1 ∧
  ρ_r0₁ = r0 ∧
  ρ_b0 = b0 ∧
  ρ_r0b0_high = r0b0_high ∧
  ρ_r0b0_low = r0b0_low ∧
  ρ_r0₂ = r0 ∧
  ρ_b1 = b1 ∧
  ρ_r0b1_high = r0b1_high ∧
  ρ_r0b1_low = r0b1_low ∧
  ρ_r1₁ = r1 ∧
  ρ_b0₁ = b0 ∧
  ρ_r1b0_high = r1b0_high ∧
  ρ_r1b0_low = r1b0_low ∧
  ρ_r1₂ = r1 ∧
  ρ_b1₁ = b1 ∧
  ρ_r1b1_high = r1b1_high ∧
  ρ_r1b1_low = r1b1_low ∧
  ρ_n0 = n0 ∧
  ρ_k0 = k0 ∧
  ρ_n0k0_high = n0k0_high ∧
  ρ_n0k0_low = n0k0_low ∧
  ρ_n0₁ = n0 ∧
  ρ_k1 = k1 ∧
  ρ_n0k1_high = n0k1_high ∧
  ρ_n0k1_low = n0k1_low ∧
  ρ_n1_or_g0 = n1 ∧
  ρ_k0_or_s0 = k0 ∧
  ρ_n1k0_high_or_g0s0_high = n1k0_high ∧
  ρ_n1k0_low_or_g0s0_low = n1k0_low ∧
  ρ_n1_or_g0₁ = n1 ∧
  ρ_k1_or_t0 = k1 ∧
  ρ_n1k1_high_or_g0t0_high = n1k1_high ∧
  ρ_n1k1_low_or_g0t0_low = n1k1_low

def auto_spec_u256_guarantee_inv_mod_n_MERGE (κ : ℕ) (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∃ smalls_sum_fixed : F, smalls_sum_fixed = smalls_sum + u128_bound_minus_u65_bound ∧
  IsRangeChecked (rcBound F) smalls_sum_fixed ∧
  b1 = gs1 + g0s0_high ∧
  n1 = gt1 + g0t0_high ∧
  ρ_branch_id = 1 ∧
  ρ_n1_or_g0 = g0 ∧
  ρ_k0_or_s0 = s0 ∧
  ρ_n1k0_high_or_g0s0_high = g0s0_high ∧
  ρ_n1k0_low_or_g0s0_low = g0s0_low ∧
  ρ_n1_or_g0₁ = g0 ∧
  ρ_k1_or_t0 = t0 ∧
  ρ_n1k1_high_or_g0t0_high = g0t0_high ∧
  ρ_n1k1_low_or_g0t0_low = g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_G1IsSmall (κ : ℕ) (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  smalls_sum = g1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_MERGE κ₁
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO (κ : ℕ) (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  gs1 = s0 * g1 ∧
  gt1 = t0 * g1 ∧
  s1 = zero ∧
  t1 = zero ∧
  ∃ g1_is_small : F,
  (
    (g1_is_small = 0 ∧
      smalls_sum = s0 + t0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_MERGE κ₁
        range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    ) ∨
    (g1_is_small ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_G1IsSmall κ₁
        range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_G0IsSmall (κ : ℕ) (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  smalls_sum = g0 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_MERGE κ₁
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_GIsValid (κ : ℕ) (range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∃ g0s0_low : F, g0s0_low = b0 ∧
  ∃ g0s0_high : F,
  ∃ g0t0_low : F, g0t0_low = n0 ∧
  ∃ g0t0_high : F,
  ∃ gs1 : F,
  ∃ gt1 : F,
  ∃ smalls_sum : F,
  (
    (g1 = 0 ∧
      gs1 = s1 * g0 ∧
      gt1 = t1 * g0 ∧
      ∃ g0_is_small : F,
      (
        (g0_is_small = 0 ∧
          smalls_sum = s1 + t1 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_MERGE κ₁
            range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (g0_is_small ≠ 0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_G0IsSmall κ₁
            range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO κ₁
        range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_NoInverse (κ : ℕ) (range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∃ g0 : F, g0 = g0_or_no_inv ∧
  ∃ g1 : F, g1 = g1_option ∧
  ∃ s0 : F, s0 = s_or_r0 ∧
  ∃ s1 : F, s1 = s_or_r1 ∧
  ∃ t0 : F, t0 = t_or_k0 ∧
  ∃ t1 : F, t1 = t_or_k1 ∧
  IsRangeChecked (rcBound F) g0 ∧
  IsRangeChecked (rcBound F) g1 ∧
  IsRangeChecked (rcBound F) s0 ∧
  IsRangeChecked (rcBound F) s1 ∧
  IsRangeChecked (rcBound F) t0 ∧
  IsRangeChecked (rcBound F) t1 ∧
  ∃ g0_minus_1 : F,
  (
    (g1 = 0 ∧
      g0_minus_1 = g0 - one ∧
      (
        (g0_minus_1 = 0 ∧
          n1 = zero ∧
          n0 = one ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_GIsValid κ₁
            range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (g0_minus_1 ≠ 0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_GIsValid κ₁
            range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_GIsValid κ₁
        range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_After (κ : ℕ) (range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∃ r0b0_low : F,
  ∃ r0b0_high : F,
  ∃ r0b1_low : F,
  ∃ r0b1_high : F,
  ∃ r1b0_low : F,
  ∃ r1b0_high : F,
  ∃ r1b1_low : F,
  ∃ r1b1_high : F,
  ∃ n0k0_low : F,
  ∃ n0k0_high : F,
  ∃ n0k1_low : F,
  ∃ n0k1_high : F,
  ∃ n1k0_low : F,
  ∃ n1k0_high : F,
  ∃ n1k1_low : F,
  ∃ n1k1_high : F,
  ∃ part0 : F, part0 = n0k0_low + one ∧
  ∃ part1 : F, part1 = part0 - r0b0_low ∧
  ∃ leftover : F, leftover = part1 / u128_limit ∧
  leftover = leftover * leftover ∧
  ∃ part0₁ : F, part0₁ = n0k0_high + leftover ∧
  ∃ part1₁ : F, part1₁ = part0₁ + n0k1_low ∧
  ∃ part2 : F, part2 = part1₁ + n1k0_low ∧
  ∃ part3 : F, part3 = part2 - r0b0_high ∧
  ∃ part4 : F, part4 = part3 - r0b1_low ∧
  ∃ part5 : F, part5 = part4 - r1b0_low ∧
  ∃ leftover₁ : F, leftover₁ = part5 / u128_limit ∧
  ∃ a : F, a = leftover₁ - i16_lower_bound ∧
  IsRangeChecked (rcBound F) a ∧
  ∃ a₁ : F, a₁ = leftover₁ + u128_bound_minus_i16_upper_bound ∧
  IsRangeChecked (rcBound F) a₁ ∧
  ∃ part0₂ : F, part0₂ = n0k1_high + leftover₁ ∧
  ∃ part1₂ : F, part1₂ = part0₂ + n1k0_high ∧
  ∃ part2₁ : F, part2₁ = part1₂ + n1k1_low ∧
  ∃ part3₁ : F, part3₁ = part2₁ - r1b0_high ∧
  ∃ part4₁ : F, part4₁ = part3₁ - r0b1_high ∧
  ∃ part5₁ : F, part5₁ = part4₁ - r1b1_low ∧
  ∃ leftover₂ : F, leftover₂ = part5₁ / u128_limit ∧
  ∃ a₂ : F, a₂ = leftover₂ - i16_lower_bound ∧
  IsRangeChecked (rcBound F) a₂ ∧
  ∃ a₃ : F, a₃ = leftover₂ + u128_bound_minus_i16_upper_bound ∧
  IsRangeChecked (rcBound F) a₃ ∧
  r1b1_high = n1k1_high + leftover₂ ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_Done κ₁
    range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_HighDiff (κ : ℕ) (range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  IsRangeChecked (rcBound F) diff1 ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_After κ₁
    range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n (κ : ℕ) (range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ g0_or_no_inv : F,
  ∃ g1_option : F,
  ∃ s_or_r0 : F,
  ∃ s_or_r1 : F,
  ∃ t_or_k0 : F,
  ∃ t_or_k1 : F,
  (
    (g0_or_no_inv = 0 ∧
      ∃ r0 : F, r0 = s_or_r0 ∧
      ∃ r1 : F, r1 = s_or_r1 ∧
      ∃ k0 : F, k0 = t_or_k0 ∧
      ∃ k1 : F, k1 = t_or_k1 ∧
      IsRangeChecked (rcBound F) r0 ∧
      IsRangeChecked (rcBound F) r1 ∧
      IsRangeChecked (rcBound F) k0 ∧
      IsRangeChecked (rcBound F) k1 ∧
      ∃ diff1 : F, diff1 = n1 - r1 ∧
      ∃ diff0 : F,
      ∃ diff0_min_1 : F,
      (
        (diff1 = 0 ∧
          diff0 = n0 - r0 ∧
          diff0_min_1 = diff0 - one ∧
          IsRangeChecked (rcBound F) diff0_min_1 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_After κ₁
            range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (diff1 ≠ 0 ∧
          ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_HighDiff κ₁
            range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g0_or_no_inv ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_guarantee_inv_mod_n_NoInverse κ₁
        range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )
/- # Partial proof lemmas -/

lemma r_lt_n_of_high_eq
      (n_n0 n_n1 n_r0 n_r1 : ℕ)
      (h_n_n0_lt : n_n0 < u128Limit)
      (h_n_n1_lt : n_n1 < u128Limit)
      (h_n_r0_lt : n_r0 < u128Limit)
      (h_n_r1_lt : n_r1 < u128Limit)
      (h_n1_min_r1_eq_zero: (↑n_n1 - ↑n_r1 : F) = 0)
      (h_rc: IsRangeChecked (rcBound F) (↑n_n0 - ↑n_r0 - one : F)) :
    u256_from_limbs n_r1 n_r0 < u256_from_limbs n_n1 n_n0 := by

  rcases h_rc with ⟨n_n0_min_r0_min_1, h_n_n0_min_r0_min_1_lt, h_n_n0_min_r0_min_1_eq⟩
  unfold u256_from_limbs
  apply add_lt_add_of_le_of_lt ; apply le_of_eq
  rw [sub_eq_zero] at h_n1_min_r1_eq_zero
  have h_eq : n_n1 = n_r1 := by
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n1_lt) (lt_PRIME_of_lt_u128Limit h_n_r1_lt) h_n1_min_r1_eq_zero
  rw [h_eq]
  rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at h_n_n0_min_r0_min_1_eq
  have h_n_eq_r_plus : n_n0 = n_r0 + 1 + n_n0_min_r0_min_1  := by
    rw [add_comm, add_comm n_r0, ←add_assoc]
    unfold one at h_n_n0_min_r0_min_1_eq
    rw [←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add] at h_n_n0_min_r0_min_1_eq
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n0_lt) _ h_n_n0_min_r0_min_1_eq
    apply lt_trans _ u128Limit_triple_lt_PRIME
    apply Nat.add_lt_add _ h_n_r0_lt ; apply Nat.add_lt_add _ (by norm_num1)
    apply lt_of_lt_of_le h_n_n0_min_r0_min_1_lt _
    apply @rcBound_hyp F
  apply Nat.lt_of_succ_le
  exact Nat.le.intro h_n_eq_r_plus.symm

lemma r_lt_n_of_high_ne
      (n_n0 n_n1 n_r0 n_r1 : ℕ)
      (h_n_n1_lt : n_n1 < u128Limit)
      (h_n_r0_lt : n_r0 < u128Limit)
      (h_n_r1_lt : n_r1 < u128Limit)
      (h_n1_min_r1_ne_zero: (↑n_n1 - ↑n_r1 : F) ≠ 0)
      (h_rc: IsRangeChecked (rcBound F) (↑n_n1 - ↑n_r1 : F)) :
    u256_from_limbs n_r1 n_r0 < u256_from_limbs n_n1 n_n0 := by

  rcases h_rc with ⟨n_n1_min_r1, h_n_n1_min_r1_lt, h_n_n1_min_r1_eq⟩
  rw [sub_eq_iff_eq_add, ←Nat.cast_add] at h_n_n1_min_r1_eq
  unfold u256_from_limbs
  have h_n1_eq : n_n1 = n_r1  + n_n1_min_r1 := by
    rw [add_comm]
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n1_lt) _ h_n_n1_min_r1_eq
    apply lt_trans _ u128Limit_double_lt_PRIME ; apply Nat.add_lt_add _ h_n_r1_lt
    apply lt_of_lt_of_le h_n_n1_min_r1_lt _
    apply @rcBound_hyp F
  have h_r1_le_succ_n1 : n_r1 + 1 ≤ n_n1 := by
    apply lt_of_le_of_ne (Nat.le.intro h_n1_eq.symm)
    by_contra h_ne
    apply h_n1_min_r1_ne_zero ; rw [h_ne] ; apply sub_self
  apply Nat.lt_add_right
  apply lt_of_lt_of_le _ (Nat.mul_le_mul_left _ h_r1_le_succ_n1)
  rw [Nat.left_distrib, Nat.mul_one]
  apply Nat.add_lt_add_left h_n_r0_lt

/- # Limb 0 -/

-- This is identical to the lemma in u512_safe_divmod_by_u256_soundness_spec

lemma limb0_eq (n_n0k0_low n_r0b0_low : ℕ)
    (part0 part1 leftover: F)
    (h_part0: part0 = ↑n_n0k0_low + ↑1)
    (h_part1 : part1 = part0 - ↑n_r0b0_low)
    (h_leftover1: leftover = part1 / u128_limit)
    (h_leftover2: leftover = leftover * leftover)
    (h_n_n0k0_low_lt: n_n0k0_low < u128Limit)
    (h_n_r0b0_low_lt : n_r0b0_low < u128Limit) :
  ∃ n_lo :ℕ,
    leftover = ↑n_lo ∧ (n_lo = 0 ∨ n_lo = 1) ∧ (n_n0k0_low + 1 : ℤ) = ↑n_r0b0_low + ↑n_lo * ↑u128Limit := by

  norm_cast
  have lo_zero_or_one : leftover = 0 ∨ leftover = 1 := by
    apply eq_zero_or_eq_one_of_mul_eq_self h_leftover2.symm
  have h_p1 := (eq_div_iff_mul_eq u128Limit_coe_ne_zero).mp h_leftover1
  cases' lo_zero_or_one with h_0 h_1
  · use_only 0 ; rw [Nat.cast_zero] ; use_only h_0 ; constructor ; left ; apply Eq.refl
    rw [zero_mul, add_zero]
    rw [←h_p1, h_0, zero_mul] at h_part1 ;
    rw [sub_eq_zero.mp h_part1.symm] at h_part0 ; norm_cast at h_part0
    apply PRIME.nat_coe_field_inj _ _ h_part0.symm
    apply add_lt_PRIME_of_lt h_n_n0k0_low_lt (by norm_num1)
    apply lt_trans h_n_r0b0_low_lt u128Limit_lt_PRIME
  use_only 1 ; rw [Nat.cast_one] ; use_only h_1 ; constructor ; right ; apply Eq.refl
  rw [←h_p1, h_1, one_mul, eq_sub_iff_add_eq] at h_part1
  rw [←h_part1, u128_limit_eq, ←Nat.cast_add, add_comm u128Limit] at h_part0 ; norm_cast at h_part0
  apply PRIME.nat_coe_field_inj _ _ h_part0.symm
  apply add_lt_PRIME_of_lt h_n_n0k0_low_lt (by norm_num1)
  apply add_lt_PRIME_of_le (le_of_lt h_n_r0b0_low_lt) (le_of_eq rfl)

/- # Limb 1 or 2 -/

lemma limb_1_or_2_eq (n_lo : ℤ)
      (n_x0 n_x1 n_x2 n_y0 n_y1 n_y2 n_a n_a₁ : ℕ)
      (part0 part1 part2 part3 part4 part5 leftover : F)
      (h_part0: part0 = ↑n_x0 + ↑n_lo)
      (h_part1: part1 = part0 + ↑n_x1)
      (h_part2: part2 = part1 + ↑n_x2)
      (h_part3: part3 = part2 - ↑n_y0)
      (h_part4: part4 = part3 - ↑n_y1)
      (h_part5: part5 = part4 - ↑n_y2)
      (h_leftover: leftover = part5 / u128_limit)
      (h_a: (n_a : F) = leftover - i16_lower_bound)
      (h_n_a_lt: n_a < u128Limit)
      (h_a₁: (n_a₁ : F) = leftover + u128_bound_minus_i16_upper_bound)
      (h_n_a₁_lt: n_a₁ < u128Limit)
      (h_n_lo_lt : abs n_lo ≤ u8Limit)
      (h_n_x0_lt : n_x0 < u128Limit)
      (h_n_x1_lt : n_x1 < u128Limit)
      (h_n_x2_lt : n_x2 < u128Limit)
      (h_n_y0_lt : n_y0 < u128Limit)
      (h_n_y1_lt : n_y1 < u128Limit)
      (h_n_y2_lt : n_y2 < u128Limit) :
    ∃ n_lo₁ : ℤ, leftover = ↑n_lo₁ ∧ abs n_lo₁ ≤ u8Limit ∧  n_x0 + n_x1 + n_x2 = n_lo₁ * u128Limit + n_y2 + n_y1 + n_y0 - n_lo := by

    use_only n_a + i16Min
    replace h_a := eq_sub_iff_add_eq.mp h_a
    constructor
    · rw [←h_a, i16_lower_bound_eq, coe_eq_int_coe_coe n_a, ←Int.cast_add]
    have h_n_lo₁_lt : abs (n_a + i16Min) ≤ u8Limit := by
      rw [abs_le]
      constructor
      · unfold u8Limit i16Min
        apply Int.le_add_of_sub_right_le ; norm_num1
        apply Int.zero_le_ofNat
      rw [←h_a, add_assoc, u_128_bound_plus_sub_i16_bounds, ←Nat.cast_add] at h_a₁
      have hb : n_a + (u128Limit - 2 * u8Limit) < PRIME := by
        apply lt_trans _ u128Limit_double_lt_PRIME
        apply Nat.add_lt_add h_n_a_lt
        unfold u128Limit ; norm_num1
      have h := PRIME.nat_coe_field_inj (lt_trans h_n_a₁_lt u128Limit_lt_PRIME) hb h_a₁
      rw [←(Nat.add_sub_of_le (show 2 * u8Limit ≤ u128Limit by norm_num1))] at h_n_a₁_lt
      rw [h, add_lt_add_iff_right _] at h_n_a₁_lt
      apply Int.add_le_of_le_sub_right ; rw [u8_limit_minus_i16Min_eq]
      rw [Int.ofNat_le]
      apply le_trans (le_of_lt h_n_a₁_lt)
      unfold u8Limit u16Limit ; norm_num1
    use_only h_n_lo₁_lt
    rw [eq_sub_iff_add_eq, add_comm _ n_lo, ←add_assoc, ←add_assoc]
    rw [add_comm] at h_part0
    rw [h_part0] at h_part1
    rw [h_part1] at h_part2
    rw [h_part2] at h_part3
    rw [h_part3] at h_part4
    rw [h_part4, ←((eq_div_iff_mul_eq u128Limit_coe_ne_zero).mp h_leftover), ←h_a, i16_lower_bound_eq, u128_limit_eq] at h_part5
    simp only [eq_sub_iff_add_eq] at h_part5
    simp only [coe_eq_int_coe_coe] at h_part5
    simp only [←Int.cast_add, ←Int.cast_mul] at h_part5
    apply PRIME.int_coe_inj h_part5.symm
    apply lt_of_le_of_lt (abs_sub _ _)
    have h_p : (u8Limit * u128Limit + u128Limit + u128Limit + u128Limit : ℤ) + ↑(u8Limit + u128Limit + u128Limit + u128Limit) < ↑PRIME := by
      unfold u8Limit u128Limit PRIME ; norm_num1
    apply lt_of_le_of_lt _ h_p
    apply add_le_add
    simp only [add_assoc]
    apply le_trans (abs_add _ _)
    apply add_le_add
    rw [abs_mul]
    rw [Int.abs_natCast]
    rw [(mul_le_mul_right (by norm_num1))] ; apply h_n_lo₁_lt
    norm_cast
    apply Nat.add_le_add (le_of_lt h_n_y2_lt)
    apply Nat.add_le_add (le_of_lt h_n_y1_lt) (le_of_lt h_n_y0_lt)
    simp only [add_assoc]
    apply le_trans (abs_add _ _)
    rw [Nat.cast_add]
    apply add_le_add h_n_lo_lt
    norm_cast
    apply Nat.add_le_add (le_of_lt h_n_x0_lt)
    apply Nat.add_le_add (le_of_lt h_n_x1_lt) (le_of_lt h_n_x2_lt)

/- Continuation of the proof of the specs (for the case an inverse exists) beginning at the After label -/


lemma inv_exists_at_After
      {range_check: F}
      {n_b0 n_b1 n_n0 n_n1 n_r0 n_r1 n_k0 n_k1 : ℕ}
      {ρ_branch_id
        ρ_r0 ρ_r1
        ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
        ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
        ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
        ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
        ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
        ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
        ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
        ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F}
      (h_n_b0_lt: n_b0 < u128Limit)
      (h_n_b1_lt: n_b1 < u128Limit)
      (h_n_n0_lt: n_n0 < u128Limit)
      (h_n_n1_lt: n_n1 < u128Limit)
      (h_n_r0_lt: n_r0 < u128Limit)
      (h_n_r1_lt: n_r1 < u128Limit)
      (h_n_k0_lt: n_k0 < u128Limit)
      (h_n_k1_lt: n_k1 < u128Limit)
      (h_r_lt_n : u256_from_limbs n_r1 n_r0 < u256_from_limbs n_n1 n_n0)
      (h_After: ∃ (κ₁ : ℕ),
          auto_spec_u256_guarantee_inv_mod_n_After κ₁
            range_check ↑n_b0 ↑n_b1 ↑n_n0 ↑n_n1 ↑n_r0 ↑n_r1 ↑n_k0 ↑n_k1
            ρ_branch_id
            ρ_r0 ρ_r1
            ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
            ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
            ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
            ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
            ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
            ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
            ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
            ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low) :
    ρ_branch_id = 0 ∧ (
      -- Guarantee specs
      u128_mul_guarantee ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low →
      u128_mul_guarantee ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low →
      u128_mul_guarantee ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low →
      u128_mul_guarantee ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low →
      u128_mul_guarantee ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low →
      u128_mul_guarantee ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low →
      u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
      u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
        ∃ n_r0 : ℕ, is_u128_of ρ_r0 n_r0 ∧
        ∃ n_r1 : ℕ, is_u128_of ρ_r1 n_r1 ∧
        u256_from_limbs n_r1 n_r0 < u256_from_limbs n_n1 n_n0 ∧
        u256_from_limbs n_r1 n_r0 * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0]) := by

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  rcases h_After with ⟨-, r0b0_low, r0b0_high, r0b1_low, r0b1_high, r1b0_low, r1b0_high, r1b1_low, r1b1_high, n0k0_low, n0k0_high, n0k1_low,
    n0k1_high, n1k0_low, n1k0_high, n1k1_low, n1k1_high, h_cont⟩
  -- limb 0
  rcases h_cont with ⟨part0, h_part0, part1, h_part1, leftover, h_leftover, h_leftover_0_or_1, h_cont⟩
  -- limb 1
  rcases h_cont with ⟨part0₁, h_part0₁, part1₁, h_part1₁, part2, h_part2, part3, h_part3, part4, h_part4, part5, h_part5, h_cont⟩
  rcases h_cont with ⟨leftover₁, h_leftover₁, a, h_a, ⟨n_a, h_n_a_lt, rfl⟩, a₁, h_a₁, ⟨n_a₁, h_n_a₁_lt, rfl⟩, h_cont⟩
  replace h_n_a_lt := lt_of_lt_of_le h_n_a_lt h_rcBound
  replace h_n_a₁_lt := lt_of_lt_of_le h_n_a₁_lt h_rcBound
  -- limb 2
  rcases h_cont with ⟨part0₂, h_part0₂, part1₂, h_part1₂, part2₁, h_part2₁, part3₁, h_part3₁, part4₁, h_part4₁, part5₁, h_part5₁, h_cont⟩
  rcases h_cont with ⟨leftover₂, h_leftover₂, a₂, h_a₂, ⟨n_a₂, h_n_a₂_lt, rfl⟩, a₃, h_a₃, ⟨n_a₃, h_n_a₃_lt, rfl⟩, h_cont⟩
  replace h_n_a₂_lt := lt_of_lt_of_le h_n_a₂_lt h_rcBound
  replace h_n_a₃_lt := lt_of_lt_of_le h_n_a₃_lt h_rcBound
  --limb 3
  rcases h_cont with ⟨h_r1b1_high_eq, h_ret⟩

  -- return arguments
  rcases h_ret with ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

  constructor ; rfl

  rintro h_g_r0b0 h_g_r0b1 h_g_r1b0 h_g_r1b1 h_g_n0k0 h_g_n0k1 h_g_n1k0 h_g_n1k1

  rcases h_g_r0b0 ⟨h_n_r0_lt, rfl⟩ ⟨h_n_b0_lt, rfl⟩ with
    ⟨n_r0b0_high, ⟨h_n_r0b0_high_lt, rfl⟩, n_r0b0_low, ⟨h_n_r0b0_low_lt, rfl⟩, h_r0b0_mul⟩
  rcases h_g_r0b1 ⟨h_n_r0_lt, rfl⟩ ⟨h_n_b1_lt, rfl⟩ with
    ⟨n_r0b1_high, ⟨h_n_r0b1_high_lt, rfl⟩, n_r0b1_low, ⟨h_n_r0b1_low_lt, rfl⟩, h_r0b1_mul⟩
  rcases h_g_r1b0 ⟨h_n_r1_lt, rfl⟩ ⟨h_n_b0_lt, rfl⟩ with
    ⟨n_r1b0_high, ⟨h_n_r1b0_high_lt, rfl⟩, n_r1b0_low, ⟨h_n_r1b0_low_lt, rfl⟩, h_r1b0_mul⟩
  rcases h_g_r1b1 ⟨h_n_r1_lt, rfl⟩ ⟨h_n_b1_lt, rfl⟩ with
    ⟨n_r1b1_high, ⟨h_n_r1b1_high_lt, rfl⟩, n_r1b1_low, ⟨h_n_r1b1_low_lt, rfl⟩, h_r1b1_mul⟩
  rcases h_g_n0k0 ⟨h_n_n0_lt, rfl⟩ ⟨h_n_k0_lt, rfl⟩ with
    ⟨n_n0k0_high, ⟨h_n_n0k0_high_lt, rfl⟩, n_n0k0_low, ⟨h_n_n0k0_low_lt, rfl⟩, h_n0k0_mul⟩
  rcases h_g_n0k1 ⟨h_n_n0_lt, rfl⟩ ⟨h_n_k1_lt, rfl⟩ with
    ⟨n_n0k1_high, ⟨h_n_n0k1_high_lt, rfl⟩, n_n0k1_low, ⟨h_n_n0k1_low_lt, rfl⟩, h_n0k1_mul⟩
  rcases h_g_n1k0 ⟨h_n_n1_lt, rfl⟩ ⟨h_n_k0_lt, rfl⟩ with
    ⟨n_n1k0_high, ⟨h_n_n1k0_high_lt, rfl⟩, n_n1k0_low, ⟨h_n_n1k0_low_lt, rfl⟩, h_n1k0_mul⟩
  rcases h_g_n1k1 ⟨h_n_n1_lt, rfl⟩ ⟨h_n_k1_lt, rfl⟩ with
    ⟨n_n1k1_high, ⟨h_n_n1k1_high_lt, rfl⟩, n_n1k1_low, ⟨h_n_n1k1_low_lt, rfl⟩, h_n1k1_mul⟩

  use_only n_r0, ⟨h_n_r0_lt, rfl⟩
  use_only n_r1, ⟨h_n_r1_lt, rfl⟩
  use_only h_r_lt_n
  suffices h_exists_k : ∃ k : ℕ, u256_from_limbs n_r1 n_r0 * u256_from_limbs n_b1 n_b0 = k * u256_from_limbs n_n1 n_n0 + 1 by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd] ; rw[dvd_def]
    rcases h_exists_k with ⟨k, h_mul⟩
    use_only k
    rw [sub_eq_iff_eq_add] ; norm_cast ; rw [mul_comm _ k] ; exact h_mul

  use_only u256_from_limbs n_k1 n_k0

  -- limb 0
  have h_limb0 := limb0_eq
    n_n0k0_low n_r0b0_low part0 part1 leftover
    h_part0 h_part1 h_leftover h_leftover_0_or_1 h_n_n0k0_low_lt h_n_r0b0_low_lt
  rcases h_limb0 with ⟨n_lo, rfl, h_n_lo_zero_or_one, h_limb0⟩
  have h_n_lo_le : abs (n_lo : ℤ) ≤ u8Limit := by
    rw [Int.abs_natCast _]
    rcases h_n_lo_zero_or_one with rfl|rfl
    norm_num1
    norm_num1
  -- limb 1
  rw [coe_eq_int_coe_coe n_lo] at h_part0₁
  have h_limb1 := limb_1_or_2_eq
      (n_lo : ℤ) n_n0k0_high n_n0k1_low n_n1k0_low n_r0b0_high n_r0b1_low n_r1b0_low n_a n_a₁
      part0₁ part1₁ part2 part3 part4 part5 leftover₁
      h_part0₁ h_part1₁ h_part2 h_part3 h_part4 h_part5
      h_leftover₁ h_a h_n_a_lt h_a₁ h_n_a₁_lt h_n_lo_le
      h_n_n0k0_high_lt h_n_n0k1_low_lt h_n_n1k0_low_lt h_n_r0b0_high_lt h_n_r0b1_low_lt h_n_r1b0_low_lt
  rcases h_limb1 with ⟨n_lo₁, rfl, h_n_lo₁_le, h_limb1⟩
  --limb 2
  have h_limb2 := limb_1_or_2_eq
      n_lo₁ n_n0k1_high n_n1k0_high n_n1k1_low n_r1b0_high n_r0b1_high n_r1b1_low n_a₂ n_a₃
      part0₂ part1₂ part2₁ part3₁ part4₁ part5₁ leftover₂
      h_part0₂ h_part1₂ h_part2₁ h_part3₁ h_part4₁ h_part5₁
      h_leftover₂ h_a₂ h_n_a₂_lt h_a₃ h_n_a₃_lt h_n_lo₁_le
      h_n_n0k1_high_lt h_n_n1k0_high_lt h_n_n1k1_low_lt h_n_r1b0_high_lt h_n_r0b1_high_lt h_n_r1b1_low_lt
  rcases h_limb2 with ⟨n_lo₂, rfl, h_n_lo₂_le, h_limb2⟩
  -- limb3
  have h_limb3 : (n_r1b1_high : ℤ) = ↑n_n1k1_high + n_lo₂ := by
    rw [coe_eq_int_coe_coe, coe_eq_int_coe_coe] at h_r1b1_high_eq
    rw [←Int.cast_add] at h_r1b1_high_eq
    apply PRIME.int_coe_inj h_r1b1_high_eq
    apply lt_of_le_of_lt (abs_sub _ _)
    apply lt_of_le_of_lt (add_le_add_right (abs_add _ _) _)
    have h_p : (u128Limit + u128Limit + u128Limit : ℤ) < ↑PRIME := by unfold u128Limit PRIME ; norm_num1
    apply lt_trans _ h_p
    apply add_lt_add ; apply add_lt_add
    norm_cast
    apply lt_of_le_of_lt h_n_lo₂_le ; norm_num1
    norm_cast

  -- Rearrange the equality before applying the limbs
  unfold u256_from_limbs
  have h_lhs : (u128Limit * n_r1 + n_r0) * (u128Limit * n_b1 + n_b0) =
    u128Limit * u128Limit * (n_r1 * n_b1) + u128Limit * (n_r1 * n_b0 + n_r0 * n_b1) + n_r0 * n_b0 := by ring
  have h_rhs : (u128Limit * n_k1 + n_k0) * (u128Limit * n_n1 + n_n0) + 1 =
    u128Limit * u128Limit * (n_n1 * n_k1) + u128Limit * (n_n1 * n_k0 + n_n0 * n_k1) + n_n0 * n_k0 + 1 := by ring
  rw [h_lhs, h_rhs]
  rw [h_r0b0_mul, h_r0b1_mul, h_r1b0_mul, h_r1b1_mul, h_n0k0_mul, h_n0k1_mul, h_n1k0_mul, h_n1k1_mul]
  unfold u256_from_limbs

  rw [←Int.natCast_inj]

  have h_lhs₁ : (↑(u128Limit * u128Limit * (u128Limit * n_r1b1_high + n_r1b1_low) +
    u128Limit * (u128Limit * n_r1b0_high + n_r1b0_low + (u128Limit * n_r0b1_high + n_r0b1_low)) +
    (u128Limit * n_r0b0_high + n_r0b0_low)) : ℤ) =
      ↑u128Limit * ↑u128Limit * ↑u128Limit * ↑n_r1b1_high +
      ↑u128Limit * ↑u128Limit * (↑n_r1b1_low + ↑n_r1b0_high + ↑n_r0b1_high) +
      ↑u128Limit * (↑n_r1b0_low + ↑n_r0b1_low + ↑n_r0b0_high) +
      ↑n_r0b0_low := by norm_cast ; ring
  have h_rhs₁ : (↑(u128Limit * u128Limit * (u128Limit * n_n1k1_high + n_n1k1_low) +
    u128Limit * (u128Limit * n_n1k0_high + n_n1k0_low + (u128Limit * n_n0k1_high + n_n0k1_low)) +
    (u128Limit * n_n0k0_high + n_n0k0_low) + 1) : ℤ) =
      ↑u128Limit * ↑u128Limit * ↑u128Limit * ↑n_n1k1_high +
      ↑u128Limit * ↑u128Limit * (↑n_n0k1_high + ↑n_n1k0_high + ↑n_n1k1_low) +
      ↑u128Limit * (↑n_n0k0_high + ↑n_n0k1_low + ↑n_n1k0_low) +
      (↑n_n0k0_low + 1) := by norm_cast ; ring
  rw [h_lhs₁, h_rhs₁]
  rw [h_limb0]
  rw [h_limb1]
  rw [h_limb2]
  rw [h_limb3]

  ring

/-! # No inverse lemmas -/

lemma no_mod_inv_of_not_coprime {b m : ℕ}
      (h : ¬ Nat.Coprime b m) :
    ¬ ∃ a, a * b ≡ 1 [MOD m] := by
  by_contra h_inv
  rcases h_inv with ⟨a, h_inv⟩
  apply h
  have h_gcd := Nat.ModEq.gcd_eq h_inv
  rw [Nat.gcd_one_left, ←Nat.Coprime] at h_gcd
  apply Nat.Coprime.coprime_mul_left h_gcd

lemma not_coprime_of_exists_gcd {m n : ℕ}
      (h : ∃ g s t : ℕ, 1 < g ∧ g * s = m  ∧  g * t = n) :
    ¬ Nat.Coprime m n := by
  rcases h with ⟨g, s, t, h_g_gt, rfl, rfl⟩
  by_contra h_coprime
  rw [Nat.Coprime, Nat.gcd_mul_left] at h_coprime
  rcases Nat.eq_zero_or_pos (Nat.gcd s t) with h_zero|h_gt_zero
  · rw [h_zero, mul_zero] at h_coprime ; apply zero_ne_one h_coprime
  apply (not_lt.mpr _) h_g_gt
  rw [←h_coprime] ; apply Nat.le_mul_of_pos_right _ h_gt_zero

lemma smalls_sum_lt_u65Limit (smalls_sum : F) (n_smalls_sum_fixed : ℕ)
      (h_smalls_sum_fixed: ↑n_smalls_sum_fixed = smalls_sum + u128_bound_minus_u65_bound)
      (h_n_smalls_sum_fixed_lt: n_smalls_sum_fixed < u128Limit) :
    ∀ n : ℕ, n < u128Limit + u128Limit → smalls_sum = ↑n → n < u65Limit := by
  intros n h_n_lt h_n_eq
  rw [←(Nat.sub_sub_self (show u65Limit ≤ u128Limit by norm_num1))]
  apply Nat.lt_of_succ_le ; rw [Nat.le_sub_iff_add_le (by norm_num1)] ; rw [Nat.succ_add] ; apply Nat.succ_le_of_lt
  rw [h_n_eq, u128_bound_minus_u65_bound_eq, ←Nat.cast_add] at h_smalls_sum_fixed
  have h_n : n_smalls_sum_fixed = n + (u128Limit - u65Limit) := by
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_smalls_sum_fixed_lt) _ h_smalls_sum_fixed
    apply lt_trans _ u128Limit_triple_lt_PRIME
    apply add_lt_add h_n_lt (by norm_num1)
  rw [←h_n]
  exact h_n_smalls_sum_fixed_lt

lemma mul_smalls_lt {n_s n_t n_g : ℕ} {smalls_sum : F}
      (h_n_s_lt: n_s < u128Limit)
      (h_n_t_lt: n_t < u128Limit)
      (h_n_g_lt: n_g < u128Limit)
      (h_smalls_sum : smalls_sum = ↑n_g ∨ smalls_sum = ↑n_s + ↑n_t)
      (h_smalls_sum_lt: ∀ (n : ℕ), n < u128Limit + u128Limit → smalls_sum = ↑n → n < u65Limit) :
    n_s * n_g < u65Limit * u128Limit := by
  cases' h_smalls_sum with h_g0_small h_s1_t1_small
  · rw [mul_comm]
    apply Nat.mul_lt_mul_of_le_of_lt _ h_n_s_lt (by norm_num1); apply le_of_lt
    apply h_smalls_sum_lt _ _ h_g0_small
    apply lt_trans h_n_g_lt ; norm_num1
  apply Nat.mul_lt_mul_of_le_of_lt _ h_n_g_lt (by norm_num1)
  apply le_trans (Nat.le_add_right n_s n_t) ; apply le_of_lt
  apply h_smalls_sum_lt
  apply add_lt_add h_n_s_lt h_n_t_lt
  rw [h_s1_t1_small] ; norm_cast

lemma no_inverse_at_Merge
      (range_check : F)
      (n_b0 n_b1 n_n0 n_n1 n_g0 n_g1 n_s0 n_s1 n_t0 n_t1 : ℕ)
      (g0s0_low g0t0_low g0s0_high g0t0_high smalls_sum : F)
      (ρ_branch_id
          ρ_r0 ρ_r1
          ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
          ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
          ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
          ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
          ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
          ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
          ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
          ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F)
      (h_n_b0_lt: n_b0 < u128Limit)
      (h_n_b1_lt: n_b1 < u128Limit)
      (h_n_n0_lt: n_n0 < u128Limit)
      (h_n_n1_lt: n_n1 < u128Limit)
      (h_n_g0_lt: n_g0 < u128Limit)
      (h_n_g1_lt: n_g1 < u128Limit)
      (h_n_s0_lt: n_s0 < u128Limit)
      (h_n_s1_lt: n_s1 < u128Limit)
      (h_n_t0_lt: n_t0 < u128Limit)
      (h_n_t1_lt: n_t1 < u128Limit)
      (h_g0s0_low: g0s0_low = ↑n_b0)
      (h_g0t0_low: g0t0_low = ↑n_n0)
      (h_gst : (n_g1 = 0 ∧ (smalls_sum = ↑n_g0 ∨ smalls_sum = ↑n_s1 + ↑n_t1)) ∨
        (n_s1 = 0 ∧ n_t1 = 0 ∧ (smalls_sum = ↑n_g1 ∨ smalls_sum = ↑n_s0 + ↑n_t0)))
      (h_one_lt_g : 1 < u256_from_limbs n_g1 n_g0)
      (h_Merge : ∃ κ₁,
        auto_spec_u256_guarantee_inv_mod_n_MERGE κ₁ range_check
          g0s0_low (↑n_b1) g0t0_low (↑n_n1) (↑n_g0) (↑n_s0) (↑n_t0) g0s0_high g0t0_high
          ↑(u128Limit * n_s1 * n_g1 + n_s1 * n_g0 + n_s0 * n_g1)
          ↑(u128Limit * n_t1 * n_g1 + n_t1 * n_g0 + n_t0 * n_g1)
          smalls_sum
          ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1
    ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high
    ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
    ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low) :
    ρ_branch_id = 1 ∧ (
      u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
      u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
        ¬ ∃ r, r * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0]) := by

  rcases h_Merge with ⟨-, smalls_sum_fixed, h_smalls_sum_fixed, ⟨n_smalls_sum_fixed, h_n_smalls_sum_fixed_lt, rfl⟩, h_cont⟩
  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound
  replace h_n_smalls_sum_fixed_lt := lt_of_lt_of_le h_n_smalls_sum_fixed_lt h_rcBound

  have h_smalls_sum_lt := smalls_sum_lt_u65Limit smalls_sum n_smalls_sum_fixed h_smalls_sum_fixed h_n_smalls_sum_fixed_lt

  rcases h_cont with ⟨h_b1, h_n1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor ; rfl

  rintro h_g_g0s0 h_g_g0t0
  rcases h_g_g0s0 ⟨h_n_g0_lt, rfl⟩ ⟨h_n_s0_lt, rfl⟩ with
    ⟨n_g0s0_high, ⟨h_n_g0s0_high_lt, rfl⟩, n_g0s0_low, ⟨h_n_g0s0_low_lt, rfl⟩, h_g0s0_mul⟩
  rcases h_g_g0t0 ⟨h_n_g0_lt, rfl⟩ ⟨h_n_t0_lt, rfl⟩ with
    ⟨n_g0t0_high, ⟨h_n_g0t0_high_lt, rfl⟩, n_g0t0_low, ⟨h_n_g0t0_low_lt, rfl⟩, h_g0t0_mul⟩
  have n_b0_eq : n_g0s0_low = n_b0 := by
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_g0s0_low_lt) (lt_PRIME_of_lt_u128Limit h_n_b0_lt) h_g0s0_low
  rw [n_b0_eq] at h_g0s0_mul
  have n_n0_eq : n_g0t0_low = n_n0 := by
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_g0t0_low_lt) (lt_PRIME_of_lt_u128Limit h_n_n0_lt) h_g0t0_low
  rw [n_n0_eq] at h_g0t0_mul

  have h_b1_eq : n_b1 = u128Limit * n_s1 * n_g1 + n_s1 * n_g0 + n_s0 * n_g1 + n_g0s0_high := by
    rw [←Nat.cast_add] at h_b1
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_b1_lt) _ h_b1
    cases' h_gst with h h
    · rcases h with ⟨rfl, h_small⟩
      ring_nf
      apply lt_trans _ u65Limit_mul_u128Limit_add_u128Limit_lt_PRIME
      apply add_lt_add _ h_n_g0s0_high_lt
      apply mul_smalls_lt h_n_s1_lt h_n_t1_lt h_n_g0_lt h_small h_smalls_sum_lt
    rcases h with ⟨rfl, rfl, h_small⟩
    ring_nf
    apply lt_trans _ u65Limit_mul_u128Limit_add_u128Limit_lt_PRIME
    apply add_lt_add _ h_n_g0s0_high_lt
    rw [mul_comm]
    apply mul_smalls_lt h_n_s0_lt h_n_t0_lt h_n_g1_lt h_small h_smalls_sum_lt

  have h_n1_eq : n_n1 = u128Limit * n_t1 * n_g1 + n_t1 * n_g0 + n_t0 * n_g1 + n_g0t0_high := by
    rw [←Nat.cast_add] at h_n1
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n1_lt) _ h_n1
    cases' h_gst with h h
    · rcases h with ⟨rfl, h_small⟩
      ring_nf
      apply lt_trans _ u65Limit_mul_u128Limit_add_u128Limit_lt_PRIME
      apply add_lt_add _ h_n_g0t0_high_lt
      rw [add_comm (n_s1 : F) (n_t1 : F)] at h_small
      apply mul_smalls_lt h_n_t1_lt h_n_s1_lt h_n_g0_lt h_small h_smalls_sum_lt
    rcases h with ⟨rfl, rfl, h_small⟩
    ring_nf
    apply lt_trans _ u65Limit_mul_u128Limit_add_u128Limit_lt_PRIME
    apply add_lt_add _ h_n_g0t0_high_lt
    rw [mul_comm]
    rw [add_comm (n_s0 : F) (n_t0 : F)] at h_small
    apply mul_smalls_lt h_n_t0_lt h_n_s0_lt h_n_g1_lt h_small h_smalls_sum_lt

  suffices h_has_gcd : ∃ n_g n_s n_t, 1 < n_g ∧ n_g * n_s = u256_from_limbs n_b1 n_b0 ∧ n_g * n_t = u256_from_limbs n_n1 n_n0 by
    apply no_mod_inv_of_not_coprime
    apply not_coprime_of_exists_gcd
    apply h_has_gcd

  use_only (u256_from_limbs n_g1 n_g0), (u256_from_limbs n_s1 n_s0), (u256_from_limbs n_t1 n_t0)
  constructor ; exact h_one_lt_g
  unfold u256_from_limbs
  constructor
  · have h_lhs : (u128Limit * n_g1 + n_g0) * (u128Limit * n_s1 + n_s0) =
      u128Limit * (u128Limit * n_s1 *n_g1 +  n_s1 * n_g0 + n_s0 * n_g1) + (n_g0 * n_s0) := by ring
    rw [h_lhs]
    rw [h_b1_eq, h_g0s0_mul]
    unfold u256_from_limbs
    ring
  have h_lhs : (u128Limit * n_g1 + n_g0) * (u128Limit * n_t1 + n_t0) =
    u128Limit * (u128Limit * n_t1 *n_g1 +  n_t1 * n_g0 + n_t0 * n_g1) + (n_g0 * n_t0) := by ring
  rw [h_lhs]
  rw [h_n1_eq, h_g0t0_mul]
  unfold u256_from_limbs
  ring

lemma no_inverse_at_GIsValid
      {range_check : F}
      {n_b0 n_b1 n_n0 n_n1 n_g0 n_g1 n_s0 n_s1 n_t0 n_t1 : ℕ}
      {ρ_branch_id
          ρ_r0 ρ_r1
          ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
          ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
          ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
          ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
          ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
          ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
          ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
          ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F}
      (h_n_b0_lt: n_b0 < u128Limit)
      (h_n_b1_lt: n_b1 < u128Limit)
      (h_n_n0_lt: n_n0 < u128Limit)
      (h_n_n1_lt: n_n1 < u128Limit)
      (h_n_g0_lt: n_g0 < u128Limit)
      (h_n_g1_lt: n_g1 < u128Limit)
      (h_n_s0_lt: n_s0 < u128Limit)
      (h_n_s1_lt: n_s1 < u128Limit)
      (h_n_t0_lt: n_t0 < u128Limit)
      (h_n_t1_lt: n_t1 < u128Limit)
      (h_one_lt_g : 1 < u256_from_limbs n_g1 n_g0)
      (h_GIsValid :
        ∃ κ₁, auto_spec_u256_guarantee_inv_mod_n_GIsValid κ₁
          range_check ↑n_b0 ↑n_b1 ↑n_n0 ↑n_n1 ↑n_g0 ↑n_g1 ↑n_s0 ↑n_s1 ↑n_t0 ↑n_t1
          ρ_branch_id
          ρ_r0 ρ_r1
          ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
          ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
          ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
          ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
          ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
          ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
          ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
          ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low) :
    ρ_branch_id = 1 ∧ (
      u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
      u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
        ¬ ∃ r, r * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0]) := by

  rcases h_GIsValid with ⟨-, g0s0_low, h_g0s0_low, g0s0_high, g0t0_low, h_g0t0_low, g0t0_high, gs1, gt1, h_cont⟩

  rcases h_cont with ⟨smalls_sum, ⟨h_g1_eq_zero, h_gs1_eq, h_gt1_eq, h_cont⟩|⟨h_g1_ne_zero, h_cont⟩⟩
  · have h_g1_eq_zero : n_g1 = 0 := PRIME.nat_coe_field_zero (lt_PRIME_of_lt_u128Limit h_n_g1_lt) rfl h_g1_eq_zero
    have h_gs1 : n_s1 * n_g0 = u128Limit * n_s1 * n_g1 + n_s1 * n_g0 + n_s0 * n_g1 := by rw [h_g1_eq_zero] ; ring
    have h_gt1 : n_t1 * n_g0 = u128Limit * n_t1 * n_g1 + n_t1 * n_g0 + n_t0 * n_g1 := by rw [h_g1_eq_zero] ; ring
    rw [←Nat.cast_mul, h_gs1] at h_gs1_eq
    rw [←Nat.cast_mul, h_gt1] at h_gt1_eq

    rcases h_cont with ⟨g0_is_small, ⟨h_g0_is_small_eq_zero, h_smalls_sum, h_Merge⟩|⟨h_g0_is_small_ne_zero, -, h_smalls_sum, h_Merge⟩⟩
    · rw [h_gs1_eq, h_gt1_eq] at h_Merge
      apply no_inverse_at_Merge
        (h_n_b0_lt := h_n_b0_lt)
        (h_n_b1_lt := h_n_b1_lt)
        (h_n_n0_lt := h_n_n0_lt)
        (h_n_n1_lt := h_n_n1_lt)
        (h_n_g0_lt := h_n_g0_lt)
        (h_n_g1_lt := h_n_g1_lt)
        (h_n_s0_lt := h_n_s0_lt)
        (h_n_s1_lt := h_n_s1_lt)
        (h_n_t0_lt := h_n_t0_lt)
        (h_n_t1_lt := h_n_t1_lt)
        (h_g0s0_low := h_g0s0_low)
        (h_g0t0_low := h_g0t0_low)
        (h_gst := Or.inl ⟨h_g1_eq_zero, Or.inr h_smalls_sum⟩)
        (h_one_lt_g := h_one_lt_g)
        (h_Merge := h_Merge)

    rw [h_gs1_eq, h_gt1_eq] at h_Merge
    apply no_inverse_at_Merge
      (h_n_b0_lt := h_n_b0_lt)
      (h_n_b1_lt := h_n_b1_lt)
      (h_n_n0_lt := h_n_n0_lt)
      (h_n_n1_lt := h_n_n1_lt)
      (h_n_g0_lt := h_n_g0_lt)
      (h_n_g1_lt := h_n_g1_lt)
      (h_n_s0_lt := h_n_s0_lt)
      (h_n_s1_lt := h_n_s1_lt)
      (h_n_t0_lt := h_n_t0_lt)
      (h_n_t1_lt := h_n_t1_lt)
      (h_g0s0_low := h_g0s0_low)
      (h_g0t0_low := h_g0t0_low)
      (h_gst := Or.inl ⟨h_g1_eq_zero, Or.inl h_smalls_sum⟩)
      (h_one_lt_g := h_one_lt_g)
      (h_Merge := h_Merge)

  rcases h_cont with ⟨-, h_gs1_eq, h_gt1_eq, h_s1_eq_zero, h_t1_eq_zero, h_cont⟩
  have h_s1_eq_zero : n_s1 = 0 := PRIME.nat_coe_field_zero (lt_PRIME_of_lt_u128Limit h_n_s1_lt) rfl h_s1_eq_zero
  have h_t1_eq_zero : n_t1 = 0 := PRIME.nat_coe_field_zero (lt_PRIME_of_lt_u128Limit h_n_t1_lt) rfl h_t1_eq_zero
  have h_gs1 : n_s0 * n_g1 = u128Limit * n_s1 * n_g1 + n_s1 * n_g0 + n_s0 * n_g1 := by rw [h_s1_eq_zero] ; ring
  have h_gt1 : n_t0 * n_g1 = u128Limit * n_t1 * n_g1 + n_t1 * n_g0 + n_t0 * n_g1 := by rw [h_t1_eq_zero] ; ring
  rw [←Nat.cast_mul, h_gs1] at h_gs1_eq
  rw [←Nat.cast_mul, h_gt1] at h_gt1_eq
  rcases h_cont with ⟨g1_is_small,
    ⟨h_g1_is_small_eq_zero, h_smalls_sum, h_Merge⟩|⟨h_g1_is_small_ne_zero, -, h_smalls_sum, h_Merge⟩⟩
  · rw [h_gs1_eq, h_gt1_eq] at h_Merge
    apply no_inverse_at_Merge
      (h_n_b0_lt := h_n_b0_lt)
      (h_n_b1_lt := h_n_b1_lt)
      (h_n_n0_lt := h_n_n0_lt)
      (h_n_n1_lt := h_n_n1_lt)
      (h_n_g0_lt := h_n_g0_lt)
      (h_n_g1_lt := h_n_g1_lt)
      (h_n_s0_lt := h_n_s0_lt)
      (h_n_s1_lt := h_n_s1_lt)
      (h_n_t0_lt := h_n_t0_lt)
      (h_n_t1_lt := h_n_t1_lt)
      (h_g0s0_low := h_g0s0_low)
      (h_g0t0_low := h_g0t0_low)
      (h_gst := Or.inr ⟨h_s1_eq_zero, h_t1_eq_zero, Or.inr h_smalls_sum⟩)
      (h_one_lt_g := h_one_lt_g)
      (h_Merge := h_Merge)
  rw [h_gs1_eq, h_gt1_eq] at h_Merge
  apply no_inverse_at_Merge
    (h_n_b0_lt := h_n_b0_lt)
    (h_n_b1_lt := h_n_b1_lt)
    (h_n_n0_lt := h_n_n0_lt)
    (h_n_n1_lt := h_n_n1_lt)
    (h_n_g0_lt := h_n_g0_lt)
    (h_n_g1_lt := h_n_g1_lt)
    (h_n_s0_lt := h_n_s0_lt)
    (h_n_s1_lt := h_n_s1_lt)
    (h_n_t0_lt := h_n_t0_lt)
    (h_n_t1_lt := h_n_t1_lt)
    (h_g0s0_low := h_g0s0_low)
    (h_g0t0_low := h_g0t0_low)
    (h_gst := Or.inr ⟨h_s1_eq_zero, h_t1_eq_zero, Or.inl h_smalls_sum⟩)
    (h_one_lt_g := h_one_lt_g)
    (h_Merge := h_Merge)

lemma no_inverse_at_NoInverse
      {range_check : F}
      {n_b0 n_b1 n_n0 n_n1 : ℕ}
      {g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 : F}
      {ρ_branch_id
          ρ_r0 ρ_r1
          ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
          ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
          ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
          ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
          ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
          ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
          ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
          ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F}
      (h_n_b0_lt: n_b0 < u128Limit)
      (h_n_b1_lt: n_b1 < u128Limit)
      (h_n_n0_lt: n_n0 < u128Limit)
      (h_n_n1_lt: n_n1 < u128Limit)
      (h_NoInverse : g0_or_no_inv ≠ 0 ∧
        ∃ κ₁, auto_spec_u256_guarantee_inv_mod_n_NoInverse κ₁
          range_check ↑n_b0 ↑n_b1 ↑n_n0 ↑n_n1
          g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1
          ρ_branch_id
          ρ_r0 ρ_r1
          ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low
          ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low
          ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low
          ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low
          ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low
          ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low
          ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low
          ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low) :
    ρ_branch_id = 1 ∧ u256_from_limbs n_n1 n_n0 = 1 ∨
    ρ_branch_id = 1 ∧ (
      u128_mul_guarantee ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low →
      u128_mul_guarantee ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low →
        ¬ ∃ r, r * u256_from_limbs n_b1 n_b0 ≡ 1 [MOD u256_from_limbs n_n1 n_n0]) := by

  rcases h_NoInverse with ⟨h_g0_or_no_inv, -, g0, rfl, g1, rfl, s0, rfl, s1, rfl, t0, rfl, t1, rfl, h_cont⟩

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  rcases h_cont with ⟨⟨n_g0, h_n_g0_lt, rfl⟩, ⟨n_g1, h_n_g1_lt, rfl⟩, h_cont⟩
  replace h_n_g0_lt := lt_of_lt_of_le h_n_g0_lt h_rcBound
  replace h_n_g1_lt := lt_of_lt_of_le h_n_g1_lt h_rcBound
  rcases h_cont with ⟨⟨n_s0, h_n_s0_lt, rfl⟩, ⟨n_s1, h_n_s1_lt, rfl⟩, h_cont⟩
  replace h_n_s0_lt := lt_of_lt_of_le h_n_s0_lt h_rcBound
  replace h_n_s1_lt := lt_of_lt_of_le h_n_s1_lt h_rcBound
  rcases h_cont with ⟨⟨n_t0, h_n_t0_lt, rfl⟩, ⟨n_t1, h_n_t1_lt, rfl⟩, h_cont⟩
  replace h_n_t0_lt := lt_of_lt_of_le h_n_t0_lt h_rcBound
  replace h_n_t1_lt := lt_of_lt_of_le h_n_t1_lt h_rcBound

  rw [←(PRIME.nat_coe_field_iff_ne_zero (lt_PRIME_of_lt_u128Limit h_n_g0_lt) rfl)] at h_g0_or_no_inv

  rcases h_cont with ⟨g0_minus_one, ⟨h_g1_zero, h_cont⟩|⟨h_g1_ne_zero, h_cont⟩⟩
  · rcases h_cont with ⟨h_g0_minus_one, ⟨h_g0_minus_one_eq_zero, h_n1_zero, h_n0_one, h_cont⟩|⟨h_g0_minus_one_ne_zero, h_cont⟩⟩
    · left
      constructor
      · rcases h_cont with ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, h_cont|h_cont⟩|⟨_, _, h_cont⟩⟩
        · rcases h_cont with ⟨_, _, _, _, _, _, _, _, h_branch_id, _⟩
          use h_branch_id
        · rcases h_cont with ⟨_, _, _, _, _, _, _, _, _, h_branch_id, _⟩
          use h_branch_id
        rcases h_cont with ⟨_, _, _, _, _, h_cont|h_cont⟩
        · rcases h_cont with ⟨_, _, _, _, _, _, _, _, h_branch_id, _⟩
          use h_branch_id
        rcases h_cont with ⟨_, _, _, _, _, _, _, _, _, h_branch_id, _⟩
        use h_branch_id
      rw [zero, ←Nat.cast_zero] at h_n1_zero
      have h_n_n1_zero := PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n1_lt) (by rw [PRIME] ; norm_num1) h_n1_zero
      rw [one, ←Nat.cast_one] at h_n0_one
      have h_n_n0_one := PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_n0_lt) (by rw [PRIME] ; norm_num1) h_n0_one
      rw [h_n_n1_zero, h_n_n0_one]
      unfold u256_from_limbs ; norm_num1
    right
    have h_one_lt_g : 1 < u256_from_limbs n_g1 n_g0 := by
      unfold u256_from_limbs
      apply lt_of_lt_of_le _ (Nat.le_add_left _ _)
      have h_one_le_g0 := Nat.one_le_iff_ne_zero.mpr h_g0_or_no_inv
      apply Nat.lt_of_le_of_ne h_one_le_g0
      rw [h_g0_minus_one] at h_g0_minus_one_ne_zero
      by_contra h_eq
      rw [←h_eq, one, Nat.cast_one, sub_self _] at h_g0_minus_one_ne_zero
      apply h_g0_minus_one_ne_zero ; rfl
    apply no_inverse_at_GIsValid
      h_n_b0_lt h_n_b1_lt h_n_n0_lt h_n_n1_lt
      h_n_g0_lt h_n_g1_lt h_n_s0_lt h_n_s1_lt h_n_t0_lt h_n_t1_lt
      h_one_lt_g
      (h_GIsValid := h_cont)
  have h_one_lt_g : 1 < u256_from_limbs n_g1 n_g0 := by
    unfold u256_from_limbs
    apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
    rw [←(Nat.mul_one 1)] ; apply Nat.mul_lt_mul_of_lt_of_le' (by norm_num1) _ Nat.zero_lt_one
    rw [Nat.one_le_iff_ne_zero]
    apply (PRIME.nat_coe_field_iff_ne_zero (lt_PRIME_of_lt_u128Limit h_n_g1_lt) rfl).mpr h_g1_ne_zero
  right
  apply no_inverse_at_GIsValid
    h_n_b0_lt h_n_b1_lt h_n_n0_lt h_n_n1_lt
    h_n_g0_lt h_n_g1_lt h_n_s0_lt h_n_s1_lt h_n_t0_lt h_n_t1_lt
    h_one_lt_g
    (h_GIsValid := h_cont)


theorem sound_u256_guarantee_inv_mod_n
    (κ : ℕ)
    (range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : F)
    (h_auto : auto_spec_u256_guarantee_inv_mod_n κ range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low) :
  spec_u256_guarantee_inv_mod_n κ range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low := by

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  rintro n_b0 ⟨h_n_b0_lt, rfl⟩ n_b1 ⟨h_n_b1_lt, rfl⟩ n_n0 ⟨h_n_n0_lt, rfl⟩ n_n1 ⟨h_n_n1_lt, rfl⟩
  rcases h_auto with ⟨-, -, g0_or_no_inv, g1_option, s_or_r0, s_or_r1, t_or_k0, t_or_k1, h_has_inv|h_not_coprime⟩
  · left
    rcases h_has_inv with ⟨rfl, r0, rfl, r1, tfl, k0, rfl, k1, rfl, h_has_inv⟩
    rcases h_has_inv with ⟨⟨n_r0, h_n_r0_lt, rfl⟩, ⟨n_r1, h_n_r1_lt, rfl⟩, ⟨n_k0, h_n_k0_lt, rfl⟩, ⟨n_k1, h_n_k1_lt, rfl⟩, h_has_inv⟩
    replace h_n_r0_lt := lt_of_lt_of_le h_n_r0_lt h_rcBound
    replace h_n_r1_lt := lt_of_lt_of_le h_n_r1_lt h_rcBound
    replace h_n_k0_lt := lt_of_lt_of_le h_n_k0_lt h_rcBound
    replace h_n_k1_lt := lt_of_lt_of_le h_n_k1_lt h_rcBound
    rcases h_has_inv with ⟨diff1, rfl, diff0, diff_min_1, h_n1_eq_r1|h_n1_ne_r1⟩
    · rcases h_n1_eq_r1 with ⟨h_n1_min_r1_zero, rfl, rfl, h_rc, h_After⟩
      have h_r_lt_n := r_lt_n_of_high_eq n_n0 n_n1 n_r0 n_r1 h_n_n0_lt h_n_n1_lt h_n_r0_lt h_n_r1_lt h_n1_min_r1_zero h_rc
      -- continue the proof at the AFTER block
      apply inv_exists_at_After h_n_b0_lt h_n_b1_lt h_n_n0_lt h_n_n1_lt h_n_r0_lt h_n_r1_lt h_n_k0_lt h_n_k1_lt h_r_lt_n (h_After := h_After)
    rcases h_n1_ne_r1 with ⟨h_n1_min_r1_ne_zero, -, h_rc, h_After⟩
    have h_r_lt_n := r_lt_n_of_high_ne n_n0 n_n1 n_r0 n_r1 h_n_n1_lt h_n_r0_lt h_n_r1_lt h_n1_min_r1_ne_zero h_rc
    -- continue the proof at the AFTER block
    apply inv_exists_at_After h_n_b0_lt h_n_b1_lt h_n_n0_lt h_n_n1_lt h_n_r0_lt h_n_r1_lt h_n_k0_lt h_n_k1_lt h_r_lt_n (h_After := h_After)
  right
  apply no_inverse_at_NoInverse h_n_b0_lt h_n_b1_lt h_n_n0_lt h_n_n1_lt (h_NoInverse := h_not_coprime)
