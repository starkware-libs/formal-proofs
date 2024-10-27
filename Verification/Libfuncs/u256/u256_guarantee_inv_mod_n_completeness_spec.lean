import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u256_guarantee_inv_mod_n_completeness

def zero : ℤ := (0 : ℤ) -- 0
def one : ℤ := (1 : ℤ) -- 1
def u128_bound_minus_u65_bound : ℤ := (340282366920938463426481119284349108224 : ℤ) -- BigInt::from(2).pow(128) - BigInt::from(2).pow(65)
def u128_bound_minus_i16_upper_bound : ℤ := (340282366920938463463374607431768178688 : ℤ) -- u128::MAX - i16::MAX as u128
def i16_lower_bound : ℤ := (-32768 : ℤ) -- i16::MIN
def u128_limit : ℤ := (340282366920938463463374607431768211456 : ℤ) -- (BigInt::from(u128::MAX) + 1) as BigInt
def u64_limit : ℤ := (18446744073709551616 : ℤ) -- (BigInt::from(u64::MAX) + 1) as BigInt

lemma u128_limit_eq : u128_limit = ↑u128Limit := by rfl

def auto_spec_u256_guarantee_inv_mod_n_Done (range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
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

def auto_spec_u256_guarantee_inv_mod_n_MERGE (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  ∃ smalls_sum_fixed : ℤ, smalls_sum_fixed % PRIME = (smalls_sum + u128_bound_minus_u65_bound) % PRIME ∧
  VmIsRangeChecked u128Limit smalls_sum_fixed ∧
  b1 % PRIME = (gs1 + g0s0_high) % PRIME ∧
  n1 % PRIME = (gt1 + g0t0_high) % PRIME ∧
  ρ_branch_id = 1 ∧
  ρ_n1_or_g0 = g0 ∧
  ρ_k0_or_s0 = s0 ∧
  ρ_n1k0_high_or_g0s0_high = g0s0_high ∧
  ρ_n1k0_low_or_g0s0_low = g0s0_low ∧
  ρ_n1_or_g0₁ = g0 ∧
  ρ_k1_or_t0 = t0 ∧
  ρ_n1k1_high_or_g0t0_high = g0t0_high ∧
  ρ_n1k1_low_or_g0t0_low = g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_G1IsSmall (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  smalls_sum = g1 ∧
  auto_spec_u256_guarantee_inv_mod_n_MERGE
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  gs1 % PRIME = (s0 * g1) % PRIME ∧
  gt1 % PRIME = (t0 * g1) % PRIME ∧
  s1 = zero ∧
  t1 = zero ∧
  ∃ g1_is_small : ℤ,
  (
    (g1_is_small = 0 ∧
      smalls_sum % PRIME = (s0 + t0) % PRIME ∧
      auto_spec_u256_guarantee_inv_mod_n_MERGE
        range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    ) ∨
    (g1_is_small ≠ 0 ∧
      auto_spec_u256_guarantee_inv_mod_n_G1IsSmall
        range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_G0IsSmall (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  smalls_sum = g0 ∧
  auto_spec_u256_guarantee_inv_mod_n_MERGE
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_GIsValid (range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  ∃ g0s0_low : ℤ, g0s0_low = b0 ∧
  ∃ g0s0_high : ℤ,
  ∃ g0t0_low : ℤ, g0t0_low = n0 ∧
  ∃ g0t0_high : ℤ,
  ∃ gs1 : ℤ,
  ∃ gt1 : ℤ,
  ∃ smalls_sum : ℤ,
  (
    (g1 = 0 ∧
      gs1 % PRIME = (s1 * g0) % PRIME ∧
      gt1 % PRIME = (t1 * g0) % PRIME ∧
      ∃ g0_is_small : ℤ,
      (
        (g0_is_small = 0 ∧
          smalls_sum % PRIME = (s1 + t1) % PRIME ∧
          auto_spec_u256_guarantee_inv_mod_n_MERGE
            range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (g0_is_small ≠ 0 ∧
          auto_spec_u256_guarantee_inv_mod_n_G0IsSmall
            range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g1 ≠ 0 ∧
      auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO
        range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_NoInverse (range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  ∃ g0 : ℤ, g0 = g0_or_no_inv ∧
  ∃ g1 : ℤ, g1 = g1_option ∧
  ∃ s0 : ℤ, s0 = s_or_r0 ∧
  ∃ s1 : ℤ, s1 = s_or_r1 ∧
  ∃ t0 : ℤ, t0 = t_or_k0 ∧
  ∃ t1 : ℤ, t1 = t_or_k1 ∧
  VmIsRangeChecked u128Limit g0 ∧
  VmIsRangeChecked u128Limit g1 ∧
  VmIsRangeChecked u128Limit s0 ∧
  VmIsRangeChecked u128Limit s1 ∧
  VmIsRangeChecked u128Limit t0 ∧
  VmIsRangeChecked u128Limit t1 ∧
  ∃ g0_minus_1 : ℤ,
  (
    (g1 = 0 ∧
      g0_minus_1 % PRIME = (g0 - one) % PRIME ∧
      (
        (g0_minus_1 = 0 ∧
          n1 = zero ∧
          n0 = one ∧
          auto_spec_u256_guarantee_inv_mod_n_GIsValid
            range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (g0_minus_1 ≠ 0 ∧
          auto_spec_u256_guarantee_inv_mod_n_GIsValid
            range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g1 ≠ 0 ∧
      auto_spec_u256_guarantee_inv_mod_n_GIsValid
        range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

def auto_spec_u256_guarantee_inv_mod_n_After (range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  ∃ r0b0_low : ℤ,
  ∃ r0b0_high : ℤ,
  ∃ r0b1_low : ℤ,
  ∃ r0b1_high : ℤ,
  ∃ r1b0_low : ℤ,
  ∃ r1b0_high : ℤ,
  ∃ r1b1_low : ℤ,
  ∃ r1b1_high : ℤ,
  ∃ n0k0_low : ℤ,
  ∃ n0k0_high : ℤ,
  ∃ n0k1_low : ℤ,
  ∃ n0k1_high : ℤ,
  ∃ n1k0_low : ℤ,
  ∃ n1k0_high : ℤ,
  ∃ n1k1_low : ℤ,
  ∃ n1k1_high : ℤ,
  ∃ part0 : ℤ, part0 % PRIME = (n0k0_low + one) % PRIME ∧
  ∃ part1 : ℤ, part1 % PRIME = (part0 - r0b0_low) % PRIME ∧
  ∃ leftover : ℤ, part1 % PRIME = (leftover * u128_limit) % PRIME ∧
  leftover % PRIME = (leftover * leftover) % PRIME ∧
  ∃ part0₁ : ℤ, part0₁ % PRIME = (n0k0_high + leftover) % PRIME ∧
  ∃ part1₁ : ℤ, part1₁ % PRIME = (part0₁ + n0k1_low) % PRIME ∧
  ∃ part2 : ℤ, part2 % PRIME = (part1₁ + n1k0_low) % PRIME ∧
  ∃ part3 : ℤ, part3 % PRIME = (part2 - r0b0_high) % PRIME ∧
  ∃ part4 : ℤ, part4 % PRIME = (part3 - r0b1_low) % PRIME ∧
  ∃ part5 : ℤ, part5 % PRIME = (part4 - r1b0_low) % PRIME ∧
  ∃ leftover₁ : ℤ, part5 % PRIME = (leftover₁ * u128_limit) % PRIME ∧
  ∃ a : ℤ, a % PRIME = (leftover₁ - i16_lower_bound) % PRIME ∧
  VmIsRangeChecked u128Limit a ∧
  ∃ a₁ : ℤ, a₁ % PRIME = (leftover₁ + u128_bound_minus_i16_upper_bound) % PRIME ∧
  VmIsRangeChecked u128Limit a₁ ∧
  ∃ part0₂ : ℤ, part0₂ % PRIME = (n0k1_high + leftover₁) % PRIME ∧
  ∃ part1₂ : ℤ, part1₂ % PRIME = (part0₂ + n1k0_high) % PRIME ∧
  ∃ part2₁ : ℤ, part2₁ % PRIME = (part1₂ + n1k1_low) % PRIME ∧
  ∃ part3₁ : ℤ, part3₁ % PRIME = (part2₁ - r1b0_high) % PRIME ∧
  ∃ part4₁ : ℤ, part4₁ % PRIME = (part3₁ - r0b1_high) % PRIME ∧
  ∃ part5₁ : ℤ, part5₁ % PRIME = (part4₁ - r1b1_low) % PRIME ∧
  ∃ leftover₂ : ℤ, part5₁ % PRIME = (leftover₂ * u128_limit) % PRIME ∧
  ∃ a₂ : ℤ, a₂ % PRIME = (leftover₂ - i16_lower_bound) % PRIME ∧
  VmIsRangeChecked u128Limit a₂ ∧
  ∃ a₃ : ℤ, a₃ % PRIME = (leftover₂ + u128_bound_minus_i16_upper_bound) % PRIME ∧
  VmIsRangeChecked u128Limit a₃ ∧
  r1b1_high % PRIME = (n1k1_high + leftover₂) % PRIME ∧
  auto_spec_u256_guarantee_inv_mod_n_Done
    range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n_HighDiff (range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  VmIsRangeChecked u128Limit diff1 ∧
  auto_spec_u256_guarantee_inv_mod_n_After
    range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low

def auto_spec_u256_guarantee_inv_mod_n (range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ g0_or_no_inv : ℤ,
  ∃ g1_option : ℤ,
  ∃ s_or_r0 : ℤ,
  ∃ s_or_r1 : ℤ,
  ∃ t_or_k0 : ℤ,
  ∃ t_or_k1 : ℤ,
  (
    (g0_or_no_inv = 0 ∧
      ∃ r0 : ℤ, r0 = s_or_r0 ∧
      ∃ r1 : ℤ, r1 = s_or_r1 ∧
      ∃ k0 : ℤ, k0 = t_or_k0 ∧
      ∃ k1 : ℤ, k1 = t_or_k1 ∧
      VmIsRangeChecked u128Limit r0 ∧
      VmIsRangeChecked u128Limit r1 ∧
      VmIsRangeChecked u128Limit k0 ∧
      VmIsRangeChecked u128Limit k1 ∧
      ∃ diff1 : ℤ, diff1 % PRIME = (n1 - r1) % PRIME ∧
      ∃ diff0 : ℤ,
      ∃ diff0_min_1 : ℤ,
      (
        (diff1 = 0 ∧
          diff0 % PRIME = (n0 - r0) % PRIME ∧
          diff0_min_1 % PRIME = (diff0 - one) % PRIME ∧
          VmIsRangeChecked u128Limit diff0_min_1 ∧
          auto_spec_u256_guarantee_inv_mod_n_After
            range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        ) ∨
        (diff1 ≠ 0 ∧
          auto_spec_u256_guarantee_inv_mod_n_HighDiff
            range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
        )
      )
    ) ∨
    (g0_or_no_inv ≠ 0 ∧
      auto_spec_u256_guarantee_inv_mod_n_NoInverse
        range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low
    )
  )

-- # First case: modulo 1 (n = 1)

lemma spec_satisfiable_u256_guarantee_inv_mod_1
    (range_check b0 b1 n0 n1 : ℤ)
    -- Add assumptions on the arguments here.
    (h_b0_nonneg : 0 ≤ b0)
    (h_b1_nonneg : 0 ≤ b1)
    (h_n0_nonneg : 0 ≤ n0)
    (h_n1_nonneg : 0 ≤ n1)
    (h_b0_lt : b0 < u128Limit)
    (h_b1_lt : b1 < u128Limit)
    (h_n0_lt : n0 < u128Limit)
    (h_n1_lt : n1 < u128Limit)
    (h_n_nonzero : 0 ≠ n0 ∨ 0 ≠ n1)
    -- The special case handled here
    (h_nn_1 : u256_from_limbs (Int.toNat n1) (Int.toNat n0) = 1) :
  ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
    auto_spec_u256_guarantee_inv_mod_n range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low := by

  -- replace the integers by the equivalent natural numbers.
  rw [←(Int.toNat_of_nonneg h_b0_nonneg), ←(Int.toNat_of_nonneg h_b1_nonneg)]
  rw [←(Int.toNat_of_nonneg h_n0_nonneg), ←(Int.toNat_of_nonneg h_n1_nonneg)]
  rw [←(Int.toNat_lt h_b0_nonneg)] at h_b0_lt
  rw [←(Int.toNat_lt h_b1_nonneg)] at h_b1_lt
  rw [←(Int.toNat_lt h_n0_nonneg)] at h_n0_lt
  rw [←(Int.toNat_lt h_n1_nonneg)] at h_n1_lt

  have h_n1 : ↑(Int.toNat n1) = (0 : ℤ) := by
    rw [←Nat.cast_zero, Nat.cast_inj, ←Nat.lt_one_iff]
    apply lt_one_of_mul_lt_right (a := u128Limit)
    apply lt_of_le_of_lt (le_self_add (c := Int.toNat n0))
    dsimp [u256_from_limbs] at h_nn_1 ; rw [h_nn_1]
    norm_num1

  have h_n0 : ↑(Int.toNat n0) = (1 : ℤ) := by
    rw [←Nat.cast_one, Nat.cast_inj]
    unfold u256_from_limbs at h_nn_1
    simp only [Nat.cast_inj.mp h_n1] at h_nn_1
    rw [mul_zero, zero_add] at h_nn_1
    exact h_nn_1

  use 1 -- The branch ID

  -- The following return values are ignored in this branch
  use 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0

  -- The following return values are used in this branch.
  use 1, b0, 0, b0
  use 1, 1, 0, 1

  use range_check, rfl
  use 1, 0, b0, b1, 1, 0
  right
  use zero_ne_one.symm
  use 1, rfl, 0, rfl, b0, rfl, b1, rfl, 1, rfl, 0, rfl
  constructor
  · use 1 ; norm_num1 ; trivial
  constructor
  · use 0 ; norm_num1 ; trivial
  constructor
  · use Int.toNat b0, h_b0_lt, (Int.toNat_of_nonneg h_b0_nonneg).symm
  constructor
  · use Int.toNat b1, h_b1_lt, (Int.toNat_of_nonneg h_b1_nonneg).symm
  constructor
  · use 1 ; norm_num1 ; trivial
  constructor
  · use 0 ; norm_num1 ; trivial
  use 0
  left
  use rfl
  constructor
  · congr 1
  left
  rw [zero, one]
  use rfl, h_n1, h_n0
  use b0, (Int.toNat_of_nonneg h_b0_nonneg).symm
  use 0, 1, h_n0.symm, 0, b1, 0, 1
  left
  use rfl
  constructor
  · congr 1
    apply (mul_one _).symm
  constructor
  · congr 1
  use 1
  right
  use one_ne_zero, rfl
  use 1 + u128_bound_minus_u65_bound, rfl
  constructor
  · use 1 + (u128Limit - u65Limit)
    constructor
    · apply Nat.add_lt_of_lt_sub
      rw [Nat.sub_sub_self (by norm_num1)] ; norm_num1
    unfold u128_bound_minus_u65_bound ; norm_num1
  rw [add_zero]
  constructor
  · congr 1
    apply (Int.toNat_of_nonneg h_b1_nonneg)
  rw [add_zero]
  constructor
  · congr 1
  use rfl

-- # Axiliary lemmas

lemma mul_mod_right (a b n : ℕ) : a * b % n = a * (b % n) % n := by
  conv_lhs => rw [←(Nat.mod_add_div b n)]
  rw [Nat.left_distrib, ←mul_assoc, mul_comm a n, mul_assoc]
  rw [←Nat.add_mod_mod, Nat.mul_mod n _ n, Nat.mod_self, zero_mul, Nat.zero_mod, add_zero]

lemma overflow_0_or_n (m n : ℕ) (h_m : 0 < m) (h_n : 1 < n) :
  ((m - 1) % n + 1 - m % n) = 0  ∨ ((m - 1) % n + 1 - m % n) = n := by
  by_cases h : (m -1) % n + 1 % n < n
  · left
    apply Nat.sub_eq_of_eq_add ; rw [zero_add]
    conv in m % n => rw [←Nat.sub_add_cancel (Nat.one_le_of_lt h_m)]
    rw [Nat.add_mod_of_add_mod_lt h]
    rw [Nat.mod_eq_of_lt h_n]
  right
  apply Nat.sub_eq_of_eq_add
  rw [add_comm n _]
  conv in m % n => rw [←Nat.sub_add_cancel (Nat.one_le_of_lt h_m)]
  rw [Nat.add_mod_add_of_le_add_mod (le_of_not_lt h)]
  rw [Nat.mod_eq_of_lt h_n]

/-
  Same as above, but for natural numbers cast into integers. Basically the same
  proof, but with some extra cast handling.
-/
lemma int_overflow_0_or_n (m n : ℕ) (h_m : 0 < m) (h_n : 1 < n) :
  (((m : ℤ) - 1) % n + 1 - m % n) = 0  ∨ (((m : ℤ) - 1) % n + 1 - m % n) = n := by
  by_cases h : (m -1) % n + 1 % n < n
  · left
    rw [sub_eq_iff_eq_add, zero_add]
    rw [Int.ofNat_mod_ofNat]
    conv in m % n => rw [←Nat.sub_add_cancel (Nat.one_le_of_lt h_m)]
    rw [Nat.add_mod_of_add_mod_lt h]
    rw [Nat.mod_eq_of_lt h_n]
    rw [←Nat.cast_one, ←Nat.cast_sub (Nat.one_le_of_lt h_m)]
    norm_cast
  right
  rw [sub_eq_iff_eq_add]
  rw [add_comm (n :ℤ) _, Int.ofNat_mod_ofNat, ←Nat.cast_add]
  conv in m % n => rw [←Nat.sub_add_cancel (Nat.one_le_of_lt h_m)]
  rw [Nat.add_mod_add_of_le_add_mod (le_of_not_lt h)]
  rw [←Nat.cast_one, ←Nat.cast_sub (Nat.one_le_of_lt h_m)]
  rw [Nat.mod_eq_of_lt h_n]
  norm_cast

lemma zero_lt_mul_of_zero_lt { a b : ℕ } : 0 < a → 0 < b → 0 < a * b := by
  intros h_a h_b
  apply Nat.zero_lt_of_ne_zero
  apply Nat.mul_ne_zero
  apply Nat.not_eq_zero_of_lt h_a
  apply Nat.not_eq_zero_of_lt h_b

lemma mul_div_lt_u128Limit {a b : ℕ} (h_a: a < u128Limit) (h_b : b < u128Limit) :
  (a : ℤ) * b / u128Limit < u128Limit := by
  apply Int.ediv_lt_of_lt_mul
  norm_num1
  norm_cast
  apply Nat.mul_lt_mul_of_lt_of_le h_a (le_of_lt h_b)
  norm_num1

lemma Int.fromNat_mul_nonneg {a b : ℕ} : 0 ≤ (a : ℤ) * b := by norm_cast ; apply Nat.zero_le

lemma Int.zero_le_mul_mod_fromNat {a b m : ℕ} : 0 ≤ (a : ℤ) * b % m := by
  norm_cast ; apply Nat.zero_le

lemma Int.zero_le_mul_fromNat_div_u128_Limit {a b : ℕ} : 0 ≤ (a : ℤ) * b / u128Limit := by
  norm_cast ; apply zero_le

lemma zero_lt_sub_lt {a b : ℤ} (h_lt : b < a) : 0 < a - b := by
  apply Int.lt_sub_left_of_add_lt ; rwa [add_zero]

lemma one_le_sub_lt {a b : ℤ} (h_lt : b < a) : 1 ≤ a - b := by
  rw [←zero_add 1, Int.add_one_le_iff] ; apply zero_lt_sub_lt h_lt

lemma Int.zero_lt_add_of_lt {a b :ℤ} (h_lt_a: 0 < a) (h_lt_b : 0 < b) : 0 < a + b := by
  apply lt_of_le_of_lt _ (Int.add_lt_add h_lt_a h_lt_b)
  norm_num1

lemma Int.zero_lt_add_of_le_of_lt {a b :ℤ} (h_le_a: 0 ≤ a) (h_lt_b : 0 < b) : 0 < a + b := by
  apply lt_of_le_of_lt _ (Int.add_lt_add_of_le_of_lt h_le_a h_lt_b)
  norm_num1

lemma Int.zero_le_add_of_le {a b :ℤ} (h_le_a: 0 ≤ a) (h_le_b : 0 ≤ b) : 0 ≤ a + b := by
  apply le_trans _ (Int.add_le_add h_le_a h_le_b)
  norm_num1

lemma mod_u128Limit_lt_u128Limit {a : ℕ} : (a : ℤ) % u128Limit < u128Limit := by
  rw [Int.ofNat_mod_ofNat, Nat.cast_lt] ; apply Nat.mod_lt ; norm_num1

lemma Int.div_u128Limit_lt_mul_lt_u128Limit {a b : ℕ} (h_a : a < u128Limit) (h_b : b < u128Limit) :
  (a : ℤ) * b / u128Limit < u128Limit := by
  apply Int.ediv_lt_of_lt_mul (by norm_num1)
  apply Int.mul_lt_mul' (le_of_lt (Nat.cast_lt.mpr h_a)) (Nat.cast_lt.mpr h_b) (Int.natCast_nonneg b) (by norm_num1)

lemma Int.lt_three_sub_of_lt_u128Limit {a b c d : ℤ} (h_a : -3 < a) (h_b : b < u128Limit) (h_c : c < u128Limit) (h_d : d < u128Limit) :
  -3 * u128Limit < a - b - c - d := by
  rw [←Int.zero_add (-3 * u128Limit), Int.neg_mul, ←Int.sub_eq_add_neg]
  rw [show (3 : ℤ) * u128Limit = (u128Limit + u128Limit + u128Limit) by norm_num1]
  apply Int.sub_left_lt_of_lt_add
  suffices h_sum : 0 < a + (u128Limit - b) + (u128Limit - c) + (u128Limit - d) by
    apply lt_of_lt_of_le h_sum
    apply le_of_eq
    ring
  apply lt_of_lt_of_le _ (Int.add_le_add_left (one_le_sub_lt h_d) _)
  apply lt_of_lt_of_le _ (Int.add_le_add_right (Int.add_le_add_left (one_le_sub_lt h_c) _) _)
  apply lt_of_lt_of_le _ (Int.add_le_add_right (Int.add_le_add_right (Int.add_le_add_left (one_le_sub_lt h_b) _) _) _)
  simp only [add_assoc]
  apply lt_of_le_of_lt _ (Int.add_lt_add_right h_a _)
  norm_num1

lemma Int.add_lt_add_of_add_1 {a b c d : ℤ} (h₁ : -1 + a < b) (h₂ : c < d) : a + c < b + d := by
  apply Int.add_lt_add_of_le_of_lt _ h₂
  rwa [←Int.sub_one_lt_iff, Int.sub_eq_add_neg, add_comm]

lemma Int.three_add_lt_of_lt_u128Limit {a b c d : ℤ} (h_a : a < u128Limit) (h_b : b < 3) (h_c : c < u128Limit) (h_d : d < u128Limit) :
  a + b + c + d < 3 * u128Limit := by
  rw [show (3 : ℤ) * u128Limit = (u128Limit + u128Limit + u128Limit) by norm_num1]
  apply Int.add_lt_add_of_add_1 _ h_d
  simp only [←add_assoc]
  apply Int.add_lt_add_of_add_1 _ h_c
  simp only [←add_assoc]
  rw [←zero_add (u128Limit : ℤ)]
  simp only [add_assoc] ; rw [add_comm a b] ; simp only [←add_assoc]
  apply Int.add_lt_add_of_add_1 _ h_a
  simp only [←add_assoc]
  apply lt_of_lt_of_le (Int.add_lt_add_left h_b _)
  norm_num1

lemma Int.three_add_lt_of_zero_or_one_of_lt_u128Limit {a b c d : ℤ} (h_a : a < u128Limit) (h_b : b = 0 ∨ b = 1) (h_c : c < u128Limit) (h_d : d < u128Limit) :
  a + b + c + d < 3 * u128Limit := by
  have h_b_lt : b < 3 := by
    cases' h_b with h_z h_o
    · rw [h_z] ; norm_num1
    rw [h_o] ; norm_num1
  apply Int.three_add_lt_of_lt_u128Limit h_a h_b_lt h_c h_d

lemma is_range_checked_sub_i16_lower_bound {leftover : ℤ}
    (h_leftover_lt : leftover < 3)
    (h_leftover_gt: -3 < leftover) :
  VmIsRangeChecked u128Limit (leftover - i16_lower_bound) := by
  let a := leftover - i16_lower_bound
  have h_a_nonneg : 0 ≤ a := by
    apply le_trans _ (Int.add_le_add_right (show -3 ≤ leftover by apply le_of_lt h_leftover_gt) _)
    unfold i16_lower_bound
    norm_num1

  use a.toNat
  constructor
  · rw [Int.toNat_lt h_a_nonneg]
    apply Int.sub_right_lt_of_lt_add
    apply lt_trans h_leftover_lt
    unfold i16_lower_bound
    norm_num1
  apply (Int.toNat_of_nonneg h_a_nonneg).symm

lemma is_range_checked_add_u128_bound_minus_i16_upper_bound {leftover : ℤ}
    (h_leftover_lt : leftover < 3)
    (h_leftover_gt: -3 < leftover) :
  VmIsRangeChecked u128Limit (leftover + u128_bound_minus_i16_upper_bound) := by
  let a := leftover + u128_bound_minus_i16_upper_bound
  have h_a_nonneg : 0 ≤ a := by
    apply le_trans _ (Int.add_le_add_right (show -3 ≤ leftover by apply le_of_lt h_leftover_gt) _)
    unfold u128_bound_minus_i16_upper_bound
    norm_num1

  use a.toNat
  rw [←Int.ofNat_lt]
  rw [Int.toNat_of_nonneg h_a_nonneg]
  constructor
  · apply lt_trans (Int.add_lt_add_right h_leftover_lt _)
    unfold u128_bound_minus_i16_upper_bound
    norm_num1
  rfl

lemma spec_satisfiable_u256_guarantee_inv_mod_n_After
    (range_check : ℤ)
    (nb0 nb1 nn0 nn1 r : ℕ)
    (h_b0_lt : nb0 < u128Limit)
    (h_b1_lt : nb1 < u128Limit)
    (h_n0_lt : nn0 < u128Limit)
    (h_n1_lt : nn1 < u128Limit)
    (h_n_nonzero : (0 : ℤ) ≠ nn0 ∨ (0 : ℤ) ≠ nn1)
    (h_inv : (u256_from_limbs nb1 nb0) * r % (u256_from_limbs nn1 nn0) = 1)
    (h_nn_1 : u256_from_limbs nn1 nn0 ≠ 1)
    (h_r_lt_nn : r < u256_from_limbs nn1 nn0) :
    let r0 := r % u128Limit
    let r1 := r / u128Limit
    let k := (r * (u256_from_limbs nb1 nb0) - 1) / (u256_from_limbs nn1 nn0)
    let k0 := k % u128Limit
    let k1 := k / u128Limit
    auto_spec_u256_guarantee_inv_mod_n_After
      range_check nb0 nb1 nn0 nn1 (r % u128Limit) (r / u128Limit) k0 k1
      0 r0 r1
      r0 nb0 (r0 * nb0 / u128Limit) (r0 * nb0 % u128Limit)
      r0 nb1 (r0 * nb1 / u128Limit) (r0 * nb1 % u128Limit)
      r1 nb0 (r1 * nb0 / u128Limit) (r1 * nb0 % u128Limit)
      r1 nb1 (r1 * nb1 / u128Limit) (r1 * nb1 % u128Limit)
      nn0 k0 (nn0 * k0 / u128Limit) (nn0 * k0 % u128Limit)
      nn0 k1 (nn0 * k1 / u128Limit) (nn0 * k1 % u128Limit)
      nn1 k0 (nn1 * k0 / u128Limit) (nn1 * k0 % u128Limit)
      nn1 k1 (nn1 * k1 / u128Limit) (nn1 * k1 % u128Limit) := by

  let nb := u256_from_limbs nb1 nb0
  let nn := u256_from_limbs nn1 nn0

  have h_nb0_from_nb : nb0 = nb % u128Limit := by
    dsimp [nb] ; unfold u256_from_limbs
    rw [Nat.mul_add_mod]
    apply (Nat.mod_eq_of_lt h_b0_lt).symm
  have h_nn0_from_nn : nn0 = nn % u128Limit := by
    dsimp [nn] ; unfold u256_from_limbs
    rw [Nat.mul_add_mod]
    apply (Nat.mod_eq_of_lt h_n0_lt).symm

  have h_nb1_from_nb : nb1 = nb / u128Limit := by
    dsimp [nb] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_b0_lt, zero_add]
  have h_nn1_from_nn : nn1 = nn / u128Limit := by
    dsimp [nn] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_n0_lt, zero_add]

  have h_1_lt_nn : 1 < nn := by
    apply lt_of_le_of_ne _ h_nn_1.symm
    apply Nat.one_le_iff_ne_zero.mpr
    -- seems to be available only in newer versions of the library
    have add_eq_zero_iff {n m : ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
      constructor ; exact Nat.eq_zero_of_add_eq_zero ; intro ⟨h1, h2⟩ ; rw [h1, h2]
    unfold u256_from_limbs
    rw [Ne, add_eq_zero_iff, not_and_or]
    norm_cast at h_n_nonzero
    cases' h_n_nonzero with h_n h_n
    · right ; rw [eq_comm] ; apply h_n
    left ; rw [mul_eq_zero, not_or] ; constructor ; norm_num1 ; rw [eq_comm] ; apply h_n

  let r0 := r % u128Limit
  let r1 := r / u128Limit
  let k := (r * nb - 1) / nn
  let k0 := k % u128Limit
  let k1 := k / u128Limit

  have h_r_from_limbs : r = u256_from_limbs r1 r0 := by
    unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div
  have h_k_from_limbs : k = u256_from_limbs k1 k0 := by
    unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div

  have h_nb_pos : 0 < nb := by
    simp only [nb]
    apply Nat.zero_lt_of_ne_zero
    by_contra h_nb_zero
    rw [h_nb_zero, zero_mul, Nat.zero_mod] at h_inv
    apply zero_ne_one h_inv

  have h_r_pos : 0 < r := by
    apply Nat.zero_lt_of_ne_zero
    by_contra h
    rw [h] at h_inv
    rw [mul_zero, Nat.zero_mod] at h_inv
    apply zero_ne_one h_inv

  have h_r1_le_nn1 : r1 ≤ nn1 := by
    rw [h_nn1_from_nn] ; apply Nat.div_le_div_right ; apply le_of_lt ; apply h_r_lt_nn

  have h_k_lt : k < nb := by
    apply lt_of_le_of_lt (Nat.div_le_div_right (b := r * nb) (Nat.sub_le _ _))
    conv_rhs => rw [←(Nat.mul_div_cancel_left nb (lt_trans zero_lt_one h_1_lt_nn))]
    apply Nat.div_lt_div_of_lt_of_dvd
    apply Nat.dvd_mul_right
    apply Nat.mul_lt_mul_of_lt_of_le'
    apply h_r_lt_nn
    apply le_of_eq
    rfl
    exact h_nb_pos
  have h_k1_le_nb1 : k1 ≤ nb1 := by
    rw [h_nb1_from_nb] ; apply Nat.div_le_div_right ; apply le_of_lt ; apply h_k_lt

  have h_k0_lt_u128Limit : k0 < u128Limit := by
    apply Nat.mod_lt ; norm_num1
  have h_k1_lt_u128Limit : k1 < u128Limit := by
    apply lt_of_le_of_lt h_k1_le_nb1 h_b1_lt
  have h_r0_lt_u128Limit : r0 < u128Limit := by
    apply Nat.mod_lt ; norm_num1
  have h_r1_lt_u128Limit : r1 < u128Limit := by
    apply lt_of_le_of_lt h_r1_le_nn1 h_n1_lt

  have n_dvd_b_mul_r_min_1 : nn ∣ r * nb - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [mul_comm] ; rw [h_inv]
    apply (Nat.mod_eq_of_lt h_1_lt_nn).symm

  have h_nk_add_1_min_rb : (nn : ℤ) * k + 1 - r * nb = 0 := by
    simp only [k] ; rw [←Nat.cast_mul]
    rw [Nat.mul_div_eq_iff_dvd.mpr n_dvd_b_mul_r_min_1]
    rw [Nat.cast_sub (Nat.one_le_of_lt (zero_lt_mul_of_zero_lt h_r_pos h_nb_pos))]
    rw [Nat.cast_mul]
    ring

  have h_n_mul_k : (nn : ℤ) * k % u128Limit = (r * nb - 1) % u128Limit := by
    rw [←Nat.cast_mul nn k]
    rw [←Nat.mul_div_assoc nn n_dvd_b_mul_r_min_1]
    rw [Nat.mul_div_cancel_left _ (Nat.zero_lt_of_lt h_1_lt_nn)]
    rw [Nat.cast_sub, Nat.cast_mul, Nat.cast_one]
    apply Nat.le_of_pred_lt ; rw [Nat.pred_succ]
    apply zero_lt_mul_of_zero_lt h_r_pos h_nb_pos

  have h_n0k0_eq_nk_mod : (nn0 : ℤ) * k0 % u128Limit = nn * k % u128Limit := by
    norm_cast
    rw [Nat.mul_mod nn0 k0 _]
    rw [h_nn0_from_nn, Nat.mod_mod k _]
    rw [Nat.mod_mod, ←Nat.mul_mod]

  have h_r0b0_eq_rb_mod : (r0 : ℤ) * nb0 % u128Limit = r * nb % u128Limit := by
    norm_cast
    rw [Nat.mul_mod r0 nb0 _]
    rw [Nat.mod_mod r _, h_nb0_from_nb]
    rw [Nat.mod_mod, ←Nat.mul_mod]

  have h_leftover_zero_or_one :
      (((r : ℤ) * nb - 1) % u128Limit + 1 - r * nb % u128Limit) / u128Limit = 0 ∨
      (((r : ℤ) * nb - 1) % u128Limit + 1 - r * nb % u128Limit) / u128Limit = 1 := by
    simp only [←Nat.cast_mul]
    cases' int_overflow_0_or_n (r * nb) u128Limit (zero_lt_mul_of_zero_lt h_r_pos h_nb_pos) (by norm_num1) with h_z h_u128
    · left
      rw [h_z] ; simp only [EuclideanDomain.zero_div]
    right
    rw [h_u128] ; simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self]

  use r0 * nb0 % u128Limit, r0 * nb0 / u128Limit
  use r0 * nb1 % u128Limit, r0 * nb1 / u128Limit
  use r1 * nb0 % u128Limit, r1 * nb0 / u128Limit
  use r1 * nb1 % u128Limit, r1 * nb1 / u128Limit
  use nn0 * k0 % u128Limit, nn0 * k0 / u128Limit
  use nn0 * k1 % u128Limit, nn0 * k1 / u128Limit
  use nn1 * k0 % u128Limit, nn1 * k0 / u128Limit
  use nn1 * k1 % u128Limit, nn1 * k1 / u128Limit

  unfold one

  -- Limb 0
  use (nn0 : ℤ) * k0 % u128Limit + 1, rfl
  use (nn0 : ℤ) * k0 % u128Limit + 1 - r0 * nb0 % u128Limit, rfl
  use ((nn0 : ℤ) * k0 % u128Limit + 1 - r0 * nb0 % u128Limit) / u128_limit

  have h_pre_parts : (nn : ℤ) * k + 1 - r * nb =
    u128Limit * (u128Limit * ((nn1 * k1) - (r1 * nb1))) + u128Limit * (nn0 * k1 + nn1 * k0 - r0 * nb1 - r1 * nb0)
      + (nn0 * k0 + 1 - r0 * nb0) := by
    rw [h_r_from_limbs, h_k_from_limbs] ; simp only [nn, nb]
    unfold u256_from_limbs
    rw [←Nat.cast_one] ; simp only [Nat.cast_mul, Nat.cast_add]
    ring_nf

  let parts := (u128Limit : ℤ) * (u128Limit * (
        (nn1 * k1) - (r1 * nb1) + nn0 * k1 / u128Limit + nn1 * k0 / u128Limit - r0 * nb1 / u128Limit - r1 * nb0 / u128Limit))
    + u128Limit * ((nn0 * k1) % u128Limit + (nn1 * k0) % u128Limit - (r0 * nb1) % u128Limit - (r1 * nb0) % u128Limit + nn0 * k0 / u128Limit - r0 * nb0 / u128Limit)
      + ((nn0 * k0) % u128Limit + 1 - (r0 * nb0) % u128Limit)

  have h_parts_eq : (nn : ℤ) * k + 1 - r * nb = parts := by
    rw [h_pre_parts]
    simp only [←Nat.cast_mul]
    conv_lhs =>
      rw [←Nat.mod_add_div (nn0 * k0) u128Limit, ←Nat.mod_add_div (r0 * nb0) u128Limit]
      rw [←Nat.mod_add_div (nn0 * k1) u128Limit, ←Nat.mod_add_div (nn1 * k0) u128Limit]
      rw [←Nat.mod_add_div (r0 * nb1) u128Limit, ←Nat.mod_add_div (r1 * nb0) u128Limit]
    simp only [Nat.cast_add, Nat.cast_mul u128Limit, ←Int.ofNat_mod_ofNat, Int.ofNat_ediv, Nat.cast_mul]
    ring

  have h_parts_eq_zero : (0 : ℤ) = parts := by
    rw [←h_parts_eq] ; exact h_nk_add_1_min_rb.symm

  have h_last_part_eq : ((nn0 * k0) % u128Limit + 1 - (r0 * nb0) % u128Limit) =
    - ((u128Limit : ℤ) * (u128Limit * (
        (nn1 * k1) - (r1 * nb1) + nn0 * k1 / u128Limit + nn1 * k0 / u128Limit - r0 * nb1 / u128Limit - r1 * nb0 / u128Limit))
        + u128Limit * ((nn0 * k1) % u128Limit + (nn1 * k0) % u128Limit - (r0 * nb1) % u128Limit - (r1 * nb0) % u128Limit + nn0 * k0 / u128Limit - r0 * nb0 / u128Limit)) := by
    apply (Int.neg_eq_of_add_eq_zero _).symm
    rw [h_parts_eq_zero]

  constructor
  · congr 1
    apply (Int.ediv_mul_cancel _).symm
    rw [h_last_part_eq]
    rw [Int.dvd_neg]
    apply Int.dvd_add
    apply Int.dvd_mul_right
    apply Int.dvd_mul_right

  constructor
  · simp only [h_n0k0_eq_nk_mod, h_r0b0_eq_rb_mod, h_n_mul_k]
    rw [u128_limit_eq]
    cases' h_leftover_zero_or_one with h_z h_o
    · simp only [h_z]
      rw [zero_mul]
    simp only [h_o]
    rw [one_mul]
  -- Limb 1
  let leftover := ((nn0 : ℤ) * ↑k0 % ↑u128Limit + 1 - ↑r0 * ↑nb0 % ↑u128Limit) / ↑u128Limit
  let part0 := ↑nn0 * ↑k0 / ↑u128Limit + leftover
  let part1 := part0 + ↑nn0 * ↑k1 % ↑u128Limit
  let part2 := part1 + ↑nn1 * ↑k0 % ↑u128Limit
  let part3 := part2 - ↑r0 * ↑nb0 / ↑u128Limit
  let part4 := part3 - ↑r0 * ↑nb1 % ↑u128Limit
  let part5 := part4 - ↑r1 * ↑nb0 % ↑u128Limit
  let leftover₁ := part5 / ↑u128Limit
  let a := leftover₁ - i16_lower_bound

  use part0, rfl, part1, rfl, part2, rfl, part3, rfl, part4, rfl, part5, rfl, leftover₁

  have h_part5_from_parts : (u128Limit : ℤ) *
    ((nn1 * k1) - (r1 * nb1) + nn0 * k1 / u128Limit + nn1 * k0 / u128Limit - r0 * nb1 / u128Limit - r1 * nb0 / u128Limit)
    + part5 = parts / u128Limit := by
    simp only [parts, part5, part4, part3, part2, part1, part0, leftover]
    rw [add_assoc] ; rw [Int.add_ediv_of_dvd_left, Int.add_ediv_of_dvd_left]
    rw [Int.mul_ediv_cancel_left _ (by norm_num1), Int.mul_ediv_cancel_left _ (by norm_num1)]
    ring
    apply Int.dvd_mul_right
    apply Int.dvd_add ; apply Int.dvd_mul_right ; apply Int.dvd_mul_right

  have h_part5_eq : part5 = - ((u128Limit : ℤ) *
    ((nn1 * k1) - (r1 * nb1) + nn0 * k1 / u128Limit + nn1 * k0 / u128Limit - r0 * nb1 / u128Limit - r1 * nb0 / u128Limit)) := by
    rw [←h_parts_eq_zero, Int.zero_ediv] at h_part5_from_parts
    rw [←Int.neg_eq_of_add_eq_zero h_part5_from_parts]

  have h_leftover₁_eq : leftover₁ =
      -((nn1 * k1) - (r1 * nb1) + nn0 * k1 / u128Limit + nn1 * k0 / u128Limit - r0 * nb1 / u128Limit - r1 * nb0 / u128Limit) := by
    simp only [leftover₁] ; rw [h_part5_eq]
    rw [Int.neg_ediv_of_dvd (Int.dvd_mul_right _ _)]
    rw [Int.mul_ediv_cancel_left _ (by norm_num1)]

  have h_u128Limit_dvd_part5 : (u128Limit : ℤ) ∣ part5 := by
    rw [h_part5_eq, Int.dvd_neg]
    apply Int.dvd_mul_right

  have h_part5_gt : (-3 : ℤ) * u128Limit < part5 := by
    apply Int.lt_three_sub_of_lt_u128Limit _ (mul_div_lt_u128Limit h_r0_lt_u128Limit h_b0_lt)
      mod_u128Limit_lt_u128Limit mod_u128Limit_lt_u128Limit
    apply lt_of_lt_of_le (show -3 < 0 by norm_num1)
    apply Int.zero_le_add_of_le _ Int.zero_le_mul_mod_fromNat
    apply Int.zero_le_add_of_le _ Int.zero_le_mul_mod_fromNat
    apply Int.zero_le_add_of_le Int.zero_le_mul_fromNat_div_u128_Limit
    simp only [leftover]
    simp only [h_n0k0_eq_nk_mod, h_r0b0_eq_rb_mod, h_n_mul_k]
    cases' h_leftover_zero_or_one with h_z h_o
    · rw [h_z]
    rw [h_o] ; apply zero_le_one

  have h_leftover₁_gt : (-3 : ℤ) < leftover₁ := by
    apply Int.lt_of_mul_lt_mul_right _ (show 0 ≤ ↑u128Limit by norm_num1)
    rw [Int.ediv_mul_cancel h_u128Limit_dvd_part5]
    apply h_part5_gt

  have h_part5_lt :
    part5 < 3 * u128Limit := by
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_mod_fromNat)
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_mod_fromNat)
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_fromNat_div_u128_Limit)
    apply Int.three_add_lt_of_zero_or_one_of_lt_u128Limit _ _ mod_u128Limit_lt_u128Limit mod_u128Limit_lt_u128Limit
    apply Int.div_u128Limit_lt_mul_lt_u128Limit h_n0_lt h_k0_lt_u128Limit
    simp only [leftover]
    simp only [h_n0k0_eq_nk_mod, h_r0b0_eq_rb_mod, h_n_mul_k]
    apply h_leftover_zero_or_one

  have h_leftover₁_lt : leftover₁ < 3 := by
    apply Int.lt_of_mul_lt_mul_right _ (show 0 ≤ ↑u128Limit by norm_num1)
    rw [Int.ediv_mul_cancel h_u128Limit_dvd_part5]
    apply h_part5_lt

  constructor
  · congr 1 ; apply (Int.ediv_mul_cancel h_u128Limit_dvd_part5).symm

  use a, rfl

  -- range check on 'a'
  use (is_range_checked_sub_i16_lower_bound h_leftover₁_lt h_leftover₁_gt)
  -- range check on a₁
  use leftover₁ + u128_bound_minus_i16_upper_bound, rfl
  use (is_range_checked_add_u128_bound_minus_i16_upper_bound h_leftover₁_lt h_leftover₁_gt)

  -- limb2

  let part0₁ := ↑nn0 * ↑k1 / ↑u128Limit + leftover₁
  let part1₁ := part0₁ + ↑nn1 * ↑k0 / ↑u128Limit
  let part2₁ := part1₁ + ↑nn1 * ↑k1 % ↑u128Limit
  let part3₁ := part2₁ - ↑r1 * ↑nb0 / ↑u128Limit
  let part4₁ := part3₁ - ↑r0 * ↑nb1 / ↑u128Limit
  let part5₁ := part4₁ - ↑r1 * ↑nb1 % ↑u128Limit
  let leftover₂ := part5₁ / ↑u128Limit
  let a₂ := leftover₂ - i16_lower_bound

  use part0₁, rfl, part1₁, rfl, part2₁, rfl, part3₁, rfl, part4₁, rfl, part5₁, rfl, leftover₂

  have h_part5₁_eq : part5₁ = -((u128Limit : ℤ) * ((nn1 * k1) / u128Limit - (r1 * nb1) / u128Limit)) := by
    simp only [part5₁, part4₁, part3₁, part2₁, part1₁, part0₁]
    rw [←Int.emod_add_ediv ((nn1: ℤ) * k1) u128Limit, ←Int.emod_add_ediv ((r1 : ℤ) * nb1) u128Limit] at h_leftover₁_eq
    rw [h_leftover₁_eq]
    ring

  have h_leftover₂_eq : leftover₂ = -((nn1 * k1) / u128Limit - (r1 * nb1) / u128Limit) := by
    simp only [leftover₂]
    rw [h_part5₁_eq]
    rw [Int.neg_ediv_of_dvd (Int.dvd_mul_right _ _)]
    rw [Int.mul_ediv_cancel_left _ (by norm_num1)]

  have h_u128Limit_dvd_part5₁ : (u128Limit : ℤ) ∣ part5₁ := by
    rw [h_part5₁_eq, Int.dvd_neg]
    apply Int.dvd_mul_right

  have h_part5₁_gt : (-3 : ℤ) * u128Limit < part5₁ := by
    apply Int.lt_three_sub_of_lt_u128Limit _ (mul_div_lt_u128Limit h_r1_lt_u128Limit h_b0_lt)
      (mul_div_lt_u128Limit h_r0_lt_u128Limit h_b1_lt) mod_u128Limit_lt_u128Limit
    apply lt_of_lt_of_le _ (Int.add_le_add_left Int.zero_le_mul_mod_fromNat _) ; rw [add_zero]
    apply lt_of_lt_of_le _ (Int.add_le_add_left Int.zero_le_mul_fromNat_div_u128_Limit _) ; rw [add_zero]
    apply lt_of_lt_of_le _ (Int.add_le_add_right Int.zero_le_mul_fromNat_div_u128_Limit _) ; rw [zero_add]
    apply h_leftover₁_gt

  have h_leftover₂_gt : (-3 : ℤ) < leftover₂ := by
    apply Int.lt_of_mul_lt_mul_right _ (show 0 ≤ ↑u128Limit by norm_num1)
    rw [Int.ediv_mul_cancel h_u128Limit_dvd_part5₁]
    apply h_part5₁_gt

  have h_part5₁_lt :
    part5₁ < 3 * u128Limit := by
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_mod_fromNat)
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_fromNat_div_u128_Limit)
    apply lt_of_le_of_lt (Int.sub_le_self _ Int.zero_le_mul_fromNat_div_u128_Limit)
    apply Int.three_add_lt_of_lt_u128Limit (mul_div_lt_u128Limit h_n0_lt h_k1_lt_u128Limit)
      _ (mul_div_lt_u128Limit h_n1_lt h_k0_lt_u128Limit) mod_u128Limit_lt_u128Limit
    apply h_leftover₁_lt

  have h_leftover₂_lt : leftover₂ < 3 := by
    apply Int.lt_of_mul_lt_mul_right _ (show 0 ≤ ↑u128Limit by norm_num1)
    rw [Int.ediv_mul_cancel h_u128Limit_dvd_part5₁]
    apply h_part5₁_lt

  constructor
  · congr 1 ; apply (Int.ediv_mul_cancel h_u128Limit_dvd_part5₁).symm

  use a₂, rfl

  -- range check on 'a'
  use (is_range_checked_sub_i16_lower_bound h_leftover₂_lt h_leftover₂_gt)
  -- range check on a₁
  use leftover₂ + u128_bound_minus_i16_upper_bound, rfl
  use (is_range_checked_add_u128_bound_minus_i16_upper_bound h_leftover₂_lt h_leftover₂_gt)

  -- limb 3
  constructor
  · rw [h_leftover₂_eq]; simp

  use rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl

-- # Main proof of co-prime (1 < n) case

theorem spec_satisfiable_u256_guarantee_inv_mod_n_coprime
    (range_check : ℤ)
    (nb0 nb1 nn0 nn1 : Nat)
    (h_b0_lt : nb0 < u128Limit)
    (h_b1_lt : nb1 < u128Limit)
    (h_n0_lt : nn0 < u128Limit)
    (h_n1_lt : nn1 < u128Limit)
    (h_n_nonzero : (0 : ℤ) ≠ nn0 ∨ (0 : ℤ) ≠ nn1)
    (h_1_lt_nn : 1 < (u256_from_limbs nn1 nn0))
    (h_nn_1 : u256_from_limbs nn1 nn0 ≠ 1)
    (h_cp : Nat.Coprime (u256_from_limbs nb1 nb0) (u256_from_limbs nn1 nn0)) :
  ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
    auto_spec_u256_guarantee_inv_mod_n range_check nb0 nb1 nn0 nn1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low := by

  let nb := u256_from_limbs nb1 nb0
  let nn := u256_from_limbs nn1 nn0

  have h_nb1_from_nb : nb1 = nb / u128Limit := by
    dsimp [nb] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_b0_lt, zero_add]
  have h_nn1_from_nn : nn1 = nn / u128Limit := by
    dsimp [nn] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_n0_lt, zero_add]

  rcases Nat.exists_mul_emod_eq_one_of_coprime h_cp h_1_lt_nn with ⟨r', h_inv⟩
  rw [mul_mod_right] at h_inv

  let r := r' % nn
  let r0 := r % u128Limit
  let r1 := r / u128Limit
  let k := (r * nb - 1) / nn
  let k0 := k % u128Limit
  let k1 := k / u128Limit

  have h_r_from_limbs : r = u256_from_limbs r1 r0 := by
    unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div

  have h_nb_pos : 0 < nb := by
    apply Nat.zero_lt_of_ne_zero
    by_contra h_nb_zero
    simp only [nb] at h_nb_zero
    rw [h_nb_zero, zero_mul, Nat.zero_mod] at h_inv
    apply zero_ne_one h_inv

  have h_r_lt_nn : r < nn := by apply Nat.mod_lt ; apply lt_trans _ h_1_lt_nn ; norm_num1
  have h_r1_le_nn1 : r1 ≤ nn1 := by
    rw [h_nn1_from_nn] ; apply Nat.div_le_div_right ; apply le_of_lt ; apply h_r_lt_nn

  have h_k_lt : k < nb := by
    apply lt_of_le_of_lt (Nat.div_le_div_right (b := r * nb) (Nat.sub_le _ _))
    conv_rhs => rw [←(Nat.mul_div_cancel_left nb (lt_trans zero_lt_one h_1_lt_nn))]
    apply Nat.div_lt_div_of_lt_of_dvd
    apply Nat.dvd_mul_right
    apply Nat.mul_lt_mul_of_lt_of_le'
    apply Nat.mod_lt ; apply lt_trans zero_lt_one h_1_lt_nn
    apply le_of_eq
    rfl
    exact h_nb_pos
  have h_k1_le_nb1 : k1 ≤ nb1 := by
    rw [h_nb1_from_nb] ; apply Nat.div_le_div_right ; apply le_of_lt ; apply h_k_lt

  have h_k0_lt_u128Limit : k0 < u128Limit := by
    apply Nat.mod_lt ; norm_num1
  have h_k1_lt_u128Limit : k1 < u128Limit := by
    apply lt_of_le_of_lt h_k1_le_nb1 h_b1_lt
  have h_r0_lt_u128Limit : r0 < u128Limit := by
    apply Nat.mod_lt ; norm_num1
  have h_r1_lt_u128Limit : r1 < u128Limit := by
    apply lt_of_le_of_lt h_r1_le_nn1 h_n1_lt

  use 0
  use r0, r1
  use r0, nb0, r0 * nb0 / u128Limit, r0 * nb0 % u128Limit
  use r0, nb1, r0 * nb1 / u128Limit, r0 * nb1 % u128Limit
  use r1, nb0, r1 * nb0 / u128Limit, r1 * nb0 % u128Limit
  use r1, nb1, r1 * nb1 / u128Limit, r1 * nb1 % u128Limit
  use nn0, k0, nn0 * k0 / u128Limit, nn0 * k0 % u128Limit
  use nn0, k1, nn0 * k1 / u128Limit, nn0 * k1 % u128Limit
  use nn1, k0, nn1 * k0 / u128Limit, nn1 * k0 % u128Limit
  use nn1, k1, nn1 * k1 / u128Limit, nn1 * k1 % u128Limit

  use range_check, rfl
  use 0, 0, r0, r1, k0, k1
  left

  use rfl, r0, rfl, r1, rfl, k0, rfl, k1, rfl
  constructor
  · use r0
  constructor
  · use r1
  constructor
  · use k0
  constructor
  · use k1
  use (nn1 : ℤ) - r1, rfl
  use (nn0 : ℤ) - r0, (nn0 : ℤ) - ↑r0 - 1
  by_cases h_diff1 : (nn1 : ℤ) - ↑r1 = 0
  · left
    have h_r1_eq_nn1 : r1 = nn1 := by
      rw [Int.sub_eq_zero, Int.natCast_inj] at h_diff1
      exact h_diff1.symm
    have h_r0_lt_nn0 : r0 < nn0 := by
      apply Nat.lt_of_add_lt_add_left (n := u128Limit * nn1)
      apply lt_of_le_of_lt _ h_r_lt_nn
      apply le_of_eq ; rw [←h_r1_eq_nn1] ; apply h_r_from_limbs.symm
    unfold one
    use h_diff1, rfl, rfl
    constructor
    · use nn0 - r0 - 1
      constructor
      · apply lt_of_le_of_lt (Nat.sub_le _ _)
        apply lt_of_le_of_lt (Nat.sub_le _ _) h_n0_lt
      rw [Nat.cast_sub _, Nat.cast_sub _, Nat.cast_one]
      apply le_of_lt h_r0_lt_nn0
      apply Nat.succ_le_iff.mpr
      apply Nat.sub_pos_of_lt h_r0_lt_nn0

    apply spec_satisfiable_u256_guarantee_inv_mod_n_After range_check nb0 nb1 nn0 nn1 r
      h_b0_lt h_b1_lt h_n0_lt h_n1_lt h_n_nonzero h_inv h_nn_1 h_r_lt_nn

  right
  use h_diff1
  constructor
  · use nn1 - r1
    constructor
    · apply lt_of_le_of_lt (Nat.sub_le nn1 r1)
      apply h_n1_lt
    apply (Nat.cast_sub h_r1_le_nn1).symm
  apply spec_satisfiable_u256_guarantee_inv_mod_n_After range_check nb0 nb1 nn0 nn1 r
      h_b0_lt h_b1_lt h_n0_lt h_n1_lt h_n_nonzero h_inv h_nn_1 h_r_lt_nn

-- # Main proof of non-coprime (with 1 < n) case

lemma high_limb_from_u256_from_limbs (n0 n1 : ℕ) (h_n0_lt : n0 < u128Limit) :
    n1 = (u256_from_limbs n1 n0) / u128Limit := by
  unfold u256_from_limbs
  rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right u128Limit n1)]
  rw [Nat.mul_div_right, Nat.div_eq_of_lt h_n0_lt, add_zero]
  norm_num1

lemma u256_from_limb_low (n0 n1 : ℕ) (h_n0_lt : n0 < u128Limit) :
    (u256_from_limbs n1 n0) % u128Limit = n0 := by
  unfold u256_from_limbs
  rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h_n0_lt]

lemma u256_from_limbs_mul_low {k0 k1 m0 m1 n0 n1 : ℕ}
    (h_n0_lt : n0 < u128Limit)
    (h_mul : u256_from_limbs k1 k0 * u256_from_limbs m1 m0 = u256_from_limbs n1 n0) :
  k0 * m0 % u128Limit = n0 := by

  rw [←u256_from_limb_low n0 n1 h_n0_lt]
  unfold u256_from_limbs
  unfold u256_from_limbs at h_mul
  have h_parts : (u128Limit * k1 + k0) * (u128Limit * m1 + m0) =
    u128Limit * (u128Limit * (k1 * m1) + k1 * m0 + k0 * m1) + k0 * m0 := by ring
  rw [h_parts] at h_mul
  rw [←h_mul, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]

lemma u256_from_limbs_mul_high_of_high_eq_zero {k0 k1 m0 m1 n0 n1 : ℕ}
    (h_m1_zero : m1 = 0)
    (h_n0_lt : n0 < u128Limit)
    (h_mul : u256_from_limbs k1 k0 * u256_from_limbs m1 m0 = u256_from_limbs n1 n0) :
  n1 = k1 * m0 + m0 * k0 / u128Limit := by

  rw [high_limb_from_u256_from_limbs n0 n1 h_n0_lt]
  rw [←h_mul]
  unfold u256_from_limbs
  rw [h_m1_zero, mul_zero, zero_add, Nat.right_distrib, mul_assoc]

  rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right u128Limit _)]
  rw [mul_comm k0 m0, Nat.mul_div_right]
  norm_num1

lemma u256_from_limbs_lt_of_lt {n1 n0 : ℕ} (h_n0_lt : n0 < u128Limit) (h_n1_lt : n1 < u128Limit):
    u256_from_limbs n1 n0 < u128Limit * u128Limit := by
  unfold u256_from_limbs
  apply lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt h_n1_lt)) h_n0_lt)
  apply le_of_eq
  ring

lemma u256_limb_zero_of_mul_lt {m0 m1 n0 n1 : ℕ} :
  u256_from_limbs m1 m0 * u256_from_limbs n1 n0 < u128Limit * u128Limit → m1 = 0 ∨ n1 = 0 := by
  unfold u256_from_limbs
  intro h
  rw [←Nat.zero_eq_mul]
  have h_parts : (u128Limit * m1 + m0) * (u128Limit * n1 + n0) =
    u128Limit * u128Limit * (m1 * n1) + (u128Limit * (m1 * n0 + m0 * n1) + m0 * n0) := by ring
  rw [h_parts] at h
  have h_u128_sq_lt := lt_of_le_of_lt (Nat.le_add_right (u128Limit * u128Limit * (m1 * n1)) _) h
  by_contra h_ne_zero
  rw [←Ne] at h_ne_zero
  apply Nat.not_le.mpr h_u128_sq_lt
  apply Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_ne_zero h_ne_zero.symm)

lemma u256_limb_mul_lt_of_mul_lt {m0 m1 n0 n1 : ℕ} :
  u256_from_limbs m1 m0 * u256_from_limbs n1 n0 < u128Limit * u128Limit →
    m1 * n0 < u128Limit ∧ m0 * n1 < u128Limit := by
  unfold u256_from_limbs
  intro h
  have h_parts : (u128Limit * m1 + m0) * (u128Limit * n1 + n0) =
    u128Limit * (m1 * n0 + m0 * n1) + (u128Limit * u128Limit * (m1 * n1) + m0 * n0) := by ring
  rw [h_parts] at h
  have h_u128_sq_lt := lt_of_le_of_lt (Nat.le_add_right (u128Limit * (m1 * n0 + m0 * n1)) _) h
  rw [Nat.mul_lt_mul_left (by norm_num1)] at h_u128_sq_lt
  constructor
  · apply lt_of_le_of_lt (Nat.le_add_right _ _) h_u128_sq_lt
  apply lt_of_le_of_lt (Nat.le_add_left _ _) h_u128_sq_lt

lemma lt_u64_of_mul_lt_u128 {m n : ℕ} (h_lt : m * n < u128Limit) : m < u64Limit ∨ n < u64Limit := by
  rw [(show u128Limit = u64Limit * u64Limit by norm_num1)] at h_lt
  by_contra h
  apply Nat.not_le.mpr h_lt
  rw [not_or, Nat.not_lt, Nat.not_lt] at h
  exact Nat.mul_le_mul h.1 h.2

lemma lt_u64_of_mul_lt_u128_of_left_not_lt_u64 {m n : ℕ} (h_lt : m * n < u128Limit) : ¬ m < u64Limit → n < u64Limit := by
  intro h_left
  apply (or_iff_right h_left).mp (lt_u64_of_mul_lt_u128 h_lt)

lemma lt_u64_of_mul_lt_u128_of_right_not_lt_u64 {m n : ℕ} (h_lt : m * n < u128Limit) : ¬ n < u64Limit → m < u64Limit := by
  intro h_right
  apply (or_iff_left h_right).mp (lt_u64_of_mul_lt_u128 h_lt)

lemma one_lt_g_of_not_coprime {b n : ℕ} (h_not_coprime : Nat.gcd b n ≠ 1) :
    let g := if (Nat.gcd b n) % 2 = 0 then 2 else Nat.gcd b n
    1 < g := by
  let g := if (Nat.gcd b n) % 2 = 0 then 2 else Nat.gcd b n
  by_cases h_even : (Nat.gcd b n) % 2 = 0
  · simp only [g, eq_true h_even, ite_true]
    norm_num1
  simp only [g, eq_false h_even, ite_false]
  apply lt_of_le_of_ne _ h_not_coprime.symm
  apply Nat.one_le_of_lt (Nat.zero_lt_of_ne_zero _)
  by_contra h
  apply h_even
  rw [h, Nat.zero_mod]

lemma g_dvd_gcd {b n : ℕ}:
    let g := if (Nat.gcd b n) % 2 = 0 then 2 else Nat.gcd b n
    g ∣ Nat.gcd b n := by
  let g := if (Nat.gcd b n) % 2 = 0 then 2 else Nat.gcd b n
  by_cases h_even : (Nat.gcd b n) % 2 = 0
  · simp only [g, eq_true h_even, ite_true]
    apply Nat.dvd_of_mod_eq_zero h_even
  simp only [g, eq_false h_even, ite_false]
  apply Nat.dvd_refl

lemma spec_satisfiable_u256_guarantee_inv_mod_n_GIsValid
    (range_check : ℤ)
    (nb0 nb1 nn0 nn1 : ℕ)
    (h_b0_lt : nb0 < u128Limit)
    (h_b1_lt : nb1 < u128Limit)
    (h_n0_lt : nn0 < u128Limit)
    (h_n1_lt : nn1 < u128Limit) :
    let nb := u256_from_limbs nb1 nb0
    let nn := u256_from_limbs nn1 nn0
    let g := if (Nat.gcd nb nn) % 2 = 0 then 2 else Nat.gcd nb nn
    let g0 := g % u128Limit
    let g1 := g / u128Limit
    let s := nb / g
    let t := nn / g
    let s0 := s % u128Limit
    let s1 := s / u128Limit
    let t0 := t % u128Limit
    let t1 := t / u128Limit
    auto_spec_u256_guarantee_inv_mod_n_GIsValid
      range_check nb0 nb1 nn0 nn1 g0 g1 s0 s1 t0 t1
      1 0 0
      0 0 0 0
      0 0 0 0
      0 0 0 0
      0 0 0 0
      0 0 0 0
      0 0 0 0
      -- Only the following return values are used in this branch.
      g0 s0 (g0 * s0 / u128Limit) (g0 * s0 % u128Limit)
      g0 t0 (g0 * t0 / u128Limit) (g0 * t0 % u128Limit) := by

    let nb := u256_from_limbs nb1 nb0
    let nn := u256_from_limbs nn1 nn0
    let g := if (Nat.gcd nb nn) % 2 = 0 then 2 else Nat.gcd nb nn
    let g0 := g % u128Limit
    let g1 := g / u128Limit
    let s := nb / g
    let t := nn / g
    let s0 := s % u128Limit
    let s1 := s / u128Limit
    let t0 := t % u128Limit
    let t1 := t / u128Limit

    have h_g_dvd_gcd : g ∣ Nat.gcd nb nn := by
      apply g_dvd_gcd
    have h_g_dvd_nb : g ∣ nb := by
      apply Nat.dvd_trans h_g_dvd_gcd (Nat.gcd_dvd_left _ _)
    have h_g_dvd_nn : g ∣ nn := by
      apply Nat.dvd_trans h_g_dvd_gcd (Nat.gcd_dvd_right _ _)
    have h_s_mul_g : s * g = nb := by
      simp only [s] ; apply Nat.div_mul_cancel h_g_dvd_nb
    have h_t_mul_g : t * g = nn := by
      simp only [t] ; apply Nat.div_mul_cancel h_g_dvd_nn

    have h_g_from_limbs : g = u256_from_limbs g1 g0 := by
      unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div
    have h_s_from_limbs : s = u256_from_limbs s1 s0 := by
      unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div
    have h_t_from_limbs : t = u256_from_limbs t1 t0 := by
      unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div

    have h_nn_lt : nn < u128Limit * u128Limit := by
      simp only [nn]
      apply u256_from_limbs_lt_of_lt h_n0_lt h_n1_lt

    have h_nb_lt : nb < u128Limit * u128Limit := by
      simp only [nb]
      apply u256_from_limbs_lt_of_lt h_b0_lt h_b1_lt

    have h_s1_zero_or_g1_zero : s1 = 0 ∨ g1 = 0 := by
      rw [←h_s_mul_g, h_g_from_limbs, h_s_from_limbs] at h_nb_lt
      apply u256_limb_zero_of_mul_lt h_nb_lt

    have h_t1_zero_or_g1_zero : t1 = 0 ∨ g1 = 0 := by
      rw [←h_t_mul_g, h_g_from_limbs, h_t_from_limbs] at h_nn_lt
      apply u256_limb_zero_of_mul_lt h_nn_lt

    have h_s1_g0_s0_g1_lt : s1 * g0 < u128Limit ∧ s0 * g1 < u128Limit := by
      rw [←h_s_mul_g, h_g_from_limbs, h_s_from_limbs] at h_nb_lt
      apply u256_limb_mul_lt_of_mul_lt h_nb_lt

    have h_t1_g0_t0_g1_lt : t1 * g0 < u128Limit ∧ t0 * g1 < u128Limit := by
      rw [←h_t_mul_g, h_g_from_limbs, h_t_from_limbs] at h_nn_lt
      apply u256_limb_mul_lt_of_mul_lt h_nn_lt

    use (g0 * s0) % u128Limit
    constructor
    · norm_cast
      rw [mul_comm]
      rw [h_s_from_limbs, h_g_from_limbs] at h_s_mul_g
      apply u256_from_limbs_mul_low h_b0_lt h_s_mul_g
    use (g0 * s0) / u128Limit
    use (g0 * t0) % u128Limit
    constructor
    · norm_cast
      rw [mul_comm]
      rw [h_t_from_limbs, h_g_from_limbs] at h_t_mul_g
      apply u256_from_limbs_mul_low h_n0_lt h_t_mul_g
    use (g0 * t0) / u128Limit

    by_cases h_g1_eq_zero : (g1 : ℤ) = 0
    · use s1 * g0, t1 * g0
      by_cases h_g0_is_small : g0 < 18446744073709551616
      · use g0
        left
        use h_g1_eq_zero, rfl, rfl
        use 1
        right
        use zero_ne_one.symm
        use rfl
        -- MERGE
        use g0 + u128_bound_minus_u65_bound, rfl
        constructor
        · use g0 + 340282366920938463426481119284349108224
          constructor
          · apply lt_trans (Nat.add_lt_add_right h_g0_is_small _)
            norm_num1
          unfold u128_bound_minus_u65_bound ; rw [Nat.cast_add] ; rfl
        constructor
        · norm_cast
          simp only [nb, h_s_from_limbs, h_g_from_limbs] at h_s_mul_g
          congr 1
          apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_g1_eq_zero) h_b0_lt h_s_mul_g
        constructor
        · norm_cast
          simp only [nn, h_t_from_limbs, h_g_from_limbs] at h_t_mul_g
          congr 1
          apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_g1_eq_zero) h_n0_lt h_t_mul_g
        use rfl

      have h_s1_lt_u64 : s1 < u64Limit := lt_u64_of_mul_lt_u128_of_right_not_lt_u64 h_s1_g0_s0_g1_lt.1 h_g0_is_small
      have h_t1_lt_u64 : t1 < u64Limit := lt_u64_of_mul_lt_u128_of_right_not_lt_u64 h_t1_g0_t0_g1_lt.1 h_g0_is_small

      use s1 + t1
      left
      use h_g1_eq_zero, rfl, rfl
      use 0
      left
      use rfl, rfl
      -- MERGE
      use s1 + t1 + u128_bound_minus_u65_bound, rfl
      constructor
      · use s1 + t1 + 340282366920938463426481119284349108224
        constructor
        · apply lt_of_lt_of_le (Nat.add_lt_add_right (Nat.add_lt_add h_s1_lt_u64 h_t1_lt_u64) _)
          norm_num1
        unfold u128_bound_minus_u65_bound ; rw [Nat.cast_add] ; rfl
      constructor
      · norm_cast
        simp only [nb, h_s_from_limbs, h_g_from_limbs] at h_s_mul_g
        congr 1
        apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_g1_eq_zero) h_b0_lt h_s_mul_g
      constructor
      · norm_cast
        simp only [nn, h_t_from_limbs, h_g_from_limbs] at h_t_mul_g
        congr 1
        apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_g1_eq_zero) h_n0_lt h_t_mul_g
      use rfl

    have h_s1_zero : s1 = 0 := by
      rw [Nat.cast_eq_zero] at h_g1_eq_zero
      apply (or_iff_left h_g1_eq_zero).mp h_s1_zero_or_g1_zero
    have h_t1_zero : t1 = 0 := by
      rw [Nat.cast_eq_zero] at h_g1_eq_zero
      apply (or_iff_left h_g1_eq_zero).mp h_t1_zero_or_g1_zero
    use s0 * g1, t0 * g1
    by_cases h_g1_is_small : g1 < 18446744073709551616
    · use g1
      right
      use h_g1_eq_zero, rfl, rfl
      rw [zero]
      constructor
      · rw [Nat.cast_eq_zero] ; apply h_s1_zero
      constructor
      · rw [Nat.cast_eq_zero] ; apply h_t1_zero
      use 1
      right
      use one_ne_zero
      use rfl
      -- MERGE
      use g1 + u128_bound_minus_u65_bound, rfl
      constructor
      · use g1 + 340282366920938463426481119284349108224
        constructor
        · apply lt_trans (Nat.add_lt_add_right h_g1_is_small _)
          norm_num1
        unfold u128_bound_minus_u65_bound ; rw [Nat.cast_add] ; rfl
      constructor
      · norm_cast
        simp only [nb, h_s_from_limbs, h_g_from_limbs, mul_comm] at h_s_mul_g
        rw [mul_comm s0 g1, mul_comm g0 s0]
        congr 1
        apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_s1_zero) h_b0_lt h_s_mul_g
      constructor
      · norm_cast
        simp only [nn, h_t_from_limbs, h_g_from_limbs, mul_comm] at h_t_mul_g
        rw [mul_comm t0 g1, mul_comm g0 t0]
        congr 1
        apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_t1_zero) h_n0_lt h_t_mul_g
      use rfl

    have h_s0_lt_u64 : s0 < u64Limit := lt_u64_of_mul_lt_u128_of_right_not_lt_u64 h_s1_g0_s0_g1_lt.2 h_g1_is_small
    have h_t0_lt_u64 : t0 < u64Limit := lt_u64_of_mul_lt_u128_of_right_not_lt_u64 h_t1_g0_t0_g1_lt.2 h_g1_is_small

    use s0 + t0
    right
    -- S1_AND_T1_EQ_ZERO
    use h_g1_eq_zero, rfl, rfl
    rw [zero]
    rw [Nat.cast_eq_zero] at h_g1_eq_zero
    constructor
    · rw [Nat.cast_eq_zero]
      apply (or_iff_left h_g1_eq_zero).mp h_s1_zero_or_g1_zero
    constructor
    · rw [Nat.cast_eq_zero]
      apply (or_iff_left h_g1_eq_zero).mp h_t1_zero_or_g1_zero
    use 0
    left
    use rfl, rfl
    -- MERGE
    use s0 + t0 + u128_bound_minus_u65_bound, rfl
    constructor
    · use s0 + t0 + 340282366920938463426481119284349108224
      constructor
      · apply lt_of_lt_of_le (Nat.add_lt_add_right (Nat.add_lt_add h_s0_lt_u64 h_t0_lt_u64) _)
        norm_num1
      unfold u128_bound_minus_u65_bound ; rw [Nat.cast_add] ; rfl
    constructor
    · norm_cast
      simp only [nb, h_s_from_limbs, h_g_from_limbs, mul_comm] at h_s_mul_g
      rw [mul_comm s0 g1, mul_comm g0 s0]
      congr 1
      apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_s1_zero) h_b0_lt h_s_mul_g
    constructor
    · norm_cast
      simp only [nn, h_t_from_limbs, h_g_from_limbs, mul_comm] at h_t_mul_g
      rw [mul_comm t0 g1, mul_comm g0 t0]
      congr 1
      apply u256_from_limbs_mul_high_of_high_eq_zero (Nat.cast_eq_zero.mp h_t1_zero) h_n0_lt h_t_mul_g
    use rfl

theorem spec_satisfiable_u256_guarantee_inv_mod_n_non_coprime
    (range_check : ℤ)
    (nb0 nb1 nn0 nn1 : Nat)
    (h_b0_lt : nb0 < u128Limit)
    (h_b1_lt : nb1 < u128Limit)
    (h_n0_lt : nn0 < u128Limit)
    (h_n1_lt : nn1 < u128Limit)
    (h_n_nonzero : (0 : ℤ) ≠ nn0 ∨ (0 : ℤ) ≠ nn1)
    (h_1_lt_nn : 1 < (u256_from_limbs nn1 nn0))
    (h_nn_1 : u256_from_limbs nn1 nn0 ≠ 1)
    (h_cp : ¬Nat.Coprime (u256_from_limbs nb1 nb0) (u256_from_limbs nn1 nn0)) :
  ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
    auto_spec_u256_guarantee_inv_mod_n range_check nb0 nb1 nn0 nn1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low := by

  let nb := u256_from_limbs nb1 nb0
  let nn := u256_from_limbs nn1 nn0

  have h_zero_lt_nn : 0 < nn := lt_trans Nat.zero_lt_one h_1_lt_nn

  have h_nb1_from_nb : nb1 = nb / u128Limit := by
    dsimp [nb] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_b0_lt, zero_add]
  have h_nn1_from_nn : nn1 = nn / u128Limit := by
    dsimp [nn] ; unfold u256_from_limbs
    rw [add_comm] ; rw [Nat.add_mul_div_left _ _ (by norm_num1)]
    rw [(Nat.div_eq_zero_iff (b := u128Limit) (by norm_num1)).mpr h_n0_lt, zero_add]

  let g := if (Nat.gcd nb nn) % 2 = 0 then 2 else Nat.gcd nb nn

  rw [Nat.Coprime, ←Ne] at h_cp

  have h_1_lt_g : 1 < g := by
    apply one_lt_g_of_not_coprime h_cp

  have h_g_dvd_gcd : g ∣ Nat.gcd nb nn := by
    apply g_dvd_gcd
  have h_g_dvd_nb : g ∣ nb := by
    apply Nat.dvd_trans h_g_dvd_gcd (Nat.gcd_dvd_left _ _)
  have h_g_dvd_nn : g ∣ nn := by
    apply Nat.dvd_trans h_g_dvd_gcd (Nat.gcd_dvd_right _ _)

  let g0 := g % u128Limit
  let g1 := g / u128Limit
  let s := nb / g
  let t := nn / g
  let s0 := s % u128Limit
  let s1 := s / u128Limit
  let t0 := t % u128Limit
  let t1 := t / u128Limit

  have h_g_from_limbs : g = u256_from_limbs g1 g0 := by
    unfold u256_from_limbs ; rw [eq_comm, add_comm] ; apply Nat.mod_add_div

  have h_s_dvd_nb : s ∣ nb := Nat.div_dvd_of_dvd h_g_dvd_nb
  have h_t_dvd_nn : t ∣ nn := Nat.div_dvd_of_dvd h_g_dvd_nn

  have h_g0_ne_zero : (g0 : ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    by_cases h_even : (Nat.gcd nb nn) % 2 = 0
    · simp only [g0, g, eq_true h_even, ite_true]
      norm_num1
    simp only [g0, g, eq_false h_even, ite_false]
    by_contra h
    apply h_even
    rw [←Nat.zero_mod 2]
    apply Nat.ModEq.of_dvd (show 2 ∣ u128Limit by norm_num1)
    rw [←Nat.zero_mod u128Limit] at h
    apply h

  have h_g1_le_nn1 : g1 ≤ nn1 := by
    rw [h_nn1_from_nn] ; apply Nat.div_le_div_right
    apply Nat.le_of_dvd h_zero_lt_nn h_g_dvd_nn

  have h_s1_le_nb1 : s1 ≤ nb1 := by
    by_cases h : nb = 0
    · simp only [s1, s]
      rw [h, Nat.zero_div, Nat.zero_div]
      apply Nat.zero_le
    rw [h_nb1_from_nb] ; apply Nat.div_le_div_right
    apply Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h) h_s_dvd_nb

  have h_t1_le_nn1 : t1 ≤ nn1 := by
    rw [h_nn1_from_nn] ; apply Nat.div_le_div_right
    apply Nat.le_of_dvd h_zero_lt_nn h_t_dvd_nn

  have h_g1_lt_u128Limit: g1 < u128Limit := by
    apply lt_of_le_of_lt h_g1_le_nn1 h_n1_lt
  have h_s1_lt_u128Limit: s1 < u128Limit := by
    apply lt_of_le_of_lt h_s1_le_nb1 h_b1_lt
  have h_t1_lt_u128Limit: t1 < u128Limit := by
    apply lt_of_le_of_lt h_t1_le_nn1 h_n1_lt

  use 1 -- The branch ID

  -- The following return values are ignored in this branch
  use 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0
  use 0, 0, 0, 0

  -- The following return values are used in this branch.
  use g0, s0, (g0 * s0 / u128Limit), (g0 * s0 % u128Limit)
  use g0, t0, (g0 * t0 / u128Limit), (g0 * t0 % u128Limit)

  use range_check, rfl
  use g0, g1, s0, s1, t0, t1

  right
  use h_g0_ne_zero, g0, rfl, g1, rfl, s0, rfl, s1, rfl, t0, rfl, t1, rfl

  constructor
  · use g0, Nat.mod_lt g (by norm_num1)
  constructor
  · use g1
  constructor
  · use s0, Nat.mod_lt s (by norm_num1)
  constructor
  · use s1
  constructor
  · use t0, Nat.mod_lt t (by norm_num1)
  constructor
  · use t1

  rw [one]
  use g0 - 1
  by_cases h_g1_zero : (g1 : ℤ) = 0
  · left
    use h_g1_zero, rfl
    right
    constructor
    · by_contra h_g0_1
      rw [Int.sub_eq_zero, Nat.cast_eq_one] at h_g0_1
      rw [h_g_from_limbs, h_g0_1, (Nat.cast_eq_zero.mp h_g1_zero)] at h_1_lt_g
      unfold u256_from_limbs at h_1_lt_g
      rw [Nat.mul_zero, Nat.zero_add] at h_1_lt_g
      apply lt_irrefl _ h_1_lt_g
    apply spec_satisfiable_u256_guarantee_inv_mod_n_GIsValid range_check nb0 nb1 nn0 nn1
      h_b0_lt h_b1_lt h_n0_lt h_n1_lt
  right
  use h_g1_zero
  apply spec_satisfiable_u256_guarantee_inv_mod_n_GIsValid range_check nb0 nb1 nn0 nn1
    h_b0_lt h_b1_lt h_n0_lt h_n1_lt

-- # Main proof

theorem spec_satisfiable_u256_guarantee_inv_mod_n
    (range_check b0 b1 n0 n1 : ℤ)
    -- Add assumptions on the arguments here.
    (h_b0_nonneg : 0 ≤ b0)
    (h_b1_nonneg : 0 ≤ b1)
    (h_n0_nonneg : 0 ≤ n0)
    (h_n1_nonneg : 0 ≤ n1)
    (h_b0_lt : b0 < u128Limit)
    (h_b1_lt : b1 < u128Limit)
    (h_n0_lt : n0 < u128Limit)
    (h_n1_lt : n1 < u128Limit)
    (h_n_nonzero : 0 ≠ n0 ∨ 0 ≠ n1) :
  ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
    auto_spec_u256_guarantee_inv_mod_n range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low := by

  by_cases h_nn_1 : u256_from_limbs (Int.toNat n1) (Int.toNat n0) = 1
  · apply spec_satisfiable_u256_guarantee_inv_mod_1
      range_check b0 b1 n0 n1
      h_b0_nonneg h_b1_nonneg h_n0_nonneg h_n1_nonneg
      h_b0_lt h_b1_lt h_n0_lt h_n1_lt
      h_n_nonzero h_nn_1

  let nb0 := Int.toNat b0
  let nb1 := Int.toNat b1
  let nn0 := Int.toNat n0
  let nn1 := Int.toNat n1

  -- replace the integers by the equivalent natural numbers.
  rw [←(Int.toNat_of_nonneg h_b0_nonneg), ←(Int.toNat_of_nonneg h_b1_nonneg)]
  rw [←(Int.toNat_of_nonneg h_n0_nonneg), ←(Int.toNat_of_nonneg h_n1_nonneg)]
  rw [←(Int.toNat_lt h_b0_nonneg)] at h_b0_lt
  rw [←(Int.toNat_lt h_b1_nonneg)] at h_b1_lt
  rw [←(Int.toNat_lt h_n0_nonneg)] at h_n0_lt
  rw [←(Int.toNat_lt h_n1_nonneg)] at h_n1_lt
  rw [←(Int.toNat_of_nonneg h_n0_nonneg), ←(Int.toNat_of_nonneg h_n1_nonneg)] at h_n_nonzero

  let nb := u256_from_limbs nb1 nb0
  let nn := u256_from_limbs nn1 nn0

  rw [←Ne] at h_nn_1

  have h_1_lt_nn : 1 < nn := by
    apply lt_of_le_of_ne _ h_nn_1.symm
    apply Nat.one_le_iff_ne_zero.mpr
    -- seems to be available only in newer versions of the library
    have add_eq_zero_iff {n m : ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
      constructor ; exact Nat.eq_zero_of_add_eq_zero ; intro ⟨h1, h2⟩ ; rw [h1, h2]
    unfold u256_from_limbs
    rw [Ne, add_eq_zero_iff, not_and_or]
    norm_cast at h_n_nonzero
    cases' h_n_nonzero with h_n h_n
    · right ; rw [eq_comm] ; apply h_n
    left ; rw [mul_eq_zero, not_or] ; constructor ; norm_num1 ; rw [eq_comm] ; apply h_n

  by_cases h_cp : Nat.Coprime nb nn
  · apply spec_satisfiable_u256_guarantee_inv_mod_n_coprime range_check
      nb0 nb1 nn0 nn1
      h_b0_lt h_b1_lt h_n0_lt h_n1_lt
      h_n_nonzero h_1_lt_nn h_nn_1 h_cp

  apply spec_satisfiable_u256_guarantee_inv_mod_n_non_coprime range_check
    nb0 nb1 nn0 nn1
    h_b0_lt h_b1_lt h_n0_lt h_n1_lt
    h_n_nonzero h_1_lt_nn h_nn_1 h_cp
