import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_overflowing_add_completeness

def u128_limit : ℤ := (340282366920938463463374607431768211456 : ℤ) -- (BigInt::from(u128::MAX) + 1) as BigInt


def auto_spec_u128_overflowing_add_NoOverflow (range_check a_plus_b ρ_branch_id ρ_a_plus_b : ℤ) : Prop :=
  VmIsRangeChecked u128Limit a_plus_b ∧
  ρ_branch_id = 0 ∧
  ρ_a_plus_b = a_plus_b

def auto_spec_u128_overflowing_add (range_check a b ρ_branch_id ρ_a_plus_b : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ no_overflow : ℤ,
  ∃ a_plus_b : ℤ, a_plus_b % PRIME = (a + b) % PRIME ∧
  (
    (no_overflow = 0 ∧
      ∃ wrapping_a_plus_b : ℤ, wrapping_a_plus_b % PRIME = (a_plus_b - u128_limit) % PRIME ∧
      VmIsRangeChecked u128Limit wrapping_a_plus_b ∧
      ρ_branch_id = 1 ∧
      ρ_a_plus_b = wrapping_a_plus_b
    ) ∨
    (no_overflow ≠ 0 ∧
      auto_spec_u128_overflowing_add_NoOverflow
        range_check a_plus_b ρ_branch_id ρ_a_plus_b
    )
  )


theorem spec_satisfiable_u128_overflowing_add
    (range_check a b : ℤ)
    -- Add assumptions on the arguments here.
    (h_a_nonneg: 0 ≤ a)
    (h_b_nonneg: 0 ≤ b)
    (h_a_lt: a < u128Limit)
    (h_b_lt: b < u128Limit) :
  ∃ (ρ_branch_id ρ_a_plus_b : ℤ),
    auto_spec_u128_overflowing_add range_check a b ρ_branch_id ρ_a_plus_b := by
  let na := Int.toNat a
  let nb := Int.toNat b
  rw [←(Int.toNat_of_nonneg h_a_nonneg), ←(Int.toNat_of_nonneg h_b_nonneg)]
  rw [←(Int.toNat_lt h_a_nonneg)] at h_a_lt
  rw [←(Int.toNat_lt h_b_nonneg)] at h_b_lt
  by_cases hab : na + nb < u128Limit
  · use 0, na + nb
    use range_check, rfl, 1, na + nb, rfl
    right
    use one_ne_zero
    constructor
    · use na + nb, hab
      apply Nat.cast_add
    use rfl
  use 1, na + nb - u128Limit
  use range_check, rfl, 0, na + nb, rfl
  left
  use rfl, na + nb - u128Limit
  constructor
  · norm_cast
  constructor
  · use na + nb - u128Limit
    constructor
    · apply lt_of_add_lt_add_right
      rw [tsub_add_cancel_of_le (le_of_not_gt hab)]
      apply add_lt_add h_a_lt h_b_lt
    rw [Nat.cast_sub, Nat.cast_add]
    apply le_of_not_gt hab
  use rfl
  done
