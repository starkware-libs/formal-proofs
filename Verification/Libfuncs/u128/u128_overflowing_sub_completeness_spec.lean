import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_overflowing_sub_completeness

def u128_limit : ℤ := (340282366920938463463374607431768211456 : ℤ) -- BigInt::from(u128::MAX) + BigInt::from(1)


def auto_spec_u128_overflowing_sub_NoOverflow (range_check a_minus_b ρ_branch_id ρ_a_minus_b : ℤ) : Prop :=
  VmIsRangeChecked u128Limit a_minus_b ∧
  ρ_branch_id = 0 ∧
  ρ_a_minus_b = a_minus_b

def auto_spec_u128_overflowing_sub (range_check a b ρ_branch_id ρ_a_minus_b : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ a_ge_b : ℤ,
  ∃ a_minus_b : ℤ, a_minus_b % PRIME = (a - b) % PRIME ∧
  (
    (a_ge_b = 0 ∧
      ∃ wrapping_a_minus_b : ℤ, wrapping_a_minus_b % PRIME = (a_minus_b + u128_limit) % PRIME ∧
      VmIsRangeChecked u128Limit wrapping_a_minus_b ∧
      ρ_branch_id = 1 ∧
      ρ_a_minus_b = wrapping_a_minus_b
    ) ∨
    (a_ge_b ≠ 0 ∧
      auto_spec_u128_overflowing_sub_NoOverflow
        range_check a_minus_b ρ_branch_id ρ_a_minus_b
    )
  )

theorem spec_satisfiable_u128_overflowing_sub
    (range_check a b : ℤ)
    -- Add assumptions on the arguments here.
    (h_a_nonneg: 0 ≤ a)
    (h_b_nonneg: 0 ≤ b)
    (h_a_lt: a < u128Limit)
    (h_b_lt: b < u128Limit) :
  ∃ (ρ_branch_id ρ_a_minus_b : ℤ),
    auto_spec_u128_overflowing_sub range_check a b ρ_branch_id ρ_a_minus_b := by
  let na := Int.toNat a
  let nb := Int.toNat b
  by_cases hab : na < nb
  · use 1, a - b + u128_limit
    use range_check, rfl, 0, a - b, rfl
    left
    use rfl
    refine ⟨_, rfl, ?_, rfl, rfl⟩
    rw [sub_add_eq_add_sub]
    use na + u128Limit - nb
    have : nb ≤ na + u128Limit := by
      trans; swap; apply Nat.le_add_left
      rw [Int.toNat_le]
      apply le_of_lt h_b_lt
    constructor
    . apply Nat.sub_lt_right_of_lt_add this
      rw [add_comm]
      apply add_lt_add_left hab
    rw [Nat.cast_sub this, Nat.cast_add]
    rw [Int.toNat_of_nonneg h_a_nonneg, Int.toNat_of_nonneg h_b_nonneg]; rfl
  use 0, a - b
  use range_check, rfl, 1, a - b, rfl
  right
  constructor; norm_num
  refine ⟨?_, rfl, rfl⟩
  use na - nb
  constructor
  . apply lt_of_le_of_lt tsub_le_self
    rw [Int.toNat_lt h_a_nonneg]
    exact h_a_lt
  rw [Nat.cast_sub (le_of_not_lt hab)]
  rw [Int.toNat_of_nonneg h_a_nonneg, Int.toNat_of_nonneg h_b_nonneg]
