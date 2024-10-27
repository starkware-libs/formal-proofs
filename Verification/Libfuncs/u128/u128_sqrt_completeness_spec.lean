import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Mathlib.Tactic.NormNum.NatSqrt

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_sqrt_completeness

def u125_upper_fixer : ℤ := (297747071055821155530452781502797185024 : ℤ) -- BigInt::from(u128::MAX - (u128::pow(2, 125) - 1))


def auto_spec_u128_sqrt (range_check value ρ_root : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ fixed_root : ℤ,
  ∃ root_squared : ℤ,
  ∃ value_minus_root_squared : ℤ,
  ∃ root_times_two : ℤ,
  ∃ diff : ℤ,
  ∃ root : ℤ,
  fixed_root % PRIME = (root + u125_upper_fixer) % PRIME ∧
  VmIsRangeChecked u128Limit root ∧
  VmIsRangeChecked u128Limit fixed_root ∧
  root_squared % PRIME = (root * root) % PRIME ∧
  value_minus_root_squared % PRIME = (value - root_squared) % PRIME ∧
  VmIsRangeChecked u128Limit value_minus_root_squared ∧
  root_times_two % PRIME = (root + root) % PRIME ∧
  diff % PRIME = (root_times_two - value_minus_root_squared) % PRIME ∧
  VmIsRangeChecked u128Limit diff ∧
  ρ_root = root


theorem spec_satisfiable_u128_sqrt
    (range_check value : ℤ)
    -- Add assumptions on the arguments here.
    (h_value_nonneg: 0 ≤ value)
    (h_value_lt: value < u128Limit) :
  ∃ (ρ_root : ℤ),
    auto_spec_u128_sqrt range_check value ρ_root := by
  let root := value.toNat.sqrt
  use root
  use range_check, rfl
  use root + u125_upper_fixer
  use root * root
  use value - root * root
  use root + root
  use (root + root) - (value - root * root)
  use root
  use rfl
  have root_le : root ≤ Nat.sqrt (2^128) := by
    apply Nat.sqrt_le_sqrt
    apply le_of_lt
    norm_num
    rw [←Int.toNat_lt_toNat] at h_value_lt
    exact h_value_lt
    norm_num [u128Limit]
  have : VmIsRangeChecked u128Limit ↑root := by
    refine ⟨root, ?_, rfl⟩
    apply lt_of_le_of_lt root_le
    norm_num
  use this
  have : VmIsRangeChecked u128Limit (↑root + u125_upper_fixer) := by
    use root + (2^128 - 2^125)
    constructor
    . apply lt_of_le_of_lt
      apply add_le_add_right root_le
      norm_num [u128Limit]
    . rw [Nat.cast_add]
      norm_num; rfl
  use this, rfl, rfl
  have : VmIsRangeChecked u128Limit (value - ↑root * ↑root) := by
    use value.toNat - root * root
    constructor
    . apply lt_of_le_of_lt (Nat.sub_le _ _)
      rw [←Int.toNat_lt_toNat] at h_value_lt
      exact h_value_lt
      norm_num [u128Limit]
    . rw [Nat.cast_sub, Nat.cast_mul, Int.toNat_of_nonneg h_value_nonneg]
      apply Nat.sqrt_le _
  use this, rfl, rfl
  have : VmIsRangeChecked u128Limit (↑root + ↑root - (value - ↑root * ↑root)) := by
    use root + root - (value.toNat - root * root)
    constructor
    . apply lt_of_le_of_lt (Nat.sub_le _ _)
      apply lt_of_le_of_lt (add_le_add root_le root_le)
      norm_num [u128Limit]
    . rw [Nat.cast_sub, Nat.cast_add, Nat.cast_sub, Nat.cast_mul, Int.toNat_of_nonneg h_value_nonneg]
      apply Nat.sqrt_le _
      rw [Nat.sub_le_iff_le_add, add_comm, ←add_assoc]
      apply Nat.sqrt_le_add
  use this
