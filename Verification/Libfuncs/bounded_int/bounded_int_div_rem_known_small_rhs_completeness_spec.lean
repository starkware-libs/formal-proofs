import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace bounded_int_div_rem_known_small_rhs_completeness

def one : ℤ := (1 : ℤ) -- 1


def auto_spec_bounded_int_div_rem_known_small_rhs (range_check a b ρ_q ρ_r : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ r_plus_1 : ℤ,
  ∃ b_minus_r_minus_1 : ℤ,
  ∃ bq : ℤ,
  ∃ q : ℤ,
  ∃ r : ℤ, VmIsRangeChecked u128Limit r ∧
  r_plus_1 % PRIME = (r + one) % PRIME ∧
  b_minus_r_minus_1 % PRIME = (b - r_plus_1) % PRIME ∧
  VmIsRangeChecked u128Limit b_minus_r_minus_1 ∧
  VmIsRangeChecked u128Limit q ∧
  bq % PRIME = (b * q) % PRIME ∧
  a % PRIME = (bq + r) % PRIME ∧
  ρ_q = q ∧
  ρ_r = r


theorem spec_satisfiable_bounded_int_div_rem_known_small_rhs
    (range_check a b : ℤ)
    (lhs rhs : IntRange)
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some RemDivAlg.KnownSmallRhs)
    (h_a_inRange : InRange a lhs)
    (h_b_inRange : InRange b rhs) :
  ∃ (ρ_q ρ_r : ℤ),
    auto_spec_bounded_int_div_rem_known_small_rhs range_check a b ρ_q ρ_r := by

  rcases DivRemAlg_KnownSmallRhs_bounds h_lhs_nonneg h_rhs_pos h_alg h_a_inRange h_b_inRange with
    ⟨h_a_nonneg, h_b_pos, h_q_lt, h_b_lt⟩

  let na := Int.toNat a
  let nb := Int.toNat b
  have h_b_nonneg := le_of_lt h_b_pos

  rw [←(Int.toNat_of_nonneg h_b_nonneg), ←Nat.cast_mul, Nat.cast_lt] at h_b_lt
  rw [←Nat.cast_zero, ←Int.lt_toNat] at h_b_pos
  rw [←(Int.toNat_of_nonneg h_a_nonneg), ←(Int.toNat_of_nonneg h_b_nonneg), ←Int.natCast_div, Nat.cast_lt] at h_q_lt

  let q := na / nb
  let r := na % nb

  use q, r, range_check, rfl, r + 1, b - (r + 1), b * q, q, r

  rw [←(Int.toNat_of_nonneg h_a_nonneg), ←(Int.toNat_of_nonneg h_b_nonneg)]

  have h_nb_lt_u128 : nb < u128Limit := by
    apply Nat.lt_of_mul_lt_mul_right (a := u128Limit)
    apply lt_trans h_b_lt
    rw [PRIME] ; norm_num1

  constructor
  · use r
    constructor
    · apply lt_trans (Nat.mod_lt na h_b_pos)
      assumption
    rfl
  rw [one]

  use rfl, rfl

  constructor
  · use nb - (r + 1)
    constructor
    · apply lt_of_le_of_lt (Nat.sub_le _ _)
      assumption
    rw [←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_sub _]
    rw [←Nat.succ_eq_add_one, Nat.succ_le_iff]
    apply Nat.mod_lt na h_b_pos

  constructor
  · use na / nb

  use rfl

  constructor
  · congr 1
    norm_cast
    exact (Nat.div_add_mod _ _).symm

  use rfl
