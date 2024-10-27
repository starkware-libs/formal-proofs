import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace bounded_int_div_rem_known_small_quotient_completeness

def one : ℤ := (1 : ℤ) -- 1
def u128_bound_minus_q_upper : ℤ := (340282366920938463463374607431768211440 : ℤ) -- (BigInt::one().shl(128) - q_upper_bound) as BigInt

namespace bounded_int_div_rem_known_small_quotient_generalized

-- This section generalizes the bound and proves that the specifications can be satisfied for
-- any value of the bound which is non-negative (and under the additional assumption for the
-- small lhs case).

variable (u128_bound_minus_q_upper : ℤ)

def auto_spec_bounded_int_div_rem_known_small_quotient (range_check a b ρ_q ρ_r : ℤ) : Prop :=
  ∃ orig_range_check : ℤ, orig_range_check = range_check ∧
  ∃ r_plus_1 : ℤ,
  ∃ b_minus_r_minus_1 : ℤ,
  ∃ bq : ℤ,
  ∃ q : ℤ,
  ∃ r : ℤ,
  VmIsRangeChecked u128Limit q ∧
  VmIsRangeChecked u128Limit r ∧
  r_plus_1 % PRIME = (r + one) % PRIME ∧
  b_minus_r_minus_1 % PRIME = (b - r_plus_1) % PRIME ∧
  VmIsRangeChecked u128Limit b_minus_r_minus_1 ∧
  ∃ b_or_q_bound_rc_value : ℤ,
  b_or_q_bound_rc_value % PRIME = (q + u128_bound_minus_q_upper) % PRIME ∧
  VmIsRangeChecked u128Limit b_or_q_bound_rc_value ∧
  bq % PRIME = (b * q) % PRIME ∧
  a % PRIME = (bq + r) % PRIME ∧
  ρ_q = q ∧
  ρ_r = r


theorem spec_satisfiable_bounded_int_div_rem_known_small_quotient
    (range_check a b : ℤ)
    (lhs rhs : IntRange)
    (q_upper_bound : ℕ)
    -- (h_u128_bound_minus_q_upper_nonneg : 0 ≤ u128_bound_minus_q_upper)
    (h_q_upper_bound_eq : u128_bound_minus_q_upper = u128Limit - q_upper_bound)
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some (RemDivAlg.KnownSmallQuotient q_upper_bound))
    (h_a_inRange : InRange a lhs)
    (h_b_inRange : InRange b rhs) :

  ∃ (ρ_q ρ_r : ℤ),
    auto_spec_bounded_int_div_rem_known_small_quotient u128_bound_minus_q_upper range_check a b ρ_q ρ_r := by

  rcases DivRemAlg_KnownSmallQuotient_bounds h_lhs_nonneg h_rhs_pos h_alg h_a_inRange h_b_inRange with
    ⟨h_a_nonneg, h_b_pos, h_b_le, h_q_lt, h_q_upper_bound_le_u128, h_q_upper_bound_lt⟩

  let na := Int.toNat a
  let nb := Int.toNat b
  have h_b_nonneg := le_of_lt h_b_pos

  have h_u128_bound_minus_q_upper_nonneg : 0 ≤ u128_bound_minus_q_upper := by
    rw [h_q_upper_bound_eq]
    apply Int.sub_nonneg_of_le
    apply h_q_upper_bound_le_u128

  rw [Nat.cast_le] at h_q_upper_bound_le_u128

  rw [←(Int.toNat_of_nonneg h_b_nonneg), Nat.cast_le] at h_b_le
  rw [←Nat.cast_zero, ←Int.lt_toNat] at h_b_pos
  rw [←(Int.toNat_of_nonneg h_a_nonneg), ←(Int.toNat_of_nonneg h_b_nonneg), ←Int.natCast_div, Nat.cast_lt] at h_q_lt
  rw [←Nat.cast_mul, Nat.cast_lt] at h_q_upper_bound_lt

  let q := na / nb
  let r := na % nb

  use q, r, range_check, rfl, r + 1, b - (r + 1), b * q, q, r

  rw [←(Int.toNat_of_nonneg h_a_nonneg), ←(Int.toNat_of_nonneg h_b_nonneg)]

  have h_q_upper_bound_lt_u128 : q_upper_bound < u128Limit := by
    apply Nat.lt_of_mul_lt_mul_right (a := u128Limit)
    apply lt_trans h_q_upper_bound_lt
    rw [PRIME] ; norm_num1

  constructor
  · use q
    constructor
    · apply lt_trans h_q_lt h_q_upper_bound_lt_u128
    rfl

  constructor
  · use r
    constructor
    · apply lt_of_lt_of_le (Nat.mod_lt na h_b_pos)
      assumption
    rfl

  rw [one]
  use rfl, rfl

  constructor
  · use nb - (r + 1)
    constructor
    · apply lt_of_lt_of_le (Nat.sub_lt h_b_pos _) h_b_le
      apply Nat.zero_lt_succ
    rw [←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_sub _]
    rw [←Nat.succ_eq_add_one, Nat.succ_le_iff]
    apply Nat.mod_lt na h_b_pos

  use q + u128_bound_minus_q_upper, rfl

  constructor
  · use q + u128_bound_minus_q_upper.toNat
    constructor
    · rw [Int.sub_nonneg_toNat h_q_upper_bound_eq h_q_upper_bound_le_u128]
      apply lt_of_lt_of_le (Nat.add_lt_add_right h_q_lt _)
      rw [Nat.add_sub_cancel' (le_of_lt h_q_upper_bound_lt_u128)]
    rw [←(Int.toNat_of_nonneg h_u128_bound_minus_q_upper_nonneg)]
    rfl

  use rfl
  constructor
  · congr 1
    norm_cast
    exact (Nat.div_add_mod _ _).symm

  use rfl

end bounded_int_div_rem_known_small_quotient_generalized

-- The specs and proof in this section (which are used in the automatic completeness proof)
-- are the specs and theorem of the generalized section, applied to the specific bound value
-- for which the code was compiled.

def auto_spec_bounded_int_div_rem_known_small_quotient (range_check a b ρ_q ρ_r : ℤ) : Prop :=
  bounded_int_div_rem_known_small_quotient_generalized.auto_spec_bounded_int_div_rem_known_small_quotient
    u128_bound_minus_q_upper range_check a b ρ_q ρ_r

theorem spec_satisfiable_bounded_int_div_rem_known_small_quotient
    (range_check a b : ℤ)
    (lhs rhs : IntRange)
    (q_upper_bound : ℕ)
    (h_q_upper_bound_eq : u128_bound_minus_q_upper = u128Limit - q_upper_bound)
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some (RemDivAlg.KnownSmallQuotient q_upper_bound))
    (h_a_inRange : InRange a lhs)
    (h_b_inRange : InRange b rhs) :

  ∃ (ρ_q ρ_r : ℤ),
    auto_spec_bounded_int_div_rem_known_small_quotient range_check a b ρ_q ρ_r := by
  apply bounded_int_div_rem_known_small_quotient_generalized.spec_satisfiable_bounded_int_div_rem_known_small_quotient
    u128_bound_minus_q_upper
    range_check a b
    lhs rhs
    q_upper_bound
    h_q_upper_bound_eq
    h_lhs_nonneg
    h_rhs_pos
    h_alg
    h_a_inRange
    h_b_inRange
