import Verification.Semantics.Completeness.VmHoare
import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_safe_divmod_known_small_lhs_completeness

def one : ℤ := (1 : ℤ) -- 1
def limiter_bound : ℤ := (18446744073709551616 : ℤ) -- lhs_upper_sqrt.clone()
def u128_bound_minus_limiter_bound : ℤ := (340282366920938463444927863358058659840 : ℤ) -- (BigInt::one().shl(128) - lhs_upper_sqrt) as BigInt

def u64_bound : ℤ := limiter_bound
def u128_bound_minus_u64_bound : ℤ := u128_bound_minus_limiter_bound

def auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : ℤ) : Prop :=
  VmIsRangeChecked u128Limit b_or_q_bound_rc_value ∧
  bq % PRIME = (b * q) % PRIME ∧
  a % PRIME = (bq + r) % PRIME ∧
  ρ_q = q ∧
  ρ_r = r

def auto_spec_u128_safe_divmod_known_small_lhs_QIsSmall (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : ℤ) : Prop :=
  b_or_q_bound_rc_value % PRIME = (q + u128_bound_minus_limiter_bound) % PRIME ∧
  auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ
    range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r

def auto_spec_u128_safe_divmod_known_small_lhs (range_check a b ρ_q ρ_r : ℤ) : Prop :=
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
  ∃ q_is_small : ℤ,
  (
    (q_is_small = 0 ∧
      ∃ b_or_q_bound_rc_value : ℤ,
      b_or_q_bound_rc_value % PRIME = (b + u128_bound_minus_limiter_bound) % PRIME ∧
      auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    ) ∨
    (q_is_small ≠ 0 ∧
      ∃ b_or_q_bound_rc_value : ℤ,
      auto_spec_u128_safe_divmod_known_small_lhs_QIsSmall
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    )
  )


/-theorem spec_satisfiable_u128_safe_divmod_known_small_lhs
    (range_check a b : ℤ)
    -- Add assumptions on the arguments here.
    :
  ∃ (ρ_q ρ_r : ℤ),
    auto_spec_u128_safe_divmod_known_small_lhs range_check a b ρ_q ρ_r := by
  sorry-/

-- note: this is the better definition of VmIsRangeChecked
theorem VmIsRangeChecked_aux {a : ℤ} (h : 0 ≤ a) (h' : a < u128Limit) :
    VmIsRangeChecked u128Limit a := by
  refine ⟨a.toNat, ?_, ?_⟩
  . rw [Int.toNat_lt h]
    exact h'
  rw [Int.toNat_of_nonneg h]

theorem spec_satisfiable_u128_safe_divmod_known_small_lhs
    (range_check a b : ℤ)
    -- Add assumptions on the arguments here.
    (h_a_nonneg: 0 ≤ a)
    (h_b_ge_1: 1 ≤ b)
    (h_a_lt: a < u128Limit)
    (h_b_lt: b < u128Limit) :
  ∃ (ρ_q ρ_r : ℤ),
    auto_spec_u128_safe_divmod_known_small_lhs range_check a b ρ_q ρ_r := by
  use a / b, a % b
  use range_check, rfl
  use a % b + 1
  use b - (a % b + 1)
  have bne0 : b ≠ 0 := by
    apply ne_of_gt
    apply lt_of_lt_of_le (by norm_num) h_b_ge_1
  have b_nonneg : 0 ≤ b := le_trans (by norm_num) h_b_ge_1
  have b_pos : 0 < b := lt_of_lt_of_le (by norm_num) h_b_ge_1
  have amodb_nonneg : 0 ≤ a % b := Int.emod_nonneg _ bne0
  have adivb_nonneg : 0 ≤ a / b := by
    apply Int.ediv_nonneg h_a_nonneg
    apply le_trans (by norm_num) h_b_ge_1
  have amodb_lt : a % b < b := Int.emod_lt_of_pos _ b_pos
  have rc_q : VmIsRangeChecked u128Limit (a / b) := by
    apply VmIsRangeChecked_aux adivb_nonneg
    apply lt_of_le_of_lt _ h_a_lt
    apply Int.ediv_le_self _ h_a_nonneg
  have rc_r : VmIsRangeChecked u128Limit (a % b) := by
    apply VmIsRangeChecked_aux amodb_nonneg
    apply lt_trans amodb_lt h_b_lt
  have rc_diff : VmIsRangeChecked u128Limit (b - (a % b + 1)) := by
    apply VmIsRangeChecked_aux
    apply sub_nonneg_of_le
    apply Int.add_one_le_of_lt amodb_lt
    linarith
  by_cases hqsmall : a / b < u64_bound
  . use b * (a / b), a / b, a % b, rc_q, rc_r
    constructor ; congr 1
    constructor; congr 1
    use rc_diff
    use 1
    right
    constructor; norm_num
    use a / b + (2^128 - 2^64)
    constructor; congr 1; norm_num [u128_bound_minus_u64_bound]
    constructor
    . show VmIsRangeChecked u128Limit (a / b + (2 ^ 128 - 2 ^ 64))
      apply VmIsRangeChecked_aux
      . apply add_nonneg adivb_nonneg (by norm_num)
      apply lt_of_lt_of_le
      apply add_lt_add_right hqsmall
      norm_num [u64_bound, u128Limit, limiter_bound]
    refine ⟨rfl, ?_, rfl, rfl⟩
    rw [add_comm, Int.emod_add_ediv]
  . use b * (a / b), a / b, a % b, rc_q, rc_r, rfl
    constructor; congr 1
    use rc_diff
    use 0
    left
    use rfl
    use b + (2^128 - 2^64)
    constructor; congr 1; norm_num [u128_bound_minus_u64_bound]
    constructor
    . show VmIsRangeChecked u128Limit (b + (2 ^ 128 - 2 ^ 64))
      apply VmIsRangeChecked_aux
      apply add_nonneg b_nonneg (by norm_num)
      rw [not_lt] at hqsmall
      have : b < 2^64 := by
        by_contra h
        rw [not_lt] at h
        have := mul_le_mul hqsmall h (by norm_num) adivb_nonneg
        revert h_a_lt
        apply not_lt_of_ge
        apply le_trans this
        apply le_trans (le_add_of_nonneg_right amodb_nonneg)
        rw [add_comm, Int.emod_add_ediv']
      apply lt_of_lt_of_le (add_lt_add_right this _)
      norm_num [u128Limit]
    refine ⟨rfl, ?_, rfl, rfl⟩
    rw [add_comm, Int.emod_add_ediv]
