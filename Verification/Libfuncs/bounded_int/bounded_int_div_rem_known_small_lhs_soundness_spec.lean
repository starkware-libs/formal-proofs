import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace bounded_int_div_rem_knonw_small_lhs_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def one : F := (1 : F) -- 1
def limiter_bound : F := (18446744073709551616 : F) -- lhs_upper_sqrt.clone()
def u128_bound_minus_limiter_bound : F := (340282366920938463444927863358058659840 : F) -- (BigInt::one().shl(128) - lhs_upper_sqrt) as BigInt

namespace bounded_int_div_rem_known_small_lhs_generalized

-- This section generalizes the bound and proves that the user specifications follow from
-- the automatic specifications for any value of the bound.

variable (u128_bound_minus_limiter_bound : F)

def spec_bounded_int_div_rem_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  ∀ (lhs_upper_sqrt n_a n_b : ℕ) (lhs rhs : IntRange),
    u128_bound_minus_limiter_bound = (↑(u128Limit - lhs_upper_sqrt) : F) →
    a = ↑n_a ∧ n_a < PRIME →
    b = ↑n_b →
    try_new lhs rhs = some (RemDivAlg.KnownSmallLhs lhs_upper_sqrt) →
    0 ≤ lhs.lower →
    0 < rhs.lower →
    InRange n_a lhs →
    InRange n_b rhs →
      ∃ (n_q n_r : ℕ), ρ_q = ↑n_q ∧ ρ_r = ↑n_r ∧ n_r < n_b ∧ n_a = n_q * n_b + n_r

def auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  IsRangeChecked (rcBound F) b_or_q_bound_rc_value ∧
  bq = b * q ∧
  a = bq + r ∧
  ρ_q = q ∧
  ρ_r = r

def auto_spec_bounded_int_div_rem_known_small_lhs_QIsSmall (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  b_or_q_bound_rc_value = q + u128_bound_minus_limiter_bound ∧
  ∃ (κ₁ : ℕ), auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ κ₁
    range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r

def auto_spec_bounded_int_div_rem_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ r_plus_1 : F,
  ∃ b_minus_r_minus_1 : F,
  ∃ bq : F,
  ∃ q : F,
  ∃ r : F,
  IsRangeChecked (rcBound F) q ∧
  IsRangeChecked (rcBound F) r ∧
  r_plus_1 = r + one ∧
  b_minus_r_minus_1 = b - r_plus_1 ∧
  IsRangeChecked (rcBound F) b_minus_r_minus_1 ∧
  ∃ q_is_small : F,
  (
    (q_is_small = 0 ∧
      ∃ b_or_q_bound_rc_value : F,
      b_or_q_bound_rc_value = b + u128_bound_minus_limiter_bound ∧
      ∃ (κ₁ : ℕ), auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ κ₁
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    ) ∨
    (q_is_small ≠ 0 ∧
      ∃ b_or_q_bound_rc_value : F,
      ∃ (κ₁ : ℕ), auto_spec_bounded_int_div_rem_known_small_lhs_QIsSmall u128_bound_minus_limiter_bound κ₁
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    )
  )


theorem sound_bounded_int_div_rem_known_small_lhs
    (κ : ℕ)
    (range_check a b ρ_q ρ_r : F)
    (h_auto : auto_spec_bounded_int_div_rem_known_small_lhs u128_bound_minus_limiter_bound κ range_check a b ρ_q ρ_r) :
  spec_bounded_int_div_rem_known_small_lhs u128_bound_minus_limiter_bound κ range_check a b ρ_q ρ_r := by

  intros lhs_upper_sqrt n_a n_b lhs rhs h_u128_bound_minus_lhs_upper_sqrt h_a h_b h_alg h_lhs_nonneg h_rhs_pos h_a_inRange h_b_inRange

  rcases DivRemAlg_KnownSmallLhs_bounds h_lhs_nonneg h_rhs_pos h_alg h_a_inRange h_b_inRange with
    ⟨-, -, h_n_b_le, -, h_lhs_upper_sqrt_lt, -⟩

  rw [Nat.cast_le] at h_n_b_le

  rcases h_auto with ⟨-, -, r_plus_1, b_minus_r_minus_1, bq, q, r,
    ⟨n_q, h_n_q_lt, rfl⟩, h_rc_r,
    h_r_plus_1, h_b_minus_r_minus_1,
    ⟨n_b_minus_r_minus_1, h_n_b_minus_r_minus_1_lt, rfl⟩, h_auto⟩

  rcases h_rc_r with ⟨n_r, h_n_r_lt, rfl⟩

  rcases h_a with ⟨rfl, h_n_a_lt⟩
  rcases h_b with ⟨rfl⟩

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  replace h_n_q_lt := lt_of_lt_of_le h_n_q_lt h_rcBound
  replace h_n_r_lt := lt_of_lt_of_le h_n_r_lt h_rcBound
  replace h_n_b_minus_r_minus_1_lt := lt_of_lt_of_le h_n_b_minus_r_minus_1_lt h_rcBound

  have h_n_r_lt_n_b : n_r < n_b := by
    apply Nat.lt_of_succ_le ; rw [←Nat.add_one]
    apply le_trans (Nat.le_add_left _ n_b_minus_r_minus_1)
    apply le_of_eq ; rw [←add_assoc]
    rw [eq_sub_iff_add_eq, h_r_plus_1, one, ←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add, ←add_assoc] at h_b_minus_r_minus_1
    apply PRIME.nat_coe_field_inj
      (lt_u128_triple_add_lt_PRIME _ _ 1 h_n_b_minus_r_minus_1_lt h_n_r_lt (by norm_num1))
      (lt_of_le_of_lt h_n_b_le u128Limit_lt_PRIME) h_b_minus_r_minus_1

  rcases h_auto with ⟨q_is_small, q_is_small_eq_zero|q_is_small_ne_zero⟩

  · rcases q_is_small_eq_zero with ⟨h_q_is_small_eq_zero, b_or_q_bound_rc_value, h_b_or_q_bound_rc_value, -,
      ⟨n_b_or_q_bound_rc_value, h_n_b_or_q_bound_rc_value_lt, rfl⟩, h_bq, h_a, rfl, rfl⟩

    -- b < lhs_upper_sqrt
    use n_q, n_r, rfl, rfl, h_n_r_lt_n_b
    replace h_n_b_or_q_bound_rc_value_lt := lt_of_lt_of_le h_n_b_or_q_bound_rc_value_lt h_rcBound

    replace h_n_b_lt : n_b < lhs_upper_sqrt := by
      apply lt_of_add_sub_lt (b := u128Limit)
      apply lt_of_eq_of_lt _ h_n_b_or_q_bound_rc_value_lt
      rw [h_u128_bound_minus_lhs_upper_sqrt, ←Nat.cast_add] at h_b_or_q_bound_rc_value
      apply PRIME.nat_coe_field_inj _ (lt_PRIME_of_lt_u128Limit h_n_b_or_q_bound_rc_value_lt) h_b_or_q_bound_rc_value.symm
      apply le_u128_add_le_u128_lt_PRIME _ _ h_n_b_le
      apply Nat.sub_le

    rw [h_bq, mul_comm] at h_a ; norm_cast at h_a
    apply PRIME.nat_coe_field_inj h_n_a_lt _ h_a

    apply lt_trans (Nat.add_lt_add_left h_n_r_lt_n_b _)
    rw [←Nat.succ_mul, mul_comm]

    apply lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h_n_q_lt))
    apply lt_of_le_of_lt _ h_lhs_upper_sqrt_lt
    apply Nat.mul_le_mul_right _ (le_of_lt h_n_b_lt)

  rcases q_is_small_ne_zero with ⟨h_q_is_small_ne_zero, b_or_q_bound_rc_value, -,
    h_b_or_q_bound_rc_value, -,
    ⟨n_b_or_q_bound_rc_value, h_n_b_or_q_bound_rc_value_lt, rfl⟩, h_bq, h_a, rfl, rfl⟩

  -- q < lhs_upper_sqrt
  use n_q, n_r, rfl, rfl, h_n_r_lt_n_b
  replace h_n_b_or_q_bound_rc_value_lt := lt_of_lt_of_le h_n_b_or_q_bound_rc_value_lt h_rcBound

  have h_n_q_lt : n_q < lhs_upper_sqrt := by
    apply lt_of_add_sub_lt (b := u128Limit)
    apply lt_of_eq_of_lt _ h_n_b_or_q_bound_rc_value_lt
    rw [h_u128_bound_minus_lhs_upper_sqrt, ←Nat.cast_add] at h_b_or_q_bound_rc_value
    apply PRIME.nat_coe_field_inj _ (lt_PRIME_of_lt_u128Limit h_n_b_or_q_bound_rc_value_lt) h_b_or_q_bound_rc_value.symm
    apply lt_u128_add_le_u128_lt_PRIME _ _ h_n_q_lt
    apply Nat.sub_le

  rw [h_bq, mul_comm] at h_a ; norm_cast at h_a
  apply PRIME.nat_coe_field_inj h_n_a_lt _ h_a

  apply lt_trans (Nat.add_lt_add_left h_n_r_lt_n_b _)
  rw [←Nat.succ_mul, mul_comm]

  apply lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h_n_q_lt))
  rw [mul_comm]
  apply lt_of_le_of_lt _ h_lhs_upper_sqrt_lt
  apply Nat.mul_le_mul_left _ h_n_b_le

end bounded_int_div_rem_known_small_lhs_generalized

-- The specs and proof in this section (which are used in the automatic soundness proof)
-- are the specs and theorem of the generalized section, applied to the specific bound value
-- for which the code was compiled.

def spec_bounded_int_div_rem_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  bounded_int_div_rem_known_small_lhs_generalized.spec_bounded_int_div_rem_known_small_lhs
    u128_bound_minus_limiter_bound κ range_check a b ρ_q ρ_r

def auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  bounded_int_div_rem_known_small_lhs_generalized.auto_spec_bounded_int_div_rem_known_small_lhs_VerifyBQ
    κ range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r

def auto_spec_bounded_int_div_rem_known_small_lhs_QIsSmall (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  bounded_int_div_rem_known_small_lhs_generalized.auto_spec_bounded_int_div_rem_known_small_lhs_QIsSmall
    u128_bound_minus_limiter_bound κ range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r

def auto_spec_bounded_int_div_rem_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  bounded_int_div_rem_known_small_lhs_generalized.auto_spec_bounded_int_div_rem_known_small_lhs
    u128_bound_minus_limiter_bound κ range_check a b ρ_q ρ_r

theorem sound_bounded_int_div_rem_known_small_lhs
    (κ : ℕ)
    (range_check a b ρ_q ρ_r : F)
    (h_auto : auto_spec_bounded_int_div_rem_known_small_lhs κ range_check a b ρ_q ρ_r) :
  spec_bounded_int_div_rem_known_small_lhs κ range_check a b ρ_q ρ_r := by

  apply bounded_int_div_rem_known_small_lhs_generalized.sound_bounded_int_div_rem_known_small_lhs
    u128_bound_minus_limiter_bound κ range_check a b ρ_q ρ_r h_auto