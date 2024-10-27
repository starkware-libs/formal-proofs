import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_safe_divmod_known_small_lhs_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def one : F := (1 : F) -- 1
def limiter_bound : F := (18446744073709551616 : F) -- lhs_upper_sqrt.clone()
def u128_bound_minus_limiter_bound : F := (340282366920938463444927863358058659840 : F) -- (BigInt::one().shl(128) - lhs_upper_sqrt) as BigInt

lemma eq_u128_bound_minus_limiter_bound : u128_bound_minus_limiter_bound = ((u128Limit - u64Limit : ℕ) : F) := by
  unfold u128_bound_minus_limiter_bound u128Limit u64Limit ; norm_num1

def spec_u128_safe_divmod_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  ∀ (n_a n_b : ℕ),
    is_u128_of a n_a →
    is_u128_of b n_b →
    b ≠ 0 →
      ∃ (n_q n_r : ℕ), is_u128_of ρ_q n_q ∧ is_u128_of ρ_r n_r ∧ n_r < n_b ∧ n_a = n_q * n_b + n_r

def auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  IsRangeChecked (rcBound F) b_or_q_bound_rc_value ∧
  bq = b * q ∧
  a = bq + r ∧
  ρ_q = q ∧
  ρ_r = r

def auto_spec_u128_safe_divmod_known_small_lhs_QIsSmall (κ : ℕ) (range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r : F) : Prop :=
  b_or_q_bound_rc_value = q + u128_bound_minus_limiter_bound ∧
  ∃ (κ₁ : ℕ), auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ κ₁
    range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r

def auto_spec_u128_safe_divmod_known_small_lhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
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
      ∃ (κ₁ : ℕ), auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ κ₁
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    ) ∨
    (q_is_small ≠ 0 ∧
      ∃ b_or_q_bound_rc_value : F,
      ∃ (κ₁ : ℕ), auto_spec_u128_safe_divmod_known_small_lhs_QIsSmall κ₁
        range_check a b b_or_q_bound_rc_value bq q r ρ_q ρ_r
    )
  )

theorem sound_u128_safe_divmod_known_small_lhs
    (κ : ℕ)
    (range_check a b ρ_q ρ_r : F)
    (h_auto : auto_spec_u128_safe_divmod_known_small_lhs κ range_check a b ρ_q ρ_r) :
  spec_u128_safe_divmod_known_small_lhs κ range_check a b ρ_q ρ_r := by

  intros n_a n_b h_u128_a h_u128_b h_b_ne_0
  unfold is_u128_of

  rcases h_auto with ⟨-, -, r_plus_1, b_minus_r_minus_1, bq, q, r,
    ⟨n_q, h_n_q_lt, rfl⟩, h_rc_r,
    h_r_plus_1, h_b_minus_r_minus_1,
    ⟨n_b_minus_r_minus_1, h_n_b_minus_r_minus_1_lt, rfl⟩, h_auto⟩

  rcases h_rc_r with ⟨n_r, h_n_r_lt, rfl⟩

  rcases h_u128_a with ⟨h_n_a_lt, rfl⟩
  rcases h_u128_b with ⟨h_n_b_lt, rfl⟩

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
      (lt_PRIME_of_lt_u128Limit h_n_b_lt) h_b_minus_r_minus_1

  rcases h_auto with ⟨q_is_small, q_is_small_eq_zero|q_is_small_ne_zero⟩

  · rcases q_is_small_eq_zero with ⟨h_q_is_small_eq_zero, b_or_q_bound_rc_value, h_b_or_q_bound_rc_value, -,
      ⟨n_b_or_q_bound_rc_value, h_n_b_or_q_bound_rc_value_lt, rfl⟩, h_bq, h_a, rfl, rfl⟩

    -- b < 2 ^ 64
    use n_q, n_r, ⟨h_n_q_lt, rfl⟩, ⟨h_n_r_lt, rfl⟩, h_n_r_lt_n_b
    replace h_n_b_or_q_bound_rc_value_lt := lt_of_lt_of_le h_n_b_or_q_bound_rc_value_lt h_rcBound

    have h_n_b_lt_u64 : n_b < u64Limit := by
      apply lt_of_add_sub_lt (b := u128Limit)
      apply lt_of_eq_of_lt _ h_n_b_or_q_bound_rc_value_lt
      rw [eq_u128_bound_minus_limiter_bound, ←Nat.cast_add] at h_b_or_q_bound_rc_value
      apply PRIME.nat_coe_field_inj _ (lt_PRIME_of_lt_u128Limit h_n_b_or_q_bound_rc_value_lt) h_b_or_q_bound_rc_value.symm
      rw [u128Limit, u64Limit] ; norm_num1
      apply lt_u128_add_lt_PRIME _ _ h_n_b_lt ; norm_num1

    rw [h_bq, mul_comm] at h_a ; norm_cast at h_a
    apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_a_lt) _ h_a
    apply lt_u128_mul_u64_add_u128_lt_PRIME _ _ _ h_n_q_lt h_n_b_lt_u64 h_n_r_lt

  rcases q_is_small_ne_zero with ⟨h_q_is_small_ne_zero, b_or_q_bound_rc_value, -,
    h_b_or_q_bound_rc_value, -,
    ⟨n_b_or_q_bound_rc_value, h_n_b_or_q_bound_rc_value_lt, rfl⟩, h_bq, h_a, rfl, rfl⟩

  -- q < 2 ^ 64
  use n_q, n_r, ⟨h_n_q_lt, rfl⟩, ⟨h_n_r_lt, rfl⟩, h_n_r_lt_n_b
  replace h_n_b_or_q_bound_rc_value_lt := lt_of_lt_of_le h_n_b_or_q_bound_rc_value_lt h_rcBound

  have h_n_q_lt_u64 : n_q < u64Limit := by
    apply lt_of_add_sub_lt (b := u128Limit)
    apply lt_of_eq_of_lt _ h_n_b_or_q_bound_rc_value_lt
    rw [eq_u128_bound_minus_limiter_bound, ←Nat.cast_add] at h_b_or_q_bound_rc_value
    apply PRIME.nat_coe_field_inj _ (lt_PRIME_of_lt_u128Limit h_n_b_or_q_bound_rc_value_lt) h_b_or_q_bound_rc_value.symm
    rw [u128Limit, u64Limit] ; norm_num1
    apply lt_u128_add_lt_PRIME _ _ h_n_q_lt ; norm_num1

  rw [h_bq, mul_comm] at h_a ; norm_cast at h_a
  apply PRIME.nat_coe_field_inj (lt_PRIME_of_lt_u128Limit h_n_a_lt) _ h_a
  rw [mul_comm]
  apply lt_u128_mul_u64_add_u128_lt_PRIME _ _ _ h_n_b_lt h_n_q_lt_u64 h_n_r_lt
