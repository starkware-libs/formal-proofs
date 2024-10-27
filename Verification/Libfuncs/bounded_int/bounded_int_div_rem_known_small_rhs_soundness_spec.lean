import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace bounded_int_div_rem_known_small_rhs_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def one : F := (1 : F) -- 1

/-
  extern type BoundedInt<const MIN: felt252, const MAX: felt252>;
  type DivRemType = (
      BoundedInt<16, 85>,
      BoundedInt<0, 7>,
  );

  extern fn bounded_int_div_rem<T1, T2>(a: T1, b: NonZero<T2>) -> DivRemType implicits(RangeCheck) nopanic;

  fn foo(a: BoundedInt<128, 255>, b: NonZero<BoundedInt<3, 8>>) -> DivRemType {
      bounded_int_div_rem(a, b)
}
-/

def spec_bounded_int_div_rem_known_small_rhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  ∀ (n_a n_b : ℕ) (lhs rhs : IntRange),
    a = ↑n_a ∧ n_a < PRIME →
    b = ↑n_b →
    try_new lhs rhs = some RemDivAlg.KnownSmallRhs →
    0 ≤ lhs.lower →
    0 < rhs.lower →
    InRange n_a lhs →
    InRange n_b rhs →
      ∃ (n_q n_r : ℕ), ρ_q = ↑n_q ∧ ρ_r = ↑n_r ∧ n_r < n_b ∧ n_a = n_q * n_b + n_r

def auto_spec_bounded_int_div_rem_known_small_rhs (κ : ℕ) (range_check a b ρ_q ρ_r : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ r_plus_1 : F,
  ∃ b_minus_r_minus_1 : F,
  ∃ bq : F,
  ∃ q : F,
  ∃ r : F, IsRangeChecked (rcBound F) r ∧
  r_plus_1 = r + one ∧
  b_minus_r_minus_1 = b - r_plus_1 ∧
  IsRangeChecked (rcBound F) b_minus_r_minus_1 ∧
  IsRangeChecked (rcBound F) q ∧
  bq = b * q ∧
  a = bq + r ∧
  ρ_q = q ∧
  ρ_r = r


theorem sound_bounded_int_div_rem_known_small_rhs
    (κ : ℕ)
    (range_check a b ρ_q ρ_r : F)
    (h_auto : auto_spec_bounded_int_div_rem_known_small_rhs κ range_check a b ρ_q ρ_r) :
  spec_bounded_int_div_rem_known_small_rhs κ range_check a b ρ_q ρ_r := by

  intros n_a n_b lhs rhs h_a h_b h_alg h_lhs_nonneg h_rhs_pos h_a_inRange h_b_inRange

  rcases DivRemAlg_KnownSmallRhs_bounds h_lhs_nonneg h_rhs_pos h_alg h_a_inRange h_b_inRange with
    ⟨-, -, -, h_n_b_lt⟩

  rw [←Nat.cast_mul, Nat.cast_lt] at h_n_b_lt

  rcases h_auto with ⟨-, -, r_plus_1, b_minus_r_minus_1, bq, q, r,
    ⟨n_r, h_n_r_lt, rfl⟩,
    h_r_plus_1, h_b_minus_r_minus_1,
    ⟨n_b_minus_r_minus_1, h_n_b_minus_r_minus_1_lt, rfl⟩,
    ⟨n_q, h_n_q_lt, rfl⟩,
    h_bq, h_a_bq_r, rfl, rfl⟩

  have h_rcBound := @rcBound_hyp F
  replace h_n_q_lt := lt_of_lt_of_le h_n_q_lt h_rcBound
  replace h_n_r_lt := lt_of_lt_of_le h_n_r_lt h_rcBound
  replace h_n_b_minus_r_minus_1_lt := lt_of_lt_of_le h_n_b_minus_r_minus_1_lt h_rcBound

  use n_q, n_r, rfl, rfl

  rcases h_a with ⟨rfl, h_n_a_lt⟩
  rcases h_b with ⟨rfl⟩

  have h_n_r_lt_n_b : n_r < n_b := by
    apply Nat.lt_of_succ_le ; rw [←Nat.add_one]
    apply le_trans (Nat.le_add_left _ n_b_minus_r_minus_1)
    apply le_of_eq ; rw [←add_assoc]
    rw [eq_sub_iff_add_eq, h_r_plus_1, one, ←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add, ←add_assoc] at h_b_minus_r_minus_1
    apply PRIME.nat_coe_field_inj
      (lt_u128_triple_add_lt_PRIME _ _ 1 h_n_b_minus_r_minus_1_lt h_n_r_lt (by norm_num1))
      (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by norm_num1)) h_n_b_lt) h_b_minus_r_minus_1

  use h_n_r_lt_n_b

  rw [h_bq, mul_comm] at h_a_bq_r ; norm_cast at h_a_bq_r
  apply PRIME.nat_coe_field_inj h_n_a_lt _ h_a_bq_r

  apply lt_trans (Nat.add_lt_add_left h_n_r_lt_n_b _)
  rw [←Nat.succ_mul, mul_comm]
  apply lt_of_le_of_lt _ h_n_b_lt
  apply Nat.mul_le_mul_left
  apply Nat.succ_le_of_lt
  exact h_n_q_lt
