import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def limit : F := (18446744073709551616 : F) -- LIMIT
def a_imm : F := (10633823966279327296825105735305134080 : F) -- a_imm
def b_imm_fix : F := (319014718988379808888171140034867494911 : F) -- (BigInt::from(u128::MAX) - b_imm + 1) as BigInt
def u128_limit_minus_1 : F := (340282366920938463463374607431768211455 : F) -- u128::MAX
def u128_limit_minus_2 : F := (340282366920938463463374607431768211454 : F) -- u128::MAX - 1
def fixer_limit : F := (340282366920938463444927863358058659840 : F) -- (u128::MAX - LIMIT + 1)

-- defined manually:
def n_a_imm : ℕ := 10633823966279327296825105735305134080
def n_b_imm : ℕ := 21267647932558654575203467396900716545 -- (PRIME - 2^64) % (2^128 - 2)
def n_b_imm_fix : ℕ := 319014718988379808888171140034867494911

lemma coe_n_bimm_fix_eq : (n_b_imm_fix : F) = b_imm_fix := rfl

def spec_u64_try_from_felt252 (κ : ℕ) (range_check value ρ_branch_id ρ_value : F) : Prop :=
  ∃ nvalue < PRIME,
    value = ↑nvalue ∧
    ((nvalue < 2^64 ∧ ρ_branch_id = 0 ∧ ρ_value = value) ∨
     (nvalue ≥ 2^64 ∧ ρ_branch_id = 1))

def auto_spec_u64_try_from_felt252_IsSmall (κ : ℕ) (range_check value ρ_branch_id ρ_value : F) : Prop :=
  IsRangeChecked (rcBound F) value ∧
  ∃ value_upper_limit : F, value_upper_limit = value + fixer_limit ∧
  IsRangeChecked (rcBound F) value_upper_limit ∧
  ρ_branch_id = 0 ∧
  ρ_value = value

def auto_spec_u64_try_from_felt252 (κ : ℕ) (range_check value ρ_branch_id ρ_value : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ is_small : F,
  (
    (is_small = 0 ∧
      ∃ shifted_value : F, shifted_value = value - limit ∧
      ∃ x_part : F,
      ∃ x : F,
      x_part = x * a_imm ∧
      ∃ y : F,
      shifted_value = x_part + y ∧
      IsRangeChecked (rcBound F) y ∧
      ∃ y_fixed : F,
      y_fixed = y + b_imm_fix ∧
      IsRangeChecked (rcBound F) y_fixed ∧
      IsRangeChecked (rcBound F) x ∧
      ∃ diff : F,
      diff = x - u128_limit_minus_1 ∧
      (
        (diff = 0 ∧
          false
        ) ∨
        (diff ≠ 0 ∧
          ρ_branch_id = 1
        )
      )
    ) ∨
    (is_small ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u64_try_from_felt252_IsSmall κ₁
        range_check value ρ_branch_id ρ_value
    )
  )

theorem sound_u64_try_from_felt252
    (κ : ℕ)
    (range_check value ρ_branch_id ρ_value : F)
    (h_auto : auto_spec_u64_try_from_felt252 κ range_check value ρ_branch_id ρ_value) :
  spec_u64_try_from_felt252 κ range_check value ρ_branch_id ρ_value := by
  rcases h_auto with ⟨-, -, is_small, hsmallz | hsmallnz⟩
  . rcases hsmallz with ⟨-, shifted_value, shifted_value_eq,
      partx, x, partx_eq, y, value_eq, rc_y, y_fixed, y_fixed_eq, rc_y_fixed, rc_x,
      diff, diffeq, ⟨-, hcontr⟩ | ⟨diff_ne_z, ρ_branch_id_eq_1 ⟩⟩
    . contradiction
    rcases rc_x with ⟨n_x, n_x_lt, x_eq⟩
    rcases rc_y with ⟨n_y, n_y_lt, y_eq⟩
    rcases rc_y_fixed with ⟨n_y_fixed, n_y_fixed_lt, n_y_fixed_eq⟩
    have h1 : n_y < n_b_imm := by
      have : n_y_fixed = n_y + n_b_imm_fix := by
        apply @PRIME.nat_coe_field_inj F
        . apply lt_trans n_y_fixed_lt (rcBound_lt_PRIME)
        . apply lt_of_lt_of_le
          apply add_lt_add_right
          apply lt_of_lt_of_le n_y_lt (rcBound_hyp F)
          rw [n_b_imm_fix, PRIME]
          norm_num
        rw [←n_y_fixed_eq, Nat.cast_add, ←y_eq, y_fixed_eq]
        rfl
      apply lt_of_add_lt_add_right
      rw [←this]
      apply lt_of_lt_of_le n_y_fixed_lt
      apply le_trans (rcBound_hyp F)
      rw [n_b_imm, n_b_imm_fix]
      norm_num
    have h2 : n_x < 2^128 - 1 := by
      apply lt_of_le_of_ne
      apply Nat.le_sub_one_of_lt
      apply lt_of_lt_of_le n_x_lt (rcBound_hyp F)
      intro hcontra
      apply diff_ne_z
      simp only [diffeq, x_eq, hcontra, ge_iff_le, Nat.cast_sub, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one, u128_limit_minus_1]
      norm_num
    use n_x * n_a_imm + n_y + 2^64
    have : n_x * n_a_imm + n_y < PRIME - 2^64 := by
      apply lt_of_lt_of_le
      apply add_lt_add_of_le_of_lt
      apply Nat.mul_le_mul_right
      apply Nat.le_pred_of_lt
      apply h2
      apply h1
      rw [n_a_imm, n_b_imm]
      norm_num [PRIME]
    constructor
    . apply lt_of_lt_of_le
      apply add_lt_add_right this
      rw [tsub_add_cancel_of_le]
      rw [PRIME]; norm_num
    constructor
    . rw [← (add_eq_of_eq_sub shifted_value_eq), value_eq, partx_eq, x_eq, y_eq]
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, limit, a_imm, n_a_imm]
      simp
    right
    constructor
    . apply le_add_left; rfl
    exact ρ_branch_id_eq_1
  rcases hsmallnz with ⟨-, -, rc_value, value_upper_limit,
    value_upper_limit_eq, rc_value_upper_limit, ρ_branch_id_eq, ρ_value_eq⟩
  rcases rc_value with ⟨n_value, n_value_lt, value_eq⟩
  rcases rc_value_upper_limit with ⟨n_value_upper_limit, n_value_upper_limit_lt,
    value_upper_limit_eq'⟩
  have h1 : n_value_upper_limit = n_value + (2^128 - 2^64) := by
    apply @PRIME.nat_coe_field_inj F
    . exact n_value_upper_limit_lt.trans rcBound_lt_PRIME
    . apply lt_of_lt_of_le
      apply add_lt_add_right (n_value_lt.trans (rcBound_hyp F))
      rw [PRIME]; norm_num
    . rw [← value_upper_limit_eq', value_upper_limit_eq, value_eq, fixer_limit, Nat.cast_add]
      simp;
  have := tsub_eq_of_eq_add h1
  use n_value, n_value_lt.trans rcBound_lt_PRIME, value_eq
  left
  constructor
  . rw [←this]
    apply lt_of_lt_of_le
    rw [tsub_lt_tsub_iff_right]
    apply (lt_of_lt_of_le n_value_upper_limit_lt (rcBound_hyp F))
    . rw [h1]
      apply le_add_left; rfl
    norm_num
  use ρ_branch_id_eq
