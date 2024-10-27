import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u128_overflowing_add_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def u128_limit : F := (340282366920938463463374607431768211456 : F) -- (BigInt::from(u128::MAX) + 1) as BigInt

def spec_u128_overflowing_add (κ : ℕ) (range_check a b ρ_branch_id ρ_a_plus_b : F) : Prop :=
  ∃ (n : ℕ), is_u128_of ρ_a_plus_b n ∧ (a + b = u128Limit + ρ_a_plus_b ∨ a + b = ρ_a_plus_b)

def auto_spec_u128_overflowing_add_NoOverflow (κ : ℕ) (range_check a_plus_b ρ_branch_id ρ_a_plus_b : F) : Prop :=
  IsRangeChecked (rcBound F) a_plus_b ∧
  ρ_branch_id = 0 ∧
  ρ_a_plus_b = a_plus_b

def auto_spec_u128_overflowing_add (κ : ℕ) (range_check a b ρ_branch_id ρ_a_plus_b : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ no_overflow : F,
  ∃ a_plus_b : F, a_plus_b = a + b ∧
  (
    (no_overflow = 0 ∧
      ∃ wrapping_a_plus_b : F, wrapping_a_plus_b = a_plus_b - u128_limit ∧
      IsRangeChecked (rcBound F) wrapping_a_plus_b ∧
      ρ_branch_id = 1 ∧
      ρ_a_plus_b = wrapping_a_plus_b
    ) ∨
    (no_overflow ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u128_overflowing_add_NoOverflow κ₁
        range_check a_plus_b ρ_branch_id ρ_a_plus_b
    )
  )


theorem sound_u128_overflowing_add
    (κ : ℕ)
    (range_check a b ρ_branch_id ρ_a_plus_b : F)
    (h_auto : auto_spec_u128_overflowing_add κ range_check a b ρ_branch_id ρ_a_plus_b) :
  spec_u128_overflowing_add κ range_check a b ρ_branch_id ρ_a_plus_b :=
by
  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound
  rcases h_auto with ⟨-, -, no_overflow, a_plus_b, h_a_plus_b, h_cont|h_cont⟩
  · rcases h_cont with ⟨-, wrapping_a_plus_b, h_wrapping_a_plus_b,
      ⟨n_wrapping_a_plus_b, h_n_wrapping_a_plus_b_lt, rfl⟩, rfl, rfl⟩
    replace h_n_wrapping_a_plus_b_lt := lt_of_lt_of_le h_n_wrapping_a_plus_b_lt h_rcBound
    use n_wrapping_a_plus_b
    constructor
    · use h_n_wrapping_a_plus_b_lt
    left
    rw [←h_a_plus_b, h_wrapping_a_plus_b, u128_limit, u128Limit]
    ring
  rcases h_cont with ⟨-, -, ⟨n_a_plus_b, h_n_a_plus_b_lt, rfl⟩, rfl, rfl⟩
  replace h_n_a_plus_b_lt := lt_of_lt_of_le h_n_a_plus_b_lt h_rcBound
  use n_a_plus_b
  constructor
  · use h_n_a_plus_b_lt
  right
  rw [h_a_plus_b]
