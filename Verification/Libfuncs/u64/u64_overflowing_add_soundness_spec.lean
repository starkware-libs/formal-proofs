import Verification.Libfuncs.Common

namespace u64_overflowing_add_soundness
open Nat

variable {F : Type} [Field F] [PreludeHyps F]

def spec_u64_overflowing_add (a b ρ_overflow ρ_add : F) : Prop :=
  ∀ na : ℕ, is_u64_of a na →
  ∀ nb : ℕ, is_u64_of b nb →
  ∃ n : ℕ, is_u64_of ρ_add n ∧
    (ρ_overflow = 1 ∧ na + nb = n + u64Limit ∨
     ρ_overflow = 0 ∧ na + nb = n)

def auto_spec_u64_overflowing_add (a b ρ_overflow ρ_add : F) : Prop :=
   ∃ no_overflow : F,
   ∃ deferred_a_plus_b : F, deferred_a_plus_b = a + b ∧
   ((no_overflow = 0 ∧
      ∃ fixed_a_plus_b : F, fixed_a_plus_b = deferred_a_plus_b - u64Limit ∧
      IsRangeChecked (rcBound F) fixed_a_plus_b ∧
      ρ_overflow = 1 ∧ ρ_add = fixed_a_plus_b)
    ∨
    (no_overflow ≠ 0 ∧
      IsRangeChecked (rcBound F) (deferred_a_plus_b + u128Limit - u64Limit) ∧
      ρ_overflow = 0 ∧ ρ_add = deferred_a_plus_b))

theorem sound_u64_overflowing_add {a b ρ_branch_id ρ_a_plus_b : F}
    (h_auto : auto_spec_u64_overflowing_add a b ρ_branch_id ρ_a_plus_b) :
  spec_u64_overflowing_add a b ρ_branch_id ρ_a_plus_b := by
  rintro na ⟨h_na_lt, rfl⟩ nb ⟨h_nb_lt, rfl⟩
  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound
  have hab := Nat.add_lt_add h_na_lt h_nb_lt
  have h₂ : na + nb < PRIME := lt_trans hab u64Limit_double_lt_PRIME
  rcases h_auto with ⟨n_overflow, deferred_a_plus_b, rfl, h_overflow | h_no_overflow⟩
  · rcases h_overflow with ⟨_, fixed_a_plus_b, h_fixed_a_plus_b, ⟨n, h_rc_lt, rfl⟩, rfl, rfl⟩
    replace h_rc_lt := lt_of_lt_of_le h_rc_lt h_rcBound
    use n
    have h₁ : n + u64Limit < PRIME := add_lt_PRIME_of_lt h_rc_lt u64Limit_lt_u128Limit
    rw [eq_sub_iff_add_eq, ← cast_add, ← cast_add] at h_fixed_a_plus_b
    constructor
    · constructor
      · rw [← PRIME.nat_coe_field_inj h₁ h₂ h_fixed_a_plus_b] at hab
        exact lt_of_add_lt_add_right hab
      · rfl
    exact Or.inl ⟨rfl, (PRIME.nat_coe_field_inj h₁ h₂ h_fixed_a_plus_b).symm⟩
  rcases h_no_overflow with ⟨_, ⟨n, h_rc_lt, h_rc_eq⟩, rfl, rfl⟩
  replace h_rc_lt := lt_of_lt_of_le h_rc_lt h_rcBound
  have h_u64_le_u128 := (le_of_lt u64Limit_lt_u128Limit)
  have h_n_gt : u128Limit - u64Limit ≤ n := by
    rw [← cast_add, ← cast_add, ← cast_sub (le_trans (le_of_lt u64Limit_lt_u128Limit) (le_add_self))] at h_rc_eq
    have h₁ : na + nb + u128Limit - u64Limit < PRIME := by
      apply tsub_lt_of_lt
      exact add_lt_PRIME_of_le (le_of_lt (add_lt_u128Limit_of_lt_u64Limit h_na_lt h_nb_lt)) (le_refl _)
    have h₂ := lt_trans h_rc_lt u128Limit_lt_PRIME
    have h := PRIME.nat_coe_field_inj h₁ h₂ h_rc_eq
    rw [← h, Nat.add_sub_assoc h_u64_le_u128]
    exact le_add_left _ _
  use n - (u128Limit - u64Limit)
  constructor
  · constructor
    · apply @Nat.lt_of_add_lt_add_right _ _ (u128Limit - u64Limit) _
      rw [Nat.sub_add_cancel h_n_gt, ← Nat.add_sub_assoc h_u64_le_u128, add_comm, Nat.add_sub_cancel]
      exact h_rc_lt
    · rw [Nat.cast_sub h_n_gt, Nat.cast_sub h_u64_le_u128, ← h_rc_eq, add_sub_assoc,
        add_sub_cancel_right]
  right
  use rfl
  rw [add_sub_assoc, ← cast_sub (le_of_lt u64Limit_lt_u128Limit), ← cast_add, ← cast_add] at h_rc_eq
  symm; rw [Nat.sub_eq_iff_eq_add h_n_gt]; symm
  apply PRIME.nat_coe_field_inj _ _ h_rc_eq
  · apply lt_trans (add_lt_add_right (Nat.add_lt_add h_na_lt h_nb_lt) _)
    unfold PRIME; norm_num1
  · exact lt_trans h_rc_lt u128Limit_lt_PRIME

end u64_overflowing_add_soundness
