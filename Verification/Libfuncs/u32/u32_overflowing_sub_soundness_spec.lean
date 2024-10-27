import Verification.Libfuncs.Common

namespace u32_overflowing_sub_soundness
open Nat

variable {F : Type} [Field F] [PreludeHyps F]

def spec_u32_overflowing_sub (a b ρ_overflow ρ_sub : F) : Prop :=
  ∀ na : ℕ, is_u32_of a na →
  ∀ nb : ℕ, is_u32_of b nb →
  ∃ n : ℕ, is_u32_of ρ_sub n ∧
    (ρ_overflow = 1 ∧ ρ_sub = a - b + u32Limit ∨
     ρ_overflow = 0 ∧ ρ_sub = a - b)

def auto_spec_u32_overflowing_sub (a b ρ_overflow ρ_sub : F) : Prop :=
  ∃ a_ge_b : F,
  ∃ a_minus_b : F, a_minus_b = a - b ∧
    ((a_ge_b = 0 ∧
      ∃ fixed_a_minus_b : F, fixed_a_minus_b = a_minus_b + u128Limit ∧
      IsRangeChecked (rcBound F) fixed_a_minus_b ∧
      ρ_overflow = 1 ∧ ρ_sub = a_minus_b + u32Limit)
    ∨
    (a_ge_b ≠ 0 ∧
      IsRangeChecked (rcBound F) a_minus_b ∧
      ρ_overflow = 0 ∧ ρ_sub = a_minus_b))

theorem sound_u32_overflowing_sub {a b ρ_overflow ρ_add : F}
  (h_auto : auto_spec_u32_overflowing_sub a b ρ_overflow ρ_add) :
  spec_u32_overflowing_sub a b ρ_overflow ρ_add := by
  rintro na ⟨hna, rfl⟩ nb ⟨hnb, rfl⟩
  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound
  rcases h_auto with ⟨_, _, rfl, ⟨rfl, _, rfl, ⟨m, h₁, h₂⟩, rfl, rfl⟩ | ⟨_, ⟨m, h₁, h₂⟩, rfl, rfl⟩⟩
  · have hm_u128 := lt_of_lt_of_le h₁ h_rcBound
    use m + u32Limit - u128Limit
    constructor
    · constructor
      · exact add_sub_lt u32Limit_pos hm_u128
      have hm₂ : u128Limit ≤ m + u32Limit := by
        rw [add_comm, ← (add_left_inj (u32Limit : F)), add_assoc] at h₂
        conv at h₂ => lhs; rhs; rw [add_comm]
        rw [← add_sub_assoc, ← cast_add, ← cast_sub, ← cast_add, ← cast_add] at h₂
        rw [PRIME.nat_coe_field_inj (add_lt_PRIME_of_lt hm_u128 u32Limit_lt_u128Limit) _ h₂.symm]
        · exact le_self_add
        · apply add_lt_PRIME_of_le (le_refl _)
          have htemp₁ : u32Limit + na - nb ≤ u32Limit + na := by exact Nat.sub_le _ _
          have htemp₂ : u32Limit + na ≤ u32Limit + u32Limit := le_of_lt ((add_lt_add_iff_left _).mpr hna)
          have htemp₃ : u32Limit + u32Limit ≤ u128Limit := by unfold u32Limit u128Limit; norm_num1
          exact le_trans (le_trans htemp₁ htemp₂) htemp₃
        · exact le_trans (le_of_lt hnb) (le_self_add)
      rw [← eq_sub_iff_add_eq] at h₂
      rw [h₂, add_comm_sub, ← add_sub_assoc, cast_sub hm₂, cast_add]
    exact Or.inl ⟨rfl, rfl⟩
  · use m
    constructor
    · constructor
      · apply lt_of_le_of_lt _ hna
        apply le_trans (le_add_right m nb)
        rw [sub_eq_iff_eq_add, ← cast_add] at h₂
        rw [PRIME.nat_coe_field_inj _ (lt_trans hna u32Limit_lt_PRIME) h₂.symm]
        exact add_lt_PRIME_of_lt (lt_of_lt_of_le h₁ h_rcBound)
          (lt_trans hnb u32Limit_lt_u128Limit)
      exact h₂
    exact Or.inr ⟨rfl, rfl⟩

end u32_overflowing_sub_soundness