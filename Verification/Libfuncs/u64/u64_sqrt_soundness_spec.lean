import Verification.Libfuncs.Common

namespace u64_sqrt_soundness
open Nat

variable {F : Type} [Field F] [PreludeHyps F]

@[reducible, inline] def sqrtAdjustment : ℕ := u128Limit - 2^125

lemma u128Limit_minus_sqrtAdjustment : u128Limit - sqrtAdjustment = 2^125 := by
  unfold u128Limit sqrtAdjustment; norm_num1

theorem sqrtAdjustment_lt_u128Limit : sqrtAdjustment < u128Limit := by
  unfold sqrtAdjustment u128Limit; norm_num1

def spec_u64_sqrt (a ρ_sqrt : F) : Prop := ∀ na, is_u64_of a na → is_u32_of ρ_sqrt na.sqrt

def auto_spec_u64_sqrt (a ρ_sqrt : F) : Prop :=
  ∃ ret_val : F,
  ∃ sqrt_adj : F, sqrt_adj = ret_val + sqrtAdjustment ∧
  ∃ lb : F, lb = a - (ret_val * ret_val) ∧
  ∃ ub : F, ub = (ret_val + ret_val) - lb ∧
  IsRangeChecked (rcBound F) ret_val ∧
  IsRangeChecked (rcBound F) sqrt_adj ∧
  IsRangeChecked (rcBound F) lb ∧
  IsRangeChecked (rcBound F) ub ∧
  ρ_sqrt = ret_val

lemma factoring (a : ℕ) : a + a + a * a + 1 = (a + 1) * (a + 1) := by ring

theorem sound_u64_sqrt {a ρ_sqrt : F}
  (h_auto : auto_spec_u64_sqrt a ρ_sqrt) : spec_u64_sqrt a ρ_sqrt := by
  rcases h_auto with ⟨_, _, rfl, _, rfl, _, rfl, h₁, h₂, h₃, h₄, rfl⟩
  have h_rc_bound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rc_bound
  rcases h₁ with ⟨ret_val, h_ret_val_lt, rfl⟩
  rcases h₂ with ⟨sqrt_adj, hadj_lt, h_sqrt_adj⟩
  rcases h₃ with ⟨lb, h_lb_lt, h_lb⟩
  rcases h₄ with ⟨ub, h_ub_lt, h_ub⟩
  rintro na ⟨hna_lt, rfl⟩
  constructor
  · rw [← u32Limit_squared_eq] at hna_lt
    exact Nat.sqrt_lt_of_lt_square hna_lt
  · have h_le : ret_val * ret_val ≤ na := by
      clear h_ub_lt h_ub ub
      rw [sub_eq_iff_eq_add, ← cast_mul, ← cast_add] at h_lb
      rw [PRIME.nat_coe_field_inj (lt_trans hna_lt u64Limit_lt_PRIME) _ h_lb]
      · exact le_add_self
      · rw [← cast_add] at h_sqrt_adj
        rw [← PRIME.nat_coe_field_inj _ _ h_sqrt_adj] at hadj_lt
        · have hbig := lt_tsub_iff_right.mpr (lt_of_lt_of_le hadj_lt h_rc_bound)
          rw [u128Limit_minus_sqrtAdjustment] at hbig
          apply lt_trans ((add_lt_add_iff_right _).mpr (lt_of_lt_of_le h_lb_lt h_rc_bound))
          apply lt_tsub_iff_left.mp
          apply lt_trans (mul_self_lt_mul_self hbig)
          · unfold PRIME u128Limit; norm_num1
        exact add_lt_PRIME_of_lt (lt_of_lt_of_le h_ret_val_lt h_rc_bound)
            sqrtAdjustment_lt_u128Limit
        exact lt_trans (lt_of_lt_of_le hadj_lt h_rc_bound) u128Limit_lt_PRIME
    have h_le' : ret_val ≤ na.sqrt := by
      have := sqrt_le_sqrt h_le
      rw [sqrt_eq] at this
      exact this
    have h_ge : ret_val ≥ na.sqrt := by
      clear h_le' h_le h_lb h_lb_lt lb
      rw [← cast_mul, ← cast_add, ← sub_add, sub_add_eq_add_sub,
        ← cast_add, sub_eq_iff_eq_add, ← cast_add] at h_ub
      have h_left_lt : ret_val + ret_val + ret_val * ret_val < PRIME := by
        · rw [← Nat.cast_add] at h_sqrt_adj
          have h₁ := add_lt_PRIME_of_lt (lt_of_lt_of_le h_ret_val_lt h_rc_bound)
              sqrtAdjustment_lt_u128Limit
          have h₂ := lt_trans (lt_of_lt_of_le hadj_lt h_rc_bound) u128Limit_lt_PRIME
          have := PRIME.nat_coe_field_inj h₁ h₂ h_sqrt_adj
          · rw [← this] at hadj_lt
            have : ret_val < u128Limit - sqrtAdjustment :=
              lt_tsub_iff_right.mpr (lt_of_lt_of_le hadj_lt h_rc_bound)
            rw [u128Limit_minus_sqrtAdjustment] at this
            have := Nat.add_lt_add (Nat.add_lt_add this this) (mul_self_lt_mul_self this)
            apply lt_trans this
            unfold PRIME
            norm_num1
      have h_right_lt : ub + na < PRIME := add_lt_PRIME_of_lt (lt_of_lt_of_le h_ub_lt h_rc_bound)
          (lt_trans hna_lt u64Limit_lt_u128Limit)
      have := PRIME.nat_coe_field_inj h_left_lt h_right_lt h_ub
      have h_le : na ≤ ub + na := le_add_self
      rw [← this] at h_le
      have := lt_succ_of_le h_le
      rw [succ_eq_add_one, factoring] at this
      exact le_of_lt_succ (sqrt_lt_of_lt_square this)
    rw [antisymm h_le' h_ge]

end u64_sqrt_soundness