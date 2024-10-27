import Verification.Libfuncs.u32.u32_sqrt_soundness_spec
import Verification.Libfuncs.u32.u32_sqrt_code

namespace u32_sqrt_soundness
open u32_sqrt_code

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)

theorem auto_sound_u32_sqrt
  -- arguments
  (range_check_ptr a : F)
  -- code is in memory at s.pc
  (hmem : MemAt mem u32_sqrt_code σ.pc)
  -- input arguments on the stack
  (_ : range_check_ptr = mem (σ.fp - 4))
  (hin_a : a = mem (σ.fp - 3)) :
  -- conclusion
  EnsuresRet mem σ fun κ τ =>
    ∃ μ ≤ κ, RcEnsures mem (rcBound F) μ (mem (σ.fp - 4)) (mem (τ.ap - 2))
      (spec_u32_sqrt a (mem (τ.ap - 1))) := by
  apply ensures_of_ensuresb
  intro νbound
  step_assert_eq hmem0 hmem, hmem1 hmem with h_adj   -- √a + adjustment
  step_assert_eq hmem2 hmem with h_ret_val_rc -- Range check for returned value
  step_assert_eq hmem3 hmem with h_adj_rc     -- Range check for √a + adjustment
  step_assert_eq hmem4 hmem with h_lb         -- ⌊√a⌋ * ⌊√a⌋ lower bound
  step_assert_eq hmem5 hmem with h_lb_diff    -- a - ⌊√a⌋ * ⌊√a⌋
  step_assert_eq hmem6 hmem with h_lb_diff_rc -- Range check the above value
  step_assert_eq hmem7 hmem with h_dbl        -- ⌊√a⌋ + ⌊√a⌋
  step_assert_eq hmem8 hmem with h_sum        -- ⌊√a⌋ + ⌊√a⌋ - (a - ⌊√a⌋ * ⌊√a⌋)
  step_assert_eq hmem9 hmem with h_sum_rc     -- Range check
  step_assert_eq hmem10 hmem, hmem11 hmem with h_new_rc_ptr -- Updated range check pointer
  step_assert_eq hmem12 hmem with h_ret_val       -- Return value
  step_ret hmem13 hmem
  step_done
  arith_simps
  simp only [true_and]
  use_only 4 + 0
  constructor
  · norm_num1
  constructor
  · arith_simps; exact h_new_rc_ptr
  intro h_range_check_ptr
  suffices auto_spec : auto_spec_u32_sqrt a _ by
    apply spec_u32_sqrt_of_auto_spec; apply auto_spec
  use_only mem (σ.ap + 5), mem σ.ap
  constructor
  · unfold sqrtAdjustment u128Limit; norm_num1; exact h_adj
  use_only mem (σ.ap + 2)
  constructor
  · rw [← sub_eq_iff_eq_add] at h_lb_diff
    rw [← h_lb_diff, hin_a, h_lb]
  use_only mem (σ.ap + 4)
  constructor
  · rw [← sub_eq_iff_eq_add] at h_sum
    rw [← h_sum, h_dbl]
  -- Now handle all the range checks
  have h₀ := h_range_check_ptr 0
  have h₁ := h_range_check_ptr 1
  have h₂ := h_range_check_ptr 2
  have h₃ := h_range_check_ptr 3
  simp at h₀ h₁ h₂ h₃
  exact ⟨h_ret_val_rc.symm ▸ h₀, h_adj_rc.symm ▸ h₁, h_lb_diff_rc.symm ▸ h₂,
    h_sum_rc.symm ▸ h₃, h_ret_val⟩

end u32_sqrt_soundness
