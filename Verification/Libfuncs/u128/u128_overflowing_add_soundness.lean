import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u128.u128_overflowing_add_soundness_spec
import Verification.Libfuncs.u128.u128_overflowing_add_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u128_overflowing_add_code
open u128_overflowing_add_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u128_overflowing_add_NoOverflow
  -- arguments
  (range_check a_plus_b : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u128_overflowing_add_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a_plus_b : a_plus_b = mem (σ.ap + 1))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 8, ap := σ.ap + 2, fp := σ.fp }
    (fun κ τ =>
    1 ≤ κ ∧ RcEnsures mem (rcBound F) 1 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (auto_spec_u128_overflowing_add_NoOverflow κ range_check a_plus_b (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- range check for a_plus_b
  step_assert_eq hmem8 hmem with rc_a_plus_b
  -- return values
  step_advance_ap hmem9 hmem, hmem10 hmem
  --   range check return value
  step_assert_eq hmem11 hmem, hmem12 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 1
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem13 hmem, hmem14 hmem with ret_branch_id
  step_assert_eq hmem15 hmem with ret_a_plus_b
  step_ret hmem16 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  rc_app rc_h_range_check 0 htv_a_plus_b rc_a_plus_b
  arith_simps
  use_only ret_branch_id
  rw [htv_a_plus_b] ; exact ret_a_plus_b
  done

theorem auto_sound_u128_overflowing_add
  -- arguments
  (range_check a b : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u128_overflowing_add_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a : a = mem (σ.fp - 4))
  (htv_b : b = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    1 ≤ κ ∧ RcEnsures mem (rcBound F) 1 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_u128_overflowing_add κ range_check a b (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 5) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar no_overflow
  mkdef hl_no_overflow : no_overflow = mem σ.ap
  have htv_no_overflow : no_overflow = mem σ.ap := by
    exact hl_no_overflow
  -- tempvar a_plus_b
  step_assert_eq hmem0 hmem with tv_a_plus_b
  mkdef hl_a_plus_b : a_plus_b = a + b
  have htv_a_plus_b : a_plus_b = mem (σ.ap + 1) := by
    rw [hl_a_plus_b, htv_a, htv_b, tv_a_plus_b]
  -- jump to NoOverflow if no_overflow != 0
  step_jnz hmem1 hmem, hmem2 hmem with hcond1 hcond1
  ·
    -- no_overflow = 0
    have a1 : no_overflow = 0 := by simp only [htv_no_overflow]; exact hcond1
    -- tempvar wrapping_a_plus_b
    step_assert_eq hmem3 hmem, hmem4 hmem with tv_wrapping_a_plus_b
    mkdef hl_wrapping_a_plus_b : wrapping_a_plus_b = a_plus_b - u128_limit
    have htv_wrapping_a_plus_b : wrapping_a_plus_b = mem (σ.ap + 2) := by
      rw [hl_wrapping_a_plus_b, htv_a_plus_b, u128_limit, tv_wrapping_a_plus_b, add_sub_cancel_right]
    -- range check for wrapping_a_plus_b
    step_assert_eq hmem5 hmem with rc_wrapping_a_plus_b
    step_jump_imm hmem6 hmem, hmem7 hmem
    -- return values
    --   range check return value
    step_assert_eq hmem17 hmem, hmem18 hmem with ret_range_check₁
    mkdef hl_range_check₁ : range_check₁ = range_check + 1
    let htv_range_check₁ : range_check₁ = _ := by
      apply Eq.symm; apply Eq.trans ret_range_check₁
      simp only [hl_range_check₁, htv_range_check]
    step_assert_eq hmem19 hmem, hmem20 hmem with ret_branch_id
    step_assert_eq hmem21 hmem with ret_a_plus_b
    step_ret hmem22 hmem
    step_done
    use_only rfl, rfl
    -- range check condition
    constructor
    norm_num1
    constructor
    · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u128_overflowing_add _ range_check a b _ _ by
      apply sound_u128_overflowing_add ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only no_overflow
    use_only a_plus_b, hl_a_plus_b
    left
    use_only a1
    use_only wrapping_a_plus_b, hl_wrapping_a_plus_b
    rc_app rc_h_range_check 0 htv_wrapping_a_plus_b rc_wrapping_a_plus_b
    arith_simps
    use_only ret_branch_id
    rw [htv_wrapping_a_plus_b] ; exact ret_a_plus_b
    done
  -- no_overflow ≠ 0
  have a1 : no_overflow ≠ 0 := by simp only [htv_no_overflow]; exact hcond1
  arith_simps
  apply ensuresbRet_trans (auto_sound_u128_overflowing_add_NoOverflow mem σ
    range_check a_plus_b
    hmem
    htv_range_check
    htv_a_plus_b
    νbound)
  intros κ_NoOverflow _ h_NoOverflow
  rcases h_NoOverflow with ⟨rc_m_le_NoOverflow, hblk_range_check_ptr, h_NoOverflow⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_NoOverflow (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u128_overflowing_add _ range_check a b _ _ by
    apply sound_u128_overflowing_add ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only no_overflow
  use_only a_plus_b, hl_a_plus_b
  right
  use_only a1
  use_only κ_NoOverflow
  apply h_NoOverflow rc_h_range_check
  done
