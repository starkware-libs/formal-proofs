import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u128.u128_safe_divmod_soundness_spec
import Verification.Libfuncs.u128.u128_safe_divmod_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u128_safe_divmod_known_small_lhs_code
open u128_safe_divmod_known_small_lhs_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u128_safe_divmod_known_small_lhs_VerifyBQ
  -- arguments
  (range_check a b b_or_q_bound_rc_value bq q r : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u128_safe_divmod_known_small_lhs_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a : a = mem (σ.fp - 4))
  (htv_b : b = mem (σ.fp - 3))
  (htv_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3))
  (htv_bq : bq = mem (σ.ap + 4))
  (htv_q : q = mem (σ.ap + 5))
  (htv_r : r = mem (σ.ap + 6))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 14, ap := σ.ap + 7, fp := σ.fp }
    (fun κ τ =>
    4 ≤ κ ∧ RcEnsures mem (rcBound F) 4 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (auto_spec_u128_safe_divmod_known_small_lhs_VerifyBQ κ range_check a b b_or_q_bound_rc_value bq q r (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- range check for b_or_q_bound_rc_value
  step_assert_eq hmem14 hmem with rc_b_or_q_bound_rc_value
  -- assert
  step_assert_eq hmem15 hmem with ha15
  have a15 : bq = b * q := by
    rw [htv_bq, htv_b, htv_q] ; exact ha15
  -- assert
  step_assert_eq hmem16 hmem with ha16
  have a16 : a = bq + r := by
    rw [htv_a, htv_bq, htv_r] ; exact ha16
  -- return values
  --   range check return value
  step_assert_eq hmem17 hmem, hmem18 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 4
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem19 hmem with ret_q
  step_assert_eq hmem20 hmem with ret_r
  step_ret hmem21 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  rc_app rc_h_range_check 3 htv_b_or_q_bound_rc_value rc_b_or_q_bound_rc_value
  use_only a15
  use_only a16
  arith_simps
  constructor ; rw [htv_q] ; exact ret_q
  rw [htv_r] ; exact ret_r
  done

theorem auto_sound_u128_safe_divmod_known_small_lhs_QIsSmall
  -- arguments
  (range_check a b b_or_q_bound_rc_value bq q r : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u128_safe_divmod_known_small_lhs_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a : a = mem (σ.fp - 4))
  (htv_b : b = mem (σ.fp - 3))
  (htv_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3))
  (htv_bq : bq = mem (σ.ap + 4))
  (htv_q : q = mem (σ.ap + 5))
  (htv_r : r = mem (σ.ap + 6))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 12, ap := σ.ap + 6, fp := σ.fp }
    (fun κ τ =>
    4 ≤ κ ∧ RcEnsures mem (rcBound F) 4 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (auto_spec_u128_safe_divmod_known_small_lhs_QIsSmall κ range_check a b b_or_q_bound_rc_value bq q r (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem12 hmem, hmem13 hmem with ha12
  have a12 : b_or_q_bound_rc_value = q + u128_bound_minus_limiter_bound := by
    rw [htv_b_or_q_bound_rc_value, htv_q, u128_bound_minus_limiter_bound] ; exact ha12
  arith_simps
  apply ensuresbRet_trans (auto_sound_u128_safe_divmod_known_small_lhs_VerifyBQ mem σ
    range_check a b b_or_q_bound_rc_value bq q r
    hmem
    htv_range_check
    htv_a
    htv_b
    htv_b_or_q_bound_rc_value
    htv_bq
    htv_q
    htv_r
    νbound)
  intros κ_VerifyBQ _ h_VerifyBQ
  rcases h_VerifyBQ with ⟨rc_m_le_VerifyBQ, hblk_range_check_ptr, h_VerifyBQ⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_VerifyBQ (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a12
  use_only κ_VerifyBQ
  apply h_VerifyBQ rc_h_range_check
  done

theorem auto_sound_u128_safe_divmod_known_small_lhs
  -- arguments
  (range_check a b : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u128_safe_divmod_known_small_lhs_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a : a = mem (σ.fp - 4))
  (htv_b : b = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    4 ≤ κ ∧ RcEnsures mem (rcBound F) 4 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_u128_safe_divmod_known_small_lhs κ range_check a b (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 5) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar r_plus_1
  mkdef hl_r_plus_1 : r_plus_1 = mem σ.ap
  have htv_r_plus_1 : r_plus_1 = mem σ.ap := by
    exact hl_r_plus_1
  -- tempvar b_minus_r_minus_1
  mkdef hl_b_minus_r_minus_1 : b_minus_r_minus_1 = mem (σ.ap + 1)
  have htv_b_minus_r_minus_1 : b_minus_r_minus_1 = mem (σ.ap + 1) := by
    exact hl_b_minus_r_minus_1
  -- tempvar bq
  mkdef hl_bq : bq = mem (σ.ap + 4)
  have htv_bq : bq = mem (σ.ap + 4) := by
    exact hl_bq
  -- tempvar q
  mkdef hl_q : q = mem (σ.ap + 5)
  have htv_q : q = mem (σ.ap + 5) := by
    exact hl_q
  -- tempvar r
  mkdef hl_r : r = mem (σ.ap + 6)
  have htv_r : r = mem (σ.ap + 6) := by
    exact hl_r
  -- range check for q
  step_assert_eq hmem0 hmem with rc_q
  -- range check for r
  step_assert_eq hmem1 hmem with rc_r
  -- assert
  step_assert_eq hmem2 hmem, hmem3 hmem with ha2
  have a2 : r_plus_1 = r + one := by
    rw [htv_r_plus_1, htv_r, one] ; exact ha2
  -- assert
  step_assert_eq hmem4 hmem with ha4
  have a4 : b_minus_r_minus_1 = b - r_plus_1 := by
    rw [htv_b_minus_r_minus_1, htv_b, htv_r_plus_1, ha4, add_sub_cancel_right]
  -- range check for b_minus_r_minus_1
  step_assert_eq hmem5 hmem with rc_b_minus_r_minus_1
  -- tempvar q_is_small
  mkdef hl_q_is_small : q_is_small = mem (σ.ap + 2)
  have htv_q_is_small : q_is_small = mem (σ.ap + 2) := by
    exact hl_q_is_small
  -- jump to QIsSmall if q_is_small != 0
  step_jnz hmem6 hmem, hmem7 hmem with hcond6 hcond6
  ·
    -- q_is_small = 0
    have a6 : q_is_small = 0 := by simp only [htv_q_is_small]; exact hcond6
    -- tempvar b_or_q_bound_rc_value
    mkdef hl_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3)
    have htv_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3) := by
      exact hl_b_or_q_bound_rc_value
    -- assert
    step_assert_eq hmem8 hmem, hmem9 hmem with ha8
    have a8 : b_or_q_bound_rc_value = b + u128_bound_minus_limiter_bound := by
      rw [htv_b_or_q_bound_rc_value, htv_b, u128_bound_minus_limiter_bound] ; exact ha8
    step_jump_imm hmem10 hmem, hmem11 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u128_safe_divmod_known_small_lhs_VerifyBQ mem σ
      range_check a b b_or_q_bound_rc_value bq q r
      hmem
      htv_range_check
      htv_a
      htv_b
      htv_b_or_q_bound_rc_value
      htv_bq
      htv_q
      htv_r
      νbound)
    intros κ_VerifyBQ _ h_VerifyBQ
    rcases h_VerifyBQ with ⟨rc_m_le_VerifyBQ, hblk_range_check_ptr, h_VerifyBQ⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_VerifyBQ (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u128_safe_divmod_known_small_lhs _ range_check a b _ _ by
      apply sound_u128_safe_divmod_known_small_lhs ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only r_plus_1
    use_only b_minus_r_minus_1
    use_only bq
    use_only q
    use_only r
    rc_app rc_h_range_check 0 htv_q rc_q
    rc_app rc_h_range_check 1 htv_r rc_r
    use_only a2
    use_only a4
    rc_app rc_h_range_check 2 htv_b_minus_r_minus_1 rc_b_minus_r_minus_1
    use_only q_is_small
    left
    use_only a6
    use_only b_or_q_bound_rc_value
    use_only a8
    use_only κ_VerifyBQ
    apply h_VerifyBQ rc_h_range_check
    done
  -- q_is_small ≠ 0
  have a6 : q_is_small ≠ 0 := by simp only [htv_q_is_small]; exact hcond6
  -- tempvar b_or_q_bound_rc_value
  mkdef hl_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3)
  have htv_b_or_q_bound_rc_value : b_or_q_bound_rc_value = mem (σ.ap + 3) := by
    exact hl_b_or_q_bound_rc_value
  arith_simps
  apply ensuresbRet_trans (auto_sound_u128_safe_divmod_known_small_lhs_QIsSmall mem σ
    range_check a b b_or_q_bound_rc_value bq q r
    hmem
    htv_range_check
    htv_a
    htv_b
    htv_b_or_q_bound_rc_value
    htv_bq
    htv_q
    htv_r
    νbound)
  intros κ_QIsSmall _ h_QIsSmall
  rcases h_QIsSmall with ⟨rc_m_le_QIsSmall, hblk_range_check_ptr, h_QIsSmall⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_QIsSmall (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u128_safe_divmod_known_small_lhs _ range_check a b _ _ by
    apply sound_u128_safe_divmod_known_small_lhs ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only r_plus_1
  use_only b_minus_r_minus_1
  use_only bq
  use_only q
  use_only r
  rc_app rc_h_range_check 0 htv_q rc_q
  rc_app rc_h_range_check 1 htv_r rc_r
  use_only a2
  use_only a4
  rc_app rc_h_range_check 2 htv_b_minus_r_minus_1 rc_b_minus_r_minus_1
  use_only q_is_small
  right
  use_only a6
  use_only b_or_q_bound_rc_value
  use_only κ_QIsSmall
  apply h_QIsSmall rc_h_range_check
  done
