import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_rhs_soundness_spec
import Verification.Libfuncs.bounded_int.bounded_int_div_rem_known_small_rhs_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open bounded_int_div_rem_known_small_rhs_code
open bounded_int_div_rem_known_small_rhs_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_bounded_int_div_rem_known_small_rhs
  -- arguments
  (range_check a b : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem bounded_int_div_rem_known_small_rhs_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 5))
  (htv_a : a = mem (σ.fp - 4))
  (htv_b : b = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    3 ≤ κ ∧ RcEnsures mem (rcBound F) 3 (mem (σ.fp - 5)) (mem (τ.ap - 3))
      (spec_bounded_int_div_rem_known_small_rhs κ range_check a b (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
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
  mkdef hl_bq : bq = mem (σ.ap + 2)
  have htv_bq : bq = mem (σ.ap + 2) := by
    exact hl_bq
  -- tempvar q
  mkdef hl_q : q = mem (σ.ap + 3)
  have htv_q : q = mem (σ.ap + 3) := by
    exact hl_q
  -- tempvar r
  mkdef hl_r : r = mem (σ.ap + 4)
  have htv_r : r = mem (σ.ap + 4) := by
    exact hl_r
  -- range check for r
  step_assert_eq hmem0 hmem with rc_r
  -- assert
  step_assert_eq hmem1 hmem, hmem2 hmem with ha1
  have a1 : r_plus_1 = r + one := by
    rw [htv_r_plus_1, htv_r, one] ; exact ha1
  -- assert
  step_assert_eq hmem3 hmem with ha3
  have a3 : b_minus_r_minus_1 = b - r_plus_1 := by
    rw [htv_b_minus_r_minus_1, htv_b, htv_r_plus_1, ha3, add_sub_cancel_right]
  -- range check for b_minus_r_minus_1
  step_assert_eq hmem4 hmem with rc_b_minus_r_minus_1
  -- range check for q
  step_assert_eq hmem5 hmem with rc_q
  -- assert
  step_assert_eq hmem6 hmem with ha6
  have a6 : bq = b * q := by
    rw [htv_bq, htv_b, htv_q] ; exact ha6
  -- assert
  step_assert_eq hmem7 hmem with ha7
  have a7 : a = bq + r := by
    rw [htv_a, htv_bq, htv_r] ; exact ha7
  -- return values
  --   range check return value
  step_assert_eq hmem8 hmem, hmem9 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 3
  -- have htv_range_check₁ : range_check₁ = ?h := by
  --   apply Eq.symm; apply Eq.trans ret_range_check₁
  --   simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem10 hmem with ret_q
  step_assert_eq hmem11 hmem with ret_r
  step_ret hmem12 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_bounded_int_div_rem_known_small_rhs _ range_check a b _ _ by
    apply sound_bounded_int_div_rem_known_small_rhs ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only r_plus_1
  use_only b_minus_r_minus_1
  use_only bq
  use_only q
  use_only r
  rc_app rc_h_range_check 0 htv_r rc_r
  use_only a1
  use_only a3
  rc_app rc_h_range_check 1 htv_b_minus_r_minus_1 rc_b_minus_r_minus_1
  rc_app rc_h_range_check 2 htv_q rc_q
  use_only a6
  use_only a7
  arith_simps
  constructor ; rw [htv_q] ; exact ret_q
  rw [htv_r] ; exact ret_r
  done
