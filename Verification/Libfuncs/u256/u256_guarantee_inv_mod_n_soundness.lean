import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u256.u256_guarantee_inv_mod_n_soundness_spec
import Verification.Libfuncs.u256.u256_guarantee_inv_mod_n_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

open u256_guarantee_inv_mod_n_code
open u256_guarantee_inv_mod_n_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F] (mem : F → F) (σ : RegisterState F)


theorem auto_sound_u256_guarantee_inv_mod_n_Done
  -- arguments
  (range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_r0 : r0 = mem (σ.ap + 2))
  (htv_r1 : r1 = mem (σ.ap + 3))
  (htv_k0 : k0 = mem (σ.ap + 4))
  (htv_k1 : k1 = mem (σ.ap + 5))
  (htv_r0b0_low : r0b0_low = mem (σ.ap + 9))
  (htv_r0b0_high : r0b0_high = mem (σ.ap + 10))
  (htv_r0b1_low : r0b1_low = mem (σ.ap + 11))
  (htv_r0b1_high : r0b1_high = mem (σ.ap + 12))
  (htv_r1b0_low : r1b0_low = mem (σ.ap + 13))
  (htv_r1b0_high : r1b0_high = mem (σ.ap + 14))
  (htv_r1b1_low : r1b1_low = mem (σ.ap + 15))
  (htv_r1b1_high : r1b1_high = mem (σ.ap + 16))
  (htv_n0k0_low : n0k0_low = mem (σ.ap + 17))
  (htv_n0k0_high : n0k0_high = mem (σ.ap + 18))
  (htv_n0k1_low : n0k1_low = mem (σ.ap + 19))
  (htv_n0k1_high : n0k1_high = mem (σ.ap + 20))
  (htv_n1k0_low : n1k0_low = mem (σ.ap + 21))
  (htv_n1k0_high : n1k0_high = mem (σ.ap + 22))
  (htv_n1k1_low : n1k1_low = mem (σ.ap + 23))
  (htv_n1k1_high : n1k1_high = mem (σ.ap + 24))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 102, ap := σ.ap + 46, fp := σ.fp }
    (fun κ τ =>
    9 ≤ κ ∧ RcEnsures mem (rcBound F) 9 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_Done κ range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- return values
  --   range check return value
  step_assert_eq hmem102 hmem, hmem103 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 9
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem104 hmem, hmem105 hmem with ret_branch_id
  step_assert_eq hmem106 hmem with ret_r0
  step_assert_eq hmem107 hmem with ret_r1
  step_assert_eq hmem108 hmem with ret_r0₁
  step_assert_eq hmem109 hmem with ret_b0
  step_assert_eq hmem110 hmem with ret_r0b0_high
  step_assert_eq hmem111 hmem with ret_r0b0_low
  step_assert_eq hmem112 hmem with ret_r0₂
  step_assert_eq hmem113 hmem with ret_b1
  step_assert_eq hmem114 hmem with ret_r0b1_high
  step_assert_eq hmem115 hmem with ret_r0b1_low
  step_assert_eq hmem116 hmem with ret_r1₁
  step_assert_eq hmem117 hmem with ret_b0₁
  step_assert_eq hmem118 hmem with ret_r1b0_high
  step_assert_eq hmem119 hmem with ret_r1b0_low
  step_assert_eq hmem120 hmem with ret_r1₂
  step_assert_eq hmem121 hmem with ret_b1₁
  step_assert_eq hmem122 hmem with ret_r1b1_high
  step_assert_eq hmem123 hmem with ret_r1b1_low
  step_assert_eq hmem124 hmem with ret_n0
  step_assert_eq hmem125 hmem with ret_k0
  step_assert_eq hmem126 hmem with ret_n0k0_high
  step_assert_eq hmem127 hmem with ret_n0k0_low
  step_assert_eq hmem128 hmem with ret_n0₁
  step_assert_eq hmem129 hmem with ret_k1
  step_assert_eq hmem130 hmem with ret_n0k1_high
  step_assert_eq hmem131 hmem with ret_n0k1_low
  step_assert_eq hmem132 hmem with ret_n1_or_g0
  step_assert_eq hmem133 hmem with ret_k0_or_s0
  step_assert_eq hmem134 hmem with ret_n1k0_high_or_g0s0_high
  step_assert_eq hmem135 hmem with ret_n1k0_low_or_g0s0_low
  step_assert_eq hmem136 hmem with ret_n1_or_g0₁
  step_assert_eq hmem137 hmem with ret_k1_or_t0
  step_assert_eq hmem138 hmem with ret_n1k1_high_or_g0t0_high
  step_assert_eq hmem139 hmem with ret_n1k1_low_or_g0t0_low
  step_ret hmem140 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  arith_simps
  use_only ret_branch_id
  constructor ; rw [htv_r0] ; exact ret_r0
  constructor ; rw [htv_r1] ; exact ret_r1
  constructor ; rw [htv_r0] ; exact ret_r0₁
  constructor ; rw [htv_b0] ; exact ret_b0
  constructor ; rw [htv_r0b0_high] ; exact ret_r0b0_high
  constructor ; rw [htv_r0b0_low] ; exact ret_r0b0_low
  constructor ; rw [htv_r0] ; exact ret_r0₂
  constructor ; rw [htv_b1] ; exact ret_b1
  constructor ; rw [htv_r0b1_high] ; exact ret_r0b1_high
  constructor ; rw [htv_r0b1_low] ; exact ret_r0b1_low
  constructor ; rw [htv_r1] ; exact ret_r1₁
  constructor ; rw [htv_b0] ; exact ret_b0₁
  constructor ; rw [htv_r1b0_high] ; exact ret_r1b0_high
  constructor ; rw [htv_r1b0_low] ; exact ret_r1b0_low
  constructor ; rw [htv_r1] ; exact ret_r1₂
  constructor ; rw [htv_b1] ; exact ret_b1₁
  constructor ; rw [htv_r1b1_high] ; exact ret_r1b1_high
  constructor ; rw [htv_r1b1_low] ; exact ret_r1b1_low
  constructor ; rw [htv_n0] ; exact ret_n0
  constructor ; rw [htv_k0] ; exact ret_k0
  constructor ; rw [htv_n0k0_high] ; exact ret_n0k0_high
  constructor ; rw [htv_n0k0_low] ; exact ret_n0k0_low
  constructor ; rw [htv_n0] ; exact ret_n0₁
  constructor ; rw [htv_k1] ; exact ret_k1
  constructor ; rw [htv_n0k1_high] ; exact ret_n0k1_high
  constructor ; rw [htv_n0k1_low] ; exact ret_n0k1_low
  constructor ; rw [htv_n1] ; exact ret_n1_or_g0
  constructor ; rw [htv_k0] ; exact ret_k0_or_s0
  constructor ; rw [htv_n1k0_high] ; exact ret_n1k0_high_or_g0s0_high
  constructor ; rw [htv_n1k0_low] ; exact ret_n1k0_low_or_g0s0_low
  constructor ; rw [htv_n1] ; exact ret_n1_or_g0₁
  constructor ; rw [htv_k1] ; exact ret_k1_or_t0
  constructor ; rw [htv_n1k1_high] ; exact ret_n1k1_high_or_g0t0_high
  rw [htv_n1k1_low] ; exact ret_n1k1_low_or_g0t0_low
  done

theorem auto_sound_u256_guarantee_inv_mod_n_MERGE
  -- arguments
  (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_g0s0_low : g0s0_low = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_g0t0_low : g0t0_low = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0 : g0 = mem σ.ap)
  (htv_s0 : s0 = mem (σ.ap + 2))
  (htv_t0 : t0 = mem (σ.ap + 4))
  (htv_g0s0_high : g0s0_high = mem (σ.ap + 7))
  (htv_g0t0_high : g0t0_high = mem (σ.ap + 8))
  (htv_gs1 : gs1 = mem (σ.ap + 9))
  (htv_gt1 : gt1 = mem (σ.ap + 10))
  (htv_smalls_sum : smalls_sum = mem (σ.ap + 11))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 95, ap := σ.ap + 13, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_MERGE κ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar smalls_sum_fixed
  step_assert_eq hmem95 hmem, hmem96 hmem with tv_smalls_sum_fixed
  mkdef hl_smalls_sum_fixed : smalls_sum_fixed = smalls_sum + u128_bound_minus_u65_bound
  have htv_smalls_sum_fixed : smalls_sum_fixed = mem (σ.ap + 13) := by
    rw [hl_smalls_sum_fixed, htv_smalls_sum, u128_bound_minus_u65_bound, tv_smalls_sum_fixed]
  -- range check for smalls_sum_fixed
  step_assert_eq hmem97 hmem with rc_smalls_sum_fixed
  -- assert
  step_assert_eq hmem98 hmem with ha98
  have a98 : b1 = gs1 + g0s0_high := by
    rw [htv_b1, htv_gs1, htv_g0s0_high] ; exact ha98
  -- assert
  step_assert_eq hmem99 hmem with ha99
  have a99 : n1 = gt1 + g0t0_high := by
    rw [htv_n1, htv_gt1, htv_g0t0_high] ; exact ha99
  step_jump_imm hmem100 hmem, hmem101 hmem
  -- return values
  step_advance_ap hmem141 hmem, hmem142 hmem
  --   range check return value
  step_assert_eq hmem143 hmem, hmem144 hmem with ret_range_check₁
  mkdef hl_range_check₁ : range_check₁ = range_check + 7
  let htv_range_check₁ : range_check₁ = _ := by
    apply Eq.symm; apply Eq.trans ret_range_check₁
    simp only [hl_range_check₁, htv_range_check]
  step_assert_eq hmem145 hmem, hmem146 hmem with ret_branch_id
  step_assert_eq hmem147 hmem, hmem148 hmem with ret_r0
  step_assert_eq hmem149 hmem, hmem150 hmem with ret_r1
  step_assert_eq hmem151 hmem, hmem152 hmem with ret_r0₁
  step_assert_eq hmem153 hmem, hmem154 hmem with ret_b0
  step_assert_eq hmem155 hmem, hmem156 hmem with ret_r0b0_high
  step_assert_eq hmem157 hmem, hmem158 hmem with ret_r0b0_low
  step_assert_eq hmem159 hmem, hmem160 hmem with ret_r0₂
  step_assert_eq hmem161 hmem, hmem162 hmem with ret_b1
  step_assert_eq hmem163 hmem, hmem164 hmem with ret_r0b1_high
  step_assert_eq hmem165 hmem, hmem166 hmem with ret_r0b1_low
  step_assert_eq hmem167 hmem, hmem168 hmem with ret_r1₁
  step_assert_eq hmem169 hmem, hmem170 hmem with ret_b0₁
  step_assert_eq hmem171 hmem, hmem172 hmem with ret_r1b0_high
  step_assert_eq hmem173 hmem, hmem174 hmem with ret_r1b0_low
  step_assert_eq hmem175 hmem, hmem176 hmem with ret_r1₂
  step_assert_eq hmem177 hmem, hmem178 hmem with ret_b1₁
  step_assert_eq hmem179 hmem, hmem180 hmem with ret_r1b1_high
  step_assert_eq hmem181 hmem, hmem182 hmem with ret_r1b1_low
  step_assert_eq hmem183 hmem, hmem184 hmem with ret_n0
  step_assert_eq hmem185 hmem, hmem186 hmem with ret_k0
  step_assert_eq hmem187 hmem, hmem188 hmem with ret_n0k0_high
  step_assert_eq hmem189 hmem, hmem190 hmem with ret_n0k0_low
  step_assert_eq hmem191 hmem, hmem192 hmem with ret_n0₁
  step_assert_eq hmem193 hmem, hmem194 hmem with ret_k1
  step_assert_eq hmem195 hmem, hmem196 hmem with ret_n0k1_high
  step_assert_eq hmem197 hmem, hmem198 hmem with ret_n0k1_low
  step_assert_eq hmem199 hmem with ret_n1_or_g0
  step_assert_eq hmem200 hmem with ret_k0_or_s0
  step_assert_eq hmem201 hmem with ret_n1k0_high_or_g0s0_high
  step_assert_eq hmem202 hmem with ret_n1k0_low_or_g0s0_low
  step_assert_eq hmem203 hmem with ret_n1_or_g0₁
  step_assert_eq hmem204 hmem with ret_k1_or_t0
  step_assert_eq hmem205 hmem with ret_n1k1_high_or_g0t0_high
  step_assert_eq hmem206 hmem with ret_n1k1_low_or_g0t0_low
  step_ret hmem207 hmem
  step_done
  use_only rfl, rfl
  -- range check condition
  constructor
  norm_num1
  constructor
  · arith_simps ; rw [ret_range_check₁] ; try { norm_cast }
  intro rc_h_range_check
  use_only smalls_sum_fixed, hl_smalls_sum_fixed
  rc_app rc_h_range_check 6 htv_smalls_sum_fixed rc_smalls_sum_fixed

  use_only a98
  use_only a99
  arith_simps
  use_only ret_branch_id
  constructor ; rw [htv_g0] ; exact ret_n1_or_g0
  constructor ; rw [htv_s0] ; exact ret_k0_or_s0
  constructor ; rw [htv_g0s0_high] ; exact ret_n1k0_high_or_g0s0_high
  constructor ; rw [htv_g0s0_low] ; exact ret_n1k0_low_or_g0s0_low
  constructor ; rw [htv_g0] ; exact ret_n1_or_g0₁
  constructor ; rw [htv_t0] ; exact ret_k1_or_t0
  constructor ; rw [htv_g0t0_high] ; exact ret_n1k1_high_or_g0t0_high
  rw [htv_g0t0_low] ; exact ret_n1k1_low_or_g0t0_low
  done

theorem auto_sound_u256_guarantee_inv_mod_n_G1IsSmall
  -- arguments
  (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_g0s0_low : g0s0_low = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_g0t0_low : g0t0_low = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0 : g0 = mem σ.ap)
  (htv_g1 : g1 = mem (σ.ap + 1))
  (htv_s0 : s0 = mem (σ.ap + 2))
  (htv_t0 : t0 = mem (σ.ap + 4))
  (htv_g0s0_high : g0s0_high = mem (σ.ap + 7))
  (htv_g0t0_high : g0t0_high = mem (σ.ap + 8))
  (htv_gs1 : gs1 = mem (σ.ap + 9))
  (htv_gt1 : gt1 = mem (σ.ap + 10))
  (htv_smalls_sum : smalls_sum = mem (σ.ap + 11))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 94, ap := σ.ap + 13, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_G1IsSmall κ range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem94 hmem with ha94
  have a94 : smalls_sum = g1 := by
    rw [htv_smalls_sum, htv_g1] ; exact ha94
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_MERGE mem σ
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
    hmem
    htv_range_check
    htv_g0s0_low
    htv_b1
    htv_g0t0_low
    htv_n1
    htv_g0
    htv_s0
    htv_t0
    htv_g0s0_high
    htv_g0t0_high
    htv_gs1
    htv_gt1
    htv_smalls_sum
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a94
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO
  -- arguments
  (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_g0s0_low : g0s0_low = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_g0t0_low : g0t0_low = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0 : g0 = mem σ.ap)
  (htv_g1 : g1 = mem (σ.ap + 1))
  (htv_s0 : s0 = mem (σ.ap + 2))
  (htv_s1 : s1 = mem (σ.ap + 3))
  (htv_t0 : t0 = mem (σ.ap + 4))
  (htv_t1 : t1 = mem (σ.ap + 5))
  (htv_g0s0_high : g0s0_high = mem (σ.ap + 7))
  (htv_g0t0_high : g0t0_high = mem (σ.ap + 8))
  (htv_gs1 : gs1 = mem (σ.ap + 9))
  (htv_gt1 : gt1 = mem (σ.ap + 10))
  (htv_smalls_sum : smalls_sum = mem (σ.ap + 11))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 83, ap := σ.ap + 8, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO κ range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem83 hmem with ha83
  have a83 : gs1 = s0 * g1 := by
    rw [htv_gs1, htv_s0, htv_g1] ; exact ha83
  -- assert
  step_assert_eq hmem84 hmem with ha84
  have a84 : gt1 = t0 * g1 := by
    rw [htv_gt1, htv_t0, htv_g1] ; exact ha84
  -- assert
  step_assert_eq hmem85 hmem, hmem86 hmem with ha85
  have a85 : s1 = zero := by
    rw [htv_s1, zero] ; exact ha85
  -- assert
  step_assert_eq hmem87 hmem, hmem88 hmem with ha87
  have a87 : t1 = zero := by
    rw [htv_t1, zero] ; exact ha87
  -- tempvar g1_is_small
  mkdef hl_g1_is_small : g1_is_small = mem (σ.ap + 12)
  have htv_g1_is_small : g1_is_small = mem (σ.ap + 12) := by
    exact hl_g1_is_small
  -- jump to G1IsSmall if g1_is_small != 0
  step_jnz hmem89 hmem, hmem90 hmem with hcond89 hcond89
  ·
    -- g1_is_small = 0
    have a89 : g1_is_small = 0 := by simp only [htv_g1_is_small]; exact hcond89
    -- assert
    step_assert_eq hmem91 hmem with ha91
    have a91 : smalls_sum = s0 + t0 := by
      rw [htv_smalls_sum, htv_s0, htv_t0] ; exact ha91
    step_jump_imm hmem92 hmem, hmem93 hmem
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_MERGE mem σ
      range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
      hmem
      htv_range_check
      htv_g0s0_low
      htv_b1
      htv_g0t0_low
      htv_n1
      htv_g0
      htv_s0
      htv_t0
      htv_g0s0_high
      htv_g0t0_high
      htv_gs1
      htv_gt1
      htv_smalls_sum
      νbound)
    intros κ_MERGE _ h_MERGE
    rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only a83
    use_only a84
    use_only a85
    use_only a87
    use_only g1_is_small
    left
    use_only a89
    use_only a91
    use_only κ_MERGE
    apply h_MERGE rc_h_range_check
    done
  -- g1_is_small ≠ 0
  have a89 : g1_is_small ≠ 0 := by simp only [htv_g1_is_small]; exact hcond89
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_G1IsSmall mem σ
    range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
    hmem
    htv_range_check
    htv_g0s0_low
    htv_b1
    htv_g0t0_low
    htv_n1
    htv_g0
    htv_g1
    htv_s0
    htv_t0
    htv_g0s0_high
    htv_g0t0_high
    htv_gs1
    htv_gt1
    htv_smalls_sum
    νbound)
  intros κ_G1IsSmall _ h_G1IsSmall
  rcases h_G1IsSmall with ⟨rc_m_le_G1IsSmall, hblk_range_check_ptr, h_G1IsSmall⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_G1IsSmall (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a83
  use_only a84
  use_only a85
  use_only a87
  use_only g1_is_small
  right
  use_only a89
  use_only κ_G1IsSmall
  apply h_G1IsSmall rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_G0IsSmall
  -- arguments
  (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_g0s0_low : g0s0_low = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_g0t0_low : g0t0_low = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0 : g0 = mem σ.ap)
  (htv_s0 : s0 = mem (σ.ap + 2))
  (htv_t0 : t0 = mem (σ.ap + 4))
  (htv_g0s0_high : g0s0_high = mem (σ.ap + 7))
  (htv_g0t0_high : g0t0_high = mem (σ.ap + 8))
  (htv_gs1 : gs1 = mem (σ.ap + 9))
  (htv_gt1 : gt1 = mem (σ.ap + 10))
  (htv_smalls_sum : smalls_sum = mem (σ.ap + 11))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 80, ap := σ.ap + 11, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_G0IsSmall κ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- assert
  step_assert_eq hmem80 hmem with ha80
  have a80 : smalls_sum = g0 := by
    rw [htv_smalls_sum, htv_g0] ; exact ha80
  step_jump_imm hmem81 hmem, hmem82 hmem
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_MERGE mem σ
    range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
    hmem
    htv_range_check
    htv_g0s0_low
    htv_b1
    htv_g0t0_low
    htv_n1
    htv_g0
    htv_s0
    htv_t0
    htv_g0s0_high
    htv_g0t0_high
    htv_gs1
    htv_gt1
    htv_smalls_sum
    νbound)
  intros κ_MERGE _ h_MERGE
  rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only a80
  use_only κ_MERGE
  apply h_MERGE rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_GIsValid
  -- arguments
  (range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0 : g0 = mem σ.ap)
  (htv_g1 : g1 = mem (σ.ap + 1))
  (htv_s0 : s0 = mem (σ.ap + 2))
  (htv_s1 : s1 = mem (σ.ap + 3))
  (htv_t0 : t0 = mem (σ.ap + 4))
  (htv_t1 : t1 = mem (σ.ap + 5))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 71, ap := σ.ap + 7, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_GIsValid κ range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- let
  mkdef hl_g0s0_low : g0s0_low = b0
  have htv_g0s0_low : g0s0_low = mem (σ.fp - 6) := by
    rw [hl_g0s0_low, htv_b0]
  -- tempvar g0s0_high
  mkdef hl_g0s0_high : g0s0_high = mem (σ.ap + 7)
  have htv_g0s0_high : g0s0_high = mem (σ.ap + 7) := by
    exact hl_g0s0_high
  -- let
  mkdef hl_g0t0_low : g0t0_low = n0
  have htv_g0t0_low : g0t0_low = mem (σ.fp - 4) := by
    rw [hl_g0t0_low, htv_n0]
  -- tempvar g0t0_high
  mkdef hl_g0t0_high : g0t0_high = mem (σ.ap + 8)
  have htv_g0t0_high : g0t0_high = mem (σ.ap + 8) := by
    exact hl_g0t0_high
  -- tempvar gs1
  mkdef hl_gs1 : gs1 = mem (σ.ap + 9)
  have htv_gs1 : gs1 = mem (σ.ap + 9) := by
    exact hl_gs1
  -- tempvar gt1
  mkdef hl_gt1 : gt1 = mem (σ.ap + 10)
  have htv_gt1 : gt1 = mem (σ.ap + 10) := by
    exact hl_gt1
  -- tempvar smalls_sum
  mkdef hl_smalls_sum : smalls_sum = mem (σ.ap + 11)
  have htv_smalls_sum : smalls_sum = mem (σ.ap + 11) := by
    exact hl_smalls_sum
  -- jump to S1_AND_T1_EQ_ZERO if g1 != 0
  step_jnz hmem71 hmem, hmem72 hmem with hcond71 hcond71
  ·
    -- g1 = 0
    have a71 : g1 = 0 := by simp only [htv_g1]; exact hcond71
    -- assert
    step_assert_eq hmem73 hmem with ha73
    have a73 : gs1 = s1 * g0 := by
      rw [htv_gs1, htv_s1, htv_g0] ; exact ha73
    -- assert
    step_assert_eq hmem74 hmem with ha74
    have a74 : gt1 = t1 * g0 := by
      rw [htv_gt1, htv_t1, htv_g0] ; exact ha74
    -- tempvar g0_is_small
    mkdef hl_g0_is_small : g0_is_small = mem (σ.ap + 12)
    have htv_g0_is_small : g0_is_small = mem (σ.ap + 12) := by
      exact hl_g0_is_small
    -- jump to G0IsSmall if g0_is_small != 0
    step_jnz hmem75 hmem, hmem76 hmem with hcond75 hcond75
    ·
      -- g0_is_small = 0
      have a75 : g0_is_small = 0 := by simp only [htv_g0_is_small]; exact hcond75
      -- assert
      step_assert_eq hmem77 hmem with ha77
      have a77 : smalls_sum = s1 + t1 := by
        rw [htv_smalls_sum, htv_s1, htv_t1] ; exact ha77
      step_jump_imm hmem78 hmem, hmem79 hmem
      arith_simps
      apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_MERGE mem σ
        range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
        hmem
        htv_range_check
        htv_g0s0_low
        htv_b1
        htv_g0t0_low
        htv_n1
        htv_g0
        htv_s0
        htv_t0
        htv_g0s0_high
        htv_g0t0_high
        htv_gs1
        htv_gt1
        htv_smalls_sum
        νbound)
      intros κ_MERGE _ h_MERGE
      rcases h_MERGE with ⟨rc_m_le_MERGE, hblk_range_check_ptr, h_MERGE⟩
      -- range check condition
      constructor
      apply le_trans rc_m_le_MERGE (Nat.le_add_right _ _)
      constructor
      · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
      intro rc_h_range_check
      use_only g0s0_low, hl_g0s0_low
      use_only g0s0_high
      use_only g0t0_low, hl_g0t0_low
      use_only g0t0_high
      use_only gs1
      use_only gt1
      use_only smalls_sum
      left
      use_only a71
      use_only a73
      use_only a74
      use_only g0_is_small
      left
      use_only a75
      use_only a77
      use_only κ_MERGE
      apply h_MERGE rc_h_range_check
      done
    -- g0_is_small ≠ 0
    have a75 : g0_is_small ≠ 0 := by simp only [htv_g0_is_small]; exact hcond75
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_G0IsSmall mem σ
      range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum
      hmem
      htv_range_check
      htv_g0s0_low
      htv_b1
      htv_g0t0_low
      htv_n1
      htv_g0
      htv_s0
      htv_t0
      htv_g0s0_high
      htv_g0t0_high
      htv_gs1
      htv_gt1
      htv_smalls_sum
      νbound)
    intros κ_G0IsSmall _ h_G0IsSmall
    rcases h_G0IsSmall with ⟨rc_m_le_G0IsSmall, hblk_range_check_ptr, h_G0IsSmall⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_G0IsSmall (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only g0s0_low, hl_g0s0_low
    use_only g0s0_high
    use_only g0t0_low, hl_g0t0_low
    use_only g0t0_high
    use_only gs1
    use_only gt1
    use_only smalls_sum
    left
    use_only a71
    use_only a73
    use_only a74
    use_only g0_is_small
    right
    use_only a75
    use_only κ_G0IsSmall
    apply h_G0IsSmall rc_h_range_check
    done
  -- g1 ≠ 0
  have a71 : g1 ≠ 0 := by simp only [htv_g1]; exact hcond71
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO mem σ
    range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum
    hmem
    htv_range_check
    htv_g0s0_low
    htv_b1
    htv_g0t0_low
    htv_n1
    htv_g0
    htv_g1
    htv_s0
    htv_s1
    htv_t0
    htv_t1
    htv_g0s0_high
    htv_g0t0_high
    htv_gs1
    htv_gt1
    htv_smalls_sum
    νbound)
  intros κ_S1_AND_T1_EQ_ZERO _ h_S1_AND_T1_EQ_ZERO
  rcases h_S1_AND_T1_EQ_ZERO with ⟨rc_m_le_S1_AND_T1_EQ_ZERO, hblk_range_check_ptr, h_S1_AND_T1_EQ_ZERO⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_S1_AND_T1_EQ_ZERO (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only g0s0_low, hl_g0s0_low
  use_only g0s0_high
  use_only g0t0_low, hl_g0t0_low
  use_only g0t0_high
  use_only gs1
  use_only gt1
  use_only smalls_sum
  right
  use_only a71
  use_only κ_S1_AND_T1_EQ_ZERO
  apply h_S1_AND_T1_EQ_ZERO rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_NoInverse
  -- arguments
  (range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_g0_or_no_inv : g0_or_no_inv = mem σ.ap)
  (htv_g1_option : g1_option = mem (σ.ap + 1))
  (htv_s_or_r0 : s_or_r0 = mem (σ.ap + 2))
  (htv_s_or_r1 : s_or_r1 = mem (σ.ap + 3))
  (htv_t_or_k0 : t_or_k0 = mem (σ.ap + 4))
  (htv_t_or_k1 : t_or_k1 = mem (σ.ap + 5))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 55, ap := σ.ap + 1, fp := σ.fp }
    (fun κ τ =>
    7 ≤ κ ∧ RcEnsures mem (rcBound F) 7 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_NoInverse κ range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- let
  mkdef hl_g0 : g0 = g0_or_no_inv
  have htv_g0 : g0 = mem σ.ap := by
    rw [hl_g0, htv_g0_or_no_inv]
  -- let
  mkdef hl_g1 : g1 = g1_option
  have htv_g1 : g1 = mem (σ.ap + 1) := by
    rw [hl_g1, htv_g1_option]
  -- let
  mkdef hl_s0 : s0 = s_or_r0
  have htv_s0 : s0 = mem (σ.ap + 2) := by
    rw [hl_s0, htv_s_or_r0]
  -- let
  mkdef hl_s1 : s1 = s_or_r1
  have htv_s1 : s1 = mem (σ.ap + 3) := by
    rw [hl_s1, htv_s_or_r1]
  -- let
  mkdef hl_t0 : t0 = t_or_k0
  have htv_t0 : t0 = mem (σ.ap + 4) := by
    rw [hl_t0, htv_t_or_k0]
  -- let
  mkdef hl_t1 : t1 = t_or_k1
  have htv_t1 : t1 = mem (σ.ap + 5) := by
    rw [hl_t1, htv_t_or_k1]
  -- range check for g0
  step_assert_eq hmem55 hmem with rc_g0
  -- range check for g1
  step_assert_eq hmem56 hmem with rc_g1
  -- range check for s0
  step_assert_eq hmem57 hmem with rc_s0
  -- range check for s1
  step_assert_eq hmem58 hmem with rc_s1
  -- range check for t0
  step_assert_eq hmem59 hmem with rc_t0
  -- range check for t1
  step_assert_eq hmem60 hmem with rc_t1
  -- tempvar g0_minus_1
  mkdef hl_g0_minus_1 : g0_minus_1 = mem (σ.ap + 6)
  have htv_g0_minus_1 : g0_minus_1 = mem (σ.ap + 6) := by
    exact hl_g0_minus_1
  -- jump to GIsValid if g1 != 0
  step_jnz hmem61 hmem, hmem62 hmem with hcond61 hcond61
  ·
    -- g1 = 0
    have a61 : g1 = 0 := by simp only [htv_g1]; exact hcond61
    -- assert
    step_assert_eq hmem63 hmem, hmem64 hmem with ha63
    have a63 : g0_minus_1 = g0 - one := by
      rw [htv_g0_minus_1, htv_g0, one, ha63, add_sub_cancel_right]
    -- jump to GIsValid if g0_minus_1 != 0
    step_jnz hmem65 hmem, hmem66 hmem with hcond65 hcond65
    ·
      -- g0_minus_1 = 0
      have a65 : g0_minus_1 = 0 := by simp only [htv_g0_minus_1]; exact hcond65
      -- assert
      step_assert_eq hmem67 hmem, hmem68 hmem with ha67
      have a67 : n1 = zero := by
        rw [htv_n1, zero] ; exact ha67
      -- assert
      step_assert_eq hmem69 hmem, hmem70 hmem with ha69
      have a69 : n0 = one := by
        rw [htv_n0, one] ; exact ha69
      arith_simps
      apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_GIsValid mem σ
        range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1
        hmem
        htv_range_check
        htv_b0
        htv_b1
        htv_n0
        htv_n1
        htv_g0
        htv_g1
        htv_s0
        htv_s1
        htv_t0
        htv_t1
        νbound)
      intros κ_GIsValid _ h_GIsValid
      rcases h_GIsValid with ⟨rc_m_le_GIsValid, hblk_range_check_ptr, h_GIsValid⟩
      -- range check condition
      constructor
      apply le_trans rc_m_le_GIsValid (Nat.le_add_right _ _)
      constructor
      · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
      intro rc_h_range_check
      use_only g0, hl_g0
      use_only g1, hl_g1
      use_only s0, hl_s0
      use_only s1, hl_s1
      use_only t0, hl_t0
      use_only t1, hl_t1
      rc_app rc_h_range_check 0 htv_g0 rc_g0

      rc_app rc_h_range_check 1 htv_g1 rc_g1

      rc_app rc_h_range_check 2 htv_s0 rc_s0

      rc_app rc_h_range_check 3 htv_s1 rc_s1

      rc_app rc_h_range_check 4 htv_t0 rc_t0

      rc_app rc_h_range_check 5 htv_t1 rc_t1

      use_only g0_minus_1
      left
      use_only a61
      use_only a63
      left
      use_only a65
      use_only a67
      use_only a69
      use_only κ_GIsValid
      apply h_GIsValid rc_h_range_check
      done
    -- g0_minus_1 ≠ 0
    have a65 : g0_minus_1 ≠ 0 := by simp only [htv_g0_minus_1]; exact hcond65
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_GIsValid mem σ
      range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1
      hmem
      htv_range_check
      htv_b0
      htv_b1
      htv_n0
      htv_n1
      htv_g0
      htv_g1
      htv_s0
      htv_s1
      htv_t0
      htv_t1
      νbound)
    intros κ_GIsValid _ h_GIsValid
    rcases h_GIsValid with ⟨rc_m_le_GIsValid, hblk_range_check_ptr, h_GIsValid⟩
    -- range check condition
    constructor
    apply le_trans rc_m_le_GIsValid (Nat.le_add_right _ _)
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    use_only g0, hl_g0
    use_only g1, hl_g1
    use_only s0, hl_s0
    use_only s1, hl_s1
    use_only t0, hl_t0
    use_only t1, hl_t1
    rc_app rc_h_range_check 0 htv_g0 rc_g0

    rc_app rc_h_range_check 1 htv_g1 rc_g1

    rc_app rc_h_range_check 2 htv_s0 rc_s0

    rc_app rc_h_range_check 3 htv_s1 rc_s1

    rc_app rc_h_range_check 4 htv_t0 rc_t0

    rc_app rc_h_range_check 5 htv_t1 rc_t1

    use_only g0_minus_1
    left
    use_only a61
    use_only a63
    right
    use_only a65
    use_only κ_GIsValid
    apply h_GIsValid rc_h_range_check
    done
  -- g1 ≠ 0
  have a61 : g1 ≠ 0 := by simp only [htv_g1]; exact hcond61
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_GIsValid mem σ
    range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1
    hmem
    htv_range_check
    htv_b0
    htv_b1
    htv_n0
    htv_n1
    htv_g0
    htv_g1
    htv_s0
    htv_s1
    htv_t0
    htv_t1
    νbound)
  intros κ_GIsValid _ h_GIsValid
  rcases h_GIsValid with ⟨rc_m_le_GIsValid, hblk_range_check_ptr, h_GIsValid⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_GIsValid (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only g0, hl_g0
  use_only g1, hl_g1
  use_only s0, hl_s0
  use_only s1, hl_s1
  use_only t0, hl_t0
  use_only t1, hl_t1
  rc_app rc_h_range_check 0 htv_g0 rc_g0

  rc_app rc_h_range_check 1 htv_g1 rc_g1

  rc_app rc_h_range_check 2 htv_s0 rc_s0

  rc_app rc_h_range_check 3 htv_s1 rc_s1

  rc_app rc_h_range_check 4 htv_t0 rc_t0

  rc_app rc_h_range_check 5 htv_t1 rc_t1

  use_only g0_minus_1
  right
  use_only a61
  use_only κ_GIsValid
  apply h_GIsValid rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_After
  -- arguments
  (range_check b0 b1 n0 n1 r0 r1 k0 k1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_r0 : r0 = mem (σ.ap + 2))
  (htv_r1 : r1 = mem (σ.ap + 3))
  (htv_k0 : k0 = mem (σ.ap + 4))
  (htv_k1 : k1 = mem (σ.ap + 5))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 18, ap := σ.ap + 24, fp := σ.fp }
    (fun κ τ =>
    9 ≤ κ ∧ RcEnsures mem (rcBound F) 9 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_After κ range_check b0 b1 n0 n1 r0 r1 k0 k1 (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- tempvar r0b0_low
  mkdef hl_r0b0_low : r0b0_low = mem (σ.ap + 9)
  have htv_r0b0_low : r0b0_low = mem (σ.ap + 9) := by
    exact hl_r0b0_low
  -- tempvar r0b0_high
  mkdef hl_r0b0_high : r0b0_high = mem (σ.ap + 10)
  have htv_r0b0_high : r0b0_high = mem (σ.ap + 10) := by
    exact hl_r0b0_high
  -- tempvar r0b1_low
  mkdef hl_r0b1_low : r0b1_low = mem (σ.ap + 11)
  have htv_r0b1_low : r0b1_low = mem (σ.ap + 11) := by
    exact hl_r0b1_low
  -- tempvar r0b1_high
  mkdef hl_r0b1_high : r0b1_high = mem (σ.ap + 12)
  have htv_r0b1_high : r0b1_high = mem (σ.ap + 12) := by
    exact hl_r0b1_high
  -- tempvar r1b0_low
  mkdef hl_r1b0_low : r1b0_low = mem (σ.ap + 13)
  have htv_r1b0_low : r1b0_low = mem (σ.ap + 13) := by
    exact hl_r1b0_low
  -- tempvar r1b0_high
  mkdef hl_r1b0_high : r1b0_high = mem (σ.ap + 14)
  have htv_r1b0_high : r1b0_high = mem (σ.ap + 14) := by
    exact hl_r1b0_high
  -- tempvar r1b1_low
  mkdef hl_r1b1_low : r1b1_low = mem (σ.ap + 15)
  have htv_r1b1_low : r1b1_low = mem (σ.ap + 15) := by
    exact hl_r1b1_low
  -- tempvar r1b1_high
  mkdef hl_r1b1_high : r1b1_high = mem (σ.ap + 16)
  have htv_r1b1_high : r1b1_high = mem (σ.ap + 16) := by
    exact hl_r1b1_high
  -- tempvar n0k0_low
  mkdef hl_n0k0_low : n0k0_low = mem (σ.ap + 17)
  have htv_n0k0_low : n0k0_low = mem (σ.ap + 17) := by
    exact hl_n0k0_low
  -- tempvar n0k0_high
  mkdef hl_n0k0_high : n0k0_high = mem (σ.ap + 18)
  have htv_n0k0_high : n0k0_high = mem (σ.ap + 18) := by
    exact hl_n0k0_high
  -- tempvar n0k1_low
  mkdef hl_n0k1_low : n0k1_low = mem (σ.ap + 19)
  have htv_n0k1_low : n0k1_low = mem (σ.ap + 19) := by
    exact hl_n0k1_low
  -- tempvar n0k1_high
  mkdef hl_n0k1_high : n0k1_high = mem (σ.ap + 20)
  have htv_n0k1_high : n0k1_high = mem (σ.ap + 20) := by
    exact hl_n0k1_high
  -- tempvar n1k0_low
  mkdef hl_n1k0_low : n1k0_low = mem (σ.ap + 21)
  have htv_n1k0_low : n1k0_low = mem (σ.ap + 21) := by
    exact hl_n1k0_low
  -- tempvar n1k0_high
  mkdef hl_n1k0_high : n1k0_high = mem (σ.ap + 22)
  have htv_n1k0_high : n1k0_high = mem (σ.ap + 22) := by
    exact hl_n1k0_high
  -- tempvar n1k1_low
  mkdef hl_n1k1_low : n1k1_low = mem (σ.ap + 23)
  have htv_n1k1_low : n1k1_low = mem (σ.ap + 23) := by
    exact hl_n1k1_low
  -- tempvar n1k1_high
  mkdef hl_n1k1_high : n1k1_high = mem (σ.ap + 24)
  have htv_n1k1_high : n1k1_high = mem (σ.ap + 24) := by
    exact hl_n1k1_high
  -- tempvar part0
  step_assert_eq hmem18 hmem, hmem19 hmem with tv_part0
  mkdef hl_part0 : part0 = n0k0_low + one
  have htv_part0 : part0 = mem (σ.ap + 25) := by
    rw [hl_part0, htv_n0k0_low, one, tv_part0]
  -- tempvar part1
  step_assert_eq hmem20 hmem with tv_part1
  mkdef hl_part1 : part1 = part0 - r0b0_low
  have htv_part1 : part1 = mem (σ.ap + 26) := by
    rw [hl_part1, htv_part0, htv_r0b0_low, tv_part1, add_sub_cancel_right]
  -- tempvar leftover
  step_assert_eq hmem21 hmem, hmem22 hmem with tv_leftover
  mkdef hl_leftover : leftover = part1 / u128_limit
  have htv_leftover : leftover = mem (σ.ap + 27) := by
    rw [hl_leftover, htv_part1, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- assert
  step_assert_eq hmem23 hmem with ha23
  have a23 : leftover = leftover * leftover := by
    rw [htv_leftover] ; exact ha23
  -- tempvar part0₁
  step_assert_eq hmem24 hmem with tv_part0₁
  mkdef hl_part0₁ : part0₁ = n0k0_high + leftover
  have htv_part0₁ : part0₁ = mem (σ.ap + 28) := by
    rw [hl_part0₁, htv_n0k0_high, htv_leftover, tv_part0₁]
  -- tempvar part1₁
  step_assert_eq hmem25 hmem with tv_part1₁
  mkdef hl_part1₁ : part1₁ = part0₁ + n0k1_low
  have htv_part1₁ : part1₁ = mem (σ.ap + 29) := by
    rw [hl_part1₁, htv_part0₁, htv_n0k1_low, tv_part1₁]
  -- tempvar part2
  step_assert_eq hmem26 hmem with tv_part2
  mkdef hl_part2 : part2 = part1₁ + n1k0_low
  have htv_part2 : part2 = mem (σ.ap + 30) := by
    rw [hl_part2, htv_part1₁, htv_n1k0_low, tv_part2]
  -- tempvar part3
  step_assert_eq hmem27 hmem with tv_part3
  mkdef hl_part3 : part3 = part2 - r0b0_high
  have htv_part3 : part3 = mem (σ.ap + 31) := by
    rw [hl_part3, htv_part2, htv_r0b0_high, tv_part3, add_sub_cancel_right]
  -- tempvar part4
  step_assert_eq hmem28 hmem with tv_part4
  mkdef hl_part4 : part4 = part3 - r0b1_low
  have htv_part4 : part4 = mem (σ.ap + 32) := by
    rw [hl_part4, htv_part3, htv_r0b1_low, tv_part4, add_sub_cancel_right]
  -- tempvar part5
  step_assert_eq hmem29 hmem with tv_part5
  mkdef hl_part5 : part5 = part4 - r1b0_low
  have htv_part5 : part5 = mem (σ.ap + 33) := by
    rw [hl_part5, htv_part4, htv_r1b0_low, tv_part5, add_sub_cancel_right]
  -- tempvar leftover₁
  step_assert_eq hmem30 hmem, hmem31 hmem with tv_leftover₁
  mkdef hl_leftover₁ : leftover₁ = part5 / u128_limit
  have htv_leftover₁ : leftover₁ = mem (σ.ap + 34) := by
    rw [hl_leftover₁, htv_part5, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover₁.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- tempvar a
  step_assert_eq hmem32 hmem, hmem33 hmem with tv_a
  mkdef hl_a : a = leftover₁ - i16_lower_bound
  have htv_a : a = mem (σ.ap + 35) := by
    rw [hl_a, htv_leftover₁, i16_lower_bound, tv_a, add_sub_cancel_right]
  -- range check for a
  step_assert_eq hmem34 hmem with rc_a
  -- tempvar a₁
  step_assert_eq hmem35 hmem, hmem36 hmem with tv_a₁
  mkdef hl_a₁ : a₁ = leftover₁ + u128_bound_minus_i16_upper_bound
  have htv_a₁ : a₁ = mem (σ.ap + 36) := by
    rw [hl_a₁, htv_leftover₁, u128_bound_minus_i16_upper_bound, tv_a₁]
  -- range check for a₁
  step_assert_eq hmem37 hmem with rc_a₁
  -- tempvar part0₂
  step_assert_eq hmem38 hmem with tv_part0₂
  mkdef hl_part0₂ : part0₂ = n0k1_high + leftover₁
  have htv_part0₂ : part0₂ = mem (σ.ap + 37) := by
    rw [hl_part0₂, htv_n0k1_high, htv_leftover₁, tv_part0₂]
  -- tempvar part1₂
  step_assert_eq hmem39 hmem with tv_part1₂
  mkdef hl_part1₂ : part1₂ = part0₂ + n1k0_high
  have htv_part1₂ : part1₂ = mem (σ.ap + 38) := by
    rw [hl_part1₂, htv_part0₂, htv_n1k0_high, tv_part1₂]
  -- tempvar part2₁
  step_assert_eq hmem40 hmem with tv_part2₁
  mkdef hl_part2₁ : part2₁ = part1₂ + n1k1_low
  have htv_part2₁ : part2₁ = mem (σ.ap + 39) := by
    rw [hl_part2₁, htv_part1₂, htv_n1k1_low, tv_part2₁]
  -- tempvar part3₁
  step_assert_eq hmem41 hmem with tv_part3₁
  mkdef hl_part3₁ : part3₁ = part2₁ - r1b0_high
  have htv_part3₁ : part3₁ = mem (σ.ap + 40) := by
    rw [hl_part3₁, htv_part2₁, htv_r1b0_high, tv_part3₁, add_sub_cancel_right]
  -- tempvar part4₁
  step_assert_eq hmem42 hmem with tv_part4₁
  mkdef hl_part4₁ : part4₁ = part3₁ - r0b1_high
  have htv_part4₁ : part4₁ = mem (σ.ap + 41) := by
    rw [hl_part4₁, htv_part3₁, htv_r0b1_high, tv_part4₁, add_sub_cancel_right]
  -- tempvar part5₁
  step_assert_eq hmem43 hmem with tv_part5₁
  mkdef hl_part5₁ : part5₁ = part4₁ - r1b1_low
  have htv_part5₁ : part5₁ = mem (σ.ap + 42) := by
    rw [hl_part5₁, htv_part4₁, htv_r1b1_low, tv_part5₁, add_sub_cancel_right]
  -- tempvar leftover₂
  step_assert_eq hmem44 hmem, hmem45 hmem with tv_leftover₂
  mkdef hl_leftover₂ : leftover₂ = part5₁ / u128_limit
  have htv_leftover₂ : leftover₂ = mem (σ.ap + 43) := by
    rw [hl_leftover₂, htv_part5₁, u128_limit, div_eq_iff_mul_eq] ; exact tv_leftover₂.symm
    apply PRIME.nat_cast_ne_zero (by norm_num1) ; rw [PRIME] ; norm_num1
  -- tempvar a₂
  step_assert_eq hmem46 hmem, hmem47 hmem with tv_a₂
  mkdef hl_a₂ : a₂ = leftover₂ - i16_lower_bound
  have htv_a₂ : a₂ = mem (σ.ap + 44) := by
    rw [hl_a₂, htv_leftover₂, i16_lower_bound, tv_a₂, add_sub_cancel_right]
  -- range check for a₂
  step_assert_eq hmem48 hmem with rc_a₂
  -- tempvar a₃
  step_assert_eq hmem49 hmem, hmem50 hmem with tv_a₃
  mkdef hl_a₃ : a₃ = leftover₂ + u128_bound_minus_i16_upper_bound
  have htv_a₃ : a₃ = mem (σ.ap + 45) := by
    rw [hl_a₃, htv_leftover₂, u128_bound_minus_i16_upper_bound, tv_a₃]
  -- range check for a₃
  step_assert_eq hmem51 hmem with rc_a₃
  -- assert
  step_assert_eq hmem52 hmem with ha52
  have a52 : r1b1_high = n1k1_high + leftover₂ := by
    rw [htv_r1b1_high, htv_n1k1_high, htv_leftover₂] ; exact ha52
  step_jump_imm hmem53 hmem, hmem54 hmem
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_Done mem σ
    range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high
    hmem
    htv_range_check
    htv_b0
    htv_b1
    htv_n0
    htv_n1
    htv_r0
    htv_r1
    htv_k0
    htv_k1
    htv_r0b0_low
    htv_r0b0_high
    htv_r0b1_low
    htv_r0b1_high
    htv_r1b0_low
    htv_r1b0_high
    htv_r1b1_low
    htv_r1b1_high
    htv_n0k0_low
    htv_n0k0_high
    htv_n0k1_low
    htv_n0k1_high
    htv_n1k0_low
    htv_n1k0_high
    htv_n1k1_low
    htv_n1k1_high
    νbound)
  intros κ_Done _ h_Done
  rcases h_Done with ⟨rc_m_le_Done, hblk_range_check_ptr, h_Done⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_Done (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  use_only r0b0_low
  use_only r0b0_high
  use_only r0b1_low
  use_only r0b1_high
  use_only r1b0_low
  use_only r1b0_high
  use_only r1b1_low
  use_only r1b1_high
  use_only n0k0_low
  use_only n0k0_high
  use_only n0k1_low
  use_only n0k1_high
  use_only n1k0_low
  use_only n1k0_high
  use_only n1k1_low
  use_only n1k1_high
  use_only part0, hl_part0
  use_only part1, hl_part1
  use_only leftover, hl_leftover
  use_only a23
  use_only part0₁, hl_part0₁
  use_only part1₁, hl_part1₁
  use_only part2, hl_part2
  use_only part3, hl_part3
  use_only part4, hl_part4
  use_only part5, hl_part5
  use_only leftover₁, hl_leftover₁
  use_only a, hl_a
  rc_app rc_h_range_check 5 htv_a rc_a

  use_only a₁, hl_a₁
  rc_app rc_h_range_check 6 htv_a₁ rc_a₁

  use_only part0₂, hl_part0₂
  use_only part1₂, hl_part1₂
  use_only part2₁, hl_part2₁
  use_only part3₁, hl_part3₁
  use_only part4₁, hl_part4₁
  use_only part5₁, hl_part5₁
  use_only leftover₂, hl_leftover₂
  use_only a₂, hl_a₂
  rc_app rc_h_range_check 7 htv_a₂ rc_a₂

  use_only a₃, hl_a₃
  rc_app rc_h_range_check 8 htv_a₃ rc_a₃

  use_only a52
  use_only κ_Done
  apply h_Done rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n_HighDiff
  -- arguments
  (range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  (htv_r0 : r0 = mem (σ.ap + 2))
  (htv_r1 : r1 = mem (σ.ap + 3))
  (htv_k0 : k0 = mem (σ.ap + 4))
  (htv_k1 : k1 = mem (σ.ap + 5))
  (htv_diff1 : diff1 = mem (σ.ap + 6))
  (νbound : ℕ)
  -- conclusion
  : EnsuresbRet νbound mem
    { pc := σ.pc + 17, ap := σ.ap + 24, fp := σ.fp }
    (fun κ τ =>
    9 ≤ κ ∧ RcEnsures mem (rcBound F) 9 (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (auto_spec_u256_guarantee_inv_mod_n_HighDiff κ range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  -- range check for diff1
  step_assert_eq hmem17 hmem with rc_diff1
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_After mem σ
    range_check b0 b1 n0 n1 r0 r1 k0 k1
    hmem
    htv_range_check
    htv_b0
    htv_b1
    htv_n0
    htv_n1
    htv_r0
    htv_r1
    htv_k0
    htv_k1
    νbound)
  intros κ_After _ h_After
  rcases h_After with ⟨rc_m_le_After, hblk_range_check_ptr, h_After⟩
  -- range check condition
  constructor
  apply le_trans rc_m_le_After (Nat.le_add_right _ _)
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  rc_app rc_h_range_check 4 htv_diff1 rc_diff1

  use_only κ_After
  apply h_After rc_h_range_check
  done

theorem auto_sound_u256_guarantee_inv_mod_n
  -- arguments
  (range_check b0 b1 n0 n1 : F)
  -- code is in memory at σ.pc + start offset
  (hmem : MemAt mem u256_guarantee_inv_mod_n_code σ.pc)
  -- input arguments on the stack
  (htv_range_check : range_check = mem (σ.fp - 7))
  (htv_b0 : b0 = mem (σ.fp - 6))
  (htv_b1 : b1 = mem (σ.fp - 5))
  (htv_n0 : n0 = mem (σ.fp - 4))
  (htv_n1 : n1 = mem (σ.fp - 3))
  -- conclusion
  : EnsuresRet mem σ (fun κ τ =>
    ∃ μ ≤ κ, 7 ≤ μ ∧ RcEnsures mem (rcBound F) μ (mem (σ.fp - 7)) (mem (τ.ap - 36))
      (spec_u256_guarantee_inv_mod_n κ range_check b0 b1 n0 n1 (mem (τ.ap - 35)) (mem (τ.ap - 34)) (mem (τ.ap - 33)) (mem (τ.ap - 32)) (mem (τ.ap - 31)) (mem (τ.ap - 30)) (mem (τ.ap - 29)) (mem (τ.ap - 28)) (mem (τ.ap - 27)) (mem (τ.ap - 26)) (mem (τ.ap - 25)) (mem (τ.ap - 24)) (mem (τ.ap - 23)) (mem (τ.ap - 22)) (mem (τ.ap - 21)) (mem (τ.ap - 20)) (mem (τ.ap - 19)) (mem (τ.ap - 18)) (mem (τ.ap - 17)) (mem (τ.ap - 16)) (mem (τ.ap - 15)) (mem (τ.ap - 14)) (mem (τ.ap - 13)) (mem (τ.ap - 12)) (mem (τ.ap - 11)) (mem (τ.ap - 10)) (mem (τ.ap - 9)) (mem (τ.ap - 8)) (mem (τ.ap - 7)) (mem (τ.ap - 6)) (mem (τ.ap - 5)) (mem (τ.ap - 4)) (mem (τ.ap - 3)) (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
by
  apply ensures_of_ensuresb; intro νbound
  -- let
  mkdef hl_orig_range_check : orig_range_check = range_check
  have htv_orig_range_check : orig_range_check = mem (σ.fp - 7) := by
    rw [hl_orig_range_check, htv_range_check]
  -- tempvar g0_or_no_inv
  mkdef hl_g0_or_no_inv : g0_or_no_inv = mem σ.ap
  have htv_g0_or_no_inv : g0_or_no_inv = mem σ.ap := by
    exact hl_g0_or_no_inv
  -- tempvar g1_option
  mkdef hl_g1_option : g1_option = mem (σ.ap + 1)
  have htv_g1_option : g1_option = mem (σ.ap + 1) := by
    exact hl_g1_option
  -- tempvar s_or_r0
  mkdef hl_s_or_r0 : s_or_r0 = mem (σ.ap + 2)
  have htv_s_or_r0 : s_or_r0 = mem (σ.ap + 2) := by
    exact hl_s_or_r0
  -- tempvar s_or_r1
  mkdef hl_s_or_r1 : s_or_r1 = mem (σ.ap + 3)
  have htv_s_or_r1 : s_or_r1 = mem (σ.ap + 3) := by
    exact hl_s_or_r1
  -- tempvar t_or_k0
  mkdef hl_t_or_k0 : t_or_k0 = mem (σ.ap + 4)
  have htv_t_or_k0 : t_or_k0 = mem (σ.ap + 4) := by
    exact hl_t_or_k0
  -- tempvar t_or_k1
  mkdef hl_t_or_k1 : t_or_k1 = mem (σ.ap + 5)
  have htv_t_or_k1 : t_or_k1 = mem (σ.ap + 5) := by
    exact hl_t_or_k1
  -- jump to NoInverse if g0_or_no_inv != 0
  step_jnz hmem0 hmem, hmem1 hmem with hcond0 hcond0
  ·
    -- g0_or_no_inv = 0
    have a0 : g0_or_no_inv = 0 := by simp only [htv_g0_or_no_inv]; exact hcond0
    -- let
    mkdef hl_r0 : r0 = s_or_r0
    have htv_r0 : r0 = mem (σ.ap + 2) := by
      rw [hl_r0, htv_s_or_r0]
    -- let
    mkdef hl_r1 : r1 = s_or_r1
    have htv_r1 : r1 = mem (σ.ap + 3) := by
      rw [hl_r1, htv_s_or_r1]
    -- let
    mkdef hl_k0 : k0 = t_or_k0
    have htv_k0 : k0 = mem (σ.ap + 4) := by
      rw [hl_k0, htv_t_or_k0]
    -- let
    mkdef hl_k1 : k1 = t_or_k1
    have htv_k1 : k1 = mem (σ.ap + 5) := by
      rw [hl_k1, htv_t_or_k1]
    -- range check for r0
    step_assert_eq hmem2 hmem with rc_r0
    -- range check for r1
    step_assert_eq hmem3 hmem with rc_r1
    -- range check for k0
    step_assert_eq hmem4 hmem with rc_k0
    -- range check for k1
    step_assert_eq hmem5 hmem with rc_k1
    -- tempvar diff1
    step_assert_eq hmem6 hmem with tv_diff1
    mkdef hl_diff1 : diff1 = n1 - r1
    have htv_diff1 : diff1 = mem (σ.ap + 6) := by
      rw [hl_diff1, htv_n1, htv_r1, tv_diff1, add_sub_cancel_right]
    step_advance_ap hmem7 hmem, hmem8 hmem
    -- tempvar diff0
    mkdef hl_diff0 : diff0 = mem (σ.ap + 7)
    have htv_diff0 : diff0 = mem (σ.ap + 7) := by
      exact hl_diff0
    -- tempvar diff0_min_1
    mkdef hl_diff0_min_1 : diff0_min_1 = mem (σ.ap + 8)
    have htv_diff0_min_1 : diff0_min_1 = mem (σ.ap + 8) := by
      exact hl_diff0_min_1
    -- jump to HighDiff if diff1 != 0
    step_jnz hmem9 hmem, hmem10 hmem with hcond9 hcond9
    ·
      -- diff1 = 0
      have a9 : diff1 = 0 := by simp only [htv_diff1]; exact hcond9
      -- assert
      step_assert_eq hmem11 hmem with ha11
      have a11 : diff0 = n0 - r0 := by
        rw [htv_diff0, htv_n0, htv_r0, ha11, add_sub_cancel_right]
      -- assert
      step_assert_eq hmem12 hmem, hmem13 hmem with ha12
      have a12 : diff0_min_1 = diff0 - one := by
        rw [htv_diff0_min_1, htv_diff0, one, ha12, add_sub_cancel_right]
      -- range check for diff0_min_1
      step_assert_eq hmem14 hmem with rc_diff0_min_1
      step_jump_imm hmem15 hmem, hmem16 hmem
      arith_simps
      apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_After mem σ
        range_check b0 b1 n0 n1 r0 r1 k0 k1
        hmem
        htv_range_check
        htv_b0
        htv_b1
        htv_n0
        htv_n1
        htv_r0
        htv_r1
        htv_k0
        htv_k1
        νbound)
      intros κ_After _ h_After
      rcases h_After with ⟨rc_m_le_After, hblk_range_check_ptr, h_After⟩
      -- range check condition
      use_only 9
      constructor
      apply le_trans rc_m_le_After (Nat.le_add_right _ _)
      constructor ; norm_num1
      constructor
      · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
      intro rc_h_range_check
      suffices auto_spec : auto_spec_u256_guarantee_inv_mod_n _ range_check b0 b1 n0 n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ by
        apply sound_u256_guarantee_inv_mod_n ; apply auto_spec
      use_only orig_range_check, hl_orig_range_check
      use_only g0_or_no_inv
      use_only g1_option
      use_only s_or_r0
      use_only s_or_r1
      use_only t_or_k0
      use_only t_or_k1
      left
      use_only a0
      use_only r0, hl_r0
      use_only r1, hl_r1
      use_only k0, hl_k0
      use_only k1, hl_k1
      rc_app rc_h_range_check 0 htv_r0 rc_r0

      rc_app rc_h_range_check 1 htv_r1 rc_r1

      rc_app rc_h_range_check 2 htv_k0 rc_k0

      rc_app rc_h_range_check 3 htv_k1 rc_k1

      use_only diff1, hl_diff1
      use_only diff0
      use_only diff0_min_1
      left
      use_only a9
      use_only a11
      use_only a12
      rc_app rc_h_range_check 4 htv_diff0_min_1 rc_diff0_min_1

      use_only κ_After
      apply h_After rc_h_range_check
      done
    -- diff1 ≠ 0
    have a9 : diff1 ≠ 0 := by simp only [htv_diff1]; exact hcond9
    arith_simps
    apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_HighDiff mem σ
      range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1
      hmem
      htv_range_check
      htv_b0
      htv_b1
      htv_n0
      htv_n1
      htv_r0
      htv_r1
      htv_k0
      htv_k1
      htv_diff1
      νbound)
    intros κ_HighDiff _ h_HighDiff
    rcases h_HighDiff with ⟨rc_m_le_HighDiff, hblk_range_check_ptr, h_HighDiff⟩
    -- range check condition
    use_only 9
    constructor
    apply le_trans rc_m_le_HighDiff (Nat.le_add_right _ _)
    constructor ; norm_num1
    constructor
    · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
    intro rc_h_range_check
    suffices auto_spec : auto_spec_u256_guarantee_inv_mod_n _ range_check b0 b1 n0 n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ by
      apply sound_u256_guarantee_inv_mod_n ; apply auto_spec
    use_only orig_range_check, hl_orig_range_check
    use_only g0_or_no_inv
    use_only g1_option
    use_only s_or_r0
    use_only s_or_r1
    use_only t_or_k0
    use_only t_or_k1
    left
    use_only a0
    use_only r0, hl_r0
    use_only r1, hl_r1
    use_only k0, hl_k0
    use_only k1, hl_k1
    rc_app rc_h_range_check 0 htv_r0 rc_r0

    rc_app rc_h_range_check 1 htv_r1 rc_r1

    rc_app rc_h_range_check 2 htv_k0 rc_k0

    rc_app rc_h_range_check 3 htv_k1 rc_k1

    use_only diff1, hl_diff1
    use_only diff0
    use_only diff0_min_1
    right
    use_only a9
    use_only κ_HighDiff
    apply h_HighDiff rc_h_range_check
    done
  -- g0_or_no_inv ≠ 0
  have a0 : g0_or_no_inv ≠ 0 := by simp only [htv_g0_or_no_inv]; exact hcond0
  arith_simps
  apply ensuresbRet_trans (auto_sound_u256_guarantee_inv_mod_n_NoInverse mem σ
    range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1
    hmem
    htv_range_check
    htv_b0
    htv_b1
    htv_n0
    htv_n1
    htv_g0_or_no_inv
    htv_g1_option
    htv_s_or_r0
    htv_s_or_r1
    htv_t_or_k0
    htv_t_or_k1
    νbound)
  intros κ_NoInverse _ h_NoInverse
  rcases h_NoInverse with ⟨rc_m_le_NoInverse, hblk_range_check_ptr, h_NoInverse⟩
  -- range check condition
  use_only 7
  constructor
  apply le_trans rc_m_le_NoInverse (Nat.le_add_right _ _)
  constructor ; norm_num1
  constructor
  · arith_simps ; rw [hblk_range_check_ptr] ; try { norm_cast }
  intro rc_h_range_check
  suffices auto_spec : auto_spec_u256_guarantee_inv_mod_n _ range_check b0 b1 n0 n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ by
    apply sound_u256_guarantee_inv_mod_n ; apply auto_spec
  use_only orig_range_check, hl_orig_range_check
  use_only g0_or_no_inv
  use_only g1_option
  use_only s_or_r0
  use_only s_or_r1
  use_only t_or_k0
  use_only t_or_k1
  right
  use_only a0
  use_only κ_NoInverse
  apply h_NoInverse rc_h_range_check
  done
