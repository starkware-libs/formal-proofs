import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common
import Verification.Libfuncs.u256.u256_guarantee_inv_mod_n_completeness_spec
import Verification.Libfuncs.u256.u256_guarantee_inv_mod_n_code

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Tactic
open Mrel
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 10000000

open vm_u256_guarantee_inv_mod_n_code
open u256_guarantee_inv_mod_n_completeness

variable (mem : Mrel → Mrel) (σ : VmRegisterState)

theorem complete_u256_guarantee_inv_mod_n_Done_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_r0 : val r0 = mem (exec (σ.ap + 2)))
    (htv_r1 : val r1 = mem (exec (σ.ap + 3)))
    (htv_k0 : val k0 = mem (exec (σ.ap + 4)))
    (htv_k1 : val k1 = mem (exec (σ.ap + 5)))
    (htv_r0b0_low : val r0b0_low = mem (exec (σ.ap + 9)))
    (htv_r0b0_high : val r0b0_high = mem (exec (σ.ap + 10)))
    (htv_r0b1_low : val r0b1_low = mem (exec (σ.ap + 11)))
    (htv_r0b1_high : val r0b1_high = mem (exec (σ.ap + 12)))
    (htv_r1b0_low : val r1b0_low = mem (exec (σ.ap + 13)))
    (htv_r1b0_high : val r1b0_high = mem (exec (σ.ap + 14)))
    (htv_r1b1_low : val r1b1_low = mem (exec (σ.ap + 15)))
    (htv_r1b1_high : val r1b1_high = mem (exec (σ.ap + 16)))
    (htv_n0k0_low : val n0k0_low = mem (exec (σ.ap + 17)))
    (htv_n0k0_high : val n0k0_high = mem (exec (σ.ap + 18)))
    (htv_n0k1_low : val n0k1_low = mem (exec (σ.ap + 19)))
    (htv_n0k1_high : val n0k1_high = mem (exec (σ.ap + 20)))
    (htv_n1k0_low : val n1k0_low = mem (exec (σ.ap + 21)))
    (htv_n1k0_high : val n1k0_high = mem (exec (σ.ap + 22)))
    (htv_n1k1_low : val n1k1_low = mem (exec (σ.ap + 23)))
    (htv_n1k1_high : val n1k1_high = mem (exec (σ.ap + 24)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_Done range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 46) (range_check + 9),
    VmRangeChecked loc.rc_vals (range_check + 9) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 102, ap := (σ.ap + 46), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 46) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 9) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_ρ_branch_id, h_ρ_r0, h_ρ_r1, h_ρ_r0₁, h_ρ_b0, h_ρ_r0b0_high, h_ρ_r0b0_low, h_ρ_r0₂, h_ρ_b1, h_ρ_r0b1_high, h_ρ_r0b1_low, h_ρ_r1₁, h_ρ_b0₁, h_ρ_r1b0_high, h_ρ_r1b0_low, h_ρ_r1₂, h_ρ_b1₁, h_ρ_r1b1_high, h_ρ_r1b1_low, h_ρ_n0, h_ρ_k0, h_ρ_n0k0_high, h_ρ_n0k0_low, h_ρ_n0₁, h_ρ_k1, h_ρ_n0k1_high, h_ρ_n0k1_low, h_ρ_n1_or_g0, h_ρ_k0_or_s0, h_ρ_n1k0_high_or_g0s0_high, h_ρ_n1k0_low_or_g0s0_low, h_ρ_n1_or_g0₁, h_ρ_k1_or_t0, h_ρ_n1k1_high_or_g0t0_high, h_ρ_n1k1_low_or_g0t0_low⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 46)) with
        | 0 => rc (range_check + 9)
        | 1 => val ρ_branch_id
        | 2 => val ρ_r0
        | 3 => val ρ_r1
        | 4 => val ρ_r0₁
        | 5 => val ρ_b0
        | 6 => val ρ_r0b0_high
        | 7 => val ρ_r0b0_low
        | 8 => val ρ_r0₂
        | 9 => val ρ_b1
        | 10 => val ρ_r0b1_high
        | 11 => val ρ_r0b1_low
        | 12 => val ρ_r1₁
        | 13 => val ρ_b0₁
        | 14 => val ρ_r1b0_high
        | 15 => val ρ_r1b0_low
        | 16 => val ρ_r1₂
        | 17 => val ρ_b1₁
        | 18 => val ρ_r1b1_high
        | 19 => val ρ_r1b1_low
        | 20 => val ρ_n0
        | 21 => val ρ_k0
        | 22 => val ρ_n0k0_high
        | 23 => val ρ_n0k0_low
        | 24 => val ρ_n0₁
        | 25 => val ρ_k1
        | 26 => val ρ_n0k1_high
        | 27 => val ρ_n0k1_low
        | 28 => val ρ_n1_or_g0
        | 29 => val ρ_k0_or_s0
        | 30 => val ρ_n1k0_high_or_g0s0_high
        | 31 => val ρ_n1k0_low_or_g0s0_low
        | 32 => val ρ_n1_or_g0₁
        | 33 => val ρ_k1_or_t0
        | 34 => val ρ_n1k1_high_or_g0t0_high
        | 35 => val ρ_n1k1_low_or_g0t0_low
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 9)) with
        | _ => (0 : ℤ)

  let loc := (⟨36, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 46) (range_check + 9))

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_12 := assign_exec_of_lt mem loc (σ.ap + 12)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_13 := assign_exec_of_lt mem loc (σ.ap + 13)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_14 := assign_exec_of_lt mem loc (σ.ap + 14)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_15 := assign_exec_of_lt mem loc (σ.ap + 15)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_16 := assign_exec_of_lt mem loc (σ.ap + 16)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_17 := assign_exec_of_lt mem loc (σ.ap + 17)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_18 := assign_exec_of_lt mem loc (σ.ap + 18)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_19 := assign_exec_of_lt mem loc (σ.ap + 19)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_20 := assign_exec_of_lt mem loc (σ.ap + 20)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_21 := assign_exec_of_lt mem loc (σ.ap + 21)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_22 := assign_exec_of_lt mem loc (σ.ap + 22)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_23 := assign_exec_of_lt mem loc (σ.ap + 23)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_24 := assign_exec_of_lt mem loc (σ.ap + 24)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_46 := assign_exec_pos mem loc (σ.ap + 46)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_47 := assign_exec_pos mem loc (σ.ap + 47)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_48 := assign_exec_pos mem loc (σ.ap + 48)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_49 := assign_exec_pos mem loc (σ.ap + 49)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_50 := assign_exec_pos mem loc (σ.ap + 50)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_51 := assign_exec_pos mem loc (σ.ap + 51)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_52 := assign_exec_pos mem loc (σ.ap + 52)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_53 := assign_exec_pos mem loc (σ.ap + 53)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_54 := assign_exec_pos mem loc (σ.ap + 54)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_55 := assign_exec_pos mem loc (σ.ap + 55)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_56 := assign_exec_pos mem loc (σ.ap + 56)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_57 := assign_exec_pos mem loc (σ.ap + 57)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_58 := assign_exec_pos mem loc (σ.ap + 58)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_59 := assign_exec_pos mem loc (σ.ap + 59)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_60 := assign_exec_pos mem loc (σ.ap + 60)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_61 := assign_exec_pos mem loc (σ.ap + 61)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_62 := assign_exec_pos mem loc (σ.ap + 62)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_63 := assign_exec_pos mem loc (σ.ap + 63)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_64 := assign_exec_pos mem loc (σ.ap + 64)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_65 := assign_exec_pos mem loc (σ.ap + 65)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_66 := assign_exec_pos mem loc (σ.ap + 66)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_67 := assign_exec_pos mem loc (σ.ap + 67)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_68 := assign_exec_pos mem loc (σ.ap + 68)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_69 := assign_exec_pos mem loc (σ.ap + 69)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_70 := assign_exec_pos mem loc (σ.ap + 70)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_71 := assign_exec_pos mem loc (σ.ap + 71)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_72 := assign_exec_pos mem loc (σ.ap + 72)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_73 := assign_exec_pos mem loc (σ.ap + 73)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_74 := assign_exec_pos mem loc (σ.ap + 74)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_75 := assign_exec_pos mem loc (σ.ap + 75)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_76 := assign_exec_pos mem loc (σ.ap + 76)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_77 := assign_exec_pos mem loc (σ.ap + 77)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_78 := assign_exec_pos mem loc (σ.ap + 78)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_79 := assign_exec_pos mem loc (σ.ap + 79)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_80 := assign_exec_pos mem loc (σ.ap + 80)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_81 := assign_exec_pos mem loc (σ.ap + 81)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_zero
  --   range check return value
  vm_step_assert_eq hmem102 hmem, hmem103 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem103 hmem]
    simp only [h_ap_plus_46]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem104 hmem, hmem105 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem105 hmem]
    simp only [h_ap_plus_47]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_branch_id]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem106 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_48]
    simp only [h_ap_plus_2]
    simp only [←htv_r0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem107 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_49]
    simp only [h_ap_plus_3]
    simp only [←htv_r1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem108 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_50]
    simp only [h_ap_plus_2]
    simp only [←htv_r0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem109 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_51]
    simp only [h_ap_minus_6]
    simp only [←htv_b0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_b0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem110 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_52]
    simp only [h_ap_plus_10]
    simp only [←htv_r0b0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0b0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem111 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_53]
    simp only [h_ap_plus_9]
    simp only [←htv_r0b0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0b0_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem112 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_54]
    simp only [h_ap_plus_2]
    simp only [←htv_r0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0₂]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem113 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_55]
    simp only [h_ap_minus_5]
    simp only [←htv_b1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_b1]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem114 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_56]
    simp only [h_ap_plus_12]
    simp only [←htv_r0b1_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0b1_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem115 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_57]
    simp only [h_ap_plus_11]
    simp only [←htv_r0b1_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r0b1_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem116 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_58]
    simp only [h_ap_plus_3]
    simp only [←htv_r1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem117 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_59]
    simp only [h_ap_minus_6]
    simp only [←htv_b0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_b0₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem118 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_60]
    simp only [h_ap_plus_14]
    simp only [←htv_r1b0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1b0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem119 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_61]
    simp only [h_ap_plus_13]
    simp only [←htv_r1b0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1b0_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem120 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_62]
    simp only [h_ap_plus_3]
    simp only [←htv_r1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1₂]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem121 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_63]
    simp only [h_ap_minus_5]
    simp only [←htv_b1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_b1₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem122 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_64]
    simp only [h_ap_plus_16]
    simp only [←htv_r1b1_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1b1_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem123 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_65]
    simp only [h_ap_plus_15]
    simp only [←htv_r1b1_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_r1b1_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem124 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_66]
    simp only [h_ap_minus_4]
    simp only [←htv_n0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem125 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_67]
    simp only [h_ap_plus_4]
    simp only [←htv_k0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem126 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_68]
    simp only [h_ap_plus_18]
    simp only [←htv_n0k0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0k0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem127 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_69]
    simp only [h_ap_plus_17]
    simp only [←htv_n0k0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0k0_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem128 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_70]
    simp only [h_ap_minus_4]
    simp only [←htv_n0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem129 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_71]
    simp only [h_ap_plus_5]
    simp only [←htv_k1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k1]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem130 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_72]
    simp only [h_ap_plus_20]
    simp only [←htv_n0k1_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0k1_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem131 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_73]
    simp only [h_ap_plus_19]
    simp only [←htv_n0k1_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n0k1_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem132 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_74]
    simp only [h_ap_minus_3]
    simp only [←htv_n1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1_or_g0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem133 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_75]
    simp only [h_ap_plus_4]
    simp only [←htv_k0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k0_or_s0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem134 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_76]
    simp only [h_ap_plus_22]
    simp only [←htv_n1k0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k0_high_or_g0s0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem135 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_77]
    simp only [h_ap_plus_21]
    simp only [←htv_n1k0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k0_low_or_g0s0_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem136 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_78]
    simp only [h_ap_minus_3]
    simp only [←htv_n1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1_or_g0₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem137 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_79]
    simp only [h_ap_plus_5]
    simp only [←htv_k1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k1_or_t0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem138 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_80]
    simp only [h_ap_plus_24]
    simp only [←htv_n1k1_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k1_high_or_g0t0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem139 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_81]
    simp only [h_ap_plus_23]
    simp only [←htv_n1k1_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k1_low_or_g0t0_low]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem140 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_46]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl
  done

theorem complete_u256_guarantee_inv_mod_n_MERGE_from_spec
    -- arguments
    (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_g0s0_low : val g0s0_low = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_g0t0_low : val g0t0_low = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0 : val g0 = mem (exec σ.ap))
    (htv_s0 : val s0 = mem (exec (σ.ap + 2)))
    (htv_t0 : val t0 = mem (exec (σ.ap + 4)))
    (htv_g0s0_high : val g0s0_high = mem (exec (σ.ap + 7)))
    (htv_g0t0_high : val g0t0_high = mem (exec (σ.ap + 8)))
    (htv_gs1 : val gs1 = mem (exec (σ.ap + 9)))
    (htv_gt1 : val gt1 = mem (exec (σ.ap + 10)))
    (htv_smalls_sum : val smalls_sum = mem (exec (σ.ap + 11)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_MERGE range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 13) (range_check + 6),
    VmRangeChecked loc.rc_vals (range_check + 6) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 95, ap := (σ.ap + 13), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 13) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 6) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, smalls_sum_fixed, h_smalls_sum_fixed, h_rc_smalls_sum_fixed, h_α98, h_α99, h_ρ_branch_id, h_ρ_n1_or_g0, h_ρ_k0_or_s0, h_ρ_n1k0_high_or_g0s0_high, h_ρ_n1k0_low_or_g0s0_low, h_ρ_n1_or_g0₁, h_ρ_k1_or_t0, h_ρ_n1k1_high_or_g0t0_high, h_ρ_n1k1_low_or_g0t0_low⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 13)) with
        | 0 => val smalls_sum_fixed
        | 1 => val 0
        | 2 => val 0
        | 3 => val 0
        | 4 => val 0
        | 5 => val 0
        | 6 => val 0
        | 7 => val 0
        | 8 => val 0
        | 9 => val 0
        | 10 => val 0
        | 11 => val 0
        | 12 => val 0
        | 13 => val 0
        | 14 => val 0
        | 15 => val 0
        | 16 => val 0
        | 17 => val 0
        | 18 => val 0
        | 19 => val 0
        | 20 => val 0
        | 21 => val 0
        | 22 => val 0
        | 23 => val 0
        | 24 => val 0
        | 25 => val 0
        | 26 => val 0
        | 27 => val 0
        | 28 => val 0
        | 29 => val 0
        | 30 => val 0
        | 31 => val 0
        | 32 => val 0
        | 33 => rc (range_check + 7)
        | 34 => val ρ_branch_id
        | 35 => val 0
        | 36 => val 0
        | 37 => val 0
        | 38 => val 0
        | 39 => val 0
        | 40 => val 0
        | 41 => val 0
        | 42 => val 0
        | 43 => val 0
        | 44 => val 0
        | 45 => val 0
        | 46 => val 0
        | 47 => val 0
        | 48 => val 0
        | 49 => val 0
        | 50 => val 0
        | 51 => val 0
        | 52 => val 0
        | 53 => val 0
        | 54 => val 0
        | 55 => val 0
        | 56 => val 0
        | 57 => val 0
        | 58 => val 0
        | 59 => val 0
        | 60 => val 0
        | 61 => val ρ_n1_or_g0
        | 62 => val ρ_k0_or_s0
        | 63 => val ρ_n1k0_high_or_g0s0_high
        | 64 => val ρ_n1k0_low_or_g0s0_low
        | 65 => val ρ_n1_or_g0₁
        | 66 => val ρ_k1_or_t0
        | 67 => val ρ_n1k1_high_or_g0t0_high
        | 68 => val ρ_n1k1_low_or_g0t0_low
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 6)) with
        | 0 => (↑smalls_sum_fixed : ℤ)
        | _ => (0 : ℤ)

  let loc := (⟨69, exec_vals, 1, rc_vals⟩ : LocalAssignment (σ.ap + 13) (range_check + 6))

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_of_lt mem loc (σ.ap + 7)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_of_lt mem loc (σ.ap + 8)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_13 := assign_exec_pos mem loc (σ.ap + 13)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_14 := assign_exec_pos mem loc (σ.ap + 14)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_15 := assign_exec_pos mem loc (σ.ap + 15)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_16 := assign_exec_pos mem loc (σ.ap + 16)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_17 := assign_exec_pos mem loc (σ.ap + 17)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_18 := assign_exec_pos mem loc (σ.ap + 18)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_19 := assign_exec_pos mem loc (σ.ap + 19)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_20 := assign_exec_pos mem loc (σ.ap + 20)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_21 := assign_exec_pos mem loc (σ.ap + 21)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_22 := assign_exec_pos mem loc (σ.ap + 22)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_23 := assign_exec_pos mem loc (σ.ap + 23)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_24 := assign_exec_pos mem loc (σ.ap + 24)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_25 := assign_exec_pos mem loc (σ.ap + 25)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_26 := assign_exec_pos mem loc (σ.ap + 26)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_27 := assign_exec_pos mem loc (σ.ap + 27)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_28 := assign_exec_pos mem loc (σ.ap + 28)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_29 := assign_exec_pos mem loc (σ.ap + 29)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_30 := assign_exec_pos mem loc (σ.ap + 30)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_31 := assign_exec_pos mem loc (σ.ap + 31)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_32 := assign_exec_pos mem loc (σ.ap + 32)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_33 := assign_exec_pos mem loc (σ.ap + 33)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_34 := assign_exec_pos mem loc (σ.ap + 34)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_35 := assign_exec_pos mem loc (σ.ap + 35)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_36 := assign_exec_pos mem loc (σ.ap + 36)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_37 := assign_exec_pos mem loc (σ.ap + 37)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_38 := assign_exec_pos mem loc (σ.ap + 38)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_39 := assign_exec_pos mem loc (σ.ap + 39)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_40 := assign_exec_pos mem loc (σ.ap + 40)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_41 := assign_exec_pos mem loc (σ.ap + 41)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_42 := assign_exec_pos mem loc (σ.ap + 42)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_43 := assign_exec_pos mem loc (σ.ap + 43)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_44 := assign_exec_pos mem loc (σ.ap + 44)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_45 := assign_exec_pos mem loc (σ.ap + 45)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_46 := assign_exec_pos mem loc (σ.ap + 46)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_47 := assign_exec_pos mem loc (σ.ap + 47)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_48 := assign_exec_pos mem loc (σ.ap + 48)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_49 := assign_exec_pos mem loc (σ.ap + 49)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_50 := assign_exec_pos mem loc (σ.ap + 50)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_51 := assign_exec_pos mem loc (σ.ap + 51)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_52 := assign_exec_pos mem loc (σ.ap + 52)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_53 := assign_exec_pos mem loc (σ.ap + 53)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_54 := assign_exec_pos mem loc (σ.ap + 54)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_55 := assign_exec_pos mem loc (σ.ap + 55)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_56 := assign_exec_pos mem loc (σ.ap + 56)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_57 := assign_exec_pos mem loc (σ.ap + 57)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_58 := assign_exec_pos mem loc (σ.ap + 58)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_59 := assign_exec_pos mem loc (σ.ap + 59)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_60 := assign_exec_pos mem loc (σ.ap + 60)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_61 := assign_exec_pos mem loc (σ.ap + 61)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_62 := assign_exec_pos mem loc (σ.ap + 62)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_63 := assign_exec_pos mem loc (σ.ap + 63)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_64 := assign_exec_pos mem loc (σ.ap + 64)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_65 := assign_exec_pos mem loc (σ.ap + 65)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_66 := assign_exec_pos mem loc (σ.ap + 66)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_67 := assign_exec_pos mem loc (σ.ap + 67)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_68 := assign_exec_pos mem loc (σ.ap + 68)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_69 := assign_exec_pos mem loc (σ.ap + 69)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_70 := assign_exec_pos mem loc (σ.ap + 70)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_71 := assign_exec_pos mem loc (σ.ap + 71)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_72 := assign_exec_pos mem loc (σ.ap + 72)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_73 := assign_exec_pos mem loc (σ.ap + 73)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_74 := assign_exec_pos mem loc (σ.ap + 74)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_75 := assign_exec_pos mem loc (σ.ap + 75)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_76 := assign_exec_pos mem loc (σ.ap + 76)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_77 := assign_exec_pos mem loc (σ.ap + 77)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_78 := assign_exec_pos mem loc (σ.ap + 78)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_79 := assign_exec_pos mem loc (σ.ap + 79)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_80 := assign_exec_pos mem loc (σ.ap + 80)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_81 := assign_exec_pos mem loc (σ.ap + 81)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_6 := assign_rc_pos mem loc (range_check + 6)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_rec
    · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
      apply h_rc_smalls_sum_fixed
    apply VmRangeChecked_zero
  vm_step_assert_eq hmem95 hmem, hmem96 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem96 hmem]
    simp only [h_ap_plus_13]
    simp only [h_ap_plus_11]
    simp only [←htv_smalls_sum]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_bound_minus_u65_bound] at h_smalls_sum_fixed
    simp only [h_smalls_sum_fixed]
  vm_step_assert_eq hmem97 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_13]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_6]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem98 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_minus_5]
    simp only [←htv_b1]
    simp only [h_ap_plus_9]
    simp only [←htv_gs1]
    simp only [h_ap_plus_7]
    simp only [←htv_g0s0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α98]
  vm_step_assert_eq hmem99 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_minus_3]
    simp only [←htv_n1]
    simp only [h_ap_plus_10]
    simp only [←htv_gt1]
    simp only [h_ap_plus_8]
    simp only [←htv_g0t0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α99]
  vm_step_jump_imm hmem100 hmem, hmem101 hmem
  vm_step_advance_ap hmem141 hmem, hmem142 hmem
  --   range check return value
  vm_step_assert_eq hmem143 hmem, hmem144 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem144 hmem]
    simp only [h_ap_plus_46]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_rc
  vm_step_assert_eq hmem145 hmem, hmem146 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem146 hmem]
    simp only [h_ap_plus_47]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_branch_id]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem147 hmem, hmem148 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem148 hmem]
    simp only [h_ap_plus_48]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem149 hmem, hmem150 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem150 hmem]
    simp only [h_ap_plus_49]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem151 hmem, hmem152 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem152 hmem]
    simp only [h_ap_plus_50]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem153 hmem, hmem154 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem154 hmem]
    simp only [h_ap_plus_51]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem155 hmem, hmem156 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem156 hmem]
    simp only [h_ap_plus_52]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem157 hmem, hmem158 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem158 hmem]
    simp only [h_ap_plus_53]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem159 hmem, hmem160 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem160 hmem]
    simp only [h_ap_plus_54]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem161 hmem, hmem162 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem162 hmem]
    simp only [h_ap_plus_55]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem163 hmem, hmem164 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem164 hmem]
    simp only [h_ap_plus_56]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem165 hmem, hmem166 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem166 hmem]
    simp only [h_ap_plus_57]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem167 hmem, hmem168 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem168 hmem]
    simp only [h_ap_plus_58]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem169 hmem, hmem170 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem170 hmem]
    simp only [h_ap_plus_59]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem171 hmem, hmem172 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem172 hmem]
    simp only [h_ap_plus_60]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem173 hmem, hmem174 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem174 hmem]
    simp only [h_ap_plus_61]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem175 hmem, hmem176 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem176 hmem]
    simp only [h_ap_plus_62]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem177 hmem, hmem178 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem178 hmem]
    simp only [h_ap_plus_63]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem179 hmem, hmem180 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem180 hmem]
    simp only [h_ap_plus_64]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem181 hmem, hmem182 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem182 hmem]
    simp only [h_ap_plus_65]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem183 hmem, hmem184 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem184 hmem]
    simp only [h_ap_plus_66]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem185 hmem, hmem186 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem186 hmem]
    simp only [h_ap_plus_67]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem187 hmem, hmem188 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem188 hmem]
    simp only [h_ap_plus_68]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem189 hmem, hmem190 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem190 hmem]
    simp only [h_ap_plus_69]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem191 hmem, hmem192 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem192 hmem]
    simp only [h_ap_plus_70]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem193 hmem, hmem194 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem194 hmem]
    simp only [h_ap_plus_71]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem195 hmem, hmem196 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem196 hmem]
    simp only [h_ap_plus_72]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem197 hmem, hmem198 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem198 hmem]
    simp only [h_ap_plus_73]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem199 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_74]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [←htv_g0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1_or_g0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem200 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_75]
    simp only [h_ap_plus_2]
    simp only [←htv_s0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k0_or_s0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem201 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_76]
    simp only [h_ap_plus_7]
    simp only [←htv_g0s0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k0_high_or_g0s0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem202 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_77]
    simp only [h_ap_minus_6]
    simp only [←htv_g0s0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k0_low_or_g0s0_low]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem203 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_78]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [←htv_g0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1_or_g0₁]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem204 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_79]
    simp only [h_ap_plus_4]
    simp only [←htv_t0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_k1_or_t0]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem205 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_80]
    simp only [h_ap_plus_8]
    simp only [←htv_g0t0_high]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k1_high_or_g0t0_high]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem206 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_81]
    simp only [h_ap_minus_4]
    simp only [←htv_g0t0_low]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_ρ_n1k1_low_or_g0t0_low]
    apply Mrel.Equiv.refl_val
  apply ret_returns
  apply hmem207 hmem
  constructor
  · vm_arith_simps
  simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero]
  simp only [add_sub_assoc] ; norm_num1
  simp only [h_ap_plus_46]
  try dsimp [exec_vals, rc_vals]
  try ring_nf
  try rfl
  done

theorem complete_u256_guarantee_inv_mod_n_G1IsSmall_from_spec
    -- arguments
    (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_g0s0_low : val g0s0_low = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_g0t0_low : val g0t0_low = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0 : val g0 = mem (exec σ.ap))
    (htv_g1 : val g1 = mem (exec (σ.ap + 1)))
    (htv_s0 : val s0 = mem (exec (σ.ap + 2)))
    (htv_t0 : val t0 = mem (exec (σ.ap + 4)))
    (htv_g0s0_high : val g0s0_high = mem (exec (σ.ap + 7)))
    (htv_g0t0_high : val g0t0_high = mem (exec (σ.ap + 8)))
    (htv_gs1 : val gs1 = mem (exec (σ.ap + 9)))
    (htv_gt1 : val gt1 = mem (exec (σ.ap + 10)))
    (htv_smalls_sum : val smalls_sum = mem (exec (σ.ap + 11)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_G1IsSmall range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 13) (range_check + 6),
    VmRangeChecked loc.rc_vals (range_check + 6) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 94, ap := (σ.ap + 13), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 13) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 6) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_α94, h_block_MERGE⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 13)) with
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 6)) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨0, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 13) (range_check + 6))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0s0_low]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0t0_low]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
    simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
  have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
  have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
  have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 7) (by apply Int.add_lt_add_left ; norm_num1), htv_g0s0_high]
  have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 8) (by apply Int.add_lt_add_left ; norm_num1), htv_g0t0_high]
  have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 9) (by apply Int.add_lt_add_left ; norm_num1), htv_gs1]
  have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 10) (by apply Int.add_lt_add_left ; norm_num1), htv_gt1]
  have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 11) (by apply Int.add_lt_add_left ; norm_num1), htv_smalls_sum]
  have h_MERGE := complete_u256_guarantee_inv_mod_n_MERGE_from_spec
    (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_MERGE⟩

  have h_ap_concat : (σ.ap + 13) = (σ.ap + 13) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_MERGE with ⟨loc₁, h_rc_MERGE, h_MERGE⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_of_lt mem loc (σ.ap + 7)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_of_lt mem loc (σ.ap + 8)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
    (by apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_MERGE
  vm_step_assert_eq hmem94 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_11]
    simp only [←htv_smalls_sum]
    simp only [h_ap_plus_1]
    simp only [←htv_g1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_α94]
    apply Mrel.Equiv.refl_val
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_MERGE
  done

theorem complete_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO_from_spec
    -- arguments
    (range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_g0s0_low : val g0s0_low = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_g0t0_low : val g0t0_low = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0 : val g0 = mem (exec σ.ap))
    (htv_g1 : val g1 = mem (exec (σ.ap + 1)))
    (htv_s0 : val s0 = mem (exec (σ.ap + 2)))
    (htv_s1 : val s1 = mem (exec (σ.ap + 3)))
    (htv_t0 : val t0 = mem (exec (σ.ap + 4)))
    (htv_t1 : val t1 = mem (exec (σ.ap + 5)))
    (htv_g0s0_high : val g0s0_high = mem (exec (σ.ap + 7)))
    (htv_g0t0_high : val g0t0_high = mem (exec (σ.ap + 8)))
    (htv_gs1 : val gs1 = mem (exec (σ.ap + 9)))
    (htv_gt1 : val gt1 = mem (exec (σ.ap + 10)))
    (htv_smalls_sum : val smalls_sum = mem (exec (σ.ap + 11)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 12) (range_check + 6),
    VmRangeChecked loc.rc_vals (range_check + 6) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 83, ap := (σ.ap + 8), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 12) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 6) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_α83, h_α84, h_α85, h_α87, g1_is_small, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_g1_is_small, h_α91, h_block_MERGE⟩
    let exec_vals :=
        fun (i : ℤ) =>
          match (i - (σ.ap + 12)) with
          | 0 => val g1_is_small
          | _ => val 0

    let rc_vals :=
        fun (i : ℤ) =>
          match (i - (range_check + 6)) with
          | _ => (0 : ℤ)

    let loc₀ := (⟨1, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 12) (range_check + 6))

    have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
      have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
        (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      simp only [this, htv_range_check]
    have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
      have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
        (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      simp only [this, htv_g0s0_low]
    have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
      have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
        (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      simp only [this, htv_b1]
    have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
      have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
        (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      simp only [this, htv_g0t0_low]
    have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
      have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
        (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      simp only [this, htv_n1]
    have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
      simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
    have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
    have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
    have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 7) (by apply Int.add_lt_add_left ; norm_num1), htv_g0s0_high]
    have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 8) (by apply Int.add_lt_add_left ; norm_num1), htv_g0t0_high]
    have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 9) (by apply Int.add_lt_add_left ; norm_num1), htv_gs1]
    have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 10) (by apply Int.add_lt_add_left ; norm_num1), htv_gt1]
    have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
      simp only [assign_exec_of_lt mem loc₀ (σ.ap + 11) (by apply Int.add_lt_add_left ; norm_num1), htv_smalls_sum]
    have h_MERGE := complete_u256_guarantee_inv_mod_n_MERGE_from_spec
      (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_MERGE⟩

    have h_ap_concat : (σ.ap + 13) = (σ.ap + 12) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
    have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
    rcases h_MERGE with ⟨loc₁, h_rc_MERGE, h_MERGE⟩

    let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

    have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
      (by apply Int.lt_add_of_pos_right ; norm_num1)
    have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_7 := assign_exec_of_lt mem loc (σ.ap + 7)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_8 := assign_exec_of_lt mem loc (σ.ap + 8)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
      (by apply Int.add_lt_add_left ; norm_num1)
    have h_ap_plus_12 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 12)
      (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

    use loc
    constructor
    · apply VmRangeChecked_concat
      · apply VmRangeChecked_zero
      apply h_rc_MERGE
    vm_step_assert_eq hmem83 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_9]
      simp only [←htv_gs1]
      simp only [h_ap_plus_2]
      simp only [←htv_s0]
      simp only [h_ap_plus_1]
      simp only [←htv_g1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [h_α83]
    vm_step_assert_eq hmem84 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_10]
      simp only [←htv_gt1]
      simp only [h_ap_plus_4]
      simp only [←htv_t0]
      simp only [h_ap_plus_1]
      simp only [←htv_g1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [h_α84]
    vm_step_assert_eq hmem85 hmem, hmem86 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem86 hmem]
      simp only [h_ap_plus_3]
      simp only [←htv_s1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      simp only [zero] at h_α85
      simp only [h_α85]
      apply Mrel.Equiv.refl_val
    vm_step_assert_eq hmem87 hmem, hmem88 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      rw [assign_prog] ; rw [hmem88 hmem]
      simp only [h_ap_plus_5]
      simp only [←htv_t1]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      simp only [zero] at h_α87
      simp only [h_α87]
      apply Mrel.Equiv.refl_val
    vm_step_jnz hmem89 hmem, hmem90 hmem
    -- g1_is_small = 0
    swap
    · norm_num1
      simp only [h_ap_plus_12]
      dsimp [exec_vals]
      simp only [Int.add_comm σ.ap 12, Int.add_sub_cancel]
      ring_nf ; simp only [val.injEq, Int.reduceNeg]
      simp only [hc_g1_is_small]
      simp only [not_true, false_implies]
    intro _
    vm_step_assert_eq hmem91 hmem
    constructor
    · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
      try norm_num1
      try simp only [hin_fp]
      simp only [h_ap_plus_11]
      simp only [←htv_smalls_sum]
      simp only [h_ap_plus_2]
      simp only [←htv_s0]
      simp only [h_ap_plus_4]
      simp only [←htv_t0]
      try dsimp [exec_vals, rc_vals]
      try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
      dsimp [Mrel.Equiv]
      simp only [h_α91]
    vm_step_jump_imm hmem92 hmem, hmem93 hmem
    rw [assign_concat, concat_exec_num, concat_rc_num]
    simp only [Nat.cast_add]
    try simp only [Nat.cast_zero, Int.zero_add]
    try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
    try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
    norm_num1
    try simp only [←Int.add_assoc]
    apply h_MERGE
  rcases h_spec with ⟨hc_g1_is_small, h_block_G1IsSmall⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 12)) with
        | 0 => val g1_is_small
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 6)) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨1, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 12) (range_check + 6))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0s0_low]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0t0_low]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
    simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
  have h_g1_ap : val ↑g1 = Assign mem loc₀ (exec (σ.ap + 1)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 1) (by apply Int.add_lt_add_left ; norm_num1), htv_g1]
  have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
  have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
  have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 7) (by apply Int.add_lt_add_left ; norm_num1), htv_g0s0_high]
  have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 8) (by apply Int.add_lt_add_left ; norm_num1), htv_g0t0_high]
  have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 9) (by apply Int.add_lt_add_left ; norm_num1), htv_gs1]
  have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 10) (by apply Int.add_lt_add_left ; norm_num1), htv_gt1]
  have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 11) (by apply Int.add_lt_add_left ; norm_num1), htv_smalls_sum]
  have h_G1IsSmall := complete_u256_guarantee_inv_mod_n_G1IsSmall_from_spec
    (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_g1_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_G1IsSmall⟩

  have h_ap_concat : (σ.ap + 13) = (σ.ap + 12) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_G1IsSmall with ⟨loc₁, h_rc_G1IsSmall, h_G1IsSmall⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_of_lt mem loc (σ.ap + 7)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_of_lt mem loc (σ.ap + 8)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_12 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 12)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_G1IsSmall
  vm_step_assert_eq hmem83 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_9]
    simp only [←htv_gs1]
    simp only [h_ap_plus_2]
    simp only [←htv_s0]
    simp only [h_ap_plus_1]
    simp only [←htv_g1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α83]
  vm_step_assert_eq hmem84 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_10]
    simp only [←htv_gt1]
    simp only [h_ap_plus_4]
    simp only [←htv_t0]
    simp only [h_ap_plus_1]
    simp only [←htv_g1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α84]
  vm_step_assert_eq hmem85 hmem, hmem86 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem86 hmem]
    simp only [h_ap_plus_3]
    simp only [←htv_s1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [zero] at h_α85
    simp only [h_α85]
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem87 hmem, hmem88 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem88 hmem]
    simp only [h_ap_plus_5]
    simp only [←htv_t1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [zero] at h_α87
    simp only [h_α87]
    apply Mrel.Equiv.refl_val
  vm_step_jnz hmem89 hmem, hmem90 hmem
  -- g1_is_small ≠ 0
  · norm_num1
    simp only [h_ap_plus_12]
    dsimp [exec_vals]
    simp only [Int.add_comm σ.ap 12, Int.add_sub_cancel]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_g1_is_small
    injection h_cond
  intro _
  simp only [assign_prog, hmem90 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_G1IsSmall
  done

theorem complete_u256_guarantee_inv_mod_n_G0IsSmall_from_spec
    -- arguments
    (range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_g0s0_low : val g0s0_low = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_g0t0_low : val g0t0_low = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0 : val g0 = mem (exec σ.ap))
    (htv_s0 : val s0 = mem (exec (σ.ap + 2)))
    (htv_t0 : val t0 = mem (exec (σ.ap + 4)))
    (htv_g0s0_high : val g0s0_high = mem (exec (σ.ap + 7)))
    (htv_g0t0_high : val g0t0_high = mem (exec (σ.ap + 8)))
    (htv_gs1 : val gs1 = mem (exec (σ.ap + 9)))
    (htv_gt1 : val gt1 = mem (exec (σ.ap + 10)))
    (htv_smalls_sum : val smalls_sum = mem (exec (σ.ap + 11)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_G0IsSmall range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 13) (range_check + 6),
    VmRangeChecked loc.rc_vals (range_check + 6) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 80, ap := (σ.ap + 11), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 13) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 6) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_α80, h_block_MERGE⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 13)) with
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 6)) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨0, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 13) (range_check + 6))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0s0_low]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_g0t0_low]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
    simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
  have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
  have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
  have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 7) (by apply Int.add_lt_add_left ; norm_num1), htv_g0s0_high]
  have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 8) (by apply Int.add_lt_add_left ; norm_num1), htv_g0t0_high]
  have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 9) (by apply Int.add_lt_add_left ; norm_num1), htv_gs1]
  have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 10) (by apply Int.add_lt_add_left ; norm_num1), htv_gt1]
  have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 11) (by apply Int.add_lt_add_left ; norm_num1), htv_smalls_sum]
  have h_MERGE := complete_u256_guarantee_inv_mod_n_MERGE_from_spec
    (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_MERGE⟩

  have h_ap_concat : (σ.ap + 13) = (σ.ap + 13) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_MERGE with ⟨loc₁, h_rc_MERGE, h_MERGE⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_of_lt mem loc (σ.ap + 7)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_of_lt mem loc (σ.ap + 8)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_of_lt mem loc (σ.ap + 9)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_of_lt mem loc (σ.ap + 10)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_of_lt mem loc (σ.ap + 11)
    (by apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_MERGE
  vm_step_assert_eq hmem80 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_11]
    simp only [←htv_smalls_sum]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [←htv_g0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    simp only [h_α80]
    apply Mrel.Equiv.refl_val
  vm_step_jump_imm hmem81 hmem, hmem82 hmem
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_MERGE
  done

#exit

theorem complete_u256_guarantee_inv_mod_n_GIsValid_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0 : val g0 = mem (exec σ.ap))
    (htv_g1 : val g1 = mem (exec (σ.ap + 1)))
    (htv_s0 : val s0 = mem (exec (σ.ap + 2)))
    (htv_s1 : val s1 = mem (exec (σ.ap + 3)))
    (htv_t0 : val t0 = mem (exec (σ.ap + 4)))
    (htv_t1 : val t1 = mem (exec (σ.ap + 5)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_GIsValid range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 7) (range_check + 6),
    VmRangeChecked loc.rc_vals (range_check + 6) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 71, ap := (σ.ap + 7), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 7) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 6) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, g0s0_low, h_g0s0_low, g0s0_high, g0t0_low, h_g0t0_low, g0t0_high, gs1, gt1, smalls_sum, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_g1, h_α73, h_α74, g0_is_small, h_spec|h_spec⟩
    · rcases h_spec with ⟨hc_g0_is_small, h_α77, h_block_MERGE⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - (σ.ap + 7)) with
            | 0 => val g0s0_high
            | 1 => val g0t0_high
            | 2 => val gs1
            | 3 => val gt1
            | 4 => val smalls_sum
            | 5 => val g0_is_small
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - (range_check + 6)) with
            | _ => (0 : ℤ)

      let loc₀ := (⟨6, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 7) (range_check + 6))

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_range_check]
      have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, h_g0s0_low, htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b1]
      have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, h_g0t0_low, htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n1]
      have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
        simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
      have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
      have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
      have h_g0s0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 7)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
        simp only [h_g0s0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_g0t0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 8)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
        simp only [h_g0t0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_gs1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 9)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
        simp only [h_gs1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_gt1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 10)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
        simp only [h_gt1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_smalls_sum_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 11)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
        simp only [h_smalls_sum_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_MERGE := complete_u256_guarantee_inv_mod_n_MERGE_from_spec
        (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_MERGE⟩

      have h_ap_concat : (σ.ap + 13) = (σ.ap + 7) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_MERGE with ⟨loc₁, h_rc_MERGE, h_MERGE⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
        (by apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_7 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 7)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_8 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 8)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_9 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 9)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_10 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 10)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_11 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 11)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_12 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 12)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_zero
        apply h_rc_MERGE
      vm_step_jnz hmem71 hmem, hmem72 hmem
      -- g1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_1]
        simp only [←htv_g1]
        simp only [hc_g1]
        simp only [ne_self_iff_false, false_implies]
      intro _
      vm_step_assert_eq hmem73 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_9]
        simp only [h_ap_plus_3]
        simp only [←htv_s1]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←htv_g0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        dsimp [Mrel.Equiv]
        simp only [h_α73]
      vm_step_assert_eq hmem74 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_10]
        simp only [h_ap_plus_5]
        simp only [←htv_t1]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←htv_g0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        dsimp [Mrel.Equiv]
        simp only [h_α74]
      vm_step_jnz hmem75 hmem, hmem76 hmem
      -- g0_is_small = 0
      swap
      · norm_num1
        simp only [h_ap_plus_12]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 12, Int.add_sub_cancel]
        ring_nf ; simp only [val.injEq, Int.reduceNeg]
        simp only [hc_g0_is_small]
        simp only [not_true, false_implies]
      intro _
      vm_step_assert_eq hmem77 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_11]
        simp only [h_ap_plus_3]
        simp only [←htv_s1]
        simp only [h_ap_plus_5]
        simp only [←htv_t1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        dsimp [Mrel.Equiv]
        simp only [h_α77]
      vm_step_jump_imm hmem78 hmem, hmem79 hmem
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_MERGE
    · rcases h_spec with ⟨hc_g0_is_small, h_block_G0IsSmall⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - (σ.ap + 7)) with
            | 0 => val g0s0_high
            | 1 => val g0t0_high
            | 2 => val gs1
            | 3 => val gt1
            | 4 => val smalls_sum
            | 5 => val g0_is_small
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - (range_check + 6)) with
            | _ => (0 : ℤ)

      let loc₀ := (⟨6, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 7) (range_check + 6))

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_range_check]
      have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, h_g0s0_low, htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b1]
      have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, h_g0t0_low, htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n1]
      have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
        simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
      have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
      have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
      have h_g0s0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 7)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
        simp only [h_g0s0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_g0t0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 8)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
        simp only [h_g0t0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_gs1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 9)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
        simp only [h_gs1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_gt1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 10)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
        simp only [h_gt1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_smalls_sum_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 11)
        (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
        simp only [h_smalls_sum_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_G0IsSmall := complete_u256_guarantee_inv_mod_n_G0IsSmall_from_spec
        (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 s0 t0 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_s0_ap h_t0_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_G0IsSmall⟩

      have h_ap_concat : (σ.ap + 13) = (σ.ap + 7) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_G0IsSmall with ⟨loc₁, h_rc_G0IsSmall, h_G0IsSmall⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
        (by apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_7 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 7)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_8 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 8)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_9 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 9)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_10 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 10)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_11 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 11)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_12 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 12)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_zero
        apply h_rc_G0IsSmall
      vm_step_jnz hmem71 hmem, hmem72 hmem
      -- g1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_1]
        simp only [←htv_g1]
        simp only [hc_g1]
        simp only [ne_self_iff_false, false_implies]
      intro _
      vm_step_assert_eq hmem73 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_9]
        simp only [h_ap_plus_3]
        simp only [←htv_s1]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←htv_g0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        dsimp [Mrel.Equiv]
        simp only [h_α73]
      vm_step_assert_eq hmem74 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_10]
        simp only [h_ap_plus_5]
        simp only [←htv_t1]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←htv_g0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        dsimp [Mrel.Equiv]
        simp only [h_α74]
      vm_step_jnz hmem75 hmem, hmem76 hmem
      -- g0_is_small ≠ 0
      · norm_num1
        simp only [h_ap_plus_12]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 12, Int.add_sub_cancel]
        intro h_cond
        try ring_nf at h_cond
        exfalso
        apply hc_g0_is_small
        injection h_cond
      intro _
      simp only [assign_prog, hmem76 hmem, Mrel.toInt]
      vm_arith_simps
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_G0IsSmall
  rcases h_spec with ⟨hc_g1, h_block_S1_AND_T1_EQ_ZERO⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 7)) with
        | 0 => val g0s0_high
        | 1 => val g0t0_high
        | 2 => val gs1
        | 3 => val gt1
        | 4 => val smalls_sum
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 6)) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨5, exec_vals, 0, rc_vals⟩ : LocalAssignment (σ.ap + 7) (range_check + 6))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_g0s0_low_ap : val ↑g0s0_low = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, h_g0s0_low, htv_b0]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_g0t0_low_ap : val ↑g0t0_low = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, h_g0t0_low, htv_n0]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
    simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), htv_g0]
  have h_g1_ap : val ↑g1 = Assign mem loc₀ (exec (σ.ap + 1)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 1) (by apply Int.add_lt_add_left ; norm_num1), htv_g1]
  have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_s0]
  have h_s1_ap : val ↑s1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), htv_s1]
  have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_t0]
  have h_t1_ap : val ↑t1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), htv_t1]
  have h_g0s0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 7)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_g0s0_high_ap : val ↑g0s0_high = Assign mem loc₀ (exec (σ.ap + 7)) := by
    simp only [h_g0s0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_g0t0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 8)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_g0t0_high_ap : val ↑g0t0_high = Assign mem loc₀ (exec (σ.ap + 8)) := by
    simp only [h_g0t0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_gs1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 9)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_gs1_ap : val ↑gs1 = Assign mem loc₀ (exec (σ.ap + 9)) := by
    simp only [h_gs1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_gt1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 10)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_gt1_ap : val ↑gt1 = Assign mem loc₀ (exec (σ.ap + 10)) := by
    simp only [h_gt1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_smalls_sum_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 11)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_smalls_sum_ap : val ↑smalls_sum = Assign mem loc₀ (exec (σ.ap + 11)) := by
    simp only [h_smalls_sum_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_S1_AND_T1_EQ_ZERO := complete_u256_guarantee_inv_mod_n_S1_AND_T1_EQ_ZERO_from_spec
    (Assign mem loc₀) σ range_check g0s0_low b1 g0t0_low n1 g0 g1 s0 s1 t0 t1 g0s0_high g0t0_high gs1 gt1 smalls_sum hmem hin_fp h_range_check_ap h_g0s0_low_ap h_b1_ap h_g0t0_low_ap h_n1_ap h_g0_ap h_g1_ap h_s0_ap h_s1_ap h_t0_ap h_t1_ap h_g0s0_high_ap h_g0t0_high_ap h_gs1_ap h_gt1_ap h_smalls_sum_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_S1_AND_T1_EQ_ZERO⟩

  have h_ap_concat : (σ.ap + 12) = (σ.ap + 7) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 6) = (range_check + 6) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_S1_AND_T1_EQ_ZERO with ⟨loc₁, h_rc_S1_AND_T1_EQ_ZERO, h_S1_AND_T1_EQ_ZERO⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_7 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 7)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_8 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 8)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 9)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 10)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 11)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_S1_AND_T1_EQ_ZERO
  vm_step_jnz hmem71 hmem, hmem72 hmem
  -- g1 ≠ 0
  · norm_num1
    simp only [h_ap_plus_1]
    simp only [←htv_g1]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_g1
    injection h_cond
  intro _
  simp only [assign_prog, hmem72 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_S1_AND_T1_EQ_ZERO
  done

theorem complete_u256_guarantee_inv_mod_n_NoInverse_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_g0_or_no_inv : val g0_or_no_inv = mem (exec σ.ap))
    (htv_g1_option : val g1_option = mem (exec (σ.ap + 1)))
    (htv_s_or_r0 : val s_or_r0 = mem (exec (σ.ap + 2)))
    (htv_s_or_r1 : val s_or_r1 = mem (exec (σ.ap + 3)))
    (htv_t_or_k0 : val t_or_k0 = mem (exec (σ.ap + 4)))
    (htv_t_or_k1 : val t_or_k1 = mem (exec (σ.ap + 5)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_NoInverse range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 6) (range_check + 0),
    VmRangeChecked loc.rc_vals (range_check + 0) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 55, ap := (σ.ap + 1), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 6) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, g0, h_g0, g1, h_g1, s0, h_s0, s1, h_s1, t0, h_t0, t1, h_t1, h_rc_g0, h_rc_g1, h_rc_s0, h_rc_s1, h_rc_t0, h_rc_t1, g0_minus_1, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_g1, h_α63, h_spec|h_spec⟩
    · rcases h_spec with ⟨hc_g0_minus_1, h_α67, h_α69, h_block_GIsValid⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - (σ.ap + 6)) with
            | 0 => val g0_minus_1
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - range_check) with
            | 0 => (↑g0 : ℤ)
            | 1 => (↑g1 : ℤ)
            | 2 => (↑s0 : ℤ)
            | 3 => (↑s1 : ℤ)
            | 4 => (↑t0 : ℤ)
            | 5 => (↑t1 : ℤ)
            | _ => (0 : ℤ)

      let loc₀ := (⟨1, exec_vals, 6, rc_vals⟩ : LocalAssignment (σ.ap + 6) (range_check + 0))

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_range_check]
      have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b1]
      have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n1]
      have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
        simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), h_g0, htv_g0_or_no_inv]
      have h_g1_ap : val ↑g1 = Assign mem loc₀ (exec (σ.ap + 1)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 1) (by apply Int.add_lt_add_left ; norm_num1), h_g1, htv_g1_option]
      have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), h_s0, htv_s_or_r0]
      have h_s1_ap : val ↑s1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), h_s1, htv_s_or_r1]
      have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), h_t0, htv_t_or_k0]
      have h_t1_ap : val ↑t1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), h_t1, htv_t_or_k1]
      have h_GIsValid := complete_u256_guarantee_inv_mod_n_GIsValid_from_spec
        (Assign mem loc₀) σ range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_g0_ap h_g1_ap h_s0_ap h_s1_ap h_t0_ap h_t1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_GIsValid⟩

      have h_ap_concat : (σ.ap + 7) = (σ.ap + 6) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 6) = (range_check + 0) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_GIsValid with ⟨loc₁, h_rc_GIsValid, h_GIsValid⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
        (by apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_3 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 3)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_4 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 4)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_5 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 5)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_t1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_t0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_s1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_s0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_g1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_g0
          apply VmRangeChecked_zero
        apply h_rc_GIsValid
      vm_step_assert_eq hmem55 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←h_g0, ←htv_g0_or_no_inv]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem56 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_1]
        simp only [←h_g1, ←htv_g1_option]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem57 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_2]
        simp only [←h_s0, ←htv_s_or_r0]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_2]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem58 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_3]
        simp only [←h_s1, ←htv_s_or_r1]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem59 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_4]
        simp only [←h_t0, ←htv_t_or_k0]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_4]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem60 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_5]
        simp only [←h_t1, ←htv_t_or_k1]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_5]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_jnz hmem61 hmem, hmem62 hmem
      -- g1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_1]
        simp only [←h_g1, ←htv_g1_option]
        simp only [hc_g1]
        simp only [ne_self_iff_false, false_implies]
      intro _
      vm_step_assert_eq hmem63 hmem, hmem64 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        rw [assign_prog] ; rw [hmem64 hmem]
        simp only [h_ap_plus_6]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←h_g0, ←htv_g0_or_no_inv]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α63
        dsimp [Mrel.Equiv]
        simp only [one] at h_α63
        simp only [h_α63]
      vm_step_jnz hmem65 hmem, hmem66 hmem
      -- g0_minus_1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_6]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 6, Int.add_sub_cancel]
        ring_nf ; simp only [val.injEq, Int.reduceNeg]
        simp only [hc_g0_minus_1]
        simp only [not_true, false_implies]
      intro _
      vm_step_assert_eq hmem67 hmem, hmem68 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        rw [assign_prog] ; rw [hmem68 hmem]
        simp only [h_ap_minus_3]
        simp only [←htv_n1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        simp only [zero] at h_α67
        simp only [h_α67]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem69 hmem, hmem70 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        rw [assign_prog] ; rw [hmem70 hmem]
        simp only [h_ap_minus_4]
        simp only [←htv_n0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        simp only [one] at h_α69
        simp only [h_α69]
        apply Mrel.Equiv.refl_val
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_GIsValid
    · rcases h_spec with ⟨hc_g0_minus_1, h_block_GIsValid⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - (σ.ap + 6)) with
            | 0 => val g0_minus_1
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - range_check) with
            | 0 => (↑g0 : ℤ)
            | 1 => (↑g1 : ℤ)
            | 2 => (↑s0 : ℤ)
            | 3 => (↑s1 : ℤ)
            | 4 => (↑t0 : ℤ)
            | 5 => (↑t1 : ℤ)
            | _ => (0 : ℤ)

      let loc₀ := (⟨1, exec_vals, 6, rc_vals⟩ : LocalAssignment (σ.ap + 6) (range_check + 0))

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_range_check]
      have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_b1]
      have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
          (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
        simp only [this, htv_n1]
      have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
        simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), h_g0, htv_g0_or_no_inv]
      have h_g1_ap : val ↑g1 = Assign mem loc₀ (exec (σ.ap + 1)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 1) (by apply Int.add_lt_add_left ; norm_num1), h_g1, htv_g1_option]
      have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), h_s0, htv_s_or_r0]
      have h_s1_ap : val ↑s1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), h_s1, htv_s_or_r1]
      have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), h_t0, htv_t_or_k0]
      have h_t1_ap : val ↑t1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), h_t1, htv_t_or_k1]
      have h_GIsValid := complete_u256_guarantee_inv_mod_n_GIsValid_from_spec
        (Assign mem loc₀) σ range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_g0_ap h_g1_ap h_s0_ap h_s1_ap h_t0_ap h_t1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_GIsValid⟩

      have h_ap_concat : (σ.ap + 7) = (σ.ap + 6) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 6) = (range_check + 0) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_GIsValid with ⟨loc₁, h_rc_GIsValid, h_GIsValid⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
        (by apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
        (by apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_3 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 3)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_4 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 4)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_5 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 5)
        (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_t1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_t0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_s1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_s0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_g1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_g0
          apply VmRangeChecked_zero
        apply h_rc_GIsValid
      vm_step_assert_eq hmem55 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←h_g0, ←htv_g0_or_no_inv]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem56 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_1]
        simp only [←h_g1, ←htv_g1_option]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem57 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_2]
        simp only [←h_s0, ←htv_s_or_r0]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_2]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem58 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_3]
        simp only [←h_s1, ←htv_s_or_r1]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem59 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_4]
        simp only [←h_t0, ←htv_t_or_k0]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_4]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem60 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_5]
        simp only [←h_t1, ←htv_t_or_k1]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_5]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_jnz hmem61 hmem, hmem62 hmem
      -- g1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_1]
        simp only [←h_g1, ←htv_g1_option]
        simp only [hc_g1]
        simp only [ne_self_iff_false, false_implies]
      intro _
      vm_step_assert_eq hmem63 hmem, hmem64 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        rw [assign_prog] ; rw [hmem64 hmem]
        simp only [h_ap_plus_6]
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        simp only [←h_g0, ←htv_g0_or_no_inv]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α63
        dsimp [Mrel.Equiv]
        simp only [one] at h_α63
        simp only [h_α63]
      vm_step_jnz hmem65 hmem, hmem66 hmem
      -- g0_minus_1 ≠ 0
      · norm_num1
        simp only [h_ap_plus_6]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 6, Int.add_sub_cancel]
        intro h_cond
        try ring_nf at h_cond
        exfalso
        apply hc_g0_minus_1
        injection h_cond
      intro _
      simp only [assign_prog, hmem66 hmem, Mrel.toInt]
      vm_arith_simps
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_GIsValid
  rcases h_spec with ⟨hc_g1, h_block_GIsValid⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 6)) with
        | 0 => val g0_minus_1
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | 0 => (↑g0 : ℤ)
        | 1 => (↑g1 : ℤ)
        | 2 => (↑s0 : ℤ)
        | 3 => (↑s1 : ℤ)
        | 4 => (↑t0 : ℤ)
        | 5 => (↑t1 : ℤ)
        | _ => (0 : ℤ)

  let loc₀ := (⟨1, exec_vals, 6, rc_vals⟩ : LocalAssignment (σ.ap + 6) (range_check + 0))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b0]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n0]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_g0_ap : val ↑g0 = Assign mem loc₀ (exec σ.ap) := by
    simp only [assign_exec_of_lt mem loc₀ σ.ap (by apply Int.lt_add_of_pos_right ; norm_num1), h_g0, htv_g0_or_no_inv]
  have h_g1_ap : val ↑g1 = Assign mem loc₀ (exec (σ.ap + 1)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 1) (by apply Int.add_lt_add_left ; norm_num1), h_g1, htv_g1_option]
  have h_s0_ap : val ↑s0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), h_s0, htv_s_or_r0]
  have h_s1_ap : val ↑s1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), h_s1, htv_s_or_r1]
  have h_t0_ap : val ↑t0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), h_t0, htv_t_or_k0]
  have h_t1_ap : val ↑t1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), h_t1, htv_t_or_k1]
  have h_GIsValid := complete_u256_guarantee_inv_mod_n_GIsValid_from_spec
    (Assign mem loc₀) σ range_check b0 b1 n0 n1 g0 g1 s0 s1 t0 t1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_g0_ap h_g1_ap h_s0_ap h_s1_ap h_t0_ap h_t1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_GIsValid⟩

  have h_ap_concat : (σ.ap + 7) = (σ.ap + 6) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 6) = (range_check + 0) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_GIsValid with ⟨loc₁, h_rc_GIsValid, h_GIsValid⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_of_lt mem loc σ.ap
    (by apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_of_lt mem loc (σ.ap + 1)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_3 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 3)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_4 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 4)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_5 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 5)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_t1
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_t0
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_s1
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_s0
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_g1
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_g0
      apply VmRangeChecked_zero
    apply h_rc_GIsValid
  vm_step_assert_eq hmem55 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    simp only [←h_g0, ←htv_g0_or_no_inv]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_0]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem56 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_1]
    simp only [←h_g1, ←htv_g1_option]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_1]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem57 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_2]
    simp only [←h_s0, ←htv_s_or_r0]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_2]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem58 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_3]
    simp only [←h_s1, ←htv_s_or_r1]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_3]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem59 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_4]
    simp only [←h_t0, ←htv_t_or_k0]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem60 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_5]
    simp only [←h_t1, ←htv_t_or_k1]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_jnz hmem61 hmem, hmem62 hmem
  -- g1 ≠ 0
  · norm_num1
    simp only [h_ap_plus_1]
    simp only [←h_g1, ←htv_g1_option]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_g1
    injection h_cond
  intro _
  simp only [assign_prog, hmem62 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_GIsValid
  done

theorem complete_u256_guarantee_inv_mod_n_After_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 r0 r1 k0 k1 : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_r0 : val r0 = mem (exec (σ.ap + 2)))
    (htv_r1 : val r1 = mem (exec (σ.ap + 3)))
    (htv_k0 : val k0 = mem (exec (σ.ap + 4)))
    (htv_k1 : val k1 = mem (exec (σ.ap + 5)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_After range_check b0 b1 n0 n1 r0 r1 k0 k1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 9) (range_check + 5),
    VmRangeChecked loc.rc_vals (range_check + 5) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 18, ap := (σ.ap + 24), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 9) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 5) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, r0b0_low, r0b0_high, r0b1_low, r0b1_high, r1b0_low, r1b0_high, r1b1_low, r1b1_high, n0k0_low, n0k0_high, n0k1_low, n0k1_high, n1k0_low, n1k0_high, n1k1_low, n1k1_high, part0, h_part0, part1, h_part1, leftover, h_leftover, h_α23, part0₁, h_part0₁, part1₁, h_part1₁, part2, h_part2, part3, h_part3, part4, h_part4, part5, h_part5, leftover₁, h_leftover₁, a, h_a, h_rc_a, a₁, h_a₁, h_rc_a₁, part0₂, h_part0₂, part1₂, h_part1₂, part2₁, h_part2₁, part3₁, h_part3₁, part4₁, h_part4₁, part5₁, h_part5₁, leftover₂, h_leftover₂, a₂, h_a₂, h_rc_a₂, a₃, h_a₃, h_rc_a₃, h_α52, h_block_Done⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 9)) with
        | 0 => val r0b0_low
        | 1 => val r0b0_high
        | 2 => val r0b1_low
        | 3 => val r0b1_high
        | 4 => val r1b0_low
        | 5 => val r1b0_high
        | 6 => val r1b1_low
        | 7 => val r1b1_high
        | 8 => val n0k0_low
        | 9 => val n0k0_high
        | 10 => val n0k1_low
        | 11 => val n0k1_high
        | 12 => val n1k0_low
        | 13 => val n1k0_high
        | 14 => val n1k1_low
        | 15 => val n1k1_high
        | 16 => val part0
        | 17 => val part1
        | 18 => val leftover
        | 19 => val part0₁
        | 20 => val part1₁
        | 21 => val part2
        | 22 => val part3
        | 23 => val part4
        | 24 => val part5
        | 25 => val leftover₁
        | 26 => val a
        | 27 => val a₁
        | 28 => val part0₂
        | 29 => val part1₂
        | 30 => val part2₁
        | 31 => val part3₁
        | 32 => val part4₁
        | 33 => val part5₁
        | 34 => val leftover₂
        | 35 => val a₂
        | 36 => val a₃
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 5)) with
        | 0 => (↑a : ℤ)
        | 1 => (↑a₁ : ℤ)
        | 2 => (↑a₂ : ℤ)
        | 3 => (↑a₃ : ℤ)
        | _ => (0 : ℤ)

  let loc₀ := (⟨37, exec_vals, 4, rc_vals⟩ : LocalAssignment (σ.ap + 9) (range_check + 5))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b0]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n0]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_r0_ap : val ↑r0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_r0]
  have h_r1_ap : val ↑r1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), htv_r1]
  have h_k0_ap : val ↑k0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_k0]
  have h_k1_ap : val ↑k1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), htv_k1]
  have h_r0b0_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 9)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r0b0_low_ap : val ↑r0b0_low = Assign mem loc₀ (exec (σ.ap + 9)) := by
    simp only [h_r0b0_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r0b0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 10)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r0b0_high_ap : val ↑r0b0_high = Assign mem loc₀ (exec (σ.ap + 10)) := by
    simp only [h_r0b0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r0b1_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 11)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r0b1_low_ap : val ↑r0b1_low = Assign mem loc₀ (exec (σ.ap + 11)) := by
    simp only [h_r0b1_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r0b1_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 12)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r0b1_high_ap : val ↑r0b1_high = Assign mem loc₀ (exec (σ.ap + 12)) := by
    simp only [h_r0b1_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r1b0_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 13)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r1b0_low_ap : val ↑r1b0_low = Assign mem loc₀ (exec (σ.ap + 13)) := by
    simp only [h_r1b0_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r1b0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 14)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r1b0_high_ap : val ↑r1b0_high = Assign mem loc₀ (exec (σ.ap + 14)) := by
    simp only [h_r1b0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r1b1_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 15)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r1b1_low_ap : val ↑r1b1_low = Assign mem loc₀ (exec (σ.ap + 15)) := by
    simp only [h_r1b1_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_r1b1_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 16)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_r1b1_high_ap : val ↑r1b1_high = Assign mem loc₀ (exec (σ.ap + 16)) := by
    simp only [h_r1b1_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n0k0_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 17)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n0k0_low_ap : val ↑n0k0_low = Assign mem loc₀ (exec (σ.ap + 17)) := by
    simp only [h_n0k0_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n0k0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 18)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n0k0_high_ap : val ↑n0k0_high = Assign mem loc₀ (exec (σ.ap + 18)) := by
    simp only [h_n0k0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n0k1_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 19)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n0k1_low_ap : val ↑n0k1_low = Assign mem loc₀ (exec (σ.ap + 19)) := by
    simp only [h_n0k1_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n0k1_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 20)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n0k1_high_ap : val ↑n0k1_high = Assign mem loc₀ (exec (σ.ap + 20)) := by
    simp only [h_n0k1_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n1k0_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 21)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n1k0_low_ap : val ↑n1k0_low = Assign mem loc₀ (exec (σ.ap + 21)) := by
    simp only [h_n1k0_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n1k0_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 22)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n1k0_high_ap : val ↑n1k0_high = Assign mem loc₀ (exec (σ.ap + 22)) := by
    simp only [h_n1k0_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n1k1_low_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 23)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n1k1_low_ap : val ↑n1k1_low = Assign mem loc₀ (exec (σ.ap + 23)) := by
    simp only [h_n1k1_low_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_n1k1_high_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 24)
    (by use (Int.add_le_add_left (by norm_num1) _) ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_n1k1_high_ap : val ↑n1k1_high = Assign mem loc₀ (exec (σ.ap + 24)) := by
    simp only [h_n1k1_high_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_Done := complete_u256_guarantee_inv_mod_n_Done_from_spec
    (Assign mem loc₀) σ range_check b0 b1 n0 n1 r0 r1 k0 k1 r0b0_low r0b0_high r0b1_low r0b1_high r1b0_low r1b0_high r1b1_low r1b1_high n0k0_low n0k0_high n0k1_low n0k1_high n1k0_low n1k0_high n1k1_low n1k1_high hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_r0_ap h_r1_ap h_k0_ap h_k1_ap h_r0b0_low_ap h_r0b0_high_ap h_r0b1_low_ap h_r0b1_high_ap h_r1b0_low_ap h_r1b0_high_ap h_r1b1_low_ap h_r1b1_high_ap h_n0k0_low_ap h_n0k0_high_ap h_n0k1_low_ap h_n0k1_high_ap h_n1k0_low_ap h_n1k0_high_ap h_n1k1_low_ap h_n1k1_high_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_Done⟩

  have h_ap_concat : (σ.ap + 46) = (σ.ap + 9) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 9) = (range_check + 5) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_Done with ⟨loc₁, h_rc_Done, h_Done⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_9 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 9)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_10 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 10)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_11 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 11)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_12 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 12)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_13 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 13)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_14 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 14)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_15 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 15)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_16 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 16)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_17 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 17)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_18 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 18)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_19 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 19)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_20 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 20)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_21 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 21)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_22 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 22)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_23 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 23)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_24 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 24)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_25 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 25)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_26 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 26)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_27 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 27)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_28 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 28)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_29 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 29)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_30 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 30)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_31 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 31)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_32 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 32)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_33 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 33)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_34 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 34)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_35 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 35)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_36 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 36)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_37 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 37)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_38 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 38)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_39 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 39)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_40 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 40)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_41 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 41)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_42 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 42)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_43 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 43)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_44 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 44)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_45 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 45)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_5 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 5)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_6 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 6)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_7 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 7)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_8 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 8)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_a₃
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_a₂
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_a₁
      apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_a
      apply VmRangeChecked_zero
    apply h_rc_Done
  vm_step_assert_eq hmem18 hmem, hmem19 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem19 hmem]
    simp only [h_ap_plus_25]
    simp only [h_ap_plus_17]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [one] at h_part0
    simp only [h_part0]
  vm_step_assert_eq hmem20 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_26]
    simp only [h_ap_plus_25]
    simp only [h_ap_plus_9]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part1
    dsimp [Mrel.Equiv]
    simp only [h_part1]
  vm_step_assert_eq hmem21 hmem, hmem22 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem22 hmem]
    simp only [h_ap_plus_27]
    simp only [h_ap_plus_26]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_limit] at h_leftover
    simp only [h_leftover]
  vm_step_assert_eq hmem23 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_27]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α23]
  vm_step_assert_eq hmem24 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_28]
    simp only [h_ap_plus_18]
    simp only [h_ap_plus_27]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part0₁]
  vm_step_assert_eq hmem25 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_29]
    simp only [h_ap_plus_28]
    simp only [h_ap_plus_19]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part1₁]
  vm_step_assert_eq hmem26 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_30]
    simp only [h_ap_plus_29]
    simp only [h_ap_plus_21]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part2]
  vm_step_assert_eq hmem27 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_31]
    simp only [h_ap_plus_30]
    simp only [h_ap_plus_10]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part3
    dsimp [Mrel.Equiv]
    simp only [h_part3]
  vm_step_assert_eq hmem28 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_32]
    simp only [h_ap_plus_31]
    simp only [h_ap_plus_11]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part4
    dsimp [Mrel.Equiv]
    simp only [h_part4]
  vm_step_assert_eq hmem29 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_33]
    simp only [h_ap_plus_32]
    simp only [h_ap_plus_13]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part5
    dsimp [Mrel.Equiv]
    simp only [h_part5]
  vm_step_assert_eq hmem30 hmem, hmem31 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem31 hmem]
    simp only [h_ap_plus_34]
    simp only [h_ap_plus_33]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_limit] at h_leftover₁
    simp only [h_leftover₁]
  vm_step_assert_eq hmem32 hmem, hmem33 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem33 hmem]
    simp only [h_ap_plus_35]
    simp only [h_ap_plus_34]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_a
    dsimp [Mrel.Equiv]
    simp only [i16_lower_bound] at h_a
    simp only [h_a]
  vm_step_assert_eq hmem34 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_35]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_5]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem35 hmem, hmem36 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem36 hmem]
    simp only [h_ap_plus_36]
    simp only [h_ap_plus_34]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_bound_minus_i16_upper_bound] at h_a₁
    simp only [h_a₁]
  vm_step_assert_eq hmem37 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_36]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_6]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem38 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_37]
    simp only [h_ap_plus_20]
    simp only [h_ap_plus_34]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part0₂]
  vm_step_assert_eq hmem39 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_38]
    simp only [h_ap_plus_37]
    simp only [h_ap_plus_22]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part1₂]
  vm_step_assert_eq hmem40 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_39]
    simp only [h_ap_plus_38]
    simp only [h_ap_plus_23]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_part2₁]
  vm_step_assert_eq hmem41 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_40]
    simp only [h_ap_plus_39]
    simp only [h_ap_plus_14]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part3₁
    dsimp [Mrel.Equiv]
    simp only [h_part3₁]
  vm_step_assert_eq hmem42 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_41]
    simp only [h_ap_plus_40]
    simp only [h_ap_plus_12]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part4₁
    dsimp [Mrel.Equiv]
    simp only [h_part4₁]
  vm_step_assert_eq hmem43 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_42]
    simp only [h_ap_plus_41]
    simp only [h_ap_plus_15]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_part5₁
    dsimp [Mrel.Equiv]
    simp only [h_part5₁]
  vm_step_assert_eq hmem44 hmem, hmem45 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem45 hmem]
    simp only [h_ap_plus_43]
    simp only [h_ap_plus_42]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_limit] at h_leftover₂
    simp only [h_leftover₂]
  vm_step_assert_eq hmem46 hmem, hmem47 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem47 hmem]
    simp only [h_ap_plus_44]
    simp only [h_ap_plus_43]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    rw [Int.eq_sub_emod_iff_add_emod_eq] at h_a₂
    dsimp [Mrel.Equiv]
    simp only [i16_lower_bound] at h_a₂
    simp only [h_a₂]
  vm_step_assert_eq hmem48 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_44]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_7]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem49 hmem, hmem50 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    rw [assign_prog] ; rw [hmem50 hmem]
    simp only [h_ap_plus_45]
    simp only [h_ap_plus_43]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [u128_bound_minus_i16_upper_bound] at h_a₃
    simp only [h_a₃]
  vm_step_assert_eq hmem51 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_45]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_8]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  vm_step_assert_eq hmem52 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_16]
    simp only [h_ap_plus_24]
    simp only [h_ap_plus_43]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    dsimp [Mrel.Equiv]
    simp only [h_α52]
  vm_step_jump_imm hmem53 hmem, hmem54 hmem
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_Done
  done

theorem complete_u256_guarantee_inv_mod_n_HighDiff_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (htv_r0 : val r0 = mem (exec (σ.ap + 2)))
    (htv_r1 : val r1 = mem (exec (σ.ap + 3)))
    (htv_k0 : val k0 = mem (exec (σ.ap + 4)))
    (htv_k1 : val k1 = mem (exec (σ.ap + 5)))
    (htv_diff1 : val diff1 = mem (exec (σ.ap + 6)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n_HighDiff range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment (σ.ap + 9) (range_check + 4),
    VmRangeChecked loc.rc_vals (range_check + 4) loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) { pc := σ.pc + 17, ap := (σ.ap + 24), fp := σ.fp } (fun κ τ =>
      τ.ap = (σ.ap + 9) + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc ((range_check + 4) + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_rc_diff1, h_block_After⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - (σ.ap + 9)) with
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - (range_check + 4)) with
        | 0 => (↑diff1 : ℤ)
        | _ => (0 : ℤ)

  let loc₀ := (⟨0, exec_vals, 1, rc_vals⟩ : LocalAssignment (σ.ap + 9) (range_check + 4))

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 7)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_range_check]
  have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 6)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b0]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 5)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_b1]
  have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 4)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n0]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    have := assign_exec_of_lt mem loc₀ (σ.ap - 3)
      (by apply lt_trans _ (Int.lt_add_of_pos_right σ.ap (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
    simp only [this, htv_n1]
  have h_r0_ap : val ↑r0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 2) (by apply Int.add_lt_add_left ; norm_num1), htv_r0]
  have h_r1_ap : val ↑r1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 3) (by apply Int.add_lt_add_left ; norm_num1), htv_r1]
  have h_k0_ap : val ↑k0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 4) (by apply Int.add_lt_add_left ; norm_num1), htv_k0]
  have h_k1_ap : val ↑k1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap + 5) (by apply Int.add_lt_add_left ; norm_num1), htv_k1]
  have h_After := complete_u256_guarantee_inv_mod_n_After_from_spec
    (Assign mem loc₀) σ range_check b0 b1 n0 n1 r0 r1 k0 k1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_r0_ap h_r1_ap h_k0_ap h_k1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_After⟩

  have h_ap_concat : (σ.ap + 9) = (σ.ap + 9) + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 5) = (range_check + 4) + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_After with ⟨loc₁, h_rc_After, h_After⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply lt_trans _ (Int.lt_add_of_pos_right _ (by norm_num1)) ; apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_2 := assign_exec_of_lt mem loc (σ.ap + 2)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_of_lt mem loc (σ.ap + 3)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_of_lt mem loc (σ.ap + 4)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_of_lt mem loc (σ.ap + 5)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_6 := assign_exec_of_lt mem loc (σ.ap + 6)
    (by apply Int.add_lt_add_left ; norm_num1)
  have h_rc_plus_4 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 4)
    (by constructor ; apply Int.add_le_add_left ; norm_num1 ; rw [add_assoc] ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_rec
      · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
        apply h_rc_diff1
      apply VmRangeChecked_zero
    apply h_rc_After
  vm_step_assert_eq hmem17 hmem
  constructor
  · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
    try norm_num1
    try simp only [hin_fp]
    simp only [h_ap_plus_6]
    simp only [←htv_diff1]
    simp only [h_ap_minus_7]
    simp only [←htv_range_check]
    simp only [h_rc_plus_4]
    try dsimp [exec_vals, rc_vals]
    try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
    apply Mrel.Equiv.refl_val
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_After
  done

theorem complete_u256_guarantee_inv_mod_n_from_spec
    -- arguments
    (range_check b0 b1 n0 n1 : ℤ)
    -- code is in memory at σ.pc + start offset
    (hmem : ProgAt mem vm_u256_guarantee_inv_mod_n_code σ.pc)
    -- input arguments on the stack
    (hin_fp : σ.fp = σ.ap)
    (htv_range_check : rc range_check = mem (exec (σ.ap - 7)))
    (htv_b0 : val b0 = mem (exec (σ.ap - 6)))
    (htv_b1 : val b1 = mem (exec (σ.ap - 5)))
    (htv_n0 : val n0 = mem (exec (σ.ap - 4)))
    (htv_n1 : val n1 = mem (exec (σ.ap - 3)))
    (h_spec: ∃ (ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low : ℤ),
               auto_spec_u256_guarantee_inv_mod_n range_check b0 b1 n0 n1 ρ_branch_id ρ_r0 ρ_r1 ρ_r0₁ ρ_b0 ρ_r0b0_high ρ_r0b0_low ρ_r0₂ ρ_b1 ρ_r0b1_high ρ_r0b1_low ρ_r1₁ ρ_b0₁ ρ_r1b0_high ρ_r1b0_low ρ_r1₂ ρ_b1₁ ρ_r1b1_high ρ_r1b1_low ρ_n0 ρ_k0 ρ_n0k0_high ρ_n0k0_low ρ_n0₁ ρ_k1 ρ_n0k1_high ρ_n0k1_low ρ_n1_or_g0 ρ_k0_or_s0 ρ_n1k0_high_or_g0s0_high ρ_n1k0_low_or_g0s0_low ρ_n1_or_g0₁ ρ_k1_or_t0 ρ_n1k1_high_or_g0t0_high ρ_n1k1_low_or_g0t0_low)
  -- conclusion
  : ∃ loc : LocalAssignment σ.ap range_check,
    VmRangeChecked loc.rc_vals range_check loc.rc_num u128Limit ∧
    Returns PRIME (Assign mem loc) σ (fun κ τ =>
      τ.ap = σ.ap + loc.exec_num ∧
      Assign mem loc (exec (τ.ap - 36)) = rc (range_check + loc.rc_num)) := by
  rcases h_spec with ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, orig_range_check, h_orig_range_check, g0_or_no_inv, g1_option, s_or_r0, s_or_r1, t_or_k0, t_or_k1, h_spec|h_spec⟩
  · rcases h_spec with ⟨hc_g0_or_no_inv, r0, h_r0, r1, h_r1, k0, h_k0, k1, h_k1, h_rc_r0, h_rc_r1, h_rc_k0, h_rc_k1, diff1, h_diff1, diff0, diff0_min_1, h_spec|h_spec⟩
    · rcases h_spec with ⟨hc_diff1, h_α11, h_α12, h_rc_diff0_min_1, h_block_After⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - σ.ap) with
            | 0 => val g0_or_no_inv
            | 1 => val g1_option
            | 2 => val s_or_r0
            | 3 => val s_or_r1
            | 4 => val t_or_k0
            | 5 => val t_or_k1
            | 6 => val diff1
            | 7 => val diff0
            | 8 => val diff0_min_1
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - range_check) with
            | 0 => (↑r0 : ℤ)
            | 1 => (↑r1 : ℤ)
            | 2 => (↑k0 : ℤ)
            | 3 => (↑k1 : ℤ)
            | 4 => (↑diff0_min_1 : ℤ)
            | _ => (0 : ℤ)

      let loc₀ := (⟨9, exec_vals, 5, rc_vals⟩ : LocalAssignment σ.ap range_check)

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 7) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
      have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 6) (by apply Int.sub_lt_self ; norm_num1), htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_b1]
      have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 4) (by apply Int.sub_lt_self ; norm_num1), htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 3) (by apply Int.sub_lt_self ; norm_num1), htv_n1]
      have h_r0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_r0_ap : val ↑r0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [h_r0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_r0] ; rfl
      have h_r1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_r1_ap : val ↑r1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
        simp only [h_r1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_r1] ; rfl
      have h_k0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 4)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_k0_ap : val ↑k0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [h_k0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_k0] ; rfl
      have h_k1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 5)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_k1_ap : val ↑k1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
        simp only [h_k1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_k1] ; rfl
      have h_After := complete_u256_guarantee_inv_mod_n_After_from_spec
        (Assign mem loc₀) σ range_check b0 b1 n0 n1 r0 r1 k0 k1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_r0_ap h_r1_ap h_k0_ap h_k1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_After⟩

      have h_ap_concat : (σ.ap + 9) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 5) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_After with ⟨loc₁, h_rc_After, h_After⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat σ.ap
        (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 1)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 4)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 5)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_7 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 7)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_8 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 8)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_3 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_4 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 4)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_diff0_min_1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_k1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_k0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_r1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_r0
          apply VmRangeChecked_zero
        apply h_rc_After
      vm_step_jnz hmem0 hmem, hmem1 hmem
      -- g0_or_no_inv = 0
      swap
      · norm_num1
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        dsimp [exec_vals]
        simp only [Int.sub_self]
        ring_nf ; simp only [val.injEq, Int.reduceNeg]
        simp only [hc_g0_or_no_inv]
        simp only [not_true, false_implies]
      intro _
      vm_step_assert_eq hmem2 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_2]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_r0]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem3 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_3]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_r1]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem4 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_4]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_2]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_k0]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem5 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_5]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_k1]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem6 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_6]
        simp only [h_ap_minus_3]
        simp only [←htv_n1]
        simp only [h_ap_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_diff1
        dsimp [Mrel.Equiv]
        try simp only [h_r1] at h_diff1
        simp only [h_diff1]
      vm_step_advance_ap hmem7 hmem, hmem8 hmem
      vm_step_jnz hmem9 hmem, hmem10 hmem
      -- diff1 = 0
      swap
      · norm_num1
        simp only [h_ap_plus_6]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 6, Int.add_sub_cancel]
        ring_nf ; simp only [val.injEq, Int.reduceNeg]
        simp only [hc_diff1]
        simp only [not_true, false_implies]
      intro _
      vm_step_assert_eq hmem11 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_7]
        simp only [h_ap_minus_4]
        simp only [←htv_n0]
        simp only [h_ap_plus_2]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α11
        dsimp [Mrel.Equiv]
        try simp only [h_r0] at h_α11
        simp only [h_α11]
      vm_step_assert_eq hmem12 hmem, hmem13 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        rw [assign_prog] ; rw [hmem13 hmem]
        simp only [h_ap_plus_8]
        simp only [h_ap_plus_7]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_α12
        dsimp [Mrel.Equiv]
        simp only [one] at h_α12
        simp only [h_α12]
      vm_step_assert_eq hmem14 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_8]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_4]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        apply Mrel.Equiv.refl_val
      vm_step_jump_imm hmem15 hmem, hmem16 hmem
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_After
    · rcases h_spec with ⟨hc_diff1, h_block_HighDiff⟩
      let exec_vals :=
          fun (i : ℤ) =>
            match (i - σ.ap) with
            | 0 => val g0_or_no_inv
            | 1 => val g1_option
            | 2 => val s_or_r0
            | 3 => val s_or_r1
            | 4 => val t_or_k0
            | 5 => val t_or_k1
            | 6 => val diff1
            | 7 => val diff0
            | 8 => val diff0_min_1
            | _ => val 0

      let rc_vals :=
          fun (i : ℤ) =>
            match (i - range_check) with
            | 0 => (↑r0 : ℤ)
            | 1 => (↑r1 : ℤ)
            | 2 => (↑k0 : ℤ)
            | 3 => (↑k1 : ℤ)
            | _ => (0 : ℤ)

      let loc₀ := (⟨9, exec_vals, 4, rc_vals⟩ : LocalAssignment σ.ap range_check)

      have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 7) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
      have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 6) (by apply Int.sub_lt_self ; norm_num1), htv_b0]
      have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_b1]
      have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 4) (by apply Int.sub_lt_self ; norm_num1), htv_n0]
      have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
        simp only [assign_exec_of_lt mem loc₀ (σ.ap - 3) (by apply Int.sub_lt_self ; norm_num1), htv_n1]
      have h_r0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_r0_ap : val ↑r0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
        simp only [h_r0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_r0] ; rfl
      have h_r1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_r1_ap : val ↑r1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
        simp only [h_r1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_r1] ; rfl
      have h_k0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 4)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_k0_ap : val ↑k0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
        simp only [h_k0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_k0] ; rfl
      have h_k1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 5)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_k1_ap : val ↑k1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
        simp only [h_k1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rw [h_k1] ; rfl
      have h_diff1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 6)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_diff1_ap : val ↑diff1 = Assign mem loc₀ (exec (σ.ap + 6)) := by
        simp only [h_diff1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
      have h_HighDiff := complete_u256_guarantee_inv_mod_n_HighDiff_from_spec
        (Assign mem loc₀) σ range_check b0 b1 n0 n1 r0 r1 k0 k1 diff1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_r0_ap h_r1_ap h_k0_ap h_k1_ap h_diff1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_HighDiff⟩

      have h_ap_concat : (σ.ap + 9) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
      have h_rc_concat : (range_check + 4) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
      rcases h_HighDiff with ⟨loc₁, h_rc_HighDiff, h_HighDiff⟩

      let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

      have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
        (by apply Int.sub_lt_self ; norm_num1)
      have h_ap_plus_0 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat σ.ap
        (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
      have h_ap_plus_1 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 1)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_2 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_3 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_4 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 4)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_5 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 5)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_6 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 6)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_7 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 7)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_ap_plus_8 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 8)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_0 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 0)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_1 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 1)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_2 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 2)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
      have h_rc_plus_3 := assign_rc_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (range_check + 3)
        (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

      use loc
      constructor
      · apply VmRangeChecked_concat
        · apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_k1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_k0
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_r1
          apply VmRangeChecked_rec
          · try norm_num1 ; dsimp [rc_vals] ; try ring_nf
            apply h_rc_r0
          apply VmRangeChecked_zero
        apply h_rc_HighDiff
      vm_step_jnz hmem0 hmem, hmem1 hmem
      -- g0_or_no_inv = 0
      swap
      · norm_num1
        try simp only [add_zero]
        simp only [h_ap_plus_0]
        dsimp [exec_vals]
        simp only [Int.sub_self]
        ring_nf ; simp only [val.injEq, Int.reduceNeg]
        simp only [hc_g0_or_no_inv]
        simp only [not_true, false_implies]
      intro _
      vm_step_assert_eq hmem2 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_2]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_0]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_r0]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem3 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_3]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_1]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_r1]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem4 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_4]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_2]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_k0]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem5 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_5]
        simp only [h_ap_minus_7]
        simp only [←htv_range_check]
        simp only [h_rc_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        try simp only [h_k1]
        apply Mrel.Equiv.refl_val
      vm_step_assert_eq hmem6 hmem
      constructor
      · try simp only [neg_clip_checked', ←Int.sub_eq_add_neg]
        try norm_num1
        try simp only [hin_fp]
        simp only [h_ap_plus_6]
        simp only [h_ap_minus_3]
        simp only [←htv_n1]
        simp only [h_ap_plus_3]
        try dsimp [exec_vals, rc_vals]
        try simp only [add_sub_add_comm, add_sub_right_comm, sub_add_cancel_left, sub_self] ; try norm_num1
        rw [Int.eq_sub_emod_iff_add_emod_eq] at h_diff1
        dsimp [Mrel.Equiv]
        try simp only [h_r1] at h_diff1
        simp only [h_diff1]
      vm_step_advance_ap hmem7 hmem, hmem8 hmem
      vm_step_jnz hmem9 hmem, hmem10 hmem
      -- diff1 ≠ 0
      · norm_num1
        simp only [h_ap_plus_6]
        dsimp [exec_vals]
        simp only [Int.add_comm σ.ap 6, Int.add_sub_cancel]
        intro h_cond
        try ring_nf at h_cond
        exfalso
        apply hc_diff1
        injection h_cond
      intro _
      simp only [assign_prog, hmem10 hmem, Mrel.toInt]
      vm_arith_simps
      rw [assign_concat, concat_exec_num, concat_rc_num]
      simp only [Nat.cast_add]
      try simp only [Nat.cast_zero, Int.zero_add]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
      try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
      norm_num1
      try simp only [←Int.add_assoc]
      apply h_HighDiff
  rcases h_spec with ⟨hc_g0_or_no_inv, h_block_NoInverse⟩
  let exec_vals :=
      fun (i : ℤ) =>
        match (i - σ.ap) with
        | 0 => val g0_or_no_inv
        | 1 => val g1_option
        | 2 => val s_or_r0
        | 3 => val s_or_r1
        | 4 => val t_or_k0
        | 5 => val t_or_k1
        | _ => val 0

  let rc_vals :=
      fun (i : ℤ) =>
        match (i - range_check) with
        | _ => (0 : ℤ)

  let loc₀ := (⟨6, exec_vals, 0, rc_vals⟩ : LocalAssignment σ.ap range_check)

  have h_range_check_ap : rc ↑range_check = Assign mem loc₀ (exec (σ.ap - 7)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 7) (by apply Int.sub_lt_self ; norm_num1), htv_range_check]
  have h_b0_ap : val ↑b0 = Assign mem loc₀ (exec (σ.ap - 6)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 6) (by apply Int.sub_lt_self ; norm_num1), htv_b0]
  have h_b1_ap : val ↑b1 = Assign mem loc₀ (exec (σ.ap - 5)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 5) (by apply Int.sub_lt_self ; norm_num1), htv_b1]
  have h_n0_ap : val ↑n0 = Assign mem loc₀ (exec (σ.ap - 4)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 4) (by apply Int.sub_lt_self ; norm_num1), htv_n0]
  have h_n1_ap : val ↑n1 = Assign mem loc₀ (exec (σ.ap - 3)) := by
    simp only [assign_exec_of_lt mem loc₀ (σ.ap - 3) (by apply Int.sub_lt_self ; norm_num1), htv_n1]
  have h_g0_or_no_inv_exec_pos := assign_exec_pos mem loc₀ σ.ap
    (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
  have h_g0_or_no_inv_ap : val ↑g0_or_no_inv = Assign mem loc₀ (exec σ.ap) := by
    simp only [h_g0_or_no_inv_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_g1_option_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_g1_option_ap : val ↑g1_option = Assign mem loc₀ (exec (σ.ap + 1)) := by
    simp only [h_g1_option_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_s_or_r0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_s_or_r0_ap : val ↑s_or_r0 = Assign mem loc₀ (exec (σ.ap + 2)) := by
    simp only [h_s_or_r0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_s_or_r1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_s_or_r1_ap : val ↑s_or_r1 = Assign mem loc₀ (exec (σ.ap + 3)) := by
    simp only [h_s_or_r1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_t_or_k0_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 4)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_t_or_k0_ap : val ↑t_or_k0 = Assign mem loc₀ (exec (σ.ap + 4)) := by
    simp only [h_t_or_k0_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_t_or_k1_exec_pos := assign_exec_pos mem loc₀ (σ.ap + 5)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_t_or_k1_ap : val ↑t_or_k1 = Assign mem loc₀ (exec (σ.ap + 5)) := by
    simp only [h_t_or_k1_exec_pos] ; dsimp [exec_vals] ; ring_nf ; rfl
  have h_NoInverse := complete_u256_guarantee_inv_mod_n_NoInverse_from_spec
    (Assign mem loc₀) σ range_check b0 b1 n0 n1 g0_or_no_inv g1_option s_or_r0 s_or_r1 t_or_k0 t_or_k1 hmem hin_fp h_range_check_ap h_b0_ap h_b1_ap h_n0_ap h_n1_ap h_g0_or_no_inv_ap h_g1_option_ap h_s_or_r0_ap h_s_or_r1_ap h_t_or_k0_ap h_t_or_k1_ap ⟨ρ_branch_id, ρ_r0, ρ_r1, ρ_r0₁, ρ_b0, ρ_r0b0_high, ρ_r0b0_low, ρ_r0₂, ρ_b1, ρ_r0b1_high, ρ_r0b1_low, ρ_r1₁, ρ_b0₁, ρ_r1b0_high, ρ_r1b0_low, ρ_r1₂, ρ_b1₁, ρ_r1b1_high, ρ_r1b1_low, ρ_n0, ρ_k0, ρ_n0k0_high, ρ_n0k0_low, ρ_n0₁, ρ_k1, ρ_n0k1_high, ρ_n0k1_low, ρ_n1_or_g0, ρ_k0_or_s0, ρ_n1k0_high_or_g0s0_high, ρ_n1k0_low_or_g0s0_low, ρ_n1_or_g0₁, ρ_k1_or_t0, ρ_n1k1_high_or_g0t0_high, ρ_n1k1_low_or_g0t0_low, h_block_NoInverse⟩

  have h_ap_concat : (σ.ap + 6) = σ.ap + ↑loc₀.exec_num := by dsimp ; try rw [add_assoc] ; norm_num1 ; rfl
  have h_rc_concat : (range_check + 0) = range_check + ↑loc₀.rc_num := by simp only [add_assoc] ; simp
  rcases h_NoInverse with ⟨loc₁, h_rc_NoInverse, h_NoInverse⟩

  let loc := ConcatAssignments loc₀ loc₁ h_ap_concat h_rc_concat

  have h_ap_minus_7 := assign_exec_of_lt mem loc (σ.ap - 7)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_6 := assign_exec_of_lt mem loc (σ.ap - 6)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_5 := assign_exec_of_lt mem loc (σ.ap - 5)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_4 := assign_exec_of_lt mem loc (σ.ap - 4)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_minus_3 := assign_exec_of_lt mem loc (σ.ap - 3)
    (by apply Int.sub_lt_self ; norm_num1)
  have h_ap_plus_0 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat σ.ap
    (by use le_refl _ ; apply Int.lt_add_of_pos_right ; norm_num1)
  have h_ap_plus_1 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 1)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_2 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 2)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_3 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 3)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_4 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 4)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)
  have h_ap_plus_5 := assign_exec_concat_loc₀ mem loc₀ loc₁ h_ap_concat h_rc_concat (σ.ap + 5)
    (by use (Int.le_add_of_nonneg_right (by norm_num1)) ; apply Int.add_lt_add_left ; norm_num1)

  use loc
  constructor
  · apply VmRangeChecked_concat
    · apply VmRangeChecked_zero
    apply h_rc_NoInverse
  vm_step_jnz hmem0 hmem, hmem1 hmem
  -- g0_or_no_inv ≠ 0
  · norm_num1
    try simp only [add_zero]
    simp only [h_ap_plus_0]
    dsimp [exec_vals]
    simp only [Int.sub_self]
    intro h_cond
    try ring_nf at h_cond
    exfalso
    apply hc_g0_or_no_inv
    injection h_cond
  intro _
  simp only [assign_prog, hmem1 hmem, Mrel.toInt]
  vm_arith_simps
  rw [assign_concat, concat_exec_num, concat_rc_num]
  simp only [Nat.cast_add]
  try simp only [Nat.cast_zero, Int.zero_add]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.exec_num)]
  try simp only [←(Int.add_assoc _ _  ↑loc₁.rc_num)]
  norm_num1
  try simp only [←Int.add_assoc]
  apply h_NoInverse
  done
