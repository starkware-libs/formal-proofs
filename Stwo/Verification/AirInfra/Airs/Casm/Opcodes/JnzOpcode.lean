
import Mathlib.Data.List.Indexes
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst
import Verification.AirInfra.Airs.Casm.Opcodes.Util
import Verification.AirInfra.Airs.ConvolutionUtils.Karatsuba

namespace Felt252Words

def limb_sum (y : Felt252Words) : Felt := ∑ i : Fin FELT252_N_WORDS, y i
def limb_sum_squares (y : Felt252Words) : Felt := ∑ i : Fin FELT252_N_WORDS, if Felt252_Felts_list[i]! = 0 then y i else ((y i - Felt252_Felts_list[i]!) ^ 2)
end Felt252Words

namespace Felt252Nats

theorem zero_if_sum_limbs_zero
    {yn : Felt252Nats}
    {y : Felt252Words}
    (h_rc : IsRangeChecked yn y)
    (h_sum : y.limb_sum = 0) :
    yn.eval = 0 := by
  have : Stwo.P ∣ ∑ i : Fin FELT252_N_WORDS, yn i := by
    rw [←CharP.cast_eq_zero_iff (R := Felt), ←h_sum, Felt252Words.limb_sum, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (h_rc i).1.symm)
  have : ∑ i : Fin FELT252_N_WORDS, yn i = 0 := by
    apply Nat.eq_zero_of_dvd_of_lt this
    apply lt_of_le_of_lt (b := ∑ i : Fin FELT252_N_WORDS, 2^9)
    . apply Finset.sum_le_sum (fun i _ => le_of_lt (h_rc i).2)
    simp [Stwo.P, FELT252_N_WORDS]
  have : ∀ i, yn i = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg] at this <;> simp_all
  simp [Felt252Nats.eval, this]

theorem aux {yn : Felt252Nats} :
    (List.mapIdx (fun i a => a * (2 ^ 9) ^ i) (List.ofFn yn)).sum =
      ∑ x : Fin FELT252_N_WORDS, yn x * 2 ^ (FELT252_BITS_PER_WORD * ↑x) := by
  rw [Finset.sum_fin_eq_sum_range, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi, dif_pos (by exact hi), ←pow_mul, List.get_ofFn]; rfl

-- TODO(Jeremy): move this
instance : CharP Felt252 Felt252Prime := by
  dsimp [Felt252]; rw [← @ringChar.eq_iff, ZMod.ringChar_zmod_n]

theorem not_zero_if_sums_inversible [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]-- only one direction is needed?
    {yn : Felt252Nats}
    {y : Felt252Words}
    (h_rc : IsRangeChecked yn y) :
    ((∃ inv1 : Felt, inv1 * y.limb_sum = 1) ∧ (∃ inv2 : Felt, inv2 * y.limb_sum_squares = 1)) → (yn.eval ≠ 0) := by

  rintro ⟨⟨inv1, h_inv1⟩, ⟨inv2, h_inv2⟩⟩
  have sum_neq_zero : y.limb_sum ≠ 0 := by intro htmp; simp_all
  have sum_squares_neq_zero : y.limb_sum_squares ≠ 0 := by intro htmp; simp_all

  by_contra eval_zero

  have h_sum_zero_zmod : ↑(∑ i, yn i * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = (0 : Felt252) := by
    rw [← eval_zero, Felt252Nats.eval_eq_eval', Felt252Nats.eval', Felt252Nats.eval_nat]

  have : Felt252Prime ∣ ∑ i, yn i * 2 ^ (FELT252_BITS_PER_WORD * ↑i) := by
    rwa [←CharP.cast_eq_zero_iff (R := Felt252)]
  rw [dvd_def] at this
  rcases this with ⟨k, h_mul_p_k⟩

  have h_eval_lt : ∑ i, (yn i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i) < 2 * Felt252Prime := by
    calc
      ∑ i : Fin FELT252_N_WORDS, (yn i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i) ≤
        ∑ i : Fin FELT252_N_WORDS, ((2^9 - 1) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.mul_le_mul_right
        exact Nat.le_of_lt_add_one (h_rc i).2
      _ < 2 * Felt252Prime := by
        decide

  have k_le_one : k < 2 := by
    rw [h_mul_p_k, mul_comm] at h_eval_lt
    exact Nat.lt_of_mul_lt_mul_right h_eval_lt

  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  . have : ∀ i, yn i = 0 := by
      simpa using h_mul_p_k
    simp [Felt252Words.limb_sum, fun i => (h_rc i).1, this] at sum_neq_zero

  let f252_digits := Nat.digits (2^9) Felt252Prime

  let len := f252_digits.length
  have h_f252_digits : f252_digits = Nat.digits 512 Felt252Prime := by rfl

  have h_list_len : (Felt252_Felts_list.length) = 28 := by
    dsimp[Felt252_Felts_list]

  have h_28_digits_pre := Nat.digits_len 512 Felt252Prime (show 1<512 by norm_num) (show Felt252Prime≠0 by norm_num[Felt252Prime])

  have h_28_digits: f252_digits.length = 28 := by
    dsimp[f252_digits]
    dsimp[Felt252Prime]
    dsimp[Felt252Prime] at h_28_digits_pre
    rw[h_28_digits_pre]
    simp
    norm_num[Nat.log]

  have h_f252_digits_consts: (Nat.digits (2^9) Felt252Prime) = Felt252_Felts_list.map (fun x => x.val) := by
    dsimp[Felt252_Felts_list]
    dsimp[Felt252Prime]
    norm_num
    decide

  have h_len_simp : (List.mapIdx (fun i a => a * (2 ^ 9) ^ i) (List.ofFn yn)).length = FELT252_N_WORDS := by
    simp

  have h_len_le : (List.mapIdx (fun i a => a * (2 ^ 9) ^ i) (List.ofFn yn)).length ≤ FELT252_N_WORDS := by
    simp

  have h_len_set_simp : Fin (List.mapIdx (fun i a => a * (2 ^ 9) ^ i) (List.ofFn yn)).length = Fin FELT252_N_WORDS := by
    rw[h_len_simp]

  let dumbcast := Fin.castLE h_len_le

  have h_of_digits : Nat.ofDigits (2^9) (List.ofFn yn) = Felt252Prime := by
    rw [Nat.ofDigits_eq_sum_mapIdx (2^9) (List.ofFn yn)]
    rw [aux]

    exact h_mul_p_k

  have h_last_digit : (∀ (h : List.ofFn yn ≠ []), (List.ofFn yn).getLast h ≠ 0) := by
    intro h_tmp
    simp
    by_contra h_last_digit_zero
    dsimp[FELT252_N_WORDS] at h_mul_p_k

    let boundingFn : Fin 28 → Nat := fun x => if x = 27 then 0 else ((2^9 - 1) * (2 ^ (9 * (x : Nat))))
    have h_boundingFn : (∀ i : Fin 28, (yn i * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) ≤ (boundingFn i)) := by
      intro i
      dsimp[boundingFn]
      by_cases is27 : i = 27
      · rw[is27]
        simp
        exact h_last_digit_zero
      · rw[if_neg is27]
        dsimp[FELT252_BITS_PER_WORD]
        apply Nat.mul_le_mul_right
        exact Nat.le_of_lt_add_one (h_rc i).2
    have h_boundingFn_sum : (∑ i : Fin 28, (yn i * 2 ^ (FELT252_BITS_PER_WORD * ↑i))) ≤ (∑ i : Fin 28, boundingFn i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply h_boundingFn
    rw[h_mul_p_k] at h_boundingFn_sum
    have h_boundingFn_sum2 : ∑ i : Fin 28, boundingFn i < Felt252Prime := by
      decide
    linarith [h_boundingFn_sum, h_boundingFn_sum2]

  have digit_lc : (∀ l ∈ List.ofFn yn, l < 2 ^ 9) := by
    intro l hl
    rcases List.mem_ofFn.mp hl with ⟨li, hli⟩
    rw[← hli]
    exact (h_rc li).2

  have h_list_identity := Nat.digits_ofDigits (2^9) (by norm_num) (List.ofFn yn) digit_lc h_last_digit
  rw[h_of_digits] at h_list_identity

  rw[h_f252_digits_consts] at h_list_identity

  have htmp2 : ∀ i : Fin FELT252_N_WORDS, ((List.map (fun x => x.val) Felt252_Felts_list)[i]!) = (Felt252_Felts_list[i]!).val := by
    decide

  have h_each_index_felt : ∀ i : Fin FELT252_N_WORDS, y i = Felt252_Felts_list[i]! := by
    intro i
    have htmp: yn i = (List.ofFn yn)[↑i]! := by
      trans (List.ofFn yn).get ↑i
      . rw [List.get_ofFn]; rfl
      simp
    rw [(h_rc i).1, htmp, ←h_list_identity, htmp2 i]
    simp [Felt]

  dsimp [Felt252Words.limb_sum_squares] at sum_squares_neq_zero
  apply sum_squares_neq_zero
  apply Finset.sum_eq_zero
  intro i hi
  split <;> next h => simp [h_each_index_felt i, h]

end Felt252Nats

namespace Felt252Expr

def limb_sum (y : Felt252Expr) : FeltExpr := (List.finRange FELT252_N_WORDS).map y |>.foldl (· + ·) (FeltExpr.const 0)

open Fin.NatCast

theorem eval_of_limb_sum [Fact (Nat.Prime Stwo.P)] {y : Felt252Expr} {varAssign : VarAssign} :
  y.limb_sum.eval varAssign = (y.eval varAssign).limb_sum := by

  unfold Felt252Words.limb_sum
  unfold limb_sum
  exact FeltExpr.eval_foldl_add_map_fin FELT252_N_WORDS y varAssign

def limb_sum_squares (y : Felt252Expr) : FeltExpr := (List.finRange FELT252_N_WORDS |>.map fun i => if Felt252_Felts_list[i]! = 0 then (y i) else ((y i - FeltExpr.const (Felt252_Felts_list[i]!)) * (y i - FeltExpr.const (Felt252_Felts_list[i]!)))).foldl (· + ·) (FeltExpr.const 0)

theorem eval_of_limb_sum_squares [Fact (Nat.Prime Stwo.P)] {y : Felt252Expr} {varAssign : VarAssign} :
  y.limb_sum_squares.eval varAssign = (y.eval varAssign).limb_sum_squares := by

  unfold Felt252Words.limb_sum_squares
  unfold limb_sum_squares

  rw[FeltExpr.eval_foldl_add_map_fin FELT252_N_WORDS (fun i => if Felt252_Felts_list[i]! = 0 then (y i) else ((y i - FeltExpr.const (Felt252_Felts_list[i]!)) * (y i - FeltExpr.const (Felt252_Felts_list[i]!)))) varAssign]

  have h2 : ∀ i : Fin FELT252_N_WORDS,
    FeltExpr.eval varAssign
      (if Felt252_Felts_list[i]! = 0 then y i
      else (y i - FeltExpr.const (Felt252_Felts_list[i]!)) * (y i - FeltExpr.const (Felt252_Felts_list[i]!))) =
    if Felt252_Felts_list[i]! = 0 then eval varAssign y i else (eval varAssign y i - Felt252_Felts_list[i]!) ^ 2 := by

    intro i
    by_cases is_0_at_ind : (Felt252_Felts_list[i]! = 0)
    · rw [is_0_at_ind]
      simp
      dsimp[Felt252Expr.eval]
    · rw[if_neg is_0_at_ind]
      rw[if_neg is_0_at_ind]
      simp only [FeltExpr.eval_mul]
      simp only [FeltExpr.eval_sub]
      simp only [FeltExpr.eval_const]
      dsimp[Felt252Expr.eval]
      ring_nf

  rw[Finset.sum_congr rfl (fun i _ => h2 i)]

end Felt252Expr

namespace JnzOpcode

def JNZ_FLAGS : Flags where
  dst_base_fp := none
  op0_base_fp := some true
  op1_imm := some true
  op1_base_fp := some false
  op1_base_ap := some false
  res_add := some false
  res_mul := some false
  pc_update_jump := some false
  pc_update_jump_rel := some false
  pc_update_jnz := some true
  ap_update_add := some false
  ap_update_add_1 := none
  opcode_call := some false
  opcode_ret := some false
  opcode_assert_eq := some false

def jnzInstrStwo (dst : DstSpec) (ap_update : Bool) := jnzInstr (Op0Spec.fp_plus (-1)) (Op1Spec.mem_pc_plus 1) dst ap_update

def jnz_instr (dst_base_fp ap_update_add_1 : Bool) (offset_dst : Felt) : Instr :=
    jnzInstrStwo
      (if dst_base_fp then
            (DstSpec.mem_fp_plus (int_from_Felt offset_dst))
            else
              (DstSpec.mem_ap_plus (int_from_Felt offset_dst)))
      (ap_update_add_1)

namespace JnzNotTakenOpcode

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal): Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (none) (some 65535) (some 1) (JNZ_FLAGS)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧

    ∃ (dst_val : Felt252Words),
      (
          Felt252IdMemory.read_felt252.spec memory
            (((ρflags FLAG_DST_BASE_FP_INDEX) * casmStateVal.fp + (1 - (ρflags FLAG_DST_BASE_FP_INDEX)) * casmStateVal.ap) + (offset_as_signed_Felt ρoffset0))
            dst_val
      ) ∧
      dst_val.limb_sum = 0 ∧

      ρCasmStateVal = ⟨casmStateVal.pc + 2,
        casmStateVal.ap + ρflags FLAG_AP_UPDATE_ADD_1_INDEX, casmStateVal.fp⟩


def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat)
    : Prop :=
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (offset_dst : Felt), ∃ (dst_base_fp ap_update_add_1 : Bool),
          mem (casmStateVal.pc.toFelt252) = (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction.toNat ∧
          (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction.NextState mem
            casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))


theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal) :
    spec memory casmStateVal ρCasmStateVal num_steps := by

  intro ns_lim cs_bound
  rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, dst_val, hread_dst, h_dst_val_ls, rfl⟩

  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hoffset0 hoffset1 hoffset2 hflags
  rcases hverifyInstruction with ⟨instr, hinstr_pc, hinstr_offsets_flags⟩
  rcases hinstr_pc with ⟨instr252, hinstr252_pc, hinstr252_encodes⟩

  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252_pc with ⟨value_n, hvalue_n⟩ --

  rw [hoffset1, hoffset2] at hinstr_offsets_flags
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr_offsets_flags
  dsimp [OFFSET_BITS] at hinstr_offsets_flags

  dsimp [JNZ_FLAGS, Flags.to_arr] at hflags
  rw [hflags 1, hflags 2, hflags 3, hflags 4, hflags 5, hflags 6, hflags 7, hflags 8,
      hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr_offsets_flags
  simp only [Bool.toFelt_inj] at hinstr_offsets_flags

  rcases hinstr_offsets_flags with ⟨h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp[CasmStateVal.strongly_bounded]
    constructor
    · use ap_nat + (ρflags FLAG_AP_UPDATE_ADD_1_INDEX).val
      dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX]
      rw [h_apAdd1]
      constructor
      · calc
          ap_nat + ZMod.val instr.apAdd1.toFelt < 2 ^ 29 + num_steps + ZMod.val instr.apAdd1.toFelt := by
            linarith
          _ <= 2 ^ 29 + num_steps + 1 := by
            apply add_le_add_left instr.apAdd1.toFelt_le_one
          _ = 2 ^ 29 + (num_steps + 1) := by
            linarith
      · rw[Nat.cast_add, h_ap_nat, ← (instr.apAdd1).toFelt_val_coe]

    · use fp_nat
      constructor
      · linarith
      · exact h_fp_nat

  intro mem hmem

  rw [hmem.2 _ _ _ hinstr252_pc hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252_encodes]

  use ρoffset0
  use instr.dstReg
  use instr.apAdd1

  constructor
  · apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [jnz_instr, jnzInstrStwo, jnzInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←BitVec_toFelt_inj]
      by_cases h0 : instr.dstReg <;> simp [h0] <;> simp only [h_offDst] <;>
      exact BitVec_u16_eq_from_Felt_to_u16
    · simp only [←h_offOp0]
    · simp only [←h_dstOp1]
    · cases instr.dstReg <;> simp
    · simp only [←h_op0Reg]
    · simp only [←h_op1Imm]
    · simp only [←h_op1Fp]
    · simp only [←h_op1Ap]
    · simp only [←h_resAdd]
    · simp only [←h_resMul]
    · simp only [←h_pcJumpAbs]
    · simp [←h_pcJumpRel]
    · simp only [←h_pcJnz]
    · simp only [←h_apAdd]
    · rfl
    · simp only [←h_opcodeCall]
    · simp only [←h_opcodeRet]
    · simp only [←h_opcodeAssertEq]
    -- The next state is as defined by the semantics
  apply nextState_jnz _ _ _ _ _ _ _|>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]

  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252_pc

  have pc_plus2 : (casmStateVal.pc + 2).toFelt252 = casmStateVal.pc.toFelt252 + 2 := toFelt252_add_two_of_RangeChecked pc_rc

  unfold Felt252IdMemory.read_felt252.spec at hread_dst
  unfold Felt252IdMemory.read_felt252.spec_auto at hread_dst

  rcases memory.IsRangeChecked_of_HasValue memChecked hread_dst with ⟨dst_val_n, h_dst_val_n⟩

  constructor
  · cases dstReg_val : instr.dstReg
    · simp
      have h_dst_address : mem (casmStateVal.ap.toFelt252 + intClip (int_from_Felt ρoffset0)) =
        dst_val_n.eval := by
        dsimp only [FLAG_DST_BASE_FP_INDEX] at hread_dst
        rw[h_dstReg, dstReg_val] at hread_dst
        simp only [Bool.toFelt] at hread_dst
        simp at hread_dst
        rw [← hmem.2 (casmStateVal.ap + offset_as_signed_Felt ρoffset0) dst_val dst_val_n hread_dst h_dst_val_n]
        rw[h_offDst]
        rw [toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
      rw[h_dst_address]
      rw[Felt252Nats.zero_if_sum_limbs_zero h_dst_val_n h_dst_val_ls]
      simp
      exact pc_plus2

    · simp
      have h_dst_address : mem (casmStateVal.fp.toFelt252 + intClip (int_from_Felt ρoffset0)) =
        dst_val_n.eval := by
        dsimp only [FLAG_DST_BASE_FP_INDEX] at hread_dst
        rw[h_dstReg, dstReg_val] at hread_dst
        simp only [Bool.toFelt] at hread_dst
        simp at hread_dst
        rw [← hmem.2 (casmStateVal.fp + offset_as_signed_Felt ρoffset0) dst_val dst_val_n hread_dst h_dst_val_n]
        rw[h_offDst]
        rw [toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
      rw[h_dst_address]
      rw[Felt252Nats.zero_if_sum_limbs_zero h_dst_val_n h_dst_val_ls]
      simp
      exact pc_plus2

  constructor
  · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX]
    rw[h_apAdd1]
    cases apAdd1_val : instr.apAdd1
    · simp [Bool.toFelt]
    · simp [Bool.toFelt]
      exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat (show ap_nat < 2 ^ 29 + num_steps + 2 by linarith[ap_bound])

  rfl

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState):
    AirBuilder × AirLookupTerms × CasmState :=

  let _state := DecodeInstruction.call airBuilder lookupTerms
    none (some 65535) (some 1) JNZ_FLAGS casmState.pc

  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset_dst := _state.2.2.1 --
  let flags := _state.2.2.2.2.2

  let flag_dst_base_fp := flags FLAG_DST_BASE_FP_INDEX
  let ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

  let _state:= ab1.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)
  let ab2:= _state.1
  let mem_dst_base := _state.2

  let _state := Felt252IdMemory.read_felt252 ab2 lt1 (mem_dst_base + offset_dst)
  let ab3 := _state.1
  let lt2 := _state.2.1
  let dst := _state.2.2

  let dst_sum := dst.limb_sum

  let ab4 := AirBuilder.constrain ab3 dst_sum

  (ab4, lt2, ⟨casmState.pc + FeltExpr.const 2, casmState.ap + ap_update_add_1, casmState.fp⟩)


theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
    (casmState : CasmState)
    (num_steps: Nat):
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) num_steps := by

  unfold call; lift_lets
  intro state1 ab1 lt1 offset_dst flags
    flag_dst_base_fp flag_op1_base_ap
    state2 ab2 mem_dst_base
    state3 ab3 lt2 dst
    dst_sum
    ab4
  intro hab4 hlt2

  have ⟨hab3, h_c_offset_dst⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab4

  have h_dst_sum: dst_sum = dst.limb_sum := by --
    rfl

  have ⟨hab2, hlt1, hread_felt252⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab2 _ _ h_rc h_mem.1 (mem_dst_base + offset_dst) hab3 hlt2

  have hread_felt252_simp : Felt252IdMemory.read_felt252.spec memAssign (FeltExpr.eval varAssign (mem_dst_base + offset_dst)) (Felt252Expr.eval varAssign dst) := by
    exact hread_felt252

  have h_mem_dst_base_def: mem_dst_base = (ab1.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)).2 := by
    rfl

  have ⟨hab1, h_mem_dst_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2
  have h_mem_dst_base : FeltExpr.eval varAssign mem_dst_base = FeltExpr.eval varAssign
    (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap) := by
    rw [h_mem_dst_base_def]
    exact h_mem_dst_base_pre

  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab _ _ h_rc h_mem h_verify_instr none (some 65535) (some 1) JNZ_FLAGS casmState.pc hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_

  constructor
  . exact h_decode
  use Felt252Expr.eval varAssign dst

  constructor
  · simp only [FeltExpr.eval_add] at hread_felt252_simp
    rw [h_mem_dst_base] at hread_felt252_simp
    unfold offset_dst flag_dst_base_fp flags state1 at hread_felt252_simp
    simp only [FeltExpr.eval_add] at hread_felt252_simp
    simp only [offset_as_signed_Felt_as_offset]
    exact hread_felt252_simp

  constructor
  · have : (Felt252Expr.eval varAssign dst).limb_sum = FeltExpr.eval varAssign dst_sum := by
      rw [dst.eval_of_limb_sum]
    rw [this]
    exact h_c_offset_dst

  rfl

theorem sound_jnz_not_taken [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset_dst, dst_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction
  use h_instr


end JnzNotTakenOpcode

namespace JnzTakenOpcode

variable [Fact (Nat.Prime Stwo.P)]

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal): Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (none) (some 65535) (some 1) (JNZ_FLAGS)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧

    ∃ (dst_val : Felt252Words),
      (
          Felt252IdMemory.read_felt252.spec memory
            (((ρflags FLAG_DST_BASE_FP_INDEX) * casmStateVal.fp + (1 - (ρflags FLAG_DST_BASE_FP_INDEX)) * casmStateVal.ap) + (offset_as_signed_Felt ρoffset0))
            dst_val
      ) ∧
      (∃ res: Felt, res * dst_val.limb_sum = 1 ) ∧
      (∃ res_squares: Felt, res_squares * dst_val.limb_sum_squares = 1) ∧
      ∃ (delta_pc : Felt),
      (
          Felt252IdMemory.read_rel_imm.spec memory
            (casmStateVal.pc + 1)
            delta_pc
      ) ∧

      ρCasmStateVal = ⟨casmStateVal.pc + delta_pc,
        casmStateVal.ap + ρflags FLAG_AP_UPDATE_ADD_1_INDEX, casmStateVal.fp⟩


def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat)
    : Prop :=
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (offset_dst : Felt), ∃ (dst_base_fp ap_update_add_1 : Bool),
          mem (casmStateVal.pc.toFelt252) = (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction.toNat ∧
          (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction.NextState mem
            casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))


theorem spec_of_spec_auto [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal) :
    spec memory casmStateVal ρCasmStateVal num_steps := by

  intro ns_lim cs_bound
  rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode,
    dst_val, hread_dst, h_res, h_res_squares, delta_pc, h_delta_pc, rfl⟩
  -- ⟨ res, h_res⟩
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hoffset0 hoffset1 hoffset2 hflags
  rcases hverifyInstruction with ⟨instr, hinstr_pc, hinstr_offsets_flags⟩
  rcases hinstr_pc with ⟨instr252, hinstr252_pc, hinstr252_encodes⟩

  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252_pc with ⟨value_n, hvalue_n⟩ --

  rw [hoffset1, hoffset2] at hinstr_offsets_flags
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr_offsets_flags
  dsimp [OFFSET_BITS] at hinstr_offsets_flags

  dsimp [JNZ_FLAGS, Flags.to_arr] at hflags
  rw [hflags 1, hflags 2, hflags 3, hflags 4, hflags 5, hflags 6, hflags 7, hflags 8,
      hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr_offsets_flags
  simp only [Bool.toFelt_inj] at hinstr_offsets_flags

  rcases hinstr_offsets_flags with ⟨h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp[CasmStateVal.strongly_bounded]
    constructor
    · use ap_nat + (ρflags FLAG_AP_UPDATE_ADD_1_INDEX).val
      dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX]
      rw [h_apAdd1]
      constructor
      · calc
          ap_nat + ZMod.val instr.apAdd1.toFelt < 2 ^ 29 + num_steps + ZMod.val instr.apAdd1.toFelt := by
            linarith
          _ <= 2 ^ 29 +  num_steps + 1 := by
            apply add_le_add_left instr.apAdd1.toFelt_le_one
          _ = 2 ^ 29 + (num_steps + 1) := by
            linarith
      · rw[Nat.cast_add, h_ap_nat, ← (instr.apAdd1).toFelt_val_coe]

    · use fp_nat
      constructor
      · linarith
      · exact h_fp_nat

  intro mem hmem

  rw [hmem.2 _ _ _ hinstr252_pc hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252_encodes]

  use ρoffset0
  use instr.dstReg
  use instr.apAdd1

  constructor
  · apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [jnz_instr, jnzInstrStwo, jnzInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←BitVec_toFelt_inj]
      by_cases h0 : instr.dstReg <;> simp [h0] <;> simp only [h_offDst] <;>
      exact BitVec_u16_eq_from_Felt_to_u16
    · simp only [←h_offOp0]
    · simp only [←h_dstOp1]

    · cases instr.dstReg <;> simp

    · simp only [←h_op0Reg]
    · simp only [←h_op1Imm]
    · simp only [←h_op1Fp]
    · simp only [←h_op1Ap]
    · simp only [←h_resAdd]
    · simp only [←h_resMul]
    · simp only [←h_pcJumpAbs]
    · simp [←h_pcJumpRel]
    · simp only [←h_pcJnz]
    · simp only [←h_apAdd]
    · rfl
    · simp only [←h_opcodeCall]
    · simp only [←h_opcodeRet]
    · simp only [←h_opcodeAssertEq]
    -- The next state is as defined by the semantics
  apply nextState_jnz _ _ _ _ _ _ _|>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]

  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252_pc

  unfold Felt252IdMemory.read_felt252.spec at hread_dst
  unfold Felt252IdMemory.read_felt252.spec_auto at hread_dst

  rcases memory.IsRangeChecked_of_HasValue memChecked hread_dst with ⟨dst_val_n, h_dst_val_n⟩

  have dst_val_neq_zero : dst_val_n.eval ≠ 0 := by
        exact (Felt252Nats.not_zero_if_sums_inversible h_dst_val_n) ⟨ h_res, h_res_squares ⟩

  constructor
  · cases dstReg_val : instr.dstReg
    · simp
      have h_dst_address : mem (casmStateVal.ap.toFelt252 + intClip (int_from_Felt ρoffset0)) =
        dst_val_n.eval := by
        dsimp only [FLAG_DST_BASE_FP_INDEX] at hread_dst
        rw[h_dstReg, dstReg_val] at hread_dst
        simp only [Bool.toFelt] at hread_dst
        simp at hread_dst
        rw [← hmem.2 (casmStateVal.ap + offset_as_signed_Felt ρoffset0) dst_val dst_val_n hread_dst h_dst_val_n]
        rw[h_offDst]
        rw [toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
      rw[h_dst_address]

      simp[dst_val_neq_zero]
      unfold intClip natClip ; simp ; norm_num

      -- capsulate? in theorem? used in call_opcode too.
      rcases h_delta_pc with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
      have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.pc + 1) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
        use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
      rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩
      rw [←toFelt252_add_one_of_RangeChecked pc_rc]
      rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
      rcases pc_rc with ⟨pc_nat, h_pc_lt, h_pc_eq⟩
      have h_pc_lt2 : pc_nat < 2 ^ 30 - 1 := by
        calc
          pc_nat < 2 ^ 29 := h_pc_lt
          _ < 2 ^ 30 - 1 := by norm_num
      exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt2 hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2

    · simp
      have h_dst_address : mem (casmStateVal.fp.toFelt252 + intClip (int_from_Felt ρoffset0)) =
        dst_val_n.eval := by
        dsimp only [FLAG_DST_BASE_FP_INDEX] at hread_dst
        rw[h_dstReg, dstReg_val] at hread_dst
        simp only [Bool.toFelt] at hread_dst
        simp at hread_dst
        rw [← hmem.2 (casmStateVal.fp + offset_as_signed_Felt ρoffset0) dst_val dst_val_n hread_dst h_dst_val_n]
        rw[h_offDst]
        rw [toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
      rw[h_dst_address]

      -- have zxc := Felt252Nats.not_zero_iff_sums_inversible
      --rw[Felt252Nats.zero_if_sum_limbs_zero h_dst_val_n h_dst_val_ls]

      simp[dst_val_neq_zero]
      unfold intClip natClip ; simp ; norm_num

      -- capsulate? in theorem? used in call_opcode too.
      rcases h_delta_pc with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
      have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.pc + 1) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
        use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
      rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩
      rw [←toFelt252_add_one_of_RangeChecked pc_rc]
      rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
      rcases pc_rc with ⟨pc_nat, h_pc_lt, h_pc_eq⟩
      have h_pc_lt2 : pc_nat < 2 ^ 30 - 1 := by
        calc
          pc_nat < 2 ^ 29 := h_pc_lt
          _ < 2 ^ 30 - 1 := by norm_num
      exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt2 hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2

  constructor
  · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX]
    rw[h_apAdd1]
    cases apAdd1_val : instr.apAdd1
    · simp [Bool.toFelt]
    · simp [Bool.toFelt]
      exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat (show ap_nat < 2 ^ 29 + num_steps + 2 by linarith[ap_bound])

  rfl



  def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState):
    AirBuilder × AirLookupTerms × CasmState :=

  let _state := DecodeInstruction.call airBuilder lookupTerms
    none (some 65535) (some 1) JNZ_FLAGS casmState.pc

  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset_dst := _state.2.2.1 --
  let flags := _state.2.2.2.2.2

  let flag_dst_base_fp := flags FLAG_DST_BASE_FP_INDEX
  let ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

  let _state:= ab1.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)
  let ab2:= _state.1
  let mem_dst_base := _state.2

  let _state := Felt252IdMemory.read_felt252 ab2 lt1 (mem_dst_base + offset_dst)
  let ab3 := _state.1
  let lt2 := _state.2.1
  let dst := _state.2.2

  let dst_sum := dst.limb_sum
  let res := (FeltExpr.const 1) / dst_sum
  let ab4 := AirBuilder.constrain ab3 (res * dst_sum - FeltExpr.const 1)

  let dst_sum_squares := dst.limb_sum_squares
  let res_squares := (FeltExpr.const 1) / dst_sum_squares
  let ab5 := AirBuilder.constrain ab4 (res_squares * dst_sum_squares - FeltExpr.const 1)

  let _state := Felt252IdMemory.read_rel_imm ab5 lt2 (casmState.pc + FeltExpr.const 1)
  let ab6:= _state.1
  let lt3 := _state.2.1
  let delta_pc := _state.2.2

  (ab6, lt3, ⟨casmState.pc + delta_pc, casmState.ap + ap_update_add_1, casmState.fp⟩)


theorem sound_auto [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
    (casmState : CasmState)
    (num_steps: Nat):
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) num_steps := by

  unfold call; lift_lets
  intro state1 ab1 lt1 offset_dst flags
    flag_dst_base_fp flag_op1_base_ap
    state2 ab2 mem_dst_base
    state3 ab3 lt2 dst
    dst_sum
    res
    ab4
    dst_sum_squares
    res_squares
    ab5
    state4 ab6 lt3 delta_pc
  intro hab6 hlt3

  have ⟨hab5, hlt2, hread_rel_imm⟩ := Felt252IdMemory.read_rel_imm.sound_auto varAssign memAssign ab5 _ _ h_mem.1 (casmState.pc + FeltExpr.const 1) hab6 hlt3
  have hread_rel_imm_simp : Felt252IdMemory.read_rel_imm.spec memAssign (FeltExpr.eval varAssign (casmState.pc + FeltExpr.const 1)) (FeltExpr.eval varAssign delta_pc) := by
    exact hread_rel_imm

  have ⟨hab4, h_sum_squares_inv⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
  have ⟨hab3, h_sum_inv⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab4

  have h_dst_sum: dst_sum = dst.limb_sum := by --
    rfl
  have h_dst_sum_squares: dst_sum_squares = dst.limb_sum_squares := by --
    rfl

  have ⟨hab2, hlt1, hread_felt252⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab2 _ _ h_rc h_mem.1 (mem_dst_base + offset_dst) hab3 hlt2

  have hread_felt252_simp : Felt252IdMemory.read_felt252.spec memAssign (FeltExpr.eval varAssign (mem_dst_base + offset_dst)) (Felt252Expr.eval varAssign dst) := by
    exact hread_felt252

  have h_mem_dst_base_def: mem_dst_base = (ab1.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)).2 := by
    rfl

  have ⟨hab1, h_mem_dst_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2
  have h_mem_dst_base : FeltExpr.eval varAssign mem_dst_base = FeltExpr.eval varAssign
    (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap) := by
    rw [h_mem_dst_base_def]
    exact h_mem_dst_base_pre

  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab _ _ h_rc h_mem h_verify_instr none (some 65535) (some 1) JNZ_FLAGS casmState.pc hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_

  constructor
  . exact h_decode
  use Felt252Expr.eval varAssign dst

  constructor
  · simp only [FeltExpr.eval_add] at hread_felt252_simp
    rw [h_mem_dst_base] at hread_felt252_simp
    unfold offset_dst flag_dst_base_fp flags state1 at hread_felt252_simp
    simp only [FeltExpr.eval_add] at hread_felt252_simp
    simp only [offset_as_signed_Felt_as_offset]
    exact hread_felt252_simp

  constructor
  · use FeltExpr.eval varAssign res
    have : (Felt252Expr.eval varAssign dst).limb_sum = FeltExpr.eval varAssign dst_sum := by
      rw [dst.eval_of_limb_sum]
    rw [this]
    simp only [← FeltExpr.eval_mul]
    simp only [FeltExpr.eval_sub, FeltExpr.eval_const] at h_sum_inv
    rw[sub_eq_zero] at h_sum_inv
    exact h_sum_inv

  constructor
  · use FeltExpr.eval varAssign res_squares
    have : (Felt252Expr.eval varAssign dst).limb_sum_squares = FeltExpr.eval varAssign dst_sum_squares := by
      rw [dst.eval_of_limb_sum_squares]
    rw [this]
    simp only [← FeltExpr.eval_mul]
    simp only [FeltExpr.eval_sub, FeltExpr.eval_const] at h_sum_squares_inv
    rw[sub_eq_zero] at h_sum_squares_inv
    exact h_sum_squares_inv

  use delta_pc.eval varAssign
  constructor
  · simp only [FeltExpr.eval_add, FeltExpr.eval_const] at hread_rel_imm_simp
    dsimp only [CasmState.eval]
    exact hread_rel_imm_simp

  rfl

theorem sound_jnz_taken [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset_dst, dst_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction
  use h_instr


end JnzTakenOpcode

end JnzOpcode
