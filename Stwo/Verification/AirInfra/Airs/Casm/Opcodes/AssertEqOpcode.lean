
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Core.Felt252IdMemory.VerifyEqual
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst
import Verification.AirInfra.Airs.Casm.Opcodes.Util

namespace AssertEqOpcode

def flag_assert (is_imm is_double_deref : Bool) := ¬(is_imm = true ∧ is_double_deref = true)

def CALL_FLAGS (is_imm is_double_deref : Bool) : Flags where
  dst_base_fp := none
  op0_base_fp := if is_double_deref = true then none else some true
  op1_imm := some is_imm
  op1_base_fp := if is_double_deref = false ∧ is_imm = false then none else some false
  op1_base_ap := if is_double_deref = false ∧ is_imm = false then none else some false
  res_add := some false
  res_mul := some false
  pc_update_jump := some false
  pc_update_jump_rel := some false
  pc_update_jnz := some false
  ap_update_add := some false
  ap_update_add_1 := none
  opcode_call := some false
  opcode_ret := some false
  opcode_assert_eq := some true


def decodeOffset0 : Option (BitVec 16) := none
def decodeOffset1 (is_imm is_double_deref : Bool) : Option (BitVec 16) :=
  if is_imm then some (-1) else (if is_double_deref then none else some (-1))
def decodeOffset2 (is_imm : Bool) : Option (BitVec 16) := if is_imm then some 1 else none

def call
    (is_imm is_double_deref : Bool)
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=

  let offset0 := decodeOffset0
  let offset1 := decodeOffset1 is_imm is_double_deref
  let offset2 := decodeOffset2 is_imm

  let _state := DecodeInstruction.call airBuilder lookupTerms
    offset0 offset1 offset2 (CALL_FLAGS is_imm is_double_deref) casmState.pc
  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset0₁ := _state.2.2.1
  let offset1₁ := _state.2.2.2.1
  let offset2₁ := _state.2.2.2.2.1
  let flags := _state.2.2.2.2.2

  let flag_dst_base_fp := flags FLAG_DST_BASE_FP_INDEX
  let flag_op0_base_fp := flags FLAG_OP0_BASE_FP_INDEX
  let flag_op1_base_fp := flags FLAG_OP1_BASE_FP_INDEX
  let flag_op1_base_ap := flags FLAG_OP1_BASE_AP_INDEX
  let flag_ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

  let mem_dst_base := flag_dst_base_fp * casmState.fp + (FeltExpr.const 1 - flag_dst_base_fp) * casmState.ap

  let _state := if is_double_deref = true then (
        let mem0_base := flag_op0_base_fp * casmState.fp + (FeltExpr.const 1 - flag_op0_base_fp) * casmState.ap
        Felt252IdMemory.read_address ab1 lt1 (mem0_base + offset1₁)
      )
      else (if is_imm = true then
          (ab1, lt1, casmState.pc)
        else
          let ab2' := AirBuilder.constrain ab1 (flag_op1_base_fp + flag_op1_base_ap - FeltExpr.const 1)
          (ab2', lt1, flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
      )
  let ab2 := _state.1
  let lt2 := _state.2.1
  let mem1_base := _state.2.2
  let _state := MemVerifyEqual.call ab2 lt2 (mem_dst_base + offset0₁) (mem1_base + offset2₁)
  let ab3 := _state.1
  let lt3 := _state.2

  let next_ap := casmState.ap + flag_ap_update_add_1

  let next_pc := if is_imm = true then
      casmState.pc + FeltExpr.const 2
    else casmState.pc + FeltExpr.const 1

  (ab3, lt3, ⟨next_pc, next_ap, casmState.fp⟩)

def mkAssertEqInstr (is_imm is_double_deref : Bool)
    (dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2 : Felt) : Instr :=
  let dstOff := int_from_Felt offset0
  let op0Off := if is_double_deref = true then (int_from_Felt offset1) else (-1)
  let op1Off := if is_imm = true then 1 else (int_from_Felt offset2)
  assertEqInstr
    -- op0
    (if op0_base_fp = 1 then Op0Spec.fp_plus op0Off else Op0Spec.ap_plus op0Off)
    -- res
    (ResSpec.op1
      (if is_double_deref = true then
          (Op1Spec.mem_op0_plus op1Off)
        else (if is_imm then
            (Op1Spec.mem_pc_plus 1)
          else (if op1_base_fp = 1 then Op1Spec.mem_fp_plus op1Off else Op1Spec.mem_ap_plus op1Off))))
    -- dst
    (if dst_base_fp = 1 then (DstSpec.mem_fp_plus dstOff) else DstSpec.mem_ap_plus dstOff)
    -- ap_update
    (ap_update_add_1 = 1)

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (is_imm is_double_deref : Bool) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory decodeOffset0 (decodeOffset1 is_imm is_double_deref) (decodeOffset2 is_imm) (CALL_FLAGS is_imm is_double_deref)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ρCasmStateVal = ⟨
      if is_imm = true then casmStateVal.pc + 2 else casmStateVal.pc + 1,
      casmStateVal.ap + ρflags FLAG_AP_UPDATE_ADD_1_INDEX,
      casmStateVal.fp
    ⟩ ∧
    ∃ mem1_base,
      (if is_double_deref = true then
        Felt252IdMemory.read_address.spec
          memory
          (ρflags FLAG_OP0_BASE_FP_INDEX * casmStateVal.fp
            + (1 - ρflags FLAG_OP0_BASE_FP_INDEX) * casmStateVal.ap + (offset_as_signed_Felt ρoffset1))
          mem1_base
        else (if is_imm = true then
            mem1_base = casmStateVal.pc
          else
            mem1_base = (ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp + ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap) ∧
            ρflags FLAG_OP1_BASE_FP_INDEX + ρflags FLAG_OP1_BASE_AP_INDEX - 1 = 0
        )) ∧
      MemVerifyEqual.spec memory
          ((ρflags FLAG_DST_BASE_FP_INDEX) * casmStateVal.fp
            + (1 - ρflags FLAG_DST_BASE_FP_INDEX) * casmStateVal.ap + (offset_as_signed_Felt ρoffset0))
          (mem1_base + (offset_as_signed_Felt ρoffset2))

def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (is_imm is_double_deref : Bool) (num_steps: Nat) : Prop :=
    flag_assert is_imm is_double_deref →
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2 : Felt),
          mem (casmStateVal.pc.toFelt252) =
            (mkAssertEqInstr is_imm is_double_deref dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction.toNat ∧
          (mkAssertEqInstr is_imm is_double_deref dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction.NextState mem
            casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))

set_option maxHeartbeats 300000 in
theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {is_imm is_double_deref : Bool}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal is_imm is_double_deref) :
    spec memory casmStateVal ρCasmStateVal is_imm is_double_deref num_steps := by
  intro h_flags_assert ns_lim cs_bound

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, rfl, mem1_base, h_mem1_base, h_verify_eq⟩
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hflags
  rcases hverifyInstruction with ⟨instr, hinstr1, hinstr2⟩
  rcases hinstr1 with ⟨instr252, hinstr252a, hinstr252b⟩
  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a
  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩

  simp [decodeOffset0] at hoffset0
  simp [decodeOffset1] at hoffset1
  simp [decodeOffset2] at hoffset2
  dsimp [CALL_FLAGS, Flags.to_arr] at hflags
  rw [hflags 2, hflags 5, hflags 6, hflags 7, hflags 8, hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr2
  simp only [Bool.toFelt_inj] at hinstr2
  rcases hinstr2 with ⟨h_offDst, h_offOp0, h_offOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX] ; rw [h_apAdd1]
    exact CasmStateVal.next_state_strongly_bound_of_apAdd1 cs_bound

  intro mem hmem
  rw [hmem.2 _ _ _ hinstr252a hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]

  use ρflags FLAG_DST_BASE_FP_INDEX
  use ρflags FLAG_OP0_BASE_FP_INDEX
  use ρflags FLAG_OP1_BASE_FP_INDEX
  use ρflags FLAG_AP_UPDATE_ADD_1_INDEX
  use ρoffset0, ρoffset1, ρoffset2
  unfold FLAG_DST_BASE_FP_INDEX FLAG_OP0_BASE_FP_INDEX FLAG_OP1_BASE_FP_INDEX FLAG_AP_UPDATE_ADD_1_INDEX
  constructor
  · -- The instruction is in memory at pc
    apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [mkAssertEqInstr, assertEqInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←BitVec_toFelt_inj]
      by_cases h0 : ρflags 0 = 1 <;> simp [h0] <;> simp only [h_offDst] <;>
      exact BitVec_u16_eq_from_Felt_to_u16
    · simp only [←BitVec_toFelt_inj]
      by_cases h_dd : is_double_deref = true
      · by_cases h0 : ρflags 1 = 1 <;> simp [h0] <;> simp only [h_offOp0, if_pos h_dd] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      simp [if_neg h_dd] at hoffset1
      by_cases h1 : ρflags 1 = 1 <;> simp [h1, if_neg h_dd] <;> simp only [←h_offOp0] <;>
      rw [hoffset1] <;> simp [BitVec.as_u16, offset_as_u16, OFFSET_BITS]
    · simp only [←BitVec_toFelt_inj, ←h_offOp1]
      by_cases h_imm : is_imm = true
      · cases is_double_deref <;> simp only [if_pos h_imm] at hoffset2 <;>
        simp [if_pos h_imm, hoffset2] <;> simp [BitVec.as_u16, offset_as_u16, OFFSET_BITS]
      cases is_double_deref <;> simp [if_neg h_imm] <;>
      by_cases h3 : ρflags 3 = 1 <;>
      simp [h3, h_offOp1] <;> exact BitVec_u16_eq_from_Felt_to_u16
    -- The flags
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : ρflags 0 = 1 <;> simp [h0]
      · simp only [←h_dstReg, h0]
        simp [Bool.toFelt]
      simp only [h_dstReg] at h0
      exact Bool.false_toFelt_eq h0
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : ρflags 1 = 1 <;> simp [h0]
      · simp only [←h_op0Reg, h0]
        simp [Bool.toFelt]
      simp only [h_op0Reg] at h0
      exact Bool.false_toFelt_eq h0
    · simp only [←Bool.toFelt_inj, ←h_op1Imm]
      by_cases h0 : ρflags 3 = 1 <;> simp [h0] <;>
      unfold flag_assert at h_flags_assert <;> revert h_flags_assert <;>
      cases is_double_deref <;> cases is_imm <;>
      simp [Bool.false_toFelt_ne_true_toFelt]
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : ρflags 3 = 1 <;> simp [h0, ←h_op1Fp]
      · cases is_double_deref <;> cases is_imm <;>
        simp [Bool.toFelt] <;>
        have hflag3 := hflags 3 <;> simp [Fin.coe_ofNat_eq_mod] at hflag3 <;>
        simp [h0, Bool.toFelt] at hflag3
      cases is_double_deref <;> cases is_imm <;>
      simp only [h_op1Fp] at h0 <;> simp only [h_op1Fp] <;>
      simp [Bool.false_toFelt_ne_true_toFelt, Bool.false_toFelt_eq h0]
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : is_double_deref = false ∧ is_imm = false
      · simp [h0.1, h0.2, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at h_mem1_base
        have h_cflags := h_mem1_base.2
        simp only [←h_op1Ap]
        simp [h0.1, h0.2, Bool.toFelt]
        by_cases h0 : ρflags 3 = 1 <;> simp [h0]
        · simp [h0] at h_cflags ; exact h_cflags
        rw [h_op1Fp, Bool.toFelt_ne_one_iff_eq_zero, ←h_op1Fp] at h0
        simp only [h0, zero_add, sub_eq_zero] at h_cflags
        exact h_cflags
      simp [h0] at hflags
      have hflag3 := hflags 3 ; simp [Fin.coe_ofNat_eq_mod] at hflag3
      have hflag4 := hflags 4 ; simp [Fin.coe_ofNat_eq_mod] at hflag4
      simp only [hflag4, Bool.toFelt_inj] at h_op1Ap
      simp [hflag3, ←h_op1Ap, Bool.toFelt]
      revert h0
      cases is_double_deref <;> cases is_imm <;> simp
    · simp only [←h_resAdd]
    · simp only [←h_resMul]
    · simp only [←h_pcJumpAbs]
    · simp [←h_pcJumpRel]
    · simp only [←h_pcJnz]
    · simp only [←h_apAdd]
    · simp only [h_apAdd1]
      exact Bool.eq_decide_toFelt_eq_1
    · simp only [←h_opcodeCall]
    · simp only [←h_opcodeRet]
    · simp only [←h_opcodeAssertEq]
  -- The next state is as defined by the semantics
  apply nextState_assert_eq _ _ _ _ _ _ _|>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]

  constructor
  · -- The pc is advanced correctly
    unfold flag_assert at h_flags_assert
    cases is_double_deref
    · cases is_imm <;> by_cases h0 : ρflags 3 = 1 <;> simp [h0] <;>
      exact toFelt252_add_of_RangeChecked _ pc_rc (by simp [Stwo.P])
    simp at h_flags_assert
    rw [h_flags_assert]
    by_cases h0 : ρflags 3 = 1 <;> simp <;>
    exact toFelt252_add_of_RangeChecked _ pc_rc (by simp [Stwo.P])
  constructor
  · -- The ap is advanced correctly
    simp only [h_apAdd1]
    cases instr.apAdd1
    · simp [Bool.toFelt]
    · simp [Bool.toFelt]
      rcases cs_bound with ⟨⟨ap_nat, ap_bound, h_ap_nat⟩, -⟩
      have : ap_nat< 2 ^ 29 + num_steps + 2 := by
        linarith
      exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat this

  constructor
  · -- The fp is unchanged.
    rfl
  -- The two values are equal
  unfold flag_assert at h_flags_assert
  cases is_double_deref
  · cases is_imm <;> simp at h_mem1_base hflags <;>
    have hflag1 := hflags 1 <;> simp [Fin.coe_ofNat_eq_mod] at hflag1
    · rw [h_mem1_base.1] at h_verify_eq
      unfold FLAG_DST_BASE_FP_INDEX FLAG_OP1_BASE_FP_INDEX FLAG_OP1_BASE_AP_INDEX at h_verify_eq
      have h_cflags := h_mem1_base.2
      unfold FLAG_OP1_BASE_FP_INDEX FLAG_OP1_BASE_AP_INDEX at h_cflags
      by_cases h3 : ρflags 3 = 1 <;> simp [h3]
      · simp [h3] at h_cflags
        revert h_verify_eq ; simp only [h_dstReg]
        cases instr.dstReg <;>
        simp only [h3, h_cflags, Bool.toFelt] <;>
        intro h_verify_eq <;> simp <;> simp at h_verify_eq <;>
        exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
      rw [h_op1Fp, Bool.toFelt_ne_one_iff_eq_zero, ←h_op1Fp] at h3
      simp only [h3, zero_add, sub_eq_zero] at h_cflags
      revert h_verify_eq ; simp only [h_dstReg]
      cases instr.dstReg <;>
      simp only [h3, h_cflags, Bool.toFelt] <;>
      intro h_verify_eq <;> simp <;> simp at h_verify_eq <;>
      exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
    rw [h_mem1_base] at h_verify_eq
    unfold MemVerifyEqual.spec MemVerifyEqual.spec_auto
      FLAG_DST_BASE_FP_INDEX at h_verify_eq
    have hflag3 := hflags 3 ; simp [Fin.coe_ofNat_eq_mod] at hflag3
    have hflag4 := hflags 4 ; simp [Fin.coe_ofNat_eq_mod] at hflag4
    simp at hoffset2
    revert h_verify_eq ; simp only [h_dstReg]
    cases instr.dstReg <;>
    simp only [hflag3, Bool.toFelt] <;>
    intro h_verify_eq <;>
    simp at h_verify_eq <;>
    rw [show (1 : Int) = (int_from_Felt ρoffset2) by rw [hoffset2] ; rw [←BitVec_toInt_eq_from_Felt_as_u16] ; simp] <;>
    exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
  -- Double deref
  simp at h_flags_assert

  simp only [↓reduceIte, FLAG_OP0_BASE_FP_INDEX] at h_mem1_base
  unfold Felt252IdMemory.read_address.spec Felt252IdMemory.read_address.spec_auto at h_mem1_base
  rcases h_mem1_base with ⟨mem1_base_252, h_num_bits, h_mem1_base_252, h_mem1_base_as_m31⟩
  simp [h_mem1_base_as_m31, FLAG_DST_BASE_FP_INDEX ] at h_verify_eq

  simp only [h_flags_assert, ↓reduceIte, Bool.false_eq_true]
  revert h_verify_eq h_mem1_base_252
  by_cases h0: ρflags 0 = 1 <;> simp [h0] <;>
  by_cases h1: ρflags 1 = 1 <;> simp [h1] <;>
  intro h_mem1_base_252 h_verify_eq <;>
  rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked h_mem1_base_252 hmem with ⟨value_n, h_mem1_base1, h_mem1_base2⟩ <;>
  rw [h_offOp0] at h_mem1_base_252 h_mem1_base2 <;>
  rw [toFelt252_add_offset_RangeChecked_eq (memory.IsRangeChecked_address_of_HasValue memChecked h_mem1_base_252)] at h_mem1_base2 <;>
  rw [←felt252_to_m31_eq mem1_base_252 value_n h_num_bits h_mem1_base1] at h_mem1_base2
  · rw [h_offOp0, h_mem1_base2]
    exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
  · rw [h_op0Reg, Bool.toFelt_ne_one_iff_eq_zero, ←h_op0Reg] at h1
    simp [h1] at h_mem1_base2
    rw [h_offOp0, h_mem1_base2]
    exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
  · rw [h_offOp0, h_mem1_base2]
    rw [h_dstReg, Bool.toFelt_ne_one_iff_eq_zero, ←h_dstReg] at h0
    simp [h0] at h_verify_eq
    exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem
  rw [h_dstReg, Bool.toFelt_ne_one_iff_eq_zero, ←h_dstReg] at h0
  rw [h_op0Reg, Bool.toFelt_ne_one_iff_eq_zero, ←h_op0Reg] at h1
  simp [h1] at h_mem1_base2
  rw [h_offOp0, h_mem1_base2]
  simp [h0] at h_verify_eq
  exact MemVerifyEqual.value_eq_of_mem_Agrees memory memChecked h_offDst h_offOp1 h_verify_eq mem hmem

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
    (is_imm is_double_deref : Bool)
    (num_steps: Nat):
    let ⟨new_ab, new_lt, ρCasmState⟩ := call is_imm is_double_deref ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) is_imm is_double_deref num_steps:= by
  unfold call DecodeInstruction.call ; lift_lets
  intro offset0 offset1 offset2
    state1 ab1 lt1 offset0₁ offset1₁ offset2₁ flags
    flag_dst_base_fp flag_op0_base_fp flag_op1_base_fp flag_op1_base_ap flag_ap_update_add_1
    mem_dst_base mem0_base ab2'
    state2 ab2 lt2 mem1_base
    state3 ab3 lt3
    next_ap next_pc
  intro hab3 hlt3
  have ⟨hab2, hlt2, verifyEqual⟩ := MemVerifyEqual.sound_auto varAssign memAssign _ _ _ h_mem.1.1
    (mem_dst_base + offset0₁) (mem1_base + offset2₁) hab3 hlt3
  cases is_double_deref
  · cases is_imm
    · have ⟨hab1, h_flags⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2
      have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
        _ _ _ h_rc h_mem h_verify_instr offset0 offset1 offset2 (CALL_FLAGS false false) casmState.pc hab1 hlt2
      use hab, hlt
      apply spec_of_spec_auto
      use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
      simp only [next_ap, next_pc, flag_ap_update_add_1, FLAG_AP_UPDATE_ADD_1_INDEX]
      use ?_, ?_, ?_, ?_
      constructor
      . exact h_decode
      constructor
      · simp ; rfl
      use (FeltExpr.eval varAssign mem1_base)
      simp only [offset_as_signed_Felt_as_offset]
      constructor
      · use rfl
        exact h_flags
      unfold mem_dst_base offset0₁ offset2₁ flag_dst_base_fp flags at verifyEqual
      exact verifyEqual
    have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      ab lt _ h_rc h_mem h_verify_instr offset0 offset1 offset2 (CALL_FLAGS true false) casmState.pc hab2 hlt2
    use hab, hlt
    apply spec_of_spec_auto
    use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
    simp only [next_ap, next_pc, flag_ap_update_add_1, FLAG_AP_UPDATE_ADD_1_INDEX]
    use ?_, ?_, ?_, ?_
    constructor
    . exact h_decode
    constructor
    · simp ; rfl
    use (FeltExpr.eval varAssign mem1_base)
    simp only [↓reduceIte, offset_as_signed_Felt_as_offset]
    use rfl
    exact verifyEqual
  have ⟨hab1, hlt1, hread_address⟩ := Felt252IdMemory.read_address.sound_auto
    varAssign memAssign ab1 lt1 h_satisfied h_rc h_mem.1 (mem0_base + offset1₁)
    hab2 hlt2
  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab lt _ h_rc h_mem h_verify_instr offset0 offset1 offset2 (CALL_FLAGS is_imm true) casmState.pc hab1 hlt1
  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  simp only [next_ap, next_pc, flag_ap_update_add_1, FLAG_AP_UPDATE_ADD_1_INDEX]
  use ?_, ?_, ?_, ?_
  constructor
  . exact h_decode
  constructor
  · cases is_imm <;> simp <;> rfl
  use (FeltExpr.eval varAssign mem1_base)
  simp only [↓reduceIte, offset_as_signed_Felt_as_offset]
  constructor
  · unfold offset1₁ mem0_base flag_op0_base_fp flags at hread_address
    simp only [FeltExpr.eval_add, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const] at hread_address
    exact hread_address
  unfold mem_dst_base offset0₁ offset2₁ flag_dst_base_fp flags at verifyEqual
  exact verifyEqual

theorem sound_assert_eq [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call false false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ false false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : AssertEqOpcode.flag_assert false false := by simp [AssertEqOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨dst_base_fp, op0_base_fp, op1_base_fp, ap_update_add_1, offset0, offset1, offset2, h_instr, h_next⟩
  use (AssertEqOpcode.mkAssertEqInstr false false
        dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr

theorem sound_assert_eq_imm [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call true false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ true false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : AssertEqOpcode.flag_assert true false := by simp [AssertEqOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨dst_base_fp, op0_base_fp, op1_base_fp, ap_update_add_1, offset0, offset1, offset2, h_instr, h_next⟩
  use (AssertEqOpcode.mkAssertEqInstr true false
        dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr

theorem sound_assert_eq_double_deref [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call false true ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ false true
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : AssertEqOpcode.flag_assert false true := by simp [AssertEqOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨dst_base_fp, op0_base_fp, op1_base_fp, ap_update_add_1, offset0, offset1, offset2, h_instr, h_next⟩
  use (AssertEqOpcode.mkAssertEqInstr false true
        dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr

end AssertEqOpcode
