
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

namespace JumpOpcode

variable [Fact (Nat.Prime Stwo.P)]

def flag_assert (rel imm double_deref : Bool) :=
  (imm = false ∨ double_deref = false) -- Cannot set flags to support double deref and immediate at the same time.
  ∧
  (rel = true ∨ imm = false) -- Immediate jump must be relative.
  ∧
  (double_deref = false ∨ rel = false) -- Double deref jump must be absolute.

def CALL_FLAGS (rel imm double_deref : Bool) : Flags where
  dst_base_fp := some true
  op0_base_fp := if double_deref = false then some true else none
  op1_imm := some imm
  op1_base_fp := if imm = true ∨ double_deref = true then some false else none
  op1_base_ap := if imm = true ∨ double_deref = true then some false else none
  res_add := some false
  res_mul := some false
  pc_update_jump := some !rel
  pc_update_jump_rel := some rel
  pc_update_jnz := some false
  ap_update_add := some false
  ap_update_add_1 := none
  opcode_call := some false
  opcode_ret := some false
  opcode_assert_eq := some false

-- Defined in the call

def decodeOffset1 (double_deref : Bool) : Option (BitVec 16) := if double_deref = true then none else some (-1)
def decodeOffset2 (imm : Bool) : Option (BitVec 16) := if imm then some 1 else none

def call
    (rel imm double_deref : Bool)
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=

  let offset1 := decodeOffset1 double_deref
  let offset2 := decodeOffset2 imm

  let _state := DecodeInstruction.call airBuilder lookupTerms
    (some (-1)) offset1 offset2 (CALL_FLAGS rel imm double_deref) casmState.pc
  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset1₁ := _state.2.2.2.1
  let offset2₁ := _state.2.2.2.2.1
  let flags := _state.2.2.2.2.2

  let flag_op0_base_fp := flags FLAG_OP0_BASE_FP_INDEX
  let flag_op1_base_fp := flags FLAG_OP1_BASE_FP_INDEX
  let flag_op1_base_ap := flags FLAG_OP1_BASE_AP_INDEX
  let flag_ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

  let _state := if imm = true then
      (ab1, lt1, casmState.pc)
      else (if double_deref = true then (
        let _state := ab1.assign (flag_op0_base_fp * casmState.fp + (FeltExpr.const 1 - flag_op0_base_fp) * casmState.ap)
        let _ab2 := _state.1
        let _mem0_base := _state.2
        Felt252IdMemory.read_address _ab2 lt1 (_mem0_base + offset1₁)
      ) else
        let _ab2 := ab1.constrain (flag_op1_base_fp + flag_op1_base_ap - FeltExpr.const 1)
        let _state := _ab2.assign (flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
        let _ab3 := _state.1
        let _mem1_base := _state.2
        (_ab3, lt1, _mem1_base)
  )
  let ab2 := _state.1
  let lt2 := _state.2.1
  let mem1_base := _state.2.2

  let _state := if rel = true then
      let _state := Felt252IdMemory.read_rel_imm ab2 lt2 (mem1_base + offset2₁)
      let _ab3 := _state.1
      let _lt3 := _state.2.1
      let _distance_to_next_pc := _state.2.2
      (_ab3, _lt3, casmState.pc + _distance_to_next_pc)
    else
      Felt252IdMemory.read_address ab2 lt2 (mem1_base + offset2₁)
  let ab3 := _state.1
  let lt3 := _state.2.1
  let next_pc := _state.2.2

  let next_ap := casmState.ap + flag_ap_update_add_1

  (ab3, lt3, ⟨next_pc, next_ap, casmState.fp⟩)

def mkJumpInstr (rel imm double_deref : Bool)
    (op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2 : Felt) : Instr :=
  let op0Off := if double_deref = true then (int_from_Felt offset1) else (-1)
  let op1Off := if imm = true then 1 else (int_from_Felt offset2)
  jumpInstr
    -- jump_abs
    (!rel)
    -- op0
    (if op0_base_fp = 1 then Op0Spec.fp_plus op0Off else Op0Spec.ap_plus op0Off)
    -- res
    (ResSpec.op1
      (if double_deref = true then
          (Op1Spec.mem_op0_plus op1Off)
        else (if imm then
            (Op1Spec.mem_pc_plus 1)
          else (if op1_base_fp = 1 then Op1Spec.mem_fp_plus op1Off else Op1Spec.mem_ap_plus op1Off))))
    -- ap_update
    (ap_update_add_1 = 1)

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (rel imm double_deref : Bool) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (some (-1)) (decodeOffset1 double_deref) (decodeOffset2 imm) (CALL_FLAGS rel imm double_deref)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ∃ mem1_base,
      (if imm = true then
          mem1_base = casmStateVal.pc
        else (if double_deref = true then
            Felt252IdMemory.read_address.spec
              memory
              (ρflags FLAG_OP0_BASE_FP_INDEX * casmStateVal.fp
                + (1 - ρflags FLAG_OP0_BASE_FP_INDEX) * casmStateVal.ap + (offset_as_signed_Felt ρoffset1))
              mem1_base
          else
            mem1_base = (ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp + ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap) ∧
            ρflags FLAG_OP1_BASE_FP_INDEX + ρflags FLAG_OP1_BASE_AP_INDEX - 1 = 0
        )) ∧
        ∃ (next_pc : CasmAddressVal),
          (if rel then
              ∃ distance_to_next_pc, Felt252IdMemory.read_rel_imm.spec memory (mem1_base + (offset_as_signed_Felt ρoffset2)) distance_to_next_pc ∧
                next_pc = casmStateVal.pc + distance_to_next_pc
            else
              Felt252IdMemory.read_address.spec memory (mem1_base + (offset_as_signed_Felt ρoffset2)) next_pc
          ) ∧
          ρCasmStateVal = ⟨next_pc, casmStateVal.ap + ρflags FLAG_AP_UPDATE_ADD_1_INDEX, casmStateVal.fp⟩

def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (rel imm double_deref : Bool)
    (num_steps: Nat) : Prop :=
    flag_assert rel imm double_deref →
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
      ρCasmStateVal.strongly_bounded (num_steps+1) ∧
        ∀ mem : Felt252 → Felt252,
          memory.Agrees mem →
            ∃ (op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2 : Felt),
              mem (casmStateVal.pc.toFelt252) =
                (mkJumpInstr rel imm double_deref op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction.toNat ∧
              (mkJumpInstr rel imm double_deref op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction.NextState mem
                casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252

theorem spec_of_spec_auto [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {rel imm double_deref : Bool}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal rel imm double_deref) :
    spec memory casmStateVal ρCasmStateVal rel imm double_deref num_steps := by
  intro h_flags_assert ns_lim cs_bound

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode,
    mem1_base, h_mem1_base, next_pc, h_next_pc, rfl⟩
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hflags
  rcases hverifyInstruction with ⟨instr, hinstr1, hinstr2⟩
  rcases hinstr1 with ⟨instr252, hinstr252a, hinstr252b⟩
  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a
  have pc_rc_tmp := pc_rc
  rcases pc_rc_tmp with ⟨pc_nat, h_pc_rc, h_pc_eq⟩
  have h_pc_lt : pc_nat < 2^30 -1 := by
    calc
      pc_nat < 2 ^ 29 := by
        exact h_pc_rc
      _ < 2 ^ 30 - 1 := by
        norm_num
  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩

  rw [hoffset0] at hinstr2
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr2
  dsimp [OFFSET_BITS] at hinstr2
  simp [decodeOffset1] at hoffset1
  simp [decodeOffset2] at hoffset2
  dsimp [CALL_FLAGS, Flags.to_arr] at hflags
  rw [hflags 0, hflags 2, hflags 5, hflags 6, hflags 7, hflags 8, hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr2
  simp only [Bool.toFelt_inj] at hinstr2
  rcases hinstr2 with ⟨h_offDst, h_offOp0, h_offOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX] ; rw [h_apAdd1]
    exact CasmStateVal.next_state_strongly_bound_of_apAdd1 cs_bound

  intro mem hmem
  rw [hmem.2 _ _ _ hinstr252a hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]

  use ρflags FLAG_OP0_BASE_FP_INDEX
  use ρflags FLAG_OP1_BASE_FP_INDEX
  use ρflags FLAG_AP_UPDATE_ADD_1_INDEX
  use ρoffset1, ρoffset2
  unfold FLAG_OP0_BASE_FP_INDEX FLAG_OP1_BASE_FP_INDEX FLAG_AP_UPDATE_ADD_1_INDEX
  constructor
  · -- The instruction is in memory at pc
    apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [mkJumpInstr, jumpInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←h_offDst]
    · simp only [←BitVec_toFelt_inj]
      by_cases h_dd : double_deref = true
      · by_cases h0 : ρflags 1 = 1 <;> simp [h0] <;> simp only [h_offOp0, if_pos h_dd] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      simp [if_neg h_dd] at hoffset1
      by_cases h1 : ρflags 1 = 1 <;> simp [h1, if_neg h_dd] <;> simp only [←h_offOp0] <;>
      rw [hoffset1] <;> simp [BitVec.as_u16, offset_as_u16, OFFSET_BITS]
    · simp only [←BitVec_toFelt_inj, ←h_offOp1]
      by_cases h_imm : imm = true
      · cases double_deref <;> simp only [if_pos h_imm] at hoffset2 <;>
        simp [if_pos h_imm, hoffset2] <;> simp [BitVec.as_u16, offset_as_u16, OFFSET_BITS]
      cases double_deref <;> simp [if_neg h_imm] <;>
      by_cases h3 : ρflags 3 = 1 <;>
      simp [h3, h_offOp1] <;> exact BitVec_u16_eq_from_Felt_to_u16
    -- The flags
    · simp [←h_dstReg]
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : ρflags 1 = 1 <;> simp [h0]
      · simp only [←h_op0Reg, h0]
        simp [Bool.toFelt]
      simp only [h_op0Reg] at h0
      exact Bool.false_toFelt_eq h0
    · simp only [←Bool.toFelt_inj, ←h_op1Imm]
      by_cases h0 : ρflags 3 = 1 <;> simp [h0] <;>
      unfold flag_assert at h_flags_assert <;> revert h_flags_assert <;>
      cases double_deref <;> cases imm <;>
      simp [Bool.false_toFelt_ne_true_toFelt]
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : ρflags 3 = 1 <;> simp [h0, ←h_op1Fp]
      · cases double_deref <;> cases imm <;>
        simp [Bool.toFelt] <;>
        have hflag3 := hflags 3 <;> simp [Fin.coe_ofNat_eq_mod] at hflag3 <;>
        simp [h0, Bool.toFelt] at hflag3
      cases double_deref <;> cases imm <;>
      simp only [h_op1Fp] at h0 <;> simp only [h_op1Fp] <;>
      simp [Bool.false_toFelt_ne_true_toFelt, Bool.false_toFelt_eq h0]
    · simp only [←Bool.toFelt_inj]
      by_cases h0 : double_deref = false ∧ imm = false
      · simp [h0.1, h0.2, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at h_mem1_base
        have h_cflags := h_mem1_base.2
        simp only [←h_op1Ap]
        simp [h0.1, h0.2, Bool.toFelt]
        by_cases h0 : ρflags 3 = 1 <;> simp [h0]
        · simp [h0] at h_cflags ; exact h_cflags
        rw [h_op1Fp, Bool.toFelt_ne_one_iff_eq_zero, ←h_op1Fp] at h0
        simp only [h0, zero_add, sub_eq_zero] at h_cflags
        exact h_cflags
      simp only [Decidable.not_and_iff_or_not, Bool.not_eq_false, or_comm] at h0
      simp [h0] at hflags
      have hflag3 := hflags 3 ; simp [Fin.coe_ofNat_eq_mod] at hflag3
      have hflag4 := hflags 4 ; simp [Fin.coe_ofNat_eq_mod] at hflag4
      simp only [hflag4, Bool.toFelt_inj] at h_op1Ap
      simp [hflag3, ←h_op1Ap, Bool.toFelt]
      revert h0
      cases double_deref <;> cases imm <;> simp
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
  apply nextState_jump _ _ _ _ _ _ _|>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]

  constructor
  · -- The pc is advanced correctly
    cases rel
    · simp at h_next_pc
      rcases h_next_pc with ⟨next_pc252, h_num_bits, hnext_pc252, h_nextpc_as_m31⟩
      simp only [h_nextpc_as_m31]
      rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked hnext_pc252 hmem with ⟨value_n, hpc1, hpc2⟩
      have offset_rc := memory.IsRangeChecked_address_of_HasValue memChecked hnext_pc252
      simp [felt252_to_m31_eq next_pc252 value_n h_num_bits hpc1, ←hpc2, h_offOp1]
      rw [h_offOp1] at offset_rc
      rw [toFelt252_add_offset_RangeChecked_eq offset_rc]
      cases double_deref
      · cases imm <;> simp <;>
        simp [FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at h_mem1_base
        rw [h_mem1_base.1]
        · have h_cflags := h_mem1_base.2
          by_cases h3 : ρflags 3 = 1 <;> simp [h3]
          · simp [h3] at h_cflags
            simp [h_cflags]
          rw [h_op1Fp, Bool.toFelt_ne_one_iff_eq_zero, ←h_op1Fp] at h3
          simp only [h3, zero_add, sub_eq_zero] at h_cflags
          simp [h3, h_cflags]
        rw [h_mem1_base, ←h_offOp1]
        rw [show (1 : Int) = (int_from_Felt ρoffset2) by rw [hoffset2] ; rw [←BitVec_toInt_eq_from_Felt_as_u16] ; simp]
      cases imm
      · simp [FLAG_OP0_BASE_FP_INDEX] at h_mem1_base
        rcases h_mem1_base with ⟨mem1_base_252, h_num_bits, h_mem1_base_252, h_mem1_base_as_m31⟩
        rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked h_mem1_base_252 hmem with ⟨value_n, h_mem1_base1, h_mem1_base2⟩
        rw [h_offOp0] at h_mem1_base_252 h_mem1_base2
        rw [toFelt252_add_offset_RangeChecked_eq (memory.IsRangeChecked_address_of_HasValue memChecked h_mem1_base_252)] at h_mem1_base2
        rw [←felt252_to_m31_eq mem1_base_252 value_n h_num_bits h_mem1_base1] at h_mem1_base2
        simp only [h_mem1_base_as_m31]
        by_cases h1 : ρflags 1 = 1 <;> simp [h1, h_offOp0]
        · simp [h1] at h_mem1_base2
          rw [h_mem1_base2]
        rw [h_op0Reg, Bool.toFelt_ne_one_iff_eq_zero, ←h_op0Reg] at h1
        simp [h1] at h_mem1_base2
        rw [h_mem1_base2]
      simp [flag_assert] at h_flags_assert -- is false
    -- relative jump
    cases double_deref
    · simp at h_next_pc
      rcases h_next_pc with ⟨next_pc252, h_next_pc252, h_nextpc_as_m31⟩
      simp only [h_nextpc_as_m31]
      cases imm <;> simp
      · simp [FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at h_mem1_base
        have h_cflags := h_mem1_base.2
        by_cases h3 : ρflags 3 = 1 <;> simp [h3]
        · simp [h3] at h_cflags
          simp [h3, h_cflags] at h_mem1_base
          rw [h_mem1_base] at h_next_pc252
          rcases h_next_pc252 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
          have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.fp + offset_as_signed_Felt ρoffset2) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
            use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
          rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩
          rw [h_offOp1] ; rw [h_offOp1] at h_hasValue
          rw [←toFelt252_add_offset_RangeChecked_eq (memory.IsRangeChecked_address_of_HasValue memChecked h_hasValue)]
          rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
          exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2
        rw [h_op1Fp, Bool.toFelt_ne_one_iff_eq_zero, ←h_op1Fp] at h3
        simp only [h3, zero_add, sub_eq_zero] at h_cflags
        simp [h3, h_cflags] at h_mem1_base
        -- From here, it is almost the same proof as in the previous cases
        rw [h_mem1_base] at h_next_pc252
        rcases h_next_pc252 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
        have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.ap + offset_as_signed_Felt ρoffset2) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
          use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
        rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩
        rw [h_offOp1] ; rw [h_offOp1] at h_hasValue
        rw [←toFelt252_add_offset_RangeChecked_eq (memory.IsRangeChecked_address_of_HasValue memChecked h_hasValue)]
        rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
        exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2
      simp at h_mem1_base
      rw [hoffset2, h_mem1_base] at h_next_pc252
      rcases h_next_pc252 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
      have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.pc + 1) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs ) := by
        use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
      rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩
      have h_intClip_1 : (1 : Felt252) = intClip 1 := by unfold intClip natClip ; simp ; norm_num
      rw [←h_intClip_1, ←toFelt252_add_one_of_RangeChecked pc_rc]
      rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
      exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2
    simp [flag_assert] at h_flags_assert -- is false
  constructor
  · -- The ap is advanced correctly
    simp only [h_apAdd1]
    cases instr.apAdd1 <;> simp [Bool.toFelt]
    rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, -⟩
    have : ap_nat < 2 ^ 29 + num_steps + 2 := by
        linarith
    exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat this
  rfl

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
    (num_steps: Nat)
    (rel imm double_deref : Bool) :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call rel imm double_deref ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) rel imm double_deref num_steps := by
  unfold call DecodeInstruction.call ; lift_lets
  intro offset1 offset2
    state1 ab1 lt1 offset1₁ offset2₁ flags
    flag_op0_base_fp flag_op1_base_fp flag_op1_base_ap flag_ap_update_add_1
    state2₀ ab2₀ mem0_base
    ab2₁
    state3₀ ab3₀ mem1_base₀
    state2 ab2 lt2 mem1_base
    state3₁ ab3₁ lt3₁ distance_to_next_pc
    state3 ab3 lt3 next_pc next_ap

  intro hab3 hlt3
  cases rel
  · have ⟨hab2, hlt2, hread_address2⟩ := Felt252IdMemory.read_address.sound_auto
      varAssign memAssign ab2 lt2 _ h_rc h_mem.1 (mem1_base + offset2₁) hab3 hlt3
    cases imm
    · cases double_deref
      · have ⟨hab2₁, h_mem1_base⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2
        have ⟨hab1, h_flags⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2₁
        have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
          ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS False False False) casmState.pc hab1 hlt2
        use hab, hlt
        apply spec_of_spec_auto
        use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
        use ?_, ?_, ?_, ?_
        constructor
        . exact h_decode
        use FeltExpr.eval varAssign (flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
        constructor
        · simp
          constructor
          · rfl
          exact h_flags
        use FeltExpr.eval varAssign next_pc
        simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
        constructor
        · rw [←h_mem1_base]
          exact hread_address2
        simp ; rfl
      have ⟨hab2₁, hlt1, hmem, hread_address⟩ := Felt252IdMemory.read_address.sound_auto
        varAssign memAssign ab2₀ _ _ h_rc h_mem.1 (mem0_base + offset1₁) hab2 hlt2
      have ⟨hab1, h_mem0_base⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2₁
      have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
        ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS False False True) casmState.pc hab1 hlt1
      use hab, hlt
      apply spec_of_spec_auto
      use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
      use ?_, ?_, ?_, ?_
      constructor
      . exact h_decode
      use (FeltExpr.eval varAssign mem1_base)
      simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
      constructor
      · use ?_
        unfold offset1₁ mem0_base state2₀ at hread_address
        simp only [FeltExpr.eval_add, h_mem0_base] at hread_address
        exact hread_address
      use FeltExpr.eval varAssign next_pc
      --simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
      constructor
      · exact hread_address2
      simp ; rfl
    cases double_deref
    · have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
        ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS False True False) casmState.pc hab2 hlt2
      use hab, hlt
      apply spec_of_spec_auto
      use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
      use ?_, ?_, ?_, ?_
      constructor
      . exact h_decode
      use (CasmState.eval varAssign casmState).pc
      simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
      use trivial
      use FeltExpr.eval varAssign next_pc
      constructor
      · exact hread_address2
      rfl
    have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS False True True) casmState.pc hab2 hlt2
    use hab, hlt
    apply spec_of_spec_auto
    use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
    use ?_, ?_, ?_, ?_
    constructor
    . exact h_decode
    use (CasmState.eval varAssign casmState).pc
    simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
    use trivial
    use FeltExpr.eval varAssign next_pc
    constructor
    · exact hread_address2
    rfl
  have ⟨hab2, hlt2, hread_rel_imm⟩ := Felt252IdMemory.read_rel_imm.sound_auto
    varAssign memAssign ab2 lt2 _ h_mem.1 (mem1_base + offset2₁) hab3 hlt3
  cases imm
  · cases double_deref
    · have ⟨hab2₁, h_mem1_base⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2
      have ⟨hab1, h_flags⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2₁
      have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
        ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS True False False) casmState.pc hab1 hlt2
      use hab, hlt
      apply spec_of_spec_auto
      use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
      use ?_, ?_, ?_, ?_
      constructor
      . exact h_decode
      use FeltExpr.eval varAssign (flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
      constructor
      · simp
        constructor
        · rfl
        exact h_flags
      use FeltExpr.eval varAssign next_pc
      simp only [↓reduceIte, offset_as_signed_Felt_as_offset]
      constructor
      · use FeltExpr.eval varAssign distance_to_next_pc
        constructor
        · rw [←h_mem1_base]
          exact hread_rel_imm
        rfl
      simp ; rfl
    have ⟨hab2₁, hlt1, hread_address⟩ := Felt252IdMemory.read_address.sound_auto
      varAssign memAssign ab2₀ _ _ h_rc h_mem.1 (mem0_base + offset1₁) hab2 hlt2
    have ⟨hab1, h_mem0_base⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab2₁
    have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS True False True) casmState.pc hab1 hlt1
    use hab, hlt
    apply spec_of_spec_auto
    use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
    use ?_, ?_, ?_, ?_
    constructor
    . exact h_decode
    use (FeltExpr.eval varAssign mem1_base)
    simp only [Bool.false_eq_true, ↓reduceIte, offset_as_signed_Felt_as_offset]
    constructor
    · unfold offset1₁ mem0_base state2₀ at hread_address
      simp only [FeltExpr.eval_add, h_mem0_base] at hread_address
      exact hread_address
    use FeltExpr.eval varAssign next_pc
    constructor
    · use FeltExpr.eval varAssign distance_to_next_pc
      constructor
      · exact hread_rel_imm
      rfl
    simp ; rfl
  cases double_deref
  · have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS True True False) casmState.pc hab2 hlt2
    use hab, hlt
    apply spec_of_spec_auto
    use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
    use ?_, ?_, ?_, ?_
    constructor
    . exact h_decode
    use (CasmState.eval varAssign casmState).pc
    simp only [↓reduceIte, offset_as_signed_Felt_as_offset]
    use trivial
    use FeltExpr.eval varAssign next_pc
    constructor
    · use FeltExpr.eval varAssign distance_to_next_pc
      constructor
      · exact hread_rel_imm
      rfl
    rfl
  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab lt _ h_rc h_mem h_verify_instr (some (-1)) offset1 offset2 (CALL_FLAGS True True True) casmState.pc hab2 hlt2
  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_
  constructor
  . exact h_decode
  use (CasmState.eval varAssign casmState).pc
  simp only [↓reduceIte, offset_as_signed_Felt_as_offset]
  use trivial
  use FeltExpr.eval varAssign next_pc
  constructor
  · use FeltExpr.eval varAssign distance_to_next_pc
    constructor
    · exact hread_rel_imm
    rfl
  rfl

theorem sound_jump_imm [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call true true false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ num_steps true true false
      h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : flag_assert true true false := by simp [flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨op0_base_fp, op1_base_fp, ap_update_add_1, offset1, offset2, h_instr, h_next⟩
  use (mkJumpInstr true true false
        op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction
  use h_instr

theorem sound_jump_double_deref [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call false false true ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ num_steps false false true
      h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : flag_assert false false true := by simp [flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨op0_base_fp, op1_base_fp, ap_update_add_1, offset1, offset2, h_instr, h_next⟩
  use (mkJumpInstr false false true
        op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction
  use h_instr

theorem sound_jump_rel [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call true false false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ num_steps true false false
      h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : flag_assert true false false := by simp [flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨op0_base_fp, op1_base_fp, ap_update_add_1, offset1, offset2, h_instr, h_next⟩
  use (mkJumpInstr true false false
        op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction
  use h_instr

theorem sound_jump_abs [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call false false false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ num_steps false false false
      h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : flag_assert false false false := by simp [flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨op0_base_fp, op1_base_fp, ap_update_add_1, offset1, offset2, h_instr, h_next⟩
  use (mkJumpInstr false false false
        op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction
  use h_instr

end JumpOpcode
