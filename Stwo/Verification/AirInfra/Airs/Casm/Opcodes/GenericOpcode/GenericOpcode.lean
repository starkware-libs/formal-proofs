import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.DecodeGenericInst
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.EvalOperands
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.HandleOpcodes
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.UpdateRegisters

open Fin.NatCast

namespace GenericOpcode


@[irreducible]
def call [Fact (Nat.Prime Stwo.P)]
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=
  let _state := DecodeGenericInstruction.call airBuilder lookupTerms casmState.pc
  let ab1 := _state.1
  let lt1 := _state.2.1
  let flags := _state.2.2.1
  let offset0 := _state.2.2.2.1
  let offset1 := _state.2.2.2.2.1
  let offset2 := _state.2.2.2.2.2
  let _state := EvalOperands.call ab1 lt1 casmState flags offset0 offset1 offset2
  let ab2 := _state.1
  let lt2 := _state.2.1
  let dst := _state.2.2.1
  let op0 := _state.2.2.2.1
  let op1 := _state.2.2.2.2.1
  let res := _state.2.2.2.2.2
  let ab3 := HandleOpcodes.call ab2 casmState flags offset0 offset1 offset2 dst op0 res
  let _state := UpdateRegisters.call ab3 lt2 casmState flags dst op1 res
  let ab4 := _state.1
  let lt3 := _state.2.1
  let ρcasmState := _state.2.2
  (ab4, lt3, ρcasmState)

def spec_auto [Fact (Nat.Prime Stwo.P)]
    (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρcasmStateVal : CasmStateVal)
    (num_steps: Nat) : Prop :=
  memAssign.IsRangeChecked ∧
  ∃ offset0 offset1 offset2 flags,
    DecodeGenericInstruction.spec memAssign casmStateVal.pc
      (signed_as_offset_Felt offset0) (signed_as_offset_Felt offset1) (signed_as_offset_Felt offset2) flags ∧
    ∃ dst op0 op1 res, EvalOperands.spec memAssign casmStateVal offset0 offset1 offset2 flags dst op0 op1 res ∧
      HandleOpcodes.spec casmStateVal flags offset0 offset1 offset2 dst op0 res ∧
      UpdateRegisters.spec casmStateVal flags dst op1 res ρcasmStateVal num_steps

def spec [Fact (Nat.Prime Stwo.P)]
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat) : Prop :=
  num_steps < 2^29 → casmStateVal.strongly_bounded₀ num_steps →
  (ρCasmStateVal.strongly_bounded (num_steps+1)
    ∧ (∀ mem : Felt252 → Felt252,
        memory.Agrees mem →
          ∃ instruction : Instruction,
            mem (casmStateVal.pc.toFelt252) = instruction.toNat
            ∧ instruction.NextState mem
              casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))

-- YS: Move the following lemmas to Common.lean

lemma eq_toBiased16_of_signed_as_offset_Felt {x : Felt} {y : BitVec 16} (h : signed_as_offset_Felt x = ↑y.toNat) :
    x = y.toBiased16 := by
  unfold BitVec.toBiased16
  unfold signed_as_offset_Felt at h
  rw [←eq_sub_iff_add_eq] at h
  rw [h] ; rw [Int.cast_sub]
  rfl

lemma offset_as_signed_Felt_of_signed_as_offset_Felt
      {x : Felt} {y : BitVec 16} (h : signed_as_offset_Felt x = ↑y.toNat) :
    x = offset_as_signed_Felt ↑y.toNat := by
  unfold offset_as_signed_Felt
  unfold signed_as_offset_Felt at h
  rw [←eq_sub_iff_add_eq] at h
  exact h

lemma offset_as_signed_Felt_eq_toBias16 {y : BitVec 16} : offset_as_signed_Felt ↑y.toNat = y.toBiased16 := by
  unfold offset_as_signed_Felt BitVec.toBiased16 OFFSET_BITS
  norm_num ; rfl

lemma toBiased16_eq_intClip_int_from_Felt [Fact (Nat.Prime Felt252Prime)] (x : BitVec 16) :
    (x.toBiased16 : Felt252) = intClip (int_from_Felt x.toNat)  := by
  unfold BitVec.toBiased16 intClip natClip int_from_Felt int_from_u16 OFFSET_BITS
  simp ; norm_num1 ; congr
  rw [ZMod.cast_eq_val, Int.toNat_natCast, ZMod.val_cast_of_lt, Nat.mod_eq_of_lt]
  apply (BitVec.isLt x)
  unfold Stwo.P ; apply lt_trans (BitVec.isLt x) ; norm_num1

lemma mem_at_addr_eq_eval_of_HasValue [Fact (Nat.Prime Felt252Prime)]
      {x : Felt}
      {y : BitVec 16}
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      {value : Felt252Words}
      {offset : Felt}
      (memChecked : memAssign.IsRangeChecked)
      (hmem : memAssign.Agrees mem)
      (h_offset : signed_as_offset_Felt offset = ↑y.toNat)
      (h_value : memAssign.HasValue (x + offset) value) :
    mem (x.toFelt252 + ↑y.toBiased16) = value.eval := by
  rw [toBiased16_eq_intClip_int_from_Felt]
  have h_rc := memAssign.IsRangeChecked_address_of_HasValue memChecked h_value
  rw [offset_as_signed_Felt_of_signed_as_offset_Felt h_offset] at h_rc
  rw [←toFelt252_add_offset_RangeChecked_eq h_rc]
  rw [←offset_as_signed_Felt_of_signed_as_offset_Felt h_offset]
  rcases memAssign.isRangeChecked_of_hasValue_of_agrees memChecked h_value hmem with ⟨value_n, h_value_rc, h_value_n⟩
  rw [h_value_n, ←Felt252Nats.eval_Felt252Words_eq h_value_rc]

lemma mem_eq_of_HasValue [Fact (Nat.Prime Felt252Prime)]
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      {x : Felt}
      {y : BitVec 16}
      {value : Felt252Words}
      (memChecked : memAssign.IsRangeChecked)
      (hmem : memAssign.Agrees mem)
      (h_HasValue : memAssign.HasValue (x + ↑y.toBiased16) value) :
    mem (x.toFelt252 + ↑y.toBiased16) = value.eval := by
  apply mem_at_addr_eq_eval_of_HasValue memChecked hmem _ h_HasValue
  simp [signed_as_offset_Felt, BitVec.toBiased16, OFFSET_BITS]

lemma cast_aux : 15 ≤ GENERIC_FLAGS_SIZE := by unfold GENERIC_FLAGS_SIZE ; norm_num

lemma op0_eq [Fact (Nat.Prime Felt252Prime)]
      {i : Instruction}
      {s : CasmStateVal}
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      (memChecked : memAssign.IsRangeChecked)
      (hmem : memAssign.Agrees mem)
      (op0 : Felt252Words)
      (h_op0Reg : flags (Fin.castLE cast_aux 1) = i.op0Reg.toFelt)
      (h_op0_spec : EvalOperands.op0_spec memAssign s i.offOp0.toBiased16 flags op0) :
    i.op0 mem { pc := s.pc.toFelt252, ap := s.ap.toFelt252, fp := s.fp.toFelt252 } = op0.eval := by
  unfold Instruction.op0
  unfold EvalOperands.op0_spec at h_op0_spec
  simp [FLAG_OP0_BASE_FP_INDEX, h_op0Reg] at h_op0_spec
  revert h_op0_spec
  cases i.op0Reg
  all_goals {
    simp [Bool.toFelt] ; intro h_op0_spec _
    exact mem_eq_of_HasValue memChecked hmem h_op0_spec
  }

lemma op1_eq [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
      {i : Instruction}
      {s : CasmStateVal}
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      (memChecked : memAssign.IsRangeChecked)
      (hmem : memAssign.Agrees mem)
      (h_atMostOne_op1 : DecodeGenericInstruction.atMostOneTrue3 i.op1Imm i.op1Fp i.op1Ap)
      (h_op1_base_op0_eq : flags FLAG_OP1_BASE_OP0_INDEX = (!(i.op1Imm || i.op1Fp || i.op1Ap)).toFelt)
      (h_op0Reg : flags (Fin.castLE cast_aux 1) = i.op0Reg.toFelt)
      (h_op1Imm : flags (Fin.castLE cast_aux 2) = i.op1Imm.toFelt)
      (h_op1Fp : flags (Fin.castLE cast_aux 3) = i.op1Fp.toFelt)
      (h_op1Ap : flags (Fin.castLE cast_aux 4) = i.op1Ap.toFelt)
      (op0 op1 : Felt252Words)
      (h_op0_spec : EvalOperands.op0_spec memAssign s i.offOp0.toBiased16 flags op0)
      (h_op1_spec : EvalOperands.op1_spec memAssign s i.offOp1.toBiased16 flags op0 op1) :
    i.op1 mem { pc := s.pc.toFelt252, ap := s.ap.toFelt252, fp := s.fp.toFelt252 } = some op1.eval := by
  unfold Instruction.op1
  unfold EvalOperands.op1_spec at h_op1_spec
  simp [FLAG_OP1_IMM_INDEX, h_op1Imm, FLAG_OP1_BASE_FP_INDEX, h_op1Fp, FLAG_OP1_BASE_AP_INDEX, h_op1Ap] at h_op1_spec
  revert h_atMostOne_op1 h_op1_base_op0_eq h_op1_spec
  cases i.op1Imm
  · cases i.op1Fp
    · cases i.op1Ap
      · simp [Bool.toFelt] ; intro _ h_op1_base_op0_eq h_op1_spec
        rw [op0_eq memChecked hmem op0 h_op0Reg h_op0_spec]
        have h_op1_base_op0_ne : flags FLAG_OP1_BASE_OP0_INDEX ≠ 0 := by simp [h_op1_base_op0_eq]
        rw [←h_op0_spec.2 h_op1_base_op0_ne]
        rw [mem_eq_of_HasValue memChecked hmem h_op1_spec]
      simp [Bool.toFelt] ; intro _ _ h_op1_spec
      exact mem_eq_of_HasValue memChecked hmem h_op1_spec
    intro h_atMostOne_op1
    simp [DecodeGenericInstruction.atMostOneTrue3] at h_atMostOne_op1
    simp [h_atMostOne_op1, Bool.toFelt]
    intro _ h_op1_spec
    exact mem_eq_of_HasValue memChecked hmem h_op1_spec
  intro h_atMostOne_op1
  simp [DecodeGenericInstruction.atMostOneTrue3] at h_atMostOne_op1
  simp [h_atMostOne_op1, Bool.toFelt]
  intro _ h_op1_spec
  exact mem_eq_of_HasValue memChecked hmem h_op1_spec

lemma resAux_eq [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
      {i : Instruction}
      {casmStateVal : CasmStateVal}
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      {op0 op1 res : Felt252Words}
      (memChecked : memAssign.IsRangeChecked)
      (hmem : memAssign.Agrees mem)
      (h_atMostOne_op1 : DecodeGenericInstruction.atMostOneTrue3 i.op1Imm i.op1Fp i.op1Ap)
      (h_op1_base_op0_eq : flags FLAG_OP1_BASE_OP0_INDEX = (!(i.op1Imm || i.op1Fp || i.op1Ap)).toFelt)
      (h_atMostOne_res : DecodeGenericInstruction.atMostOneTrue3 i.resAdd i.resMul i.pcJnz)
      (h_res_op1_flag : flags FLAG_RES_OP1_INDEX = (!(i.resAdd || i.resMul || i.pcJnz)).toFelt)
      (h_op0Reg : flags (Fin.castLE cast_aux 1) = i.op0Reg.toFelt)
      (h_op1Imm : flags (Fin.castLE cast_aux 2) = i.op1Imm.toFelt)
      (h_op1Fp : flags (Fin.castLE cast_aux 3) = i.op1Fp.toFelt)
      (h_op1Ap : flags (Fin.castLE cast_aux 4) = i.op1Ap.toFelt)
      (h_resAdd : flags (Fin.castLE cast_aux 5) = i.resAdd.toFelt)
      (h_resMul : flags (Fin.castLE cast_aux 6) = i.resMul.toFelt)
      (h_op0_rc : Felt252Nats.ExistsIsRangeChecked op0)
      (h_op1_rc : Felt252Nats.ExistsIsRangeChecked op1)
      (h_res_rc : Felt252Nats.ExistsIsRangeChecked res)
      (h_op0_spec : EvalOperands.op0_spec memAssign casmStateVal i.offOp0.toBiased16 flags op0)
      (h_op1_spec : EvalOperands.op1_spec memAssign casmStateVal i.offOp1.toBiased16 flags op0 op1)
      (h_res_spec : EvalOperands.res_spec flags op0 op1 res) :
    i.resAux mem casmStateVal.toRegisterStateFelt252 = some res.eval := by
  rcases h_op0_rc with ⟨n_op0, h_n_op0⟩
  rcases h_op1_rc with ⟨n_op1, h_n_op1⟩
  rcases h_res_rc with ⟨n_res, h_n_res⟩
  unfold Instruction.resAux
  unfold DecodeGenericInstruction.atMostOneTrue3 at h_atMostOne_res
  unfold EvalOperands.res_spec at h_res_spec
  dsimp at h_res_spec
  simp only [h_res_op1_flag, FLAG_RES_ADD_INDEX, h_resAdd, FLAG_RES_MUL_INDEX, h_resMul] at h_res_spec
  simp [CasmStateVal.toRegisterStateFelt252]
  revert h_atMostOne_res h_res_spec
  cases i.resAdd
  · cases i.resMul
    · intro _ h_res_spec
      simp [
        op1_eq memChecked hmem h_atMostOne_op1 h_op1_base_op0_eq h_op0Reg h_op1Imm h_op1Fp h_op1Ap op0 op1 h_op0_spec h_op1_spec]
      simp [Bool.toFelt] at h_res_spec
      rw [←h_res_spec]
      --exact h_res_eval.symm
    intro h1 ; simp at h1 ; simp [h1, Bool.toFelt]
    intro h_res_spec
    simp [
      op1_eq memChecked hmem h_atMostOne_op1 h_op1_base_op0_eq h_op0Reg h_op1Imm h_op1Fp h_op1Ap op0 op1 h_op0_spec h_op1_spec,
      op0_eq memChecked hmem op0 h_op0Reg h_op0_spec]
    rw [Felt252Nats.eval_Felt252Words_eq h_n_op0, Felt252Nats.eval_Felt252Words_eq h_n_op1,
      Felt252Nats.eval_Felt252Words_eq h_n_res]
    apply h_res_spec.2 _ _ _ h_n_op0 h_n_op1 h_n_res
  intro h1 ; simp at h1 ; simp [h1.1, Bool.toFelt]
  intro h_res_spec
  simp [
    op1_eq memChecked hmem h_atMostOne_op1 h_op1_base_op0_eq h_op0Reg h_op1Imm h_op1Fp h_op1Ap op0 op1 h_op0_spec h_op1_spec,
    op0_eq memChecked hmem op0 h_op0Reg h_op0_spec]
  rw [Felt252Nats.eval_Felt252Words_eq h_n_op0, Felt252Nats.eval_Felt252Words_eq h_n_op1,
    Felt252Nats.eval_Felt252Words_eq h_n_res]
  apply h_res_spec.2 _ _ _ h_n_op0 h_n_op1 h_n_res

lemma toFelt_true : true.toFelt = 1 := rfl
lemma toFelt_false : false.toFelt = 0 := rfl

-- TODO(Jeremy): debug this
-- It has to do with match statements 0, 0, 0 => ..., 1, 0, x => ..., etc.
set_option maxHeartbeats 600000 in
theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρcasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h_spec_auto : spec_auto memory casmStateVal ρcasmStateVal num_steps) :
    spec memory casmStateVal ρcasmStateVal num_steps := by
  intro ns_lim cs_bound₀
  have cs_bound := (CasmStateVal.strongly_bounded_of_strongly_bounded₀ cs_bound₀)
  have := cs_bound
  rcases this with ⟨⟨ap_nat, ap_bound, h_ap_nat⟩, ⟨fp_nat, fp_bound, h_fp_nat⟩⟩
  rcases cs_bound₀ with ⟨⟨ap_nat₀, ap_bound₀, h_ap_nat₀⟩, _⟩

  rcases h_spec_auto with ⟨memChecked, offset0, offset1, offset2, flags, h_decode,
    dst, op0, op1, res, h_operands, h_opcodes, h_registers⟩
  rcases h_decode with ⟨instruction, h_instr,
    h_offDst, h_offOp0, h_offOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq,
    h_op1_base_op0_atMost, h_op1_base_op0_eq, h_res_op1_atMost, h_res_op1_eq, h_pc_update_regular_atMost,
    h_pc_update_regular_eq, h_ap_update_regular, h_fp_update_regular_atMost, h_fp_update_regular_eq, h_instr_size⟩
  rcases h_operands with ⟨h_dst, h_op0, h_op1_1, h_op1_2, h_res⟩
  rcases h_opcodes with ⟨h_ret, h_call, h_assert⟩
  unfold UpdateRegisters.spec at h_registers
  rcases h_registers ns_lim cs_bound with ⟨h_next_pc, h_next_ap, h_next_ap_rc, h_res_as_addr, h_next_fp, h_next_fp'⟩
  rcases h_instr with ⟨instr252, h_instr_hasValue, h_instr_encode⟩
  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked h_instr_hasValue
  rcases memory.IsRangeChecked_of_HasValue memChecked h_instr_hasValue with ⟨instr252_n, h_instr252_n⟩

  have h_op0_rc := EvalOperands.op0_IsRangeChecked_of_spec memChecked h_op0
  have h_op1_rc := EvalOperands.op1_IsRangeChecked_of_spec memChecked h_op1_2
  have h_dst_rc := EvalOperands.dst_IsRangeChecked_of_spec memChecked h_dst

  rw [eq_toBiased16_of_signed_as_offset_Felt h_offOp0] at h_op0
  rw [eq_toBiased16_of_signed_as_offset_Felt h_offOp1] at h_op1_2

  constructor
  · -- strongly bound output state
    unfold CasmStateVal.strongly_bounded
    constructor
    · rcases h_next_ap_rc with ⟨next_ap_n, h_next_ap_lt, h_next_ap_eq⟩
      use next_ap_n
      constructor
      · omega
      · exact h_next_ap_eq
    · rcases h_next_fp' with ⟨next_fp_felt, h_cond_spec, h_next_fp_eq⟩
      by_cases h_fp_update_ret_val : flags (Fin.castLE UpdateRegisters.call._proof_1 FLAG_OPCODE_RET_INDEX) = 1
      · simp[h_fp_update_ret_val] at h_cond_spec
        simp[h_fp_update_ret_val] at h_next_fp_eq
        unfold CondFelt252AsAddr.spec at h_cond_spec
        simp at h_cond_spec
        have htmp := (h_cond_spec.2.1) h_dst_rc
        rw[h_cond_spec.1] at htmp -- ?

        have h_inst_fp_update_regular_true : instruction.opcodeRet = true := by
          unfold FLAG_OPCODE_RET_INDEX at h_fp_update_ret_val
          simp at h_opcodeRet
          rw [h_fp_update_ret_val] at h_opcodeRet
          by_contra h_contra
          push_neg at h_contra
          have : instruction.opcodeRet = false := by simp [h_contra]
          rw [this] at h_opcodeRet
          simp [Bool.toFelt] at h_opcodeRet

        have h_fp_update_regular_flag_val_0: flags FLAG_FP_UPDATE_REGULAR_INDEX = 0 := by
          rw [h_fp_update_regular_eq]
          rw[h_inst_fp_update_regular_true]
          simp[Bool.toFelt]

        rw[h_fp_update_regular_flag_val_0] at h_next_fp_eq
        simp at h_next_fp_eq
        unfold DecodeGenericInstruction.atMostOneTrue at h_fp_update_regular_atMost
        rw[h_inst_fp_update_regular_true] at h_fp_update_regular_atMost
        simp at h_fp_update_regular_atMost
        have h_call_flag_val_0: flags (Fin.castLE UpdateRegisters.call._proof_1 FLAG_OPCODE_CALL_INDEX) = 0 := by
          unfold FLAG_OPCODE_CALL_INDEX
          simp at h_opcodeCall
          rw [h_opcodeCall]
          rw[h_fp_update_regular_atMost]
          simp[Bool.toFelt]
        rw[h_call_flag_val_0] at h_next_fp_eq
        simp at h_next_fp_eq

        use next_fp_felt.val
        constructor
        · rw[h_cond_spec.1]
          have htmp2 := h_dst_rc
          unfold Felt252Nats.ExistsIsRangeChecked at htmp2
          rcases htmp2 with ⟨dstn, h_dstn_rc⟩
          have := h_dstn_rc 3
          have : dstn 3 = ZMod.val (dst 3):= by
            rw[this.1]
            symm
            apply ZMod.val_natCast_of_lt
            unfold Stwo.P
            omega
          have htmp3 := h_cond_spec.2.2
          rw[← this] at htmp3
          rcases felt252_to_m31_val_isRangeChecked_specific h_dstn_rc htmp3 with ⟨dstn', h_dstn'_lt, h_dstn'_eq⟩
          rw[h_dstn'_eq]
          rw[ZMod.val_natCast_of_lt]
          omega
          unfold Stwo.P
          omega
        · rw[h_next_fp_eq]
          symm
          exact ZMod.natCast_zmod_val next_fp_felt

      have h_inst_ret_false : instruction.opcodeRet = false := by
        unfold FLAG_OPCODE_RET_INDEX at h_fp_update_ret_val
        simp at h_opcodeRet
        by_contra h_contra
        push_neg at h_contra
        have : instruction.opcodeRet = true := by simp [h_contra]
        rw [this] at h_opcodeRet
        simp [Bool.toFelt] at h_opcodeRet
        rw [h_opcodeRet] at h_fp_update_ret_val
        absurd h_fp_update_ret_val
        rfl
      have h_ret_flag_val_0: flags (Fin.castLE UpdateRegisters.call._proof_1 FLAG_OPCODE_RET_INDEX) = 0 := by
        simp at h_opcodeRet
        unfold FLAG_OPCODE_RET_INDEX
        rw[h_opcodeRet]
        rw [h_inst_ret_false]
        simp[Bool.toFelt]

      · by_cases h_call_flag_val : flags (Fin.castLE UpdateRegisters.call._proof_1 FLAG_OPCODE_CALL_INDEX) = 1
        · simp[h_call_flag_val] at h_next_fp_eq
          have h_call_flag_true : instruction.opcodeCall = true := by
            unfold FLAG_OPCODE_CALL_INDEX at h_call_flag_val
            simp at h_opcodeCall
            rw [h_call_flag_val] at h_opcodeCall
            by_contra h_contra
            push_neg at h_contra
            have : instruction.opcodeCall = false := by simp [h_contra]
            rw [this] at h_opcodeCall
            simp [Bool.toFelt] at h_opcodeCall

          have h_fp_update_regular_flag_val_0: flags FLAG_FP_UPDATE_REGULAR_INDEX = 0 := by
            rw [h_fp_update_regular_eq]
            rw[h_call_flag_true]
            simp[Bool.toFelt]

          rw[h_fp_update_regular_flag_val_0] at h_next_fp_eq
          simp at h_next_fp_eq

          rw[h_ret_flag_val_0] at h_next_fp_eq
          simp at h_next_fp_eq

          simp[h_call_flag_val] at h_call
          unfold EvalOperands.dst_spec at h_dst
          simp[h_call.2.2.2, h_call.1] at h_dst
          have ap_rc := Felt252IdMemoryAssign.IsRangeChecked_address_of_HasValue memChecked h_dst
          rcases ap_rc with ⟨ap_n, h_ap_lt, h_ap_eq⟩
          have h_ap_nat_eq : ap_nat₀ = ap_n := by
            rw[h_ap_nat₀] at h_ap_eq
            have : (↑ap_nat₀:Felt).val = (ap_n:Felt).val := by
              rw[h_ap_eq]
            rw[ZMod.val_natCast_of_lt] at this
            rw[ZMod.val_natCast_of_lt] at this
            exact this
            unfold Stwo.P
            omega
            unfold Stwo.P
            by_cases htmp4 : num_steps = 0 <;> simp[htmp4] at ap_bound₀ <;> omega
          use ap_n+2
          constructor
          · by_cases h_ns_0 : num_steps = 0
            · rw [h_ns_0, zero_add, Nat.add_lt_iff_lt_sub_right, ← h_ap_nat_eq]
              rw [if_pos h_ns_0] at ap_bound₀
              have := ap_bound₀
              apply lt_of_lt_of_le ap_bound₀
              norm_num1
            apply Nat.add_lt_add_of_lt_of_le h_ap_lt _
            apply Nat.succ_le_succ
            exact Nat.one_le_iff_ne_zero.mpr h_ns_0
          · rw[Nat.cast_add, ← h_ap_eq]
            rw[(show (↑(2:Nat):Felt) = (2:Felt) by rfl)]
            exact h_next_fp_eq


        · have h_inst_call_false : instruction.opcodeCall = false := by
            unfold FLAG_OPCODE_CALL_INDEX at h_call_flag_val
            simp at h_opcodeCall
            by_contra h_contra
            push_neg at h_contra
            have : instruction.opcodeCall = true := by simp [h_contra]
            rw [this] at h_opcodeCall
            simp [Bool.toFelt] at h_opcodeCall
            rw [h_opcodeCall] at h_call_flag_val
            absurd h_call_flag_val
            rfl
          have h_call_flag_val_0: flags (Fin.castLE UpdateRegisters.call._proof_1 FLAG_OPCODE_CALL_INDEX) = 0 := by
            simp at h_opcodeCall
            unfold FLAG_OPCODE_CALL_INDEX
            rw[h_opcodeCall]
            rw [h_inst_call_false]
            simp[Bool.toFelt]
          simp at h_next_fp_eq
          rw[h_ret_flag_val_0,h_call_flag_val_0] at h_next_fp_eq
          simp at h_next_fp_eq

          rw[h_inst_ret_false,h_inst_call_false] at h_fp_update_regular_eq
          simp[Bool.toFelt] at h_fp_update_regular_eq
          rw[h_fp_update_regular_eq, one_mul] at h_next_fp_eq

          use fp_nat
          constructor
          · omega
          rw[h_next_fp_eq]
          exact h_fp_nat

  intro mem hmem
  use instruction
  constructor
  · -- The instruction is in memory
    rw [hmem.2 _ _ _ h_instr_hasValue h_instr252_n]
    rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _  h_instr252_n h_instr_encode]
  constructor
  · -- next pc
    unfold Instruction.nextPc
    revert h_next_pc h_res
    simp only [FLAG_PC_UPDATE_JUMP_INDEX, h_pcJumpAbs, FLAG_PC_UPDATE_JUMP_REL_INDEX, h_pcJumpRel,
      FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz]
    unfold DecodeGenericInstruction.atMostOneTrue3 at h_pc_update_regular_atMost
    revert h_pc_update_regular_atMost
    unfold Instruction.res
    cases instruction.pcJumpAbs
    · cases instruction.pcJumpRel
      · cases instruction.pcJnz
        · -- next instruction
          simp [Bool.toFelt, CasmStateVal.toRegisterStateFelt252] ; intro _ h_next_pc ; rw [h_next_pc]
          simp only [h_instr_size, Instruction.size]
          cases instruction.op1Imm <;>
          simp <;> norm_num1
          simp [toFelt252_add_one_of_RangeChecked pc_rc, Option.Agrees]
          simp [toFelt252_add_two_of_RangeChecked pc_rc, Option.Agrees]
        -- conditional jump
        intro _ _ h_res
        unfold EvalOperands.dst_spec at h_dst
        simp only [FLAG_DST_BASE_FP_INDEX, h_dstReg] at h_dst
        simp only [Instruction.dst]
        revert h_res
        revert h_dst
        by_cases h_dstReg : instruction.dstReg
        all_goals {
          simp [h_dstReg, Bool.toFelt, CasmStateVal.toRegisterStateFelt252]
          intro h_dst
          rw [mem_at_addr_eq_eval_of_HasValue memChecked hmem h_offDst h_dst]
          by_cases h_eval : dst.eval = 0
          · simp only [h_eval, h_instr_size, Instruction.size]
            cases instruction.op1Imm <;> simp <;> norm_num1 <;>
            simp [Option.Agrees] <;> intro h_pc_add <;>
            simp [←toFelt252_add_one_of_RangeChecked pc_rc, ←toFelt252_add_two_of_RangeChecked pc_rc, h_pc_add]
          simp [if_neg h_eval]
          intro h_pc_add h_op1_eq
          simp [
            op1_eq memChecked hmem h_op1_base_op0_atMost h_op1_base_op0_eq h_op0Reg h_op1Imm h_op1Fp h_op1Ap op0 op1 h_op0 h_op1_2,
            Option.Agrees, h_pc_add, ←(h_op1_eq h_eval).1]
          rw [(h_op1_eq h_eval).2 _ pc_rc]
        }
      -- relative jump
      intro h1 ; simp at h1 ; simp [h1] ; simp [Bool.toFelt]
      intro h_res h_next_pc h_res_eq h_pc_add
      conv => arg 2 ; rw [CasmStateVal.toRegisterStateFelt252]
      rw [h_next_pc, h_pc_add _ pc_rc]
      have h_res_rc := EvalOperands.res_IsRangeChecked_of_spec memChecked h_op1_2 h_res
      simp [h_res_eq]
      simp only [
        resAux_eq memChecked hmem h_op1_base_op0_atMost h_op1_base_op0_eq h_res_op1_atMost h_res_op1_eq
          h_op0Reg h_op1Imm h_op1Fp h_op1Ap h_resAdd h_resMul
          h_op0_rc h_op1_rc h_res_rc h_op0 h_op1_2 h_res]
      simp [CasmStateVal.toRegisterStateFelt252, Option.Agrees]
    -- absolute jump
    intro h1 ; simp at h1 ; simp [h1.1, h1.2]
    simp [Bool.toFelt] ; intro h_res h_next_pc h_res_eq
    conv => arg 2 ; rw [CasmStateVal.toRegisterStateFelt252]
    rw [h_next_pc]
    have h_res_rc := EvalOperands.res_IsRangeChecked_of_spec memChecked h_op1_2 h_res
    simp [
      h_res_eq,
      resAux_eq memChecked hmem h_op1_base_op0_atMost h_op1_base_op0_eq h_res_op1_atMost h_res_op1_eq
        h_op0Reg h_op1Imm h_op1Fp h_op1Ap h_resAdd h_resMul
        h_op0_rc h_op1_rc h_res_rc h_op0 h_op1_2 h_res,
      Option.Agrees]
  constructor
  · -- next ap
    unfold Instruction.nextAp
    simp [
      FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OPCODE_RET_INDEX, h_opcodeRet,
      FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq,
      FLAG_AP_UPDATE_ADD_INDEX, h_apAdd, FLAG_AP_UPDATE_ADD_1_INDEX, h_apAdd1] at h_next_ap
    revert h_next_ap
    cases instruction.opcodeCall <;> cases instruction.opcodeRet <;> cases instruction.opcodeAssertEq <;>
    simp [Option.Agrees]
    pick_goal 4
    · simp [Bool.toFelt]
      intro h_next_ap
      cases instruction.apAdd <;> cases instruction.apAdd1 <;> simp
      simp only [CasmStateVal.toRegisterStateFelt252, h_next_ap, eq_comm]
      apply toFelt252_add_two_of_step_bounded ns_lim h_ap_nat ap_bound
    all_goals {
      unfold Instruction.nextApAux
      simp only [FLAG_AP_UPDATE_ADD_INDEX, h_apAdd] at h_res_as_addr
      revert h_res_as_addr
      cases instruction.apAdd <;> cases instruction.apAdd1 <;>
      intro h_res_as_addr <;>
      simp [UpdateRegisters.nextApAux, Bool.toFelt] <;>
      intro h_next_ap
      · simp only [CasmStateVal.toRegisterStateFelt252, h_next_ap]
      · simp only [CasmStateVal.toRegisterStateFelt252, h_next_ap, eq_comm]
        apply toFelt252_add_one_of_step_bounded ns_lim h_ap_nat _
        omega
      unfold Instruction.res
      revert h_res
      simp only [FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz]
      cases instruction.pcJumpAbs <;> cases instruction.pcJumpRel <;> cases instruction.pcJnz <;>
      simp [Bool.toFelt]
      all_goals {
        intro h_res
        have h_res_rc := EvalOperands.res_IsRangeChecked_of_spec memChecked h_op1_2 h_res
        simp [
          resAux_eq memChecked hmem h_op1_base_op0_atMost h_op1_base_op0_eq h_res_op1_atMost h_res_op1_eq
            h_op0Reg h_op1Imm h_op1Fp h_op1Ap h_resAdd h_resMul
            h_op0_rc h_op1_rc h_res_rc h_op0 h_op1_2 h_res]
        simp only [CasmStateVal.toRegisterStateFelt252, h_next_ap]
        simp [Bool.toFelt] at h_res_as_addr
        replace h_res_as_addr := h_res_as_addr h_res_rc
        rw [←h_res_as_addr.1, eq_comm]
        apply h_res_as_addr.2
      }
    }
  constructor
  · -- next fp
    unfold Instruction.nextFp
    simp only [EvalOperands.dst_spec, FLAG_DST_BASE_FP_INDEX, h_dstReg] at h_dst
    simp only [Instruction.dst]
    revert h_call
    revert h_next_fp h_fp_update_regular_atMost
    simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OPCODE_RET_INDEX, h_opcodeRet, FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq]
    revert h_dst
    cases instruction.opcodeCall
    · cases instruction.opcodeRet
      · cases instruction.opcodeAssertEq <;> simp [Bool.toFelt] <;>
        intro _ _ h_next_fp <;> simp [CasmStateVal.toRegisterStateFelt252, Option.Agrees, h_next_fp]
      cases instruction.opcodeAssertEq <;> simp [Bool.toFelt]
      · by_cases h_dstReg : instruction.dstReg
        all_goals {
          simp [h_dstReg, CasmStateVal.toRegisterStateFelt252]
          intro h_dst _ h_next_fp h_dst_eq
          rw [mem_at_addr_eq_eval_of_HasValue memChecked hmem h_offDst h_dst]
          rw [h_next_fp, Option.Agrees]
          exact h_dst_eq.symm
        }
      simp [Option.Agrees]
    intro h_dst h_fp_update_regular_atMost
    simp [DecodeGenericInstruction.atMostOneTrue] at h_fp_update_regular_atMost
    simp only [h_fp_update_regular_atMost]
    cases instruction.opcodeAssertEq <;> simp [Bool.toFelt]
    · intro h_next_fp h_offset0 h_offset1 _ h_dst_base
      simp [CasmStateVal.toRegisterStateFelt252, Option.Agrees, h_next_fp]
      simp only [FLAG_DST_BASE_FP_INDEX, h_dstReg] at h_dst_base
      simp [h_offset0, Bool.toFelt, Bool.false_of_toFelt_zero h_dst_base] at h_dst
      have h_ap_rc := memory.IsRangeChecked_address_of_HasValue memChecked h_dst
      exact (toFelt252_add_two_of_RangeChecked h_ap_rc).symm
    simp [Option.Agrees]
  -- asserts
  simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall,
    FLAG_OPCODE_RET_INDEX, h_opcodeRet, FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq] at h_assert
  revert h_fp_update_regular_atMost h_assert
  unfold Instruction.Asserts
  cases instruction.opcodeCall
  · cases instruction.opcodeRet
    · cases instruction.opcodeAssertEq
      · intro _ _ ; trivial
      intro _ h_assert
      simp [Bool.toFelt] at h_assert
      simp ; unfold Instruction.res Instruction.dst
      simp only [EvalOperands.dst_spec, FLAG_DST_BASE_FP_INDEX, h_dstReg] at h_dst
      revert h_res
      simp only [FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz]
      cases instruction.pcJumpAbs <;> cases instruction.pcJumpRel <;> cases instruction.pcJnz <;>
      intro h_res <;> simp [Option.Agrees]
      all_goals {
        simp [Bool.toFelt] at h_res
        have h_res_rc := EvalOperands.res_IsRangeChecked_of_spec memChecked h_op1_2 h_res
        simp only [
          resAux_eq memChecked hmem h_op1_base_op0_atMost h_op1_base_op0_eq h_res_op1_atMost h_res_op1_eq
            h_op0Reg h_op1Imm h_op1Fp h_op1Ap h_resAdd h_resMul
            h_op0_rc h_op1_rc h_res_rc h_op0 h_op1_2 h_res]
        revert h_dst
        cases instruction.dstReg
        all_goals {
          simp [Bool.toFelt, CasmStateVal.toRegisterStateFelt252] ; intro h_dst
          rw [mem_at_addr_eq_eval_of_HasValue memChecked hmem h_offDst h_dst]
          apply congr_arg _ h_assert
        }
      }
    cases instruction.opcodeAssertEq <;> simp [Bool.toFelt]
  intro h_fp_update_regular_atMost
  simp [DecodeGenericInstruction.atMostOneTrue] at h_fp_update_regular_atMost
  simp only [h_fp_update_regular_atMost]
  cases instruction.opcodeAssertEq
  · simp [Bool.toFelt]
    intro h_assert_op0 h_assert_op0_eq h_assert_dst h_assert_dst_eq
    constructor
    · simp [CasmStateVal.toRegisterStateFelt252, op0_eq memChecked hmem op0 h_op0Reg h_op0]
      rw [←h_assert_op0_eq h_op0_rc, h_assert_op0]
      unfold Instruction.size
      revert h_instr_size
      cases instruction.op1Imm
      all_goals {
        simp ; intro h ; rw [h]
        try norm_num1
        exact toFelt252_add_of_RangeChecked _ pc_rc (by simp [Stwo.P])
      }
    unfold Instruction.dst
    simp only [EvalOperands.dst_spec, FLAG_DST_BASE_FP_INDEX, h_dstReg] at h_dst
    revert h_dst
    cases instruction.dstReg
    all_goals {
      simp [Bool.toFelt, CasmStateVal.toRegisterStateFelt252]
      intro h_dst
      rw [mem_at_addr_eq_eval_of_HasValue memChecked hmem h_offDst h_dst]
      rw [←h_assert_dst, ←h_assert_dst_eq h_dst_rc]
    }
  intro _ ; trivial

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
    (num_steps: Nat) :
    let state := call ab lt casmState
    let new_ab := state.1
    let new_lt := state.2.1
    let ρcasmState := state.2.2
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρcasmState.eval varAssign) num_steps := by
  unfold call ; lift_lets
  intro state1 ab1 lt1 flags offset0 offset1 offset2
    state2 ab2 lt2 dst op0 op1 res
    ab3
    state4 ab4 lt3 ρcasmState₀
    state5 new_ab new_lt ρcasmState
  intro hab4 hlt3
  have ⟨hab3, hlt2, h_registers⟩ := UpdateRegisters.sound_auto _ memAssign _ _ _ h_rc h_mem casmState offset0 offset1 offset2 flags dst op0 op1 res num_steps hab4 hlt3
  have ⟨hab2, h_opcodes⟩ := HandleOpcodes.sound_auto _ memAssign _ _ _ _ _ _ _ _ hab3
  have ⟨hab1, hlt1, h_operands⟩ := EvalOperands.sound_auto _ _ _ _ _ h_rc h_mem _ _ _ _ _ hab2 hlt2
  have ⟨hab, hlt, h_decode⟩ := DecodeGenericInstruction.sound_auto _ _ _ _ _ h_rc h_mem h_verify_instr _ hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use (offset0.eval varAssign), (offset1.eval varAssign), (offset2.eval varAssign)
  use (fun i => (flags i).eval varAssign)
  use h_decode
  use (dst.eval varAssign), (op0.eval varAssign), (op1.eval varAssign), (res.eval varAssign)
  use (h_operands h_decode)
  use (h_opcodes h_decode)
  exact h_registers h_decode (h_operands h_decode)

theorem sound_generic [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases h_spec h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨instr, h_instr, h_next⟩
  use instr
  use h_instr

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {casmState : CasmState} :
    AirLookupTerms.NoYieldTerms (call ab lt casmState).2.1 := by
  unfold call
  repeat
    apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
  apply EvalOperands.NoYieldTerms_of_call
  repeat
    apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
  simp [h]

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {casmState : CasmState} :
    AirLookupTerms.NoTermsOfRel (call ab lt casmState).2.1 OPCODE_TRACE_REL_INDEX := by
  unfold call
  repeat
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr ;
    simp [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  apply EvalOperands.NoTermsOfRel_OPCODE_TRACE_of_call
  repeat
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr ; simp
  simp_all [VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {casmState : CasmState} :
    AirLookupTerms.RelInRelTuples (call ab lt casmState).2.1 := by
  unfold call
  repeat
    apply AirLookupTerms.add'_RelInRelTuple.mpr
  apply EvalOperands.RelInRelTuples_of_call
  repeat
    simp [DecodeGenericInstruction.call] ; apply AirLookupTerms.add'_RelInRelTuple.mpr
  simp [h]

end GenericOpcode
