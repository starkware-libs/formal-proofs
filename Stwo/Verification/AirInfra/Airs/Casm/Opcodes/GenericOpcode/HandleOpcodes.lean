import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.DecodeGenericInst
import Verification.AirInfra.Airs.Felt252Utils.CondAsSmall

open Fin.NatCast

namespace HandleOpcodes

def call
    (airBuilder : AirBuilder)
    (casmState : CasmState)
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (offset0 offset1 offset2 : FeltExpr)
    (dst op0 res : Felt252Expr)
    : AirBuilder :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  let ab1 := forLoop 0 FELT252_N_WORDS airBuilder
    fun i ab => ab.constrain ((instrFlags FLAG_OPCODE_ASSERT_EQ_INDEX) * (res i - dst i))
  let ab2 := ab1.constrain ((instrFlags FLAG_OPCODE_RET_INDEX) * (offset0 + FeltExpr.const 2))
  let ab3 := ab2.constrain ((instrFlags FLAG_OPCODE_RET_INDEX) * (offset2 + FeltExpr.const 1))
  let ab4 := ab3.constrain (
      (instrFlags FLAG_OPCODE_RET_INDEX) *
      (FeltExpr.const 4
      - instrFlags FLAG_PC_UPDATE_JUMP_INDEX
      - instrFlags FLAG_DST_BASE_FP_INDEX
      - instrFlags FLAG_OP1_BASE_FP_INDEX
      - flags FLAG_RES_OP1_INDEX)
    )
  let ab5 := ab4.constrain ((instrFlags FLAG_OPCODE_CALL_INDEX) * offset0)
  let ab6 := ab5.constrain ((instrFlags FLAG_OPCODE_CALL_INDEX) * (FeltExpr.const 1 - offset1))
  let ab7 := ab6.constrain (
      (instrFlags FLAG_OPCODE_CALL_INDEX) *
      (instrFlags FLAG_OP0_BASE_FP_INDEX + instrFlags FLAG_DST_BASE_FP_INDEX)
    )
  let _state := CondFelt252AsAddr.call ab7 dst (instrFlags FLAG_OPCODE_CALL_INDEX)
  let ab8 := _state.1
  let dst_as_addr := _state.2
  let ab9 := ab8.constrain (
      (instrFlags FLAG_OPCODE_CALL_INDEX) * (dst_as_addr - casmState.fp)
    )
  let _state := CondFelt252AsAddr.call ab9 op0 (instrFlags FLAG_OPCODE_CALL_INDEX)
  let ab10 := _state.1
  let op0_as_addr := _state.2
  let ab11 := ab10.constrain (
      (instrFlags FLAG_OPCODE_CALL_INDEX) *
      (op0_as_addr - (casmState.pc + flags INSTRUCTION_SIZE_INDEX))
    )
  ab11

def spec_auto
    (casmStateVal : CasmStateVal)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (offset0 offset1 offset2 : Felt)
    (dst op0 res : Felt252Words)
     : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  (∀ i : Fin FELT252_N_WORDS, (instrFlags FLAG_OPCODE_ASSERT_EQ_INDEX) * (res i - dst i) = 0) ∧
  instrFlags FLAG_OPCODE_RET_INDEX * (offset0 + 2) = 0 ∧
  instrFlags FLAG_OPCODE_RET_INDEX * (offset2 + 1) = 0 ∧
  instrFlags FLAG_OPCODE_RET_INDEX *
    (4
      - instrFlags FLAG_PC_UPDATE_JUMP_INDEX
      - instrFlags FLAG_DST_BASE_FP_INDEX
      - instrFlags FLAG_OP1_BASE_FP_INDEX
      - flags FLAG_RES_OP1_INDEX) = 0 ∧
  instrFlags FLAG_OPCODE_CALL_INDEX * offset0 = 0 ∧
  instrFlags FLAG_OPCODE_CALL_INDEX * (1 - offset1) = 0 ∧
  instrFlags FLAG_OPCODE_CALL_INDEX *
    (instrFlags FLAG_OP0_BASE_FP_INDEX + instrFlags FLAG_DST_BASE_FP_INDEX) = 0 ∧
  (∃ dst_as_addr, CondFelt252AsAddr.spec dst (instrFlags FLAG_OPCODE_CALL_INDEX) dst_as_addr ∧
    instrFlags FLAG_OPCODE_CALL_INDEX * (dst_as_addr - casmStateVal.fp) = 0) ∧
  ∃ op0_as_addr, CondFelt252AsAddr.spec op0 (instrFlags FLAG_OPCODE_CALL_INDEX) op0_as_addr ∧
    instrFlags FLAG_OPCODE_CALL_INDEX * (op0_as_addr - (casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX)) = 0

def spec
    (casmStateVal : CasmStateVal)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (offset0 offset1 offset2 : Felt)
    (dst op0 res : Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  (instrFlags FLAG_OPCODE_RET_INDEX ≠ 0 →
    offset0 = -2
    ∧ offset2 = -1
    ∧ instrFlags FLAG_PC_UPDATE_JUMP_INDEX = 1
    ∧ instrFlags FLAG_DST_BASE_FP_INDEX = 1
    ∧ instrFlags FLAG_OP1_BASE_FP_INDEX = 1
    ∧ flags FLAG_RES_OP1_INDEX = 1
  )
  ∧ (instrFlags FLAG_OPCODE_CALL_INDEX ≠ 0 →
      offset0 = 0
      ∧ offset1 = 1
      ∧ instrFlags FLAG_OP0_BASE_FP_INDEX = 0
      ∧ instrFlags FLAG_DST_BASE_FP_INDEX = 0
  )
  ∧ match (instrFlags FLAG_OPCODE_CALL_INDEX), (instrFlags FLAG_OPCODE_RET_INDEX), (instrFlags FLAG_OPCODE_ASSERT_EQ_INDEX) with
    | 0, 0, 0 => True
    | 1, 0, 0 => (felt252_to_m31_val op0 ADDRESS_BITS) = casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX
                  ∧ (Felt252Nats.ExistsIsRangeChecked op0 → (felt252_to_m31_val op0 ADDRESS_BITS).toFelt252 = op0.eval)
                  ∧ (felt252_to_m31_val dst ADDRESS_BITS) = casmStateVal.fp
                  ∧ (Felt252Nats.ExistsIsRangeChecked dst → (felt252_to_m31_val dst ADDRESS_BITS).toFelt252 = dst.eval)
    | 0, 0, 1 => res = dst
    | _, _, _ => True

lemma all_one_of_four_sub_eq_zero
      {w x y z : Bool}
      (h : 4 - w.toFelt - x.toFelt - y.toFelt - z.toFelt = 0) :
    w.toFelt = 1 ∧ x.toFelt = 1 ∧ y.toFelt = 1 ∧ z.toFelt = 1 := by
  cases w <;> cases x <;> cases y <;> cases z <;> simp [Bool.toFelt] at h <;> norm_num at h <;>
  try { exfalso ; apply Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h }
  simp [Bool.toFelt]

lemma all_zero_of_add_eq_zero
      {x y : Bool}
      (h : x.toFelt + y.toFelt = 0) :
    x.toFelt = 0 ∧ y.toFelt = 0 := by
  cases x <;> cases y <;> simp [Bool.toFelt] at h <;> norm_num at h
  simp [Bool.toFelt]
  all_goals { exfalso ; apply Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h }

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    {memAssign : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {flags : Fin GENERIC_FLAGS_SIZE → Felt}
    {offset0 offset1 offset2 : Felt}
    {dst op0 res : Felt252Words}
    (h_spec_auto : spec_auto casmStateVal flags offset0 offset1 offset2 dst op0 res)
    -- To prove the spec from spec_auto, we also assume the spec of DecodeGenericInstruction
    (h_decode_spec : DecodeGenericInstruction.spec memAssign casmStateVal.pc
      (signed_as_offset_Felt offset0) (signed_as_offset_Felt offset1) (signed_as_offset_Felt offset2) flags) :
    spec casmStateVal flags offset0 offset1 offset2 dst op0 res := by
  rcases h_spec_auto with ⟨h_res_dst_eq, h_ret_off0, h_ret_off2, h_ret_flags, h_call_off0, h_call_off1, h_call_flags,
    ⟨dst_addr, h_call_fp⟩,⟨op0_addr, h_call_pc⟩⟩
  rcases h_decode_spec with ⟨instr, h_hasInstr, h_offDst, h_offOp0, h_dstOp1,
    h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq,
    h_op1_base_op0_atMost, h_op1_base_op0_eq, h_res_op1_atMost, h_res_op1_eq, h_pc_update_regular_atMost, h_pc_update_regular_eq,
    h_ap_update_regular, h_fp_update_regular_atMost, h_fp_update_regular_eq, h_instr_size⟩
  constructor
  · revert h_ret_off0 h_ret_off2 h_ret_flags
    simp only [FLAG_OPCODE_RET_INDEX, h_opcodeRet, FLAG_PC_UPDATE_JUMP_INDEX, h_pcJumpAbs, FLAG_DST_BASE_FP_INDEX, h_dstReg,
      FLAG_OP1_BASE_FP_INDEX, h_op1Fp, h_res_op1_eq]
    cases instr.opcodeRet
    · simp [Bool.toFelt]
    intro h_ret_off0 h_ret_off2 h_ret_flags _
    simp [Bool.toFelt, ←eq_neg_iff_add_eq_zero] at h_ret_off0 h_ret_off2
    rw [Bool.toFelt] at h_ret_flags
    simp only [cond_true, one_mul] at h_ret_flags
    use h_ret_off0, h_ret_off2
    exact all_one_of_four_sub_eq_zero h_ret_flags
  constructor
  · revert h_call_off0 h_call_off1 h_call_flags
    simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OP0_BASE_FP_INDEX, h_op0Reg, FLAG_DST_BASE_FP_INDEX, h_dstReg]
    cases instr.opcodeCall
    · simp [Bool.toFelt]
    intro h_call_off0 h_call_off1 h_call_flags _
    simp [Bool.toFelt] at h_call_off0 h_call_off1
    rw [sub_eq_zero, Eq.comm] at h_call_off1
    use h_call_off0, h_call_off1
    rw [Bool.toFelt, cond_true, one_mul] at h_call_flags
    exact all_zero_of_add_eq_zero h_call_flags
  revert h_res_dst_eq h_call_fp h_call_pc
  simp only [FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq, FLAG_OPCODE_CALL_INDEX, h_opcodeCall,
    FLAG_OPCODE_RET_INDEX, h_opcodeRet, h_instr_size]
  cases instr.opcodeCall
  · cases instr.opcodeRet
    · cases instr.opcodeAssertEq
      · simp [Bool.toFelt]
      simp [Bool.toFelt]
      intro h1 _ _
      apply funext
      simp only [sub_eq_zero] at h1
      exact h1
    intro _ _ _ ; simp [Bool.toFelt]
  simp [Bool.toFelt] ; intro _ h_dst_addr h_dst_eq h_op0_addr h_op0_eq
  rw [h_dst_addr.1, sub_eq_zero] at h_dst_eq
  rw [h_op0_addr.1, sub_eq_zero] at h_op0_eq
  cases instr.opcodeRet <;> cases instr.opcodeAssertEq
  use h_op0_eq
  constructor
  · intro h_rc
    rw [←h_op0_addr.1]
    apply (h_op0_addr.2 (by simp)).1 h_rc
  use h_dst_eq
  · intro h_rc
    rw [←h_dst_addr.1]
    apply (h_dst_addr.2 (by simp)).1 h_rc
  all_goals trivial

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (casmState : CasmState)
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (offset0 offset1 offset2 : FeltExpr)
    (dst op0 res : Felt252Expr) :
    let new_ab := call ab casmState flags offset0 offset1 offset2 dst op0 res
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      (DecodeGenericInstruction.spec memAssign
        (CasmState.eval varAssign casmState).pc
        (signed_as_offset_Felt (offset0.eval varAssign))
        (signed_as_offset_Felt (offset1.eval varAssign))
        (signed_as_offset_Felt (offset2.eval varAssign))
        (fun i => (flags i).eval varAssign) →
          spec
            (casmState.eval varAssign)
            (fun i => (flags i).eval varAssign)
            (offset0.eval varAssign)
            (offset1.eval varAssign)
            (offset2.eval varAssign)
            (dst.eval varAssign)
            (op0.eval varAssign)
            (res.eval varAssign)
      ) := by
  unfold call ; lift_lets
  intro instrFlags
    ab1 ab2 ab3 ab4 ab5 ab6 ab7
    state1 ab8 dst_as_addr ab9
    state2 ab10 op0_as_addr ab11
    new_ab
  intro hab11
  have ⟨hab10, h_call_pc⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab11
  have ⟨hab9, h_op0_addr⟩ := CondFelt252AsAddr.sound_auto _ _ op0 (instrFlags FLAG_OPCODE_CALL_INDEX) hab10
  have ⟨hab8, h_call_fp⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab9
  have ⟨hab7, h_dst_addr⟩ := CondFelt252AsAddr.sound_auto _ _ dst (instrFlags FLAG_OPCODE_CALL_INDEX) hab8
  have ⟨hab6, h_call_base_fp⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab7
  have ⟨hab5, h_call_offset1⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab6
  have ⟨hab4, h_call_offset0⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
  have ⟨hab3, h_ret_flags⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab4
  have ⟨hab2, h_ret_offset2⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, h_ret_offset0⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2
  have ⟨hab, h_assert_eq⟩ := (AirBuilder.constraint_loop_SatisfiedBy _ varAssign _ _ (by norm_num) _).mp hab1

  use hab
  intro h_decode_spec
  apply spec_of_spec_auto _ h_decode_spec

  constructor
  · intro i
    replace h_assert_eq := h_assert_eq i.val (Nat.zero_le _) (Fin.isLt i)
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, Fin.cast_val_eq_self] at h_assert_eq
    exact h_assert_eq
  use h_ret_offset0, h_ret_offset2, h_ret_flags, h_call_offset0, h_call_offset1, h_call_base_fp
  constructor
  · use dst_as_addr.eval varAssign, h_dst_addr, h_call_fp
  use op0_as_addr.eval varAssign, h_op0_addr, h_call_pc

end HandleOpcodes
