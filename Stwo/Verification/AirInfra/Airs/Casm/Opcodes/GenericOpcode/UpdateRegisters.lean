import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.DecodeGenericInst
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.EvalOperands
import Verification.AirInfra.Airs.Casm.Opcodes.JnzOpcode
import Verification.AirInfra.Airs.Felt252Utils.CondAsSmall
import Verification.AirInfra.Airs.Casm.Opcodes.AddApOpcode



namespace UpdateRegisters



  def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState)
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (dst op1 res : Felt252Expr)
    : AirBuilder × AirLookupTerms × CasmState :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  let _state := CondFelt252AsAddr.call airBuilder res (instrFlags FLAG_PC_UPDATE_JUMP_INDEX)
  let ab1 := _state.1
  let res_as_addr := _state.2
  let _state := CondFelt252AsAddr.call ab1 dst (instrFlags FLAG_OPCODE_RET_INDEX)
  let ab2 := _state.1
  let dst_as_addr := _state.2
  let _state := CondFelt252AsRelImm.call ab2 res (instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX + instrFlags FLAG_AP_UPDATE_ADD_INDEX)
  let ab3 := _state.1
  let res_as_rel_imm := _state.2
  let dst_sum_squares := Felt252Expr.limb_sum_squares dst
  let _state := ab3.deduce
  let ab4 := _state.1
  let sum_squares_inv := _state.2
  let ab5 := ab4.constrain (dst_sum_squares * sum_squares_inv - FeltExpr.const 1)
  let dst_sum := dst.limb_sum
  let _state := ab5.deduce
  let ab6 := _state.1
  let dst_is_zero := _state.2
  let _state := ab6.deduce
  let ab7 := _state.1
  let sum_inv := _state.2
  let _state := ab7.assign (instrFlags FLAG_PC_UPDATE_JNZ_INDEX * dst_sum)
  let ab8 := _state.1
  let op1_as_rel_imm_condition := _state.2
  let _state := CondFelt252AsRelImm.call ab8 op1 op1_as_rel_imm_condition
  let ab9 := _state.1
  let op1_as_rel_imm := _state.2
  let _state := ab9.deduce
  let ab10 := _state.1
  let npc_jnz := _state.2
  let ab11 := ab10.constrain ((npc_jnz - (casmState.pc + op1_as_rel_imm)) * dst_sum)
  let ab12 := ab11.constrain ((npc_jnz - (casmState.pc + flags INSTRUCTION_SIZE_INDEX)) * (dst_sum * sum_inv - FeltExpr.const 1))
  let next_pc₀ := flags FLAG_PC_UPDATE_REGULAR_INDEX * (casmState.pc + flags INSTRUCTION_SIZE_INDEX)
                  + instrFlags FLAG_PC_UPDATE_JUMP_INDEX * res_as_addr
                  + instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX * (casmState.pc + res_as_rel_imm)
                  + instrFlags FLAG_PC_UPDATE_JNZ_INDEX * npc_jnz
  let _state := ab12.assign next_pc₀
  let ab13 := _state.1
  let next_pc := _state.2
  let next_ap₀ := casmState.ap
                  + instrFlags FLAG_AP_UPDATE_ADD_INDEX * res_as_rel_imm
                  + instrFlags FLAG_AP_UPDATE_ADD_1_INDEX * FeltExpr.const 1
                  + instrFlags FLAG_OPCODE_CALL_INDEX * FeltExpr.const 2
  let _state := ab13.assign next_ap₀
  let ab14 := _state.1
  let next_ap := _state.2
  let _state := RangeCheckAP.call ab14 lookupTerms next_ap --casmState.ap
  let ab15 := _state.1
  let rc1 := _state.2
  let next_fp₀ := flags FLAG_FP_UPDATE_REGULAR_INDEX * casmState.fp
                  + instrFlags FLAG_OPCODE_RET_INDEX * dst_as_addr
                  + instrFlags FLAG_OPCODE_CALL_INDEX * (casmState.ap + FeltExpr.const 2)
  let _state := ab15.assign next_fp₀
  let ab16 := _state.1
  let next_fp := _state.2
  (ab16, rc1, ⟨next_pc, next_ap, next_fp⟩)

def spec_auto [Fact (Nat.Prime Stwo.P)]
    (casmStateVal : CasmStateVal)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (dst op1 res : Felt252Words)
    (ρcasmStateVal : CasmStateVal) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  ∃ res_as_addr, (CondFelt252AsAddr.spec res (instrFlags FLAG_PC_UPDATE_JUMP_INDEX) res_as_addr) ∧
    ∃ dst_as_addr, (CondFelt252AsAddr.spec dst (instrFlags FLAG_OPCODE_RET_INDEX) dst_as_addr) ∧
      ∃ res_as_rel_imm,
        CondFelt252AsRelImm.spec res
          (instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX + instrFlags FLAG_AP_UPDATE_ADD_INDEX)
          res_as_rel_imm ∧
        let dst_sum_squares := Felt252Words.limb_sum_squares dst
        ∃ sum_squares_inv, dst_sum_squares * sum_squares_inv - 1 = 0 ∧
          let dst_sum := dst.limb_sum
          let op1_as_rel_imm_condition := instrFlags FLAG_PC_UPDATE_JNZ_INDEX * dst_sum
          ∃ op1_as_rel_imm, CondFelt252AsRelImm.spec op1 op1_as_rel_imm_condition op1_as_rel_imm ∧
            ∃ (sum_inv npc_jnz : Felt), (npc_jnz - (casmStateVal.pc + op1_as_rel_imm)) * dst_sum = 0 ∧
              (npc_jnz - (casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX)) * (dst_sum * sum_inv - 1) = 0 ∧
              let next_pc := flags FLAG_PC_UPDATE_REGULAR_INDEX * (casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX)
                + instrFlags FLAG_PC_UPDATE_JUMP_INDEX * res_as_addr
                + instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX * (casmStateVal.pc + res_as_rel_imm)
                + instrFlags FLAG_PC_UPDATE_JNZ_INDEX * npc_jnz
              let next_ap := casmStateVal.ap
                + instrFlags FLAG_AP_UPDATE_ADD_INDEX * res_as_rel_imm
                + instrFlags FLAG_AP_UPDATE_ADD_1_INDEX * 1
                + instrFlags FLAG_OPCODE_CALL_INDEX * 2
              let next_fp := flags FLAG_FP_UPDATE_REGULAR_INDEX * casmStateVal.fp
                + instrFlags FLAG_OPCODE_RET_INDEX * dst_as_addr
                + instrFlags FLAG_OPCODE_CALL_INDEX * (casmStateVal.ap + 2)
              IsRangeChecked 29 next_ap ∧
              ρcasmStateVal = ⟨next_pc, next_ap, next_fp⟩

def nextApAux (ap res_as_rel_imm apAdd apAdd1 : Felt) : Felt :=
  match apAdd, apAdd1 with
  | 0, 0 => ap
  | _, 0 => ap + res_as_rel_imm
  | 0, _ => ap + 1
  | _, _ => 0 -- Cannot happen, so any value will do

@[irreducible]
def spec [Fact (Nat.Prime Stwo.P)]
    (casmStateVal : CasmStateVal)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (dst op1 res : Felt252Words)
    (ρcasmStateVal : CasmStateVal)
    (num_steps: Nat): Prop :=
  num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  ( -- next pc
    match (instrFlags FLAG_PC_UPDATE_JUMP_INDEX), (instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX), (instrFlags FLAG_PC_UPDATE_JNZ_INDEX) with
    | 0, 0, 0 => ρcasmStateVal.pc = casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX
    | _, 0, 0 => ρcasmStateVal.pc = felt252_to_m31_val res ADDRESS_BITS
                  ∧ (felt252_to_m31_val res ADDRESS_BITS).toFelt252 = res.eval
    | 0, _, 0 => (ρcasmStateVal.pc = casmStateVal.pc + Felt252_to_rel_imm_val res)
                  ∧ (Felt252_to_rel_imm_val res).toFelt252 = res.eval
                  ∧ ∀ x, IsRangeChecked 29 x →
                    (x + (Felt252_to_rel_imm_val res)).toFelt252 = x.toFelt252 + (Felt252_to_rel_imm_val res).toFelt252
    | 0, 0, _ => (ρcasmStateVal.pc = if dst.eval = 0 then casmStateVal.pc + flags INSTRUCTION_SIZE_INDEX else
                                      casmStateVal.pc + Felt252_to_rel_imm_val op1)
                  ∧ (dst.eval ≠ 0 →
                      (Felt252_to_rel_imm_val op1).toFelt252 = op1.eval
                      ∧ ∀ x, IsRangeChecked 29 x →
                        (x + (Felt252_to_rel_imm_val op1)).toFelt252 = x.toFelt252 + (Felt252_to_rel_imm_val op1).toFelt252
                    )
    | _, _, _ => False
  )
  ∧ ( -- next ap
      let _nextApAux := nextApAux
        casmStateVal.ap
        (Felt252_to_rel_imm_val res)
        (instrFlags FLAG_AP_UPDATE_ADD_INDEX)
        (instrFlags FLAG_AP_UPDATE_ADD_1_INDEX)
      match (instrFlags FLAG_OPCODE_CALL_INDEX), (instrFlags FLAG_OPCODE_RET_INDEX), (instrFlags FLAG_OPCODE_ASSERT_EQ_INDEX) with
      | 0, 0, 0 => ρcasmStateVal.ap = _nextApAux
      | _, 0, 0 => ρcasmStateVal.ap = casmStateVal.ap + 2
      | 0, _, 0 => ρcasmStateVal.ap = _nextApAux
      | 0, 0, _ => ρcasmStateVal.ap = _nextApAux
      | _, _, _ => True -- Undefined behavior, not excluded by the constraints.
  )
  --∧ IsRangeChecked 29 casmStateVal.ap
  ∧ IsRangeChecked 29 ρcasmStateVal.ap
  ∧ ((instrFlags FLAG_AP_UPDATE_ADD_INDEX) ≠ 0 →
        Felt252Nats.ExistsIsRangeChecked res →
          (Felt252_to_rel_imm_val res).toFelt252 = res.eval
          ∧ (casmStateVal.ap + (Felt252_to_rel_imm_val res)).toFelt252 = casmStateVal.ap.toFelt252 + (Felt252_to_rel_imm_val res).toFelt252)
  ∧ ( -- next fp
      match (instrFlags FLAG_OPCODE_CALL_INDEX), (instrFlags FLAG_OPCODE_RET_INDEX), (instrFlags FLAG_OPCODE_ASSERT_EQ_INDEX) with
      | 0, 0, 0 => ρcasmStateVal.fp = casmStateVal.fp
      | _, 0, 0 => ρcasmStateVal.fp = casmStateVal.ap + 2
      | 0, _, 0 => ρcasmStateVal.fp = felt252_to_m31_val dst ADDRESS_BITS
          ∧ (felt252_to_m31_val dst ADDRESS_BITS).toFelt252 = dst.eval
      | 0, 0, _ => ρcasmStateVal.fp = casmStateVal.fp
      | _, _, _ => True -- Undefined behavior, not excluded by the constraints.
  ) ∧ (
    ∃ dst_as_addr', (CondFelt252AsAddr.spec dst (instrFlags FLAG_OPCODE_RET_INDEX) dst_as_addr') ∧
    ρcasmStateVal.fp = flags FLAG_FP_UPDATE_REGULAR_INDEX * casmStateVal.fp
                + instrFlags FLAG_OPCODE_RET_INDEX * dst_as_addr'
                + instrFlags FLAG_OPCODE_CALL_INDEX * (casmStateVal.ap + 2))

-- Move this to a more general place.
lemma Felt.exists_inv_of_ne_zero [h_p : Fact (Nat.Prime Stwo.P)] {x : Felt} (h_x : x ≠ 0) : ∃ x_inv, x_inv * x = 1 := by
  use x⁻¹ ; rw [mul_comm, ZMod.mul_inv_eq_gcd x]
  rw [←Nat.cast_one] ; apply congr_arg
  rw [←Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm]
  apply Nat.coprime_of_lt_prime
  · rw [←ZMod.val_ne_zero] at h_x
    exact Nat.zero_lt_of_ne_zero h_x
  apply ZMod.val_lt
  exact Fact.elim h_p

set_option maxHeartbeats 400000 in
theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memAssign : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {offset0 offset1 offset2 : Felt}
    {flags : Fin GENERIC_FLAGS_SIZE → Felt}
    {dst op0 op1 res : Felt252Words}
    {ρcasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (memChecked : memAssign.IsRangeChecked)
    (h_spec_auto : spec_auto casmStateVal flags dst op1 res ρcasmStateVal)
    -- To prove the spec from spec_auto, we also assume the spec of DecodeGenericInstruction and EvalOperands
    (h_decode_spec : DecodeGenericInstruction.spec memAssign casmStateVal.pc
      (signed_as_offset_Felt offset0) (signed_as_offset_Felt offset1) (signed_as_offset_Felt offset2) flags)
    (h_EvalOperands_spec : EvalOperands.spec memAssign casmStateVal offset0 offset1 offset2 flags dst op0 op1 res) :
    spec casmStateVal flags dst op1 res ρcasmStateVal num_steps := by
  rcases h_spec_auto with ⟨res_as_addr, h_res_as_addr, dst_as_addr, h_dst_as_addr, res_as_rel_imm, h_res_as_rel_imm,
    sum_squares_inv, h_sum_squares_inv, op1_as_rel_imm, h_op1_as_rel_imm, sum_inv, npc_jnz, h_npc_jnz1, h_npc_jnz2,
    h_ap_rc, h_ρcasmStateVal⟩
  rcases h_decode_spec with ⟨instr, h_hasInstr, h_offDst, h_offOp0, h_dstOp1,
    h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq,
    h_op1_base_op0_atMost, h_op1_base_op0_eq, h_res_op1_atMost, h_res_op1_eq, h_pc_update_regular_atMost, h_pc_update_regular_eq,
    h_ap_update_regular_atMost, h_fp_update_regular_atMost, h_fp_update_regular_eq, h_instr_size⟩
  rcases h_EvalOperands_spec with ⟨h_eval_dst, h_eval_op0, h_eval_op1_base_op0, h_eval_op1, h_eval_res⟩
  unfold spec
  intro ns_lim cs_bound
  -- next pc
  constructor
  · revert h_ρcasmStateVal h_pc_update_regular_eq h_res_as_rel_imm h_res_as_addr
    revert h_op1_as_rel_imm
    revert h_pc_update_regular_atMost
    simp only [FLAG_PC_UPDATE_JUMP_INDEX, h_pcJumpAbs, FLAG_PC_UPDATE_JUMP_REL_INDEX, h_pcJumpRel, FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz]
    cases instr.pcJumpAbs
    · cases instr.pcJumpRel
      · cases instr.pcJnz
        · intro _ _ _ _ h5 h6
          simp [Bool.toFelt, h5, h6]
        intro _ h2 _ _ h5 h6
        simp [Bool.toFelt, h5, h6, -and_imp]
        rcases Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h_eval_dst with ⟨ndst, h_dst_rc⟩
        by_cases h_dst : dst.eval = 0
        · simp [h_dst]
          have h_limb_sum : dst.limb_sum = 0 := by
            by_contra h_limb_sum
            rw [Felt252Nats.eval_Felt252Words_eq h_dst_rc] at h_dst
            apply Felt252Nats.not_zero_if_sums_inversible h_dst_rc _ h_dst
            constructor
            · exact Felt.exists_inv_of_ne_zero h_limb_sum
            use sum_squares_inv
            rw [←sub_eq_zero, mul_comm]
            exact h_sum_squares_inv
          simp [h_limb_sum, sub_eq_zero] at h_npc_jnz2
          rw [←h_npc_jnz2]
        simp [h_dst]
        have h_dst_sum_ne_zero : dst.limb_sum ≠ 0 := by
          rw [ne_eq]
          cases' not_or_of_imp (Felt252Nats.zero_if_sum_limbs_zero h_dst_rc) with h h
          · exact h
          exfalso ; apply h_dst ; rwa [Felt252Nats.eval_Felt252Words_eq h_dst_rc]
        simp [Bool.toFelt] at h2
        replace h2 := h2 h_dst_sum_ne_zero
        constructor
        · rw [mul_eq_zero] at h_npc_jnz1
          cases' h_npc_jnz1 with h_npc_jnz1 h_npc_jnz1
          · rw [sub_eq_zero] at h_npc_jnz1
            rw [h_npc_jnz1, add_left_cancel_iff]
            exact h2.1
          exfalso ; exact h_dst_sum_ne_zero h_npc_jnz1
        rw [←h2.1]
        have := h2.2 (EvalOperands.op1_IsRangeChecked_of_spec memChecked h_eval_op1)
        constructor
        · exact this.1
        have := this.2 0 (show 0 < 2 ^ 29 by norm_num)
        unfold IsRangeChecked
        exact this
      intro h1
      unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1
      simp [h1, Bool.toFelt]
      intro _ _ h4 h5 h6
      simp [h5, h6]
      have h_condition : 1 +
          flags (Fin.castLE (Nat.le_of_ble_eq_true rfl) FLAG_AP_UPDATE_ADD_INDEX) ≠ 0 := by
        simp only [FLAG_AP_UPDATE_ADD_INDEX, h_apAdd]
        cases instr.apAdd <;> simp [Bool.toFelt] ; norm_num1
        exact Felt.n_ne_zero (by norm_num) (by simp [Stwo.P])
      replace h4 := h4 h_condition
      use h4.1
      simp [FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz, h1, Bool.toFelt] at h_eval_res
      rw [←h4.1]
      have := h4.2 (EvalOperands.res_IsRangeChecked_of_spec memChecked h_eval_op1 h_eval_res)
      constructor
      · exact this.1
      have := this.2 0 (show 0 < 2 ^ 29 by norm_num)
      unfold IsRangeChecked
      exact this
    intro h1
    unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1
    simp [h1, Bool.toFelt]
    intro h2 h3 h4 h5 h6
    simp [h5, h6]
    unfold CondFelt252AsAddr.spec at h3 ; simp at h3
    use h3.1
    simp [FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz, h1, Bool.toFelt] at h_eval_res
    rw [←h3.1] ; exact h3.2.1 (EvalOperands.res_IsRangeChecked_of_spec memChecked h_eval_op1 h_eval_res)
  -- next ap
  constructor
  · revert h_ρcasmStateVal h_res_as_rel_imm
    revert h_ap_update_regular_atMost h_fp_update_regular_atMost
    simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OPCODE_RET_INDEX, h_opcodeRet,
      FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq, FLAG_AP_UPDATE_ADD_INDEX, h_apAdd,
      FLAG_AP_UPDATE_ADD_1_INDEX, h_apAdd1, FLAG_PC_UPDATE_JUMP_REL_INDEX, h_pcJumpRel]
    cases instr.opcodeCall
    · cases instr.apAdd
      · cases instr.opcodeRet <;> cases instr.opcodeAssertEq <;> cases instr.apAdd1 <;>
        intro h1 <;> unfold DecodeGenericInstruction.atMostOneTrue3 at h1 <;> simp at h1 <;>
        simp [Bool.toFelt] <;>
        intro _ _ h4 <;> simp [h4, nextApAux]
      cases instr.opcodeRet <;> cases instr.opcodeAssertEq <;> cases instr.apAdd1 <;>
      intro h1 <;> unfold DecodeGenericInstruction.atMostOneTrue3 at h1 <;> simp at h1 <;>
      simp [Bool.toFelt] <;>
      intro _ h3 h4 <;> simp [nextApAux, h4] <;> apply (h3 _).1 <;>
      cases instr.pcJumpRel <;> simp <;> norm_num1 <;>
      exact Felt.n_ne_zero (by norm_num) (by simp [Stwo.P])
    intro h1 h2 _ h4 ; unfold DecodeGenericInstruction.atMostOneTrue at h2 ; simp at h2 ; simp [h2]
    cases instr.opcodeAssertEq <;> simp [h2, h4, Bool.toFelt]
    unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1 ; simp [h1]
  constructor
  · rw[h_ρcasmStateVal]
    exact h_ap_rc
  -- ap add res as addr
  constructor
  · revert h_res_as_rel_imm
    simp only [FLAG_AP_UPDATE_ADD_INDEX, h_apAdd]
    cases instr.apAdd
    · simp [Bool.toFelt]
    simp [Bool.toFelt]
    intro h_res_as_rel_imm h_res_rc
    have h_condition :
        flags (Fin.castLE (Nat.le_of_ble_eq_true rfl) FLAG_PC_UPDATE_JUMP_REL_INDEX) + 1 ≠ 0 := by
      simp only [FLAG_PC_UPDATE_JUMP_REL_INDEX, h_pcJumpRel]
      cases instr.pcJumpRel <;> simp [Bool.toFelt] ; norm_num1
      exact Felt.n_ne_zero (by norm_num) (by simp [Stwo.P])
    replace h_res_as_rel_imm := h_res_as_rel_imm h_condition
    rw [←h_res_as_rel_imm.1]
    use (h_res_as_rel_imm.2 h_res_rc).1
    unfold CasmStateVal.strongly_bounded at cs_bound
    exact (h_res_as_rel_imm.2 h_res_rc).2 num_steps ns_lim casmStateVal.ap cs_bound.1
  -- next fp
  constructor
  · revert h_ρcasmStateVal h_fp_update_regular_eq h_dst_as_addr
    revert h_fp_update_regular_atMost
    simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OPCODE_RET_INDEX, h_opcodeRet, FLAG_OPCODE_ASSERT_EQ_INDEX, h_opcodeAssertEq]
    cases instr.opcodeCall
    · cases instr.opcodeRet
      · simp [Bool.toFelt]
        intro _ _ h3 h4
        cases instr.opcodeAssertEq <;> simp [h4] at h3 <;> simp [h3]
      simp [Bool.toFelt]
      intro _ h2 h3 h4
      simp [h4] at h3
      cases instr.opcodeAssertEq <;> simp [h3]
      use h2.1
      unfold CondFelt252AsAddr.spec at h2 ; simp at h2
      rw [←h2.1] ; exact h2.2.1 (EvalOperands.dst_IsRangeChecked_of_spec memChecked h_eval_dst)
    intro h1
    unfold DecodeGenericInstruction.atMostOneTrue at h1 ; simp at h1
    simp [h1, Bool.toFelt]
    intro h2 h3 h4
    simp [h4] at h3
    cases instr.opcodeAssertEq <;> simp [h3]
  · rw [h_ρcasmStateVal]
    simp
    use dst_as_addr
    constructor
    · exact h_dst_as_addr
    constructor
    · rfl
set_option maxHeartbeats 300000 in
theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    --{num_steps: Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (airBuilder : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (casmState : CasmState)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (dst op0 op1 res : Felt252Expr)
    (num_steps: Nat):
    let state := call airBuilder lt casmState flags dst op1 res
    let new_ab := state.1
    let new_lt := state.2.1
    let ρcasmState := state.2.2
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      airBuilder.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      (DecodeGenericInstruction.spec memAssign
        (CasmState.eval varAssign casmState).pc
        (signed_as_offset_Felt (offset0.eval varAssign))
        (signed_as_offset_Felt (offset1.eval varAssign))
        (signed_as_offset_Felt (offset2.eval varAssign))
        (fun i => (flags i).eval varAssign) →
        EvalOperands.spec memAssign
          (casmState.eval varAssign)
          (offset0.eval varAssign)
          (offset1.eval varAssign)
          (offset2.eval varAssign)
          (fun i => (flags i).eval varAssign)
          (dst.eval varAssign)
          (op0.eval varAssign)
          (op1.eval varAssign)
          (res.eval varAssign) →
            spec
              (casmState.eval varAssign)
              (fun i => (flags i).eval varAssign)
              (dst.eval varAssign)
              (op1.eval varAssign)
              (res.eval varAssign)
              (ρcasmState.eval varAssign)
              (num_steps) -- ?
      ) := by
  unfold call; lift_lets

  intro instrFlags
    state1 ab1 res_as_addr
    state2 ab2 dst_as_addr
    state3 ab3 res_as_rel_imm
    dst_sum_squares
    state4 ab4 sum_squares_inv
    ab5 dst_sum
    state5 ab6 dst_is_zero
    state6 ab7 sum_inv
    state7 ab8 op1_as_rel_imm_condition
    state8 ab9 op1_as_rel_imm
    state9 ab10 npc_jnz ab11 ab12
    next_pc₀ state10 ab13 next_pc
    next_ap₀ state11 ab14 next_ap
    state13 ab15 lt1
    next_fp₀ state12 ab16 next_fp
    state14 new_ab new_lt ρcasmState

  intro hab16 hlt1
  have ⟨hab15, h_next_fp⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab16
  have ⟨hab14, hlt, h_next_ap_rc⟩ := RangeCheckAP.sound_auto varAssign _ _ _ h_rc next_ap hab15 hlt1 --
  have ⟨hab13, h_next_ap⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab14
  have ⟨hab12, h_next_pc⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab13
  have ⟨hab11, h_jnz2⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab12
  have ⟨hab10, h_jnz1⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab11
  have hab9 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab10
  have ⟨hab8, h_op1_as_rel_imm⟩ := CondFelt252AsRelImm.sound_auto varAssign _ _ _ hab9
  have ⟨hab7, h_op1_as_rel_imm_condition⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab8
  have hab6 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab7
  have hab5 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab6
  have ⟨hab4, h_dst_sum⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
  have hab3 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab4
  have ⟨hab2, h_res_as_rel_imm⟩ := CondFelt252AsRelImm.sound_auto varAssign _ _ _ hab3
  have ⟨hab1, h_dst_as_addr⟩ := CondFelt252AsAddr.sound_auto varAssign _ _ _ hab2
  have ⟨hab, h_res_as_addr⟩ := CondFelt252AsAddr.sound_auto varAssign _ _ _ hab1

  use hab, hlt
  intro h_decode_spec h_EvalOperands_spec
  let memChecked := AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  apply spec_of_spec_auto memChecked _ h_decode_spec h_EvalOperands_spec
  use res_as_addr.eval varAssign, h_res_as_addr
  use dst_as_addr.eval varAssign, h_dst_as_addr
  use res_as_rel_imm.eval varAssign, h_res_as_rel_imm
  use sum_squares_inv.eval varAssign
  constructor
  · unfold dst_sum_squares at h_dst_sum
    simp only [FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const, Felt252Expr.eval_of_limb_sum_squares] at h_dst_sum
    exact h_dst_sum
  use op1_as_rel_imm.eval varAssign
  constructor
  · simp [op1_as_rel_imm_condition, state7, h_op1_as_rel_imm_condition,
      dst_sum, Felt252Expr.eval_of_limb_sum] at h_op1_as_rel_imm
    exact h_op1_as_rel_imm
  use sum_inv.eval varAssign, npc_jnz.eval varAssign
  constructor
  · simp only [dst_sum, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_add, Felt252Expr.eval_of_limb_sum] at h_jnz1
    exact h_jnz1
  constructor
  · simp only [dst_sum, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_add, Felt252Expr.eval_of_limb_sum] at h_jnz2
    exact h_jnz2
  constructor
  · simp
    have : FeltExpr.eval varAssign (flags (Fin.castLE call._proof_1 FLAG_AP_UPDATE_ADD_INDEX)) = FeltExpr.eval varAssign (instrFlags FLAG_AP_UPDATE_ADD_INDEX) := by
      rfl
    rw[this]
    have : FeltExpr.eval varAssign (flags (Fin.castLE call._proof_1 FLAG_AP_UPDATE_ADD_1_INDEX)) = FeltExpr.eval varAssign (instrFlags FLAG_AP_UPDATE_ADD_1_INDEX) := by
      rfl
    rw[this]
    have : FeltExpr.eval varAssign (flags (Fin.castLE call._proof_1 FLAG_OPCODE_CALL_INDEX)) = FeltExpr.eval varAssign (instrFlags FLAG_OPCODE_CALL_INDEX) := by
      rfl
    rw[this]
    have : (CasmState.eval varAssign casmState).ap = FeltExpr.eval varAssign casmState.ap := by
      rfl
    rw[this]
    have this := h_next_ap
    unfold AirBuilder.assign at this
    simp only [FeltExpr.eval_add, FeltExpr.eval_mul, FeltExpr.eval_const, next_ap₀] at this
    rw[mul_one] at this
    rw[← this]
    exact h_next_ap_rc
  simp only [ρcasmState, state14, next_pc, next_ap, next_fp, state10, state11, state12, CasmState.eval]
  simp only [h_next_pc, h_next_ap, h_next_fp, next_pc₀, next_ap₀, next_fp₀]
  rfl

end UpdateRegisters
