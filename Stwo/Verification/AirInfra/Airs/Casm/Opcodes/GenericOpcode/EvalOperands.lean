import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.DecodeGenericInst
import Verification.AirInfra.Airs.Felt252Utils.CondAsSmall
import Verification.AirInfra.Airs.Felt252Utils.Add252
import Verification.AirInfra.Airs.Felt252Utils.Mul252

open Fin.NatCast

namespace EvalOperands


def call [Fact (Nat.Prime Stwo.P)]
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState)
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (offset0 offset1 offset2 : FeltExpr) :
    AirBuilder × AirLookupTerms × Felt252Expr × Felt252Expr × Felt252Expr × Felt252Expr :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  let dst_src₀ := instrFlags FLAG_DST_BASE_FP_INDEX * casmState.fp
    + (FeltExpr.const 1 - instrFlags FLAG_DST_BASE_FP_INDEX) * casmState.ap
  let _state := airBuilder.assign dst_src₀
  let ab1 := _state.1
  let dst_src := _state.2
  let _state := Felt252IdMemory.read_felt252 ab1 lookupTerms (dst_src + offset0)
  let ab2 := _state.1
  let lt1 := _state.2.1
  let dst := _state.2.2
  let op0_src₀ := instrFlags FLAG_OP0_BASE_FP_INDEX * casmState.fp
    + (FeltExpr.const 1 - instrFlags FLAG_OP0_BASE_FP_INDEX) * casmState.ap
  let _state := ab2.assign op0_src₀
  let ab3 := _state.1
  let op0_src := _state.2
  let _state := Felt252IdMemory.read_felt252 ab3 lt1 (op0_src + offset1)
  let ab4 := _state.1
  let lt2 := _state.2.1
  let op0 := _state.2.2
  let _state := CondFelt252AsAddr.call ab4 op0 (flags FLAG_OP1_BASE_OP0_INDEX)
  let ab5 := _state.1
  let op0_as_addr := _state.2
  let op1_src₀ := instrFlags FLAG_OP1_BASE_FP_INDEX * casmState.fp
      + instrFlags FLAG_OP1_BASE_AP_INDEX * casmState.ap
      + instrFlags FLAG_OP1_IMM_INDEX * casmState.pc
      + flags FLAG_OP1_BASE_OP0_INDEX * op0_as_addr
  let _state := ab5.assign op1_src₀
  let ab6 := _state.1
  let op1_src := _state.2
  let _state := Felt252IdMemory.read_felt252 ab6 lt2 (op1_src + offset2)
  let ab7 := _state.1
  let lt3 := _state.2.1
  let op1 := _state.2.2
  let _state := Add252.call ab7 lt3 op0 op1
  let ab8 := _state.1
  let lt4 := _state.2.1
  let sum := _state.2.2
  let _state := Mul252.call ab8 lt4 op0 op1
  let ab9 := _state.1
  let lt5 := _state.2.1
  let prod := _state.2.2
  let _state := ab9.deduce252
  let ab10 := _state.1
  let res := _state.2
  let _state := ab10.letForConstraint ((FeltExpr.const 1) - instrFlags FLAG_PC_UPDATE_JNZ_INDEX)
  let ab11 := _state.1
  let res_constrained := _state.2
  let ab12 := forLoop 0 FELT252_N_WORDS ab11
      fun i ab => ab.constrain
        (res_constrained
          * (
            flags FLAG_RES_OP1_INDEX * (res i - op1 i)
            + instrFlags FLAG_RES_ADD_INDEX * (res i - sum i)
            + instrFlags FLAG_RES_MUL_INDEX * (res i - prod i)
          ))
  (ab12, lt5, dst, op0, op1, res)

def spec_auto [Fact (Nat.Prime Stwo.P)]
    (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (offset0 offset1 offset2 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρdst ρop0 ρop1 ρres: Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  let dst_src := instrFlags FLAG_DST_BASE_FP_INDEX * casmStateVal.fp
    + (1 - instrFlags FLAG_DST_BASE_FP_INDEX) * casmStateVal.ap
  Felt252IdMemory.read_felt252.spec memAssign (dst_src + offset0) ρdst ∧
  let op0_src := instrFlags FLAG_OP0_BASE_FP_INDEX * casmStateVal.fp
    + (1 - instrFlags FLAG_OP0_BASE_FP_INDEX) * casmStateVal.ap
  Felt252IdMemory.read_felt252.spec memAssign (op0_src + offset1) ρop0 ∧
  ∃ op0_as_addr, CondFelt252AsAddr.spec ρop0 (flags FLAG_OP1_BASE_OP0_INDEX) op0_as_addr ∧
    let op1_src := instrFlags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp
      + instrFlags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap
      + instrFlags FLAG_OP1_IMM_INDEX * casmStateVal.pc
      + flags FLAG_OP1_BASE_OP0_INDEX * op0_as_addr
    Felt252IdMemory.read_felt252.spec memAssign (op1_src + offset2) ρop1 ∧
    ∃ sum, Add252.spec ρop0 ρop1 sum ∧
      ∃ prod, Mul252.spec ρop0 ρop1 prod ∧
        let res_constrained := 1 - instrFlags FLAG_PC_UPDATE_JNZ_INDEX
        ∀ i : Fin FELT252_N_WORDS,
          res_constrained
            * ((flags FLAG_RES_OP1_INDEX * (ρres i - ρop1 i))
                + instrFlags FLAG_RES_ADD_INDEX * (ρres i - sum i)
                + instrFlags FLAG_RES_MUL_INDEX * (ρres i - prod i)) = 0

def dst_spec (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (offset0 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρdst : Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  memAssign.HasValue ((if instrFlags FLAG_DST_BASE_FP_INDEX ≠ 0 then casmStateVal.fp else casmStateVal.ap) + offset0) ρdst

def op0_spec (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (offset1 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρop0 : Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  memAssign.HasValue ((if instrFlags FLAG_OP0_BASE_FP_INDEX ≠ 0 then casmStateVal.fp else casmStateVal.ap) + offset1) ρop0
  ∧ ((flags FLAG_OP1_BASE_OP0_INDEX) ≠ 0 → (felt252_to_m31_val ρop0 ADDRESS_BITS).toFelt252 = ρop0.eval)

def op1_spec
    (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (offset2 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρop0 ρop1: Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  match (instrFlags FLAG_OP1_IMM_INDEX), (instrFlags FLAG_OP1_BASE_FP_INDEX), (instrFlags FLAG_OP1_BASE_AP_INDEX) with
    | 0, 0, 0 => memAssign.HasValue ((felt252_to_m31_val ρop0 ADDRESS_BITS) + offset2) ρop1
    | _, 0, 0 => memAssign.HasValue (casmStateVal.pc + offset2) ρop1
    | 0, _, 0 => memAssign.HasValue (casmStateVal.fp + offset2) ρop1
    | 0, 0, _ => memAssign.HasValue (casmStateVal.ap + offset2) ρop1
    | _, _, _ => False

def res_spec [Fact (Nat.Prime Stwo.P)]
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρop0 ρop1 ρres : Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  match (flags FLAG_RES_OP1_INDEX), (instrFlags FLAG_RES_ADD_INDEX), (instrFlags FLAG_RES_MUL_INDEX) with
    | _, 0, 0 => ρres = ρop1
    | 0, _, 0 => Add252.spec ρop0 ρop1 ρres
    | 0, 0, _ => Mul252.spec ρop0 ρop1 ρres
    | _, _, _ => False

def spec [Fact (Nat.Prime Stwo.P)]
    (memAssign : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (offset0 offset1 offset2 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt)
    (ρdst ρop0 ρop1 ρres: Felt252Words) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  dst_spec memAssign casmStateVal offset0 flags ρdst ∧
  --memAssign.HasValue ((if instrFlags FLAG_DST_BASE_FP_INDEX ≠ 0 then casmStateVal.fp else casmStateVal.ap) + offset0) ρdst ∧
  op0_spec memAssign casmStateVal offset1 flags ρop0 ∧
  -- YS: This can probably be removed, as it is contained in the following op1_spec.
  (flags FLAG_OP1_BASE_OP0_INDEX ≠ 0 → memAssign.HasValue ((felt252_to_m31_val ρop0 ADDRESS_BITS) + offset2) ρop1) ∧
  op1_spec memAssign casmStateVal offset2 flags ρop0 ρop1 ∧
  (instrFlags FLAG_PC_UPDATE_JNZ_INDEX = 0 → res_spec flags ρop0 ρop1 ρres)

lemma dst_IsRangeChecked_of_spec
      {memAssign : Felt252IdMemoryAssign}
      {casmStateVal : CasmStateVal}
      {offset0 : Felt}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      {ρdst : Felt252Words}
      (memChecked: memAssign.IsRangeChecked)
      (h : dst_spec memAssign casmStateVal offset0 flags ρdst) :
    Felt252Nats.ExistsIsRangeChecked ρdst := by
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  unfold Felt252Nats.ExistsIsRangeChecked
  unfold dst_spec at h ; dsimp at h
  revert h
  by_cases h0 : (instrFlags FLAG_OP0_BASE_FP_INDEX) = 0 <;>
  simp <;>
  intro h <;>
  apply Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h

lemma op0_IsRangeChecked_of_spec
      {memAssign : Felt252IdMemoryAssign}
      {casmStateVal : CasmStateVal}
      {offset1 : Felt}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      {ρop0 : Felt252Words}
      (memChecked: memAssign.IsRangeChecked)
      (h : op0_spec memAssign casmStateVal offset1 flags ρop0) :
    Felt252Nats.ExistsIsRangeChecked ρop0 := by
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  unfold Felt252Nats.ExistsIsRangeChecked
  unfold op0_spec at h ; dsimp at h
  revert h
  by_cases h0 : (instrFlags FLAG_OP0_BASE_FP_INDEX) = 0 <;>
  simp <;>
  intro h _ <;>
  apply Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h

lemma op1_IsRangeChecked_of_spec
      {memAssign : Felt252IdMemoryAssign}
      {casmStateVal : CasmStateVal}
      {offset2 : Felt}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      {ρop0 ρop1: Felt252Words}
      (memChecked: memAssign.IsRangeChecked)
      (h : op1_spec memAssign casmStateVal offset2 flags ρop0 ρop1) :
    Felt252Nats.ExistsIsRangeChecked ρop1 := by
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  unfold Felt252Nats.ExistsIsRangeChecked
  unfold op1_spec at h ; dsimp at h
  revert h
  by_cases h0 : (instrFlags FLAG_OP1_IMM_INDEX) = 0 <;>
  by_cases h1 : (instrFlags FLAG_OP1_BASE_FP_INDEX) = 0 <;>
  by_cases h2 : (instrFlags FLAG_OP1_BASE_AP_INDEX) = 0 <;>
  unfold instrFlags at h0 h1 h2 <;>
  simp [h0, h1, h2] <;>
  intro h <;>
  apply Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h

lemma res_IsRangeChecked_of_spec [Fact (Nat.Prime Stwo.P)]
      {memAssign : Felt252IdMemoryAssign}
      {casmStateVal : CasmStateVal}
      {offset2 : Felt}
      {flags : Fin GENERIC_FLAGS_SIZE → Felt}
      {ρop0 ρop1 ρres : Felt252Words}
      (memChecked: memAssign.IsRangeChecked)
      (h_op1 : op1_spec memAssign casmStateVal offset2 flags ρop0 ρop1)
      (h_res : res_spec flags ρop0 ρop1 ρres) :
    Felt252Nats.ExistsIsRangeChecked ρres := by
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  unfold Felt252Nats.ExistsIsRangeChecked
  -- unfold op1_spec at h ; dsimp at h
  unfold res_spec at h_res ; dsimp at h_res
  revert h_res
  by_cases h0 : (flags FLAG_RES_OP1_INDEX) = 0 <;>
  by_cases h1 : (instrFlags FLAG_RES_ADD_INDEX) = 0 <;>
  by_cases h2 : (instrFlags FLAG_RES_MUL_INDEX) = 0 <;>
  unfold instrFlags at h1 h2 <;>
  simp [h0, h1, h2] <;>
  intro h
  · rw [h] ; exact op1_IsRangeChecked_of_spec memChecked h_op1
  · apply RangeCheckMemValue.IsRangeChecked_of_spec h.1
  · apply RangeCheckMemValue.IsRangeChecked_of_spec h.1
  rw [h] ; exact op1_IsRangeChecked_of_spec memChecked h_op1

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    {memAssign : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {offset0 offset1 offset2 : Felt}
    {flags : Fin GENERIC_FLAGS_SIZE → Felt}
    {ρdst ρop0 ρop1 ρres: Felt252Words}
    (memChecked : memAssign.IsRangeChecked)
    (h_spec_auto : spec_auto memAssign casmStateVal offset0 offset1 offset2 flags ρdst ρop0 ρop1 ρres)
    -- To prove the spec from spec_auto, we also assume the spec of DecodeGenericInstruction
    (h_decode_spec : DecodeGenericInstruction.spec memAssign casmStateVal.pc
      (signed_as_offset_Felt offset0) (signed_as_offset_Felt offset1) (signed_as_offset_Felt offset2) flags) :
    spec memAssign casmStateVal offset0 offset1 offset2 flags ρdst ρop0 ρop1 ρres := by
  rcases h_spec_auto with ⟨h_dst_read, h_op0_read, op0_as_addr, h_op0_as_addr, h_op1_read, sum, h_sum, prod, h_prod, h_res⟩
  rcases h_decode_spec with ⟨instr, h_hasInstr, h_offDst, h_offOp0, h_dstOp1,
    h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq,
    h_op1_base_op0_atMost, h_op1_base_op0_eq, h_res_op1_atMost, h_res_op1_eq, h_pc_update_regular_atMost, h_pc_update_regular_eq,
    h_ap_update_regular, h_fp_update_regular_atMost, h_fp_update_regular_eq, h_instr_size⟩

  constructor
  · unfold dst_spec
    revert h_dst_read
    simp only [FLAG_DST_BASE_FP_INDEX , h_dstReg]
    cases instr.dstReg <;> simp [Bool.toFelt] <;> intro h <;> exact h
  constructor
  · revert h_op0_read
    unfold op0_spec
    simp only [FLAG_OP0_BASE_FP_INDEX, h_op0Reg]
    cases instr.op0Reg
    all_goals {
      simp [Bool.toFelt] ; intro h ; use h
      intro h_ne
      rw [←h_op0_as_addr.1]
      apply (h_op0_as_addr.2 h_ne).1
      apply Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h
    }
  constructor
  · revert h_op1_read h_op0_as_addr
    simp only [FLAG_OP1_BASE_FP_INDEX, h_op1Fp, FLAG_OP1_BASE_AP_INDEX, h_op1Ap, FLAG_OP1_IMM_INDEX, h_op1Imm, h_op1_base_op0_eq]
    cases instr.op1Fp <;> cases instr.op1Ap <;> cases instr.op1Imm <;> simp [Bool.toFelt]
    intro h1 h2
    rw [h1.1] at h2
    exact h2
  constructor
  · unfold op1_spec
    revert h_op1_read h_op0_as_addr
    revert h_op1_base_op0_atMost
    simp only [FLAG_OP1_BASE_FP_INDEX, h_op1Fp, FLAG_OP1_BASE_AP_INDEX, h_op1Ap, FLAG_OP1_IMM_INDEX, h_op1Imm, h_op1_base_op0_eq]
    cases instr.op1Imm
    · cases instr.op1Fp
      · cases instr.op1Ap
        · simp [Bool.toFelt] ; intro h1 h2 h3 ; rw [h2.1] at h3 ; exact h3
        simp [Bool.toFelt] ; intro h1 h2 h3 ; exact h3
      simp [Bool.toFelt]
      intro h1 ; unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1
      simp [h1] ; intro h2 h3 ; exact h3
    simp [Bool.toFelt]
    intro h1 ; unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1
    simp [h1.1, h1.2] ; intro h2 h3 ; exact h3
  · unfold res_spec
    revert h_res
    revert h_res_op1_atMost
    simp only [FLAG_RES_ADD_INDEX, h_resAdd, FLAG_RES_MUL_INDEX, h_resMul, FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz, h_res_op1_eq]
    cases instr.pcJnz
    · cases instr.resAdd
      · cases instr.resMul
        · simp [Bool.toFelt] ; intro h1 h2 ; apply funext ; simp only [sub_eq_zero] at h2 ; exact h2
        simp [Bool.toFelt] ; intro h1 h2 ; simp only [sub_eq_zero] at h2 ; rw [funext h2] ; exact h_prod
      intro h1 ; unfold DecodeGenericInstruction.atMostOneTrue3 at h1 ; simp at h1
      simp [h1, Bool.toFelt] ; intro h2 ; simp only [sub_eq_zero] at h2 ; rw [funext h2] ; exact h_sum
    intro h1 h2 h3 ; simp [Bool.toFelt] at h3

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
    (flags : Fin GENERIC_FLAGS_SIZE → FeltExpr)
    (offset0 offset1 offset2 : FeltExpr) :
    let state := call airBuilder lt casmState flags offset0 offset1 offset2
    let new_ab := state.1
    let new_lt := state.2.1
    let dst := state.2.2.1
    let op0 := state.2.2.2.1
    let op1 := state.2.2.2.2.1
    let res := state.2.2.2.2.2
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
          spec memAssign
            (casmState.eval varAssign)
            (offset0.eval varAssign)
            (offset1.eval varAssign)
            (offset2.eval varAssign)
            (fun i => (flags i).eval varAssign)
            (dst.eval varAssign)
            (op0.eval varAssign)
            (op1.eval varAssign)
            (res.eval varAssign)
      ) := by
  unfold call; lift_lets
  intro instrFlags
    dst_src₀ state1 ab1 dst_src state2 ab2 lt1 dst
    op0_src₀ state3 ab3 op0_src state4 ab4 lt2 op0 state5 ab5 op0_as_addr
    op1_src₀ state6 ab6 op1_src state7 ab7 lt3 op1
    state8 ab8 lt4 sum
    state9 ab9 lt5 prod
    state10 ab10 res
    state11 ab11 res_constrained ab12
    state12 new_ab new_lt _ _ _ _
  intro hab12 hlt5

  have ⟨hab11, h_res_eq⟩ := (AirBuilder.constraint_loop_SatisfiedBy _ varAssign _ _ (by norm_num) _).mp hab12
  have ⟨hab10, h_res_constrained⟩ := (AirBuilder.letForConstraint_SatisfiedBy _ _ varAssign).mp hab11
  have hab9 := (AirBuilder.deduce252_SatisfiedBy _ varAssign).mp hab10
  have ⟨hab8, hlt4, h_mul⟩ := Mul252.sound_auto varAssign _ _ _ h_rc op0 op1 hab9 hlt5
  have ⟨hab7, hlt3, h_add⟩ := Add252.sound_auto varAssign _ _ _ h_rc op0 op1 hab8 hlt4
  have ⟨hab6, hlt2, h_read_op1⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab6 _ _ h_rc h_mem.1 (op1_src + offset2) hab7 hlt3
  have ⟨hab5, h_op1_src⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab6
  have ⟨hab4, h_cond_small⟩ := CondFelt252AsAddr.sound_auto _ _ op0 (flags FLAG_OP1_BASE_OP0_INDEX) hab5
  have ⟨hab3, hlt1, h_read_op0⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab3 _ _ h_rc h_mem.1 (op0_src + offset1) hab4 hlt2
  have ⟨hab2, h_op0_src⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, hlt, h_read_dst⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab1 _ _ h_rc h_mem.1 (dst_src + offset0) hab2 hlt1
  have ⟨hab, h_dst_src⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab1

  use hab, hlt
  intro h_decode_spec
  apply spec_of_spec_auto (AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem) _ h_decode_spec

  constructor
  · simp [CasmState.eval]
    simp only [dst_src, state1, h_dst_src, FeltExpr.eval_add] at h_read_dst
    simp only [dst_src₀, instrFlags, FeltExpr.eval_add, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const] at h_read_dst
    exact h_read_dst
  constructor
  · simp [CasmState.eval]
    simp only [op0_src, state3, h_op0_src, FeltExpr.eval_add] at h_read_op0
    simp only [op0_src₀, instrFlags, FeltExpr.eval_add, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const] at h_read_op0
    exact h_read_op0
  use op0_as_addr.eval varAssign
  constructor
  · simp only [op0_as_addr]
    exact h_cond_small
  constructor
  · simp [CasmState.eval]
    simp only [op1_src, state6, h_op1_src, FeltExpr.eval_add] at h_read_op1
    simp only [op1_src₀, instrFlags, FeltExpr.eval_add,  FeltExpr.eval_mul] at h_read_op1
    exact h_read_op1
  use (fun i => (sum i).eval varAssign), h_add
  use (fun i => (prod i).eval varAssign), h_mul
  simp only
  intro i
  replace h_res_eq := h_res_eq i.val (Nat.zero_le i.val) (i.isLt)
  simp only [
    res_constrained, state11, h_res_constrained, instrFlags,
    FeltExpr.eval_add, FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const,
    Fin.cast_val_eq_self
  ] at h_res_eq
  exact h_res_eq

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {casmState : CasmState}
      {flags : Fin GENERIC_FLAGS_SIZE → FeltExpr}
      {offset0 offset1 offset2 : FeltExpr} :
    AirLookupTerms.NoYieldTerms (call ab lt casmState flags offset0 offset1 offset2).2.1 := by
  apply Mul252.NoYieldTerms_of_call
  apply Add252.NoYieldTerms_of_call
  repeat
    simp ; apply AirLookupTerms.add'_NoYieldTerms.mpr
  simp [h]

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {casmState : CasmState}
      {flags : Fin GENERIC_FLAGS_SIZE → FeltExpr}
      {offset0 offset1 offset2 : FeltExpr} :
    AirLookupTerms.NoTermsOfRel (call ab lt casmState flags offset0 offset1 offset2).2.1 OPCODE_TRACE_REL_INDEX := by
  apply Mul252.NoTermsOfRel_OPCODE_TRACE_of_call
  apply Add252.NoTermsOfRel_OPCODE_TRACE_of_call
  repeat
    simp [MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, OPCODE_TRACE_REL_INDEX] ;
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
  simp_all [MEMORY_ADDR_TO_ID_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {casmState : CasmState}
      {flags : Fin GENERIC_FLAGS_SIZE → FeltExpr}
      {offset0 offset1 offset2 : FeltExpr} :
    AirLookupTerms.RelInRelTuples (call ab lt casmState flags offset0 offset1 offset2).2.1 := by
  apply Mul252.RelInRelTuples_of_call
  apply Add252.RelInRelTuples_of_call
  repeat
    simp [Felt252IdMemory.read_felt252] ; apply AirLookupTerms.add'_RelInRelTuple.mpr
  apply ReadPositive.RelInRelTuples_of_call
  apply ReadPositive.RelInRelTuples_of_call
  simp [h]

end EvalOperands
