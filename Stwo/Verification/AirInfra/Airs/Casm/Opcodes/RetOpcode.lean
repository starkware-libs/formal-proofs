
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst
import Verification.AirInfra.Airs.Casm.Opcodes.Util

def RET_FLAGS : Flags where
  dst_base_fp := some true
  op0_base_fp := some true
  op1_imm := some false
  op1_base_fp := some true
  op1_base_ap := some false
  res_add := some false
  res_mul := some false
  pc_update_jump := some true
  pc_update_jump_rel := some false
  pc_update_jnz := some false
  ap_update_add := some false
  ap_update_add_1 := some false
  opcode_call := some false
  opcode_ret := some true
  opcode_assert_eq := some false

namespace RetOpcode

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=
  let state1 := DecodeInstruction.call airBuilder lookupTerms
    (some (-2)) (some (-1)) (some (-1)) RET_FLAGS casmState.pc
  let ab1 := state1.1
  let lt1 := state1.2.1
  let state2 := Felt252IdMemory.read_address ab1 lt1 (casmState.fp - FeltExpr.const 1)
  let ab2 := state2.1
  let lt2 := state2.2.1
  let next_pc := state2.2.2
  let state3 := Felt252IdMemory.read_address ab2 lt2 (casmState.fp - FeltExpr.const 2)
  let ab3 := state3.1
  let lt3 := state3.2.1
  let next_fp := state3.2.2
  (ab3, lt3, ⟨next_pc, casmState.ap, next_fp⟩)

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (some (-2)) (some (-1)) (some (-1)) RET_FLAGS
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
  ∃ (next_pc : CasmAddressVal),
    Felt252IdMemory.read_address.spec memory (casmStateVal.fp - 1) next_pc ∧
  ∃ (next_fp : CasmAddressVal),
    Felt252IdMemory.read_address.spec memory (casmStateVal.fp - 2) next_fp ∧
    ρCasmStateVal = ⟨next_pc, casmStateVal.ap, next_fp⟩

def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat) : Prop :=
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
    memory.Agrees mem →
      mem (casmStateVal.pc.toFelt252) = retInstr.toInstruction.toNat ∧
      retInstr.toInstruction.NextState mem
        casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))

theorem spec_of_spec_auto [Fact (Nat.Prime Felt252Prime)][Fact (Nat.Prime Stwo.P)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal) :
    spec memory casmStateVal ρCasmStateVal num_steps := by
  intro ns_lim cs_bound
  rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode,
    next_pc, hnext_pc, next_fp, hnext_fp, rfl⟩
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hoffset0 hoffset1 hoffset2 hflags
  rcases hverifyInstruction with ⟨instr, hinstr1, hinstr2⟩
  rcases hinstr1 with ⟨instr252, hinstr252a, hinstr252b⟩
  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩
  rw [hoffset0, hoffset1] at hinstr2
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr2
  dsimp [OFFSET_BITS] at hinstr2
  dsimp [RET_FLAGS, Flags.to_arr] at hflags
  rw [hflags 0, hflags 1, hflags 2, hflags 3, hflags 4, hflags 5, hflags 6, hflags 7, hflags 8,
      hflags 9, hflags 10, hflags 11, hflags 12, hflags 13, hflags 14] at hinstr2
  simp only [Bool.toFelt_inj] at hinstr2
  rcases hinstr2 with ⟨h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp only [CasmStateVal.strongly_bounded]
    constructor
    · use ap_nat
      constructor
      · linarith
      · exact h_ap_nat
    · have : 1=1 := by rfl
      rcases Felt252IdMemory.read_address.read_address_rc memChecked hnext_fp with ⟨nfp, nfp_lt, nfp_eq⟩
      use nfp
      constructor
      · linarith
      · exact nfp_eq

  intro mem hmem
  rw [hmem.2 _ _ _ hinstr252a hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]
  constructor
  . apply congr_arg ; apply congr_arg
    simp only [retInstr, Instr.toInstruction]
    rw [Instruction.ext_iff]
    simp only [←h_offDst, ←h_offOp0, ←h_dstReg, ←h_op0Reg, ←h_op1Imm,
      ←h_op1Fp, ←h_op1Ap, ←h_resAdd, ←h_resMul, ←h_pcJumpAbs, ←h_pcJumpRel, ←h_pcJnz, ←h_apAdd, ←h_apAdd1, ←h_opcodeCall, ←h_opcodeRet, ←h_opcodeAssertEq, and_true, true_and, and_self,
      Int.reduceNeg, Int.reducePow, Int.reduceAdd, Int.reduceToNat]
    rw [←BitVec_toFelt_inj, ←h_dstOp1, hoffset2]
    simp [BitVec.as_u16, offset_as_u16, OFFSET_BITS]
  apply nextState_ret _ _ _ |>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]
  constructor
  . rcases hnext_pc with ⟨next_pc252, h_num_bits, hnext_pc252, rfl⟩
    rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked hnext_pc252 hmem with ⟨value_n, hpc1, hpc2⟩
    rcases memory.IsRangeChecked_address_of_HasValue memChecked hnext_pc252 with ⟨nfp, nfp_lt, nfp_eq⟩
    simp [felt252_to_m31_eq next_pc252 value_n h_num_bits hpc1, ←hpc2]
    apply congr_arg
    rw [sub_eq_iff_eq_add] at nfp_eq
    rw [nfp_eq, add_sub_cancel_right, ←Nat.cast_one, toFelt252_add]; simp
    apply lt_of_lt_of_le (add_lt_add_right nfp_lt _)
    simp [Stwo.P]
  use rfl
  . rcases hnext_fp with ⟨next_fp252, h_num_bits, hnext_fp252, rfl⟩
    rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked hnext_fp252 hmem with ⟨value_n, hpc1, hpc2⟩
    rcases memory.IsRangeChecked_address_of_HasValue memChecked hnext_fp252 with ⟨nfp, nfp_lt, nfp_eq⟩
    simp [felt252_to_m31_eq next_fp252 value_n h_num_bits hpc1, ←hpc2]
    apply congr_arg
    rw [sub_eq_iff_eq_add] at nfp_eq
    rw [nfp_eq, add_sub_cancel_right, ←Nat.cast_two, toFelt252_add]; simp
    apply lt_of_lt_of_le (add_lt_add_right nfp_lt _)
    simp [Stwo.P]

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
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) num_steps := by
  unfold call; lift_lets
  intro state1 ab1 lt1 state2 ab2 lt2 next_pc state3 ab3 lt3 next_fp
  intro hab3 hlt3
  have ⟨hab2, hlt2, hread_address2⟩ := Felt252IdMemory.read_address.sound_auto
    varAssign memAssign ab2 lt2 h_satisfied h_rc h_mem.1 (casmState.fp - FeltExpr.const 2) hab3 hlt3
  have ⟨hab1, hlt1, hread_address1⟩ := Felt252IdMemory.read_address.sound_auto
    varAssign memAssign ab1 lt1 h_satisfied h_rc h_mem.1 (casmState.fp - FeltExpr.const 1) hab2 hlt2
  have ⟨hab, hlt, hh⟩ := DecodeInstruction.sound_auto memAssign varAssign ab lt h_satisfied h_rc h_mem h_verify_instr
    (some (-2)) (some (-1)) (some (-1)) RET_FLAGS casmState.pc hab1 hlt1
  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_
  constructor
  . exact hh
  use next_pc.eval varAssign
  constructor
  . exact hread_address1
  use next_fp.eval varAssign
  constructor
  . exact hread_address2
  simp [CasmState.eval]

theorem sound_ret [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases h_step mem h_mem_agrees with ⟨h_instr, h_next⟩
  use retInstr.toInstruction
  use h_instr


end RetOpcode
