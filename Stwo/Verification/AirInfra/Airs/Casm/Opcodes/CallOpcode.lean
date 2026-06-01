
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst
import Verification.AirInfra.Airs.Casm.Opcodes.Util

set_option maxHeartbeats 800000
-- set_option maxHeartbeats 1000000

namespace CallOpcode

variable [Fact (Nat.Prime Stwo.P)]

def flag_op1_base_ap (is_rel op1_base_fp : Bool) := if is_rel then false else !op1_base_fp
def flag_assert (is_rel op1_base_fp : Bool) := is_rel = true → op1_base_fp = false

def CALL_FLAGS (is_rel op1_base_fp : Bool) : Flags where
  dst_base_fp := some false
  op0_base_fp := some false
  op1_imm := some is_rel
  op1_base_fp := some op1_base_fp
  op1_base_ap := some (flag_op1_base_ap is_rel op1_base_fp)
  res_add := some false
  res_mul := some false
  pc_update_jump := some !is_rel
  pc_update_jump_rel := some is_rel
  pc_update_jnz := some false
  ap_update_add := some false
  ap_update_add_1 := some false
  opcode_call := some true
  opcode_ret := some false
  opcode_assert_eq := some false

def call
    (is_rel op1_base_fp : Bool)
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=
  let offset2 := if is_rel then some 1 else none
  let _state := DecodeInstruction.call airBuilder lookupTerms
    (some 0) (some 1) offset2 (CALL_FLAGS is_rel op1_base_fp) casmState.pc
  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset2₁ := _state.2.2.2.2.1
  let stored_fp_address := casmState.ap
  let _state := Felt252IdMemory.read_address ab1 lt1 stored_fp_address
  let ab2 := _state.1
  let lt2 := _state.2.1
  let stored_fp := _state.2.2
  let ab3 := AirBuilder.constrain ab2 (stored_fp - casmState.fp)

  let stored_ret_pc_address := casmState.ap + FeltExpr.const 1
  let _state := Felt252IdMemory.read_address ab3 lt2 stored_ret_pc_address
  let ab4 := _state.1
  let lt3 := _state.2.1
  let stored_ret_pc := _state.2.2
  let return_pc := casmState.pc + FeltExpr.const (1 + (if is_rel then 1 else 0))
  let ab5 := AirBuilder.constrain ab4 (stored_ret_pc - return_pc)

  -- // Update pc.

  let _state := if is_rel then
        let _state := Felt252IdMemory.read_rel_imm ab5 lt3 (casmState.pc + FeltExpr.const 1)
        let ab6 := _state.1
        let lt4 := _state.2.1
        let distance_to_next_pc := _state.2.2
        (ab6, lt4, casmState.pc + distance_to_next_pc)
      else
        let mem1_base := if op1_base_fp then casmState.fp else casmState.ap
        Felt252IdMemory.read_address ab5 lt3 (mem1_base + offset2₁)

  let ab6 := _state.1
  let lt5 := _state.2.1
  let next_pc := _state.2.2

  (ab6, lt5, ⟨next_pc, casmState.ap + FeltExpr.const 2, casmState.ap + FeltExpr.const 2⟩)

def call_instr (is_rel op1_base_fp : Bool) (offset2 : Felt) : Instr :=
    callInstr
      (!is_rel)
      (ResSpec.op1
        (if is_rel then
            (Op1Spec.mem_pc_plus 1)
          else if op1_base_fp then
              (Op1Spec.mem_fp_plus (int_from_Felt offset2))
            else
              (Op1Spec.mem_ap_plus (int_from_Felt offset2))
        )
      )

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (is_rel op1_base_fp : Bool) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (some 0) (some 1) (if is_rel then some 1 else none) (CALL_FLAGS is_rel op1_base_fp)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ∃ (next_pc : CasmAddressVal),
      (if is_rel then
        ∃ distance_to_next_pc, Felt252IdMemory.read_rel_imm.spec memory (casmStateVal.pc + 1) distance_to_next_pc ∧
          next_pc = casmStateVal.pc + distance_to_next_pc
        else
          Felt252IdMemory.read_address.spec memory
            ((if op1_base_fp then casmStateVal.fp else casmStateVal.ap) + (offset_as_signed_Felt ρoffset2))
            next_pc
      ) ∧
      -- [ap+1] = pc + is_rel ? 2 : 1
      Felt252IdMemory.read_address.spec memory (casmStateVal.ap + 1) (casmStateVal.pc + 1 + (if is_rel then 1 else 0)) ∧
      -- [ap] = fp
      Felt252IdMemory.read_address.spec memory casmStateVal.ap casmStateVal.fp ∧
      ρCasmStateVal = ⟨next_pc, casmStateVal.ap + 2, casmStateVal.ap + 2⟩

def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (is_rel op1_base_fp : Bool)
    (num_steps: Nat) : Prop :=
  flag_assert is_rel op1_base_fp →
    num_steps < 2^29 →
    casmStateVal.strongly_bounded₀ num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (offset2 : Felt),
          mem (casmStateVal.pc.toFelt252) = (call_instr is_rel op1_base_fp offset2).toInstruction.toNat ∧
          (call_instr is_rel op1_base_fp offset2).toInstruction.NextState mem
            casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))

theorem spec_of_spec_auto [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {is_rel op1_base_fp : Bool}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal is_rel op1_base_fp) :
    spec memory casmStateVal ρCasmStateVal is_rel op1_base_fp num_steps := by

  intro h_flags_assert ns_lim /-special_condition-/ cs_bound
  rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, next_pc, hnext_pc, h_ret_pc, h_ret_fp, rfl⟩
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hoffset0 hoffset1 hoffset2 hflags
  rcases hverifyInstruction with ⟨instr, hinstr1, hinstr2⟩
  rcases hinstr1 with ⟨instr252, hinstr252a, hinstr252b⟩
  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a
  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩

  rw [hoffset0, hoffset1] at hinstr2
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr2
  dsimp [OFFSET_BITS] at hinstr2
  dsimp [CALL_FLAGS, Flags.to_arr] at hflags
  rw [hflags 0, hflags 1, hflags 2, hflags 3, hflags 4, hflags 5, hflags 6, hflags 7, hflags 8,
      hflags 9, hflags 10, hflags 11, hflags 12, hflags 13, hflags 14] at hinstr2
  simp only [Bool.toFelt_inj] at hinstr2
  rcases hinstr2 with ⟨h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  rcases h_ret_fp with ⟨ret_fp_252, h_num_bits_fp, h_ret_fp_252, h_ret_fp_as_m31⟩
  have ap_rc := memory.IsRangeChecked_address_of_HasValue memChecked h_ret_fp_252
  rcases (memory.IsRangeChecked_address_of_HasValue memChecked h_ret_fp_252) with ⟨ap_nat2, ap_bound2, h_ap_nat2⟩

  constructor
  · rw [h_ap_nat2, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt _, Nat.mod_eq_of_lt _] at h_ap_nat
    rotate_left
    · apply lt_trans ap_bound ; unfold Stwo.P
      by_cases h_z : num_steps = 0
      · rw [if_pos h_z] ; norm_num
      rw [if_neg h_z, ←add_assoc, Nat.sub_add_cancel (show 1 ≤ 2 ^ 29 by norm_num)]
      apply lt_of_lt_of_le (Nat.add_lt_add_left ns_lim _)
      norm_num
    · apply lt_trans ap_bound2 ; unfold Stwo.P ; norm_num
    dsimp only [CasmStateVal.strongly_bounded]
    constructor
    all_goals
    · use ap_nat2+2
      constructor
      · by_cases h_z : num_steps = 0
        · rw [h_z, zero_add, Nat.add_lt_iff_lt_sub_right, h_ap_nat]
          rw [if_pos h_z] at ap_bound
          apply lt_of_lt_of_le ap_bound
          norm_num1
        apply Nat.add_lt_add_of_lt_of_le ap_bound2 _
        apply Nat.succ_le_succ
        exact Nat.one_le_iff_ne_zero.mpr h_z
      · rw[Nat.cast_add, h_ap_nat2]
        rfl

  intro mem hmem
  rw [hmem.2 _ _ _ hinstr252a hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]
  use ρoffset2
  constructor
  · -- The instruction is in memory at pc
    apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [call_instr, callInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←h_offDst]
    · simp only [←h_offOp0]
    · simp only [←BitVec_toFelt_inj, ←h_dstOp1]
      cases is_rel
      · cases op1_base_fp <;> simp [h_dstOp1] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      cases op1_base_fp <;> simp at hoffset2 <;> simp [hoffset2] <;>
      unfold BitVec.as_u16 offset_as_u16 OFFSET_BITS <;> simp
    -- The flags
    · simp only [←h_dstReg]
    · simp only [←h_op0Reg]
    · simp only [←h_op1Imm]
      cases is_rel <;> cases op1_base_fp <;> simp
    · simp only [←h_op1Fp]
      cases is_rel <;> cases op1_base_fp <;> simp
      simp [flag_assert] at h_flags_assert
    · simp only [←h_op1Ap]
      cases is_rel <;> cases op1_base_fp <;> simp [flag_op1_base_ap]
    · simp only [←h_resAdd]
    · simp only [←h_resMul]
    · simp only [←h_pcJumpAbs]
    · simp [←h_pcJumpRel]
    · simp only [←h_pcJnz]
    · simp only [←h_apAdd]
    · simp only [←h_apAdd1]
    · simp only [←h_opcodeCall]
    · simp only [←h_opcodeRet]
    · simp only [←h_opcodeAssertEq]
  -- The next state is as defined by the semantics
  apply nextState_call _ _ _ _ !is_rel |>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]
  --
  -- rcases h_ret_fp with ⟨ret_fp_252, h_num_bits, h_ret_fp_252, h_ret_fp_as_m31⟩
  -- rcases h_ret_fp_tmp with ⟨ret_fp_252, h_num_bits_fp, h_ret_fp_252, h_ret_fp_as_m31⟩
  --
  rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked h_ret_fp_252 hmem with ⟨value_n, hfp1, hfp2⟩
  have ap_rc := memory.IsRangeChecked_address_of_HasValue memChecked h_ret_fp_252

  constructor
  · -- The pc is advanced correctly
    cases is_rel
    · simp at hnext_pc
      rcases hnext_pc with ⟨next_pc252, h_num_bits, hnext_pc252, h_nextpc_as_m31⟩
      simp only [h_nextpc_as_m31]
      rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked hnext_pc252 hmem with ⟨value_n, hpc1, hpc2⟩
      have offset_rc := memory.IsRangeChecked_address_of_HasValue memChecked hnext_pc252
      cases op1_base_fp <;> simp [felt252_to_m31_eq next_pc252 value_n h_num_bits hpc1, ←hpc2] <;> rw [h_dstOp1] <;>
      simp at offset_rc <;> rw [h_dstOp1] at offset_rc
      · rw [toFelt252_RangeChecked_add_offset_eq ap_rc]
      rw [toFelt252_RangeChecked_add_offset_eq _]
      rw [h_ret_fp_as_m31]
      exact felt252_to_m31_val_isRangeChecked hfp1 h_num_bits_fp
    simp at hnext_pc
    rcases hnext_pc with ⟨next_pc252, hnext_pc252, h_nextpc_as_m31⟩
    simp only [h_nextpc_as_m31]
    simp ; unfold intClip natClip ; simp ; norm_num
    rcases hnext_pc252 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
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

    let hvalue_n2 := hvalue_n
    unfold small_to_felt252_val at hvalue_n2
    have h_limb3 := hvalue_n2 3 ; simp at h_limb3

    exact Felt252IdMemory.val_add_eq_add_eval_of_small h_pc_eq h_pc_lt2 hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2

  constructor
  · exact toFelt252_add_of_RangeChecked 2 ap_rc (by simp [Stwo.P])
  constructor
  · exact toFelt252_add_of_RangeChecked 2 ap_rc (by simp [Stwo.P])
  constructor
  · rcases h_ret_pc with ⟨ret_pc_252, h_num_bits, h_ret_pc_252, h_ret_pc_as_m31⟩
    rcases memory.isRangeChecked_of_hasValue_of_agrees memChecked h_ret_pc_252 hmem with ⟨value_n, hret1, hret2⟩
    cases is_rel <;> simp at h_ret_pc_as_m31
    · cases op1_base_fp <;> simp [←toFelt252_add_one_of_RangeChecked ap_rc, ←toFelt252_add_one_of_RangeChecked pc_rc, hret2, h_ret_pc_as_m31] <;>
      exact (felt252_to_m31_eq ret_pc_252 value_n h_num_bits hret1).symm
    rw [add_assoc] at h_ret_pc_as_m31 ; norm_num at h_ret_pc_as_m31
    cases op1_base_fp <;> simp [←toFelt252_add_one_of_RangeChecked ap_rc, ←toFelt252_add_two_of_RangeChecked pc_rc, hret2, h_ret_pc_as_m31] <;>
    exact (felt252_to_m31_eq ret_pc_252 value_n h_num_bits hret1).symm
  simp only [hfp2, h_ret_fp_as_m31]
  simp [felt252_to_m31_eq ret_fp_252 value_n h_num_bits_fp hfp1, ←hfp2]

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
    (is_rel op1_base_fp : Bool)
    (num_steps: Nat) :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call is_rel op1_base_fp ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) is_rel op1_base_fp num_steps := by
  unfold call ; lift_lets
  intro offset2 state1 ab1 lt1 offset2₁ stored_fp_address
    state2 ab2 lt2 stored_fp ab3 stored_ret_pc_address
    state3 ab4 lt3 stored_ret_pc return_pc ab5
    state4 ab6 lt4 distance_to_next_pc mem1_base
    state5 ab6 lt5 next_pc
  intro hab6 hlt5
  cases is_rel
  · have ⟨hab5, hlt3, hread_address2⟩ := Felt252IdMemory.read_address.sound_auto
      varAssign memAssign _ _ h_satisfied h_rc h_mem.1 (mem1_base + offset2₁) hab6 hlt5
    have ⟨hab4, h_c_ret_pc⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
    have ⟨hab3, hlt2, hread_address1⟩ := Felt252IdMemory.read_address.sound_auto
      varAssign memAssign _ _ h_satisfied h_rc h_mem.1 stored_ret_pc_address hab4 hlt3
    have ⟨hab2, h_c_stored_fp⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
    have ⟨hab1, hlt1, hread_address0⟩ := Felt252IdMemory.read_address.sound_auto
      varAssign memAssign _ _ h_satisfied h_rc h_mem.1 stored_fp_address hab2 hlt2
    have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      _ _ h_satisfied h_rc h_mem h_verify_instr (some 0) (some 1) offset2 (CALL_FLAGS False op1_base_fp) casmState.pc hab1 hlt1
    use hab, hlt
    apply spec_of_spec_auto
    use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
    use ?_, ?_, ?_, ?_
    constructor
    . exact h_decode
    use next_pc.eval varAssign
    constructor
    · cases op1_base_fp <;> unfold DecodeInstruction.call <;> simp [signed_as_offset_as_signed] <;>
      exact hread_address2
    constructor
    · have h_eq : FeltExpr.eval varAssign stored_ret_pc = FeltExpr.eval varAssign return_pc := by
        unfold FeltExpr.eval at h_c_ret_pc
        rwa [sub_eq_zero] at h_c_ret_pc
      cases op1_base_fp <;> simp <;> unfold CasmState.eval <;>
      unfold return_pc at h_eq <;> simp at h_eq <;>
      simp only [←h_eq] <;>
      exact hread_address1
    constructor
    · have h_eq : FeltExpr.eval varAssign stored_fp = (CasmState.eval varAssign casmState).fp := by
        unfold FeltExpr.eval at h_c_stored_fp
        rwa [sub_eq_zero] at h_c_stored_fp
      simp only [←h_eq] ; exact hread_address0
    simp [CasmState.eval]
  -- is_rel = true
  have ⟨hab5, hlt3, hread_rel_imm⟩ := Felt252IdMemory.read_rel_imm.sound_auto
      varAssign memAssign _ _ h_satisfied h_mem.1 (casmState.pc + FeltExpr.const 1) hab6 hlt5
  have ⟨hab4, h_c_ret_pc⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
  have ⟨hab3, hlt2, hread_address1⟩ := Felt252IdMemory.read_address.sound_auto
    varAssign memAssign _ _ h_satisfied h_rc h_mem.1 stored_ret_pc_address hab4 hlt3
  have ⟨hab2, h_c_stored_fp⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, hlt1, hread_address0⟩ := Felt252IdMemory.read_address.sound_auto
    varAssign memAssign _ _  h_satisfied h_rc h_mem.1 stored_fp_address hab2 hlt2
  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    _ _ h_satisfied h_rc h_mem h_verify_instr (some 0) (some 1) offset2 (CALL_FLAGS True op1_base_fp) casmState.pc hab1 hlt1
  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_
  constructor
  . exact h_decode
  use (CasmState.eval varAssign casmState).pc + distance_to_next_pc.eval varAssign
  constructor
  · simp ; exact hread_rel_imm
  constructor
  · have h_eq : FeltExpr.eval varAssign stored_ret_pc = FeltExpr.eval varAssign return_pc := by
      unfold FeltExpr.eval at h_c_ret_pc
      rwa [sub_eq_zero] at h_c_ret_pc
    cases op1_base_fp <;> simp <;> unfold CasmState.eval <;>
    unfold return_pc at h_eq <;> simp [←add_assoc] at h_eq <;>
    simp only [←h_eq] <;>
    exact hread_address1
  constructor
  · have h_eq : FeltExpr.eval varAssign stored_fp = (CasmState.eval varAssign casmState).fp := by
      unfold FeltExpr.eval at h_c_stored_fp
      rwa [sub_eq_zero] at h_c_stored_fp
    simp only [←h_eq] ; exact hread_address0
  simp [CasmState.eval]
  rw [←FeltExpr.eval_add]
  rfl

theorem sound_call_rel [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases CallOpcode.sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ true false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : CallOpcode.flag_assert true false := by simp [CallOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset2, h_instr, h_next⟩
  use (CallOpcode.call_instr true false offset2).toInstruction
  use h_instr

theorem sound_call_abs_base_fp [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases CallOpcode.sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ false true
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : CallOpcode.flag_assert false true := by simp [CallOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset2, h_instr, h_next⟩
  use (CallOpcode.call_instr false true offset2).toInstruction
  use h_instr

theorem sound_call_abs_base_ap [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases CallOpcode.sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ false false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : CallOpcode.flag_assert false false := by simp [CallOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset2, h_instr, h_next⟩
  use (CallOpcode.call_instr false false offset2).toInstruction
  use h_instr

end CallOpcode
