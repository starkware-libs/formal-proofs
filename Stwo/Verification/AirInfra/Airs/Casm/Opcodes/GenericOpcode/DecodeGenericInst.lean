
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst

def FLAG_OP1_BASE_OP0_INDEX : Fin 20 := 15
def FLAG_RES_OP1_INDEX : Fin 20 := 16
def FLAG_PC_UPDATE_REGULAR_INDEX : Fin 20 := 17
def FLAG_FP_UPDATE_REGULAR_INDEX : Fin 20 := 18
def INSTRUCTION_SIZE_INDEX : Fin 20 := 19

def GENERIC_FLAGS_SIZE : Nat := 20

namespace DecodeGenericInstruction

def GENERIC_FLAGS : Flags where
  dst_base_fp := none
  op0_base_fp := none
  op1_imm := none
  op1_base_fp := none
  op1_base_ap := none
  res_add := none
  res_mul := none
  pc_update_jump := none
  pc_update_jump_rel := none
  pc_update_jnz := none
  ap_update_add := none
  ap_update_add_1 := none
  opcode_call := none
  opcode_ret := none
  opcode_assert_eq := none

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms ×
      (Fin GENERIC_FLAGS_SIZE → FeltExpr) × FeltExpr × FeltExpr × FeltExpr :=
  let _state := DecodeInstruction.call airBuilder lookupTerms
    none none none GENERIC_FLAGS address
  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset0 := _state.2.2.1
  let offset1 := _state.2.2.2.1
  let offset2 := _state.2.2.2.2.1
  let flags := _state.2.2.2.2.2
  let generic_flags_vec := Array.ofFn flags
  let op1_base_op0 := FeltExpr.const 1
        - generic_flags_vec[FLAG_OP1_IMM_INDEX]!
        - generic_flags_vec[FLAG_OP1_BASE_FP_INDEX]!
        - generic_flags_vec[FLAG_OP1_BASE_AP_INDEX]!
  let ab2 := AirBuilder.constrain ab1 (op1_base_op0 * (FeltExpr.const 1 - op1_base_op0))
  let generic_flags_vec₁ := generic_flags_vec.push op1_base_op0
  let res_op1 := FeltExpr.const 1
        - generic_flags_vec₁[FLAG_RES_ADD_INDEX]!
        - generic_flags_vec₁[FLAG_RES_MUL_INDEX]!
        - generic_flags_vec₁[FLAG_PC_UPDATE_JNZ_INDEX]!
  let ab3 := AirBuilder.constrain ab2 (res_op1 * (FeltExpr.const 1 - res_op1))
  let generic_flags_vec₂ := generic_flags_vec₁.push res_op1
  let pc_update_regular := FeltExpr.const 1
        - generic_flags_vec₂[FLAG_PC_UPDATE_JUMP_INDEX]!
        - generic_flags_vec₂[FLAG_PC_UPDATE_JUMP_REL_INDEX]!
        - generic_flags_vec₂[FLAG_PC_UPDATE_JNZ_INDEX]!
  let ab4 := AirBuilder.constrain ab3 (pc_update_regular * (FeltExpr.const 1 - pc_update_regular))
  let generic_flags_vec₃ := generic_flags_vec₂.push pc_update_regular
  let ap_update_regular := FeltExpr.const 1
        - generic_flags_vec₃[FLAG_AP_UPDATE_ADD_INDEX]!
        - generic_flags_vec₃[FLAG_AP_UPDATE_ADD_1_INDEX]!
        - generic_flags_vec₃[FLAG_OPCODE_CALL_INDEX]!
  let ab5 := AirBuilder.constrain ab4 (ap_update_regular * (FeltExpr.const 1 - ap_update_regular))
  let fp_update_regular := FeltExpr.const 1
        - generic_flags_vec₃[FLAG_OPCODE_CALL_INDEX]!
        - generic_flags_vec₃[FLAG_OPCODE_RET_INDEX]!
  let ab6 := AirBuilder.constrain ab5 (fp_update_regular * (FeltExpr.const 1 - fp_update_regular))
  let generic_flags_vec₄ := generic_flags_vec₃.push fp_update_regular
  let generic_flags_vec₅ := generic_flags_vec₄.push (FeltExpr.const 1 + generic_flags_vec₄[FLAG_OP1_IMM_INDEX]!)
  let flags_array := fun i : Fin GENERIC_FLAGS_SIZE => generic_flags_vec₅[i]!
  (ab6, lt1, flags_array, offset0, offset1, offset2)

lemma aux_castLe_isLt {i : Fin 15} {h_le : 15 ≤ GENERIC_FLAGS_SIZE} : (Fin.castLE h_le i).val < 15 := by simp

lemma flags_to_flags15
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      (casmAddress : CasmAddress)
      (h_le : 15 ≤  GENERIC_FLAGS_SIZE) :
    let (_, _, ρflags, _, _, _) := call ab lt casmAddress
    ∀ i : Fin 15, ρflags (Fin.castLE h_le i) =
      (DecodeInstruction.call ab lt none none none GENERIC_FLAGS casmAddress).2.2.2.2.2 i := by
  unfold call ; lift_lets
  intro state1 ab1 lt1 offset0 offset1 offset2 flags generic_flags_vec
    op1_base_op0 ab2 generic_flags_vec₁
    res_op1 ab3 generic_flags_vec₂
    pc_update_regular ab4 generic_flags_vec₃
    ap_update_regular ab5
    fp_update_regular ab6 generic_flags_vec₄
    generic_flags_vec₅
    flags_array
  have h_vec_size : generic_flags_vec.size = 15 := by unfold generic_flags_vec ; simp
  have h_lt_vec_size₁ : 15 < generic_flags_vec₁.size := by
    unfold generic_flags_vec₁ ; simp only [Array.size_push, h_vec_size] ; norm_num
  have h_lt_vec_size₂ : 15 < generic_flags_vec₂.size := by
    unfold generic_flags_vec₂ ; simp only [Array.size_push] ; linarith
  have h_lt_vec_size₃ : 15 < generic_flags_vec₃.size := by
    unfold generic_flags_vec₃ ; simp only [Array.size_push] ; linarith
  have h_lt_vec_size₄ : 15 < generic_flags_vec₄.size := by
    unfold generic_flags_vec₄ ; simp only [Array.size_push] ; linarith
  have h_lt_vec_size₅ : 15 < generic_flags_vec₅.size := by
    unfold generic_flags_vec₅ ; simp only [Array.size_push] ; linarith
  intro i
  have h_i_lt : (Fin.castLE h_le i).val < generic_flags_vec.size := lt_of_lt_of_le aux_castLe_isLt (le_of_eq h_vec_size.symm)
  have h_i_lt₃ : (Fin.castLE h_le i).val < generic_flags_vec₃.size := lt_trans aux_castLe_isLt h_lt_vec_size₃
  have h_i_lt₄ : (Fin.castLE h_le i).val < generic_flags_vec₄.size := lt_trans aux_castLe_isLt h_lt_vec_size₄
  have h_i_lt₅ : (Fin.castLE h_le i).val < generic_flags_vec₅.size := lt_trans aux_castLe_isLt h_lt_vec_size₅
  unfold flags_array
  rw [getElem!_pos]
  -- TODO(Jeremy): why is `erw` needed here?
  erw [Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt]
  rw [Array.getElem_ofFn]
  unfold flags state1 ; simp
  exact h_i_lt

def spec_auto
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress: CasmAddressVal)
    (ρoffset0 ρoffset1 ρoffset2 : Felt)
    (ρflags : Fin GENERIC_FLAGS_SIZE → Felt) : Prop :=
  let instrFlags := fun i : Fin 15 => ρflags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  VerifyInstruction.spec memAssign casmAddress ρoffset0 ρoffset1 ρoffset2 instrFlags
  ∧ (
    let op1_base_op0 := 1 - (instrFlags FLAG_OP1_IMM_INDEX) - (instrFlags FLAG_OP1_BASE_FP_INDEX) - (instrFlags FLAG_OP1_BASE_AP_INDEX)
    op1_base_op0 * (1 - op1_base_op0) = 0 ∧
    ρflags FLAG_OP1_BASE_OP0_INDEX = op1_base_op0
  )
  ∧ (
    let res_op1 := 1 - (instrFlags FLAG_RES_ADD_INDEX) - (instrFlags FLAG_RES_MUL_INDEX) - (instrFlags FLAG_PC_UPDATE_JNZ_INDEX)
    res_op1 * (1 - res_op1) = 0 ∧
    ρflags FLAG_RES_OP1_INDEX = res_op1
  )
  ∧ (
    let pc_update_regular := 1 - (instrFlags FLAG_PC_UPDATE_JUMP_INDEX) - (instrFlags FLAG_PC_UPDATE_JUMP_REL_INDEX) - (instrFlags FLAG_PC_UPDATE_JNZ_INDEX)
    pc_update_regular * (1 - pc_update_regular) = 0 ∧
    ρflags FLAG_PC_UPDATE_REGULAR_INDEX = pc_update_regular
  )
  ∧ (
    let ap_update_regular := 1 - (instrFlags FLAG_AP_UPDATE_ADD_INDEX) - (instrFlags FLAG_AP_UPDATE_ADD_1_INDEX) - (instrFlags FLAG_OPCODE_CALL_INDEX)
    ap_update_regular * (1 - ap_update_regular) = 0
  )
  ∧ (
    let fp_update_regular := 1 - (instrFlags FLAG_OPCODE_CALL_INDEX) - (instrFlags FLAG_OPCODE_RET_INDEX)
    fp_update_regular * (1 - fp_update_regular) = 0 ∧
    ρflags FLAG_FP_UPDATE_REGULAR_INDEX = fp_update_regular
  )
  ∧ ρflags INSTRUCTION_SIZE_INDEX = 1 + instrFlags FLAG_OP1_IMM_INDEX

def atMostOneTrue (x y : Bool) : Prop := x = False ∨ y = False
def atMostOneTrue3 (x y z : Bool) : Prop := (x = False ∧ y = False) ∨ (x = False ∧ z = False) ∨ (y = False ∧ z = False)

def spec
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress: CasmAddressVal)
    (offset0 offset1 offset2 : Felt)
    (flags : Fin GENERIC_FLAGS_SIZE → Felt) : Prop :=
  let instrFlags := fun i : Fin 15 => flags (Fin.castLE (by unfold GENERIC_FLAGS_SIZE ; norm_num) i)
  ∃ instruction : Instruction,
    memAssign.HasInstruction casmAddress instruction ∧
    offset0 = instruction.offDst.toNat ∧
    offset1 = instruction.offOp0.toNat ∧
    offset2 = instruction.offOp1.toNat ∧
    instrFlags 0 = instruction.dstReg.toFelt ∧
    instrFlags 1 = instruction.op0Reg.toFelt ∧
    instrFlags 2 = instruction.op1Imm.toFelt ∧
    instrFlags 3 = instruction.op1Fp.toFelt ∧
    instrFlags 4 = instruction.op1Ap.toFelt ∧
    instrFlags 5 = instruction.resAdd.toFelt ∧
    instrFlags 6 = instruction.resMul.toFelt ∧
    instrFlags 7 = instruction.pcJumpAbs.toFelt ∧
    instrFlags 8 = instruction.pcJumpRel.toFelt ∧
    instrFlags 9 = instruction.pcJnz.toFelt ∧
    instrFlags 10 = instruction.apAdd.toFelt ∧
    instrFlags 11 = instruction.apAdd1.toFelt ∧
    instrFlags 12 = instruction.opcodeCall.toFelt ∧
    instrFlags 13 = instruction.opcodeRet.toFelt ∧
    instrFlags 14 = instruction.opcodeAssertEq.toFelt ∧
    atMostOneTrue3 instruction.op1Imm instruction.op1Fp instruction.op1Ap ∧
    flags FLAG_OP1_BASE_OP0_INDEX = (!(instruction.op1Imm || instruction.op1Fp || instruction.op1Ap)).toFelt ∧
    atMostOneTrue3 instruction.resAdd instruction.resMul instruction.pcJnz ∧
    flags FLAG_RES_OP1_INDEX = (!(instruction.resAdd || instruction.resMul || instruction.pcJnz)).toFelt ∧
    atMostOneTrue3 instruction.pcJumpAbs instruction.pcJumpRel instruction.pcJnz ∧
    flags FLAG_PC_UPDATE_REGULAR_INDEX =
      (!(instruction.pcJumpAbs || instruction.pcJumpRel || instruction.pcJnz)).toFelt ∧
    atMostOneTrue3 instruction.apAdd instruction.apAdd1 instruction.opcodeCall ∧
    atMostOneTrue instruction.opcodeCall instruction.opcodeRet ∧
    flags FLAG_FP_UPDATE_REGULAR_INDEX = (!(instruction.opcodeCall || instruction.opcodeRet)).toFelt ∧
    flags INSTRUCTION_SIZE_INDEX = if instruction.op1Imm = true then 2 else 1

lemma atMostOneTrue_of_eq_zero [Fact (Nat.Prime Stwo.P)]
      {x y : Bool}
      (h : 1 - x.toFelt - y.toFelt = 0 ∨ 1 - (1 - x.toFelt - y.toFelt) = 0) :
    atMostOneTrue x y := by
  cases' h with h h
  · cases x <;> cases y <;> simp [Bool.toFelt] at h <;>
    unfold atMostOneTrue <;> simp
  cases x <;> cases y <;> simp [Bool.toFelt] at h <;>
  unfold atMostOneTrue <;> simp
  norm_num at h
  apply Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h

lemma atMostOneTrue3_of_eq_zero [Fact (Nat.Prime Stwo.P)]
      {x y z : Bool}
      (h : 1 - x.toFelt - y.toFelt - z.toFelt = 0 ∨ 1 - (1 - x.toFelt - y.toFelt - z.toFelt) = 0) :
    atMostOneTrue3 x y z := by
  cases' h with h h
  · cases x <;> cases y <;> cases z <;> simp [Bool.toFelt] at h <;>
    unfold atMostOneTrue3 <;> simp
    norm_num at h
    exfalso ; apply Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h
  cases x <;> cases y <;> cases z <;> simp [Bool.toFelt] at h <;>
  unfold atMostOneTrue3 <;> simp <;>
  norm_num at h <;> exfalso <;>
  repeat { apply Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h }

lemma eq_not_or_2
      {x y : Bool}
      (h : 1 - x.toFelt - y.toFelt = 0 ∨ 1 - (1 - x.toFelt - y.toFelt) = 0) :
    1 - x.toFelt - y.toFelt = (!(x || y)).toFelt := by
  cases' h with h h
  · rw [h]
    cases x <;> cases y <;> simp [Bool.toFelt]
    simp [Bool.toFelt] at h
    exact h.symm
  rw [sub_eq_zero] at h
  rw [←h]
  cases x <;> cases y <;> simp [Bool.toFelt] <;> simp [Bool.toFelt] at h <;> try exact h
  exfalso ; rw [←sub_eq_zero] at h ; norm_num at h
  exact Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h

-- TODO(Jeremy): avoid this
set_option maxHeartbeats 300000 in
lemma eq_not_or_3
      {x y z : Bool}
      (h : 1 - x.toFelt - y.toFelt - z.toFelt = 0 ∨ 1 - (1 - x.toFelt - y.toFelt - z.toFelt) = 0) :
    1 - x.toFelt - y.toFelt - z.toFelt = (!(x || y || z)).toFelt := by
  cases' h with h h
  · rw [h]
    cases x <;> cases y <;> cases z <;> simp [Bool.toFelt]
    simp [Bool.toFelt] at h
    exact h.symm
  rw [sub_eq_zero] at h
  rw [←h]
  cases x <;> cases y <;> cases z <;> simp [Bool.toFelt] <;> simp [Bool.toFelt] at h <;> try exact h
  all_goals exfalso ; rw [←sub_eq_zero] at h ; norm_num at h
  all_goals try exact Felt.n_ne_zero (by norm_num) (by simp [Stwo.P]) h

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    {memAssign : Felt252IdMemoryAssign}
    {casmAddress: CasmAddressVal}
    {offset0 offset1 offset2 : Felt}
    {flags : Fin GENERIC_FLAGS_SIZE → Felt}
    (h_spec_auto : spec_auto memAssign casmAddress offset0 offset1 offset2 flags) :
    spec memAssign casmAddress offset0 offset1 offset2 flags := by
  rcases h_spec_auto with ⟨h_verify, h_op1_base_op0, h_res_op1, h_pc_update_regular, h_ap_update_regular, h_fp_update_regular, h_instr_size⟩
  rcases h_verify with ⟨instr, h_has, h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩
  unfold spec ; intro instrFlags
  use instr, h_has, h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq
  simp only [FLAG_OP1_IMM_INDEX, h_op1Imm, FLAG_OP1_BASE_FP_INDEX, h_op1Fp, FLAG_OP1_BASE_AP_INDEX, h_op1Ap] at h_op1_base_op0
  simp only [mul_eq_zero] at h_op1_base_op0
  simp only [FLAG_RES_ADD_INDEX, h_resAdd, FLAG_RES_MUL_INDEX, h_resMul, FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz] at h_res_op1
  simp only [mul_eq_zero] at h_res_op1
  simp only [
      FLAG_PC_UPDATE_JUMP_INDEX, h_pcJumpAbs,
      FLAG_PC_UPDATE_JUMP_REL_INDEX, h_pcJumpRel,
      FLAG_PC_UPDATE_JNZ_INDEX, h_pcJnz] at h_pc_update_regular
  simp only [mul_eq_zero] at h_pc_update_regular
  simp only [FLAG_OPCODE_CALL_INDEX, h_opcodeCall, FLAG_OPCODE_RET_INDEX, h_opcodeRet] at h_fp_update_regular
  simp only [mul_eq_zero] at h_fp_update_regular
  constructor
  · exact atMostOneTrue3_of_eq_zero h_op1_base_op0.1
  constructor
  · simp [h_op1_base_op0.2, eq_not_or_3 h_op1_base_op0.1]
  constructor
  · exact atMostOneTrue3_of_eq_zero h_res_op1.1
  constructor
  · simp [h_res_op1.2, eq_not_or_3 h_res_op1.1]
  constructor
  · exact atMostOneTrue3_of_eq_zero h_pc_update_regular.1
  constructor
  · simp [h_pc_update_regular.2, eq_not_or_3 h_pc_update_regular.1]
  constructor
  · simp only [
      FLAG_AP_UPDATE_ADD_INDEX, h_apAdd,
      FLAG_AP_UPDATE_ADD_1_INDEX, h_apAdd1,
      FLAG_OPCODE_CALL_INDEX, h_opcodeCall] at h_ap_update_regular
    simp only [mul_eq_zero] at h_ap_update_regular
    exact atMostOneTrue3_of_eq_zero h_ap_update_regular
  use atMostOneTrue_of_eq_zero h_fp_update_regular.1
  constructor
  · simp [h_fp_update_regular.2, eq_not_or_2 h_fp_update_regular.1]
  rw [h_instr_size, FLAG_OP1_IMM_INDEX, h_op1Imm]
  cases instr.op1Imm <;> simp [Bool.toFelt] ; norm_num

theorem sound_auto [Fact (Nat.Prime Stwo.P)]
    (memAssign : Felt252IdMemoryAssign)
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
    (casmAddress : CasmAddress) :
    let state := call ab lt casmAddress
    let new_ab := state.1
    let new_lt := state.2.1
    let ρflags := state.2.2.1
    let ρoffset0 := state.2.2.2.1
    let ρoffset1 := state.2.2.2.2.1
    let ρoffset2 := state.2.2.2.2.2
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign
        (casmAddress.eval varAssign)
        ((signed_as_offset ρoffset0).eval varAssign)
        ((signed_as_offset ρoffset1).eval varAssign)
        ((signed_as_offset ρoffset2).eval varAssign)
        (fun i => (ρflags i).eval varAssign) := by
  unfold call; lift_lets
  intro state1 ab1 lt1 offset0 offset1 offset2 flags generic_flags_vec
    op1_base_op0 ab2 generic_flags_vec₁
    res_op1 ab3 generic_flags_vec₂
    pc_update_regular ab4 generic_flags_vec₃
    ap_update_regular ab5
    fp_update_regular ab6 generic_flags_vec₄
    generic_flags_vec₅
    flags_array
    state2 new_ab new_lt ρflags ρoffset0 ρoffset1 ρoffset2
  intro hab6 hlt1
  have ⟨hab5, h_fp_update_regular⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab6
  have ⟨hab4, h_ap_update_regular⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab5
  have ⟨hab3, h_pc_update_regular⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab4
  have ⟨hab2, h_res_op1⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, h_op1_base_op0⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2
  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
      ab lt _ h_rc h_mem h_verify_instr none none none GENERIC_FLAGS casmAddress hab1 hlt1
  use hab, hlt
  apply spec_of_spec_auto

  -- Properties of the arrays and flags

  have h_vec_size : generic_flags_vec.size = 15 := by unfold generic_flags_vec ; simp
  have h_vec_size₁ : generic_flags_vec₁.size = 16 := by
    unfold generic_flags_vec₁ ; simp only [Array.size_push, h_vec_size]
  have h_vec_size₂ : generic_flags_vec₂.size = 17 := by
    unfold generic_flags_vec₂ ; simp only [Array.size_push, h_vec_size₁]
  have h_vec_size₃ : generic_flags_vec₃.size = 18 := by
    unfold generic_flags_vec₃ ; simp only [Array.size_push, h_vec_size₂]
  have h_vec_size₄ : generic_flags_vec₄.size = 19 := by
    unfold generic_flags_vec₄ ; simp only [Array.size_push, h_vec_size₃]
  have h_vec_size₅ : generic_flags_vec₅.size = 20 := by
    unfold generic_flags_vec₅ ; simp only [Array.size_push, h_vec_size₄]

  have h_le : 15 ≤  GENERIC_FLAGS_SIZE := by unfold GENERIC_FLAGS_SIZE ; norm_num1
  have h_flags : (fun i => (fun i => FeltExpr.eval varAssign (ρflags i)) (Fin.castLE h_le i)) =
      fun i => FeltExpr.eval varAssign ((DecodeInstruction.call ab lt none none none GENERIC_FLAGS casmAddress).2.2.2.2.2 i) := by
    apply funext
    intro i
    apply congr_arg
    rw [←(flags_to_flags15 ab lt casmAddress h_le) i]

  have h_vec : ∀ i : Fin 15, FeltExpr.eval varAssign generic_flags_vec[i]! =
      (fun x => (fun x => FeltExpr.eval varAssign (ρflags x)) (Fin.castLE h_le x)) i := by
    intro i
    simp only [Fin.getElem!_fin] ; rw [getElem!_pos]
    unfold generic_flags_vec flags state1
    rw [Array.getElem_ofFn]
    apply congr_arg ; unfold ρflags
    simp
    rw [←(flags_to_flags15 ab lt casmAddress h_le) i]
    simp
  have h_vec₁ : ∀ i : Fin 15, FeltExpr.eval varAssign generic_flags_vec₁[i]! =
      (fun x => (fun x => FeltExpr.eval varAssign (ρflags x)) (Fin.castLE h_le x)) i := by
    intro i ; simp only [Fin.getElem!_fin] ; rw [getElem!_pos]
    rw [Array.getElem_push_lt] ; rw [←getElem!_pos]
    apply h_vec
    unfold generic_flags_vec ; simp
  have h_vec₂ : ∀ i : Fin 15, FeltExpr.eval varAssign generic_flags_vec₂[i]! =
      (fun x => (fun x => FeltExpr.eval varAssign (ρflags x)) (Fin.castLE h_le x)) i := by
    intro i ; simp only [Fin.getElem!_fin] ; rw [getElem!_pos]
    rw [Array.getElem_push_lt] ; rw [←getElem!_pos]
    simp at h_vec₁ ; exact h_vec₁ i
    trans 15 <;> simp [h_vec_size₁]
  have h_vec₃ : ∀ i : Fin 15, FeltExpr.eval varAssign generic_flags_vec₃[i]! =
      (fun x => (fun x => FeltExpr.eval varAssign (ρflags x)) (Fin.castLE h_le x)) i := by
    intro i ; simp only [Fin.getElem!_fin] ; rw [getElem!_pos]
    rw [Array.getElem_push_lt] ; rw [←getElem!_pos]
    simp at h_vec₂ ; exact h_vec₂ i
    trans 15 <;> simp [h_vec_size₂]
  have h_vec₄ : ∀ i : Fin 15, FeltExpr.eval varAssign generic_flags_vec₄[i]! =
      (fun x => (fun x => FeltExpr.eval varAssign (ρflags x)) (Fin.castLE h_le x)) i := by
    intro i ; simp only [Fin.getElem!_fin] ; rw [getElem!_pos]
    rw [Array.getElem_push_lt] ; rw [←getElem!_pos]
    simp at h_vec₃ ; exact h_vec₃ i
    trans 15 <;> simp [h_vec_size₃]

  have h_flag_15 : ρflags FLAG_OP1_BASE_OP0_INDEX = op1_base_op0 := by
    have : FLAG_OP1_BASE_OP0_INDEX.val = 15 := by rfl
    simp only [ρflags, flags_array, state2] ; rw [getElem!_pos]
    erw [Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt]
    simp only [generic_flags_vec₁]; erw [Array.getElem_push_eq]

  have h_flag_16 : ρflags FLAG_RES_OP1_INDEX = res_op1 := by
    have : FLAG_RES_OP1_INDEX.val = 16 := by rfl
    dsimp [ρflags, state2, flags_array]; rw [this, getElem!_pos]
    rw [Array.getElem_push_lt, Array.getElem_push_lt, Array.getElem_push_lt]
    simp only [generic_flags_vec₂, ←h_vec_size₁, Array.getElem_push_eq]
    rw [h_vec_size₂] ; norm_num1
  have h_flag_17 : ρflags FLAG_PC_UPDATE_REGULAR_INDEX = pc_update_regular := by
    have : FLAG_PC_UPDATE_REGULAR_INDEX.val = 17 := by rfl
    dsimp [ρflags, flags_array, state2] ; rw [this, getElem!_pos]
    rw [Array.getElem_push_lt, Array.getElem_push_lt]
    simp only [generic_flags_vec₃, ←h_vec_size₂, Array.getElem_push_eq]
    rw [h_vec_size₃] ; norm_num1
  have h_flag_18 : ρflags FLAG_FP_UPDATE_REGULAR_INDEX = fp_update_regular := by
    have : FLAG_FP_UPDATE_REGULAR_INDEX.val = 18 := by rfl
    dsimp [ρflags, flags_array, state2] ; rw [this,getElem!_pos]
    rw [Array.getElem_push_lt]
    simp only [generic_flags_vec₄, ←h_vec_size₃, Array.getElem_push_eq]
    rw [h_vec_size₄] ; norm_num1
  have h_flag_19 : ρflags INSTRUCTION_SIZE_INDEX = FeltExpr.const 1 + generic_flags_vec₄[FLAG_OP1_IMM_INDEX]! := by
    have : INSTRUCTION_SIZE_INDEX.val = 19 := by rfl
    dsimp [ρflags, flags_array, state2] ; rw [this, getElem!_pos]
    simp only [generic_flags_vec₅, ←h_vec_size₄, Array.getElem_push_eq]
    . rfl
    rw [h_vec_size₅] ; norm_num1

  -- Back to main proof

  constructor
  · rw [h_flags]
    exact h_decode.2.2.2.2
  constructor
  · intro flag ; unfold flag
    unfold op1_base_op0 at h_op1_base_op0
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_op1_base_op0
    simp only [←h_vec]
    use h_op1_base_op0
    simp [h_flag_15, op1_base_op0]
  constructor
  · intro flag ; unfold flag
    unfold res_op1 at h_res_op1
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_res_op1
    simp only [←h_vec₁]
    use h_res_op1
    simp [h_flag_16, res_op1]
  constructor
  · intro flag ; unfold flag
    unfold pc_update_regular at h_pc_update_regular
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_pc_update_regular
    simp only [←h_vec₂]
    use h_pc_update_regular
    simp [h_flag_17, pc_update_regular]
  constructor
  · intro flag ; unfold flag
    unfold ap_update_regular at h_ap_update_regular
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_ap_update_regular
    simp only [←h_vec₃]
    exact h_ap_update_regular
  constructor
  · intro flag ; unfold flag
    unfold fp_update_regular at h_fp_update_regular
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_fp_update_regular
    simp only [←h_vec₃]
    use h_fp_update_regular
    simp [h_flag_18, fp_update_regular]
  simp [h_flag_19, ←h_vec₄]

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {address : CasmAddress} :
    AirLookupTerms.NoYieldTerms (call ab lt address).2.1 := by
  repeat
    apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
  exact h

end DecodeGenericInstruction
