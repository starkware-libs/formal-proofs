
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst
import Verification.AirInfra.Airs.Casm.Opcodes.Util

namespace RangeCheckAP

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (x : CasmAddress) :
    AirBuilder × AirLookupTerms :=

  let _state := airBuilder.deduce
  let ab1 := _state.1
  let x_bot11bits := _state.2
  let x_top18bits := (x - x_bot11bits) / (FeltExpr.const 2048)
  let lt1 := lookupTerms.add_rc 18 x_top18bits
  let lt2 := lt1.add_rc 11 x_bot11bits
  (ab1, lt2)

def spec_auto (x : CasmAddressVal) : Prop := IsRangeChecked 29 x
def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (x : CasmAddress) :
    let ⟨new_ab, new_lt⟩ := call ab lt x
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (x.eval varAssign) := by
  unfold call; lift_lets
  intro state1 ab1 x_bot8bits x_top19bits rct1 rct2
  intro hab1 hlt2

  let ⟨rc_x_bot11bits, hlt1⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign _ h_rc _ _ hlt2
  let ⟨rc_x_top18bits, hlt⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign _ h_rc _ _ hlt1
  have hab := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab1

  use hab, hlt

  rcases rc_x_bot11bits with ⟨n11, rc11, eq11⟩
  rcases rc_x_top18bits with ⟨n18, rc18, eq18⟩
  use n11 + 2048 * n18
  constructor
  · linarith[rc11, rc18]
  rw[Nat.cast_add n11 (2048 * n18), ← eq11,Nat.cast_mul 2048 n18, ← eq18]
  dsimp only [x_top19bits]
  simp only [FeltExpr.eval_div, FeltExpr.eval_const, FeltExpr.eval_sub]
  ring_nf
  rw[mul_assoc, mul_assoc, mul_comm _ 2048]
  rw[ZMod.mul_inv_of_unit]
  ring_nf
  apply (ZMod.isUnit_iff_coprime 2048 Stwo.P).mpr
  dsimp[Stwo.P]
  norm_num

end RangeCheckAP

namespace AddApOpcode

variable [Fact (Nat.Prime Stwo.P)]

def ADD_AP_FLAGS : Flags where
  dst_base_fp := some true
  op0_base_fp := some true
  op1_imm := none
  op1_base_fp := none
  op1_base_ap := none
  res_add := some false
  res_mul := some false
  pc_update_jump := some false
  pc_update_jump_rel := some false
  pc_update_jnz := some false
  ap_update_add := some true
  ap_update_add_1 := some false
  opcode_call := some false
  opcode_ret := some false
  opcode_assert_eq := some false

def addApInstr (op1spec : Op1Spec) := advanceApInstr (Op0Spec.fp_plus (-1)) (ResSpec.op1 op1spec)

def add_ap_instr (op1_imm op1_base_fp : Bool) (offset2 : Felt) : Instr :=
    addApInstr
      (if op1_imm then
            (Op1Spec.mem_pc_plus 1)
          else if op1_base_fp then
              (Op1Spec.mem_fp_plus (int_from_Felt offset2))
            else
              (Op1Spec.mem_ap_plus (int_from_Felt offset2))
        )


def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (some 65535) (some 65535) (none) (ADD_AP_FLAGS)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ∃ (op1 : Felt),
      (
          Felt252IdMemory.read_rel_imm.spec memory
            (((ρflags FLAG_OP1_IMM_INDEX) * casmStateVal.pc + (ρflags FLAG_OP1_BASE_FP_INDEX)  * casmStateVal.fp + (ρflags FLAG_OP1_BASE_AP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset2))
            op1
      ) ∧

  ((ρflags FLAG_OP1_IMM_INDEX) + (ρflags FLAG_OP1_BASE_FP_INDEX) + (ρflags FLAG_OP1_BASE_AP_INDEX) = 1) ∧
  (((offset_as_signed_Felt ρoffset2) -  1) * (ρflags FLAG_OP1_IMM_INDEX) = 0) ∧

    IsRangeChecked 29 ρCasmStateVal.ap ∧ --
      ρCasmStateVal = ⟨casmStateVal.pc +1 + (ρflags FLAG_OP1_IMM_INDEX), casmStateVal.ap + op1, casmStateVal.fp⟩


def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat)
    : Prop :=
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (offset2 : Felt), ∃ (op1_imm op1_base_fp : Bool),
          mem (casmStateVal.pc.toFelt252) = (add_ap_instr op1_imm op1_base_fp offset2).toInstruction.toNat ∧
          (add_ap_instr op1_imm op1_base_fp offset2).toInstruction.NextState mem
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

  rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, op1, hop1, hop1flags, hoff2, next_ap_rc, rfl⟩
  simp at next_ap_rc
  rcases next_ap_rc with ⟨next_ap_nat, next_ap_nat_lt, next_ap_nat_eq⟩ -- 2^27?!
  rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
  dsimp at hoffset0 hoffset1 hoffset2 hflags
  rcases hverifyInstruction with ⟨instr, hinstr_pc, hinstr_offsets_flags⟩
  rcases hinstr_pc with ⟨instr252, hinstr252_pc, hinstr252_encodes⟩

  rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252_pc with ⟨value_n, hvalue_n⟩ --

  rw [hoffset0, hoffset1] at hinstr_offsets_flags
  simp only [BitVec_toNat_toFelt_eq_as_u16_toFelt] at hinstr_offsets_flags
  dsimp [OFFSET_BITS] at hinstr_offsets_flags

  dsimp [ADD_AP_FLAGS, Flags.to_arr] at hflags
  rw [hflags 0, hflags 1, hflags 5, hflags 6, hflags 7, hflags 8,
      hflags 9, hflags 10, hflags 11, hflags 12, hflags 13, hflags 14] at hinstr_offsets_flags
  simp only [Bool.toFelt_inj] at hinstr_offsets_flags

  rcases hinstr_offsets_flags with ⟨h_offDst, h_offOp0, h_dstOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
    h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

  constructor
  · dsimp[CasmStateVal.strongly_bounded]
    constructor
    · use next_ap_nat
      constructor
      · simp at next_ap_nat_lt
        calc
          next_ap_nat < 536870912 := next_ap_nat_lt
          _ ≤ 536870912 + (num_steps + 1) := by
            apply Nat.le_add_right
      · exact next_ap_nat_eq
    · use fp_nat
      constructor
      · linarith
      · exact h_fp_nat
  intro mem hmem

  rw [hmem.2 _ _ _ hinstr252_pc hvalue_n]
  rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252_encodes]
  use ρoffset2
  use instr.op1Imm
  use instr.op1Fp


  have is_imm : instr.op1Imm → (ρflags FLAG_OP1_IMM_INDEX = 1) := by
    intro h_is_imm
    dsimp[FLAG_OP1_IMM_INDEX]
    rw[h_op1Imm]
    dsimp[Bool.toFelt]
    rw[h_is_imm]
    rfl

  have not_imm : (instr.op1Imm = false) → (ρflags FLAG_OP1_IMM_INDEX = 0) := by
    intro h_is_imm
    dsimp[FLAG_OP1_IMM_INDEX]
    rw[h_op1Imm]
    dsimp[Bool.toFelt]
    rw[h_is_imm]
    rfl

  have is_imm_not_fp_nor_ap : instr.op1Imm → ((instr.op1Fp = false) ∧ (instr.op1Ap = false)) := by
    intro h_is_imm
    simp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1flags
    rw [h_op1Imm, h_op1Fp, h_op1Ap, h_is_imm] at hop1flags
    dsimp[Bool.toFelt] at hop1flags

    cases op1Fp_val: instr.op1Fp
    · cases op1Ap_val: instr.op1Ap
      · constructor
        <;> rfl
      rw[op1Fp_val, op1Ap_val] at hop1flags
      dsimp at hop1flags
      norm_num at hop1flags
      have : 2 = 1 := by
        apply Felt.fromNat_inj
        norm_num
        norm_num
        exact hop1flags
      absurd this
      linarith

    · cases op1Ap_val: instr.op1Ap
      · rw[op1Fp_val, op1Ap_val] at hop1flags
        dsimp at hop1flags
        norm_num at hop1flags
        have : 2 = 1 := by
          apply Felt.fromNat_inj
          norm_num
          norm_num
          exact hop1flags
        absurd this
        linarith
      rw[op1Fp_val, op1Ap_val] at hop1flags
      dsimp at hop1flags
      norm_num at hop1flags
      have : 3 = 1 := by
        apply Felt.fromNat_inj
        norm_num
        norm_num
        exact hop1flags
      absurd this
      linarith

  have is_fp_not_ap : (instr.op1Fp = true) → (instr.op1Ap = false) := by
    intro isfp
    simp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1flags
    cases op1Imm_val: instr.op1Imm
    · by_contra! isap
      rw[Bool.ne_false_iff] at isap
      rw [h_op1Imm, h_op1Fp, h_op1Ap, isfp, isap, op1Imm_val] at hop1flags
      dsimp[Bool.toFelt] at hop1flags
      have : 2 = 1 := by
        apply Felt.fromNat_inj
        norm_num
        norm_num
        exact hop1flags
      absurd this
      linarith
    exact (is_imm_not_fp_nor_ap op1Imm_val).right

  have not_imm_is_fp_or_is_ap : (instr.op1Imm = false) → ((instr.op1Fp = true) ∨ (instr.op1Ap = true)) := by
    intro h_is_imm
    simp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1flags
    rw [h_op1Imm, h_op1Fp, h_op1Ap, h_is_imm] at hop1flags
    dsimp[Bool.toFelt] at hop1flags
    cases op1Fp_val: instr.op1Fp
    · cases op1Ap_val: instr.op1Ap
      · rw [op1Fp_val, op1Ap_val] at hop1flags
        dsimp[Bool.toFelt] at hop1flags
        have : 0 = 1 := by
          apply Felt.fromNat_inj
          norm_num
          norm_num
          exact hop1flags
        absurd this
        linarith
      right
      norm_num
    left
    norm_num


  have isimm_off2 : instr.op1Imm → (ρoffset2 = 32769) := by
    intro h_is_imm
    simp at hoff2
    rcases hoff2 with h_off2_32769 | h_imm_false
    · rw[offset_as_signed_Felt, OFFSET_BITS] at h_off2_32769
      simp only [Nat.add_one_sub_one, Nat.reduceShiftLeft, Nat.cast_ofNat] at h_off2_32769
      ring_nf at h_off2_32769
      calc
        ρoffset2 = 32769 + (-32769 + ρoffset2) := by
          ring_nf
        _ = 32769 := by
          rw [h_off2_32769]
          ring_nf
    · have flag_op1_imm_true : (ρflags FLAG_OP1_IMM_INDEX = 1) := is_imm h_is_imm
      rw[h_imm_false] at flag_op1_imm_true
      have : 0 = 1 := by
        apply Felt.fromNat_inj
        norm_num
        norm_num
        exact flag_op1_imm_true
      absurd this
      linarith

  constructor
  · apply congr_arg ; apply congr_arg
    simp only [Instr.toInstruction]
    dsimp [add_ap_instr, advanceApInstr, addApInstr]
    apply Instruction.ext
    -- The offsets
    · simp only [←h_offDst]
    · simp only [←h_offOp0]
    · simp only [←BitVec_toFelt_inj, ←h_dstOp1]
      cases op1Imm_val: instr.op1Imm
      · cases instr.op1Fp <;> simp [h_dstOp1] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      cases instr.op1Fp <;> simp <;>
      exact isimm_off2 op1Imm_val

    · simp only [←h_dstReg]
    · simp only [←h_op0Reg]
    · cases instr.op1Imm <;> cases instr.op1Fp <;> simp
    · cases op1Imm_val : instr.op1Imm
      · cases instr.op1Fp <;> simp
      cases op1Fp_val : instr.op1Fp
      · simp
      · simp
        have htmp3 : instr.op1Fp = false := (is_imm_not_fp_nor_ap op1Imm_val).1
        rw [op1Fp_val] at htmp3
        absurd htmp3
        norm_num

    · cases op1Imm_val : instr.op1Imm
      · cases op1Fp_val : instr.op1Fp
        · simp
          have := not_imm_is_fp_or_is_ap op1Imm_val
          simp[op1Fp_val] at this
          exact this
        · simp
          exact is_fp_not_ap op1Fp_val
      exact (is_imm_not_fp_nor_ap op1Imm_val).2
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
  apply nextState_advance_ap _ _ _ _ _ |>.mpr
  dsimp [CasmStateVal.toRegisterStateFelt252]

  have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252_pc

  have pc_plus1 : (casmStateVal.pc + 1).toFelt252 = casmStateVal.pc.toFelt252 + 1 := toFelt252_add_one_of_RangeChecked pc_rc
  have pc_plus2 : (casmStateVal.pc + 2).toFelt252 = casmStateVal.pc.toFelt252 + 2 := toFelt252_add_two_of_RangeChecked pc_rc

  constructor
  · cases op1Imm_val : instr.op1Imm
    · cases instr.op1Fp
      · simp[not_imm op1Imm_val]
        exact pc_plus1
      · simp[not_imm op1Imm_val]
        exact pc_plus1
    simp[op1Imm_val, is_imm]
    rw[add_assoc]
    exact pc_plus2

  -- The ap is advanced correctly
  constructor
  · dsimp
    have hmemlemma4 :  mem (ρflags FLAG_OP1_IMM_INDEX * casmStateVal.pc + ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp +
      ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap +
    offset_as_signed_Felt ρoffset2).toFelt252 = match
      if instr.op1Imm = true then Op1Spec.mem_pc_plus 1
      else
        if instr.op1Fp = true then Op1Spec.mem_fp_plus (int_from_Felt ρoffset2)
        else Op1Spec.mem_ap_plus (int_from_Felt ρoffset2) with
    | Op1Spec.mem_op0_plus i => mem (mem (casmStateVal.fp.toFelt252 + intClip (-1)) + intClip i)
    | Op1Spec.mem_pc_plus i => mem (casmStateVal.pc.toFelt252 + intClip i)
    | Op1Spec.mem_fp_plus i => mem (casmStateVal.fp.toFelt252 + intClip i)
    | Op1Spec.mem_ap_plus i => mem (casmStateVal.ap.toFelt252 + intClip i) := by
      dsimp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX]
      rw[h_op1Imm, h_op1Fp, h_op1Ap, h_dstOp1]
      cases op1Imm_val: instr.op1Imm
      · cases op1Fp_val : instr.op1Fp
        · have := not_imm_is_fp_or_is_ap op1Imm_val
          simp[op1Fp_val] at this
          simp[this]
          dsimp[Bool.toFelt]
          simp

          have ap_off2_rc : IsRangeChecked 29 (casmStateVal.ap + offset_as_signed_Felt ρoffset2) := by
            simp [not_imm op1Imm_val] at hop1
            dsimp[FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1
            rw[h_op1Fp, h_op1Ap, op1Fp_val, this] at hop1
            dsimp[Bool.toFelt] at hop1
            simp at hop1
            rcases hop1 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
            have h_hasValue : Felt252IdMemoryAssign.HasValue memory (casmStateVal.ap +
              offset_as_signed_Felt ρoffset2) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
              use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
            exact memory.IsRangeChecked_address_of_HasValue memChecked h_hasValue

          rw [h_dstOp1] at ap_off2_rc
          rw [toFelt252_add_offset_RangeChecked_eq ap_off2_rc]

        · simp[is_fp_not_ap op1Fp_val]
          dsimp[Bool.toFelt]
          simp
          rw [toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]

      · simp[is_imm_not_fp_nor_ap op1Imm_val]
        dsimp[Bool.toFelt]
        simp
        rw [isimm_off2 op1Imm_val] at h_dstOp1
        have : int_from_Felt ↑instr.offOp1.toNat = 1 := by
          rw [← h_dstOp1]
          dsimp [int_from_Felt, int_from_u16, OFFSET_BITS]
          have small_calc : ZMod.val (32769 : Felt) = 32769 := rfl
          rw [small_calc]
          norm_num
        rw[←this]
        rw [toFelt252_RangeChecked_add_offset_eq pc_rc]


    have hmemlemma5 : casmStateVal.ap.toFelt252 +
      (match
        if instr.op1Imm = true then Op1Spec.mem_pc_plus 1
        else
          if instr.op1Fp = true then Op1Spec.mem_fp_plus (int_from_Felt ρoffset2)
          else Op1Spec.mem_ap_plus (int_from_Felt ρoffset2) with
      | Op1Spec.mem_op0_plus i => mem (mem (casmStateVal.fp.toFelt252 + intClip (-1)) + intClip i)
      | Op1Spec.mem_pc_plus i => mem (casmStateVal.pc.toFelt252 + intClip i)
      | Op1Spec.mem_fp_plus i => mem (casmStateVal.fp.toFelt252 + intClip i)
      | Op1Spec.mem_ap_plus i => mem (casmStateVal.ap.toFelt252 + intClip i)) = casmStateVal.ap.toFelt252 +
      (mem (ρflags FLAG_OP1_IMM_INDEX * casmStateVal.pc + ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp +
      ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap +
      offset_as_signed_Felt ρoffset2).toFelt252) := by
        rw [←hmemlemma4]


    have what_remains_to_prove : (casmStateVal.ap + op1).toFelt252 = casmStateVal.ap.toFelt252 +
      mem (ρflags FLAG_OP1_IMM_INDEX * casmStateVal.pc + ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp +
            ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap +
          offset_as_signed_Felt ρoffset2).toFelt252 := by
      rcases hop1 with ⟨id, h_id, msb, msb_set_limbs, ⟨h_bits0, h_bits1, h_bits2⟩, limb0, limb1, limb2, remainder_bits, h_id_value, ⟨h_value, h_remainder_bits⟩⟩
      have h_hasValue : Felt252IdMemoryAssign.HasValue memory (ρflags FLAG_OP1_IMM_INDEX * casmStateVal.pc + ρflags FLAG_OP1_BASE_FP_INDEX * casmStateVal.fp +
        ρflags FLAG_OP1_BASE_AP_INDEX * casmStateVal.ap +
        offset_as_signed_Felt ρoffset2) (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb msb_set_limbs) := by
        use id ; simp only [Matrix.vec_single_eq_const] ; use h_id, h_id_value
      rcases memory.IsRangeChecked_of_HasValue memChecked h_hasValue with ⟨value_n, hvalue_n⟩

      rw [hmem.2 _ _ _ h_hasValue hvalue_n, h_value]
      exact Felt252IdMemory.val_add_eq_add_eval_of_small_bounded_steps num_steps ns_lim h_ap_nat ap_bound hvalue_n h_remainder_bits h_bits0 h_bits1 h_bits2

    rw [what_remains_to_prove]
    exact hmemlemma5.symm

  · rfl

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState):
    AirBuilder × AirLookupTerms × CasmState :=

  let _state := DecodeInstruction.call airBuilder lookupTerms
    (some 65535) (some 65535) none ADD_AP_FLAGS casmState.pc

  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset2 := _state.2.2.2.2.1
  let flags := _state.2.2.2.2.2

  let flag_op1_imm := flags FLAG_OP1_IMM_INDEX
  let flag_op1_base_fp := flags FLAG_OP1_BASE_FP_INDEX
  let flag_op1_base_ap := flags FLAG_OP1_BASE_AP_INDEX --

  let ab2 := AirBuilder.constrain ab1 (flag_op1_imm + flag_op1_base_fp + flag_op1_base_ap - FeltExpr.const 1)
  let ab3 := AirBuilder.constrain ab2 ((offset2 - FeltExpr.const 1) * flag_op1_imm)

  let _state:= ab3.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
  let ab4:= _state.1
  let mem1_base := _state.2

  let _state := Felt252IdMemory.read_rel_imm ab4 lt1 (mem1_base + offset2)
  let ab5:= _state.1
  let lt2 := _state.2.1
  let op1 := _state.2.2

  let next_ap := casmState.ap + op1

  let _state := RangeCheckAP.call ab5 lt2 next_ap
  let ab6 := _state.1
  let lt3 := _state.2

  (ab6, lt3, ⟨casmState.pc + FeltExpr.const 1 + flag_op1_imm, next_ap, casmState.fp⟩)


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
  intro state1 ab1 lt1 offset2 flags
    flag_op1_imm flag_op1_base_fp flag_op1_base_ap
    ab2 ab3
    state2 ab4 mem1_base
    state3 ab5 lt2 op1
    next_ap
    state4 ab6 lt3
  intro hab6 hlt3

  have ⟨hab5, hlt2, h_next_ap_rc⟩ := RangeCheckAP.sound_auto varAssign _ _ _ h_rc next_ap hab6 hlt3

  have ⟨hab4, hlt1, hread_rel_imm⟩ := Felt252IdMemory.read_rel_imm.sound_auto varAssign memAssign ab4 _ _ h_mem.1 (mem1_base + offset2) hab5 hlt2
  have hread_rel_imm_simp : Felt252IdMemory.read_rel_imm.spec memAssign (FeltExpr.eval varAssign (mem1_base + offset2)) (FeltExpr.eval varAssign op1) := by
    exact hread_rel_imm
  have h_mem1_base_def: mem1_base = (ab3.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)).2 := by
    rfl
  have ⟨hab3, h_mem1_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab4
  have h_mem1_base : FeltExpr.eval varAssign mem1_base = FeltExpr.eval varAssign
    (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap) := by
    rw [h_mem1_base_def]
    exact h_mem1_base_pre
  have ⟨hab2, h_c_offset2⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, h_c_sum_flag⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2
  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab _ h_satisfied h_rc h_mem h_verify_instr (some 65535) (some 65535) none ADD_AP_FLAGS casmState.pc hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use ?_, ?_, ?_, ?_

  constructor
  . exact h_decode
  use FeltExpr.eval varAssign op1


  constructor
  · simp only [FeltExpr.eval_add] at hread_rel_imm_simp
    rw [h_mem1_base] at hread_rel_imm_simp
    unfold offset2 flag_op1_imm flag_op1_base_fp flag_op1_base_ap flags state1 at hread_rel_imm_simp
    simp only [FeltExpr.eval_add] at hread_rel_imm_simp
    simp only [offset_as_signed_Felt_as_offset]
    exact hread_rel_imm_simp


  constructor
  · rw [← sub_eq_zero]
    simp only [FeltExpr.eval_sub, FeltExpr.eval_const, FeltExpr.eval_add, FeltExpr.eval_add] at h_c_sum_flag
    unfold flag_op1_imm flag_op1_base_fp flag_op1_base_ap flags state1 at h_c_sum_flag
    exact h_c_sum_flag

  constructor
  · simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at h_c_offset2
    unfold offset2 flag_op1_imm flags state1 at h_c_offset2
    simp only [offset_as_signed_Felt_as_offset]
    exact h_c_offset2

  constructor
  · exact h_next_ap_rc

  rfl

theorem sound_add_ap [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases h_step mem h_mem_agrees with ⟨offset2, op1_imm, op1_base_fp, h_instr, h_next⟩
  use (add_ap_instr op1_imm op1_base_fp offset2).toInstruction
  use h_instr


end AddApOpcode
