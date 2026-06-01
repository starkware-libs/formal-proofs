
import Verification.AirInfra.Airs.Casm.DecodeInstruction.DecodeInst
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Felt252Utils.VerifyMul252
import Verification.AirInfra.Airs.Felt252Utils.VerifyMulSmall
--import Verification.AirInfra.Core.Expressions.Felt252Expr --

namespace MulOpcode

def MUL_FLAGS : Flags where
    dst_base_fp := none
    op0_base_fp := none
    op1_imm := none
    op1_base_fp := none
    op1_base_ap := none
    res_add := some false
    res_mul := some true
    pc_update_jump := some false
    pc_update_jump_rel := some false
    pc_update_jnz := some false
    ap_update_add := some false
    ap_update_add_1 := none
    opcode_call := some false
    opcode_ret := some false
    opcode_assert_eq := some true

def mulInstr (op0 : Op0Spec) (op1 : Op1Spec) (dst : DstSpec) (ap_update : Bool) := assertEqInstr op0 (ResSpec.op0_times_op1 op1) dst ap_update

def mul_instr (dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2 : Felt) : Instr :=
    let op0 := if op0_base_fp = 1 then
                    (Op0Spec.fp_plus (int_from_Felt offset1))
                else
                    (Op0Spec.ap_plus (int_from_Felt offset1))

    let op1 := if op1_imm = 1 then
                    (Op1Spec.mem_pc_plus 1)
                else if op1_base_fp = 1 then
                    (Op1Spec.mem_fp_plus (int_from_Felt offset2))
                    else
                    (Op1Spec.mem_ap_plus (int_from_Felt offset2))

    let dst := if dst_base_fp = 1 then
                    (DstSpec.mem_fp_plus (int_from_Felt offset0))
                else
                    (DstSpec.mem_ap_plus (int_from_Felt offset0))
    mulInstr op0 op1 dst (ap_update_add_1 = 1)

  def spec
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal)
    (num_steps: Nat)
    : Prop :=
    num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
    (ρCasmStateVal.strongly_bounded (num_steps+1) ∧ (∀ mem : Felt252 → Felt252,
      memory.Agrees mem →
        ∃ (offset0 offset1 offset2 dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 : Felt),
          mem (casmStateVal.pc.toFelt252) = (mul_instr dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction.toNat ∧
          (mul_instr dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction.NextState mem
            casmStateVal.toRegisterStateFelt252 ρCasmStateVal.toRegisterStateFelt252))

namespace MulSmallOpcode

def spec_auto [Fact (Nat.Prime Stwo.P)]
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (none) (none) (none) (MUL_FLAGS) --
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ∃ (dst op0 op1: Felt252Words) (dst_id op0_id op1_id: Felt),
      ((
            ReadPositive.spec memory 72
            (((ρflags FLAG_DST_BASE_FP_INDEX)  * casmStateVal.fp + ((1:Felt) - ρflags FLAG_DST_BASE_FP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset0))
            dst dst_id
      ) ∧ (
            ReadPositive.spec memory 36
            (((ρflags FLAG_OP0_BASE_FP_INDEX)  * casmStateVal.fp + ((1:Felt) - ρflags FLAG_OP0_BASE_FP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset1))
            op0 op0_id
      )∧ (
            ReadPositive.spec memory 36
            (((ρflags FLAG_OP1_IMM_INDEX) * casmStateVal.pc + (ρflags FLAG_OP1_BASE_FP_INDEX)  * casmStateVal.fp + (ρflags FLAG_OP1_BASE_AP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset2))
            op1 op1_id
      )) ∧

  ((ρflags FLAG_OP1_IMM_INDEX) + (ρflags FLAG_OP1_BASE_FP_INDEX) + (ρflags FLAG_OP1_BASE_AP_INDEX) = 1) ∧
  (((offset_as_signed_Felt ρoffset2) -  1) * (ρflags FLAG_OP1_IMM_INDEX) = 0) ∧

  (∃ (dstn op0n op1n: Felt252Nats), dstn.IsRangeChecked dst ∧
      op0n.IsRangeChecked op0 ∧
      op1n.IsRangeChecked op1 ∧
      VerifyMulSmall.spec op0 op1 dst) ∧

      ρCasmStateVal = ⟨casmStateVal.pc +1 + (ρflags FLAG_OP1_IMM_INDEX), casmStateVal.ap + (ρflags FLAG_AP_UPDATE_ADD_1_INDEX) , casmStateVal.fp⟩


theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal) :
    spec memory casmStateVal ρCasmStateVal num_steps := by

    intro ns_lim cs_bound

    rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, dst, op0, op1,
        dst_id, op0_id, op1_id, ⟨hdst, hop0, hop1⟩, hop1flags, hoff2, h_mul_small, rfl⟩

    rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
    dsimp at hflags
    rcases hverifyInstruction with ⟨instr, hinstr_pc, hinstr_offsets_flags⟩
    rcases hinstr_pc with ⟨instr252, hinstr252a, hinstr252b⟩
    have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a
    rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩

    dsimp [MUL_FLAGS, Flags.to_arr] at hflags
    rw [hflags 5, hflags 6, hflags 7, hflags 8, hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr_offsets_flags
    simp only [Bool.toFelt_inj] at hinstr_offsets_flags
    rcases hinstr_offsets_flags with ⟨h_offDst, h_offOp0, h_offOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
        h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

    constructor
    · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX] ; rw [h_apAdd1]
      exact CasmStateVal.next_state_strongly_bound_of_apAdd1 cs_bound --

    intros mem hmem
    rw [hmem.2 _ _ _ hinstr252a hvalue_n]
    rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]

    use ρoffset0, ρoffset1, ρoffset2
    use ρflags FLAG_DST_BASE_FP_INDEX
    use ρflags FLAG_OP0_BASE_FP_INDEX
    use ρflags FLAG_OP1_IMM_INDEX
    use ρflags FLAG_OP1_BASE_FP_INDEX
    use ρflags FLAG_AP_UPDATE_ADD_1_INDEX
    unfold FLAG_DST_BASE_FP_INDEX FLAG_OP0_BASE_FP_INDEX FLAG_OP1_IMM_INDEX FLAG_OP1_BASE_FP_INDEX FLAG_AP_UPDATE_ADD_1_INDEX

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

    have is_op1_fp : instr.op1Fp → (ρflags FLAG_OP1_BASE_FP_INDEX = 1) := by
      intro h_flag
      dsimp[FLAG_OP1_BASE_FP_INDEX]
      rw[h_op1Fp]
      dsimp[Bool.toFelt]
      rw[h_flag]
      rfl

    have not_op1_fp : (instr.op1Fp = false) → (ρflags FLAG_OP1_BASE_FP_INDEX = 0) := by
      intro h_flag
      dsimp[FLAG_OP1_BASE_FP_INDEX]
      rw[h_op1Fp]
      dsimp[Bool.toFelt]
      rw[h_flag]
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
        simp at h_off2_32769
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

    have isimm_off3 : instr.op1Imm → 1 = (int_from_Felt ↑instr.offOp1.toNat) := by
      intro h_is_imm
      rw [← h_offOp1]
      rw [isimm_off2 h_is_imm]
      unfold int_from_Felt
      unfold int_from_u16
      dsimp [OFFSET_BITS]
      rw [(show (32769 : Felt) = (↑(32769:Nat):Felt) from rfl)]
      rw [ZMod.val_natCast_of_lt]
      norm_num
      unfold Stwo.P
      norm_num

    have h_flags_imm : (ρflags 2 = 1) → (instr.op1Imm = true) := by
      intro h_imm
      by_contra htmp
      have := Bool.bool_iff_false.mp htmp
      rw[h_imm, this] at h_op1Imm
      dsimp[Bool.toFelt] at h_op1Imm
      norm_num at h_op1Imm

    have h_flags_not_imm : (¬ (ρflags 2 = 1)) → (instr.op1Imm = false) := by
      intro h_not_imm
      cases op1imm_val: instr.op1Imm
      · rfl
      · have htmp := is_imm op1imm_val
        dsimp[FLAG_OP1_IMM_INDEX] at htmp
        rw[htmp] at h_not_imm
        absurd h_not_imm
        norm_num

    have h_flags_not_imm2 : (¬ (ρflags 2 = 1)) → (ρflags 2 = 0):= by
      intro h_not_imm
      have := h_flags_not_imm h_not_imm
      have := not_imm this
      dsimp[FLAG_OP1_IMM_INDEX] at this
      exact this

    have h_op1_not_fp : (¬ (ρflags 3 = 1)) → (instr.op1Fp = false) := by
      intro h_flag
      cases op1fp_val: instr.op1Fp
      · rfl
      · have htmp := is_op1_fp op1fp_val
        dsimp[FLAG_OP1_BASE_FP_INDEX] at htmp
        rw[htmp] at h_flag
        absurd h_flag
        norm_num

    have h_op1_not_fp2 : (¬ (ρflags 3 = 1)) → (ρflags 3 = 0):= by
      intro h_flag
      have := h_op1_not_fp h_flag
      have := not_op1_fp this
      dsimp[FLAG_OP1_BASE_FP_INDEX] at this
      exact this

    have h_dst_not_fp : (¬ (ρflags 0 = 1)) → (ρflags 0 = 0):= by
      intro h_not_fp
      cases dst_fp_val: instr.dstReg
      · rw[dst_fp_val] at h_dstReg
        dsimp[Bool.toFelt] at h_dstReg
        exact h_dstReg
      · rw[dst_fp_val] at h_dstReg
        dsimp[Bool.toFelt] at h_dstReg
        rw[h_dstReg] at h_not_fp
        absurd h_not_fp
        rfl

    have h_op0_not_fp : (¬ (ρflags 1 = 1)) → (ρflags 1 = 0):= by
      intro h_not_fp
      cases op0fp_val: instr.op0Reg
      · rw[op0fp_val] at h_op0Reg
        dsimp[Bool.toFelt] at h_op0Reg
        exact h_op0Reg
      · rw[op0fp_val] at h_op0Reg
        dsimp[Bool.toFelt] at h_op0Reg
        rw[h_op0Reg] at h_not_fp
        absurd h_not_fp
        rfl

    have h_flags_op1_not_fp : (instr.op1Fp = false) → (ρflags 3 = 0) := by
      intro h_not_fp
      rw[h_not_fp] at h_op1Fp
      dsimp[Bool.toFelt] at h_op1Fp
      exact h_op1Fp

    have h_flags_op1_not_ap : (instr.op1Ap = false) → (ρflags 4 = 0) := by
      intro h_not_ap
      rw[h_not_ap] at h_op1Ap
      dsimp[Bool.toFelt] at h_op1Ap
      exact h_op1Ap

    have is_imm_not_fp_nor_ap_flags : (ρflags 2 = 1) → ((ρflags 3 = 0) ∧ (ρflags 4 = 0)) := by
      intro h_imm
      have := is_imm_not_fp_nor_ap (h_flags_imm h_imm)
      exact ⟨h_flags_op1_not_fp this.1, h_flags_op1_not_ap this.2⟩

    have h_imm_off2 : (ρflags 2 = 1) → (int_from_Felt ρoffset2 = 1) := by
      intro h_imm
      rw[isimm_off2 (h_flags_imm h_imm)]
      dsimp[int_from_Felt]

      dsimp[int_from_u16]
      dsimp[OFFSET_BITS]
      dsimp[Stwo.P]

      have : ZMod.val (32769 : Felt) = 32769 := by
        apply ZMod.val_natCast_of_lt
        unfold Stwo.P
        norm_num

      rw[this]
      norm_num

    have h_flags_fp_not_ap : (ρflags 3 = 1) → (ρflags 4 = 0)  := by
      intro h_flags3
      cases op1fp_val: instr.op1Fp
      · rw[op1fp_val] at h_op1Fp
        rw[h_op1Fp] at h_flags3
        have : (1:Felt) = true.toFelt :=
          by dsimp[Bool.toFelt]
        rw[this] at h_flags3
        have := (Bool.toFelt_inj false true).mp h_flags3
        absurd this
        simp

      · have := is_fp_not_ap op1fp_val
        rw[this] at h_op1Ap
        dsimp[Bool.toFelt] at h_op1Ap
        exact h_op1Ap

    have h_flags_not_fp : (¬ (ρflags 3 = 1)) → (instr.op1Fp = false) := by
      intro h_not_fp
      cases op1fp_val: instr.op1Fp
      · rfl
      · rw[op1fp_val] at h_op1Fp
        dsimp[Bool.toFelt] at h_op1Fp
        rw[h_op1Fp] at h_not_fp
        absurd h_not_fp
        simp

    have h_flags_not_fp2 : (¬(ρflags 3 = 1)) → (ρflags 3 = 0) := by
      intro h_not_fp
      have := h_flags_not_fp h_not_fp
      rw[this] at h_op1Fp
      dsimp[Bool.toFelt] at h_op1Fp
      exact h_op1Fp


    have h_flags_not_imm_not_fp : (¬(ρflags 2 = 1)) → (¬(ρflags 3 = 1)) → (ρflags 4 = 1) := by
      intro h_not_imm
      intro h_not_fp
      have := not_imm_is_fp_or_is_ap (h_flags_not_imm h_not_imm)
      rw[h_flags_not_fp h_not_fp] at this
      simp at this
      rw[this] at h_op1Ap
      dsimp[Bool.toFelt] at h_op1Ap
      exact h_op1Ap

    constructor
    · -- The instruction is in memory at pc
      apply congr_arg ; apply congr_arg
      simp only [Instr.toInstruction] --
      dsimp [mul_instr, assertEqInstr, mulInstr] --
      apply Instruction.ext
      -- The offsets
      · simp only [←BitVec_toFelt_inj]
        by_cases h0 : ρflags 0 = 1 <;> simp [h0] <;> simp only [h_offDst] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      · simp only [←BitVec_toFelt_inj]
        by_cases h0 : ρflags 1 = 1 <;> simp [h0] <;> simp only [h_offOp0] <;>
        exact BitVec_u16_eq_from_Felt_to_u16

      · simp only [←BitVec_toFelt_inj, ←h_offOp1]
        · by_cases h_imm : ρflags 2 = 1
          · simp [h_imm]
            have := h_flags_imm h_imm
            exact isimm_off2 this
          · simp [h_imm]
            by_cases h_op1fp : ρflags 3 = 1
            all_goals
            · simp [h_op1fp]
              rw[h_offOp1]
              exact BitVec_u16_eq_from_Felt_to_u16

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
      · simp only [←Bool.toFelt_inj]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        · have := h_flags_imm h_imm
          simp [Bool.toFelt, this]
        by_cases h_fp : ρflags 3 = 1
        all_goals
        simp [h_fp]
        · by_cases htmp : instr.op1Imm
          · rw[htmp] at h_op1Imm
            rw[h_op1Imm] at h_imm
            dsimp[Bool.toFelt] at h_imm
            push_neg at h_imm
            absurd h_imm
            rfl
          · have := Bool.bool_iff_false.mp htmp
            rw[this]

      · simp only [←Bool.toFelt_inj]
        by_cases h_is_op1fp : ρflags 3 = 1 <;> simp [h_is_op1fp]
        · by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
          · have := h_flags_imm h_imm
            simp [Bool.toFelt]
            rw[h_is_op1fp] at h_op1Fp
            rw[(is_imm_not_fp_nor_ap this).1] at h_op1Fp
            simp[Bool.toFelt] at h_op1Fp
          · rw[h_is_op1fp] at h_op1Fp
            rw[← h_op1Fp]
            simp[Bool.toFelt]
        · by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
          all_goals
          · by_cases htmp : instr.op1Fp
            · rw[htmp] at h_op1Fp
              simp[Bool.toFelt] at h_op1Fp
              rw[h_op1Fp] at h_is_op1fp
              absurd h_is_op1fp
              rfl
            · have := Bool.bool_iff_false.mp htmp
              rw[this]
      · simp only [←Bool.toFelt_inj]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        · have := h_flags_imm h_imm
          simp [Bool.toFelt]

          have htmp2 := (is_imm_not_fp_nor_ap this).2
          rw[(is_imm_not_fp_nor_ap this).2]
          rfl
        · by_cases h_is_op1fp : ρflags 3 = 1 <;> simp [h_is_op1fp]
          · have : instr.op1Fp = true := by -- this repeats
              by_contra htmp
              have := Bool.bool_iff_false.mp htmp
              rw[h_is_op1fp, this] at h_op1Fp
              dsimp[Bool.toFelt] at h_op1Fp
              norm_num at h_op1Fp
            have := is_fp_not_ap this
            rw[this]
          · by_cases htmp : instr.op1Fp
            · rw[htmp] at h_op1Fp
              simp[Bool.toFelt] at h_op1Fp
              rw[h_op1Fp] at h_is_op1fp
              absurd h_is_op1fp
              rfl
            · by_cases htmp2 : instr.op1Imm
              · rw[htmp2] at h_op1Imm
                simp[Bool.toFelt] at h_op1Imm
                rw[h_op1Imm] at h_imm
                absurd h_imm
                rfl
              · have htmpb := Bool.bool_iff_false.mp htmp
                have htmp2b := Bool.bool_iff_false.mp htmp2
                have := not_imm_is_fp_or_is_ap htmp2b
                rw[htmpb] at this
                simp at this
                rw[this]
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

    --
    have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a

    have pc_plus1 : (casmStateVal.pc + 1).toFelt252 = casmStateVal.pc.toFelt252 + 1 := toFelt252_add_one_of_RangeChecked pc_rc
    have pc_plus2 : (casmStateVal.pc + 2).toFelt252 = casmStateVal.pc.toFelt252 + 2 := toFelt252_add_two_of_RangeChecked pc_rc

    constructor
    · -- The pc is advanced correctly
      by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
      · rw[add_assoc]
        apply pc_plus2
      · have : ρflags 2 = 0 := by
          by_cases h_is_imm : instr.op1Imm
          · rw[h_is_imm] at h_op1Imm
            dsimp[Bool.toFelt] at h_op1Imm
            rw[h_op1Imm] at h_imm
            absurd h_imm
            rfl
          · rw[Bool.bool_iff_false.mp h_is_imm] at h_op1Imm
            dsimp[Bool.toFelt] at h_op1Imm
            exact h_op1Imm
        by_cases h_is_fp : ρflags 3 = 1 <;> simp [h_is_fp, this] <;> exact pc_plus1
    constructor
    · -- The ap is advanced correctly
      simp only [h_apAdd1]
      cases instr.apAdd1
      · simp [Bool.toFelt]
      · simp [Bool.toFelt]
        rcases cs_bound with ⟨⟨_, ap_bound, h_ap_nat⟩, -⟩
        exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat (by linarith[ap_bound])

    rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

    constructor
    · -- The fp is unchanged.
        rfl
    -- The two values are equal
    rw[h_offDst]
    rw[h_offOp0]
    rw[h_offOp1]

    --rcases h_add with ⟨dstn, op0n, op1n, hdstrc, hop0rc, hop1rc, h_add_eq⟩ --@
    by_cases h_dst_fp : ρflags 0 = 1 <;> simp [h_dst_fp] <;> dsimp[FLAG_DST_BASE_FP_INDEX] at hdst
    --<;> have := hdst
    <;> try rw [h_dst_not_fp h_dst_fp] at hdst
    all_goals
    · try rw [h_dst_fp] at hdst
      simp only [sub_zero, sub_self, zero_mul, one_mul, zero_add, add_zero] at hdst
      try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
      try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
      by_cases h_op0_fp : ρflags 1 = 1 <;> simp [h_op0_fp]
      <;> dsimp[FLAG_OP0_BASE_FP_INDEX] at hop0
      <;> try rw [h_op0_not_fp h_op0_fp] at hop0
      all_goals
      · try rw [h_op0_fp] at hop0
        simp only [sub_zero, sub_self, zero_mul, one_mul, zero_add, add_zero] at hop0
        try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
        try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
        -- have hdstmem := Felt252IdMemory.read_small_mem memChecked hmem hdst -- ReadPositive.sound_auto
        -- have hop0mem := Felt252IdMemory.read_small_mem memChecked hmem hop0
        -- have hop1mem := Felt252IdMemory.read_small_mem memChecked hmem hop1
        have hdstmem := ReadPositive.read_positive_mem memChecked hmem hdst
        have hop0mem := ReadPositive.read_positive_mem memChecked hmem hop0
        have hop1mem := ReadPositive.read_positive_mem memChecked hmem hop1
        -- have hdstmem : mem (casmStateVal.fp + offset_as_signed_Felt ρoffset0).toFelt252 = dst.eval := by
        --   sorry
        -- have hop0mem : mem (casmStateVal.fp + offset_as_signed_Felt ρoffset0).toFelt252 = dst.eval := by
        --   sorry
        -- have hop1mem : mem (casmStateVal.fp + offset_as_signed_Felt ρoffset0).toFelt252 = dst.eval := by
        --   sorry
        rw[← h_offDst]
        rw[← h_offOp0]
        rw[hdstmem]
        rw[hop0mem]
        --rw[hop1mem]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        <;> dsimp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1
        --<;> try rw [h_imm] at hop1
        all_goals
        · try rw [h_imm] at hop1
          try rw [h_flags_not_imm2 h_imm] at hop1
          try rw [(is_imm_not_fp_nor_ap_flags h_imm).1] at hop1
          try rw [(is_imm_not_fp_nor_ap_flags h_imm).2] at hop1
          by_cases h_op1_fp : ρflags 3 = 1
          all_goals
          · try simp[h_op1_fp]
            try rw [h_op1_fp] at hop1
            try rw [h_flags_not_imm_not_fp h_imm h_op1_fp] at hop1
            try rw [h_flags_fp_not_ap h_op1_fp] at hop1
            try rw [h_op1_not_fp2 h_op1_fp] at hop1
            simp only [zero_mul, one_mul, zero_add, add_zero] at hop1
            try rw [isimm_off3 (h_flags_imm h_imm)]
            try rw [← toFelt252_RangeChecked_add_offset_eq pc_rc]
            try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
            try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]

            dsimp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1mem
            try rw [h_imm] at hop1mem
            try rw [h_flags_not_imm2 h_imm] at hop1mem
            try rw [(is_imm_not_fp_nor_ap_flags h_imm).1] at hop1mem
            try rw [(is_imm_not_fp_nor_ap_flags h_imm).2] at hop1mem
            try rw [h_op1_fp] at hop1mem
            try rw [h_flags_not_imm_not_fp h_imm h_op1_fp] at hop1mem
            try rw [h_flags_fp_not_ap h_op1_fp] at hop1mem
            try rw [h_op1_not_fp2 h_op1_fp] at hop1mem
            try simp only[zero_mul, one_mul, zero_add, add_zero] at hop1mem
            try rw [← h_offOp1, hop1mem]

            --exact ReadSmall.add_small_vals memChecked hop0 hop1 hdst h_add
            --exact VerifyMulSmall.
            rcases h_mul_small with ⟨dstn, op0n, op1n, hdstrc, hop0rc, hop1rc, h_mul_eq⟩
            have := h_mul_eq op0n op1n dstn hop0rc hop1rc hdstrc
            unfold VerifyMulSmall.NUM_LIMBS at this
            unfold FELT252_BITS_PER_WORD at this

            --hdst : ReadPositive.spec memory 36 (casmStateVal.fp + offset_as_signed_Felt ρoffset0) dst dst_id
            unfold ReadPositive.spec at hdst
            unfold ReadPositive.spec_auto at hdst
            have hdst_a := hdst.1

            unfold ReadPositive.spec at hop0
            unfold ReadPositive.spec_auto at hop0
            have hop0_a := hop0.1

            unfold ReadPositive.spec at hop1
            unfold ReadPositive.spec_auto at hop1
            have hop1_a := hop1.1

            have := this hop0_a hop1_a hdst_a

            --Felt252Nats.cast_eval_nat
            --Felt252Nats.eval_eq_of_IsRangeChecked
            --eval_Felt252Words_eq
            -- hdstrc : dstn.IsRangeChecked dst
            -- hop0rc : op0n.IsRangeChecked op0
            -- hop1rc : op1n.IsRangeChecked op1
            --have zxc2 := Felt252Nats.eval_eq_of_IsRangeChecked dstn dst hdstrc
            --have zxc2 := Felt252Nats.eval_Felt252Words_eq hdstrc
            rw[Felt252Nats.eval_Felt252Words_eq hdstrc]
            rw[Felt252Nats.eval_Felt252Words_eq hop0rc]
            rw[Felt252Nats.eval_Felt252Words_eq hop1rc]

            rw[this]

def call
    [Fact (Nat.Prime Stwo.P)]
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=

    let _state := DecodeInstruction.call airBuilder lookupTerms
                    none none none MUL_FLAGS casmState.pc
    let ab1 := _state.1
    let lt1 := _state.2.1
    let offset0 := _state.2.2.1
    let offset1 := _state.2.2.2.1
    let offset2 := _state.2.2.2.2.1
    let flags := _state.2.2.2.2.2

    let flag_dst_base_fp := flags FLAG_DST_BASE_FP_INDEX
    let flag_op0_base_fp := flags FLAG_OP0_BASE_FP_INDEX
    let flag_op1_imm := flags FLAG_OP1_IMM_INDEX
    let flag_op1_base_fp := flags FLAG_OP1_BASE_FP_INDEX
    let flag_op1_base_ap := flags FLAG_OP1_BASE_AP_INDEX
    let flag_ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

    let ab2 := AirBuilder.constrain ab1 (flag_op1_imm + flag_op1_base_fp + flag_op1_base_ap - FeltExpr.const 1)
    let ab3 := AirBuilder.constrain ab2 ((offset2 - FeltExpr.const 1) * flag_op1_imm)

    let _state := ab3.assign
        (flag_dst_base_fp * casmState.fp + (FeltExpr.const 1 - flag_dst_base_fp) * casmState.ap)
    let ab4:= _state.1
    let mem_dst_base := _state.2

    let _state := ab4.assign
        (flag_op0_base_fp * casmState.fp + (FeltExpr.const 1 - flag_op0_base_fp) * casmState.ap)
    let ab5:= _state.1
    let mem0_base := _state.2

    let _state:= ab5.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
    let ab6:= _state.1
    let mem1_base := _state.2

    let _state := ReadPositive.call ab6 lt1 72 (mem_dst_base + offset0)
    let ab7a := _state.1
    let lt2a := _state.2.1
    let dst := _state.2.2.1
    let _ := _state.2.2.2

    let _state := ReadPositive.call ab7a lt2a 36 (mem0_base + offset1)
    let ab7b := _state.1
    let lt2b := _state.2.1
    let op0 := _state.2.2.1
    let _ := _state.2.2.2

    let _state := ReadPositive.call ab7b lt2b 36 (mem1_base + offset2)
    let ab7 := _state.1
    let lt2 := _state.2.1
    let op1 := _state.2.2.1
    let _ := _state.2.2.2

    let _state := VerifyMulSmall.call ab7 lt2 op0 op1 dst


    let ab8 := _state.1
    let lt3 := _state.2

    let next_ap := casmState.ap + flag_ap_update_add_1
    let next_pc := casmState.pc + FeltExpr.const 1 + flag_op1_imm
    (ab8, lt3, ⟨next_pc, next_ap, casmState.fp⟩)


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
    (num_steps: Nat):
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) num_steps:= by

  unfold call; lift_lets
  intro state1 ab1 lt1 offset0 offset1 offset2 flags
    flag_dst_base_fp flag_op0_base_fp flag_op1_imm flag_op1_base_fp flag_op1_base_ap flag_ap_update_add_1
    ab2
    ab3
    state2 ab4 mem_dst_base
    state3 ab5 mem0_base
    state4 ab6 mem1_base
    state5 ab7a lt2a dst dst_id
    state6 ab7b lt2b op0 op0_id
    state7 ab7 lt2 op1 op1_id
    state8 ab8 lt3
    next_ap
    next_pc
  intro hab8 hlt3

  have hstate8 : state8 = VerifyMulSmall.call ab7 lt2 op0 op1 dst := by
    rfl

  have h_ab8_lt3_a: ab8 = (VerifyMulSmall.call ab7 lt2 op0 op1 dst).1 := by
    rw[← hstate8]

  have h_ab8_lt3_b: lt3 = (VerifyMulSmall.call ab7 lt2 op0 op1 dst).2 := by
    rw[← hstate8]

  have hmul252_a : (VerifyMulSmall.call ab7 lt2 op0 op1 dst).1.SatisfiedBy varAssign := by
    rw[← h_ab8_lt3_a]
    exact hab8

  have hmul252_b : (VerifyMulSmall.call ab7 lt2 op0 op1 dst).2.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
    rw[← h_ab8_lt3_b]
    exact hlt3

  have ⟨hab7, hlt2, h_mul_spec⟩ := VerifyMulSmall.sound_auto varAssign ab7 lt2 h_satisfied h_rc op0 op1 dst hmul252_a hmul252_b

  have ⟨hab7b, hlt2b, hread_op1⟩ := ReadPositive.sound_auto varAssign memAssign ab7b lt2b _ h_rc h_mem.1 36 (mem1_base + offset2) hab7 hlt2
  have ⟨hab7a, hlt2a, hread_op0⟩ := ReadPositive.sound_auto varAssign memAssign ab7a _ _ h_rc h_mem.1 36 (mem0_base + offset1) hab7b hlt2b
  have ⟨hab6, hlt1, hread_dst⟩ := ReadPositive.sound_auto varAssign memAssign ab6 _ _ h_rc h_mem.1 72 (mem_dst_base + offset0) hab7a hlt2a

  have h_mem_op1_base_def: mem1_base = (ab5.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)).2 := by
    rfl
  have ⟨hab5, h_mem_op1_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab6
  have h_mem_op1_base : FeltExpr.eval varAssign mem1_base = FeltExpr.eval varAssign
    (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap) := by
    rw [h_mem_op1_base_def]
    exact h_mem_op1_base_pre

  have h_mem_op0_base_def: mem0_base = (ab4.assign (flag_op0_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_op0_base_fp) * casmState.ap)).2 := by
    rfl
  have ⟨hab4, h_mem_op0_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab5
  have h_mem_op0_base : FeltExpr.eval varAssign mem0_base = FeltExpr.eval varAssign
    (flag_op0_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_op0_base_fp) * casmState.ap):= by
    rw [h_mem_op0_base_def]
    exact h_mem_op0_base_pre

  have h_mem_dst_base_def: mem_dst_base = (ab3.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)).2 := by
    rfl
  have ⟨hab3, h_mem_dst_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab4
  have h_mem_dst_base : FeltExpr.eval varAssign mem_dst_base = FeltExpr.eval varAssign
    (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap):= by
    rw [h_mem_dst_base_def]
    exact h_mem_dst_base_pre

  have ⟨hab2, h_c_offset2⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, h_c_sum_flag⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2

  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab _ _ h_rc h_mem h_verify_instr none none none MUL_FLAGS casmState.pc hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  have memChecked := AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use memChecked
  use ?_, ?_, ?_, ?_

  constructor
  . exact h_decode
  use Felt252Expr.eval varAssign dst
  use Felt252Expr.eval varAssign op0
  use Felt252Expr.eval varAssign op1

  have h_offset0_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.1 = offset0 := by
    rfl
  have h_offset1_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.1 = offset1 := by
    rfl
  have h_offset2_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.1 = offset2 := by
    rfl

  have h_flag_dst_base_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_DST_BASE_FP_INDEX) = flag_dst_base_fp := by
    rfl
  have h_flag_op0_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP0_BASE_FP_INDEX) = flag_op0_base_fp := by
    rfl
  have h_flag_op1_imm_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_IMM_INDEX) = flag_op1_imm := by
    rfl
  have h_flag_op1_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_BASE_FP_INDEX) = flag_op1_base_fp := by
    rfl
  have h_flag_op1_ap_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_BASE_AP_INDEX) = flag_op1_base_ap := by
    rfl

  have h_fp_val : FeltExpr.eval varAssign casmState.fp = (CasmState.eval varAssign casmState).fp := by
    rfl
  have h_ap_val : FeltExpr.eval varAssign casmState.ap = (CasmState.eval varAssign casmState).ap := by
    rfl
  have h_pc_val : FeltExpr.eval varAssign casmState.pc = (CasmState.eval varAssign casmState).pc := by
    rfl

  have hread_dst_simp : ReadPositive.spec memAssign 72 (FeltExpr.eval varAssign mem_dst_base + FeltExpr.eval varAssign offset0)
                        (Felt252Expr.eval varAssign dst) (FeltExpr.eval varAssign dst_id) := by
    exact hread_dst
  have hread_op0_simp : ReadPositive.spec memAssign 36 (FeltExpr.eval varAssign mem0_base + FeltExpr.eval varAssign offset1)
                        (Felt252Expr.eval varAssign op0) (FeltExpr.eval varAssign op0_id) := by
    exact hread_op0
  have hread_op1_simp : ReadPositive.spec memAssign 36 (FeltExpr.eval varAssign mem1_base + FeltExpr.eval varAssign offset2)
                        (Felt252Expr.eval varAssign op1) (FeltExpr.eval varAssign op1_id) := by
    exact hread_op1

  have mem_rc := AirLookupTerms.mem_isRangeChecked_of_agrees_range_checked memAssign h_satisfied h_rc h_mem.2.1 h_mem.2.2
  rcases ReadPositive.IsRangeChecked_of_spec mem_rc hread_dst_simp with ⟨dst_nats, h_dst_nats⟩
  rcases ReadPositive.IsRangeChecked_of_spec mem_rc hread_op0_simp with ⟨op0_nats, h_op0_nats⟩
  rcases ReadPositive.IsRangeChecked_of_spec mem_rc hread_op1_simp with ⟨op1_nats, h_op1_nats⟩

  use (FeltExpr.eval varAssign dst_id)
  use (FeltExpr.eval varAssign op0_id)
  use (FeltExpr.eval varAssign op1_id)

  constructor
  · constructor
    . rw[h_flag_dst_base_fp_def, h_offset0_def]
      simp only [FeltExpr.eval_add] at h_mem_dst_base
      simp only [FeltExpr.eval_mul] at h_mem_dst_base
      simp only [FeltExpr.eval_sub] at h_mem_dst_base
      simp only [FeltExpr.eval_const] at h_mem_dst_base
      rw[h_fp_val, h_ap_val] at h_mem_dst_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_dst_base]
      exact hread_dst --hread_dst_simp

    constructor
    · rw[h_flag_op0_fp_def, h_offset1_def]
      simp only [FeltExpr.eval_add] at h_mem_op0_base
      simp only [FeltExpr.eval_mul] at h_mem_op0_base
      simp only [FeltExpr.eval_sub] at h_mem_op0_base
      simp only [FeltExpr.eval_const] at h_mem_op0_base
      rw[h_fp_val, h_ap_val] at h_mem_op0_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_op0_base]
      exact hread_op0 --hread_op0_simp

    · rw[h_flag_op1_imm_def, h_flag_op1_fp_def, h_flag_op1_ap_def, h_offset2_def]
      simp only [FeltExpr.eval_add] at h_mem_op1_base
      simp only [FeltExpr.eval_mul] at h_mem_op1_base
      rw[h_fp_val, h_ap_val, h_pc_val] at h_mem_op1_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_op1_base]
      exact hread_op1 --hread_op1_simp

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
  · use dst_nats, op0_nats, op1_nats
  constructor

theorem sound_mul_small [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases h_step mem h_mem_agrees with ⟨offset0, offset1, offset2, dst_base_fp, op0_base_fp, op1_imm, op1_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (mul_instr dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {casmState : CasmState} :
    AirLookupTerms.NoYieldTerms (call ab lt casmState).2.1 := by
  unfold call
  apply VerifyMulSmall.NoYieldTerms_of_call
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
  apply VerifyMulSmall.NoTermsOfRel_OPCODE_TRACE_of_call
  repeat
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr ;
    simp [MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  simp_all [VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {casmState : CasmState} :
    AirLookupTerms.RelInRelTuples (call ab lt casmState).2.1 := by
  unfold call
  apply VerifyMulSmall.RelInRelTuples_of_call
  repeat
    apply ReadPositive.RelInRelTuples_of_call
  repeat
    simp [DecodeInstruction.call] ; apply AirLookupTerms.add'_RelInRelTuple.mpr
  simp [h]

end MulSmallOpcode

namespace Mul252Opcode

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (casmStateVal : CasmStateVal)
    (ρCasmStateVal : CasmStateVal) : Prop :=
  memory.IsRangeChecked ∧
  ∃ (ρoffset0 ρoffset1 ρoffset2 : Felt) (ρflags : Fin 15 → Felt),
    DecodeInstruction.spec memory (none) (none) (none) (MUL_FLAGS)
      casmStateVal.pc ρoffset0 ρoffset1 ρoffset2 ρflags ∧
    ∃ (dst op0 op1: Felt252Words),
      ((
            Felt252IdMemory.read_felt252.spec memory
            (((ρflags FLAG_DST_BASE_FP_INDEX)  * casmStateVal.fp + ((1:Felt) - ρflags FLAG_DST_BASE_FP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset0))
            dst
      ) ∧ (
            Felt252IdMemory.read_felt252.spec memory
            (((ρflags FLAG_OP0_BASE_FP_INDEX)  * casmStateVal.fp + ((1:Felt) - ρflags FLAG_OP0_BASE_FP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset1))
            op0
      )∧ (
            Felt252IdMemory.read_felt252.spec memory
            (((ρflags FLAG_OP1_IMM_INDEX) * casmStateVal.pc + (ρflags FLAG_OP1_BASE_FP_INDEX)  * casmStateVal.fp + (ρflags FLAG_OP1_BASE_AP_INDEX)  * casmStateVal.ap) + (offset_as_signed_Felt ρoffset2))
            op1
      )) ∧

  ((ρflags FLAG_OP1_IMM_INDEX) + (ρflags FLAG_OP1_BASE_FP_INDEX) + (ρflags FLAG_OP1_BASE_AP_INDEX) = 1) ∧
  (((offset_as_signed_Felt ρoffset2) -  1) * (ρflags FLAG_OP1_IMM_INDEX) = 0) ∧

  (∃ (dstn op0n op1n: Felt252Nats), dstn.IsRangeChecked dst ∧
      op0n.IsRangeChecked op0 ∧
      op1n.IsRangeChecked op1 ∧
      dstn.eval = op0n.eval * op1n.eval) ∧

      ρCasmStateVal = ⟨casmStateVal.pc +1 + (ρflags FLAG_OP1_IMM_INDEX), casmStateVal.ap + (ρflags FLAG_AP_UPDATE_ADD_1_INDEX) , casmStateVal.fp⟩


theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memory : Felt252IdMemoryAssign}
    {casmStateVal : CasmStateVal}
    {ρCasmStateVal : CasmStateVal}
    {num_steps: Nat}
    (h : spec_auto memory casmStateVal ρCasmStateVal) :
    spec memory casmStateVal ρCasmStateVal num_steps := by

    intro ns_lim cs_bound

    rcases h with ⟨memChecked, ρoffset0, ρoffset1, ρoffset2, ρflags, hdecode, dst, op0, op1,
        ⟨hdst, hop0, hop1⟩, hop1flags, hoff2, h_mul, rfl⟩

    rcases hdecode with ⟨hoffset0, hoffset1, hoffset2, hflags, hverifyInstruction⟩
    dsimp at hflags
    rcases hverifyInstruction with ⟨instr, hinstr_pc, hinstr_offsets_flags⟩
    rcases hinstr_pc with ⟨instr252, hinstr252a, hinstr252b⟩
    have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a
    rcases memory.IsRangeChecked_of_HasValue memChecked hinstr252a with ⟨value_n, hvalue_n⟩

    dsimp [MUL_FLAGS, Flags.to_arr] at hflags
    rw [hflags 5, hflags 6, hflags 7, hflags 8, hflags 9, hflags 10, hflags 12, hflags 13, hflags 14] at hinstr_offsets_flags
    simp only [Bool.toFelt_inj] at hinstr_offsets_flags
    rcases hinstr_offsets_flags with ⟨h_offDst, h_offOp0, h_offOp1, h_dstReg, h_op0Reg, h_op1Imm, h_op1Fp, h_op1Ap, h_resAdd, h_resMul,
        h_pcJumpAbs, h_pcJumpRel, h_pcJnz, h_apAdd, h_apAdd1, h_opcodeCall, h_opcodeRet, h_opcodeAssertEq⟩

    constructor
    · dsimp only [FLAG_AP_UPDATE_ADD_1_INDEX] ; rw [h_apAdd1]
      exact CasmStateVal.next_state_strongly_bound_of_apAdd1 cs_bound --

    intros mem hmem
    rw [hmem.2 _ _ _ hinstr252a hvalue_n]
    rw [←EncodeInstruction_n_of_EncodeInstruction _ _ _ hvalue_n hinstr252b]

    use ρoffset0, ρoffset1, ρoffset2
    use ρflags FLAG_DST_BASE_FP_INDEX
    use ρflags FLAG_OP0_BASE_FP_INDEX
    use ρflags FLAG_OP1_IMM_INDEX
    use ρflags FLAG_OP1_BASE_FP_INDEX
    use ρflags FLAG_AP_UPDATE_ADD_1_INDEX
    unfold FLAG_DST_BASE_FP_INDEX FLAG_OP0_BASE_FP_INDEX FLAG_OP1_IMM_INDEX FLAG_OP1_BASE_FP_INDEX FLAG_AP_UPDATE_ADD_1_INDEX

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

    have is_op1_fp : instr.op1Fp → (ρflags FLAG_OP1_BASE_FP_INDEX = 1) := by
      intro h_flag
      dsimp[FLAG_OP1_BASE_FP_INDEX]
      rw[h_op1Fp]
      dsimp[Bool.toFelt]
      rw[h_flag]
      rfl

    have not_op1_fp : (instr.op1Fp = false) → (ρflags FLAG_OP1_BASE_FP_INDEX = 0) := by
      intro h_flag
      dsimp[FLAG_OP1_BASE_FP_INDEX]
      rw[h_op1Fp]
      dsimp[Bool.toFelt]
      rw[h_flag]
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
        simp at h_off2_32769
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

    have isimm_off3 : instr.op1Imm → 1 = (int_from_Felt ↑instr.offOp1.toNat) := by
      intro h_is_imm
      rw [← h_offOp1]
      rw [isimm_off2 h_is_imm]
      unfold int_from_Felt
      unfold int_from_u16
      dsimp [OFFSET_BITS]
      rw [(show (32769 : Felt) = (↑(32769:Nat):Felt) from rfl)]
      rw [ZMod.val_natCast_of_lt]
      norm_num
      unfold Stwo.P
      norm_num

    have h_flags_imm : (ρflags 2 = 1) → (instr.op1Imm = true) := by
      intro h_imm
      by_contra htmp
      have := Bool.bool_iff_false.mp htmp
      rw[h_imm, this] at h_op1Imm
      dsimp[Bool.toFelt] at h_op1Imm
      norm_num at h_op1Imm

    have h_flags_not_imm : (¬ (ρflags 2 = 1)) → (instr.op1Imm = false) := by
      intro h_not_imm
      cases op1imm_val: instr.op1Imm
      · rfl
      · have htmp := is_imm op1imm_val
        dsimp[FLAG_OP1_IMM_INDEX] at htmp
        rw[htmp] at h_not_imm
        absurd h_not_imm
        norm_num

    have h_flags_not_imm2 : (¬ (ρflags 2 = 1)) → (ρflags 2 = 0):= by
      intro h_not_imm
      have := h_flags_not_imm h_not_imm
      have := not_imm this
      dsimp[FLAG_OP1_IMM_INDEX] at this
      exact this

    have h_op1_not_fp : (¬ (ρflags 3 = 1)) → (instr.op1Fp = false) := by
      intro h_flag
      cases op1fp_val: instr.op1Fp
      · rfl
      · have htmp := is_op1_fp op1fp_val
        dsimp[FLAG_OP1_BASE_FP_INDEX] at htmp
        rw[htmp] at h_flag
        absurd h_flag
        norm_num

    have h_op1_not_fp2 : (¬ (ρflags 3 = 1)) → (ρflags 3 = 0):= by
      intro h_flag
      have := h_op1_not_fp h_flag
      have := not_op1_fp this
      dsimp[FLAG_OP1_BASE_FP_INDEX] at this
      exact this

    have h_dst_not_fp : (¬ (ρflags 0 = 1)) → (ρflags 0 = 0):= by
      intro h_not_fp
      cases dst_fp_val: instr.dstReg
      · rw[dst_fp_val] at h_dstReg
        dsimp[Bool.toFelt] at h_dstReg
        exact h_dstReg
      · rw[dst_fp_val] at h_dstReg
        dsimp[Bool.toFelt] at h_dstReg
        rw[h_dstReg] at h_not_fp
        absurd h_not_fp
        rfl

    have h_op0_not_fp : (¬ (ρflags 1 = 1)) → (ρflags 1 = 0):= by
      intro h_not_fp
      cases op0fp_val: instr.op0Reg
      · rw[op0fp_val] at h_op0Reg
        dsimp[Bool.toFelt] at h_op0Reg
        exact h_op0Reg
      · rw[op0fp_val] at h_op0Reg
        dsimp[Bool.toFelt] at h_op0Reg
        rw[h_op0Reg] at h_not_fp
        absurd h_not_fp
        rfl

    have h_flags_op1_not_fp : (instr.op1Fp = false) → (ρflags 3 = 0) := by
      intro h_not_fp
      rw[h_not_fp] at h_op1Fp
      dsimp[Bool.toFelt] at h_op1Fp
      exact h_op1Fp

    have h_flags_op1_not_ap : (instr.op1Ap = false) → (ρflags 4 = 0) := by
      intro h_not_ap
      rw[h_not_ap] at h_op1Ap
      dsimp[Bool.toFelt] at h_op1Ap
      exact h_op1Ap

    have is_imm_not_fp_nor_ap_flags : (ρflags 2 = 1) → ((ρflags 3 = 0) ∧ (ρflags 4 = 0)) := by
      intro h_imm
      have := is_imm_not_fp_nor_ap (h_flags_imm h_imm)
      exact ⟨h_flags_op1_not_fp this.1, h_flags_op1_not_ap this.2⟩

    have h_imm_off2 : (ρflags 2 = 1) → (int_from_Felt ρoffset2 = 1) := by
      intro h_imm
      rw[isimm_off2 (h_flags_imm h_imm)]
      dsimp[int_from_Felt]

      dsimp[int_from_u16]
      dsimp[OFFSET_BITS]
      dsimp[Stwo.P]

      have : ZMod.val (32769 : Felt) = 32769 := by
        apply ZMod.val_natCast_of_lt
        unfold Stwo.P
        norm_num

      rw[this]
      norm_num

    have h_flags_fp_not_ap : (ρflags 3 = 1) → (ρflags 4 = 0)  := by
      intro h_flags3
      cases op1fp_val: instr.op1Fp
      · rw[op1fp_val] at h_op1Fp
        rw[h_op1Fp] at h_flags3
        have : (1:Felt) = true.toFelt :=
          by dsimp[Bool.toFelt]
        rw[this] at h_flags3
        have := (Bool.toFelt_inj false true).mp h_flags3
        absurd this
        simp

      · have := is_fp_not_ap op1fp_val
        rw[this] at h_op1Ap
        dsimp[Bool.toFelt] at h_op1Ap
        exact h_op1Ap

    have h_flags_not_fp : (¬ (ρflags 3 = 1)) → (instr.op1Fp = false) := by
      intro h_not_fp
      cases op1fp_val: instr.op1Fp
      · rfl
      · rw[op1fp_val] at h_op1Fp
        dsimp[Bool.toFelt] at h_op1Fp
        rw[h_op1Fp] at h_not_fp
        absurd h_not_fp
        simp

    have h_flags_not_fp2 : (¬(ρflags 3 = 1)) → (ρflags 3 = 0) := by
      intro h_not_fp
      have := h_flags_not_fp h_not_fp
      rw[this] at h_op1Fp
      dsimp[Bool.toFelt] at h_op1Fp
      exact h_op1Fp


    have h_flags_not_imm_not_fp : (¬(ρflags 2 = 1)) → (¬(ρflags 3 = 1)) → (ρflags 4 = 1) := by
      intro h_not_imm
      intro h_not_fp
      have := not_imm_is_fp_or_is_ap (h_flags_not_imm h_not_imm)
      rw[h_flags_not_fp h_not_fp] at this
      simp at this
      rw[this] at h_op1Ap
      dsimp[Bool.toFelt] at h_op1Ap
      exact h_op1Ap


    constructor
    · -- The instruction is in memory at pc
      apply congr_arg ; apply congr_arg
      simp only [Instr.toInstruction] --
      dsimp [mul_instr, assertEqInstr, mulInstr] --
      apply Instruction.ext
      -- The offsets
      · simp only [←BitVec_toFelt_inj]
        by_cases h0 : ρflags 0 = 1 <;> simp [h0] <;> simp only [h_offDst] <;>
        exact BitVec_u16_eq_from_Felt_to_u16
      · simp only [←BitVec_toFelt_inj]
        by_cases h0 : ρflags 1 = 1 <;> simp [h0] <;> simp only [h_offOp0] <;>
        exact BitVec_u16_eq_from_Felt_to_u16

      · simp only [←BitVec_toFelt_inj, ←h_offOp1]
        --cases op1Imm_val: instr.op1Imm
        · by_cases h_imm : ρflags 2 = 1
          · simp [h_imm]
            have := h_flags_imm h_imm
            exact isimm_off2 this
          · simp [h_imm]
            by_cases h_op1fp : ρflags 3 = 1
            all_goals
            · simp [h_op1fp]
              rw[h_offOp1]
              exact BitVec_u16_eq_from_Felt_to_u16

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
      · simp only [←Bool.toFelt_inj]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        · have := h_flags_imm h_imm
          simp [Bool.toFelt, this]
        by_cases h_fp : ρflags 3 = 1
        all_goals
        simp [h_fp]
        · by_cases htmp : instr.op1Imm
          · rw[htmp] at h_op1Imm
            rw[h_op1Imm] at h_imm
            dsimp[Bool.toFelt] at h_imm
            push_neg at h_imm
            absurd h_imm
            rfl
          · have := Bool.bool_iff_false.mp htmp
            rw[this]
            --
      · simp only [←Bool.toFelt_inj]
        by_cases h_is_op1fp : ρflags 3 = 1 <;> simp [h_is_op1fp]
        · by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
          · have := h_flags_imm h_imm
            simp [Bool.toFelt]
            rw[h_is_op1fp] at h_op1Fp
            rw[(is_imm_not_fp_nor_ap this).1] at h_op1Fp
            simp[Bool.toFelt] at h_op1Fp
          · rw[h_is_op1fp] at h_op1Fp
            rw[← h_op1Fp]
            simp[Bool.toFelt]
        · by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
          all_goals
          · by_cases htmp : instr.op1Fp
            · rw[htmp] at h_op1Fp
              simp[Bool.toFelt] at h_op1Fp
              rw[h_op1Fp] at h_is_op1fp
              absurd h_is_op1fp
              rfl
            · have := Bool.bool_iff_false.mp htmp
              rw[this]
      · simp only [←Bool.toFelt_inj]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        · have := h_flags_imm h_imm
          simp [Bool.toFelt]
          have htmp2 := (is_imm_not_fp_nor_ap this).2
          rw[(is_imm_not_fp_nor_ap this).2]
          rfl
        · by_cases h_is_op1fp : ρflags 3 = 1 <;> simp [h_is_op1fp]
          · have : instr.op1Fp = true := by -- this repeats
              by_contra htmp
              have := Bool.bool_iff_false.mp htmp
              rw[h_is_op1fp, this] at h_op1Fp
              dsimp[Bool.toFelt] at h_op1Fp
              norm_num at h_op1Fp
            have := is_fp_not_ap this
            rw[this]
          · by_cases htmp : instr.op1Fp
            · rw[htmp] at h_op1Fp
              simp[Bool.toFelt] at h_op1Fp
              rw[h_op1Fp] at h_is_op1fp
              absurd h_is_op1fp
              rfl
            · by_cases htmp2 : instr.op1Imm
              · rw[htmp2] at h_op1Imm
                simp[Bool.toFelt] at h_op1Imm
                rw[h_op1Imm] at h_imm
                absurd h_imm
                rfl
              · have htmpb := Bool.bool_iff_false.mp htmp
                have htmp2b := Bool.bool_iff_false.mp htmp2
                have := not_imm_is_fp_or_is_ap htmp2b
                rw[htmpb] at this
                simp at this
                rw[this]
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

    --
    have pc_rc := memory.IsRangeChecked_address_of_HasValue memChecked hinstr252a

    have pc_plus1 : (casmStateVal.pc + 1).toFelt252 = casmStateVal.pc.toFelt252 + 1 := toFelt252_add_one_of_RangeChecked pc_rc
    have pc_plus2 : (casmStateVal.pc + 2).toFelt252 = casmStateVal.pc.toFelt252 + 2 := toFelt252_add_two_of_RangeChecked pc_rc

    constructor
    · -- The pc is advanced correctly
      by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
      · rw[add_assoc]
        apply pc_plus2
      · have : ρflags 2 = 0 := by
          by_cases h_is_imm : instr.op1Imm
          · rw[h_is_imm] at h_op1Imm
            dsimp[Bool.toFelt] at h_op1Imm
            rw[h_op1Imm] at h_imm
            absurd h_imm
            rfl
          · rw[Bool.bool_iff_false.mp h_is_imm] at h_op1Imm
            dsimp[Bool.toFelt] at h_op1Imm
            exact h_op1Imm
        by_cases h_is_fp : ρflags 3 = 1 <;> simp [h_is_fp, this] <;> exact pc_plus1
    constructor
    · -- The ap is advanced correctly
      simp only [h_apAdd1]
      cases instr.apAdd1
      · simp [Bool.toFelt]
      · simp [Bool.toFelt]
        rcases cs_bound with ⟨⟨_, ap_bound, h_ap_nat⟩, -⟩
        exact toFelt252_add_one_of_step_bounded ns_lim h_ap_nat (by linarith[ap_bound])

    rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩

    constructor
    · -- The fp is unchanged.
        rfl
    -- The two values are equal

    rw[h_offDst]
    rw[h_offOp0]
    rw[h_offOp1]

    rcases h_mul with ⟨dstn, op0n, op1n, hdstrc, hop0rc, hop1rc, h_mul_eq⟩

    by_cases h_dst_fp : ρflags 0 = 1 <;> simp [h_dst_fp] <;> dsimp[FLAG_DST_BASE_FP_INDEX] at hdst
    --<;> have := hdst
    <;> try rw [h_dst_not_fp h_dst_fp] at hdst
    all_goals
    · try rw [h_dst_fp] at hdst
      simp only [sub_zero, sub_self, zero_mul, one_mul, zero_add, add_zero] at hdst
      try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
      try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
      by_cases h_op0_fp : ρflags 1 = 1 <;> simp [h_op0_fp]
      <;> dsimp[FLAG_OP0_BASE_FP_INDEX] at hop0
      <;> try rw [h_op0_not_fp h_op0_fp] at hop0
      all_goals
      · try rw [h_op0_fp] at hop0
        simp only [sub_zero, sub_self, zero_mul, one_mul, zero_add, add_zero] at hop0
        try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
        try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]
        have hdstmem := (hmem.2 _ _ dstn hdst) hdstrc
        have hop0mem := (hmem.2 _ _ op0n hop0) hop0rc
        have hop1mem := (hmem.2 _ _ op1n hop1) hop1rc
        rw[← h_offDst]
        rw[← h_offOp0]
        rw[hdstmem]
        rw[hop0mem]
        by_cases h_imm : ρflags 2 = 1 <;> simp [h_imm]
        <;> dsimp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1
        all_goals
        · try rw [h_imm] at hop1
          try rw [h_flags_not_imm2 h_imm] at hop1
          try rw [(is_imm_not_fp_nor_ap_flags h_imm).1] at hop1
          try rw [(is_imm_not_fp_nor_ap_flags h_imm).2] at hop1
          by_cases h_op1_fp : ρflags 3 = 1
          all_goals
          · try simp[h_op1_fp]
            try rw [h_op1_fp] at hop1
            try rw [h_flags_not_imm_not_fp h_imm h_op1_fp] at hop1
            try rw [h_flags_fp_not_ap h_op1_fp] at hop1
            try rw [h_op1_not_fp2 h_op1_fp] at hop1
            simp only [zero_mul, one_mul, zero_add, add_zero] at hop1
            try rw [isimm_off3 (h_flags_imm h_imm)]
            try rw [← toFelt252_RangeChecked_add_offset_eq pc_rc]
            try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_fp_nat fp_bound]
            try rw [← toFelt252_step_bounded_add_offset_eq ns_lim h_ap_nat ap_bound]

            dsimp[FLAG_OP1_IMM_INDEX, FLAG_OP1_BASE_FP_INDEX, FLAG_OP1_BASE_AP_INDEX] at hop1mem
            try rw [h_imm] at hop1mem
            try rw [h_flags_not_imm2 h_imm] at hop1mem
            try rw [(is_imm_not_fp_nor_ap_flags h_imm).1] at hop1mem
            try rw [(is_imm_not_fp_nor_ap_flags h_imm).2] at hop1mem
            try rw [h_op1_fp] at hop1mem
            try rw [h_flags_not_imm_not_fp h_imm h_op1_fp] at hop1mem
            try rw [h_flags_fp_not_ap h_op1_fp] at hop1mem
            try rw [h_op1_not_fp2 h_op1_fp] at hop1mem
            try simp only[zero_mul, one_mul, zero_add, add_zero] at hop1mem
            try rw [← h_offOp1, hop1mem]
            exact h_mul_eq

@[irreducible]
def call
    [Fact (Nat.Prime Stwo.P)]
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmState : CasmState) :
    AirBuilder × AirLookupTerms × CasmState :=

    let _state := DecodeInstruction.call airBuilder lookupTerms
                    none none none MUL_FLAGS casmState.pc
    let ab1 := _state.1
    let lt1 := _state.2.1
    let offset0 := _state.2.2.1
    let offset1 := _state.2.2.2.1
    let offset2 := _state.2.2.2.2.1
    let flags := _state.2.2.2.2.2

    let flag_dst_base_fp := flags FLAG_DST_BASE_FP_INDEX
    let flag_op0_base_fp := flags FLAG_OP0_BASE_FP_INDEX
    let flag_op1_imm := flags FLAG_OP1_IMM_INDEX
    let flag_op1_base_fp := flags FLAG_OP1_BASE_FP_INDEX
    let flag_op1_base_ap := flags FLAG_OP1_BASE_AP_INDEX
    let flag_ap_update_add_1 := flags FLAG_AP_UPDATE_ADD_1_INDEX

    let ab2 := AirBuilder.constrain ab1 (flag_op1_imm + flag_op1_base_fp + flag_op1_base_ap - FeltExpr.const 1)
    let ab3 := AirBuilder.constrain ab2 ((offset2 - FeltExpr.const 1) * flag_op1_imm)

    let _state := ab3.assign
        (flag_dst_base_fp * casmState.fp + (FeltExpr.const 1 - flag_dst_base_fp) * casmState.ap)
    let ab4:= _state.1
    let mem_dst_base := _state.2

    let _state := ab4.assign
        (flag_op0_base_fp * casmState.fp + (FeltExpr.const 1 - flag_op0_base_fp) * casmState.ap)
    let ab5:= _state.1
    let mem0_base := _state.2

    let _state:= ab5.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)
    let ab6:= _state.1
    let mem1_base := _state.2

    let _state := Felt252IdMemory.read_felt252 ab6 lt1 (mem_dst_base + offset0)
    let ab7a := _state.1
    let lt2a := _state.2.1
    let dst := _state.2.2

    let _state := Felt252IdMemory.read_felt252 ab7a lt2a (mem0_base + offset1)
    let ab7b := _state.1
    let lt2b := _state.2.1
    let op0 := _state.2.2

    let _state := Felt252IdMemory.read_felt252 ab7b lt2b (mem1_base + offset2)
    let ab7 := _state.1
    let lt2 := _state.2.1
    let op1 := _state.2.2
    let _state := VerifyMul252.call ab7 lt2 op0 op1 dst
    let ab8 := _state.1
    let lt3 := _state.2

    let next_ap := casmState.ap + flag_ap_update_add_1
    let next_pc := casmState.pc + FeltExpr.const 1 + flag_op1_imm
    (ab8, lt3, ⟨next_pc, next_ap, casmState.fp⟩)

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
    (num_steps: Nat):
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmState.eval varAssign) (ρCasmState.eval varAssign) num_steps:= by

  unfold call; lift_lets
  intro state1 ab1 lt1 offset0 offset1 offset2 flags
    flag_dst_base_fp flag_op0_base_fp flag_op1_imm flag_op1_base_fp flag_op1_base_ap flag_ap_update_add_1
    ab2
    ab3
    state2 ab4 mem_dst_base
    state3 ab5 mem0_base
    state4 ab6 mem1_base
    state5 ab7a lt2a dst
    state6 ab7b lt2b op0
    state7 ab7 lt2 op1
    state8 ab8 lt3
    next_ap
    next_pc
  intro hab8 hlt3

  have hstate8 : state8 = VerifyMul252.call ab7 lt2 op0 op1 dst := by
    rfl

  have h_ab8_lt3_a: ab8 = (VerifyMul252.call ab7 lt2 op0 op1 dst).1 := by
    rw[← hstate8]

  have h_ab8_lt3_b: lt3 = (VerifyMul252.call ab7 lt2 op0 op1 dst).2 := by
    rw[← hstate8]

  have hmul252_a : (VerifyMul252.call ab7 lt2 op0 op1 dst).1.SatisfiedBy varAssign := by
    rw[← h_ab8_lt3_a]
    exact hab8

  have hmul252_b : (VerifyMul252.call ab7 lt2 op0 op1 dst).2.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
    rw[← h_ab8_lt3_b]
    exact hlt3

  have ⟨hab7, hlt2, h_mul_spec⟩ := VerifyMul252.sound_auto varAssign ab7 lt2 h_satisfied h_rc op0 op1 dst hmul252_a hmul252_b

  have ⟨hab7b, hlt2b, hread_op1⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab7b lt2b _ h_rc h_mem.1 (mem1_base + offset2) hab7 hlt2
  have ⟨hab7a, hlt2a, hread_op0⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab7a _ _ h_rc h_mem.1 (mem0_base + offset1) hab7b hlt2b
  have ⟨hab6, hlt1, hread_dst⟩ := Felt252IdMemory.read_felt252.sound_auto varAssign memAssign ab6 _ _ h_rc h_mem.1 (mem_dst_base + offset0) hab7a hlt2a

  have h_mem_op1_base_def: mem1_base = (ab5.assign (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap)).2 := by
    rfl
  have ⟨hab5, h_mem_op1_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab6
  have h_mem_op1_base : FeltExpr.eval varAssign mem1_base = FeltExpr.eval varAssign
    (flag_op1_imm * casmState.pc + flag_op1_base_fp * casmState.fp + flag_op1_base_ap * casmState.ap) := by
    rw [h_mem_op1_base_def]
    exact h_mem_op1_base_pre

  have h_mem_op0_base_def: mem0_base = (ab4.assign (flag_op0_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_op0_base_fp) * casmState.ap)).2 := by
    rfl
  have ⟨hab4, h_mem_op0_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab5
  have h_mem_op0_base : FeltExpr.eval varAssign mem0_base = FeltExpr.eval varAssign
    (flag_op0_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_op0_base_fp) * casmState.ap):= by
    rw [h_mem_op0_base_def]
    exact h_mem_op0_base_pre

  have h_mem_dst_base_def: mem_dst_base = (ab3.assign (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap)).2 := by
    rfl
  have ⟨hab3, h_mem_dst_base_pre⟩ := (AirBuilder.assign_SatisfiedBy _ _ varAssign).mp hab4
  have h_mem_dst_base : FeltExpr.eval varAssign mem_dst_base = FeltExpr.eval varAssign
    (flag_dst_base_fp * casmState.fp + ((FeltExpr.const 1) - flag_dst_base_fp) * casmState.ap):= by
    rw [h_mem_dst_base_def]
    exact h_mem_dst_base_pre

  have ⟨hab2, h_c_offset2⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab3
  have ⟨hab1, h_c_sum_flag⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2

  have ⟨hab, hlt, h_decode⟩ := DecodeInstruction.sound_auto memAssign varAssign
    ab _ _ h_rc h_mem h_verify_instr none none none MUL_FLAGS casmState.pc hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto
  have memChecked := AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use memChecked
  use ?_, ?_, ?_, ?_

  constructor
  . exact h_decode
  use Felt252Expr.eval varAssign dst
  use Felt252Expr.eval varAssign op0
  use Felt252Expr.eval varAssign op1

  have h_offset0_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.1 = offset0 := by
    rfl
  have h_offset1_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.1 = offset1 := by
    rfl
  have h_offset2_def : (DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.1 = offset2 := by
    rfl

  have h_flag_dst_base_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_DST_BASE_FP_INDEX) = flag_dst_base_fp := by
    rfl
  have h_flag_op0_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP0_BASE_FP_INDEX) = flag_op0_base_fp := by
    rfl
  have h_flag_op1_imm_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_IMM_INDEX) = flag_op1_imm := by
    rfl
  have h_flag_op1_fp_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_BASE_FP_INDEX) = flag_op1_base_fp := by
    rfl
  have h_flag_op1_ap_def: ((DecodeInstruction.call ab lt none none none MUL_FLAGS casmState.pc).2.2.2.2.2 FLAG_OP1_BASE_AP_INDEX) = flag_op1_base_ap := by
    rfl

  have h_fp_val : FeltExpr.eval varAssign casmState.fp = (CasmState.eval varAssign casmState).fp := by
    rfl
  have h_ap_val : FeltExpr.eval varAssign casmState.ap = (CasmState.eval varAssign casmState).ap := by
    rfl
  have h_pc_val : FeltExpr.eval varAssign casmState.pc = (CasmState.eval varAssign casmState).pc := by
    rfl

  have hread_dst_simp : Felt252IdMemory.read_felt252.spec memAssign (FeltExpr.eval varAssign mem_dst_base + FeltExpr.eval varAssign offset0) (Felt252Expr.eval varAssign dst) := by
    exact hread_dst
  have hread_op0_simp : Felt252IdMemory.read_felt252.spec memAssign (FeltExpr.eval varAssign mem0_base + FeltExpr.eval varAssign offset1) (Felt252Expr.eval varAssign op0) := by
    exact hread_op0
  have hread_op1_simp : Felt252IdMemory.read_felt252.spec memAssign (FeltExpr.eval varAssign mem1_base + FeltExpr.eval varAssign offset2) (Felt252Expr.eval varAssign op1) := by
    exact hread_op1

  rcases (memChecked.2 hread_dst_simp) with ⟨dst_nats, h_dst_nats⟩
  rcases (memChecked.2 hread_op0_simp) with ⟨op0_nats, h_op0_nats⟩
  rcases (memChecked.2 hread_op1_simp) with ⟨op1_nats, h_op1_nats⟩

  constructor
  · constructor
    . rw[h_flag_dst_base_fp_def, h_offset0_def]
      simp only [FeltExpr.eval_add] at h_mem_dst_base
      simp only [FeltExpr.eval_mul] at h_mem_dst_base
      simp only [FeltExpr.eval_sub] at h_mem_dst_base
      simp only [FeltExpr.eval_const] at h_mem_dst_base
      rw[h_fp_val, h_ap_val] at h_mem_dst_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_dst_base]
      exact hread_dst_simp

    constructor
    · rw[h_flag_op0_fp_def, h_offset1_def]
      simp only [FeltExpr.eval_add] at h_mem_op0_base
      simp only [FeltExpr.eval_mul] at h_mem_op0_base
      simp only [FeltExpr.eval_sub] at h_mem_op0_base
      simp only [FeltExpr.eval_const] at h_mem_op0_base
      rw[h_fp_val, h_ap_val] at h_mem_op0_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_op0_base]
      exact hread_op0_simp

    · rw[h_flag_op1_imm_def, h_flag_op1_fp_def, h_flag_op1_ap_def, h_offset2_def]
      simp only [FeltExpr.eval_add] at h_mem_op1_base
      simp only [FeltExpr.eval_mul] at h_mem_op1_base
      rw[h_fp_val, h_ap_val, h_pc_val] at h_mem_op1_base
      simp only [offset_as_signed_Felt_as_offset]
      rw[← h_mem_op1_base]
      exact hread_op1_simp

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
  · use dst_nats, op0_nats, op1_nats
    use h_dst_nats
    use h_op0_nats
    use h_op1_nats
    rw[h_mul_spec op0_nats op1_nats dst_nats h_op0_nats h_op1_nats h_dst_nats]

  constructor


theorem sound_mul_252 [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
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
  rcases h_step mem h_mem_agrees with ⟨offset0, offset1, offset2, dst_base_fp, op0_base_fp, op1_imm, op1_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (mul_instr dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {casmState : CasmState} :
    AirLookupTerms.NoYieldTerms (call ab lt casmState).2.1 := by
  unfold call
  apply VerifyMul252.NoYieldTerms_of_call
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
  apply VerifyMul252.NoTermsOfRel_OPCODE_TRACE_of_call
  repeat
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr ;
    simp [MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  simp_all [VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {casmState : CasmState} :
    AirLookupTerms.RelInRelTuples (call ab lt casmState).2.1 := by
  unfold call
  apply VerifyMul252.RelInRelTuples_of_call
  repeat
    apply ReadPositive.RelInRelTuples_of_call
  repeat
    simp [DecodeInstruction.call] ; apply AirLookupTerms.add'_RelInRelTuple.mpr
  simp [h]

end Mul252Opcode

end MulOpcode
