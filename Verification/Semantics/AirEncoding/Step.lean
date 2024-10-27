/-
The constraints that govern the one-step machine transition.
-/
import Verification.Semantics.Cpu
import Verification.Semantics.AirEncoding.Constraints

variable {F : Type _} [Field F]

-- from trace_data (indexed by step)
variable {off_op0_tilde off_op1_tilde off_dst_tilde : F} {f_tilde : TildeType F}
  {fp ap pc : F}
  {next_fp next_ap next_pc : F}
  {dst_addr op0_addr op1_addr : F}
  {dst op0 op1 mul res t0 t1 : F}

-- from instruction constraints
variable {inst : Instruction}

-- from memory constraints
variable {mem : F → F}

-- from instruction constraints
variable (h_off_dst_tilde : off_dst_tilde = ↑inst.offDst.toNat)
  (h_off_op0_tilde : off_op0_tilde = ↑inst.offOp0.toNat)
  (h_off_op1_tilde : off_op1_tilde = ↑inst.offOp1.toNat)
  (h_flags : ∀ i, f_tilde.toF i = ↑(inst.flags.getLsbD i).toNat)

-- from memory constraints
variable (h_mem_pc : mem pc = inst.toNat)
  (h_mem_dst_addr : mem dst_addr = dst)
  (h_mem_op0_addr : mem op0_addr = op0)
  (h_mem_op1_addr : mem op1_addr = op1)

-- step constraints
variable
  (h_dst_addr :
    dst_addr = f_tilde.fDstReg * fp + (1 - f_tilde.fDstReg) * ap + (off_dst_tilde - 2 ^ 15))
  (h_op0_addr :
    op0_addr = f_tilde.fOp0Reg * fp + (1 - f_tilde.fOp0Reg) * ap + (off_op0_tilde - 2 ^ 15))
  (h_op1_addr : op1_addr =
      f_tilde.fOp1Imm * pc + f_tilde.fOp1Ap * ap + f_tilde.fOp1Fp * fp +
          (1 - f_tilde.fOp1Imm - f_tilde.fOp1Ap - f_tilde.fOp1Fp) * op0 +
        (off_op1_tilde - 2 ^ 15))
  (h_mul : mul = op0 * op1)
  (h_res : (1 - f_tilde.fPcJnz) * res =
      f_tilde.fResAdd * (op0 + op1) + f_tilde.fResMul * mul +
        (1 - f_tilde.fResAdd - f_tilde.fResMul - f_tilde.fPcJnz) * op1)
  (h_t0_eq : t0 = f_tilde.fPcJnz * dst)
  (h_t1_eq : t1 = t0 * res)
  (h_next_pc_eq : (t1 - f_tilde.fPcJnz) * (next_pc - (pc + (f_tilde.fOp1Imm + 1))) = 0)
  (h_next_pc_eq' :
    t0 * (next_pc - (pc + op1)) + (1 - f_tilde.fPcJnz) * next_pc -
        ((1 - f_tilde.fPcJumpAbs - f_tilde.fPcJumpRel - f_tilde.fPcJnz) *
              (pc + (f_tilde.fOp1Imm + 1)) +
            f_tilde.fPcJumpAbs * res +
          f_tilde.fPcJumpRel * (pc + res)) = 0)
  (h_opcode_call : f_tilde.fOpcodeCall * (dst - fp) = 0)
  (h_opcode_call' : f_tilde.fOpcodeCall * (op0 - (pc + (f_tilde.fOp1Imm + 1))) = 0)
  (h_opcode_assert_eq : f_tilde.fOpcodeAssertEq * (dst - res) = 0)
  (h_next_ap : next_ap = ap + f_tilde.fApAdd * res + f_tilde.fApAdd1 + f_tilde.fOpcodeCall * 2)
  (h_next_fp :
    next_fp = f_tilde.fOpcodeRet * dst + f_tilde.fOpcodeCall * (ap + 2) +
        (1 - f_tilde.fOpcodeRet - f_tilde.fOpcodeCall) * fp)

/- The correctness theorems.  -/

include h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr in
theorem op0_eq : op0 = inst.op0 mem ⟨pc, ap, fp⟩ := by
  have : f_tilde.fOp0Reg = ↑inst.op0Reg.toNat := by
    rw [TildeType.fOp0Reg, h_flags, Instruction.flags]
    rw [BitVec.getLsb_ofBoolListLE]; rfl
  rw [Instruction.op0, ← h_mem_op0_addr, h_op0_addr, h_off_op0_tilde, BitVec.toBiased16, this]
  cases inst.op0Reg <;> norm_num

include h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr in
theorem op1_agrees : (inst.op1 mem ⟨pc, ap, fp⟩).Agrees op1 := by
  have h1 : f_tilde.fOp1Imm = ↑inst.op1Imm.toNat := by
    rw [TildeType.fOp1Imm, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 : f_tilde.fOp1Ap = ↑inst.op1Ap.toNat := by
    rw [TildeType.fOp1Ap, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 : f_tilde.fOp1Fp = ↑inst.op1Fp.toNat := by
    rw [TildeType.fOp1Fp, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h4 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr
  rw [← h_mem_op1_addr, h_op1_addr, h_off_op1_tilde, Instruction.op1, h1, h2, h3, h4]
  cases inst.op1Imm <;> cases inst.op1Fp <;> cases inst.op1Ap <;>
    norm_num [Instruction.op1, Option.Agrees, BitVec.toBiased16]

include h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res in
theorem resAux_agrees : f_tilde.fPcJnz = false.toNat → (inst.resAux mem ⟨pc, ap, fp⟩).Agrees res := by
  intro h; revert h_res; rw [h]; simp
  have h1 : f_tilde.fResAdd = ↑inst.resAdd.toNat := by
    rw [TildeType.fResAdd, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 : f_tilde.fResMul = ↑inst.resMul.toNat := by
    rw [TildeType.fResMul, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr
  have h4 :=
    op1_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr
  revert h4
  rw [Instruction.resAux, h1, h2]
  cases' inst.op1 mem _ with op1 <;> cases inst.resAdd <;> cases inst.resMul <;>
        simp [Instruction.resAux, Option.Agrees] <;>
      intro h5 h6 <;>
    simp [h3, h5, h6, h_mul]

include h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res in
theorem res_agrees : (inst.res mem ⟨pc, ap, fp⟩).Agrees res := by
  have h1 : f_tilde.fPcJnz = ↑inst.pcJnz.toNat := by
    rw [TildeType.fPcJnz, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 :=
    resAux_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res
  revert h2
  rw [Instruction.res, h1]
  cases inst.pcJumpAbs <;> cases inst.pcJumpRel <;> cases inst.pcJnz <;>
    simp [Instruction.res, Option.Agrees]

include h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr in
theorem dst_eq : dst = inst.dst mem ⟨pc, ap, fp⟩ := by
  have : f_tilde.fDstReg = ↑inst.dstReg.toNat := by
    rw [TildeType.fDstReg, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  rw [Instruction.dst, ← h_mem_dst_addr, h_dst_addr, h_off_dst_tilde, BitVec.toBiased16, this]
  cases inst.dstReg <;> norm_num

section
variable [DecidableEq F]

include h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr
  h_dst_addr h_op0_addr h_op1_addr h_mul h_res
  h_t0_eq h_t1_eq h_next_pc_eq h_next_pc_eq' in
theorem nextPc_agrees : (inst.nextPc mem ⟨pc, ap, fp⟩).Agrees next_pc := by
  have h1 : f_tilde.fPcJumpAbs = ↑inst.pcJumpAbs.toNat := by
    rw [TildeType.fPcJumpAbs, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 : f_tilde.fPcJumpRel = ↑inst.pcJumpRel.toNat := by
    rw [TildeType.fPcJumpRel, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 : f_tilde.fPcJnz = ↑inst.pcJnz.toNat := by
    rw [TildeType.fPcJnz, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h4 : f_tilde.fDstReg = ↑inst.dstReg.toNat := by
    rw [TildeType.fDstReg, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h5 : f_tilde.fResMul = ↑inst.resMul.toNat := by
    rw [TildeType.fResMul, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h6 : f_tilde.fResAdd = ↑inst.resAdd.toNat := by
    rw [TildeType.fResAdd, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h7 : f_tilde.fOp1Imm = ↑inst.op1Imm.toNat := by
    rw [TildeType.fOp1Imm, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h8 := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr
  have h9 :=
    op1_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr
  have h10 :=
    res_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res
  rw [h_t0_eq] at h_t1_eq h_next_pc_eq'
  rw [h_t1_eq] at h_next_pc_eq
  revert h_next_pc_eq h_next_pc_eq'
  rw [Instruction.nextPc, h1, h2, h3]
  cases inst.pcJumpAbs <;> cases inst.pcJumpRel <;> cases inst.pcJnz <;>
    simp [Instruction.nextPc, Option.Agrees]
  · rw [Instruction.size, h7]; intro h; symm; exact eq_of_sub_eq_zero h
  · intro h_next_pc_eq h_next_pc_eq'
    by_cases h : inst.dst mem ⟨pc, ap, fp⟩ = 0
    · rw [if_pos h]
      cases' h_next_pc_eq with h' h'
      · simp [h8, h] at h'
      simp [Option.Agrees]
      rw [h7] at h'
      symm; exact eq_of_sub_eq_zero h'
    cases' h_next_pc_eq' with h' h'
    · rw [h8] at h' ; contradiction
    · rw [if_neg h]
      revert h9
      cases inst.op1 mem ⟨pc, ap, fp⟩ <;> simp [Option.Agrees, Instruction.nextPc]
      rintro rfl
      symm; exact eq_of_sub_eq_zero h'
  · revert h10
    cases inst.res mem ⟨pc, ap, fp⟩ <;> simp [Option.Agrees, Instruction.nextPc]
    rintro rfl
    intro h'; symm; exact eq_of_sub_eq_zero h'
  · intro h; revert h10
    cases inst.res mem ⟨pc, ap, fp⟩ <;> simp [Option.Agrees]
    rintro rfl
    symm; exact eq_of_sub_eq_zero h

end

include h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res h_next_ap in
theorem next_ap_agrees_aux (h : f_tilde.fOpcodeCall = 0) :
    (inst.nextApAux mem ⟨pc, ap, fp⟩).Agrees next_ap := by
  have h1 : f_tilde.fApAdd = ↑inst.apAdd.toNat := by
    rw [TildeType.fApAdd, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 : f_tilde.fApAdd1 = ↑inst.apAdd1.toNat := by
    rw [TildeType.fApAdd1, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 :=
    res_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res
  revert h_next_ap
  rw [Instruction.nextApAux, h1, h2, h]
  cases inst.apAdd <;> cases inst.apAdd1 <;>
        simp [Instruction.nextApAux, Option.Agrees] <;>
      intro h' <;>
    rw [h']
  revert h3
  cases inst.res mem ⟨pc, ap, fp⟩ <;> simp [Option.Agrees, Instruction.nextApAux]

include h_off_op0_tilde h_off_op1_tilde h_flags
  h_mem_op0_addr h_mem_op1_addr
  h_op0_addr h_op1_addr h_mul h_res h_next_ap in
theorem nextAp_agrees : (inst.nextAp mem ⟨pc, ap, fp⟩).Agrees next_ap := by
  have h1 : f_tilde.fOpcodeCall = ↑inst.opcodeCall.toNat := by
    rw [TildeType.fOpcodeCall, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 : f_tilde.fApAdd = ↑inst.apAdd.toNat := by
    rw [TildeType.fApAdd, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h4 : f_tilde.fApAdd1 = ↑inst.apAdd1.toNat := by
    rw [TildeType.fApAdd1, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h5 :=
    next_ap_agrees_aux h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr
      h_op0_addr h_op1_addr h_mul h_res h_next_ap
  revert h5
  rw [Instruction.nextAp, h1]
  cases hoc : inst.opcodeCall <;> cases inst.opcodeRet <;> cases inst.opcodeAssertEq <;>
    simp [Instruction.nextAp, Option.Agrees]
  revert h_next_ap; rw [h1, h3, h4]
  cases inst.apAdd <;> cases inst.apAdd1 <;> simp [Instruction.nextAp, Option.Agrees, hoc]
  apply Eq.symm

include h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr h_next_fp in
theorem nextFp_agrees : (inst.nextFp mem ⟨pc, ap, fp⟩).Agrees next_fp := by
  have h1 : f_tilde.fOpcodeCall = ↑inst.opcodeCall.toNat := by
    rw [TildeType.fOpcodeCall, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h2 : f_tilde.fOpcodeRet = ↑inst.opcodeRet.toNat := by
    rw [TildeType.fOpcodeRet, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr
  revert next_fp
  rw [Instruction.nextFp]; rw [h1, h2]
  cases inst.opcodeCall <;> cases inst.opcodeRet <;> cases inst.opcodeAssertEq <;>
    simp [Instruction.nextFp, Option.Agrees, h3]

include f_tilde h_flags h_off_dst_tilde h_mem_dst_addr h_dst_addr h_off_op0_tilde h_mem_op0_addr
  h_op0_addr h_off_op1_tilde h_mem_op1_addr h_op1_addr h_mul h_res h_opcode_call h_opcode_call'
  h_opcode_assert_eq in
theorem asserts_hold : inst.Asserts mem ⟨pc, ap, fp⟩ := by
  have h1 : f_tilde.fOpcodeCall = ↑inst.opcodeCall.toNat := by
    rw [TildeType.fOpcodeCall, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h3 : f_tilde.fOpcodeAssertEq = ↑inst.opcodeAssertEq.toNat := by
    rw [TildeType.fOpcodeAssertEq, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h4 : f_tilde.fOp1Imm = ↑inst.op1Imm.toNat := by
    rw [TildeType.fOp1Imm, h_flags, Instruction.flags, BitVec.getLsb_ofBoolListLE]; rfl
  have h5 := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr
  have h6 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr
  have h7 :=
    res_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res
  revert h_opcode_call h_opcode_call' h_opcode_assert_eq
  rw [Instruction.Asserts, h1, h3]
  cases inst.opcodeCall <;> cases inst.opcodeRet <;> cases inst.opcodeAssertEq <;>
        simp [Instruction.Asserts, Option.Agrees, h3, ← h5, ← h6] <;>
      intro h <;>
    rw [eq_of_sub_eq_zero h]
  · exact h7
  · simp [Instruction.size, h4]
    intro h; rw [eq_of_sub_eq_zero h]

/- The main theorem: the constraints imply that the next state is as expected.  -/
variable [DecidableEq F]

include
  h_off_dst_tilde
  h_off_op0_tilde
  h_off_op1_tilde
  h_flags
  h_mem_pc
  h_mem_dst_addr
  h_mem_op0_addr
  h_mem_op1_addr
  h_dst_addr
  h_op0_addr
  h_op1_addr
  h_mul
  h_res
  h_t0_eq
  h_t1_eq
  h_next_pc_eq
  h_next_pc_eq'
  h_opcode_call
  h_opcode_call'
  h_opcode_assert_eq
  h_next_ap
  h_next_fp

theorem nextState_eq : NextState mem ⟨pc, ap, fp⟩ ⟨next_pc, next_ap, next_fp⟩ :=
   ⟨inst, h_mem_pc,
    nextPc_agrees h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
      h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr h_dst_addr h_op0_addr h_op1_addr
      h_mul h_res h_t0_eq h_t1_eq h_next_pc_eq h_next_pc_eq',
    nextAp_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res h_next_ap,
    nextFp_agrees h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr h_next_fp,
    asserts_hold h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags h_mem_dst_addr
      h_mem_op0_addr h_mem_op1_addr h_dst_addr h_op0_addr h_op1_addr h_mul h_res h_opcode_call
      h_opcode_call' h_opcode_assert_eq⟩
