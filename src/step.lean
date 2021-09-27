/-
The constraints that govern the one-step machine transition.
-/
import cpu constraints

variables {F : Type*} [field F]

/- from trace_data (indexed by step) -/
variables {off_op0_tilde
           off_op1_tilde
           off_dst_tilde              : F}
variable  {f_tilde                    : tilde_type F}
variables {fp ap pc                   : F}
variables {next_fp next_ap next_pc    : F}
variables {dst_addr op0_addr op1_addr : F}
variables {dst op0 op1 mul res t0 t1  : F}

/- from instruction constraints -/
variable {inst  : instruction}

/- from memory constraints -/
variable {mem : F → F}

/- from instruction constraints -/
variable h_off_dst_tilde : off_dst_tilde = ↑inst.off_dst.to_natr
variable h_off_op0_tilde : off_op0_tilde = ↑inst.off_op0.to_natr
variable h_off_op1_tilde : off_op1_tilde = ↑inst.off_op1.to_natr
variable h_flags         : ∀ i, f_tilde.to_f i = ↑(inst.flags.nth i).to_nat

/- from memory constraints -/
variable h_mem_pc       : mem pc = inst.to_nat
variable h_mem_dst_addr : mem dst_addr = dst
variable h_mem_op0_addr : mem op0_addr = op0
variable h_mem_op1_addr : mem op1_addr = op1

/- step constraints -/
variable h_dst_addr : dst_addr =
    f_tilde.f_dst_reg * fp + (1 - f_tilde.f_dst_reg) * ap + (off_dst_tilde - 2^15)

variable h_op0_addr : op0_addr =
    f_tilde.f_op0_reg * fp + (1 - f_tilde.f_op0_reg) * ap + (off_op0_tilde - 2^15)

variable h_op1_addr : op1_addr =
    f_tilde.f_op1_imm * pc + f_tilde.f_op1_ap * ap + f_tilde.f_op1_fp * fp +
    (1 - f_tilde.f_op1_imm - f_tilde.f_op1_ap - f_tilde.f_op1_fp) * op0 +
    (off_op1_tilde - 2^15)

variable h_mul : mul = op0 * op1

variable h_res : (1 - f_tilde.f_pc_jnz) * res =
    f_tilde.f_res_add * (op0 + op1) +  f_tilde.f_res_mul * mul +
    (1 - f_tilde.f_res_add - f_tilde.f_res_mul - f_tilde.f_pc_jnz) * op1

variable h_t0_eq : t0 = f_tilde.f_pc_jnz * dst

variable h_t1_eq : t1 = t0 * res

variable h_next_pc_eq :
    (t1 - f_tilde.f_pc_jnz) * (next_pc - (pc + (f_tilde.f_op1_imm + 1))) = 0

variable h_next_pc_eq' :
    t0 * (next_pc - (pc + op1)) + (1 - f_tilde.f_pc_jnz) * next_pc -
      ((1 - f_tilde.f_pc_jump_abs - f_tilde.f_pc_jump_rel - f_tilde.f_pc_jnz) *
          (pc + (f_tilde.f_op1_imm + 1)) +
        f_tilde.f_pc_jump_abs * res + f_tilde.f_pc_jump_rel * (pc + res)) = 0

variable h_opcode_call : f_tilde.f_opcode_call * (dst - fp) = 0

variable h_opcode_call' :
    f_tilde.f_opcode_call * (op0 - (pc + (f_tilde.f_op1_imm + 1))) = 0

variable h_opcode_assert_eq : f_tilde.f_opcode_assert_eq * (dst - res) = 0

variable h_next_ap :
    next_ap = ap + f_tilde.f_ap_add * res + f_tilde.f_ap_add1 + f_tilde.f_opcode_call * 2

variable h_next_fp : next_fp = f_tilde.f_opcode_ret * dst + f_tilde.f_opcode_call * (ap + 2) +
    (1 - f_tilde.f_opcode_ret - f_tilde.f_opcode_call) * fp

/-
The correctness theorems.
-/

section
include h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr

theorem op0_eq : op0 = inst.op0 mem ⟨pc, ap, fp⟩ :=
begin
  have : f_tilde.f_op0_reg = ↑(inst.op0_reg.to_nat) := h_flags _,
  rw [instruction.op0, ←h_mem_op0_addr, h_op0_addr, h_off_op0_tilde, bitvec.to_biased_16, this],
  cases inst.op0_reg; simp
end
end

section
include h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr

theorem op1_agrees : (inst.op1 mem ⟨pc, ap, fp⟩).agrees op1 :=
begin
  have h1 : f_tilde.f_op1_imm = ↑(inst.op1_imm.to_nat) := h_flags _,
  have h2 : f_tilde.f_op1_ap = ↑(inst.op1_ap.to_nat) := h_flags _,
  have h3 : f_tilde.f_op1_fp = ↑(inst.op1_fp.to_nat) := h_flags _,
  have h4 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr,
  rw [←h_mem_op1_addr, h_op1_addr, h_off_op1_tilde, instruction.op1, h1, h2, h3, h4],
  cases inst.op1_imm; cases inst.op1_fp; cases inst.op1_ap;
    simp [instruction.op1._match_1, option.agrees, bitvec.to_biased_16]
end
end

section
include h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res

theorem res_aux_agrees : f_tilde.f_pc_jnz = ff.to_nat →
  (inst.res_aux mem ⟨pc, ap, fp⟩).agrees res :=
begin
  intro h, revert h_res, rw h, simp,
  have h1 : f_tilde.f_res_add = ↑(inst.res_add.to_nat) := h_flags _,
  have h2 : f_tilde.f_res_mul = ↑(inst.res_mul.to_nat) := h_flags _,
  have h3 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr,
  have h4 := op1_agrees h_off_op0_tilde h_off_op1_tilde h_flags
                 h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr,
  revert h4,
  rw [instruction.res_aux, h1, h2],
  cases inst.op1 mem _ with op1; cases inst.res_add; cases inst.res_mul;
    simp [instruction.res_aux._match_1, option.agrees];
    intros h5 h6; simp [h3, h5, h6, h_mul]
end

theorem res_agrees : (inst.res mem ⟨pc, ap, fp⟩).agrees res :=
begin
  have h1 : f_tilde.f_pc_jnz = ↑(inst.pc_jnz.to_nat) := h_flags _,
  have h2 := res_aux_agrees h_off_op0_tilde h_off_op1_tilde
                h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res,
  revert h2,
  rw [instruction.res, h1],
  cases inst.pc_jump_abs; cases inst.pc_jump_rel; cases inst.pc_jnz;
    simp [instruction.res._match_1, option.agrees],
end
end

section
include h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr

theorem dst_eq : dst = inst.dst mem ⟨pc, ap, fp⟩ :=
begin
  have : f_tilde.f_dst_reg = ↑(inst.dst_reg.to_nat) := h_flags _,
  rw [instruction.dst, ←h_mem_dst_addr, h_dst_addr, h_off_dst_tilde, bitvec.to_biased_16, this],
  cases inst.dst_reg; simp
end
end

section
variable [decidable_eq F]

include h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr
include h_dst_addr h_op0_addr h_op1_addr h_mul h_res
include h_t0_eq h_t1_eq h_next_pc_eq h_next_pc_eq'

theorem next_pc_agrees : (inst.next_pc mem ⟨pc, ap, fp⟩).agrees next_pc :=
begin
  have h1  : f_tilde.f_pc_jump_abs = ↑(inst.pc_jump_abs.to_nat) := h_flags _,
  have h2  : f_tilde.f_pc_jump_rel = ↑(inst.pc_jump_rel.to_nat) := h_flags _,
  have h3  : f_tilde.f_pc_jnz = ↑(inst.pc_jnz.to_nat) := h_flags _,
  have h4  : f_tilde.f_dst_reg = ↑(inst.dst_reg.to_nat) := h_flags _,
  have h5  : f_tilde.f_res_mul = ↑(inst.res_mul.to_nat) := h_flags _,
  have h6  : f_tilde.f_res_add = ↑(inst.res_add.to_nat) := h_flags _,
  have h7  : f_tilde.f_op1_imm = ↑(inst.op1_imm.to_nat) := h_flags _,
  have h8  := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr,
  have h9  := op1_agrees h_off_op0_tilde h_off_op1_tilde h_flags
                h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr,
  have h10 := res_agrees h_off_op0_tilde h_off_op1_tilde
                h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res,
  rw h_t0_eq at h_t1_eq h_next_pc_eq',
  rw h_t1_eq at h_next_pc_eq,
  revert h_next_pc_eq h_next_pc_eq' ,
  rw [instruction.next_pc, h1, h2, h3],
  cases inst.pc_jump_abs; cases inst.pc_jump_rel; cases inst.pc_jnz;
    simp [instruction.next_pc._match_1, option.agrees],
  { rw [instruction.size, h7], intro h, symmetry, exact eq_of_sub_eq_zero h },
  { intros h_next_pc_eq h_next_pc_eq',
    by_cases h : inst.dst mem ⟨pc, ap, fp⟩ = 0,
    { rw [if_pos h],
       cases h_next_pc_eq  with h' h',
      { simp [h8, h] at h',
        contradiction },
      rw [option.agrees],
      rw h7 at h',
      symmetry, exact eq_of_sub_eq_zero h'
    },
    cases h_next_pc_eq' with h' h',
    { rw h8 at h', contradiction },
    { rw [if_neg h],
      revert h9,
      cases inst.op1 mem ⟨pc, ap, fp⟩; simp [option.agrees, instruction.next_pc._match_3],
      rintro rfl,
      symmetry, exact eq_of_sub_eq_zero h' } },
  { revert h10,
    cases inst.res mem ⟨pc, ap, fp⟩;
    simp [option.agrees, instruction.next_pc._match_2],
    rintro rfl,
    intro h', symmetry, exact eq_of_sub_eq_zero h' },
  { intro h, revert h10,
    cases inst.res mem ⟨pc, ap, fp⟩; simp [option.agrees],
    rintro rfl,
    symmetry, exact eq_of_sub_eq_zero h }
end

end

section
include h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res h_next_ap

theorem next_ap_agrees_aux (h : f_tilde.f_opcode_call = 0) :
  (inst.next_ap_aux mem ⟨pc, ap, fp⟩).agrees next_ap :=
begin
  have h1 : f_tilde.f_ap_add = ↑(inst.ap_add.to_nat) := h_flags _,
  have h2 : f_tilde.f_ap_add1 = ↑(inst.ap_add1.to_nat) := h_flags _,
  have h3 := res_agrees h_off_op0_tilde h_off_op1_tilde
                h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res,
  revert h_next_ap,
  rw [instruction.next_ap_aux, h1, h2, h],
  cases inst.ap_add; cases inst.ap_add1;
    simp [instruction.next_ap_aux._match_1, option.agrees]; intro h'; rw h',
  revert h3,
  cases inst.res mem ⟨pc, ap, fp⟩; simp [option.agrees, instruction.next_ap_aux._match_2]
end
end

section
include h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_op0_addr h_mem_op1_addr
include h_op0_addr h_op1_addr h_mul h_res h_next_ap

theorem next_ap_agrees : (inst.next_ap mem ⟨pc, ap, fp⟩).agrees next_ap :=
begin
  have h1 : f_tilde.f_opcode_call = ↑(inst.opcode_call.to_nat) := h_flags _,
  have h2 : f_tilde.f_opcode_ret = ↑(inst.opcode_ret.to_nat) := h_flags _,
  have h3 : f_tilde.f_ap_add = ↑(inst.ap_add.to_nat) := h_flags _,
  have h4 : f_tilde.f_ap_add1 = ↑(inst.ap_add1.to_nat) := h_flags _,
  have h5 := next_ap_agrees_aux h_off_op0_tilde h_off_op1_tilde
                h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res h_next_ap,
  revert h5,
  rw [instruction.next_ap, h1],
  cases inst.opcode_call; cases inst.opcode_ret; cases inst.opcode_assert_eq;
    simp [instruction.next_ap._match_1, option.agrees],
  revert h_next_ap, rw [h1, h3, h4],
  cases inst.ap_add; cases inst.ap_add1;
    simp [instruction.next_ap._match_2, option.agrees],
  apply eq.symm
end
end

section
include h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr h_next_fp

theorem next_fp_agrees : (inst.next_fp mem ⟨pc, ap, fp⟩).agrees next_fp :=
begin
  have h1 : f_tilde.f_opcode_call = ↑(inst.opcode_call.to_nat) := h_flags _,
  have h2 : f_tilde.f_opcode_ret = ↑(inst.opcode_ret.to_nat) := h_flags _,
  have h3  := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr,
  revert next_fp,
  rw [instruction.next_fp, h1, h2],
  cases inst.opcode_call; cases inst.opcode_ret; cases inst.opcode_assert_eq;
    simp [instruction.next_fp._match_1, option.agrees, h3]
end
end

section
include h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
include h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr
include h_dst_addr h_op0_addr h_op1_addr h_mul h_res
include h_opcode_call h_opcode_call' h_opcode_assert_eq

theorem asserts_hold : inst.asserts mem ⟨pc, ap, fp⟩ :=
begin
  have h1 : f_tilde.f_opcode_call = ↑(inst.opcode_call.to_nat) := h_flags _,
  have h2 : f_tilde.f_opcode_ret = ↑(inst.opcode_ret.to_nat) := h_flags _,
  have h3 : f_tilde.f_opcode_assert_eq = ↑(inst.opcode_assert_eq.to_nat) := h_flags _,
  have h4 : f_tilde.f_op1_imm = ↑(inst.op1_imm.to_nat) := h_flags _,
  have h5 := @dst_eq _ _ _ _ _ _ pc _ _ _ _ h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr,
  have h6 := @op0_eq _ _ _ _ _ _ pc _ _ _ _ h_off_op0_tilde h_flags h_mem_op0_addr h_op0_addr,
  have h7 := res_agrees h_off_op0_tilde h_off_op1_tilde
                h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr h_op1_addr h_mul h_res,
  revert h_opcode_call h_opcode_call' h_opcode_assert_eq,
  rw [instruction.asserts, h1, h3],
  cases inst.opcode_call; cases inst.opcode_ret; cases inst.opcode_assert_eq;
    simp [instruction.asserts._match_1, option.agrees, h3, ←h5, ←h6];
    intro h; rw [eq_of_sub_eq_zero h],
  { exact h7 },
  { simp [instruction.size, h4],
    intro h; rw [eq_of_sub_eq_zero h] }
end
end

/-
The main theorem: the constraints imply that the next state is as expected.
-/
variable [decidable_eq F]

theorem next_state_eq :
  next_state mem ⟨pc, ap, fp⟩ ⟨next_pc, next_ap, next_fp⟩ :=
⟨ inst,
  h_mem_pc,
  next_pc_agrees h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
    h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr
    h_dst_addr h_op0_addr h_op1_addr h_mul h_res
    h_t0_eq h_t1_eq h_next_pc_eq h_next_pc_eq',
  next_ap_agrees h_off_op0_tilde h_off_op1_tilde h_flags
    h_mem_op0_addr h_mem_op1_addr
    h_op0_addr h_op1_addr h_mul h_res h_next_ap,
  next_fp_agrees h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr h_next_fp,
  asserts_hold h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
    h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr
    h_dst_addr h_op0_addr h_op1_addr h_mul h_res
    h_opcode_call h_opcode_call' h_opcode_assert_eq ⟩

-- We can use the linter to confirm that there are no extraneous dependencies.
-- #lint
