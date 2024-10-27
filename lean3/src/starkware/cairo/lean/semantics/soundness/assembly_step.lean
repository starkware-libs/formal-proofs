/-
This file does the following proves theorems characterizing the next state for each
assembly language instruction, simply by unfolding it to the machine instruction and
unraveling the CPU semantics.
-/
import starkware.cairo.lean.semantics.cpu
import starkware.cairo.lean.semantics.assembly

/-- Lifts the `next_state` semantics from machine instructions to assembly instructions. -/
def instr.next_state {F : Type*} [field F] [decidable_eq F]
  (i : instr) (mem : F → F) (s t : register_state F) :=
i.to_instruction.next_state mem s t

/-
Functions for clipping natural numbers and integers to the right range.
-/

section
variables {F : Type*} [field F]

def int_clip (x : int) : F := nat_clip x - 2^15

lemma int_clip_eq {x : int} (h₁ : -2^15 ≤ x) (h₂ : x < 2^15) : (int_clip x : F) = x :=
begin
  have h : (x + 2^15).to_nat ≤ 2^16 - 1,
  { rw [int.to_nat_le, int.coe_nat_sub],
    apply int.le_sub_one_of_lt,
    apply lt_of_lt_of_le (add_lt_add_right h₂ _),
    norm_num, norm_num },
  rw [int_clip, nat_clip, nat.mod_eq_of_lt],
  have h' : x = ((x + 2 ^ 15).to_nat : ℤ) - 2^15,
  { apply eq_sub_of_add_eq, rw [int.to_nat_of_nonneg], linarith },
  conv { to_rhs, rw h' }, simp,
  apply nat.lt_of_succ_le,
  convert nat.succ_le_succ h
end

lemma int_clip_eq' (x : int) : int_clip x = ((nat_clip x - 2^15 : int) : F) :=
by simp [int_clip]

@[simp] theorem int.zero_clip : int_clip 0 = (0 : F) :=
by rw int_clip_eq; norm_num

@[simp] lemma clip_checked (x : int) (h₁ :-2^15 ≤ x) (h₂ : x < 2^15) :
  (int_clip (@checked x h₁ h₂) : F) = ↑x := int_clip_eq h₁ h₂

end

/-
Semantics of the assembly language.
-/

section

variables {F : Type*} [field F]
variable mem : F → F
variables s t : register_state F
variables (op0 : op0_spec) (res : res_spec) (dst : dst_spec) (ap_update : bool)

@[simp] def bump_ap : bool → F
| tt := s.ap + 1
| ff := s.ap

@[simp] def compute_op0 : op0_spec → F
| (op0_spec.ap_plus i) := mem (s.ap + int_clip i)
| (op0_spec.fp_plus i) := mem (s.fp + int_clip i)

@[simp] def compute_op1 : op1_spec → F
| (op1_spec.mem_op0_plus i) := mem (compute_op0 mem s op0 + int_clip i)
| (op1_spec.mem_pc_plus i)  := mem (s.pc + int_clip i)
| (op1_spec.mem_fp_plus i)  := mem (s.fp + int_clip i)
| (op1_spec.mem_ap_plus i)  := mem (s.ap + int_clip i)

@[simp] def compute_dst : dst_spec → F
| (dst_spec.mem_ap_plus i) := mem (s.ap + int_clip i)
| (dst_spec.mem_fp_plus i) := mem (s.fp + int_clip i)

@[simp] def compute_res : res_spec → F
| (res_spec.op1 o1)           := compute_op1 mem s op0 o1
| (res_spec.op0_plus_op1 o1)  := compute_op0 mem s op0 + compute_op1 mem s op0 o1
| (res_spec.op0_times_op1 o1) := compute_op0 mem s op0 * compute_op1 mem s op0 o1

@[simp] def bump_pc : bool → F
| ff := s.pc + 1
| tt := s.pc + 2

@[simp] def jump_pc : bool → F → F
| ff i := s.pc + i
| tt i := i

@[simp] lemma instruction_next_ap_aux_match_eq (i : instruction) :
  (instruction.next_ap_aux._match_1 i mem s ff ap_update) = some (bump_ap s ap_update) :=
by cases ap_update; { simp [instruction.next_ap_aux._match_1] }

lemma instruction_op1_match_eq (i : instruction) (op1 : op1_spec) (h : i.op0_reg = op0.op0_reg)
    (h' : i.off_op0.to_natr = nat_clip op0.off_op0)
    (h'' : i.off_op1.to_natr = nat_clip op1.op1) :
  (instruction.op1._match_1 i mem s op1.op1_imm op1.op1_fp op1.op1_ap) =
    some (compute_op1 mem s op0 op1) :=
begin
  cases op1 with op1 op1 op1 op1; simp [instruction.op1._match_1, instruction.op0, h];
    cases op0 with op0 op0; simp [bitvec.to_biased_16, h', h'']; refl
end

lemma instruction_res_aux_match_eq (i : instruction) (h : i.op0_reg = op0.op0_reg)
    (h' : i.off_op0.to_natr = nat_clip op0.off_op0) :
  instruction.res_aux._match_1 i mem s
      (some (compute_op1 mem s op0 res.to_op1)) res.res_add res.res_mul =
    some (compute_res mem s op0 res) :=
begin
  cases res with op1 op1 op1; simp [instruction.res_aux._match_1, instruction.op0, h, h'];
  cases op0 with op0 op0; simp [h', bitvec.to_biased_16]; try {refl}; {left, refl}
end

variable [decidable_eq F]

theorem next_state_assert_eq :
  (assert_eq_instr op0 res dst ap_update).next_state mem s t ↔
     (t.pc = bump_pc s res.to_op1.op1_imm ∧
      t.ap = bump_ap s ap_update ∧
      t.fp = s.fp ∧
      compute_dst mem s dst = compute_res mem s op0 res) :=
begin
  simp [instr.next_state, assert_eq_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux],
  apply and_congr, { cases res.to_op1.op1_imm; simp; split; apply eq.symm },
  repeat { apply and_congr, split; apply eq.symm },
  transitivity ((some (compute_res mem s op0 res)).agrees (compute_dst mem s dst)),
  swap, { split; apply eq.symm },
  congr',
  { simp [instruction.res, instruction.res_aux, instruction.op1],
    convert (instruction_res_aux_match_eq mem s op0 res _ _ _); try {simp},
    convert (instruction_op1_match_eq mem s op0 _ _ _ _ _); simp [nat_clip] },
  cases dst; simp [bitvec.to_biased_16]; refl
end

theorem next_state_jump (jump_abs : bool) :
  (jump_instr jump_abs op0 res ap_update).next_state mem s t ↔
    (t.pc = jump_pc s jump_abs (compute_res mem s op0 res) ∧
     t.ap = bump_ap s ap_update ∧
     t.fp = s.fp) :=
begin
  simp [instr.next_state, jump_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux],
  apply and_congr, swap,
  { split; rintros ⟨h1, h2⟩; rw [h1, h2]; split; trivial },
  apply option.agrees_iff_of_eq_some,
  cases jump_abs; simp [instruction.next_pc._match_1, instruction.res, instruction.res_aux],
  swap,
  { convert (instruction_res_aux_match_eq mem s op0 res _ _ _); try {simp},
    convert (instruction_op1_match_eq mem s op0 _ _ _ _ _); simp [nat_clip] },
  transitivity (instruction.next_pc._match_2 s (some (compute_res mem s op0 res))),
  swap, { refl }, congr',
  convert (instruction_res_aux_match_eq mem s op0 res _ _ _); try {simp},
  convert (instruction_op1_match_eq mem s op0 _ _ _ _ _); simp [nat_clip]
end

theorem next_state_jnz (op1 : op1_spec) :
  (jnz_instr op0 op1 dst ap_update).next_state mem s t ↔
    ((t.pc = if compute_dst mem s dst = 0 then
               bump_pc s op1.op1_imm
             else
               s.pc + compute_op1 mem s op0 op1) ∧
      t.ap = bump_ap s ap_update ∧
      t.fp = s.fp) :=
begin
  simp [instr.next_state, jnz_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux],
  apply and_congr, swap,
  { split; rintros ⟨h1, h2⟩; rw [h1, h2]; split; trivial },
  apply option.agrees_iff_of_eq_some, rw option.some_if,
  congr',
  { cases dst with dst_reg dst_off; simp [bitvec.to_biased_16]; refl },
  { cases op1.op1_imm; simp; refl },
  transitivity (instruction.next_pc._match_3 s (some (compute_op1 mem s op0 op1))),
  swap, { refl }, congr',
  convert (instruction_op1_match_eq mem s op0 _ _ _ _ _); simp [nat_clip]
end

theorem next_state_call (call_abs : bool) :
  (call_instr call_abs res).next_state mem s t ↔
    (t.pc = jump_pc s call_abs (compute_res mem s (op0_spec.ap_plus 1) res) ∧
     t.ap = s.ap + 2 ∧
     t.fp = s.ap + 2 ∧
     mem (s.ap + 1) = bump_pc s res.to_op1.op1_imm ∧
     mem s.ap = s.fp) :=
begin
  simp [instr.next_state, call_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux],
  apply and_congr, swap,
  { apply and_congr, { split; intro h; rw h },
    apply and_congr, { split; intro h; rw h },
    apply and_congr,
      { simp [instruction.op0, instruction.off_op0],
        rw [bitvec.to_biased_16, instr.off_op0_to_instruction], dsimp,
        rw [←int_clip_eq', @int_clip_eq]; norm_num,
        cases res.to_op1.op1_imm; simp, refl },
    rw [bitvec.to_biased_16, instr.off_dst_to_instruction], dsimp,
    rw [←int_clip_eq', @int_clip_eq]; norm_num },
  apply option.agrees_iff_of_eq_some,
  cases call_abs; simp [instruction.next_pc._match_1, instruction.res, instruction.res_aux],
  { transitivity (instruction.next_pc._match_2 s (some (compute_res mem s 'op0[ap+ 1] res))),
    swap, { refl }, congr',
    convert (instruction_res_aux_match_eq mem s 'op0[ap+ 1] res _ _ _); try { simp [checked] },
    convert (instruction_op1_match_eq mem s 'op0[ap+ 1] _ _ _ _ _); simp [nat_clip, checked] },
  convert (instruction_res_aux_match_eq mem s 'op0[ap+ 1] res _ _ _); try { simp [checked] },
  convert (instruction_op1_match_eq mem s 'op0[ap+ 1] _ _ _ _ _); simp [nat_clip, checked],
end

theorem next_state_ret :
  ret_instr.next_state mem s t ↔
    (t.pc = mem (s.fp + -1) ∧
     t.ap = s.ap ∧
     t.fp = mem (s.fp - 2)) :=
begin
  simp [instr.next_state, ret_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux, instruction.res,
    instruction.res_aux, instruction.res_aux._match_1, instruction.op1],
  rw [bitvec.to_biased_16, instr.off_op1_to_instruction], dsimp,
  rw [bitvec.to_biased_16, instr.off_dst_to_instruction], dsimp,
  rw [←int_clip_eq', ←int_clip_eq', int_clip_eq, int_clip_eq, sub_eq_add_neg]; norm_num,
  repeat { apply and_congr, split; apply eq.symm },
  split; apply eq.symm
end

theorem next_state_advance_ap :
  (advance_ap_instr op0 res).next_state mem s t ↔
     (t.pc = bump_pc s res.to_op1.op1_imm ∧
      t.ap = s.ap + compute_res mem s op0 res ∧
      t.fp = s.fp) :=
begin
  simp [instr.next_state, advance_ap_instr, instruction.next_state, option.agrees,
    instruction.next_pc, instruction.size, instruction.next_fp, instruction.next_ap,
    instruction.asserts, instruction.dst, instruction.next_ap_aux, instruction.res,
    instruction.res_aux, instruction.op1],
  apply and_congr, { cases res.to_op1.op1_imm; simp; split; apply eq.symm },
  apply and_congr, swap, { split; apply eq.symm },
  apply option.agrees_iff_of_eq_some,
  have : ∀ (s : register_state F) x y, x = some y →
      instruction.next_ap_aux._match_2 s x = some (s.ap + y),
  { rintros s x y rfl, simp [instruction.next_ap_aux._match_2] },
  apply this s,
  convert (instruction_res_aux_match_eq mem s op0 res _ _ _); try {simp},
  convert (instruction_op1_match_eq mem s op0 _ _ _ _ _); simp [nat_clip]
end

end
