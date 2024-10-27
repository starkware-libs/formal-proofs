/-
This file provides an assembly language description of Cairo machine instructions, as well as
hackish Lean notation that approximates the Cairo assembly syntax.
-/
import starkware.cairo.lean.semantics.instruction

def checked (x : int) {h₁ : -2^15 ≤ x} {h₂ : x < 2^15} : int := x

notation `'[#` x `]` := @checked x (by norm_num) (by norm_num)

def nat_clip (x : int) : nat := ((x + 2^15).to_nat % 2^16 : nat)

def checked_int_nz (x : ℤ) (h0 : abs x ≠ 0) (h1 : abs x < 2^63) := x

lemma checked_int_nz_eq (x : ℤ) (h0 : abs x ≠ 0) (h1 : abs x < 2^63) :
  checked_int_nz x h0 h1 = x := rfl

meta def abs_lt_tac : tactic unit :=
`[ { rw abs_of_nonneg, norm_num, norm_num } <|> { rw abs_of_nonpos, norm_num, norm_num } ]

notation `'[#nz` x `]` := checked_int_nz x (by norm_num) (by abs_lt_tac)

/-
A more convenient representation of instructions.
-/

structure instr :=
(off_dst   : int)
(off_op0   : int)
(off_op1   : int)
(dst_reg   : bool)
(op0_reg   : bool)
(op1_src   : bool × bool × bool)
(res_logic : bool × bool)
(pc_update : bool × bool × bool)
(ap_update : bool × bool)
(opcode    : bool × bool × bool)

namespace instr

def to_instruction (i : instr) : instruction :=
{ off_dst := bitvec.of_natr 16 (i.off_dst + 2^15).to_nat,
  off_op0 := bitvec.of_natr 16 (i.off_op0 + 2^15).to_nat,
  off_op1 := bitvec.of_natr 16 (i.off_op1 + 2^15).to_nat,
  flags   := { val := [i.dst_reg,
                       i.op0_reg,
                       i.op1_src.1, i.op1_src.2.1, i.op1_src.2.2,
                       i.res_logic.1, i.res_logic.2,
                       i.pc_update.1, i.pc_update.2.1, i.pc_update.2.2,
                       i.ap_update.1, i.ap_update.2,
                       i.opcode.1, i.opcode.2.1, i.opcode.2.2],
               property := rfl } }

def to_nat (i : instr) : nat :=
i.to_instruction.to_nat

@[simp] lemma dst_reg_to_instruction (i : instr) : i.to_instruction.dst_reg = i.dst_reg := rfl
@[simp] lemma op0_reg_to_instruction (i : instr) : i.to_instruction.op0_reg = i.op0_reg := rfl
@[simp] lemma op1_imm_to_instruction (i : instr) : i.to_instruction.op1_imm = i.op1_src.1 := rfl
@[simp] lemma op1_fp_to_instruction (i : instr) : i.to_instruction.op1_fp = i.op1_src.2.1 := rfl
@[simp] lemma op1_ap_to_instruction (i : instr) : i.to_instruction.op1_ap = i.op1_src.2.2 := rfl
@[simp] lemma res_add_to_instruction (i : instr) : i.to_instruction.res_add = i.res_logic.1 := rfl
@[simp] lemma res_mul_to_instruction (i : instr) : i.to_instruction.res_mul = i.res_logic.2 := rfl
@[simp] lemma pc_jump_abs_to_instruction (i : instr) :
                i.to_instruction.pc_jump_abs = i.pc_update.1 := rfl
@[simp] lemma pc_jump_rel_to_instruction (i : instr) :
                i.to_instruction.pc_jump_rel = i.pc_update.2.1 := rfl
@[simp] lemma pc_jnz_to_instruction (i : instr) : i.to_instruction.pc_jnz = i.pc_update.2.2 := rfl
@[simp] lemma ap_add_to_instruction (i : instr) : i.to_instruction.ap_add = i.ap_update.1 := rfl
@[simp] lemma ap_add1_to_instruction (i : instr) : i.to_instruction.ap_add1 = i.ap_update.2 := rfl
@[simp] lemma opcode_call_to_instruction (i : instr) :
                i.to_instruction.opcode_call = i.opcode.1 := rfl
@[simp] lemma opcode_ret_to_instruction (i : instr) :
                i.to_instruction.opcode_ret = i.opcode.2.1 := rfl
@[simp] lemma opcode_assert_eq_to_instruction (i : instr) :
                i.to_instruction.opcode_assert_eq = i.opcode.2.2 := rfl

@[simp] lemma off_dst_to_instruction (i : instr) :
  i.to_instruction.off_dst.to_natr = nat_clip i.off_dst :=
by simp [instr.to_instruction, bitvec.to_natr_of_natr, nat_clip]

@[simp] lemma off_op0_to_instruction (i : instr) :
  i.to_instruction.off_op0.to_natr = nat_clip i.off_op0 :=
by simp [instr.to_instruction, bitvec.to_natr_of_natr, nat_clip]

@[simp] lemma off_op1_to_instruction (i : instr) :
  i.to_instruction.off_op1.to_natr = nat_clip i.off_op1 :=
by simp [instr.to_instruction, bitvec.to_natr_of_natr, nat_clip]

end instr

/-
Model the assembly language.
-/

inductive op0_spec
| ap_plus : int → op0_spec
| fp_plus : int → op0_spec

@[simp] def op0_spec.op0_reg : op0_spec → bool
| (op0_spec.ap_plus i) := ff
| (op0_spec.fp_plus i) := tt

@[simp] def op0_spec.off_op0 : op0_spec → int
| (op0_spec.ap_plus i) := i
| (op0_spec.fp_plus i) := i

inductive op1_spec
| mem_op0_plus : int → op1_spec
| mem_pc_plus  : int → op1_spec
| mem_fp_plus  : int → op1_spec
| mem_ap_plus  : int → op1_spec

@[simp] def op1_spec.op1 : op1_spec → int
| (op1_spec.mem_op0_plus i) := i
| (op1_spec.mem_pc_plus i)  := i
| (op1_spec.mem_fp_plus i)  := i
| (op1_spec.mem_ap_plus i)  := i

@[simp] def op1_spec.op1_imm : op1_spec → bool
| (op1_spec.mem_pc_plus i)  := tt
| _                         := ff

@[simp] def op1_spec.op1_fp : op1_spec → bool
| (op1_spec.mem_fp_plus i)  := tt
| _                         := ff

@[simp] def op1_spec.op1_ap : op1_spec → bool
| (op1_spec.mem_ap_plus i)  := tt
| _                         := ff

inductive res_spec
| op1           : op1_spec → res_spec
| op0_plus_op1  : op1_spec → res_spec
| op0_times_op1 : op1_spec → res_spec

@[simp] def res_spec.res_add : res_spec → bool
| (res_spec.op0_plus_op1 i) := tt
| _                         := ff

@[simp] def res_spec.res_mul : res_spec → bool
| (res_spec.op0_times_op1 i) := tt
| _                          := ff

@[simp] def res_spec.to_op1 : res_spec → op1_spec
| (res_spec.op1 o1)           := o1
| (res_spec.op0_plus_op1 o1)  := o1
| (res_spec.op0_times_op1 o1) := o1

inductive dst_spec
| mem_ap_plus  : int → dst_spec
| mem_fp_plus  : int → dst_spec

@[simp] def dst_spec.dst_reg : dst_spec → bool
| (dst_spec.mem_ap_plus i) := ff
| (dst_spec.mem_fp_plus i) := tt

@[simp] def dst_spec.off_dst : dst_spec → int
| (dst_spec.mem_ap_plus i) := i
| (dst_spec.mem_fp_plus i) := i

def assert_eq_instr (op0 : op0_spec) (res : res_spec) (dst : dst_spec) (ap_update : bool) : instr :=
{ off_dst   := dst.off_dst,
  off_op0   := op0.off_op0,
  off_op1   := res.to_op1.op1,
  dst_reg   := dst.dst_reg,
  op0_reg   := op0.op0_reg,
  op1_src   := (res.to_op1.op1_imm, res.to_op1.op1_fp, res.to_op1.op1_ap),
  res_logic := (res.res_add, res.res_mul),
  pc_update := (ff, ff, ff),
  ap_update := (ff, ap_update),
  opcode    := (ff, ff, tt) }

def jump_instr (jump_abs : bool) (op0 : op0_spec) (res : res_spec) (ap_update : bool) : instr :=
{ off_dst   := -1,
  off_op0   := op0.off_op0,
  off_op1   := res.to_op1.op1,
  dst_reg   := tt,
  op0_reg   := op0.op0_reg,
  op1_src   := (res.to_op1.op1_imm, res.to_op1.op1_fp, res.to_op1.op1_ap),
  res_logic := (res.res_add, res.res_mul),
  pc_update := (jump_abs, bnot jump_abs, ff),
  ap_update := (ff, ap_update),
  opcode    := (ff, ff, ff) }

def jnz_instr (op0 : op0_spec) (op1 : op1_spec) (dst : dst_spec) (ap_update : bool) : instr :=
{ off_dst   := dst.off_dst,
  off_op0   := op0.off_op0,
  off_op1   := op1.op1,
  dst_reg   := dst.dst_reg,
  op0_reg   := op0.op0_reg,
  op1_src   := (op1.op1_imm, op1.op1_fp, op1.op1_ap),
  res_logic := (ff, ff),
  pc_update := (ff, ff, tt),
  ap_update := (ff, ap_update),
  opcode    := (ff, ff, ff) }

def call_instr (call_abs : bool) (res : res_spec) : instr :=
{ off_dst   := 0,
  off_op0   := 1,
  off_op1   := res.to_op1.op1,
  dst_reg   := ff,
  op0_reg   := ff,
  op1_src   := (res.to_op1.op1_imm, res.to_op1.op1_fp, res.to_op1.op1_ap),
  res_logic := (res.res_add, res.res_mul),
  pc_update := (call_abs, bnot call_abs, ff),
  ap_update := (ff, ff),
  opcode    := (tt, ff, ff) }

def ret_instr : instr :=
{ off_dst   := -2,
  off_op0   := -1,
  off_op1   := -1,
  dst_reg   := tt,
  op0_reg   := tt,
  op1_src   := (ff, tt, ff),
  res_logic := (ff, ff),
  pc_update := (tt, ff, ff),
  ap_update := (ff, ff),
  opcode    := (ff, tt, ff) }

def advance_ap_instr (op0 : op0_spec) (res : res_spec) : instr :=
{ off_dst   := -1,
  off_op0   := op0.off_op0,
  off_op1   := res.to_op1.op1,
  dst_reg   := tt,
  op0_reg   := op0.op0_reg,
  op1_src   := (res.to_op1.op1_imm, res.to_op1.op1_fp, res.to_op1.op1_ap),
  res_logic := (res.res_add, res.res_mul),
  pc_update := (ff, ff, ff),
  ap_update := (tt, ff),
  opcode    := (ff, ff, ff) }

/-
Notations for the assembly language.
-/

notation `'op0[ap]`         := op0_spec.ap_plus '[# 0]
notation `'op0[fp]`         := op0_spec.fp_plus '[# 0]
notation `'op0[ap+` i `]`   := op0_spec.ap_plus '[# i]
notation `'op0[fp+` i `]`   := op0_spec.fp_plus '[# i]

notation `'op1[op0]`        := op1_spec.mem_op0_plus '[# 0]
notation `'op1[pc]`         := op1_spec.mem_pc_plus  '[# 0]
notation `'op1[fp]`         := op1_spec.mem_fp_plus  '[# 0]
notation `'op1[ap]`         := op1_spec.mem_ap_plus  '[# 0]
notation `'op1[op0+` i `]`  := op1_spec.mem_op0_plus '[# i]
notation `'op1[pc+` i `]`   := op1_spec.mem_pc_plus  '[# i]
notation `'op1[fp+` i `]`   := op1_spec.mem_fp_plus  '[# i]
notation `'op1[ap+` i `]`   := op1_spec.mem_ap_plus  '[# i]
notation `'op1[imm]`        := op1_spec.mem_pc_plus  '[# 1]

notation `'res[` o1 `]`     := res_spec.op1 o1
notation `'res[op0+` o1 `]` := res_spec.op0_plus_op1 o1
notation `'res[op0*` o1 `]` := res_spec.op0_times_op1 o1

notation `'dst[ap]`         := dst_spec.mem_ap_plus '[# 0]
notation `'dst[fp]`         := dst_spec.mem_fp_plus '[# 0]
notation `'dst[ap+` i `]`   := dst_spec.mem_ap_plus '[# i]
notation `'dst[fp+` i `]`   := dst_spec.mem_fp_plus '[# i]

notation `'assert_eq[op0:=` op0 `,` dst `===` res `]`      := assert_eq_instr op0 res dst ff
notation `'assert_eq[op0:=` op0 `,` dst `===` res `;ap++]` := assert_eq_instr op0 res dst tt
notation `'assert_eq[` dst `===` res `]`      := assert_eq_instr (op0_spec.fp_plus (-1)) res dst ff
notation `'assert_eq[` dst `===` res `;ap++]` := assert_eq_instr (op0_spec.fp_plus (-1)) res dst tt

notation `'jmp_abs[` o1 `]`            := jump_instr tt (op0_spec.fp_plus (-1)) (res_spec.op1 o1) ff
notation `'jmp_abs[+` o0 `,` o1 `]`    := jump_instr tt o0 (res_spec.op0_plus_op1 o1) ff
notation `'jmp_abs[*` o0 `,` o1 `]`    := jump_instr tt o0 (res_spec.op0_times_op1 o1) ff
notation `'jmp_abs[` o1 `;ap++]`       := jump_instr tt (op0_spec.fp_plus (-1)) (res_spec.op1 o1) tt
notation `'jmp_abs[+` o0 `,` o1 `;ap++]` := jump_instr tt o0 (res_spec.op0_plus_op1 o1) tt
notation `'jmp_abs[*` o0 `,` o1 `;ap++]` := jump_instr tt o0 (res_spec.op0_times_op1 o1) tt

notation `'jmp_rel[` o1 `]`            := jump_instr ff (op0_spec.fp_plus (-1)) (res_spec.op1 o1) ff
notation `'jmp_rel[+` o0 `,` o1 `]`    := jump_instr ff o0 (res_spec.op0_plus_op1 o1) ff
notation `'jmp_rel[*` o0 `,` o1 `]`    := jump_instr ff o0 (res_spec.op0_times_op1 o1) ff
notation `'jmp_rel[` o1 `;ap++]`       := jump_instr ff (op0_spec.fp_plus (-1)) (res_spec.op1 o1) tt
notation `'jmp_rel[+` o0 `,` o1 `;ap++]` := jump_instr ff o0 (res_spec.op0_plus_op1 o1) tt
notation `'jmp_rel[*` o0 `,` o1 `;ap++]` := jump_instr ff o0 (res_spec.op0_times_op1 o1) tt

notation `'jnz_rel[` o1 `,` dst `]`      := jnz_instr (op0_spec.fp_plus (-1)) o1 dst ff
notation `'jnz_rel[` o1 `,` dst `;ap++]` := jnz_instr (op0_spec.fp_plus (-1)) o1 dst tt
notation `'jnz_rel[op0:=` op0 `,` o1 `,` dst `]`      := jnz_instr op0 o1 dst ff
notation `'jnz_rel[op0:=` op0 `,` o1 `,` dst `;ap++]` := jnz_instr op0 o1 dst tt

notation `'call_abs[` o1 `]` := call_instr tt (res_spec.op1 o1)
notation `'call_rel[` o1 `]` := call_instr ff (res_spec.op1 o1)

notation `'ret[]` := ret_instr

notation `'ap+=[op0:=` op0 `,` res `]` := advance_ap_instr op0 res
notation `'ap+=[` res `]`              := advance_ap_instr (op0_spec.fp_plus (-1)) res

notation `'assert_eq[op0:=` op0 `,` dst `===` res `]` := assert_eq_instr op0 res dst ff
