/-
Cairo CPU and instructions. Given the memory and the current processor state, this file specifies
the next state relation.

"Undefined" behavior means that it is possible for more than one state to be a valid next state.
When a function has return type `option F`, the value `none` signifies undefined behavior.

Note: mathlib has a function `bitvec.to_nat` which converts a bitvector to a natural numbers, but
makes bit 0 the msb. The Cairo convention takes bit 0 to be the lsb, so we define `bitvec.to_natr b`
to be `bitvec.to_nat b.reverse`.
-/
import starkware.cairo.lean.semantics.util

noncomputable theory

@[ext]
structure register_state (F : Type*) :=
(pc : F)
(ap : F)
(fp : F)

@[derive decidable_eq, ext]
structure instruction :=
(off_dst : bitvec 16)
(off_op0 : bitvec 16)
(off_op1 : bitvec 16)
(flags   : bitvec 15)

-- flag bits
notation `DST_REG`          := 0
notation `OP0_REG`          := 1
notation `OP1_IMM`          := 2
notation `OP1_FP`           := 3
notation `OP1_AP`           := 4
notation `RES_ADD`          := 5
notation `RES_MUL`          := 6
notation `PC_JUMP_ABS`      := 7
notation `PC_JUMP_REL`      := 8
notation `PC_JNZ`           := 9
notation `AP_ADD`           := 10
notation `AP_ADD1`          := 11
notation `OPCODE_CALL`      := 12
notation `OPCODE_RET`       := 13
notation `OPCODE_ASSERT_EQ` := 14

namespace instruction

variable i : instruction

def dst_reg     := i.flags.nth DST_REG
def op0_reg     := i.flags.nth OP0_REG
def op1_imm     := i.flags.nth OP1_IMM                  -- op1 src
def op1_fp      := i.flags.nth OP1_FP                   -- op1 src
def op1_ap      := i.flags.nth OP1_AP                   -- op1 src
def res_add     := i.flags.nth RES_ADD                  -- res logic
def res_mul     := i.flags.nth RES_MUL                  -- res logic
def pc_jump_abs := i.flags.nth PC_JUMP_ABS              -- pc update
def pc_jump_rel := i.flags.nth PC_JUMP_REL              -- pc update
def pc_jnz      := i.flags.nth PC_JNZ                   -- pc update
def ap_add      := i.flags.nth AP_ADD                   -- ap update
def ap_add1     := i.flags.nth AP_ADD1                  -- ap update
def opcode_call := i.flags.nth OPCODE_CALL              -- opcode
def opcode_ret  := i.flags.nth OPCODE_RET               -- opcode
def opcode_assert_eq := i.flags.nth OPCODE_ASSERT_EQ    -- opcode

def to_nat (inst : instruction) : ℕ :=
           inst.off_dst.to_natr +
    2^16 * inst.off_op0.to_natr +
    2^32 * inst.off_op1.to_natr +
    2^48 * inst.flags.to_natr

end instruction

namespace instruction

variables {F : Type*} [field F]
variable  i : instruction
variable  mem : F → F
variables s : register_state F

def size : F :=
i.op1_imm.to_nat + 1

def op0 :=
cond i.op0_reg
  (mem (s.fp + i.off_op0.to_biased_16))
  (mem (s.ap + i.off_op0.to_biased_16))

def op1 : option F :=
match /- op1 src -/ i.op1_imm, i.op1_fp, i.op1_ap with
| ff, ff, ff := some (mem (i.op0 mem s + i.off_op1.to_biased_16))
| tt, ff, ff := some (mem (s.pc + i.off_op1.to_biased_16))
| ff, tt, ff := some (mem (s.fp + i.off_op1.to_biased_16))
| ff, ff, tt := some (mem (s.ap + i.off_op1.to_biased_16))
| _,  _,  _  := none
end

def res_aux : option F :=
match /- res logic -/ i.op1 mem s, i.res_add, i.res_mul with
| some op1, ff, ff := some op1
| some op1, tt, ff := some (i.op0 mem s + op1)
| some op1, ff, tt := some (i.op0 mem s * op1)
| _,        _,  _  := none
end

-- returns `none` if behavior undefined
def res : option F :=
match /- pc update -/ i.pc_jump_abs, i.pc_jump_rel, i.pc_jnz with
| ff, ff, ff := i.res_aux mem s
| tt, ff, ff := i.res_aux mem s
| ff, tt, ff := i.res_aux mem s
| _,  _,  _  := none    -- undefined behavior
end

def dst :=
cond i.dst_reg
  (mem (s.fp + i.off_dst.to_biased_16))
  (mem (s.ap + i.off_dst.to_biased_16))

def next_pc [decidable_eq F] : option F :=
match /- pc update -/ i.pc_jump_abs, i.pc_jump_rel, i.pc_jnz with
| ff, ff, ff := some (s.pc + i.size)                 -- next instruction
| tt, ff, ff := i.res mem s                          -- absolute jump
| ff, tt, ff := match i.res mem s with               -- relative jump
                | some res := some (s.pc + res)
                | none     := none
                end
| ff, ff, tt := if i.dst mem s = 0 then              -- conditional jump
                  some (s.pc + i.size)
                else
                  match i.op1 mem s with
                  | some op1 := some (s.pc + op1)
                  | none     := none
                  end
| _,  _,  _  := none
end

def next_ap_aux : option F :=
match i.ap_add, i.ap_add1 with    -- ap update
| ff, ff := some s.ap
| tt, ff := match i.res mem s with
            | some res := some (s.ap + res)
            | none     := none
            end
| ff, tt := some (s.ap + 1)
| _,  _  := none
end

def next_ap : option F :=
match /- opcode -/ i.opcode_call, i.opcode_ret, i.opcode_assert_eq with
| ff, ff, ff := i.next_ap_aux mem s
| tt, ff, ff := match i.ap_add, i.ap_add1 with                    -- call instruction
                | ff, ff := some (s.ap + 2)
                | _,  _  := none
                end
| ff, tt, ff := i.next_ap_aux mem s                               -- ret instruction
| ff, ff, tt := i.next_ap_aux mem s                               -- assert equal instruction
| _,  _,  _  := none
end

def next_fp : option F :=
match /- opcode -/ i.opcode_call, i.opcode_ret, i.opcode_assert_eq with
| ff, ff, ff := some s.fp
| tt, ff, ff := some (s.ap + 2)                                   -- call instruction
| ff, tt, ff := some (i.dst mem s)                                -- ret instruction
| ff, ff, tt := some s.fp                                         -- assert equal instruction
| _,  _,  _  := none
end

def asserts : Prop :=
match /- opcode -/ i.opcode_call, i.opcode_ret, i.opcode_assert_eq with
| ff, ff, ff := true
| tt, ff, ff := i.op0 mem s = s.pc + i.size ∧ i.dst mem s = s.fp  -- call instruction
| ff, tt, ff := true                                              -- ret instruction
| ff, ff, tt := (i.res mem s).agrees (i.dst mem s)                -- assert equal instruction
| _,  _,  _  := true
end

variables [decidable_eq F] (t : register_state F)

/-- Given instruction `i`, memory `mem`, and state `s`, `t` is a possible next state. -/
def next_state : Prop :=
(i.next_pc mem s).agrees t.pc ∧
(i.next_ap mem s).agrees t.ap ∧
(i.next_fp mem s).agrees t.fp ∧
i.asserts mem s

end instruction

/-- Given memory `mem` and current state `s`, `t` is a possible next state. -/
def next_state {F : Type*} [field F] [decidable_eq F] (mem : F → F) (s t : register_state F) :
  Prop :=
∃ i : instruction, mem s.pc = ↑i.to_nat ∧ i.next_state mem s t
