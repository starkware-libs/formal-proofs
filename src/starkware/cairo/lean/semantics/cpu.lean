/-
Cairo CPU and instructions. Given the memory and the current processor state, this file specifies
the next state relation.

"Undefined" behavior means that it is possible for more than one state to be a valid next state.
When a function has return type `option F`, the value `none` signifies undefined behavior.

Note: mathlib has a function `bitvec.to_nat` which converts a bitvector to a natural numbers, but
makes bit 0 the msb. The Cairo convention takes bit 0 to be the lsb, so we define `bitvec.to_natr b`
to be `bitvec.to_nat b.reverse`.
-/
import starkware.cairo.lean.semantics.instruction

noncomputable theory

@[ext]
structure register_state (F : Type*) :=
(pc : F)
(ap : F)
(fp : F)

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
