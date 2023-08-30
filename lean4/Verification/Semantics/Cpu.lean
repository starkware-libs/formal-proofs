/-
Cairo CPU and instructions. Given the memory and the current processor state, this file specifies
the next state relation.

"Undefined" behavior means that it is possible for more than one state to be a valid next state.
When a function has return type `option F`, the value `none` signifies undefined behavior.
-/
import Verification.Semantics.Instruction

noncomputable section

@[ext] structure RegisterState (F : Type _) where
  pc : F
  ap : F
  fp : F

namespace Instruction

variable {F : Type _} [Field F] (i : Instruction) (mem : F → F) (s : RegisterState F)

def size : F := i.op1Imm.toNat + 1

def op0 := cond i.op0Reg (mem (s.fp + i.offOp0.toBiased16)) (mem (s.ap + i.offOp0.toBiased16))

def op1 : Option F :=
  match i.op1Imm, i.op1Fp, i.op1Ap with  -- op1 src
    | false, false, false => some (mem (i.op0 mem s + i.offOp1.toBiased16))
    | true,  false, false => some (mem (s.pc + i.offOp1.toBiased16))
    | false, true,  false => some (mem (s.fp + i.offOp1.toBiased16))
    | false, false, true  => some (mem (s.ap + i.offOp1.toBiased16))
    | _,     _,     _     => none

def resAux : Option F :=
  match i.op1 mem s, i.resAdd, i.resMul with  -- res logic
    | some op1, false, false => some op1
    | some op1, true,  false => some (i.op0 mem s + op1)
    | some op1, false, true  => some (i.op0 mem s * op1)
    | _,        _,     _     => none

-- returns `none` if behavior undefined
def res : Option F :=
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with  -- pc update
    | false, false, false => i.resAux mem s
    | true,  false, false => i.resAux mem s
    | false, true,  false => i.resAux mem s
    | _,     _,     _     => none  -- undefined behavior

def dst := cond i.dstReg (mem (s.fp + i.offDst.toBiased16)) (mem (s.ap + i.offDst.toBiased16))

def nextPc [DecidableEq F] : Option F :=
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with     -- pc update
    | false, false, false => some (s.pc + i.size)  -- next instruction
    | true,  false, false => i.res mem s           -- absolute jump
    | false, true,  false =>
        match i.res mem s with                     -- relative jump
          | some res => some (s.pc + res)
          | none     => none
    | false, false, true  =>
        if i.dst mem s = 0 then                    -- conditional jump
          some (s.pc + i.size)
        else
          match i.op1 mem s with
            | some op1 => some (s.pc + op1)
            | none     => none
    | _,     _,     _     => none

def nextApAux : Option F :=
  match i.apAdd, i.apAdd1 with  -- ap update
    | false, false => some s.ap
    | true,  false =>
        match i.res mem s with
          | some res => some (s.ap + res)
          | none     => none
    | false, true  => some (s.ap + 1)
    | _,     _     => none

def nextAp : Option F :=
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with  -- opcode
    | false, false, false => i.nextApAux mem s
    | true,  false, false =>
        match i.apAdd, i.apAdd1 with                -- call instruction
          | false, false => some (s.ap + 2)
          | _,     _     => none
    | false, true,  false => i.nextApAux mem s      -- ret instruction
    | false, false, true  => i.nextApAux mem s      -- assert equal instruction
    | _, _, _ => none

def nextFp : Option F :=
  -- opcode
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with
    | false, false, false => some s.fp
    | true,  false, false => some (s.ap + 2)       -- call instruction
    | false, true,  false => some (i.dst mem s)    -- ret instruction
    | false, false, true  => some s.fp             -- assert equal instruction
    | _,     _,     _     => none

def Asserts : Prop :=
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with  -- opcode
  | false, false, false => True
  | true,  false, false =>         -- call instruction
      i.op0 mem s = s.pc + i.size ∧ i.dst mem s = s.fp
  | false, true,  false => True    -- ret instruction
  | false, false, true  =>         -- assert equal instruction
      (i.res mem s).Agrees (i.dst mem s)
  | _,     _,     _     => True

variable [DecidableEq F] (t : RegisterState F)

/-- Given instruction `i`, memory `mem`, and state `s`, `t` is a possible next state. -/
protected def NextState : Prop :=
  (i.nextPc mem s).Agrees t.pc ∧
    (i.nextAp mem s).Agrees t.ap ∧ (i.nextFp mem s).Agrees t.fp ∧ i.Asserts mem s

end Instruction

/-- Given memory `mem` and current state `s`, `t` is a possible next state. -/
def NextState {F : Type _} [Field F] [DecidableEq F] (mem : F → F) (s t : RegisterState F) : Prop :=
  ∃ i : Instruction, mem s.pc = ↑i.toNat ∧ i.NextState mem s t
