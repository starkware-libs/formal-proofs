/-
This is a variant of `cpu.lean` that describes the semantics of instructions in terms of the
`vm`. We use the same notion of `instruction`, but now register states and memory vals
are analogues of the Cairo VM's `MaybeRelocatable` vals.

Note: defining addition on values to be addition modulo PRIME causes problems:
- addition is not associative (e.g. `(prog m + val n) + val k`)
- `x + 0 = x` can fail because `val m + 0 = val (m % PRIME)`.
Requiring values to be residues modulo PRIME could be problematic -- it will require checks
everywhere, including, possibly, on segment offsets where we don't have a bound.

Instead, we treat values as integers, but then make the semantics of assertion to be
equality modulo `PRIME`.
-/
import Verification.Semantics.Cpu

noncomputable section

-- TODO(Jeremy): we can add others
inductive Mrel
  | prog : Int → Mrel
  | exec : Int → Mrel
  | rc : Int → Mrel
  | val : Int → Mrel
  | error : Mrel
  deriving DecidableEq

namespace Mrel

def add : Mrel → Mrel → Mrel
  | prog m, val n => prog (m + n)
  | exec m, val n => exec (m + n)
  | rc m,   val n => rc (m + n)
  | val m,  val n => val (m + n)
  | _,      _     => error

def mul : Mrel → Mrel → Mrel
  | val m, val n => val (m * n)
  | _,     _     => error

def neg : Mrel → Mrel
  | val m => val (-m)
  | _     => error

def sub : Mrel → Mrel → Mrel
  | val m,  val n  => val (m - n)
  | prog m, prog n => val (m - n)
  | prog m, val n  => prog (m - n)
  | exec m, exec n => val (m - n)
  | exec m, val n  => exec (m - n)
  | rc m,   rc n   => val (m - n)
  | rc m,   val n  => rc (m - n)
  | _,      _      => error

def IsVal : Mrel → Prop
  | val _ => True
  | _     => False

def IsProg : Mrel → Prop
  | prog _ => True
  | _      => False

def IsExec : Mrel → Prop
  | exec _ => True
  | _      => False

def IsRc : Mrel → Prop
  | rc _ => True
  | _    => False

def toInt : Mrel → Int
  | prog m => m
  | exec m => m
  | rc m   => m
  | val m  => m
  | error  => 0

/-
Note: it's still not a monoid, because. e.g. `0 + prog m = error`.
-/
instance : Add Mrel := ⟨add⟩
instance : Mul Mrel := ⟨mul⟩
instance : Neg Mrel := ⟨neg⟩
instance : Sub Mrel := ⟨sub⟩
instance : Zero Mrel := ⟨val 0⟩
instance : One Mrel := ⟨val 1⟩
instance : Coe Int Mrel := ⟨fun i => val i⟩

theorem add_def (x y : Mrel) : x + y = add x y := rfl
theorem mul_def (x y : Mrel) : x * y = mul x y := rfl
theorem neg_def (x : Mrel) : -x = neg x := rfl
theorem sub_def (x y : Mrel) : x - y = sub x y := rfl
theorem zero_def : (0 : Mrel) = val 0 := rfl
theorem one_def : (1 : Mrel) = val 1 := rfl

@[simp] theorem add_val_zero (a : Mrel) : add a (val 0) = a := by cases a <;> simp [Mrel.add]

-- TODO (Cayden/Jeremy): bit0 and bit1 were deprecated. Delete these?
theorem bit0_val (x : Int) : (val x) + (val x) = val (x + x) := rfl
theorem bit1_val (x : Int) : (val x) + (val x) + 1 = val (x + x + 1) := rfl

protected theorem add_assoc (a b c : Mrel) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> simp only [add_def, add, add_assoc]

@[simp] theorem coe_def (x : Int) : (x : Mrel) = val x := rfl

@[simp] protected theorem add_zero (a : Mrel) : a + val 0 = a := by cases a <;> simp [add_def, add]

theorem sub_val (a : Mrel) (x : Int) : a - val x = a + val (-x) := by
  cases a <;> simp [sub_def, sub, add_def, add, sub_eq_add_neg]

def Equiv (PRIME : Int) : Mrel → Mrel → Prop
  | val m, val n => m % PRIME = n % PRIME
  | prog m, prog n => m = n
  | exec m, exec n => m = n
  | rc m, rc n => m = n
  | _, _ => False

-- NOTE: reflexivity fails on an error
theorem Equiv.refl_val {PRIME : Int} (m : Int) : Equiv PRIME (val m) (val m) := rfl
theorem Equiv.refl_prog {PRIME : Int} (m : Int) : Equiv PRIME (prog m) (prog m) := rfl
theorem Equiv.refl_exec {PRIME : Int} (m : Int) : Equiv PRIME (exec m) (exec m) := rfl
theorem Equiv.refl_rc {PRIME : Int} (m : Int) : Equiv PRIME (rc m) (rc m) := rfl

@[symm]
theorem Equiv.symm {PRIME : Int} {a b : Mrel} (h : Equiv PRIME a b) : Equiv PRIME b a := by
  cases a <;> cases b <;> simp_all [Equiv]

@[trans]
theorem Equiv.trans {PRIME : Int} {a b c : Mrel} (h1 : Equiv PRIME a b) (h2 : Equiv PRIME b c) :
    Equiv PRIME a c := by cases a <;> cases b <;> cases c <;> simp_all [Equiv]

def Agrees (PRIME : Int) : Option Mrel → Mrel → Prop
  | some a, b => Equiv PRIME a b
  | none, _ => True

end Mrel

@[ext]
structure VmRegisterState where
  pc : Int  -- offset to `prog`
  ap : Int  -- offset to `exec`
  fp : Int  -- offset to `exec`

namespace Instruction
open Mrel

variable (PRIME : Int) (i : Instruction) (mem : Mrel → Mrel) (s : VmRegisterState)

def vmSize : Int := i.op1Imm.toNat + 1

def vmOp0 := cond i.op0Reg (mem (exec s.fp + val i.offOp0.toBiased16))
                           (mem (exec s.ap + val i.offOp0.toBiased16))

def vmOp1 : Option Mrel :=
  match i.op1Imm, i.op1Fp, i.op1Ap with  -- op1 src
    | false, false, false => some (mem (i.vmOp0 mem s + val i.offOp1.toBiased16))
    | true,  false, false => some (mem (prog (s.pc + i.offOp1.toBiased16)))
    | false, true,  false => some (mem (exec (s.fp + i.offOp1.toBiased16)))
    | false, false, true  => some (mem (exec (s.ap + i.offOp1.toBiased16)))
    | _,     _,     _     => none

def vmResAux : Option Mrel :=
  match i.vmOp1 mem s, i.resAdd, i.resMul with  -- res logic
    | some op1, false, false => some op1
    | some op1, true,  false => some (i.vmOp0 mem s + op1)
    | some op1, false, true  => some (i.vmOp0 mem s * op1)
    | _,        _,     _     => none

-- returns `none` if behavior undefined
def vmRes : Option Mrel :=
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with  -- pc update
    | false, false, false => i.vmResAux mem s
    | true,  false, false => i.vmResAux mem s
    | false, true,  false => i.vmResAux mem s
    | _,     _,     _     => none  -- undefined behavior


def vmDst :=
  cond i.dstReg (mem (exec s.fp + i.offDst.toBiased16)) (mem (exec s.ap + i.offDst.toBiased16))

/-
Note: we should add assertions that in the various clauses, the
values are in the right segment -- `prog` for absolute junp,
`val` fo relative and conditional jump. Returning `none` won't
do it -- that's nondeterministic behavior.
-/

def vmNextPc : Option Int :=
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with  -- pc update
    | false, false, false => some (s.pc + i.vmSize)           -- next instruction
    | true,  false, false => (i.vmRes mem s).map Mrel.toInt   -- absolute jump
    | false, true,  false =>                                  -- relative jump
        match i.vmRes mem s with
          | some res => some (s.pc + res.toInt)
          | none     => none
    | false, false, true  =>                                  -- conditional jump
        if i.vmDst mem s = 0 then
          some (s.pc + i.vmSize)
        else
          match i.vmOp1 mem s with
            | some op1 => some (s.pc + op1.toInt)
            | none     => none
    | _,     _,     _     => none

-- Not used yet -- see previous comment.
def VmNextPcReqs : Prop :=
  match i.pcJumpAbs, i.pcJumpRel, i.pcJnz with  -- pc update
    | false, false, false => True    -- next instruction
    | true,  false, false =>         -- absolute jump
      match i.vmRes mem s with
        | some res => res.IsProg
        | _        => True
    | false, true,  false =>
        match i.vmRes mem s with     -- relative jump
          | some res => res.IsVal
          | _       => True
    | false, false, true  =>         -- conditional jump
        i.vmDst mem s = 0 ∨
          match i.vmOp1 mem s with
            | some op1 => op1.IsVal
            | _       => False
    | _,     _,     _     => True

def vmNextApAux : Option Int :=
  match i.apAdd, i.apAdd1 with  -- ap update
    | false, false => some s.ap
    | true,  false =>
        match i.vmRes mem s with
          | some res => some (s.ap + res.toInt)
          | _        => none
    | false, true  => some (s.ap + 1)
    | _,     _     => none

def vmNextAp : Option Int :=
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with  -- opcode
    | false, false, false => i.vmNextApAux mem s
    | true,  false, false =>                      -- call instruction
        match i.apAdd, i.apAdd1 with
          | false, false => some (s.ap + 2)
          | _,     _     => none
    | false, true, false  => i.vmNextApAux mem s  -- ret instruction
    | false, false, true  => i.vmNextApAux mem s  -- assert eq instruction
    | _,     _,     _     => none

/- See the comments above -/
def vmNextFp : Option Int :=
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with  -- opcode
    | false, false, false => some s.fp
    | true,  false, false => some (s.ap + 2)             -- call instruction
    | false, true,  false => some (i.vmDst mem s).toInt  -- ret instruction
    | false, false, true  => some s.fp                   -- assert eq instruction
    | _,     _,     _     => none

def VmAsserts : Prop :=
  match i.opcodeCall, i.opcodeRet, i.opcodeAssertEq with  -- opcode
    | false, false, false => True
    | true,  false, false =>        -- call instruction
        i.vmOp0 mem s = prog (s.pc + i.vmSize) ∧ i.vmDst mem s = exec s.fp
    | false, true, false => True    -- ret instruction
    | false, false, true =>         -- assert eq instruction
        Mrel.Agrees PRIME (i.vmRes mem s) (i.vmDst mem s)
    |  _, _, _ => True

variable (t : VmRegisterState)

/-- Given instruction `i`, memory `mem`, and state `s`, `t` is a possible next state. -/
protected def VmNextState : Prop :=
  (i.vmNextPc mem s).Agrees t.pc ∧
    (i.vmNextAp mem s).Agrees t.ap ∧ (i.vmNextFp mem s).Agrees t.fp ∧ i.VmAsserts PRIME mem s

end Instruction

/-- Given memory `mem` and current state `s`, `t` is a possible next state. -/
def VmNextState (PRIME : Int) (mem : Mrel → Mrel) (s t : VmRegisterState) : Prop :=
  ∃ i : Instruction, mem (Mrel.prog s.pc) = Mrel.val ↑i.toNat ∧ i.VmNextState PRIME mem s t
