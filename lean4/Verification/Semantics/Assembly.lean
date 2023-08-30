/-
This file provides an assembly language description of Cairo machine instructions, as well as
Cairo assembly syntax.

Note: mathlib has a function `Bitvec.toNat` which converts a bitvector to a natural numbers, but
makes bit 0 the msb. The Cairo convention takes bit 0 to be the lsb, so we define `Bitvec.toNatr b`
to be `Bitvec.toNat b.reverse`.
-/
import Verification.Semantics.Instruction

def checked (x : Int) {_ : -2 ^ 15 ≤ x} {_ : x < 2 ^ 15} : Int := x

def natClip (x : Int) : Nat := ((x + 2 ^ 15).toNat % 2 ^ 16 : Nat)

def checkedIntNz (x : ℤ) (_ : abs x ≠ 0) (_ : abs x < 2 ^ 63) := x

theorem checkedIntNz_eq (x : ℤ) (h0 : abs x ≠ 0) (h1 : abs x < 2 ^ 63) :
 checkedIntNz x h0 h1 = x := rfl

macro "abs_lt_tac" : tactic =>
  `(tactic| (rw [abs_of_nonneg]; norm_num; norm_num)) <|>
  `(tactic| (rw [abs_of_nonpos]; norm_num; norm_num))

-- note: we used to have:
-- notation "'[#" x "]" => @checked x (by norm_num) (by norm_num)
-- notation "'[#nz" x "]" => checkedIntNz x (by norm_num) (by abs_lt_tac)
-- now we just expand it in the translation

/-
A more convenient representation of instructions.
-/

structure Instr where
  offDst : Int
  offOp0 : Int
  offOp1 : Int
  dstReg : Bool
  op0Reg : Bool
  op1Src : Bool × Bool × Bool
  resLogic : Bool × Bool
  pcUpdate : Bool × Bool × Bool
  apUpdate : Bool × Bool
  opcode : Bool × Bool × Bool

namespace Instr

variable (i : Instr)

def toInstruction : Instruction
    where
  offDst := Bitvec.ofNatr 16 (i.offDst + 2 ^ 15).toNat
  offOp0 := Bitvec.ofNatr 16 (i.offOp0 + 2 ^ 15).toNat
  offOp1 := Bitvec.ofNatr 16 (i.offOp1 + 2 ^ 15).toNat
  flags :=
    { val :=
        [i.dstReg, i.op0Reg, i.op1Src.1, i.op1Src.2.1, i.op1Src.2.2, i.resLogic.1, i.resLogic.2,
          i.pcUpdate.1, i.pcUpdate.2.1, i.pcUpdate.2.2, i.apUpdate.1, i.apUpdate.2, i.opcode.1,
          i.opcode.2.1, i.opcode.2.2]
      property := rfl }

def toNat : Nat := i.toInstruction.toNat

@[simp] theorem dstReg_toInstruction : i.toInstruction.dstReg = i.dstReg := rfl
@[simp] theorem op0Reg_toInstruction : i.toInstruction.op0Reg = i.op0Reg := rfl
@[simp] theorem op1Imm_toInstruction : i.toInstruction.op1Imm = i.op1Src.1 := rfl
@[simp] theorem op1Fp_toInstruction : i.toInstruction.op1Fp = i.op1Src.2.1 := rfl
@[simp] theorem op1Ap_toInstruction : i.toInstruction.op1Ap = i.op1Src.2.2 := rfl
@[simp] theorem resAdd_toInstruction : i.toInstruction.resAdd = i.resLogic.1 := rfl
@[simp] theorem resMul_toInstruction : i.toInstruction.resMul = i.resLogic.2 := rfl
@[simp] theorem pcJumpAbs_toInstruction : i.toInstruction.pcJumpAbs = i.pcUpdate.1 := rfl
@[simp] theorem pcJumpRel_toInstruction : i.toInstruction.pcJumpRel = i.pcUpdate.2.1 := rfl
@[simp] theorem pcJnz_toInstruction : i.toInstruction.pcJnz = i.pcUpdate.2.2 := rfl
@[simp] theorem apAdd_toInstruction : i.toInstruction.apAdd = i.apUpdate.1 := rfl
@[simp] theorem apAdd1_toInstruction : i.toInstruction.apAdd1 = i.apUpdate.2 := rfl
@[simp] theorem opcodeCall_toInstruction : i.toInstruction.opcodeCall = i.opcode.1 := rfl
@[simp] theorem opcodeRet_toInstruction : i.toInstruction.opcodeRet = i.opcode.2.1 := rfl
@[simp] theorem opcodeAssertEq_toInstruction : i.toInstruction.opcodeAssertEq = i.opcode.2.2 := rfl

@[simp] theorem offDst_toInstruction : i.toInstruction.offDst.toNatr = natClip i.offDst := by
  simp [Instr.toInstruction, Bitvec.toNatr_ofNatr, natClip]

@[simp] theorem offOp0_toInstruction : i.toInstruction.offOp0.toNatr = natClip i.offOp0 := by
  simp [Instr.toInstruction, Bitvec.toNatr_ofNatr, natClip]

@[simp] theorem offOp1_toInstruction : i.toInstruction.offOp1.toNatr = natClip i.offOp1 := by
  simp [Instr.toInstruction, Bitvec.toNatr_ofNatr, natClip]

end Instr

/- Model the assembly language.  -/
inductive Op0Spec
  | ap_plus : Int → Op0Spec
  | fp_plus : Int → Op0Spec

@[simp]
def Op0Spec.op0Reg : Op0Spec → Bool
  | Op0Spec.ap_plus _ => false
  | Op0Spec.fp_plus _ => true

@[simp]
def Op0Spec.offOp0 : Op0Spec → Int
  | Op0Spec.ap_plus i => i
  | Op0Spec.fp_plus i => i

inductive Op1Spec
  | mem_op0_plus : Int → Op1Spec
  | mem_pc_plus : Int → Op1Spec
  | mem_fp_plus : Int → Op1Spec
  | mem_ap_plus : Int → Op1Spec

@[simp]
def Op1Spec.op1 : Op1Spec → Int
  | Op1Spec.mem_op0_plus i => i
  | Op1Spec.mem_pc_plus i => i
  | Op1Spec.mem_fp_plus i => i
  | Op1Spec.mem_ap_plus i => i

@[simp]
def Op1Spec.op1Imm : Op1Spec → Bool
  | Op1Spec.mem_pc_plus _ => true
  | _ => false

@[simp]
def Op1Spec.op1Fp : Op1Spec → Bool
  | Op1Spec.mem_fp_plus _ => true
  | _ => false

@[simp]
def Op1Spec.op1Ap : Op1Spec → Bool
  | Op1Spec.mem_ap_plus _ => true
  | _ => false

inductive ResSpec
  | op1 : Op1Spec → ResSpec
  | op0_plus_op1 : Op1Spec → ResSpec
  | op0_times_op1 : Op1Spec → ResSpec

@[simp]
def ResSpec.resAdd : ResSpec → Bool
  | ResSpec.op0_plus_op1 _=> true
  | _ => false

@[simp]
def ResSpec.resMul : ResSpec → Bool
  | ResSpec.op0_times_op1 _ => true
  | _ => false

@[simp]
def ResSpec.toOp1 : ResSpec → Op1Spec
  | ResSpec.op1 o1 => o1
  | ResSpec.op0_plus_op1 o1 => o1
  | ResSpec.op0_times_op1 o1 => o1

inductive DstSpec
  | mem_ap_plus : Int → DstSpec
  | mem_fp_plus : Int → DstSpec

@[simp]
def DstSpec.dstReg : DstSpec → Bool
  | DstSpec.mem_ap_plus _ => false
  | DstSpec.mem_fp_plus _ => true

@[simp]
def DstSpec.offDst : DstSpec → Int
  | DstSpec.mem_ap_plus i => i
  | DstSpec.mem_fp_plus i => i

def assertEqInstr (op0 : Op0Spec) (res : ResSpec) (dst : DstSpec) (ap_update : Bool) : Instr where
  offDst := dst.offDst
  offOp0 := op0.offOp0
  offOp1 := res.toOp1.op1
  dstReg := dst.dstReg
  op0Reg := op0.op0Reg
  op1Src := (res.toOp1.op1Imm, res.toOp1.op1Fp, res.toOp1.op1Ap)
  resLogic := (res.resAdd, res.resMul)
  pcUpdate := (false, false, false)
  apUpdate := (false, ap_update)
  opcode := (false, false, true)

def jumpInstr (jump_abs : Bool) (op0 : Op0Spec) (res : ResSpec) (ap_update : Bool) : Instr where
  offDst := -1
  offOp0 := op0.offOp0
  offOp1 := res.toOp1.op1
  dstReg := true
  op0Reg := op0.op0Reg
  op1Src := (res.toOp1.op1Imm, res.toOp1.op1Fp, res.toOp1.op1Ap)
  resLogic := (res.resAdd, res.resMul)
  pcUpdate := (jump_abs, not jump_abs, false)
  apUpdate := (false, ap_update)
  opcode := (false, false, false)

def jnzInstr (op0 : Op0Spec) (op1 : Op1Spec) (dst : DstSpec) (ap_update : Bool) : Instr where
  offDst := dst.offDst
  offOp0 := op0.offOp0
  offOp1 := op1.op1
  dstReg := dst.dstReg
  op0Reg := op0.op0Reg
  op1Src := (op1.op1Imm, op1.op1Fp, op1.op1Ap)
  resLogic := (false, false)
  pcUpdate := (false, false, true)
  apUpdate := (false, ap_update)
  opcode := (false, false, false)

def callInstr (call_abs : Bool) (res : ResSpec) : Instr where
  offDst := 0
  offOp0 := 1
  offOp1 := res.toOp1.op1
  dstReg := false
  op0Reg := false
  op1Src := (res.toOp1.op1Imm, res.toOp1.op1Fp, res.toOp1.op1Ap)
  resLogic := (res.resAdd, res.resMul)
  pcUpdate := (call_abs, not call_abs, false)
  apUpdate := (false, false)
  opcode := (true, false, false)

def retInstr : Instr where
  offDst := -2
  offOp0 := -1
  offOp1 := -1
  dstReg := true
  op0Reg := true
  op1Src := (false, true, false)
  resLogic := (false, false)
  pcUpdate := (true, false, false)
  apUpdate := (false, false)
  opcode := (false, true, false)

def advanceApInstr (op0 : Op0Spec) (res : ResSpec) : Instr where
  offDst := -1
  offOp0 := op0.offOp0
  offOp1 := res.toOp1.op1
  dstReg := true
  op0Reg := op0.op0Reg
  op1Src := (res.toOp1.op1Imm, res.toOp1.op1Fp, res.toOp1.op1Ap)
  resLogic := (res.resAdd, res.resMul)
  pcUpdate := (false, false, false)
  apUpdate := (true, false)
  opcode := (false, false, false)

/-
For parsing
-/

namespace Casm

declare_syntax_cat casm_instr
declare_syntax_cat casm_dst
declare_syntax_cat casm_res
declare_syntax_cat casm_op0
declare_syntax_cat casm_op1

/- operand 0 -/
scoped syntax "[ap]"                 : casm_op0
scoped syntax "[fp]"                 : casm_op0
scoped syntax "[ap" " + " num "]"    : casm_op0
scoped syntax "[fp" " + " num "]"    : casm_op0
scoped syntax "[ap" " + " "-"num "]" : casm_op0
scoped syntax "[fp" " + " "-"num "]" : casm_op0

/- operand 1 -/
scoped syntax "[ap]"                         : casm_op1
scoped syntax "[fp]"                         : casm_op1
scoped syntax "[pc]"                         : casm_op1
scoped syntax "[" casm_op0 "]"               : casm_op1
scoped syntax "[ap" " + " num "]"            : casm_op1
scoped syntax "[fp" " + " num "]"            : casm_op1
scoped syntax "[pc" " + " num "]"            : casm_op1
scoped syntax "[" casm_op0 " + " num "]"     : casm_op1
scoped syntax "[ap" " + " "-" num "]"        : casm_op1
scoped syntax "[fp" " + " "-" num "]"        : casm_op1
scoped syntax "[pc" " + " "-" num "]"        : casm_op1
scoped syntax "[" casm_op0 " + " "-" num "]" : casm_op1
scoped syntax num                            : casm_op1
scoped syntax "-" num                        : casm_op1

/- destination-/
scoped syntax "[ap]"                  : casm_dst
scoped syntax "[fp]"                  : casm_dst
scoped syntax "[ap" " + " num "]"     : casm_dst
scoped syntax "[fp" " + " num "]"     : casm_dst
scoped syntax "[ap" " + " "-"num "]"  : casm_dst
scoped syntax "[fp" " + " "-" num "]" : casm_dst

/- result -/
scoped syntax casm_op0 " + "  casm_op1 : casm_res
scoped syntax casm_op0 " * "  casm_op1 : casm_res
scoped syntax casm_op1                 : casm_res

/- instruction -/

scoped syntax:50 casm_dst:51 " = " casm_res:50 ";"                      : casm_instr
scoped syntax:50 casm_dst:51 " = " casm_res:50  "," "ap++" ";"          : casm_instr

scoped syntax "jmp" "abs" casm_res ";"                                 : casm_instr
scoped syntax "jmp" "abs" casm_res "," "ap++" ";"                      : casm_instr
scoped syntax "jmp" "rel" casm_res ";"                                 : casm_instr
scoped syntax "jmp" "rel" casm_res "," "ap++" ";"                      : casm_instr
scoped syntax "jmp" "rel" casm_op1 "if" casm_dst "!= 0" ";"            : casm_instr
scoped syntax "jmp" "rel" casm_op1 "if" casm_dst "!= 0" "," "ap++" ";" : casm_instr
scoped syntax "call" "abs" casm_op1 ";"                                 : casm_instr
scoped syntax "call" "rel" casm_op1 ";"                                 : casm_instr
scoped syntax "ret" ";"                                            : casm_instr
scoped syntax "ap" "+=" casm_res ";"                                    : casm_instr

/- term-level syntax -/

scoped syntax "casm_instr!{" casm_instr "}" : term
scoped syntax "casm_code!{" casm_instr* "}" : term

/-
Parsing rules.
-/

open Lean

def parseChecked (n : TSyntax `term) : MacroM (TSyntax `term) :=
  `(@checked $n (by norm_num) (by norm_num))

def parseOp0 : Syntax → MacroM (TSyntax `term)
  | `(casm_op0| [ap])           => do `(Op0Spec.ap_plus $(← parseChecked (← `(0))))
  | `(casm_op0| [fp])           => do `(Op0Spec.fp_plus $(← parseChecked (← `(0))))
  | `(casm_op0| [ap + $n:num])  => do `(Op0Spec.ap_plus $(← parseChecked n))
  | `(casm_op0| [fp + $n:num])  => do `(Op0Spec.fp_plus $(← parseChecked n))
  | `(casm_op0| [ap + -$n:num]) => do `(Op0Spec.ap_plus $(← parseChecked (← `(- $n))))
  | `(casm_op0| [fp + -$n:num]) => do `(Op0Spec.fp_plus $(← parseChecked (← `(- $n))))
  | _                           => Macro.throwUnsupported

/-- Returns the `op1` specification, possibly an `op0` specification or an immediate value,
    and whether the second argument is an immediate value. -/
def parseOp1 : Syntax → MacroM (TSyntax `term × Option (TSyntax `term) × Bool)
  | `(casm_op1| [ap]) =>
      return (← do `(Op1Spec.mem_ap_plus $(← parseChecked (← `(0)))), none, false)
  | `(casm_op1| [fp]) =>
      return (← do `(Op1Spec.mem_fp_plus $(← parseChecked (← `(0)))), none, false)
  | `(casm_op1| [pc]) =>
      return (← do `(Op1Spec.mem_pc_plus $(← parseChecked (← `(0)))), none, false)
  | `(casm_op1| [ap + $n:num]) =>
      return (← do `(Op1Spec.mem_ap_plus $(← parseChecked n)), none, false)
  | `(casm_op1| [fp + $n:num]) =>
      return (← do `(Op1Spec.mem_fp_plus $(← parseChecked n)), none, false)
  | `(casm_op1| [pc + $n:num]) =>
      return (← do `(Op1Spec.mem_pc_plus $(← parseChecked n)), none, false)
  | `(casm_op1| [ap + -$n:num]) =>
      return (← do `(Op1Spec.mem_ap_plus (-$(← parseChecked n))), none, false)
  | `(casm_op1| [fp + -$n:num]) =>
      return (← do `(Op1Spec.mem_fp_plus (-$(← parseChecked n))), none, false)
  | `(casm_op1| [pc + -$n:num]) =>
      return (← do `(Op1Spec.mem_pc_plus (-$(← parseChecked n))), none, false)
  | `(casm_op1| [$op0:casm_op0]) =>
      return (← do `(Op1Spec.mem_op0_plus $(← parseChecked (← `(0)))), some (← parseOp0 op0), false)
  | `(casm_op1| [$op0:casm_op0 + $n:num]) =>
      return (← do `(Op1Spec.mem_op0_plus $(← parseChecked n)), some (← parseOp0 op0), false)
  | `(casm_op1| [$op0:casm_op0 + -$n:num]) =>
      return (← do `(Op1Spec.mem_op0_plus (-$(← parseChecked n))), some (← parseOp0 op0), false)
  | `(casm_op1| $n:num) =>
      return (← do `(Op1Spec.mem_pc_plus $(← parseChecked (← `(1)))), some n, true)
  | `(casm_op1| -$n:num) =>
      return (← do `(Op1Spec.mem_pc_plus $(← parseChecked (← `(1)))), some (← `(-$(n))), true)
  | _ => Macro.throwUnsupported

def parseDst : Syntax → MacroM (TSyntax `term)
  | `(casm_dst| [ap])           => do `(DstSpec.mem_ap_plus $(← parseChecked (← `(0))))
  | `(casm_dst| [fp])           => do `(DstSpec.mem_fp_plus $(← parseChecked (← `(0))))
  | `(casm_dst| [ap + $n:num])  => do `(DstSpec.mem_ap_plus $(← parseChecked n))
  | `(casm_dst| [fp + $n:num])  => do `(DstSpec.mem_fp_plus $(← parseChecked n))
  | `(casm_dst| [ap + -$n:num]) => do `(DstSpec.mem_ap_plus (-$(← parseChecked n)))
  | `(casm_dst| [fp + -$n:num]) => do `(DstSpec.mem_fp_plus (-$(← parseChecked n)))
  | _                           => Macro.throwUnsupported

-- op0 and res and optional immediate argument
def parseRes : Syntax → MacroM (TSyntax `term × TSyntax `term × Option (TSyntax `term))
  | `(casm_res| $op0:casm_op0 + $op1:casm_op1) => do
      let (top1, t, is_imm) ← parseOp1 op1
      if is_imm then
        return (← parseOp0 op0, ← `(ResSpec.op0_plus_op1 $top1), t)
      else
        return (← parseOp0 op0, ← `(ResSpec.op0_plus_op1 $top1), none)
  | `(casm_res| $op0:casm_op0 * $op1:casm_op1) => do
      let (top1, t?, is_imm) ← parseOp1 op1
      if is_imm then
        return (← parseOp0 op0, ← `(ResSpec.op0_times_op1 $top1), t?)
      else
        return (← parseOp0 op0, ← `(ResSpec.op0_times_op1 $top1), none)
  | `(casm_res| $op1:casm_op1)                 => do
      let (top1, t?, is_imm) ← parseOp1 op1
      if is_imm then
        return (← `(Op0Spec.fp_plus (-1)), ← `(ResSpec.op1 $top1), t?)
      else
        match t? with
          | some t => return (t, ← `(ResSpec.op1 $top1), none)
          | none   => return (← `(Op0Spec.fp_plus (-1)), ← `(ResSpec.op1 $top1), none)
  | _                                         => Macro.throwUnsupported

def parseAssertEq : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| $dst:casm_dst = $res:casm_res;)       => do
      let tdst ← parseDst dst
      let (top0, tres, timm) ← parseRes res
      return (← `(assertEqInstr $top0 $tres $tdst false |>.toNat), timm)
  | `(casm_instr| $dst:casm_dst = $res:casm_res, ap++;) => do
      let tdst ← parseDst dst
      let (top0, tres, timm) ← parseRes res
      return (← `(assertEqInstr $top0 $tres $tdst true |>.toNat), timm)
  | _                                                   => Macro.throwUnsupported

-- With a `jump rel` command, we need to check that the immediate argument is nonzero,
-- i.e. it is not a halt command.
def parseJump : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| jmp abs $res:casm_res;)       => do
      let (top0, tres, timm?) ← parseRes res
      return (← `(jumpInstr true $top0 $tres false |>.toNat), timm?)
  | `(casm_instr| jmp rel $res:casm_res;)       => do
      let (top0, tres, timm?) ← parseRes res
      let some timm := timm? | Macro.throwUnsupported
      return (← `(jumpInstr false $top0 $tres false |>.toNat),
        some (← `(checkedIntNz $timm (by norm_num) (by abs_lt_tac))))
  | `(casm_instr| jmp abs $res:casm_res, ap++;)       => do
      let (top0, tres, timm?) ← parseRes res
      return (← `(jumpInstr true $top0 $tres true |>.toNat), timm?)
  | `(casm_instr| jmp rel $res:casm_res, ap++;)       => do
      let (top0, tres, timm?) ← parseRes res
      let some timm := timm? | Macro.throwUnsupported
      return (← `(jumpInstr false $top0 $tres true |>.toNat),
        some (← `(checkedIntNz $timm (by norm_num) (by abs_lt_tac))))
  | _                                                   => Macro.throwUnsupported

def parseJnz : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| jmp rel $op1: casm_op1 if $dst:casm_dst != 0;)      => do
      let (top1, t?, is_imm) ← parseOp1 op1
      let tdst ← parseDst dst
      if is_imm then
        return (← `(jnzInstr (Op0Spec.fp_plus (-1)) $top1 $tdst false |>.toNat), t?)
      else
        let some t := t? | Macro.throwUnsupported
        return (← `(jnzInstr $t $top1 $tdst false |>.toNat), none)
  | `(casm_instr| jmp rel $op1: casm_op1 if $dst:casm_dst != 0, ap++;) => do
      let (top1, t?, is_imm) ← parseOp1 op1
      let tdst ← parseDst dst
      if is_imm then
        return (← `(jnzInstr (Op0Spec.fp_plus (-1)) $top1 $tdst true |>.toNat), t?)
      else
        let some t := t? | Macro.throwUnsupported
        return (← `(jnzInstr $t $top1 $tdst false |>.toNat), none)
  | _                                                                   => Macro.throwUnsupported

def parseCall : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| call abs $op1:casm_op1;) => do
      let (top1, t?, is_imm) ← parseOp1 op1
      if is_imm then
        return (← `(callInstr true (ResSpec.op1 $top1) |>.toNat), t?)
      else
        return (← `(callInstr true (ResSpec.op1 $top1) |>.toNat), none)
  | `(casm_instr| call rel $op1:casm_op1;) => do
      let (top1, t?, is_imm) ← parseOp1 op1
      if is_imm then
        return (← `(callInstr false (ResSpec.op1 $top1) |>.toNat), t?)
      else
        return (← `(callInstr false (ResSpec.op1 $top1) |>.toNat), none)
  | _                                      => Macro.throwUnsupported

def parseRet : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| ret;) => return (← `(retInstr |>.toNat), none)
  | _                        => Macro.throwUnsupported

def parseAdvanceAp : Syntax → MacroM (TSyntax `term × Option (TSyntax `term))
  | `(casm_instr| ap += $res:casm_res;)       => do
      let (top0, tres, timm) ← parseRes res
      return (← `(advanceApInstr $top0 $tres |>.toNat), timm)
  | _                        => Macro.throwUnsupported

def parseInstr (instr : Syntax) : MacroM (TSyntax `term × Option (TSyntax `term)) :=
  parseAssertEq instr <|> parseJump instr <|> parseJnz instr <|> parseCall instr <|>
    parseRet instr <|> parseAdvanceAp instr

/- Convert an instruction to a term of type `Nat` or `Nat × Nat`. -/

macro_rules
  | `(casm_instr!{$instr:casm_instr}) => do
      let (tinstr, timm?) ← parseInstr instr
      match timm? with
        | some timm => `(Prod.mk $tinstr $timm)
        | none      => return tinstr

/- Convert a program to a list of terms of type `Nat`. -/

-- TODO: understand the performance problem.
-- The first two `macro_rules` implementations are too slow.

-- macro_rules
--   | `(casm_code!{$instrs*}) => do
--     let mut ts : Array (TSyntax `term) := #[]
--     for instr in instrs do
--       let (tinstr, timm?) ← parseInstr instr
--       ts := ts.push tinstr
--       match timm? with
--         | some timm => ts := ts.push timm
--         | none      => continue
--     `([ $ts,* ])

-- def instr_loop : List (TSyntax `casm_instr) → MacroM (List (TSyntax `term))
--   | [] => return []
--   | (instr :: instrs) => do
--       let (tinstr, timm?) ← parseInstr instr
--       let tail ← instr_loop instrs
--       match timm? with
--         | some timm => return tinstr :: timm :: tail
--         | none      => return tinstr :: tail

-- macro_rules
--   | `(casm_code!{$instrs*}) => do
--     --let instrs' := instrs.toList
--     let ts : Array (TSyntax `term) := [].toArray --(← instr_loop instrs').toArray
--     `([ $ts,* ])

def instr_loop : List (TSyntax `casm_instr) → MacroM (TSyntax `term)
  | [] => `(List.nil)
  | (instr :: instrs) => do
      let (tinstr, timm?) ← parseInstr instr
      let tail ← instr_loop instrs
      match timm? with
        | some timm => `(List.cons $tinstr (List.cons $timm $tail))
        | none      => `(List.cons $tinstr $tail)

macro_rules
  | `(casm_code!{$instrs*}) => instr_loop instrs.toList

end Casm
