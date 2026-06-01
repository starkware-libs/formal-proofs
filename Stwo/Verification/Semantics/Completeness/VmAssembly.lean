import Verification.Semantics.Assembly
import Verification.Semantics.Vm

/-
  The macros below are identical to micros defined in Assembly.lean except that the types are different.
  TO DO: use the same code for both.
-/

open Mrel

def ProgAt (mem : Mrel → Mrel) : List Int → Int → Prop
  | [], _  => true
  | (v :: l), pc => mem (prog pc) = val v ∧ ProgAt mem l (pc + 1)

namespace Casm
open Lean Elab Command

local syntax "stop_at_first_error" (ppLine command)* : command
open Command in elab_rules : command
  | `(stop_at_first_error $[$cmds]*) => do
    for cmd in cmds do
      elabCommand cmd.raw
      if (← get).messages.hasErrors then break

local macro "vm_instr_def0" code:ident instr:term : command =>
  `(stop_at_first_error
    theorem $(mkIdent `hmem0) {mem : Mrel → Mrel} {pos : Int} (hmem : ProgAt mem $code pos) : mem (prog pos) = $instr := by
      refine Eq.trans ?_ hmem.1; rfl)

local macro "vm_instr_def" code:ident aux:ident thm:ident auxpred:ident n:num instr:term : command =>
  `(stop_at_first_error
    def $aux {mem : Mrel → Mrel} {pos : Int} (hmem : ProgAt mem $code pos):= ($auxpred hmem).2
    theorem $thm {mem : Mrel → Mrel} {pos : Int} (hmem : ProgAt mem $code pos) : mem (prog (pos + $n)) = Mrel.val $instr := by
      refine Eq.trans ?_ ($aux hmem).1; casm_cleanup_tac)

elab "vm_casm_code_def" e:ident " := " "{" instrs:casm_instr* "}" : command => do
  elabCommand <| <-
    `(command| def $e : List Int  := casm_code!{ $instrs:casm_instr* })
  elabCommand <| <- `(command| namespace $e)
  let mut n : Nat := 0
  for instr in instrs do
    let (tinstr, timm?) ← liftMacroM <| parseInstr instr
    if n = 0 then
      elabCommand <| <- `(command| vm_instr_def0 $e $tinstr)
    else
      let aux := mkIdent s!"haux{n-1}".toName
      let thm := mkIdent s!"hmem{n}".toName
      let auxpred := if n = 1 then mkIdent ``id else mkIdent s!"haux{n-2}".toName
      let nlit := Syntax.mkNumLit (toString n)
      elabCommand <| <- `(command| vm_instr_def $e $aux $thm $auxpred $nlit $tinstr)
    n := n + 1
    match timm? with
      | some timm =>
          let aux := mkIdent s!"haux{n-1}".toName
          let thm := mkIdent s!"hmem{n}".toName
          let auxpred := if n = 1 then mkIdent ``id else mkIdent s!"haux{n-2}".toName
          let nlit := Syntax.mkNumLit (toString n)
          elabCommand <| <- `(command| vm_instr_def $e $aux $thm $auxpred $nlit $timm)
          n := n + 1
      | none      => pure ()
  elabCommand <| <- `(command| end $e)

end Casm
