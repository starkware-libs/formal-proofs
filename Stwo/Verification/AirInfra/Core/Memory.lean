import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.LookupTerm
import Verification.AirInfra.Core.Expressions.Felt252Expr

/-- Stores a table of lookups with given input and output size. -/
def Memory (inputSize outputSize : Nat) := LookupData (inputSize + outputSize)

instance (inputSize outputSize : Nat) : GetElem (Memory inputSize outputSize) Nat (Fin (inputSize + outputSize) → FeltExpr)
    (fun l i => i < Array.size l) := by
  unfold Memory; infer_instance

instance (inputSize outputSize : Nat) : Lean.ToJson (Memory inputSize outputSize) := by
  unfold Memory; infer_instance

instance (inputSize outputSize : Nat) : Lean.FromJson (Memory inputSize outputSize) := by
  unfold Memory; infer_instance

namespace Memory

def empty {inputSize outputSize : Nat} : Memory inputSize outputSize := LookupData.empty

protected def mem_verify {inputSize outputSize : Nat}
    (memory : Memory inputSize outputSize)
    (index : Fin inputSize → FeltExpr)
    (value : Fin outputSize → FeltExpr) : Memory inputSize outputSize :=
  LookupData.add memory (Fin.append index value)

def display {inputSize outputSize : Nat} (memory : Memory inputSize outputSize) : IO Unit :=
  for h:i in [:memory.size] do
    let indexAndValue := Array.ofFn memory[i]
    for h':j in [:indexAndValue.size] do
      IO.print s!"{indexAndValue[j]}"
      if j < indexAndValue.size - 1 then
        if j = inputSize - 1 then
          IO.print " -> "
        else
          IO.print ", "
    IO.println ""

end Memory

/-
Semantics.
-/

def MemAssign (inputSize outputSize : Nat) :=
  (Fin inputSize → Felt) → Option (Fin outputSize → Felt)

namespace Memory
variable {inputSize outputSize : Nat} [Fact (Nat.Prime Stwo.P)]

def SatisfiedBy (memory : Memory inputSize outputSize)
    (varAssign : VarAssign) (memAssign : MemAssign inputSize outputSize) : Prop :=
  LookupData.SatisfiedBy memory varAssign <|
    {p : (Fin inputSize → Felt) × (Fin outputSize → Felt) | memAssign p.1 = some p.2}.image
      fun p => Fin.append p.1 p.2

@[simp]
theorem add_SatisfiedBy (memory : Memory inputSize outputSize)
    (index : Fin inputSize → FeltExpr)
    (value : Fin outputSize → FeltExpr)
    (varAssign : VarAssign) (memAssign : MemAssign inputSize outputSize) :
  (memory.mem_verify index value).SatisfiedBy varAssign memAssign ↔
    (memory.SatisfiedBy varAssign memAssign ∧
      memAssign (fun i => (index i).eval varAssign) = some fun i => (value i).eval varAssign) := by
  simp only [SatisfiedBy, Memory.mem_verify, LookupData.add_SatisfiedBy, and_congr_right_iff]
  intro _
  rw [Set.mem_image]; simp only [Set.mem_setOf_eq, Prod.exists]
  constructor
  . rintro ⟨index', value', h1, h2⟩
    change _ = FeltExpr.eval varAssign ∘ Fin.append index value at h2
    rw [←Fin.append_comp] at h2
    convert h1 using 2
    . symm; apply Fin.append_inj_left h2
    . symm; apply Fin.append_inj_right h2
  . intro h
    refine ⟨_, _, h, ?_⟩
    apply Fin.append_comp


end Memory
