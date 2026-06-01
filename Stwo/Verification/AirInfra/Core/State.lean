/-
The state keeps track of all the state variables that have been declared. For deductions, it is
important to know how to compute them, but for soundness, we only need to know how many state
variables there are.
-/
import Lean.Data.Json.FromToJson

structure State where
  len : Nat
deriving Lean.ToJson, Lean.FromJson

namespace State

def empty : State := ⟨0⟩

def add (state : State) : State × Nat :=
  let len := state.len
  (⟨len+1⟩, len)

def add_n (state : State) (n : Nat) : State × Nat :=
  let len := state.len
  (⟨len+n⟩, len)

end State
