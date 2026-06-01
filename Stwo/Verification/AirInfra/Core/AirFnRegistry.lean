/-
For each air function, the registry keeps track of all the functions it depends on. We don't seem
to need this information. The one bit of information we do need is the number of temporary
variables that have been declared for use in the constraints.
-/
import Lean.Data.Json.FromToJson

structure AirFnRegistry where
  intermediateIndex : Nat
deriving Lean.ToJson, Lean.FromJson

abbrev INTERMEDIATE_VAR_PREFIX := "tmp_"

namespace AirFnRegistry

def empty : AirFnRegistry := ⟨0⟩

def get_intermediate_index (airFnRegistry : AirFnRegistry) : AirFnRegistry × Nat :=
  let index := airFnRegistry.intermediateIndex
  (⟨index+1⟩, index)

end AirFnRegistry
