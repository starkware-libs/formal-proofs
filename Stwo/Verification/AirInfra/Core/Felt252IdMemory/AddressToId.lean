import Verification.AirInfra.Core.Memory

abbrev MemoryAddressToId := Memory 1 1

def MemoryAddressToId.empty : MemoryAddressToId := Memory.empty

/- Semantics -/

abbrev MemoryAddressToIdAssign := MemAssign 1 1
