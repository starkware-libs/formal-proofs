import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Memory
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.Felt252IdMemory.Memory
import Verification.AirInfra.Airs.Casm.CasmState



namespace MemVerify

def call (airBuilder : AirBuilder) (lookupTerms : AirLookupTerms) -- (memory : Felt252IdMemory)
    (address : CasmAddress) (value : Felt252Expr) : AirBuilder × AirLookupTerms :=
  let _state := airBuilder.deduce
  let ab1 := _state.1
  let id := _state.2
  let lt1 := lookupTerms.add_addr_to_id address id
  let lt2 := lt1.add_id_to_value id value
  (ab1, lt2)

def spec_auto (memAssign : Felt252IdMemoryAssign) (address : CasmAddressVal) (value : Felt252Words) :
    Prop :=
  ∃ id : Felt,
    memAssign.addressToId ![address] = some ![id] ∧
    memAssign.idToValue ![id] = some value

def spec (memAssign : Felt252IdMemoryAssign) (address : CasmAddressVal) (value : Felt252Words) :
    Prop :=
  memAssign.HasValue address value

theorem sound {memAssign : Felt252IdMemoryAssign} {address : CasmAddressVal} {value : Felt252Words}
    (h : spec_auto memAssign address value) :
  spec memAssign address value := h

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    -- (memory : Felt252IdMemory)
    (address : CasmAddress)
    (value : Felt252Expr) :
    let ⟨new_ab, new_lt⟩ := call ab lt address value
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (address.eval varAssign) (value.eval varAssign) := by
  unfold call ; lift_lets
  intro state1 ab1 id lt1 lt2
  intro hab1 hlt2
  have hab := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab1
  have ⟨h_has, hlt⟩ := AirLookupTerms.HasValue_add_mem _ _ memAssign _ h_mem _ _ _ hlt2
  use hab, hlt
  exact h_has

lemma NoYieldTerms_of_call
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {addr : FeltExpr}
      {value : Felt252Expr} :
    AirLookupTerms.NoYieldTerms (call ab lt addr value).2 := by
  unfold call AirLookupTerms.add_addr_to_id AirLookupTerms.add_id_to_value
  simp only [←AirLookupTerms.add'_eq_add]
  apply AirLookupTerms.add'_NoYieldTerms.mpr
  repeat
    simp ; apply AirLookupTerms.add'_NoYieldTerms.mpr
  simp [h]

end MemVerify
