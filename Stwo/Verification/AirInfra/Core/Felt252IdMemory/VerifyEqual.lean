import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Airs.Casm.CasmState
import Verification.AirInfra.Core.Felt252IdMemory.Memory



namespace MemVerifyEqual

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address1 : CasmAddress)
    (address2 : CasmAddress) :
    AirBuilder × AirLookupTerms :=

  let ab_res := airBuilder.deduce.1
  let id := airBuilder.deduce.2
  let lt1 := lookupTerms.add_addr_to_id address1 id
  let lt2 := lt1.add_addr_to_id address2 id
  (ab_res, lt2)

def spec_auto
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress1: CasmAddressVal)
    (casmAddress2: CasmAddressVal) : Prop :=
    ∃ id : Felt,
      memAssign.addressToId ![casmAddress1] = some ![id] ∧
      memAssign.addressToId ![casmAddress2] = some ![id]

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_mem : AirLookupTerms.AddrToIdYieldsAgree memAssign h_satisfied.values (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX))
    (casmAddress1: CasmAddress)
    (casmAddress2: CasmAddress) :

    let ⟨new_ab, new_lt⟩  := call ab lt casmAddress1 casmAddress2
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmAddress1.eval varAssign) (casmAddress2.eval varAssign) := by

    unfold call; lift_lets
    intro ab_res id lt1 lt2
    intro hab1 hlt2
    have ⟨h_addr_id2, hlt1⟩ := lt1.mem_addr_to_id_SatisfiedBy_add varAssign memAssign h_satisfied h_mem casmAddress2 id hlt2
    have ⟨h_addr_id1, hlt⟩ := lt.mem_addr_to_id_SatisfiedBy_add varAssign memAssign h_satisfied h_mem casmAddress1 id hlt1
    have hab := (ab.deduce_SatisfiedBy varAssign).1 hab1
    use hab, hlt
    use FeltExpr.eval varAssign id

theorem value_eq_of_mem_Agrees [Fact (Nat.Prime Felt252Prime)]
    (memAssign : Felt252IdMemoryAssign)
    (memChecked : memAssign.IsRangeChecked)
    {base_addr1 base_addr2 : CasmAddressVal}
    {offset1 offset2 : Felt}
    {bitvec1 bitvec2 : BitVec 16}
    (h_offset1 : offset1 = bitvec1.toNat)
    (h_offset2 : offset2 = bitvec2.toNat)
    (h : spec memAssign
          (base_addr1 + offset_as_signed_Felt offset1)
          (base_addr2 + offset_as_signed_Felt offset2)) :
    ∀ mem : Felt252 → Felt252,
      memAssign.Agrees mem →
        mem (base_addr1.toFelt252 + intClip (int_from_Felt offset1)) =
        mem (base_addr2.toFelt252 + intClip (int_from_Felt offset2))  := by
  intro mem hmem
  simp only [h_offset1, h_offset2]
  simp only [h_offset1, h_offset2] at h
  rcases h with ⟨id, h_id⟩
  rw [←toFelt252_add_offset_RangeChecked_eq (memChecked.1 h_id.1)]
  rw [←toFelt252_add_offset_RangeChecked_eq (memChecked.1 h_id.2)]
  apply hmem.1 ; exact ⟨id, h_id⟩

end MemVerifyEqual
