
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst

namespace DecodeInstruction

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (const_offset0 const_offset1 const_offset2 : Option (BitVec 16))
    (const_flags : Flags)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms ×
      FeltExpr × FeltExpr × FeltExpr × (Fin 15 → FeltExpr) :=
  let (ab1, off0) :=
    match const_offset0 with
      | some off => (airBuilder, FeltExpr.const off.as_u16)
      | none => airBuilder.deduce
  let (ab2, off1) :=
    match const_offset1 with
      | some off => (ab1, FeltExpr.const off.as_u16)
      | none => ab1.deduce
  let (ab3, off2) :=
    match const_offset2 with
      | some off => (ab2, FeltExpr.const off.as_u16)
      | none => ab2.deduce
  let (ab4, flagArray) := forLoop 0 15 (ab3, #[]) fun i (ab, flagArray) =>
    match const_flags.to_arr[i]! with
      | some flag => (ab, flagArray.push (FeltExpr.const flag.toFelt))
      | none => let (ab, flag) := ab.deduce
                (ab, flagArray.push flag)
  let flags := fun i : Fin 15 => flagArray[i]!
  let lt1 := lookupTerms.add_verify_instr address off0 off1 off2 flags
    -- TODO (Jeremy): replacing `flags` by this crashes
    -- (fun i : Fin 15 => flagArray.get! i)
  (ab4, lt1, offset_as_signed off0, offset_as_signed off1, offset_as_signed off2, flags)

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (const_offset0 const_offset1 const_offset2 : Option (BitVec 16))
    (const_flags : Flags)
    (casmAddress: CasmAddressVal)
    (ρoffset0 ρoffset1 ρoffset2 : Felt)
    (ρflags : Fin 15 → Felt) : Prop :=
  (match const_offset0 with
    | some off0 => ρoffset0 = ↑off0.as_u16
    | none => True) ∧
  (match const_offset1 with
    | some off1 => ρoffset1 = ↑off1.as_u16
    | none => True) ∧
  (match const_offset2 with
    | some off2 => ρoffset2 = ↑off2.as_u16
    | none => True) ∧
  (∀ i : Fin 15,
      match const_flags.to_arr[i]'i.isLt with
        | some flag => ρflags i  = ↑flag.toFelt
        | none => True) ∧
  VerifyInstruction.spec memory casmAddress ρoffset0 ρoffset1 ρoffset2 ρflags

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memAssign : Felt252IdMemoryAssign)
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
    (const_offset0 const_offset1 const_offset2 : Option (BitVec 16))
    (const_flags : Flags)
    (casmAddress : CasmAddress) :
    let state := call ab lt const_offset0 const_offset1 const_offset2 const_flags casmAddress
    let new_ab := state.1
    let new_lt := state.2.1
    let ρoffset0 := state.2.2.1
    let ρoffset1 := state.2.2.2.1
    let ρoffset2 := state.2.2.2.2.1
    let ρflags := state.2.2.2.2.2
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign const_offset0 const_offset1 const_offset2 const_flags
        (casmAddress.eval varAssign)
        ((signed_as_offset ρoffset0).eval varAssign)
        ((signed_as_offset ρoffset1).eval varAssign)
        ((signed_as_offset ρoffset2).eval varAssign)
        (fun i => (ρflags i).eval varAssign) := by
  let aux0 :=
    match const_offset0 with
      | some off => (ab, FeltExpr.const off.as_u16)
      | none => ab.deduce
  let ab1 := aux0.1
  let aux1 :=
    match const_offset1 with
      | some off => (ab1, FeltExpr.const off.as_u16)
      | none => ab1.deduce
  let ab2 := aux1.1
  let aux2 :=
    match const_offset2 with
      | some off => (ab2, FeltExpr.const off.as_u16)
      | none => ab2.deduce
  let ab3 := aux2.1
  let aux3 := forLoop 0 15 (ab3, #[]) fun i (ab, flagArray) =>
    match const_flags.to_arr[i]! with
      | some flag => (ab, flagArray.push (FeltExpr.const flag.toFelt))
      | none => let (ab, flag) := ab.deduce
                (ab, flagArray.push flag)
  dsimp only [call]
  intro hab4 hlt1

  have ⟨h_verify, hlt⟩ := AirLookupTerms.add_verify_instr_sound _ _ memAssign _ h_rc h_mem h_verify_instr _ _ _ _ _ hlt1
  let Invariant : Nat → AirBuilder × Array FeltExpr → Prop :=
    fun i x =>
      (x.1.SatisfiedBy varAssign → ab3.SatisfiedBy varAssign) ∧
      x.2.size = i ∧
      ∀ j, (h : j < x.2.size) →
        match const_flags.to_arr[j]! with
          | some flag => x.2[j].eval varAssign = ↑flag.toFelt
          | none => True
  have hinv1 : Invariant 15 aux3 := by
    apply forLoopCorrect (Invariant := Invariant)
    . norm_num
    . use id, rfl
      intro j hj
      simp at hj
    . rintro i - ilt ⟨ab, flagArray⟩ ⟨h1, h2, h3⟩
      dsimp at *; split <;>
      { next b flag heq =>
        constructor
        . exact h1
        . constructor
          . simp [h2]
          . simp only [Array.size_push]
            intro j hj
            rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h' | h'
            . simp only [Nat.succ_eq_add_one, add_lt_add_iff_right] at h'
              simp only [Array.getElem_push_lt h']
              apply h3 j h'
            . subst h2
              simp_all }
  have hab3 := hinv1.1 hab4
  simp [ab3, aux2] at hab3
  have hab2 : ab2.SatisfiedBy varAssign := by
    split at hab3 <;> simpa using hab3
  simp [ab2, aux1] at hab2
  have hab1 : ab1.SatisfiedBy varAssign := by
    split at hab2 <;> simpa using hab2
  simp [ab1, aux0] at hab1
  have hab : ab.SatisfiedBy varAssign := by
    split at hab1 <;> simpa using hab1
  use hab, hlt
  constructor
  . split <;> simp [signed_as_offset_as_signed]
  constructor
  . split <;> simp [signed_as_offset_as_signed]
  constructor
  . split <;> simp [signed_as_offset_as_signed]
  constructor
  . intro i
    have :=  i.isLt; simp [←hinv1.2.1] at this
    convert hinv1.2.2 i.val this
    . have : i.val < const_flags.to_arr.size := i.isLt
      simp_all
    . change aux3.2[i.val]! = aux3.2[i.val]
      simp_all
  simp [signed_as_offset_as_signed]
  exact h_verify

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {const_offset0 const_offset1 const_offset2 : Option (BitVec 16)}
      {const_flags : Flags}
      {address : CasmAddress} :
    AirLookupTerms.NoYieldTerms (call ab lt const_offset0 const_offset1 const_offset2 const_flags address).2.1 := by
  repeat
    apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
  exact h


end DecodeInstruction
