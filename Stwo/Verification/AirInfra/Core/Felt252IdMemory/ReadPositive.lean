import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.Casm.CasmState
import Verification.AirInfra.Core.Felt252IdMemory.Memory

/-
Note: reversed the order of the functions in the file because Lean does not allow forward references.
-/



namespace RangeCheckLastLimb

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (bits_in_ms_limb : Nat)
    (msl : FeltExpr) :
    AirBuilder × AirLookupTerms :=
  match bits_in_ms_limb with
  | 0 => (airBuilder, lookupTerms)
  | 1 => (airBuilder.constrain (msl * (FeltExpr.const 1 - msl)), lookupTerms)
  | 2 => let (ab1, mslh) := airBuilder.deduce
         let ab2 := ab1.constrain (mslh * (FeltExpr.const 1 - mslh))
         let (ab3, msll) := ab2.letForConstraint (msl - (mslh * FeltExpr.const 2))
         let ab4 := ab3.constrain (msll * (FeltExpr.const 1 - msll))
         (ab4, lookupTerms)
  | _ => let lt1 := lookupTerms.add_rc bits_in_ms_limb msl
         (airBuilder, lt1)

def spec
  (bits_in_ms_limb : Nat)
  (msl : Felt) : Prop :=
  bits_in_ms_limb > 0 → IsRangeChecked bits_in_ms_limb msl

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (bits_in_ms_limb : Nat)
    (msl : FeltExpr) :
    let ⟨new_ab, new_lt⟩ :=
      call ab lt bits_in_ms_limb msl
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec bits_in_ms_limb (msl.eval varAssign) := by
  dsimp [call]
  split
  . simp_all [spec]
  . simp only [AirBuilder.constrain_SatisfiedBy, FeltExpr.eval_mul, FeltExpr.eval_sub,
    FeltExpr.eval_const, mul_eq_zero, and_imp, spec]
    intro h1 h2 h3
    use h1, h3
    rintro -
    unfold IsRangeChecked
    rcases h2 with h2 |h2
    . use 0; simp [h2]
    . use 1; simp [eq_of_sub_eq_zero h2]
  . simp only [AirBuilder.constrain_SatisfiedBy, AirBuilder.letForConstraint_SatisfiedBy,
    AirBuilder.deduce_SatisfiedBy, FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const,
    mul_eq_zero, and_imp, spec]
    let (ab1, mslh) := ab.deduce
    let ab2 := ab1.constrain (mslh * (FeltExpr.const 1 - mslh))
    let (ab3, msll) := ab2.letForConstraint (msl - (mslh * FeltExpr.const 2))
    dsimp; intro h1 h2 h3 h4 h5
    use h1, h5
    rw [eq_add_of_sub_eq h3.symm]
    rintro -
    unfold IsRangeChecked
    rcases h2 with h2 |h2
    . rw [h2]
      rcases h4 with h4 | h4
      . use 0; simp [h4]
      . use 1; simp [eq_of_sub_eq_zero h4]
    . rw [eq_of_sub_eq_zero h2 |>.symm]
      rcases h4 with h4 | h4
      . use 2; simp [h4]
      . use 3; simp [eq_of_sub_eq_zero h4 |>.symm]; norm_num
  . intro h1 h2
    rcases AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ h2 with ⟨h3, h4⟩
    use h1, h4
    intro _
    exact h3

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {bits_in_ms_limb : Nat}
      {msl : FeltExpr} :
    AirLookupTerms.RelInRelTuples (call ab lt bits_in_ms_limb msl).2 := by
  unfold call
  split
  all_goals
    try apply AirLookupTerms.add'_RelInRelTuple.mpr
    exact h

end RangeCheckLastLimb



namespace ReadPositive

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (num_bits : Nat)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × Felt252Expr × FeltExpr :=
  let ab1 := airBuilder.deduce.1
  let id := airBuilder.deduce.2
  let lt1 := lookupTerms.add_addr_to_id address id
  let num_nonzero_limbs := num_bits.div_ceil FELT252_BITS_PER_WORD
  let bits_in_ms_limb := num_bits % FELT252_BITS_PER_WORD
  let forLoopVal := forLoop 0 num_nonzero_limbs (ab1, #[]) fun _ (ab, limbArray) =>
    let next_state := ab.deduce
    (next_state.1, limbArray.push next_state.2)
  let ab2 := forLoopVal.1
  let limbArray := forLoopVal.2
  let ab3_lt2 := if bits_in_ms_limb > 0 then
               let msl := limbArray[num_nonzero_limbs - 1]!
               RangeCheckLastLimb.call ab2 lt1 bits_in_ms_limb msl
             else
               (ab2, lt1)
  let ab3 := ab3_lt2.1
  let lt2 := ab3_lt2.2
  let expected_value_in_memory : Felt252Expr := fun i =>
        if i.val < num_nonzero_limbs then
          limbArray[i.val]!
        else
          FeltExpr.const 0
  let lt3 := lt2.add_id_to_value id expected_value_in_memory
  (ab3, lt3, expected_value_in_memory, id)

open Fin.NatCast in
def has_num_bits (num_bits : Nat) (value : Felt252Words) :=
  let num_nonzero_limbs := num_bits.div_ceil FELT252_BITS_PER_WORD
  let bits_in_ms_limb := num_bits % FELT252_BITS_PER_WORD
  num_bits ≤ 252 →
    (bits_in_ms_limb > 0 → IsRangeChecked bits_in_ms_limb (value ↑(num_nonzero_limbs - 1))) ∧
    (∀ i, num_nonzero_limbs ≤ i.val → value i = 0)

def spec_auto
    (memAssign : Felt252IdMemoryAssign)
    (num_bits : Nat)
    (casmAddress: CasmAddressVal)
    (ρExpectedValueInMemory : Felt252Words)
    (ρId : Felt) : Prop :=
  has_num_bits num_bits ρExpectedValueInMemory ∧
  memAssign.addressToId ![casmAddress] = some ![ρId] ∧
  memAssign.idToValue   ![ρId] = some ρExpectedValueInMemory

open Fin.NatCast in
def spec_auto'
    (memAssign : Felt252IdMemoryAssign)
    (num_bits : Nat)
    (casmAddress: CasmAddressVal)
    (ρExpectedValueInMemory : Felt252Words)
    (ρId : Felt) : Prop :=
  let num_nonzero_limbs := num_bits.div_ceil FELT252_BITS_PER_WORD
  let bits_in_ms_limb := num_bits % FELT252_BITS_PER_WORD
  num_bits ≤ 252 →
    (bits_in_ms_limb > 0 → IsRangeChecked bits_in_ms_limb (ρExpectedValueInMemory ↑(num_nonzero_limbs - 1))) ∧
    (∀ i, num_nonzero_limbs ≤ i.val → ρExpectedValueInMemory i = 0) ∧
    memAssign.addressToId ![casmAddress] = some ![ρId] ∧
    memAssign.idToValue   ![ρId] = some ρExpectedValueInMemory

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (num_bits : Nat)
    (casmAddress: CasmAddress) :
    let ⟨new_ab, new_lt, ρExpectedValueInMemory, ρId⟩ := call ab lt num_bits casmAddress
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign num_bits (casmAddress.eval varAssign) (ρExpectedValueInMemory.eval varAssign)
        (ρId.eval varAssign) := by
  unfold call; lift_lets
  intro ab1 id lt1 num_nonzero_limbs bits_in_ms_limb forLoopVal ab2 limbArray msl ab3_lt2 ab3 lt2 expected_value_in_memory lt3
  dsimp
  intro hab3 hlt3
  have ⟨h_id_to_value, hlt2⟩ := AirLookupTerms.mem_id_to_value_SatisfiedBy_add _ _ memAssign _ h_mem.2 _ _ hlt3
  let msl := limbArray[num_nonzero_limbs - 1]!
  have ⟨hab2, hlt1, hh⟩ : ab2.SatisfiedBy varAssign ∧
    lt1.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
    (RangeCheckLastLimb.spec bits_in_ms_limb (msl.eval varAssign)) := by
    if h : bits_in_ms_limb > 0 then
      have : ⟨ab3, lt2⟩ = RangeCheckLastLimb.call ab2 lt1 bits_in_ms_limb msl := by
        revert ab3 lt2 ab3_lt2 msl
        simp [h, msl]
      apply RangeCheckLastLimb.sound_auto _ _ _ _ h_rc
      dsimp
      change (RangeCheckLastLimb.call ab2 lt1 bits_in_ms_limb msl).1.SatisfiedBy varAssign
      rw [←this]; exact hab3
      change (RangeCheckLastLimb.call ab2 lt1 bits_in_ms_limb msl).2.UseAgree _ _ _ _
      rw [←this]; exact hlt2
    else
      have : (ab3, lt2) = (ab2, lt1) := by
        revert ab3 lt2 ab3_lt2 msl
        simp [h]
      simp only [Prod.mk.injEq] at this
      rw [←this.1, ←this.2]
      use hab3, hlt2
      rw [RangeCheckLastLimb.spec]; intro _; omega
  have ⟨h_addr_to_id, hlt⟩ := AirLookupTerms.mem_addr_to_id_SatisfiedBy_add _ _ memAssign _ h_mem.1 _ _ hlt1
  let Invariant : Nat → AirBuilder × Array FeltExpr → Prop :=
    fun i x =>
      (x.1.SatisfiedBy varAssign → ab1.SatisfiedBy varAssign) ∧
      x.2.size = i
  have hinv1 : Invariant num_nonzero_limbs ⟨ab2, limbArray⟩ := by
    apply forLoopCorrect (Invariant := Invariant)
    . simp
    . simp [Invariant]
    . intro i _ _ ⟨ab, a⟩; simp [Invariant]
  have hab1 : ab1.SatisfiedBy varAssign := hinv1.1 hab2
  have hlimbArray : limbArray.size = num_nonzero_limbs := hinv1.2
  use hab1, hlt
  constructor
  . intro hnum_bits_le
    constructor
    · convert hh
      dsimp [Felt252Expr.eval]
      congr
      revert msl; dsimp; intro _
      unfold expected_value_in_memory
      rw [if_pos]
      congr
      . simp [num_nonzero_limbs]
        apply Nat.div_ceil_aux2 _ hnum_bits_le
      have : 0 ≠ num_bits := by
        rintro rfl; simp_all [bits_in_ms_limb]
      simp; apply Nat.div_ceil_aux3; omega
    intro i hi
    simp only [Felt252Expr.eval]
    unfold expected_value_in_memory
    rw [if_neg]
    . simp
    linarith
  use h_addr_to_id

theorem HasValue_of_spec [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
   {address : CasmAddressVal}
   {value : Felt252Words}
   {id : Felt}
   {memoryAssign : Felt252IdMemoryAssign}
   {num_bits : Nat}
   (h_read_positive: spec memoryAssign num_bits address value id):
  (memoryAssign.HasValue address value) := by
  rcases h_read_positive with ⟨_, h_addr2id, h_id2val⟩
  unfold Felt252IdMemoryAssign.HasValue
  use id

theorem IsRangeChecked_of_spec [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
   {address : CasmAddressVal}
   {value : Felt252Words}
   {id : Felt}
   {memoryAssign : Felt252IdMemoryAssign}
   {num_bits : Nat}
   (h_mem_rc: memoryAssign.IsRangeChecked)
   (h_read_positive: spec memoryAssign num_bits address value id):
  (∃ value_n : Felt252Nats, value_n.IsRangeChecked value) := by
  have := HasValue_of_spec h_read_positive
  exact Felt252IdMemoryAssign.IsRangeChecked_of_HasValue h_mem_rc this


theorem read_positive_mem [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
   {address : CasmAddressVal}
   {value : Felt252Words}
   {id : Felt}
   {mem : Felt252 → Felt252}
   {memoryAssign : Felt252IdMemoryAssign}
   {num_bits : Nat}
   (h_mem_rc: memoryAssign.IsRangeChecked) --
   (hmem: memoryAssign.Agrees mem)
   (h_read_positive: spec memoryAssign num_bits address value id):
  (mem address.toFelt252 = value.eval) := by
  have := HasValue_of_spec h_read_positive
  rcases Felt252IdMemoryAssign.isRangeChecked_of_hasValue_of_agrees h_mem_rc this hmem with ⟨value_n, h1, h2⟩
  rw[← Felt252Nats.eval_Felt252Words_eq h1] at h2
  exact h2

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {num_bits : Nat}
      {address : CasmAddress} :
    AirLookupTerms.RelInRelTuples (call ab lt num_bits address).2.1 := by
  unfold call
  repeat
    apply AirLookupTerms.add'_RelInRelTuple.mpr
  by_cases h_gt : num_bits % FELT252_BITS_PER_WORD > 0
  · simp [if_pos h_gt]
    apply RangeCheckLastLimb.RelInRelTuples_of_call
    apply AirLookupTerms.add'_RelInRelTuple.mpr
    exact h
  simp [if_neg h_gt]
  apply AirLookupTerms.add'_RelInRelTuple.mpr
  exact h

end ReadPositive

/-
In the Rust code, this is in `memory.rs` (corresponding to `Memory.Lean`).
-/

namespace Felt252IdMemory



def read_address_and_id
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × CasmAddress × FeltExpr :=
  let (ab1, lt1, address_f252, id) :=
    ReadPositive.call airBuilder lookupTerms ADDRESS_BITS address
  (ab1,lt1, felt252_to_m31 address_f252 ADDRESS_BITS, id)

namespace read_address_and_id

def spec_auto
    (memAssign : Felt252IdMemoryAssign)
    (address: CasmAddressVal)
    (ρCasmAddressVal : CasmAddressVal)
    (ρId : Felt) : Prop :=
  ∃ address_f252 : Felt252Words,
    ReadPositive.spec memAssign ADDRESS_BITS address address_f252 ρId ∧
    ρCasmAddressVal = felt252_to_m31_val address_f252 ADDRESS_BITS

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (casmAddress: CasmAddress) :
    let ⟨new_ab, new_lt, ρExpectedValueInMemory, ρId⟩ := read_address_and_id ab lt casmAddress
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmAddress.eval varAssign) (ρExpectedValueInMemory.eval varAssign)
        (ρId.eval varAssign) := by
  let aux := ReadPositive.call ab lt ADDRESS_BITS casmAddress
  intro hab hlt
  have ⟨hab', hlt', hspec⟩ := ReadPositive.sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem ADDRESS_BITS casmAddress
    hab hlt
  use hab', hlt'
  use aux.2.2.1.eval varAssign
  use hspec
  rw [felt252_to_m31_eval]; rfl

end read_address_and_id



def read_address
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × CasmAddress :=
  let (ab1, lt1, newAddress, _) :=
    read_address_and_id airBuilder lookupTerms address
  (ab1, lt1, newAddress)

namespace read_address

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (address : CasmAddressVal)
    (ρAddress : CasmAddressVal) : Prop :=
  ∃ felt252,
    ReadPositive.has_num_bits ADDRESS_BITS felt252 ∧
    memory.HasValue address felt252 ∧
    ρAddress = felt252_to_m31_val felt252 ADDRESS_BITS

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (casmAddress: CasmAddress) :
    let ⟨new_ab, new_lt, ρExpectedValueInMemory⟩ := read_address ab lt casmAddress
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmAddress.eval varAssign) (ρExpectedValueInMemory.eval varAssign) := by
  let aux := read_address_and_id ab lt casmAddress
  intro hab hlt
  have ⟨hab', hlt', val, hspec⟩ := read_address_and_id.sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem casmAddress hab hlt
  use hab', hlt', val
  clear hab hlt
  rw [ReadPositive.spec, ReadPositive.spec_auto] at hspec
  use hspec.1.1
  constructor
  . use aux.2.2.2.eval varAssign
    use hspec.1.2.1
    use hspec.1.2.2
  use hspec.2

open Fin.NatCast

theorem read_address_last_limb [Fact (Nat.Prime Stwo.P)]
    {felt252 : Felt252Words}
    {value: Nat}
    (h : ReadPositive.has_num_bits ADDRESS_BITS felt252)
    (h_val: felt252 3 = ↑value)
    (hval_lt: value < 2^9) :
    value < 2^2 := by

    have hxn3b : IsRangeChecked 2 (felt252 3) := by
      apply (h _).1 _
      dsimp[ADDRESS_BITS]
      norm_num
      dsimp [ADDRESS_BITS, FELT252_BITS_PER_WORD]
      norm_num
    have htmp: (felt252 3).val = value := by
      rw[h_val]
      apply ZMod.val_natCast_of_lt
      dsimp[Stwo.P]
      linarith

    rcases hxn3b with ⟨nval3, nval3_lt, hnval3⟩
    have : value = nval3 := by
      rw[← htmp]
      rw[hnval3]
      apply ZMod.val_natCast_of_lt
      dsimp[Stwo.P]
      linarith
    rw[this]
    exact nval3_lt

theorem read_address_rc [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    {memAssign : Felt252IdMemoryAssign}
    {address : CasmAddressVal}
    {ρAddress : CasmAddressVal}
    (memChecked : memAssign.IsRangeChecked)
    (h: spec memAssign address ρAddress) :
    IsRangeChecked 29 ρAddress := by

  rcases h with ⟨felt252, h1, h2, rfl⟩
  dsimp [felt252_to_m31_val, ADDRESS_BITS, FELT252_BITS_PER_WORD]
  have : Nat.div_ceil 29 9 = 4 := by
    dsimp [Nat.div_ceil]
  rw[this]
  dsimp[felt252_to_m31_val.aux, FELT252_BITS_PER_WORD]
  simp only [Fin.isValue, Nat.cast_zero, zero_add, Nat.cast_one, Fin.reduceAdd]
  rcases Felt252IdMemoryAssign.IsRangeChecked_of_HasValue memChecked h2 with ⟨value_n, hvalue_n⟩
  let hxn0 := hvalue_n 0
  let hxn1 := hvalue_n 1
  let hxn2 := hvalue_n 2
  let hxn3 := hvalue_n 3

  have hxn3b : value_n 3 < 2^2 := read_address_last_limb h1 hxn3.1 hxn3.2
  use value_n 0 + value_n 1 * 512 + value_n 2 * 262144 + value_n 3 * 134217728
  constructor
  · linarith
  rw[Nat.cast_add, Nat.cast_mul,Nat.cast_add, Nat.cast_mul,Nat.cast_add, Nat.cast_mul, hxn0.1, hxn1.1, hxn2.1, hxn3.1]
  ring_nf


end read_address



def read_felt252
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × Felt252Expr :=
  let (ab1, lt1, value, _) :=
    ReadPositive.call airBuilder lookupTerms 252 address
  (ab1, lt1, value)
namespace read_felt252

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (address : CasmAddressVal)
    (ρExpectedValueInMemory : Felt252Words) : Prop :=
    memory.HasValue address ρExpectedValueInMemory

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (casmAddress: CasmAddress) :
    let ⟨new_ab, new_lt, ρExpectedValueInMemory⟩ := read_felt252 ab lt casmAddress
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (casmAddress.eval varAssign) (ρExpectedValueInMemory.eval varAssign) := by
  let aux := ReadPositive.call ab lt 252 casmAddress
  intro hab hlt
  have ⟨hab', hlt', hspec⟩ := ReadPositive.sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem 252 casmAddress hab hlt
  use hab', hlt'
  use aux.2.2.2.eval varAssign
  exact hspec.2

end read_felt252

end Felt252IdMemory
