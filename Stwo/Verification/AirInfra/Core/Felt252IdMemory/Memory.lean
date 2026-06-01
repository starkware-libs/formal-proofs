import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.Felt252IdMemory.AddressToId
import Verification.AirInfra.Core.Felt252IdMemory.IdToBig
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck

noncomputable section

structure Felt252IdMemory where
  addressToId : MemoryAddressToId
  idToValue : MemoryIdToBig
deriving Lean.ToJson, Lean.FromJson

namespace Felt252IdMemory

def empty : Felt252IdMemory where
  addressToId := MemoryAddressToId.empty
  idToValue := MemoryIdToBig.empty

-- `read_rel_imm` is in `ReadSmall.lean`.

-- `read_address_and_id` is in `ReadPositive.lean`.

-- `read_address` is in `ReadPositive.lean`.

def AddrToIdLookupCall : AirBuilder × AirLookupTerms :=
  let _state := AirBuilder.empty.deduce
  let ab1 := _state.1
  let addr := _state.2
  let _state := ab1.deduce
  let ab2 := _state.1
  let id := _state.2
  let lt1 := AirLookupTerms.empty.add MEMORY_ADDR_TO_ID_REL_INDEX
    (p_tuple_expr MEMORY_ADDR_TO_ID_REL_INDEX ![addr, id]) .yield
  let lt2 := lt1.add_rc 29 addr -- use
  (ab2, lt2)

def IdToValueLookupCall : AirBuilder × AirLookupTerms :=
  let _state := AirBuilder.empty.deduce
  let ab1 := _state.1
  let id := _state.2
  let _state := ab1.deduce252
  let ab2 := _state.1
  let value := _state.2
  let lt1 := AirLookupTerms.empty.add
    MEMORY_ID_TO_VALUE_REL_INDEX
    (p_tuple_expr MEMORY_ID_TO_VALUE_REL_INDEX ((Fin.append ![id] value) ∘ Fin.cast (by simp ; rfl)))
    .yield
  let lt2 := forLoop 0 FELT252_N_WORDS lt1 (fun i lt => lt.add_rc 9 (value (Fin.ofNat _ i))) -- use
  (ab2, lt2)

lemma mem_yield_not_range_check
  (start_lt : AirLookupTerms)
  (value : Felt252Expr)
  (n : Nat) :
  n ≤ FELT252_N_WORDS →
    ∀ t : LookupTerm rel_lengths,
      t.useOrYield = .yield →
        t ∈ forLoop 0 n start_lt
          (fun i lt => lt.add_rc 9 (value (Fin.ofNat _ i))) →
            t ∈ start_lt := by
  induction n
  case zero =>
    intro _ t h_yield
    simp [forLoop_start]
  case succ n ih =>
    intro h_n_le t h_yield
    simp [forLoop_succ]
    intro h_t_mem
    apply ih (Nat.le_of_succ_le h_n_le) t h_yield
    apply AirLookupTerms.mem_add'_ne h_t_mem
    simp [h_yield]

lemma mem_yield_of_IdToValueLookupCall :
  ∀ t ∈ Felt252IdMemory.IdToValueLookupCall.2,
    t.useOrYield = .yield →
      t ∈ AirLookupTerms.empty.add
            MEMORY_ID_TO_VALUE_REL_INDEX
            (p_tuple_expr
              MEMORY_ID_TO_VALUE_REL_INDEX
              ((Fin.append ![AirBuilder.empty.deduce.2] AirBuilder.empty.deduce.1.deduce252.2) ∘ Fin.cast (by simp ; rfl)))
            .yield := by
  intro t h_t_mem h_yield
  apply mem_yield_not_range_check _ AirBuilder.empty.deduce.1.deduce252.2 FELT252_N_WORDS (Nat.le_refl _) t h_yield h_t_mem

lemma range_check_mem_forLoop_j
    (start_lt : AirLookupTerms)
    (j : Fin FELT252_N_WORDS) :
    let value := AirBuilder.empty.deduce.1.deduce252.2
    {
      rel := RANGE_CHECK_REL_INDEX,
      tuple := p_tuple_expr RANGE_CHECK_REL_INDEX ![FeltExpr.const 9, FeltExpr.var (VarIndex.stateVar (↑j + 1))],
      useOrYield := UseOrYield.use
    } ∈
      forLoop 0 (j.val + 1) start_lt (fun i lt => lt.add_rc 9 (value (Fin.ofNat _ i))) := by
  simp [forLoop_succ]
  rw [AirLookupTerms.add_rc, AirLookupTerms.add, Array.mem_push]
  right
  simp [AirBuilder.deduce252, State.add_n, State.add, AirBuilder.deduce, AirBuilder.empty, State.empty, add_comm]

lemma mem_forLoop_of_mem_forLoop_j {start_lt : AirLookupTerms} {j : Fin FELT252_N_WORDS} {value : Felt252Expr} {n : Nat} :
    ∀ t, t ∈ forLoop 0 (j.val + 1) start_lt (fun i lt => lt.add_rc 9 (value (Fin.ofNat _ i))) →
      t ∈ forLoop 0 (j.val + 1 + n) start_lt (fun i lt => lt.add_rc 9 (value (Fin.ofNat _ i))) := by
  intro t
  induction n
  case zero => simp only [imp_self]
  case succ n ih =>
    intro h_j ;
    rw [←add_assoc, forLoop_succ, AirLookupTerms.add_rc, AirLookupTerms.add, Array.mem_push]
    left
    exact ih h_j
    exact Nat.zero_le _

lemma mem_range_check_of_IdToValueLookupCall (j : Fin FELT252_N_WORDS) :
    {
      rel := RANGE_CHECK_REL_INDEX,
      tuple := p_tuple_expr RANGE_CHECK_REL_INDEX ![FeltExpr.const 9, FeltExpr.var (VarIndex.stateVar (↑j + 1))],
      useOrYield := UseOrYield.use
    } ∈
      Felt252IdMemory.IdToValueLookupCall.2 := by
  unfold Felt252IdMemory.IdToValueLookupCall ; simp only
  let n := FELT252_N_WORDS - j - 1
  have h_eq : FELT252_N_WORDS = j.val + 1 + n := by
    unfold n ; rw [Nat.sub_sub, ←Nat.add_sub_assoc (Nat.succ_le_of_lt (Fin.isLt _)), Nat.add_sub_cancel_left]
  simp only [h_eq]
  apply mem_forLoop_of_mem_forLoop_j _ (range_check_mem_forLoop_j _ _)

end Felt252IdMemory

/-
Semantics
-/

structure Felt252IdMemoryAssign where
  addressToId : MemoryAddressToIdAssign
  idToValue : MemoryIdToBigAssign

/-
TODO(Jeremy): reconcile naming; in `Verification.Semanatics.Soundness.Hoare`, `IsRangeChecked` means something different.
-/

namespace Felt252IdMemoryAssign

def HasId (memoryAssign : Felt252IdMemoryAssign) (address : Felt) (id : Felt) : Prop :=
  memoryAssign.addressToId ![address] = some ![id]

def AgreesEq (memoryAssign : Felt252IdMemoryAssign) (mem : Felt252 → Felt252) : Prop :=
  ∀ address1 address2,
    (∃ id, memoryAssign.HasId address1 id ∧ memoryAssign.HasId address2 id) →
      mem address1.toFelt252 = mem address2.toFelt252

def HasValue (memoryAssign : Felt252IdMemoryAssign) (address : Felt) (value : Felt252Words) : Prop :=
  ∃ id : Felt,
    memoryAssign.addressToId ![address] = some ![id] ∧
    memoryAssign.idToValue   ![id] = some value

lemma HasId_of_HasValue (memoryAssign : Felt252IdMemoryAssign) (address : Felt) (value : Felt252Words) :
    memoryAssign.HasValue address value → ∃ id, memoryAssign.HasId address id := by
  intro h
  rcases h with ⟨id, h_id, -⟩
  use id ; exact h_id

def IsAddressRangeChecked (memoryAssign : Felt252IdMemoryAssign) : Prop :=
  ∀ {address id}, memoryAssign.HasId address id → _root_.IsRangeChecked 29 address

def IsValueRangeChecked (memoryAssign : Felt252IdMemoryAssign) : Prop :=
  ∀ {address value},
    memoryAssign.HasValue address value →
      ∃ value_n : Felt252Nats,
        value_n.IsRangeChecked value

def IsRangeChecked (memoryAssign : Felt252IdMemoryAssign) : Prop :=
  memoryAssign.IsAddressRangeChecked ∧ memoryAssign.IsValueRangeChecked

theorem IsRangeChecked_of_HasValue {memoryAssign : Felt252IdMemoryAssign}
    {address : Felt} {value : Felt252Words}
    (h0 : memoryAssign.IsRangeChecked)
    (h1 : memoryAssign.HasValue address value) :
      ∃ value_n : Felt252Nats, value_n.IsRangeChecked value :=
  (h0.2 h1)

theorem IsRangeChecked_address_of_HasValue {memoryAssign : Felt252IdMemoryAssign}
    {address : Felt} {value : Felt252Words}
    (h0 : memoryAssign.IsRangeChecked)
    (h1 : memoryAssign.HasValue address value) :
      _root_.IsRangeChecked 29 address := by
  rcases (HasId_of_HasValue _ _ _ h1) with ⟨id, h_id⟩
  exact h0.1 h_id

def Agrees (memoryAssign : Felt252IdMemoryAssign) (mem : Felt252 → Felt252) : Prop :=
  memoryAssign.AgreesEq mem ∧
  ∀ address value (value_n : Felt252Nats),
    memoryAssign.HasValue address value →
    value_n.IsRangeChecked value →
      mem address.toFelt252 = value_n.eval

theorem isRangeChecked_of_hasValue_of_agrees
    {memoryAssign : Felt252IdMemoryAssign}
    {mem : Felt252 → Felt252}
    {address : Felt} {value : Felt252Words}
    (h0 : memoryAssign.IsRangeChecked)
    (h1 : memoryAssign.HasValue address value)
    (h2 : memoryAssign.Agrees mem) :
      ∃ value_n : Felt252Nats, value_n.IsRangeChecked value ∧
        mem address.toFelt252 = value_n.eval := by
  rcases IsRangeChecked_of_HasValue h0 h1 with ⟨value_n, h3⟩
  have := h2.2 address value value_n h1 h3
  use value_n, h3

/-
  Felt252 Memory Construction from Memory Assignment
-/

open Classical

-- The set of all Felt addresses which have a unique value in the memory assignment
def MemValueAddrs (memAssign : Felt252IdMemoryAssign) :=
  Finset.subtype
    (fun addr => ∃ value : Felt252Words × Felt252Nats, memAssign.HasValue addr value.1 ∧ Felt252Nats.IsRangeChecked value.2 value.1)
    (Finset.univ : Finset (Felt))

def Mem252FromMemAssign (memAssign : Felt252IdMemoryAssign) : Felt252 → Felt252 :=
  fun addr => match (MemValueAddrs memAssign).toList.find? fun x => x.val.toFelt252 = addr with
    | some x => (Exists.choose x.property).2.eval
    | none => 0

lemma value_eq_of_HasId {memAssign : Felt252IdMemoryAssign} :
    ∀ {addr1 addr2 id},
      memAssign.HasId addr1 id → memAssign.HasId addr2 id →
        ∀ value, memAssign.HasValue addr1 value ↔ memAssign.HasValue addr2 value := by
  intro addr1 addr2 id h_has1 h_has2
  intro value
  constructor
  all_goals
    intro h_has_value
    rcases h_has_value with ⟨id', h_add, h_value⟩
  case' mp => rw [h_has1] at h_add
  case' mpr => rw [h_has2] at h_add
  all_goals
    simp at h_add
    rw [←h_add] at h_value
  exact ⟨id, h_has1, h_value⟩
  exact ⟨id, h_has2, h_value⟩

lemma HasValue_unique {memAssign : Felt252IdMemoryAssign} :
    ∀ addr value1 value2,
      memAssign.HasValue addr value1 → memAssign.HasValue addr value2 → value1 = value2 := by
  intro addr value1 value2 h_has1 h_has2
  rcases h_has1 with ⟨id1, h_id1, h_value1⟩
  rcases h_has2 with ⟨id2, h_id2, h_value2⟩
  simp only [h_id1, Option.some.injEq, Matrix.vecCons_inj, and_true] at h_id2
  simp only [h_id2, h_value2, Option.some.injEq] at h_value1
  exact h_value1.symm

lemma toFelt252_inj {a b : Felt} :
    a.toFelt252 = b.toFelt252 → a = b := by
  intro h
  unfold Felt.toFelt252 at h
  apply add_right_cancel (b := ↑(2 ^ 29 + 1))
  apply ZMod.val_injective
  rw [sub_left_inj] at h
  apply Nat.cast_inj_of_lt_char _ _ h
  all_goals
    apply lt_trans (ZMod.val_lt _)
    simp [Stwo.P, Felt252, ZMod.ringChar_zmod_n, Felt252Prime]

lemma exists_unique_of_exists {memAssign : Felt252IdMemoryAssign} :
  ∀ addr,
    (∃ vs : Felt252Words × Felt252Nats, memAssign.HasValue addr vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1) →
    ∃! vs_unique : Felt252Words × Felt252Nats,
      memAssign.HasValue addr vs_unique.1 ∧ Felt252Nats.IsRangeChecked vs_unique.2 vs_unique.1 := by
  intro addr h_addr
  rcases h_addr with ⟨x, h_x⟩
  use x, h_x
  intro y h_y
  have h_eq : y.1 = x.1 := HasValue_unique addr y.1 x.1 h_y.1 h_x.1
  ext
  exact h_eq
  simp only [h_eq] at h_y
  exact Felt252Nats.eq_of_IsRangeChecked_eq h_y.2 h_x.2

lemma Mem252FromMemAssign_eq_of_exists {memAssign : Felt252IdMemoryAssign} :
  ∀ addr (vs : Felt252Words × Felt252Nats),
      (memAssign.HasValue addr vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1) →
        Mem252FromMemAssign memAssign addr.toFelt252 = vs.2.eval := by
  intro addr vs h_vs
  cases h_find : (MemValueAddrs memAssign).toList.find? fun x => x.val.toFelt252 = addr.toFelt252
  case none =>
    exfalso
    rw [List.find?_eq_none] at h_find
    replace h_find := h_find ⟨addr, ⟨vs, h_vs⟩⟩
    simp at h_find
    apply h_find
    unfold MemValueAddrs
    rw [Finset.mem_subtype]
    apply Finset.mem_univ
  case some v =>
    have h_v : addr = v := by
      apply toFelt252_inj
      have h_eq := List.find?_some h_find
      simp_all
    simp only [h_v] at h_find h_vs
    unfold Mem252FromMemAssign
    simp only [h_v, h_find]
    congr
    have h_unique := exists_unique_of_exists v ⟨vs, h_vs⟩
    exact ExistsUnique.unique h_unique (Classical.choose_spec v.property) h_vs

lemma Mem252FromMemAssign_eq_zero_of_not_exists {memAssign : Felt252IdMemoryAssign} :
  ∀ addr,
    (¬∃ (vs : Felt252Words × Felt252Nats),(memAssign.HasValue addr vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1)) →
        Mem252FromMemAssign memAssign addr.toFelt252 = 0 := by
  intro addr h_not_exists
  cases h_find : (MemValueAddrs memAssign).toList.find? fun x => x.val.toFelt252 = addr.toFelt252
  case none =>
    simp only [Mem252FromMemAssign, h_find]
  case some v =>
    exfalso
    have h_v : addr = v := by
      apply toFelt252_inj
      have h_eq := List.find?_some h_find
      simp_all
    apply h_not_exists
    rw [h_v]
    exact v.property

lemma same_value_eq_of_id_eq
      {memAssign : Felt252IdMemoryAssign}
      {addr1 addr2 : Felt}
      (h_id : ∃ id, memAssign.HasId addr1 id ∧ memAssign.HasId addr2 id) :
    ∀ (vs : Felt252Words × Felt252Nats),
        (memAssign.HasValue addr1 vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1) ↔
        (memAssign.HasValue addr2 vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1) := by
  intro vs
  rcases h_id with ⟨id, h_has1, h_has2⟩
  have h_value := value_eq_of_HasId h_has1 h_has2
  constructor
  · intro h_vs
    use (h_value vs.1).mp h_vs.1, h_vs.2
  intro h_vs
  use (h_value vs.1).mpr h_vs.1, h_vs.2

lemma exists_value_eq_of_id_eq
      {memAssign : Felt252IdMemoryAssign}
      {addr1 addr2 : Felt}
      (h_id : ∃ id, memAssign.HasId addr1 id ∧ memAssign.HasId addr2 id) :
    (∃ (vs : Felt252Words × Felt252Nats),(memAssign.HasValue addr1 vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1)) ↔
        (∃ (vs : Felt252Words × Felt252Nats),(memAssign.HasValue addr2 vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1)) := by
  constructor
  all_goals
    intro h
    rcases h with ⟨vs, h_vs⟩
    use vs
  exact (same_value_eq_of_id_eq h_id vs).mp h_vs
  exact (same_value_eq_of_id_eq h_id vs).mpr h_vs


lemma Mem252FromMemAssign_agrees {memAssign : Felt252IdMemoryAssign} :
    memAssign.Agrees (Mem252FromMemAssign memAssign) := by
  constructor
  · intro addr1 addr2 h_id
    by_cases h : ∃ (vs : Felt252Words × Felt252Nats),(memAssign.HasValue addr1 vs.1 ∧ Felt252Nats.IsRangeChecked vs.2 vs.1)
    · rcases h with ⟨vs, h_vs1⟩
      have h_vs2 := (same_value_eq_of_id_eq h_id vs).mp h_vs1
      rw [Mem252FromMemAssign_eq_of_exists addr1 _ h_vs1, Mem252FromMemAssign_eq_of_exists addr2 _ h_vs2]
    have h2 := (not_iff_not.mpr (exists_value_eq_of_id_eq h_id)).mp h
    rw [Mem252FromMemAssign_eq_zero_of_not_exists _ h, Mem252FromMemAssign_eq_zero_of_not_exists _ h2]
  intro addr value value_n h_has h_rc
  apply Mem252FromMemAssign_eq_of_exists (memAssign := memAssign) addr (value, value_n)
  simp [h_has, h_rc]

end Felt252IdMemoryAssign

namespace Felt252IdMemory
variable {inputSize outputSize : Nat} [Fact (Nat.Prime Stwo.P)]

@[simp] def SatisfiedBy (memory : Felt252IdMemory)
    (varAssign : VarAssign) (memAssign : Felt252IdMemoryAssign) : Prop :=
  memory.addressToId.SatisfiedBy varAssign memAssign.addressToId ∧
  memory.idToValue.SatisfiedBy varAssign memAssign.idToValue

end Felt252IdMemory

/-
  Memory lookups
-/

namespace AirLookupTerms

protected def add_addr_to_id (lookups : AirLookupTerms) (addr id : FeltExpr) :
  AirLookupTerms := lookups.add MEMORY_ADDR_TO_ID_REL_INDEX (p_tuple_expr MEMORY_ADDR_TO_ID_REL_INDEX ![addr, id]) .use

protected def add_id_to_value (lookups : AirLookupTerms) (id : FeltExpr) (value : Felt252Expr) :
  AirLookupTerms := lookups.add MEMORY_ID_TO_VALUE_REL_INDEX
    (p_tuple_expr MEMORY_ID_TO_VALUE_REL_INDEX ((Fin.append ![id] value) ∘ Fin.cast (by simp ; rfl)))
    .use

-- The yields for the memory relations agree with the given memory assignment.

def AddrToIdYieldsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths MEMORY_ADDR_TO_ID_REL_INDEX)}
    (lookups : RelationTuples partition) : Prop :=
  ∀ y ∈ yield_tuples lookups, memoryAssign.HasId (y 1) (y 2)

def IdToValueYieldsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths MEMORY_ID_TO_VALUE_REL_INDEX)}
    (lookups : RelationTuples partition) : Prop :=
  ∀ y ∈ yield_tuples lookups, memoryAssign.idToValue ![y 1] = some (fun i : Fin FELT252_N_WORDS => y i.succ.succ)

def MemAddrAgreesRangeChecked [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths RANGE_CHECK_REL_INDEX)}
    (rc_lookups : RelationTuples partition) : Prop :=
  ∀ addr id : Felt, memoryAssign.HasId addr id → (p_tuple RANGE_CHECK_REL_INDEX ![29, addr]) ∈ use_tuples rc_lookups

def MemValueAgreesRangeChecked [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths RANGE_CHECK_REL_INDEX)}
    (rc_lookups : RelationTuples partition) : Prop :=
  ∀ (id : Felt) (value : Felt252Words),
    memoryAssign.idToValue ![id] = some value → ∀ i, (p_tuple RANGE_CHECK_REL_INDEX ![9, value i]) ∈ use_tuples rc_lookups

def MemYieldsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {id_p value_p : Fin (NUM_PARTITIONS + 1)}
    {id_partition : LookupPartition v id_p (rel_lengths MEMORY_ADDR_TO_ID_REL_INDEX)}
    {value_partition : LookupPartition v value_p (rel_lengths MEMORY_ID_TO_VALUE_REL_INDEX)}
    (id_lookups : RelationTuples id_partition)
    (value_lookups : RelationTuples value_partition) : Prop :=
  AddrToIdYieldsAgree memoryAssign v id_lookups ∧ IdToValueYieldsAgree memoryAssign v value_lookups

def MemYieldsAgreeAndRangeChecked [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (memoryAssign : Felt252IdMemoryAssign)
    (v : LookupValues t n_s NUM_PARTITIONS)
    {rc_p id_p value_p : Fin (NUM_PARTITIONS + 1)}
    {rc_partition : LookupPartition v rc_p (rel_lengths RANGE_CHECK_REL_INDEX)}
    {id_partition : LookupPartition v id_p (rel_lengths MEMORY_ADDR_TO_ID_REL_INDEX)}
    {value_partition : LookupPartition v value_p (rel_lengths MEMORY_ID_TO_VALUE_REL_INDEX)}
    (rc_lookups : RelationTuples rc_partition)
    (id_lookups : RelationTuples id_partition)
    (value_lookups : RelationTuples value_partition) : Prop :=
  MemYieldsAgree memoryAssign v id_lookups value_lookups
    ∧ MemAddrAgreesRangeChecked memoryAssign v rc_lookups
    ∧ MemValueAgreesRangeChecked memoryAssign v rc_lookups

lemma mem_addr_to_id_SatisfiedBy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (term : LookupTerm rel_lengths)
      (varAssign : VarAssign)
      (memoryAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_agrees : UseAgrees term varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (h_mem : AddrToIdYieldsAgree memoryAssign h_satisfied.values (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)) :
    term.rel = MEMORY_ADDR_TO_ID_REL_INDEX → term.useOrYield = .use →
      memoryAssign.addressToId ![(term.eval varAssign).tuple 1] = some ![(term.eval varAssign).tuple 2] := by
  intro h_rel h_use
  have h_chain : term.rel ∉ chain_rels := by rw [h_rel] ; apply memory_addr_not_chain_rel
  apply rel_lookup_sound term h_use h_chain varAssign h_satisfied h_agrees (fun x => memoryAssign.addressToId ![x 1] = some ![x 2])
  simp [MEMORY_ADDR_TO_ID_REL_INDEX] at h_rel h_mem
  rw [h_rel]
  intro y h_y
  apply h_mem y
  exact h_y

def MemIdToValueTerm (id : FeltExpr) (value : Felt252Expr) : LookupTerm rel_lengths := {
  rel := MEMORY_ID_TO_VALUE_REL_INDEX
  tuple := p_tuple_expr MEMORY_ID_TO_VALUE_REL_INDEX ((Fin.append ![id] value) ∘ Fin.cast (by simp ; rfl))
  useOrYield := .use
}

lemma MemIdToValue_tuple_len_eq : raw_rel_lengths MEMORY_ID_TO_VALUE_REL_INDEX + 1 = 1 + FELT252_N_WORDS := by
  simp [raw_rel_lengths, MEMORY_ID_TO_VALUE_REL_INDEX, FELT252_N_WORDS] ; rfl

def MemIdToValueRawTuple (id : Felt) (value : Felt252Words) : Fin (raw_rel_lengths MEMORY_ID_TO_VALUE_REL_INDEX + 1) → Felt :=
  (Fin.append ![id] value) ∘ Fin.cast MemIdToValue_tuple_len_eq

lemma id_eq_MemIdToValueTuple (id : Felt) (value : Felt252Words) :
    p_tuple MEMORY_ID_TO_VALUE_REL_INDEX (MemIdToValueRawTuple id value) 1 = id := by
  exact rfl

lemma value_eq_MemIdToValueTuple (id : Felt) (value : Felt252Words) :
    (fun i => p_tuple MEMORY_ID_TO_VALUE_REL_INDEX (MemIdToValueRawTuple id value) i.succ.succ) = value := by
  apply funext
  intro i
  rw [p_tuple_i_eq_tuple_i_sub_one]
  · simp [MemIdToValueRawTuple]
    rw [←Fin.append_right ![id] value]
    apply congr_arg
    rw [Fin.natAdd_mk]
    simp [add_comm]
  · rw [Fin.val_ne_zero_iff]
    apply Fin.succ_ne_zero
  simp [Fin.succ]
  apply lt_of_lt_of_le (Fin.isLt i)
  simp [FELT252_N_WORDS, raw_rel_lengths, MEMORY_ID_TO_VALUE_REL_INDEX]
  rfl

lemma mem_id_to_value_SatisfiedBy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (id : FeltExpr)
      (value : Felt252Expr)
      (varAssign : VarAssign)
      (memoryAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_agrees : UseAgrees (MemIdToValueTerm id value) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (h_mem : IdToValueYieldsAgree memoryAssign h_satisfied.values (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX)) :
    memoryAssign.idToValue ![id.eval varAssign] = some (value.eval varAssign) := by
  replace h_mem := h_mem (p_tuple MEMORY_ID_TO_VALUE_REL_INDEX (MemIdToValueRawTuple (id.eval varAssign) (value.eval varAssign)))
  rw [id_eq_MemIdToValueTuple, value_eq_MemIdToValueTuple] at h_mem
  apply h_mem
  rcases mem_yield_of_mem_use h_satisfied MEMORY_ID_TO_VALUE_REL_INDEX memory_id_not_chain_rel ((MemIdToValueTerm id value).eval varAssign).tuple (h_agrees rfl) with
    ⟨y, h_y_mem, h_eq⟩
  suffices h : p_tuple MEMORY_ID_TO_VALUE_REL_INDEX (MemIdToValueRawTuple (FeltExpr.eval varAssign id) (Felt252Expr.eval varAssign value)) = y by
    rw [h] ; apply h_y_mem
  rw [←h_eq]
  unfold MemIdToValueTerm LookupTerm.eval
  exact List.ofFn_inj.mp rfl

lemma mem_addr_to_id_SatisfiedBy_add [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (memoryAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_mem : AddrToIdYieldsAgree memoryAssign h_satisfied.values (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX))
      (addr id : FeltExpr) :
    UseAgree (terms.add_addr_to_id addr id) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      memoryAssign.addressToId ![addr.eval varAssign] = some ![(id.eval varAssign)]
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
  intro h
  have h_agree_addr_to_id := UseAgree_add.mp h
  simp_all only [and_true]
  apply mem_addr_to_id_SatisfiedBy
    { rel := MEMORY_ADDR_TO_ID_REL_INDEX, tuple := p_tuple_expr MEMORY_ADDR_TO_ID_REL_INDEX ![addr, id], useOrYield := .use }
    _ _ _ h_agree_addr_to_id.1 h_mem
  simp ; simp

lemma mem_id_to_value_SatisfiedBy_add [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (memoryAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_mem : IdToValueYieldsAgree memoryAssign h_satisfied.values (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (id : FeltExpr)
      (value : Felt252Expr) :
    UseAgree (terms.add_id_to_value id value) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      memoryAssign.idToValue ![id.eval varAssign] = some (value.eval varAssign)
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
  intro h
  have h_agree_id_to_value := UseAgree_add.mp h
  simp_all only [and_true]
  apply mem_id_to_value_SatisfiedBy _ _ _ _ _ h_agree_id_to_value.1 h_mem

lemma HasValue_add_mem [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (memoryAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_mem : MemYieldsAgree memoryAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (addr id : FeltExpr)
      (value : Felt252Expr) :
    UseAgree ((terms.add_addr_to_id addr id).add_id_to_value id value) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      Felt252IdMemoryAssign.HasValue memoryAssign (addr.eval varAssign) (value.eval varAssign)
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
  intro h
  have h_agree_id_to_value := UseAgree_add.mp h
  have h_agree_addr_to_id := UseAgree_add.mp h_agree_id_to_value.2
  simp_all only [and_true]
  use (id.eval varAssign)
  constructor
  · apply mem_addr_to_id_SatisfiedBy _ _ _ _ h_agree_addr_to_id.1 h_mem.1
    simp ; simp
  apply mem_id_to_value_SatisfiedBy _ _ _ _ _ h_agree_id_to_value.1 h_mem.2

lemma mem_isRangeChecked_of_agrees_range_checked [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      (memAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_id : MemAddrAgreesRangeChecked memAssign h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_value : MemValueAgreesRangeChecked memAssign h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX)) :
    memAssign.IsRangeChecked := by
  constructor
  · intro addr id h_has
    apply h_rc (p_tuple RANGE_CHECK_REL_INDEX ![29, addr])
    rcases mem_yield_of_mem_use _ _ range_check_not_chain_rel _ (h_id addr id h_has) with ⟨y, h_y_mem, h_y_eq⟩
    simp [h_y_eq, h_y_mem]
  intro addr value h_has
  suffices h : ∀ i, ∃ n : Nat, value i = ↑n ∧ n < 2^9 by
    use fun i => Classical.choose (h i)
    intro i
    apply Classical.choose_spec (h i)
  intro i
  rcases h_has with ⟨id, h_to_id, h_to_value⟩
  rcases mem_yield_of_mem_use _ _ range_check_not_chain_rel _ (h_value id value h_to_value i) with ⟨y, h_y_mem, h_y_eq⟩
  rw [←h_y_eq] at h_y_mem
  rcases h_rc (p_tuple RANGE_CHECK_REL_INDEX ![9, (value i)]) h_y_mem with ⟨n, h_n_lt, h_n_eq⟩
  use n, h_n_eq, h_n_lt

lemma mem_isRangeChecked_of_agree_and_range_checked [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      (memAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX)) :
    memAssign.IsRangeChecked := by
  apply mem_isRangeChecked_of_agrees_range_checked _ _ h_rc h_mem.2.1 h_mem.2.2

end AirLookupTerms
