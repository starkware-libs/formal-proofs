import Verification.AirInfra.Soundness.Components
import Verification.AirInfra.Soundness.PublicMemory
import Verification.AirInfra.Soundness.OpcodeLookupCall
import Verification.AirInfra.Core.Felt252IdMemory.Memory
import Verification.AirInfra.Airs.Casm.DecodeInstruction.VerifyInst

noncomputable section

open OpcodeLookup

def ComponentLookupCall [Fact (Nat.Prime Stwo.P)]
      (c : Component) : AirBuilder × AirLookupTerms :=
     match c with
      | .Opcode (o : Opcode) => OpcodeLookup.LookupCall o
      | .RangeCheck => RangeCheckTable.LookupCall
      | .MemoryAddrToId => Felt252IdMemory.AddrToIdLookupCall
      | .MemoryIdToValue => Felt252IdMemory.IdToValueLookupCall
      | .VerifyInstr => VerifyInstruction.LookupCall

-- For component c: evaluations of all its lookup terms.
def ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)] (c : Component) (varAssigns : Array VarAssign) :=
  (ComponentLookupCall c).2.flatMap (fun term => (varAssigns.map (fun v => (term.eval v))))
-- All evaluated lookups of all components.
def ComponentLookups [Fact (Nat.Prime Stwo.P)] (varAssigns : Component → Array VarAssign) :=
  Component.univ.toArray.flatMap (fun c => ComponentLookupTermsEval c (varAssigns c))

/-
  Add the lookups not added by the components:
  1. The public memory use memory lookups.
  2. The initial and final state trace lookups.
-/
def AllLookups [Fact (Nat.Prime Stwo.P)]
      (inp : InputData)
      (pubMem : PublicMem.Lookups)
      (varAssigns : Component → Array VarAssign) :=
    (((ComponentLookups varAssigns).append pubMem.lookups).push
        { rel := OPCODE_TRACE_REL_INDEX, tuple := CasmStateValTuple (initialState inp), useOrYield := .yield }
    ).push
       { rel := OPCODE_TRACE_REL_INDEX, tuple := CasmStateValTuple (finalState inp), useOrYield := .use }


lemma mem_ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)] {c : Component} {varAssigns : Array VarAssign} :
  ∀ t_eval ∈ ComponentLookupTermsEval c varAssigns,
    ∃ (t : LookupTerm rel_lengths) (v : VarAssign),
      t ∈ (ComponentLookupCall c).2 ∧
      v ∈ varAssigns ∧
      t_eval = t.eval v := by
  intro t_eval h_t_eval
  simp only [ComponentLookupTermsEval, Array.mem_flatMap, Array.mem_map, eq_comm] at h_t_eval
  rcases h_t_eval with ⟨t, h_t, v, h_v, h_eq⟩
  exact ⟨t, v, h_t, h_v, h_eq⟩

def OpcodeVarAssigns (varAssigns : Component → Array VarAssign) : Opcode → Array VarAssign :=
  fun o => varAssigns (.Opcode o)

/-
  Specific Relation Lookups
-/

-- The component lookups for a specific relation and use/yield choice.
def RelComponentLookups [Fact (Nat.Prime Stwo.P)]
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (useOrYield : UseOrYield) :=
  (ComponentLookups varAssigns).filter (fun term => term.rel = rel ∧ term.useOrYield = useOrYield)

lemma RelComponentLookups_rel_eq [Fact (Nat.Prime Stwo.P)]
      {varAssigns : Component → Array VarAssign}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {useOrYield : UseOrYield}:
    ∀ t ∈ RelComponentLookups varAssigns rel useOrYield, t.rel = rel := by
  intro t h_t
  exact (decide_eq_true_iff.mp (Array.mem_filter.mp h_t).2).1

-- Auxiliary lemmas
lemma Array.flatMap_filter {α : Type u_1} {β : Type u_2} {as : Array α} {f : α → Array β} {p : α → Bool}
    (h : ∀ a, p a = false → f a = #[]) :
    flatMap f (Array.filter p as) = flatMap f as := by
  simp only [Array.flatMap_def]
  conv_rhs => rw [←Array.flatten_filter_not_isEmpty, Array.filter_map]
  conv_lhs => rw [←Array.flatten_filter_not_isEmpty, Array.filter_map]
  simp only [filter_filter]
  congr
  apply funext
  intro x
  rw [Bool.and_eq_left_iff_imp]
  simp [not_imp_comm]
  exact h x

lemma Array.flatMap_filter' {α : Type u_1} {β : Type u_2} (as : Array α) (f : α → Array β) (p : α → Bool) (q : β → Bool)
    (h1 : ∀ a, p a = false → filter q (f a) = #[])
    (h2 : ∀ a, p a = true → filter q (f a) = f a) :
    flatMap f (Array.filter p as) = flatMap (filter q ∘ f) as := by
  simp only [Array.flatMap_def]
  conv_rhs => rw [←Array.flatten_filter_not_isEmpty, Array.filter_map]
  conv_lhs => rw [←Array.flatten_filter_not_isEmpty, Array.filter_map] ; simp only [filter_filter]
  congr 1
  have h_f : (fun a => ((fun xs => !xs.isEmpty) ∘ f) a && p a) = ((fun xs => !xs.isEmpty) ∘ (fun as => filter q as) ∘ f) := by
    apply funext ; intro a
    by_cases h_p : p a
    · simp [h_p, h2 a]
    rw [Bool.not_eq_true] at h_p
    simp only [h_p, Bool.and_false, Function.comp_apply]
    rw [eq_comm, Bool.not_eq_false', Array.isEmpty_iff]
    exact h1 a h_p
  rw [h_f, Array.map_eq_map_iff]
  intro a h_a
  rw [Array.mem_filter] at h_a
  by_cases h_p : p a
  · simp [h2 a h_p]
  rw [Bool.not_eq_true] at h_p
  simp only [Function.comp_apply, h1 a h_p, Bool.not_eq_true', Array.isEmpty_eq_false_iff] at h_a
  exfalso ; exact h_a.2 rfl

lemma Array.flatMap_filter'' {α : Type u_1} {β : Type u_2} (as : Array α) (f : α → Array β) (p : α → Bool) (q : β → Bool)
    (h1 : ∀ a, p a = false → filter q (f a) = #[])
    (h2 : ∀ a, p a = true → filter q (f a) = f a) :
    flatMap f (Array.filter p as) = flatMap (fun a => filter q (f a)) as := by
  rw [Array.flatMap_filter' as f p q h1 h2]
  congr 1


-- Alternative definition, where we first filter the lookup terms and only then
-- evaluate and collect the lookups.
def RelComponentLookups_alt [Fact (Nat.Prime Stwo.P)]
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (useOrYield : UseOrYield) :=
  Component.univ.toArray.flatMap (fun c =>
      ((ComponentLookupCall c).2.filter (fun term => term.rel = rel ∧ term.useOrYield = useOrYield)).flatMap
        (fun term => ((varAssigns c).map (fun v => (term.eval v)))))

-- Filtering after evaluating and collecting all lookups is the same as filtering
-- the lookup terms and then evaluating and collecting all lookups.
lemma RelComponentLookups_eq_RelComponentLookups_alt [Fact (Nat.Prime Stwo.P)]
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (useOrYield : UseOrYield) :
    RelComponentLookups varAssigns rel useOrYield = RelComponentLookups_alt varAssigns rel useOrYield := by
  unfold RelComponentLookups ComponentLookups ComponentLookupTermsEval
  rw [Array.filter_flatMap]
  congr 1 ; apply funext ; intro c
  rw [Array.filter_flatMap, eq_comm]
  apply Array.flatMap_filter'
  · intro t h_t
    rw [Array.filter_map, Array.map_eq_empty_iff]
    simp only [Array.filter_eq_empty_iff, Function.comp_apply, LookupTerm.eval, h_t]
    simp
  intro t h_t
  simp only [Array.filter_eq_self, LookupTerm.eval]
  intro tv h_tv
  rw [Array.mem_map] at h_tv
  rcases h_tv with ⟨v, h_v⟩
  simp [←h_v.2]
  rw [decide_eq_true_eq] at h_t
  exact h_t

-- All lookups for a specific relation and use/yield choice.
def RelLookups [Fact (Nat.Prime Stwo.P)]
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (useOrYield : UseOrYield) :=
  (AllLookups inp pubMemLookups varAssigns).filter (fun term => term.rel = rel ∧ term.useOrYield = useOrYield)

lemma RelLookups_rel_eq [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {useOrYield : UseOrYield}:
    ∀ t ∈ RelLookups inp pubMemLookups varAssigns rel useOrYield, t.rel = rel := by
  intro t h_t
  exact (decide_eq_true_iff.mp (Array.mem_filter.mp h_t).2).1

lemma RelLookups_useOrYield_eq [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {useOrYield : UseOrYield}:
    ∀ t ∈ RelLookups inp pubMemLookups varAssigns rel useOrYield, t.useOrYield = useOrYield := by
  intro t h_t
  exact (decide_eq_true_iff.mp (Array.mem_filter.mp h_t).2).2

def RelLookups_eq_RelComponentLookups [Fact (Nat.Prime Stwo.P)]
      (inp : InputData)
      (pubMemLookups : PublicMem.Lookups)
      (varAssigns : Component → Array VarAssign)
      (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (useOrYield : UseOrYield) :
    rel ≠ OPCODE_TRACE_REL_INDEX ∧ useOrYield = .yield →
      RelLookups inp pubMemLookups varAssigns rel useOrYield = RelComponentLookups varAssigns rel useOrYield := by
  intro h
  rw [ne_eq, eq_comm] at h
  simp only [RelLookups, AllLookups, Bool.decide_and, Array.filter_push, decide_eq_false h.1,
    Bool.false_and, Bool.false_eq_true]
  simp only [↓reduceIte, Array.append_eq_append, Array.size_append, Array.filter_append]
  simp only [RelComponentLookups, Bool.decide_and, Array.append_right_eq_self, Array.filter_eq_empty_iff, h.2]
  intro t h_t
  simp  [(pubMemLookups.h_mem t h_t).1]

-- The component tuples for a specific relation.
def RelComponentLookupTuples [Fact (Nat.Prime Stwo.P)]
      (varAssigns : Component → Array VarAssign)
      (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (useOrYield : UseOrYield)
    : Array (Fin (rel_lengths rel + 1) → Felt) :=
  (RelComponentLookups varAssigns rel useOrYield).attach.map
    (fun t => t.1.tuple ∘ Fin.cast (by simp only [RelComponentLookups_rel_eq t t.2]))

-- All tuples for a specific relation and use/yield choice.
def RelLookupTuples [Fact (Nat.Prime Stwo.P)]
      (inp : InputData)
      (pubMemLookups : PublicMem.Lookups)
      (varAssigns : Component → Array VarAssign)
      (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (useOrYield : UseOrYield)
    : Array (Fin (rel_lengths rel + 1) → Felt) :=
  (RelLookups inp pubMemLookups varAssigns rel useOrYield).attach.map
    (fun t => t.1.tuple ∘ Fin.cast (by simp only [RelLookups_rel_eq t t.2]))

lemma mem_RelLookupTuples_iff [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {useOrYield : UseOrYield} :
    ∀ tuple, tuple ∈ RelLookupTuples inp pubMemLookups varAssigns rel useOrYield ↔
      ∃ term ∈ RelLookups inp pubMemLookups varAssigns rel useOrYield,
        ∃ (h : term.rel = rel),
          term.useOrYield = useOrYield ∧ tuple = term.tuple ∘ Fin.cast (by simp [h]) := by
  intro tuple
  constructor
  · intro h_tuple_mem
    simp only [RelLookupTuples, Array.mem_map] at h_tuple_mem
    rcases h_tuple_mem with ⟨term, h_term_mem, h_term⟩
    use term, (Subtype.mem term), (RelLookups_rel_eq _ (Subtype.mem term))
    use (RelLookups_useOrYield_eq _ (Subtype.mem term)), h_term.symm
  intro h_term
  rcases h_term with ⟨term, h_term_mem, h_rel, h_useOrYield, h_tuple⟩
  simp only [RelLookupTuples, Array.mem_map]
  use ⟨term, h_term_mem⟩
  constructor
  · apply Array.mem_attach
  simp only [h_tuple.symm]

/-
  Global Assumptions
-/

-- All variable assignments to the components satisfy the component constraints.
def ComponentsSatisfied [Fact (Nat.Prime Stwo.P)] (varAssigns : Component → Array VarAssign) :=
  ∀ c, ∀ v ∈ varAssigns c, (ComponentLookupCall c).1.SatisfiedBy v

/-
  Use agrees

  For a specific relation, the tuples resulting from evaluating
  the use lookup terms are equal to the use tuples for that relation
  which appear in the lookup constraints.
-/

def RelUseLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    {values : LookupValues t n_s NUM_PARTITIONS}
    {partition : LookupPartition values (rel_partition rel) (rel_lengths rel)}
    (tuples : RelationTuples partition) :=
  Multiset.map partition.tuples tuples.use_i.val =
    (RelLookupTuples inp pubMemLookups varAssigns rel .use).toList

/-
  Yield agrees

  For a specific relation, the tuples resulting from evaluating
  the yield lookup terms are equal to the use tuples for that relation
  which appear in the lookup constraints.
-/

def RelYieldLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign)
    (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    {values : LookupValues t n_s NUM_PARTITIONS}
    {partition : LookupPartition values (rel_partition rel) (rel_lengths rel)}
    (tuples : RelationTuples partition) :=
  Multiset.map partition.tuples tuples.yield_i.val =
    (RelLookupTuples inp pubMemLookups varAssigns rel .yield).toList

/-
  Use Lookups Agree
-/

lemma use_mem_iff_mem [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition rel) (rel_lengths rel)}
      {tuples : RelationTuples partition} :
    ∀ t, t ∈ use_tuples tuples ↔ t ∈ Multiset.map partition.tuples tuples.use_i.val := by
  intro t
  simp [use_tuples, Finset.image]

lemma yield_mem_iff_mem [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition rel) (rel_lengths rel)}
      {tuples : RelationTuples partition} :
    ∀ t, t ∈ yield_tuples tuples ↔ t ∈ Multiset.map partition.tuples tuples.yield_i.val := by
  intro t
  simp [yield_tuples, Finset.image]

lemma UseAgree_of_RelLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    ∀ c, ∀ v ∈ varAssigns c, (ComponentLookupCall c).2.UseAgree v values partitions tuples := by
  intro c v h_v
  simp only [AirLookupTerms.UseAgree]
  intro t h_t_mem h_t_use
  rw [use_mem_iff_mem, h_agree t.rel]
  simp only [Multiset.mem_coe, Array.mem_toList_iff]
  simp only [RelLookupTuples, Array.mem_map]
  simp only [Array.mem_attach, true_and, Subtype.exists]
  use t.eval v
  have h_mem : LookupTerm.eval v t ∈ RelLookups inp pubMemLookups varAssigns t.rel UseOrYield.use := by
    simp [RelLookups]
    constructor
    · simp only [AllLookups, Array.mem_push]
      left ; left
      simp only [Array.append_eq_append, Array.mem_append]
      left
      simp only [ComponentLookups, Array.mem_flatMap]
      use c
      rw [Array.mem_toArray]
      use Component.univ_complete c
      simp [ComponentLookupTermsEval]
      use t, h_t_mem, v
    simp [LookupTerm.eval, h_t_use]
  use h_mem
  simp

lemma pub_mem_of_RelLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      --{values : LookupValues t n_s NUM_LOOKUP_REL_MINUS_ONE}
      --{tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples values k (rel_lengths k)}
      (h_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups) :
    ∀ addr252 value252,
      inp.mStar addr252 = some value252 →
         ∃ (addr id : Felt) (value : Felt252Words),
          addr.toFelt252 = addr252 ∧
          value.eval = value252 ∧
            (p_tuple MEMORY_ADDR_TO_ID_REL_INDEX ![addr, id]) ∈ use_tuples (tuples MEMORY_ADDR_TO_ID_REL_INDEX) ∧
            (p_tuple MEMORY_ID_TO_VALUE_REL_INDEX ((Fin.append ![id] value) ∘ Fin.cast (by simp ; rfl))) ∈
              use_tuples (tuples MEMORY_ID_TO_VALUE_REL_INDEX) := by
    intro addr252 value252 h_mStar
    rcases h_pubMem addr252 value252 h_mStar with ⟨addr, id, value, h_addr_eq, h_value_eq, h_addr_lk, h_value_lk⟩
    use addr, id, value, h_addr_eq, h_value_eq
    simp only [use_mem_iff_mem]
    rw [h_agree, h_agree]
    simp only [Multiset.mem_coe, Array.mem_toList_iff, mem_RelLookupTuples_iff]
    constructor
    · use { rel := MEMORY_ADDR_TO_ID_REL_INDEX, tuple := p_tuple MEMORY_ADDR_TO_ID_REL_INDEX ![addr, id], useOrYield := UseOrYield.use }
      constructor
      · unfold RelLookups AllLookups
        simp only [Array.mem_filter, Bool.decide_and, decide_true, Bool.and_self, and_true]
        simp only [Array.mem_push]
        left ; left
        rw [Array.append_eq_append]
        apply Array.mem_append_right _ h_addr_lk
      use rfl, rfl
      simp
    use {
      rel := MEMORY_ID_TO_VALUE_REL_INDEX,
      tuple := p_tuple MEMORY_ID_TO_VALUE_REL_INDEX (Fin.append ![id] value ∘ Fin.cast (by simp ; rfl)),
      useOrYield := UseOrYield.use }
    constructor
    · unfold RelLookups AllLookups
      simp only [Array.mem_filter, Bool.decide_and, decide_true, Bool.and_self, and_true]
      simp only [Array.mem_push]
      left ; left
      rw [Array.append_eq_append]
      apply Array.mem_append_right _ h_value_lk
    use rfl, rfl
    simp

/-
  Verify Instruction Lookups
-/

-- The yield VERIFY_INSTR evaluated lookups
def VerifyInstrYieldLookups [Fact (Nat.Prime Stwo.P)]
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign) :=
  RelLookups inp pubMemLookups varAssigns VERIFY_INSTR_REL_INDEX .yield

lemma VerifyInstrLookups_rel_eq [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ t ∈ VerifyInstrYieldLookups inp pubMemLookups varAssigns, t.rel = VERIFY_INSTR_REL_INDEX := by
  intro t h_t
  exact (decide_eq_true_iff.mp (Array.mem_filter.mp h_t).2).1

lemma verify_instr_not_mem_ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)]
      (c : Component)
      (h_c : c ≠ .VerifyInstr)
      (varAssigns : Array VarAssign) :
    ∀ tv : LookupTermVal rel_lengths,
        decide (tv.rel = VERIFY_INSTR_REL_INDEX ∧ tv.useOrYield = UseOrYield.yield) = true →
          tv ∉ (ComponentLookupTermsEval c varAssigns) := by
    intro tv h_tv
    by_contra h_tv_eval
    rcases mem_ComponentLookupTermsEval tv h_tv_eval with ⟨t, v, h_t, h_v, h_eq⟩
    simp [LookupTerm.eval] at h_eq
    simp [decide_eq_true_eq, h_eq] at h_tv
    cases c
    case Opcode o =>
      simp [OpcodeLookup.lookupCall_yield_term t h_t h_tv.2] at h_tv
      exact not_eq_of_beq_eq_false rfl h_tv
    case VerifyInstr =>
      exfalso ; apply h_c rfl
    case MemoryIdToValue =>
      have h_t_mem := Felt252IdMemory.mem_yield_of_IdToValueLookupCall t h_t h_tv.2
      apply AirLookupTerms.not_mem_add' _ h_t_mem
      simp [h_tv.1, h_tv.2, MEMORY_ID_TO_VALUE_REL_INDEX, VERIFY_INSTR_REL_INDEX]
      apply Array.not_mem_empty
    all_goals
      revert h_t
      repeat
        apply AirLookupTerms.not_mem_add'
        simp [h_tv.1, h_tv.2, RANGE_CHECK_REL_INDEX, MEMORY_ADDR_TO_ID_REL_INDEX, VERIFY_INSTR_REL_INDEX]
      apply Array.not_mem_empty



lemma mem_VerifyInstrLookups [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ VerifyInstrYieldLookups inp pubMemLookups varAssigns,
      ∃ t ∈ VerifyInstruction.LookupCall.2, ∃ v ∈ varAssigns .VerifyInstr, tv = t.eval v := by
  intro tv h_tv
  rw [VerifyInstrYieldLookups, RelLookups_eq_RelComponentLookups _ _ _ _ _] at h_tv
  · simp only [RelComponentLookups, Array.mem_filter, ComponentLookups, Array.mem_flatMap] at h_tv
    rcases h_tv with ⟨⟨c, h_c_mem, h_tv_mem⟩, h_p⟩
    by_cases h : c = .VerifyInstr
    · rw [h] at h_tv_mem
      rcases mem_ComponentLookupTermsEval tv h_tv_mem with ⟨t, v, h_t_mem, h_v_mem, h_tv_eq⟩
      use t, h_t_mem, v
    exfalso
    apply verify_instr_not_mem_ComponentLookupTermsEval _ _ _ tv h_p h_tv_mem
    simp [h]
  simp [VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma VerifyInstrYieldAgrees_of_agree_and_satisfy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_components: ComponentsSatisfied varAssigns)
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_agree : RelYieldLookupsAgree inp pubMemLookups varAssigns VERIFY_INSTR_REL_INDEX (tuples VERIFY_INSTR_REL_INDEX)) :
    AirLookupTerms.VerifyInstrYieldAgrees tuples := by
  unfold AirLookupTerms.VerifyInstrYieldAgrees
  intro tuple h_tuple_mem
  rw [yield_mem_iff_mem, h_agree] at h_tuple_mem
  simp only [Multiset.mem_coe, Array.mem_toList_iff] at h_tuple_mem
  simp only [RelLookupTuples, Array.mem_map] at h_tuple_mem
  simp only [Array.mem_attach, true_and, Subtype.exists] at h_tuple_mem
  rcases h_tuple_mem with ⟨t, h_t_mem, h_t_eq⟩
  rcases mem_VerifyInstrLookups t h_t_mem with ⟨t_verify, h_t_verify_mem, v, h_v_mem, h_eval_eq⟩
  use t_verify, h_t_verify_mem
  simp only [RelLookups, Array.mem_filter, decide_eq_true_eq] at h_t_mem
  subst h_eval_eq
  simp only [LookupTerm.eval] at h_t_mem
  use h_t_mem.2.1, h_t_mem.2.2
  use v, h_components .VerifyInstr v h_v_mem
  use UseAgree_of_RelLookupsAgree h_use_agree .VerifyInstr v h_v_mem
  simp only [←h_t_eq]
  simp only [LookupTerm.eval]
  apply funext
  intro i
  simp


/-
  Opcode Trace lookups
-/

lemma filter_Component_univ_eq_Opcode_univ :
    Array.map (fun o => Component.Opcode o) Opcode.univ.toArray =
      (Array.filter (fun c => match c with | .Opcode _ => true | _ => false) Component.univ.toArray) := by
  simp only [List.filter_toArray, Component.univ, List.filter_append, List.filter_filter]
  simp only [←List.append_toArray]
  rw [Array.append_right_eq_self.mpr _]
  · rw [List.filter_map, ←List.map_toArray]
    congr 2
    rw [eq_comm, List.filter_eq_self]
    simp
  simp only [←Array.isEmpty_iff, List.isEmpty_toArray, List.isEmpty_iff, List.filter_eq_nil_iff]
  intro c h_c
  simp only [Bool.and_eq_true, not_and, Bool.not_eq_true]
  intro h
  split
  · rfl
  simp_all

lemma flatMap_filter_Component_univ_eq_flatMap_Opcode_univ {α : Type u_1} {f : Component → Array α} :
    Array.flatMap (fun o => f (Component.Opcode o)) Opcode.univ.toArray =
      Array.flatMap f (Array.filter (fun c => match c with | .Opcode _ => true | _ => false) Component.univ.toArray) := by
  rw [←filter_Component_univ_eq_Opcode_univ, Array.flatMap_map]

lemma NoTermsOfRel_OPCODE_TRACE [Fact (Nat.Prime Stwo.P)] (c : Component)
      (h_c : (match c with
              | Component.Opcode _ => true
              | _ => false) = false) :
    AirLookupTerms.NoTermsOfRel (ComponentLookupCall c).2 OPCODE_TRACE_REL_INDEX := by
  cases c
  · exfalso ; simp at h_c
  all_goals
    repeat
      apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
      simp [RANGE_CHECK_REL_INDEX, MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]
    apply AirLookupTerms.empty_NoTermsOfRel OPCODE_TRACE_REL_INDEX

lemma RelComponentLookups_OPCODE_TRACE_eq [Fact (Nat.Prime Stwo.P)]
    {varAssigns : Component → Array VarAssign}
    {useOrYield : UseOrYield} :
    RelComponentLookups varAssigns OPCODE_TRACE_REL_INDEX useOrYield =
      Array.flatMap
    (fun o =>
      Array.flatMap (fun term => Array.map (fun v => LookupTerm.eval v term) (OpcodeVarAssigns varAssigns o))
        (Array.filter (fun term => decide (term.rel = OPCODE_TRACE_REL_INDEX ∧ term.useOrYield = useOrYield))
          (OpcodeAirFns o).2.1))
    Opcode.univ.toArray := by
  unfold RelComponentLookups ComponentLookups ComponentLookupTermsEval ComponentLookupCall LookupCall OpcodeVarAssigns
  rw [Array.filter_flatMap]
  rw [←Array.flatMap_filter (p := (fun c => match c with | .Opcode _ => true | _ => false))]
  · rw [←flatMap_filter_Component_univ_eq_flatMap_Opcode_univ]
    congr
    apply funext
    intro o
    simp only
    rw [Array.filter_flatMap, eq_comm]
    apply Array.flatMap_filter'
    · intro term h_term
      simp only [Array.filter_map, LookupTerm.eval]
      simp only [Array.map_eq_empty_iff, Array.filter_eq_empty_iff, Function.comp_apply]
      simp [h_term]
    intro term h_term
    simp only [Array.filter_map]
    congr
    simp only [Array.filter_eq_self, LookupTerm.eval, Function.comp_apply]
    simp [h_term]
  intro c h_c
  simp only [Array.filter_eq_empty_iff]
  cases c
  · simp at h_c
  all_goals
    simp only
    intro tv h_tv
    simp only [Array.mem_flatMap] at h_tv
    rcases h_tv with ⟨t, h_t_mem, h_tv_mem⟩
    rw [Array.mem_iff_getElem] at h_t_mem
    rw [Array.mem_map] at h_tv_mem
    rcases h_t_mem with ⟨i, h_i_lt, h_i_eq⟩
    rcases h_tv_mem with ⟨v, h_v_mem, h_tv_eq⟩
    simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, not_and_or, ←h_tv_eq, LookupTerm.eval, ←h_i_eq]
    left
  case MemoryAddrToId =>
    have h_no_rel := NoTermsOfRel_OPCODE_TRACE .MemoryAddrToId h_c i h_i_lt
    simp_all [ComponentLookupCall]
  case MemoryIdToValue =>
    have h_no_rel := NoTermsOfRel_OPCODE_TRACE .MemoryIdToValue h_c i h_i_lt
    simp_all [ComponentLookupCall]
  case VerifyInstr =>
    have h_no_rel := NoTermsOfRel_OPCODE_TRACE .VerifyInstr h_c i h_i_lt
    simp_all [ComponentLookupCall]
  case RangeCheck =>
    have h_no_rel := NoTermsOfRel_OPCODE_TRACE .RangeCheck h_c i h_i_lt
    simp_all [ComponentLookupCall]


lemma RelComponentLookups_OPCODE_TRACE_eq_InStateLookups [Fact (Nat.Prime Stwo.P)]
      {varAssigns : Component → Array VarAssign} :
    RelComponentLookups varAssigns OPCODE_TRACE_REL_INDEX .use = (InStateLookups (OpcodeVarAssigns varAssigns)) := by
  apply RelComponentLookups_OPCODE_TRACE_eq

lemma RelComponentLookups_OPCODE_TRACE_eq_OutStateLookups [Fact (Nat.Prime Stwo.P)]
      {varAssigns : Component → Array VarAssign} :
    RelComponentLookups varAssigns OPCODE_TRACE_REL_INDEX .yield = (OutStateLookups (OpcodeVarAssigns varAssigns)) := by
  apply RelComponentLookups_OPCODE_TRACE_eq

lemma opcode_trace_use_RelLookups_eq [Fact (Nat.Prime Stwo.P)]
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use =
      (InStateTuples inp (OpcodeVarAssigns varAssigns)).map
        (fun s => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .use, tuple := s }) := by
  rw [terms_InStateTuples_eq_InStateLookups]
  simp [RelLookups, AllLookups]
  simp only [←Bool.decide_and, Array.append_push]
  congr
  rw [Array.append_right_eq_self.mpr _]
  · exact RelComponentLookups_OPCODE_TRACE_eq_InStateLookups
  rw [Array.filter_eq_empty_iff]
  intro t h_t
  cases (pubMemLookups.h_mem t h_t).2
  case inl h => simp [h, MEMORY_ADDR_TO_ID_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  case inr h => simp [h, MEMORY_ID_TO_VALUE_REL_INDEX, OPCODE_TRACE_REL_INDEX]


lemma opcode_trace_yield_RelLookups_eq [Fact (Nat.Prime Stwo.P)]
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .yield =
      (OutStateTuples inp (OpcodeVarAssigns varAssigns)).map
        (fun s => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .yield, tuple := s }) := by
  rw [terms_OutStateTuples_eq_OutStateLookups]
  simp [RelLookups, AllLookups]
  simp only [←Bool.decide_and, Array.append_push]
  congr
  rw [Array.append_right_eq_self.mpr _]
  · exact RelComponentLookups_OPCODE_TRACE_eq_OutStateLookups
  rw [Array.filter_eq_empty_iff]
  intro t h_t
  simp [(pubMemLookups.h_mem t h_t).1]

lemma RelLookups_OPCODE_TRACE_OpcodeStatePairVals_size_eq [Fact (Nat.Prime Stwo.P)]
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size =
      (OpcodeStatePairVals (OpcodeVarAssigns varAssigns)).size + 1 := by
  rw [←InStateTuples_OpcodeStatePairVals_size_eq (inp := inp)]
  rw [opcode_trace_use_RelLookups_eq, Array.size_map]

lemma InOpcodeStatesAgree_of_RelUseLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_agree : RelUseLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples) :
    Multiset.ofList (InStateTuples inp (OpcodeVarAssigns varAssigns)).toList = Multiset.map partition.tuples h_tuples.use_i.val := by
  rw [h_agree]
  congr 2
  unfold RelLookupTuples
  rw [←(Array.map_inj_right (β := LookupTermVal rel_lengths) (f := fun s => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .use, tuple := s }) _)]
  · rw [(opcode_trace_use_RelLookups_eq (pubMemLookups := pubMemLookups)).symm]
    simp only [Array.map_map, Function.comp_def]
    simp only [Array.map_attach_eq_pmap]
    rw [eq_comm]
    simp only [Array.pmap_eq_self]
    intro t h_t_mem
    cases t
    have h_rel := RelLookups_rel_eq _ h_t_mem
    have h_useOrYield := RelLookups_useOrYield_eq _ h_t_mem
    simp at h_rel
    simp at h_useOrYield
    ext
    · simp [h_rel]
    · subst h_rel
      apply heq_of_eq
      simp
    simp [h_useOrYield]
  intro t1 t2 h_eq
  simp at h_eq
  exact h_eq

lemma OutOpcodeStatesAgree_of_RelYieldLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_agree : RelYieldLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples) :
    Multiset.ofList (OutStateTuples inp (OpcodeVarAssigns varAssigns)).toList = Multiset.map partition.tuples h_tuples.yield_i.val := by
  rw [h_agree]
  congr 2
  unfold RelLookupTuples
  rw [←(Array.map_inj_right (β := LookupTermVal rel_lengths) (f := fun s => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .yield, tuple := s }) _)]
  · simp only [(opcode_trace_yield_RelLookups_eq (pubMemLookups := pubMemLookups)).symm]
    simp only [Array.map_map, Function.comp_def]
    simp only [Array.map_attach_eq_pmap]
    rw [eq_comm]
    simp only [Array.pmap_eq_self]
    intro t h_t_mem
    cases t
    have h_rel := RelLookups_rel_eq _ h_t_mem
    have h_useOrYield := RelLookups_useOrYield_eq _ h_t_mem
    simp at h_rel
    simp at h_useOrYield
    ext
    · simp [h_rel]
    · subst h_rel
      apply heq_of_eq
      simp
    simp [h_useOrYield]
  intro t1 t2 h_eq
  simp at h_eq
  exact h_eq

lemma OpcodeStatesAgree_of_lookups_agree [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      (h_tuples : RelationTuples partition)
      (h_use_agree : RelUseLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples)
      (h_yield_agree : RelYieldLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples) :
    OpcodeStatesAgree inp h_tuples (OpcodeVarAssigns varAssigns) := by
  constructor
  · exact InOpcodeStatesAgree_of_RelUseLookupsAgree h_use_agree
  exact OutOpcodeStatesAgree_of_RelYieldLookupsAgree h_yield_agree

/-
  Memory Component
-/

/-
  Memory relation yields are all from the memory components.
-/

-- The memory evaluated yield lookups

def MemAddrToIdYieldLookups [Fact (Nat.Prime Stwo.P)]
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign) :=
  RelLookups inp pubMemLookups varAssigns MEMORY_ADDR_TO_ID_REL_INDEX .yield
def MemIdToValueYieldLookups [Fact (Nat.Prime Stwo.P)]
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign) :=
  RelLookups inp pubMemLookups varAssigns MEMORY_ID_TO_VALUE_REL_INDEX .yield

lemma mem_addr_to_id_not_mem_ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)]
      {c : Component}
      (h_c : c ≠ .MemoryAddrToId)
      (varAssigns : Array VarAssign) :
    ∀ tv : LookupTermVal rel_lengths,
        decide (tv.rel = MEMORY_ADDR_TO_ID_REL_INDEX ∧ tv.useOrYield = UseOrYield.yield) = true →
          tv ∉ (ComponentLookupTermsEval c varAssigns) := by
    intro tv h_tv
    by_contra h_tv_eval
    rcases mem_ComponentLookupTermsEval tv h_tv_eval with ⟨t, v, h_t, h_v, h_eq⟩
    simp [LookupTerm.eval] at h_eq
    simp [decide_eq_true_eq, h_eq] at h_tv
    cases c
    case Opcode o =>
      simp [OpcodeLookup.lookupCall_yield_term t h_t h_tv.2] at h_tv
      exact not_eq_of_beq_eq_false rfl h_tv
    case MemoryAddrToId =>
      exfalso ; apply h_c rfl
    case MemoryIdToValue =>
      have h_t_mem := Felt252IdMemory.mem_yield_of_IdToValueLookupCall t h_t h_tv.2
      apply AirLookupTerms.not_mem_add' _ h_t_mem
      simp [h_tv.1, h_tv.2, MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX]
      apply Array.not_mem_empty
    case RangeCheck =>
      revert h_t
      apply AirLookupTerms.not_mem_add'
      simp only [AirLookupTerms.empty]
      constructor
      · apply Array.not_mem_empty
      simp [h_tv.1, h_tv.2, MEMORY_ADDR_TO_ID_REL_INDEX, RANGE_CHECK_REL_INDEX, NUM_LOOKUP_REL_MINUS_ONE]
    case VerifyInstr =>
      revert h_t
      apply AirLookupTerms.not_mem_add'
      simp [h_tv.1, h_tv.2, MEMORY_ADDR_TO_ID_REL_INDEX, VERIFY_INSTR_REL_INDEX]
      apply AirLookupTerms.not_mem_of_NoYieldTerms h_tv.2 (VerifyInstruction.NoYieldTerms_of_call _)
      apply AirLookupTerms.empty_NoYieldTerms

lemma mem_MemAddrToIdYieldLookups [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ MemAddrToIdYieldLookups inp pubMemLookups varAssigns,
      ∃ t ∈ Felt252IdMemory.AddrToIdLookupCall.2,
        ∃ v ∈ varAssigns .MemoryAddrToId,
          tv = t.eval v ∧ t.rel = MEMORY_ADDR_TO_ID_REL_INDEX ∧ t.useOrYield = .yield := by
  intro tv h_tv
  rw [MemAddrToIdYieldLookups, RelLookups_eq_RelComponentLookups _ _ _ _ _] at h_tv
  · simp only [RelComponentLookups, Array.mem_filter, ComponentLookups, Array.mem_flatMap] at h_tv
    rcases h_tv with ⟨⟨c, h_c_mem, h_tv_mem⟩, h_p⟩
    by_cases h : c = .MemoryAddrToId
    · rw [h] at h_tv_mem
      rcases mem_ComponentLookupTermsEval tv h_tv_mem with ⟨t, v, h_t_mem, h_v_mem, h_tv_eq⟩
      use t, h_t_mem, v, h_v_mem, h_tv_eq
      simp [h_tv_eq, LookupTerm.eval] at h_p
      exact h_p
    exfalso
    apply mem_addr_to_id_not_mem_ComponentLookupTermsEval _ _ tv h_p h_tv_mem
    simp [h]
  simp [MEMORY_ADDR_TO_ID_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma mem_MemAddrToIdYieldLookups' [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ MemAddrToIdYieldLookups inp pubMemLookups varAssigns,
      ∃ v ∈ varAssigns .MemoryAddrToId,
        tv = {
          rel := MEMORY_ADDR_TO_ID_REL_INDEX,
          useOrYield := .yield,
          tuple := p_tuple MEMORY_ADDR_TO_ID_REL_INDEX ![v (.stateVar 0), v (.stateVar 1)]
        } := by
  intro tv h_tv
  rcases mem_MemAddrToIdYieldLookups tv h_tv with ⟨t, h_t_mem, v, h_v_mem, h_tv_eq, h_rel, h_useOrYield⟩
  use v, h_v_mem
  cases t
  simp at h_rel h_useOrYield
  simp [h_tv_eq, LookupTerm.eval, h_rel, h_useOrYield]
  subst h_rel
  -- Needed for the proof in case we switch back to multiple partitions
  -- apply heq_of_eq
  have h_t_eq := AirLookupTerms.mem_add'_ne_rel h_t_mem
  simp [MEMORY_ADDR_TO_ID_REL_INDEX, RANGE_CHECK_REL_INDEX, NUM_LOOKUP_REL_MINUS_ONE] at h_t_eq
  have h_t_eq := AirLookupTerms.mem_add' _ h_t_eq
  simp [AirLookupTerms.empty] at h_t_eq
  replace h_t_eq := Or.resolve_left h_t_eq (Array.not_mem_empty _)
  simp [AirBuilder.empty, AirBuilder.deduce, State.add, State.empty] at h_t_eq
  simp [h_t_eq.1]
  exact List.ofFn_inj.mp rfl

lemma mem_id_to_value_not_mem_ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)]
      {c : Component}
      (h_c : c ≠ .MemoryIdToValue)
      (varAssigns : Array VarAssign) :
    ∀ tv : LookupTermVal rel_lengths,
        decide (tv.rel = MEMORY_ID_TO_VALUE_REL_INDEX ∧ tv.useOrYield = UseOrYield.yield) = true →
          tv ∉ (ComponentLookupTermsEval c varAssigns) := by
    intro tv h_tv
    by_contra h_tv_eval
    rcases mem_ComponentLookupTermsEval tv h_tv_eval with ⟨t, v, h_t, h_v, h_eq⟩
    simp [LookupTerm.eval] at h_eq
    simp [decide_eq_true_eq, h_eq] at h_tv
    cases c
    case Opcode o =>
      simp [OpcodeLookup.lookupCall_yield_term t h_t h_tv.2] at h_tv
      exact not_eq_of_beq_eq_false rfl h_tv
    case MemoryIdToValue =>
      exfalso ; apply h_c rfl
    case VerifyInstr =>
      revert h_t
      apply AirLookupTerms.not_mem_add'
      simp [h_tv.1, h_tv.2, MEMORY_ID_TO_VALUE_REL_INDEX, VERIFY_INSTR_REL_INDEX]
      apply AirLookupTerms.not_mem_of_NoYieldTerms h_tv.2 (VerifyInstruction.NoYieldTerms_of_call _)
      apply AirLookupTerms.empty_NoYieldTerms
    all_goals
      revert h_t
      repeat
        apply AirLookupTerms.not_mem_add'
        simp [h_tv.1, h_tv.2, MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, RANGE_CHECK_REL_INDEX]
      apply Array.not_mem_empty

lemma mem_MemIdToValueYieldLookups [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ MemIdToValueYieldLookups inp pubMemLookups varAssigns,
      ∃ t ∈ Felt252IdMemory.IdToValueLookupCall.2,
        ∃ v ∈ varAssigns .MemoryIdToValue,
          tv = t.eval v ∧ t.rel = MEMORY_ID_TO_VALUE_REL_INDEX ∧ t.useOrYield = .yield := by
  intro tv h_tv
  rw [MemIdToValueYieldLookups, RelLookups_eq_RelComponentLookups _ _ _ _ _] at h_tv
  · simp only [RelComponentLookups, Array.mem_filter, ComponentLookups, Array.mem_flatMap] at h_tv
    rcases h_tv with ⟨⟨c, h_c_mem, h_tv_mem⟩, h_p⟩
    by_cases h : c = .MemoryIdToValue
    · rw [h] at h_tv_mem
      rcases mem_ComponentLookupTermsEval tv h_tv_mem with ⟨t, v, h_t_mem, h_v_mem, h_tv_eq⟩
      use t, h_t_mem, v, h_v_mem, h_tv_eq
      simp [h_tv_eq, LookupTerm.eval] at h_p
      exact h_p
    exfalso
    apply mem_id_to_value_not_mem_ComponentLookupTermsEval _ _ tv h_p h_tv_mem
    simp [h]
  simp [MEMORY_ID_TO_VALUE_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma mem_MemIdToValueYieldLookups' [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ MemIdToValueYieldLookups inp pubMemLookups varAssigns,
      ∃ v ∈ varAssigns .MemoryIdToValue,
        tv = {
          rel := MEMORY_ID_TO_VALUE_REL_INDEX,
          useOrYield := .yield,
          tuple := p_tuple MEMORY_ID_TO_VALUE_REL_INDEX
                    ((Fin.append ![v (.stateVar 0)] ((fun i => (v (.stateVar (i + 1)))) : Felt252Words))
                      ∘ Fin.cast (by simp [MEMORY_ID_TO_VALUE_REL_INDEX, FELT252_N_WORDS] ; rfl))
        } := by
  intro tv h_tv
  rcases mem_MemIdToValueYieldLookups tv h_tv with ⟨t, h_t_mem, v, h_v_mem, h_tv_eq, h_rel, h_useOrYield⟩
  use v, h_v_mem
  cases t
  simp at h_rel h_useOrYield
  simp [h_tv_eq, LookupTerm.eval, h_rel, h_useOrYield]
  subst h_rel
  -- Needed for the proof in case we switch back to multiple partitions
  -- apply heq_of_eq
  replace h_t_mem := Felt252IdMemory.mem_yield_of_IdToValueLookupCall _ h_t_mem h_useOrYield
  have h_t_eq := AirLookupTerms.mem_add' _ h_t_mem
  simp [AirLookupTerms.empty] at h_t_eq
  replace h_t_eq := Or.resolve_left h_t_eq (Array.not_mem_empty _)
  simp [AirBuilder.empty, AirBuilder.deduce, State.add, State.empty, AirBuilder.deduce252] at h_t_eq
  simp [h_t_eq.1]
  exact List.ofFn_inj.mp rfl

-- Range checks on memory

lemma exists_mem_addr_range_check [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ i, (h_i_lt : i < (varAssigns Component.MemoryAddrToId).size) →
      (p_tuple RANGE_CHECK_REL_INDEX ![29, (varAssigns Component.MemoryAddrToId)[i] (VarIndex.stateVar 0)]) ∈
        RelLookupTuples inp pubMemLookups varAssigns RANGE_CHECK_REL_INDEX UseOrYield.use := by
  intro i h_i_lt
  rw [mem_RelLookupTuples_iff]
  unfold RelLookups AllLookups
  use {
    rel := RANGE_CHECK_REL_INDEX,
    useOrYield := .use,
    tuple := p_tuple RANGE_CHECK_REL_INDEX ![29, (varAssigns Component.MemoryAddrToId)[i] (VarIndex.stateVar 0)] }
  simp only [Fin.cast_refl, CompTriple.comp_eq, and_self, exists_const, and_true]
  simp only [Array.mem_filter, Array.mem_push, RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX] ; simp
  rw [ComponentLookups, Array.mem_flatMap]
  left
  use .MemoryAddrToId
  simp [Component.univ_complete .MemoryAddrToId]
  rw [ComponentLookupTermsEval, Array.mem_flatMap, ComponentLookupCall, Felt252IdMemory.AddrToIdLookupCall]
  use {
    rel := RANGE_CHECK_REL_INDEX,
    useOrYield := .use,
    tuple := p_tuple_expr RANGE_CHECK_REL_INDEX ![FeltExpr.const 29, AirBuilder.empty.deduce.2] }
  constructor
  · simp only
    exact Array.mem_push_self
  rw [Array.mem_map]
  use (varAssigns Component.MemoryAddrToId)[i], Array.getElem_mem h_i_lt
  simp [RANGE_CHECK_REL_INDEX, AirBuilder.deduce, AirBuilder.empty, State.add, State.empty, LookupTerm.eval]
  exact List.ofFn_inj.mp rfl

lemma exists_mem_value_range_check [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ i, (h_i_lt : i < (varAssigns Component.MemoryIdToValue).size) →
      ∀ (j : Fin FELT252_N_WORDS),
        p_tuple RANGE_CHECK_REL_INDEX ![9, (varAssigns Component.MemoryIdToValue)[i] (VarIndex.stateVar (j + 1))] ∈
          RelLookupTuples inp pubMemLookups varAssigns RANGE_CHECK_REL_INDEX UseOrYield.use := by
  intro i h_i_lt j
  rw [mem_RelLookupTuples_iff]
  unfold RelLookups AllLookups
  use {
    rel := RANGE_CHECK_REL_INDEX,
    useOrYield := .use,
    tuple := p_tuple RANGE_CHECK_REL_INDEX ![9, (varAssigns Component.MemoryIdToValue)[i] (VarIndex.stateVar (j + 1))] }
  simp only [Fin.cast_refl, CompTriple.comp_eq, and_self, exists_const, and_true]
  simp only [Array.mem_filter, Array.mem_push, RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX] ; simp
  rw [ComponentLookups, Array.mem_flatMap]
  left
  use .MemoryIdToValue
  simp [Component.univ_complete .MemoryIdToValue]
  rw [ComponentLookupTermsEval, Array.mem_flatMap, ComponentLookupCall]
  use {
    rel := RANGE_CHECK_REL_INDEX,
    useOrYield := .use,
    tuple := p_tuple_expr RANGE_CHECK_REL_INDEX ![FeltExpr.const 9, FeltExpr.var (VarIndex.stateVar (j + 1))] }
  constructor
  · exact Felt252IdMemory.mem_range_check_of_IdToValueLookupCall j
  rw [Array.mem_map]
  use (varAssigns Component.MemoryIdToValue)[i], Array.getElem_mem h_i_lt
  simp [RANGE_CHECK_REL_INDEX, LookupTerm.eval]
  exact List.ofFn_inj.mp rfl

/-
  The first column in the memory components is filled sequentially: 0, 1, 2, ...
  We here use a weaker assumption that no two assignments have the same value
  for the first column.
-/

def IsMemAssign (varAssigns : Array VarAssign) : Prop :=
  ∀ i j, (hi : i < varAssigns.size) → (hj : j < varAssigns.size) →
    varAssigns[i] (.stateVar 0) = varAssigns[j] (.stateVar 0) → i = j

def MemAssignFromVarAssigns (addr_assign id_assign : Array VarAssign) : Felt252IdMemoryAssign :=
  {
    addressToId :=
      fun addr => match addr_assign.find? (fun v => v (.stateVar 0) = (addr 0)) with
      | some v => some ![v (.stateVar 1)]
      | none => none
    idToValue :=
      fun id => match id_assign.find? (fun v => v (.stateVar 0) = (id 0)) with
      | some v => some fun i => (v (.stateVar (i + 1)))
      | none => none
  }

lemma memory_assign_addr_to_id_of_mem_yields_agree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      (tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k)))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId)) :
    AirLookupTerms.AddrToIdYieldsAgree
      (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
      values
      (tuples MEMORY_ADDR_TO_ID_REL_INDEX) := by
  intro y h_y_mem
  rw [yield_mem_iff_mem, h_yield_agree MEMORY_ADDR_TO_ID_REL_INDEX] at h_y_mem
  simp [mem_RelLookupTuples_iff _] at h_y_mem
  rcases h_y_mem with ⟨t, h_t_mem, h_t_useOrYield, ⟨h_rel, h_tuple⟩⟩
  rcases mem_MemAddrToIdYieldLookups' t h_t_mem with ⟨v, h_v_mem, h_t_eq⟩
  simp [Felt252IdMemoryAssign.HasId, MemAssignFromVarAssigns]
  subst h_t_eq
  simp at h_tuple
  have h_tuple_1 : y 1 = v (VarIndex.stateVar 0) := by simp [h_tuple, p_tuple_one_eq_tuple_zero]
  have h_find : Array.find? (fun v => decide (v (VarIndex.stateVar 0) = y 1)) (varAssigns Component.MemoryAddrToId) = some v := by
    simp [Array.find?_eq_some_iff_getElem, h_tuple_1]
    rw [Array.mem_iff_getElem] at h_v_mem
    rcases h_v_mem with ⟨i, h_i_lt, h_eq⟩
    use i, h_i_lt, h_eq
    intro j h_j h_v_eq
    rw [←h_eq] at h_v_eq
    apply ne_of_lt h_j
    apply h_is_mem_addr_to_id _ _ _ _ h_v_eq
  rw [h_find, h_tuple] ;
  simp [p_tuple_two_eq_tuple_one]

lemma memory_assign_id_to_value_of_mem_yields_agree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      (tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k)))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue)) :
    AirLookupTerms.IdToValueYieldsAgree
      (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
      values
      (tuples MEMORY_ID_TO_VALUE_REL_INDEX) := by
  intro y h_y_mem
  rw [yield_mem_iff_mem, h_yield_agree MEMORY_ID_TO_VALUE_REL_INDEX] at h_y_mem
  simp [mem_RelLookupTuples_iff _] at h_y_mem
  rcases h_y_mem with ⟨t, h_t_mem, h_t_useOrYield, ⟨h_rel, h_tuple⟩⟩
  rcases mem_MemIdToValueYieldLookups' t h_t_mem with ⟨v, h_v_mem, h_t_eq⟩
  simp [MemAssignFromVarAssigns]
  subst h_t_eq
  simp at h_tuple
  have h_1 : y 1 = v (VarIndex.stateVar 0) := by
    rw [h_tuple]
    apply AirLookupTerms.id_eq_MemIdToValueTuple _ (fun i => v (VarIndex.stateVar (↑i + 1)))
  have h_find : Array.find? (fun v => decide (v (VarIndex.stateVar 0) = y 1)) (varAssigns Component.MemoryIdToValue) = some v := by
    simp [Array.find?_eq_some_iff_getElem, h_1]
    rw [Array.mem_iff_getElem] at h_v_mem
    rcases h_v_mem with ⟨i, h_i_lt, h_eq⟩
    use i, h_i_lt, h_eq
    intro j h_j h_v_eq
    rw [←h_eq] at h_v_eq
    apply ne_of_lt h_j
    apply h_is_mem_id_to_value _ _ _ _ h_v_eq
  simp [h_find]
  rw [h_tuple, eq_comm]
  have h_v := AirLookupTerms.value_eq_MemIdToValueTuple (v (VarIndex.stateVar 0)) (fun i => v (VarIndex.stateVar (↑i + 1)))
  unfold AirLookupTerms.MemIdToValueRawTuple at h_v
  apply h_v

lemma exists_var_assign_of_HasId
      {varAssigns : Component → Array VarAssign}
      {addr id : Felt} :
    (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue)).HasId addr id →
      ∃ (i : Nat) (h : i < (varAssigns .MemoryAddrToId).size),
        (varAssigns .MemoryAddrToId)[i] (.stateVar 0) = addr
        ∧ (varAssigns .MemoryAddrToId)[i] (.stateVar 1) = id := by
  intro h_has
  simp only [MemAssignFromVarAssigns, Felt252IdMemoryAssign.HasId, Matrix.cons_val_fin_one] at h_has
  cases h_some : (Array.find? (fun v => decide (v (VarIndex.stateVar 0) = addr)) (varAssigns Component.MemoryAddrToId)).isSome
  case false =>
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h_some
    simp [h_some] at h_has
  case true =>
    rw [Option.isSome_iff_exists] at h_some
    rcases h_some with ⟨id', h_find⟩
    simp [h_find] at h_has
    rw [Array.find?_eq_some_iff_getElem] at h_find
    rcases h_find with ⟨h_eq_addr, i, h_i_lt, h_eq_id, h_first⟩
    use i, h_i_lt
    rw [←h_eq_id, decide_eq_true_iff] at h_eq_addr
    use h_eq_addr
    rw [h_eq_id, h_has]

lemma exists_var_assign_of_id_has_value
      {varAssigns : Component → Array VarAssign}
      {id : Felt}
      {value : Felt252Words}:
    (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue)).idToValue ![id] = some value →
      ∃ (i : Nat) (h : i < (varAssigns .MemoryIdToValue).size),
        (varAssigns .MemoryIdToValue)[i] (.stateVar 0) = id
        ∧ ∀ j : Fin FELT252_N_WORDS, (varAssigns .MemoryIdToValue)[i] (.stateVar (j + 1)) = value j := by
  intro h_has
  simp only [MemAssignFromVarAssigns, Matrix.cons_val_fin_one] at h_has
  cases h_some : (Array.find? (fun v => decide (v (VarIndex.stateVar 0) = id)) (varAssigns Component.MemoryIdToValue)).isSome
  case false =>
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h_some
    simp [h_some] at h_has
  case true =>
    rw [Option.isSome_iff_exists] at h_some
    rcases h_some with ⟨value', h_find⟩
    simp [h_find] at h_has
    rw [Array.find?_eq_some_iff_getElem] at h_find
    rcases h_find with ⟨h_eq_id, i, h_i_lt, h_eq_value, h_first⟩
    use i, h_i_lt
    rw [←h_eq_value, decide_eq_true_iff] at h_eq_id
    use h_eq_id
    intro j
    rw [h_eq_value, ←h_has]

lemma memory_assign_addr_range_checked_of_agrees [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      (tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k)))
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    AirLookupTerms.MemAddrAgreesRangeChecked
      (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
      values
      (tuples RANGE_CHECK_REL_INDEX) := by
  intro addr id
  rw [use_mem_iff_mem, h_use_agree RANGE_CHECK_REL_INDEX]
  intro h_has
  rcases exists_var_assign_of_HasId h_has with ⟨i, h_i_lt, h_eq_addr, h_eq_id⟩
  simp only [Multiset.mem_coe, Array.mem_toList_iff, ←h_eq_addr]
  apply exists_mem_addr_range_check

lemma memory_assign_value_range_checked_of_agrees [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      (tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k)))
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    AirLookupTerms.MemValueAgreesRangeChecked
      (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
      values
      (tuples RANGE_CHECK_REL_INDEX) := by
  intro id value
  simp only [use_mem_iff_mem]
  rw [h_use_agree RANGE_CHECK_REL_INDEX]
  intro h_has
  rcases exists_var_assign_of_id_has_value h_has with ⟨i, h_i_lt, h_eq_id, h_eq_value⟩
  simp only [Multiset.mem_coe, Array.mem_toList_iff, ←h_eq_value]
  apply exists_mem_value_range_check

lemma memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue)) :
      AirLookupTerms.MemYieldsAgreeAndRangeChecked
        (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
        values
        (tuples RANGE_CHECK_REL_INDEX)
        (tuples MEMORY_ADDR_TO_ID_REL_INDEX)
        (tuples MEMORY_ID_TO_VALUE_REL_INDEX) := by
  unfold AirLookupTerms.MemYieldsAgreeAndRangeChecked
  constructor
  · use memory_assign_addr_to_id_of_mem_yields_agree varAssigns tuples h_yield_agree h_is_mem_addr_to_id
    use memory_assign_id_to_value_of_mem_yields_agree varAssigns tuples h_yield_agree h_is_mem_id_to_value
  use memory_assign_addr_range_checked_of_agrees varAssigns tuples h_use_agree
  exact memory_assign_value_range_checked_of_agrees varAssigns tuples h_use_agree

/- Memory assignment with the required agreement properties exists. -/

lemma memory_assign_of_mem_use_and_yields_agree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue)) :
    ∃ memoryAssign : Felt252IdMemoryAssign,
      AirLookupTerms.MemYieldsAgreeAndRangeChecked
        memoryAssign values
        (tuples RANGE_CHECK_REL_INDEX)
        (tuples MEMORY_ADDR_TO_ID_REL_INDEX)
        (tuples MEMORY_ID_TO_VALUE_REL_INDEX) := by
  use MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue)
  apply memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees varAssigns h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value

/-
  Range Check Component
-/

def RangeCheckYieldLookups [Fact (Nat.Prime Stwo.P)]
    (inp : InputData)
    (pubMemLookups : PublicMem.Lookups)
    (varAssigns : Component → Array VarAssign) :=
  RelLookups inp pubMemLookups varAssigns RANGE_CHECK_REL_INDEX .yield

lemma mem_range_check_not_mem_ComponentLookupTermsEval [Fact (Nat.Prime Stwo.P)]
      {c : Component}
      (h_c : c ≠ .RangeCheck)
      (varAssigns : Array VarAssign) :
    ∀ tv : LookupTermVal rel_lengths,
        decide (tv.rel = RANGE_CHECK_REL_INDEX ∧ tv.useOrYield = UseOrYield.yield) = true →
          tv ∉ (ComponentLookupTermsEval c varAssigns) := by
    intro tv h_tv
    by_contra h_tv_eval
    rcases mem_ComponentLookupTermsEval tv h_tv_eval with ⟨t, v, h_t, h_v, h_eq⟩
    simp [LookupTerm.eval] at h_eq
    simp [decide_eq_true_eq, h_eq] at h_tv
    cases c
    case RangeCheck =>
      exfalso ; apply h_c rfl
    case Opcode o =>
      simp [OpcodeLookup.lookupCall_yield_term t h_t h_tv.2] at h_tv
      exact not_eq_of_beq_eq_false rfl h_tv
    case VerifyInstr =>
      revert h_t
      apply AirLookupTerms.not_mem_add'
      simp [h_tv.1, h_tv.2, RANGE_CHECK_REL_INDEX, VERIFY_INSTR_REL_INDEX]
      apply AirLookupTerms.not_mem_of_NoYieldTerms h_tv.2 (VerifyInstruction.NoYieldTerms_of_call _)
      apply AirLookupTerms.empty_NoYieldTerms
    all_goals
      revert h_t
      repeat
        apply AirLookupTerms.not_mem_add'
        simp [h_tv.1, h_tv.2, MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, RANGE_CHECK_REL_INDEX, NUM_LOOKUP_REL_MINUS_ONE]
      simp only [AirLookupTerms.empty]
      apply Array.not_mem_empty

lemma mem_RangeCheckYieldLookups [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ RangeCheckYieldLookups inp pubMemLookups varAssigns,
      ∃ t ∈ RangeCheckTable.LookupCall.2,
        ∃ v ∈ varAssigns .RangeCheck,
          tv = t.eval v ∧ t.rel = RANGE_CHECK_REL_INDEX ∧ t.useOrYield = .yield := by
  intro tv h_tv
  rw [RangeCheckYieldLookups, RelLookups_eq_RelComponentLookups _ _ _ _ _] at h_tv
  · simp only [RelComponentLookups, Array.mem_filter, ComponentLookups, Array.mem_flatMap] at h_tv
    rcases h_tv with ⟨⟨c, h_c_mem, h_tv_mem⟩, h_p⟩
    by_cases h : c = .RangeCheck
    · rw [h] at h_tv_mem
      rcases mem_ComponentLookupTermsEval tv h_tv_mem with ⟨t, v, h_t_mem, h_v_mem, h_tv_eq⟩
      use t, h_t_mem, v, h_v_mem, h_tv_eq
      simp [h_tv_eq, LookupTerm.eval] at h_p
      exact h_p
    exfalso
    apply mem_range_check_not_mem_ComponentLookupTermsEval _ _ tv h_p h_tv_mem
    simp [h]
  simp [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma mem_RangeCheckYieldLookups' [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign} :
    ∀ tv ∈ RangeCheckYieldLookups inp pubMemLookups varAssigns,
      ∃ v ∈ varAssigns .RangeCheck,
        tv = {
          rel := RANGE_CHECK_REL_INDEX,
          useOrYield := .yield,
          tuple := p_tuple RANGE_CHECK_REL_INDEX ![v (.stateVar 0), v (.stateVar 1)] } := by
  intro tv h_tv
  rcases mem_RangeCheckYieldLookups tv h_tv with ⟨t, h_t_mem, v, h_v_mem, h_tv_eq, h_rel, h_useOrYield⟩
  use v, h_v_mem
  cases t
  simp at h_rel h_useOrYield
  simp [h_tv_eq, LookupTerm.eval, h_rel, h_useOrYield]
  subst h_rel
  -- Needed for the proof in case we switch back to multiple partitions
  -- apply heq_of_eq
  have h_t_eq := AirLookupTerms.mem_add' _ h_t_mem
  simp [AirLookupTerms.empty] at h_t_eq
  replace h_t_eq := Or.resolve_left h_t_eq (Array.not_mem_empty _)
  simp [AirBuilder.empty, AirBuilder.deduce, State.add, State.empty] at h_t_eq
  simp [h_t_eq.1]
  exact List.ofFn_inj.mp rfl

def IsRangeCheckAssign (varAssigns : Array VarAssign) : Prop :=
  ∀ i, (hi : i < varAssigns.size) →
    IsRangeChecked (varAssigns[i] (.stateVar 0)).val (varAssigns[i] (.stateVar 1))

lemma range_checked_yields_of_range_check_assign [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck)) :
    RangeCheckYields _ (tuples RANGE_CHECK_REL_INDEX) := by
  intro y h_y_mem
  simp only [yield_mem_iff_mem] at h_y_mem
  rw [h_yield_agree RANGE_CHECK_REL_INDEX] at h_y_mem
  simp [mem_RelLookupTuples_iff _] at h_y_mem
  rcases h_y_mem with ⟨t, h_t_mem, h_t_useOrYield, ⟨h_rel, h_tuple⟩⟩
  rcases mem_RangeCheckYieldLookups' t h_t_mem with ⟨v, h_v_mem, h_t_eq⟩
  subst h_t_eq
  simp at h_tuple
  rw [h_tuple, p_tuple_one_eq_tuple_zero, p_tuple_two_eq_tuple_one]
  simp
  rw [Array.mem_iff_getElem] at h_v_mem
  rcases h_v_mem with ⟨i, h_i_lt, h_eq⟩
  simp only [←h_eq]
  exact h_rc i h_i_lt

/-
  Public Memory
-/

lemma mem_memory_assign_of_pub_mem [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue)) :
    let memAssign := MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue)
    ∀ addr252 value252,
      inp.mStar addr252 = some value252 →
        ∃ (addr id : Felt) (value : Felt252Words),
          addr.toFelt252 = addr252 ∧
          value.eval = value252 ∧
          memAssign.HasId addr id ∧ memAssign.idToValue ![id] = some value := by
  intro memAssign addr252 value252 h_mStar
  rcases pub_mem_of_RelLookupsAgree h_use_agree h_pubMem addr252 value252 h_mStar with
    ⟨addr, id, value, h_addr_eq, h_value_eq, h_addr_mem, h_id_mem⟩
  use addr, id, value, h_addr_eq, h_value_eq
  rcases mem_yield_of_mem_use h_satisfied MEMORY_ADDR_TO_ID_REL_INDEX memory_addr_not_chain_rel _ h_addr_mem with
    ⟨addr_t, h_addr_t_mem, h_addr_t_eq⟩
  rw [←h_addr_t_eq] at h_addr_t_mem
  have h_id := memory_assign_addr_to_id_of_mem_yields_agree varAssigns h_satisfied.tuples h_yield_agree h_is_mem_addr_to_id _ h_addr_t_mem
  simp [p_tuple_one_eq_tuple_zero, p_tuple_two_eq_tuple_one] at h_id
  use h_id
  rcases mem_yield_of_mem_use h_satisfied MEMORY_ID_TO_VALUE_REL_INDEX memory_id_not_chain_rel _ h_id_mem with
    ⟨id_t, h_id_t_mem, h_id_t_eq⟩
  rw [←h_id_t_eq] at h_id_t_mem
  have h_value := memory_assign_id_to_value_of_mem_yields_agree varAssigns h_satisfied.tuples h_yield_agree h_is_mem_id_to_value _ h_id_t_mem
  have h_1 := AirLookupTerms.id_eq_MemIdToValueTuple id value
  simp [AirLookupTerms.MemIdToValueRawTuple] at h_1
  have h_v := AirLookupTerms.value_eq_MemIdToValueTuple id value
  simp [AirLookupTerms.MemIdToValueRawTuple] at h_v
  simp [h_1, h_v] at h_value
  exact h_value

lemma mem_extends_pub_mem [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {mem : Felt252 → Felt252}
      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue))
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck)) :
    let memAssign := MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue)
    memAssign.Agrees mem → Option.FnExtends mem inp.mStar := by
  intro memAssign h_mem_agrees addr252
  unfold Option.Agrees
  by_cases h : (inp.mStar addr252).isSome
  · rcases Option.isSome_iff_exists.mp h with ⟨value252, h_value252⟩
    simp only [h_value252]
    rcases mem_memory_assign_of_pub_mem
            h_pubMem h_satisfied h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value
            addr252 value252 h_value252
      with ⟨addr, id, value, h_addr_eq, h_value_eq, h_has, h_value⟩
    rw [←h_value_eq, ←h_addr_eq]
    have h_rc_yield := range_checked_yields_of_range_check_assign varAssigns h_yield_agree h_rc
    have h_mem_assign := memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees
                          varAssigns h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value
    have h_is_mem_rc := AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked memAssign h_satisfied h_rc_yield h_mem_assign
    rcases Felt252IdMemoryAssign.IsRangeChecked_of_HasValue h_is_mem_rc ⟨id, h_has, h_value⟩ with ⟨value_n, h_value_n_rc⟩
    rw [h_mem_agrees.2 addr value value_n ⟨id, h_has, h_value⟩ h_value_n_rc]
    apply Felt252Nats.eval_Felt252Words_eq h_value_n_rc
  rw [Option.not_isSome_iff_eq_none] at h
  simp [h]

/-
  Relation Encoded in Tuples
-/

lemma components_RelInRelTuples [Fact (Nat.Prime Stwo.P)] :
    ∀ c, AirLookupTerms.RelInRelTuples (ComponentLookupCall c).2 := by
  intro c
  cases c
  all_goals
    simp only [ComponentLookupCall]
    repeat
      apply AirLookupTerms.add'_RelInRelTuple.mpr
    try apply AirLookupTerms.empty_RelInRelTuple
  -- Opcodes
  apply OpcodeLookup.opcodes_RelInRelTuples

lemma rel_in_RelLookupTuples [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {useOrYield : UseOrYield} :
    ∀ tuple ∈ RelLookupTuples inp pubMemLookups varAssigns rel useOrYield, tuple 0 = rel := by
  intro tuple h_tuple_mem
  rcases (mem_RelLookupTuples_iff tuple).mp h_tuple_mem with ⟨tv, h_t_mem, h_rel, h_t_useOrYield, h_t_eq⟩
  simp only [RelLookups, Array.mem_filter, AllLookups, Array.mem_push] at h_t_mem
  simp [h_t_eq, ←h_rel]
  cases h_t_mem.1
  case inl h =>
    cases h
    case inl h =>
      rw [Array.append_eq_append, Array.mem_append] at h
      cases h
      case inl h =>
        simp only [ComponentLookups, ComponentLookupTermsEval, Array.mem_flatMap, Array.mem_map] at h
        rcases h with ⟨c, h_c_mem, t, h_t_mem, v, h_v_mem, h_eq⟩
        rcases Array.mem_iff_getElem.mp h_t_mem with ⟨i, h_i, h_i_eq⟩
        have h_rel_in_tuple := components_RelInRelTuples c i h_i
        rw [h_i_eq] at h_rel_in_tuple
        rw [←h_eq]
        simp [LookupTerm.eval, h_rel_in_tuple]
      case inr h =>
        exact pubMemLookups.rel_in_lookup tv h
    case inr h =>
      subst h
      simp [CasmStateValTuple]
      apply p_tuple_zero
  case inr h =>
    subst h
    simp [CasmStateValTuple]
    apply p_tuple_zero

lemma partition_tuple_mem_RelLookupTuples [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      (h_use_agree : ∀ k, RelUseLookupsAgree inp pubMemLookups varAssigns k (tuples k))
      (h_yield_agree : ∀ k, RelYieldLookupsAgree inp pubMemLookups varAssigns k (tuples k)) :
    ∀ k, ∀ i ∈ (tuples k).use_i ∪ (tuples k).yield_i, (partitions (rel_partition k)).tuples i ∈
      (RelLookupTuples inp pubMemLookups varAssigns k .use) ++ (RelLookupTuples inp pubMemLookups varAssigns k .yield) := by
  intro k i h_i_mem
  rw [Array.mem_append]
  rw [Finset.mem_union] at h_i_mem
  cases h_i_mem
  case inl h =>
    left
    rw [←Array.mem_toList_iff, ←Multiset.mem_coe, ←h_use_agree k]
    simp only [Multiset.mem_map, Finset.mem_val]
    use i
  case' inr h =>
    right
    rw [←Array.mem_toList_iff, ←Multiset.mem_coe, ←h_yield_agree k]
    simp only [Multiset.mem_map, Finset.mem_val]
    use i

lemma partition_tuples_disjoint_of_rel_in_rel [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (covering: RelationsCoverPartitions tuples)
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    ∀ k, ∀ i ∈ (tuples k).use_i ∪ (tuples k).yield_i,
      ∀ j ∉ (tuples k).use_i ∪ (tuples k).yield_i, (partitions (rel_partition k)).tuples i ≠ (partitions (rel_partition k)).tuples j := by
  intro k i h_i_mem j h_j_nin
  rcases covering (rel_partition k) j with ⟨k_j, h_k_rel, h_k_j_mem⟩
  simp only [Fin.cast_eq_self] at h_k_j_mem
  have h_k_j_ne : ¬(k_j = k) := by
    by_contra h_k ; rw [h_k] at h_k_j_mem ; exact h_j_nin h_k_j_mem
  have h_k_mem_rel := partition_tuple_mem_RelLookupTuples h_use_agree h_yield_agree k i h_i_mem
  have h_k_j_mem_rel := partition_tuple_mem_RelLookupTuples h_use_agree h_yield_agree k_j j h_k_j_mem
  rw [Array.mem_append] at h_k_mem_rel h_k_j_mem_rel
  have h_0_eq_k : (partitions (rel_partition k)).tuples i 0 = k := by
    cases h_k_mem_rel with | inl h | inr h
    all_goals apply rel_in_RelLookupTuples _ h
  have h_0_eq_k_j : (partitions (rel_partition k)).tuples j 0 = k_j := by
    cases h_k_j_mem_rel with | inl h | inr h
    all_goals apply rel_in_RelLookupTuples _ h
  rw [ne_eq, funext_iff, Classical.not_forall]
  use 0
  simp [h_0_eq_k, h_0_eq_k_j]
  intro h_eq
  apply h_k_j_ne
  rw [←Fin.val_eq_val]
  apply Nat.cast_inj_of_lt_char _ _ h_eq.symm
  all_goals
    apply lt_trans (Fin.isLt _)
    simp [NUM_LOOKUP_REL_MINUS_ONE, Felt, ZMod.ringChar_zmod_n, Stwo.P]
