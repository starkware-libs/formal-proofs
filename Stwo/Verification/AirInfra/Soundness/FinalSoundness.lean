import Verification.AirInfra.Soundness.OpcodeLookupCall
import Verification.AirInfra.Soundness.ComponentLookupCall

noncomputable section

/-
  # Cycles in chain relations
-/

-- Auxiliary definitions and lemma on directed graphs.

def CountFirstSecondEq { α : Type _} [DecidableEq α] (edges : Multiset (α × α)) :=
  ∀ a, Multiset.count a (Multiset.map (fun x => x.fst) edges) = Multiset.count a (Multiset.map (fun x => x.snd) edges)

def CycleThrough { α : Type _} [DecidableEq α] (edges : Multiset (α × α)) (e : α × α) :=
  e.fst = e.snd
  ∨ ∃ n < edges.card - 1, ∃ path : Fin (n + 1) → (α × α),
    (∀ i, path i ∈ edges.erase e)
    ∧ (path 0).fst = e.snd
    ∧ (path (Fin.last n)).snd = e.fst
    ∧ ∀ i : Fin n, (path i.castSucc).snd = (path i.succ).fst

lemma cycle_of_equal_count_nodes { α : Type _} [DecidableEq α] (edges : Multiset (α × α)) (h : CountFirstSecondEq edges) :
    ∀ e ∈ edges, CycleThrough edges e := by
  suffices h_m : ∀ m : Nat, ∀ (edges : Multiset (α × α)), edges.card < m → CountFirstSecondEq edges → ∀ e ∈ edges, CycleThrough edges e by
    exact h_m edges.card.succ edges (by simp) h
  intro m ; induction m
  case zero => intro _ h_c ; exfalso ; exact Nat.not_lt_zero _ h_c
  case succ m ih =>
    intro edges h_m h_count e h_e_mem
    by_cases h_eq : e.fst = e.snd
    · left ; exact h_eq
    right
    have h_fst : ∃ e₀ ∈ edges, e₀.fst = e.snd := by
      apply (Multiset.mem_map).mp
      apply Multiset.count_ne_zero.mp
      rw [h_count e.2]
      apply Multiset.count_ne_zero.mpr
      apply (Multiset.mem_map).mpr
      use e
    rcases h_fst with ⟨e₀, h_e₀_mem, h_e₀⟩
    have h_e₀_ne : e₀ ≠ e := by
      rw [←h_e₀] at h_eq ; rw [ne_eq, Prod.eq_iff_fst_eq_snd_eq, not_and_or, eq_comm] ; left ; exact h_eq
    replace h_e₀_mem := (Multiset.mem_erase_of_ne h_e₀_ne).mpr h_e₀_mem
    have h_card_erase := Multiset.card_erase_add_one h_e_mem
    rw [←Multiset.card_erase_add_one h_e₀_mem] at h_card_erase
    let edges₀ := Multiset.cons (e.fst, e₀.snd) ((edges.erase e).erase e₀)
    have h_card_lt : edges₀.card < m := by
      simp [←h_card_erase] at h_m
      apply lt_of_le_of_lt _ h_m
      rw [Multiset.card_cons]
    have h_count₀ : CountFirstSecondEq edges₀ := by
      intro a
      unfold edges₀ ; simp only [Multiset.map_cons]
      simp only [Multiset.map_erase_of_mem _ _ h_e₀_mem]
      simp only [Multiset.cons_erase (Multiset.mem_map_of_mem (fun x => x.2) h_e₀_mem)]
      simp only [Multiset.map_erase_of_mem _ _ h_e_mem]
      rw [Multiset.erase_comm, h_e₀]
      rw [Multiset.cons_erase _]
      by_cases h_a : a = e.2
      · simp only [h_a, Multiset.count_erase_self, h_count e.2]
      simp only [Multiset.count_erase_of_ne h_a, h_count a]
      simp only [Multiset.mem_erase_of_ne h_eq, Multiset.mem_map_of_mem (fun x => x.1) h_e_mem]
    replace ih := ih edges₀ h_card_lt h_count₀ (e.fst, e₀.snd) (Multiset.mem_cons_self _ _)
    by_cases h0 : e.fst = e₀.snd
    · use 0
      constructor
      · apply Nat.zero_lt_sub_of_lt
        apply lt_of_le_of_lt _ (Multiset.card_erase_lt_of_mem h_e_mem)
        rw [Nat.succ_le, Multiset.card_pos_iff_exists_mem]
        exact ⟨e₀, h_e₀_mem⟩
      use ![e₀]
      simp [Fin.fin_one_eq_zero, h_e₀_mem]
      use h_e₀ ; exact h0.symm
    rcases or_iff_not_imp_left.mp ih h0 with ⟨n, h_n_lt, path, h_path_mem, h_start, h_end, h_path⟩
    use (n+1)
    constructor
    · simp [←h_card_erase]
      simp [edges₀, Multiset.card_cons] at h_n_lt
      exact h_n_lt
    use Fin.cons e₀ path
    constructor
    · intro i
      by_cases h_i : i = 0
      · simp [h_i, Fin.cons_zero, h_e₀_mem]
      rw [Multiset.erase_cons_head] at h_path_mem
      rcases Fin.eq_succ_of_ne_zero h_i with ⟨j, h_j⟩
      rw [h_j, Fin.cons_succ]
      exact Multiset.mem_of_mem_erase (h_path_mem j)
    simp [h_e₀, h_end]
    intro i
    by_cases h_i : i = 0
    · simp [h_i, h_start]
    rcases Fin.eq_succ_of_ne_zero h_i with ⟨j, h_j⟩
    simp only [h_j, ←Fin.succ_castSucc, Fin.cons_succ, h_path j]

lemma set_count_lift [Fact (Nat.Prime Stwo.P)] {m n : Nat}
      {tuples : Fin m → Fin (n + 1) → Felt}
      (s : Finset (Fin m)) :
    ∀ t, set_count tuples s t = set_count ((liftLF (n := n + 1)) ∘ tuples) s ((liftLF (n := n + 1)) t) := by
  intro t ; unfold set_count
  rw [←Multiset.map_map, Eq.comm]
  convert Multiset.count_map_eq_count' liftLF (Multiset.map tuples s.val) _ t
  unfold liftLF
  intro x1 x2 h
  apply funext
  intro i
  apply (FaithfulSMul.algebraMap_injective (R := Felt) (A := LookupF))
  exact congrFun h i

lemma equal_count_tuples_chain_rel_of_multiplicity_one [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {values : LookupValues t n_s n_p}
      (h_constraints : LookupConstraints values)
      {p : Fin (n_p + 1)} -- partition number
      {k : Fin (n_r + 1)} -- relation number
      {chain_rel : Finset (Fin (n_r + 1))}
      (h_k : k ∈ chain_rel)
      {partition: LookupPartition values p (tl p)}
      (h_tuples : RelationTuples partition)
      (h_yield_lt : h_tuples.yield_i.card < ringChar Felt)
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet k chain_rel h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1) :
    ∀ t, set_count partition.tuples h_tuples.use_i t = set_count partition.tuples h_tuples.yield_i t := by
  rw [NotInBadSet, if_pos h_k] at h_bad
  have h_use_lt : h_tuples.use_i.card < ringChar LookupF := by simp [LookupF_ringChar_eq, h_tuples.h_use_lt]
  replace h_yield_lt : h_tuples.yield_i.card < ringChar LookupF := by simp [LookupF_ringChar_eq, h_yield_lt]
  have h_lift_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i,
        ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, liftLF (partition.tuples i) ≠ liftLF (partition.tuples j) := by
    intro i h_i j h_j
    exact liftLF_ne_of_ne _ _ (h_disjoint i h_i j h_j)
  intro t
  simp only [set_count_lift]
  apply equal_count_tuples_of_multiplicity_one
    h_constraints.h_z h_constraints.h_cumulativeC h_constraints.h_cyclic
    h_tuples.use_i h_tuples.yield_i h_use_lt h_yield_lt h_lift_disjoint
    partition.h_surOn h_tuples.h_use_mult_one h_inj h_y partition.h_combine_eq h_bad

open OpcodeLookup

lemma count_yield_indxs_eq_count_use_indxs [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {inp : InputData}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {p : Fin (NUM_PARTITIONS + 1)}
      {partition : LookupPartition values p (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      {varAssigns : Opcode → Array VarAssign}
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns) :
    h_tuples.yield_i.card = h_tuples.use_i.card := by
  have h_use_card := congr_arg (fun x => x.card) h_agree.1
  have h_yield_card := congr_arg (fun x => x.card) h_agree.2
  simp only [Multiset.coe_card, Array.length_toList, Multiset.card_map, Finset.card_val] at h_use_card h_yield_card
  rw [←h_use_card, ←h_yield_card]
  unfold OutStateTuples InStateTuples
  simp

-- Assuming the state tuples are equal (as a multiset) to the lookup tuples, multiplicity 1 implies
-- equal counts for the state tuples.

lemma equal_count_state_tuples_of_multiplicity_one [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      (h_constraints : LookupConstraints values)
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet OPCODE_TRACE_REL_INDEX chain_rels h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1)
      (inp : InputData)
      (varAssigns : Opcode → Array VarAssign)
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns):
    ∀ t, (InStateTuples inp varAssigns).count t = (OutStateTuples inp varAssigns).count t := by
  intro t
  simp only [←Array.count_toList, ←Multiset.coe_count]
  rw [h_agree.1, h_agree.2]
  have h_yield_lt : h_tuples.yield_i.card < ringChar Felt := by
    rw [count_yield_indxs_eq_count_use_indxs h_agree]
    exact h_tuples.h_use_lt
  have h_count := equal_count_tuples_chain_rel_of_multiplicity_one
    h_constraints opcode_trace_is_chain_rel h_tuples h_yield_lt h_disjoint h_bad h_inj h_y t
  unfold set_count at h_count
  convert h_count

lemma equal_count_states_of_multiplicity_one [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      (h_constraints : LookupConstraints values)
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet OPCODE_TRACE_REL_INDEX chain_rels h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1)
      (inp : InputData)
      (varAssigns : Opcode → Array VarAssign)
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns):
    ∀ a, List.count a (List.map (fun x => x.fst) (StatePairTuples inp varAssigns).toList) =
      List.count a (List.map (fun x => x.snd) (StatePairTuples inp varAssigns).toList) := by
  intro t
  simp only [←Array.toList_map]
  simp only [Array.count_toList]
  apply equal_count_state_tuples_of_multiplicity_one
    h_constraints h_disjoint h_bad h_inj h_y inp varAssigns h_agree

lemma cycle_through_state_pairs [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      (h_constraints : LookupConstraints values)
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet OPCODE_TRACE_REL_INDEX chain_rels h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1)
      (inp : InputData)
      (varAssigns : Opcode → Array VarAssign)
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns):
    CycleThrough
      (StatePairTuples inp varAssigns).toList
      (CasmStateValTuple (finalState inp), CasmStateValTuple (initialState inp))
     := by
  apply cycle_of_equal_count_nodes (StatePairTuples inp varAssigns).toList _
    (CasmStateValTuple (finalState inp), CasmStateValTuple (initialState inp))
  · rw [Multiset.mem_coe, Array.mem_toList_iff]
    simp [StatePairTuples]
  unfold CountFirstSecondEq
  intro a
  simp only [Multiset.map_coe, Multiset.coe_count]
  apply equal_count_states_of_multiplicity_one
    h_constraints h_disjoint h_bad h_inj h_y inp varAssigns h_agree

lemma tuple_pair_mem [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {varAssigns : Opcode → Array VarAssign}
      (x : (Fin (TUPLE_SIZE + 1) → Felt) × (Fin (TUPLE_SIZE + 1) → Felt)) :
    x ∈ Multiset.erase (↑(StatePairTuples inp varAssigns).toList)
        (CasmStateValTuple (finalState inp), CasmStateValTuple (initialState inp)) ↔
    x ∈ (Array.map (fun pa => (CasmStateValTuple pa.1, CasmStateValTuple pa.2)) (OpcodeStatePairVals varAssigns)) := by
  simp only [StatePairTuples, Array.toList_push, ←Multiset.coe_add]
  rw [Multiset.erase_add_right_pos]
  · rw [Multiset.coe_erase]
    simp only [List.erase_cons]
    simp only [BEq.rfl, ↓reduceIte, Multiset.coe_nil, Multiset.add_zero, Multiset.mem_coe, Array.mem_toList_iff]
  simp

lemma opcode_path_of_tuple_path [Fact (Nat.Prime Stwo.P)]
      {n : Nat}
      {varAssigns : Opcode → Array VarAssign}
      {tpath : Fin (n + 1) → (Fin (TUPLE_SIZE + 1) → Felt) × (Fin (TUPLE_SIZE + 1) → Felt)}
      (h_tpath : ∀ (i : Fin (n + 1)),
        tpath i ∈ Array.map (fun pa => (CasmStateValTuple pa.1, CasmStateValTuple pa.2)) (OpcodeStatePairVals varAssigns)) :
    ∃ spath : Fin (n + 1) → (Opcode × VarAssign),
      ∀ (i : Fin (n + 1)),
        (spath i).2 ∈ varAssigns (spath i).1 ∧
        tpath i = (CasmStateValTuple (OpcodeInStateVal (spath i)), CasmStateValTuple (OpcodeOutStateVal (spath i))) := by
  suffices h : ∀ (i : Fin (n + 1)), ∃ (pa : Opcode × VarAssign),
                  pa.2 ∈ varAssigns pa.1 ∧
                  tpath i = (CasmStateValTuple (OpcodeInStateVal pa), CasmStateValTuple (OpcodeOutStateVal pa)) by
    use fun i => Classical.choose (h i)
    intro i
    apply Classical.choose_spec (h i)
  intro i
  simp only [Array.mem_map] at h_tpath
  rcases h_tpath i with ⟨a, h_a_mem, h_a_eq⟩
  rw [OpcodeStatePairVals, Array.mem_flatMap] at h_a_mem
  rcases h_a_mem with ⟨opcode, h_opcode_mem, h_a_mem'⟩
  rw [Array.mem_map] at h_a_mem'
  rcases h_a_mem' with ⟨v, h_v_mem, h_v_eq⟩
  use (opcode, v), h_v_mem
  rw [←h_a_eq, ←h_v_eq]

lemma exec_path [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      (h_constraints : LookupConstraints values)
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet OPCODE_TRACE_REL_INDEX chain_rels h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1)
      (inp : InputData)
      (varAssigns : Opcode → Array VarAssign)
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns) :
    initialState inp = finalState inp ∨
    ∃ n : Nat, n < (OpcodeStatePairVals varAssigns).size
      ∧ ∃ path : Fin (n + 1) → (Opcode × VarAssign),
        (∀ i, (path i).2 ∈ varAssigns (path i).1)
        ∧ OpcodeInStateVal (path 0) = initialState inp
        ∧ OpcodeOutStateVal (path (Fin.last n)) = finalState inp
        ∧ ∀ i : Fin n, OpcodeOutStateVal (path i.castSucc)  = OpcodeInStateVal (path i.succ) := by
  cases cycle_through_state_pairs h_constraints h_disjoint h_bad h_inj h_y inp varAssigns h_agree
  · case inl h =>
      left
      apply CasmStateValTuple_inj
      simp at h
      exact h.symm
  case inr h =>
    right
    rcases h with ⟨n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ⟩
    use n
    constructor
    · apply lt_of_lt_of_le h_n_lt
      simp [StatePairTuples]
    simp only [tuple_pair_mem] at h_path_mem
    rcases opcode_path_of_tuple_path h_path_mem with ⟨spath, h_spath⟩
    use spath
    rw [forall_and] at h_spath
    use h_spath.1
    simp [h_spath.2] at h_path_start
    use CasmStateValTuple_inj h_path_start
    simp [h_spath.2] at h_path_end
    use CasmStateValTuple_inj h_path_end
    simp [h_spath.2] at h_path_succ
    intro i
    exact CasmStateValTuple_inj (h_path_succ i)

lemma exec_step_sound [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : ℕ}
      {o : Opcode}
      {v : VarAssign}
      -- memory
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      -- Lookups
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      -- opcode constraints
      (h_opcode_satisfied : (OpcodeAirFns o).1.SatisfiedBy v)
      -- Terms agree
      (h_lookup_terms_agree : (OpcodeAirFns o).2.1.UseAgree v h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      -- other relations
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      (num_steps : Nat)
      (h_num_steps : num_steps < 2 ^ 29) :
      (OpcodeInStateVal (o, v)).strongly_bounded₀ num_steps →
        (OpcodeOutStateVal (o, v)).strongly_bounded (num_steps + 1)
          ∧ NextState mem (OpcodeInStateVal (o, v)).toRegisterStateFelt252 (OpcodeOutStateVal (o, v)).toRegisterStateFelt252 := by
  have h_agree1 := AirLookupTerms.UseAgree_add.mp h_lookup_terms_agree
  rcases AirLookupTerms.UseAgree_add.mp h_agree1.2 with ⟨_, h_agree⟩
  simp [OpcodeAirFns, OpcodeLookupCall, OpcodeCall] at h_opcode_satisfied
  revert h_opcode_satisfied h_agree
  cases o
  case Generic =>
    intro h_sat h_agree h_bound
    apply GenericOpcode.sound_generic v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallRel =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_rel v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallAbsBaseFP =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_abs_base_fp v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallAbsBaseAP =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_abs_base_ap v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Ret =>
    intro h_sat h_agree h_bound
    apply RetOpcode.sound_ret v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEq =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEqImm =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq_imm v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEqDoubleDeref =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq_double_deref v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpImm =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_imm v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpDoubleDeref =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_double_deref v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpRel =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_rel v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpAbs =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_abs v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JnzNotTaken =>
    intro h_sat h_agree h_bound
    apply JnzOpcode.JnzNotTakenOpcode.sound_jnz_not_taken v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JnzTaken =>
    intro h_sat h_agree h_bound
    apply JnzOpcode.JnzTakenOpcode.sound_jnz_taken v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AddAp =>
    intro h_sat h_agree h_bound
    apply AddApOpcode.sound_add_ap v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AddSmall =>
    intro h_sat h_agree h_bound
    apply AddOpcode.AddSmallOpcode.sound_add_small v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Add252 =>
    intro h_sat h_agree h_bound
    apply AddOpcode.Add252Opcode.sound_add_252 v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case MulSmall =>
    intro h_sat h_agree h_bound
    apply MulOpcode.MulSmallOpcode.sound_mul_small v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Mul252 =>
    intro h_sat h_agree h_bound
    apply MulOpcode.Mul252Opcode.sound_mul_252 v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree

lemma exec_sound [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : ℕ}

      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}

      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups)

      -- Lookups are satisfied
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)

      -- Lookups agree with the assignments to the lookup terms
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      -- Memory assignments are functions.
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue))
      -- Range check rows are range checked.
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck))
      -- The constraints of the components are satisfied.
      (h_components: ComponentsSatisfied varAssigns)

      -- Number of steps
      (h_num_steps :  (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size ≤ 2^29)
      (h_state_bound : (initialState inp).strongly_bounded₀ 0) :

    ∃ memAssign : Felt252IdMemoryAssign,
      ∀ mem : Felt252 → Felt252,
        memAssign.Agrees mem →
          Option.FnExtends mem inp.mStar ∧
          (initialState inp = finalState inp ∨
              ∃ n : Nat, n < (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size
              ∧ ∃ exec : Fin (n + 1) → (Opcode × VarAssign),
                (∀ i, (exec i).2 ∈ varAssigns (.Opcode (exec i).1))
                ∧ OpcodeInStateVal (exec 0) = initialState inp
                ∧ OpcodeOutStateVal (exec (Fin.last n)) = finalState inp
                ∧ (∀ i : Fin n, OpcodeOutStateVal (exec i.castSucc)  = OpcodeInStateVal (exec i.succ))
                ∧ ∀ i : Fin (n + 1),
                  (OpcodeOutStateVal (exec i)).strongly_bounded (i.val + 1) ∧
                  NextState mem (OpcodeInStateVal (exec i)).toRegisterStateFelt252 (OpcodeOutStateVal (exec i)).toRegisterStateFelt252) := by
  have h_verify_instr := VerifyInstrYieldAgrees_of_agree_and_satisfy
    varAssigns h_components h_use_agree (h_yield_agree VERIFY_INSTR_REL_INDEX)
  have h_opcodes_satisfied : ∀ o, ∀ v ∈ varAssigns (.Opcode o), (OpcodeAirFns o).1.SatisfiedBy v := by
    intro o v ; exact h_components (.Opcode o) v
  have h_lookup_terms_agree :
      ∀ o, ∀ v ∈ varAssigns (.Opcode o), (OpcodeAirFns o).2.1.UseAgree v h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
    intro o v
    exact UseAgree_of_RelLookupsAgree h_use_agree (.Opcode o) v
  have h_opcode_agree : OpcodeStatesAgree inp (h_satisfied.tuples OPCODE_TRACE_REL_INDEX) (OpcodeVarAssigns varAssigns) := by
    exact OpcodeStatesAgree_of_lookups_agree
      (h_satisfied.tuples OPCODE_TRACE_REL_INDEX)
      (h_use_agree OPCODE_TRACE_REL_INDEX)
      (h_yield_agree OPCODE_TRACE_REL_INDEX)
  have h_mem_assign := memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees
                        varAssigns h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value
  have h_rc_yield := range_checked_yields_of_range_check_assign varAssigns h_yield_agree h_rc
  have h_disjoint := partition_tuples_disjoint_of_rel_in_rel (h_satisfied.covering) h_use_agree h_yield_agree OPCODE_TRACE_REL_INDEX

  use (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
  intro mem h_mem_agrees
  use mem_extends_pub_mem h_pubMem h_satisfied h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value h_rc h_mem_agrees
  cases exec_path h_satisfied.constraints h_disjoint (h_satisfied.h_bad OPCODE_TRACE_REL_INDEX)
          (h_satisfied.h_inj OPCODE_TRACE_REL_INDEX opcode_trace_is_chain_rel)
          (h_satisfied.h_chain OPCODE_TRACE_REL_INDEX opcode_trace_is_chain_rel)
          inp _ h_opcode_agree
  case inl h => left ; exact h
  case inr h_exec =>
    right
    rcases h_exec with ⟨n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ⟩
    replace h_n_lt := (Nat.lt_succ_of_lt h_n_lt)
    rw [Nat.succ_eq_add_one, ←@RelLookups_OPCODE_TRACE_OpcodeStatePairVals_size_eq _ inp pubMemLookups varAssigns] at h_n_lt
    use n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ
    intro i
    induction i using Fin.induction
    case zero =>
      rw [←h_path_start] at h_state_bound
      exact (exec_step_sound h_mem_agrees
              (h_opcodes_satisfied (path 0).1 (path 0).2 (h_path_mem 0))
              (h_lookup_terms_agree (path 0).1 (path 0).2 (h_path_mem 0))
              h_rc_yield h_mem_assign h_verify_instr 0 (by norm_num) h_state_bound)
    case succ i ih =>
    · apply exec_step_sound h_mem_agrees
              (h_opcodes_satisfied (path i.succ).1 (path i.succ).2 (h_path_mem i.succ))
              (h_lookup_terms_agree (path i.succ).1 (path i.succ).2 (h_path_mem i.succ))
              h_rc_yield h_mem_assign h_verify_instr i.succ
      · rw [Fin.val_succ, Nat.add_lt_iff_lt_sub_right]
        apply lt_of_lt_of_le (Fin.isLt i)
        apply Nat.le_sub_one_of_lt
        exact lt_of_lt_of_le h_n_lt h_num_steps
      apply CasmStateVal.strongly_bounded₀_of_strongly_bounded
      · simp
      rw [←h_path_succ i]
      apply ih.1

theorem trace_sound [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : ℕ}

      (inp : InputData)
      (pubMemLookups : PublicMem.Lookups)
      (varAssigns : Component → Array VarAssign)

      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups)

      -- Lookups are satisfied
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      -- Lookups agree with the assignments to the lookup terms
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      -- Memory assignments are functions.
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue))
      -- Range check rows are range checked.
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck))

      -- The constraints of the components are satisfied.
      (h_components: ComponentsSatisfied varAssigns)

      -- Number of steps
      (h_num_steps :  (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size ≤ 2^29)
      (h_state_bound : (initialState inp).strongly_bounded₀ 0) :

    ∃ mem : Felt252 → Felt252,
      Option.FnExtends mem inp.mStar ∧
      ∃ n : Nat, n ≤ 2^29
        ∧ ∃ exec : Fin (n + 1) → RegisterState Felt252,
            exec 0 = (initialState inp).toRegisterStateFelt252
            ∧ exec (Fin.last n) = (finalState inp).toRegisterStateFelt252
            ∧ ∀ i : Fin n, NextState mem (exec i.castSucc) (exec i.succ) := by
  rcases exec_sound
          h_pubMem h_satisfied h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value
          h_rc h_components h_num_steps h_state_bound
    with ⟨memAssign, h_exec⟩
  replace h_exec := h_exec memAssign.Mem252FromMemAssign memAssign.Mem252FromMemAssign_agrees
  use memAssign.Mem252FromMemAssign
  use h_exec.1
  cases h_exec.2
  case inl h =>
    use 0 ; simp
    use ![(initialState inp).toRegisterStateFelt252]
    simp [h]
  case inr h =>
    rcases h with ⟨n, h_n_lt, exec, _, h_initial, h_final, h_in_out, h_exec⟩
    have h_n_last : (Fin.last (n + 1)) = Fin.natAdd (n + 1) 0 := by rfl
    use n + 1
    constructor
    · linarith
    use Fin.append (fun i => (OpcodeInStateVal (exec i)).toRegisterStateFelt252)
          ![(OpcodeOutStateVal (exec (Fin.last n))).toRegisterStateFelt252]
    constructor
    · rw [←h_initial]
      have h_zero : (0 : Fin (n + 1 + 1)) = (Fin.castAdd 1 0) := by rfl
      simp only [h_zero, Fin.append_left]
    constructor
    · rw [←h_final]
      simp [h_n_last, Fin.append_right]
    intro i
    by_cases h_last : i = Fin.last n
    · have h_n_last_succ : (Fin.last n).castSucc = (Fin.castAdd 1 ((Fin.last n))) := by rfl
      simp [h_last, h_n_last, h_n_last_succ]
      exact (h_exec (Fin.last n)).2

    have h_i : i.castSucc = (Fin.castAdd 1 i) := by rfl
    have h_i_succ : i.succ = (Fin.castAdd 1 (i + 1)) := by
      simp [Fin.castAdd, Fin.succ, Fin.castLE]
      apply (Fin.val_add_one_of_lt _).symm
      exact Ne.lt_of_le h_last (Fin.le_last i)
    simp [h_i, h_i_succ]
    rcases Fin.exists_castSucc_eq.mpr h_last with ⟨j, h_j_eq⟩
    simp only [←h_j_eq, Fin.coeSucc_eq_succ, ←h_in_out j]
    exact (h_exec (j.castSucc)).2
