import Verification.AirInfra.Soundness.Components
import Verification.AirInfra.Core.LookupTerm
import Verification.AirInfra.Airs.Casm.Opcodes.GenericOpcode.GenericOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.CallOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.RetOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.AssertEqOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.JumpOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.JnzOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.AddApOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.AddOpcode
import Verification.AirInfra.Airs.Casm.Opcodes.MulOpcode

noncomputable section

namespace OpcodeLookup

/-
  Opcode lookup call
-/

-- Check whether the order below is the correct order.
def CasmStateTuple (casmState : CasmState) := ![casmState.pc, casmState.ap, casmState.fp]
def CasmStateValTuple (casmStateVal : CasmStateVal) := p_tuple OPCODE_TRACE_REL_INDEX ![casmStateVal.pc, casmStateVal.ap, casmStateVal.fp]
def CasmStateEvalTuple [Fact (Nat.Prime Stwo.P)] (casmState : CasmState) (varAssign : VarAssign) :=
  CasmStateValTuple (casmState.eval varAssign)

lemma CasmStateValTuple_inj {s1 s2 : CasmStateVal} (h : CasmStateValTuple s1 = CasmStateValTuple s2) : s1 = s2 := by
  replace h := p_tuple_inj h
  ext ; exact congr_fun h 0 ; exact congr_fun h 1 ; exact congr_fun h 2

/-
  A lookup for an opcode call. Deduces the input state, calls the air function and adds use and yield
  lookup terms for the input and output states (respectively).
-/
def OpcodeLookupCall [Fact (Nat.Prime Stwo.P)]
      (call: AirBuilder → AirLookupTerms → CasmState → AirBuilder × AirLookupTerms × CasmState)
      : AirBuilder × AirLookupTerms × CasmState × CasmState :=
    let _state := AirBuilder.empty.deduce
    let ab1 := _state.1
    let pc_in := _state.2
    let _state := ab1.deduce
    let ab2 := _state.1
    let ap_in := _state.2
    let _state := ab2.deduce
    let ab3 := _state.1
    let fp_in := _state.2
    let _state := call ab3 AirLookupTerms.empty { pc := pc_in, ap := ap_in, fp := fp_in }
    let ab4 := _state.1
    let lt1 := _state.2.1
    let out_state := _state.2.2
    let lt2 := lt1.add
                OPCODE_TRACE_REL_INDEX
                (p_tuple_expr OPCODE_TRACE_REL_INDEX (CasmStateTuple { pc := pc_in, ap := ap_in, fp := fp_in }))
                .use
    let lt3 := lt2.add OPCODE_TRACE_REL_INDEX (p_tuple_expr OPCODE_TRACE_REL_INDEX (CasmStateTuple out_state)) .yield
    (ab4, lt3, { pc := pc_in, ap := ap_in, fp := fp_in }, out_state)

-- Auxiliary definition describing the call without the addition of the opcode lookup terms.
-- This is used as an intermediate structure in some of the definitions and theorems below.
def OpcodeLookupCallAux [Fact (Nat.Prime Stwo.P)]
      (call: AirBuilder → AirLookupTerms → CasmState → AirBuilder × AirLookupTerms × CasmState)
      : AirBuilder × AirLookupTerms × CasmState :=
    let _state := AirBuilder.empty.deduce
    let ab1 := _state.1
    let pc_in := _state.2
    let _state := ab1.deduce
    let ab2 := _state.1
    let ap_in := _state.2
    let _state := ab2.deduce
    let ab3 := _state.1
    let fp_in := _state.2
    let _state := call ab3 AirLookupTerms.empty { pc := pc_in, ap := ap_in, fp := fp_in }
    let ab4 := _state.1
    let lt1 := _state.2.1
    let out_state := _state.2.2
    (ab4, lt1, out_state)

def OpcodeCall [Fact (Nat.Prime Stwo.P)] (o : Opcode) :
    AirBuilder → AirLookupTerms → CasmState → AirBuilder × AirLookupTerms × CasmState :=
  match o with
    | .Generic => GenericOpcode.call
    | .CallRel => (CallOpcode.call true false)
    | .CallAbsBaseFP => (CallOpcode.call false true)
    | .CallAbsBaseAP => (CallOpcode.call false false)
    | .Ret => RetOpcode.call
    | .AssertEq =>  (AssertEqOpcode.call false false)
    | .AssertEqImm =>  (AssertEqOpcode.call true false)
    | .AssertEqDoubleDeref =>  (AssertEqOpcode.call false true)
    | .JumpImm =>  (JumpOpcode.call true true false)
    | .JumpDoubleDeref =>  (JumpOpcode.call false false true)
    | .JumpRel =>  (JumpOpcode.call true false false)
    | .JumpAbs =>  (JumpOpcode.call false false false)
    | .JnzNotTaken =>  (JnzOpcode.JnzNotTakenOpcode.call)
    | .JnzTaken =>  (JnzOpcode.JnzTakenOpcode.call)
    | .AddAp =>  (AddApOpcode.call)
    | .AddSmall =>  (AddOpcode.AddSmallOpcode.call)
    | .Add252 =>  (AddOpcode.Add252Opcode.call)
    | .MulSmall =>  (MulOpcode.MulSmallOpcode.call)
    | .Mul252 =>  (MulOpcode.Mul252Opcode.call)

def OpcodeAirFns [Fact (Nat.Prime Stwo.P)] (o : Opcode) : AirBuilder × AirLookupTerms × CasmState × CasmState :=
  OpcodeLookupCall (OpcodeCall o)

def LookupCall [Fact (Nat.Prime Stwo.P)] (o : Opcode) : AirBuilder × AirLookupTerms :=
  ((OpcodeAirFns o).1, (OpcodeAirFns o).2.1)

def OpcodeInStateVal [Fact (Nat.Prime Stwo.P)] (oe : Opcode × VarAssign) :=
  (OpcodeAirFns oe.1).2.2.1.eval oe.2
def OpcodeOutStateVal [Fact (Nat.Prime Stwo.P)] (oe : Opcode × VarAssign) :=
  (OpcodeAirFns oe.1).2.2.2.eval oe.2

def initialState (inp : InputData) : CasmStateVal := { pc := inp.initialPc, ap := inp.initialAp, fp := inp.initialAp }
def finalState (inp : InputData) : CasmStateVal := { pc := inp.finalPc, ap := inp.finalAp, fp := inp.initialAp }

-- State pairs

/-
  For the proof that there is path through state in/out pairs, construct these pairs and the corresponding
  tuple.
-/

-- In/out state pairs
def OpcodeStatePairVals [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :=
  Opcode.univ.toArray.flatMap
    (fun o => (varAssigns o).map (fun v => (OpcodeInStateVal (o, v), OpcodeOutStateVal (o, v))))

def StatePairTuples [Fact (Nat.Prime Stwo.P)] (inp : InputData) (varAssigns : Opcode → Array VarAssign) :=
  ((OpcodeStatePairVals varAssigns).map (fun pa => (CasmStateValTuple pa.1, CasmStateValTuple pa.2))).push
    (CasmStateValTuple (finalState inp), CasmStateValTuple (initialState inp))

-- All state in/out tuples (including initial and final state)

def InStateTuples [Fact (Nat.Prime Stwo.P)] (inp : InputData) (varAssigns : Opcode → Array VarAssign)
    : Array (Fin (rel_lengths OPCODE_TRACE_REL_INDEX + 1) → Felt) :=
  (StatePairTuples inp varAssigns).map (fun pair => pair.fst)
def OutStateTuples [Fact (Nat.Prime Stwo.P)] (inp : InputData) (varAssigns : Opcode → Array VarAssign)
    : Array (Fin (rel_lengths OPCODE_TRACE_REL_INDEX + 1) → Felt) :=
  (StatePairTuples inp varAssigns).map (fun pair => pair.snd)

lemma InStateTuples_OpcodeStatePairVals_size_eq [Fact (Nat.Prime Stwo.P)] {inp : InputData} {varAssigns : Opcode → Array VarAssign} :
    (InStateTuples inp varAssigns).size = (OpcodeStatePairVals varAssigns).size + 1 := by
  simp only [InStateTuples, Array.size_map, StatePairTuples, Array.size_push]

lemma OutStateTuples_OpcodeStatePairVals_size_eq [Fact (Nat.Prime Stwo.P)] {inp : InputData} {varAssigns : Opcode → Array VarAssign} :
    (OutStateTuples inp varAssigns).size = (OpcodeStatePairVals varAssigns).size + 1 := by
  simp only [OutStateTuples, Array.size_map, StatePairTuples, Array.size_push]

-- State in/out values per opcode

/-
  To show that the in/out state tuples are the same as the tuples generated from the
  lookup terms added by the components (+ the initial and final states) we need to look at
  the same set of states, but separated into the in/out sets.
-/

-- The evaluated input casm states of all opcodes.
def OpcodeInStateVals [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :=
  Opcode.univ.toArray.flatMap (fun o => (varAssigns o).map (fun v => OpcodeInStateVal (o, v)))
-- The evaluated output casm states of all opcodes.
def OpcodeOutStateVals [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :=
  Opcode.univ.toArray.flatMap (fun o => (varAssigns o).map (fun v => OpcodeOutStateVal (o, v)))

-- All state in/out values (including initial and final state)

def InStateVals [Fact (Nat.Prime Stwo.P)] (inp : InputData) (varAssigns : Opcode → Array VarAssign) :=
  (OpcodeInStateVals varAssigns).push (finalState inp)
def OutStateVals [Fact (Nat.Prime Stwo.P)] (inp : InputData) (varAssigns : Opcode → Array VarAssign) :=
  (OpcodeOutStateVals varAssigns).push (initialState inp)

lemma InStateVals_tuples_eq_InStateTuples [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {varAssigns : Opcode → Array VarAssign} :
    (InStateVals inp varAssigns).map (fun s => CasmStateValTuple s) = InStateTuples inp varAssigns := by
  simp only [InStateTuples, StatePairTuples, InStateVals, Array.map_push]
  congr 1
  simp only [OpcodeStatePairVals, OpcodeInStateVals, Array.map_map, Array.map_flatMap, Function.comp_def]

lemma OutStateVals_tuples_eq_OutStateTuples [Fact (Nat.Prime Stwo.P)]
      {inp : InputData}
      {varAssigns : Opcode → Array VarAssign} :
    (OutStateVals inp varAssigns).map (fun s => CasmStateValTuple s) = OutStateTuples inp varAssigns := by
  simp only [OutStateTuples, StatePairTuples, OutStateVals, Array.map_push]
  congr 1
  simp only [OpcodeStatePairVals, OpcodeOutStateVals, Array.map_map, Array.map_flatMap, Function.comp_def]

/-
  Opcode lookup terms (and their evaluations)
-/

/-
  Here, we no longer look at the in/out states, but at the lookup terms added by the
  opcode lookup call functions.
-/

def InStateLookupTerms [Fact (Nat.Prime Stwo.P)] (lt : AirLookupTerms) :=
  lt.filter (fun term => term.rel = OPCODE_TRACE_REL_INDEX ∧ term.useOrYield = .use)
def OutStateLookupTerms [Fact (Nat.Prime Stwo.P)] (lt : AirLookupTerms) :=
  lt.filter (fun term => term.rel = OPCODE_TRACE_REL_INDEX ∧ term.useOrYield = .yield)
-- Evaluation of these on the possible variable assignments.
def OpcodeInStateLookups [Fact (Nat.Prime Stwo.P)] (o : Opcode) (varAssigns : Array VarAssign) :=
 (InStateLookupTerms (OpcodeAirFns o).2.1).flatMap (fun term => (varAssigns.map (fun v => term.eval v)))
def OpcodeOutStateLookups [Fact (Nat.Prime Stwo.P)] (o : Opcode) (varAssigns : Array VarAssign) :=
 (OutStateLookupTerms (OpcodeAirFns o).2.1).flatMap (fun term => (varAssigns.map (fun v => term.eval v)))
-- The union of these over all opcodes.
def InStateLookups [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :=
  Opcode.univ.toArray.flatMap (fun o => OpcodeInStateLookups o (varAssigns o))
def OutStateLookups [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :=
  Opcode.univ.toArray.flatMap (fun o => OpcodeOutStateLookups o (varAssigns o))

/-
  Opcode lookup terms
-/

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)] (o : Opcode) :
    AirLookupTerms.NoYieldTerms (OpcodeLookupCallAux (OpcodeCall o)).2.1 := by
  unfold OpcodeLookupCallAux OpcodeCall
  cases o
  case Generic =>
    apply GenericOpcode.NoYieldTerms_of_call
    apply AirLookupTerms.empty_NoYieldTerms
  case MulSmall =>
    apply MulOpcode.MulSmallOpcode.NoYieldTerms_of_call
    apply AirLookupTerms.empty_NoYieldTerms
  case Mul252 =>
    apply MulOpcode.Mul252Opcode.NoYieldTerms_of_call
    apply AirLookupTerms.empty_NoYieldTerms
  all_goals {
    repeat
      apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
    apply AirLookupTerms.empty_NoYieldTerms
  }

lemma lookupCall_yield_term [Fact (Nat.Prime Stwo.P)] {o : Opcode} :
    ∀ t ∈ (OpcodeAirFns o).2.1, t.useOrYield = .yield →
      t = {
          rel := OPCODE_TRACE_REL_INDEX,
          tuple := p_tuple_expr OPCODE_TRACE_REL_INDEX (CasmStateTuple (OpcodeLookupCallAux (OpcodeCall o)).2.2)
          useOrYield := .yield
      } := by
  intro t h_t h_yield
  rw [OpcodeAirFns, OpcodeLookupCall, ←AirLookupTerms.add'_eq_add] at h_t
  apply Or.resolve_left (AirLookupTerms.mem_add' t h_t)
  apply AirLookupTerms.yield_not_mem_NoYieldTerms h_yield
  apply AirLookupTerms.add'_NoYieldTerms.mpr ; simp
  apply NoYieldTerms_of_call

lemma lookupCall_yield_term_eval [Fact (Nat.Prime Stwo.P)] {o : Opcode} {varAssign : VarAssign} :
    ∀ t ∈ (OpcodeAirFns o).2.1, t.useOrYield = .yield →
      t.eval varAssign = {
          rel := OPCODE_TRACE_REL_INDEX,
          --tuple := p_tuple OPCODE_TRACE_REL_INDEX (CasmStateEvalTuple (OpcodeLookupCallAux (OpcodeCall o)).2.2 varAssign)
          tuple := CasmStateEvalTuple (OpcodeLookupCallAux (OpcodeCall o)).2.2 varAssign
          useOrYield := .yield
      } := by
  intro t h_t h_y
  rw [lookupCall_yield_term t h_t h_y]
  simp [LookupTerm.eval]
  exact List.ofFn_inj.mp rfl

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)] (o : Opcode) :
    AirLookupTerms.NoTermsOfRel (OpcodeLookupCallAux (OpcodeCall o)).2.1 OPCODE_TRACE_REL_INDEX := by
  unfold OpcodeLookupCallAux OpcodeCall
  cases o
  case Generic =>
    apply GenericOpcode.NoTermsOfRel_OPCODE_TRACE_of_call
    apply AirLookupTerms.empty_NoTermsOfRel OPCODE_TRACE_REL_INDEX
  case MulSmall =>
    apply MulOpcode.MulSmallOpcode.NoTermsOfRel_OPCODE_TRACE_of_call
    apply AirLookupTerms.empty_NoTermsOfRel OPCODE_TRACE_REL_INDEX
  case Mul252 =>
    apply MulOpcode.Mul252Opcode.NoTermsOfRel_OPCODE_TRACE_of_call
    apply AirLookupTerms.empty_NoTermsOfRel OPCODE_TRACE_REL_INDEX
  all_goals {
    repeat
      apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
      simp [RANGE_CHECK_REL_INDEX, MEMORY_ADDR_TO_ID_REL_INDEX, MEMORY_ID_TO_VALUE_REL_INDEX, VERIFY_INSTR_REL_INDEX, OPCODE_TRACE_REL_INDEX]
    apply AirLookupTerms.empty_NoTermsOfRel OPCODE_TRACE_REL_INDEX
  }

/-
  The following two lemmas show that all lookup terms for the opcode relation are
  the input and output states added by OpcodeLookupCall.
-/

lemma InStateLookupTerms_eq_in_state [Fact (Nat.Prime Stwo.P)] :
    ∀ o, (InStateLookupTerms (OpcodeAirFns o).2.1) =
      #[{
          rel := OPCODE_TRACE_REL_INDEX,
          useOrYield := .use,
          tuple := p_tuple_expr OPCODE_TRACE_REL_INDEX (CasmStateTuple (OpcodeAirFns o).2.2.1)
        }] := by
  intro o
  unfold OpcodeAirFns OpcodeLookupCall InStateLookupTerms
  rw [AirLookupTerms.add_is_eq_of_ne _]
  rw [AirLookupTerms.add_is_singleton_of_no_terms_of_rel _]
  apply NoTermsOfRel_OPCODE_TRACE_of_call
  simp

lemma OutStateLookupTerms_eq_out_state [Fact (Nat.Prime Stwo.P)] :
    ∀ o, (OutStateLookupTerms (OpcodeAirFns o).2.1) =
      #[{
          rel := OPCODE_TRACE_REL_INDEX,
          useOrYield := .yield,
          tuple := p_tuple_expr OPCODE_TRACE_REL_INDEX (CasmStateTuple (OpcodeAirFns o).2.2.2)
        }] := by
  intro o
  unfold OpcodeAirFns OpcodeLookupCall OutStateLookupTerms
  rw [AirLookupTerms.add_is_singleton_of_filter _]
  rw [AirLookupTerms.add_is_eq_of_ne _]
  rw [Array.filter_eq_empty_iff]
  intro t h_t
  simp only [decide_eq_true_eq, Classical.not_and_iff_not_or_not]
  left
  rw [Array.mem_iff_getElem] at h_t
  rcases h_t with ⟨i, h_i, h_eq⟩
  rw [←h_eq]
  apply (NoTermsOfRel_OPCODE_TRACE_of_call o) i h_i
  simp

lemma InStateLookups_eq_in_state_vals [Fact (Nat.Prime Stwo.P)] {varAssigns : Opcode → Array VarAssign} :
  InStateLookups varAssigns =
    (OpcodeInStateVals varAssigns).map
      (fun s => {
        rel := OPCODE_TRACE_REL_INDEX,
        useOrYield := .use,
        tuple := CasmStateValTuple s
      }) := by
  unfold InStateLookups OpcodeInStateVals
  rw [Array.map_flatMap]
  congr
  funext o
  unfold OpcodeInStateLookups
  simp only [InStateLookupTerms_eq_in_state, Array.flatMap_singleton, LookupTerm.eval]
  simp only [Array.map_map, Function.comp_def, Array.map_eq_map_iff]
  intro v h_v_mem
  simp [CasmStateValTuple, CasmStateTuple]
  exact List.ofFn_inj.mp rfl

lemma terms_InStateTuples_eq_InStateLookups [Fact (Nat.Prime Stwo.P)] {inp : InputData} {varAssigns : Opcode → Array VarAssign} :
  (InStateTuples inp varAssigns).map (fun t => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .use, tuple := t }) =
    (InStateLookups varAssigns).push { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .use, tuple := CasmStateValTuple (finalState inp) } := by
  simp only [←InStateVals_tuples_eq_InStateTuples, InStateVals, Array.map_push]
  simp only [InStateLookups_eq_in_state_vals]
  simp ; congr

lemma OutStateLookups_eq_out_state_vals [Fact (Nat.Prime Stwo.P)] (varAssigns : Opcode → Array VarAssign) :
  OutStateLookups varAssigns =
    (OpcodeOutStateVals varAssigns).map (fun s => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .yield, tuple := CasmStateValTuple s }) := by
  unfold OutStateLookups OpcodeOutStateVals
  rw [Array.map_flatMap]
  congr
  funext o
  unfold OpcodeOutStateLookups
  simp only [OutStateLookupTerms_eq_out_state, Array.flatMap_singleton, LookupTerm.eval]
  simp only [Array.map_map, Function.comp_def, Array.map_eq_map_iff]
  intro v h_v_mem
  simp [CasmStateValTuple, CasmStateTuple]
  exact List.ofFn_inj.mp rfl

lemma terms_OutStateTuples_eq_OutStateLookups [Fact (Nat.Prime Stwo.P)] {inp : InputData} {varAssigns : Opcode → Array VarAssign} :
  (OutStateTuples inp varAssigns).map (fun t => { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .yield, tuple := t }) =
    (OutStateLookups varAssigns).push { rel := OPCODE_TRACE_REL_INDEX, useOrYield := .yield, tuple := CasmStateValTuple (initialState inp) } := by
  simp only [←OutStateVals_tuples_eq_OutStateTuples, OutStateVals, Array.map_push]
  simp only [OutStateLookups_eq_out_state_vals]
  simp ; congr

/-
  Relation Encoded in Tuple
-/

lemma opcodes_RelInRelTuples [Fact (Nat.Prime Stwo.P)] {ab : AirBuilder} {s : CasmState}:
    ∀ o, AirLookupTerms.RelInRelTuples (OpcodeCall o ab AirLookupTerms.empty s).2.1 := by
  intro o
  cases o
  all_goals
    repeat
      apply AirLookupTerms.add'_RelInRelTuple.mpr
    try apply AirLookupTerms.empty_RelInRelTuple
  · apply GenericOpcode.RelInRelTuples_of_call
    apply AirLookupTerms.empty_RelInRelTuple
  · apply MulOpcode.MulSmallOpcode.RelInRelTuples_of_call
    apply AirLookupTerms.empty_RelInRelTuple
  apply MulOpcode.Mul252Opcode.RelInRelTuples_of_call
  apply AirLookupTerms.empty_RelInRelTuple

/-
  Agreement
-/

/-
  This is the condition we need to ensure that the satisfaction of the lookup constraints implies that
  there is path (trace) through in/out evaluated state pairs.

  The condition states that the use lookup tuples are exactly those in InStateTuples and the yield lookup tuples
  are exactly those in OutStateTuples.
-/

def OpcodeStatesAgree [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
    (inp : InputData)
    {v : LookupValues t n_s NUM_PARTITIONS}
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths OPCODE_TRACE_REL_INDEX)}
    (lookups : RelationTuples partition)
    (varAssigns : Opcode → Array VarAssign) :=
  Multiset.ofList (InStateTuples inp varAssigns).toList = Multiset.map partition.tuples lookups.use_i.val
  ∧ Multiset.ofList (OutStateTuples inp varAssigns).toList = Multiset.map partition.tuples lookups.yield_i.val


end OpcodeLookup
