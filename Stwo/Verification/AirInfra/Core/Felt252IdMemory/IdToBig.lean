import Verification.AirInfra.Core.Memory
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck

open Fin.NatCast

abbrev MemoryIdToBig := Memory 1 FELT252_N_WORDS

def MemoryIdToBig.empty : MemoryIdToBig := Memory.empty

/- Semantics -/

abbrev MemoryIdToBigAssign := MemAssign 1 FELT252_N_WORDS

namespace RangeCheckMemValue



/-
  YS: This function does not model the original Rust function accurately. The Rust range_check
  function selects which range check table to use (depending on the type of the range check) and then
  adds a lookup for the range check table for that type (in our case, the table for pairs with
  FELT252_BITS_PER_WORD bits each). Currently, our modeling has a single range check table, where
  each range check is for a single value and specifies the number of bits to check.

  While the current definition does not exactly reflect the lookup which takes place, it does already
  group the lookups into pairs, so replacing the range-check lookup in the definition below should not
  affect most of the proofs below.
-/

@[irreducible]
def rangeCheck_9_9_const {N : Nat} [NeZero N] (value : Fin N → FeltExpr) (i : Nat) (lt : AirLookupTerms) :=
  (lt.add_rc FELT252_BITS_PER_WORD (value (i * 2))).add_rc FELT252_BITS_PER_WORD (value (i * 2 + 1))

def call
    {N : Nat}
    [NeZero N]
    (lookupTerms : AirLookupTerms)
    (value : Fin N → FeltExpr) :
    AirLookupTerms :=
  forLoop 0 (N / 2) lookupTerms (rangeCheck_9_9_const value)

def spec_auto {N : Nat} (value : Fin N → Felt) : Prop :=
  ∀ i : Fin N, i < (N / 2) * 2 → IsRangeChecked FELT252_BITS_PER_WORD (value i)

def spec {N : Nat} (value : Fin N → Felt) :=
  2 ∣ N → ∀ i : Fin N, IsRangeChecked FELT252_BITS_PER_WORD (value i)

lemma rangeCheck_9_9_const_UseAgree' [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {N : Nat} [NeZero N]
      {lt : AirLookupTerms}
      {varAssign : VarAssign}
      {value : Fin N → FeltExpr}
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX)) :
  ∀ i < N / 2,
    AirLookupTerms.UseAgree (rangeCheck_9_9_const value i lt) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
    AirLookupTerms.UseAgree lt varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples
      ∧ IsRangeChecked 9 ((value  (i * 2)).eval varAssign)
      ∧ IsRangeChecked 9 ((value  (i * 2 + 1)).eval varAssign) := by
  unfold rangeCheck_9_9_const FELT252_BITS_PER_WORD
  intro i h_i h_agree
  have h1 := AirLookupTerms.IsRangeChecked_add_rc _ _ _ h_rc _ _ h_agree
  have h2 := AirLookupTerms.IsRangeChecked_add_rc _ _ _ h_rc _ _ h1.2
  exact ⟨h2.2, h2.1, h1.1⟩


theorem rc_loop_n_UseAgree' [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {N : Nat} [NeZero N]
      (lt : AirLookupTerms)
      (varAssign : VarAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (start n : Nat)
      (h_n_le : start + n ≤ N / 2)
      (value : Fin N → FeltExpr) :
    AirLookupTerms.UseAgree (forLoop start (start + n) lt (rangeCheck_9_9_const value)) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      AirLookupTerms.UseAgree lt varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples
      ∧ ∀ i, i < n * 2 → IsRangeChecked 9 ((value (start * 2 + i)).eval varAssign) := by
  unfold forLoop
  induction n with
  | zero => simp [forLoopAux] ; intro h ; simp only [add_zero] at h_n_le ; exact h
  | succ l h_ind =>
    replace h_ind := h_ind (le_of_lt (Nat.succ_le.mp h_n_le))
    rw [add_tsub_cancel_left] at h_ind
    rw [add_tsub_cancel_left]
    rw [forLoopAux_succ]
    intro h
    have h1 := rangeCheck_9_9_const_UseAgree' _ h_rc (start + l) (by linarith [h_n_le]) h
    have h2 := h_ind h1.1
    use h2.1
    have h3 : (l + 1) * 2 = l * 2 + 1 + 1 := by ring
    rw [h3, Nat.forall_lt_succ, Nat.forall_lt_succ]
    have h_l2 : (((l * 2) : ℕ) : Fin N) = (l : Fin N) * 2 := by
      ext; simp [Fin.coe_mul]
    constructor
    · use h2.2
      rw [h_l2, ←right_distrib, ←Nat.cast_add] ;
      exact h1.2.1
    rw [Nat.cast_add, ←add_assoc, h_l2, ←right_distrib, ←Nat.cast_add]
    exact h1.2.2

theorem rc_loop_UseAgree' [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {N : Nat} [NeZero N]
      (lt : AirLookupTerms)
      (varAssign : VarAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (value : Fin N → FeltExpr) :
    AirLookupTerms.UseAgree (forLoop 0 (N / 2) lt (rangeCheck_9_9_const value)) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      AirLookupTerms.UseAgree lt varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples
      ∧ ∀ i, i < (N / 2) * 2 → IsRangeChecked 9 ((value i).eval varAssign) := by
  have h := rc_loop_n_UseAgree' lt varAssign _ h_rc 0 (N/2) (by simp) value
  simp at h
  exact h

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
    {N : Nat}
    [NeZero N]
    (varAssign : VarAssign)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (value : Fin N → FeltExpr) :
    AirLookupTerms.UseAgree (call lt value) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      AirLookupTerms.UseAgree lt varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (fun i => (value i).eval varAssign) := by
  unfold call
  intro hlt
  let ⟨hlt, h_checked⟩ := rc_loop_UseAgree' _ _ _ h_rc _ hlt
  use hlt
  intro h_N i
  have : i.val < (N / 2) * 2 := by simp [Nat.div_mul_cancel h_N]
  replace h_checked := h_checked i.val this
  simp only [Fin.cast_val_eq_self] at h_checked
  simp only [FELT252_BITS_PER_WORD, h_checked]

-- Specialized for the case where the value is Felt252
theorem sound_auto_Felt252 [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
    (varAssign : VarAssign)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (value : Felt252Expr) :
    AirLookupTerms.UseAgree (call lt value) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      AirLookupTerms.UseAgree lt varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (fun i => (value i).eval varAssign) := by
  apply sound_auto _ _ _ h_rc

lemma IsRangeChecked_of_spec {x : Felt252Words} (h : spec x) :
    ∃ xn : Felt252Nats, xn.IsRangeChecked x := by
  unfold spec IsRangeChecked FELT252_N_WORDS FELT252_BITS_PER_WORD at h
  norm_num at h
  use fun i => Classical.choose (h i)
  intro i
  rw [and_comm]
  apply Classical.choose_spec (h i)

lemma NoYieldTerms_of_call {N : Nat} [NeZero N]
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {value : Fin N → FeltExpr} :
    AirLookupTerms.NoYieldTerms (call lt value) := by
  apply forLoopCorrect _ _ _ _ (by simp) (fun _ lt => AirLookupTerms.NoYieldTerms lt) h
  intro i h_i_0 h_i_lt lt_i h_lt_i
  unfold rangeCheck_9_9_const AirLookupTerms.add_rc
  apply AirLookupTerms.add'_NoYieldTerms.mpr
  simp ; apply AirLookupTerms.add'_NoYieldTerms.mpr
  simp [h_lt_i]

lemma NoTermsOfRel_OPCODE_TRACE_of_call {N : Nat} [NeZero N]
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {value : Fin N → FeltExpr} :
    AirLookupTerms.NoTermsOfRel (call lt value) OPCODE_TRACE_REL_INDEX := by
  apply forLoopCorrect _ _ _ _ (by simp) (fun _ lt => AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX) h
  intro i h_i_0 h_i_lt lt_i h_lt_i
  unfold rangeCheck_9_9_const AirLookupTerms.add_rc
  apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
  simp [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
  simp_all [OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call {N : Nat} [NeZero N]
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {value : Fin N → FeltExpr} :
    AirLookupTerms.RelInRelTuples (call lt value) := by
  apply forLoopCorrect _ _ _ _ (by simp) (fun _ lt => AirLookupTerms.RelInRelTuples lt) h
  intro i h_i_0 h_i_lt lt_i h_lt_i
  unfold rangeCheck_9_9_const AirLookupTerms.add_rc
  repeat
    apply AirLookupTerms.add'_RelInRelTuple.mpr
  simp [h_lt_i]

end RangeCheckMemValue
