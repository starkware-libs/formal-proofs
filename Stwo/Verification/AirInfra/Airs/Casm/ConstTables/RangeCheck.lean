/-
For now, we model these simply as tables of lookups. Air functions that do range checks
take a table as input and return and extended table as output.

We currently represent the table as a list of memory / bitsize pairs, rather than a family
of tables (though the latter is closer to the Rust code).
-/
import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Memory
import Verification.AirInfra.Core.LookupTerm

def RangeCheckTable := Array (FeltExpr × Nat)
deriving Lean.ToJson, Lean.FromJson

instance: GetElem RangeCheckTable Nat (FeltExpr × Nat) (fun l i => i < Array.size l) := by
  unfold RangeCheckTable; infer_instance

/-
TODO(Jeremy): this name clashes with the one in `Verification.Semantics.Soundness.Hoare`.
Use `IsRangeCheckedBits` or something like that.
-/

def IsRangeChecked {R : Type*} [Ring R] (len : Nat) (x : R) : Prop :=
  ∃ n : Nat, n < 2^len ∧ x = ↑n

lemma isRangeChecked_of_isRangeChecked_of_le {R : Type*} [Ring R] {len₀ len₁ : Nat} {x : R} :
    len₀ ≤ len₁ → IsRangeChecked len₀ x → IsRangeChecked len₁ x := by
  intro h1 h2
  rcases h2 with ⟨n, h_n_lt, h_n_eq⟩
  use n, ?_, h_n_eq
  apply lt_of_lt_of_le h_n_lt
  exact Nat.pow_le_pow_right (by norm_num) h1

namespace RangeCheckTable

def empty : RangeCheckTable := Array.empty

protected def add (rangeCheckTable : RangeCheckTable) (len : Nat) (x : FeltExpr) :
  RangeCheckTable := rangeCheckTable.push (x, len)

def display (rangeCheckTable : RangeCheckTable) : IO Unit := do
  for h:i in [:rangeCheckTable.size] do
    let (value, len) := rangeCheckTable[i]
    IO.println s!"{i}: {value} {len}"

end RangeCheckTable

/-
Semantics.
-/

namespace RangeCheckTable

def SatisfiedBy [Fact (Nat.Prime Stwo.P)]
    (varAssign : VarAssign)
    (rangeCheckTable : RangeCheckTable) :=
    ∀ i, ∀ (h : i < rangeCheckTable.size),
      let (value, len) := rangeCheckTable[i]
      IsRangeChecked len (value.eval varAssign)

@[simp] theorem rangeCheckSatisfiedBy_add [Fact (Nat.Prime Stwo.P)]
    (varAssign : VarAssign)
    (rangeCheckTable : RangeCheckTable)
    (len : Nat)
    (x : FeltExpr) :
  (rangeCheckTable.add len x).SatisfiedBy varAssign ↔
    rangeCheckTable.SatisfiedBy varAssign ∧
      IsRangeChecked len (x.eval varAssign) := by
  simp [SatisfiedBy, RangeCheckTable.add]
  unfold RangeCheckTable at *
  constructor
  . intro h
    constructor
    . intro i hi
      specialize h i (by omega)
      rwa [Array.getElem_push_lt hi] at h
    specialize h _ (Nat.lt_succ_self _)
    rwa [Array.getElem_push_eq] at h
  intro h i hi
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
  . rw [Array.getElem_push_lt hi]
    apply h.1 i hi
  rw [Array.getElem_push_eq]
  exact h.2

/-
  Range Check Component Lookup Call
-/
def LookupCall : AirBuilder × AirLookupTerms :=
  let _state := AirBuilder.empty.deduce
  let ab1 := _state.1
  let len := _state.2
  let _state := ab1.deduce
  let ab2 := _state.1
  let value := _state.2
  let lt1 := AirLookupTerms.empty.add RANGE_CHECK_REL_INDEX (p_tuple_expr RANGE_CHECK_REL_INDEX ![len, value]) .yield
  (ab2, lt1)

end RangeCheckTable

-- For a given number of bits (n) all values i < 2 ^ n are in the yields for
-- the range check relation.
def RangeCheckYields [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (v : LookupValues t n_s NUM_PARTITIONS)
    {p : Fin (NUM_PARTITIONS + 1)}
    {partition : LookupPartition v p (rel_lengths RANGE_CHECK_REL_INDEX)}
    (lookups : RelationTuples partition) : Prop :=
  ∀ y ∈ yield_tuples lookups, IsRangeChecked (y 1).val (y 2)

lemma rc_SatisfiedBy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (term : LookupTerm rel_lengths)
      (varAssign : VarAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_agrees : UseAgrees term varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX)) :
    term.rel = RANGE_CHECK_REL_INDEX → term.useOrYield = .use →
       IsRangeChecked ((term.eval varAssign).tuple 1).val ((term.eval varAssign).tuple 2) := by
  intro h_rel h_use
  have h_chain : term.rel ∉ chain_rels := by
    rw [h_rel] ; apply range_check_not_chain_rel
  apply rel_lookup_sound term h_use h_chain varAssign h_satisfied h_agrees (fun x => IsRangeChecked (x 1).val (x 2))
  simp [RANGE_CHECK_REL_INDEX] at h_rel h_rc
  rw [h_rel]
  intro y h_y
  apply h_rc y
  exact h_y

namespace AirLookupTerms

-- Add a use term to the range check relation
-- (this still used a single relation for all range checks)

protected def add_rc (lookups : AirLookupTerms) (n : Nat) (x : FeltExpr) :
  AirLookupTerms := lookups.add RANGE_CHECK_REL_INDEX (p_tuple_expr RANGE_CHECK_REL_INDEX ![(FeltExpr.const n), x]) .use

lemma IsRangeChecked_add_rc [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (n : Nat)
      (x : FeltExpr) :
    UseAgree (terms.add_rc n x) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      IsRangeChecked n (x.eval varAssign)
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
  intro h
  have h_agree := UseAgree_add.mp h
  have h_sat := rc_SatisfiedBy _ _ _ h_agree.1 h_rc
  unfold LookupTerm.eval at h_sat
  simp at h_sat
  simp_all only [and_true]
  apply isRangeChecked_of_isRangeChecked_of_le _ h_sat
  rw [p_tuple_expr_i_eq_tuple_i_sub_one]
  all_goals simp [partition_lengths, rel_partition, RANGE_CHECK_REL_INDEX, TUPLE_SIZE]
  rw [ZMod.val_natCast]
  exact Nat.mod_le _ _

-- In this definition, the bit number is also a Felt
protected def add_rc_n_expr (lookups : AirLookupTerms) (n x : FeltExpr) :
  AirLookupTerms := lookups.add RANGE_CHECK_REL_INDEX (p_tuple_expr RANGE_CHECK_REL_INDEX ![n, x]) .use

lemma IsRangeChecked_add_rc_n_expr [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (n x : FeltExpr) :
    UseAgree (terms.add_rc_n_expr n x) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      IsRangeChecked (n.eval varAssign).val (x.eval varAssign)
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
  intro h
  have h_agree := UseAgree_add.mp h
  have h_sat := rc_SatisfiedBy _ _ _ h_agree.1 h_rc
  simp at h_sat
  simp_all only [and_true]
  exact h_sat


end AirLookupTerms
