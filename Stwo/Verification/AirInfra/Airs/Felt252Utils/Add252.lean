import Verification.AirInfra.Core.Felt252IdMemory.IdToBig
import Verification.AirInfra.Airs.Felt252Utils.VerifyAdd252



namespace Add252

def call [Fact (Nat.Prime Stwo.P)]
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (a b : Felt252Expr) :
    AirBuilder × AirLookupTerms × Felt252Expr :=
  let _state := airBuilder.deduce252
  let ab1 := _state.1
  let c := _state.2
  let lt1 := RangeCheckMemValue.call lookupTerms c
  let ab2 := VerifyAdd252.call ab1 a b c
  (ab2, lt1, c)

def spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
  RangeCheckMemValue.spec c ∧ VerifyAdd252.spec a b c

def spec := spec_auto

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (a b : Felt252Expr) :
    let ⟨new_ab, new_lt, c⟩ := call ab lt a b
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (a.eval varAssign) (b.eval varAssign) (c.eval varAssign) := by
  unfold call ; lift_lets
  intro state1 ab1 c lt1 ab2
  intro hab2 hlt1
  have ⟨hab1, h_sum⟩ := VerifyAdd252.sound_auto varAssign ab1 a b c hab2
  have ⟨hlt, h_checked⟩ := RangeCheckMemValue.sound_auto_Felt252 varAssign _ _ h_rc _ hlt1
  have hab := (AirBuilder.deduce252_SatisfiedBy _ varAssign).mp hab1
  use hab, hlt
  use h_checked

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {a b : Felt252Expr} :
    AirLookupTerms.NoYieldTerms (call ab lt a b).2.1 := by
  apply RangeCheckMemValue.NoYieldTerms_of_call
  exact h

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {a b : Felt252Expr} :
    AirLookupTerms.NoTermsOfRel (call ab lt a b).2.1 OPCODE_TRACE_REL_INDEX:= by
  apply RangeCheckMemValue.NoTermsOfRel_OPCODE_TRACE_of_call
  exact h

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {a b : Felt252Expr} :
    AirLookupTerms.RelInRelTuples (call ab lt a b).2.1 := by
  apply RangeCheckMemValue.RelInRelTuples_of_call
  exact h

end Add252
