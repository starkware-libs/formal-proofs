
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.LookupTerm
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck

-- TODO(Jeremy): move this
namespace Matrix

@[simp]
lemma cons_val_five {α : Type} {m : Nat} (x : α) (u : Fin m.succ.succ.succ.succ.succ → α) :
    vecCons x u 5 = vecHead (vecTail (vecTail (vecTail (vecTail u)))) :=
  rfl

end Matrix

namespace EncodeOffsets

def call (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (off0_f off1_f off2_f : FeltExpr) : AirBuilder × AirLookupTerms × (Fin 6 → FeltExpr) :=
  let _state := airBuilder.deduce
  let ab0 := _state.1
  let low0_f := _state.2
  let _state := ab0.deduce
  let ab1 := _state.1
  let mid0_f := _state.2

  let new_off0_f := low0_f + (mid0_f * FeltExpr.const (1 <<< 9))
  let ab2 := ab1.constrain (new_off0_f - off0_f)

  let _state := ab2.deduce
  let ab3 := _state.1
  let low1_f := _state.2
  let _state := ab3.deduce
  let ab4 := _state.1
  let mid1_f := _state.2
  let _state := ab4.deduce
  let ab5 := _state.1
  let high1_f := _state.2

  let new_off1_f := (low1_f + (mid1_f * FeltExpr.const (1 <<< 2))) +
    (high1_f * FeltExpr.const (1 <<< 11))
  let ab6 := ab5.constrain (new_off1_f - off1_f)

  let _state := ab6.deduce
  let ab7 := _state.1
  let low2_f := _state.2
  let _state := ab7.deduce
  let ab8 := _state.1
  let mid2_f := _state.2
  let _state := ab8.deduce
  let ab9 := _state.1
  let high2_f := _state.2

  let new_off2_f := (low2_f + (mid2_f * FeltExpr.const (1 <<< 4))) +
    (high2_f * FeltExpr.const (1 <<< 13))
  let ab10 := ab9.constrain (new_off2_f - off2_f)

  let lt1 := lookupTerms.add_rc 7 mid0_f
  let lt2 := lt1.add_rc 2 low1_f
  let lt3 := lt2.add_rc 5 high1_f
  let lt4 := lt3.add_rc 4 low2_f
  let lt5 := lt4.add_rc 3 high2_f

  (ab10, lt5,
  fun i => match i with
    | 0 => low0_f
    | 1 => mid0_f + (low1_f * FeltExpr.const (1 <<< 7))
    | 2 => mid1_f
    | 3 => high1_f + (low2_f * FeltExpr.const (1 <<< 5))
    | 4 => mid2_f
    | 5 => high2_f)

def spec_auto (off0_f off1_f off2_f : Felt) (ρout : Fin 6 → Felt) : Prop :=
  ∃ low0_f mid0_f : Felt,
    let new_off0_f := low0_f + (mid0_f * (1 <<< 9))
    new_off0_f - off0_f = 0 ∧
  ∃ low1_f mid1_f high1_f : Felt,
    let new_off1_f := (low1_f + (mid1_f * (1 <<< 2))) + (high1_f * (1 <<< 11))
    new_off1_f - off1_f = 0 ∧
  ∃ low2_f mid2_f high2_f : Felt,
    let new_off2_f := (low2_f + (mid2_f * (1 <<< 4))) + (high2_f * (1 <<< 13))
    new_off2_f - off2_f = 0 ∧
    IsRangeChecked 7 mid0_f ∧
    IsRangeChecked 2 low1_f ∧
    IsRangeChecked 5 high1_f ∧
    IsRangeChecked 4 low2_f ∧
    IsRangeChecked 3 high2_f ∧
    ρout = ![low0_f, mid0_f + (low1_f * (1 <<< 7)), mid1_f, high1_f + (low2_f * (1 <<< 5)),
               mid2_f, high2_f]

def spec (off0_f off1_f off2_f : Felt) (ρout : Fin 6 → Felt) :=
  IsRangeChecked 9 (ρout 0) →
  IsRangeChecked 9 (ρout 2) →
  IsRangeChecked 9 (ρout 4) →
  ∃ low0 : BitVec 9,
  ∃ mid0 : BitVec 7,
  ∃ low1 : BitVec 2,
  ∃ mid1 : BitVec 9,
  ∃ high1 : BitVec 5,
  ∃ low2 : BitVec 4,
  ∃ mid2 : BitVec 9,
  ∃ high2 : BitVec 3,
    off0_f = (mid0 ++ low0).toNat ∧
    off1_f = (high1 ++ mid1 ++ low1).toNat ∧
    off2_f = (high2 ++ mid2 ++ low2).toNat ∧
    ρout = ![(low0.toNat : Felt), (low1 ++ mid0).toNat, mid1.toNat, (low2 ++ high1).toNat, mid2.toNat,
             high2.toNat]

theorem sound {off0_f off1_f off2_f : Felt} {ρout : Fin 6 → Felt}
    (hspec: spec_auto off0_f off1_f off2_f ρout) :
    spec off0_f off1_f off2_f ρout := by
  rcases hspec with ⟨low0_f, mid0_f, h1, low1_f, mid1_f, high1_f, h2, low2_f, mid2_f,
    high2_f, h3,
      ⟨n_mid0, n_mid0_lt, rfl⟩,
      ⟨n_low1, n_low1_lt, rfl⟩,
      ⟨n_high1, n_high1_lt, rfl⟩,
      ⟨n_low2, n_low2_lt, rfl⟩,
      ⟨n_high2, n_high2_lt, rfl⟩,
      ρout_eq⟩
  have ρout0_eq : ρout 0 = low0_f := by
    rw [ρout_eq]; rfl
  have ρout2_eq : ρout 2 = mid1_f := by
    rw [ρout_eq]; rfl
  have ρout4_eq : ρout 4 = mid2_f := by
    rw [ρout_eq]; rfl
  intro hρout0 hρout2 hρout4
  rcases hρout0 with ⟨n_low0, n_low0_lt, n_low0_eq⟩
  rcases hρout2 with ⟨n_mid1, n_mid1_lt, n_mid1_eq⟩
  rcases hρout4 with ⟨n_mid2, n_mid2_lt, n_mid2_eq⟩
  use n_low0, n_mid0, n_low1, n_mid1, n_high1, n_low2, n_mid2, n_high2
  simp only [Nat.reduceAdd, BitVec.natCast_eq_ofNat, Nat.succ_eq_add_one, BitVec.toNat_ofNat,
    Nat.reducePow]
  rw [←eq_of_sub_eq_zero h1, ←eq_of_sub_eq_zero h2, ←eq_of_sub_eq_zero h3, ρout_eq]
  constructor
  . rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n_mid0_lt,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt n_low0_lt]
    rw [Nat.shiftLeft_eq n_mid0, mul_comm n_mid0, ←Nat.two_pow_add_eq_or_of_lt n_low0_lt, mul_comm]
    rw [←ρout0_eq, n_low0_eq]
    simp; ring
  constructor
  . rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt n_low1_lt, Nat.mod_eq_of_lt n_mid1_lt,
      Nat.mod_eq_of_lt n_high1_lt]
    simp only [Nat.shiftLeft_eq]
    rw [mul_comm n_high1, ←Nat.two_pow_add_eq_or_of_lt n_mid1_lt, one_mul, mul_comm _ (2^2), ←Nat.two_pow_add_eq_or_of_lt n_low1_lt, ←ρout2_eq,
      n_mid1_eq]
    simp; ring
  constructor
  . rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt n_high2_lt, Nat.mod_eq_of_lt n_mid2_lt,
      Nat.mod_eq_of_lt n_low2_lt]
    simp only [Nat.shiftLeft_eq, one_mul]
    rw [mul_comm n_high2, ←Nat.two_pow_add_eq_or_of_lt n_mid2_lt, mul_comm _ (2^4), ←Nat.two_pow_add_eq_or_of_lt n_low2_lt, ←ρout4_eq,
      n_mid2_eq]
    simp; ring
  ext i; fin_cases i <;> simp
  . simp at n_low0_lt
    rw [Nat.mod_eq_of_lt n_low0_lt, ←ρout0_eq, n_low0_eq]
  . rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n_low1_lt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt n_mid0_lt]
    simp only [Nat.shiftLeft_eq]
    rw [mul_comm n_low1, ←Nat.two_pow_add_eq_or_of_lt n_mid0_lt]
    simp; ring
  . simp at n_mid1_lt
    rw [Nat.mod_eq_of_lt n_mid1_lt, ←ρout2_eq, n_mid1_eq]
  . rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt n_low2_lt, Nat.mod_eq_of_lt n_high1_lt]
    simp only [Nat.shiftLeft_eq]
    rw [mul_comm n_low2, ←Nat.two_pow_add_eq_or_of_lt n_high1_lt]
    simp; ring
  . simp at n_mid2_lt
    rw [Nat.mod_eq_of_lt n_mid2_lt, ←ρout4_eq, n_mid2_eq]
  simp at n_high2_lt
  rw [Nat.mod_eq_of_lt n_high2_lt]

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (off0_f off1_f off2_f : FeltExpr) :
    let ⟨new_ab, new_lt, ρout⟩ := EncodeOffsets.call ab lt off0_f off1_f off2_f
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (off0_f.eval varAssign) (off1_f.eval varAssign) (off2_f.eval varAssign)
        (fun i => (ρout i).eval varAssign) := by
  unfold call ; lift_lets
  intro state1 ab0 low0_f state2 ab1 mid0_f new_off0_f ab2
    state3 ab3 low1_f state4 ab4 mid1_f state5 ab5 high1_f new_off1_f ab6
    state7 ab7 low2_f state8 ab8 mid2_f state9 ab9 high2_f new_off2_f ab10
    lt1 lt2 lt3 lt4 lt5
  intro hab10 hlt5
  have ⟨hrc5, hlt4⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt5
  have ⟨hrc4, hlt3⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt4
  have ⟨hrc3, hlt2⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt3
  have ⟨hrc2, hlt1⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt2
  have ⟨hrc1, hlt⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt1

  have ⟨hab9, h_new_off2_f⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab10
  have hab8 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab9
  have hab7 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab8
  have hab6 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab7
  have ⟨hab5, h_new_off1_f⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab6
  have hab4 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab5
  have hab3 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab4
  have hab2 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab3
  have ⟨hab1, h_new_off0_f⟩ := (AirBuilder.constrain_SatisfiedBy _ _ varAssign).mp hab2
  have hab0 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab1
  have hab := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab0

  use hab, hlt
  apply sound

  use low0_f.eval varAssign, mid0_f.eval varAssign
  intro new_off0_f
  use h_new_off0_f
  use low1_f.eval varAssign, mid1_f.eval varAssign, high1_f.eval varAssign
  intro new_off1_f
  use h_new_off1_f
  use low2_f.eval varAssign, mid2_f.eval varAssign, high2_f.eval varAssign
  intro new_off2_f
  use h_new_off2_f
  use hrc1, hrc2, hrc3, hrc4, hrc5
  exact List.ofFn_inj.mp rfl

lemma NoYieldTerms_of_call
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {offset0 offset1 offset2 : FeltExpr} :
    AirLookupTerms.NoYieldTerms (call ab lt offset0 offset1 offset2).2.1 := by
  unfold call AirLookupTerms.add_rc
  simp only [←AirLookupTerms.add'_eq_add]
  apply AirLookupTerms.add'_NoYieldTerms.mpr
  repeat
    simp ; apply AirLookupTerms.add'_NoYieldTerms.mpr
  simp [h]

end EncodeOffsets
