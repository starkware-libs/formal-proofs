
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Expressions.Felt252Expr

open Fin.NatCast

namespace EncodeFlags

def call (airBuilder : AirBuilder) (flags : Fin 15 → FeltExpr) : AirBuilder × FeltExpr × FeltExpr :=
  let ab1 :=
    forLoop 0 15 airBuilder fun i ab =>
      ab.constrain (flags i * (FeltExpr.const 1 - flags i))
  let felt5 :=
    forLoop 0 6 (FeltExpr.const 0) fun i felt =>
      felt + (flags i * FeltExpr.const (1 <<< (i + 3)))
  let felt6 :=
    forLoop 0 9 (FeltExpr.const 0) fun i felt =>
      felt + (flags (i + 6) * FeltExpr.const (1 <<< i))
  (ab1, felt5, felt6)

def spec_auto (flags : Fin 15 → Felt) (ρfelt5 ρfelt6 : Felt) : Prop :=
  (∀ i, flags i * (1 - flags i) = 0) ∧
  ρfelt5 = ∑ i ∈ Finset.range 6, flags i * (1 <<< (i + 3)) ∧
  ρfelt6 = ∑ i ∈ Finset.range 9, flags ↑(i + 6) * (1 <<< i)

def spec (flags_f : Fin 15 → Felt) (ρfelt5 ρfelt6 : Felt) : Prop :=
  ∃ flags : Fin 15 → Bool,
    (∀ i, flags_f i = (flags i).toNat) ∧
    ρfelt5 = ∑ i ∈ Finset.range 6, (flags i).toNat * (1 <<< (i + 3)) ∧
    ρfelt6 = ∑ i ∈ Finset.range 9, (flags ↑(i + 6)).toNat * (1 <<< i)

theorem spec_sound [Fact (Nat.Prime Stwo.P)] {flags : Fin 15 → Felt} {ρfelt5 ρfelt6 : Felt}
    (hspec: spec_auto flags ρfelt5 ρfelt6) :
    spec flags ρfelt5 ρfelt6 := by
  rcases hspec with ⟨h1, h2, h3⟩
  use fun i => flags i |>.toBool
  simp [←Bool.toFelt_eq, Felt.toBool_toFelt, h1]
  use h2, h3

lemma aux1 [Fact (Nat.Prime Stwo.P)] (varAssign : VarAssign) (flags : Fin 15 → FeltExpr) :
  (forLoop 0 6 (FeltExpr.const 0) fun i felt =>
      felt + (flags ↑i * FeltExpr.const (1 <<< (i + 3)))).eval varAssign =
    ∑ i ∈ Finset.range 6, (flags ↑(i : Nat)).eval varAssign * (1 <<< (i + 3)) := by
  let Invariant : Nat → FeltExpr → Prop := fun i felt =>
    felt.eval varAssign = ∑ j ∈ Finset.range i, (flags ↑(j : Nat)).eval varAssign * (1 <<< (j + 3))
  show Invariant 6 (forLoop 0 6 (FeltExpr.const 0) fun i felt =>
      felt + (flags i * FeltExpr.const (1 <<< (i + 3))))
  apply forLoopCorrect
  . norm_num
  . rfl
  . rintro i - - e he
    unfold Invariant at *;
    simp [he, Finset.sum_range_succ]

lemma aux2 [Fact (Nat.Prime Stwo.P)] (varAssign : VarAssign) (flags : Fin 15 → FeltExpr) :
  (forLoop 0 9 (FeltExpr.const 0) fun i felt =>
      felt + (flags (i + 6) * FeltExpr.const (1 <<< i))).eval varAssign =
    ∑ i ∈ Finset.range 9, (flags (i + 6)).eval varAssign * (1 <<< i) := by
  let Invariant : Nat → FeltExpr → Prop := fun i felt =>
    felt.eval varAssign = ∑ j ∈ Finset.range i, (flags (j + 6)).eval varAssign * (1 <<< j)
  show Invariant 9 (forLoop 0 9 (FeltExpr.const 0) fun i felt =>
      felt + (flags (i + 6) * FeltExpr.const (1 <<< i)))
  apply forLoopCorrect
  . norm_num
  . rfl
  . rintro i - - e he
    unfold Invariant at *;
    simp [he, Finset.sum_range_succ]

theorem sound_auto [Fact (Nat.Prime Stwo.P)]
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (flags : Fin 15 → FeltExpr) :
    let ⟨new_ab, felt5, felt6⟩ := call ab flags
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (fun i => (flags i).eval varAssign)
        (felt5.eval varAssign) (felt6.eval varAssign) := by
  simp only [call]
  intro h1
  let Invariant : Nat → AirBuilder → Prop := fun i ab' =>
    ab'.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
        ∀ j < i, (h : j < 15) →
          (flags ⟨j, h⟩).eval varAssign * (1 - (flags ⟨j, h⟩).eval varAssign) = 0
  have : Invariant 15 (forLoop 0 15 ab fun i ab' =>
           ab'.constrain (flags i * (FeltExpr.const 1 - flags i))) := by
    apply (forLoopCorrect 0 15 ab _ (by norm_num) Invariant)
    . intro h; use h; simp
    rintro j - hj ab' hab' h1
    simp only [AirBuilder.constrain_SatisfiedBy, FeltExpr.eval_mul, FeltExpr.eval_sub,
      FeltExpr.eval_const] at h1
    specialize hab' h1.1
    use hab'.1
    intro i ilt h
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ilt) with ilt | rfl
    . apply hab'.2 i ilt
    convert h1.2 <;> simp [Nat.mod_eq_of_lt hj]
  specialize this h1
  use this.1
  apply spec_sound
  simp only [spec_auto]
  refine ⟨?_, aux1 _ _, aux2 _ _⟩
  convert this.2
  constructor
  . intro h j jlt _
    apply h ⟨j, jlt⟩
  intro h i
  apply h _ (Fin.is_lt _)

end EncodeFlags
