import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.AirFn
import Verification.Semantics.Util

-- TODO(Jeremy): move these

theorem Zmod.cast_inj_of_lt_char {n : Nat} {i j : ℤ}
    (h : (i : ZMod n) = (j : ZMod n)) (h' : abs (j - i) < n) : i = j :=
  Int.cast_inj_of_lt_char (ZMod.charP n) h h'

theorem Felt252_cast_inj_of_lt_char {i j : ℤ}
    (h : (i : Felt252) = (j : Felt252)) (h' : abs (j - i) < Felt252Prime) : i = j :=
  Int.cast_inj_of_lt_char (ZMod.charP Felt252Prime) h h'

theorem Felt_cast_inj_of_lt_char {i j : ℤ}
    (h : (i : Felt) = (j : Felt)) (h' : abs (j - i) < Stwo.P) : i = j :=
  Int.cast_inj_of_lt_char (ZMod.charP Stwo.P) h h'

theorem Fin.castLE_last {n : Nat} (i : Fin n) (h : i.val + 1 ≤ n):
    Fin.castLE h (Fin.last i) = i := rfl

namespace VerifyAdd252

def call [Fact (Nat.Prime Stwo.P)] (ab : AirBuilder) (a b c : Felt252Expr) : AirBuilder :=
  let aux1 := ab.deduce
  let ab1 := aux1.1
  let sub_p_bit := aux1.2
  let ab2 := ab1.constrain (sub_p_bit * (sub_p_bit - FeltExpr.const 1))
  let aux2 :=
    Fin.hIterate (P := fun _ => AirBuilder × FeltExpr)
      (init := (ab2, FeltExpr.const 0))
      (n := FELT252_N_WORDS - 1)
      (f := fun i p1 =>
        let ab := p1.1
        let prev_carry := p1.2
        let carry := a i.castSucc + b i.castSucc + prev_carry - c i.castSucc -
          FeltExpr.const (P_FELTS[i]) * sub_p_bit
        let p2 := ab.letForConstraint (carry * FeltExpr.const (1 / (1 <<< FELT252_BITS_PER_WORD)))
        let ab := p2.1
        let carry := p2.2
        let ab := ab.constrain (carry * (carry * carry - FeltExpr.const 1))
        (ab, carry))
  let ab3 := aux2.1
  let carry := aux2.2
  let i : Fin (FELT252_N_WORDS) := @Fin.last (FELT252_N_WORDS - 1)
  ab3.constrain (a i + b i + carry - c i - FeltExpr.const (P_FELTS[i]) * sub_p_bit)

def spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
  ∃ sub_p_bit : Felt,
    sub_p_bit * (sub_p_bit - 1) = 0 ∧
  ∃ prev_carry : Felt252Words,
    prev_carry 0 = 0 ∧
    (∀ i : Fin (FELT252_N_WORDS - 1),
      let carry' := a i.castSucc + b i.castSucc + prev_carry i.castSucc - c i.castSucc -
        P_FELTS[i.castSucc] * sub_p_bit
      let carry := carry' * (1 / (1 <<< FELT252_BITS_PER_WORD))
      carry * (carry * carry - 1) = 0 ∧
      prev_carry i.succ = carry) ∧
    let i : Fin FELT252_N_WORDS := @Fin.last (FELT252_N_WORDS - 1)
    a i + b i + prev_carry i - c i - (P_FELTS[i]) * sub_p_bit = 0

def spec (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
    ∀ an bn cn : Felt252Nats,
      an.IsRangeChecked a → bn.IsRangeChecked b → cn.IsRangeChecked c →
      an.eval + bn.eval = cn.eval

-- TODO(Jeremy): see if we can speed this up or break it up to avoid increasing `maxHeartbeats`
set_option maxHeartbeats 250000
theorem spec_of_spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] (hspec : spec_auto a b c) :
    spec a b c := by
  intro an bn cn han hbn hcn
  rcases hspec with ⟨sub_p_bit, hsub_p_bit, prev_carry, hprev_carry0, hmain, hlast⟩
  rw [mul_eq_zero] at hsub_p_bit
  rw [an.eval_eq_of_IsRangeChecked _ han, bn.eval_eq_of_IsRangeChecked _ hbn,
    cn.eval_eq_of_IsRangeChecked _ hcn]
  rw [←Nat.cast_add]
  have h1 : ∀ i : Fin FELT252_N_WORDS,
      prev_carry i = 0 ∨ prev_carry i = 1 ∨ prev_carry i = -1 := by
    intro i
    rcases i.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
    . left; assumption
    . have : ∃ c, c * (c * c - 1) = 0 ∧ prev_carry j.succ = c := by
        constructor; apply hmain
      rcases this with ⟨c, hc1, rfl⟩
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hc1 with hc1 | hc1
      . left; assumption
      . have : (prev_carry j.succ + 1) * (prev_carry j.succ - 1) = 0 := by rw [←hc1]; ring
        rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
        . right; right
          apply eq_neg_of_add_eq_zero_left h
        . right; left
          apply eq_of_sub_eq_zero h
  have h2 : ∀ i : Fin (FELT252_N_WORDS - 1),
      prev_carry i.succ =
        (a i.castSucc + b i.castSucc + prev_carry i.castSucc - c i.castSucc -
            P_FELTS[i.castSucc] * sub_p_bit) *
          ((1 / (1 <<< FELT252_BITS_PER_WORD))) := by
    intro i
    exact hmain i |>.2
  have h2' : ∀ i : Fin (FELT252_N_WORDS - 1),
      prev_carry i.succ * 2^FELT252_BITS_PER_WORD =
        (a i.castSucc + b i.castSucc + prev_carry i.castSucc -
            c i.castSucc - P_FELTS[i.castSucc] * sub_p_bit) := by
    intro i
    rw [←eq_div_iff_mul_eq]; swap; simp [FELT252_BITS_PER_WORD]
    . apply Ring.two_ne_zero
      simp [Felt, ZMod.ringChar_zmod_n, Stwo.P]
    convert h2 _ using 1
    rw [Nat.cast_one, Nat.one_shiftLeft, mul_one_div]
    simp
  let carryAux (i : Felt) : Int :=
    if i = 1 then 1 else
      if i = -1 then -1 else 0
  have cast_carryAux (i : Fin FELT252_N_WORDS) :
      ↑(carryAux (prev_carry i)) = prev_carry i := by
    simp [carryAux]
    rcases h1 i with h' | h' | h' <;> simp [h']
    simp [Felt]
    rw [@neg_one_eq_one_iff, ZMod.ringChar_zmod_n]
    simp [Stwo.P]
  let carry_z (i : Fin (FELT252_N_WORDS + 1)) : Int :=
    i.lastCases 0 fun j => carryAux (prev_carry j)
  have cast_carry_z (i : Fin FELT252_N_WORDS) :
    prev_carry i = ↑(carry_z i.castSucc) := by
      simp [carry_z, cast_carryAux]
  have hcarry_z_aux : ∀ i, |carry_z i| = 0 ∨ |carry_z i| = 1 := by
    intro i
    rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    . simp [carry_z, carryAux]
      split <;> simp
      split <;> simp
      assumption
    . simp [carry_z]
  have abs_carry_z_le : ∀ i, |carry_z i| ≤ 1 := by
    intro i
    rcases hcarry_z_aux i with h' | h' <;> simp [h']
  let sub_p_bit_z : Int := if sub_p_bit = 1 then 1 else 0
  have cast_sub_p_bit_z : sub_p_bit = ↑sub_p_bit_z := by
    simp [sub_p_bit_z]
    rcases hsub_p_bit with rfl | h
    . simp
    rw [eq_of_sub_eq_zero h]; simp
  have abs_sub_p_bit_z_le : |sub_p_bit_z| ≤ 1 := by
    simp [sub_p_bit_z]; split <;> simp
  have hh : ∀ j, |↑(an j) + ↑(bn j) + carry_z j.castSucc - ↑(cn j) -
        ↑P_FELTS[j] * sub_p_bit_z -
      carry_z j.succ * 2 ^ FELT252_BITS_PER_WORD| < ↑Stwo.P := by
    intro j
    apply lt_of_le_of_lt
    show _ ≤ 2^9 + 2^9 + 1 + 2^9 + 256 * 1 + 1 * 2^9
    . apply le_trans
      apply abs_sub
      apply add_le_add; swap
      . rw [abs_mul]
        apply Int.mul_le_mul_of_nonneg_right (abs_carry_z_le j.succ)
        simp
      apply le_trans
      apply abs_sub
      apply add_le_add; swap
      . rw [abs_mul]
        refine mul_le_mul ?_ abs_sub_p_bit_z_le (by simp) (by simp)
        simp; apply P_FELTS_le
      apply le_trans
      apply abs_sub
      apply add_le_add; swap
      . simp only [Int.abs_natCast, Int.reducePow,  Nat.cast_le_ofNat]
        apply le_of_lt (hcn _ |>.2)
      apply le_trans
      apply abs_add
      apply add_le_add; swap
      . apply abs_carry_z_le
      apply le_trans
      apply abs_add
      apply add_le_add
      . simp only [Int.abs_natCast, Int.reducePow,  Nat.cast_le_ofNat]
        apply le_of_lt (han _ |>.2)
      . simp only [Int.abs_natCast, Int.reducePow,  Nat.cast_le_ofNat]
        apply le_of_lt (hbn _ |>.2)
    simp [Stwo.P]
  have h3 : ∀ i : Fin FELT252_N_WORDS,
      carry_z i.succ * 2^FELT252_BITS_PER_WORD =
        (an i + bn i + carry_z i.castSucc -
          cn i - P_FELTS[i] * sub_p_bit_z) := by
    intro i
    rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    . apply Felt_cast_inj_of_lt_char
      . rw [Fin.succ_castSucc]
        simp [-Fin.castSucc_succ, ←cast_carry_z, ←cast_sub_p_bit_z]
        have := cast_carry_z j.castSucc
        have := h2' j
        convert h2' j
        . symm; apply han _ |>.1
        . symm; apply hbn _ |>.1
        . symm; apply hcn _ |>.1
      apply hh
    . simp [Fin.coe_ofNat_eq_mod]
      apply Felt_cast_inj_of_lt_char
      . have : ↑(carry_z 28) = 0 := by
          simp [carry_z]
          apply Fin.lastCases_last
        rw [this, zero_mul]
        simp [FELT252_N_WORDS] at hlast
        simp [←cast_sub_p_bit_z]
        rw [show a = fun i => ↑(an i) from funext (han . |>.1)] at hlast
        rw [show b = fun i => ↑(bn i) from funext (hbn . |>.1)] at hlast
        rw [show c = fun i => ↑(cn i) from funext (hcn . |>.1)] at hlast
        rw [cast_carry_z] at hlast; simp at hlast
        exact hlast.symm
      apply hh
  have h4 : ∀ k : Fin (FELT252_N_WORDS + 1),
      ∑ i : Fin (k.val), (an (i.castLE (Nat.le_of_lt_succ k.isLt)) +
          bn (i.castLE (Nat.le_of_lt_succ k.isLt))) * 2^(FELT252_BITS_PER_WORD * i) =
        ∑ i : Fin (k.val), ((cn (i.castLE (Nat.le_of_lt_succ k.isLt)) +
            sub_p_bit_z * P_FELTS[i.castLE (Nat.le_of_lt_succ k.isLt)]) *
              2^(FELT252_BITS_PER_WORD * i)) +
            carry_z k * 2^(FELT252_BITS_PER_WORD * k) := by
    intro k
    refine k.induction ?_ ?_
    . simp [carry_z]
      have : NeZero (FELT252_N_WORDS - 1) := by simp [FELT252_N_WORDS]; infer_instance
      rw [←Fin.castSucc_zero, Fin.lastCases_castSucc]
      simp [carryAux, hprev_carry0]
    intro i ih
    simp only [Fin.coe_castSucc, Fin.getElem_fin, Fin.coe_castLE, Fin.val_succ] at ih ⊢
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Nat.cast_add, Nat.cast_mul, Nat.cast_add]
    simp only [Fin.castLE_castSucc, Fin.coe_castSucc, Fin.val_last] at ih ⊢
    rw [ih, add_assoc, add_assoc]
    congr 1
    simp only [mul_add, pow_add, mul_one]
    rw [mul_comm (2 ^ _), ←mul_assoc, h3]
    simp [Fin.castLE_last]
    ring
  have h5 := h4 (Fin.last FELT252_N_WORDS)
  simp only [Fin.val_last, Fin.castLE_rfl, id_eq, Fin.lastCases_last, zero_mul, add_zero,
    Fin.getElem_fin, carry_z, carryAux, add_mul, Finset.sum_add_distrib] at h5
  rw [show a = fun i => ↑(an i) from funext (han . |>.1)]
  rw [show b = fun i => ↑(bn i) from funext (hbn . |>.1)]
  rw [show c = fun i => ↑(cn i) from funext (hcn . |>.1)]
  dsimp
  have ha : ∀ i, ZMod.val (↑(an i) : Felt) = an i := by
    intro i
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    apply lt_of_lt_of_le (han i).2
    simp [Stwo.P]
  have hb : ∀ i, ZMod.val (↑(bn i) : Felt) = bn i := by
    intro i
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    apply lt_of_lt_of_le (hbn i).2
    simp [Stwo.P]
  have hc : ∀ i, ZMod.val (↑(cn i) : Felt) = cn i := by
    intro i
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    apply lt_of_lt_of_le (hcn i).2
    simp [Stwo.P]
  simp only [ha, hb, hc]
  have : ∀ x : Nat, (↑x : Felt252) = (↑(↑x : ℤ) : Felt252) := by simp
  rw [this, h5]
  dsimp [sub_p_bit_z]
  split
  . rw [Int.cast_add, Int.cast_sum, Nat.cast_sum]
    simp; decide
  . simp only [zero_mul]
    rw [Finset.sum_const_zero, add_zero]
    rw [Int.cast_sum, Nat.cast_sum]
    simp

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (a b c : Felt252Expr) :
    let new_ab := call ab a b c
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (a.eval varAssign) (b.eval varAssign) (c.eval varAssign) := by
  intro new_ab hnew_ab
  let aux1 := ab.deduce
  let ab1 := aux1.1
  let sub_p_bit := aux1.2
  let ab2 := ab1.constrain (sub_p_bit * (sub_p_bit - FeltExpr.const 1))
  let aux2 :=
    Fin.hIterate (P := fun _ => AirBuilder × FeltExpr)
      (init := (ab2, FeltExpr.const 0))
      (n := FELT252_N_WORDS - 1)
      (f := fun i p1 =>
        let iab1 := p1.1
        let prev_carry1 := p1.2
        let carry1 := a i.castSucc + b i.castSucc + prev_carry1 - c i.castSucc -
          FeltExpr.const (P_FELTS[i]) * sub_p_bit
        let p2 := iab1.letForConstraint
          (carry1 * FeltExpr.const ((1 : Felt) / (1 <<< FELT252_BITS_PER_WORD)))
        let iab2 := p2.1
        let carry2 := p2.2
        let iab3 := iab2.constrain (carry2 * (carry2 * carry2 - FeltExpr.const 1))
        (iab3, carry2))
  let ab3 := aux2.1
  let carry := aux2.2
  let i : Fin (FELT252_N_WORDS) := @Fin.last (FELT252_N_WORDS - 1)
  have ⟨hab3, h3⟩ : ab3.SatisfiedBy varAssign ∧
      (a i + b i + carry - c i - FeltExpr.const (P_FELTS[i]) * sub_p_bit).eval varAssign = 0 := by
    apply ab3.constrain_SatisfiedBy _ varAssign |>.mp hnew_ab
  let Q (i : Nat) (p : AirBuilder × FeltExpr) :=
    (h : i ≤ FELT252_N_WORDS - 1) →
    p.1.SatisfiedBy varAssign →
      ab2.SatisfiedBy varAssign ∧
      ∃ prev_carries : Fin i.succ → Felt,
        prev_carries 0 = 0 ∧
        (∀ j : Fin i,
          let carry' : Felt := (a (Fin.castLE h j).castSucc |>.eval varAssign) +
                (b (Fin.castLE h j).castSucc |>.eval varAssign) +
              (prev_carries j.castSucc) - (c (Fin.castLE h j).castSucc |>.eval varAssign)
               - P_FELTS[(Fin.castLE h j)] * (sub_p_bit.eval varAssign)
          let carry := carry' * (1 / (1 <<< FELT252_BITS_PER_WORD))
          carry * (carry * carry - 1) = 0 ∧
          prev_carries j.succ = carry) ∧
        (prev_carries (Fin.last i) = p.2.eval varAssign)
  have haux2 : Q (FELT252_N_WORDS - 1) aux2 := by
    apply Fin.hIterate_elim
    . simp [Q]
      intro h
      use h, (fun _ => 0)
    rintro i ⟨ab, prev_carry⟩ ih h'
    specialize ih (le_trans (Nat.le_succ _) h')
    lift_lets
    intro iab1 prev_carry1; dsimp -zeta [iab1, prev_carry1]
    rintro carry1 p2 iab2 carry2 iab3 hiab3
    have ⟨hiab2, hc⟩ := iab2.constrain_SatisfiedBy _ varAssign |>.mp hiab3
    have ⟨hiab1, hc'⟩ := iab1.constrain_SatisfiedBy _ varAssign |>.mp hiab2
    specialize ih hiab1
    rcases ih with ⟨hab2, prev_carries, hprev_carry_0, hcarry, hcarry_last⟩
    use hab2, Fin.snoc prev_carries (carry2.eval varAssign)
    constructor
    . rw [←Fin.castSucc_zero, Fin.snoc_castSucc, hprev_carry_0]
    constructor
    . intro j carry' carry
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      . constructor
        . dsimp [carry, carry']
          rw [Fin.snoc_castSucc]
          apply hcarry j |>.1
        . rw [Fin.succ_castSucc, Fin.snoc_castSucc]
          convert hcarry j |>.2 using 1
          dsimp [carry, carry']
          rw [Fin.snoc_castSucc]
      . have carry_eq : carry = FeltExpr.eval varAssign carry2 := by
          simp only [FeltExpr.eval_sub, FeltExpr.eval_mul, FeltExpr.eval_const] at hc'
          convert (eq_of_sub_eq_zero hc').symm
          dsimp [carry', carry1]
          rw [Fin.snoc_castSucc]
          congr 3
        constructor
        . simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const] at hc
          rw [carry_eq, hc]
        . rw [Fin.succ_last, Fin.snoc_last, carry_eq]
    rw [Fin.snoc_last]
  have ⟨hab2, prev_carries, hpc0, hpcj, hpclast⟩ := haux2 (le_refl (FELT252_N_WORDS - 1)) hab3
  have ⟨hab1, h1⟩  : ab1.SatisfiedBy varAssign ∧
      ((sub_p_bit * (sub_p_bit - FeltExpr.const 1)).eval varAssign = 0) :=
    ab1.constrain_SatisfiedBy _ varAssign |>.mp hab2
  have hab := ab.deduce_SatisfiedBy varAssign |>.mp hab1
  use hab
  apply spec_of_spec_auto
  use sub_p_bit.eval varAssign
  constructor
  . simp [-mul_eq_zero] at h1
    exact h1
  use prev_carries, hpc0, hpcj
  convert h3
  dsimp [i]
  simp [Felt252Expr.eval]
  exact hpclast

end VerifyAdd252
