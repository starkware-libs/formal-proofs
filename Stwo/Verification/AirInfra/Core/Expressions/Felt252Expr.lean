import Verification.AirInfra.Core.Expressions.Expr

-- TODO(Jeremy): rewrite some of these in terms of `eval_poly`.
-- Also: reconcile `eval_poly` with `Nat.ofDigits`, which is a version restrited on nats.

def Felt252Expr := Fin FELT252_N_WORDS → FeltExpr

/-
Semantics.
-/

def Felt252Words := Fin FELT252_N_WORDS → Felt

def Felt252Nats := Fin FELT252_N_WORDS → Nat

def Felt252Ints := Fin FELT252_N_WORDS → Int

namespace Felt252Expr

variable [Fact (Nat.Prime Stwo.P)]

def eval (varAssign : VarAssign) : Felt252Expr → Felt252Words :=
  fun expr i => (expr i).eval varAssign

end Felt252Expr

def Felt252Prime : Nat := 2^251 + 17 * 2^192 + 1

def Felt252 := ZMod Felt252Prime

def Felt252_Felts_list : List Felt := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 136, 0, 0, 0, 0, 0, 256]

def Felt252_Felts : Felt252Words :=
  fun i =>
    match Felt252_Felts_list[i]? with
    | some v => v
    | none   => 0

instance : CommRing Felt252 := by rw [Felt252]; infer_instance

instance : DecidableEq Felt252 := by rw [Felt252]; infer_instance

instance [Fact (Nat.Prime Felt252Prime)] : Field Felt252 := by rw [Felt252]; infer_instance

/-- Casting a CasmAddressVal to a Felt252 -/
def Felt.toFelt252 (x : Felt) : Felt252 := (x + ↑((2^29 + 1):Nat)).val - (2^29 + 1)
-- def Felt.toFelt252 (x : Felt) : Felt252 := (x + ↑((2 : Nat )^27)).val - 2^27

theorem toFelt252_add {n a : Nat} (h : n + a < Stwo.P - 2^29 - 1) : -- ?
    ((↑n : Felt) + ↑a).toFelt252 =
    (↑n : Felt).toFelt252 + ↑a := by
  simp only [Felt.toFelt252, ←Nat.cast_add]
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
  . simp [Nat.cast_add] at *; ring
  omega; omega

theorem toFelt252_sub {n a : Nat} (h : a ≤ n + (2^29 + 1)) (h' : n < Stwo.P  - 2^29 -1) : ((↑n : Felt) - ↑a).toFelt252 =
    (↑n : Felt).toFelt252 - ↑a := by
  unfold Felt.toFelt252
  rw [sub_add_eq_add_sub, ←Nat.cast_add, ←Nat.cast_sub h]
  repeat rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; swap; omega
  rw [Nat.cast_sub h]
  abel

theorem toFelt.of_lt {n : Nat} (h : n < Stwo.P  - 2^29 -1) : (↑n : Felt).toFelt252 = ↑n := by --
  simp only [Felt.toFelt252, ←Nat.cast_add]
  repeat rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; swap; omega
  simp [Nat.cast_add]
  norm_num

theorem toFelt.neg_of_lt {n : Nat} (h : n ≤ 2^29 + 1): (-(↑n : Felt)).toFelt252 = - ↑n := by
  have h1 : n ≤ 0 + (2^29 + 1) := by omega
  have h2 : 0 < Stwo.P - 2^29 -1 := by
    unfold Stwo.P
    norm_num
  have := toFelt252_sub h1 h2
  simp at this
  rw[this]
  simp
  unfold Felt.toFelt252
  rw[zero_add, ZMod.val_natCast_of_lt]
  norm_num
  unfold Stwo.P
  norm_num


theorem toFelt252_add' {n a : Nat} (h : n + a < Stwo.P  - 2^29 -1) : ((↑n : Felt) + ↑a).toFelt252 =
    ↑n + ↑a := by
  simp only [Felt.toFelt252, ←Nat.cast_add]
  repeat rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; swap; omega
  simp [Nat.cast_add]
  norm_num

-- theorem toFelt252_add'' {n a : Nat} (h : n < Stwo.P  - 2^29) (h2: a < 2^29) : ((↑n : Felt) + ↑a).toFelt252 =
--     ↑n + ↑a := by
--   simp only [Felt.toFelt252, ←Nat.cast_add]
--   repeat rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; swap; omega
--   simp [Nat.cast_add]
--   norm_num
--   #check ZMod.val_cast_of_lt

theorem toFelt252_sub' {n a : Nat} (h : a ≤ n + (2^29 +1)) (h' : n < Stwo.P  - 2^29 -1) : ((↑n : Felt) - ↑a).toFelt252 =
    ↑n - ↑a := by
  unfold Felt.toFelt252
  rw [sub_add_eq_add_sub, ←Nat.cast_add, ←Nat.cast_sub h]
  repeat rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; swap; omega
  rw [Nat.cast_sub h, Nat.cast_add]
  ring_nf

-- theorem toFelt252_add_small {an bn : Nat} (han : (an ≤ (2^29 - 1) ∨ ((an < Stwo.P)∧(an ≥ Stwo.P - 2^29 - 1)))) (h' : n < Stwo.P  - 2^29 -1) : ((↑n : Felt) - ↑a).toFelt252 =
--     ↑n - ↑a := by

theorem toFelt252_add_small {a b : Felt} (ha : a.val ≤ (2^29 - 1) ∨ (a.val ≥ Stwo.P - 2^29 - 1))
  (hb : b.val ≤ (2^29 - 1) ∨ (b.val ≥ Stwo.P - 2^29 - 1))
  (hc : (a+b).val ≤ (2^29 - 1) ∨ ((a+b).val ≥ Stwo.P - 2^29 - 1)) :
  ((a+b).toFelt252 = a.toFelt252 + b.toFelt252) := by

  have ha_cast : (↑a.val : Felt) = a := by
    simp
    apply ZMod.cast_id
  have hb_cast : (↑b.val : Felt) = b := by
    simp
    apply ZMod.cast_id

  let mb := -b
  have hmb : mb = -b := by rfl
  have hmb2 : b = -mb := by rw [hmb]; ring
  have hmb_cast : (↑mb.val : Felt) = mb := by
    simp
    apply ZMod.cast_id

  let ma := -a
  have hma : ma = -a := by rfl
  have hma2 : a = -ma := by rw [hma]; ring
  have hma_cast : (↑ma.val : Felt) = ma := by
    simp
    apply ZMod.cast_id

  cases ha <;> rename _ => ha2 <;> cases hb <;> rename _ => hb2
  · have h : a.val + b.val < Stwo.P - 2^29 - 1 := by
      calc
        a.val + b.val ≤ (2^29 - 1) + (2^29 - 1) := by omega
        _ = 2^30 - 2 := by norm_num
        _ < Stwo.P - 2^29 - 1 := by
          unfold Stwo.P
          norm_num
    have := toFelt252_add' h
    rw[ha_cast, hb_cast] at this
    rw [this]
    nth_rw 2 [← ha_cast, ← hb_cast]
    rw [toFelt.of_lt (show a.val < Stwo.P - 2^29 -1 by unfold Stwo.P; omega),
        toFelt.of_lt (show b.val < Stwo.P - 2^29 -1 by unfold Stwo.P; omega)]

  · rw [hmb2]
    --have := add_neg' a mb
    ring_nf

    have h1pre : b ≠ 0 := by
      intro hb0
      rw[hb0] at hb2
      unfold Stwo.P at hb2
      norm_num at hb2
    have h1 : NeZero b := ⟨h1pre⟩

    have h2 : mb.val = Stwo.P - b.val := by
      rw [hmb]
      rw [ZMod.val_neg_of_ne_zero b]
    have h3 :mb.val ≤ 2^29 +1 := by
      rw[h2]
      calc
        Stwo.P - ZMod.val b ≤ Stwo.P - (Stwo.P - 2^29 -1) := by omega
        _ = 2^29 +1 := by
          rw [Nat.sub_sub]
          rw [Nat.sub_sub_right, add_comm Stwo.P, Nat.add_sub_cancel]
          unfold Stwo.P
          norm_num
    have h4 : mb.val ≤ a.val + (2^29 +1) := by
      calc
        mb.val ≤ 2^29 +1 := h3
        _ ≤ a.val + (2^29 +1) := by omega
    have h5 : a.val < Stwo.P - 2^29 -1 := by
      unfold Stwo.P
      omega
    have := toFelt252_sub' h4 h5
    rw[ha_cast, hmb_cast] at this
    rw [← toFelt.of_lt h5] at this
    rw[ha_cast] at this
    -- have hmb3 : b.toFelt252 = -(mb.toFelt252) := by --(b + ↑((2^29 + 1):Nat)).val - (2^29 + 1)
    --   unfold Felt.toFelt252
    --   linarith
    rw [this]
    have htmp := toFelt.neg_of_lt h3
    rw[sub_eq_add_neg]
    rw[← htmp, hmb_cast]

  · rw [hma2]
    --have := add_neg' a mb
    ring_nf

    have h1pre : a ≠ 0 := by
      intro ha0
      rw[ha0] at ha2
      unfold Stwo.P at ha2
      norm_num at ha2
    have h1 : NeZero a := ⟨h1pre⟩

    have h2 : ma.val = Stwo.P - a.val := by
      rw [hma]
      rw [ZMod.val_neg_of_ne_zero a]
    have h3 :ma.val ≤ 2^29 +1 := by
      rw[h2]
      calc
        Stwo.P - ZMod.val a ≤ Stwo.P - (Stwo.P - 2^29 -1) := by omega
        _ = 2^29 +1 := by
          rw [Nat.sub_sub]
          rw [Nat.sub_sub_right, add_comm Stwo.P, Nat.add_sub_cancel]
          unfold Stwo.P
          norm_num
    have h4 : ma.val ≤ b.val + (2^29 +1) := by
      calc
        ma.val ≤ 2^29 +1 := h3
        _ ≤ b.val + (2^29 +1) := by omega
    have h5 : b.val < Stwo.P - 2^29 -1 := by
      unfold Stwo.P
      omega
    have := toFelt252_sub' h4 h5
    rw[hb_cast, hma_cast] at this
    rw [← toFelt.of_lt h5] at this
    rw[hb_cast] at this
    rw[add_comm, ← sub_eq_add_neg]
    rw [this]
    have htmp := toFelt.neg_of_lt h3
    rw[sub_eq_add_neg]
    rw[← htmp, hma_cast, add_comm]

  · have h1 : a.val + b.val ≥ Stwo.P := by
      calc
        ZMod.val a + ZMod.val b ≥ (Stwo.P - 2^29 -1) + (Stwo.P - 2^29 -1) := by omega
        _ ≥ Stwo.P := by
          unfold Stwo.P
          norm_num
    -- have h2 : a.val + b.val = (a.val + b.val - Stwo.P) + Stwo.P := by
    --   rw[Nat.sub_add_cancel _]
    --   omega
    have h2 : ZMod.val (↑(ZMod.val a + ZMod.val b) : Felt) = ZMod.val (↑((ZMod.val a + ZMod.val b) - Stwo.P) : Felt) := by
        unfold Felt
        rw[ZMod.val_natCast, ZMod.val_natCast]
        rw[Nat.mod_eq_sub_mod h1]
    have h3 : (ZMod.val a + ZMod.val b) - Stwo.P < Stwo.P := by
      calc
        (ZMod.val a + ZMod.val b) - Stwo.P < (Stwo.P + Stwo.P) - Stwo.P := by
          have htmp1 : ZMod.val a < Stwo.P := by
            apply ZMod.val_lt
          have htmp2 : ZMod.val b < Stwo.P := by
            apply ZMod.val_lt
          omega
        _ = Stwo.P := by norm_num
    have h4 : ZMod.val (↑(ZMod.val a + ZMod.val b) : Felt) = (ZMod.val a + ZMod.val b) - Stwo.P := by
      rw[h2]
      rw[ZMod.val_natCast_of_lt h3]

    cases hc <;> rename _ => hc2
    · absurd hc2
      push_neg
      rw [← ha_cast, ← hb_cast, ← Nat.cast_add, h4]
      calc
        2 ^ 29 - 1 < Stwo.P - 2 ^ 29 - 1 + (Stwo.P - 2 ^ 29 - 1) - Stwo.P := by
          unfold Stwo.P
          norm_num
        _ ≤ (ZMod.val a + ZMod.val b) - Stwo.P := by
          omega

    · unfold Felt.toFelt252
      rw[← add_sub_assoc]
      rw[sub_eq_add_neg, sub_eq_add_neg]
      apply add_right_cancel_iff.mpr

      have htriv1 : ((2 ^ 29 + 1) : Felt) = ↑(2 ^ 29 + 1 : Nat) := by
        rfl

      have h5a : ZMod.val (a + ↑(2 ^ 29 + 1)) = ZMod.val a + (2 ^ 29 + 1) - Stwo.P:= by
        rw[← ha_cast, htriv1, ←Nat.cast_add]
        rw[ZMod.val_natCast]
        rw[ha_cast]
        calc
          (ZMod.val a + (2 ^ 29 + 1)) % Stwo.P = (ZMod.val a + (2 ^ 29 + 1) - Stwo.P) % Stwo.P:= by
            rw[Nat.mod_eq_sub_mod _]
            omega
          _ = ZMod.val a + (2 ^ 29 + 1) - Stwo.P := by
            apply Nat.mod_eq_of_lt
            calc
              ZMod.val a + (2 ^ 29 + 1) - Stwo.P < Stwo.P + (2 ^ 29 + 1) - Stwo.P := by
                have htmp1 : ZMod.val a < Stwo.P := by
                  apply ZMod.val_lt
                omega
              _ = 2 ^ 29 + 1 := by norm_num
              _ < Stwo.P := by
                unfold Stwo.P
                norm_num

      have h5b : ZMod.val (b + ↑(2 ^ 29 + 1)) = ZMod.val b + (2 ^ 29 + 1) - Stwo.P:= by
        rw[← hb_cast, htriv1, ←Nat.cast_add]
        rw[ZMod.val_natCast]
        rw[hb_cast]
        calc
          (ZMod.val b + (2 ^ 29 + 1)) % Stwo.P = (ZMod.val b + (2 ^ 29 + 1) - Stwo.P) % Stwo.P:= by
            rw[Nat.mod_eq_sub_mod _]
            omega
          _ = ZMod.val b + (2 ^ 29 + 1) - Stwo.P := by
            apply Nat.mod_eq_of_lt
            calc
              ZMod.val b + (2 ^ 29 + 1) - Stwo.P < Stwo.P + (2 ^ 29 + 1) - Stwo.P := by
                have htmp1 : ZMod.val b < Stwo.P := by
                  apply ZMod.val_lt
                omega
              _ = 2 ^ 29 + 1 := by norm_num
              _ < Stwo.P := by
                unfold Stwo.P
                norm_num

      rw[← htriv1]
      rw [h5a, h5b]

      have hab_cast : (↑(a + b).val : Felt) = a + b := by
        simp
        apply ZMod.cast_id

      have h6 : ZMod.val (a + b + (2 ^ 29 + 1)) = ZMod.val (a + b) + (2 ^ 29 + 1) - Stwo.P := by
        rw[← hab_cast, htriv1, ←Nat.cast_add]
        rw[ZMod.val_natCast]
        rw[hab_cast]
        calc
          (ZMod.val (a+b) + (2 ^ 29 + 1)) % Stwo.P = (ZMod.val (a+b) + (2 ^ 29 + 1) - Stwo.P) % Stwo.P:= by
            rw[Nat.mod_eq_sub_mod _]
            omega
          _ = ZMod.val (a+b) + (2 ^ 29 + 1) - Stwo.P := by
            apply Nat.mod_eq_of_lt
            calc
              ZMod.val (a+b) + (2 ^ 29 + 1) - Stwo.P < Stwo.P + (2 ^ 29 + 1) - Stwo.P := by
                have htmp1 : ZMod.val (a+b) < Stwo.P := by
                  apply ZMod.val_lt
                omega
              _ = 2 ^ 29 + 1 := by norm_num
              _ < Stwo.P := by
                unfold Stwo.P
                norm_num

      rw[h6]
      rw[Nat.cast_sub]
      rw[Nat.cast_sub]
      rw[Nat.cast_sub]

      rw[← add_sub_assoc]
      rw[sub_eq_add_neg, sub_eq_add_neg]
      apply add_right_cancel_iff.mpr
      --rw[← add_assoc]
      rw[Nat.cast_add]
      nth_rw 3 [Nat.cast_add]
      rw[← add_assoc]
      apply add_right_cancel_iff.mpr
        --rw[Nat.mod_eq_sub_mod h1]
      rw[Nat.cast_add]
      nth_rw 2 [sub_eq_add_neg]
      rw [add_assoc]
      nth_rw 4 [add_comm]
      rw [← add_assoc]

      have htriv2 : ((2 ^ 29 + 1) : Felt252) = ↑(2 ^ 29 + 1 : Nat) := by
        rfl

      rw[htriv2]
      rw[add_sub_cancel_right]
      rw [add_assoc]
      nth_rw 3 [add_comm]
      rw [←add_assoc]
      rw[← sub_eq_add_neg]

      have h7 : ZMod.val (a + b) = (ZMod.val a + ZMod.val b) - Stwo.P := by
        nth_rw 1 [←ha_cast, ←hb_cast, ←Nat.cast_add]
        rw[ZMod.val_natCast]
        calc
          (ZMod.val a + ZMod.val b) % Stwo.P = (ZMod.val a + ZMod.val b - Stwo.P) % Stwo.P:= by
            rw[Nat.mod_eq_sub_mod _]
            omega
          _ = ZMod.val a + ZMod.val b - Stwo.P:= by
            apply Nat.mod_eq_of_lt
            calc
              ZMod.val a + ZMod.val b - Stwo.P < Stwo.P + Stwo.P - Stwo.P := by
                have htmp1 : ZMod.val a < Stwo.P := by
                  apply ZMod.val_lt
                have htmp2 : ZMod.val b < Stwo.P := by
                  apply ZMod.val_lt
                omega
              _ = Stwo.P := by norm_num

      rw[h7]
      rw[Nat.cast_sub]
      rw[Nat.cast_add]

      omega
      omega
      omega
      omega









namespace Felt252Words

@[irreducible]
def eval (x : Felt252Words) : Felt252 :=
  ∑ i : Fin FELT252_N_WORDS, (x i).toFelt252 * 2^(FELT252_BITS_PER_WORD * i)

end Felt252Words

-- evaluating a tuple as coefficients of a polynomial with a given base.
-- TODO(Jeremy): move somewhere else

def eval_poly {R : Type*} [Semiring R] (x : R) {n : Nat} (coeff : Fin n → R) : R :=
  ∑ i : Fin n, coeff i * x ^ i.val

theorem eval_poly_add {R : Type*} [Ring R] (x : R) {n : Nat} (c1 c2 : Fin n → R) :
    eval_poly x (c1 + c2) = eval_poly x c1 + eval_poly x c2 := by
  unfold eval_poly
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp; rw [add_mul]

theorem eval_poly_sub {R : Type*} [Ring R] (x : R) {n : Nat} (c1 c2 : Fin n → R) :
    eval_poly x (c1 - c2) = eval_poly x c1 - eval_poly x c2 := by
  unfold eval_poly
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp; rw [sub_mul]

section
open Fin.NatCast

def eval_poly' {R : Type*} [Semiring R] (x : R) {n : Nat} [NeZero n] (coeff : Fin n → R) : R :=
  ∑ i ∈ Finset.range n, coeff ↑i * x ^ i

def eval_poly_eq_eval_poly' {R : Type*} [Semiring R] (x : R) (n : Nat) [NeZero n] (coeff : Fin n → R) :
    eval_poly x coeff = eval_poly' x coeff :=
  calc eval_poly x coeff
    = ∑ i : Fin n, coeff ↑i.val * x ^ i.val := Finset.sum_congr rfl (by simp)
  _ = ∑ i ∈ Finset.range n, coeff ↑i * x ^ i :=
        Fin.sum_univ_eq_sum_range (f := fun i => coeff ↑i * x ^ i) _

end

lemma sum_eq_foldl [AddCommMonoid α] (xs : List α) (h : xs ≠ []) :
    xs.sum = xs.tail.foldl (· + ·) (xs.head h) := by
  rcases xs with _ | ⟨x, xs⟩
  . contradiction
  rw [List.sum_eq_foldl]; simp

namespace FeltExpr

lemma eval_foldl_add [Fact (Nat.Prime Stwo.P)] (xs : List FeltExpr) (x : FeltExpr) :
    (xs.foldl (. + .) x |>.eval varAssign) =
      (xs.map (FeltExpr.eval varAssign )).foldl (. + .) (x.eval varAssign) := by
  induction xs generalizing x <;> simp_all

lemma eval_foldl_add_map_fin [Fact (Nat.Prime Stwo.P)]
    (N : Nat) (y : Fin N → FeltExpr) (varAssign : VarAssign) :
    eval varAssign (((List.finRange N).map y).foldl (· + ·) (const 0)) =
      ∑ i : Fin N, eval varAssign (y i) := by
  simp [eval_foldl_add, ←List.sum_eq_foldl, ←List.ofFn_eq_map, Fin.sum_ofFn]

end FeltExpr


namespace Felt252Nats

-- evaluate as a Felt252. The cast is pushed inward.
def eval (xn : Felt252Nats) : Felt252 :=
  ∑ i : Fin FELT252_N_WORDS, xn i * 2^(FELT252_BITS_PER_WORD * i)

def eval_nat (xn : Felt252Nats) : Nat :=
  ∑ i : Fin FELT252_N_WORDS, xn i * 2^(FELT252_BITS_PER_WORD * i)

-- evaluate as a Felt252 with the cast on the outside.
-- TODO(Jeremy): this should be the default, i.e. switch eval and eval'

def eval' (xn : Felt252Nats) : Felt252 := eval_nat xn

theorem eval_eq_eval' (xn : Felt252Nats) : xn.eval = xn.eval' := by
  rw [eval, eval', eval_nat, Nat.cast_sum]; simp

theorem cast_eval_nat (xn : Felt252Nats) : ↑(xn.eval_nat) = xn.eval := by
  rw [eval, eval_nat, Nat.cast_sum]; simp

theorem intCast_eval_nat (xn : Felt252Nats) :
    (eval_nat xn : Int) = eval_poly (2^9) (fun i => ↑(xn i)) := by
  rw [eval_nat, eval_poly, Nat.cast_sum]; simp
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_mul, FELT252_BITS_PER_WORD]; norm_num

theorem intCast_eval_nat_alt (xn : Felt252Nats) :
    (eval_nat xn : Int) = ↑(eval_poly (2^9) xn) := by
  rw [eval_nat, eval_poly, Nat.cast_sum, Nat.cast_sum]; simp
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_mul, FELT252_BITS_PER_WORD]; norm_num

def IsRangeChecked (xn : Felt252Nats) (x : Felt252Words) : Prop :=
    ∀ i, x i = ↑(xn i) ∧ xn i < 2^9

def ExistsIsRangeChecked (x : Felt252Words) : Prop :=
  ∃ xn : Felt252Nats, xn.IsRangeChecked x

lemma eq_val_of_IsRangeChecked (xn : Felt252Nats) (x : Felt252Words) :
    IsRangeChecked xn x → ∀ i : Fin FELT252_N_WORDS, (x i).val = xn i := by
  intro h i
  rw [(h i).1, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  apply lt_trans (h i).2
  unfold Stwo.P
  norm_num1

lemma eval_eq_of_IsRangeChecked (xn : Felt252Nats) (x : Felt252Words) :
    IsRangeChecked xn x →
      xn.eval = ∑ i : Fin FELT252_N_WORDS, (x i).val * 2^(FELT252_BITS_PER_WORD * i) := by
  intro h
  simp only [eq_val_of_IsRangeChecked xn x h]
  unfold eval
  norm_cast

lemma eq_of_IsRangeChecked_eq {xn1 xn2 : Felt252Nats} {x : Felt252Words}
    (h1: IsRangeChecked xn1 x) (h2: IsRangeChecked xn2 x) :
    xn1 = xn2 := by
    unfold Felt252Nats at *
    apply funext
    intro i
    rw[← eq_val_of_IsRangeChecked xn1 x h1 i]
    rw[← eq_val_of_IsRangeChecked xn2 x h2 i]


lemma eq_zero_of_IsRangeChecked (xn : Felt252Nats) (x : Felt252Words) :
    IsRangeChecked xn x → ∀ i : Fin FELT252_N_WORDS, (x i) = 0 ↔ xn i = 0 := by
  intro h i
  rw [(h i).1, ←ZMod.val_eq_zero, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt _]
  apply lt_trans (h i).2
  unfold Stwo.P
  norm_num1

-- On the left, the cast from ℕ to Felt252 is applied to each (xn i) separately,
-- on the right, it is applied to the whole sum.
lemma eval_cast_add (xn : Felt252Nats) :
    xn.eval = ↑(∑ i : Fin FELT252_N_WORDS, xn i * 2^(FELT252_BITS_PER_WORD * i)) := by
  rw [eval, Nat.cast_sum]; simp

-- When the Felt252Words value is range checked, we can perform the sum directly, without
-- having to convert first to the Felt252Nats representation.
lemma eval_Felt252Words_eq {x : Felt252Words} {xn : Felt252Nats} (h_rc : IsRangeChecked xn x) :
    x.eval = xn.eval := by
  unfold Felt252Words.eval
  apply Finset.sum_congr ; rfl
  intro i h_i
  apply congr_arg₂ _ _ rfl
  rw [(h_rc i).1]
  apply toFelt.of_lt
  apply lt_trans (h_rc i).2
  unfold Stwo.P ; norm_num1

end Felt252Nats
