import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Airs.ConvolutionUtils.Karatsuba
import Verification.Semantics.Util

open Fin.NatCast



-- Note: P = 2^251 + 17*2^192 + 1

namespace VerifyMul252

abbrev CONV_LEN := 2 * FELT252_N_WORDS - 1
abbrev MAX_WORD := (1 <<< FELT252_BITS_PER_WORD) - 1
abbrev MUL_RANGE_CHECKS := 19

abbrev shift := FeltExpr.const (1 <<< FELT252_BITS_PER_WORD)
abbrev shift_inverse := FeltExpr.unary .inverse shift

def aux1 (conv_tmps : Fin 55 → FeltExpr) : Felt252Expr :=
  let step0 : Felt252Expr := fun _ => FeltExpr.const 0
  let step1 : Felt252Expr := fun j =>
    if j.val < 21 then step0 j + FeltExpr.const 32 * conv_tmps j.val else step0 j
  let step2 : Felt252Expr := fun j =>
    if 1 ≤ j.val ∧ j.val < 22 then step1 j + FeltExpr.const 1 * conv_tmps (j.val - 1) else step1 j
  let step3 : Felt252Expr := fun j =>
    if 7 ≤ j.val then step2 j + FeltExpr.const 2 * conv_tmps (j.val - 7) else step2 j
  let step4 : Felt252Expr := fun j =>
    step3 j - FeltExpr.const 4 * conv_tmps (j.val + 21)
  let step5 : Felt252Expr := fun j =>
    if j.val < 6 then step4 j + FeltExpr.const 8 * conv_tmps (j.val + 49) else step4 j
  let step6 : Felt252Expr := fun j =>
    if 21 ≤ j.val ∧ j.val < 27 then step5 j + FeltExpr.const 64 * conv_tmps (j.val + 28) else step5 j
  let step7 : Felt252Expr := fun j =>
    if 22 ≤ j.val then step6 j + FeltExpr.const 2 * conv_tmps (j.val + 27) else step6 j
  step7

lemma eval_ite [Fact (Nat.Prime Stwo.P)] (cond : Prop) [Decidable cond] (a b : FeltExpr) (varAssign : VarAssign) :
    (if cond then a else b).eval varAssign = if cond then a.eval varAssign else b.eval varAssign := by
  split_ifs <;> simp

def aux1_felt (conv_tmps : Fin 55 → Felt) : Felt252Words :=
  let step0 : Felt252Words := fun _ => 0
  let step1 : Felt252Words := fun j =>
    if j.val < 21 then step0 j + 32 * conv_tmps j.val else step0 j
  let step2 : Felt252Words := fun j =>
    if 1 ≤ j.val ∧ j.val < 22 then step1 j + conv_tmps (j.val - 1) else step1 j
  let step3 : Felt252Words := fun j =>
    if 7 ≤ j.val then step2 j + 2 * conv_tmps (j.val - 7) else step2 j
  let step4 : Felt252Words := fun j =>
    step3 j - 4 * conv_tmps (j.val + 21)
  let step5 : Felt252Words := fun j =>
    if j.val < 6 then step4 j + 8 * conv_tmps (j.val + 49) else step4 j
  let step6 : Felt252Words := fun j =>
    if 21 ≤ j.val ∧ j.val < 27 then step5 j + 64 * conv_tmps (j.val + 28) else step5 j
  let step7 : Felt252Words := fun j =>
    if 22 ≤ j.val then step6 j + 2 * conv_tmps (j.val + 27) else step6 j
  step7

lemma aux1_eval [Fact (Nat.Prime Stwo.P)]
    (conv_tmps : Fin 55 → FeltExpr) (varAssign : VarAssign) (i : Fin FELT252_N_WORDS) :
    (aux1 conv_tmps i).eval varAssign = aux1_felt (fun j => (conv_tmps j).eval varAssign) i := by
  simp [aux1, aux1_felt, eval_ite]

def aux1_ints (conv_tmps : Fin 55 → Int) : Fin FELT252_N_WORDS → Int :=
  let step0 : Fin FELT252_N_WORDS → Int := fun _ => 0
  let step1 : Fin FELT252_N_WORDS → Int := fun j =>
    if j.val < 21 then step0 j + 32 * conv_tmps j.val else step0 j
  let step2 : Fin FELT252_N_WORDS → Int := fun j =>
    if 1 ≤ j.val ∧ j.val < 22 then step1 j + conv_tmps (j.val - 1) else step1 j
  let step3 : Fin FELT252_N_WORDS → Int := fun j =>
    if 7 ≤ j.val then step2 j + 2 * conv_tmps (j.val - 7) else step2 j
  let step4 : Fin FELT252_N_WORDS → Int := fun j =>
    step3 j - 4 * conv_tmps (j.val + 21)
  let step5 : Fin FELT252_N_WORDS → Int := fun j =>
    if j.val < 6 then step4 j + 8 * conv_tmps (j.val + 49) else step4 j
  let step6 : Fin FELT252_N_WORDS → Int := fun j =>
    if 21 ≤ j.val ∧ j.val < 27 then step5 j + 64 * conv_tmps (j.val + 28) else step5 j
  let step7 : Fin FELT252_N_WORDS → Int := fun j =>
    if 22 ≤ j.val then step6 j + 2 * conv_tmps (j.val + 27) else step6 j
  step7

def aux1_ints_alt (x : Fin 55 → Int) : Fin FELT252_N_WORDS → Int :=
  let part1 : Fin FELT252_N_WORDS → Int := fun i =>
    if i.val < 21 then 32 * x i else 0
  let part2 : Fin FELT252_N_WORDS → Int := fun i =>
    if 1 ≤ i.val ∧ i.val < 22 then x (i.val - 1) else 0
  let part3 : Fin FELT252_N_WORDS → Int := fun i =>
    if 7 ≤ i.val then 2 * x (i.val - 7) else 0
  let part4 : Fin FELT252_N_WORDS → Int := fun i =>
     -4 * x (i.val + 21)
  let part5 : Fin FELT252_N_WORDS → Int := fun i =>
    if i.val < 6 then 8 * x (i.val + 49) else 0
  let part6 : Fin FELT252_N_WORDS → Int := fun i =>
    if 21 ≤ i.val ∧ i.val < 27 then 64 * x (i.val + 28) else 0
  let part7 : Fin FELT252_N_WORDS → Int := fun i =>
    if 22 ≤ i.val then 2 * x (i.val + 27) else 0
  part1 + part2 + part3 + part4 + part5 + part6 + part7

lemma aux1_ints_eq_aux1_ints_alt (x : Fin 55 → Int) :
    aux1_ints x = aux1_ints_alt x := by
  ext i
  unfold aux1_ints; dsimp
  fin_cases i <;> (simp [aux1_ints_alt, sub_eq_add_neg, neg_mul])

-- TODO(Jeremy): move these
theorem eval_poly_smul {R : Type*} [Ring R] (x m : R) {n : Nat} (c : Fin n → R) :
    m * eval_poly x c = eval_poly x (fun x => m * c x) := by
  unfold eval_poly
  rw [Finset.mul_sum]; simp [mul_assoc]

theorem eval_poly_drop_tail {R : Type*} [Ring R] (x : R) {m n : Nat} (h : m ≤ n) (c : Fin n → R)
    (h' : ∀ i : Fin n, m ≤ i → c i = 0) :
    eval_poly x c = eval_poly x (fun i : Fin m => c (Fin.castLE h i)) := by
  unfold eval_poly
  simp [Finset.sum_fin_eq_sum_range]; symm
  apply Finset.sum_subset_zero_on_sdiff
  . simp [h]
  . simp_all
  intro i hi; simp at hi
  rw [dif_pos hi, dif_pos _]; omega

theorem eval_poly_pad_tail {R : Type*} [Ring R] (x : R) {m n : Nat} (h : m ≤ n) (c : Fin m → R) :
    eval_poly x c = eval_poly x
      (fun i : Fin n => if h:i.val < m then c (Fin.castLT i h) else 0) := by
  rw [eval_poly_drop_tail _ h]
  . congr
    ext i
    simp [Fin.castLE, Fin.castLT]
  . intro i hi; simp_all

theorem eval_poly_drop_initial {R : Type*} [CommRing R] (x : R) {m n : Nat} [NeZero n] (h : m ≤ n)
    (c : Fin n → R)
    (h' : ∀ i : Fin n, i.val < m → c i = 0) :
    eval_poly x c = eval_poly x
      (fun i : Fin (n - m) =>
        x^m * c (Fin.cast (by simp [h]) (Fin.natAdd m i))) := by
  unfold eval_poly
  simp [Finset.sum_fin_eq_sum_range]
  trans (∑ i ∈ Finset.range (m + (n - m)), if h' : i < m then 0 else
    c ↑i * x^i)
  apply Finset.sum_congr
  . congr; omega
  . intro i hi
    simp at hi
    have : i < n := by omega
    rw [dif_pos this]
    split
    next h'' => rw [h'] <;> simp [h'']
    congr
    rw [Nat.mod_eq_of_lt this]
  rw [Finset.sum_range_add]
  conv => rhs; apply (zero_add _).symm
  apply congr; apply congr_arg
  . apply Finset.sum_eq_zero
    simp
    intro i hi1 hi2
    rw [h'] <;> simp
    omega
  apply Finset.sum_congr rfl
  simp; intro i hi
  rw [dif_pos]; swap; omega
  conv => rhs; rw [mul_comm (x^m), mul_assoc]
  congr
  . ext; simp
    rw [Fin.val_add]; simp
    rw [Nat.mod_eq_of_lt]; omega
  rw [pow_add, mul_comm]

abbrev BASE : ℤ := 2^9

lemma aux1_ints_eval (x : Fin 55 → Int) :
  let x_bottom : Fin 21 → Int := fun i => x i
  let x_middle : Fin 28 → Int := fun i => x (i + 21)
  let x_top : Fin 6 → Int := fun i => x (i + 49)
  eval_poly BASE (aux1_ints x) =
    (2^5 + 2^9 + 2^64) * eval_poly BASE x_bottom +
      -4 * eval_poly BASE x_middle +
        (2^3 + 2^195 + 2^199) * eval_poly BASE x_top := by
  intro x_bottom x_middle x_top
  rw [aux1_ints_eq_aux1_ints_alt]
  unfold aux1_ints_alt; lift_lets; intro part1 part2 part3 part4 part5 part6 part7
  simp only [eval_poly_add]
  have : eval_poly BASE part1 = 2^5 * eval_poly BASE x_bottom := by
    rw [eval_poly_drop_tail (m := 21) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part1]; omega
    rw [eval_poly_smul]
    congr; ext i
    simp [part1, x_bottom]
  rw [this]
  have : eval_poly BASE part2 = 2^9 * eval_poly BASE x_bottom := by
    rw [eval_poly_drop_tail (m := 22) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part2]; omega
    rw [eval_poly_drop_initial (m := 1) BASE (by simp)]; swap
    . intro i; simp [part2]; omega
    rw [eval_poly_smul]
    congr; ext i
    have := i.isLt
    simp [part2, x_bottom, BASE]; omega
  rw [this]
  have : eval_poly BASE part3 = 2^64 * eval_poly BASE x_bottom := by
    rw [eval_poly_drop_initial (m := 7) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part3]; omega
    rw [eval_poly_smul]
    congr; ext i
    have := i.isLt
    simp [part3, x_bottom, BASE]; omega
  rw [this]
  have : eval_poly BASE part4 = -4 * eval_poly BASE x_middle := by
    rw [eval_poly_smul]
  rw [this]
  have : eval_poly BASE part5 = 2^3 * eval_poly BASE x_top := by
    rw [eval_poly_drop_tail (m := 6) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part5]; omega
    rw [eval_poly_smul]
    congr; ext i
    have := i.isLt
    simp [part5, x_top]
  rw [this]
  have : eval_poly BASE part6 = 2^195 * eval_poly BASE x_top := by
    rw [eval_poly_drop_tail (m := 27) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part6]; omega
    rw [eval_poly_drop_initial (m := 21) BASE (by simp)]; swap
    . intro i; simp [part6]; omega
    rw [eval_poly_smul]
    apply congr_arg
    ext i
    have := i.isLt
    simp [part6, x_top, BASE]
    rw [if_pos, ←mul_assoc]
    congr 1
    . rw [add_comm 21, add_assoc]; rfl
    . omega
  rw [this]
  have : eval_poly BASE part7 = 2^199 * eval_poly BASE x_top := by
    rw [eval_poly_drop_initial (m := 22) BASE (by simp [FELT252_N_WORDS])]; swap
    . intro i; simp [part7]; omega
    rw [eval_poly_smul]
    apply congr_arg
    ext i
    have := i.isLt
    simp [part7, x_top, BASE]
    rw [←mul_assoc]
    congr 1
    . rw [add_comm 22, add_assoc]; rfl
  rw [this]
  ring

lemma eval_poly_55_split (x : Fin 55 → Int) :
    let x_bottom : Fin 21 → Int := fun i => x i
    let x_middle : Fin 28 → Int := fun i => x (i + 21)
    let x_top : Fin 6 → Int := fun i => x (i + 49)
    eval_poly BASE x = eval_poly BASE x_bottom +
      2^189 * (eval_poly BASE x_middle) +
      2^441 * (eval_poly BASE x_top) := by
  unfold eval_poly
  intro x_bottom x_middle x_top
  rw [Fin.sum_univ_add (a := 21) (b := 34), Fin.sum_univ_add (a := 28) (b := 6),
    Finset.mul_sum, Finset.mul_sum, add_assoc]
  apply congr
  . apply congr_arg
    apply Finset.sum_congr rfl
    rintro i -
    simp [x_bottom, Fin.castAdd, Fin.castLE]; congr; omega
  apply congr
  . apply congr_arg
    apply Finset.sum_congr rfl
    rintro i -
    rw [mul_comm (2^189), mul_assoc]
    congr; swap
    . simp [pow_add, BASE, add_comm]
    apply Fin.eq_of_val_eq; simp [Fin.val_add]; omega
  apply Finset.sum_congr rfl
  rintro i -
  rw [mul_comm (2^441), mul_assoc]
  congr; swap
  . simp only [BASE, Fin.coe_natAdd]
    rw [←add_assoc, add_comm, pow_add]; norm_num
  apply Fin.eq_of_val_eq; simp [Fin.val_add]; omega

lemma eval_aux1_ints_mod (x : Fin 55 → Int) :
    eval_poly BASE (aux1_ints x) ≡ (2^5 + 2^9 + 2^64) * eval_poly BASE x [ZMOD Felt252Prime] := by
  rw [eval_poly_55_split, mul_add, mul_add, aux1_ints_eval]
  apply Int.ModEq.add
  . apply Int.ModEq.add
    . apply Int.ModEq.refl
    . rw [←mul_assoc]
      apply Int.ModEq.mul_right
      rw [Int.ModEq.eq_1]; norm_num [Felt252Prime]
  rw [←mul_assoc]
  apply Int.ModEq.mul_right
  rw [Int.ModEq.eq_1]; norm_num [Felt252Prime]

lemma aux1_invertible (x : Int) (h : (2^5 + 2^9 + 2^64) * x ≡ 0 [ZMOD Felt252Prime]) :
    x ≡ 0 [ZMOD Felt252Prime] := by
  have := Int.ModEq.mul_left (-(2^187)) h; rw [mul_zero] at this
  trans; swap; apply this
  nth_rewrite 1 [←one_mul x]
  rw [←mul_assoc]
  apply Int.ModEq.mul_right
  rw [Int.ModEq.eq_1]; norm_num [Felt252Prime]

lemma aux1_ints_cast (conv_tmps : Fin 55 → Int) :
    (fun i => (↑(aux1_ints conv_tmps i) : Felt)) = aux1_felt (fun i => (conv_tmps i : Felt)) := by
  ext i
  simp only [aux1_ints, zero_add, Int.cast_ite, Int.cast_add, Int.cast_mul, Int.cast_sub,
    Int.cast_ofNat, aux1_felt]; rfl

lemma aux1_ints_bound (conv_tmps : Fin 55 → Int) (h : ∀ i, |conv_tmps i| ≤ b):
    ∀ i, |aux1_ints conv_tmps i| ≤ 113 * b := by
  have bnonneg : 0 ≤ b := le_trans (abs_nonneg (conv_tmps 0)) (h 0)
  dsimp -zeta [aux1_ints]; lift_lets
  intro step0 step1 step2 step3 step4 step5 step6 step7 i
  have h1 : |step1 i| ≤ 32 * b := by
    simp [step1, step0]; split
    . rw [abs_mul]; simp; apply h
    . simp [bnonneg]
  have h2 : |step2 i| ≤ 33 * b := by
    simp [step2]; split
    . apply le_trans (abs_add _ _)
      linarith [h (↑(i.val) - 1)]
    . linarith
  have h3 : |step3 i| ≤ 35 * b := by
    simp [step3]; split
    . apply le_trans (abs_add _ _)
      rw [abs_mul]; simp
      linarith [h (↑(i.val) - 7)]
    . linarith
  have h4 : |step4 i| ≤ 39 * b := by
    simp [step4]
    apply le_trans (abs_sub _ _)
    rw [abs_mul]; simp
    linarith [h (↑(i.val) + 21)]
  have h5 : |step5 i| ≤ 47 * b := by
    simp [step5]; split
    . apply le_trans (abs_add _ _)
      rw [abs_mul]; simp
      linarith [h (↑(i.val) + 49)]
    . linarith
  have h6 : |step6 i| ≤ 111 * b := by
    simp [step6]; split
    . apply le_trans (abs_add _ _)
      rw [abs_mul]; simp
      linarith [h (↑(i.val) + 28)]
    . linarith
  have h7 : |step7 i| ≤ 113 * b := by
    simp [step7]; split
    . apply le_trans (abs_add _ _)
      rw [abs_mul]; simp
      linarith [h (↑(i.val) + 27)]
    . linarith
  exact h7

def aux2 (conv_mod_tmps : Felt252Expr) (k_expr : FeltExpr) : Felt252Expr
  | 0 => conv_mod_tmps 0  - FeltExpr.const 1 * k_expr
  | 21 => conv_mod_tmps 21 - FeltExpr.const 136 * k_expr
  | 27 => conv_mod_tmps 27 - FeltExpr.const 256 * k_expr
  | i => conv_mod_tmps i

def aux2_felt (conv_mod_tmps : Felt252Words) (k_expr : Felt) : Felt252Words
  | 0 => conv_mod_tmps 0  - k_expr
  | 21 => conv_mod_tmps 21 - 136 * k_expr
  | 27 => conv_mod_tmps 27 - 256 * k_expr
  | i => conv_mod_tmps i

theorem aux2_eval' [Fact (Nat.Prime Stwo.P)]
    (conv_mod_tmps : Fin FELT252_N_WORDS → FeltExpr) (k_expr : FeltExpr)
    (varAssign : VarAssign) (i : Fin FELT252_N_WORDS) :
    (aux2 conv_mod_tmps k_expr i).eval varAssign =
      aux2_felt (fun j => (conv_mod_tmps j).eval varAssign) (k_expr.eval varAssign) i := by
  simp [aux2, aux2_felt]
  split <;> simp

theorem aux2_eval [Fact (Nat.Prime Stwo.P)]
    (conv_mod_tmps : Fin FELT252_N_WORDS → FeltExpr) (k_expr : FeltExpr)
    (varAssign : VarAssign) :
    (aux2 conv_mod_tmps k_expr).eval varAssign =
      aux2_felt (fun j => (conv_mod_tmps j).eval varAssign) (k_expr.eval varAssign) := by
  apply funext
  intro i
  simp [Felt252Expr.eval, aux2_eval']

def aux2_ints (conv_mod_tmps : Fin FELT252_N_WORDS → Int) (k_expr : Int) : Fin FELT252_N_WORDS → Int
  | 0 => conv_mod_tmps 0  - 1 * k_expr
  | 21 => conv_mod_tmps 21 - 136 * k_expr
  | 27 => conv_mod_tmps 27 - 256 * k_expr
  | i => conv_mod_tmps i

def Felt252Prime_coeffs : Fin FELT252_N_WORDS → Int
  | 0 => 1
  | 21 => 136
  | 27 => 256
  | _ => 0

lemma eval_aux2_ints_mod (x : Fin FELT252_N_WORDS → Int) (k : Int) :
    eval_poly BASE (aux2_ints x k) ≡ eval_poly BASE x [ZMOD Felt252Prime] := by
  suffices eval_poly BASE (aux2_ints x k) =
      eval_poly BASE (x - (fun i => k * Felt252Prime_coeffs i)) by
    rw [this, eval_poly_sub, Int.modEq_iff_dvd, sub_sub_cancel, ←eval_poly_smul]
    exact Int.dvd_mul_left k ↑Felt252Prime
  unfold aux2_ints
  congr
  ext i; unfold Felt252Prime_coeffs
  split <;> simp [mul_comm k]

theorem aux2_ints_cast (conv_mod_tmps : Fin FELT252_N_WORDS → Int) (k_expr : Int) :
    (fun i => (↑(aux2_ints conv_mod_tmps k_expr i) : Felt)) =
      aux2_felt (fun i => (conv_mod_tmps i : Felt)) k_expr := by
  ext i
  unfold aux2_ints aux2_felt
  split <;> simp

lemma aux2_ints_bound (conv_mod_tmps : Fin FELT252_N_WORDS → Int) (k_expr : Int)
    (h : ∀ i, |conv_mod_tmps i| ≤ b) :
    ∀ i, |aux2_ints conv_mod_tmps k_expr i| ≤ b + 256 * |k_expr| := by
  have bnonneg : 0 ≤ b := le_trans (abs_nonneg (conv_mod_tmps 0)) (h 0)
  intro i
  unfold aux2_ints
  split
  . apply le_trans (abs_sub _ _)
    rw [abs_mul]; simp
    linarith [h 0, abs_nonneg k_expr]
  . apply le_trans (abs_sub _ _)
    rw [abs_mul]; simp
    linarith [h 21, abs_nonneg k_expr]
  . apply le_trans (abs_sub _ _)
    rw [abs_mul]; simp
    linarith [h 27, abs_nonneg k_expr]
  linarith [h i, abs_nonneg k_expr]

def call [Fact (Nat.Prime Stwo.P)] (ab : AirBuilder) (lookupTerms : AirLookupTerms)
    (a b c : Felt252Expr) : AirBuilder × AirLookupTerms :=
  let conv_tmps_aux := DoubleKaratsuba.call ab 7 a b
  let ab1 := conv_tmps_aux.1
  let conv_tmps0 : Fin CONV_LEN → FeltExpr := conv_tmps_aux.2
  let conv_tmps1 := fun i => if i.val < FELT252_N_WORDS then conv_tmps0 i - c i else conv_tmps0 i
  let conv_tmps_aux := ab1.letRec conv_tmps1
  let ab2 := conv_tmps_aux.1
  let conv_tmps := conv_tmps_aux.2

  let conv_mod_tmps_aux := ab2.letRec (aux1 conv_tmps)
  let ab3 := conv_mod_tmps_aux.1
  let conv_mod_tmps2 := conv_mod_tmps_aux.2

  let k_expr_aux := ab3.deduce
  let ab4 := k_expr_aux.1
  let k_expr := k_expr_aux.2

  let lt1 := lookupTerms.add_rc MUL_RANGE_CHECKS (k_expr + FeltExpr.const (1 <<< 18))

  let conv_mod_tmps := aux2 conv_mod_tmps2 k_expr

  let aux :=
    Fin.hIterate (P := fun _ => AirBuilder × AirLookupTerms × FeltExpr)
      (init := (ab4, lt1, FeltExpr.const 0))
      (n := FELT252_N_WORDS - 1)
      (f := fun i p1 =>
        let ab50 := p1.1
        let lt := p1.2.1
        let prev_carry := p1.2.2
        let conv_mod := conv_mod_tmps i.castSucc
        let shifted_carry := conv_mod + prev_carry
        let loop_aux := ab50.deduce
        let ab51 := loop_aux.1
        let carry := loop_aux.2
        let ab52 := ab51.constrain (carry * shift - shifted_carry)
        let lt' := lt.add_rc MUL_RANGE_CHECKS (carry + FeltExpr.const (1 <<< 17))
        (ab52, lt', carry))
  let ab5 := aux.1
  let lt2 := aux.2.1
  let carry := aux.2.2
  let i : Fin FELT252_N_WORDS := @Fin.last (FELT252_N_WORDS - 1)
  let ab6 := ab5.constrain (conv_mod_tmps i + carry)
  (ab6, lt2)

def spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
  ∃ conv_tmps0 : Fin CONV_LEN → Felt,
    DoubleKaratsuba.spec (N := 7) a b conv_tmps0 ∧
  ∃ conv_tmps : Fin CONV_LEN → Felt,
    conv_tmps = (fun i => if i.val < FELT252_N_WORDS then conv_tmps0 i - c i else conv_tmps0 i) ∧
  ∃ conv_mod_tmps0 : Fin FELT252_N_WORDS → Felt,
    conv_mod_tmps0 = aux1_felt conv_tmps ∧
  ∃ k_expr : Felt,
    IsRangeChecked MUL_RANGE_CHECKS (k_expr + 2^18) ∧
  ∃ conv_mod_tmps,
    conv_mod_tmps = aux2_felt conv_mod_tmps0 k_expr ∧
  ∃ prev_carry : Fin FELT252_N_WORDS → Felt,
    prev_carry 0 = 0 ∧
    (∀ i : Fin (FELT252_N_WORDS - 1),
      prev_carry i.succ * (1 <<< FELT252_BITS_PER_WORD) =
        conv_mod_tmps i.castSucc + prev_carry i.castSucc ∧
      IsRangeChecked MUL_RANGE_CHECKS (prev_carry i.succ + (1 <<< 17))) ∧
    let i : Fin FELT252_N_WORDS := @Fin.last (FELT252_N_WORDS - 1)
    conv_mod_tmps i + prev_carry i = 0

def spec (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
    ∀ an bn cn : Felt252Nats,
      an.IsRangeChecked a → bn.IsRangeChecked b → cn.IsRangeChecked c →
      an.eval * bn.eval = cn.eval

-- TODO(Jeremy): move this, or, better, change the definition of IsRangeChecked to use this
lemma IsRangeChecked_iff (x : Felt) (n : Nat) :
    IsRangeChecked n x ↔ x.val < 2^n := by
  constructor
  . rintro ⟨m, hm, rfl⟩
    by_cases h' : 2^n ≤ Stwo.P
    . rwa [ZMod.val_cast_of_lt]; omega
    rw [not_le] at h'
    exact lt_trans (ZMod.val_lt (n := Stwo.P) ↑m) h'
  intro h
  use ZMod.val x, h
  rw [ZMod.natCast_zmod_val]

lemma aux
    (prev_carry_ints : Fin FELT252_N_WORDS → Int)
    (conv_mod_tmps_ints : Fin FELT252_N_WORDS → Int)
    (hprev_carry_ints0 : prev_carry_ints 0 = 0)
    (hprev_carry_ints : ∀ (i : Fin (FELT252_N_WORDS - 1)),
      prev_carry_ints i.succ * 2 ^ 9 = conv_mod_tmps_ints i.castSucc + prev_carry_ints i.castSucc) :
    ∀ k : Fin FELT252_N_WORDS,
      ∑ i : Fin k.val, (conv_mod_tmps_ints (i.castLE (Nat.le_of_lt k.isLt))) * 2^(FELT252_BITS_PER_WORD * i) =
          prev_carry_ints k * 2^(FELT252_BITS_PER_WORD * k) := by
  intro k
  refine k.induction ?_ ?_
  . simp [hprev_carry_ints0]
  intro i ih
  simp only [Fin.val_succ]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.coe_castSucc, Fin.val_last]
  simp at ih
  rw [ih, mul_add, mul_one, pow_add, mul_comm (2 ^ _) (2 ^ _), ←mul_assoc,
    FELT252_BITS_PER_WORD, hprev_carry_ints i, add_comm, add_mul]
  simp; rfl

theorem spec_of_spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)]
    (hspec : spec_auto a b c) :
    spec a b c := by
  rcases hspec with ⟨conv_tmps0, /- hconv_tmps0 -/ rfl, conv_tmps, /- hconv_temps -/ rfl, conv_mod_tmps0,
    hconv_mod_tmps0, k_expr, hk_expr, conv_mod_tmps, hconv_mod_tmps, prev_carry, hprev_carry0,
    hprev_carry, hlast⟩
  rw [IsRangeChecked_iff, MUL_RANGE_CHECKS] at hk_expr
  let k_expr_int := ((k_expr + 2 ^ 18).val : ℤ) - 2^18
  have hk_expr_int1 : k_expr_int < 2^18 := by omega
  have hk_expr_int2 : -(2^18) ≤ k_expr_int := by omega
  rw [spec]
  intro an bn cn han hbn hcn
  dsimp at hconv_mod_tmps0
  let anbn_m_cn : Fin (2 * FELT252_N_WORDS - 1) → Int := fun i =>
    (↑(simple_convolution_val _ an bn i) - if i.val < FELT252_N_WORDS then ↑(cn i) else 0)
  let conv_mod_tmps0_ints : Fin FELT252_N_WORDS → Int := aux1_ints anbn_m_cn
  let conv_mod_tmps_ints : Fin FELT252_N_WORDS → Int := aux2_ints conv_mod_tmps0_ints k_expr_int
  let prev_carry_ints : Fin FELT252_N_WORDS → Int := fun i =>
    (ZMod.val (prev_carry i + ((2 ^ 17 : ℕ) : Felt)) : ℤ) - 2^17
  have hprev_carry_ints1 : ∀ i, -(2^17) ≤ prev_carry_ints i := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with (rfl | ⟨j, rfl⟩)
    . unfold prev_carry_ints
      rw [hprev_carry0, zero_add, ZMod.val]; simp
    . have := hprev_carry j |>.2
      unfold prev_carry_ints
      omega
  have hprev_carry_ints2 : ∀ i, prev_carry_ints i < 2^19 - 2^17 := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with (rfl | ⟨j, rfl⟩)
    . unfold prev_carry_ints
      rw [hprev_carry0, zero_add, ZMod.val_cast_of_lt] <;> simp [Stwo.P]
    . have := hprev_carry j |>.2
      unfold prev_carry_ints
      rw [IsRangeChecked_iff, MUL_RANGE_CHECKS, ←Nat.cast_lt (α := Int)] at this
      apply sub_lt_sub_right
      exact this
  have hprev_carry_ints_le : ∀ i, |prev_carry_ints i| ≤ 2^19 := by
    intro i
    by_cases h : prev_carry_ints i ≥ 0
    . rw [abs_of_nonneg h]
      have := hprev_carry_ints2 i
      omega
    . rw [abs_of_neg (lt_of_not_ge h)]
      have := hprev_carry_ints1 i
      omega
  have hcast_prev_carry_ints :
      ∀ i, (↑(prev_carry_ints i) : Felt) = prev_carry i := by
    intro i
    unfold prev_carry_ints
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]; simp
  have : ∀ i, |anbn_m_cn i| ≤ 28 * 2^18 + 2^9 := by
    intro i
    apply le_trans (abs_sub _ _)
    simp only [Nat.abs_cast]
    apply add_le_add
    . have : (28 : ℤ) * 2^18 = ↑(28 * 2^9 * 2^9 : ℕ) := by simp
      rw [this, Nat.cast_le]
      have := fun i => han i |>.2
      apply simple_convolution_val_bound 28 (2^9) an bn (fun i => le_of_lt (han i |>.2))
        (fun i => le_of_lt (hbn i |>.2))
    . have : (2^9 : ℤ) = (2^9 : ℕ) := by simp
      split; swap; simp
      rw [this]; simp
      apply le_of_lt
      apply hcn _ |>.2
  have : ∀ i, |conv_mod_tmps0_ints i| ≤ 113 * (28 * 2^18 + 2^9) := aux1_ints_bound _ this
  have hconv_mod_tmps_ints_le :
      ∀ i, |conv_mod_tmps_ints i| ≤ 113 * (28 * 2^18 + 2^9) + 256 * 2^18 := by
    intro i
    apply le_trans; swap
    . apply add_le_add_left
      apply mul_le_mul_of_nonneg_left (b := |k_expr_int|) _ (by simp)
      by_cases h : k_expr_int ≥ 0
      . rw [abs_of_nonneg h]; omega
      . rw [abs_of_neg (lt_of_not_ge h)]; omega
    apply aux2_ints_bound _ k_expr_int this
  have hcast_conv_mod_tmps_ints :
      ∀ i, (↑(conv_mod_tmps_ints i) : Felt) = conv_mod_tmps i := by
    intro i
    unfold conv_mod_tmps_ints
    simp [hconv_mod_tmps]
    rw [congr_fun (aux2_ints_cast conv_mod_tmps0_ints k_expr_int) i]
    apply congr_fun
    apply congr; swap
    . unfold k_expr_int
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]; norm_num
    apply congr_arg
    ext i
    rw [hconv_mod_tmps0]
    unfold conv_mod_tmps0_ints
    rw [congr_fun (aux1_ints_cast _) i]
    apply congr_fun
    apply congr_arg
    ext i
    unfold anbn_m_cn
    simp [FELT252_N_WORDS]
    rw [← congr_fun (cast_simple_convolution_val_eq (N := 28) _ _) i]
    have : a = fun i => ↑(an i) := by apply funext; intro i; exact han i |>.1
    rw [this]
    have : b = fun i => ↑(bn i) := by apply funext; intro i; exact hbn i |>.1
    rw [this]
    have : c = fun i => ↑(cn i) := by apply funext; intro i; exact hcn i |>.1
    rw [this]
    split; simp_all; simp
  have hprev_carry_ints0 : prev_carry_ints 0 = 0 := by
    apply Int.cast_inj_of_lt_char instCharPFeltP
    . rw [Int.cast_zero, hcast_prev_carry_ints, hprev_carry0]
    rw [zero_sub, abs_neg]
    apply lt_of_le_of_lt (hprev_carry_ints_le 0)
    simp [Stwo.P]
  have hprev_carry_ints : ∀ (i : Fin (FELT252_N_WORDS - 1)),
      prev_carry_ints i.succ * 2^9 =
        conv_mod_tmps_ints i.castSucc + prev_carry_ints i.castSucc := by
    intro i
    apply Int.cast_inj_of_lt_char instCharPFeltP
    . rw [Int.cast_mul, Int.cast_add, hcast_prev_carry_ints, hcast_prev_carry_ints,
        hcast_conv_mod_tmps_ints]
      exact hprev_carry i |>.1
    apply lt_of_le_of_lt
    apply abs_add
    apply lt_of_le_of_lt
    apply add_le_add
    . apply le_trans (abs_add _ _)
      apply add_le_add
      . apply hconv_mod_tmps_ints_le
      . apply hprev_carry_ints_le
    change _ ≤ 2^19 * 2^9
    rw [abs_neg, abs_mul, abs_of_nonneg (a := 2^9) (by simp)]
    apply mul_le_mul_of_nonneg_right (hprev_carry_ints_le _) (by simp)
    simp [Stwo.P]
  have hprev_carry_ints_last :
      let i := Fin.last (FELT252_N_WORDS - 1);
      conv_mod_tmps_ints i + prev_carry_ints i = 0 := by
    apply Int.cast_inj_of_lt_char instCharPFeltP
    . rw [Int.cast_zero, Int.cast_add, hcast_conv_mod_tmps_ints, hcast_prev_carry_ints]
      exact hlast
    rw [zero_sub, abs_neg]
    apply lt_of_le_of_lt (abs_add _ _)
    apply lt_of_le_of_lt
    apply add_le_add (hconv_mod_tmps_ints_le _) (hprev_carry_ints_le _)
    simp [Stwo.P]
  have hsum_eq_zero :
    ∑ i : Fin FELT252_N_WORDS, conv_mod_tmps_ints i * 2^(FELT252_BITS_PER_WORD * i) = 0 := by
    change ∑ i : Fin (FELT252_N_WORDS - 1 + 1), _ = 0
    rw [Fin.sum_univ_castSucc]
    have := aux prev_carry_ints conv_mod_tmps_ints hprev_carry_ints0 hprev_carry_ints (Fin.last _)
    conv =>  lhs; congr; exact this; rfl
    norm_num [Fin.last]
    rw [←add_mul, add_comm]
    apply mul_eq_zero_of_left
    exact hprev_carry_ints_last
  simp only [←Felt252Nats.cast_eval_nat]
  suffices ((an.eval_nat : Int) : Felt252) * ((bn.eval_nat : Int) : Felt252) =
      ((cn.eval_nat : Int) : Felt252) by
    simpa [-CharP.cast_eq_zero] using this
  apply eq_of_sub_eq_zero
  rw [←Int.cast_mul, ←Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, ←Int.modEq_zero_iff_dvd]
  apply aux1_invertible
  have : eval_poly BASE conv_mod_tmps_ints = 0 := by
    rw [←hsum_eq_zero, eval_poly]
    apply Finset.sum_congr rfl
    rintro i -
    rw [pow_mul]; rfl
  rw [←this]; symm; trans
  apply eval_aux2_ints_mod
  trans
  apply eval_aux1_ints_mod
  apply Int.ModEq.mul_left
  suffices eval_poly BASE anbn_m_cn = ↑an.eval_nat * ↑bn.eval_nat - ↑cn.eval_nat by rw [this]
  trans; apply eval_poly_sub
  dsimp [BASE]
  apply congr
  . apply congr_arg
    simp only [Felt252Nats.intCast_eval_nat_alt]
    rw [←Nat.cast_mul, ←simple_convolution_val_spec]
    simp [-CharP.cast_eq_zero, eval_poly]
  dsimp [FELT252_N_WORDS]
  simp only [Felt252Nats.intCast_eval_nat]
  rw [eval_poly_pad_tail (m := 28) (n := 55)]; swap; norm_num
  apply congr_arg
  ext i
  split <;> simp [Fin.castLT]
  apply congr_arg
  apply Fin.eq_of_val_eq
  simpa

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (a b c : Felt252Expr) :
    let new_ab_lt := call ab lt a b c
    new_ab_lt.1.SatisfiedBy varAssign →
    new_ab_lt.2.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (a.eval varAssign) (b.eval varAssign) (c.eval varAssign) := by
  intro new_ab_lt hnew_ab hnew_lt

  let conv_tmps_aux := DoubleKaratsuba.call ab 7 a b
  let ab1 := conv_tmps_aux.1
  let conv_tmps0 : Fin CONV_LEN → FeltExpr := conv_tmps_aux.2
  let conv_tmps1 := fun i => if i.val < FELT252_N_WORDS then conv_tmps0 i - c i else conv_tmps0 i
  let conv_tmps_aux := ab1.letRec conv_tmps1
  let ab2 := conv_tmps_aux.1
  let conv_tmps := conv_tmps_aux.2

  let conv_mod_tmps_aux := ab2.letRec (aux1 conv_tmps)
  let ab3 := conv_mod_tmps_aux.1
  let conv_mod_tmps2 := conv_mod_tmps_aux.2

  let k_expr_aux := ab3.deduce
  let ab4 := k_expr_aux.1
  let k_expr := k_expr_aux.2

  let lt1 := lt.add_rc MUL_RANGE_CHECKS (k_expr + FeltExpr.const (1 <<< 18))

  let conv_mod_tmps := aux2 conv_mod_tmps2 k_expr

  let aux :=
    Fin.hIterate (P := fun _ => AirBuilder × AirLookupTerms × FeltExpr)
      (init := (ab4, lt1, FeltExpr.const 0))
      (n := FELT252_N_WORDS - 1)
      (f := fun i p1 =>
        let ab50 := p1.1
        let lt := p1.2.1
        let prev_carry := p1.2.2
        let conv_mod := conv_mod_tmps i.castSucc
        let shifted_carry := conv_mod + prev_carry
        let loop_aux := ab50.deduce
        let ab51 := loop_aux.1
        let carry := loop_aux.2
        let ab52 := ab51.constrain (carry * shift - shifted_carry)
        let lt' := lt.add_rc MUL_RANGE_CHECKS (carry + FeltExpr.const (1 <<< 17))
        (ab52, lt', carry))
  let ab5 := aux.1
  let lt2 := aux.2.1
  let carry := aux.2.2
  let i : Fin FELT252_N_WORDS := @Fin.last (FELT252_N_WORDS - 1)
  let ab6 := ab5.constrain (conv_mod_tmps i + carry)
  have ⟨hab5, h5⟩ : ab5.SatisfiedBy varAssign ∧
      (conv_mod_tmps i + carry).eval varAssign = 0 :=
    ab5.constrain_SatisfiedBy (conv_mod_tmps i + carry) varAssign |>.mp hnew_ab
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) :=
    (h : i ≤ FELT252_N_WORDS - 1) →
    p.1.SatisfiedBy varAssign →
    p.2.1.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab4.SatisfiedBy varAssign ∧
      lt1.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      ∃ prev_carries : Fin i.succ → Felt,
        prev_carries 0 = 0 ∧
        (∀ j : Fin i,
          let conv_mod := conv_mod_tmps j
          let shifted_carry := conv_mod.eval varAssign + prev_carries j.castSucc
          prev_carries j.succ * shift.eval varAssign - shifted_carry = 0 ∧
          IsRangeChecked MUL_RANGE_CHECKS (prev_carries j.succ + (1 <<< 17))) ∧
        (prev_carries (Fin.last i) = p.2.2.eval varAssign)
  have haux : Q (FELT252_N_WORDS - 1) aux := by
    apply Fin.hIterate_elim
    . simp [Q]
      intro h1 h2
      use h1, h2, fun _ => 0
    rintro i ⟨ab, lt, prev_carry⟩ ih h'

    lift_lets
    intro iab50 ilt iprev_carry iconv_mod ishifted_carry iloop_aux;
      dsimp -zeta [iab50, ilt, iprev_carry, iloop_aux]
    rintro  iab51 icarry iab52 ilt' hiab52 hlt'
    have ⟨hab, hab50⟩ := ab.constrain_SatisfiedBy _ varAssign |>.mp hiab52
    have ⟨hrangechecked, hlt⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt'
    specialize ih (le_trans (Nat.le_succ _) h') hab hlt
    rcases ih with ⟨hab4, hlt1, prev_carries, hprev_carry_0, hcarry, hcarry_last⟩
    use hab4, hlt1, Fin.snoc prev_carries (icarry.eval varAssign)
    constructor
    . rw [←Fin.castSucc_zero, Fin.snoc_castSucc, hprev_carry_0]
    constructor
    . intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      . constructor
        . rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          have := hcarry j |>.1
          convert this using 2
        . rw [Fin.succ_castSucc, Fin.snoc_castSucc]
          convert hcarry j |>.2
      . constructor
        . rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hcarry_last, Fin.val_last,
            Fin.coe_eq_castSucc]
          exact hab50
        . rw [Fin.succ_last, Fin.snoc_last]
          exact hrangechecked
    rw [Fin.snoc_last]
  have ⟨hab4, hlt1, prev_carries, hpc0, hpcj, hpclast⟩ :=
    haux (le_refl (FELT252_N_WORDS - 1)) hab5 hnew_lt
  have hab3 := ab3.deduce_SatisfiedBy varAssign |>.mp hab4
  have ⟨hlt', hlt⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hlt1
  have ⟨hab2, h2⟩ := (ab2.letRec_SatisfiedBy _ _).mp hab3
  have : NeZero CONV_LEN := Nat.instNeZeroSucc
  have ⟨hab1, h1⟩ := (ab1.letRec_SatisfiedBy _ _).mp hab2
  have ⟨hab, hspec⟩ := DoubleKaratsuba.sound_auto 7 a b varAssign ab hab1
  change DoubleKaratsuba.spec (N := 7) _ _ (FeltExpr.eval varAssign ∘ conv_tmps0) at hspec
  use hab, hlt
  apply spec_of_spec_auto
  rw [spec_auto]
  use FeltExpr.eval varAssign ∘ conv_tmps0, hspec
  use FeltExpr.eval varAssign ∘ conv_tmps
  constructor
  . ext i; dsimp
    rw [h1]; unfold conv_tmps1
    split <;> simp [FELT252_N_WORDS, Felt252Expr.eval]
  refine ⟨_, rfl, ?_⟩
  use k_expr.eval varAssign, hlt'
  use conv_mod_tmps.eval varAssign
  constructor
  . unfold conv_mod_tmps conv_mod_tmps2
    rw [aux2_eval]
    apply congr_fun
    apply congr_arg
    ext j
    rw [h2, aux1_eval]; rfl
  use prev_carries, hpc0
  constructor
  . intro j
    constructor
    . apply eq_of_sub_eq_zero
      unfold Felt252Expr.eval
      convert (hpcj j).1
      simp
    . exact (hpcj j).2
  rw [←h5]
  simp [i, Felt252Expr.eval]
  exact hpclast

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {a b c : Felt252Expr} :
    AirLookupTerms.NoYieldTerms (call ab lt a b c).2 := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.NoYieldTerms p.2.1
  apply Fin.hIterate_elim Q
  · apply AirLookupTerms.add'_NoYieldTerms.mpr
    simp [h]
  intro k s q_k_1
  apply AirLookupTerms.add'_NoYieldTerms.mpr
  unfold Q at q_k_1
  simp [q_k_1]

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {a b c : Felt252Expr} :
    AirLookupTerms.NoTermsOfRel (call ab lt a b c).2 OPCODE_TRACE_REL_INDEX := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.NoTermsOfRel p.2.1 OPCODE_TRACE_REL_INDEX
  apply Fin.hIterate_elim Q
  · apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
    simp_all [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  intro k s q_k_1
  apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
  unfold Q at q_k_1
  simp_all [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {a b c : Felt252Expr} :
    AirLookupTerms.RelInRelTuples (call ab lt a b c).2 := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.RelInRelTuples p.2.1
  apply Fin.hIterate_elim Q
  · apply AirLookupTerms.add'_RelInRelTuple.mpr
    simp [h]
  intro k s q_k_1
  apply AirLookupTerms.add'_RelInRelTuple.mpr
  unfold Q at q_k_1
  simp [q_k_1]


end VerifyMul252
