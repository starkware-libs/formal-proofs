import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.AirFn
import Verification.Semantics.Util

-- allows cast from Nat to Fin
open Fin.NatCast



def simple_convolution (N : Nat) (x y : Fin N → FeltExpr) : Fin (2 * N - 1) → FeltExpr :=
  fun i : Fin (2 * N - 1) =>
    let convolution_start := i.val - (N - 1)   -- truncated substraction
    let convolution_end := min i.val (N - 1)
    let convolution_range :=
      List.range (convolution_end + 1 - convolution_start) |>.map (convolution_start + .)
    have h : ∀ j ∈ convolution_range, j < N ∧ i - j < N := by
      simp [convolution_range, convolution_start, convolution_end]; omega
    let summands := convolution_range.pmap (fun j h' => x ⟨j,h'.1⟩ * y ⟨i - j, h'.2⟩) h
    have : summands ≠ [] := by simp [convolution_range, summands]; omega
    summands.tail.foldl (. + .) (summands.head this)

lemma convolution_range_to_Finset_eq (N : Nat) (i : Fin (2 * N - 1)) :
    let convolution_start := i.val - (N - 1)   -- truncated substraction
    let convolution_end := min i.val (N - 1)
    let convolution_range :=
      List.range (convolution_end + 1 - convolution_start) |>.map (convolution_start + .)
    convolution_range.toFinset = Finset.Icc convolution_start convolution_end := by
  ext n
  simp only [List.mem_toFinset, List.mem_map, List.mem_range, Finset.mem_Icc, tsub_le_iff_right,
    le_inf_iff]
  constructor
  . rintro ⟨a, ha, h1, rfl⟩; omega
  . rintro ⟨h1, h2, h3⟩
    use n - (i.val - (N - 1))
    constructor
    . omega
    omega

lemma Nodup_convolution_range (N : Nat) (i : Fin (2 * N - 1)) :
    let convolution_start := i.val - (N - 1)   -- truncated substraction
    let convolution_end := min i.val (N - 1)
    let convolution_range :=
      List.range (convolution_end + 1 - convolution_start) |>.map (convolution_start + .)
    convolution_range.Nodup := by
  rw [List.nodup_map_iff]; apply List.nodup_range
  simp [Function.Injective]

def simple_convolution_val' (N : Nat) (x y : Fin N → Felt) : Fin (2 * N - 1) → Felt :=
  fun i : Fin (2 * N - 1) =>
    let convolution_start := i.val - (N - 1)   -- truncated substraction
    let convolution_end := min i.val (N - 1)
    let convolution_range :=
      List.range (convolution_end + 1 - convolution_start) |>.map (convolution_start + .)
    have h : ∀ j ∈ convolution_range, j < N ∧ i - j < N := by
      simp [convolution_range, convolution_start, convolution_end]; omega
    let summands := convolution_range.pmap (fun j h' => x ⟨j,h'.1⟩ * y ⟨i - j, h'.2⟩) h
    summands.sum

def simple_convolution_val {R : Type*} [CommSemiring R]
    (N : Nat) [NeZero N] (x y : Fin N → R) : Fin (2 * N - 1) → R :=
  fun i : Fin (2 * N - 1) =>
    let convolution_start := i.val - (N - 1)
    let convolution_end := min i.val (N - 1)
    let convolution_range := Finset.Icc convolution_start convolution_end
    ∑ j ∈ convolution_range, x ↑j * y ↑(i.val - j)

def cast_simple_convolution_val_eq {R : Type*} [CommSemiring R]
    (N : Nat) [NeZero N] (xn yn : Fin N → Nat) :
    simple_convolution_val N (fun i => (xn i : R)) (fun i => (yn i : R)) =
      fun i => ↑(simple_convolution_val N xn yn i) := by
  unfold simple_convolution_val; ext i; simp

theorem simple_convolution_val_bound (N : Nat) [NeZero N] (bound : Nat)
    (xn yn : Fin N → Nat)
    (hx : ∀ i, xn i ≤ bound) (hy : ∀ i, yn i ≤ bound) :
    ∀ i : Fin (2 * N - 1), simple_convolution_val N xn yn i ≤ N * bound * bound := by
  unfold simple_convolution_val; dsimp
  intro i
  have : ∀ s : Finset Nat, ∀ j ∈ s, xn ↑j * yn ↑(i.val - j) ≤ bound * bound :=
    fun _ j _ => Nat.mul_le_mul (hx _) (hy _)
  trans; apply Finset.sum_le_card_nsmul _ _ _ (this _)
  simp only [Nat.card_Icc, smul_eq_mul, mul_assoc]; gcongr; omega

theorem simple_convolution_val'_eq_simple_convolution_val
    (N : Nat) [NeZero N] (x y : Fin N → Felt) :
    simple_convolution_val' N x y = simple_convolution_val N x y := by
  ext i; simp -zeta only [simple_convolution_val, simple_convolution_val']
  lift_lets; intro convolution_start convolution_end convolution_range convolution_range'
  have h : ∀ j ∈ convolution_range, j < N ∧ i - j < N := by
      simp [convolution_range, convolution_start, convolution_end]; omega
  let summands := convolution_range.pmap (fun j (h' : j < N ∧ i - j < N)  => x ↑j * y ↑(i - j)) h
  dsimp
  trans summands.sum
  . congr
    ext j h'
    congr
    . rw [Nat.mod_eq_of_lt h'.1]
    . rw [Nat.mod_eq_of_lt h'.2]
  dsimp [summands]
  rw [List.pmap_eq_map, Finset.sum_list_map_count]
  apply Finset.sum_congr
  . dsimp [convolution_range']
    rw [convolution_range_to_Finset_eq]
  intro j hj
  rw [List.count_eq_of_nodup, if_pos]; simp; swap
  . apply Nodup_convolution_range
  rwa [←List.mem_toFinset, convolution_range_to_Finset_eq]

theorem simple_convolution_val_distrib_left (N : Nat) [NeZero N] (x y0 y1 : Fin N → Felt) :
    simple_convolution_val N x (y0 + y1) =
      simple_convolution_val N x y0 + simple_convolution_val N x y1 := by
  unfold simple_convolution_val
  ext i; dsimp
  rw [←Finset.sum_add_distrib]; simp [mul_add]

theorem simple_convolution_val_distrib_right (N : Nat) [NeZero N] (x0 x1 y : Fin N → Felt) :
    simple_convolution_val N (x0 + x1) y =
      simple_convolution_val N x0 y + simple_convolution_val N x1 y := by
  unfold simple_convolution_val
  ext i; dsimp
  rw [←Finset.sum_add_distrib]; simp [add_mul]

theorem simple_convolution_comm (N : Nat) [NeZero N] (x y : Fin N → Felt) :
    simple_convolution_val N x y = simple_convolution_val N y x := by
  unfold simple_convolution_val
  ext i; simp
  let flip := fun j => i.val - j
  have : (Finset.Icc (i.val - (N - 1)) (i.val ⊓ (N - 1)) |>.image flip) =
      Finset.Icc (i.val - (N - 1)) (i.val ⊓ (N - 1)) := by
    ext j; simp only [Finset.mem_image, Finset.mem_Icc, tsub_le_iff_right, le_inf_iff, flip]
    constructor
    . rintro ⟨k, hk⟩; omega
    . intro h; use i.val - j; omega
  conv => lhs; rw [←this]
  rw [Finset.sum_image]; swap
  . simp [flip, Set.InjOn]; omega
  apply Finset.sum_congr rfl
  simp [flip]; intro j hj0 hj1 hj2; rw [mul_comm]
  congr; omega

theorem eval_simple_convolution_eq_aux [Fact (Nat.Prime Stwo.P)]
      (N : Nat) (x y : Fin N → FeltExpr) (varAssign : VarAssign) :
    ∀ i : Fin (2 * N - 1),
      (simple_convolution N x y i).eval varAssign =
        simple_convolution_val' N (FeltExpr.eval varAssign ∘ x) (FeltExpr.eval varAssign ∘ y) i := by
  intro i
  dsimp -zeta only [simple_convolution, simple_convolution_val']
  lift_lets
  intro convolution_start convolution_end convolution_range
  dsimp
  rw [FeltExpr.eval_foldl_add, sum_eq_foldl]; swap
  . simp; omega
  simp [convolution_range, List.map_pmap]

theorem eval_simple_convolution_eq [Fact (Nat.Prime Stwo.P)] {N : Nat}
    (x y : Fin N → FeltExpr)
    (varAssign : VarAssign) :
    FeltExpr.eval varAssign ∘ (simple_convolution N x y) =
      simple_convolution_val' N (FeltExpr.eval varAssign ∘ x)
        (FeltExpr.eval varAssign ∘ y) := by
  ext i; apply eval_simple_convolution_eq_aux

lemma simple_convolution_val_spec_aux (N : Nat) [NeZero N] : Finset.range N ×ˢ Finset.range N =
  (Finset.range (2 * N - 1) |>.biUnion fun i =>
    (Finset.Icc (i - (N - 1)) (min i (N - 1)) |>.image fun j => (j, i - j))) := by
  ext p; simp; constructor
  . rintro ⟨h1, h2⟩
    use p.1 + p.2
    constructor
    . omega
    . use p.1; simp; omega
  . rintro ⟨i, hi, j, ⟨hj1, hj2⟩, rfl⟩; simp; omega

theorem simple_convolution_val_spec {R : Type*} [CommSemiring R]
    (N : Nat) [NeZero N] (base : R) (x y : Fin N → R) :
    eval_poly base (simple_convolution_val N x y) =
      eval_poly base x * eval_poly base y := by
  have : NeZero (2 * N - 1) := by
    simp_all [neZero_iff]; omega
  simp only [eval_poly_eq_eval_poly', eval_poly', Finset.mul_sum, Finset.sum_mul]
  trans (∑ p ∈ Finset.range N ×ˢ Finset.range N, x ↑p.1 * base ^ p.1 * (y ↑p.2 * base ^ p.2))
  . rw [simple_convolution_val_spec_aux, Finset.sum_biUnion]
    . apply Finset.sum_congr rfl
      intro n
      rw [Finset.mem_range]; intro hn
      rw [simple_convolution_val, Finset.sum_image]; swap
      . intro x; simp; tauto
      rw [Finset.sum_mul]
      apply Finset.sum_congr
      . rw [Fin.val_natCast, Nat.mod_eq_of_lt hn]
      simp only [Finset.mem_Icc, tsub_le_iff_right, le_inf_iff, Fin.val_natCast, and_imp]
      intro i hi1 hi2 hi3
      rw [Nat.mod_eq_of_lt hn]
      ring_nf
      simp only [mul_assoc]; congr
      rw [←pow_add]
      simp [*]
    rw [Finset.pairwiseDisjoint_iff]; simp only [Finset.coe_range, Set.mem_Iio]
    intro i hi j hj ⟨x, hx⟩
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_Icc, tsub_le_iff_right,
      le_inf_iff] at hx
    rcases hx with ⟨⟨u, ⟨hu1, hu2, hu3⟩⟩, ⟨v, ⟨⟨hv1, hv2⟩, hv3⟩⟩⟩
    simp at hv3
    omega
  . simp [Finset.sum_product]; rw [Finset.sum_comm]



def karatsuba_finish {N : Nat} (z0 z2 z3 : Fin N → FeltExpr) :
    Fin (2 * N + 1) → FeltExpr :=
  let ceil_half_len := (N + 1) / 2
  let aux : Fin (2 * N + 1) → FeltExpr :=
    fun i : Fin (2 * N + 1) =>
      if h : i.val < N then
        z0 ⟨i.val, h⟩
      else if h' : i.val = N then
        FeltExpr.const 0
      else
        z2 ⟨i.val - (N + 1), by omega⟩
  fun i : Fin (2 * N + 1) =>
    if h : i.val < ceil_half_len then
      aux i
    else if h' : i.val < ceil_half_len + N then
      let i' : Fin N := ⟨i.val - ceil_half_len, by omega⟩
      aux i + (z3 i' - z0 i' - z2 i')
    else
      aux i

def karatsuba_finish_val {N : Nat} (z0 z2 z3 : Fin N → Felt) :
    Fin (2 * N + 1) → Felt :=
  let ceil_half_len := (N + 1) / 2
  let aux : Fin (2 * N + 1) → Felt :=
    fun i : Fin (2 * N + 1) =>
      if h : i.val < N then
        z0 ⟨i.val, h⟩
      else if h' : i.val = N then
        0
      else
        z2 ⟨i.val - (N + 1), by omega⟩
  fun i : Fin (2 * N + 1) =>
    if h : i.val < ceil_half_len then
      aux i
    else if h' : i.val < ceil_half_len + N then
      let i' : Fin N := ⟨i.val - ceil_half_len, by omega⟩
      aux i + (z3 i' - z0 i' - z2 i')
    else
      aux i

theorem eval_karatsuba_finish_eq [Fact (Nat.Prime Stwo.P)] {N : Nat}
    (z0 z2 z3 : Fin N → FeltExpr)
    (varAssign : VarAssign) :
    FeltExpr.eval varAssign ∘ (karatsuba_finish z0 z2 z3) =
      karatsuba_finish_val (FeltExpr.eval varAssign ∘ z0)
        (FeltExpr.eval varAssign ∘ z2) (FeltExpr.eval varAssign ∘ z3) := by
  unfold karatsuba_finish karatsuba_finish_val
  ext j
  simp only [Function.comp_apply, apply_dite (FeltExpr.eval varAssign), FeltExpr.eval_add,
    FeltExpr.eval_sub]
  rfl

def karatsuba_finish_val' {k : Nat} (z0 z2 z3 : Fin (2 * k + 1) → Felt) :
    Fin (2 * (2 * k + 1) + 1) → Felt :=
  let z1 := z3 - z0 - z2
  fun i : Fin (2 * (2 * k + 1) + 1) =>
    if h0 : i.val < k + 1 then z0 ⟨i.val, by omega⟩
    else if h1 : i.val < 2 * k + 1 then
      let i' : Fin (2 * k + 1) := ⟨i.val - (k + 1), by omega⟩
      z0 ⟨i.val, by omega⟩ + z1 i'
    else if h2 : i.val = 2 * k + 1 then
      let i' : Fin (2 * k + 1) := ⟨k, by omega⟩
      z1 i'
    else if h3 : i.val < 3 * k + 2 then
      let i0 : Fin (2 * k + 1) := ⟨i.val - 2 * (k + 1), by omega⟩
      let i' : Fin (2 * k + 1) := ⟨i.val - (k + 1), by omega⟩
      z2 i0 + z1 i'
    else
      have := i.isLt
      let i0 : Fin (2 * k + 1) := ⟨i.val - 2 * (k + 1), by omega⟩
      z2 i0

theorem karatsuba_finish_val_eq_karatsuba_finish_val' {k : Nat}
    (z0 z2 z3 : Fin (2 * k + 1) → Felt) :
    karatsuba_finish_val z0 z2 z3 = karatsuba_finish_val' z0 z2 z3 := by
  ext i
  rw [karatsuba_finish_val']; dsimp
  split_ifs <;> (dsimp -zeta [karatsuba_finish_val]; lift_lets; intro ceil_half_len aux; dsimp)
  . rw [dif_pos]; dsimp [aux]; rw [dif_pos]; omega
  . rw [dif_neg, dif_pos]; dsimp [aux]; rw [dif_pos]; congr
    all_goals { omega }
  . rw [dif_neg, dif_pos]; dsimp [aux]; rw [dif_neg, dif_pos, zero_add]; congr
    all_goals { omega }
  . rw [dif_neg, dif_pos]; dsimp [aux]; rw [dif_neg, dif_neg]; congr 1; congr
    all_goals { omega }
  . rw [dif_neg, dif_neg]; dsimp [aux]; rw [dif_neg, dif_neg]; congr 1; congr
    all_goals { omega }

-- Note the use of 2 * k + 1 rather than 2 * k - 1. It's more convenient than working with
-- the assumption `k ≠ 0`.

theorem karatsuba_finish_val_spec (k m : Nat) (hm : m = 2 * (k + 1))
    (x y : Fin m → Felt) :
    let x0 : Fin (k + 1) → Felt := x ∘ Fin.castLE (by omega)
    let x1 : Fin (k + 1) → Felt := x ∘
      (fun i => Fin.cast (show (k + 1) + (k + 1) = m by rw [hm]; omega) (Fin.natAdd (k + 1) i))
    let y0 : Fin (k + 1) → Felt := y ∘ Fin.castLE (by omega)
    let y1 : Fin (k + 1) → Felt := y ∘
      (fun i => Fin.cast (show (k + 1) + (k + 1) = m by rw [hm]; omega) (Fin.natAdd (k + 1) i))
    ∀ z0 : Fin (2 * (k + 1) - 1) → Felt,
      z0 = simple_convolution_val _ x0 y0 →
    ∀ z2 : Fin (2 * (k + 1) - 1) → Felt,
      z2 = simple_convolution_val _ x1 y1 →
    ∀ z3 : Fin (2 * (k + 1) - 1) → Felt,
      z3 = simple_convolution_val _ (x0 + x1) (y0 + y1) →
    ∀ i,
      have : NeZero m := by rw [neZero_iff]; omega
      karatsuba_finish_val' z0 z2 z3 i = simple_convolution_val _ x y ⟨i.val, by omega⟩ := by
  subst hm
  intro x0 x1 y0 y1 z0 hz0 z2 hz2 z3 hz3 i; dsimp
  rw [hz0, hz2, hz3]; clear hz0 z0 hz2 z2 hz3 z3
  dsimp (zeta := false) only [karatsuba_finish_val']
  lift_lets; intro z1; dsimp
  have : z1 = simple_convolution_val _ x0 y1 + simple_convolution_val _ x1 y0 := by
    simp [z1, simple_convolution_val_distrib_left, simple_convolution_val_distrib_right]; ring
  rw [this]; clear z1 this
  split
  . unfold simple_convolution_val; dsimp
    rw [tsub_eq_zero_of_le (by omega), tsub_eq_zero_of_le (by omega), Nat.min_eq_left (by omega),
      Nat.min_eq_left (by omega)]
    apply Finset.sum_congr rfl
    simp [x0, y0]; intro j hj; congr
    . rw [Nat.mod_eq_of_lt]; omega
    . rw [Nat.mod_eq_of_lt]; omega
  split
  . unfold simple_convolution_val; dsimp
    rw [Nat.min_eq_right (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    have : i.val ≤ (k + 1) + k := by omega
    rw [←Nat.sub_add_eq, tsub_eq_zero_of_le this]; clear this
    have : i.val ≤ 2 * (k + 1) - 1 := by omega
    rw [tsub_eq_zero_of_le this]; clear this
    have : Finset.Icc 0 i.val = Finset.Icc (i.val - k) k ∪ Finset.Icc 0 (i.val - (k + 1)) ∪
      Finset.Icc (k + 1) i.val := by
      ext x; simp; omega
    rw [this, Finset.sum_union, Finset.sum_union]; swap
    . rw [Finset.disjoint_iff_ne]; simp; omega
    swap; rw [Finset.disjoint_iff_ne]; simp; omega
    rw [add_assoc]; congr 1
    . apply Finset.sum_congr rfl
      simp [x0, y0]; intro j hj0 hj1; congr
      . rw [Nat.mod_eq_of_lt]; omega
      . rw [Nat.mod_eq_of_lt]; omega
    congr 1
    . apply Finset.sum_congr rfl
      simp [x0, y1]; intro j hj0; congr
      . simp; omega
      . ext; simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
    have : Finset.Icc (k + 1) ↑i = (Finset.Icc 0 (↑i - (k + 1))).image (. + (k + 1)) := by
      ext j; simp; omega
    rw [this, Finset.sum_image]; swap
    . intro j; simp
    apply Finset.sum_congr rfl
    simp only [Finset.mem_Icc, zero_le, true_and, Fin.natAdd_eq_addNat, Function.comp_apply,
      x1, y0]; intro j hj0; congr
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; omega
    . ext; simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;>
        try omega
      rw [Nat.mod_eq_of_lt] <;> omega
  split
  . unfold simple_convolution_val; dsimp
    rw [tsub_self, min_self, tsub_eq_zero_of_le (by omega), Nat.min_eq_left (by omega)]
    have : Finset.Icc 0 ↑i = Finset.Icc 0 k ∪ Finset.Icc (k + 1) (2 * k + 1) := by
      ext x; simp; omega
    rw [this, Finset.sum_union]; swap
    . rw [Finset.disjoint_iff_ne]; simp; omega
    congr 1
    . apply Finset.sum_congr rfl
      simp [x0, y1]; intro j hj; congr
      . rw [Nat.mod_eq_of_lt]; omega
      . ext; simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
    have : Finset.Icc (k + 1) (2 * k + 1) = (Finset.Icc 0 k).image (. + (k + 1)) := by
      ext j; simp; omega
    rw [this, Finset.sum_image]; swap
    . intro j; simp
    apply Finset.sum_congr rfl
    simp [-Nat.cast_sub, -Nat.cast_add, x1, y0]
    intro j hj
    congr
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; omega
    . rw [Nat.mod_eq_of_lt] <;> omega
  split
  . unfold simple_convolution_val; dsimp
    rw [tsub_eq_zero_of_le (by omega), Nat.min_eq_left (by omega), Nat.min_eq_right (by omega),
      Nat.min_eq_right (by omega)]
    have : Finset.Icc (↑i - (2 * (k + 1) - 1)) (2 * (k + 1) - 1) =
      Finset.Icc (k + 1) (↑i - (k + 1)) ∪ Finset.Icc (↑i - (2 * (k + 1) - 1)) k ∪
        Finset.Icc (↑i - k) (2 * (k + 1) - 1) := by
      ext x; simp; omega
    rw [this, Finset.sum_union, Finset.sum_union]; swap
    . rw [Finset.disjoint_iff_ne]; simp; omega
    swap; rw [Finset.disjoint_iff_ne]; simp; omega
    rw [add_assoc]; congr 1
    . have : Finset.Icc (k + 1) (↑i - (k + 1)) = (Finset.Icc 0 (↑i - (2 * (k + 1)))).image (. + (k + 1)) := by
        ext j; simp; omega
      rw [this, Finset.sum_image]; swap
      . intro j; simp
      apply Finset.sum_congr rfl
      simp only [Finset.mem_Icc, zero_le, true_and, x1, y1]; dsimp
      intro j hj0; congr
      . ext; rw [Fin.val_cast_of_lt]; swap; omega
        simp; omega
      . ext; rw [Fin.val_cast_of_lt]; swap; omega
        simp; rw [Nat.mod_eq_of_lt] <;> omega
    congr 1
    . apply Finset.sum_congr
      . congr 1; omega
      simp only [Finset.mem_Icc, tsub_le_iff_right, and_imp, x0, y1]
      intro j hj0 hj1; dsimp
      congr
      . simp; rw [Nat.mod_eq_of_lt]; omega
      . ext; simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
    have : Finset.Icc (↑i - k) (2 * (k + 1) - 1) =
        (Finset.Icc (↑i - (k + 1) - k) k).image (. + (k + 1)) := by
      ext; simp; omega
    rw [this, Finset.sum_image]; swap
    . rintro - - - -; simp
    apply Finset.sum_congr rfl
    simp only [Finset.mem_Icc, tsub_le_iff_right, and_imp, x1, y0]
    intro j hj0 hj1; dsimp
    congr
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; omega
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> try omega
      rw [Nat.mod_eq_of_lt] <;> omega
  . unfold simple_convolution_val; dsimp
    rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    have : Finset.Icc (↑i - (2 * (k + 1) - 1)) (2 * (k + 1) - 1) =
        (Finset.Icc (↑i - 2 * (k + 1) - k) k).image (. + (k + 1)) := by
      ext x; simp; omega
    rw [this, Finset.sum_image]; swap
    . intro j; simp
    apply Finset.sum_congr rfl
    simp only [Finset.mem_Icc, tsub_le_iff_right, and_imp, x1, y1]
    intro j hj0 hj1; dsimp
    congr
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; omega
    . ext; rw [Fin.val_cast_of_lt]; swap; omega
      simp; rw [Nat.mod_eq_of_lt] <;> omega



-- TODO(Jeremy): move this

namespace AirBuilder

def letRec (ab : AirBuilder) {N : Nat} (exprs : Fin N → FeltExpr) :
    AirBuilder × (Fin N → FeltExpr) :=
  Fin.hIterate (P := fun i => AirBuilder × (Fin i → FeltExpr))
    (init := (ab, Fin.elim0))
    (n := N)
    (f := fun i p1 =>
      let ab_prev := p1.1
      let tuple_prev := p1.2
      let aux1 := ab_prev.letForConstraint (exprs i)
      (aux1.1, Fin.snoc tuple_prev aux1.2))

@[simp]
theorem letRec_SatisfiedBy [Fact (Nat.Prime Stwo.P)]
    (ab : AirBuilder) {N : Nat} [NeZero N] (exprs : Fin N → FeltExpr) (varAssign : VarAssign) :
  (ab.letRec exprs).1.SatisfiedBy varAssign ↔
    ab.SatisfiedBy varAssign ∧
      ∀ i, ((ab.letRec exprs).2 i).eval varAssign = (exprs i).eval varAssign := by
  let P := fun i => AirBuilder × (Fin i → FeltExpr)
  let Q : ∀ i : Nat, P i → Prop := fun i p =>
    p.1.SatisfiedBy varAssign ↔
      ab.SatisfiedBy varAssign ∧
      ∀ j, (p.2 j).eval varAssign = (exprs j).eval varAssign
  convert Fin.hIterate_elim Q _ _ _ _; simp
  . simp [Q]
  . intro k p
    dsimp [Q]
    intro h
    rw [letForConstraint_SatisfiedBy, h, and_assoc]
    apply and_congr_right'
    constructor
    . intro h j
      rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      . convert h.1 j using 1; simp
      . convert h.2 <;> simp
    . intro h
      constructor
      . intro j
        convert h j.castSucc using 1; simp
      . convert h (Fin.last k) using 2 <;> simp

end AirBuilder

namespace SingleKaratsuba

def call (N : Nat) (ab : AirBuilder) (x y : Fin (2 * N) → FeltExpr) :
    AirBuilder × (Fin (2 * (2 * N - 1) + 1) → FeltExpr) :=
  let x0 : Fin N → FeltExpr := x ∘ Fin.castLE (by omega)
  let x1 : Fin N → FeltExpr := x ∘
    (fun i => Fin.cast (show N + N = 2 * N by omega) (Fin.natAdd N i))
  let y0 : Fin N → FeltExpr := y ∘ Fin.castLE (by omega)
  let y1 : Fin N → FeltExpr := y ∘
    (fun i => Fin.cast (show N + N = 2 * N by omega) (Fin.natAdd N i))

  let z0_aux : Fin (2 * N - 1) → FeltExpr := simple_convolution N x0 y0
  let ab1_aux := ab.letRec z0_aux
  let ab1 := ab1_aux.1
  let z0 : Fin (2 * N - 1) → FeltExpr := ab1_aux.2

  let z2_aux : Fin (2 * N - 1) → FeltExpr := simple_convolution N x1 y1
  let ab2_aux := ab1.letRec z2_aux
  let ab2 := ab2_aux.1
  let z2 : Fin (2 * N - 1) → FeltExpr := ab2_aux.2

  let sum_x_aux : Fin N → FeltExpr := fun i => x0 i + x1 i
  let ab3_aux := ab2.letRec sum_x_aux
  let ab3 := ab3_aux.1
  let x_sum : Fin N → FeltExpr := ab3_aux.2

  let sum_y_aux : Fin N → FeltExpr := fun i => y0 i + y1 i
  let ab4_aux := ab3.letRec sum_y_aux
  let ab4 := ab4_aux.1
  let y_sum : Fin N → FeltExpr := ab4_aux.2

  let z3 := simple_convolution N x_sum y_sum
  (ab4, karatsuba_finish z0 z2 z3)

def auto_spec (x y : Fin (2 * N) → Felt) (ρout : Fin (2 * (2 * N - 1) + 1) → Felt) :=
  let x0 : Fin N → Felt := x ∘ Fin.castLE (by omega)
  let x1 : Fin N → Felt := x ∘
    (fun i => Fin.cast (show N + N = 2 * N by omega) (Fin.natAdd N i))
  let y0 : Fin N → Felt := y ∘ Fin.castLE (by omega)
  let y1 : Fin N → Felt := y ∘ (fun i => Fin.cast (show N + N = 2 * N by omega) (Fin.natAdd N i))
  let z0 : Fin (2 * N - 1) → Felt := simple_convolution_val' N x0 y0
  let z2 : Fin (2 * N - 1) → Felt := simple_convolution_val' N x1 y1
  let x_sum : Fin N → Felt := x0 + x1
  let y_sum : Fin N → Felt := y0 + y1
  let z3 : Fin (2 * N - 1) → Felt := simple_convolution_val' N x_sum y_sum
  ρout = karatsuba_finish_val z0 z2 z3

def spec [NeZero N] (x y : Fin (2 * N) → Felt) (ρout : Fin (2 * (2 * N - 1) + 1) → Felt) :=
  ρout = simple_convolution_val _ x y ∘ Fin.cast (by have := NeZero.ne N; omega)

theorem spec_of_auto_spec (k : Nat)
    (x y : Fin (2 * (k + 1)) → Felt)
    (ρout : Fin (2 * (2 * (k + 1) - 1) + 1) → Felt)
    (h_spec : auto_spec x y ρout) :
    spec x y ρout := by
  unfold auto_spec at h_spec
  revert h_spec
  lift_lets
  rintro x0 x1 y0 y1 z0 z2 x_sum y_sum z3 rfl
  rw [spec, karatsuba_finish_val_eq_karatsuba_finish_val']
  ext i
  apply karatsuba_finish_val_spec
  . unfold z0; rw [simple_convolution_val'_eq_simple_convolution_val]
  . unfold z2; rw [simple_convolution_val'_eq_simple_convolution_val]
  . unfold z3; rw [simple_convolution_val'_eq_simple_convolution_val]
  . rfl

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    (N : Nat) [NeZero N]
    (x y : Fin (2 * N) → FeltExpr)
    (varAssign : VarAssign)
    (ab : AirBuilder):
    let ⟨new_ab, ρout⟩ := call N ab x y
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (FeltExpr.eval varAssign ∘ x) (FeltExpr.eval varAssign ∘ y)
        (FeltExpr.eval varAssign ∘ ρout) := by
  unfold call; lift_lets
  intro x0 x1 y0 y1 z0_aux ab1_aux ab1 z0 z2_aux ab2_aux ab2 z2 sum_x_aux ab3_aux ab3 x_sum
    sum_y_aux ab4_aux ab4 y_sum z3 hab4
  have ⟨hab3, h3⟩ := (ab3.letRec_SatisfiedBy _ _).mp hab4
  have ⟨hab2, h2⟩ := (ab2.letRec_SatisfiedBy _ _).mp hab3
  have : NeZero (2 * N - 1) := by simp_all [neZero_iff]; omega
  have ⟨hab1, h1⟩ := (ab1.letRec_SatisfiedBy _ _).mp hab2
  have ⟨hab, h0⟩ := (ab.letRec_SatisfiedBy _ _).mp hab1
  use hab
  rcases N with _ | k
  . simp at this
  apply spec_of_auto_spec
  rw [auto_spec, eval_karatsuba_finish_eq, eval_simple_convolution_eq]
  apply congr; apply congr; apply congr_arg
  . ext i
    trans; apply h0 i
    rw [eval_simple_convolution_eq_aux]
    congr
  . ext i
    trans; apply h1 i
    rw [eval_simple_convolution_eq_aux]
    congr
  . ext i
    congr 1
    . ext j; dsimp
      rw [←FeltExpr.eval_add]
      apply h2 j
    . ext j; dsimp
      rw [←FeltExpr.eval_add]
      apply h3 j

end SingleKaratsuba



namespace DoubleKaratsuba

def call (ab : AirBuilder) (N : Nat) (x y : Fin (4 * N) → FeltExpr) :
    AirBuilder × (Fin (2 * (2 * (2 * N - 1) + 1) + 1) → FeltExpr) :=
  let x0 : Fin (2 * N) → FeltExpr := x ∘ Fin.castLE (by omega)
  let x1 : Fin (2 * N) → FeltExpr := x ∘
    (fun i => Fin.cast (show 2 * N + 2 * N = 4 * N by omega) (Fin.natAdd (2 * N) i))
  let y0 : Fin (2 * N) → FeltExpr := y ∘ Fin.castLE (by omega)
  let y1 : Fin (2 * N) → FeltExpr := y ∘
    (fun i => Fin.cast (show 2 * N + 2 * N = 4 * N by omega) (Fin.natAdd (2 * N) i))

  let ab1_z0 := SingleKaratsuba.call N ab x0 y0
  let ab2_z2 := SingleKaratsuba.call N ab1_z0.1 x1 y1

  let x_sum : Fin (2 * N) → FeltExpr := x0 + x1
  let y_sum : Fin (2 * N) → FeltExpr := y0 + y1

  let ab3_z3 := SingleKaratsuba.call N ab2_z2.1 x_sum y_sum
  -- Note: we are using `FeltExpr`s rather than `BoundedFeltExpr`s
  let result_exprs := karatsuba_finish ab1_z0.2 ab2_z2.2 ab3_z3.2
  (ab3_z3.1, result_exprs)

def auto_spec [NeZero N] (x y : Fin (4 * N) → Felt)
    (ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt) :=
  let x0 : Fin (2 * N) → Felt := x ∘ Fin.castLE (by omega)
  let x1 : Fin (2 * N) → Felt := x ∘
    (fun i => Fin.cast (show 2 * N + 2 * N = 4 * N by omega) (Fin.natAdd (2 * N) i))
  let y0 : Fin (2 * N) → Felt := y ∘ Fin.castLE (by omega)
  let y1 : Fin (2 * N) → Felt := y ∘
    (fun i => Fin.cast (show 2 * N + 2 * N = 4 * N by omega) (Fin.natAdd (2 * N) i))
  ∃ z0, SingleKaratsuba.spec x0 y0 z0 ∧
  ∃ z2, SingleKaratsuba.spec x1 y1 z2 ∧
    let x_sum : Fin (2 * N) → Felt := x0 + x1
    let y_sum : Fin (2 * N) → Felt := y0 + y1
  ∃ z3, SingleKaratsuba.spec x_sum y_sum z3 ∧
    ρout = karatsuba_finish_val z0 z2 z3

def spec [NeZero N] (x y : Fin (4 * N) → Felt) (ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt) :=
  ρout = simple_convolution_val _ x y ∘ Fin.cast (by have := NeZero.ne N; omega)

theorem spec_of_auto_spec (k : Nat)
    (x y : Fin (4 * (k + 1)) → Felt)
    (ρout : Fin (2 * (2 * (2 * (k + 1) - 1) + 1) + 1) → Felt)
    (h_spec : auto_spec x y ρout) :
    spec x y ρout := by
  unfold auto_spec at h_spec
  revert h_spec; lift_lets
  rintro x0 x1 y0 y1 x_sum y_sum ⟨z0, hz0, z2, hz2, z3, hz3, rfl⟩
  rw [spec, karatsuba_finish_val_eq_karatsuba_finish_val']
  ext i
  apply karatsuba_finish_val_spec
  . apply hz0
  . apply hz2
  . apply hz3
  . omega

def spec' [NeZero N] (x y : Fin (4 * N) → Felt) (ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt) :=
  ∀ i, ρout i = simple_convolution_val _ x y ⟨i.val, by have := i.isLt; have := NeZero.ne N; omega⟩

theorem spec'_of_spec [NeZero N]
    {x y : Fin (4 * N) → Felt}
    {ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt}
    (h_spec : spec x y ρout) :
    spec' x y ρout := by
  unfold spec spec' at *
  intro i; rw [h_spec]; rfl

def spec_alt [NeZero N]
    (x y : Fin (4 * N) → Felt)
    (ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt)
    (base : Felt) :=
  eval_poly base ρout = eval_poly base x * eval_poly base y

theorem spec_alt_of_spec [Fact (Nat.Prime Stwo.P)] [NeZero N]
    {x y : Fin (4 * N) → Felt}
    {ρout : Fin (2 * (2 * (2 * N - 1) + 1) + 1) → Felt}
    (base : Felt)
    (h_spec : spec x y ρout) :
    spec_alt x y ρout base := by
  unfold spec spec_alt at *
  subst h_spec
  rw [←simple_convolution_val_spec]
  congr 1
  . have := NeZero.ne N; omega
  rw [Fin.heq_fun_iff]; swap
  . have := NeZero.ne N; omega
  intro i; rfl

theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    (N : Nat) [nez : NeZero N]
    (x y : Fin (4 * N) → FeltExpr)
    (varAssign : VarAssign)
    (ab : AirBuilder):
    let ⟨new_ab, ρout⟩ := call ab N x y
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (FeltExpr.eval varAssign ∘ x) (FeltExpr.eval varAssign ∘ y)
        (FeltExpr.eval varAssign ∘ ρout) := by
  unfold call; lift_lets
  intro x0 x1 y0 y1 ab1_z0 ab2_z2 x_sum y_sum ab3_z3 result hab3
  have ⟨hab2, h2⟩ := SingleKaratsuba.sound_auto N x_sum y_sum varAssign ab2_z2.1 hab3
  have ⟨hab1, h1⟩ := SingleKaratsuba.sound_auto N x1 y1 varAssign ab1_z0.1 hab2
  have ⟨hab, h0⟩ := SingleKaratsuba.sound_auto N x0 y0 varAssign ab hab1
  use hab
  rcases N with _ | k
  . simp at nez
  apply spec_of_auto_spec
  rw [auto_spec]
  use (FeltExpr.eval varAssign ∘ ab1_z0.2), h0, (FeltExpr.eval varAssign ∘ ab2_z2.2), h1,
    (FeltExpr.eval varAssign ∘ ab3_z3.2), h2
  rw [eval_karatsuba_finish_eq]

end DoubleKaratsuba
