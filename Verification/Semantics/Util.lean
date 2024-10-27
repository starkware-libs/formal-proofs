import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fin.Basic
import Init.Data.BitVec.Lemmas
import Verification.Semantics.SimpAttr

open scoped BigOperators

@[class] structure CharGe263 (F : Type _) [Field F] where
  h : ringChar F ≥ 2 ^ 63

/- some generic simplifier rules -/
theorem add_neg_eq_sub {G : Type _} [AddGroup G] (a b : G) : a + -b = a - b := by
  rw [sub_eq_add_neg]

theorem sub_add_eq_add_neg_add {G : Type _} [AddGroup G] (a b c : G) : a - b + c = a + (-b + c) :=
  by rw [sub_eq_add_neg, add_assoc]

attribute [simp] Bool.toNat

namespace Int

theorem abs_le_of_dvd {i j : Int} (h : i ∣ j) (h' : 0 < j) : abs i ≤ j :=
  Int.le_of_dvd h' ((abs_dvd _ _).mpr h)

theorem modEq_iff_sub_mod_eq_zero {i j m : ℤ} : i ≡ j [ZMOD m] ↔ (i - j) % m = 0 := by
  rw [Int.modEq_iff_dvd, ← neg_sub, dvd_neg, Int.dvd_iff_emod_eq_zero]

end Int

attribute [int_cast_simps] Int.ofNat_zero Int.ofNat_one Int.ofNat_add
  Int.coe_nat_pow Int.cast_add Int.cast_mul Int.cast_sub Int.cast_zero
  Int.cast_one

macro (name := simp_int_casts) "simp_int_casts" : tactic => `(tactic|
  simp only [int_cast_simps] )

macro (name := simp_int_casts_at) "simp_int_casts_at" h:ident : tactic => `(tactic|
  simp only [int_cast_simps] at ($h) )

/- option -/
namespace Option

def Agrees {α : Type _} : Option α → α → Prop
  | some a, b => a = b
  | none, _ => True

def FnExtends {α β : Type _} (f : α → β) (f' : α → Option β) : Prop :=
  ∀ x, (f' x).Agrees (f x)

theorem eq_of_fnExtends {α β : Type _} {f : α → β} {f' : α → Option β} (h : FnExtends f f') {a : α}
    {b : β} (h' : f' a = some b) : f a = b := by symm; have := h a; rwa [h'] at this

theorem agrees_iff_of_eq_some {T : Type _} {a : Option T} {b : T} (h : a = some b) (c : T) :
    a.Agrees c ↔ c = b := by rw [h]; simp [Option.Agrees]; constructor <;> apply Eq.symm

theorem some_if {T : Type _} (P : Prop) [Decidable P] (a b : T) :
    Option.some (if P then a else b) = if P then Option.some a else Option.some b := by
  by_cases h : P;
  · simp [if_pos h]
  · simp [if_neg h]

end Option

/- vector -/
namespace Mathlib.Vector

variable {α : Type _}

theorem reverse_cons {n : ℕ} (a : α) (v : Vector α n) :
    reverse (cons a v) = append (reverse v) (cons a nil) := by
  apply toList_injective;
  simp [reverse]

end Mathlib.Vector

namespace Fin

theorem exists_fin_castSucc {n : ℕ} {P : Fin (n + 1) → Prop} :
  (∃ i, P i) ↔ (∃ i : Fin n, P (castSucc i)) ∨ P (last n) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
    · left; use j
    right; assumption
  rintro (⟨i, h⟩ | h) <;> exact Exists.intro _ h

@[simp]
theorem revPerm_zero {n : ℕ} : revPerm (0 : Fin (n + 1)) = last n := by rfl

@[simp]
theorem revPerm_last {n : ℕ} : revPerm (last n) = 0 := by
  rw [← revPerm_zero]; simp only [revPerm_apply, rev_zero, rev_last]

theorem castSucc_add_one_revPerm {n : ℕ} {i : Fin n} :
  revPerm (castSucc i + 1) + 1 = revPerm (castSucc i) := by
  cases' i with i' h'
  ext
  simp [val_add, revPerm_apply, val_one']
  rw [@Nat.mod_eq_of_lt (i' + 1), Nat.mod_eq_of_lt]
  · have := Nat.succ_le_of_lt h'
    rw [Nat.succ_eq_add_one] at this
    rw [←Nat.sub_sub, Nat.sub_add_cancel]
    apply (add_le_add_iff_right i').mp
    rwa [Nat.add_comm, Nat.sub_add_cancel (le_of_lt h')]
  · apply Nat.succ_lt_succ_iff.mpr
    cases' n with n
    · exact absurd (Nat.zero_le i') (not_le_of_lt h')
    · rw [Nat.succ_sub_succ]
      exact lt_of_le_of_lt (Nat.sub_le n i') (Nat.lt_succ_self n)
  · exact Nat.succ_lt_succ_iff.mpr h'

theorem castSucc_revPerm {n : ℕ} (i : Fin n) : castSucc (revPerm i) = revPerm i.succ := by
  cases' i with i' h'; ext; simp

theorem revPerm_castSucc (i : Fin n) : revPerm (castSucc i) = succ (revPerm i) := i.rev_castSucc

@[simp] theorem revPerm_revPerm (i : Fin n) : revPerm (revPerm i) = i := i.rev_rev

@[simp] theorem revPerm_lt_revPerm {i j : Fin n} : revPerm i < revPerm j ↔ j < i := rev_lt_rev

theorem eq_zero_of_le_zero {n : ℕ} {i : Fin (n + 1)} (h : i ≤ 0) : i = 0 := by
  cases i; ext; apply Nat.eq_zero_of_le_zero h

theorem of_le_succ {n : ℕ} {i : Fin (n + 1)} {j : Fin n} (h : i ≤ j.succ) :
    i ≤ castSucc j ∨ i = j.succ := by
  cases i; cases j
  simp [Fin.succ] at *
  exact Nat.of_le_succ h

theorem le_of_lt_succ {n : ℕ} {i : Fin (n + 1)} {j : Fin n} (h : i < j.succ) : i ≤ castSucc j := by
  cases i; cases j; exact Nat.le_of_lt_succ h

theorem one_eq_succ_zero {n : ℕ} : (1 : Fin (n + 2)) = Fin.succ 0 := rfl

/-- This lemma is useful for rewriting `fin (n + 1)` as `fin (m + j + 1)`,
    given `i : fin (n + 1)` and `m = ↑i`. -/
theorem exists_eq_add {n : ℕ} (i : Fin (n + 1)) : ∃ m j, m = ↑i ∧ n = m + j := by
  cases' Nat.exists_eq_add_of_le (Nat.le_of_lt_succ i.2) with j hj
  exact ⟨↑i, j, rfl, hj⟩

def castOffset {n : ℕ} (m : ℕ) (i : Fin n) : Fin (m + n) :=
  ⟨m + ↑i, add_lt_add_left i.is_lt _⟩

def castOffset' {n : ℕ} (m : ℕ) (j : Fin (n + 1)) : Fin (m + n + 1) :=
  @castOffset (n + 1) m j

theorem castSucc_castOffset {n m : ℕ} (i : Fin n) :
    Fin.castOffset m (castSucc i) = castSucc (Fin.castOffset m i) := by cases i; rfl

theorem succ_castOffset {n m : ℕ} (i : Fin n) :
    Fin.castOffset m i.succ = (Fin.castOffset m i).succ := by cases i; rfl

section

variable {n : ℕ}

def range (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun j => castSucc j < i

@[simp]
theorem mem_range (i : Fin n) (j : Fin (n + 1)) : i ∈ range j ↔ castSucc i < j := by simp [range]

@[simp]
theorem range_zero : range (0 : Fin (n + 1)) = ∅ := by ext i; simp [range, Fin.zero_le]

@[simp]
theorem range_one : range (1 : Fin (n + 2)) = {(0 : Fin (n + 1))} := by
  ext i
  rw [mem_range, Finset.mem_singleton, one_eq_succ_zero, castSucc_lt_succ_iff, le_zero_iff]

theorem range_succ_eq_insert (i : Fin n) : range i.succ = insert i (range (castSucc i)) :=
  by
  ext j
  rw [mem_range, Finset.mem_insert, mem_range, castSucc_lt_succ_iff, le_iff_lt_or_eq,
    castSucc_lt_castSucc_iff, or_comm]

theorem range_last : range (Fin.last n) = Finset.univ := by
  ext i; simp [mem_range, castSucc_lt_last]

@[simp]
theorem not_mem_range_self (i : Fin n) : i ∉ range (castSucc i) := by rw [mem_range]; apply lt_irrefl

@[simp]
theorem self_mem_range_succ (i : Fin n) : i ∈ range i.succ := by
  rw [mem_range]; apply castSucc_lt_succ

@[simp]
theorem range_subset {i j : Fin (n + 1)} : range i ⊆ range j ↔ i ≤ j := by
  rw [Finset.subset_iff]; constructor
  · intro h
    by_cases h' : i = 0
    · rw [h']; apply zero_le
    have : i.pred h' ∈ range i := by
      rw [mem_range];
      conv =>
        rhs
        rw [← succ_pred i h']
      rw [castSucc_lt_succ_iff]
    specialize h this
    rwa [mem_range, castSucc_lt_iff_succ_le, succ_pred i h'] at h
  intro h k
  rw [mem_range, mem_range]
  intro h'
  exact lt_of_lt_of_le h' h

section

variable {β : Type _} [CommMonoid β]

theorem prod_range_zero (f : Fin n → β) : (∏ k in range 0, f k) = 1 := by
  rw [range_zero, Finset.prod_empty]

theorem sum_range_zero {β : Type _} [AddCommMonoid β] (f : Fin n → β) : (∑ k in range 0, f k) = 0 :=
  by rw [range_zero, Finset.sum_empty]

@[to_additive existing]
theorem prod_range_one (f : Fin (n + 1) → β) : (∏ k in range 1, f k) = f 0 := by
  rw [range_one]; rw [Finset.prod_singleton]

@[to_additive]
theorem prod_range_succ (f : Fin n → β) (i : Fin n) :
    (∏ x in range i.succ, f x) = f i * ∏ x in range (castSucc i), f x := by
  rw [range_succ_eq_insert, Finset.prod_insert (not_mem_range_self i)]

theorem prod_range_succ' (f : Fin (n + 1) → β) (i : Fin (n + 1)) :
    (∏ k in range i.succ, f k) = (∏ k in range i, f k.succ) * f 0 := by
  induction' i using Fin.inductionOn with i' ih
  · rw [prod_range_succ, castSucc_zero, prod_range_zero, prod_range_zero, mul_comm]
  · rw [prod_range_succ fun k => f k.succ, mul_assoc, ← ih, succ_castSucc, prod_range_succ]

theorem sum_range_succ' {β : Type _} [AddCommMonoid β] (f : Fin (n + 1) → β) (i : Fin (n + 1)) :
    (∑ k in range i.succ, f k) = (∑ k in range i, f k.succ) + f 0 := by
  induction' i using Fin.inductionOn with i' ih
  · rw [sum_range_succ, castSucc_zero, sum_range_zero, sum_range_zero, add_comm]
  ·  rw [sum_range_succ fun k => f k.succ, add_assoc, ← ih, succ_castSucc, sum_range_succ]

end

/- currently not used, but maybe useful?

theorem add_one_eq_of_lt_last {n : ℕ} {i : fin (n + 1)} (h : i < last n) :
  i + 1 = ⟨i.1 + 1, nat.succ_lt_succ h⟩ :=
begin
  cases i with i' h', ext,
  simp [fin.coe_add, fin.coe_one'],
  apply nat.mod_eq_of_lt,
  apply nat.succ_lt_succ,
  apply h
end

theorem lt_of_add_one_le {n : ℕ} {i j : fin (n + 1)} (h : i < last n) (h' : i + 1 ≤ j) :
  i < j :=
begin
  cases i with i hi,
  cases j with j hj,
  simp [fin.le_def, fin.coe_add, fin.coe_one'],
  rw add_one_eq_of_lt_last h at h',
  apply nat.lt_of_succ_le h'
end

theorem add_one_rev_lt_last {n : ℕ} {i : fin (n + 1)} (h : i < fin.last n) :
  (i + 1).rev < fin.last n :=
begin
  rw [add_one_eq_of_lt_last h, rev, lt_def],
  dsimp [fin.last],
  rw nat.succ_sub_succ,
  apply nat.sub_lt,
  { apply lt_of_le_of_lt (nat.zero_le _) h },
  apply nat.zero_lt_succ
end
-/
end

end Fin

/- BitVec -/

namespace BitVec

variable {n : ℕ} (b : BitVec n)

def toBiased16 : ℤ := (b.toNat : Int) - 2 ^ 15

def ofFnBE (f : Fin n → Bool) : BitVec n :=
  ofBoolListBE (List.ofFn f) |>.cast (by rw [List.length_ofFn])

theorem getMsbD_ofFnBE (f : Fin n → Bool) (i : Fin n) :
    getMsbD (ofFnBE f) i = f i := by
  have : ↑i < List.length (List.ofFn f) := by rw [List.length_ofFn]; exact i.2
  simp [ofFnBE, getMsbD_cast, List.getD_eq_getElem, this]

theorem ofFnBE_getMsbD : (ofFnBE fun i : Fin n => getMsbD b i) = b := by
  apply eq_of_getMsbD_eq; intro i; rw [getMsbD_ofFnBE]

def ofFnLE (f : Fin n → Bool) : BitVec n :=
  ofBoolListLE (List.ofFn f) |>.cast (by rw [List.length_ofFn])

theorem ofBoolListLE_cast (l1 l2 : List Bool) (h : l1 = l2) (h' : l1.length = l2.length) :
    (ofBoolListLE l1 |>.cast h') = ofBoolListLE l2 := by
  subst h
  rfl

theorem getLsbD_ofFnLE (f : Fin n → Bool) (i : Fin n) :
    getLsbD (ofFnLE f) i = f i := by
  have : ↑i < List.length (List.ofFn f) := by rw [List.length_ofFn]; exact i.2
  simp [ofFnLE, getLsbD_cast, List.getD_eq_getElem, this]

theorem ofFnLE_getLsb : (ofFnLE fun i : Fin n => getLsbD b i) = b := by
  apply eq_of_getLsbD_eq; intro i; rw [getLsbD_ofFnLE]

theorem toNat_le : b.toNat ≤ 2 ^ n - 1 := by
  apply le_tsub_of_add_le_right
  apply Nat.succ_le_of_lt
  apply isLt

theorem toNat_inj {n : ℕ} {b1 b2 : BitVec n} (h : b1.toNat = b2.toNat) : b1 = b2 := by
  rcases b1 with ⟨b1, h1⟩; rcases b2 with ⟨b2, h2⟩; cases h; rfl

end BitVec

/- Casting nat and int to a ring with positive characteristic.  -/
namespace Nat

variable {R : Type _} [Ring R]

theorem cast_inj_of_lt_char' {a b : ℕ} (hlt : a ≤ b) (h : b < ringChar R) (h : (a : R) = (b : R)) :
    a = b := by
  suffices b - a = 0 by apply le_antisymm hlt; rwa [← Nat.sub_eq_zero_iff_le]
  have h1 : ((b - a : ℕ) : R) = 0 := by rw [Nat.cast_sub hlt, h, sub_self]
  rw [ringChar.spec] at h1
  suffices ¬b - a > 0 by linarith
  intro (this : b - a > 0)
  have : ringChar R ≤ b - a := Nat.le_of_dvd this h1
  have : b - a ≤ b := tsub_le_self
  linarith

theorem cast_inj_of_lt_char {a b : ℕ} (ha : a < ringChar R) (hb : b < ringChar R)
    (h : (a : R) = (b : R)) : a = b := by
  rcases le_or_gt a b with (h_le | h_le)
  · exact cast_inj_of_lt_char' h_le hb h
  · exact (cast_inj_of_lt_char' (le_of_lt h_le) ha h.symm).symm

end Nat

namespace Int

theorem cast_ne_zero_of_abs_lt_char {R : Type _} [Ring R] {x : ℤ} (h0 : abs x ≠ 0)
    (h1 : abs x < ringChar R) : (x : R) ≠ 0 := by
  have h3 : (abs x).toNat < ringChar R := by
    rwa [← Int.toNat_of_nonneg (abs_nonneg x), Int.ofNat_lt] at h1
  intro h; apply h0
  suffices (abs x).toNat = 0 by rw [← Int.toNat_of_nonneg (abs_nonneg x), this]; rfl
  apply Nat.cast_inj_of_lt_char h3 (lt_of_le_of_lt (Nat.zero_le _) h3)

  have : ((abs x).toNat : R) = (((abs x).toNat : ℤ) : R) := by
    rw [@cast_natCast]
  apply Eq.trans this
  rw [Int.toNat_of_nonneg (abs_nonneg x)]
  cases' le_or_gt 0 x with h4 h4
  · rw [abs_of_nonneg h4, h, Nat.cast_zero]
  rw [abs_of_neg h4]; simp [h]

theorem cast_inj_of_lt_char {R : Type _} [Ring R] {i j : ℤ} {p : ℕ} (charR : CharP R p)
    (h : (i : R) = (j : R)) (h' : abs (j - i) < p) : i = j := by
  symm
  apply eq_of_sub_eq_zero
  rw [← abs_eq_zero]
  by_contra nez
  apply not_le_of_lt h'
  apply Int.le_of_dvd
  apply lt_of_le_of_ne (abs_nonneg _) (Ne.symm nez)
  rw [dvd_abs]
  have : (↑(j - i) : R) = 0 := by simp [h]
  exact (CharP.intCast_eq_zero_iff R p _).mp this

theorem cast_eq_zero_of_lt_char (R : Type _) [Ring R] {i : ℤ} (p : ℕ) [charR : CharP R p]
    (h : (i : R) = 0) (h' : abs i < p) : i = 0 := by
  have := @Int.cast_inj_of_lt_char _ _ i 0 p charR
  simp at this
  apply this <;> assumption

end Int

/- Ring theory.  -/
open Finset Polynomial

section

variable {R : Type _} [CommSemiring R]

@[simp]
theorem eval_multiset_prod (m : Multiset (Polynomial R)) (z : R) :
    eval z (m.prod) = (m.map (eval z)).prod :=
  (@Multiset.prod_hom _ R _ _ m _ _ _ (evalRingHom z)).symm

theorem natDegree_add (p q : Polynomial R) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  by_cases hpq : p + q = 0; · simp [hpq]
  have := degree_add_le p q
  rw [degree_eq_natDegree hp, degree_eq_natDegree hq, degree_eq_natDegree hpq] at this
  simp [WithBot.coe_le_coe, le_max_iff] at this ⊢
  exact this

end

section

variable {R : Type _} [CommRing R] [IsDomain R]

private theorem multiset_prod_X_sub_C_aux (m : Multiset R) :
    (m.map fun r => X - C r).prod ≠ 0 ∧ (m.map fun r => X - C r).prod.natDegree = (Multiset.card m) := by
  induction' m using Multiset.induction_on with a m ih;
  · simp
  · have h : X - C a ≠ 0 := X_sub_C_ne_zero a
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    constructor; · exact mul_ne_zero h ih.1
    rw [natDegree_mul h ih.1, ih.2]; simp [add_comm]

theorem multiset_prod_X_sub_C_ne_zero (m : Multiset R) : (m.map fun r => X - C r).prod ≠ 0 :=
  (multiset_prod_X_sub_C_aux m).1

theorem natDegree_multiset_prod_X_sub_C (m : Multiset R) :
    (m.map fun r => X - C r).prod.natDegree = Multiset.card m :=
  (multiset_prod_X_sub_C_aux m).2

theorem multiset_prod_x_sub_c_roots (m : Multiset R) : (m.map fun r => X - C r).prod.roots = m := by
  have h' : (0 : Polynomial R) ∉ Multiset.map (fun r : R => X - C r) m := by
    rw [Multiset.mem_map];
    rintro ⟨r, _, h''⟩; apply X_sub_C_ne_zero _ h''
  rw [roots_multiset_prod _ h', Multiset.bind, Multiset.join]; simp

end
