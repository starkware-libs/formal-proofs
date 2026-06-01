import Std
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-
Bitvec
-/

namespace BitVec

def toArray {n : Nat} (v : BitVec n) : Array Bool :=
  Array.ofFn (fun i : Fin n => v.getLsbD i)

@[simp] theorem toArray_nil : toArray nil = #[] := by rfl

@[simp] theorem toArray_nil' : toArray 0#0 = #[] := by rfl

@[simp] theorem getMsb_ge (x : BitVec w) (i : Nat) (ge : i ≥ w) : getMsbD x i = false := by simp [*, getMsbD]

theorem getMsb_concat {n : Nat} {v : BitVec n} {b : Bool} {i : Nat} :
    (v.concat b).getMsbD i = if i = n then b else v.getMsbD i := by
  by_cases h : i < n + 1
  . rw [←getLsbD_rev (v.concat b) ⟨i, h⟩, getLsbD_concat]
    simp only [Fin.val_rev, Nat.succ_sub_succ_eq_sub]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | h
    . have : i ≠ n := by omega
      have : n - i ≠ 0 := by omega
      rw [←getLsbD_rev v ⟨i, h⟩]
      simp [*, Nat.sub_add_eq]
    . simp [h]
  rw [if_neg (by omega)]
  rw [getMsb_ge, getMsb_ge] <;> omega

theorem toArray_cons {n : Nat} {v : BitVec n} {b : Bool} :
    toArray (v.cons b) = (toArray v).push b := by
  unfold toArray
  apply Array.ext; simp
  simp only [Array.size_ofFn, Array.size_push, Array.getElem_ofFn, Array.getElem_push]
  intro i h _
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
  . simp [h', getLsbD_cons, ne_of_lt h']
  . simp [h', getElem_cons]

theorem toArray_concat {n : Nat} {v : BitVec n} {b : Bool} :
    toArray (v.concat b) = #[b] ++ (toArray v) := by
  unfold toArray
  apply Array.ext; simp [Array.size_append, add_comm]
  simp only [Array.size_ofFn, Array.size_append, List.size_toArray, List.length_singleton,
    Array.getElem_ofFn]
  intro i h _
  rw [getLsbD_concat]
  rcases i with (_ |  i')
  . simp [Array.getElem_append_left]
  rw [Array.getElem_append_right] <;> simp_all

theorem toNat_cons'' {w : Nat} {a : Bool} {x : BitVec w} :
    (cons a x).toNat = a.toNat * 2^w + x.toNat := by
  simp [cons, Nat.shiftLeft_eq, Nat.mul_comm _ (2^w), Nat.two_pow_add_eq_or_of_lt, x.isLt]

theorem toNat_append' {n m : Nat} (x : BitVec n) (y : BitVec m) :
    BitVec.toNat (x ++ y) = 2^m * BitVec.toNat x + BitVec.toNat y := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^m),
    ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt y)]

end BitVec

/-
Option
-/

def Option.agrees : Option α → α → Prop
| (some x), y => x = y
| none,     _ => True

/-
Fin
-/

namespace Fin

theorem append_comp {m n : Nat} {α β : Type*}
      (v : Fin m → α) (w : Fin n → α) (f : α → β) :
    append (f ∘ v) (f ∘ w) = f ∘ (append v w) := by
  ext i
  refine addCases ?_ ?_ i <;> simp

theorem append_inj_left {m n : Nat} {α : Type*}
      {v v' : Fin m → α} {w w' : Fin n → α} (h : append v w = append v' w') :
    v = v' := by
  ext i
  have := congr_fun h (castAdd _ i)
  simpa using this

theorem append_inj_right {m n : Nat} {α : Type*}
      {v v' : Fin m → α} {w w' : Fin n → α} (h : append v w = append v' w') :
    w = w' := by
  ext i
  have := congr_fun h (natAdd _ i)
  simpa using this

end Fin

/-
Matrix
-/

namespace Matrix

theorem vecAppend_comp {m n o : Nat} {α β : Type*} (h : o = m + n)
      (v : Fin m → α) (w : Fin n → α) (f : α → β) :
    vecAppend h (f ∘ v) (f ∘ w) = f ∘ (vecAppend h v w) := by
  cases h; apply Fin.append_comp

end Matrix

/-
Loops.
-/

def forLoopAux {α : Type*} (start n : Nat) (init : α) (body : Nat → α → α) : α :=
  loop n start init
where
  loop : Nat → Nat → α → α
  | 0,   _, a => a
  | i+1, j, a => loop i (j + 1) (body j a)

theorem forLoopAux_succ (start n : Nat) (init : α) (body : Nat → α → α) :
    forLoopAux start (n + 1) init body =
      body (start + n) (forLoopAux start n init body) := by
  simp only [forLoopAux]
  induction n generalizing init start
  case zero => simp [forLoopAux.loop]
  case succ n ih =>
    conv =>
      rhs
      rw [forLoopAux.loop]
    rw [forLoopAux.loop, ih]
    congr 1; omega

theorem forLoopAuxCorrect {α : Type*} (start n : Nat) (init : α) (body : Nat → α → α)
      (P : Nat → α → Prop)
      (hstart : P start init)
      (hstep : ∀ i < n, ∀ a, P (start + i) a → P (start + i + 1) (body (start + i) a)) :
    P (start + n) (forLoopAux start n init body) := by
  rw [forLoopAux]
  induction n generalizing start init
  case zero =>
    exact hstart
  case succ n ih =>
    rw [forLoopAux.loop, Nat.add_succ, ←Nat.succ_add]
    apply ih
    . apply hstep 0; simp; exact hstart
    intro i hi init
    have := hstep i.succ (Nat.succ_lt_succ hi) init
    convert this using 2 <;> try { omega }
    congr 1; omega

def forLoop {α : Type*} (start finish : Nat) (init : α) (body : Nat → α → α) : α :=
  forLoopAux start (finish - start) init body

theorem forLoop_start {α : Type*} (start : Nat) (init : α) (body : Nat → α → α) :
    forLoop start start init body = init := by
  simp [forLoop, forLoopAux, forLoopAux.loop]

theorem forLoop_succ (start finish : Nat) (init : α) (body : Nat → α → α) (hle : start ≤ finish):
    forLoop start (finish + 1) init body = body finish (forLoop start finish init body) := by
  have : finish + 1 - start = finish - start + 1 := by omega
  simp [forLoop, this]
  rw [forLoopAux_succ]
  congr
  omega

theorem forLoopCorrect {α : Type*} (start finish : Nat) (init : α) (body : Nat → α → α)
      (hle : start ≤ finish)
      (Invariant : Nat → α → Prop)
      (hstart : Invariant start init)
      (step : ∀ i, start ≤ i → i < finish →
        ∀ a, Invariant i a → Invariant (i + 1) (body i a)) :
    Invariant finish (forLoop start finish init body) := by
  have : ∀ i < finish - start, ∀ a, Invariant (start + i) a → Invariant (start + i + 1) (body (start + i) a) := by
    intro i hi
    convert step (start + i) _ _ using 1 <;> omega
  convert forLoopAuxCorrect start (finish - start) init body Invariant hstart this using 1
  omega

def forLoopSpec {α : Type*} (Invariant : Nat → α → Prop) (start finish : Nat) (init : α) (out : α) (rel : Nat → α → α → Prop) :
    Prop :=
  start ≤ finish →
    Invariant start init →
    (∀ i, start ≤ i → i < finish →
      ∀ a next_a, Invariant i a → rel i a next_a → Invariant (i + 1) next_a) →
    Invariant finish out

/-
Misc
-/

lemma cast_bif (R : Type) [Semiring R] (b : Bool) : ((bif b then 1 else 0 : ℕ) : R) = bif b then 1 else 0 := by
  cases b <;> simp

lemma bif_one_zero_le (b : Bool) :
  (bif b then 1 else 0) ≤ 1 := by
cases b <;> simp

/-
ZMod
-/

namespace ZMod

lemma val_bif (n : Nat) [h : n.AtLeastTwo] (b : Bool):
    ZMod.val (bif b then (1 : ZMod n) else 0) = bif b then 1 else 0 := by
  cases b <;> simp [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one, h.ne_one]

end ZMod
