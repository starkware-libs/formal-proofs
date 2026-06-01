/-
This file represents values in the `air_infra` project that come from the `stwo` project.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

def Stwo.P : ℕ := 2147483647   -- The Mersenne prime, 2^31 - 1

def Felt := ZMod Stwo.P

instance : NeZero Stwo.P := by rw [neZero_iff] ; simp [Stwo.P]

-- TODO(Jeremy): move these

instance (n : Nat) : Lean.ToJson (ZMod n) where
  toJson := match n with
             | 0 => fun x : Int => Lean.toJson x
             | n+1 => fun x : Fin (n+1) => Lean.toJson x.val

instance (n : Nat) : Lean.FromJson (ZMod n) where
  fromJson? := match n with
                | 0 => fun s => (Lean.fromJson? s : Except String Int)
                | _+1 => fun s => let x : Except String Nat := Lean.fromJson? s
                                  x.bind (fun m => .ok ↑m)

deriving instance Lean.ToJson for Felt
deriving instance Lean.FromJson for Felt

namespace Felt

protected def toUInt32 (x : Felt) : UInt32 :=
  ⟨x.val, lt_of_lt_of_le x.isLt (by simp)⟩

end Felt

protected def UInt32.toFelt (x : UInt32) : Felt := (x.toFin.val : ZMod Stwo.P)

instance : CommRing Felt := inferInstanceAs (CommRing (ZMod Stwo.P))
instance : DecidableEq Felt := inferInstanceAs (DecidableEq (ZMod Stwo.P))
instance : Inhabited Felt := inferInstanceAs (Inhabited (ZMod Stwo.P))
instance : CharP Felt Stwo.P := inferInstanceAs (CharP (ZMod Stwo.P) Stwo.P)
instance : Hashable Felt := ⟨fun x => x.val.toUInt64⟩
instance : ToString Felt := ⟨fun x => toString x.val⟩
instance : Repr Felt := ⟨fun x _=> repr x.val⟩
instance : AndOp Felt := ⟨fun x y => (x.toUInt32 &&& y.toUInt32).toFelt⟩
instance : OrOp Felt := ⟨fun x y => (x.toUInt32 ||| y.toUInt32).toFelt⟩
instance : Complement Felt := ⟨fun x => (~~~x.toUInt32).toFelt⟩
instance : ShiftLeft Felt := ⟨fun x y => (x.toUInt32 <<< y.toUInt32).toFelt⟩
instance : Fintype Felt := by apply ZMod.fintype

instance : CommRing Felt := inferInstanceAs (CommRing (ZMod Stwo.P))

instance [Fact (Nat.Prime Stwo.P)] : Field Felt := inferInstanceAs (Field (ZMod Stwo.P))

instance : Fact (2 < Stwo.P) := by
  rw [fact_iff] ; unfold Stwo.P ; norm_num1
instance : Fact (2 < ringChar Felt) := by
  rw [fact_iff] ; unfold Felt ; rw [ZMod.ringChar_zmod_n] ; unfold Stwo.P ; norm_num1


abbrev FELT252_N_WORDS := 28
def FELT252_BITS_PER_WORD := 9

/- The prime 2**251 + 17 * 2**192 + 1 as a `Felt252`. -/

def P_FELTS : Array Nat := #[
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 136, 0, 0, 0, 0, 0, 256]

theorem P_FELTS_le : ∀ i : Fin FELT252_N_WORDS, P_FELTS[i] ≤ 256 := by
  intro i; fin_cases i <;> simp [P_FELTS]

lemma Felt.n_ne_zero {n : Nat} (h_0 : n ≠ 0) (h_n : n < Stwo.P): (n : Felt) ≠ 0 := by
  rw [←ZMod.val_ne_zero, ZMod.val_natCast_of_lt h_n] ; norm_num ; exact h_0

/-
`Bool` and `Felt`.
-/

def Bool.toFelt (b : Bool) : Felt := bif b then 1 else 0

def Felt.toBool (x : Felt) : Bool :=
  if x = 0 then false else true

lemma Bool.toFelt_le_one [Fact (Nat.Prime Stwo.P)] (x : Bool) : ZMod.val x.toFelt ≤ 1 := by
  unfold Bool.toFelt
  cases x
  · simp
  · simp
    rw [← Nat.cast_one]
    rw[ZMod.val_natCast]
    dsimp[Stwo.P]
    rfl

lemma Bool.toFelt_val_coe [Fact (Nat.Prime Stwo.P)] (x : Bool) : x.toFelt = ↑(ZMod.val x.toFelt) := by
  unfold Bool.toFelt
  cases x <;> simp


lemma Felt.toBool_toFelt [Fact (Nat.Prime Stwo.P)] {x : Felt} (h : x * (1 - x) = 0) : x.toBool.toFelt = x := by
  rw [mul_eq_zero] at h
  by_cases hx : x = 0 <;> simp_all [Felt.toBool, Bool.toFelt]
  rw [eq_of_sub_eq_zero h]

lemma Bool.toFelt_toBool [Fact (Nat.Prime Stwo.P)] (x : Bool) : x.toFelt.toBool = x := by
  unfold Bool.toFelt
  cases x <;> simp_all [Felt.toBool]

lemma Felt.toBool_inj [Fact (Nat.Prime Stwo.P)] {x y : Felt}
    (hx : x * (1 - x) = 0)
    (hy : y * (1 - y) = 0) :
    x.toBool = y.toBool ↔ x = y := by
  constructor; swap; simp +contextual
  intro h
  rw [←Felt.toBool_toFelt hx, h, Felt.toBool_toFelt hy]

lemma Bool.toFelt_inj [Fact (Nat.Prime Stwo.P)] (a b : Bool) : a.toFelt = b.toFelt ↔ a = b := by
  constructor; swap; simp +contextual
  intro h
  rw [←Bool.toFelt_toBool a, h, Bool.toFelt_toBool]

lemma Bool.toFelt_eq (b : Bool) : b.toFelt = ↑b.toNat := by
  cases b <;> simp [Bool.toFelt]

lemma Bool.false_toFelt_eq {b : Bool} (h : ¬b.toFelt = 1) : b.toFelt = false.toFelt := by
  cases b
  rfl
  exfalso ; apply h ; simp [Bool.toFelt]

lemma Bool.toFelt_ne_one_iff_eq_zero [Fact (Nat.Prime Stwo.P)] {b : Bool} :
    ¬b.toFelt = 1 ↔ b.toFelt = 0 := by
  cases b <;> simp [Bool.toFelt]

lemma Bool.false_toFelt_ne_true_toFelt [Fact (Nat.Prime Stwo.P)] :
    ¬ (false.toFelt = true.toFelt) := by
  simp [Bool.toFelt_inj]

lemma Bool.eq_decide_toFelt_eq_1 [Fact (Nat.Prime Stwo.P)] {b : Bool} :
    b = decide (b.toFelt = 1) := by
  cases b <;> simp [toFelt]

lemma Bool.false_of_toFelt_zero [Fact (Nat.Prime Stwo.P)] {b : Bool} (h : b.toFelt = 0) : b = false := by
  apply (Bool.toFelt_inj _ _).mp
  rw [h] ; rfl

-- theorem IsRangeCheckedVal [Fact (Nat.Prime Stwo.P)] {len : Nat} {x : Felt} (IsRangeChecked len x):
--   x.val < 2^len := by
--   rcases h with ⟨n, hn1, hn2⟩
--   rw [←hn2]
--   rw [ZMod.val_natCast_of_lt hn1]
--   exact hn1

theorem val_add_small_le {a b : Felt} {t: Nat} (ha : a.val ≤ t ∨ (a.val ≥ Stwo.P - t)) -- t1, t2, t1+t2? use for toFelt252_add_small?
  (hb : b.val ≤ t ∨ (b.val ≥ Stwo.P - t))
  (ht : t ≤ 2^27) :
  (a + b).val ≤ 2 * t ∨ (a + b).val ≥ Stwo.P - 2 * t := by

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
  · left
    rw[ZMod.val_add_of_lt]
    omega
    unfold Stwo.P
    omega

  · rw [hmb2]
    ring_nf

    have h1pre : b ≠ 0 := by
      intro hb0
      rw[hb0] at hb2
      unfold Stwo.P at hb2
      norm_num at hb2
      omega
    have h1 : NeZero b := ⟨h1pre⟩

    have h2 : mb.val = Stwo.P - b.val := by
      rw [hmb]
      rw [ZMod.val_neg_of_ne_zero b]


    have : (a.val ≥ mb.val) ∨ (a.val < mb.val) := by omega
    cases this <;> rename _ => hcompare
    · left
      rw[ZMod.val_sub]
      omega
      exact hcompare
    · right
      have h_nz_pre : mb - a ≠ 0 := by
        intro hz
        rw[sub_eq_iff_eq_add, zero_add] at hz
        rw[hz] at hcompare
        omega
      have h_nz : NeZero (mb - a) := ⟨h_nz_pre⟩
      have : a-mb = -(mb - a) := by ring
      rw[this]
      rw [ZMod.val_neg_of_ne_zero (mb-a)]
      apply ge_iff_le.mpr
      apply (Nat.sub_le_sub_iff_left _).mpr
      rw[ZMod.val_sub]
      omega
      omega
      apply ZMod.val_le

  · rw [hma2]
    ring_nf

    have h1pre : a ≠ 0 := by
      intro ha0
      rw[ha0] at ha2
      unfold Stwo.P at ha2
      norm_num at ha2
      omega
    have h1 : NeZero a := ⟨h1pre⟩

    have h2 : ma.val = Stwo.P - a.val := by
      rw [hma]
      rw [ZMod.val_neg_of_ne_zero a]

    have : (b.val ≥ ma.val) ∨ (b.val < ma.val) := by omega
    cases this <;> rename _ => hcompare
    · left
      rw[add_comm, ←sub_eq_add_neg]
      rw[ZMod.val_sub]
      omega
      exact hcompare
    · right
      have h_nz_pre : ma - b ≠ 0 := by
        intro hz
        rw[sub_eq_iff_eq_add, zero_add] at hz
        rw[hz] at hcompare
        omega
      have h_nz : NeZero (ma - b) := ⟨h_nz_pre⟩
      have : -ma+b = -(ma - b) := by ring
      rw[this]
      rw [ZMod.val_neg_of_ne_zero (ma-b)]
      apply ge_iff_le.mpr
      apply (Nat.sub_le_sub_iff_left _).mpr
      rw[ZMod.val_sub]
      omega
      omega
      apply ZMod.val_le

  · right
    rw[ZMod.val_add_of_le]
    calc
      a.val + b.val - Stwo.P
          ≥ (Stwo.P - t) + (Stwo.P - t) - Stwo.P  := by omega
      _ = 2 * (Stwo.P - t) - Stwo.P  := by ring_nf
      _ ≥ 2 * Stwo.P - 2*t - Stwo.P := by rw [Nat.mul_sub]
      _ = Stwo.P + Stwo.P - Stwo.P - 2*t := by
        rw [Nat.sub_sub, add_comm, ← Nat.sub_sub]
        omega -- ?
    apply ge_iff_le.mp
    calc
      a.val + b.val ≥ (Stwo.P - t) + (Stwo.P - t) := by omega
      _ = 2 * Stwo.P - 2*t := by
        rw [← Nat.mul_sub]
        ring_nf
      _ ≥ Stwo.P := by
        unfold Stwo.P
        omega
        --apply ge_iff_le.mpr
        -- apply Nat.sub_ge_iff
        -- apply (Nat.sub_le_iff_le_add).mpr
        -- linarith





    -- have := toFelt252_sub' h4 h5
    -- rw[ha_cast, hmb_cast] at this
    -- rw [← toFelt.of_lt h5] at this
    -- rw[ha_cast] at this
    -- rw [this]
    -- have htmp := toFelt.neg_of_lt h3
    -- rw[sub_eq_add_neg]
    -- rw[← htmp, hmb_cast]

theorem val_add_small_lt {a b : Felt} {t: Nat} (ha : a.val < t ∨ (a.val > Stwo.P - t)) -- t1, t2, t1+t2? use for toFelt252_add_small?
  (hb : b.val < t ∨ (b.val > Stwo.P - t))
  (ht : t ≤ 2^28) :
  (a + b).val < 2 * t ∨ (a + b).val > Stwo.P - 2 * t := by

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
  · left
    rw[ZMod.val_add_of_lt]
    omega
    unfold Stwo.P
    omega

  · rw [hmb2]
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


    have : (a.val ≥ mb.val) ∨ (a.val < mb.val) := by omega
    cases this <;> rename _ => hcompare
    · left
      rw[ZMod.val_sub]
      omega
      exact hcompare
    · right
      have h_nz_pre : mb - a ≠ 0 := by
        intro hz
        rw[sub_eq_iff_eq_add, zero_add] at hz
        rw[hz] at hcompare
        omega
      have h_nz : NeZero (mb - a) := ⟨h_nz_pre⟩
      have : a-mb = -(mb - a) := by ring
      rw[this]
      rw [ZMod.val_neg_of_ne_zero (mb-a)]
      apply gt_iff_lt.mpr
      apply Nat.sub_lt_sub_left
      rw[ZMod.val_sub]
      omega
      omega
      rw[ZMod.val_sub]
      rw[h2]
      apply (Nat.sub_lt_iff_lt_add _).mpr
      apply (Nat.sub_lt_iff_lt_add _).mpr
      omega
      apply ZMod.val_le
      omega
      omega

  · rw [hma2]
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

    have : (b.val ≥ ma.val) ∨ (b.val < ma.val) := by omega
    cases this <;> rename _ => hcompare
    · left
      rw[add_comm, ←sub_eq_add_neg]
      rw[ZMod.val_sub]
      omega
      exact hcompare
    · right
      have h_nz_pre : ma - b ≠ 0 := by
        intro hz
        rw[sub_eq_iff_eq_add, zero_add] at hz
        rw[hz] at hcompare
        omega
      have h_nz : NeZero (ma - b) := ⟨h_nz_pre⟩
      have : -ma+b = -(ma - b) := by ring
      rw[this]
      rw [ZMod.val_neg_of_ne_zero (ma-b)]
      apply gt_iff_lt.mpr
      apply Nat.sub_lt_sub_left _ _
      apply ZMod.val_lt
      rw[ZMod.val_sub]
      omega
      omega

  · right
    rw[ZMod.val_add_of_le]
    calc
      a.val + b.val - Stwo.P
          > (Stwo.P - t) + (Stwo.P - t) - Stwo.P  := by
        apply Nat.sub_lt_sub_right
        unfold Stwo.P
        omega
        omega
      _ = 2 * (Stwo.P - t) - Stwo.P  := by ring_nf
      _ ≥ 2 * Stwo.P - 2*t - Stwo.P := by rw [Nat.mul_sub]
      _ = Stwo.P + Stwo.P - Stwo.P - 2*t := by
        rw [Nat.sub_sub, add_comm, ← Nat.sub_sub]
        omega
    apply ge_iff_le.mp
    calc
      a.val + b.val ≥ (Stwo.P - t) + (Stwo.P - t) := by omega
      _ = 2 * Stwo.P - 2*t := by
        rw [← Nat.mul_sub]
        ring_nf
      _ ≥ Stwo.P := by
        unfold Stwo.P
        omega
