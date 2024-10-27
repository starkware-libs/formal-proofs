/-
  Specifications file for bigint_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.cairo_secp.constants_spec

import starkware.cairo.common.cairo_secp.bigint3_spec

open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.cairo_secp.constants

namespace starkware.cairo.common.cairo_secp.bigint

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def φ_UnreducedBigInt5.d0 := 0
@[reducible] def φ_UnreducedBigInt5.d1 := 1
@[reducible] def φ_UnreducedBigInt5.d2 := 2
@[reducible] def φ_UnreducedBigInt5.d3 := 3
@[reducible] def φ_UnreducedBigInt5.d4 := 4
@[ext] structure UnreducedBigInt5 (mem : F → F) :=
  (d0 : F) (d1 : F) (d2 : F) (d3 : F) (d4 : F)
@[reducible] def φ_UnreducedBigInt5.SIZE := 5
@[reducible] def UnreducedBigInt5.SIZE := 5
@[ext] structure π_UnreducedBigInt5 (mem : F → F) :=
  (σ_ptr : F) (d0 : F) (d1 : F) (d2 : F) (d3 : F) (d4 : F)
  (h_d0 : d0 = mem (σ_ptr + φ_UnreducedBigInt5.d0))
  (h_d1 : d1 = mem (σ_ptr + φ_UnreducedBigInt5.d1))
  (h_d2 : d2 = mem (σ_ptr + φ_UnreducedBigInt5.d2))
  (h_d3 : d3 = mem (σ_ptr + φ_UnreducedBigInt5.d3))
  (h_d4 : d4 = mem (σ_ptr + φ_UnreducedBigInt5.d4))
@[reducible] def π_UnreducedBigInt5.SIZE := 5
@[reducible] def cast_UnreducedBigInt5 (mem : F → F) (p : F) : UnreducedBigInt5 mem := {
  d0 := mem (p + φ_UnreducedBigInt5.d0),
  d1 := mem (p + φ_UnreducedBigInt5.d1),
  d2 := mem (p + φ_UnreducedBigInt5.d2),
  d3 := mem (p + φ_UnreducedBigInt5.d3),
  d4 := mem (p + φ_UnreducedBigInt5.d4)
}
@[reducible] def cast_π_UnreducedBigInt5 (mem : F → F) (p : F) : π_UnreducedBigInt5 mem := {
  σ_ptr := p,
  d0 := mem (p + φ_UnreducedBigInt5.d0),
  d1 := mem (p + φ_UnreducedBigInt5.d1),
  d2 := mem (p + φ_UnreducedBigInt5.d2),
  d3 := mem (p + φ_UnreducedBigInt5.d3),
  d4 := mem (p + φ_UnreducedBigInt5.d4),
  h_d0 := rfl,
  h_d1 := rfl,
  h_d2 := rfl,
  h_d3 := rfl,
  h_d4 := rfl
}
instance π_UnreducedBigInt5_to_F {mem : F → F} : has_coe (π_UnreducedBigInt5 mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_UnreducedBigInt5_ptr {mem : F → F} {x y : π_UnreducedBigInt5 mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_d0, y.h_d0, h_p] },
  try { ext }, repeat { rw [x.h_d1, y.h_d1, h_p] },
  try { ext }, repeat { rw [x.h_d2, y.h_d2, h_p] },
  try { ext }, repeat { rw [x.h_d3, y.h_d3, h_p] },
  try { ext }, repeat { rw [x.h_d4, y.h_d4, h_p] }
end
lemma eq_UnreducedBigInt5_π_cast {mem : F → F} {x y : F} :
  cast_π_UnreducedBigInt5 mem x = cast_π_UnreducedBigInt5 mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_UnreducedBigInt5_π_ptr_cast {mem : F → F} {x : π_UnreducedBigInt5 mem} {y : F} :
  x = cast_π_UnreducedBigInt5 mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_UnreducedBigInt5_π_cast {mem : F → F} {x : F} :(↑(cast_π_UnreducedBigInt5 mem x) : F) = x := rfl

-- End of main scope definitions.

namespace nondet_bigint3

@[reducible] def MAX_SUM := 3 * (BASE - 1)

end nondet_bigint3

namespace BigInt3

def add {mem : F → F} (x y : BigInt3 mem) : BigInt3 mem :=
{ d0 := x.d0 + y.d0, d1 := x.d1 + y.d1, d2 := x.d2 + y.d2 }

def sub {mem : F → F} (x y : BigInt3 mem) : BigInt3 mem :=
{ d0 := x.d0 - y.d0, d1 := x.d1 - y.d1, d2 := x.d2 - y.d2 }

def toSumBigInt3 {mem : F → F} (x : BigInt3 mem) : SumBigInt3 mem := ⟨x.d0, x.d1, x.d2⟩

end BigInt3

namespace UnreducedBigInt3

def add {mem : F → F} (x y : UnreducedBigInt3 mem) : UnreducedBigInt3 mem :=
{ d0 := x.d0 + y.d0, d1 := x.d1 + y.d1, d2 := x.d2 + y.d2 }

def sub {mem : F → F} (x y : UnreducedBigInt3 mem) : UnreducedBigInt3 mem :=
{ d0 := x.d0 - y.d0, d1 := x.d1 - y.d1, d2 := x.d2 - y.d2 }

end UnreducedBigInt3

namespace SumBigInt3

def add {mem : F → F} (x y : SumBigInt3 mem) : SumBigInt3 mem :=
{ d0 := x.d0 + y.d0, d1 := x.d1 + y.d1, d2 := x.d2 + y.d2 }

def sub {mem : F → F} (x y : SumBigInt3 mem) : SumBigInt3 mem :=
{ d0 := x.d0 - y.d0, d1 := x.d1 - y.d1, d2 := x.d2 - y.d2 }

def toBigInt3 {mem : F → F} (x : SumBigInt3 mem) : BigInt3 mem := ⟨x.d0, x.d1, x.d2⟩

theorem toBigInt3_toSumBigInt3 {mem : F → F} (x : SumBigInt3 mem) :
  BigInt3.toSumBigInt3 (toBigInt3 x) = x :=
by ext; refl

end SumBigInt3

@[ext]
structure bigint3 := (i0 i1 i2 : ℤ)

namespace bigint3

def val (x : bigint3) : int := x.i2 * ↑BASE^2 + x.i1 * ↑BASE + x.i0

def toBigInt3 {mem : F → F} (x : bigint3) : BigInt3 mem := ⟨x.i0, x.i1, x.i2⟩

def toUnreducedBigInt3 {mem : F → F} (x : bigint3) : UnreducedBigInt3 mem := ⟨x.i0, x.i1, x.i2⟩

def toSumBigInt3 {mem : F → F} (x : bigint3) : SumBigInt3 mem := ⟨x.i0, x.i1, x.i2⟩

theorem toBigInt3_toSumBigInt3 {mem : F → F} (x : bigint3) :
  BigInt3.toSumBigInt3 (x.toBigInt3) = (x.toSumBigInt3 : SumBigInt3 mem) :=
by cases x; refl

theorem eq_toBigInt3_iff_eq_toSumBigInt3 {mem : F → F} {x : SumBigInt3 mem} {ix : bigint3} :
  x = ix.toSumBigInt3 ↔ SumBigInt3.toBigInt3 x = ix.toBigInt3 :=
begin
  split,
  { intro h, rw [h], refl },
  intro h,
  rw [← toBigInt3_toSumBigInt3, ← h, SumBigInt3.toBigInt3_toSumBigInt3]
end

def add (x y : bigint3) : bigint3 :=
{ i0 := x.i0 + y.i0, i1 := x.i1 + y.i1, i2 := x.i2 + y.i2 }

theorem toBigInt3_add {mem : F → F} (x y : bigint3) : ((x.add y).toBigInt3 : BigInt3 mem) =
  BigInt3.add (x.toBigInt3) (y.toBigInt3) :=
by simp [BigInt3.add, toBigInt3, bigint3.add]

theorem toUnreducedBigInt3_add {mem : F → F} (x y : bigint3) :
    ((x.add y).toUnreducedBigInt3 : UnreducedBigInt3 mem) =
  UnreducedBigInt3.add (x.toUnreducedBigInt3) (y.toUnreducedBigInt3) :=
by simp [UnreducedBigInt3.add, toUnreducedBigInt3, bigint3.add]

theorem add_val (x y : bigint3) : (x.add y).val = x.val + y.val :=
by { simp [val, add], ring }

def sub (x y : bigint3) : bigint3 :=
{ i0 := x.i0 - y.i0, i1 := x.i1 - y.i1, i2 := x.i2 - y.i2 }

theorem toBigInt3_sub {mem : F → F} (x y : bigint3) : ((x.sub y).toBigInt3 : BigInt3 mem) =
  BigInt3.sub (x.toBigInt3) (y.toBigInt3) :=
by simp [BigInt3.sub, toBigInt3, bigint3.sub]

theorem toUnreducedBigInt3_sub {mem : F → F} (x y : bigint3) : ((x.sub y).toUnreducedBigInt3 : UnreducedBigInt3 mem) =
  UnreducedBigInt3.sub (x.toUnreducedBigInt3) (y.toUnreducedBigInt3) :=
by simp [UnreducedBigInt3.sub, toUnreducedBigInt3, bigint3.sub]

theorem sub_val (x y : bigint3) : (x.sub y).val = x.val - y.val :=
by { simp [val, sub], ring }

def cmul (c : ℤ) (x : bigint3) : bigint3 :=
{ i0 := c * x.i0, i1 := c * x.i1, i2 := c * x.i2}

theorem cmul_val (c : ℤ) (x : bigint3) : (x.cmul c).val = c * x.val :=
by { simp [val, cmul], ring }

def mul (x y : bigint3) : bigint3 :=
{ i0 := x.i0 * y.i0 + (x.i1 * y.i2 + x.i2 * y.i1) * (4 * SECP_REM),
  i1 := x.i0 * y.i1 + x.i1 * y.i0 + (x.i2 * y.i2) * (4 * SECP_REM),
  i2 := x.i0 * y.i2 + x.i1 * y.i1 + x.i2 * y.i0 }

theorem mul_val (x y : bigint3) : (x.mul y).val ≡ x.val * y.val [ZMOD ↑SECP_PRIME] :=
begin
  have aux : (4 : ℤ) ∣ ↑BASE ^ 3,
  { dsimp only [BASE], simp_int_casts, norm_num1 },
  rw [int.modeq_iff_dvd],
  use [4 * (x.i1 * y.i2 + x.i2 * y.i1 + BASE * (x.i2 * y.i2))],
  rw SECP_PRIME_eq,
  simp only [val, mul],
  conv { to_rhs, rw [←mul_assoc, sub_mul, int.div_mul_cancel aux] },
  generalize : SECP_REM = S,
  generalize : BASE = B,
  ring
end

def sqr (x : bigint3) : bigint3 := x.mul x

theorem sqr_val (x : bigint3) : x.sqr.val ≡ x.val^2 [ZMOD ↑SECP_PRIME] :=
by { rw pow_two, exact mul_val x x }

def bounded (x : bigint3) (b : ℤ) := abs x.i0 ≤ b ∧ abs x.i1 ≤ b ∧ abs x.i2 ≤ b

theorem bounded_of_bounded_of_le {x : bigint3} {b₁ b₂ : ℤ} (bddx : x.bounded b₁) (hle : b₁ ≤ b₂) :
  x.bounded b₂ :=
⟨bddx.1.trans hle, bddx.2.1.trans hle, bddx.2.2.trans hle⟩

theorem bounded_add {x y : bigint3} {b₁ b₂ : int} (bddx : x.bounded b₁) (bddy : y.bounded b₂) :
  (x.add y).bounded (b₁ + b₂) :=
⟨(abs_add _ _).trans (add_le_add bddx.1 bddy.1),
  (abs_add _ _).trans (add_le_add bddx.2.1 bddy.2.1),
  (abs_add _ _).trans (add_le_add bddx.2.2 bddy.2.2)⟩

theorem bounded_sub {x y : bigint3} {b₁ b₂ : int} (bddx : x.bounded b₁) (bddy : y.bounded b₂) :
  (x.sub y).bounded (b₁ + b₂) :=
⟨(abs_sub _ _).trans (add_le_add bddx.1 bddy.1),
         (abs_sub _ _).trans (add_le_add bddx.2.1 bddy.2.1),
         (abs_sub _ _).trans (add_le_add bddx.2.2 bddy.2.2)⟩

theorem bounded_cmul {x : bigint3} {c b : int} (bddx : x.bounded b) :
  (x.cmul c).bounded (abs c * b) :=
begin
  simp [cmul, bigint3.bounded, abs_mul],
  exact ⟨mul_le_mul_of_nonneg_left bddx.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.2 (abs_nonneg _)⟩
end

theorem bounded_cmul' {x : bigint3} {c b : int} (h : 0 ≤ c) (bddx : x.bounded b) :
  (x.cmul c).bounded (c * b) :=
by { convert bounded_cmul bddx, rw abs_of_nonneg h }

theorem bounded_mul {x y : bigint3} {b : ℤ} (hx : x.bounded b) (hy : y.bounded b) :
  (x.mul y).bounded (b^2 * (8 * SECP_REM + 1)) :=
begin
  have bnonneg : 0 ≤ b := le_trans (abs_nonneg _) hx.1,
  have secp4nonneg : (0 : ℤ) ≤ 4 * ↑SECP_REM,
  { apply mul_nonneg, norm_num1, rw [SECP_REM], simp_int_casts, norm_num1 },
  have secp4ge1 : (1 : ℤ) ≤ 4 * ↑SECP_REM,
  { rw [SECP_REM], simp_int_casts, norm_num1 },
  simp only [bigint3.mul, bigint3.bounded],
  split,
  { transitivity b * b + (b * b + b * b) * (4 * ↑SECP_REM),
    { apply le_trans, apply abs_add,
      apply add_le_add, rw abs_mul,
      apply mul_le_mul hx.1 hy.1 (abs_nonneg _) bnonneg,
      rw [abs_mul, abs_of_nonneg secp4nonneg],
      apply mul_le_mul_of_nonneg_right _ secp4nonneg,
      apply le_trans, apply abs_add, rw [abs_mul, abs_mul],
      apply add_le_add, apply mul_le_mul hx.2.1 hy.2.2 (abs_nonneg _) bnonneg,
      apply mul_le_mul hx.2.2 hy.2.1 (abs_nonneg _) bnonneg },
    apply le_of_eq, ring },
  split,
  { transitivity b * b + b * (b * (4 * ↑SECP_REM)) + (b * b) * (4 * ↑SECP_REM),
    { apply le_trans, apply abs_add,
      apply add_le_add,
      apply le_trans, apply abs_add,
      rw [abs_mul, abs_mul], apply add_le_add,
      apply mul_le_mul hx.1 hy.2.1 (abs_nonneg _) bnonneg,
      apply mul_le_mul hx.2.1 _ (abs_nonneg _) bnonneg,
      rw [←mul_one(abs y.i0)],
      apply mul_le_mul hy.1 secp4ge1 zero_le_one bnonneg,
      rw [abs_mul, abs_mul, abs_of_nonneg secp4nonneg],
      apply mul_le_mul_of_nonneg_right _ secp4nonneg,
      apply mul_le_mul hx.2.2 hy.2.2 (abs_nonneg _) bnonneg,
    },
    apply le_of_eq, ring },
  transitivity (b * b + b * b + b * b),
  apply le_trans, apply abs_add, apply add_le_add,
  apply le_trans, apply abs_add, rw [abs_mul, abs_mul],
  apply add_le_add,
  apply mul_le_mul hx.1 hy.2.2 (abs_nonneg _) bnonneg,
  apply mul_le_mul hx.2.1 hy.2.1 (abs_nonneg _) bnonneg,
  rw abs_mul,
  apply mul_le_mul hx.2.2 hy.1 (abs_nonneg _) bnonneg,
  transitivity (b^2 * 3),
  apply le_of_eq, ring,
  apply mul_le_mul_of_nonneg_left _ (pow_two_nonneg b),
  rw [SECP_REM], simp_int_casts, norm_num1
end

theorem bounded_sqr {x : bigint3} {b : ℤ} (hx : x.bounded b) :
  (x.sqr).bounded (b^2 * (8 * SECP_REM + 1)) :=
bounded_mul hx hx

end bigint3

theorem bigint3_eqs {mem : F → F} {x : BigInt3 mem} {i0 i1 i2 : ℤ} (h : x = (bigint3.mk i0 i1 i2).toBigInt3) :
  x.d0 = i0 ∧ x.d1 = i1 ∧ x.d2 = i2 :=
by { rwa BigInt3.ext_iff at h }

theorem unreduced_bigint3_eqs {mem : F → F} {x : UnreducedBigInt3 mem} {i0 i1 i2 : ℤ} (h : x = (bigint3.mk i0 i1 i2).toUnreducedBigInt3) :
  x.d0 = i0 ∧ x.d1 = i1 ∧ x.d2 = i2 :=
by { rwa UnreducedBigInt3.ext_iff at h }

theorem cast_int_eq_of_bdd_3BASE {i j : int}
    (heq : (i : F) = (j : F))
    (ibdd : abs i ≤ 3 * BASE - 1)
    (jbdd : abs j ≤ 3 * BASE - 1) :
  i = j :=
begin
  apply PRIME.int_coe_inj heq,
  apply lt_of_le_of_lt,
  apply abs_sub,
  apply lt_of_le_of_lt,
  apply add_le_add jbdd ibdd,
  dsimp only [BASE, PRIME],
  simp_int_casts,
  norm_num
end

theorem toBigInt3_eq_toBigInt3_of_bounded_3BASE {mem : F → F} {a b : bigint3}
    (heq : (a.toBigInt3 : BigInt3 mem) = b.toBigInt3)
    (abdd : a.bounded (3 * BASE - 1))
    (bbdd : b.bounded (3 * BASE - 1)) :
  a = b :=
begin
  simp [BigInt3.ext_iff, bigint3.toBigInt3] at heq,
  ext,
  { apply cast_int_eq_of_bdd_3BASE heq.1 abdd.1 bbdd.1 },
  { apply cast_int_eq_of_bdd_3BASE heq.2.1 abdd.2.1 bbdd.2.1 },
  { apply cast_int_eq_of_bdd_3BASE heq.2.2 abdd.2.2 bbdd.2.2 }
end

theorem toBigInt3_eq_zero_of_bounded_3BASE {mem : F → F} {a : bigint3}
    (heq : (a.toBigInt3 : BigInt3 mem) = ⟨0, 0, 0⟩)
    (abdd : a.bounded (3 * BASE - 1)) :
  a = ⟨0, 0, 0⟩ :=
begin
  have : (a.toBigInt3 : BigInt3 mem) = bigint3.toBigInt3 ⟨0, 0, 0⟩,
  { rw heq, simp [bigint3.toBigInt3] },
  apply toBigInt3_eq_toBigInt3_of_bounded_3BASE this abdd,
  simp [bigint3.bounded],
  norm_num
end

@[ext] structure bigint5 := (i0 i1 i2 i3 i4 : ℤ)

def bigint3.bigint5_mul (ix iy : bigint3) : bigint5 :=
{ i0 := ix.i0 * iy.i0,
  i1 := ix.i0 * iy.i1 + ix.i1 * iy.i0,
  i2 := ix.i0 * iy.i2 + ix.i1 * iy.i1 + ix.i2 * iy.i0,
  i3 := ix.i1 * iy.i2 + ix.i2 * iy.i1,
  i4 := ix.i2 * iy.i2 }

def BigInt3.UnreducedBigInt5_mul {mem : F → F} (x y : BigInt3 mem) : UnreducedBigInt5 mem :=
{ d0 := x.d0 * y.d0,
  d1 := x.d0 * y.d1 + x.d1 * y.d0,
  d2 := x.d0 * y.d2 + x.d1 * y.d1 + x.d2 * y.d0,
  d3 := x.d1 * y.d2 + x.d2 * y.d1,
  d4 := x.d2 * y.d2 }

def bigint5.toUnreducedBigInt5 {mem : F → F} (x : bigint5) : UnreducedBigInt5 mem := ⟨x.i0, x.i1, x.i2, x.i3, x.i4⟩

theorem bigint3.bigint5_mul_toUnreducedBigInt5 {mem : F → F} (ix iy : bigint3) :
  ((ix.bigint5_mul iy).toUnreducedBigInt5 : UnreducedBigInt5 mem) =
    BigInt3.UnreducedBigInt5_mul (ix.toBigInt3) (iy.toBigInt3) :=
by simp [bigint5.toUnreducedBigInt5, bigint3.toBigInt3, bigint3.bigint5_mul,
       BigInt3.UnreducedBigInt5_mul]

def bigint3.to_bigint5 (ix : bigint3) : bigint5 := ⟨ix.i0, ix.i1, ix.i2, 0, 0⟩

def BigInt3.toUnreducedBigInt5  {F : Type} [field F] [decidable_eq F] [prelude_hyps F] {mem : F → F}
    (x : BigInt3 mem) : UnreducedBigInt5 mem := ⟨x.d0, x.d1, x.d2, 0, 0⟩

theorem bigint3.to_bigint5_to_Unreduced_BigInt5 {mem : F → F} (ix : bigint3) :
  (ix.to_bigint5.toUnreducedBigInt5 : UnreducedBigInt5 mem) =
    BigInt3.toUnreducedBigInt5 ix.toBigInt3 :=
begin
  simp [bigint5.toUnreducedBigInt5, bigint3.to_bigint5, bigint3.toBigInt3,
    BigInt3.toUnreducedBigInt5]
end

namespace UnreducedBigInt5

def add {mem : F → F} (x y : UnreducedBigInt5 mem) : UnreducedBigInt5 mem :=
{ d0 := x.d0 + y.d0, d1 := x.d1 + y.d1, d2 := x.d2 + y.d2, d3 := x.d3 + y.d3, d4 := x.d4 + y.d4 }

def sub {mem : F → F} (x y : UnreducedBigInt5 mem) : UnreducedBigInt5 mem :=
{ d0 := x.d0 - y.d0, d1 := x.d1 - y.d1, d2 := x.d2 - y.d2, d3 := x.d3 - y.d3, d4 := x.d4 - y.d4 }

end UnreducedBigInt5

namespace bigint5

def val (x : bigint5) : int := x.i4 * ↑BASE^4 + x.i3 * ↑BASE^3 + x.i2 * ↑BASE^2 +
  x.i1 * ↑BASE + x.i0

def add (x y : bigint5) : bigint5 :=
{ i0 := x.i0 + y.i0, i1 := x.i1 + y.i1, i2 := x.i2 + y.i2, i3 := x.i3 + y.i3, i4 := x.i4 + y.i4 }

theorem toUnreducedBigInt5_add {mem : F → F} (x y : bigint5) :
    ((x.add y).toUnreducedBigInt5 : UnreducedBigInt5 mem) =
  UnreducedBigInt5.add (x.toUnreducedBigInt5) (y.toUnreducedBigInt5) :=
by simp [UnreducedBigInt5.add, toUnreducedBigInt5, bigint5.add]

theorem add_val (x y : bigint5) : (x.add y).val = x.val + y.val :=
by { simp [val, add], ring }

def sub (x y : bigint5) : bigint5 :=
{ i0 := x.i0 - y.i0, i1 := x.i1 - y.i1, i2 := x.i2 - y.i2, i3 := x.i3 - y.i3, i4 := x.i4 - y.i4 }

theorem toUnreducedBigInt5_sub {mem : F → F} (x y : bigint5) :
    ((x.sub y).toUnreducedBigInt5 : UnreducedBigInt5 mem) =
  UnreducedBigInt5.sub (x.toUnreducedBigInt5) (y.toUnreducedBigInt5) :=
by simp [UnreducedBigInt5.sub, toUnreducedBigInt5, bigint5.sub]

theorem sub_val (x y : bigint5) : (x.sub y).val = x.val - y.val :=
by { simp [val, sub], ring }

def cmul (c : ℤ) (x : bigint5) : bigint5 :=
{ i0 := c * x.i0, i1 := c * x.i1, i2 := c * x.i2, i3 := c * x.i3, i4 := c * x.i4 }

def bounded (x : bigint5) (b : ℤ) := abs x.i0 ≤ b ∧ abs x.i1 ≤ b ∧ abs x.i2 ≤ b ∧
  abs x.i3 ≤ b ∧ abs x.i4 ≤ b

theorem bounded_of_bounded_of_le {x : bigint5} {b₁ b₂ : ℤ} (bddx : x.bounded b₁) (hle : b₁ ≤ b₂) :
  x.bounded b₂ :=
⟨bddx.1.trans hle, bddx.2.1.trans hle, bddx.2.2.1.trans hle, bddx.2.2.2.1.trans hle,
  bddx.2.2.2.2.trans hle⟩

theorem bounded_add {x y : bigint5} {b₁ b₂ : int} (bddx : x.bounded b₁) (bddy : y.bounded b₂) :
  (x.add y).bounded (b₁ + b₂) :=
⟨(abs_add _ _).trans (add_le_add bddx.1 bddy.1),
  (abs_add _ _).trans (add_le_add bddx.2.1 bddy.2.1),
  (abs_add _ _).trans (add_le_add bddx.2.2.1 bddy.2.2.1),
  (abs_add _ _).trans (add_le_add bddx.2.2.2.1 bddy.2.2.2.1),
  (abs_add _ _).trans (add_le_add bddx.2.2.2.2 bddy.2.2.2.2)⟩

theorem bounded_sub {x y : bigint5} {b₁ b₂ : int} (bddx : x.bounded b₁) (bddy : y.bounded b₂) :
  (x.sub y).bounded (b₁ + b₂) :=
⟨(abs_sub _ _).trans (add_le_add bddx.1 bddy.1),
  (abs_sub _ _).trans (add_le_add bddx.2.1 bddy.2.1),
  (abs_sub _ _).trans (add_le_add bddx.2.2.1 bddy.2.2.1),
  (abs_sub _ _).trans (add_le_add bddx.2.2.2.1 bddy.2.2.2.1),
  (abs_sub _ _).trans (add_le_add bddx.2.2.2.2 bddy.2.2.2.2) ⟩

theorem bounded_cmul {x : bigint5} {c b : int} (bddx : x.bounded b) :
  (x.cmul c).bounded (abs c * b) :=
begin
  simp [cmul, bigint5.bounded, abs_mul],
  exact ⟨mul_le_mul_of_nonneg_left bddx.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.2.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.2.2.1 (abs_nonneg _),
         mul_le_mul_of_nonneg_left bddx.2.2.2.2 (abs_nonneg _)⟩
end

theorem bounded_cmul' {x : bigint5} {c b : int} (h : 0 ≤ c) (bddx : x.bounded b) :
  (x.cmul c).bounded (c * b) :=
by { convert bounded_cmul bddx, rw abs_of_nonneg h }

theorem toUnreducedBigInt5_eq_of_sub_bounded {mem : F → F} {a b : bigint5}
    (heq : (a.toUnreducedBigInt5 : UnreducedBigInt5 mem) = b.toUnreducedBigInt5)
    (bdd : (b.sub a).bounded (PRIME - 1)) :
  a = b :=
begin
  simp [UnreducedBigInt5.ext_iff, bigint5.toUnreducedBigInt5] at heq,
  have h : (PRIME : ℤ) - 1 < PRIME, by norm_num,
  ext,
  exact PRIME.int_coe_inj heq.1 (lt_of_le_of_lt bdd.1 h),
  exact PRIME.int_coe_inj heq.2.1 (lt_of_le_of_lt bdd.2.1 h),
  exact PRIME.int_coe_inj heq.2.2.1 (lt_of_le_of_lt bdd.2.2.1 h),
  exact PRIME.int_coe_inj heq.2.2.2.1 (lt_of_le_of_lt bdd.2.2.2.1 h),
  exact PRIME.int_coe_inj heq.2.2.2.2 (lt_of_le_of_lt bdd.2.2.2.2 h),
end

end bigint5

theorem bigint3.bounded_bigint5_mul {x y : bigint3} {b : ℤ}
    (hx : x.bounded b) (hy : y.bounded b) :
  (x.bigint5_mul y).bounded (3 * b^2) :=
begin
  have bnn : 0 ≤ b := le_trans (abs_nonneg _) hx.1,
  have b2nn: 0 ≤ b^2 := sq_nonneg b,
  have b2le3b2   : b^2 ≤ 3 * b^2, by linarith,
  have b2b2le3b2 : b^2 + b^2 ≤ 3 * b^2, by linarith,
  have b23eq : 3 * b^2 = b^2 + b^2 + b^2, by linarith,
  simp [bigint3.bigint5_mul],
  split,
  { apply le_trans _ b2le3b2,
    rw [abs_mul, pow_two],
    exact mul_le_mul hx.1 hy.1 (abs_nonneg _) bnn },
  split,
  { apply le_trans _ b2b2le3b2,
    refine le_trans (abs_add _ _) _,
    simp_rw [abs_mul, pow_two],
    apply add_le_add,
    exact mul_le_mul hx.1 hy.2.1 (abs_nonneg _) bnn,
    exact mul_le_mul hx.2.1 hy.1 (abs_nonneg _) bnn },
  split,
  { rw [b23eq, pow_two],
    refine le_trans (abs_add _ _) _,
    apply add_le_add,
    refine le_trans (abs_add _ _) _,
    simp_rw abs_mul, apply add_le_add,
    exact mul_le_mul hx.1 hy.2.2 (abs_nonneg _) bnn,
    exact mul_le_mul hx.2.1 hy.2.1 (abs_nonneg _) bnn,
    rw abs_mul,
    exact mul_le_mul hx.2.2 hy.1 (abs_nonneg _) bnn },
  split,
  { apply le_trans _ b2b2le3b2,
    refine le_trans (abs_add _ _) _,
    simp_rw [abs_mul, pow_two],
    apply add_le_add,
    exact mul_le_mul hx.2.1 hy.2.2 (abs_nonneg _) bnn,
    exact mul_le_mul hx.2.2 hy.2.1 (abs_nonneg _) bnn },
  apply le_trans _ b2le3b2,
  rw [abs_mul, pow_two],
  exact mul_le_mul hx.2.2 hy.2.2 (abs_nonneg _) bnn
end

theorem bigint3.to_bigint5_bounded {x : bigint3} {b : ℤ} (hx : x.bounded b) :
  x.to_bigint5.bounded b :=
begin
  use [hx.1, hx.2.1, hx.2.2],
  simp [bigint3.to_bigint5],
  apply le_trans (abs_nonneg _ ) hx.1
end

/-
-- Function: bigint_mul
-/

/- bigint_mul autogenerated specification -/

-- Do not change this definition.
def auto_spec_bigint_mul (mem : F → F) (κ : ℕ) (x y : BigInt3 mem) (ρ_res : UnreducedBigInt5 mem) : Prop :=
  14 ≤ κ ∧
  ρ_res = {
    d0 := x.d0 * y.d0,
    d1 := x.d0 * y.d1 + x.d1 * y.d0,
    d2 := x.d0 * y.d2 + x.d1 * y.d1 + x.d2 * y.d0,
    d3 := x.d1 * y.d2 + x.d2 * y.d1,
    d4 := x.d2 * y.d2
  }

-- You may change anything in this definition except the name and arguments.
def spec_bigint_mul (mem : F → F) (κ : ℕ) (x y : BigInt3 mem) (ρ_res : UnreducedBigInt5 mem) : Prop :=
  ρ_res = BigInt3.UnreducedBigInt5_mul x y

/- bigint_mul soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_bigint_mul
    {mem : F → F}
    (κ : ℕ)
    (x y : BigInt3 mem) (ρ_res : UnreducedBigInt5 mem)
    (h_auto : auto_spec_bigint_mul mem κ x y ρ_res) :
  spec_bigint_mul mem κ x y ρ_res :=
begin
  exact h_auto.2
end

/-
-- Function: nondet_bigint3
-/

/- nondet_bigint3 autogenerated specification -/

-- Do not change this definition.
def auto_spec_nondet_bigint3 (mem : F → F) (κ : ℕ) (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem) : Prop :=
  ∃ res : BigInt3 mem,
  ∃ MAX_SUM : F, MAX_SUM = 232113757366008801543585789 ∧
  mem range_check_ptr = MAX_SUM - (res.d0 + res.d1 + res.d2) ∧
  is_range_checked (rc_bound F) (MAX_SUM - (res.d0 + res.d1 + res.d2)) ∧
  ∃ range_check_ptr₁ : F, range_check_ptr₁ = range_check_ptr + 4 ∧
  mem (range_check_ptr₁ - 3) = res.d0 ∧
  is_range_checked (rc_bound F) (res.d0) ∧
  mem (range_check_ptr₁ - 2) = res.d1 ∧
  is_range_checked (rc_bound F) (res.d1) ∧
  mem (range_check_ptr₁ - 1) = res.d2 ∧
  is_range_checked (rc_bound F) (res.d2) ∧
  10 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₁ ∧
  ρ_res = res

-- You may change anything in this definition except the name and arguments.
def spec_nondet_bigint3 (mem : F → F) (κ : ℕ) (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem) : Prop :=
  ∃ nd0 nd1 nd2 slack : ℕ,
    nd0 < rc_bound F ∧
    nd1 < rc_bound F ∧
    nd2 < rc_bound F ∧
    slack < rc_bound F ∧
    ρ_res = bigint3.toBigInt3 { i0 := nd0, i1 := nd1, i2 := nd2 } ∧
    nd0 + nd1 + nd2 + slack = 3 * (BASE - 1)

theorem nondet_bigint3_corr {mem : F → F} {k : ℕ} {range_check_ptr : F} {ret0 : F} {x : BigInt3 mem}
    (h : spec_nondet_bigint3 mem k range_check_ptr ret0 x) :
  ∃ ix : bigint3, x = ix.toBigInt3 ∧ ix.bounded (3 * (BASE - 1)) :=
begin
  have BASEge1: 1 ≤ BASE, by { unfold BASE, norm_num1 },
  rcases h with ⟨nd0, nd1, nd2, _, _, _, _, _, xeq, sumeq⟩,
  refine ⟨_, xeq, _⟩,
  simp only [bigint3.bounded],
  have : (3 : ℤ) * (↑BASE - 1) = ↑(3 * (BASE - 1)),
  { rw [int.coe_nat_mul, int.coe_nat_sub BASEge1], simp },
  rw [this, ←sumeq], norm_cast, simp only [add_assoc],
  split, apply nat.le_add_right,
  split, apply le_trans (nat.le_add_right _ _) (nat.le_add_left _ _),
  apply le_trans _ (nat.le_add_left _ _),
  apply le_trans (nat.le_add_right _ _) (nat.le_add_left _ _),
end

/- nondet_bigint3 soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_nondet_bigint3
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem)
    (h_auto : auto_spec_nondet_bigint3 mem κ range_check_ptr ρ_range_check_ptr ρ_res) :
  spec_nondet_bigint3 mem κ range_check_ptr ρ_range_check_ptr ρ_res :=
begin
  rcases h_auto with ⟨res, MAX_SUM, MAX_SUM_eq,
    _, ⟨slack, slack_lt, slack_eq⟩,
    rp1, rp1eq,
    resd0eq,
    ⟨nd0, nd0_lt, nd0_eq⟩,
    resd1eq,
    ⟨nd1, nd1_lt, nd1_eq⟩,
    resd2eq,
    ⟨nd2, nd2_lt, nd2_eq⟩,
    _,
    rp1eq',
    reseq⟩,
  use [nd0, nd1, nd2, slack, nd0_lt, nd1_lt, nd2_lt, slack_lt],
  split, { rw reseq, ext; simp [bigint3.toBigInt3]; assumption },
  rw BASE, norm_num1,
  apply @PRIME.nat_coe_field_inj F,
  transitivity 4 * rc_bound F, linarith,
  apply lt_of_le_of_lt (mul_le_mul_left' (rc_bound_hyp F) 4),
  rw PRIME, norm_num1,
  rw PRIME, norm_num1,
  simp only [nat.cast_add, ←slack_eq, ←nd0_eq, ←nd1_eq, ←nd2_eq, add_sub_cancel'_right, nat.cast_bit0, nat.cast_bit1, nat.cast_one],
  rw MAX_SUM_eq
end


end starkware.cairo.common.cairo_secp.bigint
