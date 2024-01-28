/-
  Specifications file for bigint_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.secp256r1.constants_spec

import starkware.cairo.common.cairo_secp.bigint3_spec

open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.secp256r1.constants
namespace starkware.cairo.common.secp256r1.bigint

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

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

theorem toSumBigInt3_add {mem : F → F} (x y : bigint3) :
    ((x.add y).toSumBigInt3 : SumBigInt3 mem) =
  SumBigInt3.add (x.toSumBigInt3) (y.toSumBigInt3) :=
by simp [SumBigInt3.add, toSumBigInt3, bigint3.add]

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

theorem toSumBigInt3_sub {mem : F → F} (x y : bigint3) : ((x.sub y).toSumBigInt3 : SumBigInt3 mem) =
  SumBigInt3.sub (x.toSumBigInt3) (y.toSumBigInt3) :=
by simp [SumBigInt3.sub, toSumBigInt3, bigint3.sub]

theorem sub_val (x y : bigint3) : (x.sub y).val = x.val - y.val :=
by { simp [val, sub], ring }

def cmul (c : ℤ) (x : bigint3) : bigint3 :=
{ i0 := c * x.i0, i1 := c * x.i1, i2 := c * x.i2}

theorem cmul_val (c : ℤ) (x : bigint3) : (x.cmul c).val = c * x.val :=
by { simp [val, cmul], ring }

def mul (x y : bigint3) : bigint3 :=
{ i0 := x.i0 * y.i0 + BASE3_MOD_P0 * (x.i1 * y.i2 + x.i2 * y.i1) + BASE4_MOD_P0 * (x.i2 * y.i2),
  i1 := x.i0 * y.i1 + x.i1 * y.i0 + BASE3_MOD_P1 * (x.i1 * y.i2 + x.i2 * y.i1) + BASE4_MOD_P1 * (x.i2 * y.i2),
  i2 := x.i0 * y.i2 + x.i1 * y.i1 + x.i2 * y.i0 + BASE3_MOD_P2 * (x.i1 * y.i2 + x.i2 * y.i1) + BASE4_MOD_P2 * (x.i2 * y.i2)}

theorem mul_val (x y : bigint3) : (x.mul y).val ≡ x.val * y.val [ZMOD secp_p] :=
begin
  have : x.val * y.val - (x.mul y).val = (x.i1 * y.i2 + x.i2 * y.i1) * (BASE^3 - BASE3_MOD_P) +
    x.i2 * y.i2 * (BASE^4 - BASE4_MOD_P),
  { simp only [val, mul, BASE3_MOD_P, BASE4_MOD_P, val], ring },
  rw [BASE3_MOD_P_diff_eq, BASE4_MOD_P_diff_eq, ←mul_assoc, ←mul_assoc, ←add_mul] at this,
  rw [int.modeq_iff_dvd, this],
  apply dvd_mul_left
end

def sqr (x : bigint3) : bigint3 := x.mul x

theorem sqr_val (x : bigint3) : x.sqr.val ≡ x.val^2 [ZMOD secp_p] :=
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

-- secp256r1 requires this more refined bound:

def bounded' (x : bigint3) (b : ℤ) := abs x.i0 ≤ 8 * b ∧ abs x.i1 ≤ 8 * b ∧ abs x.i2 ≤ b

theorem bounded'_add {x y : bigint3} {b₁ b₂ : int} (bddx : x.bounded' b₁) (bddy : y.bounded' b₂) :
  (x.add y).bounded' (b₁ + b₂) :=
begin
  split,
  { apply le_trans, apply abs_add, rw [mul_add], apply (add_le_add bddx.1 bddy.1) },
    split,
  { apply le_trans, apply abs_add, rw [mul_add], apply (add_le_add bddx.2.1 bddy.2.1) },
  { apply le_trans, apply abs_add, apply (add_le_add bddx.2.2 bddy.2.2) },
end

theorem bounded'_sub {x y : bigint3} {b₁ b₂ : int} (bddx : x.bounded' b₁) (bddy : y.bounded' b₂) :
  (x.sub y).bounded' (b₁ + b₂) :=
begin
  split,
  { apply le_trans, apply abs_sub, rw [mul_add], apply (add_le_add bddx.1 bddy.1) },
    split,
  { apply le_trans, apply abs_sub, rw [mul_add], apply (add_le_add bddx.2.1 bddy.2.1) },
  { apply le_trans, apply abs_sub, apply (add_le_add bddx.2.2 bddy.2.2) },
end

theorem bounded'_cmul {x : bigint3} {c b : int} (bddx : x.bounded' b) :
  (x.cmul c).bounded' (abs c * b) :=
begin
  simp [cmul, bigint3.bounded', abs_mul],
  split,
  { apply le_trans, apply mul_le_mul_of_nonneg_left bddx.1 (abs_nonneg _),
    rw mul_left_comm },
  split,
  { apply le_trans, apply mul_le_mul_of_nonneg_left bddx.2.1 (abs_nonneg _),
    rw mul_left_comm },
  exact mul_le_mul_of_nonneg_left bddx.2.2 (abs_nonneg _)
end

theorem bounded'_cmul' {x : bigint3} {c b : int} (h : 0 ≤ c) (bddx : x.bounded' b) :
  (x.cmul c).bounded' (c * b) :=
by { convert bounded'_cmul bddx, rw abs_of_nonneg h }

theorem bounded'_of_bounded'_of_le {x : bigint3} {b₁ b₂ : ℤ} (bddx : x.bounded' b₁) (hle : b₁ ≤ b₂) :
  x.bounded' b₂ :=
begin
  split,
  { apply bddx.1.trans, apply mul_le_mul_of_nonneg_left hle, norm_num1 },
  split,
  { apply bddx.2.1.trans, apply mul_le_mul_of_nonneg_left hle, norm_num1 },
  exact bddx.2.2.trans hle
end

theorem bounded_of_bounded'  {x : bigint3} {b : ℤ} (bddx : x.bounded' b) : x.bounded (8 * b) :=
begin
  use [bddx.1, bddx.2.1],
  apply le_trans bddx.2.2,
  suffices : 1 * b ≤ 8 * b,
  { rwa [one_mul] at this },
  have : 0 ≤ b := (abs_nonneg _).trans bddx.2.2,
  apply mul_le_mul_of_nonneg_right _ this,
  norm_num1
end

-- This is sharp in the sense that replacing `2^58` by `2^57` fails.
theorem bounded_mul {x y : bigint3} {b : ℤ} (hx : x.bounded' b) (hy : y.bounded' b) :
  (x.mul y).bounded (b^2 * (2^76 + 2^58)) :=
begin
  have b8nonneg : 0 ≤ 8 * b := le_trans (abs_nonneg _) hx.1,
  have bnonneg : 0 ≤ b := by
    {apply nonneg_of_mul_nonneg_right b8nonneg, norm_num1 },
  simp only [bigint3.mul, bigint3.bounded],
  split,
   { transitivity (8 * b) * (8 * b) + 4 * (8 * b * b + b * (8 * b)) +
       2^56 * (b * b) , -- (8x)*(8x) + 4*2*(8x)*x + 2**56*x*x
     { apply le_trans, apply abs_add,
       apply add_le_add, rw [BASE3_MOD_P0],
       apply le_trans, apply abs_add,
       apply add_le_add,
       rw [abs_mul], apply mul_le_mul hx.1 hy.1 (abs_nonneg _) b8nonneg,
       rw [abs_mul, abs_of_nonneg], apply mul_le_mul_of_nonneg_left, norm_num1,
       apply le_trans, apply abs_add,
       apply add_le_add,
       rw [abs_mul], apply mul_le_mul hx.2.1 hy.2.2 (abs_nonneg _) b8nonneg,
       rw [abs_mul], apply mul_le_mul hx.2.2 hy.2.1 (abs_nonneg _) bnonneg,
       norm_num1, norm_num1,
       rw [abs_mul], apply mul_le_mul,
       rw [BASE4_MOD_P0], norm_num1,
       rw abs_of_nonneg, norm_num1,
       rw [abs_mul], apply mul_le_mul hx.2.2 hy.2.2 (abs_nonneg _) bnonneg,
       apply abs_nonneg, norm_num1 },
       apply le_of_eq_of_le,
       show _ = b^2 * (128 + 2^56), ring,
       apply mul_le_mul_of_nonneg_left, norm_num1, apply pow_two_nonneg },
    split,
    { transitivity (8 * b) * (8 * b) + (8 * b) * (8 * b) +
        | BASE3_MOD_P1 | * (8 * b * b + b * (8 * b)) + | BASE4_MOD_P1 | * (b * b),
      apply le_trans, apply abs_add,
      apply add_le_add,
      apply le_trans, apply abs_add,
      apply add_le_add,
      apply le_trans, apply abs_add,
      apply add_le_add,
      rw [abs_mul],
      apply mul_le_mul hx.1 hy.2.1 (abs_nonneg _) b8nonneg,
      rw [abs_mul],
      apply mul_le_mul hx.2.1 hy.1 (abs_nonneg _) b8nonneg,
      rw [abs_mul],
      apply mul_le_mul_of_nonneg_left,
      apply le_trans, apply abs_add,
      rw [abs_mul, abs_mul],
      apply add_le_add,
      apply mul_le_mul hx.2.1 hy.2.2 (abs_nonneg _) b8nonneg,
      apply mul_le_mul hx.2.2 hy.2.1 (abs_nonneg _) bnonneg,
      apply abs_nonneg,
      rw [abs_mul, abs_mul],
      apply mul_le_mul_of_nonneg_left,
      apply mul_le_mul hx.2.2 hy.2.2 (abs_nonneg _) bnonneg,
      apply abs_nonneg,
      apply le_of_eq_of_le,
      show _ = b^2 * (128 + 2^16 + (2^66 - 4)),
      { rw [BASE3_MOD_P1, BASE4_MOD_P1], norm_num [abs_of_neg], ring },
      apply mul_le_mul_of_nonneg_left, norm_num1, apply pow_two_nonneg },
    transitivity 8 * b * b + (8 * b) * (8 * b) + b * (8 * b) +
      | BASE3_MOD_P2 | * (8 * b * b + b * (8 * b)) + | BASE4_MOD_P2 | * (b * b),
    apply le_trans, apply abs_add,
    apply add_le_add,
    apply le_trans, apply abs_add,
    apply add_le_add,
    apply le_trans, apply abs_add,
    apply add_le_add,
    apply le_trans, apply abs_add,
    apply add_le_add,
    rw [abs_mul],
    apply mul_le_mul hx.1 hy.2.2 (abs_nonneg _) b8nonneg,
    rw [abs_mul],
    apply mul_le_mul hx.2.1 hy.2.1 (abs_nonneg _) b8nonneg,
    rw [abs_mul],
    apply mul_le_mul hx.2.2 hy.1 (abs_nonneg _) bnonneg,
    rw [abs_mul],
    have : |x.i1 * y.i2 + x.i2 * y.i1| ≤ (8 * b * b + b * (8 * b)),
    { apply le_trans, apply abs_add,
      apply add_le_add,
      rw [abs_mul],
      apply mul_le_mul hx.2.1 hy.2.2 (abs_nonneg _) b8nonneg,
      rw [abs_mul],
      apply mul_le_mul hx.2.2 hy.2.1 (abs_nonneg _) bnonneg },
    -- TODO(Jeremy): I don't know why `convert` is needed, but `apply` and `refine` result in
    -- nondeterministic timeouts
    convert mul_le_mul_of_nonneg_left this (abs_nonneg _),
    rw [abs_mul],
    apply mul_le_mul_of_nonneg_left,
    rw [abs_mul],
    apply mul_le_mul hx.2.2 hy.2.2 (abs_nonneg _) bnonneg,
    apply abs_nonneg,
    apply le_of_eq_of_le,
    show _ = b^2 * (80 + |BASE3_MOD_P2| * 16 + |BASE4_MOD_P2|),
    { ring },
    rw [BASE3_MOD_P2, BASE4_MOD_P2], norm_num [abs_of_nonneg],
    apply mul_le_mul_of_nonneg_left, norm_num1, apply pow_two_nonneg
end

theorem bounded_sqr {x : bigint3} {b : ℤ} (hx : x.bounded' b) :
  (x.sqr).bounded (b^2 * (2^76 + 2^58)) :=
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

theorem cast_int_eq_of_bdd_8D2BOUND {i j : int}
    (heq : (i : F) = (j : F))
    (ibdd : abs i ≤ 8 * D2_BOUND)
    (jbdd : abs j ≤ 8 * D2_BOUND) :
  i = j :=
begin
  apply PRIME.int_coe_inj heq,
  apply lt_of_le_of_lt,
  apply abs_sub,
  apply lt_of_le_of_lt,
  apply add_le_add jbdd ibdd,
  dsimp only [D2_BOUND, PRIME],
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

theorem toBigInt3_eq_toBigInt3_of_bounded_8D2BOUND {mem : F → F} {a b : bigint3}
    (heq : (a.toBigInt3 : BigInt3 mem) = b.toBigInt3)
    (abdd : a.bounded (8 * D2_BOUND))
    (bbdd : b.bounded (8 * D2_BOUND)) :
  a = b :=
begin
  simp [BigInt3.ext_iff, bigint3.toBigInt3] at heq,
  ext,
  { apply cast_int_eq_of_bdd_8D2BOUND heq.1 abdd.1 bbdd.1 },
  { apply cast_int_eq_of_bdd_8D2BOUND heq.2.1 abdd.2.1 bbdd.2.1 },
  { apply cast_int_eq_of_bdd_8D2BOUND heq.2.2 abdd.2.2 bbdd.2.2 }
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

theorem toBigInt3_eq_zero_of_bounded_8D2BOUND {mem : F → F} {a : bigint3}
    (heq : (a.toBigInt3 : BigInt3 mem) = ⟨0, 0, 0⟩)
    (abdd : a.bounded (8 * D2_BOUND)) :
  a = ⟨0, 0, 0⟩ :=
begin
  have : (a.toBigInt3 : BigInt3 mem) = bigint3.toBigInt3 ⟨0, 0, 0⟩,
  { rw heq, simp [bigint3.toBigInt3] },
  apply toBigInt3_eq_toBigInt3_of_bounded_8D2BOUND this abdd,
  simp [bigint3.bounded]
end

/-
-- Function: nondet_bigint3
-/

-- You may change anything in this definition except the name and arguments.
def spec_nondet_bigint3 (mem : F → F) (κ : ℕ) (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem) : Prop :=
  ∃ nd0 nd1 nd2 : ℕ,
    nd0 < rc_bound F ∧
    nd1 < rc_bound F ∧
    nd2 < rc_bound F ∧
    ρ_res = bigint3.toBigInt3 { i0 := nd0, i1 := nd1, i2 := nd2 } ∧
    nd0 + nd1 < 2 * BASE ∧
    nd2 < D2_BOUND

theorem nondet_bigint3_corr {mem : F → F} {k : ℕ} {range_check_ptr : F} {ret0 : F} {x : BigInt3 mem}
    (h : spec_nondet_bigint3 mem k range_check_ptr ret0 x) :
  ∃ ix : bigint3, x = ix.toBigInt3 ∧ ix.bounded' D2_BOUND :=
begin
  have BASEge1: 1 ≤ BASE, by { unfold BASE, norm_num1 },
  rcases h with ⟨nd0, nd1, nd2, _, _, _, xeq, sumlt, hlt⟩,
  refine ⟨_, xeq, _⟩,
  simp [bigint3.bounded'],
  have : (nd0 : ℤ) ≤ ((2 * BASE : ℕ) : ℤ),
  { rw [int.coe_nat_le_coe_nat_iff], apply le_of_lt,  apply lt_of_le_of_lt _ sumlt,
    apply nat.le_add_right },
  split,
  apply le_trans this, rw [BASE, nat.cast_mul, nat.cast_pow], simp_int_casts, norm_num1,
  have : (nd1 : ℤ) ≤ ((2 * BASE : ℕ) : ℤ),
  { rw [int.coe_nat_le_coe_nat_iff], apply le_of_lt,  apply lt_of_le_of_lt _ sumlt,
    apply nat.le_add_left },
  split,
  apply le_trans this, rw [BASE, nat.cast_mul, nat.cast_pow], simp_int_casts, norm_num1,
  have : (nd2 : ℤ) ≤ D2_BOUND,
  { rw [int.coe_nat_le_coe_nat_iff], apply le_of_lt hlt },
  apply le_trans this, rw D2_BOUND, simp_int_casts, norm_num1,
end


/- nondet_bigint3 autogenerated specification -/

-- Do not change this definition.
def auto_spec_nondet_bigint3 (mem : F → F) (κ : ℕ) (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem) : Prop :=
  ∃ res : BigInt3 mem,
  mem range_check_ptr = res.d0 + res.d1 + (2 ^ 128 - 2 * BASE) ∧
  is_range_checked (rc_bound F) (res.d0 + res.d1 + (2 ^ 128 - 2 * BASE)) ∧
  mem (range_check_ptr + 1) = res.d2 + (2 ^ 128 - D2_BOUND) ∧
  is_range_checked (rc_bound F) (res.d2 + (2 ^ 128 - D2_BOUND)) ∧
  ∃ range_check_ptr₁ : F, range_check_ptr₁ = range_check_ptr + 2 ∧
  ∃ range_check_ptr₂ : F, range_check_ptr₂ = range_check_ptr₁ + 3 ∧
  mem (range_check_ptr₂ - 3) = res.d0 ∧
  is_range_checked (rc_bound F) (res.d0) ∧
  mem (range_check_ptr₂ - 2) = res.d1 ∧
  is_range_checked (rc_bound F) (res.d1) ∧
  mem (range_check_ptr₂ - 1) = res.d2 ∧
  is_range_checked (rc_bound F) (res.d2) ∧
  10 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₂ ∧
  ρ_res = res

/- nondet_bigint3 soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_nondet_bigint3
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr ρ_range_check_ptr : F) (ρ_res : BigInt3 mem)
    (h_auto : auto_spec_nondet_bigint3 mem κ range_check_ptr ρ_range_check_ptr ρ_res) :
  spec_nondet_bigint3 mem κ range_check_ptr ρ_range_check_ptr ρ_res :=
begin
  rcases h_auto with ⟨res,
    _, ⟨sum1, sum1_lt, sum1_eq⟩,
    _, ⟨sum2, sum2_lt, sum2_eq⟩,
    rp1, rp1eq,
    rp2, rp2eq,
    resd0eq,
    ⟨nd0, nd0_lt, nd0_eq⟩,
    resd1eq,
    ⟨nd1, nd1_lt, nd1_eq⟩,
    resd2eq,
    ⟨nd2, nd2_lt, nd2_eq⟩,
    _,
    rp2eq',
    reseq⟩,
  use [nd0, nd1, nd2, nd0_lt, nd1_lt, nd2_lt],
  split, { rw reseq, ext; simp [bigint3.toBigInt3]; assumption },
  split,
  { have : nd0 + nd1 + (2 ^ 128 - 2 * BASE) = sum1,
    { apply @PRIME.nat_coe_field_inj F,
      transitivity 2^128 + 2^128 + (2 ^ 128 - 2 * BASE),
      apply add_lt_add_right,
      apply add_lt_add,
      apply lt_of_lt_of_le nd0_lt (rc_bound_hyp F),
      apply lt_of_lt_of_le nd1_lt (rc_bound_hyp F),
      rw [BASE, PRIME], norm_num1,
      apply lt_trans sum1_lt rc_bound_lt_PRIME,
      rw [nat.cast_add, nat.cast_add, ←nd0_eq, ←nd1_eq, ←sum1_eq],
      rw [nat.cast_sub, nat.cast_pow, nat.cast_mul, BASE],
      simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
      rw [BASE], norm_num1 },
    apply @nat.lt_of_add_lt_add_right _ (2 ^ 128 - 2 * BASE),
    rw this,
    apply lt_of_lt_of_le (lt_of_lt_of_le sum1_lt (rc_bound_hyp F)),
    rw BASE; norm_num1 },
  have : nd2 + (2 ^ 128 - D2_BOUND) = sum2,
  { apply @PRIME.nat_coe_field_inj F,
    transitivity 2^128 + (2 ^ 128 - D2_BOUND),
    apply add_lt_add_right,
    apply lt_of_lt_of_le nd2_lt (rc_bound_hyp F),
    rw [D2_BOUND, PRIME], norm_num1,
    apply lt_trans sum2_lt rc_bound_lt_PRIME,
      rw [nat.cast_add, ←nd2_eq, ←sum2_eq],
      rw [nat.cast_sub, nat.cast_pow, D2_BOUND, nat.cast_bit0, nat.cast_one],
    rw [D2_BOUND], norm_num1 },
  apply @nat.lt_of_add_lt_add_right _ (2 ^ 128 - D2_BOUND),
  rw this,
  apply lt_of_lt_of_le (lt_of_lt_of_le sum2_lt (rc_bound_hyp F)),
  rw D2_BOUND; norm_num1
end

end starkware.cairo.common.secp256r1.bigint
