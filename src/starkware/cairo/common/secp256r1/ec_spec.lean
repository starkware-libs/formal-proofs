/-
  Specifications file for ec_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.math_spec
import starkware.cairo.common.secp256r1.bigint_spec
import starkware.cairo.common.cairo_secp.ec_point_spec
import starkware.cairo.common.cairo_secp.bigint3_spec
import starkware.cairo.common.secp256r1.constants_spec
import starkware.cairo.common.uint256_spec
import starkware.cairo.common.secp256r1.field_spec

import starkware.cairo.common.alloc_spec

-- JDA: Additional imports.
import starkware.cairo.common.secp256r1.elliptic_curves
import number_theory.legendre_symbol.quadratic_reciprocity

open starkware.cairo.common.alloc
open starkware.cairo.common.cairo_secp.ec_point
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.math
open starkware.cairo.common.uint256
open starkware.cairo.common.secp256r1.field
open starkware.cairo.common.secp256r1.bigint
open starkware.cairo.common.secp256r1.constants
namespace starkware.cairo.common.secp256r1.ec

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

/-
-- Data for writing the specifications.
-/

structure BddECPointData {mem : F → F} (secpF : Type*) [field secpF] (pt : EcPoint mem) :=
(ix iy : bigint3)
(ixbdd : ix.bounded' D2_BOUND)
(iybdd : iy.bounded' D2_BOUND)
(ptxeq : pt.x = ix.toBigInt3)
(ptyeq : pt.y = iy.toBigInt3)
(onEC : pt.x = ⟨0, 0, 0⟩ ∨ (iy.val : secpF)^2 = (ix.val : secpF)^3 + ALPHA * ix.val + BETA)

theorem BddECPointData.onEC' {mem : F → F} {secpF : Type*} [field secpF] {pt : EcPoint mem}
    (h : BddECPointData secpF pt) (h' : pt.x ≠ ⟨0, 0, 0⟩) :
  (h.iy.val : secpF)^2 = (h.ix.val : secpF)^3 + ALPHA * h.ix.val + BETA :=
or.resolve_left h.onEC h'

section secpF

variables
  {secpF : Type}   -- in practice, zmod secp_p
  [field secpF]    -- in practice, @zmod.field _ ⟨prime_secp⟩
  [char_p secpF secp_p]
  [decidable_eq secpF]

def BddECPointData.toECPoint {mem : F → F} {pt : EcPoint mem} (h : BddECPointData secpF pt) :
    ECPoint secpF :=
if h' : pt.x = ⟨0, 0, 0⟩ then
  ECPoint.ZeroPoint
else
  ECPoint.AffinePoint ⟨h.ix.val, h.iy.val, h.onEC' h'⟩

def BddECPointData.zero {mem : F → F} : BddECPointData secpF (⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩ : EcPoint mem)  :=
{ ix := ⟨0, 0, 0⟩,
  iy := ⟨0, 0, 0⟩,
  ixbdd := by simp [bigint3.bounded']; norm_num1,
  iybdd := by simp [bigint3.bounded']; norm_num1,
  ptxeq := by simp [bigint3.toBigInt3],
  ptyeq := by simp [bigint3.toBigInt3],
  onEC := or.inl rfl }

end secpF

class secp_field (secpF : Type*) extends ec_field secpF, char_p secpF secp_p :=
(BETA_not_square : ∀ y : secpF, y^2 ≠ BETA)
(order_large : ∀ {pt : ECPoint secpF}, pt ≠ 0 → ∀ {n : ℕ}, n ≠ 0 → n < 2^252 → n • pt ≠ 0)

theorem secp_field.order_large_corr {secpF : Type*} [secp_field secpF]
  {pt : ECPoint secpF} (ptnz : pt ≠ 0) :
    ∀ {n : ℕ}, n < 2^128 → ¬ ((n * 2) • pt = pt ∨ (n * 2) • pt = -pt) :=
begin
  rintros n nlt (h | h),
  { cases n with npred,
    { rw [zero_mul, zero_smul] at h, exact ptnz h.symm},
    have : (npred * 2 + 1) • pt = 0,
    { rw [nat.succ_eq_add_one, add_mul, one_mul] at h,
      have : (npred * 2 + 1 + 1) • pt = pt := h,
      rw [add_smul, one_smul, ←sub_eq_zero, add_sub_cancel] at this,
      exact this },
    revert this, apply secp_field.order_large ptnz,
    { apply nat.succ_ne_zero},
    apply lt_of_lt_of_le,
    apply add_lt_add_right,
    apply lt_of_le_of_lt,
    apply mul_le_mul_of_nonneg_right,
    apply le_of_lt,
    apply lt_trans (nat.lt_succ_self _) nlt,
    norm_num,
    apply nat.lt_succ_self,
    norm_num },
  rw [eq_neg_iff_add_eq_zero, ← one_smul _ pt, smul_smul (n * 2) 1, ← add_smul] at h,
  revert h,
  apply secp_field.order_large ptnz,
  { apply nat.succ_ne_zero },
  rw [mul_assoc, mul_one],
  apply lt_trans,
  change (_ < 2^128 * 2 + 1),
  apply add_lt_add_right,
  apply mul_lt_mul_of_pos_right nlt,
  norm_num, norm_num
end

theorem secp_field.order_large_corr' {secpF : Type*} [secp_field secpF]
  {pt : ECPoint secpF} {n m : ℕ} (nlt : n < 2^252) (mlt : m < 2^252)
      (ptnz : pt ≠ 0) (heq : n • pt = m • pt) :
    n = m :=
begin
  by_contradiction h,
  wlog h' : n < m,
  apply this mlt nlt ptnz heq.symm (ne.symm h),
  contrapose! h,
  linarith,
  rwa [←ne, ←lt_or_lt_iff_ne] at h,
  have : (m - n) • pt = 0,
  { rw [sub_nsmul _ (le_of_lt h'), heq, add_right_neg] },
  revert this,
  apply secp_field.order_large ptnz,
  { rw [ne, tsub_eq_zero_iff_le],
    apply not_le_of_gt h' },
  apply lt_of_le_of_lt tsub_le_self mlt
end

theorem secp_field.y_ne_zero_of_on_ec  {secpF : Type*} [secp_field secpF] {x y : secpF}
  (h : on_ec (x, y)) : y ≠ 0 :=
by { contrapose! h, simp only [on_ec, h, ←sub_eq_iff_eq_add, pow_two, mul_zero, zero_sub],
     apply ne.symm, apply ec_field.ec_no_zero }

theorem secp_field.x_ne_zero_of_on_ec {secpF : Type*} [secp_field secpF] {x y : secpF}
  (h : on_ec (x, y)) : x ≠ 0 :=
by { contrapose! h, simp [on_ec, h, secp_field.BETA_not_square] }

theorem secp_field.eq_zero_of_double_eq_zero {secpF : Type*} [secp_field secpF]
  {x : ECPoint secpF} (h : 2 • x = 0) : x = 0 :=
begin
  cases x, { refl },
  simp [two_smul, ECPoint.add_def, ECPoint.add] at h,
  have : x.y ≠ -x.y,
  { intro h',
    have h_on_ec := x.h, dsimp [on_ec] at h_on_ec,
    have : 2 * x.y = 0,
    { rwa [two_mul, ←eq_neg_iff_add_eq_zero] },
    rw mul_eq_zero at this,
    simp only [or.resolve_left this ec_field.two_ne_zero, pow_two, zero_mul] at h_on_ec,
    apply ec_field.ec_no_zero x.x,
    have := h_on_ec.symm,
    rw [add_assoc, ← eq_neg_iff_add_eq_zero] at this,
    rw this, abel },
  rw dif_neg this at h,
  contradiction
end

namespace BddECPointData

theorem toECPoint_zero {mem : F → F} (secpF : Type) [secp_field secpF] :
  (BddECPointData.zero : BddECPointData secpF (⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩ : EcPoint mem)).toECPoint =
    0 :=
by { simp [toECPoint], refl }

theorem pt_zero_iff' {mem : F → F} {secpF : Type} [secp_field secpF]
    {pt : EcPoint mem} (h : BddECPointData secpF pt) :
  pt.x = ⟨0, 0, 0⟩ ↔ h.ix.val = 0 :=
begin
  split,
  { rw [h.ptxeq],
    intro heq,
    rw toBigInt3_eq_zero_of_bounded_8D2BOUND heq (bigint3.bounded_of_bounded' h.ixbdd),
    simp [bigint3.val] },
  intro heq,
  cases h.onEC with h1 h1, { exact h1 },
  exfalso,
  have : on_ec ((h.ix.val : secpF), (h.iy.val : secpF)):= h1,
  apply secp_field.x_ne_zero_of_on_ec this,
  simp [heq]
end

theorem pt_zero_iff {mem : F → F} {secpF : Type} [secp_field secpF]
    {pt : EcPoint mem} (h : BddECPointData secpF pt) :
  pt.x = ⟨0, 0, 0⟩ ↔ (h.ix.val : secpF) = 0 :=
begin
  split,
  { rw [h.ptxeq],
    intro heq,
    rw toBigInt3_eq_zero_of_bounded_8D2BOUND heq (bigint3.bounded_of_bounded' h.ixbdd),
    simp [bigint3.val] },
  intro heq,
  cases h.onEC with h1 h1, { exact h1 },
  exfalso,
  have : on_ec ((h.ix.val : secpF), (h.iy.val : secpF)):= h1,
  apply secp_field.x_ne_zero_of_on_ec this,
  simp [heq]
end

theorem toECPoint_eq_zero_iff {mem : F → F} {secpF : Type} [secp_field secpF] {pt : EcPoint mem} (h : BddECPointData secpF pt) :
  h.toECPoint = 0 ↔ pt.x = ⟨0, 0, 0⟩ :=
by { by_cases h : pt.x = ⟨0, 0, 0⟩; simp [BddECPointData.toECPoint, h, ECPoint.zero_def] }

theorem toECPoint_eq_of_eq_of_ne {mem : F → F} {secpF : Type} [secp_field secpF] {pt0 pt1 : EcPoint mem}
    {h0 : BddECPointData secpF pt0}
    {h1 : BddECPointData secpF pt1}
    (hxeq : (h0.ix.val : secpF) = (h1.ix.val : secpF))
    (hyne : (h0.iy.val : secpF) ≠ -(h1.iy.val : secpF)) :
  h0.toECPoint = h1.toECPoint :=
begin
  have aux: pt0.x = ⟨0, 0, 0⟩ ↔ pt1.x = ⟨0, 0, 0⟩,
  { rw [h1.pt_zero_iff, ←hxeq, ←h0.pt_zero_iff] },
  by_cases h: pt0.x = ⟨0, 0, 0⟩,
  { have : pt1.x = ⟨0, 0, 0⟩, by rwa ←aux,
    rw [h0.toECPoint_eq_zero_iff.mpr h, h1.toECPoint_eq_zero_iff.mpr this] },
  have : ¬ (pt1.x = ⟨0, 0, 0⟩), by rwa ←aux,
  rw [BddECPointData.toECPoint, BddECPointData.toECPoint, dif_neg h, dif_neg this],
  congr' 1, ext, { exact hxeq }, dsimp,
  have : (h0.iy.val : secpF)^2 = (h1.iy.val : secpF)^2,
  { rw [h0.onEC' h, h1.onEC' this, hxeq] },
  have := eq_or_eq_neg_of_sq_eq_sq _ _ this,
  exact or.resolve_right this hyne
end

theorem toECPoint_eq_or_eq_neg {mem : F → F} {secpF : Type} [secp_field secpF] {pt0 pt1 : EcPoint mem}
    {h0 : BddECPointData secpF pt0}
    {h1 : BddECPointData secpF pt1}
    (hxeq : (h0.ix.val : secpF) = (h1.ix.val : secpF)) :
  h0.toECPoint = h1.toECPoint ∨ h0.toECPoint = - h1.toECPoint :=
begin
  have aux: pt0.x = ⟨0, 0, 0⟩ ↔ pt1.x = ⟨0, 0, 0⟩,
  { rw [h1.pt_zero_iff, ←hxeq, ←h0.pt_zero_iff] },
  by_cases hz: pt0.x = ⟨0, 0, 0⟩,
  { have : pt1.x = ⟨0, 0, 0⟩, by rwa ←aux,
    left,
    rw [h0.toECPoint_eq_zero_iff.mpr hz, h1.toECPoint_eq_zero_iff.mpr this], },
  by_cases h : (h0.iy.val : secpF) = -(h1.iy.val : secpF),
  swap,
  { left, exact toECPoint_eq_of_eq_of_ne hxeq h},
  right,
  have : pt1.x ≠ ⟨0, 0, 0⟩, { intro h', exact hz (aux.mpr h') },
  rw [BddECPointData.toECPoint, BddECPointData.toECPoint, dif_neg hz,
    dif_neg this, ECPoint.neg_def, ECPoint.neg],
  congr, exact hxeq, exact h
end

def cast {mem : F → F} {secpF : Type} [secp_field secpF] {pt0 pt1 : EcPoint mem}
    (hp0 : BddECPointData secpF pt0) (heq : pt0 = pt1) :
  BddECPointData secpF pt1 :=
⟨hp0.ix, hp0.iy, hp0.ixbdd, hp0.iybdd, by rw [←heq, hp0.ptxeq], by rw [←heq, hp0.ptyeq],
  by rw [←heq]; exact hp0.onEC⟩

@[simp] theorem cast_toECPoint_eq  {mem : F → F} {secpF : Type} [secp_field secpF] {pt0 pt1 : EcPoint mem}
      (hp0 : BddECPointData secpF pt0) (heq : pt0 = pt1) :
  (hp0.cast heq).toECPoint = hp0.toECPoint :=
by cases heq; refl

end BddECPointData

theorem double_Affine {secpF : Type} [secp_field secpF] {x1 y1 x2 y2 : secpF}
    (h1 : on_ec (x1, y1)) (h2 : on_ec (x2, y2))
    (heq : ec_double (x1, y1) = (x2, y2)) :
  2 • ECPoint.AffinePoint ⟨x1, y1, h1⟩ = ECPoint.AffinePoint ⟨x2, y2, h2⟩ :=
begin
  have : y1 ≠ -y1,
  { intro heq,
    apply secp_field.y_ne_zero_of_on_ec h1,
    have : 2 * y1 = 0,
    { rwa [two_mul, add_eq_zero_iff_eq_neg] },
    rw mul_eq_zero at this,
    exact this.resolve_left ec_field.two_ne_zero },
  rw two_smul,
  simp [ECPoint.add_def, ECPoint.add], dsimp,
  rw [dif_neg this], congr; simp [heq]
end

theorem Affine_add_Affine {secpF : Type} [secp_field secpF] {x1 y1 x2 y2 x3 y3 : secpF}
    (h1 : on_ec (x1, y1)) (h2 : on_ec (x2, y2)) (h3 : on_ec (x3, y3)) (hne : x1 ≠ x2)
    (heq : ec_add (x1, y1) (x2, y2) = (x3, y3)) :
  ECPoint.AffinePoint ⟨x1, y1, h1⟩ + ECPoint.AffinePoint ⟨x2, y2, h2⟩ =
    ECPoint.AffinePoint ⟨x3, y3, h3⟩ :=
begin
  simp [ECPoint.add_def, ECPoint.add], dsimp,
  rw [dif_neg hne], congr; simp [heq]
end

-- You may change anything in this definition except the name and arguments.
def spec_compute_doubling_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∀ ix iy : bigint3,
    ix.bounded' D2_BOUND →
    iy.bounded' D2_BOUND →
    point.x = ix.toBigInt3 →
    point.y = iy.toBigInt3 →
    ∃ is : bigint3,
      is.bounded' D2_BOUND ∧
      ρ_slope = is.toBigInt3 ∧
      3 * ix.val^2 + ALPHA ≡ 2 * iy.val * is.val [ZMOD secp_p]

/-
-- Function: compute_doubling_slope
-/

/- compute_doubling_slope autogenerated specification -/

-- Do not change this definition.
def auto_spec_compute_doubling_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (slope : BigInt3 mem), spec_nondet_bigint3 mem κ₁ range_check_ptr range_check_ptr₁ slope ∧
  ∃ (κ₂ : ℕ) (x_sqr : UnreducedBigInt3 mem), spec_unreduced_sqr mem κ₂ point.x x_sqr ∧
  ∃ (κ₃ : ℕ) (slope_y : UnreducedBigInt3 mem), spec_unreduced_mul mem κ₃ slope point.y slope_y ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₂ : F), spec_verify_zero mem κ₄ range_check_ptr₁ {
    d0 := 3 * x_sqr.d0 + ALPHA - 2 * slope_y.d0,
    d1 := 3 * x_sqr.d1 - 2 * slope_y.d1,
    d2 := 3 * x_sqr.d2 - 2 * slope_y.d2
  } range_check_ptr₂ ∧
  κ₁ + κ₂ + κ₃ + κ₄ + 35 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₂ ∧
  ρ_slope = slope

/- compute_doubling_slope soundness theorem -/

def BOUND' : ℤ := 2^76 + 2^58

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_compute_doubling_slope
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem)
    (h_auto : auto_spec_compute_doubling_slope mem κ range_check_ptr point ρ_range_check_ptr ρ_slope) :
  spec_compute_doubling_slope mem κ range_check_ptr point ρ_range_check_ptr ρ_slope :=
begin
  rcases h_auto with ⟨_, _, slope, valid_slope, _, x_sqr, hx, _, slope_y, hslope_y, _, _, vz, _, _, ret1eq⟩,
  rcases nondet_bigint3_corr valid_slope with ⟨is, slopeeq, isbdd⟩,
  intros ix iy ixbdd iybdd ptxeq ptyeq,
  have x_sqr_eq := hx _ ptxeq,
  have slope_y_eq := hslope_y _ _ slopeeq ptyeq,
  refine ⟨_, isbdd, ret1eq.trans slopeeq, _⟩,
  set diff : bigint3 := ((ix.sqr.cmul 3).add ⟨ALPHA, 0, 0⟩).sub ((iy.mul is).cmul 2) with diff_eq,
  have diff_bdd : diff.bounded (3 * (D2_BOUND^2 * BOUND') + 3 + 2 * (D2_BOUND^2 * BOUND')),
  { rw [diff_eq],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_add,
    apply bigint3.bounded_cmul' (show (0 : ℤ) ≤ 3, by norm_num1),
    apply bigint3.bounded_sqr ixbdd,
    { simp [bigint3.bounded], rw [abs_of_nonneg]; norm_num },
    apply bigint3.bounded_cmul' (show (0 : ℤ) ≤ 2, by norm_num1),
    apply bigint3.bounded_mul iybdd isbdd },
  have : diff.val % secp_p = 0,
  { apply vz,
    { simp only [diff_eq, x_sqr_eq, slope_y_eq],
      dsimp only [bigint3.toUnreducedBigInt3, bigint3.sqr, bigint3.add, bigint3.mul, bigint3.cmul, bigint3.sub],
      simp_int_casts,
      split, ring,
      split, ring, ring },
    apply bigint3.bounded_of_bounded_of_le diff_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  symmetry,
  rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←this, diff_eq, bigint3.sub_val],
  rw [bigint3.add_val, bigint3.cmul_val, bigint3.cmul_val],
  apply int.modeq.sub,
  apply int.modeq.add,
  apply int.modeq.mul_left,
  apply int.modeq.symm,
  apply bigint3.sqr_val,
  { simp only [bigint3.val, zero_mul, zero_add] },
  rw mul_assoc,
  apply int.modeq.mul_left,
  apply int.modeq.symm,
  apply bigint3.mul_val
end

/-
-- Function: compute_slope
-/

-- You may change anything in this definition except the name and arguments.
def spec_compute_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∀ ix0 iy0 ix1 iy1 : bigint3,
    ix0.bounded' D2_BOUND →
    iy0.bounded' D2_BOUND →
    ix1.bounded' D2_BOUND →
    iy1.bounded' D2_BOUND →
    point0.x = ix0.toBigInt3 →
    point0.y = iy0.toBigInt3 →
    point1.x = ix1.toBigInt3 →
    point1.y = iy1.toBigInt3 →
    ∃ is : bigint3,
      is.bounded' D2_BOUND ∧
      ρ_slope = is.toBigInt3 ∧
      (ix0.val - ix1.val) * is.val ≡ (iy0.val - iy1.val) [ZMOD secp_p]

/- compute_slope autogenerated specification -/

-- Do not change this definition.
def auto_spec_compute_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (slope : BigInt3 mem), spec_nondet_bigint3 mem κ₁ range_check_ptr range_check_ptr₁ slope ∧
  ∃ x_diff : BigInt3 mem, x_diff = {
    d0 := point0.x.d0 - point1.x.d0,
    d1 := point0.x.d1 - point1.x.d1,
    d2 := point0.x.d2 - point1.x.d2
  } ∧
  ∃ (κ₂ : ℕ) (x_diff_slope : UnreducedBigInt3 mem), spec_unreduced_mul mem κ₂ x_diff slope x_diff_slope ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₂ : F), spec_verify_zero mem κ₃ range_check_ptr₁ {
    d0 := x_diff_slope.d0 - point0.y.d0 + point1.y.d0,
    d1 := x_diff_slope.d1 - point0.y.d1 + point1.y.d1,
    d2 := x_diff_slope.d2 - point0.y.d2 + point1.y.d2
  } range_check_ptr₂ ∧
  κ₁ + κ₂ + κ₃ + 21 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₂ ∧
  ρ_slope = slope

/- compute_slope soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_compute_slope
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem)
    (h_auto : auto_spec_compute_slope mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_slope) :
  spec_compute_slope mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_slope :=
begin
  rcases h_auto with ⟨_, _, slope, valid_slope, x_diff, x_diff_eq,
    _, x_diff_slope, h_x_diff_slope, _, _, vz, _, _, ret1eq⟩,
  rcases nondet_bigint3_corr valid_slope with ⟨is, slope_eq, isbdd⟩,
  intros ix0 iy0 ix1 iy1 ix0bdd iy0bdd ix1bdd iy1bdd pt0xeq pt0yeq pt1xeq pt1yeq,
  set ix_diff := ix0.sub ix1 with ix_diff_eq,
  have x_diff_eq' : x_diff = ix_diff.toBigInt3,
  { rw [ix_diff_eq, x_diff_eq, bigint3.toBigInt3_sub, BigInt3.sub, pt0xeq, pt1xeq] },
  have x_diff_slope_eq := h_x_diff_slope _ _ x_diff_eq' slope_eq,
  refine ⟨_, isbdd, ret1eq.trans slope_eq, _⟩,
  set diff : bigint3 := (ix_diff.mul is).sub (iy0.sub iy1) with diff_eq,
  have diff_bdd : diff.bounded
    ((D2_BOUND + D2_BOUND)^2 * BOUND' +  8 * (D2_BOUND + D2_BOUND)),
  { rw [diff_eq],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_mul,
    apply bigint3.bounded'_sub ix0bdd ix1bdd,
    apply bigint3.bounded'_of_bounded'_of_le isbdd,
    apply le_add_of_sub_left_le, rw [sub_self, D2_BOUND], simp_int_casts, norm_num1,
    apply bigint3.bounded_of_bounded',
    apply bigint3.bounded'_sub iy0bdd iy1bdd },
  have : diff.val % secp_p = 0,
  { apply vz,
    { simp only [diff_eq, x_diff_slope_eq, ix_diff_eq, pt0xeq, pt1xeq, pt0yeq, pt1yeq],
      dsimp [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, bigint3.mul, bigint3.sub],
      simp [←sub_add] },
    apply bigint3.bounded_of_bounded_of_le diff_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  symmetry,
  rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←this, diff_eq, bigint3.sub_val,
       bigint3.sub_val],
  apply int.modeq.sub,
  apply int.modeq.symm,
  apply int.modeq.trans,
  apply bigint3.mul_val,
  apply int.modeq.mul_right,
  rw [ix_diff_eq, bigint3.sub_val],
  apply int.modeq.refl
end

-- You may change anything in this definition except the name and arguments.
def spec_ec_double (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  (point.x = ⟨0, 0, 0⟩ ∧ ρ_res = point) ∨
  (point.x ≠ ⟨0, 0, 0⟩ ∧
    ∀ ix iy : bigint3,
    ix.bounded' D2_BOUND →
    iy.bounded' D2_BOUND →
    point.x = ix.toBigInt3 →
    point.y = iy.toBigInt3 →
    ∃ is inew_x inew_y : bigint3,
      is.bounded' D2_BOUND ∧
      inew_x.bounded' D2_BOUND ∧
      inew_y.bounded' D2_BOUND ∧
      ρ_res = { x := inew_x.toBigInt3, y := inew_y.toBigInt3 } ∧
      3 * ix.val^2 + ALPHA ≡ 2 * iy.val * is.val [ZMOD secp_p] ∧
      inew_x.val ≡ is.val^2 - 2 * ix.val [ZMOD secp_p] ∧
      inew_y.val ≡ (ix.val - inew_x.val) * is.val - iy.val [ZMOD secp_p])

/- ec_double block 5 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_ec_double_block5 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (slope : BigInt3 mem), spec_compute_doubling_slope mem κ₁ range_check_ptr point range_check_ptr₁ slope ∧
  ∃ (κ₂ : ℕ) (slope_sqr : UnreducedBigInt3 mem), spec_unreduced_sqr mem κ₂ slope slope_sqr ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₂ : F) (new_x : BigInt3 mem), spec_nondet_bigint3 mem κ₃ range_check_ptr₁ range_check_ptr₂ new_x ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₃ : F) (new_y : BigInt3 mem), spec_nondet_bigint3 mem κ₄ range_check_ptr₂ range_check_ptr₃ new_y ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₄ : F), spec_verify_zero mem κ₅ range_check_ptr₃ {
    d0 := slope_sqr.d0 - new_x.d0 - 2 * point.x.d0,
    d1 := slope_sqr.d1 - new_x.d1 - 2 * point.x.d1,
    d2 := slope_sqr.d2 - new_x.d2 - 2 * point.x.d2
  } range_check_ptr₄ ∧
  ∃ (κ₆ : ℕ) (x_diff_slope : UnreducedBigInt3 mem), spec_unreduced_mul mem κ₆ {
    d0 := point.x.d0 - new_x.d0,
    d1 := point.x.d1 - new_x.d1,
    d2 := point.x.d2 - new_x.d2
  } slope x_diff_slope ∧
  ∃ (κ₇ : ℕ) (range_check_ptr₅ : F), spec_verify_zero mem κ₇ range_check_ptr₄ {
    d0 := x_diff_slope.d0 - point.y.d0 - new_y.d0,
    d1 := x_diff_slope.d1 - point.y.d1 - new_y.d1,
    d2 := x_diff_slope.d2 - point.y.d2 - new_y.d2
  } range_check_ptr₅ ∧
  κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + 49 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₅ ∧
  ρ_res = {
    x := new_x,
    y := new_y
  }

/-
-- Function: ec_double
-/

/- ec_double autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_double (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ((point.x.d0 = 0 ∧
    ((point.x.d1 = 0 ∧
      ((point.x.d2 = 0 ∧
        11 ≤ κ ∧
        ρ_range_check_ptr = range_check_ptr ∧
        ρ_res = point) ∨
       (point.x.d2 ≠ 0 ∧
        ∃ (κ₁ : ℕ), auto_spec_ec_double_block5 mem κ₁ range_check_ptr point ρ_range_check_ptr ρ_res ∧
        κ₁ + 3 ≤ κ))) ∨
     (point.x.d1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_ec_double_block5 mem κ₁ range_check_ptr point ρ_range_check_ptr ρ_res ∧
      κ₁ + 2 ≤ κ))) ∨
   (point.x.d0 ≠ 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_ec_double_block5 mem κ₁ range_check_ptr point ρ_range_check_ptr ρ_res ∧
    κ₁ + 1 ≤ κ))

-- Added manually
theorem auto_spec_ec_double_better {mem : F → F} {κ : ℕ}{range_check_ptr : F} {point : EcPoint mem} {ρ_range_check_ptr : F} {ρ_res : EcPoint mem} (h : auto_spec_ec_double mem κ range_check_ptr point ρ_range_check_ptr ρ_res ) :
  (point.x.d0 = 0 ∧ point.x.d1 = 0 ∧ point.x.d2 = 0 ∧
      ρ_range_check_ptr = range_check_ptr ∧ ρ_res = point) ∨
  ((point.x.d2 ≠ 0 ∨ point.x.d1 ≠ 0 ∨ point.x.d0 ≠ 0) ∧
    ∃ (κ₁ : ℕ), auto_spec_ec_double_block5 mem κ₁ range_check_ptr point ρ_range_check_ptr ρ_res) :=
begin
  rcases h with (⟨ptx0z, (⟨ptx1z, ⟨ptx2z, h2⟩ | ⟨ptx2nz, ⟨h31, h32, _⟩⟩⟩ | ⟨ptx1nz, ⟨h41, h42, _⟩⟩)⟩ | ⟨ptx0nz, ⟨h51, h52, _⟩⟩),
  { left, use [ptx0z, ptx1z, ptx2z, h2.2] },
  { right, split, left, assumption, exact ⟨h31, h32⟩ },
  { right, split, right, left, assumption, exact ⟨h41, h42⟩ },
  right, split, right, right, assumption, exact ⟨h51, h52⟩,
end

/- ec_double soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_double
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem)
    (h_auto : auto_spec_ec_double mem κ range_check_ptr point ρ_range_check_ptr ρ_res) :
  spec_ec_double mem κ range_check_ptr point ρ_range_check_ptr ρ_res :=
begin
  rcases auto_spec_ec_double_better h_auto with
    ⟨ptx0z, ptx1z, ptx2z, _, reseq⟩ | ⟨nz, _, main_case⟩,
  { left, simp [BigInt3.ext_iff, ptx0z, ptx1z, ptx2z, reseq] },
  rcases main_case with ⟨_, _, slope, h_doubling_slope,
    _, islope_sqr, h_slope_square,
    _, _, new_x, vv_new_x, _, _, new_y, vv_new_y, _, _, vz,
    _, x_diff_slope, h_x_diff_slope,
    _, _, vz', _, _, ret1_eq⟩,
  right, split,
  { simp [BigInt3.ext_iff], tauto },
  intros ix iy ixbdd iybdd ptxeq ptyeq,
  rcases h_doubling_slope ix iy ixbdd iybdd ptxeq ptyeq with ⟨is, isbdd, slope_eq, slope_congr⟩,
  have islope_sqr_eq := h_slope_square _ slope_eq,
  rcases nondet_bigint3_corr vv_new_x with ⟨inew_x, inew_x_eq, inew_x_bdd⟩,
  rcases nondet_bigint3_corr vv_new_y with ⟨inew_y, inew_y_eq, inew_y_bdd⟩,
  set diff1 := ((is.mul is).sub inew_x).sub (ix.cmul 2) with diff1_eq,
  have diff1_bdd : diff1.bounded (D2_BOUND^2 * BOUND' + 8 * D2_BOUND + 2 * (8 * D2_BOUND)),
  { rw [diff1_eq],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_sub,
    apply bigint3.bounded_mul isbdd isbdd,
    apply bigint3.bounded_of_bounded' inew_x_bdd,
    apply bigint3.bounded_cmul,
    apply bigint3.bounded_of_bounded' ixbdd },
  have diff1_equiv : diff1.val % secp_p = 0,
  { apply vz,
    { simp only [diff1_eq, islope_sqr_eq, ptxeq, inew_x_eq],
      dsimp [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, bigint3.mul, bigint3.sub, bigint3.cmul,
        bigint3.sqr],
      simp only [int.cast_sub, int.cast_mul 2], simp_int_casts,
      split, refl, split, refl, refl
      },
    apply bigint3.bounded_of_bounded_of_le diff1_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  have : (ix.sub inew_x).toBigInt3 =
    { d0 := point.x.d0 - new_x.d0, d1 := point.x.d1 - new_x.d1, d2 := point.x.d2 - new_x.d2 },
  { rw [bigint3.toBigInt3_sub, ←ptxeq, ←inew_x_eq], refl },
  have x_diff_slope_eq := h_x_diff_slope _ _ this.symm slope_eq,
  set diff2 := (((ix.sub inew_x).mul is).sub iy).sub inew_y with diff2_eq,
  have diff2_bdd : diff2.bounded ((D2_BOUND + D2_BOUND)^2 * BOUND' + 8 * D2_BOUND + 8 * D2_BOUND),
  { rw [diff2_eq],
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' inew_y_bdd),
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' iybdd),
    apply bigint3.bounded_mul,
    apply bigint3.bounded'_sub ixbdd inew_x_bdd,
    apply bigint3.bounded'_of_bounded'_of_le isbdd,
    apply le_add_of_nonneg_left,
    dsimp only [D2_BOUND], simp_int_casts, norm_num1 },
  have diff2_equiv : diff2.val % secp_p = 0,
  { apply vz',
    { simp only [diff2_eq, x_diff_slope_eq, inew_y_eq, bigint3.toBigInt3,
        bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, ptyeq, int.cast_sub],
        split, refl, split, refl, split },
    apply bigint3.bounded_of_bounded_of_le diff2_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  use [is, inew_x, inew_y, isbdd, inew_x_bdd, inew_y_bdd],
  split, rw [ret1_eq, inew_x_eq, inew_y_eq],
  use slope_congr,
  split,
  { rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←diff1_equiv, diff1_eq, bigint3.sub_val,
      bigint3.sub_val, bigint3.cmul_val, sub_sub, add_comm, ←sub_sub, pow_two],
    apply int.modeq.sub_right,
    apply int.modeq.sub_right,
    symmetry,
    apply bigint3.mul_val },
  rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←diff2_equiv, diff2_eq, bigint3.sub_val,
       bigint3.sub_val],
  apply int.modeq.sub_right,
  apply int.modeq.sub_right,
  symmetry,
  transitivity,
  apply bigint3.mul_val,
  rw [bigint3.sub_val]
end

/- Better specification -/

def spec_ec_double' {mem : F → F} ( pt : EcPoint mem ) ( ret1 : EcPoint mem )
    (secpF : Type) [secp_field secpF] : Prop :=
  ∀ h : BddECPointData secpF pt,
    ∃ hret : BddECPointData secpF ret1,
      hret.toECPoint = 2 • h.toECPoint

theorem spec_ec_double'_of_spec_ec_double
    {mem : F → F} {κ : ℕ} {range_check_ptr : F} {pt : EcPoint mem} {ret0 : F} {ret1 : EcPoint mem}
    (h : spec_ec_double mem κ range_check_ptr pt ret0 ret1)
    (secpF : Type) [secp_field secpF] :
  spec_ec_double' pt ret1 secpF :=
begin
  intros hpt,
  rcases h with ⟨ptx0, reteq⟩ | ⟨ptxnz, h⟩,
  { rw reteq, use hpt,
    rw [hpt.toECPoint_eq_zero_iff.mpr ptx0, smul_zero] },
  rcases h hpt.ix hpt.iy hpt.ixbdd hpt.iybdd hpt.ptxeq hpt.ptyeq with
    ⟨is, inew_x, inew_y, is_bdd, inew_x_bdd, inew_y_bdd, ret1eq, mod1eq, mod2eq, mod3eq⟩,
  have onec_pt := hpt.onEC' ptxnz,
  have hptynez : (hpt.iy.val : secpF) ≠ 0 := secp_field.y_ne_zero_of_on_ec onec_pt,
  have eq1 : 3 * (hpt.ix.val : secpF)^2 + ALPHA = 2 * hpt.iy.val * is.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod1eq },
  have eq2 : (inew_x.val : secpF) = is.val ^ 2 - 2 * hpt.ix.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod2eq },
  have eq3: (inew_y.val : secpF) = (hpt.ix.val - inew_x.val) * is.val - hpt.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod3eq },
  have eq1a : (is.val : secpF) = (3 * (hpt.ix.val : secpF)^2 + ALPHA) / (2 * hpt.iy.val),
  { field_simp [ec_field.two_ne_zero], simp [ALPHA] at eq1, rw [mul_comm, eq1] },
  have ecdoubleeq : ec_double ((hpt.ix.val : secpF), hpt.iy.val) = (inew_x.val, inew_y.val),
  { simp [ec_double, ec_double_slope],
    simp [ALPHA] at eq1 eq1a,
    split, rw [eq2, eq1a, div_pow],
    rw [eq3, eq1a], congr, rw [eq2, eq1a, div_pow] },
  have onec_new: on_ec (↑(inew_x.val), ↑(inew_y.val)),
  { have := @on_ec_ec_double secpF _ (↑(hpt.ix.val), ↑(hpt.iy.val)) onec_pt hptynez,
    rw ecdoubleeq at this, exact this },
  have hhret: ¬ (inew_x.i0 = 0 ∧ inew_x.i1 = 0 ∧ inew_x.i2 = 0),
  { contrapose! onec_new,
    rw [on_ec], dsimp,
    conv { congr, to_rhs, simp [bigint3.val, onec_new.1, onec_new.2.1, onec_new.2.2] },
    apply secp_field.BETA_not_square },
  let hret : BddECPointData secpF ret1 :=
  { ix    := inew_x,
    iy    := inew_y,
    ixbdd := inew_x_bdd,
    iybdd := inew_y_bdd,
    ptxeq := by { rw ret1eq },
    ptyeq := by { rw ret1eq },
    onEC  := or.inr onec_new },
  use hret,
  have : ret1.x ≠ ⟨0, 0, 0⟩,
  { rw [ret1eq], dsimp,
    have h' := secp_field.x_ne_zero_of_on_ec onec_new,
    contrapose! h',
    have : inew_x = ⟨0, 0, 0⟩ :=
      toBigInt3_eq_zero_of_bounded_8D2BOUND h' (bigint3.bounded_of_bounded' inew_x_bdd),
    simp [this, bigint3.val] },
  dsimp [BddECPointData.toECPoint], simp [dif_neg ptxnz, dif_neg this],
  symmetry,
  apply double_Affine _ _ ecdoubleeq
end


/-
-- Function: fast_ec_add
-/

-- You may change anything in this definition except the name and arguments.
def spec_fast_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ ix0 iy0 ix1 iy1 : bigint3,
  ix0.bounded' D2_BOUND →
  iy0.bounded' D2_BOUND →
  ix1.bounded' D2_BOUND →
  iy1.bounded' D2_BOUND →
  point0.x = ix0.toBigInt3 →
  point0.y = iy0.toBigInt3 →
  point1.x = ix1.toBigInt3 →
  point1.y = iy1.toBigInt3 →
  (point0.x.d0 = 0 ∧ point0.x.d1 = 0 ∧ point0.x.d2 = 0 ∧ ρ_res = point1) ∨
  (point1.x.d0 = 0 ∧ point1.x.d1 = 0 ∧ point1.x.d2 = 0 ∧ ρ_res = point0) ∨
  ¬ (point0.x.d0 = 0 ∧ point0.x.d1 = 0 ∧ point0.x.d2 = 0) ∧
  ¬ (point1.x.d0 = 0 ∧ point1.x.d1 = 0 ∧ point1.x.d2 = 0) ∧
  ∃ is inew_x inew_y : bigint3,
    is.bounded' D2_BOUND ∧
    inew_x.bounded' D2_BOUND ∧
    inew_y.bounded' D2_BOUND ∧
    ρ_res = { x := inew_x.toBigInt3, y := inew_y.toBigInt3 } ∧
    (ix0.val - ix1.val) * is.val ≡ (iy0.val - iy1.val) [ZMOD secp_p] ∧
    inew_x.val ≡ is.val^2 - ix0.val - ix1.val [ZMOD secp_p] ∧
    inew_y.val ≡ (ix0.val - inew_x.val) * is.val - iy0.val [ZMOD secp_p]

/- fast_ec_add block 9 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_fast_ec_add_block9 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (slope : BigInt3 mem), spec_compute_slope mem κ₁ range_check_ptr point0 point1 range_check_ptr₁ slope ∧
  ∃ (κ₂ : ℕ) (slope_sqr : UnreducedBigInt3 mem), spec_unreduced_sqr mem κ₂ slope slope_sqr ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₂ : F) (new_x : BigInt3 mem), spec_nondet_bigint3 mem κ₃ range_check_ptr₁ range_check_ptr₂ new_x ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₃ : F) (new_y : BigInt3 mem), spec_nondet_bigint3 mem κ₄ range_check_ptr₂ range_check_ptr₃ new_y ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₄ : F), spec_verify_zero mem κ₅ range_check_ptr₃ {
    d0 := slope_sqr.d0 - new_x.d0 - point0.x.d0 - point1.x.d0,
    d1 := slope_sqr.d1 - new_x.d1 - point0.x.d1 - point1.x.d1,
    d2 := slope_sqr.d2 - new_x.d2 - point0.x.d2 - point1.x.d2
  } range_check_ptr₄ ∧
  ∃ (κ₆ : ℕ) (x_diff_slope : UnreducedBigInt3 mem), spec_unreduced_mul mem κ₆ {
    d0 := point0.x.d0 - new_x.d0,
    d1 := point0.x.d1 - new_x.d1,
    d2 := point0.x.d2 - new_x.d2
  } slope x_diff_slope ∧
  ∃ (κ₇ : ℕ) (range_check_ptr₅ : F), spec_verify_zero mem κ₇ range_check_ptr₄ {
    d0 := x_diff_slope.d0 - point0.y.d0 - new_y.d0,
    d1 := x_diff_slope.d1 - point0.y.d1 - new_y.d1,
    d2 := x_diff_slope.d2 - point0.y.d2 - new_y.d2
  } range_check_ptr₅ ∧
  κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + 52 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₅ ∧
  ρ_res = {
    x := new_x,
    y := new_y
  }

/- fast_ec_add block 5 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_fast_ec_add_block5 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ((point1.x.d0 = 0 ∧
    ((point1.x.d1 = 0 ∧
      ((point1.x.d2 = 0 ∧
        11 ≤ κ ∧
        ρ_range_check_ptr = range_check_ptr ∧
        ρ_res = point0) ∨
       (point1.x.d2 ≠ 0 ∧
        ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block9 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
        κ₁ + 3 ≤ κ))) ∨
     (point1.x.d1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block9 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
      κ₁ + 2 ≤ κ))) ∨
   (point1.x.d0 ≠ 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block9 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
    κ₁ + 1 ≤ κ))

/- fast_ec_add autogenerated specification -/

-- Do not change this definition.
def auto_spec_fast_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ((point0.x.d0 = 0 ∧
    ((point0.x.d1 = 0 ∧
      ((point0.x.d2 = 0 ∧
        11 ≤ κ ∧
        ρ_range_check_ptr = range_check_ptr ∧
        ρ_res = point1) ∨
       (point0.x.d2 ≠ 0 ∧
        ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block5 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
        κ₁ + 3 ≤ κ))) ∨
     (point0.x.d1 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block5 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
      κ₁ + 2 ≤ κ))) ∨
   (point0.x.d0 ≠ 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_fast_ec_add_block5 mem κ₁ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res ∧
    κ₁ + 1 ≤ κ))

/- fast_ec_add soundness theorem -/

theorem fast_ec_add_block5_spec_better {mem : F → F} {κ : ℕ}{range_check_ptr : F} {pt0 pt1 : EcPoint mem} {ret0 : F} {ret1 : EcPoint mem}
    (h_auto : auto_spec_fast_ec_add_block5 mem κ range_check_ptr pt0 pt1 ret0 ret1) :
  (pt1.x.d0 = 0 ∧ pt1.x.d1 = 0 ∧ pt1.x.d2 = 0 ∧
    ret0 = range_check_ptr ∧ ret1 = pt0) ∨
  (¬ (pt1.x.d0 = 0 ∧ pt1.x.d1 = 0 ∧ pt1.x.d2 = 0) ∧
  ∃ κ₁, auto_spec_fast_ec_add_block9 mem κ₁ range_check_ptr pt0 pt1 ret0 ret1) :=
begin
  rcases h_auto with
    ⟨pt1x0z, ⟨pt1x1z, ⟨pt1x2z, ⟨_, ret0, ret1⟩⟩ | ⟨pt1x2nz, ⟨κ₁, hblock9⟩⟩⟩ |
      ⟨pt1x1nz, ⟨κ₁, hblock9⟩⟩⟩ | ⟨pt1x0nz, ⟨κ₁, hblock9⟩⟩,
  { left, use [pt1x0z, pt1x1z, pt1x2z, ret0, ret1] },
  { right, split, intro h, apply pt1x2nz h.2.2,
    exact ⟨κ₁, hblock9.1⟩ },
  { right, split, intro h, apply pt1x1nz h.2.1,
    exact ⟨κ₁, hblock9.1⟩ },
  { right, split, intro h, apply pt1x0nz h.1,
    exact ⟨κ₁, hblock9.1⟩ }
end

theorem ec_add_mainb_spec_better {mem : F → F} {κ : ℕ} {range_check_ptr : F} {pt0 pt1 : EcPoint mem} {ret0 : F} {ret1 : EcPoint mem}
    (h_auto : auto_spec_fast_ec_add mem κ range_check_ptr pt0 pt1 ret0 ret1) :
  (pt0.x.d0 = 0 ∧ pt0.x.d1 = 0 ∧ pt0.x.d2 = 0 ∧
    ret0 = range_check_ptr ∧ ret1 = pt1) ∨
  (pt1.x.d0 = 0 ∧ pt1.x.d1 = 0 ∧ pt1.x.d2 = 0 ∧
    ret0 = range_check_ptr ∧ ret1 = pt0) ∨
  (¬(pt0.x.d0 = 0 ∧ pt0.x.d1 = 0 ∧ pt0.x.d2 = 0) ∧
    ¬ (pt1.x.d0 = 0 ∧ pt1.x.d1 = 0 ∧ pt1.x.d2 = 0) ∧
    ∃ κ₁, auto_spec_fast_ec_add_block9 mem κ₁ range_check_ptr pt0 pt1 ret0 ret1) :=
begin
  rcases h_auto with
    ⟨pt1x0z, ⟨pt1x1z, ⟨pt1x2z, ⟨_, ret0, ret1⟩⟩ | ⟨pt1x2nz, κ₁, hblock9⟩⟩ |
      ⟨pt1x1nz, κ₁, hblock9⟩⟩ | ⟨pt1x0nz, κ₁, hblock9⟩,
  { left, use [pt1x0z, pt1x1z, pt1x2z, ret0, ret1] },
  { right,
    cases fast_ec_add_block5_spec_better hblock9.1 with h' h',
    { left, exact h' },
    right, split,
    { intro h, exact pt1x2nz h.2.2 },
    exact h' },
  { right,
    cases fast_ec_add_block5_spec_better hblock9.1 with h' h',
    { left, exact h' },
    right, split,
    { intro h, exact pt1x1nz h.2.1 },
    exact h' },
  { right,
    cases fast_ec_add_block5_spec_better hblock9.1 with h' h',
    { left, exact h' },
    right, split,
    { intro h, exact pt1x0nz h.1 },
    exact h' },
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_fast_ec_add
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem)
    (h_auto : auto_spec_fast_ec_add mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res) :
  spec_fast_ec_add mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res :=
begin
  intros ix0 iy0 ix1 iy1 ix0bdd iy0bdd ix1bdd iy1bdd pt0xeq pt0yeq pt1xeq pt1yeq,
  rcases ec_add_mainb_spec_better h_auto with
    ⟨pt0x0z, pt0x1z, pt0x2z, _, ret1eq⟩ |
    ⟨pt1x0z, pt1x1z, pt1x2z, _, ret1eq⟩ |
      ⟨pt0nz, pt1nz, _, _, _, slope, h_compute_slope,
        _, islope_sqr, h_slope_sqr,
        _, _, new_x, vv_new_x, _, _, new_y, vv_new_y, _, _, vz,
        _, x_diff_slope, h_x_diff_slope,
        _, _, vz', _, _, ret1_eq⟩,
  { left, use [pt0x0z, pt0x1z, pt0x2z, ret1eq] },
  { right, left, use [pt1x0z, pt1x1z, pt1x2z, ret1eq] },
  rcases h_compute_slope ix0 iy0 ix1 iy1 ix0bdd iy0bdd ix1bdd iy1bdd pt0xeq pt0yeq pt1xeq pt1yeq
    with ⟨is, isbdd, slope_eq, slope_congr⟩,
  have islope_sqr_eq := h_slope_sqr _ slope_eq,
  rcases nondet_bigint3_corr vv_new_x with ⟨inew_x, inew_x_eq, inew_x_bdd⟩,
  rcases nondet_bigint3_corr vv_new_y with ⟨inew_y, inew_y_eq, inew_y_bdd⟩,
  set diff1 := (((is.mul is).sub inew_x).sub ix0).sub ix1 with diff1_eq,
  have diff1_bdd : diff1.bounded
    (D2_BOUND^2 * BOUND' + 8 * D2_BOUND + 8 * D2_BOUND + 8 * D2_BOUND),
  { rw [diff1_eq],
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' ix1bdd),
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' ix0bdd),
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' inew_x_bdd),
    apply bigint3.bounded_mul isbdd isbdd },
  have diff1_equiv : diff1.val % secp_p = 0,
  { apply vz,
    { simp only [diff1_eq, islope_sqr_eq, pt0xeq, pt1xeq, inew_x_eq],
      dsimp [bigint3.toBigInt3, bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, bigint3.cmul,
        bigint3.sqr],
      simp only [int.cast_sub, int.cast_mul 2], simp_int_casts,
      split, refl, split, refl, refl },
    apply bigint3.bounded_of_bounded_of_le diff1_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  have : (ix0.sub inew_x).toBigInt3 =
    { d0 := point0.x.d0 - new_x.d0, d1 := point0.x.d1 - new_x.d1, d2 := point0.x.d2 - new_x.d2 },
  { rw [bigint3.toBigInt3_sub, ←pt0xeq, ←inew_x_eq], refl },
  have x_diff_slope_eq := h_x_diff_slope _ _ this.symm slope_eq,
  set diff2 := (((ix0.sub inew_x).mul is).sub iy0).sub inew_y with diff2_eq,
  have diff2_bdd : diff2.bounded
    ((D2_BOUND + D2_BOUND)^2 * BOUND' + 8 * D2_BOUND + 8 * D2_BOUND),
  { rw [diff2_eq],
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' inew_y_bdd),
    apply bigint3.bounded_sub _ (bigint3.bounded_of_bounded' iy0bdd),
    apply bigint3.bounded_mul,
    apply bigint3.bounded'_sub ix0bdd inew_x_bdd,
    apply bigint3.bounded'_of_bounded'_of_le isbdd,
    apply le_add_of_nonneg_left,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  have diff2_equiv : diff2.val % secp_p = 0,
  { apply vz',
    { simp only [diff2_eq, x_diff_slope_eq, inew_y_eq, bigint3.toBigInt3,
        bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, pt0yeq, int.cast_sub],
        split, refl, split, refl, split },
    apply bigint3.bounded_of_bounded_of_le diff2_bdd,
    dsimp only [D2_BOUND, BOUND'], simp_int_casts, norm_num1 },
  right, right,
  use [pt0nz, pt1nz, is, inew_x, inew_y, isbdd, inew_x_bdd, inew_y_bdd],
  split, rw [ret1_eq, inew_x_eq, inew_y_eq],
  use slope_congr,
  split,
  { rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←diff1_equiv, diff1_eq, bigint3.sub_val,
      bigint3.sub_val, bigint3.sub_val, sub_sub, sub_sub, pow_two, ←add_assoc,
      add_comm _ inew_x.val, sub_sub, ←sub_sub],
    apply int.modeq.sub_right,
    apply int.modeq.sub_right,
    symmetry,
    apply bigint3.mul_val },
  rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←diff2_equiv, diff2_eq, bigint3.sub_val,
       bigint3.sub_val],
  apply int.modeq.sub_right,
  apply int.modeq.sub_right,
  symmetry,
  transitivity,
  apply bigint3.mul_val,
  rw [bigint3.sub_val]
end

/-
Better specification of fast_ec_add
-/

def spec_fast_ec_add' {mem : F → F} ( pt0 pt1 : EcPoint mem ) ( ret1 : EcPoint mem )
    (secpF : Type) [secp_field secpF] : Prop :=
  ∀ h0 : BddECPointData secpF pt0,
  ∀ h1 : BddECPointData secpF pt1,
    ((↑(h0.ix.val) : secpF) ≠ ↑(h1.ix.val) ∨ h0.toECPoint = 0 ∨ h1.toECPoint = 0) →
    ∃ hret : BddECPointData secpF ret1,
      hret.toECPoint = h0.toECPoint + h1.toECPoint

lemma D2_BOUND_lt_PRIME : (D2_BOUND : ℤ) < PRIME :=
by { rw [D2_BOUND, PRIME], simp_int_casts, norm_num1 }

lemma D2_BOUND8_lt_PRIME : 8 * (D2_BOUND : ℤ) < PRIME :=
by { rw [D2_BOUND, PRIME], simp_int_casts, norm_num1 }

theorem spec_fast_ec_add'_of_spec_fast_ec_add
    {mem : F → F} {κ : ℕ} {range_check_ptr : F} {pt0 pt1 : EcPoint mem} {ret0 : F} {ret1 : EcPoint mem}
    (h : spec_fast_ec_add mem κ range_check_ptr pt0 pt1 ret0 ret1)
    (secpF : Type) [secp_field secpF] :
  spec_fast_ec_add' pt0 pt1 ret1 secpF :=
begin
  intros h0 h1 hne,
  rcases h h0.ix h0.iy h1.ix h1.iy h0.ixbdd h0.iybdd h1.ixbdd h1.iybdd h0.ptxeq h0.ptyeq h1.ptxeq h1.ptyeq with
    h' | h' | h',
  { rcases h' with ⟨pt0x0eq, pt0x1eq, pt0x2eq, rfl⟩,
    have pt0xz : pt0.x = ⟨0, 0, 0⟩,
    { simp [BigInt3.ext_iff, pt0x0eq, pt0x1eq, pt0x2eq] },
    use h1,
    have pt0xeq := h0.ptxeq,
    simp [BigInt3.ext_iff, bigint3.toBigInt3] at pt0xeq,
    have ix0i0z: h0.ix.i0 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt0xeq.1, pt0x0eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h0.ixbdd.1,
      apply D2_BOUND8_lt_PRIME },
    have ix0i1z: h0.ix.i1 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt0xeq.2.1, pt0x1eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h0.ixbdd.2.1,
      apply D2_BOUND8_lt_PRIME },
    have ix0i2z: h0.ix.i2 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt0xeq.2.2, pt0x2eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h0.ixbdd.2.2,
      apply D2_BOUND_lt_PRIME },
    simp [BddECPointData.toECPoint, pt0xz], refl },
  { rcases h' with ⟨pt1x0eq, pt1x1eq, pt1x2eq, rfl⟩,
    have pt1xz : pt1.x = ⟨0, 0, 0⟩,
    { simp [BigInt3.ext_iff, pt1x0eq, pt1x1eq, pt1x2eq] },
    use h0,
    have pt1xeq := h1.ptxeq,
    simp [BigInt3.ext_iff, bigint3.toBigInt3] at pt1xeq,
    have ix0i0z: h1.ix.i0 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt1xeq.1, pt1x0eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h1.ixbdd.1,
      apply D2_BOUND8_lt_PRIME },
    have ix0i1z: h1.ix.i1 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt1xeq.2.1, pt1x1eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h1.ixbdd.2.1,
      apply D2_BOUND8_lt_PRIME },
    have ix0i2z: h1.ix.i2 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt1xeq.2.2, pt1x2eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h1.ixbdd.2.2,
      apply D2_BOUND_lt_PRIME },
    simp [BddECPointData.toECPoint, pt1xz], refl },
  rcases h' with ⟨pt0nz, pt1nz, is, inew_x, inew_y, is_bdd, inew_x_bdd, inew_y_bdd, ret1eq, mod1eq, mod2eq, mod3eq⟩,
  have h0ptnz : h0.toECPoint ≠ 0,
  { rw [ne, BddECPointData.toECPoint_eq_zero_iff, BigInt3.ext_iff],
    exact pt0nz },
  have h1ptnz : h1.toECPoint ≠ 0,
  { rw [ne, BddECPointData.toECPoint_eq_zero_iff, BigInt3.ext_iff],
    exact pt1nz },
  rw [←or_assoc] at hne,
  have hne := or.resolve_right (or.resolve_right hne h1ptnz) h0ptnz,
  have eq1 : ((h0.ix.val : secpF) - h1.ix.val) * is.val = h0.iy.val - h1.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod1eq },
  have eq2 : (inew_x.val : secpF) = is.val ^ 2 - h0.ix.val - h1.ix.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod2eq },
  have eq3: (inew_y.val : secpF) = (h0.ix.val - inew_x.val) * is.val - h0.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ secp_p,
    apply mod3eq },
  have nez : (h1.ix.val : secpF) - h0.ix.val ≠ 0,
  { contrapose! hne, symmetry, apply eq_of_sub_eq_zero hne },
  have eq1a : (is.val : secpF) = (h1.iy.val - h0.iy.val) / (h1.ix.val - h0.ix.val),
  { field_simp [nez], rw [←neg_sub, mul_neg, mul_comm, eq1, neg_sub] },
  have ecaddeq : ec_add ((h0.ix.val : secpF), h0.iy.val) ((h1.ix.val : secpF), h1.iy.val) = (inew_x.val, inew_y.val),
  { simp [ec_add, ec_add_slope],
    split, rw [eq2, eq1a, div_pow, sub_sub],
    rw [eq3], congr, rw [eq2, eq1a, div_pow, sub_sub], rw [eq1a] },
  have pt0nz' : pt0.x ≠ ⟨0, 0, 0⟩,
  { rw [ne, BigInt3.ext_iff], exact pt0nz },
  have pt1nz' : pt1.x ≠ ⟨0, 0, 0⟩,
  { rw [ne, BigInt3.ext_iff], exact pt1nz },
  have onec_new: on_ec (↑(inew_x.val), ↑(inew_y.val)),
  { have := @on_ec_ec_add secpF _ (↑(h0.ix.val), ↑(h0.iy.val)) (↑(h1.ix.val), ↑(h1.iy.val))
              (h0.onEC' pt0nz') (h1.onEC' pt1nz') hne,
    rw ecaddeq at this, exact this },
  let hret : BddECPointData secpF ret1 :=
  { ix    := inew_x,
    iy    := inew_y,
    ixbdd := inew_x_bdd,
    iybdd := inew_y_bdd,
    ptxeq := by { rw ret1eq },
    ptyeq := by { rw ret1eq },
    onEC  := or.inr onec_new },
  have hhret : ¬ (ret1.x = ⟨0, 0, 0⟩),
  { simp [ret1eq],
    intro h',
    apply secp_field.x_ne_zero_of_on_ec onec_new,
    suffices : inew_x = ⟨0, 0, 0⟩,
    { rw bigint3.ext_iff at this,
      simp [this, bigint3.val] },
      apply toBigInt3_eq_zero_of_bounded_8D2BOUND h',
      apply bigint3.bounded_of_bounded' inew_x_bdd },
  use hret,
  dsimp [BddECPointData.toECPoint], simp [dif_neg pt0nz', dif_neg pt1nz', dif_neg hhret],
  symmetry,
  apply Affine_add_Affine _ _ _ hne,
  rw [ecaddeq]
end


/-
-- Function: ec_add
-/

-- You may change anything in this definition except the name and arguments.
def spec_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ (secpF : Type) [secp_field secpF], by exactI
  ∀ h0 : BddECPointData secpF point0,
  ∀ h1 : BddECPointData secpF point1,
    ∃ hret : BddECPointData secpF ρ_res,
      hret.toECPoint = h0.toECPoint + h1.toECPoint


/- ec_add autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∃ x_diff : SumBigInt3 mem, x_diff = {
    d0 := point0.x.d0 - point1.x.d0,
    d1 := point0.x.d1 - point1.x.d1,
    d2 := point0.x.d2 - point1.x.d2
  } ∧
  ∃ (κ₁ : ℕ) (range_check_ptr₁ same_x : F), spec_is_zero mem κ₁ range_check_ptr x_diff range_check_ptr₁ same_x ∧
  ((same_x = 0 ∧
    ∃ (κ₂ : ℕ), spec_fast_ec_add mem κ₂ range_check_ptr₁ point0 point1 ρ_range_check_ptr ρ_res ∧
    κ₁ + κ₂ + 21 ≤ κ) ∨
   (same_x ≠ 0 ∧
    ∃ y_sum : SumBigInt3 mem, y_sum = {
      d0 := point0.y.d0 + point1.y.d0,
      d1 := point0.y.d1 + point1.y.d1,
      d2 := point0.y.d2 + point1.y.d2
    } ∧
    ∃ (κ₂ : ℕ) (range_check_ptr₂ opposite_y : F), spec_is_zero mem κ₂ range_check_ptr₁ y_sum range_check_ptr₂ opposite_y ∧
    ((opposite_y ≠ 0 ∧
      ∃ ZERO_POINT : EcPoint mem, ZERO_POINT = {
        x := { d0 := 0, d1 := 0, d2 := 0 },
        y := { d0 := 0, d1 := 0, d2 := 0 }
      } ∧
      κ₁ + κ₂ + 20 ≤ κ ∧
      ρ_range_check_ptr = range_check_ptr₂ ∧
      ρ_res = ZERO_POINT) ∨
     (opposite_y = 0 ∧
      ∃ (κ₃ : ℕ), spec_ec_double mem κ₃ range_check_ptr₂ point0 ρ_range_check_ptr ρ_res ∧
      κ₁ + κ₂ + κ₃ + 21 ≤ κ))))

/- ec_add soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_add
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem)
    (h_auto : auto_spec_ec_add mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res) :
  spec_ec_add mem κ range_check_ptr point0 point1 ρ_range_check_ptr ρ_res :=
begin
  intros secpF _,
  resetI,
  intros h0 h1,
  rcases h_auto with ⟨x_diff, x_diff_eq, _, _, same_x, h_x_diff, h'⟩,
  let ix_diff := h0.ix.sub h1.ix,
  have h2: (SumBigInt3.toBigInt3 x_diff) = ix_diff.toBigInt3,
  { dsimp [ix_diff], rw [x_diff_eq, bigint3.toBigInt3_sub, ←h0.ptxeq, ←h1.ptxeq], refl },
  have h3: ix_diff.bounded' (2 * D2_BOUND),
  { rw two_mul,
    apply bigint3.bounded'_sub h0.ixbdd h1.ixbdd },
  rcases h' with ⟨same_x_z, _, h'⟩ | ⟨same_x_nz, h'⟩,
  { have := h_x_diff _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
    have : ix_diff.val % ↑secp_p ≠ 0,
    { rcases this with ⟨_, rfl⟩ | ⟨_, _⟩,
      norm_num at same_x_z, assumption },
    apply spec_fast_ec_add'_of_spec_fast_ec_add h'.1,
    contrapose! this,
    dsimp [ix_diff], rw [bigint3.sub_val, ←int.modeq_iff_sub_mod_eq_zero,
      ←char_p.int_cast_eq_int_cast secpF],
    exact this.1 },
  have := h_x_diff _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
  have : ix_diff.val % ↑secp_p = 0,
  { rcases this with ⟨_, rfl⟩ | ⟨_, _⟩,
    assumption, norm_num at same_x_nz },
  have h0eqh1: (h0.ix.val : secpF) = h1.ix.val,
  { rw [bigint3.sub_val, ←int.modeq_iff_sub_mod_eq_zero,
       ←char_p.int_cast_eq_int_cast secpF] at this,
     exact this },
  have ptx0iff : point0.x = ⟨0, 0, 0⟩ ↔ point1.x = ⟨0, 0, 0⟩,
  { rw [h1.pt_zero_iff, ←h0eqh1, ←h0.pt_zero_iff] },
  rcases h' with ⟨y_sum, y_sum_eq, _, _, opposite_y, h_opposite_y, h'⟩,
  let iy_sum := h0.iy.add h1.iy,
  have h2: (SumBigInt3.toBigInt3 y_sum) = iy_sum.toBigInt3,
  { dsimp [iy_sum], rw [y_sum_eq, bigint3.toBigInt3_add, ←h0.ptyeq, ←h1.ptyeq], refl },
  have h3: iy_sum.bounded' (2 * D2_BOUND),
  { rw two_mul,
    apply bigint3.bounded'_add h0.iybdd h1.iybdd },
  rcases h' with ⟨opposite_y_nz, h'⟩ | ⟨opposite_y_z, _, h'⟩,
  { rcases h' with ⟨_, rfl, _, _, rfl⟩,
    use BddECPointData.zero,
    rw BddECPointData.toECPoint_zero,
    by_cases hx0: point0.x = ⟨0, 0, 0⟩,
    { have hx1: point1.x = ⟨0, 0, 0⟩ := ptx0iff.mp hx0,
      rw [BddECPointData.toECPoint, dif_pos hx0],
      rw [BddECPointData.toECPoint, dif_pos hx1],
      apply (add_zero _).symm },
    have hx1: point1.x ≠ ⟨0, 0, 0⟩,
    { rwa ptx0iff at hx0 },
    rw [BddECPointData.toECPoint, dif_neg hx0],
    rw [BddECPointData.toECPoint, dif_neg hx1],
    symmetry,
    rw [← eq_neg_iff_add_eq_zero, ECPoint.neg_def, ECPoint.neg],
    dsimp,
    congr,
    exact h0eqh1,
    have := h_opposite_y _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
    have : iy_sum.val % ↑secp_p = 0,
    { rcases this with ⟨_, _⟩ | ⟨_, hh⟩,
      assumption, contradiction },
    rw [bigint3.add_val, ←sub_neg_eq_add, ←int.modeq_iff_sub_mod_eq_zero,
       ←char_p.int_cast_eq_int_cast secpF, int.cast_neg] at this,
    exact this },
  have := h_opposite_y _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
  have h0iyneh1iy : iy_sum.val % ↑secp_p ≠ 0,
  { rcases this with ⟨_, rfl⟩ | ⟨_, _⟩,
    norm_num at opposite_y_z,
    assumption },
  rw [ne, bigint3.add_val, ←sub_neg_eq_add, ←int.modeq_iff_sub_mod_eq_zero,
      ←char_p.int_cast_eq_int_cast secpF, int.cast_neg] at h0iyneh1iy,
  have : h0.toECPoint = h1.toECPoint :=
    BddECPointData.toECPoint_eq_of_eq_of_ne h0eqh1 h0iyneh1iy,
  have : h0.toECPoint + h1.toECPoint = 2 • h0.toECPoint,
  { rw [this, two_smul] },
  rw this,
  exact spec_ec_double'_of_spec_ec_double h'.1 secpF h0
end


/-
-- Function: ec_mul_inner
-/

-- You may change anything in this definition except the name and arguments.
def spec_ec_mul_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_pow2 ρ_res : EcPoint mem) : Prop :=
   ∀ (secpF : Type) [hsecp : secp_field secpF],
   by exactI
      point.x ≠ ⟨0, 0, 0⟩ →
      ∀ hpt : BddECPointData secpF point,
      ∃ nn : ℕ,
        m = ↑nn ∧
        nn < ring_char F ∧
          (nn ≤ 128 →
            ∃ scalarn : ℕ,
              scalar = ↑scalarn ∧
              scalarn < 2^nn ∧
            ∃ hpow2 : BddECPointData secpF ρ_pow2,
              ρ_pow2.x ≠ ⟨0, 0, 0⟩ ∧
              hpow2.toECPoint = 2^nn • hpt.toECPoint ∧
            ∃ hres : BddECPointData secpF ρ_res,
              hres.toECPoint = scalarn • hpt.toECPoint)


/- ec_mul_inner autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_mul_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_pow2 ρ_res : EcPoint mem) : Prop :=
  ((m = 0 ∧
    scalar = 0 ∧
    ∃ ZERO_POINT : EcPoint mem, ZERO_POINT = {
      x := { d0 := 0, d1 := 0, d2 := 0 },
      y := { d0 := 0, d1 := 0, d2 := 0 }
    } ∧
    16 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr ∧
    ρ_pow2 = point ∧
    ρ_res = ZERO_POINT) ∨
   (m ≠ 0 ∧
    ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (double_point : EcPoint mem), spec_ec_double mem κ₁ range_check_ptr point range_check_ptr₁ double_point ∧
    ∃ anon_cond : F,
    ((anon_cond = 0 ∧
      ∃ (κ₂ : ℕ), spec_ec_mul_inner mem κ₂ range_check_ptr₁ double_point (scalar / (2 : ℤ)) (m - 1) ρ_range_check_ptr ρ_pow2 ρ_res ∧
      κ₁ + κ₂ + 22 ≤ κ) ∨
     (anon_cond ≠ 0 ∧
      ∃ (κ₂ : ℕ) (range_check_ptr₂ : F) (inner_pow2 inner_res : EcPoint mem), spec_ec_mul_inner mem κ₂ range_check_ptr₁ double_point ((scalar - 1) / (2 : ℤ)) (m - 1) range_check_ptr₂ inner_pow2 inner_res ∧
      ∃ (κ₃ : ℕ) (range_check_ptr₃ : F) (res : EcPoint mem), spec_fast_ec_add mem κ₃ range_check_ptr₂ point inner_res range_check_ptr₃ res ∧
      κ₁ + κ₂ + κ₃ + 56 ≤ κ ∧
      ρ_range_check_ptr = range_check_ptr₃ ∧
      ρ_pow2 = inner_pow2 ∧
      ρ_res = res))))

/- ec_mul_inner soundness theorem -/

lemma ec_mul_inner_aux {mem : F → F} {secpF : Type} [secp_field secpF] {pt0 pt1 : EcPoint mem}
   (h0 : BddECPointData secpF pt0)
   (h1 : BddECPointData secpF pt1)
   (hpt0xnz : pt0.x ≠ ⟨0, 0, 0⟩)
   (hxeq : (↑h0.ix.val : secpF) = h1.ix.val) :
  h1.toECPoint = h0.toECPoint ∨ h1.toECPoint = - h0.toECPoint :=
begin
  have h1xz : pt1.x ≠ ⟨0, 0, 0⟩,
  { rwa [ne, h1.pt_zero_iff, ←hxeq, ←h0.pt_zero_iff] },
  simp [BddECPointData.toECPoint, h1xz, hpt0xnz, ECPoint.neg_def, ECPoint.neg, hxeq],
  have := h0.onEC,
  simp only [hxeq, hpt0xnz, ←(h1.onEC' h1xz), false_or] at this,
  exact eq_or_eq_neg_of_sq_eq_sq _ _ this.symm
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_mul_inner
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_pow2 ρ_res : EcPoint mem)
    (h_auto : auto_spec_ec_mul_inner mem κ range_check_ptr point scalar m ρ_range_check_ptr ρ_pow2 ρ_res) :
  spec_ec_mul_inner mem κ range_check_ptr point scalar m ρ_range_check_ptr ρ_pow2 ρ_res :=
begin
  intros secpF _ ptxnez hpt,
  resetI,
  rcases h_auto with ⟨neq, scalareq, _, rfl, _, _, ret1eq, ret2eq⟩ |
    ⟨nnz, _, _, double_pt, hdouble_pt, _, heven_or_odd⟩,
  { use 0, split,
    { rw [neq, nat.cast_zero] }, split,
    { rw PRIME.char_eq, apply PRIME_pos },
    intro _,
    use 0, split,
    { rw [scalareq, nat.cast_zero] },
    split, { norm_num },
    rw [ret1eq, ret2eq], dsimp,
    use [hpt, ptxnez], simp,
    use BddECPointData.zero, simp [BddECPointData.toECPoint], refl },
  rcases spec_ec_double'_of_spec_ec_double hdouble_pt secpF hpt with
    ⟨hdouble, hdouble_eq⟩,
  have double_ne : double_pt.x ≠ ⟨0, 0, 0⟩,
  { rw [ne, ←hdouble.toECPoint_eq_zero_iff],
    contrapose! ptxnez,
    rw ptxnez at hdouble_eq,
    rw [←hpt.toECPoint_eq_zero_iff],
    exact secp_field.eq_zero_of_double_eq_zero hdouble_eq.symm },
  rcases heven_or_odd with ⟨_, _, heven, _⟩ | ⟨_, _, hodd⟩,
  { rcases heven secpF double_ne hdouble with ⟨nn', nn'eq, nn'le, haux⟩,
    use nn' + 1, split,
    { rw [nat.cast_add, nat.cast_one, ←sub_eq_iff_eq_add, nn'eq] }, split,
    { apply nat.succ_le_of_lt,
      apply lt_of_le_of_ne (nat.succ_le_of_lt nn'le),
      contrapose! nnz,
      rw [eq_add_of_sub_eq nn'eq],
      transitivity (↑(nn'.succ) : F), { simp },
      rw [nnz, ring_char.spec] },
    intro nn'le,
    have nn'le' : nn' ≤ 128 := le_trans (le_of_lt (nat.lt_succ_self _)) nn'le,
    rcases haux nn'le' with ⟨nscalar, nscalareq, nscalarlt,
      hdoublepow2, hdoublepow2ne, hdoublepow2eq, hdoubleres, hdoublereseq⟩,
    use 2 * nscalar, split,
    { rw [nat.cast_mul, ←nscalareq],
      symmetry,
      norm_cast,
      apply mul_div_cancel',
      apply PRIME.two_ne_zero },
    split,
    { rw [pow_succ],
      apply nat.mul_lt_mul_of_pos_left nscalarlt,
      norm_num },
    use [hdoublepow2, hdoublepow2ne], split,
      { rw [pow_succ', ←smul_smul, hdoublepow2eq, hdouble_eq] },
    use hdoubleres,
    rw [mul_comm 2, ←smul_smul, hdoublereseq, hdouble_eq] },
  rcases hodd with ⟨_, inner_pow2, inner_res, hodd1, _, _, res, hodd2, _, _, ret1eq, ret2eq⟩,
  rcases hodd1 secpF double_ne hdouble with ⟨nn', nn'eq, nn'le, haux⟩,
  use nn' + 1, split,
  { rw [nat.cast_add, nat.cast_one, ←sub_eq_iff_eq_add, nn'eq] }, split,
  { apply nat.succ_le_of_lt,
    apply lt_of_le_of_ne (nat.succ_le_of_lt nn'le),
    contrapose! nnz,
    rw [eq_add_of_sub_eq nn'eq],
    transitivity (↑(nn'.succ) : F), { simp },
    rw [nnz, ring_char.spec] },
  intro nn'le,
  have nn'le' : nn' ≤ 128 := le_trans (le_of_lt (nat.lt_succ_self _)) nn'le,
  rcases haux nn'le' with ⟨nscalar, nscalareq, nscalarlt, hinnerpow2, hinnerpow2ne, hinnerpow2eq,
      hinnerres, hinnerreseq⟩,
  have : (↑(hpt.ix.val) : secpF) ≠ ↑(hinnerres.ix.val),
  { intro h,
    have := ec_mul_inner_aux hpt hinnerres ptxnez h,
    rw [hinnerreseq, hdouble_eq, smul_smul] at this,
    revert this,
    apply secp_field.order_large_corr,
    { rw [ne, BddECPointData.toECPoint_eq_zero_iff],
      exact ptxnez },
    rw [div_eq_iff] at nscalareq,
    apply lt_of_lt_of_le nscalarlt,
    refine nat.pow_le_pow_of_le_right (by norm_num) nn'le',
    simp only [int.cast_bit0, int.cast_one, ne.def],
    exact PRIME.two_ne_zero F },
  rcases spec_fast_ec_add'_of_spec_fast_ec_add hodd2 secpF hpt hinnerres (or.inl this) with ⟨hret, hreteq⟩,
  use 2 * nscalar + 1, split,
  { rw [nat.cast_add, nat.cast_mul, ←nscalareq],
    symmetry, simp,
    rw mul_div_cancel' (scalar - 1) (PRIME.two_ne_zero F),
    simp },
  rw [ret1eq, ret2eq],
  split,
  { rw [pow_succ, two_mul, add_assoc, two_mul],
    apply add_lt_add_of_lt_of_le nscalarlt,
    apply nat.succ_le_of_lt nscalarlt },
  use [hinnerpow2, hinnerpow2ne], split,
  { rw [pow_succ', ←smul_smul, hinnerpow2eq, hdouble_eq] },
  use hret,
  rw [add_comm, add_smul, one_smul, mul_comm 2, ←smul_smul, hreteq, hinnerreseq, hdouble_eq]
end

/-
-- Function: ec_mul
-/

-- You may change anything in this definition except the name and arguments.
def spec_ec_mul (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar : BigInt3 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ (secpF : Type) [secp_field secpF], by exactI
    point.x ≠ ⟨0, 0, 0⟩ →
    ∀ hpt : BddECPointData secpF point,
      ∃ n0 < 2^86, scalar.d0 = ↑n0 ∧
      ∃ n1 < 2^86, scalar.d1 = ↑n1 ∧
      ∃ n2 < 2^84, scalar.d2 = ↑n2 ∧
      ∃ hres : BddECPointData secpF ρ_res,
        hres.toECPoint = (2^172 * n2 + 2^86 * n1 + n0) • hpt.toECPoint

/- ec_mul autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_mul (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar : BigInt3 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (pow2_0 res0 : EcPoint mem), spec_ec_mul_inner mem κ₁ range_check_ptr point scalar.d0 86 range_check_ptr₁ pow2_0 res0 ∧
  ∃ (κ₂ : ℕ) (range_check_ptr₂ : F) (pow2_1 res1 : EcPoint mem), spec_ec_mul_inner mem κ₂ range_check_ptr₁ pow2_0 scalar.d1 86 range_check_ptr₂ pow2_1 res1 ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₃ : F) (ret2_0 res2 : EcPoint mem), spec_ec_mul_inner mem κ₃ range_check_ptr₂ pow2_1 scalar.d2 84 range_check_ptr₃ ret2_0 res2 ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₄ : F) (res : EcPoint mem), spec_ec_add mem κ₄ range_check_ptr₃ res0 res1 range_check_ptr₄ res ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₅ : F) (res₁ : EcPoint mem), spec_ec_add mem κ₅ range_check_ptr₄ res res2 range_check_ptr₅ res₁ ∧
  κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + 71 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₅ ∧
  ρ_res = res₁

/- ec_mul soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_mul
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (scalar : BigInt3 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem)
    (h_auto : auto_spec_ec_mul mem κ range_check_ptr point scalar ρ_range_check_ptr ρ_res) :
  spec_ec_mul mem κ range_check_ptr point scalar ρ_range_check_ptr ρ_res :=
begin
  intros secpF secp_field ptxnez hpt,
  resetI,
  rcases h_auto with ⟨_, _, pow2_0, res0, h0, _, _, pow2_1, res1, h1, _, _, ret2_0, res_2, h2, _, _, res,
    h3, _, _, res₁, h4, _, _, ret1eq⟩,
  rcases h0 secpF ptxnez hpt with ⟨nb0, nb0eq, nb0lt, h0aux⟩,
  have nb0eq' : nb0 = 86,
  { apply nat.cast_inj_of_lt_char nb0lt, { rw [PRIME.char_eq, PRIME], norm_num1 },
    rw ←nb0eq, simp },
  have nb0le : nb0 ≤ 128, by { rw [nb0eq'], norm_num1 },
  rcases h0aux nb0le with ⟨n0, n0eq, n0lt, hpow20, hpow20ne, hpow20eq, hres0, hres0eq⟩,
  rcases h1 secpF hpow20ne hpow20 with ⟨nb1, nb1eq, nb1lt, h1aux⟩,
  have nb1eq' : nb1 = 86,
  { apply nat.cast_inj_of_lt_char nb1lt, { rw [PRIME.char_eq, PRIME], norm_num1 },
    rw ←nb1eq, simp },
  have nb1le : nb1 ≤ 128, by { rw [nb1eq'], norm_num1 },
  rcases h1aux nb1le with ⟨n1, n1eq, n1lt, hpow21, hpow21ne, hpow21eq, hres1, hres1eq⟩,
  rcases h2 secpF hpow21ne hpow21 with ⟨nb2, nb2eq, nb2lt, h2aux⟩,
  have nb2eq' : nb2 = 84,
  { apply nat.cast_inj_of_lt_char nb2lt, { rw [PRIME.char_eq, PRIME], norm_num1 },
    rw ←nb2eq, simp },
  have nb2le : nb2 ≤ 128, by { rw [nb2eq'], norm_num1 },
  rcases h2aux nb2le with ⟨n2, n2eq, n2lt, hpow22, hpow22ne, hpow22eq, hres2, hres2eq⟩,
  rcases h3 secpF hres0 hres1 with ⟨hres, hreseq⟩,
  rcases h4 secpF hres hres2 with ⟨hres2, hreseq2⟩,
  use n0, split, { rw ←nb0eq', exact n0lt },
  use n0eq,
  use n1, split, { rw ←nb1eq', exact n1lt },
  use n1eq,
  use n2, split, { rw ←nb2eq', exact n2lt },
  use n2eq,
  rw ret1eq,
  use hres2,
  rw [hreseq2, hres2eq, hpow21eq, hpow20eq, hreseq, hres1eq, hres0eq, hpow20eq],
  simp only [smul_smul, ←add_smul, nb0eq', nb1eq', nb2eq', BASE, pow_two],
  norm_num1,
  congr' 1,
  ring
end

/-
-- Function: fast_ec_mul_inner
-/

-- You may change anything in this definition except the name and arguments.
def spec_fast_ec_mul_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (table : π_EcPoint mem) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_point_out : EcPoint mem) (ρ_scalar_out : F) : Prop :=
  ∀ (secpF : Type) [hsecp : secp_field secpF],
  by exactI
    -- point.x ≠ ⟨0, 0, 0⟩ →
    ∀ hpt : BddECPointData secpF point,
    ∀ P : ECPoint secpF,
      (∀ i : ℕ, i < 16 →
        ∃ hres : BddECPointData secpF (cast_EcPoint mem (table.σ_ptr + i * 6)),
        hres.toECPoint = i • P) →
    ∀ k : ℕ,
      k ≤ 31 →
      m = ↑(4 * k) →
    ∀ n : ℕ,
      hpt.toECPoint = n • P →
      2^(4 * k) * (n + 1) ≤ 2^252 →
    ∀ nscalar : ℕ,
      scalar = ↑nscalar →
      ∃ nibbles : ℕ,
        nibbles < 2^(4 * k) ∧
      ρ_scalar_out = ↑(nscalar * 2^(4 * k) + nibbles) ∧
      ∃ hpoint_out : BddECPointData secpF ρ_point_out,
        hpoint_out.toECPoint = (2^(4 * k) * n + nibbles) • P

/- fast_ec_mul_inner autogenerated specification -/

-- Do not change this definition.
def auto_spec_fast_ec_mul_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (table : π_EcPoint mem) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_point_out : EcPoint mem) (ρ_scalar_out : F) : Prop :=
  ((m = 0 ∧
    11 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr ∧
    ρ_point_out = point ∧
    ρ_scalar_out = scalar) ∨
   (m ≠ 0 ∧
    ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (point₁ : EcPoint mem), spec_ec_double mem κ₁ range_check_ptr point range_check_ptr₁ point₁ ∧
    ∃ (κ₂ : ℕ) (range_check_ptr₂ : F) (point₂ : EcPoint mem), spec_ec_double mem κ₂ range_check_ptr₁ point₁ range_check_ptr₂ point₂ ∧
    ∃ (κ₃ : ℕ) (range_check_ptr₃ : F) (point₃ : EcPoint mem), spec_ec_double mem κ₃ range_check_ptr₂ point₂ range_check_ptr₃ point₃ ∧
    ∃ (κ₄ : ℕ) (range_check_ptr₄ : F) (point₄ : EcPoint mem), spec_ec_double mem κ₄ range_check_ptr₃ point₃ range_check_ptr₄ point₄ ∧
    ∃ nibble : F,
    ∃ (κ₅ : ℕ) (range_check_ptr₅ : F), spec_assert_nn_le mem κ₅ range_check_ptr₄ nibble 15 range_check_ptr₅ ∧
    ∃ (κ₆ : ℕ) (range_check_ptr₆ : F) (point₅ : EcPoint mem), spec_fast_ec_add mem κ₆ range_check_ptr₅ point₄ (cast_EcPoint mem (table.σ_ptr + nibble * 6)) range_check_ptr₆ point₅ ∧
    ∃ (κ₇ : ℕ), spec_fast_ec_mul_inner mem κ₇ range_check_ptr₆ table point₅ (16 * scalar + nibble) (m - 4) ρ_range_check_ptr ρ_point_out ρ_scalar_out ∧
    κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + 62 ≤ κ))

/- fast_ec_mul_inner soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_fast_ec_mul_inner
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (table : π_EcPoint mem) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_point_out : EcPoint mem) (ρ_scalar_out : F)
    (h_auto : auto_spec_fast_ec_mul_inner mem κ range_check_ptr table point scalar m ρ_range_check_ptr ρ_point_out ρ_scalar_out) :
  spec_fast_ec_mul_inner mem κ range_check_ptr table point scalar m ρ_range_check_ptr ρ_point_out ρ_scalar_out :=
begin
  intros secpF is_secp_field /- ptxnez -/ hpt P hP k kle meq n hpteq bd nscalar scalareq,
  resetI,
  rcases h_auto with hz | hnz,
  { rcases hz with ⟨mz, _, _, ρ_point_out_eq, ρ_scalar_out_eq⟩,
    have kz : k = 0,
    { simp only [mz, nat.cast_mul, nat.cast_bit0, nat.cast_one, zero_eq_mul] at meq,
      have := meq.resolve_left (PRIME.four_ne_zero F),
      apply PRIME.nat_coe_field_zero _ rfl this,
      apply lt_of_le_of_lt kle,
      rw [PRIME], norm_num },
    use 0, split,
    { rw [kz, mul_zero, pow_zero], exact zero_lt_one },
    split,
    { rw [kz, mul_zero, pow_zero, mul_one, add_zero, ρ_scalar_out_eq, scalareq] },
    rw [ρ_point_out_eq],
    use [hpt],
    rw [hpteq, kz, mul_zero, pow_zero, one_mul, add_zero] },
  rcases hnz with ⟨mnz, _, _, pt1, hpt1,
    _, _, pt2, hpt2,
    _, _, pt3, hpt3,
    _, _, pt4, hpt4,
    nibble, _, _, hnibble,
    _, _, pt5, hpt5,
    _, hrec, _⟩,
  rcases spec_ec_double'_of_spec_ec_double hpt1 secpF hpt with ⟨hpt1', hpt1'_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hpt2 secpF hpt1' with ⟨hpt2', hpt2'_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hpt3 secpF hpt2' with ⟨hpt3', hpt3'_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hpt4 secpF hpt3' with ⟨hpt4', hpt4'_eq⟩,
  rcases hnibble with ⟨nnibble, nslack, nnible_lt, nslack_lt, nibble_eq, sum_eq⟩,
  have kge1 : 1 ≤ k,
  { apply nat.succ_le_of_lt,
    apply nat.pos_of_ne_zero,
    intro keq,
    apply mnz,
    simp only [meq, keq, mul_zero, nat.cast_zero] },
  have nlt : n < 2^248,
  { apply nat.lt_of_succ_le,
    have : 0 < 2^4, { norm_num1 },
    apply nat.le_of_mul_le_mul_left _ this,
    apply le_trans _ (le_trans bd _),
    swap, norm_num1,
    apply mul_le_mul_right',
    apply pow_le_pow, norm_num1,
    apply le_trans _ (mul_le_mul_left' kge1 _),
    rw [mul_one] },
  have nnibble_lt : nnibble < 16,
  { have : nnibble + nslack = 15,
    { apply @PRIME.nat_coe_field_inj F,
      { apply lt_of_lt_of_le (add_lt_add (lt_of_lt_of_le nnible_lt (rc_bound_hyp F))
          (lt_of_lt_of_le nslack_lt (rc_bound_hyp F))),
        rw [PRIME], norm_num1 },
      { rw [PRIME], norm_num1 },
      rw [←sum_eq], simp only [nat.cast_bit1, nat.cast_one] },
    have : nnibble ≤ 15,
    { rw [←this], simp only [le_add_iff_nonneg_right, zero_le']},
    exact nat.lt_succ_of_le this },
  have := hP nnibble nnibble_lt,
  rw [←nibble_eq] at this,
  rcases this with ⟨hpt_nibble, pt_nibble_eq⟩,
  have hpt4'_eq_16pt : hpt4'.toECPoint = 16 • hpt.toECPoint,
  { rw [hpt4'_eq, hpt3'_eq, hpt2'_eq, hpt1'_eq],
    simp only [←mul_nsmul],
    norm_num1, refl },
  have : ↑(hpt4'.ix.val) ≠ ↑(hpt_nibble.ix.val) ∨ hpt4'.toECPoint = 0 ∨ hpt_nibble.toECPoint = 0,
  { by_cases Pz : P = 0,
    { right, right, rw [pt_nibble_eq, Pz, smul_zero] },
    by_cases nnibblez : nnibble = 0,
    { right, right, rw [pt_nibble_eq, nnibblez, zero_smul] },
    left,
    intro h,
    have := BddECPointData.toECPoint_eq_or_eq_neg h,
    rw [hpt4'_eq_16pt, pt_nibble_eq, hpteq, ←mul_smul, eq_neg_iff_add_eq_zero, ←add_nsmul] at this,
    rcases this with h | h,
    { have : 16 * n = nnibble,
      { apply secp_field.order_large_corr' _ _ Pz h,
        apply lt_of_lt_of_le (mul_lt_mul_of_pos_left nlt _), norm_num1, norm_num1,
        apply lt_of_lt_of_le nnibble_lt, norm_num1 },
      have h' := congr_arg (λ n, n % 16) this, dsimp at h',
      rw [nat.mul_mod_right, nat.mod_eq_of_lt nnibble_lt] at h',
      exact nnibblez h'.symm },
    revert h,
    apply secp_field.order_large,
    { exact Pz },
    { simp only [nnibblez, ne.def, add_eq_zero_iff, and_false, not_false_iff] },
    have : 16 * n + nnibble < 16 * (n + 1),
    { rw [mul_add, mul_one], apply add_lt_add_left nnibble_lt },
    apply lt_of_lt_of_le this,
    have : 16 * (n + 1) ≤ 16 * 2^248,
    { apply nat.mul_le_mul_left,
      apply nat.succ_le_of_lt nlt },
    apply le_trans this,
    norm_num },
  have := spec_fast_ec_add'_of_spec_fast_ec_add hpt5 secpF hpt4' hpt_nibble this,
  rcases this with ⟨hpt5', hpt5'_eq⟩,
  have hpt5'_eq' : hpt5'.toECPoint = (n * 16 + nnibble) • P,
  { rw [hpt5'_eq, hpt4'_eq_16pt, hpteq, pt_nibble_eq, mul_comm, add_smul, mul_smul] },
  have eq1 : m - 4 = ↑(4 * (k - 1)),
  { rw [meq, mul_tsub, mul_one, nat.cast_sub],
    simp only [nat.cast_bit0, nat.cast_one],
    have : 4 ≤ 4 * 1, { rw [mul_one] },
    apply le_trans this (mul_le_mul_left' kge1 _) },
  have eq2 : 2 ^ (4 * (k - 1)) * 16 = 2 ^ (4 * k),
  { have : 16 = 2 ^ (4 * 1), { norm_num1 },
    rw [this, ←pow_add, ←mul_add, nat.sub_add_cancel kge1] },
  have ineq1 : 2 ^ (4 * (k - 1)) * (n * 16 + nnibble + 1) ≤ 2 ^ 252,
  { apply le_trans _ bd,
    rw [←eq2, mul_assoc],
    apply nat.mul_le_mul_left,
    rw [mul_add, mul_one, mul_comm, add_assoc],
    apply add_le_add_left,
    apply nat.succ_le_of_lt nnibble_lt },
  have := hrec secpF hpt5' P hP (k - 1) ((nat.sub_le _ _).trans kle) eq1 _ hpt5'_eq'
    ineq1 (16 * nscalar + nnibble) (by simp [scalareq, nibble_eq]),
  rcases this with ⟨nnibbles_rec, nnibbles_rec_lt, rfl, hpoint_rec, hpoint_rec_eq⟩,
  use nnibble * 2 ^ (4 * (k - 1)) + nnibbles_rec,
  split,
  { apply @lt_of_lt_of_le _ _ _ ((nnibble + 1) * 2 ^ (4 * (k - 1))),
    { rw [add_mul, one_mul],
      apply add_lt_add_left nnibbles_rec_lt },
    rw [←eq2, mul_comm _ 16],
    apply nat.mul_le_mul_right,
    apply nat.succ_le_of_lt nnibble_lt },
  have eq3 : ∀ n, 2 ^ (4 * (k - 1)) * (n * 16 + nnibble) + nnibbles_rec
    = 2 ^ (4 * k) * n + (nnibble * 2 ^ (4 * (k - 1)) + nnibbles_rec),
  { intro n,
    rw [mul_add, add_assoc, mul_comm _ nnibble, mul_comm _ 16, ←mul_assoc, eq2] },
  split,
  rw [mul_comm, mul_comm _ nscalar, eq3, mul_comm],
  use hpoint_rec,
  rw [hpoint_rec_eq, eq3]
end

/-
-- Function: build_ec_mul_table
-/

-- You may change anything in this definition except the name and arguments.
def spec_build_ec_mul_table (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (table : π_EcPoint mem) (ρ_range_check_ptr : F) : Prop :=
∀ (secpF : Type) [hsecp : secp_field secpF],
   by exactI
      ∀ hpt : BddECPointData secpF point,
  ∀ i : ℕ, i < 16 →
    ∃ hres : BddECPointData secpF (cast_EcPoint mem (table.σ_ptr + i * 6)),
      hres.toECPoint = i • hpt.toECPoint

/- build_ec_mul_table autogenerated specification -/

-- Do not change this definition.
def auto_spec_build_ec_mul_table (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (table : π_EcPoint mem) (ρ_range_check_ptr : F) : Prop :=
  cast_EcPoint mem (table.σ_ptr) = {
    x := { d0 := 0, d1 := 0, d2 := 0 },
    y := { d0 := 0, d1 := 0, d2 := 0 }
  } ∧
  cast_EcPoint mem (table.σ_ptr + 6) = point ∧
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (t2 : EcPoint mem), spec_ec_double mem κ₁ range_check_ptr point range_check_ptr₁ t2 ∧
  cast_EcPoint mem (table.σ_ptr + 12) = t2 ∧
  ∃ (κ₂ : ℕ) (range_check_ptr₂ : F) (t3 : EcPoint mem), spec_fast_ec_add mem κ₂ range_check_ptr₁ t2 point range_check_ptr₂ t3 ∧
  cast_EcPoint mem (table.σ_ptr + 18) = t3 ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₃ : F) (t4 : EcPoint mem), spec_fast_ec_add mem κ₃ range_check_ptr₂ t3 point range_check_ptr₃ t4 ∧
  cast_EcPoint mem (table.σ_ptr + 24) = t4 ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₄ : F) (t5 : EcPoint mem), spec_fast_ec_add mem κ₄ range_check_ptr₃ t4 point range_check_ptr₄ t5 ∧
  cast_EcPoint mem (table.σ_ptr + 30) = t5 ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₅ : F) (t6 : EcPoint mem), spec_fast_ec_add mem κ₅ range_check_ptr₄ t5 point range_check_ptr₅ t6 ∧
  cast_EcPoint mem (table.σ_ptr + 36) = t6 ∧
  ∃ (κ₆ : ℕ) (range_check_ptr₆ : F) (t7 : EcPoint mem), spec_fast_ec_add mem κ₆ range_check_ptr₅ t6 point range_check_ptr₆ t7 ∧
  cast_EcPoint mem (table.σ_ptr + 42) = t7 ∧
  ∃ (κ₇ : ℕ) (range_check_ptr₇ : F) (t8 : EcPoint mem), spec_fast_ec_add mem κ₇ range_check_ptr₆ t7 point range_check_ptr₇ t8 ∧
  cast_EcPoint mem (table.σ_ptr + 48) = t8 ∧
  ∃ (κ₈ : ℕ) (range_check_ptr₈ : F) (t9 : EcPoint mem), spec_fast_ec_add mem κ₈ range_check_ptr₇ t8 point range_check_ptr₈ t9 ∧
  cast_EcPoint mem (table.σ_ptr + 54) = t9 ∧
  ∃ (κ₉ : ℕ) (range_check_ptr₉ : F) (t10 : EcPoint mem), spec_fast_ec_add mem κ₉ range_check_ptr₈ t9 point range_check_ptr₉ t10 ∧
  cast_EcPoint mem (table.σ_ptr + 60) = t10 ∧
  ∃ (κ₁₀ : ℕ) (range_check_ptr₁₀ : F) (t11 : EcPoint mem), spec_fast_ec_add mem κ₁₀ range_check_ptr₉ t10 point range_check_ptr₁₀ t11 ∧
  cast_EcPoint mem (table.σ_ptr + 66) = t11 ∧
  ∃ (κ₁₁ : ℕ) (range_check_ptr₁₁ : F) (t12 : EcPoint mem), spec_fast_ec_add mem κ₁₁ range_check_ptr₁₀ t11 point range_check_ptr₁₁ t12 ∧
  cast_EcPoint mem (table.σ_ptr + 72) = t12 ∧
  ∃ (κ₁₂ : ℕ) (range_check_ptr₁₂ : F) (t13 : EcPoint mem), spec_fast_ec_add mem κ₁₂ range_check_ptr₁₁ t12 point range_check_ptr₁₂ t13 ∧
  cast_EcPoint mem (table.σ_ptr + 78) = t13 ∧
  ∃ (κ₁₃ : ℕ) (range_check_ptr₁₃ : F) (t14 : EcPoint mem), spec_fast_ec_add mem κ₁₃ range_check_ptr₁₂ t13 point range_check_ptr₁₃ t14 ∧
  cast_EcPoint mem (table.σ_ptr + 84) = t14 ∧
  ∃ (κ₁₄ : ℕ) (range_check_ptr₁₄ : F) (t15 : EcPoint mem), spec_fast_ec_add mem κ₁₄ range_check_ptr₁₃ t14 point range_check_ptr₁₄ t15 ∧
  cast_EcPoint mem (table.σ_ptr + 90) = t15 ∧
  κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + κ₈ + κ₉ + κ₁₀ + κ₁₁ + κ₁₂ + κ₁₃ + κ₁₄ + 203 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₁₄

/-
Note: the manual soundness proof for ec_mul_table is a performance bottleneck. Doing lots of
nested cases seems to induce quadratic behavior in checking. So we use some tricks to minimize
the problem. The first is the use of `auto_spec_build_ec_mul_table'`: we break out some of the
packing and rewriting. We also use `classical.indefinite_description` rather than `rcases`
in the soundness proof.
-/

def auto_spec_build_ec_mul_table' (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (table : π_EcPoint mem) (ρ_range_check_ptr : F) : Prop :=
  cast_EcPoint mem (table.σ_ptr) = {
    x := { d0 := 0, d1 := 0, d2 := 0 },
    y := { d0 := 0, d1 := 0, d2 := 0 }
  } ∧
  cast_EcPoint mem (table.σ_ptr + 6) = point ∧
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F), spec_ec_double mem κ₁ range_check_ptr point range_check_ptr₁ (cast_EcPoint mem (table.σ_ptr + 12)) ∧
  ∃ (κ₂ : ℕ) (range_check_ptr₂ : F), spec_fast_ec_add mem κ₂ range_check_ptr₁
    (cast_EcPoint mem (table.σ_ptr + 12)) point range_check_ptr₂ (cast_EcPoint mem (table.σ_ptr + 18)) ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₃ : F), spec_fast_ec_add mem κ₃ range_check_ptr₂
    (cast_EcPoint mem (table.σ_ptr + 18)) point range_check_ptr₃ (cast_EcPoint mem (table.σ_ptr + 24)) ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₄ : F), spec_fast_ec_add mem κ₄ range_check_ptr₃
    (cast_EcPoint mem (table.σ_ptr + 24)) point range_check_ptr₄ (cast_EcPoint mem (table.σ_ptr + 30)) ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₅ : F), spec_fast_ec_add mem κ₅ range_check_ptr₄
    (cast_EcPoint mem (table.σ_ptr + 30)) point range_check_ptr₅ (cast_EcPoint mem (table.σ_ptr + 36)) ∧
  ∃ (κ₆ : ℕ) (range_check_ptr₆ : F), spec_fast_ec_add mem κ₆ range_check_ptr₅
    (cast_EcPoint mem (table.σ_ptr + 36)) point range_check_ptr₆  (cast_EcPoint mem (table.σ_ptr + 42)) ∧
  ∃ (κ₇ : ℕ) (range_check_ptr₇ : F), spec_fast_ec_add mem κ₇ range_check_ptr₆
     (cast_EcPoint mem (table.σ_ptr + 42)) point range_check_ptr₇ (cast_EcPoint mem (table.σ_ptr + 48)) ∧
  ∃ (κ₈ : ℕ) (range_check_ptr₈ : F), spec_fast_ec_add mem κ₈ range_check_ptr₇
    (cast_EcPoint mem (table.σ_ptr + 48)) point range_check_ptr₈ (cast_EcPoint mem (table.σ_ptr + 54)) ∧
  ∃ (κ₉ : ℕ) (range_check_ptr₉ : F), spec_fast_ec_add mem κ₉ range_check_ptr₈
    (cast_EcPoint mem (table.σ_ptr + 54)) point range_check_ptr₉ (cast_EcPoint mem (table.σ_ptr + 60)) ∧
  ∃ (κ₁₀ : ℕ) (range_check_ptr₁₀ : F), spec_fast_ec_add mem κ₁₀ range_check_ptr₉
    (cast_EcPoint mem (table.σ_ptr + 60)) point range_check_ptr₁₀ (cast_EcPoint mem (table.σ_ptr + 66)) ∧
  ∃ (κ₁₁ : ℕ) (range_check_ptr₁₁ : F), spec_fast_ec_add mem κ₁₁ range_check_ptr₁₀
    (cast_EcPoint mem (table.σ_ptr + 66)) point range_check_ptr₁₁ (cast_EcPoint mem (table.σ_ptr + 72)) ∧
  ∃ (κ₁₂ : ℕ) (range_check_ptr₁₂ : F), spec_fast_ec_add mem κ₁₂ range_check_ptr₁₁
    (cast_EcPoint mem (table.σ_ptr + 72)) point range_check_ptr₁₂ (cast_EcPoint mem (table.σ_ptr + 78)) ∧
  ∃ (κ₁₃ : ℕ) (range_check_ptr₁₃ : F), spec_fast_ec_add mem κ₁₃ range_check_ptr₁₂
    (cast_EcPoint mem (table.σ_ptr + 78)) point range_check_ptr₁₃ (cast_EcPoint mem (table.σ_ptr + 84)) ∧
  ∃ (κ₁₄ : ℕ) (range_check_ptr₁₄ : F), spec_fast_ec_add mem κ₁₄ range_check_ptr₁₃
    (cast_EcPoint mem (table.σ_ptr + 84)) point range_check_ptr₁₄ (cast_EcPoint mem (table.σ_ptr + 90))

theorem auto_spec_build_ec_mul_table'_of_auto_spec_build_ec_mul_table
    {mem : F → F}
    {κ : ℕ}
    {range_check_ptr : F} {point : EcPoint mem} {table : π_EcPoint mem} {ρ_range_check_ptr : F}
    (h_auto : auto_spec_build_ec_mul_table mem κ range_check_ptr point table ρ_range_check_ptr) :
  auto_spec_build_ec_mul_table' mem κ range_check_ptr point table ρ_range_check_ptr :=
begin
  rcases h_auto with ⟨hpt0, hpt1,
  k2, rc2, pt2, hpt2, rfl,
  k3, rc3, pt3, hpt3, rfl,
  k4, rc4, pt4, hpt4, rfl,
  k5, rc5, pt5, hpt5, rfl,
  k6, rc6, pt6, hpt6, rfl,
  k7, rc7, pt7, hpt7, rfl,
  k8, rc8, pt8, hpt8, rfl,
  k9, rc9, pt9, hpt9, rfl,
  k10, rc10, pt10, hpt10, rfl,
  k11, rc11, pt11, hpt11, rfl,
  k12, rc12, pt12, hpt12, rfl,
  k13, rc13, pt13, hpt13, rfl,
  k14, rc14, pt14, hpt14, rfl,
  k15, rc15, pt15, hpt15, rfl,
  hh⟩,
  use [hpt0, hpt1,
    k2, rc2, hpt2,
    k3, rc3, hpt3,
    k4, rc4, hpt4,
    k5, rc5, hpt5,
    k6, rc6, hpt6,
    k7, rc7, hpt7,
    k8, rc8, hpt8,
    k9, rc9, hpt9,
    k10, rc10, hpt10,
    k11, rc11, hpt11,
    k12, rc12, hpt12,
    k13, rc13, hpt13,
    k14, rc14, hpt14,
    k15, rc15, hpt15]
end

/- build_ec_mul_table soundness theorem -/

section
open nat

lemma sound_build_ec_mul_table_aux' {P : ℕ → Prop}
    (h : P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧
          P 10 ∧ P 11 ∧ P 12 ∧ P 13 ∧ P 14 ∧ P 15) :
  ∀ i < 16, P i :=
begin
  have : 16 = succ (succ (succ (succ (succ (succ (succ (succ (
              succ (succ (succ (succ (succ (succ (succ (succ 0)
              )))))))))))))) := rfl,
  rw this,
  simp [forall_lt_succ, and_assoc],
  exact h
end
end

section
open nat

lemma sound_build_ec_mul_table_aux {P : ℕ → Prop} :
    P 0 → P 1 → P 2 → P 3 → P 4 → P 5 → P 6 → P 7 → P 8 → P 9 →
          P 10 → P 11 → P 12 → P 13 → P 14 → P 15 →
  ∀ i < 16, P i :=
begin
  have : 16 = succ (succ (succ (succ (succ (succ (succ (succ (
              succ (succ (succ (succ (succ (succ (succ (succ 0)
              )))))))))))))) := rfl,
  rw this,
  simp [forall_lt_succ, and_assoc],
  intros,
  repeat { split, assumption },
  assumption
end
end

lemma sound_build_ec_mul_table_aux1 {mem : F → F} {pt pt' : EcPoint mem} {secpF : Type} [secp_field secpF]
    (hpt : BddECPointData secpF pt) (hpt' : BddECPointData secpF pt')
    {i : ℕ} (h : hpt'.toECPoint = i • hpt.toECPoint) (hi : i < 16)  (hi' : i ≠ 1):
  (↑(hpt'.ix.val) : secpF) ≠ ↑(hpt.ix.val) ∨
    hpt'.toECPoint = 0 ∨ hpt.toECPoint = 0 :=
begin
  by_cases h' : (hpt'.ix.val : secpF) = ↑(hpt.ix.val),
  swap, { left, exact h' },
  right,
  rcases BddECPointData.toECPoint_eq_or_eq_neg h' with h'' | h'',
  { rw [←one_smul _ hpt'.toECPoint] at h,
    right,
    by_contradiction h₃,
    apply hi',
    symmetry,
    apply secp_field.order_large_corr' _ _ h₃,
    exact (congr_arg (λ x, 1 • x) h''.symm).trans h,
    norm_num,
    apply lt_trans hi,
    norm_num },
  have := h.symm,
  rw [h'', eq_neg_iff_add_eq_zero, ←one_smul _ hpt.toECPoint, smul_smul i 1 hpt.toECPoint, mul_one, ←add_smul] at this,
  right,
  by_contradiction,
  revert this,
  apply secp_field.order_large h (nat.succ_ne_zero _),
  apply lt_of_lt_of_le (add_lt_add_right hi 1),
  norm_num
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_build_ec_mul_table
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (table : π_EcPoint mem) (ρ_range_check_ptr : F)
    (h_auto : auto_spec_build_ec_mul_table mem κ range_check_ptr point table ρ_range_check_ptr) :
  spec_build_ec_mul_table mem κ range_check_ptr point table ρ_range_check_ptr :=
begin
  intros secpF secp_field hpt,
  resetI,
  rcases auto_spec_build_ec_mul_table'_of_auto_spec_build_ec_mul_table h_auto with
    ⟨hpt0, hpt1,
    k2, rc2, hpt2,
    k3, rc3, hpt3,
    k4, rc4, hpt4,
    k5, rc5, hpt5,
    k6, rc6, hpt6,
    k7, rc7, hpt7,
    k8, rc8, hpt8,
    k9, rc9, hpt9,
    k10, rc10, hpt10,
    k11, rc11, hpt11,
    k12, rc12, hpt12,
    k13, rc13, hpt13,
    k14, rc14, hpt14,
    k15, rc15, hpt15⟩,
  have helper : ∀ n, n • hpt.toECPoint + hpt.toECPoint = (n + 1) • hpt.toECPoint,
  { intro n, abel },
  rcases spec_ec_double'_of_spec_ec_double hpt2 secpF hpt with ⟨hpt2, hpt2_eq⟩,
  rcases spec_fast_ec_add'_of_spec_fast_ec_add hpt3 secpF hpt2 hpt
    (sound_build_ec_mul_table_aux1 hpt hpt2 hpt2_eq (by norm_num) (by norm_num)) with ⟨hpt3, hpt3'_eq⟩,
  have hpt3_eq : hpt3.toECPoint = 3 • hpt.toECPoint,
  { rw [hpt3'_eq, hpt2_eq], abel },
  let hpt4_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt4 secpF hpt3 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt3 hpt3_eq (by norm_num) (by norm_num))),
  let hpt4 := hpt4_aux.1,
  have hpt4_eq : hpt4.toECPoint = 4 • hpt.toECPoint,
  { rw [hpt4_aux.2, hpt3_eq], apply helper },
  let hpt5_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt5 secpF hpt4 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt4 hpt4_eq (by norm_num) (by norm_num))),
  let hpt5 := hpt5_aux.1,
  have hpt5_eq : hpt5.toECPoint = 5 • hpt.toECPoint,
  { rw [hpt5_aux.2, hpt4_eq], apply helper },
  let hpt6_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt6 secpF hpt5 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt5 hpt5_eq (by norm_num) (by norm_num))),
  let hpt6 := hpt6_aux.1,
  have hpt6_eq : hpt6.toECPoint = 6 • hpt.toECPoint,
  { rw [hpt6_aux.2, hpt5_eq], apply helper },
  let hpt7_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt7 secpF hpt6 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt6 hpt6_eq (by norm_num) (by norm_num))),
  let hpt7 := hpt7_aux.1,
  have hpt7_eq : hpt7.toECPoint = 7 • hpt.toECPoint,
  { rw [hpt7_aux.2, hpt6_eq], apply helper },
  let hpt8_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt8 secpF hpt7 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt7 hpt7_eq (by norm_num) (by norm_num))),
  let hpt8 := hpt8_aux.1,
  have hpt8_eq : hpt8.toECPoint = 8 • hpt.toECPoint,
  { rw [hpt8_aux.2, hpt7_eq], apply helper },
  let hpt9_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt9 secpF hpt8 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt8 hpt8_eq (by norm_num) (by norm_num))),
  let hpt9 := hpt9_aux.1,
  have hpt9_eq : hpt9.toECPoint = 9 • hpt.toECPoint,
  { rw [hpt9_aux.2, hpt8_eq], apply helper },
  let hpt10_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt10 secpF hpt9 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt9 hpt9_eq (by norm_num) (by norm_num))),
  let hpt10 := hpt10_aux.1,
  have hpt10_eq : hpt10.toECPoint = 10 • hpt.toECPoint,
  { rw [hpt10_aux.2, hpt9_eq], apply helper },
  let hpt11_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt11 secpF hpt10 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt10 hpt10_eq (by norm_num) (by norm_num))),
  let hpt11 := hpt11_aux.1,
  have hpt11_eq : hpt11.toECPoint = 11 • hpt.toECPoint,
  { rw [hpt11_aux.2, hpt10_eq], apply helper },
  let hpt12_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt12 secpF hpt11 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt11 hpt11_eq (by norm_num) (by norm_num))),
  let hpt12 := hpt12_aux.1,
  have hpt12_eq : hpt12.toECPoint = 12 • hpt.toECPoint,
  { rw [hpt12_aux.2, hpt11_eq], apply helper },
  let hpt13_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt13 secpF hpt12 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt12 hpt12_eq (by norm_num) (by norm_num))),
  let hpt13 := hpt13_aux.1,
  have hpt13_eq : hpt13.toECPoint = 13 • hpt.toECPoint,
  { rw [hpt13_aux.2, hpt12_eq], apply helper },
  let hpt14_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt14 secpF hpt13 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt13 hpt13_eq (by norm_num) (by norm_num))),
  let hpt14 := hpt14_aux.1,
  have hpt14_eq : hpt14.toECPoint = 14 • hpt.toECPoint,
  { rw [hpt14_aux.2, hpt13_eq], apply helper },
  let hpt15_aux := classical.indefinite_description _
    (spec_fast_ec_add'_of_spec_fast_ec_add hpt15 secpF hpt14 hpt
      (sound_build_ec_mul_table_aux1 hpt hpt14 hpt14_eq (by norm_num) (by norm_num))),
  let hpt15 := hpt15_aux.1,
  have hpt15_eq : hpt15.toECPoint = 15 • hpt.toECPoint,
  { rw [hpt15_aux.2, hpt14_eq], apply helper },
  apply sound_build_ec_mul_table_aux,
  { rw [nat.cast_zero, zero_mul, zero_smul, add_zero, hpt0],
    use BddECPointData.zero,
    rw [BddECPointData.toECPoint_zero] },
  { rw [nat.cast_one, one_mul, one_smul, hpt1],
    use hpt },
  { use [hpt2.cast (by norm_num)],
    rw [hpt2.cast_toECPoint_eq, hpt2_eq] },
  { use [hpt3.cast (by norm_num)],
    rw [hpt3.cast_toECPoint_eq, hpt3_eq] },
  { use [hpt4.cast (by norm_num)],
    rw [hpt4.cast_toECPoint_eq, hpt4_eq] },
  { use [hpt5.cast (by norm_num)],
    rw [hpt5.cast_toECPoint_eq, hpt5_eq] },
  { use [hpt6.cast (by norm_num)],
    rw [hpt6.cast_toECPoint_eq, hpt6_eq] },
  { use [hpt7.cast (by norm_num)],
    rw [hpt7.cast_toECPoint_eq, hpt7_eq] },
  { use [hpt8.cast (by norm_num)],
    rw [hpt8.cast_toECPoint_eq, hpt8_eq] },
  { use [hpt9.cast (by norm_num)],
    rw [hpt9.cast_toECPoint_eq, hpt9_eq] },
  { use [hpt10.cast (by norm_num)],
    rw [hpt10.cast_toECPoint_eq, hpt10_eq] },
  { use [hpt11.cast (by norm_num)],
    rw [hpt11.cast_toECPoint_eq, hpt11_eq] },
  { use [hpt12.cast (by norm_num)],
    rw [hpt12.cast_toECPoint_eq, hpt12_eq] },
  { use [hpt13.cast (by norm_num)],
    rw [hpt13.cast_toECPoint_eq, hpt13_eq] },
  { use [hpt14.cast (by norm_num)],
    rw [hpt14.cast_toECPoint_eq, hpt14_eq] },
  { use [hpt15.cast (by norm_num)],
    rw [hpt15.cast_toECPoint_eq, hpt15_eq] }
end

/-
-- Function: ec_mul_by_uint256
-/

-- You may change anything in this definition except the name and arguments.
def spec_ec_mul_by_uint256 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar : Uint256 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ (secpF : Type) [secp_field secpF], by exactI
    ∀ hpt : BddECPointData secpF point,
      ∃ n0 < 2^128, scalar.low = ↑n0 ∧
      ∃ n1 < 2^128, scalar.high = ↑n1 ∧
      ∃ hres : BddECPointData secpF ρ_res,
        hres.toECPoint = (2^128 * n1 + n0) • hpt.toECPoint

/- ec_mul_by_uint256 autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_mul_by_uint256 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar : Uint256 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∃ (κ₁ : ℕ) (table : π_EcPoint mem), spec_alloc mem κ₁  table ∧
  ∃ (κ₂ : ℕ) (range_check_ptr₁ : F), spec_build_ec_mul_table mem κ₂ range_check_ptr point table range_check_ptr₁ ∧
  ∃ first_nibble : F,
  ∃ last_nibble : F,
  ∃ (κ₃ : ℕ) (range_check_ptr₂ : F), spec_assert_nn_le mem κ₃ range_check_ptr₁ first_nibble 15 range_check_ptr₂ ∧
  ∃ (κ₄ : ℕ) (range_check_ptr₃ : F) (res : EcPoint mem) (scalar_high : F), spec_fast_ec_mul_inner mem κ₄ range_check_ptr₂ table (cast_EcPoint mem (table.σ_ptr + first_nibble * 6)) first_nibble 124 range_check_ptr₃ res scalar_high ∧
  scalar_high = scalar.high ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₄ : F) (res₁ : EcPoint mem) (scalar_low : F), spec_fast_ec_mul_inner mem κ₅ range_check_ptr₃ table res 0 124 range_check_ptr₄ res₁ scalar_low ∧
  scalar.low = 16 * scalar_low + last_nibble ∧
  ∃ (κ₆ : ℕ) (range_check_ptr₅ : F), spec_assert_nn_le mem κ₆ range_check_ptr₄ last_nibble 15 range_check_ptr₅ ∧
  ∃ (κ₇ : ℕ) (range_check_ptr₆ : F) (res₂ : EcPoint mem), spec_ec_double mem κ₇ range_check_ptr₅ res₁ range_check_ptr₆ res₂ ∧
  ∃ (κ₈ : ℕ) (range_check_ptr₇ : F) (res₃ : EcPoint mem), spec_ec_double mem κ₈ range_check_ptr₆ res₂ range_check_ptr₇ res₃ ∧
  ∃ (κ₉ : ℕ) (range_check_ptr₈ : F) (res₄ : EcPoint mem), spec_ec_double mem κ₉ range_check_ptr₇ res₃ range_check_ptr₈ res₄ ∧
  ∃ (κ₁₀ : ℕ) (range_check_ptr₉ : F) (res₅ : EcPoint mem), spec_ec_double mem κ₁₀ range_check_ptr₈ res₄ range_check_ptr₉ res₅ ∧
  ∃ (κ₁₁ : ℕ), spec_ec_add mem κ₁₁ range_check_ptr₉ res₅ (cast_EcPoint mem (table.σ_ptr + last_nibble * 6)) ρ_range_check_ptr ρ_res ∧
  κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + κ₈ + κ₉ + κ₁₀ + κ₁₁ + 104 ≤ κ

/- ec_mul_by_uint256 soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_mul_by_uint256
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (scalar : Uint256 mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem)
    (h_auto : auto_spec_ec_mul_by_uint256 mem κ range_check_ptr point scalar ρ_range_check_ptr ρ_res) :
  spec_ec_mul_by_uint256 mem κ range_check_ptr point scalar ρ_range_check_ptr ρ_res :=
begin
  intros secpF secp_field hpt,
  resetI,
  rcases h_auto with ⟨_, table, _, _, _, h_spec_table, first_nibble, last_nibble,
    _, _, h_first_nibble,
    _, _, res, scalar_high, h_spec_mul_inner_high,
    h_scalar_high_eq,
    _, _, res', scalar_low, h_spec_mul_inner_low,
    h_scalar_low_eq,
    _, _, h_last_nibble,
    _, _, r0, hr0,
    _, _, r1, hr1,
    _, _, r2, hr2,
    _, _, r3, hr3,
    _, hspec_add, _⟩,
  have htable := h_spec_table secpF hpt,
  rcases h_first_nibble with ⟨nfirst_nibble, nslack, nfirst_nibble_lt, nslack_lt, first_nibble_eq,
    nfirst_nibble_sum_eq⟩,
  have nfirst_nibble_lt : nfirst_nibble < 16,
  { have : ↑(nfirst_nibble + nslack) = (↑(15 : ℕ) : F),
    { rw [←nfirst_nibble_sum_eq], simp },
    suffices hh : nfirst_nibble + nslack = 15,
    { linarith },
    apply PRIME.nat_coe_field_inj _ _ this,
    apply lt_of_lt_of_le (add_lt_add nfirst_nibble_lt nslack_lt),
    apply le_trans (add_le_add (rc_bound_hyp F) (rc_bound_hyp F)),
    rw [PRIME], norm_num,
    rw [PRIME], norm_num },
  have := htable nfirst_nibble nfirst_nibble_lt,
  rw [←first_nibble_eq] at this,
  rcases this with ⟨hpoint_first_nibble, hpoint_first_nibble_eq⟩,
  have bd0 : 2 ^ (4 * 31) * (nfirst_nibble + 1) ≤ 2^252,
  { transitivity (2 ^ (4 * 31)) * 16,
    swap, norm_num,
    apply mul_le_mul_left',
    apply nat.succ_le_of_lt nfirst_nibble_lt },
  have := h_spec_mul_inner_high secpF hpoint_first_nibble _ htable 31 (by norm_num)
    (by simp; norm_num) nfirst_nibble hpoint_first_nibble_eq bd0 _ first_nibble_eq,
  rcases this with ⟨nibbles_high, nibbles_high_lt, scalar_high_eq, hpoint_high, hpoint_high_eq⟩,
  have bd1 : 2 ^ (4 * 31) * (2 ^ (4 * 31) * nfirst_nibble + nibbles_high + 1) ≤ 2 ^ 252,
  { transitivity 2 ^ (4 * 31) * (2 ^ (4 * 31) * 15 + 2 ^ (4 * 31) ),
    swap, { norm_num },
    apply mul_le_mul_left',
    rw [add_assoc],
    apply add_le_add,
    { apply mul_le_mul_left' (nat.le_of_lt_succ nfirst_nibble_lt) },
    apply nat.succ_le_of_lt nibbles_high_lt },
  have := h_spec_mul_inner_low secpF hpoint_high _ htable 31 (by norm_num) (by simp; norm_num)
    _ hpoint_high_eq bd1 0 (by simp),
  rcases this with ⟨nibbles_low, nibbles_low_lt, scalar_low_eq, hpoint_low, hpoint_low_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hr0 secpF hpoint_low with ⟨hpt0, hpt0_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hr1 secpF hpt0 with ⟨hpt1, hpt1_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hr2 secpF hpt1 with ⟨hpt2, hpt2_eq⟩,
  rcases spec_ec_double'_of_spec_ec_double hr3 secpF hpt2 with ⟨hpt3, hpt3_eq⟩,
  rcases h_last_nibble with ⟨nlast_nibble, nslack', nlast_nibble_lt, nslack'_lt, last_nibble_eq,
    nlast_nibble_sum_eq⟩,
  have nlast_nibble_lt : nlast_nibble < 16,
  { have : ↑(nlast_nibble + nslack') = (↑(15 : ℕ) : F),
    { rw [←nlast_nibble_sum_eq], simp },
    suffices hh : nlast_nibble + nslack' = 15,
    { linarith },
    apply PRIME.nat_coe_field_inj _ _ this,
    apply lt_of_lt_of_le (add_lt_add nlast_nibble_lt nslack'_lt),
    apply le_trans (add_le_add (rc_bound_hyp F) (rc_bound_hyp F)),
    rw [PRIME], norm_num,
    rw [PRIME], norm_num },
  have := htable nlast_nibble nlast_nibble_lt,
  rw [←last_nibble_eq] at this,
  rcases this with ⟨hpoint_last_nibble, hpoint_last_nibble_eq⟩,
  have := hspec_add secpF hpt3 hpoint_last_nibble,
  rcases this with ⟨hres, hreseq⟩,
  use [16 * nibbles_low + nlast_nibble],
  split,
  { apply @lt_of_lt_of_le _ _ _ (16 * (nibbles_low + 1)),
    { rw [mul_add, mul_one],
      apply add_lt_add_left nlast_nibble_lt },
    transitivity 16 * 2 ^ (4 * 31),
    swap, { norm_num },
    apply mul_le_mul_left',
    apply nat.succ_le_of_lt nibbles_low_lt },
  split,
  { rw [h_scalar_low_eq, scalar_low_eq, last_nibble_eq, zero_mul, zero_add,
      nat.cast_add, nat.cast_mul], simp only [nat.cast_bit0, nat.cast_one] },
  use [nfirst_nibble * 2 ^ (4 * 31) + nibbles_high],
  split,
  { apply @lt_of_lt_of_le _ _ _ (15 * 2 ^ (4 * 31) + 2 ^ (4 * 31)),
    apply add_lt_add_of_le_of_lt _ nibbles_high_lt,
    apply mul_le_mul_right',
    apply nat.le_of_lt_succ nfirst_nibble_lt,
    norm_num },
  split,
  { rw [←h_scalar_high_eq, scalar_high_eq] },
  use [hres],
  rw [hreseq, hpt3_eq, hpt2_eq, hpt1_eq, hpt0_eq, hpoint_low_eq, hpoint_last_nibble_eq, smul_smul,
    smul_smul, smul_smul, smul_smul, ←add_smul],
  congr' 1, norm_num, ring
end

/-
-- Function: try_get_point_from_x
-/

def ibeta : bigint3 := ⟨BETA0, BETA1, BETA2⟩

lemma ibeta_bdd : ibeta.bounded BASE :=
begin
  dsimp [ibeta, bigint3.bounded, BASE, BETA0, BETA1, BETA2],
  simp only [nat.cast_pow], simp_int_casts,
  norm_num [abs_of_nonneg]
end

lemma ibeta_val_eq : ibeta.val = BETA :=
by { simp [ibeta, bigint3.val, BETA], ring }

-- You may change anything in this definition except the name and arguments.
def spec_try_get_point_from_x (mem : F → F) (κ : ℕ) (range_check_ptr : F) (x : BigInt3 mem) (v : F) (result : π_EcPoint mem) (ρ_range_check_ptr ρ_is_on_curve : F) : Prop :=
  ∀ (secpF : Type) [hsecp : secp_field secpF],  by exactI
    x ≠ ⟨0, 0, 0⟩ →
  ∀ ix : bigint3,
    ix.bounded' D2_BOUND →
    x = ix.toBigInt3 →
    (ρ_is_on_curve = 1 ∧
      ∃ nv : ℕ,
        nv < rc_bound F ∧
        v = ↑nv ∧
      ∃ iyval : ℕ,
        iyval < secp_p ∧
        nv % 2 = iyval % 2 ∧
      ∃ h : @on_ec secpF _ (ix.val, iyval),
      ∃ hres : BddECPointData secpF (cast_EcPoint mem result),
        hres.toECPoint = ECPoint.AffinePoint ⟨_, _, h⟩) ∨
    (ρ_is_on_curve = 0 ∧
      ∀ iy : ℤ, ¬ @on_ec secpF _ (ix.val, iy))

/- try_get_point_from_x autogenerated specification -/

-- Do not change this definition.
def auto_spec_try_get_point_from_x (mem : F → F) (κ : ℕ) (range_check_ptr : F) (x : BigInt3 mem) (v : F) (result : π_EcPoint mem) (ρ_range_check_ptr ρ_is_on_curve : F) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F), spec_assert_nn mem κ₁ range_check_ptr v range_check_ptr₁ ∧
  ∃ (κ₂ : ℕ) (x_square : UnreducedBigInt3 mem), spec_unreduced_sqr mem κ₂ x x_square ∧
  ∃ (κ₃ : ℕ) (range_check_ptr₂ : F) (x_square_reduced : BigInt3 mem), spec_reduce mem κ₃ range_check_ptr₁ x_square range_check_ptr₂ x_square_reduced ∧
  ∃ (κ₄ : ℕ) (x_cube : UnreducedBigInt3 mem), spec_unreduced_mul mem κ₄ x x_square_reduced x_cube ∧
  ∃ (κ₅ : ℕ) (range_check_ptr₃ : F) (y : BigInt3 mem), spec_nondet_bigint3 mem κ₅ range_check_ptr₂ range_check_ptr₃ y ∧
  ∃ (κ₆ : ℕ) (y_square : UnreducedBigInt3 mem), spec_unreduced_sqr mem κ₆ y y_square ∧
  ∃ is_on_curve : F,
  ((is_on_curve ≠ 0 ∧
    ∃ (κ₇ : ℕ) (range_check_ptr₄ : F), spec_validate_reduced_field_element mem κ₇ range_check_ptr₃ y range_check_ptr₄ ∧
    ∃ (κ₈ : ℕ) (range_check_ptr₅ : F), spec_assert_nn mem κ₈ range_check_ptr₄ ((y.d0 + v) / (2 : ℤ)) range_check_ptr₅ ∧
    ∃ (κ₉ : ℕ) (range_check_ptr₆ : F), spec_verify_zero mem κ₉ range_check_ptr₅ {
      d0 := x_cube.d0 + ALPHA * x.d0 + BETA0 - y_square.d0,
      d1 := x_cube.d1 + ALPHA * x.d1 + BETA1 - y_square.d1,
      d2 := x_cube.d2 + ALPHA * x.d2 + BETA2 - y_square.d2
    } range_check_ptr₆ ∧
    cast_EcPoint mem result = {
      x := x,
      y := y
    } ∧
    κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + κ₈ + κ₉ + 70 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr₆ ∧
    ρ_is_on_curve = 1) ∨
   (is_on_curve = 0 ∧
    ∃ (κ₇ : ℕ) (range_check_ptr₄ : F), spec_verify_zero mem κ₇ range_check_ptr₃ {
      d0 := x_cube.d0 + ALPHA * x.d0 + BETA0 + y_square.d0,
      d1 := x_cube.d1 + ALPHA * x.d1 + BETA1 + y_square.d1,
      d2 := x_cube.d2 + ALPHA * x.d2 + BETA2 + y_square.d2
    } range_check_ptr₄ ∧
    κ₁ + κ₂ + κ₃ + κ₄ + κ₅ + κ₆ + κ₇ + 55 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr₄ ∧
    ρ_is_on_curve = 0))

/- try_get_point_from_x soundness theorem -/

theorem try_get_aux' {a b c : ℕ} (h : a + b = 2 * c) : a % 2 = b % 2 :=
begin
  have : a + 2 * b = 2 * c + b,
  { nth_rewrite 0 (two_mul b),
    rw [←add_assoc, h] },
  have h' := congr_arg (λ n : ℕ, n % 2) this,
  dsimp at h',
  rw [nat.add_mul_mod_self_left, add_comm, nat.add_mul_mod_self_left] at h',
  exact h'
end

theorem try_get_aux'' (secpF : Type) [secp_field secpF]
    (iy ix : ℤ) (h : -(↑(iy ^ 2) : secpF) = ↑(ix ^ 3 + ALPHA * ix + BETA)) :
  ∀ iy' : ℤ, ¬ @on_ec secpF _ (ix, iy') :=
begin
  intro iy',
  rw [on_ec], simp at h |-,
  rw [←h, ←int.cast_pow, ←int.cast_pow, ←int.cast_neg, char_p.int_cast_eq_int_cast secpF secp_p],
  rw [←char_p.int_cast_eq_int_cast (zmod secp_p) secp_p, int.cast_neg, int.cast_pow,
    int.cast_pow],
  have : secp_p ≠ 0,
  { rw [secp_p, P0, P1, P2, BASE], norm_num },
  haveI : fact (nat.prime secp_p) :=
    ⟨or.resolve_right (char_p.char_is_prime_or_zero secpF secp_p) this⟩,
  have : (↑iy : zmod secp_p) ≠ 0,
  { rw [ne, char_p.int_cast_eq_zero_iff (zmod secp_p) secp_p,
      ←char_p.int_cast_eq_zero_iff secpF secp_p],
    intro h',
    simp [h'] at h,
    apply @ec_field.ec_no_zero secpF _ ↑ix,
    rw [add_assoc] at h,
    rw [eq_sub_of_add_eq h.symm], simp [ALPHA], abel },
  intro h,
  apply zmod.mod_four_ne_three_of_sq_eq_neg_sq' this h,
  rw [secp_p, P0, P1, P2, BASE],
  norm_num
end

theorem try_get_aux {F : Type} (secpF : Type) {ix : bigint3}
  {k0 k1 k2 k3 k4 k5 k6 k7 k8 : ℕ}
  [field F]
  [decidable_eq F]
  [prelude_hyps F]
  {mem : F → F}
  {range_check_ptr : F}
  {x : BigInt3 mem}
  {v : F}
  {result : π_EcPoint mem}
  [hsecp : secp_field secpF]
  (xnez : x ≠ {d0 := 0, d1 := 0, d2 := 0})
  (ixbdd : ix.bounded' ↑D2_BOUND)
  (xeq : x = ix.toBigInt3)
  {rc0 : F}
  (h_nn_v : spec_assert_nn mem k0 range_check_ptr v rc0)
  {x_square : UnreducedBigInt3 mem}
  (h_x_square : spec_unreduced_sqr mem k1 x x_square)
  {rc1 : F}
  {x_square_reduced : BigInt3 mem}
  (h_x_square_reduced : spec_reduce mem k2 rc0 x_square rc1 x_square_reduced)
  {x_cube : UnreducedBigInt3 mem}
  (h_x_cube : spec_unreduced_mul mem k3 x x_square_reduced x_cube)
  {rc2 : F}
  {y : BigInt3 mem}
  (h_nondet_bigint3_y : spec_nondet_bigint3 mem k4 rc1 rc2 y)
  {y_square : UnreducedBigInt3 mem}
  (h_unreduced_y_square : spec_unreduced_sqr mem k5 y y_square)
  {rc3 : F}
  (h_validate_reduced_y : spec_validate_reduced_field_element mem k6 rc2 y rc3)
  {rc5 : F}
  (h_nn_y_v_div : spec_assert_nn mem k7 rc3 ((y.d0 + v) / ↑(2 : ℤ)) rc5)
  {rc4 : F}
  (h_verify_zero : spec_verify_zero mem k8 rc5 {d0 := x_cube.d0 + ALPHA * x.d0 + ↑BETA0 - y_square.d0, d1 := x_cube.d1 + ALPHA * x.d1 + ↑BETA1 - y_square.d1, d2 := x_cube.d2 + ALPHA * x.d2 + ↑BETA2 - y_square.d2} rc4)
  (result_eq : cast_EcPoint mem ↑result = {x := x, y := y}) :
       ∃ (nv : ℕ),
         nv < rc_bound F ∧
           v = ↑nv ∧
             ∃ (iyval : ℕ),
               iyval < secp_p ∧
                 nv % 2 = iyval % 2 ∧
                   ∃ (h : on_ec (↑(ix.val), ↑iyval))
                     (hres : BddECPointData secpF (cast_EcPoint mem ↑result)),
                     hres.toECPoint =
                       ECPoint.AffinePoint
                         {x := ↑(ix.val), y := ↑iyval, h := h} :=
begin
  rcases h_nn_v with ⟨nv, nvlt, veq⟩,
  have x_square_eq := h_x_square ix xeq,
  have : ix.sqr.bounded (2^250 - 8 * D2_BOUND),
  { apply bigint3.bounded_of_bounded_of_le
      (bigint3.bounded_sqr ixbdd),
    rw [D2_BOUND], simp_int_casts, norm_num },
  rcases h_x_square_reduced ix.sqr this x_square_eq with
    ⟨ixsqr', ixsqr'bdd, hixsqr', x_square_reduced_eq⟩,
  have x_cube_eq := h_x_cube ix ixsqr' xeq x_square_reduced_eq,
  rcases nondet_bigint3_corr h_nondet_bigint3_y with ⟨iy, yeq, iybdd⟩,
  rcases h_validate_reduced_y with ⟨n0, n1, n2, n0le, n1le, n2le, yvallt, yeq'⟩,
  rcases h_nn_y_v_div with ⟨nydiv, nydivlt, ydiveq⟩,
  have : y.d0 + v = ↑(2 * nydiv),
  { rw [mul_comm, nat.cast_mul],
    symmetry, simp,
    rw [← (eq_div_iff (PRIME.two_ne_zero F)), ← ydiveq],
    simp },
  have : n0 + nv = 2 * nydiv,
  { rw [yeq', veq, ← nat.cast_add] at this,
    apply nat.cast_inj_of_lt_char _ _ this,
    apply lt_of_le_of_lt (add_le_add n0le (le_of_lt nvlt)),
    apply lt_of_le_of_lt (add_le_add_left (rc_bound_hyp F) _),
    rw [BASE, PRIME.char_eq, PRIME],
    norm_num,
    apply lt_of_le_of_lt,
    apply nat.mul_le_mul_left 2
      (le_trans (le_of_lt nydivlt) (rc_bound_hyp F)),
    rw [PRIME.char_eq, PRIME], norm_num },
  have n02eqmv2 : n0 % 2 = nv % 2 := try_get_aux' this,
  let  iy' : bigint3 := ⟨n0, n1, n2⟩,
  have iy'bdd : iy'.bounded' D2_BOUND,
  { simp only [bigint3.bounded', nat.abs_cast],
    split,
    { rw [←int.coe_nat_le_coe_nat_iff] at n0le,
      apply le_trans n0le,
      rw [BASE, D2_BOUND], norm_num1, simp_int_casts, norm_num1 },
    split,
    { rw [←int.coe_nat_le_coe_nat_iff] at n1le,
      apply le_trans n1le,
      rw [BASE, D2_BOUND], norm_num1, simp_int_casts, norm_num1 },
    rw [←int.coe_nat_le_coe_nat_iff] at n2le,
    apply le_trans n2le,
    rw [P2, D2_BOUND, int.coe_nat_pow], simp_int_casts, norm_num1 },
  have yeq'' : y = iy'.toBigInt3,
  { rw [yeq', bigint3.toBigInt3], dsimp [iy'],
    simp only [int.cast_coe_nat, eq_self_iff_true, and_self] },
  have y_square_eq := h_unreduced_y_square iy' yeq'',
  let idiff := (((ix.mul ixsqr').add (ix.cmul ALPHA)).add ibeta).sub iy'.sqr,
  have hidiff1 : idiff.toUnreducedBigInt3 = ⟨x_cube.d0 + ALPHA * x.d0 + BETA0 - y_square.d0,
      x_cube.d1 + ALPHA * x.d1 + BETA1 - y_square.d1, x_cube.d2 + ALPHA * x.d2 + BETA2 - y_square.d2⟩,
  {  simp only [idiff, ibeta, bigint3.toUnreducedBigInt3_add, bigint3.toUnreducedBigInt3_sub, x_cube_eq, y_square_eq, xeq],
    simp only [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, UnreducedBigInt3.add, UnreducedBigInt3.sub,
      bigint3.cmul, int.cast_mul],
    exact ⟨rfl, rfl, rfl⟩ },
  have hidiff2 : idiff.bounded (2 ^ 250),
  { suffices : idiff.bounded ((D2_BOUND^2 * BOUND') + (abs ALPHA * (8 * D2_BOUND)) + BASE +
      (D2_BOUND^2 * BOUND')),
    { apply bigint3.bounded_of_bounded_of_le this,
     rw [D2_BOUND, BOUND', BASE], simp_int_casts, norm_num [abs_of_nonneg] },
    apply bigint3.bounded_sub,
    apply bigint3.bounded_add,
    apply bigint3.bounded_add,
    apply bigint3.bounded_mul ixbdd ixsqr'bdd,
    apply bigint3.bounded_cmul (bigint3.bounded_of_bounded' ixbdd),
    { simp [ibeta, bigint3.bounded, BETA0, BETA1, BETA2],
      norm_num [abs_of_nonneg] },
    apply bigint3.bounded_sqr iy'bdd },
  have := h_verify_zero idiff hidiff1.symm hidiff2,
  have h_on_ec : on_ec ((ix.val : secpF), iy'.val),
  { simp [on_ec],
    suffices : (↑(iy'.val ^ 2) : secpF) = ↑(ix.val ^ 3 + ALPHA * ix.val + BETA),
    { simpa using this },
    rw [char_p.int_cast_eq_int_cast secpF secp_p, int.modeq],
    symmetry,
    rw [int.mod_eq_mod_iff_mod_sub_eq_zero, ←this],
    dsimp [idiff],
    rw [bigint3.sub_val, bigint3.add_val, bigint3.add_val],
    apply int.modeq.sub,
    apply int.modeq.add,
    apply int.modeq.add,
    rw [pow_succ],
    apply int.modeq.symm,
    apply int.modeq.trans,
    apply bigint3.mul_val,
    apply int.modeq.mul_left,
    apply int.modeq.trans hixsqr',
    apply bigint3.sqr_val,
    rw [bigint3.cmul_val],
    rw [ibeta_val_eq],
    apply int.modeq.symm,
    apply bigint3.sqr_val },
  have iy'valeq : (↑(n2 * BASE ^ 2 + n1 * BASE + n0) : secpF) = iy'.val,
  { dsimp [iy'], simp [bigint3.val] },
  use [nv, nvlt, veq, n2 * BASE ^ 2 + n1 * BASE + n0, yvallt],
  split,
  { rw [←n02eqmv2, nat.add_mod, nat.add_mod (n2 * _), nat.mul_mod, BASE],
    norm_num,
    rw [nat.add_mod, nat.mul_mod],
    norm_num },
  rw iy'valeq,
  use h_on_ec,
  rw result_eq,
  use (⟨ix, iy', ixbdd, iy'bdd, xeq, yeq'', or.inr h_on_ec⟩ : BddECPointData secpF {x := x, y := y}),
  simp [BddECPointData.toECPoint, dif_neg xnez]
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_try_get_point_from_x
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (x : BigInt3 mem) (v : F) (result : π_EcPoint mem) (ρ_range_check_ptr ρ_is_on_curve : F)
    (h_auto : auto_spec_try_get_point_from_x mem κ range_check_ptr x v result ρ_range_check_ptr ρ_is_on_curve) :
  spec_try_get_point_from_x mem κ range_check_ptr x v result ρ_range_check_ptr ρ_is_on_curve :=
begin
  intros secpF _,
  resetI,
  intros xnez ix ixbdd xeq,
  rcases h_auto with
    ⟨_, _, h_nn_v,
    _, x_square, h_x_square,
    _, _, x_square_reduced, h_x_square_reduced,
    _, x_cube, h_x_cube,
    _, _, y, h_nondet_bigint3_y,
    _, y_square, h_unreduced_y_square,
    is_on_curve, hcurve⟩,
  have x_square_eq := h_x_square ix xeq,
  have : ix.sqr.bounded (2^250 - 8 * D2_BOUND),
  { apply bigint3.bounded_of_bounded_of_le
      (bigint3.bounded_sqr ixbdd),
    rw [D2_BOUND], simp_int_casts, norm_num },
  rcases h_x_square_reduced ix.sqr this x_square_eq with
    ⟨ixsqr', ixsqr'bdd, hixsqr', x_square_reduced_eq⟩,
  have x_cube_eq := h_x_cube ix ixsqr' xeq x_square_reduced_eq,
  rcases nondet_bigint3_corr h_nondet_bigint3_y with ⟨iy, yeq, iybdd⟩,
  have y_square_eq := h_unreduced_y_square iy yeq,
  rcases hcurve with h_is_on_curve | h_is_not_on_curve,
  { left,
    rcases h_is_on_curve with
      ⟨is_on_curve_ne,
        _, _, h_validate_reduced_y,
        _, _, h_nn_y_v_div,
        _, _, h_verify_zero,
        result_eq,
        _, _, ρ_is_on_curve_eq⟩,
    use [ρ_is_on_curve_eq],
    exact try_get_aux secpF xnez ixbdd xeq h_nn_v h_x_square h_x_square_reduced h_x_cube h_nondet_bigint3_y h_unreduced_y_square h_validate_reduced_y h_nn_y_v_div h_verify_zero result_eq },
  right,
  rcases h_is_not_on_curve with
    ⟨_, _, _, h_verify_zero,
      _, _, ρ_is_on_curve_eq⟩,
  let idiff := (((ix.mul ixsqr').add (ix.cmul ALPHA)).add ibeta).add iy.sqr,
  have hidiff1 : idiff.toUnreducedBigInt3 = ⟨x_cube.d0 + ALPHA * x.d0 + BETA0 + y_square.d0,
      x_cube.d1 + ALPHA * x.d1 + BETA1 + y_square.d1, x_cube.d2 + ALPHA * x.d2 + BETA2 + y_square.d2⟩,
  {  simp only [idiff, ibeta, bigint3.toUnreducedBigInt3_add, x_cube_eq, y_square_eq, xeq],
    simp only [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, UnreducedBigInt3.add, UnreducedBigInt3.sub,
      bigint3.cmul, int.cast_mul],
    exact ⟨rfl, rfl, rfl⟩ },
  have hidiff2 : idiff.bounded (2 ^ 250),
  { suffices : idiff.bounded ((D2_BOUND^2 * BOUND') + (abs ALPHA * (8 * D2_BOUND)) + BASE +
      (D2_BOUND^2 * BOUND')),
    { apply bigint3.bounded_of_bounded_of_le this,
     rw [D2_BOUND, BOUND', BASE], simp_int_casts, norm_num [abs_of_nonneg] },
    apply bigint3.bounded_add,
    apply bigint3.bounded_add,
    apply bigint3.bounded_add,
    apply bigint3.bounded_mul ixbdd ixsqr'bdd,
    apply bigint3.bounded_cmul (bigint3.bounded_of_bounded' ixbdd),
    { simp [ibeta, bigint3.bounded, BETA0, BETA1, BETA2],
      norm_num [abs_of_nonneg] },
    apply bigint3.bounded_sqr iybdd },
  have := h_verify_zero idiff hidiff1.symm hidiff2,
  use ρ_is_on_curve_eq,
  apply try_get_aux'' secpF iy.val ix.val,
  apply neg_eq_of_add_eq_zero_left,
  rw [←int.cast_add, ←int.cast_zero],
  rw [char_p.int_cast_eq_int_cast secpF secp_p, int.modeq],
  rw [int.zero_mod, ←this],
  dsimp [idiff],
  rw [bigint3.add_val, bigint3.add_val, bigint3.add_val],
  apply int.modeq.add,
  apply int.modeq.add,
  apply int.modeq.add,
  rw [pow_succ],
  apply int.modeq.symm,
  apply int.modeq.trans,
  apply bigint3.mul_val,
  apply int.modeq.mul_left,
  apply int.modeq.trans hixsqr',
  apply bigint3.sqr_val,
  rw [bigint3.cmul_val],
  rw [ibeta_val_eq],
  apply int.modeq.symm,
  apply bigint3.sqr_val
end

end starkware.cairo.common.secp256r1.ec
