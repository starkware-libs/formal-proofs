/-
  Specifications file for ec_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.cairo_secp.bigint_spec
import starkware.cairo.common.cairo_secp.field_spec
import starkware.cairo.common.cairo_secp.constants_spec

import starkware.cairo.common.cairo_secp.bigint3_spec
import starkware.cairo.common.cairo_secp.ec_point_spec

-- JDA: Additional import.
import starkware.cairo.common.cairo_secp.elliptic_curves

open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.cairo_secp.ec_point

open starkware.cairo.common.cairo_secp.bigint
open starkware.cairo.common.cairo_secp.field
open starkware.cairo.common.cairo_secp.constants

namespace starkware.cairo.common.cairo_secp.ec

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

-- End of main scope definitions.

/-
-- Data for writing the specifications.
-/

structure BddECPointData {mem : F → F} (secpF : Type*) [field secpF] (pt : EcPoint mem) :=
(ix iy : bigint3)
(ixbdd : ix.bounded (3 * BASE - 1))
(iybdd : iy.bounded (3 * BASE - 1))
(ptxeq : pt.x = ix.toBigInt3)
(ptyeq : pt.y = iy.toBigInt3)
(onEC : pt.x = ⟨0, 0, 0⟩ ∨ (iy.val : secpF)^2 = (ix.val : secpF)^3 + 7)

theorem BddECPointData.onEC' {mem : F → F} {secpF : Type*} [field secpF] {pt : EcPoint mem}
    (h : BddECPointData secpF pt) (h' : pt.x ≠ ⟨0, 0, 0⟩) :
  (h.iy.val : secpF)^2 = (h.ix.val : secpF)^3 + 7 :=
or.resolve_left h.onEC h'

section secpF

variables
  {secpF : Type}   -- in practice, zmod SECP_PRIME
  [field secpF]    -- in practice, @zmod.field _ ⟨prime_secp⟩
  [char_p secpF SECP_PRIME]
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
  ixbdd := by simp [bigint3.bounded]; norm_num1,
  iybdd := by simp [bigint3.bounded]; norm_num1,
  ptxeq := by simp [bigint3.toBigInt3],
  ptyeq := by simp [bigint3.toBigInt3],
  onEC := or.inl rfl }

end secpF

def SECP_LOG2_BOUND := 100

class secp_field (secpF : Type*) extends ec_field secpF, char_p secpF SECP_PRIME :=
(seven_not_square : ∀ y : secpF, y^2 ≠ 7)
(neg_seven_not_cube : ∀ x : secpF, x^3 ≠ -7)
(order_large : ∀ {pt : ECPoint secpF}, pt ≠ 0 →
                 ∀ {n : ℕ}, n ≠ 0 → n < 2^(SECP_LOG2_BOUND + 1) + 2 → n • pt ≠ 0)

theorem secp_field.order_large_corr {secpF : Type*} [secp_field secpF]
  {pt : ECPoint secpF} (ptnz : pt ≠ 0) :
    ∀ {n : ℕ}, n < 2^SECP_LOG2_BOUND → ¬ ((n * 2) • pt = pt ∨ (n * 2) • pt = -pt) :=
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
    { apply nat.succ_ne_zero },
    apply lt_of_lt_of_le,
    apply add_lt_add_right,
    apply lt_of_le_of_lt,
    apply mul_le_mul_of_nonneg_right,
    apply le_of_lt,
    apply lt_trans (nat.lt_succ_self _) nlt,
    norm_num,
    apply nat.lt_succ_self,
    norm_num [SECP_LOG2_BOUND],
  },
  rw [eq_neg_iff_add_eq_zero, ← one_smul _ pt, smul_smul (n * 2) 1, ← add_smul] at h,
  revert h,
  apply secp_field.order_large ptnz,
  { apply nat.succ_ne_zero },
  rw [mul_assoc, mul_one],
  apply lt_trans,
  change (_ < 2^SECP_LOG2_BOUND * 2 + 1),
  apply add_lt_add_right,
  apply mul_lt_mul_of_pos_right nlt,
  norm_num, norm_num [SECP_LOG2_BOUND]
end

theorem secp_field.y_ne_zero_of_on_ec  {secpF : Type*} [secp_field secpF] {x y : secpF}
  (h : on_ec (x, y)) : y ≠ 0 :=
by { contrapose! h, simp [on_ec, h, ←sub_eq_iff_eq_add],
     apply ne.symm, apply secp_field.neg_seven_not_cube }

theorem secp_field.x_ne_zero_of_on_ec {secpF : Type*} [secp_field secpF] {x y : secpF}
  (h : on_ec (x, y)) : x ≠ 0 :=
by { contrapose! h, simp [on_ec, h, secp_field.seven_not_square] }

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
    simp [or.resolve_left this ec_field.two_ne_zero] at h_on_ec,
    apply secp_field.neg_seven_not_cube x.x,
    exact eq_neg_iff_add_eq_zero.mpr h_on_ec.symm },
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
    rw toBigInt3_eq_zero_of_bounded_3BASE heq h.ixbdd,
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
    rw toBigInt3_eq_zero_of_bounded_3BASE heq h.ixbdd,
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


/-
-- Function: ec_negate
-/

/- ec_negate autogenerated specification -/

-- Do not change this definition.
def auto_spec_ec_negate (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_point : EcPoint mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (minus_y : BigInt3 mem), spec_nondet_bigint3 mem κ₁ range_check_ptr range_check_ptr₁ minus_y ∧
  ∃ (κ₂ : ℕ) (range_check_ptr₂ : F), spec_verify_zero mem κ₂ range_check_ptr₁ {
    d0 := minus_y.d0 + point.y.d0,
    d1 := minus_y.d1 + point.y.d1,
    d2 := minus_y.d2 + point.y.d2
  } range_check_ptr₂ ∧
  κ₁ + κ₂ + 14 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₂ ∧
  ρ_point = {
    x := point.x,
    y := minus_y
  }

-- You may change anything in this definition except the name and arguments.
def spec_ec_negate (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_point : EcPoint mem) : Prop :=
  ∀ ix iy : bigint3,
    ix.bounded (3 * BASE - 1) →
    iy.bounded (3 * BASE - 1) →
    point.x = ix.toBigInt3 →
    point.y = iy.toBigInt3 →
    ∃ ineg_y : bigint3,
      ineg_y.bounded (3 * (BASE - 1)) ∧
      ρ_point = { x := ix.toBigInt3, y := ineg_y.toBigInt3 } ∧
      ineg_y.val ≡ - iy.val [ZMOD SECP_PRIME]

/- ec_negate soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_ec_negate
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_point : EcPoint mem)
    (h_auto : auto_spec_ec_negate mem κ range_check_ptr point ρ_range_check_ptr ρ_point) :
  spec_ec_negate mem κ range_check_ptr point ρ_range_check_ptr ρ_point :=
begin
  intros ix iy ixbdd iybdd ptxeq ptyeq,
  rcases h_auto with ⟨_, _, neg_y, hneg_y, _, _, hverify_zero, _, _, ρ_point_eq⟩,
  rcases nondet_bigint3_corr hneg_y with ⟨ineg_y, neg_y_eq, ineg_y_bdd⟩,
  use [ineg_y, ineg_y_bdd],
  split, { rw [ρ_point_eq, ptxeq, neg_y_eq] },
  rw [int.modeq_iff_sub_mod_eq_zero, sub_neg_eq_add, ←bigint3.add_val],
  apply hverify_zero,
  { simp [ptyeq, neg_y_eq, bigint3.add, bigint3.toUnreducedBigInt3, bigint3.toBigInt3] },
  apply bigint3.bounded_of_bounded_of_le,
  apply bigint3.bounded_add ineg_y_bdd iybdd,
  dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1
end

/- Better specification. -/

def spec_ec_negate' {mem : F → F} ( pt : EcPoint mem ) ( ret : EcPoint mem )
    (secpF : Type) [secp_field secpF] : Prop :=
  ∀ h : BddECPointData secpF pt,
    ∃ hret : BddECPointData secpF ret,
      hret.toECPoint = -h.toECPoint

theorem spec_ec_negate'_of_spec_ec_negate
    {mem : F → F} {κ : ℕ} {range_check_ptr : F} {pt : EcPoint mem} {ret0 : F} {ret : EcPoint mem}
    (h : spec_ec_negate mem κ range_check_ptr pt ret0 ret)
    (secpF : Type) [secp_field secpF] :
  spec_ec_negate' pt ret secpF :=
begin
  intro hpt,
  rcases h hpt.ix hpt.iy hpt.ixbdd hpt.iybdd hpt.ptxeq hpt.ptyeq with ⟨ineg_y, ineg_y_bdd, reteq, hineg_y⟩,
  have inegyvaleq : (ineg_y.val : secpF) = - (hpt.iy.val : secpF),
  { rw [←int.cast_neg, char_p.int_cast_eq_int_cast secpF SECP_PRIME],
    exact hineg_y },
  rw EcPoint.ext_iff at reteq,
  have retx_eq_ptx : ret.x = pt.x := reteq.1.trans (hpt.ptxeq.symm),
  let hret : BddECPointData secpF ret :=
  { ix := hpt.ix,
    iy := ineg_y,
    ixbdd := hpt.ixbdd,
    iybdd := bigint3.bounded_of_bounded_of_le ineg_y_bdd bound_slack,
    ptxeq := reteq.1,
    ptyeq := reteq.2,
    onEC :=
      begin
        cases hpt.onEC with h' h',
        { exact or.inl (retx_eq_ptx.trans h') },
        right, rw [inegyvaleq, neg_sq, h']
      end },
  use hret,
  simp [BddECPointData.toECPoint],
  by_cases h' : pt.x = ⟨0, 0, 0⟩,
  { rw [dif_pos h', dif_pos (retx_eq_ptx.trans h')],
    refl },
  rw [dif_neg h', dif_neg (ne_of_eq_of_ne retx_eq_ptx h')],
  simp [ECPoint.neg_def, ECPoint.neg, inegyvaleq]
end

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
    d0 := 3 * x_sqr.d0 - 2 * slope_y.d0,
    d1 := 3 * x_sqr.d1 - 2 * slope_y.d1,
    d2 := 3 * x_sqr.d2 - 2 * slope_y.d2
  } range_check_ptr₂ ∧
  κ₁ + κ₂ + κ₃ + κ₄ + 34 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₂ ∧
  ρ_slope = slope

-- You may change anything in this definition except the name and arguments.
def spec_compute_doubling_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∀ ix iy : bigint3,
    ix.bounded (3 * BASE - 1) →
    iy.bounded (3 * BASE - 1) →
    point.x = ix.toBigInt3 →
    point.y = iy.toBigInt3 →
    ∃ is : bigint3,
      is.bounded (3 * (BASE - 1)) ∧
      ρ_slope = is.toBigInt3 ∧
      3 * ix.val^2 ≡ 2 * iy.val * is.val [ZMOD SECP_PRIME]

/- compute_doubling_slope soundness theorem -/

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
  set diff : bigint3 := (ix.sqr.cmul 3).sub ((iy.mul is).cmul 2) with diff_eq,
  have diff_bdd : diff.bounded (5 * ((3 * BASE - 1)^2 * (8 * SECP_REM + 1))),
  { rw [diff_eq, (show (5 : ℤ) = 3 + 2, by norm_num), add_mul],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_cmul' (show (0 : ℤ) ≤ 3, by norm_num1),
    apply bigint3.bounded_sqr ixbdd,
    apply bigint3.bounded_cmul' (show (0 : ℤ) ≤ 2, by norm_num1),
    apply bigint3.bounded_mul iybdd,
    apply bigint3.bounded_of_bounded_of_le isbdd bound_slack },
  have : diff.val % SECP_PRIME = 0,
  { apply vz,
    { simp only [diff_eq, x_sqr_eq, slope_y_eq],
      dsimp [bigint3.toUnreducedBigInt3, bigint3.sqr, bigint3.mul, bigint3.cmul, bigint3.sub],
      simp_int_casts,
      split, ring,
      split, ring, ring },
      apply bigint3.bounded_of_bounded_of_le diff_bdd,
      dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
  symmetry,
  rw [int.modeq_iff_dvd, int.dvd_iff_mod_eq_zero, ←this, diff_eq, bigint3.sub_val,
    bigint3.cmul_val, bigint3.cmul_val],
  apply int.modeq.sub,
  apply int.modeq.mul_left,
  apply int.modeq.symm,
  apply bigint3.sqr_val,
  rw mul_assoc,
  apply int.modeq.mul_left,
  apply int.modeq.symm,
  apply bigint3.mul_val
end

/-
-- Function: compute_slope
-/

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

-- You may change anything in this definition except the name and arguments.
def spec_compute_slope (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_slope : BigInt3 mem) : Prop :=
  ∀ ix0 iy0 ix1 iy1 : bigint3,
    ix0.bounded (3 * BASE - 1) →
    iy0.bounded (3 * BASE - 1) →
    ix1.bounded (3 * BASE - 1) →
    iy1.bounded (3 * BASE - 1) →
    point0.x = ix0.toBigInt3 →
    point0.y = iy0.toBigInt3 →
    point1.x = ix1.toBigInt3 →
    point1.y = iy1.toBigInt3 →
    ∃ is : bigint3,
      is.bounded (3 * (BASE - 1)) ∧
      ρ_slope = is.toBigInt3 ∧
      (ix0.val - ix1.val) * is.val ≡ (iy0.val - iy1.val) [ZMOD SECP_PRIME]


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
    (((3 * BASE - 1) + (3 * BASE - 1))^2 * (8 * SECP_REM + 1) +  ((3 * BASE - 1) + (3 * BASE - 1))),
  { rw [diff_eq],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_mul,
    apply bigint3.bounded_sub ix0bdd ix1bdd,
    apply bigint3.bounded_of_bounded_of_le isbdd,
    unfold BASE, simp_int_casts, norm_num1,
    apply bigint3.bounded_sub iy0bdd iy1bdd },
  have : diff.val % SECP_PRIME = 0,
  { apply vz,
    { simp only [diff_eq, x_diff_slope_eq, ix_diff_eq, pt0xeq, pt1xeq, pt0yeq, pt1yeq],
      dsimp [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, bigint3.mul, bigint3.sub], simp [←sub_add] },
    apply bigint3.bounded_of_bounded_of_le diff_bdd,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
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

/-
-- Function: ec_double
-/

/- ec_double autogenerated specification -/

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

-- You may change anything in this definition except the name and arguments.
def spec_ec_double (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  (point.x = ⟨0, 0, 0⟩ ∧ ρ_res = point) ∨
  (point.x ≠ ⟨0, 0, 0⟩ ∧
    ∀ ix iy : bigint3,
    ix.bounded (3 * BASE - 1) →
    iy.bounded (3 * BASE - 1) →
    point.x = ix.toBigInt3 →
    point.y = iy.toBigInt3 →
    ∃ is inew_x inew_y : bigint3,
      is.bounded (3 * (BASE - 1)) ∧
      inew_x.bounded (3 * (BASE - 1)) ∧
      inew_y.bounded (3 * (↑BASE - 1)) ∧
      ρ_res = { x := inew_x.toBigInt3, y := inew_y.toBigInt3 } ∧
      3 * ix.val^2 ≡ 2 * iy.val * is.val [ZMOD SECP_PRIME] ∧
      inew_x.val ≡ is.val^2 - 2 * ix.val [ZMOD SECP_PRIME] ∧
      inew_y.val ≡ (ix.val - inew_x.val) * is.val - iy.val [ZMOD SECP_PRIME])

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
  have diff1_bdd : diff1.bounded
    ((3 * (BASE - 1))^2 * (8 * SECP_REM + 1) + 3 * (BASE - 1) + 2 * (3 * BASE - 1)),
  { rw [diff1_eq],
    apply bigint3.bounded_sub,
    apply bigint3.bounded_sub _ inew_x_bdd,
    apply bigint3.bounded_mul isbdd isbdd,
    apply bigint3.bounded_cmul ixbdd },
  have diff1_equiv : diff1.val % SECP_PRIME = 0,
  { apply vz,
    { simp only [diff1_eq, islope_sqr_eq, ptxeq, inew_x_eq],
      dsimp [bigint3.toUnreducedBigInt3, bigint3.toBigInt3, bigint3.mul, bigint3.sub, bigint3.cmul,
        bigint3.sqr],
      simp only [int.cast_sub, int.cast_mul 2], simp_int_casts,
      split, refl, split, refl, refl },
    apply bigint3.bounded_of_bounded_of_le diff1_bdd,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
  have : (ix.sub inew_x).toBigInt3 =
    { d0 := point.x.d0 - new_x.d0, d1 := point.x.d1 - new_x.d1, d2 := point.x.d2 - new_x.d2 },
  { rw [bigint3.toBigInt3_sub, ←ptxeq, ←inew_x_eq], refl },
  have x_diff_slope_eq := h_x_diff_slope _ _ this.symm slope_eq,
  set diff2 := (((ix.sub inew_x).mul is).sub iy).sub inew_y with diff2_eq,
  have diff2_bdd : diff2.bounded
    (((3 * BASE - 1) + (3 * (BASE - 1)))^2 * (8 * SECP_REM + 1) + (3 * BASE - 1) + 3 * (BASE - 1)),
  { rw [diff2_eq],
    apply bigint3.bounded_sub _ inew_y_bdd,
    apply bigint3.bounded_sub _ iybdd,
    apply bigint3.bounded_mul,
    apply bigint3.bounded_sub ixbdd inew_x_bdd,
    apply bigint3.bounded_of_bounded_of_le isbdd,
    apply le_add_of_nonneg_left,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
  have diff2_equiv : diff2.val % SECP_PRIME = 0,
  { apply vz',
    { simp only [diff2_eq, x_diff_slope_eq, inew_y_eq, bigint3.toBigInt3,
        bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, ptyeq, int.cast_sub],
        split, refl, split, refl, split },
    apply bigint3.bounded_of_bounded_of_le diff2_bdd,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
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
  have eq1 : 3 * (hpt.ix.val : secpF)^2  = 2 * hpt.iy.val * is.val,
  { norm_cast, rw  @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
    apply mod1eq },
  have eq2 : (inew_x.val : secpF) = is.val ^ 2 - 2 * hpt.ix.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
    apply mod2eq },
  have eq3: (inew_y.val : secpF) = (hpt.ix.val - inew_x.val) * is.val - hpt.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
    apply mod3eq },
  have eq1a : (is.val : secpF) = 3 * (hpt.ix.val : secpF)^2 / (2 * hpt.iy.val),
  { field_simp [ec_field.two_ne_zero], rw [mul_comm, eq1] },
  have ecdoubleeq : ec_double ((hpt.ix.val : secpF), hpt.iy.val) = (inew_x.val, inew_y.val),
  { simp [ec_double, ec_double_slope],
    split, rw [eq2, eq1a, div_pow],
    rw [eq3, eq1a], congr, rw [eq2, eq1a, div_pow] },
  have onec_new: on_ec (↑(inew_x.val), ↑(inew_y.val)),
  { have := @on_ec_ec_double secpF _ (↑(hpt.ix.val), ↑(hpt.iy.val)) onec_pt hptynez,
    rw ecdoubleeq at this, exact this },
  have hhret: ¬ (inew_x.i0 = 0 ∧ inew_x.i1 = 0 ∧ inew_x.i2 = 0),
  { contrapose! onec_new,
    rw [on_ec], dsimp,
    conv { congr, to_rhs, simp [bigint3.val, onec_new.1, onec_new.2.1, onec_new.2.2] },
    apply secp_field.seven_not_square },
  let hret : BddECPointData secpF ret1 :=
  { ix    := inew_x,
    iy    := inew_y,
    ixbdd := by apply bigint3.bounded_of_bounded_of_le inew_x_bdd; norm_num [BASE],
    iybdd := by apply bigint3.bounded_of_bounded_of_le inew_y_bdd; norm_num [BASE],
    ptxeq := by { rw ret1eq },
    ptyeq := by { rw ret1eq },
    onEC  := or.inr onec_new },
  use hret,
  have : ret1.x ≠ ⟨0, 0, 0⟩,
  { rw [ret1eq], dsimp,
    have h' := secp_field.x_ne_zero_of_on_ec onec_new,
    contrapose! h',
    have : inew_x = ⟨0, 0, 0⟩ := toBigInt3_eq_zero_of_bounded_3BASE h'
        (bigint3.bounded_of_bounded_of_le inew_x_bdd bound_slack),
    simp [this, bigint3.val] },
  dsimp [BddECPointData.toECPoint], simp [dif_neg ptxnz, dif_neg this],
  symmetry,
  apply double_Affine _ _ ecdoubleeq
end

/-
-- Function: fast_ec_add
-/

/- fast_ec_add autogenerated specification -/

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

-- You may change anything in this definition except the name and arguments.
def spec_fast_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ ix0 iy0 ix1 iy1 : bigint3,
  ix0.bounded (3 * BASE - 1) →
  iy0.bounded (3 * BASE - 1) →
  ix1.bounded (3 * BASE - 1) →
  iy1.bounded (3 * BASE - 1) →
  point0.x = ix0.toBigInt3 →
  point0.y = iy0.toBigInt3 →
  point1.x = ix1.toBigInt3 →
  point1.y = iy1.toBigInt3 →
  (point0.x.d0 = 0 ∧ point0.x.d1 = 0 ∧ point0.x.d2 = 0 ∧ ρ_res = point1) ∨
  (point1.x.d0 = 0 ∧ point1.x.d1 = 0 ∧ point1.x.d2 = 0 ∧ ρ_res = point0) ∨
  ¬ (point0.x.d0 = 0 ∧ point0.x.d1 = 0 ∧ point0.x.d2 = 0) ∧
  ¬ (point1.x.d0 = 0 ∧ point1.x.d1 = 0 ∧ point1.x.d2 = 0) ∧
  ∃ is inew_x inew_y : bigint3,
    is.bounded (3 * (BASE - 1)) ∧
    inew_x.bounded (3 * (BASE - 1)) ∧
    inew_y.bounded (3 * (BASE - 1)) ∧
    ρ_res = { x := inew_x.toBigInt3, y := inew_y.toBigInt3 } ∧
    (ix0.val - ix1.val) * is.val ≡ (iy0.val - iy1.val) [ZMOD SECP_PRIME] ∧
    inew_x.val ≡ is.val^2 - ix0.val - ix1.val [ZMOD SECP_PRIME] ∧
    inew_y.val ≡ (ix0.val - inew_x.val) * is.val - iy0.val [ZMOD SECP_PRIME]

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
    ((3 * (BASE - 1))^2 * (8 * SECP_REM + 1) + 3 * (BASE - 1) + (3 * BASE - 1) + (3 * BASE - 1)),
  { rw [diff1_eq],
    apply bigint3.bounded_sub _ ix1bdd,
    apply bigint3.bounded_sub _ ix0bdd,
    apply bigint3.bounded_sub _ inew_x_bdd,
    apply bigint3.bounded_mul isbdd isbdd },
  have diff1_equiv : diff1.val % SECP_PRIME = 0,
  { apply vz,
    { simp only [diff1_eq, islope_sqr_eq, pt0xeq, pt1xeq, inew_x_eq],
      dsimp [bigint3.toBigInt3, bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, bigint3.cmul,
        bigint3.sqr],
      simp only [int.cast_sub, int.cast_mul 2], simp_int_casts,
      split, refl, split, refl, refl },
    apply bigint3.bounded_of_bounded_of_le diff1_bdd,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
  have : (ix0.sub inew_x).toBigInt3 =
    { d0 := point0.x.d0 - new_x.d0, d1 := point0.x.d1 - new_x.d1, d2 := point0.x.d2 - new_x.d2 },
  { rw [bigint3.toBigInt3_sub, ←pt0xeq, ←inew_x_eq], refl },
  have x_diff_slope_eq := h_x_diff_slope _ _ this.symm slope_eq,
  set diff2 := (((ix0.sub inew_x).mul is).sub iy0).sub inew_y with diff2_eq,
  have diff2_bdd : diff2.bounded
    (((3 * BASE - 1) + (3 * (BASE - 1)))^2 * (8 * SECP_REM + 1) + (3 * BASE - 1) + 3 * (BASE - 1)),
  { rw [diff2_eq],
    apply bigint3.bounded_sub _ inew_y_bdd,
    apply bigint3.bounded_sub _ iy0bdd,
    apply bigint3.bounded_mul,
    apply bigint3.bounded_sub ix0bdd inew_x_bdd,
    apply bigint3.bounded_of_bounded_of_le isbdd,
    apply le_add_of_nonneg_left,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
  have diff2_equiv : diff2.val % SECP_PRIME = 0,
  { apply vz',
    { simp only [diff2_eq, x_diff_slope_eq, inew_y_eq, bigint3.toBigInt3,
        bigint3.toUnreducedBigInt3, bigint3.mul, bigint3.sub, pt0yeq, int.cast_sub],
        split, refl, split, refl, split },
    apply bigint3.bounded_of_bounded_of_le diff2_bdd,
    dsimp only [BASE, SECP_REM], simp_int_casts, norm_num1 },
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
    (↑(h0.ix.val) : secpF) ≠ ↑(h1.ix.val) →
    ∃ hret : BddECPointData secpF ret1,
      hret.toECPoint = h0.toECPoint + h1.toECPoint

theorem spec_fast_ec_add'_of_spec_ec_add
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
      apply bound_lt_prime },
    have ix0i1z: h0.ix.i1 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt0xeq.2.1, pt0x1eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h0.ixbdd.2.1,
      apply bound_lt_prime },
    have ix0i2z: h0.ix.i2 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt0xeq.2.2, pt0x2eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h0.ixbdd.2.2,
      apply bound_lt_prime },
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
      apply bound_lt_prime },
    have ix0i1z: h1.ix.i1 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt1xeq.2.1, pt1x1eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h1.ixbdd.2.1,
      apply bound_lt_prime },
    have ix0i2z: h1.ix.i2 = 0,
    { apply @PRIME.int_coe_inj F,
      rw [←pt1xeq.2.2, pt1x2eq, int.cast_zero],
      simp,
      apply lt_of_le_of_lt h1.ixbdd.2.2,
      apply bound_lt_prime },
    simp [BddECPointData.toECPoint, pt1xz], refl },
  rcases h' with ⟨pt0nz, pt1nz, is, inew_x, inew_y, is_bdd, inew_x_bdd, inew_y_bdd, ret1eq, mod1eq, mod2eq, mod3eq⟩,
  have eq1 : ((h0.ix.val : secpF) - h1.ix.val) * is.val = h0.iy.val - h1.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
    apply mod1eq },
  have eq2 : (inew_x.val : secpF) = is.val ^ 2 - h0.ix.val - h1.ix.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
    apply mod2eq },
  have eq3: (inew_y.val : secpF) = (h0.ix.val - inew_x.val) * is.val - h0.iy.val,
  { norm_cast, rw @char_p.int_cast_eq_int_cast secpF _ SECP_PRIME,
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
    ixbdd := by apply bigint3.bounded_of_bounded_of_le inew_x_bdd; norm_num [BASE],
    iybdd := by apply bigint3.bounded_of_bounded_of_le inew_y_bdd; norm_num [BASE],
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
      apply toBigInt3_eq_zero_of_bounded_3BASE h',
      apply bigint3.bounded_of_bounded_of_le inew_x_bdd; norm_num [BASE] },
  use hret,
  dsimp [BddECPointData.toECPoint], simp [dif_neg pt0nz', dif_neg pt1nz', dif_neg hhret],
  symmetry,
  apply Affine_add_Affine _ _ _ hne,
  rw [ecaddeq]
end




/-
-- Function: ec_add
-/

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

-- You may change anything in this definition except the name and arguments.
def spec_ec_add (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point0 point1 : EcPoint mem) (ρ_range_check_ptr : F) (ρ_res : EcPoint mem) : Prop :=
  ∀ (secpF : Type) [secp_field secpF], by exactI
  ∀ h0 : BddECPointData secpF point0,
  ∀ h1 : BddECPointData secpF point1,
    ∃ hret : BddECPointData secpF ρ_res,
      hret.toECPoint = h0.toECPoint + h1.toECPoint

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
  have h3: ix_diff.bounded (2^107),
  { rw (show (2^107 : ℤ) = 2^106 + 2^106, by norm_num),
    apply bigint3.bounded_sub,
    apply bigint3.bounded_of_bounded_of_le h0.ixbdd,
    rw BASE, simp_int_casts, norm_num,
    apply bigint3.bounded_of_bounded_of_le h1.ixbdd,
    rw BASE, simp_int_casts, norm_num },
  rcases h' with ⟨same_x_z, _, h'⟩ | ⟨same_x_nz, h'⟩,
  { have := h_x_diff _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
    have : ix_diff.val % ↑SECP_PRIME ≠ 0,
    { rcases this with ⟨_, rfl⟩ | ⟨_, _⟩,
      norm_num at same_x_z, assumption },
    apply spec_fast_ec_add'_of_spec_ec_add h'.1,
    contrapose! this,
    dsimp [ix_diff], rw [bigint3.sub_val, ←int.modeq_iff_sub_mod_eq_zero,
      ←char_p.int_cast_eq_int_cast secpF],
    exact this },
  have := h_x_diff _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
  have : ix_diff.val % ↑SECP_PRIME = 0,
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
  have h3: iy_sum.bounded (2^107),
  { rw (show (2^107 : ℤ) = 2^106 + 2^106, by norm_num),
    apply bigint3.bounded_add,
    apply bigint3.bounded_of_bounded_of_le h0.iybdd,
    rw BASE, simp_int_casts, norm_num,
    apply bigint3.bounded_of_bounded_of_le h1.iybdd,
    rw BASE, simp_int_casts, norm_num },
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
    have : iy_sum.val % ↑SECP_PRIME = 0,
    { rcases this with ⟨_, _⟩ | ⟨_, hh⟩,
      assumption, contradiction },
    rw [bigint3.add_val, ←sub_neg_eq_add, ←int.modeq_iff_sub_mod_eq_zero,
       ←char_p.int_cast_eq_int_cast secpF, int.cast_neg] at this,
    exact this },
  have := h_opposite_y _ (bigint3.eq_toBigInt3_iff_eq_toSumBigInt3.mpr h2) h3,
  have h0iyneh1iy : iy_sum.val % ↑SECP_PRIME ≠ 0,
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

-- You may change anything in this definition except the name and arguments.
def spec_ec_mul_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (point : EcPoint mem) (scalar m ρ_range_check_ptr : F) (ρ_pow2 ρ_res : EcPoint mem) : Prop :=
   ∀ (secpF : Type) [hsecp : secp_field secpF],
   by exactI
      point.x ≠ ⟨0, 0, 0⟩ →
      ∀ hpt : BddECPointData secpF point,
      ∃ nn : ℕ,
        m = ↑nn ∧
        nn < ring_char F ∧
          (nn ≤ SECP_LOG2_BOUND →
            ∃ scalarn : ℕ,
              scalar = ↑scalarn ∧
              scalarn < 2^nn ∧
            ∃ hpow2 : BddECPointData secpF ρ_pow2,
              ρ_pow2.x ≠ ⟨0, 0, 0⟩ ∧
              hpow2.toECPoint = 2^nn • hpt.toECPoint ∧
            ∃ hres : BddECPointData secpF ρ_res,
              hres.toECPoint = scalarn • hpt.toECPoint)


/-
-- Function: ec_mul_inner
-/

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
  simp [hxeq, hpt0xnz, ←(h1.onEC' h1xz)] at this,
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
    have nn'le' : nn' ≤ SECP_LOG2_BOUND := le_trans (le_of_lt (nat.lt_succ_self _)) nn'le,
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
  have nn'le' : nn' ≤ SECP_LOG2_BOUND := le_trans (le_of_lt (nat.lt_succ_self _)) nn'le,
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
  rcases spec_fast_ec_add'_of_spec_ec_add hodd2 secpF hpt hinnerres this with ⟨hret, hreteq⟩,
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
  have nb0le : nb0 ≤ SECP_LOG2_BOUND, by { rw [nb0eq', SECP_LOG2_BOUND], norm_num1 },
  rcases h0aux nb0le with ⟨n0, n0eq, n0lt, hpow20, hpow20ne, hpow20eq, hres0, hres0eq⟩,
  rcases h1 secpF hpow20ne hpow20 with ⟨nb1, nb1eq, nb1lt, h1aux⟩,
  have nb1eq' : nb1 = 86,
  { apply nat.cast_inj_of_lt_char nb1lt, { rw [PRIME.char_eq, PRIME], norm_num1 },
    rw ←nb1eq, simp },
  have nb1le : nb1 ≤ SECP_LOG2_BOUND, by { rw [nb1eq', SECP_LOG2_BOUND], norm_num1 },
  rcases h1aux nb1le with ⟨n1, n1eq, n1lt, hpow21, hpow21ne, hpow21eq, hres1, hres1eq⟩,
  rcases h2 secpF hpow21ne hpow21 with ⟨nb2, nb2eq, nb2lt, h2aux⟩,
  have nb2eq' : nb2 = 84,
  { apply nat.cast_inj_of_lt_char nb2lt, { rw [PRIME.char_eq, PRIME], norm_num1 },
    rw ←nb2eq, simp },
  have nb2le : nb2 ≤ SECP_LOG2_BOUND, by { rw [nb2eq', SECP_LOG2_BOUND], norm_num1 },
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

theorem ec_mul_bound {n0 n1 n2 : ℕ} (n0lt : n0 < 2^86) (n1lt : n1 < 2^86) (n2lt : n2 < 2^84) :
  2^172 * n2 + 2^86 * n1 + n0 < 2^256 :=
begin
  apply @lt_of_lt_of_le _ _ _ ((2^86)^2 * (2^84 - 1) + 2^86 * (2^86 - 1) + 2^86),
  apply add_lt_add_of_le_of_lt _ n0lt,
  apply add_le_add,
  apply nat.mul_le_mul,
  norm_num,
  apply le_tsub_of_add_le_right,
  apply nat.succ_le_of_lt n2lt,
  apply nat.mul_le_mul_left,
  apply le_tsub_of_add_le_right,
  apply nat.succ_le_of_lt n1lt,
  norm_num
end

end starkware.cairo.common.cairo_secp.ec
