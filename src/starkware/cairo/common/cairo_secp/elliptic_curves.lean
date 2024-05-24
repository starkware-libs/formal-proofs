import data.zmod.algebra
import algebraic_geometry.elliptic_curve.point
import tactic

class ec_field (F : Type*) extends field F :=
(deceqF : decidable_eq F)
(two_ne_zero : (2 : F) ≠ 0)
(three_ne_zero : (3 : F) ≠ 0)
(seven_ne_zero : (7 : F) ≠ 0)

instance ec_field.decidable_eq (F : Type*) [h : ec_field F] : decidable_eq F :=
h.deceqF

def on_ec {F : Type*} [field F] (p : F × F) := p.2^2 = p.1^3 + 7

lemma eq_or_eq_neg_of_eq_of_on_ec {F : Type*} [field F] {x1 y1 x2 y2 : F}
    (hp : on_ec (x1, y1)) (hq : on_ec (x2, y2)) (heq : x1 = x2 ) :
  y1 = y2 ∨ y1 = -y2 :=
begin
  have : y1^2 = y2^2,
  { apply hp.trans, symmetry, apply hq.trans, dsimp, rw heq },
  apply eq_or_eq_neg_of_sq_eq_sq _ _ this
end

lemma eq_of_on_ec {F : Type*} [field F] {x1 y1 x2 y2 : F}
    (hp : on_ec (x1, y1)) (hq : on_ec (x2, y2)) (heq : x1 = x2 ) (hne : y1 ≠ -y2) :
  y1 = y2 :=
or.resolve_right (eq_or_eq_neg_of_eq_of_on_ec hp hq heq) hne

@[ext] structure AffineECPoint (F : Type*) [field F] :=
(x y : F) (h : on_ec (x, y))

inductive ECPoint  (F : Type*) [field F]
| ZeroPoint : ECPoint
| AffinePoint : AffineECPoint F → ECPoint

variables {F : Type*} [ec_field F]

def ec_double_slope (p : F × F) := 3 * p.1^2 / (2 * p.2)

def ec_double (p : F × F) :=
  let slope := ec_double_slope p,
      new_x := slope^2 - 2 * p.1 in
  (new_x, (p.1 - new_x) * slope - p.2)

theorem on_ec_ec_double {p : F × F} (h : on_ec p) (h' : p.2 ≠ 0) :
  on_ec (ec_double p) :=
begin
  cases p with x y,
  have pow_three : ∀ z : F, z^3 = z * z * z, { intro z, simp [pow_succ, mul_assoc] },
  simp [on_ec, ec_double, ec_double_slope] at *,
  apply eq_of_sub_eq_zero,
  field_simp [ec_field.two_ne_zero, h, h', pow_two, pow_three], ring_nf,
  simp [h], ring_nf,
end

def ec_add_slope (p1 p2 : F × F) := (p2.2 - p1.2) / (p2.1 - p1.1)

def ec_add (p1 p2 : F × F) : F × F :=
  let slope := ec_add_slope p1 p2,
      new_x := slope^2 - (p1.1 + p2.1) in
  (new_x, (p1.1 - new_x) * slope - p1.2)

theorem on_ec_ec_add {p1 p2 : F × F} (h1 : on_ec p1) (h2 : on_ec p2) (h' : p1.1 ≠ p2.1) :
  on_ec (ec_add p1 p2) :=
begin
  cases p1 with x1 y1,
  cases p2 with x2 y2,
  have pow_three : ∀ z : F, z^3 = z * z^2, { intro z, simp [pow_succ, mul_assoc], },
  have pow_four : ∀ z : F, z^4 = z^2 * z^2, { intro z, simp [pow_succ, mul_assoc], },
  simp [on_ec, ec_add, ec_add_slope] at *,
  have : x2 - x1 ≠ 0, { contrapose! h', symmetry, apply eq_of_sub_eq_zero h' },
  apply eq_of_sub_eq_zero,
  field_simp [ec_field.two_ne_zero, pow_two, pow_three, this], ring_nf,
  simp [h1, h2, pow_three, pow_four], ring_nf,
  simp [h1, h2], ring_nf
end

namespace ECPoint

protected def add : ECPoint F → ECPoint F → ECPoint F
| ZeroPoint       b               := b
| a               ZeroPoint       := a
| (AffinePoint a) (AffinePoint b) :=
    if axbx: a.x = b.x then
      if ayby: a.y = -b.y then
        -- a = -b
        ZeroPoint
      else
        have a.y = b.y, from eq_of_on_ec a.h b.h axbx ayby,
        have a.y ≠ 0, by { contrapose! ayby, rw [←this, ayby, neg_zero] },
        let p := ec_double (a.x, a.y) in
        AffinePoint ⟨p.1, p.2, on_ec_ec_double a.h this⟩
    else
      let p := ec_add (a.x, a.y) (b.x, b.y) in
      AffinePoint ⟨p.1, p.2, on_ec_ec_add a.h b.h axbx⟩

protected def neg : ECPoint F → ECPoint F
| ZeroPoint       := ZeroPoint
| (AffinePoint a) := AffinePoint ⟨a.x, -a.y, by { simp [on_ec], exact a.h} ⟩

protected theorem add_left_neg (a : ECPoint F) : a.neg.add a = ZeroPoint :=
by { cases a; simp [ECPoint.neg, ECPoint.add] }

protected theorem add_comm (a b: ECPoint F) : a.add b = b.add a :=
begin
  cases a; cases b; simp [ECPoint.add],
  by_cases h : a.x = b.x,
  { rw [dif_pos h, dif_pos h.symm], simp [h],
    by_cases h': a.y = -b.y,
    { rw [dif_pos h', dif_pos (neg_eq_iff_eq_neg.mp h'.symm)] },
    rw [dif_neg h', dif_neg (λ h'', h' (neg_eq_iff_eq_neg.mpr h'').symm)],
    simp [eq_of_on_ec a.h b.h h h'] },
  rw [dif_neg h, dif_neg (ne.symm h)],
  have : ec_add_slope (a.x, a.y) (b.x, b.y) = ec_add_slope (b.x, b.y) (a.x, a.y),
  { simp [ec_add_slope], rw [←neg_sub b.y a.y, ←neg_sub b.x a.x, neg_div_neg_eq] },
  congr' 1, ext; dsimp [ec_add]; simp [add_comm],
  { simp [this] },
  have h1 : a.x - b.x ≠ 0, { rwa [ne, sub_eq_zero] },
  have h2 : b.x - a.x ≠ 0, { rw [ne, sub_eq_zero], exact ne.symm h },
  field_simp [ec_add_slope, h1, h2, pow_two],
  ring_nf
end

end ECPoint

open weierstrass_curve
def curve : weierstrass_curve F := ⟨0, 0, 0, 0, 7⟩

lemma on_ec_of_nonsingular {x y : F} (h : curve.nonsingular x y) :
  on_ec ⟨x, y⟩ := by
{ simp [curve, nonsingular] at h, exact h.1 }

lemma nonsingular_of_on_ec {x y : F} (h : on_ec ⟨x, y⟩) :
  curve.nonsingular x y :=
begin
  simp [curve, nonsingular],
  split, { exact h },
  apply not_or_of_imp,
  rintro (h' | h'),
  { exact absurd h' ec_field.three_ne_zero },
  rw [not_or_distrib], split,
  { apply ec_field.two_ne_zero },
  intro h'',
  simp [on_ec, h', h''] at h,
  exact ec_field.seven_ne_zero h.symm
end

def curve_to_ECPoint : (@curve F _).point → ECPoint F
  | point.zero := ECPoint.ZeroPoint
  | (@point.some _ _ _ x y h) := ECPoint.AffinePoint ⟨x, y, on_ec_of_nonsingular h⟩

def ECPoint_to_curve : ECPoint F → (@curve F _).point
  | ECPoint.ZeroPoint := point.zero
  | (ECPoint.AffinePoint ⟨x, y, h⟩) := point.some (nonsingular_of_on_ec h)

open function

lemma left_inverse_curve_to_ECPoint :
  left_inverse (@curve_to_ECPoint F _) (@ECPoint_to_curve F _) :=
begin
  rintro (⟨⟩ | ⟨x, y, h⟩),
  { refl },
  simp [curve_to_ECPoint, ECPoint_to_curve]
end

theorem ECPoint_to_curve_add (a b : ECPoint F) :
  ECPoint_to_curve (a.add b) = ECPoint_to_curve a + ECPoint_to_curve b :=
begin
  cases a with a; cases b with b; simp [ECPoint.add, ECPoint_to_curve, curve_to_ECPoint, ECPoint.add],
  cases a with ax ay ah; cases b with bx by' bh; dsimp [ECPoint_to_curve],
  rw [←point.add_def, point.add],
  by_cases xeq : ax = bx,
  { simp [dif_pos xeq, curve],
     by_cases yeqneg : ay = -by',
     { simp [dif_pos yeqneg], refl },
     simp [dif_neg yeqneg, ECPoint_to_curve, ec_double, weierstrass_curve.slope, dif_pos xeq,
       ec_double_slope],
      rw [←xeq], split; ring_nf },
  simp [dif_neg xeq, curve, ECPoint_to_curve, ec_add, weierstrass_curve.slope, ec_add_slope],
  split, ring_nf,
  have : (ax - bx) ≠ 0,
  { intro h, apply xeq, rw [eq_of_sub_eq_zero h] },
  have : (bx - ax) ≠ 0,
  { intro h, apply xeq, rw [eq_of_sub_eq_zero h] },
  field_simp [xeq], ring
end

instance : add_comm_group (ECPoint F) :=
{ add          := ECPoint.add,
  neg          := ECPoint.neg,
  zero         := ECPoint.ZeroPoint,
  add_assoc    :=
    begin
      intros a b c,
      apply (left_inverse_curve_to_ECPoint).injective,
      simp [ECPoint_to_curve_add, add_assoc]
    end,
  zero_add     := by { intro a, cases a; simp [ECPoint.add] },
  add_zero     := by { intro a, cases a; simp [ECPoint.add] },
  add_left_neg := ECPoint.add_left_neg,
  add_comm     := ECPoint.add_comm }

theorem ECPoint.add_def (x y : ECPoint F) : x + y = ECPoint.add x y := rfl

theorem ECPoint.neg_def (x : ECPoint F) : - x = ECPoint.neg x := rfl

theorem ECPoint.zero_def : (0 : ECPoint F) = ECPoint.ZeroPoint := rfl







