import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative

-- Rational functions in Lean: Mathlib.FieldTheory.RatFunc
-- Derivatives of polynomials: Polynomial.derivative

variable {F : Type _} [Field F]

noncomputable section
open Classical

open Polynomial

-- This proof is based on the proof in the library for natDegree_eq_zero_of_derivative_eq_zero
-- (except that we replace the assumption [NoZeroSMulDivisors ℕ R] by the assumption on the degree).
theorem natDegree_eq_zero_of_derivative_eq_zero {f : F[X]} {p : ℕ}
      (h_char : CharP F p)
      (h_deg_lt_char : p = 0 ∨ f.natDegree < p)
      (h : derivative f = 0) :
    f.natDegree = 0 := by
  rcases eq_or_ne f 0 with (rfl | hf)
  · exact natDegree_zero
  rw [natDegree_eq_zero_iff_degree_le_zero]
  by_contra! f_nat_degree_pos
  rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
  let m := f.natDegree - 1
  have hm : m + 1 = f.natDegree := tsub_add_cancel_of_le f_nat_degree_pos
  have h2 := coeff_derivative f m
  rw [Polynomial.ext_iff] at h
  -- The following line of the original proof was replaced by the following section.
  -- rw [h m, coeff_zero, ← Nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2
  rw [h m, coeff_zero, ← Nat.cast_add_one] at h2
  replace h2 : m + 1 = 0 ∨ coeff f (m + 1) = 0 := by
    by_cases h_coeff_zero : coeff f (m + 1) = 0
    · right ; exact h_coeff_zero
    left
    rw [←ne_eq] at h_coeff_zero
    rw [Eq.comm,  mul_comm, ←(eq_div_iff h_coeff_zero), zero_div] at h2
    rw [(charP_iff F p).mp h_char (m + 1)] at h2
    by_cases h_p_zero : p = 0
    · rw [h_p_zero] at h2
      exact zero_dvd_iff.mp h2
    exfalso
    cases' h_deg_lt_char with h_p_eq_0 h_p_ne_0
    · exact h_p_zero h_p_eq_0
    rw [hm] at h2
    exact (not_lt_of_ge (Nat.le_of_dvd f_nat_degree_pos h2)) h_p_ne_0
  replace h2 := h2.resolve_left m.succ_ne_zero
  -- replaced down to here.
  rw [hm, ← leadingCoeff, leadingCoeff_eq_zero] at h2
  exact hf h2

theorem eq_C_of_derivative_eq_zero {f : F[X]} {p : ℕ}
      (h_char : CharP F p)
      (h_deg_lt_char : p = 0 ∨ f.natDegree < p)
      (h : derivative f = 0) :
    f = C (f.coeff 0) :=
  eq_C_of_natDegree_eq_zero <| natDegree_eq_zero_of_derivative_eq_zero h_char h_deg_lt_char h

-- TODO: delete
-- theorem Polynomial.derivative_C_mul {p : F[X]} {a : F} :
--     Polynomial.derivative (C a * p) = C a * Polynomial.derivative p := by
--   rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]

-- I added 'noncomputable' here because Lean told me to. Was that the right thing to do.
noncomputable def RatFunc.derivative (x : RatFunc F) : RatFunc F :=
  RatFunc.mk (Polynomial.derivative x.num * x.denom - x.num * Polynomial.derivative x.denom) (x.denom * x.denom)

lemma RatFunc.mul_div_cancel {p q : F[X]} (h_q : q ≠ 0) :
    RatFunc.mk (p * q) q = RatFunc.mk p 1 := by
  rw [RatFunc.mk_eq_mk h_q zero_ne_one.symm, mul_one]

lemma RatFunc.mul_div_cancel' {p q : F[X]} (h_q : q ≠ 0) :
    RatFunc.mk (p * q) q = (algebraMap _ _) p := by
  rw [RatFunc.algebraMap_apply, ←RatFunc.mk_eq_div]
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  rw [RatFunc.mk_eq_mk h_q zero_ne_one.symm, mul_one]

#check div_mul_cancel

lemma RatFunc.mk_add {p₁ q₁ p₂ q₂ : F[X]} (h_q₁ : q₁ ≠ 0) (h_q₂ : q₂ ≠ 0) :
    RatFunc.mk p₁ q₁ + RatFunc.mk p₂ q₂ = RatFunc.mk (p₁ * q₂ + p₂ * q₁) (q₁ * q₂) := by
  simp only [RatFunc.mk_eq_div]
  simp only [RingHom.map_add, RingHom.map_mul]
  rw [eq_div_iff _, right_distrib, ←mul_assoc, mul_comm ((algebraMap _ _) q₁) _]
  rw [div_mul_cancel₀, ←mul_assoc, div_mul_cancel₀]
  exact RatFunc.algebraMap_ne_zero h_q₂
  exact RatFunc.algebraMap_ne_zero h_q₁
  rw [mul_ne_zero_iff]
  exact ⟨(RatFunc.algebraMap_ne_zero h_q₁), RatFunc.algebraMap_ne_zero h_q₂⟩

lemma RatFunc.algebraMap_denom_one {p : F[X]} : RatFunc.mk p 1 = (algebraMap _ _) p := by
  rw [RatFunc.algebraMap_apply, RatFunc.mk_eq_div]
  rw [Algebra.algebraMap_self, RingHom.id_apply]

lemma RatFunc.algebraMap_derivative {p : F[X]} :
    (RatFunc.mk p 1).derivative = (algebraMap _ _) (Polynomial.derivative p) := by
  rw [RatFunc.algebraMap_denom_one]
  unfold RatFunc.derivative
  simp only [RatFunc.denom_algebraMap, RatFunc.num_algebraMap]
  rw [mul_one, mul_one, Polynomial.derivative_one, mul_zero, sub_zero, RatFunc.algebraMap_denom_one]

lemma Polynomial.div_mul_gcd {p q : F[X]} (h_q : q ≠ 0) : p = (p / gcd p q) * (gcd p q) := by
  rw [mul_comm, EuclideanDomain.mul_div_cancel']
  · by_contra h ; rw [gcd_eq_zero_iff] at h ; apply (h_q h.right)
  apply gcd_dvd_left

lemma Polynomial.div_mul_gcd' {p q : F[X]} (h_q : q ≠ 0) : q = (q / gcd p q) * (gcd p q) := by
  rw [mul_comm, EuclideanDomain.mul_div_cancel']
  · by_contra h ; rw [gcd_eq_zero_iff] at h ; apply (h_q h.right)
  apply gcd_dvd_right

lemma RatFunc.mk_C_mul {p q : F[X]} {a : F} (h_a : a ≠ 0):
    RatFunc.mk (Polynomial.C a * p) (Polynomial.C a * q) = RatFunc.mk p q := by
  by_cases h_q : q = 0
  · rw [h_q, mul_zero] ; simp only [RatFunc.mk_zero]
  rw [RatFunc.mk_eq_mk (mul_ne_zero (Polynomial.C_ne_zero.mpr h_a) h_q) h_q]
  ring

lemma RatFunc.mk_derivative {p q : F[X]} (h_q : q ≠ 0):
    (RatFunc.mk p q).derivative = RatFunc.mk (Polynomial.derivative p * q - p * Polynomial.derivative q) (q * q) := by
  rw [RatFunc.mk_eq_div]
  unfold RatFunc.derivative
  simp only [RatFunc.num_div, (RatFunc.denom_div p h_q)]
  simp only [Polynomial.derivative_C_mul]
  have h_p_deriv : Polynomial.derivative p =
      Polynomial.derivative (p / gcd p q) * (gcd p q) +  (p / gcd p q) * Polynomial.derivative (gcd p q) := by
    rw [←Polynomial.derivative_mul] ; rw [←div_mul_gcd h_q]
  have h_q_deriv : Polynomial.derivative q =
      Polynomial.derivative (q / gcd p q) * (gcd p q) +  (q / gcd p q) * Polynomial.derivative (gcd p q) := by
    rw [←Polynomial.derivative_mul] ; rw [←div_mul_gcd' h_q]
  rw [h_p_deriv, h_q_deriv]
  have h_coeff_ne_zero : (leadingCoeff (q / gcd p q))⁻¹ ≠ 0 := by
    apply inv_ne_zero ; rw [Polynomial.leadingCoeff_ne_zero]
    by_contra h ; rw [Polynomial.div_eq_zero_iff (gcd_ne_zero_of_right h_q)] at h ;
    exact not_lt_of_ge (Polynomial.degree_gcd_le_right p h_q) <| h
  conv_lhs => simp only [mul_assoc] ; rw [←mul_sub_left_distrib]
  rw [mk_C_mul]
  swap
  exact h_coeff_ne_zero
  rw [RatFunc.mk_eq_mk]
  -- ring does not manage to close this, needs some help.
  . sorry
  simp_all
  simp_all

lemma RatFunc.add_derivative (x y : RatFunc F) : (x + y).derivative = x.derivative + y.derivative := by
  conv_rhs => unfold derivative
  have h_d_x := RatFunc.denom_ne_zero x
  have h_d_y := RatFunc.denom_ne_zero y
  rw [RatFunc.mk_add (mul_ne_zero h_d_x h_d_x) (mul_ne_zero h_d_y h_d_y)]
  conv_lhs =>
    rw [←RatFunc.num_div_denom x, ←RatFunc.num_div_denom y, ←RatFunc.mk_eq_div, ←RatFunc.mk_eq_div]
    rw [RatFunc.mk_add (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)]
    unfold RatFunc.derivative

  rw [RatFunc.mk_eq_mk]; swap; simp_all
  . sorry
  . sorry
  simp_all

-- Lemma 2 of the paper.

-- lemma constant_of_derivative_zero {x : RatFunc F} {p : ℕ}
--       (h_char : CharP F p)
--       (h_deg_num_lt : x.num.natDegree < p)
--       (h_deg_denom_lt : x.denom.natDegree < p)
--       (h : x.derivative = 0) :
--     ∃ a : F, x = RatFunc.C a := by
--   sorry
