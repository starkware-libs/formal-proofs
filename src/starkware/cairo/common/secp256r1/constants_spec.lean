/-
  Specifications file for constants_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.secp256r1.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def BASE := 2 ^ 86
@[reducible] def D2_BOUND := 2 ^ 84
@[reducible] def SECP_REM0 : ℤ := 1
@[reducible] def SECP_REM1 : ℤ := -(2 ^ 10)
@[reducible] def SECP_REM2 : ℤ := 4503599626321920
@[reducible] def P0 := 77371252455336267181195263
@[reducible] def P1 := 1023
@[reducible] def P2 := 19342813109330467168976896
@[reducible] def ALPHA : ℤ := (-3)
@[reducible] def BETA0 : ℤ := 23805269282153275520606283
@[reducible] def BETA1 : ℤ := 64478498050055519801623345
@[reducible] def BETA2 : ℤ := 6858709101169761702330043
@[reducible] def BASE3_MOD_P2 : ℤ := 2 ^ 54 - 2 ^ 22
@[reducible] def BASE3_MOD_P1 : ℤ := -(2 ^ 12)
@[reducible] def BASE3_MOD_P0 : ℤ := 4
@[reducible] def BASE4_MOD_P2 : ℤ := -(2 ^ 76) - 2 ^ 12
@[reducible] def BASE4_MOD_P1 : ℤ := -(2 ^ 66) + 4
@[reducible] def BASE4_MOD_P0 : ℤ := 2 ^ 56
@[reducible] def SECP_PRIME_HIGH := 340282366841710300967557013911933812736
@[reducible] def SECP_PRIME_LOW := 79228162514264337593543950335

-- End of main scope definitions.

/-
Useful calculations collected here.
-/

def BETA := BETA0 + BETA1 * BASE + BETA2 * BASE^2

def SECP_REM : ℤ := SECP_REM2 * BASE^2 + SECP_REM1 * BASE + SECP_REM0

@[reducible] def secp_p := P0 + BASE * P1 + BASE^2 * P2

lemma BASE_nonneg: 0 ≤ (↑BASE : ℤ) := nat.cast_nonneg _

lemma BASE_div_4_nonneg: 0 ≤ (↑BASE : ℤ) / 4 :=
int.div_nonneg BASE_nonneg (by norm_num)

lemma SECP_REM0_nonneg: 0 ≤ SECP_REM0 :=
by { simp only [SECP_REM0], norm_num1 }

lemma SECP_REM_nonneg: 0 ≤ SECP_REM :=
by { simp only [SECP_REM, SECP_REM0, SECP_REM1, SECP_REM2, BASE], simp_int_casts, norm_num1 }

lemma BASE_ne_zero_aux : (BASE : F) ≠ 0 :=
begin
  suffices : ((BASE : nat) : F) ≠ ((0 : nat) : F),
  { simpa },
  intro h,
  have:= PRIME.nat_coe_field_inj _ _ h,
  { norm_num at this},
  repeat {dsimp only [BASE, PRIME], norm_num }
end

lemma BASE_ne_zero_aux' : (2 : F)^86 ≠ 0 :=
begin
  suffices : ((2^86 : nat) : F) ≠ ((0 : nat) : F),
  { simpa },
  intro h,
  have:= PRIME.nat_coe_field_inj _ _ h,
  { norm_num at this},
  repeat {dsimp only [BASE, PRIME], norm_num }
end

lemma secp_p_eq : (secp_p : ℤ) = 2^256 - SECP_REM :=
begin
  simp only [secp_p, SECP_REM, SECP_REM2, SECP_REM1, SECP_REM0, BASE,
    P0, P1, P2],
  simp_int_casts,
  simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one, int.coe_nat_bit1, mul_neg],
  norm_num1
end

lemma BASE3_mod_secp_p : (BASE : ℤ) ^3 % secp_p = BASE^2 * BASE3_MOD_P2 +
    BASE * BASE3_MOD_P1 + BASE3_MOD_P0 :=
begin
  simp only [BASE, secp_p, BASE3_MOD_P2, BASE3_MOD_P1, BASE3_MOD_P0,
    P0, P1, P2],
  simp_int_casts,
  simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one, int.coe_nat_bit1, mul_neg],
  norm_num1
end

lemma BASE4_mod_secp_p : (BASE : ℤ)^4 % secp_p = BASE^2 * BASE4_MOD_P2 +
    BASE * BASE4_MOD_P1 + BASE4_MOD_P0 + secp_p :=
begin
  simp only [BASE, secp_p, BASE4_MOD_P2, BASE4_MOD_P1, BASE4_MOD_P0,
    P0, P1, P2],
  simp_int_casts,
  simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one, int.coe_nat_bit1, mul_neg],
  norm_num1,
end

def BASE3_MOD_P : ℤ := BASE^2 * BASE3_MOD_P2 + BASE * BASE3_MOD_P1 + BASE3_MOD_P0

def BASE4_MOD_P : ℤ := BASE^2 * BASE4_MOD_P2 + BASE * BASE4_MOD_P1 + BASE4_MOD_P0

theorem BASE3_MOD_P_diff_eq : (BASE : ℤ)^3 - BASE3_MOD_P = ((BASE : ℤ)^3 / secp_p) * secp_p :=
begin
  simp only [BASE, BASE3_MOD_P, secp_p, BASE3_MOD_P2, BASE3_MOD_P1, BASE3_MOD_P0,
    P0, P1, P2],
  simp_int_casts,
  simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one, int.coe_nat_bit1, mul_neg],
  norm_num1
end

theorem BASE4_MOD_P_diff_eq : (BASE : ℤ)^4 - BASE4_MOD_P = ((BASE : ℤ)^4 / secp_p + 1) * secp_p :=
begin
  simp only [BASE, BASE4_MOD_P, secp_p, BASE4_MOD_P2, BASE4_MOD_P1, BASE4_MOD_P0,
    P0, P1, P2],
  simp_int_casts,
  simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one, int.coe_nat_bit1, mul_neg],
  norm_num1,
end

end starkware.cairo.common.secp256r1.constants
