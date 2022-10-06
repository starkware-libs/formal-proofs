/-
  Specifications file for constants_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.cairo_secp.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def SECP_REM := 2 ^ 32 + 2 ^ 9 + 2 ^ 8 + 2 ^ 7 + 2 ^ 6 + 2 ^ 4 + 1
@[reducible] def BASE := 2 ^ 86
@[reducible] def P0 := 77371252455336262886226991
@[reducible] def P1 := 77371252455336267181195263
@[reducible] def P2 := 19342813113834066795298815
@[reducible] def N0 := 10428087374290690730508609
@[reducible] def N1 := 77371252455330678278691517
@[reducible] def N2 := 19342813113834066795298815
@[reducible] def BETA := 7

-- End of main scope definitions.

/-
Useful calculations collected here.
-/

@[reducible] def secp_n := N0 + BASE * N1 + BASE^2 * N2

lemma BASE_nonneg: 0 ≤ (↑BASE : ℤ) :=
by { unfold BASE, simp_int_casts, norm_num1 }

lemma BASE_div_4_nonneg: 0 ≤ (↑BASE : ℤ) / 4 :=
int.div_nonneg BASE_nonneg (by norm_num)

lemma SECP_REM_nonneg: 0 ≤ (↑SECP_REM : ℤ) :=
by { unfold SECP_REM, simp_int_casts, norm_num1 }

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

@[irreducible] def SECP_PRIME : ℕ := BASE^3 / 4 - SECP_REM

theorem SECP_PRIME_eq : (↑SECP_PRIME : ℤ) = (↑BASE : ℤ)^3 / 4 - ↑SECP_REM :=
begin
  simp only [SECP_PRIME],
  rw int.coe_nat_sub, rotate, { dsimp only [SECP_REM, BASE], norm_num },
  refl,
end

/--
Some bounds use 3 * BASE - 1, and some use 3 * (BASE - 1).
This theorem mediates between them.
-/
theorem bound_slack : (3 : ℤ) * (BASE - 1) ≤ 3 * BASE - 1 :=
by { unfold BASE, simp_int_casts, norm_num }

theorem bound_lt_prime : (3 : ℤ) * BASE - 1 < PRIME :=
by { unfold BASE, unfold PRIME, simp_int_casts, norm_num }

end starkware.cairo.common.cairo_secp.constants
