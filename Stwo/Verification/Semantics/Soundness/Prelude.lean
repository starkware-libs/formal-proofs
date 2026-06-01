/-
These are properties that depend on the specific choice of the prime field characteristic in Cairo, as well as the fact that the range check bound
`rc_bound` is less than or equal to 2^128. (In practice, they are equal.)
-/
import Verification.Semantics.Soundness.Hoare

def PRIME :=
  3618502788666131213697322783095070105623107215331596699973092056135872020481

-- for reference
theorem PRIME_gt : PRIME > 2 ^ 251 := by simp [PRIME]
theorem PRIME_pos : 0 < PRIME := by rw [PRIME]; norm_num1
theorem PRIME_sub_one_lt : PRIME - 1 < PRIME := by rw [PRIME]; norm_num1

/- Assumptions on F.  -/
class PreludeHyps (F : Type _) [Field F] where
  [charF : CharP F PRIME]
  rcBound : Nat
  rcBound_hyp : rc_bound ≤ 2 ^ 128

export PreludeHyps (charF rcBound)

variable {F : Type _} [Field F]

instance char_ge [ph : PreludeHyps F] : CharGe263 F := by
  have : ringChar F ≥ 2 ^ 63 := by
    rw [@ringChar.eq F _ PRIME ph.charF, PRIME]
    norm_num1
  exact ⟨this⟩

instance [ph : PreludeHyps F] : CharP F PRIME := ph.charF

variable [PreludeHyps F]

def rcBound_hyp (F : Type _) [Field F] [PreludeHyps F] := @PreludeHyps.rcBound_hyp F _ _

theorem two_mul_rcBound_lt_PRIME (F : Type _) [Field F] [PreludeHyps F] : 2 * rcBound F < PRIME :=
  by apply lt_of_le_of_lt (Nat.mul_le_mul_left 2 (rcBound_hyp F)); rw [PRIME]; norm_num1

theorem rcBound_lt_PRIME : rcBound F < PRIME := by linarith [two_mul_rcBound_lt_PRIME F]

namespace PRIME

theorem char_eq : ringChar F = PRIME := ringChar.eq F PRIME

theorem char_pos : 0 < ringChar F := by rw [@ringChar.eq F _ PRIME _, PRIME]; norm_num

theorem nat_coe_field_inj {a b : ℕ} (ha : a < PRIME) (hb : b < PRIME) (h : (a : F) = (b : F)) :
    a = b := by apply Nat.cast_inj_of_lt_char _ _ h <;> rwa [PRIME.char_eq]

theorem int_coe_inj {i j : ℤ} (h : (i : F) = (j : F)) (h' : abs (j - i) < PRIME) : i = j :=
  Int.cast_inj_of_lt_char charF h h'

theorem nat_coe_field_zero {x : F} {n : ℕ} (h_lt : n < PRIME) (h_cast : x = ↑n) : x = 0 → n = 0 := by
  intro h_zero; rw [h_cast, ← Nat.cast_zero] at h_zero
  apply PRIME.nat_coe_field_inj h_lt _ h_zero; rw [PRIME]; norm_num1

theorem nat_coe_field_ne_zero {x : F} {n : ℕ} (h_lt : n < PRIME) (h_cast : x = ↑n) :
    n ≠ 0 → x ≠ 0 := by
  intro h_ne_zero h_x_eq
  exact h_ne_zero (nat_coe_field_zero h_lt h_cast h_x_eq)

theorem nat_coe_field_iff_ne_zero {x : F} {n : ℕ} (h_lt : n < PRIME) (h_cast : x = ↑n) :
    n ≠ 0 ↔ x ≠ 0 := by
  constructor
  · exact nat_coe_field_ne_zero h_lt h_cast
  rw [h_cast]
  intro h_x h_n
  rw [h_n, Nat.cast_zero] at h_x
  exact (h_x rfl)

theorem nat_cast_mul_eq_one {m n : ℕ} (h : m * n % PRIME = 1) : ↑m * ↑n = (1 : F) := by
  haveI : CharP F PRIME := charF
  have primeP : Nat.Prime PRIME :=
    by
    apply Or.resolve_right (CharP.char_is_prime_or_zero F PRIME)
    rw [PRIME]; norm_num
  have : m * n ≥ 1 := by
    apply Nat.succ_le_of_lt; apply Nat.pos_of_ne_zero
    intro h'; simp [h'] at h
  apply eq_of_sub_eq_zero
  rw [← Nat.cast_one, ← Nat.cast_mul, ← Nat.cast_sub this, CharP.cast_eq_zero_iff F PRIME]
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [h, Nat.mod_eq_of_lt (Nat.Prime.two_le primeP)]

theorem int_cast_mul_eq_one {m n : ℤ} (h : m * n % PRIME = 1) : ↑m * ↑n = (1 : F) := by
  rw [← Int.cast_mul, ←Int.cast_one]
  apply (CharP.intCast_eq_intCast F PRIME).mpr
  exact h

theorem nat_cast_ne_zero {n : ℕ} (h_nz : n ≠ 0) (h_lt : n < PRIME) : (n : F) ≠ 0 := by
  simp [CharP.cast_eq_zero_iff F PRIME _]
  intro h_dvd
  have := Nat.eq_zero_of_dvd_of_lt h_dvd h_lt
  contradiction

theorem cast_ne_zero (x : ℤ) (h_nz : x ≠ 0) (h_lt : x.natAbs < PRIME) : (x : F) ≠ 0 := by
  haveI : CharP F PRIME := charF
  simp only [ne_eq, CharP.intCast_eq_zero_iff F PRIME _]
  intro h_dvd
  apply h_nz; apply Int.natAbs_eq_zero.mp; refine' Nat.eq_zero_of_dvd_of_lt _ h_lt
  exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h_dvd)

theorem div_eq_const {a b c : ℤ} (h_nz : (b : F) ≠ 0) :
    (c * b - a) % ↑PRIME = 0 → (a / b : F) = c := by
  intro h
  haveI : CharP F PRIME := charF
  symm; apply eq_div_of_mul_eq h_nz
  rw [← Int.cast_mul, ← sub_eq_zero, ← Int.cast_sub]; rw [CharP.intCast_eq_zero_iff F PRIME]
  apply Int.dvd_of_emod_eq_zero; exact h

variable (F)

theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  suffices (2 : ℤ) = 0 by norm_num at this
  have : ((2 : ℤ) : F) = ((0 : ℤ) : F) := by simp [h]
  apply PRIME.int_coe_inj this
  rw [PRIME]
  norm_num

theorem four_ne_zero : (4 : F) ≠ 0 := by
  suffices ((4 : Nat) : F) ≠ ((0 : Nat) : F) by simpa
  intro h
  have ha : 4 < PRIME := by dsimp only [PRIME]; norm_num1
  have hb : 0 < PRIME := by dsimp only [PRIME]; norm_num1
  have := PRIME.nat_coe_field_inj ha hb h
  · norm_num at this

variable {F}

end PRIME

theorem eq_zero_or_eq_one_of_mul_eq_self {R : Type _} [Ring R] [NoZeroDivisors R] {x : R}
    (h : x * x = x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  . left; exact h
  . right; rw [eq_of_sub_eq_zero h]
