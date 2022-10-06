/-
These are properties that depend on the specific choice of the prime field characteristic in Cairo, as well as the fact that the range check bound
`rc_bound` is less than or equal to 2^128. (In practice, they are equal.)
-/
import starkware.cairo.lean.semantics.soundness.hoare

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

-- for reference
lemma PRIME_gt : PRIME > 2^251 :=
by { simp [PRIME], norm_num }

lemma PRIME_pos : 0 < PRIME := by rw [PRIME]; norm_num1

lemma PRIME_sub_one_lt : PRIME - 1 < PRIME := by rw [PRIME]; norm_num1

/-
Assumptions on F.
-/

class prelude_hyps (F : Type*) [field F] :=
  [charF : char_p F PRIME]
  (rc_bound : nat)
  (rc_bound_hyp : rc_bound ≤ 2^128)

export prelude_hyps (charF rc_bound)

variables {F : Type*} [field F]

instance char_ge [ph : prelude_hyps F] : char_ge_2_63 F :=
by { rw [char_ge_2_63, @ring_char.eq F _ PRIME ph.charF, PRIME], norm_num1 }

instance [ph : prelude_hyps F] : char_p F PRIME := ph.charF

variable [prelude_hyps F]

def rc_bound_hyp (F : Type*) [field F] [prelude_hyps F] :=
@prelude_hyps.rc_bound_hyp F _ _

lemma two_mul_rc_bound_lt_PRIME (F : Type*) [field F] [prelude_hyps F] : 2 * rc_bound F < PRIME :=
by { apply lt_of_le_of_lt (nat.mul_le_mul_left 2 (rc_bound_hyp F)), rw [PRIME]; norm_num1 }

lemma rc_bound_lt_PRIME : rc_bound F < PRIME :=
by linarith [two_mul_rc_bound_lt_PRIME F]

namespace PRIME

lemma char_eq : ring_char F = PRIME :=
ring_char.eq F PRIME

lemma char_pos : 0 < ring_char F :=
by { rw [@ring_char.eq F _ PRIME _, PRIME], norm_num }

lemma nat_coe_field_inj {a b : ℕ} (ha : a < PRIME) (hb : b < PRIME) (h : (a : F)  = (b : F)) :
  a = b :=
by { apply nat.cast_inj_of_lt_char _ _ h; rwa PRIME.char_eq }

lemma int_coe_inj {i j : ℤ} (h : (i : F) = (j : F)) (h' : abs (j - i) < PRIME) : i = j :=
int.cast_inj_of_lt_char charF h h'

lemma nat_cast_mul_eq_one {m n : ℕ} (h : m * n % PRIME = 1) :
  ↑m * ↑n = (1 : F) :=
begin
  haveI : char_p F PRIME := charF,
  have primeP : nat.prime PRIME,
  { apply or.resolve_right (char_p.char_is_prime_or_zero F PRIME),
    rw [PRIME], norm_num },
  have : m * n ≥ 1,
  { apply nat.succ_le_of_lt, apply nat.pos_of_ne_zero,
    intro h', simp [h'] at h, exact h },
  apply eq_of_sub_eq_zero,
  rw [←nat.cast_one, ←nat.cast_mul, ←nat.cast_sub this, char_p.cast_eq_zero_iff F PRIME],
  apply nat.dvd_of_mod_eq_zero,
  apply nat.sub_mod_eq_zero_of_mod_eq,
  rw [h, nat.mod_eq_of_lt (nat.prime.two_le primeP)]
end

lemma int_cast_mul_eq_one {m n : ℤ} (h : m * n % PRIME = 1) :
  ↑m * ↑n = (1 : F) :=
begin
  -- find equivalent natural numbers
  -- note that `norm_cast` or `simp_int_casts` is better than `simp_int_casts` here.
  have h_p0 : (0 : ℤ) < ↑PRIME, { rw [PRIME], simp_int_casts, norm_num },
  rcases int.exists_unique_equiv_nat m h_p0 with ⟨mn, h_mn_lt, h_mn_eq⟩,
  rcases int.exists_unique_equiv_nat n h_p0 with ⟨nn, h_nn_lt, h_nn_eq⟩,
  -- convert the hypothesis
  have mul_eq := int.modeq.mul h_mn_eq h_nn_eq,
  dsimp [int.modeq] at mul_eq,
  rw [←mul_eq] at h, norm_cast at h,
  -- convert the goal
  have m_eq := (char_p.int_coe_eq_int_coe_iff F PRIME m mn).mpr h_mn_eq.symm,
  have n_eq := (char_p.int_coe_eq_int_coe_iff F PRIME n nn).mpr h_nn_eq.symm,
  norm_cast at m_eq n_eq, rw [m_eq, n_eq],
  exact nat_cast_mul_eq_one h,
end

lemma cast_ne_zero (x : ℤ) (h_nz : x ≠ 0) (h_lt : x.nat_abs < PRIME) : (x : F) ≠ 0 :=
begin
  haveI : char_p F PRIME := charF,
  simp [char_p.int_cast_eq_zero_iff F PRIME _], intro h_dvd,
  apply h_nz, apply int.nat_abs_eq_zero.mp, refine nat.eq_zero_of_dvd_of_lt _ h_lt,
  exact int.coe_nat_dvd.mp (int.dvd_nat_abs.mpr h_dvd),
end

lemma div_eq_const {a b c : ℤ } (h_nz : (b : F) ≠ 0) : (c * b - a) % ↑PRIME = 0 → (a / b : F) = c :=
begin
  intro h,
  haveI : char_p F PRIME := charF,
  symmetry, apply eq_div_of_mul_eq h_nz,
  rw [←int.cast_mul, ←sub_eq_zero, ←int.cast_sub], rw [char_p.int_cast_eq_zero_iff F PRIME],
  apply int.dvd_of_mod_eq_zero, exact h,
end

variable (F)
theorem two_ne_zero : (2 : F) ≠ 0 :=
begin
  intro h,
  suffices : (2 : ℤ) = 0,
  { norm_num at this },
  have : ((2 : ℤ) : F) = ((0 : ℤ) : F),
  { simp [h] },
  apply PRIME.int_coe_inj this,
  rw [PRIME], simp_int_casts,
  norm_num
end

lemma four_ne_zero : (4 : F) ≠ 0 :=
begin
  suffices : ((4 : nat) : F) ≠ ((0 : nat) : F),
  { simpa },
  intro h,
  have:= PRIME.nat_coe_field_inj _ _ h,
  { norm_num at this},
  repeat {dsimp only [PRIME], norm_num }
end
variable {F}

end PRIME
