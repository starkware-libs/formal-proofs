import Verification.Semantics.SimpAttr
import Verification.Semantics.Soundness.Prelude

set_option autoImplicit false

/- calculation rules for integer functions defined in terms of a nat offset -/
attribute [int_nat_offset_simps] Int.natAbs_zero Int.natAbs_one
  add_tsub_cancel_left sub_self tsub_self zero_le_one

macro (name := simp_int_nat_offset) "simp_int_nat_offset" : tactic => `(tactic|
  simp only [int_nat_offset_simps] )

/-
Constants.
-/

section

variable {F : Type} [Field F]

-- Coercion of nats up to the field are the same as casting to an int first
theorem coe_eq_int_coe_coe (n : ℕ) : (↑n : F) = ↑(↑n : ℤ) := Int.cast_natCast _ |>.symm

variable [PreludeHyps F] (mem : F → F) (σ : RegisterState F)

-- NOTE: For all these constants, immediate values are provided to reduce the
--       amount of Lean rw/unfolding required.

--  2^16 (-1)
@[reducible, inline] def u8Max : ℕ := 32767
@[reducible, inline] def u8Limit : ℕ := 32768

--  2^16 (-1)
@[reducible, inline] def u16Max : ℕ := 65535
@[reducible, inline] def u16Limit : ℕ := 65536

--  2^32 (-1)
@[reducible, inline] def u32Max : ℕ := 4294967295
@[reducible, inline] def u32Limit : ℕ := 4294967296

--  2^64 (-1)
@[reducible, inline] def u64Max : ℕ := 18446744073709551615
@[reducible, inline] def u64Limit : ℕ := 18446744073709551616

--  2^65 (-1)
@[reducible, inline] def u65Limit : ℕ := 36893488147419103232

--  2^128 (-1)
@[reducible, inline] def u128Max : ℕ := 340282366920938463463374607431768211455
@[reducible, inline] def u128Limit : ℕ := 340282366920938463463374607431768211456

@[reducible, inline] def i16Min : ℤ := -32768
@[reducible, inline] def i16Max : ℤ := 32767

theorem u16Max_lt_u128Max : u16Max < u128Max := by simp [u16Max, u128Max]
theorem u16Limit_lt_u128Max : u16Limit < u128Max := by simp [u16Limit, u128Max]
theorem u16Limit_lt_u128Limit : u16Limit < u128Limit := by simp [u16Limit, u128Limit]
theorem u16Max_lt_PRIME : u16Max < PRIME := by simp [PRIME, u16Max]
theorem u16Limit_lt_PRIME : u16Limit < PRIME := by simp [PRIME, u16Limit]

theorem u32Max_lt_u128Max : u32Max < u128Max := by simp [u32Max, u128Max]
theorem u32Max_lt_u128Limit : u32Max < u128Limit := by simp [u32Max, u128Limit]
theorem u32Limit_lt_u128Limit : u32Limit < u128Limit := by simp [u32Limit, u128Limit]
theorem u32Max_lt_PRIME : u32Max < PRIME := by simp [PRIME, u32Max]
theorem u32Limit_lt_PRIME : u32Limit < PRIME := by simp [PRIME, u32Limit]

theorem u64Max_lt_u128Max : u64Max < u128Max := by simp [u64Max, u128Max]
theorem u64Limit_lt_u128Limit : u64Limit < u128Limit := by simp [u64Limit, u128Limit]
theorem u64Max_lt_PRIME : u64Max < PRIME := by simp [PRIME, u64Max]
theorem u64Limit_lt_PRIME : u64Limit < PRIME := by simp [PRIME, u64Limit]

theorem u128Max_lt_PRIME : u128Max < PRIME := by simp [PRIME, u128Max]
theorem u128Limit_lt_PRIME : u128Limit < PRIME := by simp [PRIME, u128Limit]

theorem i16Max_abs_lt_PRIME : abs i16Max < PRIME := by simp [PRIME]
theorem i16Min_abs_lt_PRIME : abs i16Max < PRIME := by simp [PRIME]

theorem add_lt_u128Limit_of_lt_u16Limit {a b : ℕ} :
    a < u16Limit → b < u16Limit → a + b < u128Limit := by
  intro ha hb
  have : u16Limit + u16Limit < u128Limit := by unfold u16Limit u128Limit; norm_num1
  exact lt_trans (add_lt_add ha hb) this

theorem add_lt_u128Limit_of_lt_u32Limit {a b : ℕ} :
    a < u32Limit → b < u32Limit → a + b < u128Limit := by
  intro ha hb
  have : u32Limit + u32Limit < u128Limit := by unfold u32Limit u128Limit; norm_num1
  exact lt_trans (add_lt_add ha hb) this

theorem add_lt_u128Limit_of_lt_u64Limit {a b : ℕ} :
    a < u64Limit → b < u64Limit → a + b < u128Limit := by
  intro ha hb
  have : u64Limit + u64Limit < u128Limit := by unfold u64Limit u128Limit; norm_num1
  exact lt_trans (add_lt_add ha hb) this

theorem u16Limit_eq_pow : u16Limit = 2 ^ 16 := by unfold u16Limit; norm_num1
theorem u32Limit_eq_pow : u32Limit = 2 ^ 32 := by unfold u32Limit; norm_num1
theorem u64Limit_eq_pow : u64Limit = 2 ^ 64 := by unfold u64Limit; norm_num1
theorem u128Limit_eq_pow : u128Limit = 2 ^ 128 := by unfold u128Limit; norm_num1

theorem u16Max_pos : u16Max > 0 := by decide
theorem u16Limit_pos : u16Limit > 0 := by decide
theorem u16Max_ne_zero : u16Max ≠ 0 := Nat.pos_iff_ne_zero.mp u16Max_pos
theorem u16Limit_ne_zero : u16Limit ≠ 0 := Nat.pos_iff_ne_zero.mp u16Limit_pos

theorem u16Max_coe_ne_zero : (u16Max : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u16Max_lt_PRIME rfl u16Max_ne_zero

theorem u16Max_coe_coe_ne_zero : ((u16Max : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u16Max_coe_ne_zero

theorem u16Limit_coe_ne_zero : (u16Limit : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u16Limit_lt_PRIME rfl u16Limit_ne_zero

theorem u16Limit_coe_coe_ne_zero : ((u16Limit : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u16Limit_coe_ne_zero

theorem u32Max_pos : u32Max > 0 := by decide
theorem u32Limit_pos : u32Limit > 0 := by decide
theorem u32Max_ne_zero : u32Max ≠ 0 := Nat.pos_iff_ne_zero.mp u32Max_pos
theorem u32Limit_ne_zero : u32Limit ≠ 0 := Nat.pos_iff_ne_zero.mp u32Limit_pos

theorem u32Max_coe_ne_zero : (u32Max : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u32Max_lt_PRIME rfl u32Max_ne_zero

theorem u32Max_coe_coe_ne_zero : ((u32Max : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u32Max_coe_ne_zero

theorem u32Limit_coe_ne_zero : (u32Limit : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u32Limit_lt_PRIME rfl u32Limit_ne_zero

theorem u32Limit_coe_coe_ne_zero : ((u32Limit : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u32Limit_coe_ne_zero

theorem u64Max_pos : u64Max > 0 := by decide
theorem u64Max_coe_pos : (u64Max : ℤ) > 0 := by decide
theorem u64Limit_pos : u64Limit > 0 := by decide
theorem u64Limit_coe_pos : (u64Limit : ℤ) > 0 := by decide
theorem u64Max_ne_zero : u64Max ≠ 0 := Nat.pos_iff_ne_zero.mp u64Max_pos
theorem u64Limit_ne_zero : u64Limit ≠ 0 := Nat.pos_iff_ne_zero.mp u64Limit_pos

theorem u64Max_coe_ne_zero : (u64Max : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u64Max_lt_PRIME rfl u64Max_ne_zero

theorem u64Max_coe_coe_ne_zero : ((u64Max : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u64Max_coe_ne_zero

theorem u64Limit_coe_ne_zero : (u64Limit : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u64Limit_lt_PRIME rfl u64Limit_ne_zero

theorem u64Limit_coe_coe_ne_zero : ((u64Limit : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u64Limit_coe_ne_zero

theorem u128Max_pos : u128Max > 0 := by decide
theorem u128Max_coe_pos : (u128Max : ℤ) > 0 := by decide
theorem u128Limit_pos : u128Limit > 0 := by decide
theorem u128Limit_coe_pos : (u128Limit : ℤ) > 0 := by decide
theorem u128Max_ne_zero : u128Max ≠ 0 := Nat.pos_iff_ne_zero.mp u128Max_pos
theorem u128Limit_ne_zero : u128Limit ≠ 0 := Nat.pos_iff_ne_zero.mp u128Limit_pos

theorem u128Max_coe_ne_zero : (u128Max : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u128Max_lt_PRIME rfl u128Max_ne_zero

theorem u128Max_coe_coe_ne_zero : ((u128Max : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u128Max_coe_ne_zero

theorem u128Limit_coe_ne_zero : (u128Limit : F) ≠ 0 :=
  PRIME.nat_coe_field_ne_zero u128Limit_lt_PRIME rfl u128Limit_ne_zero

theorem u128Limit_coe_coe_ne_zero : ((u128Limit : ℤ) : F) ≠ 0 := by
  rw [Nat.cast_ofNat, Int.cast_ofNat]; exact u128Limit_coe_ne_zero

theorem u32Limit_eq_u32Max_succ : u32Limit = u32Max + 1 := by
  unfold u32Limit u32Max; norm_num1

theorem u32Max_lt_u32Limit : u32Max < u32Limit := by
  rw [u32Limit_eq_u32Max_succ]; exact Nat.lt_succ_self _

-- Adding and subtracting within PRIME
theorem u128Limit_double_lt_PRIME : u128Limit + u128Limit < PRIME := by
  unfold u128Limit PRIME; norm_num1

theorem u128Limit_triple_lt_PRIME : u128Limit + u128Limit + u128Limit < PRIME := by
  unfold u128Limit PRIME; norm_num1

theorem u128Limit_quadruple_lt_PRIME :
    u128Limit + u128Limit + u128Limit + u128Limit < PRIME := by
  unfold u128Limit PRIME; norm_num1

theorem lt_PRIME_of_lt_u128Limit { a : ℕ } : a < u128Limit → a < PRIME :=
  fun ha => lt_trans ha u128Limit_lt_PRIME

theorem add_lt_PRIME_of_le {a b : ℕ} : a ≤ u128Limit → b ≤ u128Limit → a + b < PRIME :=
  fun ha hb => lt_of_le_of_lt (add_le_add ha hb) u128Limit_double_lt_PRIME

theorem add_lt_PRIME_of_lt {a b : ℕ} : a < u128Limit → b < u128Limit → a + b < PRIME :=
  fun ha hb => add_lt_PRIME_of_le (le_of_lt ha) (le_of_lt hb)

theorem sub_lt_PRIME_of_le {a : ℕ} : a < PRIME → ∀ b : ℕ, a - b < PRIME := fun ha b =>
  lt_of_le_of_lt (Nat.sub_le a b) ha

-- Adding and subtracting within u128_limit
theorem u16Limit_double_lt_PRIME : u16Limit + u16Limit < PRIME :=
  add_lt_PRIME_of_lt u16Limit_lt_u128Limit u16Limit_lt_u128Limit

theorem u32Limit_double_lt_PRIME : u32Limit + u32Limit < PRIME :=
  add_lt_PRIME_of_lt u32Limit_lt_u128Limit u32Limit_lt_u128Limit

theorem u64Limit_double_lt_PRIME : u64Limit + u64Limit < PRIME :=
  add_lt_PRIME_of_lt u64Limit_lt_u128Limit u64Limit_lt_u128Limit

/- Bounded addition -/

theorem lt_u128_add_lt_PRIME (a b : ℕ) : a < u128Limit → b < u128Limit → a + b < PRIME := by
  intros h_a_lt h_b_lt
  apply lt_trans (Nat.add_lt_add h_a_lt h_b_lt) u128Limit_double_lt_PRIME

theorem lt_u128_add_le_u128_lt_PRIME (a b : ℕ) : a < u128Limit → b ≤ u128Limit → a + b < PRIME := by
  intros h_a_lt h_b_le
  apply lt_of_le_of_lt (Nat.add_le_add (le_of_lt h_a_lt) h_b_le) u128Limit_double_lt_PRIME

theorem le_u128_add_le_u128_lt_PRIME (a b : ℕ) : a ≤ u128Limit → b ≤ u128Limit → a + b < PRIME := by
  intros h_a_le h_b_le
  apply lt_of_le_of_lt (Nat.add_le_add h_a_le h_b_le) u128Limit_double_lt_PRIME

theorem lt_u128_triple_add_lt_PRIME (a b c : ℕ) : a < u128Limit → b < u128Limit → c < u128Limit → a + b + c < PRIME := by
  intros h_a_lt h_b_lt h_c_lt
  apply lt_trans (Nat.add_lt_add (Nat.add_lt_add h_a_lt h_b_lt) h_c_lt) u128Limit_triple_lt_PRIME

/- Bounded addition and multiplication -/

theorem lt_u128_mul_u64_add_u128_lt_PRIME (a b c : ℕ) : a < u128Limit → b < u64Limit → c < u128Limit → a * b + c < PRIME := by
  intros h_a_lt h_b_lt h_c_lt
  apply lt_trans (Nat.add_lt_add (Nat.mul_lt_mul_of_lt_of_lt h_a_lt h_b_lt) h_c_lt)
  rw [PRIME] ; norm_num1

/- Squares -/

section
omit [PreludeHyps F]

theorem u16Limit_squared_eq : u16Limit * u16Limit = u32Limit := by norm_num1
theorem u16Limit_coe_squared_eq : (u16Limit : F) * u16Limit = u32Limit := by norm_num1

theorem u32Limit_squared_eq : u32Limit * u32Limit = u64Limit := by norm_num1
theorem u32Limit_coe_squared_eq : (u32Limit : F) * u32Limit = u64Limit := by norm_num1

theorem u64Limit_squared_eq : u64Limit * u64Limit = u128Limit := by norm_num1
theorem u64Limit_coe_squared_eq : (u64Limit : F) * u64Limit = u128Limit := by norm_num1

end

/-! # Casting of nats into field elements, bounded -/

def is_u16_of (a : F) (na : ℕ) : Prop := na < u16Limit ∧ a = ↑na
def is_u32_of (a : F) (na : ℕ) : Prop := na < u32Limit ∧ a = ↑na
def is_u64_of (a : F) (na : ℕ) : Prop := na < u64Limit ∧ a = ↑na
def is_u128_of (a : F) (na : ℕ) : Prop := na < u128Limit ∧ a = ↑na

/-! # Forming higher-bit numbers with "limbs" -/

def u256_from_limbs (na nb : ℕ) : ℕ := (u128Limit * na) + nb

def u512_from_limbs (na nb nc nd : ℕ) : ℕ :=
  (u128Limit^3 * na) + (u128Limit^2 * nb) + (u128Limit * nc) + nd

/-! # u128 multiplication guarantee -/

def u128_mul_guarantee (a b upper lower : F) : Prop :=
  ∀ ⦃na⦄, is_u128_of a na →
  ∀ ⦃nb⦄, is_u128_of b nb →
  ∃ nh : ℕ, is_u128_of upper nh ∧
  ∃ nl : ℕ, is_u128_of lower nl ∧
    na * nb = u256_from_limbs nh nl

end

/-
General theorems.
TODO: move some of these elsewhere?
-/

namespace Nat

/-! # Divides -/

theorem dvd_sub_of_mul_add_eq_mul_add {a b c d e : ℕ} : a * b + c = a * d + e → a ∣ e - c := by
  intro h
  rcases le_or_gt c e with (h_le | h_gt)
  · have := eq_tsub_of_add_eq h
    rw [Nat.add_sub_assoc h_le (a * d), add_comm] at this
    replace this := tsub_eq_of_eq_add this
    rw [← Nat.mul_sub_left_distrib] at this
    exact Dvd.intro _ this
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h_gt)]
    exact dvd_zero _

/-! # Square root -/

theorem sqrt_lt_of_lt_square {a b : ℕ} : a < b * b → sqrt a < b := by
  intro h
  have := sqrt_le_sqrt (le_of_lt h)
  rw [sqrt_eq b] at this
  rcases eq_or_lt_of_le this with (ha | ha)
  · rw [← ha] at h
    exact absurd h (not_lt.mpr (sqrt_le a))
  · exact ha

theorem le_sqrt_of_square_le {a b : ℕ} : a * a ≤ b → a ≤ sqrt b := by
  intro h
  have := sqrt_le_sqrt h
  rw [sqrt_eq a] at this
  exact this

theorem le_sqrt_of_square_lt {a b : ℕ} : a * a < b → a ≤ sqrt b :=
  fun h => le_sqrt_of_square_le (le_of_lt h)

end Nat

/-! # Inequality reasoning -/

theorem add_sub_lt {a b c : ℕ} (hb : 0 < b) (hac : a < c) : a + b - c < b := by
  by_cases h : a + b ≤ c
  · rwa [Nat.sub_eq_zero_of_le h]
  rw [← Nat.succ_le_iff]; rw [← Nat.succ_sub (le_of_lt (lt_of_not_le h))]
  have h_ab_le : (a + b).succ ≤ c + b := by
    rw [← Nat.succ_add]
    apply Nat.add_le_add_right
    apply Nat.succ_le_of_lt
    assumption
  apply le_trans (Nat.sub_le_sub_right h_ab_le _); rw [Nat.add_sub_cancel_left]

theorem lt_of_add_sub_lt {a b c : ℕ} : a + (b - c) < b → a < c := by
  intro h
  by_cases h_c_b : c ≤ b
  · conv_rhs at h => rw [←Nat.add_sub_self_left c b]
    rw [Nat.add_sub_assoc h_c_b] at h
    rw [Nat.add_lt_add_iff_right] at h ; apply h
  rw [←lt_iff_not_le] at h_c_b
  rw [Nat.sub_eq_zero_of_le (le_of_lt h_c_b), add_zero] at h
  exact lt_trans h h_c_b

theorem sub_le_sub_of_lt {a b c : ℕ} : b < c → a - c ≤ a - b := fun hb =>
  tsub_le_tsub_left (le_of_lt hb) _

theorem sub_lt_sub_of_lt_of_lt {a b k : ℕ} : b < k → b < a → a - k < a - b := by
  intro hk ha
  induction' a with a ih generalizing b k
  · exact absurd ha (Nat.not_lt_zero _)
  · cases k
    · exact absurd hk (Nat.not_lt_zero _)
    · cases b
      · rw [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
        exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
      · rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
        exact ih (Nat.succ_lt_succ_iff.mp hk) (Nat.succ_lt_succ_iff.mp ha)

theorem sub_lt_add_sub_of_lt_of_lt {a c k : ℕ} : c < k → c < a → ∀ b : ℕ, a - k < a + b - c :=
  fun hk ha _ => lt_of_lt_of_le (sub_lt_sub_of_lt_of_lt hk ha) (tsub_le_tsub_right le_self_add c)

theorem add_lt_of_left_lt_of_add_lt {a b c d : ℕ} : a < b → b + c < d → a + c < d :=
  fun ha => lt_trans (Nat.add_lt_add_right ha _)

theorem add_lt_of_right_lt_of_add_lt {a b c d : ℕ} : b < c → a + c < d → a + b < d :=
  fun hb => lt_trans (Nat.add_lt_add_left hb _)

theorem add_lt_of_left_lt_of_lt_sub {a b c d : ℕ} : a < b → b < d - c → a + c < d :=
  fun ha hb => Nat.add_lt_of_lt_sub (lt_trans ha hb)

theorem add_lt_of_left_lt_of_lt_sub' {a b c d : ℕ} : a < b → c < d - b → a + c < d :=
  fun ha hc => add_lt_of_left_lt_of_add_lt ha
    (add_comm b c ▸ Nat.add_lt_of_lt_sub hc)

theorem add_lt_of_right_lt_of_lt_sub {a b c d : ℕ} : b < c → a < d - c → a + b < d :=
  fun hb ha => add_lt_of_right_lt_of_add_lt hb
    (Nat.add_lt_of_lt_sub ha)

theorem add_lt_of_right_lt_of_lt_sub' {a b c d : ℕ} : b < c → c < d - a → a + b < d :=
  fun hb hc => add_lt_of_right_lt_of_add_lt hb
    (add_comm a c ▸ Nat.add_lt_of_lt_sub hc)

theorem Int.add_lt_of_left_lt_of_add_lt {a b c d : ℤ} : a < b → b + c < d → a + c < d :=
  fun ha => lt_trans (Int.add_lt_add_right ha _)

theorem Int.add_lt_of_right_lt_of_add_lt {a b c d : ℤ} : b < c → a + c < d → a + b < d :=
  fun hb => lt_trans (Int.add_lt_add_left hb _)

theorem Int.add_lt_of_left_lt_of_lt_sub {a b c d : ℤ} : a < b → b < d - c → a + c < d :=
  fun ha hb => Int.add_lt_of_lt_sub_right (lt_trans ha hb)

theorem Int.add_lt_of_left_lt_of_lt_sub' {a b c d : ℤ} : a < b → c < d - b → a + c < d :=
  fun ha hc => Int.add_lt_of_left_lt_of_add_lt ha
    (add_comm b c ▸ Int.add_lt_of_lt_sub_right hc)

theorem Int.add_lt_of_right_lt_of_lt_sub {a b c d : ℤ} : b < c → a < d - c → a + b < d :=
  fun hb ha => Int.add_lt_of_right_lt_of_add_lt hb
    (Int.add_lt_of_lt_sub_right ha)

theorem Int.add_lt_of_right_lt_of_lt_sub' {a b c d : ℤ} : b < c → c < d - a → a + b < d :=
  fun hb hc => Int.add_lt_of_right_lt_of_add_lt hb
    (add_comm a c ▸ Int.add_lt_of_lt_sub_right hc)

theorem Int.eq_sub_emod_iff_add_emod_eq {a b c : ℤ} :
    a % PRIME = (b - c) % PRIME ↔ (a + c) % PRIME = b % PRIME := by
  simp only [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  rw [Int.sub_eq_add_neg, Int.neg_sub, ←Int.add_sub_assoc]

theorem Int.sub_nonneg_toNat {z : Int} {a b : ℕ} (h : z = a - b) (h_lt : b ≤ a) :
    z.toNat = a - b := by
  rw [←(Int.natCast_sub h_lt)] at h
  have h_z_nonneg : 0 ≤ z := by rw [h] ; apply Int.natCast_nonneg
  rwa [←(Int.toNat_of_nonneg h_z_nonneg), Int.ofNat_inj] at h
