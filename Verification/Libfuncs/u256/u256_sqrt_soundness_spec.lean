import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Tactic
set_option autoImplicit false
set_option maxRecDepth 1024

namespace u256_sqrt_soundness

variable {F : Type} [Field F] [DecidableEq F] [PreludeHyps F]

def u64_limit : F := (18446744073709551616 : F) -- (BigInt::from(u64::MAX) + 1) as BigInt
def u128_limit : F := (340282366920938463463374607431768211456 : F) -- (BigInt::from(u128::MAX) + 1) as BigInt
def u128_bound_minus_u65_bound : F := (340282366920938463426481119284349108224 : F) -- BigInt::from(2).pow(128) - BigInt::from(2).pow(65)
def u128_half : F := (170141183460469231731687303715884105728 : F) -- u128::MAX / 2 + 1

@[reducible, inline] def u128Bound_minus_u65Bound : ℕ := 340282366920938463426481119284349108224

theorem u128_limit_eq : u128_limit = (u128Limit : F) := by unfold u128_limit u128Limit ; norm_cast
theorem u64_limit_eq : u64_limit = (u64Limit : F) := by unfold u64_limit u64Limit ; norm_cast
theorem u128_bound_minus_u65_bound_eq : u128_bound_minus_u65_bound = (↑(u128Limit - u65Limit) : F) := by
  unfold u128_bound_minus_u65_bound u128Limit u65Limit ; norm_num1

theorem u128_bound_minus_u65_bound_eq' : u128_bound_minus_u65_bound = (u128Limit : F) - (u65Limit : F) := by
  unfold u128_bound_minus_u65_bound u128Limit u65Limit
  rw [←Nat.cast_sub] ; norm_cast ; norm_num1

theorem u128Bound_eq : u128Bound_minus_u65Bound = u128Limit - u65Limit := by
  unfold u128Bound_minus_u65Bound u128Limit u65Limit; norm_num1

-- u128::MAX / 2 + 1
def u128Half : ℕ := 170141183460469231731687303715884105728

theorem u128Half_eq : u128Half = u128Limit / 2 := by
  unfold u128Half u128Limit; norm_num1

theorem u128_half_eq : u128_half = ((u128Half : ℤ) : F) := by
  unfold u128_half u128Half ; norm_num1
theorem u64_limit_eq_coe : u64_limit = ((u64Limit : ℤ) : F) := by unfold u64_limit u64Limit ; norm_cast

def spec_u256_sqrt (κ : ℕ) (range_check value_low value_high ρ_sqrt : F) : Prop :=
  ∀ nlow, is_u128_of value_low nlow  →
  ∀ nhigh, is_u128_of value_high nhigh  →
  is_u128_of ρ_sqrt (u256_from_limbs nhigh nlow).sqrt

def auto_spec_u256_sqrt_Done (κ : ℕ) (range_check sqrt ρ_sqrt : F) : Prop :=
  ρ_sqrt = sqrt

def auto_spec_u256_sqrt_SqrtMul2MinusRemainderGeU128 (κ : ℕ) (range_check sqrt sqrt_mul_2_minus_remainder fixed_sqrt_mul_2_minus_remainder ρ_sqrt : F) : Prop :=
  fixed_sqrt_mul_2_minus_remainder = sqrt_mul_2_minus_remainder - u128_limit ∧
  IsRangeChecked (rcBound F) fixed_sqrt_mul_2_minus_remainder ∧
  ∃ (κ₁ : ℕ), auto_spec_u256_sqrt_Done κ₁
    range_check sqrt ρ_sqrt

def auto_spec_u256_sqrt (κ : ℕ) (range_check value_low value_high ρ_sqrt : F) : Prop :=
  ∃ orig_range_check : F, orig_range_check = range_check ∧
  ∃ sqrt0 : F,
  ∃ sqrt1 : F,
  ∃ remainder_low : F,
  ∃ remainder_high : F,
  ∃ sqrt_mul_2_minus_remainder_ge_u128 : F,
  IsRangeChecked (rcBound F) sqrt0 ∧
  IsRangeChecked (rcBound F) sqrt1 ∧
  ∃ sqrt0_plus_sqrt1 : F, sqrt0_plus_sqrt1 = sqrt0 + sqrt1 ∧
  ∃ a : F, a = sqrt0_plus_sqrt1 + u128_bound_minus_u65_bound ∧
  IsRangeChecked (rcBound F) a ∧
  IsRangeChecked (rcBound F) remainder_low ∧
  remainder_high = remainder_high * remainder_high ∧
  ∃ element : F, element = sqrt0 * sqrt0 ∧
  ∃ accum0 : F, accum0 = remainder_low + element ∧
  ∃ accum1 : F, accum1 = accum0 - value_low ∧
  ∃ accum2 : F, accum2 = accum1 / u64_limit ∧
  ∃ temp : F, temp = accum2 + u128_half ∧
  IsRangeChecked (rcBound F) temp ∧
  ∃ element₁ : F, element₁ = sqrt0 * sqrt1 ∧
  ∃ accum3 : F, accum3 = accum2 + element₁ ∧
  ∃ accum4 : F, accum4 = accum3 + element₁ ∧
  ∃ accum5 : F, accum5 = accum4 / u64_limit ∧
  IsRangeChecked (rcBound F) accum5 ∧
  ∃ accum6 : F, accum6 = accum5 + remainder_high ∧
  ∃ element₂ : F, element₂ = sqrt1 * sqrt1 ∧
  value_high = accum6 + element₂ ∧
  ∃ shifted_sqrt1 : F, shifted_sqrt1 = sqrt1 * u64_limit ∧
  ∃ sqrt : F, sqrt = sqrt0 + shifted_sqrt1 ∧
  ∃ shifted_remainder_high : F, shifted_remainder_high = remainder_high * u128_limit ∧
  ∃ remainder : F, remainder = remainder_low + shifted_remainder_high ∧
  ∃ sqrt_mul_2 : F, sqrt_mul_2 = sqrt + sqrt ∧
  ∃ sqrt_mul_2_minus_remainder : F, sqrt_mul_2_minus_remainder = sqrt_mul_2 - remainder ∧
  ∃ fixed_sqrt_mul_2_minus_remainder : F,
  (
    (sqrt_mul_2_minus_remainder_ge_u128 = 0 ∧
      IsRangeChecked (rcBound F) sqrt_mul_2_minus_remainder ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_sqrt_Done κ₁
        range_check sqrt ρ_sqrt
    ) ∨
    (sqrt_mul_2_minus_remainder_ge_u128 ≠ 0 ∧
      ∃ (κ₁ : ℕ), auto_spec_u256_sqrt_SqrtMul2MinusRemainderGeU128 κ₁
        range_check sqrt sqrt_mul_2_minus_remainder fixed_sqrt_mul_2_minus_remainder ρ_sqrt
    )
  )

theorem u64_square_distrib (a b : ℕ) :
  (a + b * u64Limit) * (a + b * u64Limit) =
    a * a + a * b * u64Limit + a * b * u64Limit + (b * b * u128Limit) := by ring

theorem sound_u256_sqrt
    (κ : ℕ)
    (range_check value_low value_high ρ_sqrt : F)
    (h_auto : auto_spec_u256_sqrt κ range_check value_low value_high ρ_sqrt) :
  spec_u256_sqrt κ range_check value_low value_high ρ_sqrt := by

  rintro nl ⟨h_nl_lt, rfl⟩ nh ⟨h_nh_lt, rfl⟩
  constructor
  · apply Nat.sqrt_lt_of_lt_square
    apply lt_of_lt_of_le (add_lt_add_left h_nl_lt _)
    -- Undo a multiplicative distribution
    conv => lhs; rhs; rw [← mul_one u128Limit]
    rw [← mul_add]
    exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h_nh_lt)

  have h_rcBound := @rcBound_hyp F
  rw [← u128Limit_eq_pow] at h_rcBound

  -- Unfold the autospec until a range check
  rcases h_auto with ⟨-, -, sqrt0, sqrt1, rem_low, rh, rge, h_rc_sqrt0, h_auto⟩

  rcases h_rc_sqrt0 with ⟨sqrt0, h_sqrt0_lt, rfl⟩
  replace h_sqrt0_lt := lt_of_lt_of_le h_sqrt0_lt h_rcBound

  -- Keep unfolding the autospec
  rcases h_auto with ⟨h_rc_sqrt1, _, rfl, h_auto⟩

  rcases h_rc_sqrt1 with ⟨sqrt1, h_sqrt1_lt, rfl⟩
  replace h_sqrt1_lt := lt_of_lt_of_le h_sqrt1_lt h_rcBound

  -- Keep unfolding the autospec
  rcases h_auto with ⟨_, rfl, h_rc_a, h_auto⟩
  rcases h_rc_a with ⟨a, h_a_lt, ha⟩
  replace h_a_lt := lt_of_lt_of_le h_a_lt h_rcBound

  have h₁ : sqrt0 + sqrt1 + u128Bound_minus_u65Bound < PRIME := by
    apply Nat.add_lt_of_lt_sub
    apply add_lt_of_left_lt_of_add_lt h_sqrt0_lt
    apply add_lt_of_right_lt_of_add_lt h_sqrt1_lt
    unfold PRIME
    norm_num1
  rw [u128_bound_minus_u65_bound_eq, ← Nat.cast_add, ← Nat.cast_add] at ha
  have := PRIME.nat_coe_field_inj h₁ (lt_trans h_a_lt u128Limit_lt_PRIME) ha
  subst this
  clear h₁ ha
  rw [u128Bound_eq] at h_a_lt
  replace h_a_lt := lt_tsub_iff_right.mpr h_a_lt
  rw [Nat.sub_sub_self (by norm_num1)] at h_a_lt

  -- Update the sqrt0 and sqrt1 inequalities
  replace h_sqrt0_lt := lt_of_le_of_lt (Nat.le_add_right _ _) h_a_lt
  replace h_sqrt1_lt := lt_of_le_of_lt (Nat.le_add_left _ _) h_a_lt
  clear h_a_lt

  -- Keep unfolding the autospec
  rcases h_auto with ⟨h_rc_rl, h_auto⟩

  -- Low limb of the remainder, range checked
  rcases h_rc_rl with ⟨rl, h_rl_lt, rfl⟩
  replace h_rl_lt := lt_of_lt_of_le h_rl_lt h_rcBound

  -- Keep unfolding the autospec
  rcases h_auto with ⟨h_rh, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, h_rc_temp, h_auto⟩

  -- Update the range checks
  rcases h_rc_temp with ⟨temp, h_temp_lt, h_temp⟩
  replace h_temp_lt := lt_of_lt_of_le h_temp_lt h_rcBound

  simp only [coe_eq_int_coe_coe, ← Int.cast_add, ← Int.cast_mul, ← Int.cast_sub] at h_temp
  rw [← eq_sub_iff_add_eq] at h_temp
  rw [div_eq_iff_mul_eq u64Limit_coe_ne_zero] at h_temp
  rw [u128_half_eq, u64_limit_eq_coe, ← Int.cast_sub, ← Int.cast_mul] at h_temp
  have : |(↑rl : ℤ) + ↑sqrt0 * ↑sqrt0 - ↑nl - (↑temp - ↑u128Half) * ↑u64Limit| < ↑PRIME := by
    rw [Int.sub_mul]
    rw [← sub_add]
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul]
    rw [Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_lt_sub_right
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub
      (Int.mul_lt_mul_of_pos_right (Int.ofNat_lt.mpr h_temp_lt) u64Limit_coe_pos)
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_nl_lt)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_left_lt_of_lt_sub' (Int.ofNat_lt.mpr h_rl_lt)
    rw [abs_mul, Int.abs_natCast]
    apply lt_trans (Int.ofNat_lt.mpr (Nat.mul_self_lt_mul_self h_sqrt0_lt))
    rw [u128Half_eq]
    unfold PRIME
    norm_num1

  replace this := PRIME.int_coe_inj h_temp this
  rw [mul_comm] at this
  have h_dvd := Dvd.intro _ this
  clear this h_temp h_temp_lt temp

  have h_ct : sqrt0 * sqrt1 < u65Limit * u65Limit :=
    Nat.mul_lt_mul_of_lt_of_lt h_sqrt0_lt h_sqrt1_lt

  -- Keep unfolding the autospec
  rcases h_auto with ⟨_, rfl, _, rfl, _, rfl, _, rfl, h_accum5_rc, h_auto⟩

  -- Rearrange the field elements so there are only additions and multiplications
  rcases h_accum5_rc with ⟨accum5, h_accum5_lt, h_accum5⟩
  replace h_accum5_lt := lt_of_lt_of_le h_accum5_lt h_rcBound
  simp only [coe_eq_int_coe_coe, ← Int.cast_add, ← Int.cast_mul, ← Int.cast_sub] at h_accum5
  rw [u64_limit_eq_coe, ← Int.cast_div h_dvd u64Limit_coe_coe_ne_zero] at h_accum5
  rw [div_eq_iff_mul_eq u64Limit_coe_coe_ne_zero] at h_accum5
  simp only [← Int.cast_mul, ← Int.cast_add] at h_accum5
  have : |((↑rl : ℤ) + ↑sqrt0 * ↑sqrt0 - ↑nl) / ↑u64Limit + ↑sqrt0 * ↑sqrt1 + ↑sqrt0 * ↑sqrt1 - ↑accum5 * ↑u64Limit| < ↑PRIME := by
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.mul_lt_mul_of_pos_right (Int.ofNat_lt.mpr h_accum5_lt) u64Limit_coe_pos)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_ct)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_ct)
    apply lt_of_le_of_lt (Int.abs_ediv_le_abs _ _)
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_nl_lt)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_left_lt_of_lt_sub' (Int.ofNat_lt.mpr h_rl_lt)
    apply lt_trans (Int.ofNat_lt.mpr (Nat.mul_self_lt_mul_self h_sqrt0_lt))
    unfold u65Limit PRIME
    norm_num1
  replace this := PRIME.int_coe_inj h_accum5 this
  rw [mul_comm] at this
  have h_dvd₂ := Dvd.intro _ this
  clear this h_accum5 h_accum5_lt accum5

  -- Keep unfolding the autospec
  rcases h_auto with ⟨_, rfl, _, rfl, h_root_eq, h_auto⟩
  rcases h_auto with ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, h_auto⟩

  -- The high limb of the remainder term is either 0 or 1
  replace h_rh : rh = 0 ∨ rh = 1 := by
    by_cases h : rh = 0
    · exact Or.inl h
    · have := congrArg (fun x => x / rh) h_rh
      simp only at this
      rw [div_self h, ← mul_div, div_self h, mul_one] at this
      exact Or.inr this.symm

  have h_nrh : ∃ (nrh : ℕ), (nrh = 0 ∨ nrh = 1) ∧ ↑nrh = rh := by
    rcases h_rh with (h | h)
    · use 0, Or.inl rfl
      rw [Nat.cast_zero]
      exact h.symm
    · use 1, Or.inr rfl
      rw [Nat.cast_one]
      exact h.symm
  clear h_rh
  rcases h_nrh with ⟨nrh, h_nrh, rfl⟩
  have h_nrh_lt : nrh < 2 := by
    rcases h_nrh with (rfl | rfl) <;> norm_num1

  rw [← zero_add (↑nh : F), ← Int.cast_zero, ← eq_sub_iff_add_eq] at h_root_eq
  simp only [coe_eq_int_coe_coe, ← Int.cast_add, ← Int.cast_mul, ← Int.cast_sub] at h_root_eq
  rw [u64_limit_eq_coe, ← Int.cast_div h_dvd u64Limit_coe_coe_ne_zero] at h_root_eq
  simp only [← Int.cast_add, ← Int.cast_mul] at h_root_eq
  rw [← Int.cast_div h_dvd₂ u64Limit_coe_coe_ne_zero] at h_root_eq
  simp only [← Int.cast_add, ← Int.cast_mul, ← Int.cast_sub] at h_root_eq
  have : |(((↑rl : ℤ) + ↑sqrt0 * ↑sqrt0 - ↑nl) / ↑u64Limit + ↑sqrt0 * ↑sqrt1 + ↑sqrt0 * ↑sqrt1) / ↑u64Limit + ↑nrh + ↑sqrt1 * ↑sqrt1 - ↑nh - ↑0| < ↑PRIME := by
    rw [sub_zero]
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_nh_lt)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr (Nat.mul_self_lt_mul_self h_sqrt1_lt))
    apply lt_of_le_of_lt (abs_add _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_nrh_lt)
    apply lt_of_le_of_lt (Int.abs_ediv_le_abs _ _)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_ct)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_ct)
    apply lt_of_le_of_lt (Int.abs_ediv_le_abs _ _)
    apply lt_of_le_of_lt (abs_sub _ _)
    rw [Int.abs_natCast]
    apply Int.add_lt_of_right_lt_of_lt_sub (Int.ofNat_lt.mpr h_nl_lt)
    apply lt_of_le_of_lt (abs_add _ _)
    rw [abs_mul, Int.abs_natCast, Int.abs_natCast]
    apply Int.add_lt_of_left_lt_of_lt_sub' (Int.ofNat_lt.mpr h_rl_lt)
    apply lt_trans (Int.ofNat_lt.mpr (Nat.mul_self_lt_mul_self h_sqrt0_lt))
    unfold u65Limit PRIME
    norm_num1
  replace this := PRIME.int_coe_inj h_root_eq this
  clear h_nrh_lt

  -- Rearrange the division in `this` to cast back into Nat
  rw [eq_sub_iff_add_eq, zero_add,
    ← sub_eq_iff_eq_add, ← sub_eq_iff_eq_add] at this
  symm at this
  rw [Int.ediv_eq_iff_eq_mul_right (by norm_num1) h_dvd₂,
    ← eq_sub_iff_add_eq, ← eq_sub_iff_add_eq,
    Int.ediv_eq_iff_eq_mul_right (by norm_num1) h_dvd] at this
  simp only [Int.mul_sub] at this
  simp only [← Int.mul_assoc] at this
  have h_coe : (↑u64Limit : ℤ) * ↑u64Limit = ↑(u64Limit * u64Limit) := by rfl
  rw [h_coe, u64Limit_squared_eq] at this
  clear h_coe
  rw [sub_eq_iff_eq_add] at this
  simp only [sub_add_eq_add_sub] at this
  simp only [eq_sub_iff_add_eq] at this
  have h_rearr : (↑rl : ℤ) + ↑sqrt0 * ↑sqrt0 + ↑u64Limit * ↑sqrt0 * ↑sqrt1 + ↑u64Limit * ↑sqrt0 * ↑sqrt1 + ↑u128Limit * ↑nrh +
  ↑u128Limit * ↑sqrt1 * ↑sqrt1 = ↑sqrt0 * ↑sqrt0 + ↑sqrt0 * ↑sqrt1 * ↑u64Limit + ↑sqrt0 * ↑sqrt1 * ↑u64Limit + ↑sqrt1 * ↑sqrt1 * ↑u128Limit + ↑rl +
  ↑nrh * ↑u128Limit := by ring
  rw [h_rearr] at this
  clear h_rearr
  have h_rearr : (↑u128Limit : ℤ) * ↑nh + ↑nl = ↑nh * ↑u128Limit + ↑nl := by ring
  rw [h_rearr] at this
  clear h_rearr
  symm at this
  replace h_root_eq := Nat.cast_inj.mp this
  clear this

  -- The overall proof is by antisymmetry, so prove ( ≤ ) and ( ≥ ) separately
  -- ( ≤ ) can be proven regardless of which branch we fall into
  have h_le : sqrt0 + sqrt1 * u64Limit ≤ Nat.sqrt (nh * u128Limit + nl) := by
    apply Nat.le_sqrt_of_square_le
    rw [u64_square_distrib]
    symm at h_root_eq
    rw [add_assoc] at h_root_eq
    exact Nat.le.intro h_root_eq

  have h_id : sqrt0 * sqrt0 + sqrt0 * sqrt1 * u64Limit + sqrt0 * sqrt1 * u64Limit + sqrt1 * sqrt1 * u128Limit + rl + nrh * u128Limit = (nrh * u128Limit + rl) + (sqrt0 * sqrt0 + sqrt0 * sqrt1 * u64Limit + sqrt0 * sqrt1 * u64Limit + sqrt1 * sqrt1 * u128Limit) := by ring
  rw [h_id] at h_root_eq
  clear h_id

  -- The cross-terms are less than PRIME
  have h_ct_lt : sqrt0 + sqrt1 * u64Limit + sqrt0 + sqrt1 * u64Limit < PRIME := by
    apply add_lt_of_right_lt_of_lt_sub (Nat.mul_lt_mul_of_pos_right h_sqrt1_lt u64Limit_pos)
    apply add_lt_of_right_lt_of_lt_sub (h_sqrt0_lt)
    apply add_lt_of_right_lt_of_lt_sub (Nat.mul_lt_mul_of_pos_right h_sqrt1_lt u64Limit_pos)
    apply lt_trans h_sqrt0_lt
    unfold u65Limit PRIME
    norm_num1
  clear h_sqrt0_lt h_sqrt1_lt

  -- Some helpful (identity) algebraic rearrangements, solved by the `ring` tactic
  have h_id : sqrt0 * sqrt0 + sqrt1 * u64Limit * sqrt0 + sqrt0 +
    (sqrt0 * (sqrt1 * u64Limit) + sqrt1 * u64Limit * (sqrt1 * u64Limit) +
      sqrt1 * u64Limit) + (sqrt0 + sqrt1 * u64Limit + 1) =
    (sqrt0 + sqrt1 * u64Limit + sqrt0 + sqrt1 * u64Limit + 1) +
    (sqrt0 * sqrt0 + sqrt0 * sqrt1 * u64Limit + sqrt0 * sqrt1 * u64Limit +
      sqrt1 * sqrt1 * u128Limit) := by ring

  -- Keep unfolding the autospec
  rcases h_auto with ⟨fsm2mr, ⟨rfl, ⟨sm2mr, h_sm2mr_lt, h_sm2mr⟩, -, rfl⟩ | ⟨h_rge, -, h_fsm2mr, h_fsm2mr_rc, -, rfl⟩⟩
  · replace h_sm2mr_lt := lt_of_lt_of_le h_sm2mr_lt h_rcBound
    clear h_rcBound
    rw [u64_limit_eq, ← Nat.cast_mul, ← Nat.cast_add]

    have h_ge : sqrt0 + sqrt1 * u64Limit ≥ Nat.sqrt (nh * u128Limit + nl) := by
      apply Nat.le_of_lt_succ
      apply Nat.sqrt_lt_of_lt_square
      simp only [Nat.succ_eq_add_one, mul_add, add_mul, one_mul, mul_one]
      rw [u64_limit_eq, u128_limit_eq, sub_eq_iff_eq_add, ← add_assoc, ← add_assoc] at h_sm2mr
      simp only [← Nat.cast_add, ← Nat.cast_mul] at h_sm2mr
      have h₂ : sm2mr + rl + nrh * u128Limit < PRIME := by
        rcases h_nrh with (rfl | rfl)
        · rw [zero_mul, add_zero]
          exact add_lt_PRIME_of_lt h_sm2mr_lt h_rl_lt
        · rw [one_mul, add_assoc, add_comm]
          apply lt_trans ((add_lt_add_iff_left _).mpr h_sm2mr_lt)
          rw [add_assoc]
          apply lt_trans ((add_lt_add_iff_right _).mpr h_rl_lt)
          rw [← add_assoc]
          exact u128Limit_triple_lt_PRIME
      replace h_sm2mr := PRIME.nat_coe_field_inj h_ct_lt h₂ h_sm2mr
      symm at h_sm2mr
      rw [add_assoc, add_comm, add_comm rl _] at h_sm2mr
      replace h_sm2mr := Nat.lt_succ_of_le (Nat.le.intro h_sm2mr)
      rw [Nat.succ_eq_add_one] at h_sm2mr
      -- Rearrange terms algebraically, as an identity operation
      rw [h_root_eq, h_id]
      exact (add_lt_add_iff_right _).mpr h_sm2mr
    rw [antisymm h_le h_ge, mul_comm, u256_from_limbs]
  · clear h_rge rge
    rcases h_fsm2mr_rc with ⟨fsm2mr, h_fsm2mr_lt, rfl⟩
    replace h_fsm2mr_lt := lt_of_lt_of_le h_fsm2mr_lt h_rcBound
    clear h_rcBound
    rw [u64_limit_eq, ← Nat.cast_mul, ← Nat.cast_add]

    have h_ge : sqrt0 + sqrt1 * u64Limit ≥ Nat.sqrt (nh * u128Limit + nl) := by
      apply Nat.le_of_lt_succ
      apply Nat.sqrt_lt_of_lt_square
      simp only [Nat.succ_eq_add_one, mul_add, add_mul, one_mul, mul_one]
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, ← add_assoc, ← add_assoc] at h_fsm2mr
      simp only [u64_limit_eq, u128_limit_eq, ← Nat.cast_add, ← Nat.cast_mul] at h_fsm2mr
      have h₁ : fsm2mr + u128Limit + rl + nrh * u128Limit < PRIME := by
        rw [add_assoc, add_assoc]
        apply lt_trans ((add_lt_add_iff_right _).mpr h_fsm2mr_lt)
        rw [← add_assoc, add_comm rl _, ← add_assoc]
        rcases h_nrh with (rfl | rfl)
        · rw [zero_mul, add_zero]
          apply lt_trans ((add_lt_add_iff_left _).mpr h_rl_lt)
          exact u128Limit_triple_lt_PRIME
        · rw [one_mul]
          apply lt_trans ((add_lt_add_iff_left _).mpr h_rl_lt)
          exact u128Limit_quadruple_lt_PRIME
      replace h_fsm2mr := PRIME.nat_coe_field_inj h₁ h_ct_lt h_fsm2mr
      rw [add_assoc, add_comm, add_comm rl _] at h_fsm2mr
      replace h_fsm2mr := Nat.lt_succ_of_le (Nat.le.intro h_fsm2mr)
      rw [Nat.succ_eq_add_one] at h_fsm2mr
      -- Rearrange terms algebraically, as an identity operation
      rw [h_root_eq, h_id]
      exact (add_lt_add_iff_right _).mpr h_fsm2mr
    rw [antisymm h_le h_ge, mul_comm, u256_from_limbs]
