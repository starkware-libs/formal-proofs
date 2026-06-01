/-
Some helper functions and theorems for the opcode definitions.
-/
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive

open Fin.NatCast

theorem felt252_to_m31_calc [Fact (Nat.Prime Stwo.P)] (xn : Felt252Nats)
    (h : ∀ i, xn i < 2 ^ 9) :
    xn 0 + xn 1 * 2 ^ 9 + xn 2 * 2 ^ 18 < 2^27 := by
  apply lt_of_le_of_lt (b := (2^9 - 1) + (2^9 - 1) * 2 ^ 9 + (2^9 - 1) * 2 ^ 18); swap
  . simp
  gcongr
  . have := h 0; omega
  . have := h 1; omega
  . have := h 2; omega

theorem felt252_to_m31_calc' [Fact (Nat.Prime Stwo.P)]
    {x : Felt252Words}
    {xn : Felt252Nats}
    (hxn : xn.IsRangeChecked x) :
    felt252_to_m31_val x ADDRESS_BITS = (∑ i ∈ Finset.range 4, (↑(xn ↑i) : Felt) * 2 ^ (9 * i)) := by
  rw [Felt252Nats.IsRangeChecked] at hxn
  rw [felt252_to_m31_val_eq_val', felt252_to_m31_val']
  rw [if_neg]; swap; simp [ADDRESS_BITS]
  simp only [Nat.div_ceil, ADDRESS_BITS, FELT252_BITS_PER_WORD, Nat.reduceAdd, Nat.add_one_sub_one,
    Nat.reduceDiv]
  simp only [hxn]

theorem felt252_to_m31_calc'' [Fact (Nat.Prime Stwo.P)] (xn : Felt252Nats)
    (h : ∀ i, xn i < 2 ^ 9)
    (h' : xn 3 < 2 ^ 2) :
    xn 0 + xn 1 * 2 ^ 9 + xn 2 * 2 ^ 18 + xn 3 * 2 ^ 27 < 2^29 := by
  apply lt_of_le_of_lt (b := (2^9 - 1) + (2^9 - 1) * 2 ^ 9 + (2^9 - 1) * 2 ^ 18 + (2^2 - 1) * 2 ^ 27); swap
  . simp
  gcongr
  . have := h 0; omega
  . have := h 1; omega
  . have := h 2; omega
  . have := h'; omega

theorem felt252_to_m31_eq_aux [Fact (Nat.Prime Stwo.P)] (xn : Felt252Nats)
  (h : ∀ i, xn i < 2^9)
  (h' : xn 3 < 2 ^ 2) :
  (∑ i ∈ Finset.range 4, (↑(xn ↑i) : Felt) * 2 ^ (9 * i)).toFelt252 =
    (∑ i ∈ Finset.range 4, (↑(xn ↑i) : Felt252) * 2 ^ (9 * i)) := by
  simp [Finset.sum_range_succ]
  trans ((↑(xn 0 + xn 1 * 2 ^ 9 : ℕ) : Felt) + (↑(xn 2 * 2 ^ 18 : ℕ) : Felt) + (↑(xn 3 * 2 ^ 27 : ℕ) : Felt)).toFelt252
  . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_two]
  simp only [←Nat.cast_add]
  apply Eq.trans
  apply toFelt.of_lt (lt_of_lt_of_le (felt252_to_m31_calc'' _ h h') _)
  . simp [Stwo.P]
  --simp [Nat.cast_pow, Nat.cast_two]; norm_num
  simp
  norm_num

theorem felt252_to_m31_eq [Fact (Nat.Prime Stwo.P)]
    (x : Felt252Words)
    (xn : Felt252Nats)
    (h_num_bits : ReadPositive.has_num_bits ADDRESS_BITS x)
    (hxn : xn.IsRangeChecked x) :
    (felt252_to_m31_val x ADDRESS_BITS).toFelt252 = xn.eval := by
  rw [Felt252Nats.IsRangeChecked] at hxn
  have last_limb_lt := Felt252IdMemory.read_address.read_address_last_limb h_num_bits (hxn 3).1 (hxn 3).2

  have : ADDRESS_BITS ≤ 252 := by simp [ADDRESS_BITS]
  replace h_num_bits := h_num_bits this |>.2
  simp [ADDRESS_BITS, FELT252_BITS_PER_WORD, Nat.div_ceil] at h_num_bits
  rw [Felt252Nats.eval, Finset.sum_fin_eq_sum_range]
  have : Finset.range FELT252_N_WORDS = Finset.range 4 ∪ Finset.Ico 4 FELT252_N_WORDS := by
    ext i; simp [FELT252_N_WORDS]; omega
  rw [this, Finset.sum_union]; swap
  . simp [Finset.disjoint_iff_ne]; omega
  conv => lhs; apply add_zero _ |>.symm
  apply congr_arg₂; swap; symm
  . rw [Finset.sum_eq_zero]
    intro i; simp; intro hi hi' _
    have := h_num_bits ⟨i, hi'⟩ hi
    rw [←Nat.cast_zero, hxn ⟨i, hi'⟩ |>.1] at this
    have : xn ⟨i, hi'⟩ = 0 := by
      symm
      apply Nat.cast_inj_of_lt_char' _ _ this.symm
      . simp
      simp [Felt, ZMod.ringChar_zmod_n]
      apply lt_of_lt_of_le (hxn _ |>.2)
      simp [Stwo.P]
    rw [this]; simp
  rw [felt252_to_m31_calc' hxn]
  rw [felt252_to_m31_eq_aux]; swap
  . intro i; apply hxn i |>.2
  apply Finset.sum_congr rfl
  simp; intro i hi
  rw [dif_pos]; swap
  . simp [FELT252_N_WORDS]; omega
  congr
  rw [Fin.eq_mk_iff_val_eq]
  simp; omega
  exact last_limb_lt

-- theorem felt252_to_m31_val_isRangeChecked [Fact (Nat.Prime Stwo.P)]
--     {xn : Felt252Nats}
--     {x : Felt252Words}
--     (hxn : xn.IsRangeChecked x) :
--     IsRangeChecked 27 (felt252_to_m31_val x ADDRESS_BITS) := by
--   rw [felt252_to_m31_calc' hxn, IsRangeChecked]
--   refine ⟨_, felt252_to_m31_calc xn (fun i => hxn i |>.2), ?_⟩
--   simp [Finset.sum_range_succ]; norm_num

theorem felt252_to_m31_val_isRangeChecked_specific [Fact (Nat.Prime Stwo.P)]
    {xn : Felt252Nats}
    {x : Felt252Words}
    (hxn : xn.IsRangeChecked x)
    (hxn3 : xn 3 < 2 ^ 2) :
    IsRangeChecked 29 (felt252_to_m31_val x ADDRESS_BITS) := by
  rw [felt252_to_m31_calc' hxn, IsRangeChecked]
  refine ⟨_, felt252_to_m31_calc'' xn (fun i => hxn i |>.2) hxn3, ?_⟩
  simp [Finset.sum_range_succ]; norm_num

--make it more general?
--all ReadPositive?
--all read_address?
theorem felt252_to_m31_val_isRangeChecked [Fact (Nat.Prime Stwo.P)]
    {xn : Felt252Nats}
    {x : Felt252Words}
    (hxn : xn.IsRangeChecked x)
    (hx_addr : ReadPositive.has_num_bits ADDRESS_BITS x) :
    IsRangeChecked 29 (felt252_to_m31_val x ADDRESS_BITS) := by
  rcases hx_addr (show ADDRESS_BITS ≤ 252 by simp[ADDRESS_BITS]) with ⟨h_msb_pre, h_post_msb⟩
  rcases h_msb_pre (show ADDRESS_BITS % FELT252_BITS_PER_WORD > 0 by simp [ADDRESS_BITS, FELT252_BITS_PER_WORD])
      with ⟨xn3, ⟨h_xn3_lt, h_xn3_eq⟩⟩
  -- have : ADDRESS_BITS % FELT252_BITS_PER_WORD = 2 := by
  --   simp [ADDRESS_BITS, FELT252_BITS_PER_WORD]
  -- rw [this] at *
  have : 2 ^ (ADDRESS_BITS % FELT252_BITS_PER_WORD) = 4 := by
    simp [ADDRESS_BITS, FELT252_BITS_PER_WORD]
  rw [this] at h_xn3_lt
  have h_xn3_eq_xn_3 : xn 3 = xn3 := by
    apply Felt.fromNat_inj
    linarith[(hxn 3).2]
    linarith[h_xn3_lt]
    rw[← (hxn 3).1, ← h_xn3_eq]
    simp [ADDRESS_BITS, FELT252_BITS_PER_WORD, Nat.div_ceil]

  rw [← h_xn3_eq_xn_3] at h_xn3_lt
  exact (felt252_to_m31_val_isRangeChecked_specific hxn h_xn3_lt)


  -- rw [felt252_to_m31_calc' hxn, IsRangeChecked]
  -- refine ⟨_, felt252_to_m31_calc'' xn (fun i => hxn i |>.2) hxn3, ?_⟩
  -- simp [Finset.sum_range_succ]; norm_num

