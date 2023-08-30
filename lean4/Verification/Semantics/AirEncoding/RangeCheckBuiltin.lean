import Verification.Semantics.Cpu

variable {F : Type _} [Field F]

-- number of 16-bit range-checked values
variable {rc16_len : ℕ}

-- number of 128-bit range-checked values
variable {rc_len : ℕ}

-- this is public data
variable {initial_rc_addr : F}

-- this comes from range check constraints
variable {rc16_val : Fin rc16_len → F}

-- these come from memory constraints
variable {rc_addr : Fin rc_len → F}

-- rc_builtin__mem__addr
variable {rc_val : Fin rc_len → F}

-- rc_builtin__mem__value
-- map eight rc16 values to one rc value
variable {rc_to_rc16 : Fin rc_len → Fin 8 → Fin rc16_len}

-- this comes from range check constraints
variable (h_rc16_val : ∀ i : Fin rc16_len, ∃ k : ℕ, k < 2 ^ 16 ∧ rc16_val i = ↑k)

-- these are the range check builtin constraints
variable (h_rc_init_addr : ∀ h : 0 < rc_len, rc_addr ⟨0, h⟩ = initial_rc_addr)

variable
  (h_rc_addr_step :
    ∀ i : ℕ,
      ∀ h : i.succ < rc_len, rc_addr ⟨i.succ, h⟩ = rc_addr ⟨i, (Nat.lt_succ_self _).trans h⟩ + 1)
  (h_rc_value :
    ∀ i : Fin rc_len,
      rc_val i =
        ((((((rc16_val (rc_to_rc16 i 0) * 2 ^ 16 + rc16_val (rc_to_rc16 i 1)) * 2 ^ 16 +
              rc16_val (rc_to_rc16 i 2)) * 2 ^ 16 + rc16_val (rc_to_rc16 i 3)) *
              2 ^ 16 + rc16_val (rc_to_rc16 i 4)) * 2 ^ 16 + rc16_val (rc_to_rc16 i 5)) *
              2 ^ 16 + rc16_val (rc_to_rc16 i 6)) * 2 ^ 16 + rc16_val (rc_to_rc16 i 7))

section

theorem rc_addr_eq (i : Fin rc_len) : rc_addr i = initial_rc_addr + i := by
  cases' i with i h
  induction' i with i ih
  · simp [h_rc_init_addr]
  rw [h_rc_addr_step i h, ih ((Nat.lt_succ_self _).trans h), add_assoc]
  simp

end

section

theorem rc_val_checked (i : Fin rc_len) : ∃ k : ℕ, k < 2 ^ 128 ∧ rc_val i = ↑k := by
  have rc_val_aux : ∀ {n : ℕ} (_ : n < 2 ^ 16), n ≤ 2 ^ 16 - 1 := by
    intro n h
    apply Nat.le_of_succ_le_succ
    apply le_trans (Nat.succ_le_of_lt h)
    norm_num
  rw [h_rc_value]; rcases h_rc16_val (rc_to_rc16 i 0) with ⟨k0, k0_lt, k0eq⟩
  rw [k0eq]; rcases h_rc16_val (rc_to_rc16 i 1) with ⟨k1, k1_lt, k1eq⟩
  rw [k1eq]; rcases h_rc16_val (rc_to_rc16 i 2) with ⟨k2, k2_lt, k2eq⟩
  rw [k2eq]; rcases h_rc16_val (rc_to_rc16 i 3) with ⟨k3, k3_lt, k3eq⟩
  rw [k3eq]; rcases h_rc16_val (rc_to_rc16 i 4) with ⟨k4, k4_lt, k4eq⟩
  rw [k4eq]; rcases h_rc16_val (rc_to_rc16 i 5) with ⟨k5, k5_lt, k5eq⟩
  rw [k5eq]; rcases h_rc16_val (rc_to_rc16 i 6) with ⟨k6, k6_lt, k6eq⟩
  rw [k6eq]; rcases h_rc16_val (rc_to_rc16 i 7) with ⟨k7, k7_lt, k7eq⟩
  rw [k7eq]
  norm_cast
  refine' ⟨_, _, rfl⟩
  have :
    (((((((2 ^ 16 - 1) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) *
      2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) * 
        2 ^ 16 + (2 ^ 16 - 1) < 2 ^ 128 :=
    by norm_num
  apply lt_of_le_of_lt _ this
  apply add_le_add _ (rc_val_aux k7_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k6_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k5_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k4_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k3_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k2_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k1_lt)
  apply Nat.mul_le_mul_right
  apply rc_val_aux k0_lt

end