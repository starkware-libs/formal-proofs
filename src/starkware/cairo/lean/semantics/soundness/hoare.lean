/-
Definitions and tactics for reasoning about the one-step effects of each assembly instruction.
-/
import starkware.cairo.lean.semantics.util
import starkware.cairo.lean.semantics.soundness.assembly_step
import starkware.cairo.lean.semantics.air_encoding.instruction

section main

@[class] def char_ge_2_63 (F : Type*) [field F] : Prop := ring_char F ≥ 2^63

variables {F : Type*} [field F]

/-
Reasoning about contents of memory.
-/

def mem_at (mem : F → F) : list F → F → Prop
| [] _        := true
| (v :: l) pc := mem pc = v ∧ mem_at l (pc + 1)

/-
The halting instruction is a relative jump to the same spot. In general, we don't prove that a
program will halt, but, rather, that *if* it halts it has the desired behavior. This is o.k.
because the STARK can certify that the computation has, in fact, halted.

To take a step forward, however, we need to verify that the current instruction is not a halting
instruction. The following lemmas help with do that efficiently.
-/

def jmp_rel_instr : instr := 'jmp_rel[ 'op1[imm] ]

section instr

variables (op0 : op0_spec) (op1 : op1_spec) (res : res_spec) (dst : dst_spec) (ap_update : bool)

lemma assert_eq_ne_jmp_rel :
  (assert_eq_instr op0 res dst ap_update).to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h,
  have := congr_arg instruction.opcode_assert_eq h,
  contradiction
end

lemma call_ne_jmp_rel (call_abs : bool) :
  (call_instr call_abs res).to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h,
  have := congr_arg instruction.opcode_call h,
  contradiction
end

lemma ret_ne_jmp_rel : ret_instr.to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h,
  have := congr_arg instruction.opcode_ret h,
  contradiction
end

lemma advance_ap_ne_jmp_rel :
  (advance_ap_instr op0 res).to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h,
  have := congr_arg instruction.ap_add h,
  contradiction
end

lemma jnz_ne_jmp_rel :
  (jnz_instr op0 op1 dst ap_update).to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h,
  have := congr_arg instruction.pc_jnz h,
  contradiction
end

/-- Can be used unless the jump has an immediate argument, in which case instead we have to
    check that the immediate argument is not 0. -/
lemma jump_ne_jmp_rel (jump_abs : bool) (h : res.to_op1.op1_imm = ff) :
  (jump_instr jump_abs op0 res ap_update).to_instruction ≠ jmp_rel_instr.to_instruction :=
begin
  intro h',
  have := congr_arg instruction.op1_imm h',
  dsimp [jump_instr] at this,
  rw h at this,
  contradiction
end

end instr

/-
The definition of a halting execution trace and supporting lemmas.
-/

section halting

variable [decidable_eq F]
variable mem : F → F
variables s t : register_state F

def is_halting_state := mem s.pc = jmp_rel_instr.to_nat ∧ mem (s.pc + 1) = 0

lemma not_is_halting_state_iff {mem : F → F} {s : register_state F} :
  ¬ is_halting_state mem s ↔ mem s.pc ≠ jmp_rel_instr.to_nat ∨ mem (s.pc + 1) ≠ 0 :=
decidable.not_and_distrib

def is_halting_trace {n : ℕ} (exec : fin (n + 1) → register_state F) : Prop :=
  (∀ i : fin n, next_state mem (exec i.cast_succ) (exec i.succ)) ∧
  is_halting_state mem (exec (fin.last n))

theorem eq_succ_of_not_halting_state_0 {mem : F → F} {n : ℕ}
    {exec : fin (n + 1) → register_state F}
    (h : is_halting_trace mem exec)
    (h' : ¬ is_halting_state mem (exec 0)) :
  ∃ m : ℕ, n = m.succ :=
begin
  apply nat.exists_eq_succ_of_ne_zero,
  rintro rfl,
  exact h' h.2
end

theorem is_halting_trace_step {mem : F → F} {n : ℕ} {exec : fin (n.succ + 1) → register_state F}
    (h : is_halting_trace mem exec)
    (h' : ¬ is_halting_state mem (exec 0)) :
  is_halting_trace mem (λ i, exec i.succ) :=
begin
  split,
  { intro i, convert h.1 i.succ, rw [fin.cast_succ_fin_succ] },
  exact h.2
end

theorem is_halting_trace_remainder {m n : ℕ} {exec : fin (m + n + 1) → register_state F}
    (h : is_halting_trace mem exec) :
  is_halting_trace mem (λ j : fin (n + 1), exec (fin.cast_offset' m j)) :=
begin
  rcases h with ⟨h1, h2, h3⟩,
  rw is_halting_trace,
  refine ⟨_, h2, h3⟩,
  intro i,
  convert h1 (fin.cast_offset m i),
  rw [fin.cast_offset', fin.succ_cast_offset]
end

end halting

/-
The `ensures` predicate, and a bounded version.
-/

section ensures

variable [decidable_eq F]

/--
Given `mem` and start state `s`, any halting trace `exec` with `exec 0 = s` eventually reaches a
state `t` in `i` steps such that for some `k ≤ i`, `P k (exec i)`. We use the bound on `k` to
ensure a final claim about the range of values that have been range checked.
-/
def ensures (mem : F → F) (s : register_state F) (P : ℕ → register_state F → Prop) : Prop :=
  ∀ n : ℕ, ∀ exec : fin (n+1) → register_state F,
    is_halting_trace mem exec → exec 0 = s → ∃ i : fin (n + 1), ∃ k ≤ i, P k (exec i)

/-- for use with code blocks that end with a return -/
@[reducible] def ensures_ret (mem : F → F) (s : register_state F)
    (P : ℕ → register_state F → Prop) :
  Prop :=
ensures mem s (λ k t, t.pc = mem (s.fp - 1) ∧ t.fp = mem (s.fp - 2) ∧ P k t)

def ensuresb (bound : ℕ) (mem : F → F) (s : register_state F) (P : ℕ → register_state F → Prop) :
  Prop :=
∀ n : ℕ, n < bound → ∀ exec : fin (n+1) → register_state F,
  is_halting_trace mem exec → exec 0 = s → ∃ i : fin (n + 1), ∃ k ≤ i, P k (exec i)

theorem ensures_of_ensuresb {mem : F → F} {s : register_state F}
    {P : ℕ → register_state F → Prop}
    (h : ∀ bound, ensuresb bound mem s P) :
  ensures mem s P :=
λ n, h (n + 1) _ (nat.lt_succ_self n)

theorem ensuresb_of_le {mem : F → F} {s : register_state F}
    {P : ℕ → register_state F → Prop}
    {bound₁ bound₂ : ℕ}
    (h_bound : bound₂ ≤ bound₁)
    (h : ensuresb bound₁ mem s P) :
  ensuresb bound₂ mem s P :=
begin
  intros n h_n, exact h n (nat.lt_of_lt_of_le h_n h_bound)
end

theorem ensuresb_of_ensuresb {mem : F → F} {s : register_state F}
    {P : ℕ → register_state F → Prop}
    {bound : ℕ}
    (h : ∀ bound₁ ≤ bound, ensuresb bound₁ mem s P) :
  ensuresb bound mem s P :=
h bound (le_of_eq rfl)

@[reducible] def ensuresb_ret (bound : ℕ) (mem : F → F) (s : register_state F)
    (P : ℕ → register_state F → Prop) :
  Prop :=
ensuresb bound mem s (λ k t, t.pc = mem (s.fp - 1) ∧ t.fp = mem (s.fp - 2) ∧ P k t)

theorem ensures_ret_of_ensuresb_ret {mem : F → F} {s : register_state F}
    {P : ℕ → register_state F → Prop}
    (h : ∀ bound, ensuresb_ret bound mem s P) :
  ensures_ret mem s P :=
λ n, h (n + 1) _ (nat.lt_succ_self n)

/-- Takes a step and augments `k` by 1. -/
theorem ensuresb_step {bound : ℕ}
    {mem : F → F} {s t : register_state F} {P : ℕ → register_state F → Prop}
    {Q : Prop}
    (h0 : ¬ is_halting_state mem s)
    (h1 : ∀ t', next_state mem s t' → t' = t ∧ Q)
    (h : Q → ensuresb bound mem t (λ k t', P (k + 1) t')) :
  ensuresb (bound + 1) mem s P :=
begin
  rintros n₀ n₀le exec h2 rfl,
  rcases eq_succ_of_not_halting_state_0 h2 h0 with ⟨n, rfl⟩,
  rcases h (h1 _ (h2.1 0)).2 n (nat.le_of_succ_le_succ n₀le) (λ i, exec i.succ)
      (is_halting_trace_step h2 h0) (h1 _ (h2.1 0)).1 with ⟨i, k, hik, h4⟩,
  use [i.succ, k.succ], split,
  { exact fin.succ_le_succ_iff.mpr hik },
  convert h4, simp
end

/- used to add a + 1 if necessary -/
theorem ensuresb_succ {bound : ℕ}
    {mem : F → F} {s : register_state F} {P : ℕ → register_state F → Prop}
    (h : ensuresb (bound + 1) mem s P) :
  ensuresb bound mem s P :=
λ n nlt, h _ (nlt.trans $nat.lt_succ_self _)

theorem ensuresb_test {bound : ℕ}
    {mem : F → F} {s : register_state F} {P : ℕ → register_state F → Prop}
    (h : ensuresb (bound + 1) mem s P) : ensuresb (bound + 1) mem s P := h

theorem ensuresb_trans {bound : ℕ}
    {mem : F → F} {s : register_state F} {P Q : ℕ → register_state F → Prop}
    (h0 : ensures mem s P)
    (h1 : ∀ k t, P k t → ensuresb bound mem t (λ k', Q (k + k'))) :
  ensuresb bound mem s Q :=
begin
  rintros n nlt exec h2 h3,
  rcases h0 _ _ h2 h3 with ⟨i, k, hik1, hik2⟩,
  rcases fin.exists_eq_add i with ⟨m, j, hm, rfl⟩,
  have : exec (fin.cast_offset' m 0) = exec i,
  { congr, ext, exact hm  },
  rcases h1 _ _ hik2 _ (lt_of_le_of_lt (nat.le_add_left _ _) nlt) _
    (is_halting_trace_remainder mem h2) this with ⟨i', k', hi'k', h4⟩,
  dsimp at h4,
  have : ↑k + j + 1 ≤ m + j + 1,
  { apply nat.succ_le_succ, apply nat.add_le_add_right, nth_rewrite_rhs 0 hm, exact hik1 },
  use [fin.cast_offset' m i', fin.cast_le this (fin.cast_offset' k k')],
  split,
  { rw fin.le_iff_coe_le_coe,
    simp [fin.cast_offset', fin.cast_offset],
    nth_rewrite_rhs 0 hm,
    rw fin.le_iff_coe_le_coe at hik1 hi'k',
    apply add_le_add hik1 hi'k' },
  exact h4
end

theorem ensuresb_rec_trans {bound : ℕ}
    {mem : F → F} {s : register_state F} {P Q : ℕ → register_state F → Prop}
    (h0 : ensuresb bound mem s P)
    (h1 : ∀ k t, P k t → ensuresb bound mem t (λ k', Q (k + k'))) :
  ensuresb bound mem s Q :=
begin
  rintros n nlt exec h2 h3,
  rcases h0 _ nlt _ h2 h3 with ⟨i, k, hik1, hik2⟩,
  rcases fin.exists_eq_add i with ⟨m, j, hm, rfl⟩,
  have : exec (fin.cast_offset' m 0) = exec i,
  { congr, ext, exact hm  },
  rcases h1 _ _ hik2 _ (lt_of_le_of_lt (nat.le_add_left _ _) nlt) _
    (is_halting_trace_remainder mem h2) this with ⟨i', k', hi'k', h4⟩,
  dsimp at h4,
  have : ↑k + j + 1 ≤ m + j + 1,
  { apply nat.succ_le_succ, apply nat.add_le_add_right, nth_rewrite_rhs 0 hm, exact hik1 },
  use [fin.cast_offset' m i', fin.cast_le this (fin.cast_offset' k k')],
  split,
  { rw fin.le_iff_coe_le_coe,
    simp [fin.cast_offset', fin.cast_offset],
    nth_rewrite_rhs 0 hm,
    rw fin.le_iff_coe_le_coe at hik1 hi'k',
    apply add_le_add hik1 hi'k' },
  exact h4
end

theorem ensuresb_id {bound : ℕ} {mem : F → F} {s : register_state F}
    {P : ℕ → register_state F → Prop} (h : P 0 s) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec hexec hexec0,
  use [0, 0, le_refl _],
  rwa hexec0
end

theorem ensuresb_rec {mem : F → F}
    (P : register_state F → F → ℕ → register_state F → Prop)
    (Haux : F → register_state F → Prop)
    (s : register_state F) (arg : F) (hHaux : Haux arg s)
    (hind : ∀ bound, (∀ (arg : F) (s: register_state F),
      Haux arg s → ensuresb bound mem s (P s arg)) →
        (∀ {arg : F}, ∀ {s: register_state F},
          Haux arg s → ensuresb (bound + 1) mem s (P s arg))) :
  ensures mem s (P s arg) :=
begin
  have : ∀ bound, (∀ {arg : F}, ∀ {s: register_state F},
      Haux arg s → ensuresb bound mem s (P s arg)),
  { intro bound,
    induction bound with bound ih,
    { intros _ _ _ n nlt, exact absurd nlt (nat.not_lt_zero _)},
    apply hind, exact @ih },
  apply ensures_of_ensuresb (λ bound, this bound hHaux)
end

-- for handling blocks
theorem ensuresb_ret_trans {bound : ℕ}
    {mem : F → F} {s : register_state F} {P Q : ℕ → register_state F → Prop}
    (h0 : ensuresb_ret bound mem s P)
    (h1 : ∀ k t, P k t → Q k t) :
  ensuresb_ret bound mem s Q :=
begin
  rintros n nlt exec h2 h3,
  rcases h0 _ nlt _ h2 h3 with ⟨i, k, hik1, hik2, hik3, hik4⟩,
  use [i, k, hik1, hik2, hik3, h1 _ _ hik4]
end

end ensures

/-
Characterize next state transitions.
-/

section next_state

variable [decidable_eq F]

lemma instruction.next_state_iff_of_eq [char_ge : char_ge_2_63 F] {i : instruction}
    {mem : F → F} {s t : register_state F} (h : mem s.pc = i.to_nat) :
  next_state mem s t ↔ i.next_state mem s t :=
begin
  rw [next_state], split,
  { rintros ⟨i', i'eq, i'next_state⟩,
    have : i = i' := inst_unique char_ge _ _ (h.symm.trans i'eq),
    rwa this },
  intro h', use [i, h, h']
end

variable {mem : F → F}
variable {s : register_state F}
variable {P : ℕ → register_state F → Prop}

theorem assert_eq_ensuresb' [char_ge : char_ge_2_63 F] {bound : ℕ}
    {op0 : op0_spec} {res : res_spec} {dst : dst_spec} {ap_update : bool}
    (h  : mem s.pc = (assert_eq_instr op0 res dst ap_update).to_nat)
    (h' : compute_dst mem s dst = compute_res mem s op0 res →
      ensuresb bound mem ⟨bump_pc s res.to_op1.op1_imm, bump_ap s ap_update, s.fp⟩
        (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact assert_eq_ne_jmp_rel _ _ _ _ (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨bump_pc s res.to_op1.op1_imm, bump_ap s ap_update, s.fp⟩ ∧
        compute_dst mem s dst = compute_res mem s op0 res,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_assert_eq] at ht,
    simp [ht],
    ext; simp [ht] },
  apply ensuresb_step h1 h2 h' _ nlt
end

theorem jump_ensuresb [char_ge : char_ge_2_63 F] {bound}
    {op0 : op0_spec} {res : res_spec} {ap_update : bool} {jump_abs : bool}
    (h : mem s.pc = (jump_instr jump_abs op0 res ap_update).to_nat)
    (h_aux : res.to_op1.op1_imm = ff)
    (h' : ensuresb bound mem ⟨jump_pc s jump_abs (compute_res mem s op0 res),
      bump_ap s ap_update, s.fp⟩ (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact jump_ne_jmp_rel _ _ _ _ h_aux (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨jump_pc s jump_abs (compute_res mem s op0 res), bump_ap s ap_update, s.fp⟩ ∧ true,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_jump] at ht,
    split, ext; simp [ht], trivial },
  apply ensuresb_step h1 h2 (λ _, h') _ nlt
end

theorem jump_ensuresb' [char_ge : char_ge_2_63 F] {bound : ℕ}
    {op0 : op0_spec} {res : res_spec} {ap_update : bool} {jump_abs : bool}
    (h : mem s.pc = (jump_instr jump_abs op0 res ap_update).to_nat)
    {x : ℤ} {h0 : abs x ≠ 0} {h1 : abs x < 2^63}
    (h_aux : mem (s.pc + 1) = checked_int_nz x h0 h1)
    (h' : ensuresb bound mem ⟨jump_pc s jump_abs (compute_res mem s op0 res),
      bump_ap s ap_update, s.fp⟩ (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw [not_is_halting_state_iff, h_aux], right,
    apply int.cast_ne_zero_of_abs_lt_char h0,
    apply lt_of_lt_of_le h1,
    change ((2^ 63 : ℕ) : ℤ) ≤ _,
    rw int.coe_nat_le_coe_nat_iff,
    apply char_ge },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨jump_pc s jump_abs (compute_res mem s op0 res), bump_ap s ap_update, s.fp⟩ ∧ true,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_jump] at ht,
    split, ext; simp [ht], trivial },
  apply ensuresb_step h1 h2 (λ _, h') _ nlt
end

theorem jnz_ensuresb [char_ge : char_ge_2_63 F] {bound : ℕ}
    {op0 : op0_spec} {op1 : op1_spec} {dst : dst_spec} {ap_update : bool}
    (h  : mem s.pc = (jnz_instr op0 op1 dst ap_update).to_nat)
    (h₀ : compute_dst mem s dst = 0 →
      ensuresb bound mem ⟨bump_pc s op1.op1_imm, bump_ap s ap_update, s.fp⟩ (λ k t, P (k + 1) t))
    (h₁ : compute_dst mem s dst ≠ 0 →
      ensuresb bound mem ⟨s.pc + compute_op1 mem s op0 op1, bump_ap s ap_update, s.fp⟩
        (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact jnz_ne_jmp_rel _ _ _ _ (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨ite (compute_dst mem s dst = 0) (bump_pc s op1.op1_imm)
            (s.pc + compute_op1 mem s op0 op1),  bump_ap s ap_update, s.fp⟩ ∧
        true,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_jnz] at ht,
    simp [ht],
    ext; simp [ht] },
  apply ensuresb_step h1 h2 _ _ nlt,
  by_cases h3 : compute_dst mem s dst = 0,
  { intro _,
    rw if_pos h3,
    exact h₀ h3 },
  intro _,
  rw if_neg h3,
  exact h₁ h3
end

theorem call_ensuresb [char_ge : char_ge_2_63 F] {bound : ℕ} {res : res_spec} {call_abs : bool}
    (h  : mem s.pc = (call_instr call_abs res).to_nat)
    (h' : mem s.ap = s.fp →
            mem (s.ap + 1) = bump_pc s res.to_op1.op1_imm →
            ensuresb bound mem ⟨jump_pc s call_abs (compute_res mem s (op0_spec.ap_plus 1) res),
              s.ap + 2, s.ap + 2⟩ (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact call_ne_jmp_rel _ _ (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨jump_pc s call_abs (compute_res mem s (op0_spec.ap_plus 1) res), s.ap + 2, s.ap + 2⟩ ∧
        mem (s.ap + 1) = bump_pc s res.to_op1.op1_imm ∧ mem s.ap = s.fp,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_call] at ht,
    simp [ht],
    ext; simp [ht] },
  apply ensuresb_step h1 h2 _ _ nlt,
  intro h3,
  apply h' h3.2 h3.1
end

theorem ret_ensuresb [char_ge : char_ge_2_63 F] {bound : ℕ}
    (h  : mem s.pc = ret_instr.to_nat)
    (h' : ensuresb bound mem ⟨mem (s.fp + -1), s.ap, mem (s.fp - 2)⟩ (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact ret_ne_jmp_rel (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨mem (s.fp + -1), s.ap, mem (s.fp - 2)⟩ ∧ true,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_ret] at ht,
    simp [ht],
    ext; simp [ht] },
  apply ensuresb_step h1 h2 (λ _, h') _ nlt
end

theorem call_ensuresb_trans [char_ge : char_ge_2_63 F] {bound : ℕ}
    {P Q : ℕ → register_state F → Prop}
    {res : res_spec} {call_abs : bool} {x : F}
    (h₀ : mem s.pc = x)
    (h₁ : x = (call_instr call_abs res).to_nat)
    (h₂ : ensures_ret mem ⟨jump_pc s call_abs (compute_res mem s (op0_spec.ap_plus 1) res),
            s.ap + 2, s.ap + 2⟩ P)
    (h₃ : ∀ k ap, P k ⟨bump_pc s res.to_op1.op1_imm, ap, s.fp⟩ →
            ensuresb bound mem ⟨bump_pc s res.to_op1.op1_imm, ap, s.fp⟩ (λ k', Q (k + k' + 1))) :
  ensuresb (bound + 1) mem s Q :=
begin
  apply call_ensuresb (h₀.trans h₁),
  intros h1 h2,
  apply ensuresb_trans h₂, dsimp,
  rintros k ⟨tpc, tap, tfp⟩, dsimp,
  rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero], norm_num1,
  rw [h1, h2],
  rintros ⟨rfl, rfl, hP⟩,
  apply h₃ _ _ hP
end

theorem call_rec_ensuresb_trans [char_ge : char_ge_2_63 F] {bound : ℕ}
    {P Q : ℕ → register_state F → Prop}
    {res : res_spec} {call_abs : bool} {x : F}
    (h₀ : mem s.pc = x)
    (h₁ : x = (call_instr call_abs res).to_nat)
    (h₂ : ensuresb_ret bound mem ⟨jump_pc s call_abs (compute_res mem s (op0_spec.ap_plus 1) res),
            s.ap + 2, s.ap + 2⟩ P)
    (h₃ : ∀ k ap, P k ⟨bump_pc s res.to_op1.op1_imm, ap, s.fp⟩ →
            ensuresb bound mem ⟨bump_pc s res.to_op1.op1_imm, ap, s.fp⟩ (λ k', Q (k + k' + 1))) :
  ensuresb (bound + 1) mem s Q :=
begin
  apply call_ensuresb (h₀.trans h₁),
  intros h1 h2,
  apply ensuresb_rec_trans h₂, dsimp,
  rintros k ⟨tpc, tap, tfp⟩, dsimp,
  rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero], norm_num1,
  rw [h1, h2],
  rintros ⟨rfl, rfl, hP⟩,
  apply h₃ _ _ hP
end

theorem advance_ap_ensuresb [char_ge : char_ge_2_63 F] {bound : ℕ}
    {op0 : op0_spec} {res : res_spec}
    (h  : mem s.pc = (advance_ap_instr op0 res).to_nat)
    (h' : ensuresb bound mem ⟨bump_pc s res.to_op1.op1_imm, s.ap + compute_res mem s op0 res, s.fp⟩
      (λ k t, P (k + 1) t)) :
  ensuresb (bound + 1) mem s P :=
begin
  intros n nlt exec,
  have h1 : ¬ is_halting_state mem s,
  { rw not_is_halting_state_iff, left, rw h,
    intro h0,
    exact advance_ap_ne_jmp_rel _ _ (inst_unique char_ge _ _ h0) },
  have h2 : ∀ t, next_state mem s t →
      t = ⟨bump_pc s res.to_op1.op1_imm, s.ap + compute_res mem s op0 res, s.fp⟩ ∧ true,
  { intros t ht,
    rw [instruction.next_state_iff_of_eq h, ←instr.next_state, next_state_advance_ap] at ht,
    simp [ht],
    ext; simp [ht] },
  apply ensuresb_step h1 h2 (λ _, h') _ nlt
end

end next_state

/-
Theorems to handle the range-checked hypotheses.
-/

def is_range_checked (rc_bound : ℕ) (a : F) : Prop := ∃ n : ℕ, n < rc_bound ∧ a = ↑n

def range_checked (mem : F → F) (rc_start : F) (k rc_bound : ℕ) : Prop :=
  ∀ i < k, is_range_checked rc_bound (mem (rc_start + i))

theorem range_checked_mono {mem : F → F} {rc_start : F} {k rc_bound : ℕ}
    (k' : ℕ) (k'le : k' ≤ k)
    (h : range_checked mem rc_start k rc_bound) :
  range_checked mem rc_start k' rc_bound :=
λ i iltk', h i (lt_of_lt_of_le iltk' k'le)

theorem range_checked_add_left {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : range_checked mem rc_start (k' + k) rc_bound) :
  range_checked mem rc_start k rc_bound :=
range_checked_mono _ (nat.le_add_left _ _) h

theorem range_checked_add_right {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : range_checked mem rc_start (k + k') rc_bound) :
  range_checked mem rc_start k rc_bound :=
range_checked_mono _ (nat.le_add_right _ _) h

theorem range_checked_offset {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : range_checked mem rc_start (k + k') rc_bound) :
  range_checked mem (rc_start + k') k rc_bound :=
begin
  intros i iltk,
  rcases h _ (add_lt_add_right iltk k') with ⟨i', hi'⟩,
  use i', rwa [add_assoc, ←nat.cast_add, add_comm k']
end

theorem range_checked_offset' {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : range_checked mem rc_start (k + k') rc_bound) :
  range_checked mem (rc_start + k) k' rc_bound :=
by { rw add_comm at h, exact range_checked_offset h }

def rc_ensures (mem : F → F) (rc_bound k : ℕ) (a0 a1 : F) (P : Prop) :=
a1 = a0 + k ∧ (range_checked mem a0 k rc_bound → P)

theorem rc_ensures_comp {mem : F → F} {rc_bound k0 k1 : ℕ} {a0 a1 a2 : F} {P Q : Prop}
    (h0 : rc_ensures mem rc_bound k0 a0 a1 P)
    (h1 : rc_ensures mem rc_bound k1 a1 a2 Q) :
  rc_ensures mem rc_bound (k0 + k1) a0 a2 (P ∧ Q) :=
begin
  rcases h0 with ⟨hk0, rc0⟩,
  rcases h1 with ⟨hk1, rc1⟩,
  split,
  { rw [hk1, hk0, add_assoc, nat.cast_add] },
  intro h, split,
  { exact rc0 (range_checked_add_right h) },
  apply rc1, rw hk0, exact range_checked_offset' h
end

theorem rc_ensures_trans {mem : F → F} {rc_bound k : ℕ} {a0 a1 : F} {P Q : Prop}
    (h1 : rc_ensures mem rc_bound k a0 a1 P)
    (h2 : P → Q) :
   rc_ensures mem rc_bound k a0 a1 Q :=
begin
  rcases h1 with ⟨hk, h⟩,
  exact ⟨hk, λ h', h2 (h h')⟩
end

end main

/-
Tactics.
-/

namespace tactic
setup_tactic_parser

namespace interactive

meta def arith_simps (loc : parse location) : tactic unit :=
let cfg : simp_config_ext := {},
    simp_args := mk_simp_arg_list [
    ``(int.cast_zero), ``(int.cast_one), ``(int.cast_bit0), ``(int.cast_bit1), ``(int.cast_neg),
    ``(nat.cast_zero), ``(nat.cast_one), ``(nat.cast_bit0), ``(nat.cast_bit1),
    ``(add_assoc), ``(add_sub_assoc), ``(add_zero), ``(zero_add), ``(add_right_neg), ``(add_left_neg),
        ``(add_neg_eq_sub), ``(sub_add_eq_add_neg_add), ``(mul_assoc)] in
do try $ simp_core cfg.to_simp_config cfg.discharger tt simp_args [] loc >> skip,
   try $ (tactic.norm_num1 norm_num.derive.step loc >>
   (try $ simp_core cfg.to_simp_config cfg.discharger tt simp_args [] loc >> skip))

meta def ensures_simps (loc : parse location) : tactic unit :=
let cfg : simp_config_ext := {},
    simp_args := mk_simp_arg_list [``(res_spec.to_op1), ``(compute_res), ``(compute_op1),
      ``(compute_op0), ``(op1_spec.op1_imm), ``(compute_dst), ``(bump_pc), ``(bump_ap),
      ``(jump_pc), ``(clip_checked), ``(checked_int_nz_eq),
    ``(int.cast_zero), ``(int.cast_one), ``(int.cast_bit0), ``(int.cast_bit1), ``(int.cast_neg),
    ``(nat.cast_zero), ``(nat.cast_one), ``(nat.cast_bit0), ``(nat.cast_bit1),
    ``(add_assoc), ``(add_sub_assoc), ``(add_zero), ``(zero_add), ``(add_right_neg), ``(add_left_neg),
        ``(add_neg_eq_sub), ``(sub_add_eq_add_neg_add), ``(mul_assoc)] in
do try $ simp_core cfg.to_simp_config cfg.discharger tt simp_args [] loc >> skip,
   try (tactic.norm_num1 norm_num.derive.step loc >>
   (try $ simp_core cfg.to_simp_config cfg.discharger tt simp_args [] loc >> skip))

meta def unpack_memory (code : parse ident) (h : parse $ tk "at" *> ident)
  (pat : parse $ tk "with" *>rcases_patt_parse) : tactic unit :=
let cfg : simp_config_ext := {},
    simp_args := mk_simp_arg_list [``(mem_at), ``(add_assoc), ``(and_true)] in
do unfold [code] (loc.ns [h]),
   try $ simp_core cfg.to_simp_config cfg.discharger tt simp_args [] (loc.ns [h]) >> skip,
   try $ tactic.norm_num1 norm_num.derive.step (loc.ns [h]),
   eh ← resolve_name h,
   rcases (rcases_args.rcases none eh pat)

meta def ensuresb_make_succ : tactic unit :=
  (applyc ``ensuresb_test) <|> (applyc ``ensuresb_succ)

meta def step_assert_eq (h : parse ident) (h' : parse ident?)
    (hw : parse $ tk "with" *> ident) :=
do ensuresb_make_succ,
   applyc ``assert_eq_ensuresb',
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   ensures_simps loc_target,
   match h' with
   | (some n) := do eh ← get_local n,
                    try $ tactic.rewrite_target eh >> tactic.clear eh --,
                    -- ensures_simps loc_target
   | none     := skip
   end,
   intro hw

meta def step_jump (h : parse ident) :=
do ensuresb_make_succ,
   applyc ``jump_ensuresb,
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   /- first subgoal: not an immediate argument-/
   tactic.reflexivity,
   /- main goal -/
   ensures_simps loc_target

meta def step_jump_imm (h : parse ident) (h' : parse ident) :=
do ensuresb_make_succ,
   applyc ``jump_ensuresb',
   eh ← get_local h,
   tactic.apply eh,
   arith_simps loc_target,
   eh' ← get_local h',
   tactic.apply eh',
   /- main goal -/
   ensures_simps loc_target,
   eh' ← get_local h',
   try $ tactic.rewrite_target eh',
   tactic.clear eh,
   tactic.clear eh',
   ensures_simps loc_target

meta def step_jnz (h : parse ident) (h' : parse ident?)
  (hw : parse $ tk "with" *> ident) (hw' : parse ident):=
do ensuresb_make_succ,
   applyc ``jnz_ensuresb,
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   swap,
   tactic.clear eh,
   focus $ do { ensures_simps loc_target },
   match h' with
   | (some n) := do eh ← get_local n,
                    try $ tactic.rewrite_target eh >> tactic.clear eh,
                    ensures_simps loc_target
   | none     := skip
   end,
   ehw' ← tactic.intro hw',
   try $ tactic.rewrite_target eh,
   swap,
   focus $ do { ensures_simps loc_target },
   intro hw,
   match h' with
   | (some n) := do eh ← get_local n,
                    try $ tactic.rewrite_target eh >> tactic.clear eh,
                    ensures_simps loc_target
   | none     := skip
   end

meta def step_call (h : parse ident) :=
do ensuresb_make_succ,
   applyc ``call_ensuresb,
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   ensures_simps loc_target

meta def step_ret (h : parse ident) :=
do ensuresb_make_succ,
   applyc ``ret_ensuresb,
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   ensures_simps loc_target

meta def step_advance_ap (h : parse ident) (h' : parse ident?) :=
do ensuresb_make_succ,
   applyc ``advance_ap_ensuresb,
   eh ← get_local h,
   tactic.apply eh,
   tactic.clear eh,
   ensures_simps loc_target,
   match h' with
   | (some n) := do eh ← get_local n,
                    try $ tactic.rewrite_target eh >> tactic.clear eh,
                    ensures_simps loc_target
   | none     := skip
   end

meta def step_sub (h1 : parse ident) (h2 : parse parser.pexpr) :
  tactic unit :=
focus1 $ do
  eh ← get_local h1,
  ensuresb_make_succ,
  apply ``(call_ensuresb_trans _ %%eh %%h2 _),
  refl,
  all_goals' (tactic.clear eh >> ensures_simps loc_target)

meta def step_rec_sub (h1 : parse ident) (h2 : parse parser.pexpr) :
  tactic unit :=
focus1 $ do
  eh ← get_local h1,
  ensuresb_make_succ,
  apply ``(call_rec_ensuresb_trans _ %%eh %%h2 _),
  refl,
  all_goals' (tactic.clear eh >> ensures_simps loc_target)

meta def step_done : tactic unit :=
`[ ensuresb_make_succ, apply ensuresb_id ]

/-- A weaker version of the interactive `use` tactic, which doesn't call `triv` -/
meta def use_only (l : parse pexpr_list_or_texpr) : tactic unit :=
focus1 $ tactic.use l

/-- norm_num1 plus an extra simp rule -/
meta def norm_num2 : tactic unit :=
`[ norm_num1, try { simp only [add_neg_eq_sub] } ]

section
open interactive interactive.types expr

private meta def mkdef_arg_p_aux : pexpr → parser (name × pexpr)
| (app (app (macro _ [const `eq _ ]) (local_const x _ _ _)) h) := pure (x, h)
| _ := fail "parse error"

private meta def mkdef_arg_p : parser (name × pexpr) :=
with_desc "expr = id" $ parser.pexpr 0 >>= mkdef_arg_p_aux

/--
`mkdef h : x = t` introduces a new variable `x` into the context with
assumption `h : x = t`. It is essentially a simplified version of
`generalize'` with the equation syntax reversed.
-/
meta def mkdef (h : parse ident) (_ : parse $ tk ":") (p : parse mkdef_arg_p) :
  tactic unit :=
propagate_tags $
do let (x, p) := p,
   e ← i_to_expr p,
   tgt ← target,
   tgt' ← to_expr ``(Π x, x = %%e → %%tgt),
   t ← assert h tgt',
   swap,
   exact ``(%%t %%e rfl),
   intro x,
   intro h
end

end interactive

end tactic

/-
Some useful things for the autogenerated proofs.
-/

section

theorem assert_eq_reduction {F : Type} {a b c d : F} (h : c = d) (h' : a = c ∧ d = b) :
  a = b := (h'.1.trans h).trans h'.2

variables {F : Type*} [field F]

lemma cond_aux1 {a b t : F} (h1 : t = a - b) (h2 : t = 0) : a = b :=
by { rw h2 at h1, exact eq_of_sub_eq_zero h1.symm }

lemma cond_aux2 {a b t : F} (h1 : t = a - b) (h2 : t ≠ 0) : a ≠ b :=
by { intro h3, apply h2, rwa [h3, sub_self] at h1 }

lemma eq_sub_of_eq_add {a b c : F} (h: b = a + c) : a = b - c :=
eq_sub_of_add_eq h.symm

-- a trick for inferring the value of the ap at proof time
lemma of_register_state [decidable_eq F] {bound : ℕ}
    {mem : F → F} {s : register_state F} {P : ℕ → register_state F → Prop} :
  (∀ x, x = s → ensuresb bound mem s P) →
    ensuresb bound mem s P :=
λ h, h s rfl

/-- division with a default value -/
def ddiv [decidable_eq F] (a b c : F) : F := if b ≠ 0 then a / b else c

theorem ddiv_eq [decidable_eq F] {a b c : F} (h : b ≠ 0) : ddiv a b c = a / b :=
if_pos h

theorem eq_ddiv_of_eq_mul [decidable_eq F] {a b c : F} (h : a = c * b) : c = ddiv a b c :=
begin
  by_cases h' : b ≠ 0,
  { rw [ddiv, if_pos h', eq_div_iff h', h] },
  rw [ddiv, if_neg h']
end

theorem exists_eq_ddiv_of_eq_mul [decidable_eq F] {a b c : F} (h : a = c * b) :
  ∃ d, c = ddiv a b d :=
⟨c, eq_ddiv_of_eq_mul h⟩

-- for handling division by a constant
lemma div_eq_mul_inv' {F : Type*} [field F]  {x y z : F}
  (h : y * z = 1) : x / y = x * z :=
begin
  have : y ≠ 0,
  { intro yzero, simp [yzero] at h, contradiction },
  symmetry, apply eq_div_of_mul_eq this,
  rw [mul_assoc, mul_comm z, h, mul_one],
end

end
