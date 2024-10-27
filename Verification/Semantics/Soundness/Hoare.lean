/-
Definitions and tactics for reasoning about the one-step effects of each assembly instruction.
-/
import Verification.Semantics.Util
import Verification.Semantics.Assembly
import Verification.Semantics.Soundness.AssemblyStep
import Verification.Semantics.AirEncoding.Instruction

open Casm

section Main

variable {F : Type _} [Field F]

/-
The halting instruction is a relative jump to the same spot. In general, we don't prove that a
program will halt, but, rather, that *if* it halts it has the desired behavior. This is o.k.
because the STARK can certify that the computation has, in fact, halted.

To take a step forward, however, we need to verify that the current instruction is not a halting
instruction. The following lemmas help with do that efficiently.
-/

-- TODO: Hard-coded, can we pull from casm_instr!{} instead?
-- `jmp rel [ op1_imm ]
def jmpRelInstr : Instr := jumpInstr false (Op0Spec.fp_plus (-1)) (ResSpec.op1 (Op1Spec.mem_pc_plus 1)) false

section Instr

variable (op0 : Op0Spec) (op1 : Op1Spec) (res : ResSpec) (dst : DstSpec) (ap_update : Bool)

theorem assert_eq_ne_jmp_rel : (assertEqInstr op0 res dst ap_update).toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h
  have := congr_arg Instruction.opcodeAssertEq h
  contradiction

theorem call_ne_jmp_rel (call_abs : Bool) :
    (callInstr call_abs res).toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h
  have := congr_arg Instruction.opcodeCall h
  contradiction

theorem ret_ne_jmp_rel : retInstr.toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h
  have := congr_arg Instruction.opcodeRet h
  simp [retInstr, jmpRelInstr, jumpInstr] at this

theorem advance_ap_ne_jmp_rel : (advanceApInstr op0 res).toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h
  have := congr_arg Instruction.apAdd h
  contradiction

theorem jnz_ne_jmp_rel : (jnzInstr op0 op1 dst ap_update).toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h
  have := congr_arg Instruction.pcJnz h
  contradiction

/-- Can be used unless the jump has an immediate argument, in which case instead we have to
    check that the immediate argument is not 0. -/
theorem jump_ne_jmp_rel (jump_abs : Bool) (h : res.toOp1.op1Imm = false) :
    (jumpInstr jump_abs op0 res ap_update).toInstruction ≠ jmpRelInstr.toInstruction := by
  intro h'
  have := congr_arg Instruction.op1Imm h'
  cases' res with op1spec op1spec op1spec
  repeat { cases op1spec
    <;> dsimp [jumpInstr] at this
    <;> (try { repeat { rw [← h] at this; contradiction } }; try contradiction) }

end Instr

/- The definition of a halting execution trace and supporting lemmas.  -/
section Halting

variable [DecidableEq F] (mem : F → F) (s t : RegisterState F)

def IsHaltingState := mem s.pc = jmpRelInstr.toNat ∧ mem (s.pc + 1) = 0

omit [DecidableEq F] in
theorem not_isHaltingState_iff {mem : F → F} {s : RegisterState F} :
    ¬IsHaltingState mem s ↔ mem s.pc ≠ jmpRelInstr.toNat ∨ mem (s.pc + 1) ≠ 0 :=
  not_and_or

def IsHaltingTrace {n : ℕ} (exec : Fin (n + 1) → RegisterState F) : Prop :=
  (∀ i : Fin n, NextState mem (exec (Fin.castSucc i)) (exec i.succ)) ∧
    IsHaltingState mem (exec (Fin.last n))

theorem eq_succ_of_not_halting_state_0 {mem : F → F} {n : ℕ} {exec : Fin (n + 1) → RegisterState F}
    (h : IsHaltingTrace mem exec) (h' : ¬IsHaltingState mem (exec 0)) : ∃ m : ℕ, n = m.succ := by
  apply Nat.exists_eq_succ_of_ne_zero
  rintro rfl
  exact h' h.2

theorem isHaltingTrace_step {mem : F → F} {n : ℕ} {exec : Fin (n.succ + 1) → RegisterState F}
    (h : IsHaltingTrace mem exec) :
    IsHaltingTrace mem (fun i => exec i.succ) := by
  constructor
  · intro i
    simp [← Fin.castSucc_fin_succ _ i]
    exact h.1 i.succ
  exact h.2

theorem isHaltingTrace_remainder {m n : ℕ} {exec : Fin (m + n + 1) → RegisterState F}
    (h : IsHaltingTrace mem exec) :
    IsHaltingTrace mem fun j : Fin (n + 1) => exec (Fin.castOffset' m j) := by
  rcases h with ⟨h1, h2, h3⟩
  rw [IsHaltingTrace]
  refine' ⟨_, h2, h3⟩
  intro i
  rw [Fin.castOffset']
  convert h1 (Fin.castOffset m i)

end Halting

/- The `ensures` predicate, and a bounded version.  -/
section Ensures

variable [DecidableEq F]

/-- Given `mem` and start state `s`, any halting trace `exec` with `exec 0 = s` eventually reaches a
state `t` in `i` steps such that for some `k ≤ i`, `P k (exec i)`. We use the bound on `k` to
ensure a final claim about the range of values that have been range checked.
-/
def Ensures (mem : F → F) (s : RegisterState F) (P : ℕ → RegisterState F → Prop) : Prop :=
  ∀ n : ℕ, ∀ exec : Fin (n + 1) → RegisterState F,
      IsHaltingTrace mem exec → exec 0 = s → ∃ i : Fin (n + 1), ∃ k ≤ i, P k (exec i)

/-- for use with code blocks that end with a return -/
@[reducible]
def EnsuresRet (mem : F → F) (s : RegisterState F) (P : ℕ → RegisterState F → Prop) : Prop :=
  Ensures mem s fun k t => t.pc = mem (s.fp - 1) ∧ t.fp = mem (s.fp - 2) ∧ P k t

def Ensuresb (bound : ℕ) (mem : F → F) (s : RegisterState F) (P : ℕ → RegisterState F → Prop) : Prop :=
  ∀ n : ℕ, n < bound → ∀ exec : Fin (n + 1) → RegisterState F,
        IsHaltingTrace mem exec → exec 0 = s → ∃ i : Fin (n + 1), ∃ k ≤ i, P k (exec i)

theorem ensures_of_ensuresb {mem : F → F} {s : RegisterState F} {P : ℕ → RegisterState F → Prop}
    (h : ∀ bound, Ensuresb bound mem s P) : Ensures mem s P := fun n =>
  h (n + 1) _ (Nat.lt_succ_self n)

theorem ensuresb_of_le {mem : F → F} {s : RegisterState F} {P : ℕ → RegisterState F → Prop}
    {bound₁ bound₂ : ℕ} (h_bound : bound₂ ≤ bound₁) (h : Ensuresb bound₁ mem s P) :
    Ensuresb bound₂ mem s P := by intro n h_n; exact h n (Nat.lt_of_lt_of_le h_n h_bound)

theorem ensuresb_of_ensuresb {mem : F → F} {s : RegisterState F} {P : ℕ → RegisterState F → Prop}
    {bound : ℕ} (h : ∀ bound₁ ≤ bound, Ensuresb bound₁ mem s P) : Ensuresb bound mem s P :=
  h bound (le_of_eq rfl)

@[reducible]
def EnsuresbRet (bound : ℕ) (mem : F → F) (s : RegisterState F) (P : ℕ → RegisterState F → Prop) : Prop :=
  Ensuresb bound mem s fun k t => t.pc = mem (s.fp - 1) ∧ t.fp = mem (s.fp - 2) ∧ P k t

theorem ensuresRet_of_ensuresbRet {mem : F → F} {s : RegisterState F}
    {P : ℕ → RegisterState F → Prop} (h : ∀ bound, EnsuresbRet bound mem s P) :
    EnsuresRet mem s P := fun n => h (n + 1) _ (Nat.lt_succ_self n)

/-- Takes a step and augments `k` by 1. -/
theorem ensuresb_step {bound : ℕ} {mem : F → F} {s t : RegisterState F}
    {P : ℕ → RegisterState F → Prop} {Q : Prop} (h0 : ¬IsHaltingState mem s)
    (h1 : ∀ t', NextState mem s t' → t' = t ∧ Q)
    (h : Q → Ensuresb bound mem t fun k t' => P (k + 1) t') : Ensuresb (bound + 1) mem s P := by
  rintro n₀ n₀le exec h2 rfl
  rcases eq_succ_of_not_halting_state_0 h2 h0 with ⟨n, rfl⟩
  rcases h (h1 _ (h2.1 0)).2 n (Nat.le_of_succ_le_succ n₀le) (fun i => exec i.succ)
      (isHaltingTrace_step h2) (h1 _ (h2.1 0)).1 with
    ⟨i, k, hik, h4⟩
  use i.succ, k.succ; constructor
  · exact Fin.succ_le_succ_iff.mpr hik
  convert h4

-- used to add a + 1 if necessary
theorem ensuresb_succ {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P : ℕ → RegisterState F → Prop} (h : Ensuresb (bound + 1) mem s P) : Ensuresb bound mem s P :=
  fun _ nlt => h _ (nlt.trans <| Nat.lt_succ_self _)

theorem ensuresb_test {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P : ℕ → RegisterState F → Prop} (h : Ensuresb (bound + 1) mem s P) :
    Ensuresb (bound + 1) mem s P := h

theorem ensuresb_trans {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P Q : ℕ → RegisterState F → Prop} (h0 : Ensures mem s P)
    (h1 : ∀ k t, P k t → Ensuresb bound mem t fun k' => Q (k + k')) : Ensuresb bound mem s Q := by
  rintro n nlt exec h2 h3
  rcases h0 _ _ h2 h3 with ⟨i, k, hik1, hik2⟩
  rcases Fin.exists_eq_add i with ⟨m, j, hm, rfl⟩
  have : exec (Fin.castOffset' m 0) = exec i := by congr; ext; exact hm
  rcases h1 _ _ hik2 _ (lt_of_le_of_lt (Nat.le_add_left _ _) nlt) _
      (isHaltingTrace_remainder mem h2) this with
    ⟨i', k', hi'k', h4⟩
  have : ↑k + j + 1 ≤ m + j + 1 := by
    apply Nat.succ_le_succ
    apply Nat.add_le_add_right
    apply le_trans (Fin.val_fin_le.mpr hik1)
    rw [← hm]
  use Fin.castOffset' m i', Fin.castLE this (Fin.castOffset' k k')
  constructor
  · rw [Fin.le_iff_val_le_val]
    simp [Fin.castOffset', Fin.castOffset]
    apply add_le_add _ (Fin.le_iff_val_le_val.mp hi'k')
    · apply le_trans (Fin.val_fin_le.mpr hik1)
      rw [← hm]
  exact h4

theorem ensuresb_rec_trans {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P Q : ℕ → RegisterState F → Prop} (h0 : Ensuresb bound mem s P)
    (h1 : ∀ k t, P k t → Ensuresb bound mem t fun k' => Q (k + k')) : Ensuresb bound mem s Q := by
  rintro n nlt exec h2 h3
  rcases h0 _ nlt _ h2 h3 with ⟨i, k, hik1, hik2⟩
  rcases Fin.exists_eq_add i with ⟨m, j, hm, rfl⟩
  have : exec (Fin.castOffset' m 0) = exec i := by congr; ext; exact hm
  rcases h1 _ _ hik2 _ (lt_of_le_of_lt (Nat.le_add_left _ _) nlt) _
      (isHaltingTrace_remainder mem h2) this with
    ⟨i', k', hi'k', h4⟩
  have : ↑k + j + 1 ≤ m + j + 1 := by
    apply Nat.succ_le_succ
    apply Nat.add_le_add_right
    apply le_trans (Fin.val_fin_le.mpr hik1)
    rw [← hm]
  use Fin.castOffset' m i', Fin.castLE this (Fin.castOffset' k k')
  constructor
  · rw [Fin.le_iff_val_le_val]
    simp [Fin.castOffset', Fin.castOffset]
    apply add_le_add _ (Fin.le_iff_val_le_val.mp hi'k')
    · apply le_trans (Fin.val_fin_le.mpr hik1)
      rw [← hm]
  exact h4

theorem ensuresb_id {bound : ℕ} {mem : F → F} {s : RegisterState F} {P : ℕ → RegisterState F → Prop}
    (h : P 0 s) : Ensuresb (bound + 1) mem s P := by
  intro n _ exec _ hexec0
  use 0, 0, le_refl _
  rwa [hexec0]

theorem ensuresb_rec {mem : F → F} (P : RegisterState F → F → ℕ → RegisterState F → Prop)
    (Haux : F → RegisterState F → Prop) (s : RegisterState F) (arg : F) (hHaux : Haux arg s)
    (hind : ∀ bound,
        (∀ (arg : F) (s : RegisterState F), Haux arg s → Ensuresb bound mem s (P s arg)) →
          ∀ {arg : F}, ∀ {s : RegisterState F}, Haux arg s → Ensuresb (bound + 1) mem s (P s arg)) :
    Ensures mem s (P s arg) := by
  have :
    ∀ bound, ∀ {arg : F}, ∀ {s : RegisterState F}, Haux arg s → Ensuresb bound mem s (P s arg) := by
    intro bound
    induction' bound with bound ih
    · intro _ _ _ n nlt; exact absurd nlt (Nat.not_lt_zero _)
    apply hind; exact @ih
  apply ensures_of_ensuresb fun bound => this bound hHaux

-- for handling blocks
theorem ensuresbRet_trans {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P Q : ℕ → RegisterState F → Prop} (h0 : EnsuresbRet bound mem s P)
    (h1 : ∀ k t, P k t → Q k t) : EnsuresbRet bound mem s Q := by
  rintro n nlt exec h2 h3
  rcases h0 _ nlt _ h2 h3 with ⟨i, k, hik1, hik2, hik3, hik4⟩
  exact ⟨i, k, hik1, hik2, hik3, h1 _ _ hik4⟩

end Ensures

/- Characterize next state transitions.  -/
section NextState

variable [DecidableEq F]

theorem Instruction.nextState_iff_of_eq [char_ge : CharGe263 F] {i : Instruction} {mem : F → F}
    {s t : RegisterState F} (h : mem s.pc = i.toNat) : NextState mem s t ↔ i.NextState mem s t := by
  rw [NextState]; constructor
  · rintro ⟨i', i'eq, i'next_state⟩
    have : i = i' := inst_unique char_ge _ _ (h.symm.trans i'eq)
    rwa [this]
  intro h'
  exact ⟨i, h, h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩

variable {mem : F → F} {s : RegisterState F} {P : ℕ → RegisterState F → Prop}

theorem assert_eq_ensuresb' [char_ge : CharGe263 F] {bound : ℕ} {op0 : Op0Spec} {res : ResSpec}
    {dst : DstSpec} {ap_update : Bool} (h : mem s.pc = (assertEqInstr op0 res dst ap_update).toNat)
    (h' : computeDst mem s dst = computeRes mem s op0 res →
        Ensuresb bound mem ⟨bumpPc s res.toOp1.op1Imm, bumpAp s ap_update, s.fp⟩ fun k t =>
          P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact assert_eq_ne_jmp_rel _ _ _ _ (inst_unique char_ge _ _ h0)
  have h2 :
    ∀ t, NextState mem s t →
        t = ⟨bumpPc s res.toOp1.op1Imm, bumpAp s ap_update, s.fp⟩ ∧
          computeDst mem s dst = computeRes mem s op0 res := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_assert_eq] at ht
    constructor
    · ext
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2.1
    · exact ht.2.2.2
  apply ensuresb_step h1 h2 h' _ nlt

theorem jump_ensuresb [char_ge : CharGe263 F] {bound} {op0 : Op0Spec} {res : ResSpec}
    {ap_update : Bool} {jump_abs : Bool}
    (h : mem s.pc = (jumpInstr jump_abs op0 res ap_update).toNat) (h_aux : res.toOp1.op1Imm = false)
    (h' : Ensuresb bound mem ⟨jumpPc s jump_abs (computeRes mem s op0 res), bumpAp s ap_update, s.fp⟩
        fun k t => P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact jump_ne_jmp_rel _ _ _ _ h_aux (inst_unique char_ge _ _ h0)
  have h2 :
    ∀ t, NextState mem s t →
        t = ⟨jumpPc s jump_abs (computeRes mem s op0 res), bumpAp s ap_update, s.fp⟩ ∧ True := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_jump] at ht
    constructor; ext <;> simp [ht]; trivial
  apply ensuresb_step h1 h2 (fun _ => h') _ nlt

theorem jump_ensuresb' [char_ge : CharGe263 F] {bound : ℕ} {op0 : Op0Spec} {res : ResSpec}
    {ap_update : Bool} {jump_abs : Bool}
    (h : mem s.pc = (jumpInstr jump_abs op0 res ap_update).toNat) {x : ℤ} {h0 : |x| ≠ 0}
    {h1 : |x| < 2 ^ 63} (h_aux : mem (s.pc + 1) = checkedIntNz x h0 h1)
    (h' : Ensuresb bound mem ⟨jumpPc s jump_abs (computeRes mem s op0 res), bumpAp s ap_update, s.fp⟩
        fun k t => P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff, h_aux]; right
    apply Int.cast_ne_zero_of_abs_lt_char h0
    apply lt_of_lt_of_le h1
    change ((2 ^ 63 : ℕ) : ℤ) ≤ _
    rw [Int.ofNat_le]
    apply char_ge.h
  have h2 :
    ∀ t, NextState mem s t →
        t = ⟨jumpPc s jump_abs (computeRes mem s op0 res), bumpAp s ap_update, s.fp⟩ ∧ True := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_jump] at ht
    constructor; ext <;> simp [ht]; trivial
  apply ensuresb_step h1 h2 (fun _ => h') _ nlt

theorem jnz_ensuresb [char_ge : CharGe263 F] {bound : ℕ} {op0 : Op0Spec} {op1 : Op1Spec}
    {dst : DstSpec} {ap_update : Bool} (h : mem s.pc = (jnzInstr op0 op1 dst ap_update).toNat)
    (h₀ : computeDst mem s dst = 0 →
        Ensuresb bound mem ⟨bumpPc s op1.op1Imm, bumpAp s ap_update, s.fp⟩ fun k t => P (k + 1) t)
    (h₁ : computeDst mem s dst ≠ 0 →
        Ensuresb bound mem ⟨s.pc + computeOp1 mem s op0 op1, bumpAp s ap_update, s.fp⟩ fun k t =>
          P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact jnz_ne_jmp_rel _ _ _ _ (inst_unique char_ge _ _ h0)
  have h2 :
    ∀ t, NextState mem s t →
        t = ⟨ite (computeDst mem s dst = 0) (bumpPc s op1.op1Imm)
                (s.pc + computeOp1 mem s op0 op1),
              bumpAp s ap_update, s.fp⟩ ∧ True := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_jnz] at ht
    simp [ht]
    ext <;> simp [ht]
  apply ensuresb_step h1 h2 _ _ nlt
  by_cases h3 : computeDst mem s dst = 0
  · intro
    rw [if_pos h3]
    exact h₀ h3
  intro
  rw [if_neg h3]
  exact h₁ h3

theorem call_ensuresb [char_ge : CharGe263 F] {bound : ℕ} {res : ResSpec} {call_abs : Bool}
    (h : mem s.pc = (callInstr call_abs res).toNat)
    (h' : mem s.ap = s.fp →
        mem (s.ap + 1) = bumpPc s res.toOp1.op1Imm →
          Ensuresb bound mem
            ⟨jumpPc s call_abs (computeRes mem s (Op0Spec.ap_plus 1) res), s.ap + 2, s.ap + 2⟩
            fun k t => P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact call_ne_jmp_rel _ _ (inst_unique char_ge _ _ h0)
  have h2 : ∀ t, NextState mem s t →
        t = ⟨jumpPc s call_abs (computeRes mem s (Op0Spec.ap_plus 1) res), s.ap + 2, s.ap + 2⟩ ∧
          mem (s.ap + 1) = bumpPc s res.toOp1.op1Imm ∧ mem s.ap = s.fp := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_call] at ht
    simp [ht]
    ext <;> simp [ht]
  apply ensuresb_step h1 h2 _ _ nlt
  intro h3
  apply h' h3.2 h3.1

theorem ret_ensuresb [char_ge : CharGe263 F] {bound : ℕ} (h : mem s.pc = retInstr.toNat)
    (h' : Ensuresb bound mem ⟨mem (s.fp + -1), s.ap, mem (s.fp - 2)⟩ fun k t => P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact ret_ne_jmp_rel (inst_unique char_ge _ _ h0)
  have h2 : ∀ t, NextState mem s t → t = ⟨mem (s.fp + -1), s.ap, mem (s.fp - 2)⟩ ∧ True := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_ret] at ht
    simp [ht]
    ext <;> simp [ht]
  apply ensuresb_step h1 h2 (fun _ => h') _ nlt

-- TODO: It breaks when "ap" is used below in h₃, fixed with ap'
theorem call_ensuresb_trans [char_ge : CharGe263 F] {bound : ℕ} {P Q : ℕ → RegisterState F → Prop}
    {res : ResSpec} {call_abs : Bool} {x : F} (h₀ : mem s.pc = x)
    (h₁ : x = (callInstr call_abs res).toNat)
    (h₂ : EnsuresRet mem
        ⟨jumpPc s call_abs (computeRes mem s (Op0Spec.ap_plus 1) res), s.ap + 2, s.ap + 2⟩ P)
    (h₃ : ∀ k ap', P k ⟨bumpPc s res.toOp1.op1Imm, ap', s.fp⟩ →
          Ensuresb bound mem ⟨bumpPc s res.toOp1.op1Imm, ap', s.fp⟩ fun k' => Q (k + k' + 1)) :
    Ensuresb (bound + 1) mem s Q := by
  apply call_ensuresb (h₀.trans h₁)
  intro h1 h2
  apply ensuresb_trans h₂; dsimp
  rintro k ⟨tpc, tap, tfp⟩; dsimp
  rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero]; norm_num1
  rw [h1, h2]
  rintro ⟨rfl, rfl, hP⟩
  apply h₃ _ _ hP

theorem call_rec_ensuresb_trans [char_ge : CharGe263 F] {bound : ℕ}
    {P Q : ℕ → RegisterState F → Prop} {res : ResSpec} {call_abs : Bool} {x : F} (h₀ : mem s.pc = x)
    (h₁ : x = (callInstr call_abs res).toNat)
    (h₂ : EnsuresbRet bound mem
        ⟨jumpPc s call_abs (computeRes mem s (Op0Spec.ap_plus 1) res), s.ap + 2, s.ap + 2⟩ P)
    (h₃ : ∀ k ap', P k ⟨bumpPc s res.toOp1.op1Imm, ap', s.fp⟩ →
          Ensuresb bound mem ⟨bumpPc s res.toOp1.op1Imm, ap', s.fp⟩ fun k' => Q (k + k' + 1)) :
    Ensuresb (bound + 1) mem s Q := by
  apply call_ensuresb (h₀.trans h₁)
  intro h1 h2
  apply ensuresb_rec_trans h₂; dsimp
  rintro k ⟨tpc, tap, tfp⟩; dsimp
  rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero]; norm_num1
  rw [h1, h2]
  rintro ⟨rfl, rfl, hP⟩
  apply h₃ _ _ hP

theorem advance_ap_ensuresb [char_ge : CharGe263 F] {bound : ℕ} {op0 : Op0Spec} {res : ResSpec}
    (h : mem s.pc = (advanceApInstr op0 res).toNat)
    (h' : Ensuresb bound mem ⟨bumpPc s res.toOp1.op1Imm, s.ap + computeRes mem s op0 res, s.fp⟩
        fun k t => P (k + 1) t) :
    Ensuresb (bound + 1) mem s P := by
  intro n nlt exec
  have h1 : ¬IsHaltingState mem s := by
    rw [not_isHaltingState_iff]; left; rw [h]
    intro h0
    exact advance_ap_ne_jmp_rel _ _ (inst_unique char_ge _ _ h0)
  have h2 : ∀ t, NextState mem s t →
        t = ⟨bumpPc s res.toOp1.op1Imm, s.ap + computeRes mem s op0 res, s.fp⟩ ∧ True := by
    intro t ht
    rw [Instruction.nextState_iff_of_eq h, ← Instr.NextState, nextState_advance_ap] at ht
    simp [ht]
    ext <;> simp [ht]
  apply ensuresb_step h1 h2 (fun _ => h') _ nlt

end NextState

/- Theorems to handle the range-checked hypotheses.  -/
def IsRangeChecked (rc_bound : ℕ) (a : F) : Prop :=
  ∃ n : ℕ, n < rc_bound ∧ a = ↑n

def RangeChecked (mem : F → F) (rc_start : F) (k rc_bound : ℕ) : Prop :=
  ∀ i < k, IsRangeChecked rc_bound (mem (rc_start + i))

theorem rangeChecked_mono {mem : F → F} {rc_start : F} {k rc_bound : ℕ} (k' : ℕ) (k'le : k' ≤ k)
    (h : RangeChecked mem rc_start k rc_bound) : RangeChecked mem rc_start k' rc_bound :=
  fun i iltk' => h i (lt_of_lt_of_le iltk' k'le)

theorem rangeChecked_add_left {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : RangeChecked mem rc_start (k' + k) rc_bound) : RangeChecked mem rc_start k rc_bound :=
  rangeChecked_mono _ (Nat.le_add_left _ _) h

theorem rangeChecked_add_right {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : RangeChecked mem rc_start (k + k') rc_bound) : RangeChecked mem rc_start k rc_bound :=
  rangeChecked_mono _ (Nat.le_add_right _ _) h

theorem rangeChecked_offset {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : RangeChecked mem rc_start (k + k') rc_bound) :
    RangeChecked mem (rc_start + k') k rc_bound := by
  intro i iltk
  rcases h _ (add_lt_add_right iltk k') with ⟨i', hi'⟩
  use i'; rwa [add_assoc, ← Nat.cast_add, add_comm k']

theorem rangeChecked_offset' {mem : F → F} {rc_start : F} {k' k rc_bound : ℕ}
    (h : RangeChecked mem rc_start (k + k') rc_bound) :
    RangeChecked mem (rc_start + k) k' rc_bound := by
  rw [add_comm] at h
  exact rangeChecked_offset h

def RcEnsures (mem : F → F) (rc_bound k : ℕ) (a0 a1 : F) (P : Prop) :=
  a1 = a0 + k ∧ (RangeChecked mem a0 k rc_bound → P)

theorem rcEnsures_comp {mem : F → F} {rc_bound k0 k1 : ℕ} {a0 a1 a2 : F} {P Q : Prop}
    (h0 : RcEnsures mem rc_bound k0 a0 a1 P) (h1 : RcEnsures mem rc_bound k1 a1 a2 Q) :
    RcEnsures mem rc_bound (k0 + k1) a0 a2 (P ∧ Q) := by
  rcases h0 with ⟨hk0, rc0⟩
  rcases h1 with ⟨hk1, rc1⟩
  constructor
  · rw [hk1, hk0, add_assoc, Nat.cast_add]
  intro h; constructor
  · exact rc0 (rangeChecked_add_right h)
  apply rc1; rw [hk0]; exact rangeChecked_offset' h

theorem rcEnsures_trans {mem : F → F} {rc_bound k : ℕ} {a0 a1 : F} {P Q : Prop}
    (h1 : RcEnsures mem rc_bound k a0 a1 P) (h2 : P → Q) : RcEnsures mem rc_bound k a0 a1 Q := by
  rcases h1 with ⟨hk, h⟩
  exact ⟨hk, fun h' => h2 (h h')⟩

end Main

/- Tactics.  -/
namespace Tactic

namespace Interactive

-- TODO: Figure out how to properly do an optional " at "
macro (name := arith_simps₁) "arith_simps" : tactic => `(tactic|
  ( try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
    add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc]
    try norm_num1
    try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
    add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] ))

macro (name := arith_simps₂) "arith_simps_at" loc:ident : tactic => `(tactic|
  ( try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
    add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] at ($loc)
    try norm_num1 at ($loc)
    try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
    add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] at ($loc) ))

macro (name := ensures_simps₁) "ensures_simps" : tactic => `(tactic|
  ( try simp only [ResSpec.toOp1, computeRes, computeOp1, computeOp0, Op1Spec.op1Imm,
      computeDst, bumpPc, bumpAp, jumpPc, clip_checked, checkedIntNz_eq,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc]
    try norm_num1
    try simp only [ResSpec.toOp1, computeRes, computeOp1, computeOp0, Op1Spec.op1Imm,
      computeDst, bumpPc, bumpAp, jumpPc, clip_checked, checkedIntNz_eq,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] ))

macro (name := ensures_simps₂) "ensures_simps_at" loc:ident : tactic => `(tactic|
  ( try simp only [ResSpec.toOp1, computeRes, computeOp1, computeOp0, Op1Spec.op1Imm,
      computeDst, bumpPc, bumpAp, jumpPc, clip_checked, checkedIntNz_eq,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] at ($loc)
    try norm_num1 at ($loc)
    try simp only [ResSpec.toOp1, computeRes, computeOp1, computeOp0, Op1Spec.op1Imm,
      computeDst, bumpPc, bumpAp, jumpPc, clip_checked, checkedIntNz_eq,
      Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, zero_add, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] at ($loc) ))

macro (name := unpack_memory₁) "unpack_memory" code:ident " at " loc:ident : tactic => `(tactic|
  ( unfold $code at ($loc)
    try simp only [MemAt, add_assoc, and_true, Int.cast_ofNat, Int.int_cast_ofNat, Int.cast_one, Int.cast_zero, CoeT.coe, CoeHTCT.coe] at ($loc)
    try norm_num1 at ($loc)
    rcases ($loc) ))

macro (name := unpack_memory₂) "unpack_memory" code:ident " at " loc:ident " with " pat:rcasesPat : tactic => `(tactic|
  ( unfold $code at ($loc)
    try simp only [MemAt, add_assoc, and_true, Int.cast_ofNat, Int.int_cast_ofNat, Int.cast_one, Int.cast_zero, CoeT.coe, CoeHTCT.coe] at ($loc)
    try norm_num1 at ($loc)
    rcases ($loc) with $pat ))

macro (name := next_memory) "next_memory" loc:ident " with " instr:ident : tactic => `(tactic|
  ( rcases ($loc) with ⟨$instr, $loc⟩
    try simp only [MemAt, add_assoc, and_true, Int.cast_ofNat, Int.int_cast_ofNat, Int.cast_one, Int.cast_zero, CoeT.coe, CoeHTCT.coe] at ($instr)
    try norm_num1 at ($instr)))

macro (name := ensuresb_make_succ) "ensuresb_make_succ" : tactic =>
  `(tactic| first
    | apply ensuresb_test
    | apply ensuresb_succ)

macro (name := step_assert_eq₁) "step_assert_eq" h:term " with " hw:ident : tactic => `(tactic|
  ( ensuresb_make_succ
    arith_simps
    apply assert_eq_ensuresb'
    apply $h
    ensures_simps
    intro ($hw) ) )

macro (name := step_assert_eq₂) "step_assert_eq" h:term "," h':term " with " hw:ident : tactic => `(tactic|
  ( ensuresb_make_succ
    arith_simps
    apply assert_eq_ensuresb'
    apply $h
    ensures_simps
    try rw [($h')]
    intro ($hw) ) )

macro (name := step_jump) "step_jump" h:term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply jump_ensuresb
    apply $h
    rfl
    ensures_simps ))

macro (name := step_jump_imm) "step_jump_imm" h:term "," h':term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply jump_ensuresb'
    apply $h
    ensures_simps
    apply $h'
    ensures_simps
    try rw [($h')]
    ensures_simps ))

macro (name := step_jnz₁) "step_jnz" h:term " with " hw:ident hw':ident : tactic => `(tactic|
  ( ensuresb_make_succ
    apply jnz_ensuresb
    apply $h
    ensures_simps
    intro ($hw)
    swap
    ensures_simps
    intro ($hw')
    swap ))

macro (name := step_jnz₂) "step_jnz" h:term "," h':term " with " hw:ident hw':ident : tactic => `(tactic|
  ( ensuresb_make_succ
    apply jnz_ensuresb
    apply $h
    ensures_simps
    try rw [($h')]
    intro ($hw)
    swap
    ensures_simps
    try rw [($h')]
    intro ($hw')
    swap ))

macro (name := step_call') "step_call" h:term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply call_ensuresb
    apply $h
    ensures_simps ))

macro (name := step_ret') "step_ret" h:term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply ret_ensuresb
    apply $h
    ensures_simps ))

macro (name := step_advance_ap₁) "step_advance_ap" h:term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply advance_ap_ensuresb
    apply $h
    ensures_simps ))

macro (name := step_advance_ap₂) "step_advance_ap" h:term "," h':term : tactic => `(tactic|
  ( ensuresb_make_succ
    apply advance_ap_ensuresb
    apply $h
    ensures_simps
    try rw [($h')]
    ensures_simps ))

macro (name := step_done) "step_done" : tactic =>
  `(tactic| ( ensuresb_make_succ; apply ensuresb_id ))

/-- A weaker version of the interactive `use` tactic, which doesn't call `triv` or `rfl` -/
macro (name := use_only) "use_only" es:term,+ : tactic =>
  `(tactic| refine ⟨$es,*, ?_⟩)

/-- norm_num1 plus an extra simp rule -/
macro (name := norm_num2) "norm_num2" : tactic =>
  `(tactic| ( norm_num1; try simp only [add_neg_eq_sub] ) )

/- A custom tactic for automating things that come out of Yoav's generator
   The steps to prove an IsRangeChecked tactic
-/
macro (name := rc_app) "rc_app" h_rc:ident x:num tv:ident rc:ident : tactic => `(tactic |
  ( rcases ($h_rc) ($x) (by norm_num1) with ⟨n, hn₁, hn₂⟩
    arith_simps_at hn₂
    constructor
    · use_only n, hn₁
      simp only [($tv), ($rc)]
      arith_simps
      exact hn₂
    clear hn₂
    clear hn₁
    clear n ))

/- For very long functions, this unwraps one new hypothesis at a time and simplifies it -/
macro (name := unwrap_hyp) "unwrap_hyp" "at" h:ident " as " h':ident : tactic =>
  `(tactic| (
    unfold MemAt at ($h)
    rcases ($h) with ⟨$h', $h⟩
    simp only [add_assoc, and_true, Int.cast_ofNat, Int.int_cast_ofNat, Int.cast_one, Int.cast_zero, CoeT.coe, CoeHTCT.coe] at ($h')
    norm_num1 at ($h') ))


theorem mkdef_helper {α : Type} {p : Prop} {y : α} : (∀ ⦃x⦄, x = y → p) → p :=
  fun hx => hx rfl

/--
`mkdef h : x = t` introduces a new variable `x` into the context with
assumption `h : x = t`. It is essentially a simplified version of
`generalize'` with the equation syntax reversed.
-/
macro (name := mkdef) "mkdef " h:ident " : " x:ident " = " t:term : tactic =>
  `(tactic| (
      apply @mkdef_helper _ _ $t
      intro $x $h ))

end Interactive

end Tactic

/- Some useful things for the autogenerated proofs.  -/
section

theorem assert_eq_reduction {F : Type} {a b c d : F} (h : c = d) (h' : a = c ∧ d = b) : a = b :=
  (h'.1.trans h).trans h'.2

variable {F : Type _} [Field F]

theorem cond_aux1 {a b t : F} (h1 : t = a - b) (h2 : t = 0) : a = b := by
  rw [h2] at h1
  exact eq_of_sub_eq_zero h1.symm

theorem cond_aux2 {a b t : F} (h1 : t = a - b) (h2 : t ≠ 0) : a ≠ b := by
  intro h3
  apply h2
  rwa [h3, sub_self] at h1

theorem eq_sub_of_eq_add {a b c : F} (h : b = a + c) : a = b - c :=
  eq_sub_of_add_eq h.symm

-- a trick for inferring the value of the ap at proof time
theorem of_registerState [DecidableEq F] {bound : ℕ} {mem : F → F} {s : RegisterState F}
    {P : ℕ → RegisterState F → Prop} :
    (∀ x, x = s → Ensuresb bound mem s P) → Ensuresb bound mem s P := fun h => h s rfl

/-- division with a default value -/
def ddiv [DecidableEq F] (a b c : F) : F := if b ≠ 0 then a / b else c

theorem ddiv_eq [DecidableEq F] {a b c : F} (h : b ≠ 0) : ddiv a b c = a / b :=
  if_pos h

theorem eq_ddiv_of_eq_mul [DecidableEq F] {a b c : F} (h : a = c * b) : c = ddiv a b c := by
  by_cases h' : b ≠ 0
  · rw [ddiv, if_pos h', eq_div_iff h', h]
  rw [ddiv, if_neg h']

theorem exists_eq_ddiv_of_eq_mul [DecidableEq F] {a b c : F} (h : a = c * b) :
    ∃ d, c = ddiv a b d :=
  ⟨c, eq_ddiv_of_eq_mul h⟩

-- for handling division by a constant
theorem div_eq_mul_inv' {F : Type _} [Field F] {x y z : F} (h : y * z = 1) : x / y = x * z := by
  have : y ≠ 0 := by intro yzero; simp [yzero] at h
  symm; apply eq_div_of_mul_eq this
  rw [mul_assoc, mul_comm z, h, mul_one]

end
