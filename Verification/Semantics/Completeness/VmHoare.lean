/-
Notes: this is a version of the semantics to be used for completness proofs, using
MaybeRelocatable values (called `Mrel` here) rather than elements of a Finite field.

We use the virtual machine model because completeness requires us to say that there is an
assignment to memory (specifically, the `ap` range used by the subroutines and any values
the procedure range checks) that allows the procedure to run until it returns.
This requires us to know that the program, the allocation memory, and range checked values
are all separate. Even if we wanted to keep track of that in a Finite field (which would be
a mess), we would also have to bound all the resources we use, to ensure that there isn't
a memory overflow.

Using the virtual machine brackets all that. We just assume that the memory segments are separate
and that we have as much memory as we need.

Note that since we prove soundness for the field semantics and completeness for the VM semantics,
we can't use soundness and completeness together to show that something terminates with a
certain property. The models are incomparable: soundness results sometimes require the
field to be of Finite characteristic, whereas the virtual machine assumes that the memory
is inFinite. In a soundness proof, it's not just that the values are in a Finite field; in
principle, a soudnenss proof could use the fact that memory wraps around, though it generally
doesn't.
-/

import Verification.Semantics.Completeness.VmAssembly
import Verification.Semantics.Completeness.VmAssemblyStep

set_option autoImplicit false

/-
Reasoning about contents of memory.
-/

open Mrel

/-
Returning computation sequences.
-/

def IsReturningTrace (PRIME : Int) {n : ℕ} (mem : Mrel → Mrel) (s : VmRegisterState)
    (exec : Fin (n + 1) → VmRegisterState) : Prop :=
  exec 0 = s ∧
    (∀ i : Fin n, VmNextState PRIME mem (exec i.castSucc) (exec i.succ)) ∧
      mem (prog (exec (Fin.last n)).pc) = val retInstr.toNat ∧
    (exec (Fin.last n)).fp = s.fp

def TraceStep {n : ℕ} (s : VmRegisterState) (exec : Fin n → VmRegisterState)  :
  Fin (n + 1) → VmRegisterState :=
@Fin.cases n (fun _ => VmRegisterState) s exec

theorem traceStep_zero {n : ℕ} (exec : Fin n → VmRegisterState) (s : VmRegisterState) :
  TraceStep s exec 0 = s := rfl

theorem traceStep_succ {n : ℕ} (exec : Fin n → VmRegisterState) (s : VmRegisterState)
    (i : Fin n):
  TraceStep s exec i.succ = exec i :=
by rw [TraceStep, Fin.cases_succ]

theorem is_returning_traceStep (PRIME : Int) {mem : Mrel → Mrel} {n : ℕ}
    {exec : Fin n.succ → VmRegisterState} {s t : VmRegisterState}
    (h : IsReturningTrace PRIME mem t exec)
    (h' : VmNextState PRIME mem s t)
    (h'': s.fp = t.fp) :
  IsReturningTrace PRIME mem s (TraceStep s exec) := by
  constructor
  rw [traceStep_zero]
  constructor
  · apply Fin.cases
    · rw [traceStep_succ, Fin.castSucc_zero, traceStep_zero, h.1]
      exact h'
    intro i
    rw [Fin.castSucc_fin_succ, traceStep_succ, traceStep_succ]
    apply h.2.1
  constructor
  rw [←Fin.succ_last, traceStep_succ, h.2.2.1]
  rw [←Fin.succ_last, traceStep_succ, h.2.2.2, h'']

def Returns (PRIME : Int) (mem : Mrel → Mrel) (s : VmRegisterState)
    (P : ℕ → VmRegisterState → Prop) : Prop :=
  ∃ n : ℕ, ∃ exec : Fin (n+1) → VmRegisterState,
    IsReturningTrace PRIME mem s exec ∧
      ∃ k ≤ n, P k (exec (Fin.last n))

theorem returns_step {PRIME : Int} {mem : Mrel → Mrel} {s t : VmRegisterState}
      {P : ℕ → VmRegisterState → Prop}
    (h0 : VmNextState PRIME mem s t ∧ s.fp = t.fp)
    (h1 : Returns PRIME mem t (fun k t' => P (k + 1) t')) :
  Returns PRIME mem s P := by
  rcases h1 with ⟨n, e, he0, ⟨k, hkle, hk0⟩⟩
  rcases h0 with ⟨ht, hsfp⟩
  use n+1, TraceStep s e, is_returning_traceStep PRIME he0 ht hsfp, k+1, Nat.succ_le_succ hkle
  rw [←Fin.succ_last, traceStep_succ]
  exact hk0

theorem returns_step' {PRIME : Int} {mem : Mrel → Mrel} {s t : VmRegisterState}
    {P : ℕ → VmRegisterState → Prop}
    {Q : Prop}
    (h0 : Q → VmNextState PRIME mem s t ∧ s.fp = t.fp)
    (h1 : Q ∧ Returns PRIME mem t (fun k t' => P (k + 1) t')) :
  Returns PRIME mem s P :=
returns_step (h0 h1.1) h1.2

section VmNextState

variable {mem : Mrel → Mrel}
variable {s : VmRegisterState}
variable {P : ℕ → VmRegisterState → Prop}

theorem assert_eq_returns {PRIME : Int}
    {op0 : Op0Spec} {res : ResSpec} {dst : DstSpec} {ap_update : Bool}
    (h  : mem (prog s.pc) = val (assertEqInstr op0 res dst ap_update).toNat)
    (h' : (vmComputeDst mem s dst).Equiv PRIME (vmComputeRes mem s op0 res) ∧
      Returns PRIME mem ⟨vmBumpPc s res.toOp1.op1Imm, vmBumpAp s ap_update, s.fp⟩
        (fun k t => P (k + 1) t)) :
  Returns PRIME mem s P := by
  apply returns_step' _ h'
  intro h₀
  rw [VmNextState, ←exists_and_right]
  use (assertEqInstr op0 res dst ap_update).toInstruction
  rw [←Instr.toNat, ←Instr.VmNextState, vmNextState_assert_eq]
  refine ⟨⟨h, rfl, rfl, rfl, h₀⟩, rfl⟩

theorem jump_returns {PRIME : Int}
    {op0 : Op0Spec} {res : ResSpec} {ap_update : Bool} {jump_abs : Bool}
    (h : mem (prog s.pc) = val (jumpInstr jump_abs op0 res ap_update).toNat)
    (h' : Returns PRIME mem ⟨vmJumpPc s jump_abs (vmComputeRes mem s op0 res),
      vmBumpAp s ap_update, s.fp⟩ (fun k t => P (k + 1) t)) :
  Returns PRIME mem s P := by
  apply returns_step _ h'
  constructor
  use (jumpInstr jump_abs op0 res ap_update).toInstruction
  rw [←Instr.toNat, ←Instr.VmNextState, vmNextState_jump]
  refine ⟨h, rfl, rfl, rfl⟩
  rfl

theorem jnz_returns {PRIME : Int}
    {op0 : Op0Spec} {op1 : Op1Spec} {dst : DstSpec} {ap_update : Bool}
    (h  : mem (prog s.pc) = val (jnzInstr op0 op1 dst ap_update).toNat)
    (h₀ : vmComputeDst mem s dst = 0 →
      Returns PRIME mem ⟨vmBumpPc s op1.op1Imm, vmBumpAp s ap_update, s.fp⟩
        (fun k t => P (k + 1) t))
    (h₁ : vmComputeDst mem s dst ≠ 0 →
      Returns PRIME mem ⟨s.pc + (vmComputeOp1 mem s op0 op1).toInt, vmBumpAp s ap_update, s.fp⟩
        (fun k t => P (k + 1) t)) :
  Returns PRIME mem s P := by
  by_cases h₂ : vmComputeDst mem s dst = 0
  · apply returns_step _ (h₀ h₂)
    constructor
    use (jnzInstr op0 op1 dst ap_update).toInstruction
    rw [←Instr.toNat, ←Instr.VmNextState, vmNextState_jnz, if_pos h₂]
    refine ⟨h, rfl, rfl, rfl⟩
    rfl
  apply returns_step _ (h₁ h₂)
  constructor
  use (jnzInstr op0 op1 dst ap_update).toInstruction
  rw [←Instr.toNat, ←Instr.VmNextState, vmNextState_jnz, if_neg h₂]
  refine ⟨h, rfl, rfl, rfl⟩
  rfl

theorem advance_ap_returns {PRIME : Int} {op0 : Op0Spec} {res : ResSpec}
    (h  : mem (prog s.pc) = val (advanceApInstr op0 res).toNat)
    (h' : Returns PRIME mem ⟨vmBumpPc s res.toOp1.op1Imm, s.ap + (vmComputeRes mem s op0 res).toInt, s.fp⟩
        (fun k t => P (k + 1) t)) :
  Returns PRIME mem s P := by
  apply returns_step _ h'
  constructor
  use (advanceApInstr op0 res).toInstruction
  rw [←Instr.toNat, ←Instr.VmNextState, vm_next_state_advance_ap]
  refine ⟨h, rfl, rfl, rfl⟩
  rfl

theorem ret_returns {PRIME : Int}
    (h  : mem (prog s.pc) = val (retInstr.toNat))
    (h' : P 0 s) :
  Returns PRIME mem s P := by
  use 0, fun _ => s
  constructor
  · simp [IsReturningTrace, h]
  use 0, le_refl 0, h'

end VmNextState

open Mrel

/-- Represents that part of memory that the runner for a procedure should assign:
    a segment of execution memory and some range check values. -/
structure LocalAssignment (exec_start : Int) (rc_start : Int) :=
  (exec_num : Nat)
  (exec_vals : Int → Mrel)
  (rc_num : Nat)
  (rc_vals : Int → Int)

def Assign (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start) : Mrel → Mrel
| (exec k) => if exec_start ≤ k ∧ k < exec_start + loc.exec_num then loc.exec_vals k else mem (exec k)
| (rc k)   => if rc_start ≤ k ∧ k < rc_start + loc.rc_num then val (loc.rc_vals k) else mem (rc k)
| x        => mem x

set_option linter.unusedVariables false in
def ConcatAssignments {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
  (loc₀ : LocalAssignment exec_start₀ rc_start₀)
  (loc₁ : LocalAssignment exec_start₁ rc_start₁)
  (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
  (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num)
    : LocalAssignment exec_start₀ rc_start₀
  := ⟨
    loc₀.exec_num + loc₁.exec_num,
    fun k => if exec_start₀ + loc₀.exec_num  ≤ k ∧ k < exec_start₁ + loc₁.exec_num then loc₁.exec_vals k else loc₀.exec_vals k,
    loc₀.rc_num + loc₁.rc_num,
    fun k => if rc_start₀ + loc₀.rc_num  ≤ k ∧ k < rc_start₁ + loc₁.rc_num then loc₁.rc_vals k else loc₀.rc_vals k
  ⟩

theorem assign_prog (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start) (k : Int) :
  Assign mem loc (prog k) = mem (prog k) := by simp [Assign]

theorem assign_exec_of_lt (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start)
    (k : Int) (hk : k < exec_start) :
  Assign mem loc (exec k) = mem (exec k) := by
  simp only [Assign]
  rw [if_neg]
  rw [not_and_or, ←lt_iff_not_le]
  left
  exact hk

theorem assign_exec_pos (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start)
    (k : Int) (hk : exec_start ≤ k ∧ k < exec_start + loc.exec_num) :
  Assign mem loc (exec k) = loc.exec_vals k := by
  simp only [Assign]
  rw [if_pos]
  exact hk

theorem assign_rc_of_lt (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start)
   (k : Int) (hk : k < rc_start) :
  Assign mem loc (rc k) = mem (rc k) := by
  simp only [Assign]
  rw [if_neg]
  rw [not_and_or, ←lt_iff_not_le]
  left
  exact hk

theorem assign_rc_pos (mem : Mrel → Mrel) {exec_start : Int} {rc_start : Int}
    (loc : LocalAssignment exec_start rc_start)
   (k : Int) (hk : rc_start ≤ k ∧ k < rc_start + loc.rc_num) :
  Assign mem loc (rc k) = val (loc.rc_vals k) := by
  simp only [Assign]
  rw [if_pos]
  exact hk

theorem assign_concat {mem : Mrel → Mrel}
  {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
  {loc₀ : LocalAssignment exec_start₀ rc_start₀}
  {loc₁ : LocalAssignment exec_start₁ rc_start₁}
  (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
  (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num) :
  Assign mem (ConcatAssignments loc₀ loc₁ h_exec h_rc) = Assign (Assign mem loc₀) loc₁ := by
    funext x
    cases' x with k k k
    · simp only [assign_prog]
    · simp only [Assign, ConcatAssignments]
      by_cases h₀ : k < exec_start₀
      · rw [if_neg, if_neg, if_neg] <;> rw [not_and_or, not_le] <;> left
        exact h₀
        linarith
        exact h₀
      rw [not_lt] at h₀
      by_cases h₁ : k < exec_start₀ + loc₀.exec_num
      · rw [if_pos, if_neg, if_neg, if_pos]
        · exact ⟨h₀, h₁⟩
        · rw [not_and_or, not_le] ; left ; rw [h_exec] ; exact h₁
        · rw [not_and_or, not_le] ; left ; exact h₁
        use h₀
        apply lt_of_lt_of_le h₁
        apply add_le_add_left
        rw [Nat.cast_add]
        linarith
      rw [not_lt] at h₁
      by_cases h₂ : k < exec_start₀ + loc₀.exec_num + loc₁.exec_num
      · rw [if_pos, if_pos, if_pos]
        constructor
        · rwa [h_exec]
        · simp only [h_exec] ; exact h₂
        · simp only [h_exec] ; use h₁, h₂
        · rw [add_assoc] at h₂ ; use h₀, h₂
      rw [not_lt] at h₂
      rw [if_neg, if_neg, if_neg] <;> rw [not_and_or, not_le, not_lt]
      · right ; exact h₁
      · right ; simp only [h_exec] ; exact h₂
      · right ; rw [add_assoc] at h₂ ; exact h₂
    · simp only [Assign, ConcatAssignments]
      by_cases h₀ : k < rc_start₀
      · rw [if_neg, if_neg, if_neg] <;> rw [not_and_or, not_le] <;> left
        exact h₀
        linarith
        exact h₀
      rw [not_lt] at h₀
      by_cases h₁ : k < rc_start₀ + loc₀.rc_num
      · rw [if_pos, if_neg, if_neg, if_pos]
        · exact ⟨h₀, h₁⟩
        · rw [not_and_or, not_le] ; left ; rwa [h_rc]
        · rw [not_and_or, not_le] ; left ; exact h₁
        use h₀
        apply lt_of_lt_of_le h₁
        apply add_le_add_left
        rw [Nat.cast_add]
        linarith
      rw [not_lt] at h₁
      by_cases h₂ : k < rc_start₀ + loc₀.rc_num + loc₁.rc_num
      · rw [if_pos, if_pos, if_pos]
        · simp only [h_rc] ; use h₁, h₂
        · simp only [h_rc] ; use h₁, h₂
        · rw [add_assoc] at h₂ ; use h₀, h₂
      rw [not_lt] at h₂
      rw [if_neg, if_neg, if_neg] <;> rw [not_and_or, not_le, not_lt]
      · right ; exact h₁
      · right ; simp only [h_rc] ; exact h₂
      · right ; rw [add_assoc] at h₂ ; exact h₂
    simp only [Assign, ConcatAssignments]
    simp only [Assign, ConcatAssignments]

theorem assign_exec_concat_loc₀ (mem : Mrel → Mrel)
    {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
    (loc₀ : LocalAssignment exec_start₀ rc_start₀)
    (loc₁ : LocalAssignment exec_start₁ rc_start₁)
    (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
    (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num)
    (k : Int) (hk : exec_start₀ ≤ k ∧ k < exec_start₀ + loc₀.exec_num) :
  Assign mem (ConcatAssignments loc₀ loc₁ h_exec h_rc) (exec k) = loc₀.exec_vals k := by
  rw [assign_concat h_exec h_rc]
  rw [assign_exec_of_lt (Assign mem loc₀) loc₁ k]
  apply assign_exec_pos mem loc₀ k hk
  rw [h_exec]
  exact hk.2

theorem assign_rc_concat_loc₀ (mem : Mrel → Mrel)
    {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
    (loc₀ : LocalAssignment exec_start₀ rc_start₀)
    (loc₁ : LocalAssignment exec_start₁ rc_start₁)
    (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
    (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num)
    (k : Int) (hk : rc_start₀ ≤ k ∧ k < rc_start₀ + loc₀.rc_num) :
  Assign mem (ConcatAssignments loc₀ loc₁ h_exec h_rc) (rc k) = loc₀.rc_vals k := by
  rw [assign_concat h_exec h_rc]
  rw [assign_rc_of_lt (Assign mem loc₀) loc₁ k]
  apply assign_rc_pos mem loc₀ k hk
  rw [h_rc]
  exact hk.2

theorem concat_exec_num {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
    (loc₀ : LocalAssignment exec_start₀ rc_start₀)
    (loc₁ : LocalAssignment exec_start₁ rc_start₁)
    (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
    (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num) :
  (ConcatAssignments loc₀ loc₁ h_exec h_rc).exec_num = loc₀.exec_num + loc₁.exec_num := by
  simp only [ConcatAssignments]

theorem concat_rc_num {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
    (loc₀ : LocalAssignment exec_start₀ rc_start₀)
    (loc₁ : LocalAssignment exec_start₁ rc_start₁)
    (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
    (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num) :
  (ConcatAssignments loc₀ loc₁ h_exec h_rc).rc_num = loc₀.rc_num + loc₁.rc_num := by
  simp only [ConcatAssignments]

def VmIsRangeChecked (rc_bound : ℕ) (a : Int) : Prop := ∃ n : ℕ, n < rc_bound ∧ a = ↑n

def VmRangeChecked (rc_vals : Int → Int) (rc_start : Int) (k rc_bound : ℕ) : Prop :=
  ∀ i < k, VmIsRangeChecked rc_bound (rc_vals (rc_start + i))

theorem VmRangeChecked_concat
    {rc_bound : ℕ}
    {exec_start₀ rc_start₀ exec_start₁ rc_start₁ : Int}
    {loc₀ : LocalAssignment exec_start₀ rc_start₀}
    {loc₁ : LocalAssignment exec_start₁ rc_start₁ }
    (h_exec: exec_start₁ = exec_start₀ + loc₀.exec_num)
    (h_rc : rc_start₁ = rc_start₀ + loc₀.rc_num)
    (h_loc₀ : VmRangeChecked loc₀.rc_vals rc_start₀ loc₀.rc_num rc_bound)
    (h_loc₁ : VmRangeChecked loc₁.rc_vals rc_start₁ loc₁.rc_num rc_bound) :
  VmRangeChecked
    (ConcatAssignments loc₀ loc₁ h_exec h_rc).rc_vals
    rc_start₀
    (ConcatAssignments loc₀ loc₁ h_exec h_rc).rc_num
    rc_bound := by
  intros i hi
  simp only [ConcatAssignments]
  simp only [ConcatAssignments] at hi
  by_cases h : i < ↑loc₀.rc_num
  · rw [if_neg]
    apply h_loc₀ i h
    rw [not_and_or, not_le]
    left ; apply add_lt_add_left (Nat.cast_lt.mpr h)
  rw [not_lt] at h
  rw [if_pos]
  have h_i_lt : i - loc₀.rc_num < loc₁.rc_num := by
    apply Nat.sub_lt_right_of_lt_add h ; rw [add_comm] ; exact hi
  have h_loc₁_i := h_loc₁ (i - loc₀.rc_num) h_i_lt
  rw [Nat.cast_sub h] at h_loc₁_i ; ring_nf at h_loc₁_i
  simp only [h_rc] at h_loc₁_i ; ring_nf at h_loc₁_i
  exact h_loc₁_i
  constructor
  · apply Int.add_le_add_left (Nat.cast_le.mpr h)
  simp only [h_rc]
  rw [add_assoc]
  apply Int.add_lt_add_left (Nat.cast_lt.mpr hi)

theorem VmRangeChecked_rec
    {rc_start : Int}
    {rc_vals : Int → Int}
    {rc_num rc_bound : ℕ}
    (h_next: VmIsRangeChecked rc_bound (rc_vals (rc_start + rc_num)))
    (h_ind : VmRangeChecked rc_vals rc_start rc_num rc_bound) :
  VmRangeChecked rc_vals rc_start (rc_num.succ) rc_bound := by
  intros i h_i
  rw [Nat.lt_succ, le_iff_lt_or_eq] at h_i
  cases' h_i with h h
  · exact h_ind i h
  rw [h]
  exact h_next

theorem VmRangeChecked_zero {rc_start : Int} {rc_vals : Int → Int} {rc_bound : ℕ} :
  VmRangeChecked rc_vals rc_start 0 rc_bound := by
  intros i h_i
  exfalso ; apply Nat.not_lt_zero i ; apply h_i

/-
Tactics.
-/

/- Tactics.  -/
namespace Tactic

variable {F : Type _} [Field F]

namespace Interactive

macro (name := vm_arith_simps₁) "vm_arith_simps" : tactic => `(tactic|
  ( try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg,
    Nat.cast_zero, Nat.cast_one, Nat.cast_add,
    add_assoc, add_sub_assoc, add_zero, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc]
    try norm_num1
    try simp only [Int.cast_zero, Int.cast_one, Int.cast_neg,
    Nat.cast_zero, Nat.cast_one, Nat.cast_add,
    add_assoc, add_sub_assoc, add_zero, add_neg_cancel, neg_add_cancel,
    add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] ))

macro (name := vm_returns_simps₁) "vm_returns_simps" : tactic => `(tactic|
  ( try simp only [ResSpec.toOp1, vmComputeRes, vmComputeOp1,
      vmComputeOp0, Op1Spec.op1Imm, vmComputeDst, vmBumpPc, vmBumpAp,
      vmJumpPc, clip_checked', checkedIntNz_eq,
      -- TODO: unfold arithmetic symbols, or duplicate lemmas at that level? For now, unfold.
      Mrel.add_def, Mrel.mul_def, Mrel.neg_def, Mrel.sub_def, Mrel.zero_def,
      Mrel.one_def,
      Mrel.coe_def, Mrel.add, Mrel.mul,
      -- TODO: are these needed?
      Int.cast_zero, Int.cast_one, Int.cast_neg,
      Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc]
    try norm_num1
    try simp only [ResSpec.toOp1, vmComputeRes, vmComputeOp1,
      vmComputeOp0, Op1Spec.op1Imm, vmComputeDst, vmBumpPc, vmBumpAp,
      vmJumpPc, clip_checked', checkedIntNz_eq,
      -- TODO: unfold arithmetic symbols, or duplicate lemmas at that level? For now, unfold.
      Mrel.add_def, Mrel.mul_def, Mrel.neg_def, Mrel.sub_def, Mrel.zero_def,
      Mrel.one_def,
      Mrel.coe_def, Mrel.add, Mrel.mul,
      -- TODO: are these needed?
      Int.cast_zero, Int.cast_one, Int.cast_neg,
      Nat.cast_zero, Nat.cast_one,
      add_assoc, add_sub_assoc, add_zero, add_neg_cancel, neg_add_cancel,
      add_neg_eq_sub, sub_add_eq_add_neg_add, mul_assoc] ))

/- stepping through returns -/

macro (name := vm_step_assert_eq₁) "vm_step_assert_eq" h:term : tactic => `(tactic|
  ( apply assert_eq_returns
    apply $h
    vm_returns_simps ) )

macro (name := vm_step_assert_eq₂) "vm_step_assert_eq" h:term "," h':term : tactic => `(tactic|
  ( apply assert_eq_returns
    apply $h
    vm_returns_simps
    try rw [($h')] ) )

macro (name := vm_step_jump) "vm_step_jump" h:term : tactic => `(tactic|
  ( apply jump_returns
    apply $h
    rfl
    vm_returns_simps ))

macro (name := vm_step_jump_imm) "vm_step_jump_imm" h:term "," h':term : tactic => `(tactic|
  ( apply jump_returns
    apply $h
    vm_returns_simps
    try rw [assign_prog]
    try rw [($h')]
    try rw [Mrel.toInt]
    vm_arith_simps
    vm_returns_simps ))

macro (name := vm_step_jnz₁) "vm_step_jnz" h:term : tactic => `(tactic|
  ( apply jnz_returns
    apply $h
    vm_returns_simps
    swap
    vm_returns_simps
    swap ))

macro (name := vm_step_jnz₂) "vm_step_jnz" h:term "," h':term : tactic => `(tactic|
  ( apply jnz_returns
    apply $h
    vm_returns_simps
    try rw [($h')]
    swap
    vm_returns_simps
    try rw [($h')]
    swap ))

macro (name := vm_step_advance_ap) "vm_step_advance_ap" h:term "," h':term : tactic => `(tactic|
  ( apply advance_ap_returns
    rw [assign_prog]
    apply $h
    vm_returns_simps
    rw [assign_prog, ($h'), Mrel.toInt]
    norm_num1))

end Interactive

end Tactic
