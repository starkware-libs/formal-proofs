import Verification.Semantics.Cpu
import Verification.AirInfra.Airs.Casm.Common

-- Rust code also has a description
abbrev CasmAddress := FeltExpr

-- Note: the Rust code also has an optional name
structure CasmState where
  pc : CasmAddress
  ap : CasmAddress
  fp : CasmAddress
deriving Repr, Lean.ToJson, Lean.FromJson

instance : ToString CasmState where
  toString := fun casmState => s!"\{ pc := {casmState.pc}, ap := {casmState.ap}, fp := {casmState.fp} }"

/-
Semantics.
-/

abbrev CasmAddressVal := Felt

abbrev CasmStateVal := RegisterState Felt

instance : BEq CasmStateVal where beq x y := x.pc = y.pc && x.ap = y.ap && x.pc = y.pc

def CasmStateVal.toRegisterStateFelt252 (s : CasmStateVal) : RegisterState Felt252 where
  pc := s.pc.toFelt252
  ap := s.ap.toFelt252
  fp := s.fp.toFelt252

namespace CasmState
variable [Fact (Nat.Prime Stwo.P)]

def eval (varAssign : VarAssign) (s : CasmState) : CasmStateVal where
  pc := FeltExpr.eval varAssign s.pc
  ap := FeltExpr.eval varAssign s.ap
  fp := FeltExpr.eval varAssign s.fp

end CasmState

namespace CasmStateVal

def strongly_bounded (s : CasmStateVal) (num_steps : Nat) : Prop :=
  (∃ n : Nat, (n < 2^29 + num_steps) ∧ s.ap = ↑n) ∧ (∃ m : Nat, (m < 2^29 + num_steps) ∧ s.fp = ↑m)

-- Same as strongly_bounded but with a slightly stronger condition when the number of steps is zero.
def strongly_bounded₀ (s : CasmStateVal) (num_steps : Nat) : Prop :=
  (∃ n : Nat, (n < 2^29 - 1 + if num_steps = 0 then 0 else 1 + num_steps) ∧ s.ap = ↑n) ∧ (∃ m : Nat, (m < 2^29 + num_steps) ∧ s.fp = ↑m)

lemma strongly_bounded_of_strongly_bounded₀ {s : CasmStateVal} {num_steps : Nat} (h : strongly_bounded₀ s num_steps) :
    strongly_bounded s num_steps := by
  rcases h with ⟨⟨n, h_n_lt, h_n_eq⟩, h_fp⟩
  refine ⟨⟨n, ?_, h_n_eq⟩, h_fp⟩
  apply lt_of_lt_of_le h_n_lt
  by_cases h : num_steps = 0
  · simp [h]
  simp only [if_neg h, ←add_assoc, Nat.sub_add_cancel (show 1 ≤ 2 ^ 29 by norm_num), le_refl]

lemma strongly_bounded₀_of_strongly_bounded {s : CasmStateVal} {num_steps : Nat} (h_lt : 0 < num_steps) (h : strongly_bounded s num_steps) :
    strongly_bounded₀ s num_steps := by
  rcases h with ⟨⟨n, h_n_lt, h_n_eq⟩, h_fp⟩
  refine ⟨⟨n, ?_, h_n_eq⟩, h_fp⟩
  rw [if_neg (Nat.ne_of_lt h_lt).symm, ←add_assoc, Nat.sub_add_cancel (show 1 ≤ 2 ^ 29 by norm_num)]
  exact h_n_lt

lemma next_state_strongly_bound_of_apAdd1 [Fact (Nat.Prime Stwo.P)]
      {casmStateVal : CasmStateVal}
      { next_pc : Felt }
      { flag : Bool }
      { num_steps : Nat }
      ( cs_bound : casmStateVal.strongly_bounded num_steps ) :
    CasmStateVal.strongly_bounded
      { pc := next_pc, ap := casmStateVal.ap + flag.toFelt, fp := casmStateVal.fp }
      (num_steps + 1) := by
  rcases cs_bound with ⟨⟨ ap_nat, ap_bound, h_ap_nat⟩, ⟨ fp_nat, fp_bound, h_fp_nat⟩⟩
  --have h_eq : 2 ^ 29 + (num_steps + 1) = 2 ^ 29 + num_steps := by ring
  constructor
  · use ap_nat + flag.toFelt.val
    constructor
    · calc
        ap_nat + ZMod.val flag.toFelt ≤ ap_nat + 1 := by
          apply Nat.add_le_add_left flag.toFelt_le_one ap_nat
        _ < 2 ^ 29 + num_steps + 1 := by
          linarith[ap_bound]
        _ = 2 ^ 29 + (num_steps + 1) := by
          rfl
          --apply Nat.add_sub_cancel_right
      --apply add_lt_add_of_lt_of_le ap_bound flag.toFelt_le_one
    rw [h_ap_nat, Nat.cast_add, ←Bool.toFelt_val_coe]
  use fp_nat
  rw [h_fp_nat]
  constructor
  · calc
      fp_nat < 2 ^ 29 + num_steps := by
        exact fp_bound
      _ ≤ 2 ^ 29 + (num_steps + 1) := by
        linarith
  rfl
  --use (Nat.lt_add_right _ fp_bound)

end CasmStateVal
