import Verification.AirInfra.Core.Expressions.Felt252Expr

noncomputable section

/-
  All Component Evaluated Lookups
-/

inductive Opcode where
  | Generic : Opcode
  | CallRel : Opcode
  | CallAbsBaseFP : Opcode
  | CallAbsBaseAP : Opcode
  | Ret : Opcode
  | AssertEq : Opcode
  | AssertEqImm : Opcode
  | AssertEqDoubleDeref : Opcode
  | JumpImm : Opcode
  | JumpDoubleDeref : Opcode
  | JumpRel : Opcode
  | JumpAbs : Opcode
  | JnzNotTaken : Opcode
  | JnzTaken : Opcode
  | AddAp : Opcode
  | AddSmall : Opcode
  | Add252 : Opcode
  | MulSmall : Opcode
  | Mul252 : Opcode
  deriving Fintype, DecidableEq

def Opcode.univ : List Opcode := Finset.univ.toList

inductive Component where
  | Opcode (o : Opcode) : Component
  | RangeCheck : Component
  | MemoryAddrToId : Component
  | MemoryIdToValue : Component
  | VerifyInstr : Component
  deriving Fintype, DecidableEq

def Component.univ : List Component :=
  (Opcode.univ.map (fun o => .Opcode o)) ++
    (Finset.univ.toList.filter
      fun c => match c with
      | .Opcode _ => false
      | _ => true)

lemma Component.univ_complete : ∀ c : Component, c ∈ Component.univ := by
  intro c
  simp [Component.univ]
  cases c
  · case Opcode c =>
      left ; use c
      simp [Opcode.univ]
  all_goals
    right ; simp

lemma Component.univ_noDup : Component.univ.Nodup := by
  simp only [Component.univ, List.nodup_append]
  constructor
  · apply List.Nodup.map
    · intro o1 o2
      simp only [Opcode.injEq, imp_self]
    simp only  [Opcode.univ, Finset.nodup_toList]
  constructor
  · apply List.Nodup.filter
    simp only [Finset.nodup_toList]
  intro c1 h_c1 c2 h_c2 h_eq
  rw [List.mem_filter, ←h_eq] at h_c2
  rw [List.mem_map] at h_c1
  rcases h_c1 with ⟨o, h_o_mem, h_o_eq⟩
  simp [←h_o_eq] at h_c2

/-
  Input Data
-/

structure InputData where
  initialAp : Nat
  initialPc : Nat
  finalAp : Nat
  finalPc : Nat
  mStar : Felt252 → Option Felt252
