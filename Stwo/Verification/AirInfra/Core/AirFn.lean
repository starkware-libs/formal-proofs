import Verification.AirInfra.Util
import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.AirFnRegistry
import Verification.AirInfra.Core.State

/-
The Air Builder.
-/

/-- Stores an array of constraints and the number of state and intermediate variables. -/
structure AirBuilder where
  state : State
  registry : AirFnRegistry
  constraints : Array FeltExpr
deriving Lean.ToJson, Lean.FromJson

instance : SizeOf AirBuilder :=
  ⟨fun a => a.state.len + a.registry.intermediateIndex + a.constraints.size⟩

namespace AirBuilder

def empty : AirBuilder where
  state := State.empty
  registry := AirFnRegistry.empty
  constraints := #[]

def IsPrefixOf (prefix_ab ab : AirBuilder) :=
  prefix_ab.state.len ≤ ab.state.len
  ∧ prefix_ab.registry.intermediateIndex ≤ ab.registry.intermediateIndex
  ∧ prefix_ab.constraints.isPrefixOf ab.constraints

theorem constraints_size_le_of_IsPrefixOf { prefix_ab ab : AirBuilder }
    (h : prefix_ab.IsPrefixOf ab) :
  prefix_ab.constraints.size ≤ ab.constraints.size := by
  unfold IsPrefixOf Array.isPrefixOf at h
  by_contra h_s
  simp_all only [↓reduceDIte, Bool.false_eq_true]

theorem constraint_getElem?_eq_of_IsPrefixOf {prefix_ab ab : AirBuilder} {i : Nat}
    (h : prefix_ab.IsPrefixOf ab)
    (h_i : i < prefix_ab.constraints.size) :
  ab.constraints[i]? = prefix_ab.constraints[i]? := by
  replace h := h.2.2
  simp only [←Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix, List.prefix_iff_getElem?] at h
  simp only [Array.getElem?_eq_getElem h_i, ←Array.getElem?_toList, ←Array.getElem_toList]
  apply h i

theorem constraint_getElem_eq_of_IsPrefixOf {prefix_ab ab : AirBuilder} {i : Nat}
    (h : prefix_ab.IsPrefixOf ab)
    (h_i : i < prefix_ab.constraints.size) :
  ∃ (h_i' : i < ab.constraints.size),
    ab.constraints[i] = prefix_ab.constraints[i] := by
  have h_i' := lt_of_lt_of_le h_i (constraints_size_le_of_IsPrefixOf h)
  use h_i'
  rw [←Option.some_inj, ←Array.getElem?_eq_getElem h_i, ←Array.getElem?_eq_getElem h_i']
  apply constraint_getElem?_eq_of_IsPrefixOf h h_i

def constrain (ab : AirBuilder) (expr : FeltExpr) : AirBuilder :=
  {ab with constraints := ab.constraints.push expr}

def assignVar (ab : AirBuilder) (expr var : FeltExpr) : AirBuilder :=
  ab.constrain (var - expr)

def assign (ab : AirBuilder) (expr : FeltExpr) : AirBuilder × FeltExpr :=
  let (newState, newVarNum) := ab.state.add
  let newVar := .var (.stateVar newVarNum)
  ({ab.assignVar expr newVar with state := newState}, newVar)

def letForConstraint (ab : AirBuilder) (expr : FeltExpr) : AirBuilder × FeltExpr :=
  let (newRegistry, newVarNum) := ab.registry.get_intermediate_index
  let newVar := .var (.intermediateVar newVarNum)
  ({ab.assignVar expr newVar with registry := newRegistry}, newVar)

def deduce (ab : AirBuilder) : AirBuilder × FeltExpr :=
  let (newState, newVarNum) := ab.state.add
  let newVar := .var (.stateVar newVarNum)
  ({ab with state := newState}, newVar)

def deduce252 (ab : AirBuilder) : AirBuilder × Felt252Expr :=
  let (newState, newVarStart) := ab.state.add_n FELT252_N_WORDS
  let newFelt252Var := fun (i : Fin FELT252_N_WORDS) => FeltExpr.var (.stateVar (newVarStart + i))
  ({ab with state := newState}, newFelt252Var)

def deduceN (ab : AirBuilder) (n: Nat) : AirBuilder × (Fin n → FeltExpr) :=
  let (newState, newVarStart) := ab.state.add_n n
  let newVar := fun (i : Fin n) => FeltExpr.var (.stateVar (newVarStart + i))
  ({ab with state := newState}, newVar)

-- `mem_verify` is in `Memory.lean`; the constraints are stored with the memory component,
-- not the air builder.

def display (ab : AirBuilder) : IO Unit := do
  let ⟨state, registry, constraints⟩ := ab
  IO.println s!"Number of state variables: {state.len}"
  IO.println s!"Number of intermediate variables: {registry.intermediateIndex}"
  IO.println "Constraints:"
  for h:i in [:constraints.size] do
    IO.println s!"  {i}: {constraints[i].toStr}"

/-
Semantics.
-/

section
variable [Fact (Nat.Prime Stwo.P)]

def SatisfiedBy (ab : AirBuilder) (varAssign : VarAssign) : Prop :=
   ∀ i, (h : i < ab.constraints.size) → ab.constraints[i].eval varAssign = 0

theorem prefix_SatisfiedBy {prefix_ab ab : AirBuilder}
    (h_prefix : prefix_ab.IsPrefixOf ab)
    (varAssign : VarAssign) :
  ab.SatisfiedBy varAssign → prefix_ab.SatisfiedBy varAssign := by
  intro h i hi
  rw [←(constraint_getElem_eq_of_IsPrefixOf h_prefix hi).2]
  apply h i

@[simp]
theorem constrain_SatisfiedBy (ab : AirBuilder) (expr : FeltExpr)
    (varAssign : VarAssign) :
  (ab.constrain expr).SatisfiedBy varAssign ↔
    ab.SatisfiedBy varAssign ∧ expr.eval varAssign = 0 := by
  simp only [SatisfiedBy, constrain, Array.size_push, Nat.lt_succ, Nat.le_iff_lt_or_eq]
  constructor
  . intro h
    constructor
    . intro i hi
      specialize h i (Or.inl hi)
      rwa [Array.getElem_push_lt (h := hi)] at h
    . specialize h _ (Or.inr rfl)
      rwa [Array.getElem_push_eq] at h
  . rintro ⟨h₁, h₂⟩ i (hi | hi)
    . rw [Array.getElem_push_lt (h := hi)]
      apply h₁ _ hi
    . cases hi
      rwa [Array.getElem_push_eq]

@[simp]
theorem assignVar_SatisfiedBy (ab : AirBuilder) (expr var : FeltExpr)
    (varAssign : VarAssign) :
  (ab.assignVar expr var).SatisfiedBy varAssign ↔
    ab.SatisfiedBy varAssign ∧ var.eval varAssign = expr.eval varAssign := by
  rw [assignVar, constrain_SatisfiedBy, FeltExpr.eval_sub, sub_eq_zero]

@[simp]
theorem assign_SatisfiedBy (ab : AirBuilder) (expr : FeltExpr)
    (varAssign : VarAssign) :
  (ab.assign expr).1.SatisfiedBy varAssign ↔
    ab.SatisfiedBy varAssign ∧ (ab.assign expr).2.eval varAssign =
      expr.eval varAssign := by
  rw [assign, ←assignVar_SatisfiedBy]; rfl

@[simp]
theorem letForConstraint_SatisfiedBy (ab : AirBuilder) (expr : FeltExpr)
    (varAssign : VarAssign) :
  (ab.letForConstraint expr).1.SatisfiedBy varAssign ↔
    ab.SatisfiedBy varAssign ∧
      (ab.letForConstraint expr).2.eval varAssign = expr.eval varAssign := by
  rw [letForConstraint, ←assignVar_SatisfiedBy]; rfl

@[simp]
theorem deduce_SatisfiedBy (ab : AirBuilder) (varAssign : VarAssign) :
  ab.deduce.1.SatisfiedBy varAssign ↔ ab.SatisfiedBy varAssign := by
  simp [deduce, SatisfiedBy]

@[simp]
theorem deduce252_SatisfiedBy (ab : AirBuilder) (varAssign : VarAssign) :
  ab.deduce252.1.SatisfiedBy varAssign ↔ ab.SatisfiedBy varAssign := by
  simp [deduce252, SatisfiedBy]

@[simp]
theorem deduceN_SatisfiedBy (n : Nat) (ab : AirBuilder) (varAssign : VarAssign) :
  (ab.deduceN n).1.SatisfiedBy varAssign ↔ ab.SatisfiedBy varAssign := by
  simp [deduceN, SatisfiedBy]

-- TODO (Jeremy): generalize to arbitrary start
-- Note: `α` is the data type corresponding to `FeltExpr`, while `β` is the `Felt` version.

def loop_step_spec (varAssign : VarAssign) (finish : Nat)
    (loopBody : Nat → AirBuilder × α → AirBuilder × α) (toFelt : α → β)
    (spec : Nat → β → β → Prop) : Prop :=
  ∀ i < finish, ∀ c a,
    (loopBody i (c, a)).1.SatisfiedBy varAssign →
      c.SatisfiedBy varAssign ∧
      spec i (toFelt a) (toFelt (loopBody i (c, a)).2)

theorem loop_SatisfiedBy {ab : AirBuilder}
    {varAssign : VarAssign}
    {loopBody : Nat → AirBuilder × α → AirBuilder × α}
    {finish : Nat}
    {init : α}
    (toFelt : α → β)
    (h : (forLoop 0 finish (ab, init) loopBody).1.SatisfiedBy varAssign)
    (spec : Nat → β → β → Prop)
    (h_step : loop_step_spec varAssign finish loopBody toFelt spec) :
    ab.SatisfiedBy varAssign ∧
    ∃ f : Nat → β,
      f 0 = toFelt init ∧
      (∀ i < finish, spec i (f i) (f (i + 1))) ∧
      f finish = toFelt (forLoop 0 finish (ab, init) loopBody).2 := by
  let loop i := forLoop 0 i (ab, init) loopBody
  suffices h' : ∀ i ≤ finish,
    (loop i).1.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      (∀ j < i, spec j (toFelt ((loop j).2)) (toFelt (loop (j + 1)).2))
  . specialize h' finish (le_refl _) h
    use h'.1, (fun i => (toFelt (loop i).2)), rfl, h'.2
  intro i ile
  induction i
  case zero =>
    intro h; use h; simp
  case succ i ih =>
    intro h
    simp [loop, forLoop_succ] at h
    have ilt : i < finish := by omega
    specialize h_step _ ilt _ _ h
    have ile' : i ≤ finish := by omega
    specialize ih ile' h_step.1
    use ih.1
    rw [Nat.forall_lt_succ]
    use ih.2
    dsimp [loop]
    rw [forLoop_succ (hle := Nat.zero_le _)]
    exact h_step.2

theorem constraint_loop_n_SatisfiedBy
      (ab : AirBuilder)
      (varAssign : VarAssign)
      (start n : Nat)
      (f : Nat → FeltExpr) :
    (forLoop start (start + n) ab (fun i ab => ab.constrain (f i))).SatisfiedBy varAssign ↔
      ab.SatisfiedBy varAssign ∧ ∀ i, i < n → (f (start + i)).eval varAssign = 0 := by
  unfold forLoop
  induction n with
  | zero => simp [forLoopAux] ; rfl
  | succ l h_ind =>
    rw [add_tsub_cancel_left]
    rw [forLoopAux_succ, AirBuilder.constrain_SatisfiedBy]
    rw [add_tsub_cancel_left] at h_ind
    rw [h_ind, and_assoc, Nat.forall_lt_succ]

theorem constraint_loop_SatisfiedBy
      (ab : AirBuilder)
      (varAssign : VarAssign)
      (start finish : Nat)
      (h_le : start ≤ finish)
      (f : Nat → FeltExpr) :
    (forLoop start finish ab (fun i ab => ab.constrain (f i))).SatisfiedBy varAssign ↔
      ab.SatisfiedBy varAssign ∧ ∀ i, start ≤ i → i < finish → (f i).eval varAssign = 0 := by
  rcases Nat.exists_eq_add_of_le h_le with ⟨n, h_n⟩
  simp only [h_n]
  have h (P : Nat → Prop) : (∀ i, (start ≤ i → i < start + n → P i)) ↔ ∀ i, i < n → P (start + i) := by
    constructor
    · intro h i h_i
      apply h (start + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left h_i _)
    intro h j h_ge h_lt
    rcases Nat.exists_eq_add_of_le h_ge with ⟨m, h_m⟩
    rw [h_m] at h_lt
    rw [h_m] ; apply h m (Nat.lt_of_add_lt_add_left h_lt)
  rw [h] ; apply constraint_loop_n_SatisfiedBy

end

end AirBuilder

/-
Lookup Data
-/

def LookupData (dataSize : Nat) := Array (Fin dataSize → FeltExpr)

instance (n : Nat) : Lean.ToJson (Fin n → FeltExpr) where
  toJson := fun x => Lean.toJson (Array.ofFn x)

instance (dataSize : Nat) : Lean.ToJson (LookupData dataSize) := by
  unfold LookupData; infer_instance

instance (n : Nat) : Lean.FromJson (Fin n → FeltExpr) where
  fromJson? := fun s =>
    let x : Except String (Array FeltExpr) := Lean.fromJson? s
    x.bind (fun a =>
      if h : n = a.size then
        .ok fun i => a[i]
      else
        .error "Json tuple: wrong size")

instance (dataSize : Nat) : Lean.FromJson (LookupData dataSize) := by
  unfold LookupData; infer_instance

instance (dataSize : Nat) : GetElem (LookupData dataSize) Nat (Fin dataSize → FeltExpr)
    (fun l i => i < Array.size l) := by
  unfold LookupData; infer_instance

instance (dataSize : Nat) : Membership (Fin dataSize → FeltExpr) (LookupData dataSize) := by
  unfold LookupData; infer_instance

namespace LookupData

def empty {dataSize : Nat} : LookupData dataSize := #[]

def add {dataSize : Nat} (lookupData : LookupData dataSize) (val : Fin dataSize → FeltExpr) :
    LookupData dataSize :=
  lookupData.push val

@[simp] theorem mem_add {dataSize : Nat} (v : Fin dataSize → FeltExpr)
    (lookupData : LookupData dataSize) (val : Fin dataSize → FeltExpr) :
    v ∈ lookupData.add val ↔ v ∈ lookupData ∨ v = val := by
  simp [LookupData.add]; rw [Array.mem_push]

@[simp] theorem mem_empty {dataSize : Nat} (v : Fin dataSize → FeltExpr) :
    v ∈ empty ↔ False := by
  rw [LookupData.empty, Array.mem_empty_iff]

def display {dataSize : Nat} (lookupData : LookupData dataSize) : IO Unit :=
  for h:i in [:lookupData.size] do
    let value := Array.ofFn lookupData[i]
    for h':j in [:value.size] do
      IO.print s!"{value[j]}"
      if j < dataSize then
          IO.print ", "
    IO.println ""

end LookupData

/-
Semantics.
-/

def LookupAssign (dataSize : Nat) := Set (Fin dataSize → Felt)

instance (dataSize : Nat) : Membership (Fin dataSize → Felt) (LookupAssign dataSize) := by
  unfold LookupAssign; infer_instance

namespace LookupData

variable [Fact (Nat.Prime Stwo.P)]

def eval {dataSize : Nat} (lookupData : Fin dataSize → FeltExpr) (varAssign : VarAssign) :
    Fin dataSize → Felt :=
  (fun j : Fin dataSize => (lookupData j).eval varAssign)

@[simp] theorem eval_append {m n : Nat} (lm : Fin m → FeltExpr) (ln : Fin n → FeltExpr)
      (varAssign : VarAssign) :
    eval (Fin.append lm ln) varAssign = Fin.append (eval lm varAssign) (eval ln varAssign) := by
  ext j
  simp [eval, Fin.append]
  refine Fin.addCases ?_ ?_ j <;> (intro i; simp [eval])

@[simp] theorem eval_cons {n : Nat} (l : Fin n → FeltExpr) (e : FeltExpr)
      (varAssign : VarAssign) :
    eval (Fin.cons e l) varAssign = Fin.cons (e.eval varAssign) (eval l varAssign) := by
  ext j
  simp [eval, Fin.cons]
  refine Fin.cases ?_ ?_ j <;> simp [eval]

@[simp] theorem eval_vecCons {n : Nat} (l : Fin n → FeltExpr) (e : FeltExpr)
      (varAssign : VarAssign) :
    eval (Matrix.vecCons e l) varAssign = Matrix.vecCons (e.eval varAssign) (eval l varAssign) := eval_cons l e varAssign

@[simp] theorem eval_vecEmpty :
    eval ![] varAssign = ![] := Matrix.empty_eq (eval ![] varAssign)

def SatisfiedBy {dataSize : Nat} (lookupData : LookupData dataSize)
    (varAssign : VarAssign) (lookupAssign : LookupAssign dataSize) : Prop :=
  ∀ i, (h : i < Array.size lookupData) →
    eval lookupData[i] varAssign ∈ lookupAssign

def add_SatisfiedBy {dataSize : Nat} (lookupData : LookupData dataSize)
    (val : Fin dataSize → FeltExpr)
    (varAssign : VarAssign)
    (lookupAssign : LookupAssign dataSize) :
  (lookupData.add val).SatisfiedBy varAssign lookupAssign ↔
    lookupData.SatisfiedBy varAssign lookupAssign ∧
      eval val varAssign ∈ lookupAssign := by
  simp only [SatisfiedBy, LookupData.add, Array.size_push]
  constructor
  . intro h
    constructor
    . intro i hi
      have hi' : i < Array.size lookupData + 1 := by omega
      simp at h
      convert h i hi' using 1
      ext j; rw [eval]
      congr; apply congr_fun; symm
      exact Array.getElem_push_lt hi
    . specialize h _ (Nat.lt_succ_self _)
      convert h using 1
      ext j; rw [eval]
      congr; apply congr_fun; symm
      exact Array.getElem_push_eq
  . intro h
    intro i hi
    rw [Nat.lt_succ_iff_lt_or_eq] at hi
    rcases hi with h' | rfl
    . convert h.1 i h' using 1
      ext j; rw [eval]; congr; apply congr_fun
      convert Array.getElem_push_lt h'
    . convert h.2 using 1
      ext j; rw [eval]; congr; apply congr_fun
      exact Array.getElem_push_eq

end LookupData
