import Verification.AirInfra.StwoProver
import Verification.AirInfra.Core.Expressions.Expr
import Verification.Lookups.Lookups

noncomputable section

-- The extension field QM31 used for the lookups.
def LookupF [Fact (Nat.Prime Stwo.P)] := GaloisField Stwo.P 4

instance [Fact (Nat.Prime Stwo.P)] : Field LookupF := by unfold LookupF ; infer_instance
instance [Fact (Nat.Prime Stwo.P)] : Fintype LookupF := by unfold LookupF ; apply Fintype.ofFinite
instance [Fact (Nat.Prime Stwo.P)] : DecidableEq LookupF := by
  exact Classical.typeDecidableEq (GaloisField Stwo.P 4)
instance [Fact (Nat.Prime Stwo.P)] : Algebra Felt LookupF := by unfold Felt LookupF ; infer_instance
instance [Fact (Nat.Prime Stwo.P)] : Coe Felt LookupF where coe := algebraMap Felt LookupF

def liftLF [Fact (Nat.Prime Stwo.P)] {n : Nat} (v : Fin n → Felt) : Fin n → LookupF :=
  fun i => (v i : LookupF)
instance [Fact (Nat.Prime Stwo.P)] {n : Nat} : Coe (Fin n → Felt) (Fin n → LookupF) where coe := liftLF
instance [Fact (Nat.Prime Stwo.P)] {n : Nat} : DecidableEq (Fin n → LookupF) := by infer_instance

lemma liftLF_ne_of_ne [Fact (Nat.Prime Stwo.P)] {n : Nat} (t1 t2 : Fin n → Felt) :
    t1 ≠ t2 → liftLF t1 ≠ liftLF t2 := by
  rw [not_imp_not]
  unfold liftLF
  intro h
  apply funext
  intro x
  apply (FaithfulSMul.algebraMap_injective (R := Felt) (A := LookupF))
  exact congrFun h x

lemma LookupF_ringChar_eq [Fact (Nat.Prime Stwo.P)] : ringChar LookupF = ringChar Felt := by
  unfold LookupF Felt
  exact (Algebra.ringChar_eq (ZMod Stwo.P) (GaloisField Stwo.P 4)).symm

instance [Fact (Nat.Prime Stwo.P)] : Fact (2 < ringChar LookupF) := by
  rw [fact_iff] ; rw [LookupF_ringChar_eq] ; unfold Felt ; rw [ZMod.ringChar_zmod_n] ; unfold Stwo.P ; norm_num1

inductive UseOrYield where
  | use   : UseOrYield
  | yield : UseOrYield

instance : DecidableEq UseOrYield := by
  intro a b
  cases a <;> cases b <;> simp <;>
  first | apply Decidable.isTrue ; trivial | apply Decidable.isFalse ; trivial

/-
  A lookup term represents a single lookup performed by a component.
  The same component can perform lookups for different relations,
  so the lookup term records also the relation of the lookup.
-/

/-

From core/air_body.rs:

pub enum AirBodyComponent {

    ....

    // Saves the information from the trace needed for the generation of the interaction trace,
    // and creates the constraints between the trace and the interaction trace, and the
    // constraints on the accumulated sum (the logup).
    LookupTerm {
        relation_name: String,
        felts: Vec<FeltExpr>,
        use_or_yield: UseOrYield,
    },
}

-/

-- n_r is the number of relations
-- Each relation has a fixed tuple length.
@[ext]
structure LookupTerm {n_r : ℕ} (tuple_len_minus_one : Fin (n_r + 1) → Nat) where
  rel : Fin (n_r + 1) -- The relation
  tuple : Fin ((tuple_len_minus_one rel) + 1) → FeltExpr
  useOrYield : UseOrYield

--instance {n_r : ℕ} {tl : Fin (n_r + 1) → Nat} : DecidableEq (LookupTerm tl) := by
--  sorry

@[ext]
structure LookupTermVal {n_r : ℕ} (tuple_len_minus_one : Fin (n_r + 1) → Nat) where
  rel : Fin (n_r + 1) -- The relation
  tuple: Fin ((tuple_len_minus_one rel) + 1) → Felt
  useOrYield : UseOrYield

namespace LookupTerm

def eval [Fact (Nat.Prime Stwo.P)] {n_r : ℕ} {tl : Fin (n_r + 1) → Nat}
    (varAssign : VarAssign)
    (l : LookupTerm tl) : LookupTermVal tl :=
  { rel := l.rel, tuple := (fun i => (l.tuple i).eval varAssign), useOrYield := l.useOrYield }

def SatisfiesSpec [Fact (Nat.Prime Stwo.P)] {n_r : ℕ} {tl : Fin (n_r + 1) → Nat}
      (t : LookupTerm tl)
      (k : Fin (n_r + 1))
      (h_k : t.rel = k)
      (spec : (Fin (tl k + 1) → Felt) → Prop)
      (varAssign : VarAssign) :=
    spec ((t.eval varAssign).tuple ∘ Fin.cast (by unfold LookupTerm.eval ; simp [h_k]))

end LookupTerm

-- The lookup constraints

-- # this section should be moved out of here.

-- Currently, these values, constraints, and mappings have to be added as an assumption. When we later provide
-- an explicit construction of the constraints, most of these assumptions could be proven based on that construction.

-- The values which define the lookup combined values, multipicities and partition
-- into constraints and relations.
structure LookupValues [Fact (Nat.Prime Stwo.P)] (t n_s n_p : ℕ) where
  f : Fin t → LookupF
  m : Fin t → LookupF
  s : Fin t → Fin (n_s + 1)
  pr : Fin t → Fin (n_p + 1)

-- The lookup constraints are satisfied.
structure LookupConstraints [Fact (Nat.Prime Stwo.P)] {t n_s n_r : ℕ} (values : LookupValues t n_s n_r) where
  z : Fin (n_r + 1) → LookupF
  psum : Nat → LookupF
  h_z : z ∉ exceptionalSet values.f values.m values.pr
  h_cumulativeC : cumulativeC values.f values.m values.s values.pr z psum
  h_cyclic : psum n_s.succ = psum 0

structure LookupPartition [Fact (Nat.Prime Stwo.P)] {t n_s n_p : ℕ}
    (values : LookupValues t n_s n_p)
    (p : Fin (n_p + 1))
    (tuple_len_minus_one : Nat) where
  tuples : Fin (indxsK values.pr p).length → Fin (tuple_len_minus_one + 1) → Felt -- The values in the partition (tuples)
  to_all_indxs : Fin (indxsK values.pr p).length → Fin t -- mapping into the set of all indexes
  h_surOn : to_indxs_surOn values.pr p to_all_indxs
  α : LookupF
  h_combine_eq : ∀ i, combine α (liftLF (tuples i)) = values.f (to_all_indxs i)

structure RelationTuples [Fact (Nat.Prime Stwo.P)] {t n_s n_p : ℕ}
    {values : LookupValues t n_s n_p}
    {p : Fin (n_p + 1)}
    {tuple_len_minus_one : Nat}
    (partition : LookupPartition values p tuple_len_minus_one) where
  use_i : Finset (Fin (indxsK values.pr p).length) -- a subset of the tuples are 'use' values
  yield_i : Finset (Fin (indxsK values.pr p).length) -- a subset of the tuples are 'yield' values
  h_use_lt : use_i.card < ringChar Felt
  h_use_mult_one : ∀ i, i ∈ use_i → values.m (partition.to_all_indxs i) = 1

def RelationsCoverPartitions [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
    {tl : Fin (n_p + 1) → Nat}
    {rp : Fin (n_r + 1) → Fin (n_p + 1)}
    {values : LookupValues t n_s n_p}
    {partitions : (p : Fin (n_p + 1)) → LookupPartition values p (tl p)}
    (tuples : (k : Fin (n_r + 1)) → RelationTuples (partitions (rp k))) :=
  ∀ p, ∀ (i : Fin (indxsK values.pr p).length),
    ∃ k, ∃ (h : p = rp k), (Fin.cast (by simp [h]) i) ∈ (tuples k).use_i ∪ (tuples k).yield_i

def NotInBadSet [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
    {tl : Fin (n_p + 1) → Nat}
    {values : LookupValues t n_s n_p}
    {p : Fin (n_p + 1)} -- partition number
    (k : Fin (n_r + 1)) -- relation number
    (chain_rel : Finset (Fin (n_r + 1)))
    {partition: LookupPartition values p (tl p)}
    (tuples : RelationTuples partition) :=
  if k ∈ chain_rel then partition.α ∉ chainBadSet (liftLF ∘ partition.tuples) tuples.use_i tuples.yield_i
    else partition.α ∉ badSet (liftLF ∘ partition.tuples)  tuples.use_i tuples.yield_i

-- A combined structure of all assumptions on the lookups.
structure LookupsSatisfied [Fact (Nat.Prime Stwo.P)] (t n_s n_p n_r : ℕ)
    (tl : Fin (n_p + 1) → Nat)
    (rp : Fin (n_r + 1) → Fin (n_p + 1))
    (chain_rel : Finset (Fin (n_r + 1))) where
  values : LookupValues t n_s n_p
  constraints : LookupConstraints values
  partitions : (p : Fin (n_p + 1)) → LookupPartition values p (tl p)
  tuples : (k : Fin (n_r + 1)) → RelationTuples (partitions (rp k))
  covering: RelationsCoverPartitions tuples
  h_inj: ∀ k ∈ chain_rel, (fun (i : {i // i ∈ (tuples k).use_i ∪ (tuples k).yield_i}) => (partitions (rp k)).to_all_indxs i).Injective
  h_chain: ∀ k ∈ chain_rel, ∀ i ∈ (tuples k).yield_i, values.m ((partitions (rp k)).to_all_indxs i) = -1
  h_bad : ∀ k, NotInBadSet k chain_rel (tuples k)

def use_tuples [Fact (Nat.Prime Stwo.P)] {t n_s n_p : ℕ}
    {p : Fin (n_p + 1)} -- partition number
    {tuple_len_minus_one : Nat}
    {v : LookupValues t n_s n_p}
    {partition : LookupPartition v p tuple_len_minus_one}
    (lookups : RelationTuples partition) :=
  Finset.image partition.tuples lookups.use_i

def yield_tuples [Fact (Nat.Prime Stwo.P)] {t n_s n_p : ℕ}
    {p : Fin (n_p + 1)}
    {tuple_len_minus_one : Nat}
    {v : LookupValues t n_s n_p}
    {partition : LookupPartition v p tuple_len_minus_one}
    (lookups : RelationTuples partition) :=
  Finset.image partition.tuples lookups.yield_i

lemma subset_iff_liftLF_subset [Fact (Nat.Prime Stwo.P)] {m n : Nat}
      (tuples : Fin m → Fin (n + 1) → Felt)
      (use_i yield_i : Finset (Fin m)) :
  Finset.image tuples use_i ⊆ Finset.image tuples yield_i ↔
    Finset.image (liftLF ∘ tuples) use_i ⊆ Finset.image (liftLF ∘ tuples) yield_i := by
  constructor
  · intro h x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have h_mem : tuples i ∈ Finset.image tuples yield_i :=
      h (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rcases Finset.mem_image.mp h_mem with ⟨j, hj, h_eq⟩
    have : tuples i = tuples j := h_eq.symm
    exact Finset.mem_image.mpr ⟨j, hj, by simp [this]⟩
  · intro h x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have h_mem : (liftLF (tuples i)) ∈ Finset.image (liftLF ∘ tuples) yield_i :=
      h (Finset.mem_image.mpr ⟨i, hi, by simp⟩)
    rcases Finset.mem_image.mp h_mem with ⟨j, hj, h_eq⟩
    have : tuples j = tuples i := by
      ext k
      have h_k : (tuples j k : LookupF) = (tuples i k : LookupF) := by
        simpa [liftLF] using congrArg (fun f : Fin (n + 1) → LookupF => f k) h_eq
      exact (FaithfulSMul.algebraMap_injective (R := Felt) (A := LookupF)) h_k
    exact Finset.mem_image.mpr ⟨j, hj, this⟩

lemma mem_yield_of_mem_use [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {rp : Fin (n_r + 1) → Fin (n_p + 1)}
      {chain_rel : Finset (Fin (n_r + 1))}
      (h_satisfied: LookupsSatisfied t n_s n_p n_r tl rp chain_rel) :
    ∀ k, k ∉ chain_rel → ∀ t ∈ use_tuples (h_satisfied.tuples k), ∃ y ∈ yield_tuples (h_satisfied.tuples k), t = y := by
  intro k h_k_rel t h_t_mem
  use t
  simp
  apply Finset.mem_of_subset _ h_t_mem
  unfold use_tuples yield_tuples
  let prt := h_satisfied.partitions (rp k)
  let lkups := h_satisfied.tuples k
  let v := h_satisfied.values
  let c := h_satisfied.constraints
  have h_α := h_satisfied.h_bad k
  rw [NotInBadSet, if_neg _] at h_α
  have h_use_lt : lkups.use_i.card < ringChar LookupF := by simp [LookupF_ringChar_eq, lkups.h_use_lt]
  convert tuple_inclusion_of_not_in_bad_sets v.f v.m v.s v.pr c.z c.psum c.h_z c.h_cumulativeC c.h_cyclic
    (rp k) (liftLF ∘ prt.tuples) lkups.use_i lkups.yield_i h_use_lt prt.to_all_indxs prt.h_surOn lkups.h_use_mult_one prt.α prt.h_combine_eq h_α
  exact subset_iff_liftLF_subset prt.tuples lkups.use_i lkups.yield_i
  simp [h_k_rel]

-- An assignment to a use term is a use tuple.
def UseAgrees [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
    {tl : Fin (n_p + 1) → Nat}
    {rp : Fin (n_r + 1) → Fin (n_p + 1)}
    (term : LookupTerm (tl ∘ rp))
    (varAssign : VarAssign) -- These are the rows of a component
    (values : LookupValues t n_s n_p)
    (partitions : (p : Fin (n_p + 1)) → LookupPartition values p (tl p))
    (lookups : (k : Fin (n_r + 1)) → RelationTuples (partitions (rp k))) : Prop :=
  term.useOrYield = .use → (term.eval varAssign).tuple ∈ use_tuples (lookups term.rel)

-- Soundness under the assumption that all yield tuples satisfy the spec.

lemma rel_lookup_sound [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {rp : Fin (n_r + 1) → Fin (n_p + 1)}
      {chain_rel : Finset (Fin (n_r + 1))}
      (term : LookupTerm (tl ∘ rp))
      (h_term_use : term.useOrYield = .use)
      (h_term_not_chain : term.rel ∉ chain_rel)
      (varAssign : VarAssign)
      (h_satisfied : LookupsSatisfied t n_s n_p n_r tl rp chain_rel)
      (h_agree : UseAgrees term varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (spec : (Fin ((tl ∘ rp) (term.rel) + 1) → Felt) → Prop)
      (h_spec : ∀ y ∈ yield_tuples (h_satisfied.tuples term.rel), spec y) :
    spec (term.eval varAssign).tuple := by
  rcases mem_yield_of_mem_use h_satisfied term.rel h_term_not_chain (term.eval varAssign).tuple (h_agree h_term_use) with
    ⟨y, h_y_mem, h_eq⟩
  simp [h_eq, h_spec y h_y_mem]

/-
  # Relation yields

  The following lemmas apply to relations for which the yields are added by yield
  terms of a component (and not, for example, as a constant table).
-/

/-
  The lookups for a relation whose yields are added by lookup terms
  agree with the assignments (rows) of the component(s) if applying the assignments
  to the lookup terms for the relation results in the lookups for those relations.
  Here we do not require equality, but only inclusion.

  This does not hold for relations whose yields are not the evaluation of lookup terms
  (such as constant table yields).
-/

def CompRelAgrees [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r n_c : ℕ}
    {tl : Fin (n_p + 1) → Nat}
    {rp : Fin (n_r + 1) → Fin (n_p + 1)}
    (k : Fin (n_r + 1))
    (terms : Fin (n_c + 1) → Array (LookupTerm (tl ∘ rp)))
    (varAssigns : Fin (n_c + 1) → Array VarAssign) -- These are the rows of a component
    (values : LookupValues t n_s n_p)
    (partitions : (p : Fin (n_p + 1)) → LookupPartition values p (tl p))
    (lookups : (k : Fin (n_r + 1)) → RelationTuples (partitions (rp k))) : Prop :=
  (∀ c : Fin (n_c + 1), ∀ l ∈ terms c, l.rel = k → l.useOrYield = .use →
    ∀ v ∈ varAssigns c, (l.eval v).tuple ∈ use_tuples (lookups l.rel))
  ∧
  -- Each yield tuple is the result of some variable assignment to a lookup term
  -- for the relation.
  ∀ t ∈ yield_tuples (lookups k),
    ∃ c : Fin (n_c + 1), ∃ l ∈ terms c, ∃ h : k = l.rel, ∃ v ∈ varAssigns c,
      l.useOrYield = .yield
      ∧ (l.eval v).tuple = t ∘ Fin.cast (by unfold LookupTerm.eval ; simp [h])

lemma LookupTerm_in_yield [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r n_c : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {rp : Fin (n_r + 1) → Fin (n_p + 1)}
      {chain_rel : Finset (Fin (n_r + 1))}
      (k : Fin (n_r + 1))
      (h_chain : k ∉ chain_rel)
      (terms : Fin (n_c + 1) → Array (LookupTerm (tl ∘ rp)))
      (varAssigns : Fin (n_c + 1) → Array VarAssign)
      (h_satisfied: LookupsSatisfied t n_s n_p n_r tl rp chain_rel)
      (h_agree : CompRelAgrees k terms varAssigns h_satisfied.values h_satisfied.partitions h_satisfied.tuples) :
    -- The condition term.useOrYield = .use is not necessary (as this holds trivially for the yield terms)
    ∀ c : Fin (n_c + 1), ∀ term ∈ terms c, (h₁ : term.rel = k) → term.useOrYield = .use →
      ∀ v_u ∈ varAssigns c, ∃ y_c, ∃ y_term ∈ terms y_c, ∃ h₂ : k = y_term.rel, ∃ v_y ∈ varAssigns y_c,
        y_term.useOrYield = .yield
        ∧ (y_term.eval v_y).tuple = (term.eval v_u).tuple ∘ Fin.cast (by unfold LookupTerm.eval ; simp [h₁, h₂])  := by
  intro c term h_mem h_k h_use v_u h_v_u_mem
  simp only [←h_k] at h_agree
  subst h_k
  let h_in_use := h_agree.1 c term h_mem rfl h_use v_u h_v_u_mem
  rcases mem_yield_of_mem_use h_satisfied _ h_chain _ h_in_use with ⟨y_tuple, h_y_tuple_mem, h_eq⟩
  convert h_agree.2 y_tuple h_y_tuple_mem

lemma tuple_cast_trans {n_p : ℕ} {tl : Fin (n_p + 1) → Nat}
      {k₁ k₂ k₃ : Fin (n_p + 1)}
      {t : Fin (tl k₁ + 1) → Felt}
      (h_k₁ : k₁ = k₂)
      (h_k₂ : k₂ = k₃) :
    t ∘ Fin.cast (show tl k₃ + 1 = tl k₁ + 1 by simp [h_k₁, h_k₂]) =
      (t ∘ Fin.cast (show tl k₂ + 1 = tl k₁ + 1 by simp [h_k₁])) ∘ Fin.cast (by simp [h_k₂]) :=  by
    subst h_k₂ h_k₁
    simp_all only [Fin.cast_refl, CompTriple.comp_eq]

/-
  Spec satisfied for all evaluation of all terms of relation k if it is satisfied
  for all evaluations of all yields (for that relation).
-/

lemma comp_rel_lookups_sound [Fact (Nat.Prime Stwo.P)] {t n_s n_p n_r n_c : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {rp : Fin (n_r + 1) → Fin (n_p + 1)}
      {chain_rel : Finset (Fin (n_r + 1))}
      (k : Fin (n_r + 1))
      (h_chain : k ∉ chain_rel)
      (terms : Fin (n_c + 1) → Array (LookupTerm (tl ∘ rp)))
      (varAssigns : Fin (n_c + 1) → Array VarAssign) -- yield component var assigns
      (h_satisfied : LookupsSatisfied t n_s n_p n_r tl rp chain_rel)
      (h_agree : CompRelAgrees k terms varAssigns h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (spec : (Fin ((tl ∘ rp) k + 1) → Felt) → Prop)
      (h_spec : ∀ c : Fin (n_c + 1), ∀ y_term ∈ terms c,
                  (h_k : y_term.rel = k) → y_term.useOrYield = .yield →
                    ∀ v ∈ varAssigns c, LookupTerm.SatisfiesSpec y_term k h_k spec v) :
    ∀ c : Fin (n_c + 1), ∀ term ∈ terms c, (h_k : term.rel = k) →
      ∀ v ∈ varAssigns c, LookupTerm.SatisfiesSpec term k h_k spec v := by
  intro c t h_t h_k
  cases h_y : t.useOrYield with
  | yield => apply h_spec c t h_t h_k h_y
  | use =>
    intro v h_v_mem
    rcases LookupTerm_in_yield k h_chain terms varAssigns h_satisfied h_agree c t h_t h_k h_y v h_v_mem with
      ⟨y_c, y_term, h_mem, h_rel_eq, v_y, h_v_y_mem, h_yield, h_eq⟩
    unfold LookupTerm.SatisfiesSpec
    have h_spec_y := h_spec y_c y_term h_mem h_rel_eq.symm h_yield v_y h_v_y_mem
    unfold LookupTerm.SatisfiesSpec at h_spec_y
    rw [h_eq, ←tuple_cast_trans] at h_spec_y
    exact h_spec_y
    unfold LookupTerm.eval ; simp [h_rel_eq, h_k]
    unfold LookupTerm.eval ; simp [h_rel_eq]

/-
  # disjoint relation tuples
-/

-- With one relation per partition, the disjoint tuple condition is trivial because there are
-- no indexes outside the use and yield indexes of a single relation.
lemma partition_tuples_disjoint_of_id [Fact (Nat.Prime Stwo.P)] {t n_s n_p : ℕ}
      {tl : Fin (n_p + 1) → Nat}
      {rp : Fin (n_p + 1) → Fin (n_p + 1)}
      {values : LookupValues t n_s n_p}
      {partitions : (p : Fin (n_p + 1)) → LookupPartition values p (tl p)}
      {tuples : (k : Fin (n_p + 1)) → RelationTuples (partitions (rp k))}
      (covering: RelationsCoverPartitions tuples)
      (rp_id : rp = id) :
    ∀ k, ∀ i ∈ (tuples k).use_i ∪ (tuples k).yield_i,
      ∀ j ∉ (tuples k).use_i ∪ (tuples k).yield_i, (partitions (rp k)).tuples i ≠ (partitions (rp k)).tuples j := by
  intro k i h_i j h_j
  exfalso
  apply h_j
  rcases covering (rp k) j with ⟨k', h_k'_eq, h_j_mem⟩
  simp [rp_id, Fin.val_inj] at h_k'_eq
  subst h_k'_eq
  apply h_j_mem

/-
  # Relations
-/

-- The relation index assigned to each relation.

def NUM_LOOKUP_REL_MINUS_ONE : Nat := 4
def RANGE_CHECK_REL_INDEX : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) := 0
def MEMORY_ADDR_TO_ID_REL_INDEX : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) := 1
def MEMORY_ID_TO_VALUE_REL_INDEX : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) := 2
def VERIFY_INSTR_REL_INDEX : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) := 3
def OPCODE_TRACE_REL_INDEX : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) := 4

/-
  # Old setup with one relation per partition.

-- The number of partitions
def NUM_PARTITIONS : Nat := NUM_LOOKUP_REL_MINUS_ONE -- old setup, one partition per relation.
-/

-- The tuple lengths for each relation, before mapping them into partition tuples.
def raw_rel_lengths : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) → Nat
  | 0 => 1 -- RANGE_CHECK_REL_INDEX
  | 1 => 1 -- MEMORY_ADDR_TO_ID_REL_INDEX
  | 2 => FELT252_N_WORDS -- MEMORY_ID_TO_VALUE_REL_INDEX
  | 3 => 18 -- VERIFY_INSTR_REL_INDEX
  | 4 => 2 -- OPCODE_TRACE_REL_INDEX

def TUPLE_SIZE : Nat := 29

/-
  # Old setup with one relation per partition.

def partition_lengths : Fin (NUM_PARTITIONS + 1) → Nat
  | 0 => TUPLE_SIZE -- RANGE_CHECK_REL_INDEX
  | 1 => TUPLE_SIZE -- MEMORY_ADDR_TO_ID_REL_INDEX
  | 2 => TUPLE_SIZE -- MEMORY_ID_TO_VALUE_REL_INDEX
  | 3 => TUPLE_SIZE -- VERIFY_INSTR_REL_INDEX
  | 4 => TUPLE_SIZE -- OPCODE_TRACE_REL_INDEX

def rel_partition : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) → Fin (NUM_PARTITIONS + 1) := id
-/
def NUM_PARTITIONS : Nat := 0 -- Single partition
def partition_lengths : Fin (NUM_PARTITIONS + 1) → Nat
  | 0 => TUPLE_SIZE

def rel_partition : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) → Fin (NUM_PARTITIONS + 1) := fun _ => 0

def rel_lengths : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) → Nat := partition_lengths ∘ rel_partition
def chain_rels : Finset (Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) := [OPCODE_TRACE_REL_INDEX].toFinset

lemma partition_len_eq {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)} :
    partition_lengths (rel_partition k) = TUPLE_SIZE := by rfl

lemma tuple_len_sum {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)} :
    partition_lengths (rel_partition k) + 1 =
      raw_rel_lengths k + 1 + 1 + (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) := by
  have h : raw_rel_lengths k + 1 ≤ partition_lengths (rel_partition k) := by
    rw [partition_len_eq]
    fin_cases k
    all_goals unfold raw_rel_lengths TUPLE_SIZE ; simp
  conv_rhs => rw [add_comm _ 1, add_assoc, ←Nat.add_sub_assoc h, Nat.add_sub_self_left]
  rw [add_comm]

lemma raw_len_lt_partition_len {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)} :
    raw_rel_lengths k < partition_lengths (rel_partition k) := by
  rw [partition_len_eq]
  fin_cases k
  all_goals unfold raw_rel_lengths TUPLE_SIZE ; simp

-- Embed a tuple is a larger tuple with an intial position and a final suffix
def p_tuple_embed {α : Type*}
      (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α)
    : (Fin (partition_lengths (rel_partition k) + 1) → α) :=
  (Fin.append (Fin.cons v0 tuple) suffix) ∘ Fin.cast (tuple_len_sum)

-- Back from the embedding tuple to the original tuple.
lemma p_tuple_embed_i_eq_tuple_i_sub_one
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α)
      {i : Fin (partition_lengths (rel_partition k) + 1) }
      (h_i_pos : i.val ≠ 0)
      (h_i_pred_lt : i.val - 1 < raw_rel_lengths k + 1) :
    p_tuple_embed k v0 tuple suffix i = tuple ⟨i.val - 1, h_i_pred_lt⟩ := by
  have h_lt : raw_rel_lengths k + 1 + 1 ≤ partition_lengths (rel_partition k) + 1 := by
    exact Nat.succ_le_succ (Nat.succ_le_of_lt raw_len_lt_partition_len)
  have h_i_lt : i.val < raw_rel_lengths k + 1 + 1 := by
    rw [←Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, Nat.succ_eq_add_one] at h_i_pred_lt
    apply lt_of_le_of_lt _ h_i_pred_lt
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h_i_pos)]
  unfold p_tuple_embed
  simp only [Function.comp_apply]
  have h_i_castLE := Fin.castLE_mk i.val _ _ h_i_lt h_lt
  rw [Fin.eta] at h_i_castLE
  conv_lhs => rw [←h_i_castLE, Fin.cast_castLE]
  simp only [Fin.append_left']
  have h_i : i.val = (i.val - 1) + 1 := by exact (Nat.succ_pred h_i_pos).symm
  have h_succ : Fin.mk i.val h_i_lt = (Fin.mk (i.val - 1) h_i_pred_lt).succ := by simp [←h_i]
  simp only [h_succ, Fin.cons_succ]

lemma p_tuple_embed_zero
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α) :
    p_tuple_embed k v0 tuple suffix 0 = v0 := by
  unfold p_tuple_embed ; simp [Fin.append_cons]

lemma p_tuple_embed_tuple_i
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {i : Fin (raw_rel_lengths k + 1)}
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α) :
    tuple i = p_tuple_embed k v0 tuple suffix
                (Fin.cast tuple_len_sum.symm (Fin.castAdd (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) i.succ)) := by
  rw [p_tuple_embed_i_eq_tuple_i_sub_one]
  congr
  simp

lemma p_tuple_embed_suffix_i
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {i : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1))}
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α) :
    suffix i = p_tuple_embed k v0 tuple suffix
                (Fin.cast tuple_len_sum.symm (Fin.natAdd (raw_rel_lengths k + 1 + 1) i)) := by
  simp [p_tuple_embed]

lemma p_tuple_embed_one
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      (v0 : α)
      (tuple : (Fin (raw_rel_lengths k + 1) → α))
      (suffix : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α) :
    p_tuple_embed k v0 tuple suffix 1 = tuple 0 := by
  rw [p_tuple_embed_i_eq_tuple_i_sub_one]
  congr
  all_goals
    simp [partition_lengths, rel_partition, TUPLE_SIZE]

lemma p_tuple_embed_inj
      {α : Type*}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {v0₁ v0₂ : α}
      {tuple₁ tuple₂ : (Fin (raw_rel_lengths k + 1) → α)}
      {suffix₁ suffix₂ : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) → α} :
    p_tuple_embed k v0₁ tuple₁ suffix₁ = p_tuple_embed k v0₂ tuple₂ suffix₂ →
      v0₁ = v0₂ ∧ tuple₁ = tuple₂ ∧ suffix₁ = suffix₂ := by
  intro h
  simp only [funext_iff] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [←p_tuple_embed_zero v0₁ tuple₁ suffix₁, ←p_tuple_embed_zero v0₂ tuple₂ suffix₂]
    exact h 0
  · rw [funext_iff]
    intro i
    rw [p_tuple_embed_tuple_i v0₁ tuple₁ suffix₁, p_tuple_embed_tuple_i v0₂ tuple₂ suffix₂]
    apply h
  rw [funext_iff]
  intro i
  rw [p_tuple_embed_suffix_i v0₁ tuple₁ suffix₁, p_tuple_embed_suffix_i v0₂ tuple₂ suffix₂]
  apply h

-- Convert a relation tuple into a partition tuple.
def p_tuple (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) (tuple : (Fin (raw_rel_lengths k + 1) → Felt))
    : (Fin (partition_lengths (rel_partition k) + 1) → Felt) :=
  p_tuple_embed k k tuple (fun (_ : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1))) => 0)

def p_tuple_expr (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) (tuple : (Fin (raw_rel_lengths k + 1) → FeltExpr))
    : (Fin (partition_lengths (rel_partition k) + 1) → FeltExpr) :=
  p_tuple_embed k (FeltExpr.const k) tuple (fun (_ : Fin (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1))) => (FeltExpr.const 0))

lemma p_tuple_zero
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → Felt)} :
    p_tuple k tuple 0 = k := by
  apply p_tuple_embed_zero

lemma p_tuple_expr_zero
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → FeltExpr)} :
    p_tuple_expr k tuple 0 = FeltExpr.const k := by
  apply p_tuple_embed_zero

lemma p_tuple_i_eq_tuple_i_sub_one
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → Felt)}
      {i : Fin (partition_lengths (rel_partition k) + 1) }
      (h_i_pos : i.val ≠ 0)
      (h_i_pred_lt : i.val - 1 < raw_rel_lengths k + 1) :
    p_tuple k tuple i = tuple ⟨i.val - 1, h_i_pred_lt⟩ := by
  apply p_tuple_embed_i_eq_tuple_i_sub_one _ _ _ h_i_pos h_i_pred_lt

lemma p_tuple_expr_i_eq_tuple_i_sub_one
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → FeltExpr)}
      {i : Fin (partition_lengths (rel_partition k) + 1) }
      (h_i_pos : i.val ≠ 0)
      (h_i_pred_lt : i.val - 1 < raw_rel_lengths k + 1) :
    p_tuple_expr k tuple i = tuple ⟨i.val - 1, h_i_pred_lt⟩ := by
  apply p_tuple_embed_i_eq_tuple_i_sub_one _ _ _ h_i_pos h_i_pred_lt

lemma p_tuple_one_eq_tuple_zero
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → Felt)} :
    p_tuple k tuple 1 = tuple 0 := by
  apply p_tuple_embed_one

lemma p_tuple_expr_one_eq_tuple_zero
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → FeltExpr)} :
    p_tuple_expr k tuple 1 = tuple 0 := by
  apply p_tuple_embed_one

lemma p_tuple_two_eq_tuple_one
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → Felt)} :
    p_tuple k tuple 2 = tuple 1 := by
  have h_lt : (2 : Fin (partition_lengths (rel_partition k) + 1)).val - 1 < raw_rel_lengths k + 1 := by
    fin_cases k
    all_goals simp [partition_lengths, rel_partition, TUPLE_SIZE, raw_rel_lengths]
  rw [p_tuple_i_eq_tuple_i_sub_one _ h_lt]
  · simp [partition_lengths, rel_partition, TUPLE_SIZE]
    fin_cases k
    all_goals simp
  simp [partition_lengths, rel_partition, TUPLE_SIZE]

lemma p_tuple_inj
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple₁ tuple₂ : (Fin (raw_rel_lengths k + 1) → Felt)} :
    p_tuple k tuple₁ = p_tuple k tuple₂ → tuple₁ = tuple₂ := by
  unfold p_tuple
  intro h
  exact (p_tuple_embed_inj h).2.1

lemma p_tuple_eval [Fact (Nat.Prime Stwo.P)]
      {varAssign : VarAssign}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : (Fin (raw_rel_lengths k + 1) → FeltExpr)} :
    (fun i => (p_tuple_expr k tuple i).eval varAssign) = p_tuple k (fun i => (tuple i).eval varAssign) := by
  unfold p_tuple_expr p_tuple p_tuple_embed
  apply funext
  intro i
  simp only [Function.comp_apply]
  by_cases h : i.val < raw_rel_lengths k + 1 + 1
  · have h_lt : raw_rel_lengths k + 1 + 1 ≤ partition_lengths (rel_partition k) + 1 := by
      exact Nat.succ_le_succ (Nat.succ_le_of_lt raw_len_lt_partition_len)
    have h_i_castLE := Fin.castLE_mk i.val _ _ h h_lt
    rw [Fin.eta] at h_i_castLE
    rw [←h_i_castLE, Fin.cast_castLE]
    simp only [Fin.append_left']
    by_cases h_0 : i.val = 0
    · simp [h_0]
    have h_i : i.val = (i.val - 1) + 1 := by exact (Nat.succ_pred h_0).symm
    have h_prev_lt : i.val - 1 < raw_rel_lengths k + 1 := by
      rw [←Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ←h_i] ; exact h
    have h_succ : Fin.mk i.val h = (Fin.mk (i.val - 1) h_prev_lt).succ := by simp [←h_i]
    simp only [h_succ, Fin.cons_succ]
  rw [Nat.not_lt] at h
  have h_rep_lt : i.val - (raw_rel_lengths k + 1 + 1) < (partition_lengths (rel_partition k) - (raw_rel_lengths k + 1)) := by
    rw [Nat.sub_lt_iff_lt_add h, ←add_assoc, Nat.sub_add_cancel]
    exact i.isLt
    rw [←Nat.succ_le_succ_iff]
    simp only [Nat.succ_eq_add_one]
    apply le_trans h (le_of_lt i.isLt)
  have h_i_natAdd : i = Fin.cast ?_ (Fin.natAdd (raw_rel_lengths k + 1 + 1) ⟨↑i - (raw_rel_lengths k + 1 + 1), h_rep_lt⟩) := by
    apply Fin.eq_of_val_eq
    rw [Fin.coe_cast, Fin.coe_natAdd] ; simp only
    rw [←Nat.add_sub_assoc h, Nat.add_sub_cancel_left]
  · rw [←Nat.succ_sub_succ]
    rw [←Nat.add_sub_assoc (Nat.succ_le_of_lt (Nat.succ_lt_succ raw_len_lt_partition_len)), Nat.add_sub_cancel_left]
  rw [h_i_natAdd]
  rw [Fin.cast_trans, Fin.cast_refl, id_eq]
  simp only [Fin.append_right]
  simp only [FeltExpr.eval_const]

-- Auxiliary lemmas
lemma rel_not_chain_rel (rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) : rel ≠ OPCODE_TRACE_REL_INDEX → rel ∉ chain_rels := by
    rw [chain_rels, List.mem_toFinset, List.mem_singleton, ←ne_eq] ; unfold OPCODE_TRACE_REL_INDEX ; simp
lemma range_check_not_chain_rel : RANGE_CHECK_REL_INDEX ∉ chain_rels := by
  apply rel_not_chain_rel ; unfold RANGE_CHECK_REL_INDEX OPCODE_TRACE_REL_INDEX ; simp
lemma memory_addr_not_chain_rel : MEMORY_ADDR_TO_ID_REL_INDEX ∉ chain_rels := by
  apply rel_not_chain_rel ; unfold MEMORY_ADDR_TO_ID_REL_INDEX OPCODE_TRACE_REL_INDEX ; simp
lemma memory_id_not_chain_rel : MEMORY_ID_TO_VALUE_REL_INDEX ∉ chain_rels := by
  apply rel_not_chain_rel ; unfold MEMORY_ID_TO_VALUE_REL_INDEX OPCODE_TRACE_REL_INDEX ; simp
lemma verify_instr_not_chain_rel : VERIFY_INSTR_REL_INDEX ∉ chain_rels := by
  apply rel_not_chain_rel ; unfold VERIFY_INSTR_REL_INDEX OPCODE_TRACE_REL_INDEX ; simp
lemma opcode_trace_is_chain_rel : OPCODE_TRACE_REL_INDEX ∈ chain_rels := by
  rw [chain_rels, List.mem_toFinset, List.mem_singleton]

-- Lookup terms added by a single component during the construction of the AIR.
def AirLookupTerms := Array (LookupTerm rel_lengths)

instance : Membership (LookupTerm rel_lengths) AirLookupTerms := by
  unfold AirLookupTerms; infer_instance

instance {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1) } :
    Membership (Fin (rel_lengths k) → Felt) (Finset (Fin (rel_lengths k) → Felt)) := by
  infer_instance

def RelLookupsSatisfied [Fact (Nat.Prime Stwo.P)] (t n_s : Nat) :=
  LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels

namespace AirLookupTerms

def empty : AirLookupTerms := Array.empty

lemma size_empty : empty.size = 0 := by unfold empty ; simp only [Array.size_eq_zero_iff] ; rfl

-- All use terms in a sequence of terms agree (for a given assignment) with the lookup tuples.
-- The sequence of terms is assumed to belong to the same component (but may be of different relations).
def UseAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (terms : AirLookupTerms)
    (varAssign : VarAssign) -- These are the rows of a component
    (values : LookupValues t n_s NUM_PARTITIONS)
    (partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p))
    (lookups : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))) : Prop :=
  ∀ t ∈ terms, t.useOrYield = .use → (t.eval varAssign).tuple ∈ use_tuples (lookups t.rel)

def add (terms : AirLookupTerms) (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (tuple : Fin (rel_lengths k + 1) → FeltExpr) (use_or_yield : UseOrYield) :
  AirLookupTerms :=
    terms.push { rel := k, tuple := tuple, useOrYield := use_or_yield}

-- Make the underlying type explicit, as otherwise reference by index, [i], fails.
protected def add' (terms : AirLookupTerms) (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
    (tuple : Fin (rel_lengths k + 1) → FeltExpr) (use_or_yield : UseOrYield) :
  Array (LookupTerm rel_lengths) :=
    terms.push { rel := k, tuple := tuple, useOrYield := use_or_yield}

@[simp]
lemma add'_eq_add : AirLookupTerms.add' = AirLookupTerms.add := by rfl

@[simp]
lemma terms_add_size_not_zero {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    0 < (terms.add k tuple use_or_yield).size := by
  simp [AirLookupTerms.add, Array.size_push]

lemma terms_add_size_pred_eq {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    (terms.add k tuple use_or_yield).size - 1 = terms.size := by
  simp [AirLookupTerms.add, Array.size_push]

lemma terms_add'_size_pred_eq {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    (terms.add' k tuple use_or_yield).size - 1 = terms.size := by
  simp [AirLookupTerms.add, Array.size_push]

lemma terms_add'_size_eq_succ {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    (terms.add' k tuple use_or_yield).size = terms.size + 1 := by
  simp [AirLookupTerms.add, Array.size_push]

lemma eq_add'_size_pred {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield}
      {i : Nat}
      (h1 : i < (terms.add' k tuple use_or_yield).size)
      (h2 : ¬(i < terms.size)) :
    i = (terms.add' k tuple use_or_yield).size - 1 := by
  rw [terms_add'_size_pred_eq]
  rw [terms_add'_size_eq_succ] at h1
  linarith [h1, h2]

lemma rel_add_eq_back {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    (terms.add k tuple use_or_yield).back.rel = k := by
  simp [Array.back_eq_getElem, AirLookupTerms.add, Array.getElem_push_eq]

lemma rel_add'_eq_last {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    (terms.add' k tuple use_or_yield)[(terms.add' k tuple use_or_yield).size - 1].rel = k := by
  simp [AirLookupTerms.add, Array.getElem_push_eq]

lemma rel_add_eq_last {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    let lt : Array (LookupTerm rel_lengths) := (terms.add k tuple use_or_yield)
    (lt[lt.size - 1]'(by simp [lt])).rel = k := by
  simp [AirLookupTerms.add, Array.getElem_push_eq]

lemma mem_add' {terms : AirLookupTerms} {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr} {use_or_yield : UseOrYield} :
    ∀ t ∈ (terms.add' k tuple use_or_yield),
      t ∈ terms ∨ t = { rel := k, tuple := tuple, useOrYield := use_or_yield } := by
  intro t h_t
  simp only [AirLookupTerms.add', Array.mem_push] at h_t
  exact h_t

lemma mem_add'_ne {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield}
      {t : LookupTerm rel_lengths}:
    t ∈ (terms.add' k tuple use_or_yield) →
      (t.rel ≠ k ∨ t.useOrYield ≠ use_or_yield) → t ∈ terms := by
  intro h_t_mem h_ne
  simp only [AirLookupTerms.add', Array.mem_push] at h_t_mem
  apply Or.resolve_right h_t_mem
  intro h_t_eq
  simp [h_t_eq] at h_ne

lemma mem_add'_ne_rel {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield}
      {t : LookupTerm rel_lengths}:
    t ∈ (terms.add' k tuple use_or_yield) → t.rel ≠ k → t ∈ terms := by
  intro h_t_mem h_ne
  simp only [AirLookupTerms.add', Array.mem_push] at h_t_mem
  apply Or.resolve_right h_t_mem
  intro h_t_eq
  simp [h_t_eq] at h_ne


lemma not_mem_add' {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield}
      {t : LookupTerm rel_lengths}:
    t ∉ terms ∧ (t.rel ≠ k ∨ t.useOrYield ≠ use_or_yield) → t ∉ (terms.add' k tuple use_or_yield) := by
  intro h_t h_nin
  apply h_t.1 (mem_add'_ne h_nin h_t.2)

def NoTermsOfRel (terms : Array (LookupTerm rel_lengths)) (k :  Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) :=
    ∀ i, (h : i < terms.size) → terms[i].rel ≠ k

def NoYieldTerms (terms : Array (LookupTerm rel_lengths)) :=
    ∀ i, (h : i < terms.size) → terms[i].useOrYield ≠ .yield

lemma empty_NoTermsOfRel (k :  Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) : NoTermsOfRel AirLookupTerms.empty k := by
  intro i h_i_lt
  rw [size_empty] at h_i_lt
  simp_all only [not_lt_zero']

lemma empty_NoYieldTerms : NoYieldTerms AirLookupTerms.empty := by
  intro i h_i_lt
  rw [size_empty] at h_i_lt
  simp_all only [not_lt_zero']

lemma add'_NoTermsOfRel {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield}
      (k' : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) :
    NoTermsOfRel (terms.add' k tuple use_or_yield) k' ↔
      k ≠ k' ∧ NoTermsOfRel terms k' := by
  constructor
  · simp [AirLookupTerms.add', NoTermsOfRel, Array.getElem_push]
    intro h_no
    constructor
    · have h := h_no (terms.size)
      simp at h ; exact h
    intro i h_i_lt
    have h := h_no i
    simp [h_i_lt] at h
    apply h
    omega
  intro h_no i h_i_lt
  by_cases h_lt : i < Array.size terms
  · simp [AirLookupTerms.add', Array.getElem_push]
    simp [h_lt]
    exact h_no.2 i h_lt
  simp only [eq_add'_size_pred h_i_lt h_lt, rel_add'_eq_last]
  exact h_no.1

lemma add'_NoYieldTerms {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield} :
    NoYieldTerms (terms.add' k tuple use_or_yield) ↔
      use_or_yield ≠ .yield ∧ NoYieldTerms terms := by
  constructor
  · simp [AirLookupTerms.add', NoYieldTerms, Array.getElem_push]
    intro h_no
    constructor
    · have h := h_no (terms.size)
      simp at h ; exact h
    intro i h_i_lt
    have h := h_no i
    simp [h_i_lt] at h
    apply h
    omega
  intro h_no i h_i_lt
  by_cases h_lt : i < Array.size terms
  · simp [AirLookupTerms.add', Array.getElem_push]
    simp [h_lt]
    exact h_no.2 i h_lt
  simp only [eq_add'_size_pred h_i_lt h_lt, terms_add'_size_pred_eq]
  simp only [AirLookupTerms.add', Array.getElem_push_eq]
  exact h_no.1

lemma not_mem_of_NoYieldTerms
      {terms : AirLookupTerms}
      {t : LookupTerm rel_lengths} :
    t.useOrYield = .yield → NoYieldTerms terms → t ∉ terms := by
  intro h_y_eq h_no_yield h_mem
  rw [Array.mem_iff_getElem] at h_mem
  rcases h_mem with ⟨i, h_i, h_eq⟩
  rw [←h_eq] at h_y_eq
  exact h_no_yield i h_i h_y_eq

lemma add_is_singleton_of_no_terms_of_rel {terms : AirLookupTerms}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths rel + 1) → FeltExpr}
      {use_or_yield : UseOrYield} :
    NoTermsOfRel terms rel →
      (terms.add rel tuple use_or_yield).filter (fun term => term.rel = rel ∧ term.useOrYield = use_or_yield) =
        #[{ rel := rel, tuple := tuple, useOrYield := use_or_yield}] := by
  intro h
  rw [AirLookupTerms.add, Array.filter_push] ; simp
  rw [Array.push_eq_append]
  rw [Array.filter_eq_empty_iff.mpr _]
  simp
  intro t h_t
  simp only [Bool.and_eq_true, decide_eq_true_eq, Classical.not_and_iff_not_or_not]
  left
  rw [Array.mem_iff_getElem] at h_t
  rcases h_t with ⟨i, h_i, h_eq⟩
  rw [←h_eq]
  apply h i h_i

lemma add_is_singleton_of_filter {terms : AirLookupTerms}
      {rel : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths rel + 1) → FeltExpr}
      {use_or_yield : UseOrYield} :
    terms.filter (fun term => term.rel = rel ∧ term.useOrYield = use_or_yield) = #[] →
      (terms.add rel tuple use_or_yield).filter (fun term => term.rel = rel ∧ term.useOrYield = use_or_yield) =
        #[{ rel := rel, tuple := tuple, useOrYield := use_or_yield}] := by
  intro h
  rw [AirLookupTerms.add, Array.filter_push] ; simp
  rw [Array.push_eq_append]
  simp [←Bool.decide_and, h]

lemma add_is_eq_of_ne {terms : AirLookupTerms}
      {rel rel' : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple' : Fin (rel_lengths rel' + 1) → FeltExpr}
      {use_or_yield use_or_yield' : UseOrYield} :
    rel ≠ rel' ∨ use_or_yield ≠ use_or_yield' →
      (terms.add rel' tuple' use_or_yield').filter (fun term => term.rel = rel ∧ term.useOrYield = use_or_yield) =
        terms.filter (fun term => term.rel = rel ∧ term.useOrYield = use_or_yield) := by
  intro h_ne
  rw [AirLookupTerms.add, Array.filter_push]
  simp
  intro h_rel
  cases h_ne
  case inl h => exfalso ; apply h h_rel.symm
  case inr h => exact h.symm

lemma yield_not_mem_NoYieldTerms {terms : AirLookupTerms} {t : LookupTerm rel_lengths} :
    t.useOrYield = .yield → NoYieldTerms terms → t ∉ terms := by
  intro h_yield h_no
  rw [Array.mem_def, List.mem_iff_getElem]
  by_contra h
  rcases h with ⟨i, h_i_lt, h_eq⟩
  rw [←Array.size_eq_length_toList] at h_i_lt
  apply h_no i h_i_lt
  rw [←Array.getElem_toList, h_eq, h_yield]

lemma UseAgree_add [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {lookups : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      {terms : AirLookupTerms}
      {varAssign : VarAssign} -- These are the rows of a component
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield} :
    UseAgree (terms.add k tuple use_or_yield) varAssign values partitions lookups ↔
      UseAgrees { rel := k, tuple := tuple, useOrYield := use_or_yield} varAssign values partitions lookups
      ∧ UseAgree terms varAssign values partitions lookups := by
  exact Array.forall_mem_push

-- The spec is satisfied by all assignments to all yield terms of the relation.
-- This refers to the terms and assignments for a single component.
def SatisfiedBy [Fact (Nat.Prime Stwo.P)]
      (terms : AirLookupTerms)
      (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (varAssigns : Array VarAssign)
      (spec : (Fin (rel_lengths k + 1) → Felt) → Prop) :=
     ∀ y_term ∈ terms, (h_k : y_term.rel = k) → y_term.useOrYield = .yield →
        ∀ v ∈ varAssigns, LookupTerm.SatisfiesSpec y_term k h_k spec v

-- Soundness for a relation whose yields are added by a component.
lemma rel_sound [Fact (Nat.Prime Stwo.P)] {t n_s n_c : ℕ}
      (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1))
      (h_chain : k ∉ chain_rels)
      (terms : Fin (n_c + 1) → AirLookupTerms)
      (varAssigns : Fin (n_c + 1) → Array VarAssign)
      (h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_agree : CompRelAgrees k terms varAssigns h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      (spec : (Fin (rel_lengths k + 1) → Felt) → Prop)
      (h_spec : ∀ c, (terms c).SatisfiedBy k (varAssigns c) spec) :
    ∀ c, ∀ term ∈ terms c, (h_k : term.rel = k) →
      ∀ v ∈ varAssigns c, LookupTerm.SatisfiesSpec term k h_k spec v := by
  apply comp_rel_lookups_sound k h_chain terms varAssigns h_satisfied h_agree spec h_spec

/-
  Relation Number Encoded in Tuple
-/

def RelInRelTuples (terms : Array (LookupTerm rel_lengths)) :=
    ∀ i, (h : i < terms.size) → terms[i].tuple 0 = FeltExpr.const terms[i].rel

lemma empty_RelInRelTuple : RelInRelTuples AirLookupTerms.empty := by
  intro i h_i_lt
  rw [size_empty] at h_i_lt
  simp_all only [not_lt_zero']

lemma add'_RelInRelTuple {terms : AirLookupTerms}
      {k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)}
      {tuple : Fin (raw_rel_lengths k + 1) → FeltExpr}
      {use_or_yield : UseOrYield} :
    RelInRelTuples (terms.add' k (p_tuple_expr k tuple) use_or_yield) ↔
      RelInRelTuples terms := by
  simp [AirLookupTerms.add', RelInRelTuples]
  constructor
  · intro h i h_i_lt
    replace h := h i (Nat.lt_succ_of_lt h_i_lt)
    rw [Array.getElem_push_lt h_i_lt] at h
    exact h
  intro h i h_i_lt
  by_cases h_lt : i < Array.size terms
  · replace h := h i h_lt
    rw [Array.getElem_push_lt h_lt]
    exact h
  have h_eq := Nat.eq_of_lt_succ_of_not_lt h_i_lt h_lt
  subst h_eq
  rw [Array.getElem_push_eq]
  simp only [p_tuple_expr_zero]

end AirLookupTerms
