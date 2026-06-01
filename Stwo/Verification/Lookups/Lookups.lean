import Verification.Lookups.combine

open scoped Classical

variable {F : Type _} [Field F] [Fintype F]

/-
  The main theorems for the lookups. There are two versions of the theorem here,
  one with non-collision constraints and one without. Using the non-collision constraints
  allows for a lower upper-bound on the size of the bad sets.
-/

/-

  Constraints on the Combined Values (values in F)
  ------------------------------------------------

  We consider all use and yield values to be provided as a single indexed list Fin t → F.
  The domain Fin t should be seen as a finite set of size t, without any ordering.
  When the use/yield values are tuples, this list is the list of the combined values
  (that is, after applying the combine function to map them to a value in F).
  The mapping from tuples to F is also covered by the theorems below, but most
  definitions (and proofs) can ignore this mapping and apply to the combined
  values.

  These combined use/yield values are given in the theorems below by the function f:

  f : Fin t → F  (all combined use and yield values, in arbitrary order)

  Multiple functions assign properties to these (combined) values, by assigning each index
  in Fin t to the value of that property for the corresponding use/yield value.

  Multiplicities:

  m : Fin t → F

  Each value is assigned a multiplicity. Use values must have a multiplicity of 1
  (this is enforced by the assumption h_use_mult_one). The multiplicities of the yield
  values are not explicitly constrained in any way (though the constraints will
  only hold if the sum of the multiplicities of each yield value is the negative
  of the number of use entries with that value).

  Constraint assignment:

  s : Fin t → Fin (n_s + 1)

  Each use/yield value is added to some constraint. The function s indicates
  which constraint it is added to. There are no assumptions on how the values
  are distributed among the constraints (except for the assumption that
  every value is in one and only one constraint, implicit in the definition of s).
  The number of constraints is n_s + 1 (implicitly providing the assumption that
  there is at least one constraint). There is no assumption, however, that there
  are no empty constraints (that is, constraints which are not assigned any values).

  Partitions:

  pr : Fin t → Fin (n_p + 1)

  Each use/yield value belongs to exactly one partition. The number of partitions
  is n_p + 1, implicitly providing the assumption that the number of partitions
  is not zero. There is no assumption, however, that there are no empty partitions
  (partitions which are not assigned any values).

  Random element assignment:

  z: Fin (n_p + 1) → F

  This is the random value assigned to the polynomial variables of the constraints,
  with one value per partition. The theorems below provide an upper bound on the
  size of the set of values z for which the conclusion of the theorem does not
  hold (this is the 'bad set' for z).

  Given all these definitions, the theorems assume that the cumulative constraints
  are satisfied. The two theorems have slightly different versions of these
  constraints, so details will be given below:

  h_cumulativeC: cumulativeC f m s pr z p (without inverse values)

  or

  h_cumulativeC_v : cumulativeC_v f m s v pr p z inv (with inverse values)

  (p i) is the cumulative value of the fractions in the constraints up to
  (not including) constraint i.

  An additional constraint,

  h_cyclic : p n_s.succ = p 0

  ensures that the total sum of all fractions in the constraints is zero.

  Both versions of the theorem also assume that the number of use values
  (values assigned a multiplicity of 1 by m) for each relation is smaller than
  the characteristic of the field:

  h_use_lt : ∀ k, (use_indxs m pr k).length < ringChar F

  Tuple Values
  ------------

  The following definitions define the mapping from the tuple values of each relation
  to the values in the field F which are defined by the function f.

  For each relation, all values are tuples of the same size:

  tuple_len_minus_one : Fin (n_p + 1) → Nat

  This is a function which assigns each relation a tuple length. This number is
  the tuple length minus one (as there are no tuples of length 0), so if tuple_len_minus_one k = l
  then the tuple length of relation k is l + 1.

  tuples : (k : Fin (n_p + 1)) → Fin (indxsK pr k).length → Fin (tuple_len_minus_one k + 1) → F

  These are the tuples which are the values for each relation (both use and yield). The first
  argument identifies the relation, while the second argument is a finite set whose size
  is equal to the number of indexes in Fin t which are assigned to relation k by the function pr.
  For each such index, a tuple of (tuple_len_minus_one k) + 1 values in F is defined.

  use_i : (k : Fin (n_p + 1)) → Finset (Fin (indxsK pr k).length)

  This function defines the subset of tuples which are use values. For every relation k
  this is a subset (Finset) of the range of indexes on which the tuples for that relation are defined.

  To map each tuple x to a value in F, the combine function ∑ i : Fin (n + 1), x i * (α k) ^ (i : Nat)
  is used. This function has a parameter α, chosen randomly and independently for each relation.

  α : Fin (n_p + 1) → F (one value per relation)

  In addition, since the tuples are defined on a different set of indexes than the full set of values
  (Fin t) to which the constraints are applied, we need a mapping from the indexes on
  which the tuples are defined to the indexes of the corresponding combined values
  in Fin t. This is provided by the following function:

  to_all_indxs : (k : Fin (n_p + 1)) → Fin (indxsK pr k).length → Fin t

  One needs to assume that the tuples, as defined for each relation, when combined
  by the factor α are indeed exactly those values defined for that relation by f. This
  is split across several assumptions in the theorem:

  h_surOn : the mapping is surjective on the subset of indexes in Fin t which are assigned to the relation.
  h_combine_eq : each tuple, combined into a value in F by the factor α, is equal to the corresponding value in f.
  h_use_mult_one : the use values (tuples), as defined by use_i, are all assigned a multiplicity of 1 by m.

  Under all these definitions and assumptions, the theorems show that as long as the choices of z and
  α do not fall into certain bad sets, the set of use values (tuples) is contained in the set of yield values
  (tuples) for each relation. The bad set for the value z is shared by all relations while the bad set for α
  depends on the tuple values of each relation separately.

  Two versions of the theorems are given below. In the first version only the cumulative constraints described
  above are used. In the second version, additional non-collision constraints are added. These constraints guarantee
  that the value of z for each relation does not collide with any of the (combined) values of that relation.
  This allows for a lower upper bound on the size of the bad set for z. More details are provided below.
-/

/-
  Version 1: no collision constraints

  This first version of the theorem applies to the following cumulative constraints (for every k in Fin n_s + 1):

  ∑ j ∈ (indxsK s k), (m j) * (∏ i ∈ (indxsK s k).erase(j),  (z (pr i) - f i)) = (∏ i ∈ (indxsK s k) (z (pr i) - f i)) * (p k.succ - p k)

  where (indxsK s k) are all the indexes in Fin t which are assigned by s to the k'th constraint.

  This, however, is not exactly the definition used in the theorem. Instead of working over the indexes
  in (indxsK s k), which are an arbitrary subset of Fin t, the definitions use Fin (indxsK s k).length,
  which has exactly the same number of indexes. In the definitions, we use a mapping of
  the indexes in Fin (indxsK s k).length to the indexes in (indxsK s k). We then sum over Fin (indxsK s k).length:

  ∑ j : Fin (indxsK s k).length, (m_k j) * (prodZ_exc f_k z_k j) = (prodZ f_k z_k) * (p k.succ - p k)

  where f_k, m_k, z_k are the functions f, m, z ∘ pr (which are defined on Fin t) composed after the mapping from
  the indexes in Fin (indxsK s k).length to the indexes in indxsK s k.

  prodZ_exc is (∏ i ∈ (Fin (indxsK s k).length).erase(j),  (z_k (pr i) - f_k i))
  prodZ is (∏ i ∈ (Fin Fin (indxsK s k).length), (z_k i - f_k i))

  The theorem shows that there are bad sets e (one for all relations) and b (one for each relation)
  such that if z ∉ e and α k ∉ b and the constraints hold then the use value (tuples) of relation k
  are a subset of the non-use values (tuples) of relation k.

  The size of the bad set for z has an upper bound of

  (Fintype.card F) ^ (n_p) * t + (Fintype.card F) ^ (n_p) * (max_pr_len pr)

  where n_p is the number of relations minus 1, t the total number of values (use and yield) in all
  relations and (max_pr_len pr) is the maximal number (plus one) of values (use and yield) in a single
  relation.

  Since there are (Fintype.card F) ^ (n_p + 1) ways to choose z, the probabilty of choosing a value
  in the bad set is:

  (t + max_pr_len pr) / (Fintype.card F)

  The second version of this theorem, below, removes the t from this bound.

  The size of the bad set for α for relation k is bound by

  (Finset.univ \ use_i k).card * (tuple_len_minus_one k)

  this is the number of yield values (i relation k) multiplied by the size of the tuples minus 1
  For a tuple size of 1, this will be 0.

  As the number of ways to choose α is Fintype.card F, the probability of choosing α in the bad set is

  (Finset.univ \ use_i k).card * (tuple_len_minus_one k) / Fintype.card F
-/

theorem tuple_inclusion {t n_s n_p : ℕ}
      (f : Fin t → F) -- All use and yield combined values
      (m : Fin t → F) -- Multiplicities (by h_use_mult_one below, must be 1 for use values)
      (s : Fin t → Fin (n_s + 1)) -- assignment of values to constraints
      (pr : Fin t → Fin (n_p + 1)) -- assignment of values to relations
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F) -- partial sum of fractions in constraints up to constraint i
      (h_cumulativeC : cumulativeC f m s pr z psum)
      (h_cyclic : psum n_s.succ = psum 0)
      -- For here, assumptions about the tuples of each partition
      {tuple_len_minus_one : Fin (n_p + 1) → Nat} -- The length of the tuple minus 1 for each partition.
      (tuples : (k : Fin (n_p + 1)) → Fin (indxsK pr k).length → Fin (tuple_len_minus_one k + 1) → F) -- The values (tuples) per partition
      (k : Fin (n_p + 1)) -- The partition
      {n_r : Nat} -- number of relations in this partition
      (use_i : Fin (n_r + 1) → Finset (Fin (indxsK pr k).length)) -- Subsets of the partition indexes are the use sets for the relations.
      (yield_i : Fin (n_r + 1) → Finset (Fin (indxsK pr k).length)) -- Subsets of the partition indexes are the yield sets for the relations.
      (h_use_i_lt : ∀ rel, (use_i rel).card < ringChar F)
      (h_disjoint : ∀ rel, ∀ i ∈ use_i rel ∪ yield_i rel, ∀ j ∉ use_i rel ∪ yield_i rel, tuples k i ≠ tuples k j)
      (to_all_indxs : (k : Fin (n_p + 1)) → Fin (indxsK pr k).length → Fin t) -- mapping of a partition into the set of all indexes
      (h_use_mult_one : ∀ rel i, i ∈ (use_i rel) → m (to_all_indxs k i) = 1)
      (h_surOn : ∀ k, to_indxs_surOn pr k (to_all_indxs k))
      (α : F)
      (h_combine_eq : ∀ i : Fin (indxsK pr k).length, combine α (tuples k i) = f (to_all_indxs k i)) :
    ∃ (e : Finset (Fin (n_p + 1) → F)),
      e.card ≤ (Fintype.card F) ^ (n_p) * t + (Fintype.card F) ^ (n_p) * (max_pr_len pr) ∧
      ∀ rel : Fin (n_r + 1),
        ∃ (b : Finset F),
          b.card ≤ (Finset.univ \ use_i rel).card * (tuple_len_minus_one k) ∧
          (z ∉ e ∧ α ∉ b →
            Finset.image (tuples k) (use_i rel) ⊆ Finset.image (tuples k) (yield_i rel)) := by
  use exceptionalSet f m pr, card_exceptionalSet_le f m pr
  intro rel
  use badSet (tuples k) (use_i rel) (yield_i rel)
  use card_badSet_le_yield (tuples k) (use_i rel) (yield_i rel) (h_disjoint rel)
  rintro ⟨h_z, h_α⟩
  apply tuple_inclusion_of_not_in_bad_sets f m s pr z psum h_z h_cumulativeC h_cyclic
    k (tuples k) (use_i rel) (yield_i rel) (h_use_i_lt rel) (to_all_indxs k) (h_surOn k) (h_use_mult_one rel)  α h_combine_eq h_α

/-
  Version 2: with non-collision constraints

  This version of the theorem adds non-collision constraints which check that z does not collide with
  the use and yield values. These constraints show that products ∏ (z i - f i) (on subsets of the indexes
  in a cumulative constraint) have an inverse. This ensures that the values of z do not collide with
  the values of f, but also provides the inverse values for these products, which are then used in
  the cumulative constraints.

  Since the indexes on which the products ∏ (z i - f i) are constrained to have an inverse are subsets
  of the indexes of each cumulative constraint, we need to define an additional partition function:

  v : Fin t → Fin (n_v + 1)

  and an assignment of inverse values

  inv : Fin (n_s + 1) → Fin (n_v + 1) → F

  The non-collision constraints are defined on the intersections between the partitions of v
  and of s (the partition into cumulative constraints). Therefore, there is an inverse value defined
  for every combination of values in Fin (n_s + 1) and Fin (n_v + 1). To avoid having to handle
  empty intersections between the partitions, we defined the non-collision constraints as

  ((indxsKv s v k (idxK s k i)).map fun j => (z ∘ pr) j - f j).prod * inv_k_i - 1 = 0

  where k (in Fin (n_s + 1)) defines the cumulative constraint and i selects one of the indexes
  to which the cumulative constraint applies. (indxsKv s v k (idxK s k i)) is then the subset
  of the indexes of cumulative constraint k which are assigned the same value by v as the i'th index
  in this constraint.

  The cumulative constraints are then modified to use the inverse values of the sub-products.
  The cumulative constraints are a sum of fractions (m j / ((z ∘ pr) j - f j)) converted
  into polynomial constraints by multiplying by the common denominator. Since we now have
  the inverse values (of products of these denominators), we can use those instead:

  ∑ j : Fin (indxsK s k).length,
      (funK s k m j) * (prodKv_exc s v f (z ∘ pr) k (idxK s k j)) * (inv k (v (idxK s k j))) = (p k.succ - p k)

  where prodKv_exc is a product over all indexes of cumulative constraint k which are assigned by v the same
  value as j, except for j itself (these are the indexes which belong to the same non-collision constraint as j)
  and (inv k (v (idxK s k j))) is the inverse value for the non-collision product which covers j. As in
  the previous theorem, the definitions do not use the original indexes in Fin t, but maps them from
  Fin (indxsK s k).length, which is of the same size as the subset of Fin t.

  As in the other version of this theorem, the theorem shows that there are bad sets e (one for all relations)
  and b (one for each relation) such that if z ∉ e and α k ∉ b and the constraints hold then
  the use value (tuples) of relation k are a subset of the non-use values (tuples) of relation k.

  The size of the bad set for z has an upper bound of

  (Fintype.card F) ^ (n_p) * (max_pr_len pr)

  where n_p is the number of relations minus 1, and (max_pr_len pr) is the maximal number (plus one)
  of values (use and yield) in a single relation.

  Since there are (Fintype.card F) ^ (n_p + 1) ways to choose z, the probabilty of choosing a value
  in the bad set is:

  (max_pr_len pr) / (Fintype.card F)

  This is better than the bound (t + max_pr_len pr) / (Fintype.card F) in the first version
  of the theorem.

  Exactly as in the first version of the theorem, the size of the bad set for α for relation k is bound by

  (Finset.univ \ use_i k).card * (tuple_len_minus_one k)

  this is the number of yield values (i relation k) multiplied by the size of the tuples minus 1
  For a tuple size of 1, this will be 0.

  As the number of ways to choose α is Fintype.card F, the probability of choosing α in the bad set is

  (Finset.univ \ use_i k).card * (tuple_len_minus_one k) / Fintype.card F
-/

theorem tuple_inclusion_inv {t n_s n_p n_v : ℕ}
      (f m : Fin t → F)
      (s : Fin t → Fin (n_s + 1))
      (v : Fin t → Fin (n_v + 1))
      (pr : Fin t → Fin (n_p + 1))
      (z : Fin (n_p + 1) → F)
      (psum : Nat → F)
      (inv : Fin (n_s + 1) → Fin (n_v + 1) → F)
      (h_cumulativeC_v : cumulativeC_v f m s v pr psum z inv)
      (h_cyclic : psum n_s.succ = psum 0)
      (h_nonCollision : nonCollisionC f s v pr z inv)
      -- For here, assumptions about the tuples of a specific relation
      {tuple_len_minus_one :  Fin (n_p + 1) → Nat} -- The length of the tuple - 1 for this relation.
      (tuples : (k : Fin (n_p + 1)) → Fin (indxsK pr k).length → Fin (tuple_len_minus_one k + 1) → F) -- The values of the relation (tuples)
      (k : Fin (n_p + 1)) -- The partition
      {n_r : Nat} -- number of relations in this partition
      (use_i : Fin (n_r + 1) → Finset (Fin (indxsK pr k).length)) -- Subsets of the partition indexes are the use sets for the relations.
      (yield_i : Fin (n_r + 1) → Finset (Fin (indxsK pr k).length)) -- Subsets of the partition indexes are the yield sets for the relations.
      (h_use_i_lt : ∀ rel, (use_i rel).card < ringChar F)
      (h_disjoint : ∀ rel, ∀ i ∈ use_i rel ∪ yield_i rel, ∀ j ∉ use_i rel ∪ yield_i rel, tuples k i ≠ tuples k j)
      (to_all_indxs : (k : Fin (n_p + 1)) →  Fin (indxsK pr k).length → Fin t) -- mapping into the set of all indexes
      (h_use_mult_one : ∀ rel i, i ∈ use_i rel → m (to_all_indxs k i) = 1)
      (h_surOn :  ∀ k, to_indxs_surOn pr k (to_all_indxs k))
      (α : F)
      (h_combine_eq : ∀ i, combine α (tuples k i) = f (to_all_indxs k i)) :
    ∃ (e : Finset (Fin (n_p + 1) → F)),
      e.card ≤ (Fintype.card F) ^ (n_p) * (max_pr_len pr) ∧
      ∀ rel : Fin (n_r + 1),
        ∃ (b : Finset F),
          b.card ≤ (Finset.univ \ use_i rel).card * (tuple_len_minus_one k) ∧
          (z ∉ e ∧ α ∉ b →
            Finset.image (tuples k) (use_i rel) ⊆ Finset.image (tuples k) (yield_i rel)) := by
  use zero_set_v f m pr, card_zero_set_v_le f m pr
  intro rel
  use badSet (tuples k) (use_i rel) (yield_i rel)
  use card_badSet_le_yield (tuples k) (use_i rel) (yield_i rel) (h_disjoint rel)
  rintro ⟨h_z, h_α⟩
  apply tuple_inclusion_of_not_in_bad_sets f m s pr z psum _ _ h_cyclic
    k (tuples k) (use_i rel) (yield_i rel) (h_use_i_lt rel) (to_all_indxs k) (h_surOn k) (h_use_mult_one rel)  α h_combine_eq h_α

  · apply not_mem_exceptionalSet_of_inv_and_not_zero_set_v f m s v pr z h_z
    intro k i
    apply prod_ne_zero_of_nonCollision_k_i f s v pr z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
  apply (cumulativeC_v_iff_cumulativeC f m s v pr psum z inv _).mp h_cumulativeC_v
  intro k i
  use prod_ne_zero_of_nonCollision_k_i f s v pr z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
  apply prod_inv_of_nonCollision_k_i f s v pr z k i (inv k (v (idxK s k i))) (h_nonCollision k i)
