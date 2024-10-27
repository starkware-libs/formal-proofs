import Verification.Semantics.Soundness.Prelude
import Verification.Libfuncs.Common

structure IntRange where (lower : Int) (upper: Int)

def InRange (n : Int) (range: IntRange) := range.lower ≤ n ∧ n < range.upper

inductive RemDivAlg where
  | KnownSmallLhs       (lhs_upper_sqrt : Nat)  : RemDivAlg
  | KnownSmallQuotient  (q_upper_bound : Int)   : RemDivAlg
  | KnownSmallRhs                               : RemDivAlg

/-
  /// Returns the algorithm to use for division and remainder of bounded integers.
  /// Fails if the div_rem of the ranges is not supported yet.
  ///
  /// Assumption: `lhs` is non-negative and `rhs` is positive.
  pub fn try_new(lhs: &Range, rhs: &Range) -> Option<Self> {
      let prime = Felt252::prime().to_bigint().unwrap();
      // Note that `rhs.lower` may be 0 - but since it is a non-zero type, it is guaranteed to be
      // at least 1.
      let q_max = (&lhs.upper - 1) / std::cmp::max(&rhs.lower, &BigInt::one());
      let u128_limit = BigInt::one().shl(128);
      // `q` is range checked in all algorithm variants, so `q_max` must be smaller than `2**128`.
      require(q_max < u128_limit)?;
      // `r` is range checked in all algorithm variants, so `rhs.upper` must be at most
      // `2**128 + 1`.
      require(rhs.upper <= &u128_limit + 1)?;
      if &rhs.upper * &u128_limit < prime {
          return Some(Self::KnownSmallRhs);
      }
      let q_upper_bound = q_max + 1;
      if &q_upper_bound * &u128_limit < prime {
          return Some(Self::KnownSmallQuotient { q_upper_bound });
      }
      let mut lhs_upper_sqrt = lhs.upper.sqrt();
      // Round lhs_upper_sqrt up.
      if lhs_upper_sqrt.pow(2) != lhs.upper {
          lhs_upper_sqrt += 1;
      }
      if &lhs_upper_sqrt * &u128_limit < prime {
          // Make sure `lhs_upper_sqrt < 2**128`, since the value bounded by root is range
          // checked.
          require(lhs_upper_sqrt < u128_limit)?;
          return Some(Self::KnownSmallLhs { lhs_upper_sqrt });
      }
      // No algorithm found.
      None
    }
-/

-- /// Assumption: `lhs` is non-negative and `rhs` is positive.
-- pub fn try_new(lhs: &Range, rhs: &Range) -> Option<Self> {
def try_new (lhs rhs : IntRange) : Option RemDivAlg :=
  -- let prime = Felt252::prime().to_bigint().unwrap();
  -- // Note that `rhs.lower` may be 0 - but since it is a non-zero type, it is guaranteed to be
  -- // at least 1.
  -- let q_max = (&lhs.upper - 1) / std::cmp::max(&rhs.lower, &BigInt::one());
  let q_max := (lhs.upper - 1) / (max rhs.lower 1)
  -- let u128_limit = BigInt::one().shl(128);
  -- // `q` is range checked in all algorithm variants, so `q_max` must be smaller than `2**128`.
  -- require(q_max < u128_limit)?;
  if ¬(q_max < u128Limit)
    then none
    else
      -- // `r` is range checked in all algorithm variants, so `rhs.upper` must be at most
      -- // `2**128 + 1`.
      -- require(rhs.upper <= &u128_limit + 1)?;
      if ¬(rhs.upper ≤ u128Limit + 1)
        then none
        else
          -- if &rhs.upper * &u128_limit < prime {
          --     return Some(Self::KnownSmallRhs);
          -- }
          if rhs.upper * u128Limit < PRIME
            then some RemDivAlg.KnownSmallRhs
            else
              -- let q_upper_bound = q_max + 1;
              let q_upper_bound := q_max + 1
              -- if &q_upper_bound * &u128_limit < prime {
              --     return Some(Self::KnownSmallQuotient { q_upper_bound });
              -- }
              if q_upper_bound * u128Limit < PRIME
                then some (RemDivAlg.KnownSmallQuotient q_upper_bound)
                else
                  -- let mut lhs_upper_sqrt = lhs.upper.sqrt();
                  -- // Round lhs_upper_sqrt up.
                  -- if lhs_upper_sqrt.pow(2) != lhs.upper {
                  --     lhs_upper_sqrt += 1;
                  -- }
                  let lhs_upper_sqrt :=
                    if lhs.upper.toNat.sqrt ^ 2 = lhs.upper.toNat
                      then lhs.upper.toNat.sqrt
                      else lhs.upper.toNat.sqrt + 1
                  -- if &lhs_upper_sqrt * &u128_limit < prime {
                  --     // Make sure `lhs_upper_sqrt < 2**128`, since the value bounded by root is range
                  --     // checked.
                  --     require(lhs_upper_sqrt < u128_limit)?;
                  --     return Some(Self::KnownSmallLhs { lhs_upper_sqrt });
                  -- }
                  if lhs_upper_sqrt * u128Limit < PRIME
                    then (if ¬(lhs_upper_sqrt < u128Limit)
                          then none
                          else some (RemDivAlg.KnownSmallLhs lhs_upper_sqrt))
                    -- // No algorithm found.
                    -- None
                    else none

lemma range_lower_lt_upper {r : IntRange} {a : Int} (h : InRange a r) : r.lower < r.upper :=
  lt_of_le_of_lt h.1 h.2
lemma le_upper_sub_one {r : IntRange} {a : Int} (h : InRange a r) : a ≤ r.upper - 1 := by
  rw [Int.le_sub_one_iff] ; apply h.2

lemma ediv_le_ediv_bounds {a b : Int} {lhs rhs: IntRange}
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_a : InRange a lhs)
    (h_b : InRange b rhs) :
    a / b ≤ (lhs.upper - 1) / (max rhs.lower 1) := by
  have h_b_pos := lt_of_lt_of_le h_rhs_pos h_b.1
  rw [max_eq_left (le_trans (by norm_num1) (Int.add_one_le_of_lt h_rhs_pos))]
  apply le_trans (Int.ediv_le_ediv h_b_pos (le_upper_sub_one h_a))
  rw [Int.le_ediv_iff_mul_le h_rhs_pos]
  apply le_trans _ (Int.ediv_mul_le _ (ne_of_gt h_b_pos))
  apply Int.mul_le_mul_of_nonneg_left h_b.1
  apply Int.ediv_nonneg _ (le_of_lt h_b_pos)
  rw [Int.le_sub_one_iff]
  apply lt_of_le_of_lt h_lhs_nonneg (range_lower_lt_upper h_a)

lemma bound_quotient {a b : Int} {lhs rhs: IntRange}
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_a : InRange a lhs)
    (h_b : InRange b rhs)
    (h_q : (lhs.upper - 1) / (max rhs.lower 1) < u128Limit) :
    a / b < ↑u128Limit := by
  apply lt_of_le_of_lt _ h_q
  apply ediv_le_ediv_bounds h_lhs_nonneg h_rhs_pos h_a h_b

lemma DivRemAlg_KnownSmallRhs_bounds {a b : Int} {lhs rhs: IntRange}
    -- /// Assumption: `lhs` is non-negative and `rhs` is positive.
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some RemDivAlg.KnownSmallRhs)
    (h_a : InRange a lhs)
    (h_b : InRange b rhs) :
    0 ≤ a ∧ 0 < b ∧ a / b < u128Limit ∧ b * u128Limit < PRIME := by
  have h_a_nonneg := le_trans h_lhs_nonneg h_a.1
  have h_b_pos := lt_of_lt_of_le h_rhs_pos h_b.1
  use h_a_nonneg
  use h_b_pos
  dsimp only [try_new] at h_alg
  by_cases h : (lhs.upper - 1) / (max rhs.lower 1) < u128Limit
  · use bound_quotient h_lhs_nonneg h_rhs_pos h_a h_b h
    simp only [eq_true h] at h_alg
    simp only [not_true, if_false] at h_alg
    by_cases h_rhs : rhs.upper ≤ u128Limit + 1
    · simp only [eq_true h_rhs] at h_alg
      simp only [not_true, if_false] at h_alg
      by_cases h_rhs_upper : rhs.upper * u128Limit < PRIME
      · apply lt_trans _ h_rhs_upper
        apply Int.mul_lt_mul_of_pos_right h_b.2 (by norm_num1)
      simp only [eq_false h_rhs_upper, if_false] at h_alg
      rw [ite_eq_iff] at h_alg
      cases' h_alg with h_alg_true h_alg_false
      · exfalso ; cases h_alg_true.2
      rw [ite_eq_iff] at h_alg_false
      cases' h_alg_false.2 with h_alg_true h_alg_false
      · rw [ite_eq_iff] at h_alg_true
        cases' h_alg_true.2 with h_alg_true h_alg_false
        · cases h_alg_true.2
        cases h_alg_false.2
      cases h_alg_false.2
    simp only [eq_false h_rhs] at h_alg
    simp only [not_false_iff, if_true] at h_alg
    contradiction
  simp only [eq_false h] at h_alg
  simp only [not_false_iff, if_true] at h_alg
  contradiction

lemma DivRemAlg_KnownSmallQuotient_bounds {a b : Int} {q_upper_bound : Int} {lhs rhs: IntRange}
     -- /// Assumption: `lhs` is non-negative and `rhs` is positive.
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some (RemDivAlg.KnownSmallQuotient q_upper_bound))
    (h_a : InRange a lhs)
    (h_b : InRange b rhs) :
  0 ≤ a ∧ 0 < b
    ∧ b ≤ u128Limit
    ∧ a / b < q_upper_bound
    ∧ q_upper_bound ≤ u128Limit
    ∧ q_upper_bound * u128Limit < PRIME := by

  have h_a_nonneg := le_trans h_lhs_nonneg h_a.1
  have h_b_pos := lt_of_lt_of_le h_rhs_pos h_b.1
  use h_a_nonneg
  use h_b_pos
  dsimp only [try_new] at h_alg
  by_cases h : (lhs.upper - 1) / (max rhs.lower 1) < u128Limit
  · simp only [eq_true h] at h_alg
    simp only [not_true, if_false] at h_alg
    by_cases h_rhs : rhs.upper ≤ u128Limit + 1
    · constructor
      · apply Int.le_of_sub_one_lt
        apply Int.sub_right_lt_of_lt_add
        apply lt_of_lt_of_le h_b.2 h_rhs
      simp only [eq_true h_rhs] at h_alg
      simp only [not_true, if_false] at h_alg
      by_cases h_rhs_upper : rhs.upper * u128Limit < PRIME
      · simp only [eq_true h_rhs_upper, if_true] at h_alg
        cases h_alg
      simp only [eq_false h_rhs_upper, if_false] at h_alg
      let q_max := (lhs.upper - 1) / (max rhs.lower 1)
      have hhh : (q_max + 1) ≤ u128Limit := by
        rwa [Int.add_one_le_iff]
      by_cases h_q_upper_bound : (q_max + 1) * u128Limit < PRIME
      · simp only [eq_true h_q_upper_bound, if_true] at h_alg
        injection h_alg with h_option
        injection h_option with h_q_upper_bound_eq
        rw [←h_q_upper_bound_eq]
        constructor
        · apply Int.lt_add_one_of_le
          apply ediv_le_ediv_bounds h_lhs_nonneg h_rhs_pos h_a h_b
        constructor
        · rwa [Int.add_one_le_iff]
        apply h_q_upper_bound
      simp only [eq_false h_q_upper_bound, if_false] at h_alg
      rw [ite_eq_iff] at h_alg
      cases' h_alg with h_alg_true h_alg_false
      · rw [ite_eq_iff] at h_alg_true
        cases' h_alg_true.2 with h_alg_true' h_alg_false'
        · cases h_alg_true'.2
        cases h_alg_false'.2
      cases h_alg_false.2
    simp only [eq_false h_rhs] at h_alg
    simp only [not_false_iff, if_true] at h_alg
    contradiction
  simp only [eq_false h] at h_alg
  simp only [not_false_iff, if_true] at h_alg
  contradiction

lemma DivRemAlg_KnownSmallLhs_bounds {a b : Int} {lhs_upper_sqrt : Nat} {lhs rhs: IntRange}
    -- /// Assumption: `lhs` is non-negative and `rhs` is positive.
    (h_lhs_nonneg : 0 ≤ lhs.lower)
    (h_rhs_pos : 0 < rhs.lower)
    (h_alg : try_new lhs rhs = some (RemDivAlg.KnownSmallLhs lhs_upper_sqrt))
    (h_a : InRange a lhs)
    (h_b : InRange b rhs) :
  0 ≤ a ∧ 0 < b ∧ b ≤ u128Limit
  ∧ a / b < u128Limit
  ∧ lhs_upper_sqrt * u128Limit < PRIME
  ∧ lhs_upper_sqrt < u128Limit
  ∧ a.toNat < lhs_upper_sqrt * lhs_upper_sqrt := by

  have h_a_nonneg := le_trans h_lhs_nonneg h_a.1
  have h_b_pos := lt_of_lt_of_le h_rhs_pos h_b.1
  use h_a_nonneg
  use h_b_pos
  dsimp only [try_new] at h_alg
  by_cases h : (lhs.upper - 1) / (max rhs.lower 1) < u128Limit
  · simp only [eq_true h] at h_alg
    simp only [not_true, if_false] at h_alg
    by_cases h_rhs : rhs.upper ≤ u128Limit + 1
    · constructor
      · apply Int.le_of_sub_one_lt
        apply Int.sub_right_lt_of_lt_add
        apply lt_of_lt_of_le h_b.2 h_rhs
      use bound_quotient h_lhs_nonneg h_rhs_pos h_a h_b h
      simp only [eq_true h_rhs] at h_alg
      simp only [not_true, if_false] at h_alg
      by_cases h_rhs_upper : rhs.upper * u128Limit < PRIME
      · simp only [eq_true h_rhs_upper, if_true] at h_alg
        cases h_alg
      simp only [eq_false h_rhs_upper, if_false] at h_alg
      let q_max := (lhs.upper - 1) / (max rhs.lower 1)
      by_cases h_q_upper_bound : (q_max + 1) * u128Limit < PRIME
      · simp only [eq_true h_q_upper_bound, if_true] at h_alg
        cases h_alg
      simp only [eq_false h_q_upper_bound, if_false] at h_alg
      let upper_sqrt :=
        if lhs.upper.toNat.sqrt ^ 2 = lhs.upper.toNat then lhs.upper.toNat.sqrt else lhs.upper.toNat.sqrt + 1
      by_cases h_upper_sqrt : upper_sqrt * u128Limit < PRIME
      · simp only [eq_true h_upper_sqrt, if_true] at h_alg
        by_cases h_upper_sqrt_lt : upper_sqrt < u128Limit
        · simp only [eq_true h_upper_sqrt_lt, not_true, if_false] at h_alg
          injection h_alg with h_option
          injection h_option with h_lhs_upper_sqrt_eq
          constructor
          · rw [←h_lhs_upper_sqrt_eq]
            apply h_upper_sqrt
          rw [←h_lhs_upper_sqrt_eq]
          use h_upper_sqrt_lt
          have h_toNat_upper : a.toNat < lhs.upper.toNat := by
            apply (Int.toNat_lt_toNat (lt_of_le_of_lt h_a_nonneg h_a.2)).mpr h_a.2
          apply lt_of_lt_of_le h_toNat_upper
          by_cases h_sqrt_eq : lhs.upper.toNat.sqrt ^ 2 = lhs.upper.toNat
          · simp only [eq_true h_sqrt_eq, if_true]
            rw [←Nat.pow_two _, h_sqrt_eq]
          simp only [eq_false h_sqrt_eq, if_false]
          apply le_of_lt
          apply Nat.lt_succ_sqrt _
        simp only [eq_false h_upper_sqrt_lt] at h_alg
        simp only [not_false_iff, if_true] at h_alg
        contradiction
      simp only [eq_false h_upper_sqrt, if_false] at h_alg
      contradiction
    simp only [eq_false h_rhs] at h_alg
    simp only [not_false_iff, if_true] at h_alg
    contradiction
  simp only [eq_false h] at h_alg
  simp only [not_false_iff, if_true] at h_alg
  contradiction
