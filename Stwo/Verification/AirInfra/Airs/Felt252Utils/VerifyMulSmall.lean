import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck
import Verification.AirInfra.Core.Felt252IdMemory.ReadPositive
import Verification.AirInfra.Airs.ConvolutionUtils.Karatsuba
import Verification.AirInfra.StwoProver
import Verification.Semantics.Util

namespace VerifyMulSmall

def NUM_LIMBS := 4

abbrev shift := FeltExpr.const (1 <<< FELT252_BITS_PER_WORD)
abbrev double_shift := shift * shift
abbrev double_shift_inverse := FeltExpr.unary .inverse double_shift

abbrev shift_val := ((1 <<< FELT252_BITS_PER_WORD) : Felt)
abbrev shift_inverse_val := ((1 <<< (31 - FELT252_BITS_PER_WORD)) : Felt)
abbrev double_shift_val := shift_val * shift_val
abbrev double_shift_inverse_val := ((1 <<< (31 - (2 * FELT252_BITS_PER_WORD))) : Felt)

lemma shift_inverse_val_spec :
  shift_val * shift_inverse_val = 1 := by
  simp [shift_val, shift_val, shift_inverse_val]
  unfold FELT252_BITS_PER_WORD
  unfold Felt
  unfold Stwo.P
  decide

lemma double_shift_inverse_val_spec :
  double_shift_val * double_shift_inverse_val = 1 := by
  simp [double_shift_val, shift_val, double_shift_inverse_val]
  unfold FELT252_BITS_PER_WORD
  unfold Felt
  unfold Stwo.P
  decide

lemma double_shift_inverse_val_spec2 :
  double_shift_inverse_val * shift_val = shift_inverse_val := by
  simp [shift_val, double_shift_inverse_val]
  unfold FELT252_BITS_PER_WORD
  unfold Felt
  unfold Stwo.P
  decide

lemma double_shift_inverse_val_spec2b :
  shift_val * double_shift_inverse_val = shift_inverse_val := by
  rw[mul_comm]
  exact double_shift_inverse_val_spec2

lemma double_shift_spec2 :
  shift_inverse_val * double_shift_val = shift_val := by
  simp [shift_val, double_shift_val, shift_inverse_val]
  unfold FELT252_BITS_PER_WORD
  unfold Felt
  unfold Stwo.P
  decide

lemma h_triv1 : 0 < 2 * NUM_LIMBS - 1 := by
  simp [NUM_LIMBS]
lemma h_triv2 : 2 * NUM_LIMBS - 2 < 2 * NUM_LIMBS - 1 := by
  simp [NUM_LIMBS]
lemma h_triv3 : ZMod.val (512:Felt) = 512 := by rfl
lemma h_triv4 : ZMod.val double_shift_val = 262144 := by rfl
lemma h_triv5 : ZMod.val shift_val = 2^9 := by rfl
lemma h_triv6 : ZMod.val double_shift_val = 2^18 := by rfl

def first4expr (x : Felt252Expr) : Fin 4 → FeltExpr :=
  fun i => x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

def first8expr (x : Felt252Expr) : Fin 8 → FeltExpr :=
  fun i => x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

def first4felt (x : Felt252Words) : Fin 4 → Felt :=
  fun i => x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

def first8felt (x : Felt252Words) : Fin 8 → Felt :=
  fun i => x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

def first4val (x : Felt252Words) : Fin 4 → Nat :=
  fun i => (x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩).val

def first8val (x : Felt252Words) : Fin 8 → Nat :=
  fun i => (x ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩).val

def call [Fact (Nat.Prime Stwo.P)] (ab : AirBuilder) (lookupTerms : AirLookupTerms)
    (a b c : Felt252Expr) : AirBuilder × AirLookupTerms :=

    let a4 := first4expr a
    let b4 := first4expr b
    let c8 := first8expr c

    let convolution : Fin (2 * NUM_LIMBS - 1) → FeltExpr := simple_convolution NUM_LIMBS a4 b4

    let aux :=
      Fin.hIterate (P := fun _ => AirBuilder × AirLookupTerms × FeltExpr)
        (init := (ab, lookupTerms, FeltExpr.const 0))
        (n := 2 * NUM_LIMBS - 2)
        (f := fun i p1 =>
          let prev_ab := p1.1
          let prev_lt := p1.2.1
          let prev_limb_accumulator := p1.2.2

          have conditional_shift :=
            if i.val % 2 = 1 then
              shift
            else
              FeltExpr.const 1

          let i2 : Fin 8 := ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

          let mid_limb_accumulator := prev_limb_accumulator + (convolution i.castSucc - c8 i2) * conditional_shift

          let (next_ab, next_lt, next_limb_accumulator) :=
            if i.val % 2 = 1 then
              let (prev_ab2, carry) := prev_ab.deduce
              let prev_lt2 := prev_lt.add_rc 11 carry
              let prev_ab3 := prev_ab2.constrain (carry * double_shift - mid_limb_accumulator)
              (prev_ab3, prev_lt2, carry)
            else
              (prev_ab, prev_lt, mid_limb_accumulator)

          (next_ab, next_lt, next_limb_accumulator))

    let ab2 := aux.1
    let lt2 := aux.2.1
    let limb_accumulator := aux.2.2
    let final_limb_accumulator := limb_accumulator + a4 ⟨NUM_LIMBS - 1, by decide⟩ * b4 ⟨NUM_LIMBS - 1, by decide⟩
    let ab3 := ab2.constrain
      (final_limb_accumulator - c8 ⟨2 * NUM_LIMBS - 2, by decide⟩ - c8 ⟨2 * NUM_LIMBS - 1, by decide⟩ * shift)

    (ab3, lt2)

def spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
    let a4 := first4felt a
    let b4 := first4felt b
    let c8 := first8felt c
    let convolution := simple_convolution_val' NUM_LIMBS a4 b4

    let i0 : Fin (2 * NUM_LIMBS - 1) := ⟨0, h_triv1⟩

    ∃ prev_limb_accumulator : Fin (2 * NUM_LIMBS - 1) → Felt,
      prev_limb_accumulator i0 = 0 ∧
      (∀ i : Fin (2 * NUM_LIMBS - 2),
        let conditional_shift :=
            if i.val % 2 = 1 then
              shift_val
            else
              1

        let i2 : Fin 8 := ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩
        let mid_limb_accumulator := prev_limb_accumulator i.castSucc + (convolution i.castSucc - c8 i2) * conditional_shift

        if i.val % 2 = 1 then
          let carry := mid_limb_accumulator * double_shift_inverse_val
          IsRangeChecked 11 carry ∧
          prev_limb_accumulator i.succ = carry
        else
          prev_limb_accumulator i.succ = mid_limb_accumulator) ∧

      (let i_last : Fin (2 * NUM_LIMBS - 1) := ⟨(2 * NUM_LIMBS - 2), h_triv2⟩
      let final_limb_accumulator := prev_limb_accumulator i_last + a4 ⟨NUM_LIMBS - 1, by decide⟩ * b4 ⟨NUM_LIMBS - 1, by decide⟩
      (final_limb_accumulator - c8 ⟨2 * NUM_LIMBS - 2, by decide⟩ - c8 ⟨2 * NUM_LIMBS - 1, by decide⟩ * shift_val) = 0)

def spec (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] : Prop :=
    ∀ an bn cn : Felt252Nats,
      an.IsRangeChecked a → bn.IsRangeChecked b → cn.IsRangeChecked c →
      ReadPositive.has_num_bits (NUM_LIMBS * FELT252_BITS_PER_WORD) a →
      ReadPositive.has_num_bits (NUM_LIMBS * FELT252_BITS_PER_WORD) b →
      ReadPositive.has_num_bits (2 * NUM_LIMBS * FELT252_BITS_PER_WORD) c →
      an.eval * bn.eval = cn.eval

theorem mk_2 : (⟨2, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 3)) = (2 : Fin _) := rfl
theorem mk_3 : (⟨3, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 4)) = (3 : Fin _) := rfl
theorem mk_4 : (⟨4, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 5)) = (4 : Fin _) := rfl
theorem mk_5 : (⟨5, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 6)) = (5 : Fin _) := rfl
theorem mk_6 : (⟨6, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 7)) = (6 : Fin _) := rfl
theorem mk_7 : (⟨7, by apply Nat.lt_succ_of_le; apply Nat.le_add_left⟩ : Fin (n + 8)) = (7 : Fin _) := rfl

theorem add_val_argument {a b : Felt} (ha : a.val < 2^30) (hb : b.val < 2^18) (hdiff : (a-b).val < (2^29 + 2^11)) :
          b.val ≤ a.val := by
  by_contra hcontra
  push_neg at hcontra
  let mba := b-a
  have hmba : mba = b-a := by rfl
  have hmba2 : a-b = -mba := by rw [hmba]; ring
  have hmba_cast : (↑mba.val : Felt) = mba := by
    simp
    apply ZMod.cast_id

  have h1pre : mba ≠ 0 := by
    intro hb0
    rw[hb0] at hmba2
    rw[neg_zero] at hmba2
    have h' := congrArg (fun x => x + b) hmba2
    simp at h'
    rw [h'] at hcontra
    linarith
  have h1 : NeZero mba := ⟨h1pre⟩

  rw[hmba2] at hdiff

  have h2 : mba.val = Stwo.P - (-mba).val := by
    --rw [hmba]
    rw [ZMod.val_neg_of_ne_zero mba]
    rw[Nat.sub_sub_right]
    norm_num
    apply ZMod.val_le

  have h3: mba.val > Stwo.P - (2 ^ 29 + 2 ^ 11) := by
    rw[h2]
    apply Nat.sub_lt_sub_left
    unfold Stwo.P
    linarith
    exact hdiff

  rw[hmba] at h3

  have h4: ZMod.val (b - a) + ZMod.val a > Stwo.P - (2 ^ 29 + 2 ^ 11) + ZMod.val a := by
    linarith

  have h_p_nz : NeZero Stwo.P := by rw [neZero_iff] ; simp [Stwo.P]

  rw [← ZMod.val_add_of_lt] at h4
  simp at h4

  have h5 : 2 ^ 18 < 2 ^ 18 := by
    calc
      2 ^ 18 < Stwo.P - (2 ^ 29 + 2 ^ 11) := by
        unfold Stwo.P
        norm_num
      _ ≤ Stwo.P - (2 ^ 29 + 2 ^ 11) + ZMod.val a := by
        linarith
      _ < ZMod.val b := h4
      _ < 2 ^ 18 := hb
  linarith

  rw[ZMod.val_sub]

  calc
    ZMod.val b - ZMod.val a + ZMod.val a ≤ ZMod.val b + ZMod.val a := by
      omega
    _ < 2 ^ 18 + 2 ^ 18 := by
      omega
    _ < Stwo.P := by
      unfold Stwo.P
      norm_num

  omega

theorem add_val_argument2 {a1 a2 b1 b2: Felt} (ha1 : a1.val < 2^20 + 2 ^ 11) (ha2 : a2.val < 2^20)
          (hb1 : b1.val < 2^9) (hb2 : b2.val < 2^9) (hdiff : ((a1 + 512*a2)-(b1 + 512*b2)).val < 2^29 + 2^11):
          (b1 + 512*b2).val ≤ (a1 + 512*a2).val := by

  have h1 : a1.val ≤ (2^20 + 2 ^ 11 - 1) := by
    apply Nat.lt_succ_iff.mp ha1
  have h2 : a2.val ≤ (2^20 - 1) := by
    apply Nat.lt_succ_iff.mp ha2
  have h3 : b1.val ≤ (2^9 - 1) := by
    apply Nat.lt_succ_iff.mp hb1
  have h4 : b2.val ≤ (2^9 - 1) := by
    apply Nat.lt_succ_iff.mp hb2

  apply add_val_argument
  rw[ZMod.val_add_of_lt]
  rw[ZMod.val_mul_of_lt]

  calc
    a1.val + 512 * a2.val ≤ (2^20 + 2 ^ 11 - 1) + 512 * (2^20 - 1) := by
      linarith
    _ < 2^30 := by norm_num

  unfold Stwo.P
  rw[h_triv3]
  linarith

  rw[ZMod.val_mul_of_lt]
  unfold Stwo.P
  rw[h_triv3]
  linarith

  unfold Stwo.P
  rw[h_triv3]
  linarith

  rw[ZMod.val_add_of_lt]
  rw[ZMod.val_mul_of_lt]

  calc
    b1.val + 512 * b2.val ≤ (2^9 - 1) + 512 * (2^9 - 1) := by
      linarith
    _ < 2^18 := by norm_num

  unfold Stwo.P
  rw[h_triv3]
  linarith

  rw[ZMod.val_mul_of_lt]
  unfold Stwo.P
  rw[h_triv3]
  linarith

  unfold Stwo.P
  rw[h_triv3]
  linarith

  exact hdiff

theorem add_val_argument3 {a1 a2 b1 b2 c : Felt} (ha1 : a1.val < 2^20) (ha2 : a2.val < 2^20)
          (hb1 : b1.val < 2^9) (hb2 : b2.val < 2^9) (hc : c.val < 2^11)
          (hdiff : IsRangeChecked 11 ((c + ((a1 + 512*a2)-(b1 + 512*b2))) * double_shift_inverse_val)) :
          (b1 + 512*b2).val ≤ c.val + (a1 + 512*a2).val := by

  have ha1c : (a1 + c).val < 2^20 + 2^11 := by
    rw[ZMod.val_add_of_lt]
    linarith
    unfold Stwo.P
    omega

  unfold IsRangeChecked at hdiff
  rcases hdiff with ⟨n, ⟨h_n_lt, h_n_eq⟩⟩
  have hdiff' : ((a1 + c) + 512 * a2 - (b1 + 512*b2)).val < 2^29 + 2^11 := by
    calc
      ZMod.val ((a1 + c) + 512 * a2 - (b1 + 512 * b2)) = ZMod.val (((a1 + c) + 512 * a2 - (b1 + 512 * b2)) * double_shift_inverse_val*double_shift_val) := by
        rw [mul_assoc, mul_comm double_shift_inverse_val, double_shift_inverse_val_spec, mul_one]
      _ = ZMod.val (↑n * double_shift_val) := by
        rw [add_comm a1, add_assoc c, add_sub_assoc]
        rw [h_n_eq]
      _ < 2^29 + 2^11 := by
        have : ZMod.val (512 * (512:Felt)) = 262144 := by
          rfl
        rw[ZMod.val_mul_of_lt]
        rw[ZMod.val_cast_of_lt]
        unfold double_shift_val
        unfold shift_val
        unfold FELT252_BITS_PER_WORD
        simp
        rw[this]
        linarith
        unfold Stwo.P
        linarith
        rw[ZMod.val_cast_of_lt]
        unfold double_shift_val
        unfold shift_val
        unfold FELT252_BITS_PER_WORD
        simp
        rw[this]
        unfold Stwo.P
        linarith
        unfold Stwo.P
        linarith
  rw[← ZMod.val_add_of_lt, ← add_assoc c, add_comm c]
  exact add_val_argument2 ha1c ha2 hb1 hb2 hdiff'
  rw[ZMod.val_add_of_lt]
  rw[ZMod.val_mul_of_lt]
  rw[h_triv3]
  pick_goal 3
  rw[ZMod.val_mul_of_lt]
  all_goals
  · try rw[h_triv3]
    unfold Stwo.P
    omega

set_option maxHeartbeats 500000
theorem spec_of_spec_auto (a b c : Felt252Words) [Fact (Nat.Prime Stwo.P)] (hspec : spec_auto a b c) :
    spec a b c := by
  intro an bn cn han hbn hcn han_bits hbn_bits hcn_bits
  rcases hspec with ⟨prev_limb_accumulator, h_prev_limb_accumulator_0, hmain, hlast⟩
  rw [an.eval_eq_of_IsRangeChecked _ han, bn.eval_eq_of_IsRangeChecked _ hbn,
    cn.eval_eq_of_IsRangeChecked _ hcn]
  rw [←Nat.cast_mul]

  have h_a_trunk: (∑ i : Fin 4, ZMod.val ((first4felt a) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i))
      = (∑ i : Fin FELT252_N_WORDS, ZMod.val (a i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) := by
    unfold ReadPositive.has_num_bits at han_bits
    simp at han_bits
    unfold FELT252_BITS_PER_WORD at han_bits
    unfold NUM_LIMBS at han_bits
    simp at han_bits
    have : Nat.div_ceil 36 9 = 4 := by
      unfold Nat.div_ceil
      simp
    rw[this] at han_bits
    --
    have : Finset.range FELT252_N_WORDS = Finset.range 4 ∪ Finset.Ico 4 FELT252_N_WORDS := by
      ext x --
      simp [FELT252_N_WORDS]; omega
    rw [Finset.sum_fin_eq_sum_range] --
    rw [Finset.sum_fin_eq_sum_range, this, Finset.sum_union]; swap --
    . simp [Finset.disjoint_iff_ne, FELT252_N_WORDS]; omega
    trans; symm; apply add_zero
    apply congr_arg -- !
    symm; apply Finset.sum_eq_zero
    intro i; simp; intro h1 h2 _
    rw [←ZMod.val_eq_zero];
    have h3 := han_bits ⟨i,h2⟩ h1
    rw [h3]
    rfl

  have h_b_trunk: (∑ i : Fin 4, ZMod.val ((first4felt b) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i))
      = (∑ i : Fin FELT252_N_WORDS, ZMod.val (b i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) := by
    unfold ReadPositive.has_num_bits at hbn_bits
    simp at hbn_bits
    unfold FELT252_BITS_PER_WORD at hbn_bits
    unfold NUM_LIMBS at hbn_bits
    simp at hbn_bits
    have : Nat.div_ceil 36 9 = 4 := by
      unfold Nat.div_ceil
      simp
    rw[this] at hbn_bits
    --
    have : Finset.range FELT252_N_WORDS = Finset.range 4 ∪ Finset.Ico 4 FELT252_N_WORDS := by
      ext x
      simp [FELT252_N_WORDS]; omega
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range, this, Finset.sum_union]; swap
    . simp [Finset.disjoint_iff_ne, FELT252_N_WORDS]; omega
    trans; symm; apply add_zero
    apply congr_arg
    symm; apply Finset.sum_eq_zero
    intro i; simp; intro h1 h2 _
    rw [←ZMod.val_eq_zero];
    have h3 := hbn_bits ⟨i,h2⟩ h1
    rw [h3]
    rfl

  have h_c_trunk: (∑ i : Fin 8, ZMod.val ((first8felt c) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i))
      = (∑ i : Fin FELT252_N_WORDS, ZMod.val (c i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) := by
    unfold ReadPositive.has_num_bits at hcn_bits
    simp at hcn_bits
    unfold FELT252_BITS_PER_WORD at hcn_bits
    unfold NUM_LIMBS at hcn_bits
    simp at hcn_bits
    have : Nat.div_ceil 72 9 = 8 := by
      unfold Nat.div_ceil
      simp
    rw[this] at hcn_bits
    have : Finset.range FELT252_N_WORDS = Finset.range 8 ∪ Finset.Ico 8 FELT252_N_WORDS := by
      ext x
      simp [FELT252_N_WORDS]; omega
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range, this, Finset.sum_union]; swap --
    . simp [Finset.disjoint_iff_ne, FELT252_N_WORDS]; omega
    trans; symm; apply add_zero
    apply congr_arg
    symm; apply Finset.sum_eq_zero
    intro i; simp; intro h1 h2 _
    rw [←ZMod.val_eq_zero];
    have h3 := hcn_bits ⟨i,h2⟩ h1
    rw [h3]
    rfl

  rw [← h_a_trunk, ← h_b_trunk, ← h_c_trunk]

  have h_a_poly: (∑ i : Fin 4, ZMod.val ((first4felt a) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = eval_poly (2^(FELT252_BITS_PER_WORD)) (first4val a) := by
    unfold eval_poly
    simp [Fin.sum_univ_four]
    unfold first4val
    unfold first4felt
    simp[mk_2, mk_3]
    unfold FELT252_BITS_PER_WORD
    simp

  have h_b_poly: (∑ i : Fin 4, ZMod.val ((first4felt b) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = eval_poly (2^(FELT252_BITS_PER_WORD)) (first4val b) := by
    unfold eval_poly
    simp [Fin.sum_univ_four]
    unfold first4val
    unfold first4felt
    simp[mk_2, mk_3]
    unfold FELT252_BITS_PER_WORD
    simp

  have h_c_poly: (∑ i : Fin 8, ZMod.val ((first8felt c) i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = eval_poly (2^(FELT252_BITS_PER_WORD)) (first8val c) := by
    unfold eval_poly
    simp [Fin.sum_univ_eight]
    unfold first8val
    unfold first8felt
    simp[mk_2, mk_3, mk_4, mk_5, mk_6, mk_7]
    unfold FELT252_BITS_PER_WORD
    simp

  let convolution := simple_convolution_val' NUM_LIMBS (first4felt a) (first4felt b)
  have h_convolution_def : convolution = simple_convolution_val' NUM_LIMBS (first4felt a) (first4felt b) := by
    rfl
  let convolution_val := simple_convolution_val 4 (first4val a) (first4val b) -- NUM_LIMBS
  have h_convolution_val_def : convolution_val = simple_convolution_val 4 (first4val a) (first4val b) := by
    rfl

  have h_convolution_poly: (∑ i : Fin 7, ZMod.val (convolution i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = eval_poly (2^(FELT252_BITS_PER_WORD)) convolution := by
    unfold eval_poly
    simp
    unfold NUM_LIMBS
    simp
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [pow_mul]
    left
    unfold Felt
    simp

  have h_a_bound : ∀ i : Fin 4, first4val a i ≤ 511 := by
    intro i
    have : i.val < FELT252_N_WORDS := by
      unfold FELT252_N_WORDS
      omega
    specialize han ⟨i.val, this⟩
    simp only [Nat.reducePow] at han
    unfold first4val
    rw[han.1]
    rw[ZMod.val_cast_of_lt]
    exact Nat.le_of_lt_add_one han.2
    unfold Stwo.P
    linarith

  have h_b_bound : ∀ i : Fin 4, first4val b i ≤ 511 := by
    intro i
    have : i.val < FELT252_N_WORDS := by
      unfold FELT252_N_WORDS
      omega
    specialize hbn ⟨i.val, this⟩
    simp only [Nat.reducePow] at hbn
    unfold first4val
    rw[hbn.1]
    rw[ZMod.val_cast_of_lt]
    exact Nat.le_of_lt_add_one hbn.2
    unfold Stwo.P
    linarith

  have h_convolution_val : ∀ i : Fin 7, (convolution i).val = convolution_val i := by
    intro i
    rw [h_convolution_def, h_convolution_val_def]
    apply Nat.cast_inj_of_lt_char (R := Felt) --
    . dsimp [Felt]; rw [ZMod.ringChar_zmod_n]
      apply ZMod.val_lt
    . dsimp [Felt]
      rw [ZMod.ringChar_zmod_n]
      apply lt_of_le_of_lt
      apply simple_convolution_val_bound 4 511 _ _ h_a_bound h_b_bound i
      unfold Stwo.P
      norm_num
    rw [←ZMod.cast_eq_val, ZMod.cast_id]
    have := cast_simple_convolution_val_eq (R := Felt) 4 (first4val a) (first4val b)
    have := congr_fun this i
    have h_NeZero : NeZero NUM_LIMBS := ⟨(show NUM_LIMBS ≠ 0 by unfold NUM_LIMBS; norm_num)⟩
    rw [←this, simple_convolution_val'_eq_simple_convolution_val]
    unfold NUM_LIMBS
    congr <;> (ext i; unfold first4felt; unfold first4val; simp; rw [ZMod.cast_id]) -- ?


  have h_convolution_val_poly: (∑ i : Fin 7, ZMod.val (convolution i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) = eval_poly (2^(FELT252_BITS_PER_WORD)) convolution_val := by
    unfold eval_poly
    simp
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [pow_mul]
    exact (h_convolution_val i)


  have h_convolution_bound : ∀ i : Fin 7, (convolution i).val < (1 <<< 20) := by
    intro i
    rw[h_convolution_val i]
    rw[h_convolution_val_def]
    have := simple_convolution_val_bound 4 511 (first4val a) (first4val b) h_a_bound h_b_bound i
    omega

  have h_c_bound : ∀ i : Fin 8, (first8felt c i).val < (1 <<< 9) := by
    intro i
    have : i.val < FELT252_N_WORDS := by
      unfold FELT252_N_WORDS
      omega
    specialize hcn ⟨i.val, this⟩
    simp only [Nat.reducePow] at hcn
    unfold first8felt
    rw[hcn.1]
    rw[ZMod.val_cast_of_lt]
    exact hcn.2
    unfold Stwo.P
    linarith

  unfold NUM_LIMBS at *

  have hval1_pre : prev_limb_accumulator (1:Fin 6).castSucc = prev_limb_accumulator ⟨0, by decide⟩ + (convolution ⟨0, by decide⟩ - first8felt c 0) := by
    specialize hmain ⟨0, by decide⟩
    simp at hmain
    rw[← h_convolution_def] at hmain
    simp
    exact hmain

  have hval1 : (convolution ⟨0, by decide⟩).val + 2^9 * (convolution ⟨1, by decide⟩).val =
               (first8felt c 0).val + 2^9 * (first8felt c 1).val + 2^18 * (prev_limb_accumulator ⟨2, by decide⟩).val := by
    specialize hmain ⟨1, by decide⟩
    simp only [Nat.mod_succ, ↓reduceIte] at hmain
    rw[← h_convolution_def] at hmain

    have htmp0 := h_c_bound 0
    have htmp1 := h_c_bound 1
    have htmp2 := h_convolution_bound ⟨0, by decide⟩
    have htmp3 := h_convolution_bound ⟨1, by decide⟩
    simp at htmp2
    simp at htmp3

    simp only [Fin.mk_one] at hmain
    rw[hval1_pre] at hmain

    have hmain1 := hmain.1
    unfold shift_val at hmain1
    unfold FELT252_BITS_PER_WORD at hmain1
    simp only [Fin.zero_eta, Fin.isValue, Nat.reduceShiftLeft, Nat.cast_ofNat] at hmain1
    rw[sub_mul] at hmain1
    rw[sub_eq_add_neg, sub_eq_add_neg, add_assoc] at hmain1
    nth_rw 1 [add_assoc] at hmain1
    rw [add_comm (-first8felt c 0)] at hmain1
    rw [add_assoc] at hmain1
    rw[← neg_add] at hmain1
    rw [mul_comm (convolution (1:Fin 6).castSucc)] at hmain1 -- first8felt c 3
    rw[(show first8felt c (1:Fin 8) = first8felt c 1 by simp)] at hmain1
    rw [mul_comm (first8felt c 1)] at hmain1
    rw[← sub_eq_add_neg] at hmain1
    rw[← add_sub_assoc] at hmain1
    rw[add_comm (512 * first8felt c 1)] at hmain1


    have helper_inequality : ZMod.val (first8felt c 0 + first8felt c 1 * 512) ≤
                              ZMod.val (convolution ⟨0, by decide⟩ + (convolution ⟨1, by decide⟩) * 512) := by

      have : (prev_limb_accumulator ⟨0, by decide⟩).val < 2^11 := by
        rw[h_prev_limb_accumulator_0]
        simp

      simp only [Fin.zero_eta, Fin.isValue] at this

      rw[mul_comm (first8felt c 1), mul_comm (convolution ⟨1, by decide⟩)]
      have := add_val_argument3 (h_convolution_bound ⟨0, by decide⟩) (h_convolution_bound ⟨1, by decide⟩)
                 (h_c_bound 0) (h_c_bound 1) this hmain1
      simp at h_prev_limb_accumulator_0
      rw[h_prev_limb_accumulator_0, ZMod.val_zero, zero_add] at this
      exact this


    simp at h_prev_limb_accumulator_0
    simp at hmain
    simp[mk_2]
    rw[hmain.2]
    rw[(show 262144 = double_shift_val.val by rfl)]
    rw[← ZMod.val_mul_of_lt]
    rw[mul_comm double_shift_val,mul_assoc, mul_comm double_shift_inverse_val, double_shift_inverse_val_spec,mul_one] --double_shift_inverse_val_spec
    unfold shift_val
    unfold FELT252_BITS_PER_WORD
    simp
    rw[sub_mul]
    rw[sub_eq_add_neg, sub_eq_add_neg]
    nth_rw 2 [add_assoc]
    nth_rw 2 [add_assoc]
    rw [add_comm (-first8felt c 0)]
    rw[← add_assoc]
    rw[← add_assoc]
    nth_rw 2 [add_assoc]
    nth_rw 3 [add_assoc]
    rw[← neg_add]
    rw[← sub_eq_add_neg] --

    rw[← h_triv3]
    rw[add_sub_assoc']
    rw [add_comm _ (first8felt c 0)]

    rw[← ZMod.val_mul_of_lt]
    rw[← ZMod.val_mul_of_lt]
    rw[← ZMod.val_add_of_lt]
    rw[← ZMod.val_add_of_lt]
    rw[ZMod.val_sub]
    rw[← Nat.add_sub_assoc]
    nth_rw 4 [mul_comm]
    rw[Nat.add_sub_cancel_left]
    rw[mul_comm]

    rw[h_prev_limb_accumulator_0, zero_add]

    rw[h_prev_limb_accumulator_0, zero_add]
    exact helper_inequality

    rw[h_prev_limb_accumulator_0, zero_add]
    exact helper_inequality

    calc
      ZMod.val (first8felt c 0) + (512 * first8felt c 1).val < 2^9 + 512 * 2^9 := by
        rw[ZMod.val_mul_of_lt]
        rw[h_triv3]
        apply add_lt_add
        exact h_c_bound 0
        apply mul_lt_mul_of_pos_left
        exact h_c_bound 1
        norm_num
        rw[h_triv3]
        unfold Stwo.P
        have htmp2 := h_c_bound 1
        omega
      _ < Stwo.P := by
        unfold Stwo.P
        norm_num

    rw[ZMod.val_mul_of_lt, h_triv3]
    unfold Stwo.P
    omega

    --repeat?
    rw[h_triv3]
    unfold Stwo.P
    omega

    rw[h_triv3]
    unfold Stwo.P
    omega

    rw[h_triv3]
    unfold Stwo.P
    omega

    unfold Stwo.P
    unfold double_shift_val
    unfold shift_val
    unfold FELT252_BITS_PER_WORD
    simp

    rw[(show ZMod.val ((512:Felt)*(512:Felt)) = 262144 by rfl)]

    have hmain1b := hmain.1
    unfold shift_val at hmain1b
    unfold FELT252_BITS_PER_WORD at hmain1b
    simp at hmain1b
    rw[h_prev_limb_accumulator_0, zero_add] at hmain1b
    rcases hmain1b with ⟨n, ⟨hmain1b_le, hmain1b_eq⟩⟩
    have htmp4 :  ZMod.val ((convolution ⟨0,by decide⟩ - first8felt c 0 + (convolution ⟨1,by decide⟩ - first8felt c 1) * 512) * double_shift_inverse_val) < 2^11 := by
      simp
      rw[hmain1b_eq]
      rw[ZMod.val_cast_of_lt]
      omega
      unfold Stwo.P
      omega
    simp at htmp4
    rw[h_prev_limb_accumulator_0, zero_add]
    omega


  have hval2_pre : prev_limb_accumulator ⟨3, by decide⟩ = prev_limb_accumulator ⟨2, by decide⟩ + (convolution ⟨2, by decide⟩ - first8felt c 2) := by
    specialize hmain ⟨2, by decide⟩
    simp at hmain
    rw[← h_convolution_def] at hmain
    exact hmain

  have hval2 : (prev_limb_accumulator ⟨2, by decide⟩).val + (convolution ⟨2, by decide⟩).val + 2^9 * (convolution ⟨3, by decide⟩).val =
               (first8felt c 2).val + 2^9 * (first8felt c 3).val +
               2^18 * (prev_limb_accumulator ⟨4, by decide⟩).val:= by --
    have hmain_copy := hmain
    specialize hmain_copy ⟨1, by decide⟩
    simp at hmain_copy
    rw[← h_convolution_def] at hmain_copy
    have h_pla2_rc := hmain_copy.1
    rw[← hmain_copy.2] at h_pla2_rc
    rcases h_pla2_rc with ⟨n_pla2, ⟨h_pla2_lt, h_pla2_eq⟩⟩
    have h_pla2_val_lt : ZMod.val (prev_limb_accumulator ⟨2, by decide⟩) < 2^11 := by
      simp only [mk_2]
      rw[h_pla2_eq]
      rw[ZMod.val_cast_of_lt]
      exact h_pla2_lt
      unfold Stwo.P
      omega

    specialize hmain ⟨3, by decide⟩
    simp at hmain
    rw[← h_convolution_def] at hmain

    have h_c_bound2 := h_c_bound 2
    have h_c_bound3 := h_c_bound 3
    have h_convolution_bound2 := h_convolution_bound ⟨2, by decide⟩
    have h_convolution_bound3 := h_convolution_bound ⟨3, by decide⟩

    simp at hval2_pre
    rw[hval2_pre] at hmain


    have hmain1 := hmain.1
    unfold shift_val at hmain1
    unfold FELT252_BITS_PER_WORD at hmain1
    simp at hmain1
    rw[sub_mul] at hmain1
    rw[sub_eq_add_neg, sub_eq_add_neg, add_assoc] at hmain1
    nth_rw 1 [add_assoc] at hmain1
    rw [add_comm (-first8felt c 2)] at hmain1
    rw [add_assoc] at hmain1
    rw[← neg_add] at hmain1
    rw [mul_comm (convolution (3 : Fin 7))] at hmain1
    rw [mul_comm (first8felt c 3)] at hmain1
    rw[← sub_eq_add_neg] at hmain1
    rw[← add_sub_assoc] at hmain1
    rw[add_comm (512 * first8felt c 3)] at hmain1


    have helper_inequality : ZMod.val (first8felt c 2 + first8felt c 3 * 512) ≤ ZMod.val (prev_limb_accumulator ⟨2, by decide⟩) +
                              ZMod.val (convolution ⟨2, by decide⟩ + (convolution ⟨3, by decide⟩) * 512) := by
      rw[mul_comm (first8felt c 3), mul_comm (convolution ⟨3, by decide⟩)]
      exact add_val_argument3 (h_convolution_bound ⟨2, by decide⟩) (h_convolution_bound ⟨3, by decide⟩)
                 (h_c_bound 2) (h_c_bound 3) h_pla2_val_lt hmain1

    rw[ZMod.val_add_of_lt] at helper_inequality
    rw[ZMod.val_add_of_lt] at helper_inequality
    rw[ZMod.val_mul_of_lt] at helper_inequality
    rw[ZMod.val_mul_of_lt] at helper_inequality
    rw[h_triv3] at helper_inequality
    rw[← add_assoc] at helper_inequality

    simp only [mk_4]
    rw[hmain.2]
    rw[add_mul]
    rw[mul_assoc]
    rw[mul_comm shift_val]
    rw[double_shift_inverse_val_spec2]

    rw[(show 2^18 = double_shift_val.val by rfl)]
    rw[← ZMod.val_mul_of_lt]
    rw[mul_add]
    rw[mul_comm double_shift_val]
    rw[mul_assoc]
    rw[mul_comm double_shift_inverse_val]
    rw[double_shift_inverse_val_spec, mul_one]

    rw[mul_comm double_shift_val]
    rw[mul_assoc, double_shift_spec2]
    rw[(show shift_val = 512  by rfl)]
    rw[(show 2^9 = 512  by rfl)]
    rw[sub_mul]

    have : prev_limb_accumulator (2:Fin 7) + (convolution (2:Fin 7) - first8felt c 2) +
          (convolution (3:Fin 7) * 512 - first8felt c 3 * 512) = prev_limb_accumulator ⟨2, by decide⟩ +
          convolution ⟨2, by decide⟩ + convolution ⟨3, by decide⟩ * 512 - (first8felt c 2 + first8felt c 3 * 512) := by
        simp
        ring_nf

    rw[this]
    rw[ZMod.val_sub]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[h_triv3]
    rw[← Nat.add_sub_assoc]
    rw[← Nat.sub_sub]

    have :  ZMod.val (first8felt c 2) + 512 * ZMod.val (first8felt c 3) +
          (ZMod.val (prev_limb_accumulator ⟨2, by decide⟩) + ZMod.val (convolution ⟨2, by decide⟩) +
          ZMod.val (convolution ⟨3, by decide⟩) * 512) =
        ((((ZMod.val (convolution ⟨2, by decide⟩) + 512 * ZMod.val (convolution ⟨3, by decide⟩))) +
         ZMod.val (prev_limb_accumulator ⟨2, by decide⟩)) + ZMod.val (first8felt c 3) * 512) + ZMod.val (first8felt c 2) := by
        ring_nf
    rw[this]
    rw[Nat.add_sub_cancel]
    rw[Nat.add_sub_cancel]
    ring_nf

    exact helper_inequality

    pick_goal 7
    rw[h_triv4]
    unfold Stwo.P
    rcases hmain1 with ⟨n, ⟨hmain1_lt, hmain1_eq⟩⟩
    have : (prev_limb_accumulator (2:Fin 7) + (convolution (2:Fin 7) - first8felt c 2)) * double_shift_inverse_val +
        (convolution (3:Fin 7) - first8felt c 3) * shift_inverse_val =
        (prev_limb_accumulator ⟨2, by decide⟩ + (convolution ⟨2, by decide⟩ + 512 * convolution ⟨3, by decide⟩ -
        (first8felt c 2 + 512 * first8felt c 3))) * double_shift_inverse_val := by

      simp only [mk_2, mk_3]
      rw[show ((512:Felt) = shift_val) by rfl]
      nth_rw 2 [add_mul]
      nth_rw 2 [sub_mul]
      nth_rw 2 [add_mul]
      nth_rw 2 [add_mul]
      rw [mul_comm shift_val]
      rw [mul_comm shift_val]
      rw [mul_assoc]
      rw [mul_assoc]
      rw[double_shift_inverse_val_spec2b]
      ring_nf
    rw[this]

    simp only [mk_2, mk_3]
    rw[hmain1_eq]
    rw[ZMod.val_cast_of_lt]

    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[ZMod.val_mul_of_lt]
    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[ZMod.val_mul_of_lt]
    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[h_triv3]
    any_goals unfold Stwo.P
    any_goals omega

  have hval3_pre : prev_limb_accumulator (5:Fin 7) = prev_limb_accumulator ⟨4, by decide⟩ + (convolution ⟨4, by decide⟩ - first8felt c 4) := by
    specialize hmain ⟨4, by decide⟩
    simp at hmain
    rw[← h_convolution_def] at hmain
    exact hmain

  have hval3 : (convolution ⟨4, by decide⟩).val + 2^9 * (convolution ⟨5, by decide⟩).val + (prev_limb_accumulator ⟨4, by decide⟩).val =
               (first8felt c 4).val + 2^9 * (first8felt c 5).val +
               2^18 * (prev_limb_accumulator ⟨6, by decide⟩).val:= by --
    have hmain_copy := hmain
    specialize hmain_copy ⟨3, by decide⟩
    simp at hmain_copy
    rw[← h_convolution_def] at hmain_copy
    have h_pla2_rc := hmain_copy.1
    rw[← hmain_copy.2] at h_pla2_rc
    rcases h_pla2_rc with ⟨n_pla2, ⟨h_pla2_lt, h_pla2_eq⟩⟩
    have h_pla2_val_lt : ZMod.val (prev_limb_accumulator ⟨4, by decide⟩) < 2^11 := by
      simp only [mk_4]
      rw[h_pla2_eq]
      rw[ZMod.val_cast_of_lt]
      exact h_pla2_lt
      unfold Stwo.P
      omega

    specialize hmain ⟨5, by decide⟩
    simp at hmain
    rw[← h_convolution_def] at hmain

    have h_c_bound2 := h_c_bound 4
    have h_c_bound3 := h_c_bound 5
    have h_convolution_bound2 := h_convolution_bound ⟨4, by decide⟩
    have h_convolution_bound3 := h_convolution_bound ⟨5, by decide⟩

    rw[hval3_pre] at hmain

    have hmain1 := hmain.1
    unfold shift_val at hmain1
    unfold FELT252_BITS_PER_WORD at hmain1
    simp at hmain1
    rw[sub_mul] at hmain1
    rw[sub_eq_add_neg, sub_eq_add_neg, add_assoc] at hmain1
    nth_rw 1 [add_assoc] at hmain1
    rw [add_comm (-first8felt c 4)] at hmain1
    rw [add_assoc] at hmain1
    rw[← neg_add] at hmain1
    rw [mul_comm (convolution (5:Fin 7))] at hmain1
    rw [mul_comm (first8felt c 5)] at hmain1
    rw[← sub_eq_add_neg] at hmain1
    rw[← add_sub_assoc] at hmain1
    rw[add_comm (512 * first8felt c 5)] at hmain1

    have helper_inequality : ZMod.val (first8felt c 4 + first8felt c 5 * 512) ≤ ZMod.val (prev_limb_accumulator ⟨4, by decide⟩) +
                              ZMod.val (convolution ⟨4, by decide⟩ + (convolution ⟨5, by decide⟩) * 512) := by
      rw[mul_comm (first8felt c 5), mul_comm (convolution ⟨5, by decide⟩)]
      exact add_val_argument3 (h_convolution_bound ⟨4, by decide⟩) (h_convolution_bound ⟨5, by decide⟩)
                 (h_c_bound 4) (h_c_bound 5) h_pla2_val_lt hmain1

    rw[ZMod.val_add_of_lt] at helper_inequality
    rw[ZMod.val_add_of_lt] at helper_inequality
    rw[ZMod.val_mul_of_lt] at helper_inequality
    rw[ZMod.val_mul_of_lt] at helper_inequality
    rw[h_triv3] at helper_inequality
    rw[← add_assoc] at helper_inequality

    simp only [mk_6]
    rw[hmain.2]
    rw[add_mul]
    rw[mul_assoc]
    rw[mul_comm shift_val]
    rw[double_shift_inverse_val_spec2]

    rw[(show 2^18 = double_shift_val.val by rfl)]
    rw[← ZMod.val_mul_of_lt]
    rw[mul_add]
    rw[mul_comm double_shift_val]
    rw[mul_assoc]
    rw[mul_comm double_shift_inverse_val]
    rw[double_shift_inverse_val_spec, mul_one]

    rw[mul_comm double_shift_val]
    rw[mul_assoc, double_shift_spec2]
    rw[(show shift_val = 512  by rfl)]
    rw[(show 2^9 = 512  by rfl)]
    rw[sub_mul]

    have : prev_limb_accumulator ⟨4, by decide⟩ + (convolution ⟨4, by decide⟩ - first8felt c 4) +
          (convolution (5:Fin 7) * 512 - first8felt c 5 * 512) = prev_limb_accumulator ⟨4, by decide⟩ +
          convolution ⟨4, by decide⟩ + convolution ⟨5, by decide⟩ * 512 - (first8felt c 4 + first8felt c 5 * 512) := by
        simp only [mk_5]
        ring_nf

    rw[this]
    rw[ZMod.val_sub]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[h_triv3]
    rw[← Nat.add_sub_assoc]
    rw[← Nat.sub_sub]

    have :  ZMod.val (first8felt c 4) + 512 * ZMod.val (first8felt c 5) +
          (ZMod.val (prev_limb_accumulator ⟨4, by decide⟩) + ZMod.val (convolution ⟨4, by decide⟩) +
          ZMod.val (convolution ⟨5, by decide⟩) * 512) =
        ((((ZMod.val (convolution ⟨4, by decide⟩) + 512 * ZMod.val (convolution ⟨5, by decide⟩))) +
         ZMod.val (prev_limb_accumulator ⟨4, by decide⟩)) + ZMod.val (first8felt c 5) * 512) + ZMod.val (first8felt c 4) := by
        ring_nf
    rw[this]
    rw[Nat.add_sub_cancel]
    rw[Nat.add_sub_cancel]
    ring_nf

    exact helper_inequality

    pick_goal 7
    rw[h_triv4]
    unfold Stwo.P
    rcases hmain1 with ⟨n, ⟨hmain1_lt, hmain1_eq⟩⟩
    have : (prev_limb_accumulator ⟨4, by decide⟩ + (convolution ⟨4, by decide⟩ - first8felt c 4)) * double_shift_inverse_val +
        (convolution (5:Fin 7) - first8felt c 5) * shift_inverse_val =
        (prev_limb_accumulator ⟨4, by decide⟩ + (convolution ⟨4, by decide⟩ + 512 * convolution ⟨5, by decide⟩ -
        (first8felt c 4 + 512 * first8felt c 5))) * double_shift_inverse_val := by

      simp only [mk_5]
      rw[show ((512:Felt) = shift_val) by rfl]
      nth_rw 2 [add_mul]
      nth_rw 2 [sub_mul]
      nth_rw 2 [add_mul]
      nth_rw 2 [add_mul]
      rw [mul_comm shift_val]
      rw [mul_comm shift_val]
      rw [mul_assoc]
      rw [mul_assoc]
      rw[double_shift_inverse_val_spec2b]
      --rw[double_shift_inverse_val_spec2b]
      ring_nf
    rw[this]

    simp only [mk_4, mk_5]
    rw[hmain1_eq]
    rw[ZMod.val_cast_of_lt]

    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[ZMod.val_mul_of_lt]
    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[ZMod.val_mul_of_lt]
    any_goals rw[ZMod.val_add_of_lt]
    any_goals rw[h_triv3]
    any_goals unfold Stwo.P
    any_goals omega

  have hval4 : (convolution ⟨6, by decide⟩).val  + (prev_limb_accumulator ⟨6, by decide⟩).val=
               (first8felt c 6).val + 2^9 * (first8felt c 7).val:= by --

    specialize hmain ⟨5, by decide⟩
    simp at hmain

    have h_convolution_bound_6 := h_convolution_bound 6
    have h_c_bound_6 := h_c_bound 6
    have h_c_bound_7 := h_c_bound 7

    have : first4felt a 3 * first4felt b 3 = convolution ⟨6, by decide⟩ := by
      rw[h_convolution_def]
      unfold simple_convolution_val'
      simp
    simp[mk_3] at hlast
    rw[this] at hlast
    have : convolution (6:Fin 7) = first8felt c 6 + shift_val * first8felt c 7 - prev_limb_accumulator ⟨6, by decide⟩ := by
      calc
        convolution ⟨6, by decide⟩ = (prev_limb_accumulator ⟨6, by decide⟩ + convolution ⟨6, by decide⟩ - first8felt c 6 -
                        first8felt c 7 * shift_val) + (first8felt c 6 + first8felt c 7 * shift_val) - prev_limb_accumulator ⟨6, by decide⟩ := by
          ring_nf
        _ = first8felt c 6 + shift_val * first8felt c 7 - prev_limb_accumulator ⟨6, by decide⟩ := by
          simp only [mk_6] at *
          rw[hlast]
          rw[zero_add]
          rw[mul_comm shift_val]
    simp only [mk_6] at *
    rw[this]
    rw[ZMod.val_sub]
    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]

    rw[Nat.sub_add_cancel]

    rw[← h_triv5]
    rw[← ZMod.val_mul_of_lt]
    rw[← ZMod.val_add_of_lt]

    apply add_val_argument

    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    omega
    unfold Stwo.P
    rw[h_triv5]
    omega
    unfold Stwo.P
    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    omega
    rw[h_triv5]
    omega

    rw[hmain.2]
    rcases hmain.1 with ⟨n, ⟨hmain1b_lt, hmain1b_eq⟩⟩
    rw[hmain1b_eq]
    rw[ZMod.val_cast_of_lt]
    omega

    unfold Stwo.P
    omega

    rw[← this]
    simp at h_convolution_bound_6
    omega

    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    unfold Stwo.P
    omega

    rw[h_triv5]
    unfold Stwo.P
    omega

    rw[h_triv5]
    unfold Stwo.P
    omega
    rw[h_triv5]
    unfold Stwo.P
    omega

    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    unfold Stwo.P
    omega

    rw[h_triv5]
    unfold Stwo.P
    omega

    apply add_val_argument

    rw[ZMod.val_add_of_lt]
    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    omega
    unfold Stwo.P
    rw[h_triv5]
    omega
    unfold Stwo.P
    rw[ZMod.val_mul_of_lt]
    rw[h_triv5]
    omega
    rw[h_triv5]
    omega

    rw[hmain.2]
    rcases hmain.1 with ⟨n, ⟨hmain1b_lt, hmain1b_eq⟩⟩
    rw[hmain1b_eq]
    rw[ZMod.val_cast_of_lt]
    omega

    unfold Stwo.P
    omega

    rw[← this]
    simp at h_convolution_bound_6
    omega


  have h_in_nat : (∑ i, ZMod.val (first4felt a i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i)) *
      ∑ i, ZMod.val (first4felt b i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i) =
      ∑ i, ZMod.val (first8felt c i) * 2 ^ (FELT252_BITS_PER_WORD * ↑i) := by
    rw [h_a_poly, h_b_poly]
    rw [← simple_convolution_val_spec]
    rw [← h_convolution_val_def]
    rw[← h_convolution_val_poly]

    simp [Fin.sum_univ_seven]
    simp [Fin.sum_univ_eight]

    unfold FELT252_BITS_PER_WORD

    simp only [Fin.zero_eta, Fin.mk_one] at hval1
    rw[mul_comm] at hval1
    rw[hval1]

    have : 2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨2, by decide⟩) + (ZMod.val (convolution (2:Fin 7)) * 2 ^ (9 * 2) +
          ZMod.val (convolution (3:Fin 7)) * 2 ^ (9 * 3)) =
          2 ^ (9 * 2) * (ZMod.val (prev_limb_accumulator ⟨2, by decide⟩) +
          ZMod.val (convolution ⟨2, by decide⟩) + 2 ^ 9 * ZMod.val (convolution ⟨3, by decide⟩)) := by
        simp only [mk_2, mk_3]
        ring_nf

    rw[add_assoc _ _ (ZMod.val (convolution (3:Fin 7)) * 2 ^ (9 * 3))]
    rw[add_assoc _ ( 2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨2, by decide⟩)) _]
    rw[this]
    rw[hval2]

    have :  (2 ^ (9 * 2) * (2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨4, by decide⟩)) +
        (ZMod.val (convolution (4:Fin 7)) * 2 ^ (9 * 4) + ZMod.val (convolution (5:Fin 7)) * 2 ^ (9 * 5))) =
          2 ^ (9 * 4) * (ZMod.val (convolution ⟨4, by decide⟩) + 2 ^ 9 * ZMod.val (convolution ⟨5, by decide⟩) +
          ZMod.val (prev_limb_accumulator ⟨4, by decide⟩)) := by
        simp only [mk_4, mk_5]
        ring_nf

    rw[mul_add]
    rw[add_assoc _ _ (ZMod.val (convolution (5:Fin 7)) * 2 ^ (9 * 5))]
    rw[← add_assoc _ _ (2 ^ (9 * 2) * (2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨4, by decide⟩)))]
    rw[add_assoc _ (2 ^ (9 * 2) * (2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨4, by decide⟩))) _]
    rw[this]
    rw[hval3]

    rw [mul_add (2 ^ (9 * 4))]
    rw[add_assoc _ _ (ZMod.val (convolution (6:Fin 7)) * 2 ^ (9 * 6))]
    rw[add_assoc _ _ (ZMod.val (convolution (6:Fin 7)) * 2 ^ (9 * 6))]

    have : (2 ^ (9 * 4) * (2 ^ 18 * ZMod.val (prev_limb_accumulator ⟨6, by decide⟩)) + ZMod.val (convolution (6:Fin 7)) * 2 ^ (9 * 6)) =
          2 ^ (9 * 6) * (ZMod.val (convolution ⟨6, by decide⟩) + ZMod.val (prev_limb_accumulator ⟨6, by decide⟩)) := by
        simp only [mk_6]
        ring_nf

    rw[this]
    rw[hval4]

    ring_nf

  rw[h_in_nat]

set_option maxHeartbeats 500000
theorem sound_auto [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)]
    (varAssign : VarAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (a b c : Felt252Expr) :
    let new_ab_lt := call ab lt a b c
    new_ab_lt.1.SatisfiedBy varAssign →
    new_ab_lt.2.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec (a.eval varAssign) (b.eval varAssign) (c.eval varAssign) := by

  intro res hnew_ab hnew_lt
  let new_ab := res.1
  let new_lt := res.2

  let a4 := first4expr a
  let b4 := first4expr b
  let c8 := first8expr c
  let convolution : Fin (2 * NUM_LIMBS - 1) → FeltExpr := simple_convolution NUM_LIMBS a4 b4

  let aux :=
    Fin.hIterate (P := fun _ => AirBuilder × AirLookupTerms × FeltExpr)
      (init := (ab, lt, FeltExpr.const 0))
      (n := 2 * NUM_LIMBS - 2)
      (f := fun i p1 =>
        let prev_ab := p1.1
        let prev_lt := p1.2.1
        let prev_limb_accumulator := p1.2.2

        let conditional_shift :=
          if i.val % 2 = 1 then
            shift
          else
            FeltExpr.const 1

        let i2 : Fin 8 := ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩

        let mid_limb_accumulator := prev_limb_accumulator + (convolution i.castSucc - c8 i2) * conditional_shift

        let (next_ab, next_lt, next_limb_accumulator) :=
          if i.val % 2 = 1 then
            let (prev_ab2, carry) := prev_ab.deduce
            let prev_lt2 := prev_lt.add_rc 11 carry
            let prev_ab3 := prev_ab2.constrain (carry * double_shift - mid_limb_accumulator)
            (prev_ab3, prev_lt2, carry)
          else
            (prev_ab, prev_lt, mid_limb_accumulator)

        (next_ab, next_lt, next_limb_accumulator))

  let ab2 := aux.1
  let lt2 := aux.2.1
  let limb_accumulator := aux.2.2
  let final_limb_accumulator := limb_accumulator + a4 ⟨NUM_LIMBS - 1, by decide⟩ * b4 ⟨NUM_LIMBS - 1, by decide⟩

  have ⟨hab2, h_c6c7⟩ : ab2.SatisfiedBy varAssign ∧
       (final_limb_accumulator - c8 ⟨2 * NUM_LIMBS - 2, by decide⟩ - c8 ⟨2 * NUM_LIMBS - 1, by decide⟩ * shift).eval varAssign = 0 := by
     apply ab2.constrain_SatisfiedBy _ varAssign |>.mp hnew_ab

  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) :=
     (h : i ≤ 2 * NUM_LIMBS - 2) →
     p.1.SatisfiedBy varAssign →
     p.2.1.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
     ab.SatisfiedBy varAssign ∧
     lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
     ∃ prev_limb_accumulator : Fin i.succ → Felt,
        prev_limb_accumulator 0 = 0 ∧
        (∀ j : Fin i,
        let conditional_shift :=
          if j.val % 2 = 1 then
            shift_val
          else
            (1:Felt)

        have i2 : Fin 8 := ⟨j.val, by unfold NUM_LIMBS at h; omega⟩


        have mid_limb_accumulator := (prev_limb_accumulator ⟨j.val, by omega⟩) +
          ((convolution ⟨j.val, by unfold NUM_LIMBS; unfold NUM_LIMBS at h; omega⟩).eval varAssign - (c8 i2).eval varAssign) * conditional_shift

        if j.val % 2 = 1 then
          have carry := mid_limb_accumulator * double_shift_inverse_val;
            (IsRangeChecked 11 carry) ∧
            prev_limb_accumulator j.succ = carry
        else
          prev_limb_accumulator j.succ = mid_limb_accumulator
        ) ∧ (
          prev_limb_accumulator (Fin.last i) = p.2.2.eval varAssign)

  have haux : Q (2 * NUM_LIMBS - 2) aux := by
    apply Fin.hIterate_elim
    . simp [Q]
      intro h h2
      use h, h2, (fun _ => 0)
    rintro i ⟨ab', lt', prev_limb_accumulator'⟩ ih h'

    specialize ih (le_trans (Nat.le_succ _) h')
    lift_lets
    intro iab1 lt1 prev_limb_accumulator1; dsimp -zeta [iab1, lt1, prev_limb_accumulator1] --?
    rintro conditional_shift i2 mid_limb_accumulator ha hb

    have h_conditional_shift : conditional_shift = if (↑i:Nat) % 2 = 1 then shift else FeltExpr.const 1 := by rfl
    have h_mid_limb_accumulator: mid_limb_accumulator =
         prev_limb_accumulator' + (convolution i.castSucc - c8 i2) * conditional_shift := by rfl
    rw[h_conditional_shift] at h_mid_limb_accumulator
    by_cases hcase : i.val % 2 = 1
    <;> simp [hcase]
    <;> simp [hcase] at ha hb
    · rcases ha with ⟨hab', hab'deduce⟩
      have ⟨hlt', hlt'rc⟩ := AirLookupTerms.IsRangeChecked_add_rc _ varAssign h_satisfied h_rc _ _ hb
      specialize ih hab' hlt'rc
      rcases ih with ⟨hab, ih2'⟩
      constructor
      · exact hab
      rcases ih2' with ⟨hlt, ih2⟩
      constructor
      · exact hlt
      rcases ih2 with ⟨prev_limb_accumulators, ih3⟩
      rcases ih3 with ⟨h_prev_limb_accumulator_0, ih4⟩
      rcases ih4 with ⟨for_all_j, ih5⟩

      use Fin.snoc prev_limb_accumulators ((ab'.deduce.2).eval varAssign)

      constructor
      . rw [←Fin.castSucc_zero, Fin.snoc_castSucc, h_prev_limb_accumulator_0]
      constructor
      . intro j
        by_cases hcase_j : j.val % 2 = 1
        <;> simp [hcase_j]
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
          · dsimp [Fin.snoc]
            have : (↑j:Nat) < (↑i:Nat) + 1 := by
              omega
            simp[this]
            have : ((↑j:Nat) % 2 = 1) := by
              simpa using hcase_j
            specialize for_all_j j
            simp[this] at for_all_j
            rcases for_all_j with ⟨rc_curr, ih6⟩

            have htmp2: j.castSucc.succ ≠ Fin.last (↑i + 1) := by
              simp
            constructor
            · exact rc_curr

            have : j.castSucc.succ.castPred htmp2 = j.succ := by
              ext
              rfl
            rw[this]
            rw[← ih6]

          · simp
            dsimp [Fin.snoc]
            simp
            have : (↑(1 <<< FELT252_BITS_PER_WORD):Felt) * (↑(1 <<< FELT252_BITS_PER_WORD):Felt) = double_shift_val := by
              unfold double_shift_val
              unfold shift_val
              rfl
            rw[this] at hab'deduce
            rw[sub_eq_zero] at hab'deduce
            have htmp : FeltExpr.eval varAssign ab'.deduce.2 = (FeltExpr.eval varAssign mid_limb_accumulator) * double_shift_inverse_val := by
              rw[← hab'deduce]
              rw[mul_assoc, double_shift_inverse_val_spec, mul_one]

            rw[h_mid_limb_accumulator] at htmp
            rw[htmp] at hlt'
            simp[hcase] at hlt'

            have : (↑(1 <<< FELT252_BITS_PER_WORD):Felt) = shift_val := by
              unfold shift_val
              rfl
            rw[this] at hlt'
            dsimp[i2] at hlt'

            have : FeltExpr.eval varAssign prev_limb_accumulator' = prev_limb_accumulators ⟨(↑i:Nat), by omega⟩ := by
              rw[← ih5]
              rfl
            rw[this] at hlt'

            constructor
            · exact hlt'
            have : FeltExpr.eval varAssign ab'.deduce.2 = FeltExpr.eval varAssign ab'.deduce.2 * double_shift_val * double_shift_inverse_val := by
              rw[mul_assoc, double_shift_inverse_val_spec, mul_one]
            rw[this]
            rw[hab'deduce]

            rw[h_mid_limb_accumulator]
            simp only [FeltExpr.eval_add]
            simp only [FeltExpr.eval_mul]
            simp only [FeltExpr.eval_sub]
            simp [hcase]
            have : (↑(1 <<< FELT252_BITS_PER_WORD):Felt) = shift_val := by
              unfold shift_val
              rfl
            rw[this]
            dsimp[i2]
            have : FeltExpr.eval varAssign prev_limb_accumulator' = prev_limb_accumulators ⟨(↑i:Nat), by omega⟩ := by
              rw[← ih5]
              rfl
            rw[this]
            left
            have : i.castSucc = ⟨(↑i:Nat), by omega⟩  := by
              rfl
            rw[this]

        rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · dsimp [Fin.snoc]
          have : (↑j:Nat) < (↑i:Nat) := by
            omega
          simp[this]
          have : (↑j:Nat) < (↑i:Nat) +1 := by
            omega
          simp[this]
          let cxz:= j.castSucc.succ
          let zxczxc := Fin.last (↑i + 1)
          have htmp2: j.castSucc.succ ≠ Fin.last (↑i + 1) := by
            simp
          have : j.castSucc.succ.castPred htmp2 = j.succ := by
            ext
            rfl
          rw[this]
          specialize for_all_j j
          have : ¬((↑j:Nat) % 2 = 1) := by
              simpa using hcase_j
          simp[this] at for_all_j
          exact for_all_j

        · simp [Fin.last, hcase] at hcase_j

      dsimp [Fin.snoc]
      simp

    specialize ih ha hb
    rcases ih with ⟨hab, ih2'⟩
    constructor
    · exact hab
    rcases ih2' with ⟨hlt, ih2⟩
    constructor
    · exact hlt
    rcases ih2 with ⟨prev_limb_accumulators, ih3⟩
    rcases ih3 with ⟨h_prev_limb_accumulator_0, ih4⟩
    rcases ih4 with ⟨for_all_j, ih5⟩
    use Fin.snoc prev_limb_accumulators (mid_limb_accumulator.eval varAssign)

    constructor
    . rw [←Fin.castSucc_zero, Fin.snoc_castSucc, h_prev_limb_accumulator_0]
    constructor
    . intro j
      by_cases hcase_j : j.val % 2 = 1
      <;> simp [hcase_j]
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · dsimp [Fin.snoc]
          have : (↑j:Nat) < (↑i:Nat) + 1 := by
            omega
          simp[this]
          have : ((↑j:Nat) % 2 = 1) := by
            simpa using hcase_j --?
          specialize for_all_j j
          simp[this] at for_all_j
          rcases for_all_j with ⟨rc_curr, ih6⟩
          have htmp2: j.castSucc.succ ≠ Fin.last (↑i + 1) := by
            simp
          constructor
          · exact rc_curr

          have : j.castSucc.succ.castPred htmp2 = j.succ := by
            ext
            rfl
          rw[this]
          exact ih6

        · simp [Fin.last, hcase] at hcase_j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · dsimp [Fin.snoc]
        have : (↑j:Nat) < (↑i:Nat) := by
          omega
        simp[this]
        have : (↑j:Nat) < (↑i:Nat) +1 := by
          omega
        simp[this]
        let cxz:= j.castSucc.succ
        let zxczxc := Fin.last (↑i + 1)
        have htmp2: j.castSucc.succ ≠ Fin.last (↑i + 1) := by
          simp
        have : j.castSucc.succ.castPred htmp2 = j.succ := by
          ext
          rfl
        rw[this]
        specialize for_all_j j
        have : ¬((↑j:Nat) % 2 = 1) := by
            simpa using hcase_j
        simp[this] at for_all_j
        exact for_all_j
      · simp
        dsimp [Fin.snoc]
        simp
        rw[h_mid_limb_accumulator]
        simp[hcase]
        dsimp[i2] --i_1
        have : FeltExpr.eval varAssign prev_limb_accumulator' = prev_limb_accumulators ⟨(↑i:Nat), by omega⟩ := by
          rw[← ih5]
          rfl
        rw[this]
        have : i.castSucc = ⟨(↑i:Nat), by omega⟩  := by
          rfl
        rw[this]
    simp

  have h1 := haux (le_refl (2 * NUM_LIMBS - 2)) hab2
  rw[(show aux.2.1 = lt2 by rfl)] at h1
  rw[(show aux.2.2 = limb_accumulator by rfl)] at h1

  have : res.2 = lt2 := by
    rfl

  rw[this] at hnew_lt
  have h2 := h1 hnew_lt
  rcases h2 with ⟨hab, h3⟩
  constructor
  · exact hab
  rcases h3 with ⟨hlt, h4⟩
  constructor
  · exact hlt
  apply spec_of_spec_auto
  rcases h4 with ⟨prev_limb_accumulators, h_prev_limb_accumulator_0, h_for_all_j, h_final⟩
  use prev_limb_accumulators
  constructor
  · exact h_prev_limb_accumulator_0
  constructor

  · intro i
    specialize h_for_all_j i
    have : convolution = simple_convolution NUM_LIMBS a4 b4 := by rfl
    rw[this] at h_for_all_j
    unfold NUM_LIMBS at h_for_all_j
    unfold NUM_LIMBS

    have := eval_simple_convolution_eq_aux 4 a4 b4 varAssign
    specialize this i.castSucc
    have htmp : i.castSucc = ⟨i.val,by omega⟩ := by rfl
    rw[htmp] at this
    rw[this] at h_for_all_j

    exact h_for_all_j

  simp only [FeltExpr.eval_sub] at h_c6c7
  simp only [FeltExpr.eval_mul] at h_c6c7
  rw[(show FeltExpr.eval varAssign shift = shift_val by rfl)] at h_c6c7

  have : final_limb_accumulator = limb_accumulator +
         a4 ⟨NUM_LIMBS - 1, by unfold NUM_LIMBS; omega⟩ * b4 ⟨NUM_LIMBS - 1, by unfold NUM_LIMBS; omega⟩ := by rfl

  rw[this] at h_c6c7
  simp only [FeltExpr.eval_add] at h_c6c7
  simp only [FeltExpr.eval_mul] at h_c6c7

  have hfa: (first4felt (a.eval varAssign)) ⟨NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩ = (a4 ⟨NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩).eval varAssign := by rfl
  have hfb: (first4felt (b.eval varAssign)) ⟨NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩ = (b4 ⟨NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩).eval varAssign := by rfl
  have hfc1: (first8felt (c.eval varAssign)) ⟨2*NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩ = (c8 ⟨2*NUM_LIMBS -1, by unfold NUM_LIMBS; omega⟩).eval varAssign := by rfl
  have hfc2: (first8felt (c.eval varAssign)) ⟨2*NUM_LIMBS -2, by unfold NUM_LIMBS; omega⟩ = (c8 ⟨2*NUM_LIMBS -2, by unfold NUM_LIMBS; omega⟩).eval varAssign := by rfl

  simp
  rw[hfa, hfb, hfc2, hfc1]

  have : prev_limb_accumulators ⟨2 * NUM_LIMBS - 2, h_triv2⟩ = limb_accumulator.eval varAssign := by
    rw[← h_final]
    rfl
  rw[this]

  exact h_c6c7

lemma NoYieldTerms_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {a b c : Felt252Expr} :
    AirLookupTerms.NoYieldTerms (call ab lt a b c).2 := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.NoYieldTerms p.2.1
  apply Fin.hIterate_elim Q
  · unfold Q ; simp [h]
  intro k s q_k_1
  unfold Q
  unfold Q at q_k_1
  by_cases h_k : k.val % 2 = 1
  · simp [h_k]
    apply AirLookupTerms.add'_NoYieldTerms.mpr
    simp [q_k_1]
  simp [h_k, q_k_1]

lemma NoTermsOfRel_OPCODE_TRACE_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoTermsOfRel lt OPCODE_TRACE_REL_INDEX)
      {a b c : Felt252Expr} :
    AirLookupTerms.NoTermsOfRel (call ab lt a b c).2 OPCODE_TRACE_REL_INDEX := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.NoTermsOfRel p.2.1 OPCODE_TRACE_REL_INDEX
  apply Fin.hIterate_elim Q
  · unfold Q ; simp [h]
  intro k s q_k_1
  unfold Q
  unfold Q at q_k_1
  by_cases h_k : k.val % 2 = 1
  · simp [h_k]
    apply (AirLookupTerms.add'_NoTermsOfRel OPCODE_TRACE_REL_INDEX).mpr
    simp_all [RANGE_CHECK_REL_INDEX, OPCODE_TRACE_REL_INDEX]
  simp [h_k, q_k_1]

lemma RelInRelTuples_of_call [Fact (Nat.Prime Stwo.P)]
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.RelInRelTuples lt)
      {a b c : Felt252Expr} :
    AirLookupTerms.RelInRelTuples (call ab lt a b c).2 := by
  let Q (i : Nat) (p : AirBuilder × AirLookupTerms × FeltExpr) := AirLookupTerms.RelInRelTuples p.2.1
  apply Fin.hIterate_elim Q
  · unfold Q ; simp [h]
  intro k s q_k_1
  unfold Q
  unfold Q at q_k_1
  by_cases h_k : k.val % 2 = 1
  · simp [h_k]
    apply AirLookupTerms.add'_RelInRelTuple.mpr
    simp [q_k_1]
  simp [h_k, q_k_1]

end VerifyMulSmall
