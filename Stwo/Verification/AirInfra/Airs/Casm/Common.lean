import Verification.Semantics.Util
import Verification.Semantics.Soundness.AssemblyStep
import Verification.AirInfra.Util
import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.Felt252IdMemory.Memory
import Verification.AirInfra.Airs.Casm.ConstTables.RangeCheck

def ADDRESS_BITS := 29
def OFFSET_BITS := 16

def FLAG_DST_BASE_FP_INDEX : Fin 15 := 0
def FLAG_OP0_BASE_FP_INDEX : Fin 15 := 1
def FLAG_OP1_IMM_INDEX : Fin 15 := 2
def FLAG_OP1_BASE_FP_INDEX : Fin 15 := 3
def FLAG_OP1_BASE_AP_INDEX : Fin 15 := 4
def FLAG_RES_ADD_INDEX : Fin 15 := 5
def FLAG_RES_MUL_INDEX : Fin 15 := 6
def FLAG_PC_UPDATE_JUMP_INDEX : Fin 15 := 7
def FLAG_PC_UPDATE_JUMP_REL_INDEX : Fin 15 := 8
def FLAG_PC_UPDATE_JNZ_INDEX : Fin 15 := 9
def FLAG_AP_UPDATE_ADD_INDEX : Fin 15 := 10
def FLAG_AP_UPDATE_ADD_1_INDEX : Fin 15 := 11
def FLAG_OPCODE_CALL_INDEX : Fin 15 := 12
def FLAG_OPCODE_RET_INDEX : Fin 15 := 13
def FLAG_OPCODE_ASSERT_EQ_INDEX : Fin 15 := 14

structure Flags where
  dst_base_fp : Option Bool
  op0_base_fp : Option Bool
  op1_imm : Option Bool
  op1_base_fp : Option Bool
  op1_base_ap : Option Bool
  res_add : Option Bool
  res_mul : Option Bool
  pc_update_jump : Option Bool
  pc_update_jump_rel : Option Bool
  pc_update_jnz : Option Bool
  ap_update_add : Option Bool
  ap_update_add_1 : Option Bool
  opcode_call : Option Bool
  opcode_ret : Option Bool
  opcode_assert_eq : Option Bool

namespace Flags

def to_arr (f : Flags) : Array (Option Bool) := #[
  f.dst_base_fp,
  f.op0_base_fp,
  f.op1_imm,
  f.op1_base_fp,
  f.op1_base_ap,
  f.res_add,
  f.res_mul,
  f.pc_update_jump,
  f.pc_update_jump_rel,
  f.pc_update_jnz,
  f.ap_update_add,
  f.ap_update_add_1,
  f.opcode_call,
  f.opcode_ret,
  f.opcode_assert_eq]

def to_fn (f : Flags) : Fin 15 → Option Bool
  | 0 => f.dst_base_fp
  | 1 => f.op0_base_fp
  | 2 => f.op1_imm
  | 3 => f.op1_base_fp
  | 4 => f.op1_base_ap
  | 5 => f.res_add
  | 6 => f.res_mul
  | 7 => f.pc_update_jump
  | 8 => f.pc_update_jump_rel
  | 9 => f.pc_update_jnz
  | 10 => f.ap_update_add
  | 11 => f.ap_update_add_1
  | 12 => f.opcode_call
  | 13 => f.opcode_ret
  | 14 => f.opcode_assert_eq

theorem to_fn_eq_to_arr (f : Flags) (i : Fin 15) : f.to_fn i = f.to_arr[↑i] := by
  simp only [to_fn, to_arr]; split <;> rfl

protected def sum (f : Flags) (from_i to_i : Nat) : FeltExpr := Id.run do
  let mut j := 0
  let mut sum := 0
  let arr := f.to_arr
  for i in [from_i:to_i] do
    -- TODO: bound constraint
    sum := sum + opt_bool_to_nat arr[i]!
    j := j + 1
  FeltExpr.const sum
where opt_bool_to_nat : Option Bool → Nat
  | some true => 1
  | _ => 0

end Flags

def offset_as_u16 (offset : BitVec 16) : Nat := offset.toInt + (1 <<< (OFFSET_BITS - 1))
|>.toNat

def BitVec.as_u16 (bv : BitVec 16) : Nat := offset_as_u16 bv

def int_from_u16 (x : Nat) : Int := (x : Int) - (1 <<< (OFFSET_BITS - 1))
def offset_from_u16 (x : Nat) : BitVec 16 := BitVec.ofInt 16 (int_from_u16 x)
def int_from_Felt (x : Felt) : Int := int_from_u16 x.val
def offset_from_Felt (x : Felt) : BitVec 16 := offset_from_u16 x.val

lemma int_offset_as_u16_nonneg (offset : BitVec 16) : 0 ≤ offset.toInt + (1 <<< (OFFSET_BITS - 1)) := by
  rw [BitVec.toInt_eq_toNat_bmod]
  unfold OFFSET_BITS ; dsimp ; rw [Int.add_nonneg_iff_neg_le]
  apply le_trans _ (Int.le_bmod (by norm_num1))
  norm_num1

lemma BitVec_toInt_eq_from_Felt_as_u16 {x : BitVec 16} : x.toInt = int_from_Felt ↑x.as_u16 := by
  unfold int_from_Felt int_from_u16 BitVec.as_u16 offset_as_u16
  rw [ZMod.val_natCast_of_lt, Int.toNat_of_nonneg (int_offset_as_u16_nonneg x), add_sub_cancel_right]
  rw [Int.toNat_lt (int_offset_as_u16_nonneg x)]
  -- YS: in the github repository of Mathlib there is a theorem Bitvec.toInt_lt which proves this
  -- in one step, but it does not seem available in the version of Mathlib we are currently using.
  have h_toInt_lt : x.toInt < (2 ^ 15 : Nat) := by
    unfold BitVec.toInt
    by_cases h : 2 * x.toNat < 2 ^ 16
    · rw [if_pos h, Int.ofNat_lt]
      rw [←mul_pow_sub_one (by norm_num1), Nat.mul_lt_mul_left (by norm_num1), Nat.add_one_sub_one] at h
      exact h
    rw [if_neg h, Int.sub_lt_iff, ←Nat.cast_add, Int.ofNat_lt]
    apply lt_trans (BitVec.isLt x)
    norm_num
  apply lt_trans (add_lt_add_right h_toInt_lt _)
  unfold OFFSET_BITS Stwo.P ; simp


lemma as_u16_inj (x y : BitVec 16) : x.as_u16 = y.as_u16 ↔ x = y := by
  constructor
  · intro h
    rw [←Nat.cast_inj (R := Int)] at h
    unfold BitVec.as_u16 offset_as_u16 at h
    simp only [Int.toNat_of_nonneg (int_offset_as_u16_nonneg _)] at h
    simp only [add_left_inj] at h
    exact BitVec.toInt_inj.mp h
  intro h ; rw [h]

lemma as_u16_lt (x : BitVec 16) : x.as_u16 < 2^16 := by
  unfold BitVec.as_u16 offset_as_u16
  rw [Int.toNat_lt' (by norm_num1)]
  rw [Int.add_lt_iff, BitVec.toInt_eq_toNat_bmod]
  apply lt_of_lt_of_le (Int.bmod_lt (by norm_num1))
  unfold OFFSET_BITS ; dsimp ; simp

lemma toFelt_inj_of_lt (x y : Nat) (h_x : x < 2^16) (h_y : y < 2^16) : (x : Felt) = (y : Felt) ↔ x = y := by
  constructor
  · intro h
    rw [ZMod.natCast_eq_natCast_iff] at h
    apply Nat.ModEq.eq_of_lt_of_lt h
    apply lt_of_lt_of_le h_x ; unfold Stwo.P ; norm_num1
    apply lt_of_lt_of_le h_y ; unfold Stwo.P ; norm_num1
  intro h ; rw [h]

lemma u16_toFelt_inj (x y : BitVec 16) : (x.as_u16 : Felt) = (y.as_u16 : Felt) ↔ x.as_u16 = y.as_u16 := by
  exact toFelt_inj_of_lt _ _ (as_u16_lt x) (as_u16_lt y)

lemma as_u16_toFelt_inj (x y : BitVec 16) : (x.as_u16 : Felt) = (y.as_u16 : Felt) ↔ x = y := by
  rw [u16_toFelt_inj]
  rw [as_u16_inj]

lemma BitVec_toNat_toFelt_inj (x y : BitVec 16) : (x.toNat : Felt) = (y.toNat : Felt) ↔ x.toNat = y.toNat := by
  exact toFelt_inj_of_lt _ _ (BitVec.isLt x) (BitVec.isLt y)

lemma BitVec_toFelt_inj (x y : BitVec 16) : (x.toNat : Felt) = (y.toNat : Felt) ↔ x = y := by
  rw [BitVec_toNat_toFelt_inj]
  constructor
  · apply BitVec.toNat_inj.mp
  intro h ; rw [h]

lemma BitVec_toNat_toFelt_eq_as_u16_toFelt' (x y : BitVec 16) :
    (x.toNat : Felt) = (y.as_u16 : Felt) ↔ x = BitVec.ofNat 16 (y.toInt + (1 <<< (OFFSET_BITS - 1))).toNat := by
  rw [toFelt_inj_of_lt _ _ (BitVec.isLt x) (as_u16_lt y)]
  unfold BitVec.as_u16 offset_as_u16 OFFSET_BITS
  constructor
  · intro h
    apply BitVec.toNat_inj.mp
    rw [h] ; simp ; symm
    apply Nat.mod_eq_of_lt
    apply as_u16_lt
  rintro rfl
  have := as_u16_lt y
  simpa [BitVec.as_u16, offset_as_u16] using this

lemma BitVec_toNat_toFelt_eq_as_u16_toFelt (x y : BitVec 16) :
    (x.as_u16 : Felt) = (y.toNat : Felt) ↔ BitVec.ofNat 16 (x.toInt + (1 <<< (OFFSET_BITS - 1))).toNat = y := by
  rw [toFelt_inj_of_lt _ _ (as_u16_lt x) (BitVec.isLt y)]
  unfold BitVec.as_u16 offset_as_u16 OFFSET_BITS
  constructor
  · intro h
    apply BitVec.toNat_inj.mp
    rw [h] ; simp
  rintro rfl
  simp; rw [Nat.mod_eq_of_lt]
  apply as_u16_lt

lemma BitVec_u16_eq_from_Felt_to_u16 {x : BitVec 16} :
  (x.toNat : Felt) = ↑((int_from_Felt ↑x.toNat + (1 <<< (OFFSET_BITS - 1))).toNat % (1 <<< OFFSET_BITS)) := by
  unfold int_from_Felt int_from_u16
  simp only [sub_add_cancel, Int.toNat_natCast]
  apply congr_arg
  rw [ZMod.val_natCast]
  have h_lt : x.toNat < Stwo.P := by unfold Stwo.P ; apply lt_trans (BitVec.isLt x) ; norm_num1
  simp only [Nat.mod_eq_of_lt h_lt]
  unfold OFFSET_BITS
  simp [Nat.mod_eq_of_lt (BitVec.isLt x)]

def offset_as_signed (offset : FeltExpr) : FeltExpr :=
  offset - FeltExpr.const (1 <<< (OFFSET_BITS - 1))

def offsetVal_as_signed (offset : Nat) : Int := ↑offset - (1 <<< (OFFSET_BITS - 1))

def offset_toFelt (offset : Int16) : Felt := (offset.toInt : ZMod Stwo.P)

def signed_as_offset (signed : FeltExpr) : FeltExpr :=
  signed + FeltExpr.const (1 <<< (OFFSET_BITS - 1))

@[simp]
lemma signed_as_offset_as_signed [Fact (Nat.Prime Stwo.P)] (offset : FeltExpr) (varAssign : VarAssign) :
    FeltExpr.eval varAssign (signed_as_offset (offset_as_signed offset)) = FeltExpr.eval varAssign offset := by
  simp [offset_as_signed, signed_as_offset]

def offset_as_signed_Felt (offset : Felt) : Felt := offset - (1 <<< (OFFSET_BITS - 1))

@[simp]
lemma offset_as_signed_Felt_as_offset [Fact (Nat.Prime Stwo.P)] (offset : FeltExpr) (varAssign : VarAssign) :
    offset_as_signed_Felt (FeltExpr.eval varAssign (signed_as_offset offset)) = FeltExpr.eval varAssign offset := by
  simp [offset_as_signed_Felt, signed_as_offset]

def signed_as_offset_Felt (signed : Felt) : Felt := signed + (1 <<< (OFFSET_BITS - 1))

namespace Nat

def div_ceil (n m : Nat) : Nat := (n + m - 1) / m

theorem div_ceil_pos {n : ℕ} (h : 0 < n) : 0 < n.div_ceil FELT252_BITS_PER_WORD := by
  simp only [div_ceil, FELT252_BITS_PER_WORD]
  omega

theorem div_ceil_aux2 (n : ℕ) (h : n ≤ 252) : n.div_ceil FELT252_BITS_PER_WORD - 1 < FELT252_N_WORDS := by
  simp only [div_ceil, FELT252_BITS_PER_WORD, FELT252_N_WORDS, Nat.add_one_sub_one]
  omega

theorem div_ceil_aux3 {n : Nat} (h : 0 < n) :
    (n.div_ceil FELT252_BITS_PER_WORD - 1) % FELT252_N_WORDS < n.div_ceil FELT252_BITS_PER_WORD := by
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  have := div_ceil_pos h
  omega

end Nat

open Fin.NatCast

-- use this expression because it is closest to the Rust code
def felt252_to_m31 (value : Felt252Expr) (num_bits : Nat) : FeltExpr :=
  aux (num_bits.div_ceil FELT252_BITS_PER_WORD)
where
  aux : Nat → FeltExpr
  | 0 => value 0
  | 1 => value 0
  | i+2 => aux (i+1) + value (i+1) * FeltExpr.const (1 <<< (FELT252_BITS_PER_WORD * (i+1)))

def felt252_to_m31_val (value : Felt252Words) (num_bits : Nat) : Felt :=
  aux (num_bits.div_ceil FELT252_BITS_PER_WORD)
where
  aux : Nat → Felt
  | 0 => value 0
  | 1 => value 0
  | i+2 => aux (i+1) + value (i+1) * (1 <<< (FELT252_BITS_PER_WORD * (i+1)))

-- theorem felt252_to_m31_val_bound [Fact (Nat.Prime Stwo.P)]
--           (value : Felt252Words) (num_bits : Nat) :
--     (felt252_to_m31_val value num_bits).val < (1 <<< num_bits) := by
--   generalize num_bits.div_ceil FELT252_BITS_PER_WORD = n
--   induction' n with k ih
--   . simp [felt252_to_m31_val]
--     rw [FELT252_BITS_PER_WORD]
--     norm_num




theorem felt252_to_m31_eval [Fact (Nat.Prime Stwo.P)] (value : Felt252Expr) (num_bits : Nat) (varAssign : VarAssign) :
    FeltExpr.eval varAssign (felt252_to_m31 value num_bits) =
      felt252_to_m31_val (value.eval varAssign) num_bits := by
  rw [felt252_to_m31, felt252_to_m31_val]
  generalize num_bits.div_ceil FELT252_BITS_PER_WORD = i
  cases' i with i
  . rfl
  induction' i with i ih
  . rfl
  simp [felt252_to_m31.aux, ih]; rfl

def felt252_to_m31_val' (value : Felt252Words) (num_bits : Nat) : Felt :=
  if num_bits = 0 then value 0 else
    ∑ i ∈ Finset.range (num_bits.div_ceil FELT252_BITS_PER_WORD), value i * (2 ^ (FELT252_BITS_PER_WORD * i))

theorem felt252_to_m31_val_eq_val' (value : Felt252Words) (num_bits : Nat) :
    felt252_to_m31_val value num_bits = felt252_to_m31_val' value num_bits := by
  simp [felt252_to_m31_val, felt252_to_m31_val']
  by_cases h : num_bits = 0
  . simp [h, Nat.div_ceil, FELT252_BITS_PER_WORD, felt252_to_m31_val.aux]
  simp [if_neg h]
  have h' : num_bits.div_ceil FELT252_BITS_PER_WORD ≠ 0 := by
    apply ne_of_gt; apply Nat.div_ceil_pos; omega
  generalize num_bits.div_ceil FELT252_BITS_PER_WORD = n at *
  cases' n with n; contradiction
  clear h'
  induction' n with n ih
  . simp [felt252_to_m31_val.aux, FELT252_BITS_PER_WORD]
  simp [felt252_to_m31_val.aux, ih, Finset.sum_range_succ, Nat.shiftLeft_eq]

def felt252_to_m31_val_alt (value : Felt252Words) (num_bits : Nat) : Felt :=
  if num_bits = 0 then value 0 else
    ∑ i : Fin FELT252_N_WORDS,
      if i.val < num_bits.div_ceil FELT252_BITS_PER_WORD then
        value i * (2 ^ (FELT252_BITS_PER_WORD * i.val))
      else 0

theorem felt252_to_m31_val_eq_val_alt (value : Felt252Words) (num_bits : Nat)
    (hle : num_bits.div_ceil FELT252_BITS_PER_WORD ≤ FELT252_N_WORDS) :
    felt252_to_m31_val value num_bits = felt252_to_m31_val_alt value num_bits := by
  simp [felt252_to_m31_val_eq_val', felt252_to_m31_val', felt252_to_m31_val_alt]
  by_cases h : num_bits = 0
  . simp [if_pos h]
  simp only [if_neg h]
  rw [←Finset.sum_indicator_subset _ (Finset.range_subset.mpr hle), Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos]; swap; simp_all
  simp [Set.indicator]
  split; swap; rfl
  next h' => congr; rw [Fin.eq_mk_iff_val_eq]; simp; exact lt_of_lt_of_le h' hle

-- Range checked values

theorem toFelt252_add_of_RangeChecked [Fact (Nat.Prime Stwo.P)]
    {x : Felt}
    (n : Nat)
    (h : IsRangeChecked 29 x)
    (h_n : 2^29 + n ≤ Stwo.P  - 2^29 -1) : --
    (x + n).toFelt252 = x.toFelt252 + n := by
  rcases h with ⟨nx, h_nx_lt, h_nx_eq⟩
  have : nx + n < Stwo.P - 2^29 - 1:= by
    apply lt_of_lt_of_le (add_lt_add_right h_nx_lt _) h_n
  convert toFelt252_add this

theorem toFelt252_add_one_of_RangeChecked [Fact (Nat.Prime Stwo.P)]
    {x : Felt} (h : IsRangeChecked 29 x) :
    (x + 1).toFelt252 = x.toFelt252 + 1 := by
  exact toFelt252_add_of_RangeChecked 1 h (by simp [Stwo.P])

theorem toFelt252_add_two_of_RangeChecked [Fact (Nat.Prime Stwo.P)]
    {x : Felt} (h : IsRangeChecked 29 x) :
    (x + 2).toFelt252 = x.toFelt252 + 2 := by
  exact toFelt252_add_of_RangeChecked 2 h (by simp [Stwo.P])

theorem toFelt252_RangeChecked_add_offset_eq [Fact (Nat.Prime Felt252Prime)]
    {x : Felt}
    {y : BitVec 16}
    (h_rc : IsRangeChecked 29 x) :
    (x + offset_as_signed_Felt y.toNat).toFelt252 = x.toFelt252 + intClip (int_from_Felt y.toNat) := by
  rcases h_rc with ⟨nx, h_nx_lt, h_x_eq⟩
  have h1 : ZMod.val (32768 : Felt) = 32768 := rfl
  have h2 : ZMod.val (536870912 +1 : Felt) = 536870913 := rfl
  have h2b : ZMod.val (536870913 : Felt) = 536870913 := rfl
  have h3 : ZMod.val (536838145 : Felt) = 536838145 := rfl
  norm_num at h_nx_lt

  unfold Felt.toFelt252
  rw [sub_add_eq_add_sub, sub_left_inj]
  unfold intClip natClip int_from_Felt int_from_u16 offset_as_signed_Felt OFFSET_BITS
  simp only [Nat.add_one_sub_one, Nat.reduceShiftLeft, Nat.cast_ofNat, Int.reducePow,
    sub_add_cancel, Int.toNat_natCast, Nat.reducePow]
  rw [h_x_eq]
  rw [Nat.mod_eq_of_lt _]
  rw [add_assoc, sub_add_eq_add_sub, add_sub_assoc, ←add_assoc]
  rw [ZMod.val_add_of_lt _, ZMod.val_add_of_lt _, ZMod.val_add_of_lt _]
  simp only [Nat.cast_add]
  conv_rhs => rw [add_assoc, ←add_sub_assoc] ; arg 2 ; rw [add_comm, add_sub_assoc]
  rw [←add_assoc]
  apply congr_arg
  rw [ZMod.val_sub, Nat.cast_sub] ; norm_num ; rfl

  -- The remaining inequalities and bounds

  · simp [Stwo.P] ; rw [h1, h2] ; norm_num
  · simp [Stwo.P] ; rw [h1, h2] ; norm_num
  · simp [Stwo.P]
    rw [h2b, ZMod.val_natCast_of_lt _]
    apply lt_trans (add_lt_add_right h_nx_lt _) ; norm_num
    apply lt_trans h_nx_lt ; norm_num
  · unfold Stwo.P
    rw [ZMod.val_natCast_of_lt _, ZMod.val_natCast_of_lt _]
    apply lt_trans (add_lt_add h_nx_lt (BitVec.isLt _)) ; norm_num
    apply lt_trans (BitVec.isLt _) ; norm_num
    apply lt_trans h_nx_lt ; norm_num
  · unfold Stwo.P
    norm_num
    rw [←Nat.cast_add, h3, ZMod.val_natCast_of_lt _]
    rw [Nat.add_lt_iff_lt_sub_right] ; norm_num
    apply lt_trans (add_lt_add h_nx_lt (BitVec.isLt _)) ; norm_num
    apply lt_trans (add_lt_add h_nx_lt (BitVec.isLt _)) ; norm_num
  rw [ZMod.val_natCast_of_lt _]
  exact (BitVec.isLt _)
  unfold Stwo.P
  apply lt_trans (BitVec.isLt _) ; norm_num

theorem toFelt252_add_offset_RangeChecked_eq [Fact (Nat.Prime Felt252Prime)]
    {x : Felt}
    {y : BitVec 16}
    (h_rc : IsRangeChecked 29 (x + offset_as_signed_Felt y.toNat)) :
    (x + offset_as_signed_Felt y.toNat).toFelt252 = x.toFelt252 + intClip (int_from_Felt y.toNat) := by

  have h252: (32768 : Felt252) = ((32768 : Nat) : Felt252) := by rfl
  have hfelt: (32768 : Felt) = ((32768 : Nat) : Felt) := by rfl

  rcases h_rc with ⟨nsum, h_nsum_lt, h_sum_eq⟩
  unfold offset_as_signed_Felt OFFSET_BITS at h_sum_eq
  simp only [Nat.add_one_sub_one, Nat.reduceShiftLeft, Nat.cast_ofNat] at h_sum_eq

  have h_xy : (x + ↑y.toNat).val < 2 ^ 29 + 2 ^ 29 := by
    have h_lt : ZMod.val (nsum : Felt) + ZMod.val ((32768 : Nat) : Felt) < 2 ^ 29 + 2 ^ 29 := by
      rw [ZMod.val_natCast_of_lt, ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
      linarith [h_nsum_lt]
      apply lt_trans h_nsum_lt ; unfold Stwo.P ; norm_num1
    rw [←add_sub_assoc, sub_eq_iff_eq_add] at h_sum_eq
    rw [h_sum_eq, hfelt, ZMod.val_add_of_lt]
    exact h_lt
    apply lt_trans h_lt ; unfold Stwo.P ; norm_num1

  have h_2_15_lt : 32768 ≤ (x + 536870913 + ↑y.toNat).val := by
    unfold Stwo.P
    have : ZMod.val (536870913 : Felt) = 536870913 := by
      apply ZMod.val_natCast_of_lt
      unfold Stwo.P
      norm_num
    rw [add_assoc, add_comm _ (y.toNat : Felt), ←add_assoc]
    rw [ZMod.val_add_of_lt]
    apply le_trans _ (Nat.le_add_left _ _)
    rw [this]
    norm_num1
    rw [this]
    apply lt_trans (Nat.add_lt_add_right h_xy _) ; norm_num1

  unfold Felt.toFelt252
  rw [sub_add_eq_add_sub, sub_left_inj]
  unfold intClip natClip int_from_Felt int_from_u16 offset_as_signed_Felt OFFSET_BITS
  simp only [Nat.add_one_sub_one, Nat.reduceShiftLeft, Nat.cast_ofNat, Int.reducePow,
    sub_add_cancel, Int.toNat_natCast, Nat.reducePow]
  norm_num1

  conv_lhs => rw [add_assoc] ; arg 1 ; arg 1 ; arg 2 ; rw [add_comm]
  rw [←add_assoc, ←add_sub_assoc, ←add_sub_assoc]
  rw [Nat.mod_eq_of_lt]
  rw [←Nat.cast_add, ←ZMod.val_add_of_lt]
  rw [h252, ←Nat.cast_sub, ZMod.val_sub, hfelt, ZMod.val_natCast_of_lt]

  · unfold Stwo.P ; norm_num
  · unfold Stwo.P
    rw [hfelt, ZMod.val_natCast_of_lt (by norm_num)]
    exact h_2_15_lt
  · exact h_2_15_lt
  . have h_y_lt' : y.toNat < 2^16 := BitVec.isLt y
    have h_y_lt'' : y.toNat < Stwo.P := by
      calc
        y.toNat < 2^16 := h_y_lt'
        _ ≤ Stwo.P := by
          unfold Stwo.P
          norm_num1

    have h_y_cast := ZMod.val_natCast_of_lt h_y_lt''

    have h_y_lt : (↑y.toNat : Felt).val < 2^16 := by
      unfold Stwo.P
      rw[h_y_cast]
      exact h_y_lt'

    have h_x_plus_lt : ((x + 536870913)).val < Stwo.P / 2 + 2 ^ 29 + 3 := by
      have h_sum_eq' : x = ↑nsum + 32768 - ↑y.toNat := by
        rw [eq_sub_iff_add_eq']
        rw [← h_sum_eq]
        ring_nf

      have htmp1: nsum < Stwo.P := by
        calc
          nsum < 2^29 := h_nsum_lt
          _ ≤ Stwo.P := by
            unfold Stwo.P
            norm_num1
      have h_val_nsum := ZMod.val_natCast_of_lt htmp1

      have h1 : ((↑nsum : Felt) + 32768).val = nsum + 32768 := by
        have : (↑nsum : Felt).val + (32768 : Felt).val < Stwo.P := by
          unfold Stwo.P
          rw[h_val_nsum]
          calc
            nsum + 32768 < 2^29 + 32768 := by
              exact Nat.add_lt_add_right h_nsum_lt 32768
            _ < Stwo.P := by
              unfold Stwo.P
              norm_num1
        rw [ZMod.val_add_of_lt this]
        rw[h_val_nsum]
        rfl

      by_cases htmp1 : nsum + 32768 ≥ y.toNat
      · have htmp2 : x.val < 2 ^ 29 + 2 ^ 29 := by
          have htmp3 : ZMod.val ((↑nsum : Felt) + 32768) ≥ (↑y.toNat : Felt).val := by
            rw[h1]
            rw[h_y_cast]
            exact htmp1
          calc
            x.val = ((↑nsum : Felt) + 32768 - (↑y.toNat : Felt)).val := by
              rw [h_sum_eq']
            _ = ((↑nsum : Felt) + 32768).val - (↑y.toNat : Felt).val := by
              rw [ZMod.val_sub htmp3]
            _ ≤ ((↑nsum : Felt) + 32768).val := by
              apply Nat.sub_le
            _ < 2 ^ 29 + 2 ^ 29 := by
              rw[h1]
              linarith[h_nsum_lt]

        have htmp3 : x.val + (536870913 : Felt).val < (Stwo.P / 2) + 2 ^ 29 + 3 := by--
          calc
            x.val + (536870913 : Felt).val < 2 ^ 29 + 2 ^ 29 + (536870913 : Felt).val := by
              exact add_lt_add_right htmp2 ((536870913 : Felt).val)
            _ = 2 ^ 29 + 2 ^ 29 + 536870913 := by
              rfl
            _ < (Stwo.P / 2) + 2 ^ 29 + 3 := by
              unfold Stwo.P
              norm_num1
        have : x.val + (536870913 : Felt).val < Stwo.P := by
          calc
            x.val + (536870913 : Felt).val < Stwo.P / 2 + 2 ^ 29 + 3 := htmp3
            _ ≤ Stwo.P := by
              unfold Stwo.P
              norm_num1
        rw [ZMod.val_add_of_lt this]
        exact htmp3

      · push_neg at htmp1

        have x_ne_zero : x ≠ 0 := by
          intro h0
          rw [h0] at h_sum_eq
          simp at h_sum_eq
          have : (↑y.toNat : Felt).val = ((↑nsum : Felt) + 32768).val := by
            rw [← h_sum_eq]
            ring_nf
          rw[h_y_cast, h1] at this
          rw[this] at htmp1
          linarith

        have x_ne_zero2 : NeZero x := NeZero.mk x_ne_zero


        have htmp2 : x.val > Stwo.P - 2^16 := by
          have htmp3 : ZMod.val ((↑nsum : Felt) + 32768) < (↑y.toNat : Felt).val := by
            rw[h1]
            rw[h_y_cast]
            exact htmp1

          calc
            x.val = Stwo.P - (-x).val := by
             rw[ZMod.val_neg_of_ne_zero x]
             rw[Nat.sub_sub_eq_min]
             rw[min_eq_right x.val_le]
            _ = Stwo.P - ((↑y.toNat : Felt) - ((↑nsum : Felt) + 32768) ).val := by
              rw[h_sum_eq']
              ring_nf
            _ = Stwo.P - ((↑y.toNat : Felt).val - ((↑nsum : Felt) + 32768).val) := by
              rw[ZMod.val_sub]
              exact le_of_lt htmp3
            _ = Stwo.P - (y.toNat - ((↑nsum : Felt) + 32768).val) := by
              rw[h_y_cast]
            _ ≥ Stwo.P - ↑y.toNat:= by
              apply ge_iff_le.mpr
              have : y.toNat - ZMod.val ((↑nsum : Felt) + 32768) ≤  y.toNat := by
                apply Nat.sub_le y.toNat
              exact Nat.sub_le_sub_left this Stwo.P
            _ > Stwo.P - 2^16 := by
              apply gt_iff_lt.mpr
              exact Nat.sub_lt_sub_left h_y_lt'' h_y_lt'

        rw[ZMod.val_add]
        have : ZMod.val (536870913 : Felt) = 536870913 := by
          apply ZMod.val_natCast_of_lt
          unfold Stwo.P
          norm_num1
        rw[this]

        let z := Stwo.P - x.val
        have h_z : x.val = Stwo.P - z := by
          unfold z
          rw[Nat.sub_sub_eq_min]
          rw[min_eq_right x.val_le]

        have h_z_lt : z < 2^16 := by
          unfold z
          calc
            Stwo.P - ZMod.val x < Stwo.P - (Stwo.P - 2 ^ 16) := Nat.sub_lt_sub_left (show Stwo.P - 2^16 < Stwo.P by unfold Stwo.P ; norm_num1) htmp2
            _ = 2^16 := by
              rw[Nat.sub_sub_eq_min]
              unfold Stwo.P
              norm_num

        have h_z_le2 : z ≤ 536870913 := by
          calc
            z ≤ 2^16 := le_of_lt h_z_lt
            _ ≤ 536870913 := by
              norm_num1

        have h_z_le : z ≤ Stwo.P := by
          unfold z
          apply Nat.sub_le

        rw[h_z]
        rw[← Nat.sub_add_comm h_z_le]
        rw[Nat.add_sub_assoc h_z_le2 Stwo.P]
        rw[Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
        unfold Stwo.P
        calc
          536870913 - z ≤ 536870913 := by
            apply Nat.sub_le
          _ < 2147483647 / 2 + 2 ^ 29 + 3 := by norm_num

        calc
          536870913 - z ≤ 536870913 := by
            apply Nat.sub_le
          _ < Stwo.P := by
            unfold Stwo.P
            norm_num

    calc
      ZMod.val (x + 536870913) + ZMod.val (↑y.toNat : Felt) < Stwo.P / 2 + 2 ^ 29 + 3 + 2 ^ 16 := by
        exact add_lt_add h_x_plus_lt h_y_lt
      _ ≤ Stwo.P := by
        unfold Stwo.P
        norm_num

  rw [ZMod.val_natCast_of_lt]
  linarith [BitVec.isLt y]
  unfold Stwo.P ; linarith [BitVec.isLt y]

lemma int_from_Felt_ge (n : Nat) : -2 ^ 15 ≤ int_from_Felt ↑n := by
  simp [int_from_Felt, int_from_u16, OFFSET_BITS]; apply Int.ofNat_zero_le

lemma int_from_Felt_BitVec16_lt (b : BitVec 16) : int_from_Felt b.toNat < 2^15 := by
  simp [int_from_Felt, int_from_u16, -ZMod.natCast_val, OFFSET_BITS, Stwo.P]
  rw [ZMod.val_cast_of_lt] <;> omega

theorem toFelt252_step_bounded_add_offset_eq [Fact (Nat.Prime Felt252Prime)]
    {x : Felt}
    {y : BitVec 16}
    {nx : Nat}
    {num_steps : Nat}
    (ns_lim : num_steps < 2^29) -- ≤ ?
    (h_x_eq: x = ↑nx)
    (h_nx_lt_pre : nx < 2 ^ 29 + num_steps) :
    (x + offset_as_signed_Felt y.toNat).toFelt252 = x.toFelt252 + intClip (int_from_Felt y.toNat) := by
  have aux : 1 <<< (OFFSET_BITS - 1) ≤ y.toNat + (2 ^ 29+1) := by
    rw [←Nat.sub_le_iff_le_add, OFFSET_BITS]; simp
  unfold Felt.toFelt252
  rw [h_x_eq, offset_as_signed_Felt, sub_add_eq_add_sub, sub_left_inj, ←Nat.cast_add, add_assoc,
    sub_add_eq_add_sub, ←Nat.cast_add, ←Nat.cast_sub aux, ←Nat.cast_add, ZMod.val_cast_of_lt,
    ZMod.val_cast_of_lt, Nat.cast_add, Nat.cast_sub aux, add_comm _ (2 ^ 29 +1), ←add_sub_assoc,
    Nat.cast_add, ←add_assoc, ←Nat.cast_add, add_sub_assoc, add_right_inj,
    intClip_eq (int_from_Felt_ge _) (int_from_Felt_BitVec16_lt _), int_from_Felt, int_from_u16,
    Int.cast_sub, ZMod.val_natCast_of_lt, Int.cast_natCast, Int.cast_natCast]
  all_goals { simp [OFFSET_BITS, Stwo.P]; omega }
  --

theorem toFelt252_add_of_step_bounded [Fact (Nat.Prime Stwo.P)]
    {x : Felt}
    {n : Nat}
    {nx : Nat}
    {num_steps : Nat}
    (ns_lim : num_steps < 2^29)--
    (h_x_eq: x = ↑nx)
    (h_nx_lt_pre : nx < 2 ^ 29 + num_steps) --
    (n_lim : n < 2^29) :
    (x + n).toFelt252 = x.toFelt252 + n := by
  have h_nx_lt_pre2 : nx ≤ (2 ^ 29 + num_steps) -1 := by
    apply Nat.lt_succ_iff.mp
    norm_num
    calc
      nx < 2 ^ 29 + num_steps := h_nx_lt_pre
      _ = 536870911 + num_steps +1 := by
        linarith
        --rw[add_assoc, ← add_comm _ num_steps, ← add_assoc]
  have : nx + n < Stwo.P - 2^29 -1 := by
    dsimp[Stwo.P]
    calc
      nx + n < 2^29 +nx := by
        linarith[n_lim]
      _ ≤ 2 ^ 29 + (2^29 + num_steps) -1 := by
        apply (Nat.le_pred_iff_lt (show (2 ^ 29 + (2^29 + num_steps) > 0) by linarith)).mpr
        linarith[h_nx_lt_pre2]
      _ ≤ 2 ^ 29 + ((2^29 + 2^29 - 1) - 1) := by
        simp
        linarith
      _ = 1610612734 := by norm_num
  convert toFelt252_add this
  --

theorem toFelt252_add_one_of_step_bounded [Fact (Nat.Prime Stwo.P)]
    {x : Felt}
    {nx : Nat}
    {num_steps : Nat}
    (ns_lim : num_steps < 2^29)
    (h_x_eq: x = ↑nx)
    (h_nx_lt_pre : nx < 2 ^ 29 + num_steps + 2) : -- (h_nx_lt_pre : nx < 2 ^ 29 + 2 * (num_steps - 1))
    (x + 1).toFelt252 = x.toFelt252 + 1 := by
  have : ↑nx + 1 < Stwo.P - 2^29 - 1 := by
    dsimp[Stwo.P]
    linarith[h_nx_lt_pre, ns_lim]
  have h := toFelt252_add this
  have cast1a: (↑(1:Nat): Felt) = 1 := by rfl
  have cast1b: (↑(1:Nat): Felt252) = 1 := by rfl
  rw[← h_x_eq, cast1a, cast1b] at h
  exact h

theorem toFelt252_add_two_of_step_bounded [Fact (Nat.Prime Stwo.P)]
    {x : Felt}
    {nx : Nat}
    {num_steps : Nat}
    (ns_lim : num_steps < 2^29)
    (h_x_eq: x = ↑nx)
    (h_nx_lt_pre : nx < 2 ^ 29 + num_steps) :
    (x + 2).toFelt252 = x.toFelt252 + 2 := by
  have : ↑nx + 2 < Stwo.P - 2^29 - 1 := by
    dsimp[Stwo.P]
    linarith[h_nx_lt_pre, ns_lim]
  have h := toFelt252_add this
  have cast1a: (↑(2:Nat): Felt) = 2 := by rfl
  have cast1b: (↑(2:Nat): Felt252) = 2 := by rfl
  rw[← h_x_eq, cast1a, cast1b] at h
  exact h


theorem Felt.fromNat_inj (a b : ℕ) : (a<2147483647) → (b<2147483647) → (a : Felt) = (b : Felt) → a = b := by
  intro ha hb h
  have char_eq : ringChar (ZMod Stwo.P) = Stwo.P  := ZMod.ringChar_zmod_n Stwo.P

  have a_lt_char : a < ringChar (ZMod Stwo.P) := by
    dsimp[Stwo.P] at *
    rwa[char_eq]

  have b_lt_char : b < ringChar (ZMod Stwo.P) := by
    dsimp[Stwo.P] at *
    rwa[char_eq]

  apply Nat.cast_inj_of_lt_char a_lt_char b_lt_char h
