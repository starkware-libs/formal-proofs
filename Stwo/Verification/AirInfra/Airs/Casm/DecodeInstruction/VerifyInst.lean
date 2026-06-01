import Verification.Semantics.Instruction
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.LookupTerm
import Verification.AirInfra.Core.Felt252IdMemory.Verify
import Verification.AirInfra.Airs.Casm.CasmState
import Verification.AirInfra.Airs.Casm.DecodeInstruction.EncodeOffsets
import Verification.AirInfra.Airs.Casm.DecodeInstruction.EncodeFlags

open Fin.NatCast

-- TODO(Jeremy): move this
def EncodesInstruction (felt252 : Felt252Words) (instruction : Instruction) : Prop :=
  instruction.toNat = (felt252 0).val + 2^9 * (felt252 1).val + 2^18 * (felt252 2).val + 2^27 * (felt252 3).val + 2^36 * (felt252 4).val + 2^45 * (felt252 5).val + 2^54 * (felt252 6).val ∧
  ∀ i : Fin FELT252_N_WORDS, i > 6 → felt252 i = 0

lemma EncodeInstruction_n_of_EncodeInstruction
    (felt252 : Felt252Words)
    (felt252n : Felt252Nats)
    (instruction : Instruction)
    (h : Felt252Nats.IsRangeChecked felt252n felt252) :
  EncodesInstruction felt252 instruction → instruction.toNat = felt252n.eval := by
  intro h_encode
  unfold EncodesInstruction at h_encode
  simp only [Felt252Nats.eq_val_of_IsRangeChecked felt252n felt252 h] at h_encode
  simp only [Felt252Nats.eq_zero_of_IsRangeChecked felt252n felt252 h] at h_encode
  rw [Felt252Nats.eval_eq_of_IsRangeChecked felt252n felt252 h]
  simp only [Felt252Nats.eq_val_of_IsRangeChecked felt252n felt252 h]
  simp only [h_encode]
  apply congr_arg
  rw [Finset.sum_fin_eq_sum_range]
  rw [(show Finset.range FELT252_N_WORDS = Finset.range (7 + (FELT252_N_WORDS - 7)) by norm_num1 ; rfl)]
  rw [Finset.sum_range_add]
  have h_zero : ∀ x, (h : 7 + x < FELT252_N_WORDS) → felt252n ⟨7 + x, h⟩ = 0 := by
    intro x h_x
    apply h_encode.2 ⟨7 + x, h_x⟩
    rw [gt_iff_lt, Fin.lt_iff_val_lt_val]
    simp only [Fin.isValue]
    apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
    -- TODO (Yoav): this is repeated below. Extract this as a lemma in utils.
    have val_x : ∀ x : Nat, x < 28 → @Fin.val 28 (@OfNat.ofNat (Fin 28) x Fin.instOfNat) = x := by
      intro x h_x ; simp [Fin.coe_ofNat_eq_mod]; apply Nat.mod_eq_of_lt ; apply lt_of_eq_of_lt _ h_x ; rfl
    rw [val_x 6 (by norm_num1)]
    norm_num1
  simp only [h_zero, zero_mul, dite_eq_ite, ite_self 0, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_range]
  have h_i_lt : ∀ i : Fin 7, (i : Nat) < FELT252_N_WORDS := by intro i ; apply lt_trans i.isLt ; norm_num1
  have h_if_pos : ∀ i : Fin 7,
    (if h : ↑i < FELT252_N_WORDS then felt252n ⟨↑i, h⟩ * 2 ^ (FELT252_BITS_PER_WORD * ↑i) else 0) =
    felt252n i * 2 ^ (FELT252_BITS_PER_WORD * i) := by
    intro i ; rw [dif_pos (h_i_lt i)]
    simp; congr
    have h_i_mod : ↑i % FELT252_N_WORDS = ↑i := Nat.mod_eq_of_lt (h_i_lt i)
    simp only [h_i_mod]
  simp only [h_if_pos]
  have val_x : ∀ x : Nat, x < 7 → @Fin.val 7 (@OfNat.ofNat (Fin 7) x Fin.instOfNat) = x := by
    intro x h_x ; simp  [Fin.coe_ofNat_eq_mod]; apply Nat.mod_eq_of_lt ; apply lt_of_eq_of_lt _ h_x ; rfl
  rw [Fin.sum_univ_seven]
  rw [val_x 0 (by norm_num1), val_x 1 (by norm_num1), val_x 2 (by norm_num1), val_x 3 (by norm_num1)]
  rw [val_x 4 (by norm_num1), val_x 5 (by norm_num1), val_x 6 (by norm_num1)]
  unfold FELT252_BITS_PER_WORD
  norm_num1 ; ring

-- TODO(Jeremy): move this
def Felt252IdMemoryAssign.HasInstruction
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress : CasmAddressVal)
    (instruction : Instruction) : Prop :=
  ∃ val : Felt252Words,
    memAssign.HasValue casmAddress val ∧
    EncodesInstruction val instruction

namespace VerifyInstruction

def call
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) :
    AirBuilder × AirLookupTerms :=
  let _state := EncodeOffsets.call airBuilder lookupTerms offset0 offset1 offset2
  let ab1 := _state.1
  let lt1 := _state.2.1
  let offset_felts := _state.2.2

  let _state := EncodeFlags.call ab1 flags
  let ab2 := _state.1
  let felt5_high := _state.2.1
  let felt6 := _state.2.2
  let felt5 := offset_felts 5 + felt5_high
  let expected_instruction : Felt252Expr := fun i => match i with
    | 0 => offset_felts 0
    | 1 => offset_felts 1
    | 2 => offset_felts 2
    | 3 => offset_felts 3
    | 4 => offset_felts 4
    | 5 => felt5
    | 6 => felt6
    | _ => FeltExpr.const 0
  let _state := MemVerify.call ab2 lt1 casmAddress expected_instruction
  let ab3 := _state.1
  let lt2 := _state.2
  (ab3, lt2)

def lookupSize := 19

def Lookup := LookupData lookupSize

instance : Membership (Fin lookupSize → FeltExpr) Lookup := by
  unfold Lookup; infer_instance

namespace Lookup

def add (lookup : Lookup) (val : Fin lookupSize → FeltExpr) : Lookup := LookupData.add lookup val

@[simp] theorem mem_add (v : Fin lookupSize → FeltExpr) (lookup : Lookup) (val : Fin lookupSize → FeltExpr) :
    v ∈ (lookup.add val) ↔ v ∈ lookup ∨ v = val:= by
  simp [Lookup.add]; rw [LookupData.mem_add]

end Lookup

def argsToLookup (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) : Fin lookupSize → FeltExpr :=
  Fin.append ![casmAddress, offset0, offset1, offset2] flags

theorem argsToLookup.ext_iff (c c' : CasmAddress) (o0 o1 o2 o0' o1' o2' : FeltExpr) (f f' : Fin 15 → FeltExpr) :
    argsToLookup c o0 o1 o2 f = argsToLookup c' o0' o1' o2' f' ↔
      c = c' ∧ o0 = o0' ∧ o1 = o1' ∧ o2 = o2' ∧ f = f' := by
  simp [argsToLookup]
  constructor; swap; simp_all
  intro h
  have hh := congr_fun (Fin.append_inj_left h)
  use hh 0, hh 1, hh 2, hh 3, Fin.append_inj_right h

@[simp] theorem eval_argsToLookup [Fact (Nat.Prime Stwo.P)]
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) :
  LookupData.eval (argsToLookup casmAddress offset0 offset1 offset2 flags) varAssign =
    Fin.append ![FeltExpr.eval varAssign casmAddress, FeltExpr.eval varAssign offset0, FeltExpr.eval varAssign offset1, FeltExpr.eval varAssign offset2]
      (fun i => FeltExpr.eval varAssign (flags i)) := by
  simp [argsToLookup]; rfl

def lookup_call
    (lookup : Lookup)
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) : Lookup :=
  lookup.add (argsToLookup casmAddress offset0 offset1 offset2 flags)

/-
structure Instruction where
  offDst : BitVec 16
  offOp0 : BitVec 16
  offOp1 : BitVec 16
  -- flags
  dstReg : Bool
  op0Reg : Bool
  op1Imm : Bool
  op1Fp : Bool
  op1Ap : Bool
  resAdd : Bool
  resMul : Bool
  pcJumpAbs : Bool
  pcJumpRel : Bool
  pcJnz : Bool
  apAdd : Bool
  apAdd1 : Bool
  opcodeCall : Bool
  opcodeRet : Bool
  opcodeAssertEq : Bool
  deriving DecidableEq
-/

def spec_auto
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress: CasmAddressVal)
    (offset0 offset1 offset2 : Felt)
    (flags : Fin 15 → Felt) : Prop :=
  memAssign.IsRangeChecked ∧
  ∃ encodedOffsets : Fin 6 → Felt,
    EncodeOffsets.spec offset0 offset1 offset2 encodedOffsets ∧
  ∃ felt5 felt6 : Felt,
    EncodeFlags.spec flags felt5 felt6 ∧
  MemVerify.spec memAssign casmAddress fun i =>
    match i with
      | 0 => encodedOffsets 0
      | 1 => encodedOffsets 1
      | 2 => encodedOffsets 2
      | 3 => encodedOffsets 3
      | 4 => encodedOffsets 4
      | 5 => encodedOffsets 5 + felt5
      | 6 => felt6
      | _ => 0

def spec
    (memAssign : Felt252IdMemoryAssign)
    (casmAddress: CasmAddressVal)
    (offset0 offset1 offset2 : Felt)
    (flags : Fin 15 → Felt) : Prop :=
  ∃ instruction : Instruction,
    memAssign.HasInstruction casmAddress instruction ∧
    offset0 = instruction.offDst.toNat ∧
    offset1 = instruction.offOp0.toNat ∧
    offset2 = instruction.offOp1.toNat ∧
    flags 0 = instruction.dstReg.toFelt ∧
    flags 1 = instruction.op0Reg.toFelt ∧
    flags 2 = instruction.op1Imm.toFelt ∧
    flags 3 = instruction.op1Fp.toFelt ∧
    flags 4 = instruction.op1Ap.toFelt ∧
    flags 5 = instruction.resAdd.toFelt ∧
    flags 6 = instruction.resMul.toFelt ∧
    flags 7 = instruction.pcJumpAbs.toFelt ∧
    flags 8 = instruction.pcJumpRel.toFelt ∧
    flags 9 = instruction.pcJnz.toFelt ∧
    flags 10 = instruction.apAdd.toFelt ∧
    flags 11 = instruction.apAdd1.toFelt ∧
    flags 12 = instruction.opcodeCall.toFelt ∧
    flags 13 = instruction.opcodeRet.toFelt ∧
    flags 14 = instruction.opcodeAssertEq.toFelt

lemma ZMod.StwoP_val_bif (b : Bool) :
    ZMod.val (bif b then (1 : ZMod Stwo.P) else 0) = bif b then 1 else 0 := by
  cases b <;> simp; rfl

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    {memAssign : Felt252IdMemoryAssign}
    {casmAddress: CasmAddressVal}
    {offset0 offset1 offset2 : Felt}
    {flags : Fin 15 → Felt}
    (h_spec_auto : spec_auto memAssign casmAddress offset0 offset1 offset2 flags) :
    spec memAssign casmAddress offset0 offset1 offset2 flags := by
  rcases h_spec_auto with ⟨memAssign_rc, encodedOffsets, h_EncodeOffsets, felt5, felt6, h_EncodeFlags, h_MemVerify⟩
  rcases memAssign.IsRangeChecked_of_HasValue memAssign_rc h_MemVerify with ⟨value_n, hvalue_n⟩
  rcases h_EncodeFlags with ⟨flagsb, h_flagsb, felt5_eq, felt6_eq⟩
  have rc0 : IsRangeChecked 9 (encodedOffsets 0) := by
    use value_n 0
    have := hvalue_n 0
    use this.2, this.1
  have rc2 : IsRangeChecked 9 (encodedOffsets 2) := by
    use value_n 2
    have := hvalue_n 2
    use this.2, this.1
  have rc4 : IsRangeChecked 9 (encodedOffsets 4) := by
    use value_n 4
    have := hvalue_n 4
    use this.2, this.1
  rcases h_EncodeOffsets rc0 rc2 rc4 with ⟨low0, mid0, low1, mid1, high1, low2, mid2, high2, offset0_eq,
    offset1_eq, offset2_eq, encodedOffsets_eq⟩
  let instruction : Instruction := {
    offDst := mid0 ++ low0
    offOp0 := high1 ++ mid1 ++ low1
    offOp1 := high2 ++ mid2 ++ low2
    dstReg := flagsb 0
    op0Reg := flagsb 1
    op1Imm := flagsb 2
    op1Fp := flagsb 3
    op1Ap := flagsb 4
    resAdd := flagsb 5
    resMul := flagsb 6
    pcJumpAbs := flagsb 7
    pcJumpRel := flagsb 8
    pcJnz := flagsb 9
    apAdd := flagsb 10
    apAdd1 := flagsb 11
    opcodeCall := flagsb 12
    opcodeRet := flagsb 13
    opcodeAssertEq := flagsb 14 }
  rw [MemVerify.spec] at h_MemVerify
  use instruction
  unfold Felt252IdMemoryAssign.HasInstruction
  have haux : ∑ x ∈ Finset.range 6, ↑(bif flagsb ↑x then 1 else 0) * ↑(2 ^ (x + 3)) ≤ 1 * 2^3 + 1 * 2^4 + 1 * 2^5 +
    1 * 2^6 + 1 * 2^7 + 1 * 2^8 := by
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      Fin.isValue, zero_add, Nat.cast_one, Nat.reduceAdd, Nat.cast_ofNat]
    gcongr <;> apply bif_one_zero_le
  have : 281474976710656 * (BitVec.ofBoolListLE
          [flagsb 0, flagsb 1, flagsb 2, flagsb 3, flagsb 4, flagsb 5, flagsb 6, flagsb 7, flagsb 8, flagsb 9,
            flagsb 10, flagsb 11, flagsb 12, flagsb 13, flagsb 14]).toNat =
    (35184372088832 * ZMod.val (n := Stwo.P) (∑ x ∈ Finset.range 6, ↑(bif flagsb ↑x then 1 else 0 : ℕ) * 2 ^ (x + 3)) +
                    18014398509481984 *
                      ZMod.val (n := Stwo.P) (∑ x ∈ Finset.range 9, ↑(bif flagsb (↑x + 6) then 1 else 0 : ℕ) * 2 ^ x)) := by
    simp only [Fin.isValue, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofBoolListLE,
      BitVec.toNat_concat, BitVec.toNat_ofNat, pow_zero, Nat.zero_mod, zero_mul, Bool.toNat,
      zero_add, Finset.range_succ, Finset.range_zero, insert_empty_eq, cast_bif, Finset.mem_insert,
      Nat.succ_ne_self, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, Nat.cast_ofNat,
      one_ne_zero, Nat.cast_one, Finset.sum_singleton, Nat.cast_zero, ZMod.val_add, ZMod.val_mul,
      ZMod.StwoP_val_bif, Nat.add_mod_mod, Nat.mod_add_mod, Fin.reduceAdd, pow_one, mul_one]
    norm_num
    simp only [Fin.isValue, Stwo.P, ZMod.val_ofNat, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . ring
    . apply lt_of_le_of_lt (b := 1 * 256 + (1 * 128 + (1 * 64 + (1 * 32 + (1 * 16 + (1 * 8 + (1 * 4 + (1 * 2 + 1 * 1)))))))) _ (by norm_num)
      gcongr <;> apply bif_one_zero_le
    . apply lt_of_le_of_lt (b := 1 * 256 + (1 * 128 + (1 * 64 + (1 * 32 + (1 * 16 + 1 * 8))))) _ (by norm_num)
      gcongr <;> apply bif_one_zero_le
  constructor
  . refine ⟨_, h_MemVerify, ?_⟩
    unfold EncodesInstruction; simp [encodedOffsets_eq]
    constructor
    . simp [felt5_eq, felt6_eq, instruction, Instruction.toNat, Instruction.flags]
      simp only [Nat.shiftLeft_eq, one_mul]
      rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^9), ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt low0)]
      rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^2), ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt low1)]
      rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^9), ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt mid1)]
      rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^4), ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt low2)]
      rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm _ (2^9), ←Nat.two_pow_add_eq_or_of_lt (BitVec.isLt mid2)]
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt low0) (by simp [Stwo.P])
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
      rw [BitVec.toNat_append']
      rw [BitVec.toNat_append']
      rw [ZMod.val_add, Nat.mod_eq_of_lt]; swap
      . rw [ZMod.val_natCast_of_lt]; swap
        . apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
        simp only [←Nat.cast_mul]
        rw [←Nat.cast_sum]
        rw [ZMod.val_natCast_of_lt]; swap
        . apply lt_of_le_of_lt haux
          simp [Stwo.P]
        apply lt_of_lt_of_le
        apply add_lt_add_of_lt_of_le (BitVec.isLt _) haux
        simp [Stwo.P]
      rw [ZMod.val_cast_of_lt]; swap;
        apply lt_of_lt_of_le (BitVec.isLt _) (by simp [Stwo.P])
      simp [mul_add, add_assoc]
      rw [this]
      ring
    . intro i
      fin_cases i <;> simp [Fin.lt_def, Fin.coe_ofNat_eq_mod, FELT252_N_WORDS]
  simp [instruction, offset0_eq, offset1_eq, offset2_eq, h_flagsb, Bool.toFelt, cast_bif]

theorem sound_auto [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
    (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) :
    let ⟨new_ab, new_lt⟩ := call ab lt casmAddress offset0 offset1 offset2 flags
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign
        (casmAddress.eval varAssign)
        (offset0.eval varAssign)
        (offset1.eval varAssign)
        (offset2.eval varAssign)
        (fun i => (flags i).eval varAssign) := by
  unfold call ; lift_lets
  intro state1 ab1 lt1 offset_felts state2 ab2 felt5_high felt6 felt5 expected_instruction state3 ab3 lt2

  intro hab3 hlt2
  have ⟨hab2, hlt1, h_mem_verify⟩ := MemVerify.sound_auto _ memAssign _ _ _ h_mem.1 _ _ hab3 hlt2
  have ⟨hab1, h_flags⟩ := EncodeFlags.sound_auto _ _ _ hab2
  have ⟨hab, hlt, h_offsets⟩ := EncodeOffsets.sound_auto _ _ _ _ h_rc _ _ _ hab1 hlt1

  use hab, hlt
  apply spec_of_spec_auto

  use AirLookupTerms.mem_isRangeChecked_of_agree_and_range_checked _ _ h_rc h_mem
  use (fun i => (offset_felts i).eval varAssign), h_offsets
  refine ⟨_, _, h_flags, ?_⟩
  convert h_mem_verify using 1
  unfold Felt252Expr.eval
  dsimp [Felt252Words]
  ext i
  split <;> try {rfl}
  simp [expected_instruction]

/-
Semantics
-/

def verifyInstrTuple
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr)
    : Fin (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1) → FeltExpr :=
  (Fin.append ![casmAddress, offset0, offset1, offset2] flags) ∘ Fin.cast (by simp ; rfl)

def verifyInstrUseTerm
    (casmAddress : CasmAddress)
    (offset0 offset1 offset2 : FeltExpr)
    (flags : Fin 15 → FeltExpr) : LookupTerm rel_lengths := {
  rel := VERIFY_INSTR_REL_INDEX
  tuple := p_tuple_expr VERIFY_INSTR_REL_INDEX (verifyInstrTuple casmAddress offset0 offset1 offset2 flags)
  useOrYield := .use
}

lemma address_of_verifyInstrTuple
      (casmAddress : CasmAddress)
      (offset0 offset1 offset2 : FeltExpr)
      (flags : Fin 15 → FeltExpr) :
    verifyInstrTuple casmAddress offset0 offset1 offset2 flags 0 = casmAddress := by
  rfl

lemma verifyInstrTuple_eval_inj [Fact (Nat.Prime Stwo.P)]
      {casmAddress₁ : CasmAddress} {offset0₁ offset1₁ offset2₁ : FeltExpr} {flags₁ : Fin 15 → FeltExpr} {varAssign₁ : VarAssign}
      {casmAddress₂ : CasmAddress} {offset0₂ offset1₂ offset2₂ : FeltExpr} {flags₂ : Fin 15 → FeltExpr} {varAssign₂ : VarAssign}
      (h : (fun i => FeltExpr.eval varAssign₁ (verifyInstrTuple casmAddress₁ offset0₁ offset1₁ offset2₁ flags₁ i)) =
              fun i => FeltExpr.eval varAssign₂ (verifyInstrTuple casmAddress₂ offset0₂ offset1₂ offset2₂ flags₂ i)) :
    casmAddress₁.eval varAssign₁ = casmAddress₂.eval varAssign₂
    ∧ offset0₁.eval varAssign₁ = offset0₂.eval varAssign₂
    ∧ offset1₁.eval varAssign₁ = offset1₂.eval varAssign₂
    ∧ offset2₁.eval varAssign₁ = offset2₂.eval varAssign₂
    ∧ (fun i => (flags₁ i).eval varAssign₁) = (fun i => (flags₂ i).eval varAssign₂) := by
  unfold verifyInstrTuple at h
  use congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3
  funext i
  have h_flags := congrFun h (Fin.natAdd 4 i)
  simp at h_flags
  exact h_flags

lemma verifyInstrTuple_embed_eval_inj [Fact (Nat.Prime Stwo.P)]
      {casmAddress₁ : CasmAddress} {offset0₁ offset1₁ offset2₁ : FeltExpr} {flags₁ : Fin 15 → FeltExpr} {varAssign₁ : VarAssign}
      {casmAddress₂ : CasmAddress} {offset0₂ offset1₂ offset2₂ : FeltExpr} {flags₂ : Fin 15 → FeltExpr} {varAssign₂ : VarAssign}
      (h : (fun i =>
              FeltExpr.eval varAssign₁
                (p_tuple_expr VERIFY_INSTR_REL_INDEX (verifyInstrTuple casmAddress₁ offset0₁ offset1₁ offset2₁ flags₁) i)) =
            fun i =>
              FeltExpr.eval varAssign₂
                (p_tuple_expr VERIFY_INSTR_REL_INDEX (verifyInstrTuple casmAddress₂ offset0₂ offset1₂ offset2₂ flags₂) i)) :
    casmAddress₁.eval varAssign₁ = casmAddress₂.eval varAssign₂
    ∧ offset0₁.eval varAssign₁ = offset0₂.eval varAssign₂
    ∧ offset1₁.eval varAssign₁ = offset1₂.eval varAssign₂
    ∧ offset2₁.eval varAssign₁ = offset2₂.eval varAssign₂
    ∧ (fun i => (flags₁ i).eval varAssign₁) = (fun i => (flags₂ i).eval varAssign₂) := by
  apply verifyInstrTuple_eval_inj
  simp only [p_tuple_eval] at h
  apply p_tuple_inj h

lemma tuple_eq_verifyInstrTuple
      (tuple : Fin (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1) → FeltExpr) :
    tuple = verifyInstrTuple (tuple 0) (tuple 1) (tuple 2) (tuple 3) (fun (i : Fin 15) => tuple (Fin.natAdd 4 i)) := by
  unfold verifyInstrTuple
  exact List.ofFn_inj.mp rfl

lemma NoYieldTerms_of_call
      {ab : AirBuilder}
      {lt : AirLookupTerms}
      (h : AirLookupTerms.NoYieldTerms lt)
      {casmAddress : CasmAddress}
      {offset0 offset1 offset2 : FeltExpr}
      {flags : Fin 15 → FeltExpr} :
    AirLookupTerms.NoYieldTerms (call ab lt casmAddress offset0 offset1 offset2 flags).2 := by
  unfold call
  apply MemVerify.NoYieldTerms_of_call
  apply EncodeOffsets.NoYieldTerms_of_call
  exact h

/-
  Lookup call function for the verify instruction component.

  Creates an empty AIR builder and an empty lookup term list, deduces the input expressions
  and call the verify instruction AIR function.
-/

def LookupCall [Fact (Nat.Prime Stwo.P)] : AirBuilder × AirLookupTerms :=
    let _state := AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)
    let ab1 := _state.1
    let input := _state.2
    let h_lt : 15 ≤ rel_lengths VERIFY_INSTR_REL_INDEX + 1 := by
      simp [VERIFY_INSTR_REL_INDEX, rel_lengths] ; exact Nat.le_of_ble_eq_true rfl
    let _state := call ab1 AirLookupTerms.empty (input 0) (input 1) (input 2) (input 3)
                          (fun (i : Fin 15) => input (i.castLE h_lt + 4))
    let ab2 := _state.1
    let lt1 := _state.2
    let lt2 := lt1.add VERIFY_INSTR_REL_INDEX (p_tuple_expr VERIFY_INSTR_REL_INDEX input) .yield
    (ab2, lt2)

lemma lookupCall_yield_term [Fact (Nat.Prime Stwo.P)] :
    ∀ t ∈ LookupCall.2, t.useOrYield = .yield →
      t = {
          rel := VERIFY_INSTR_REL_INDEX,
          tuple := (p_tuple_expr VERIFY_INSTR_REL_INDEX (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).2),
          useOrYield := .yield
      } := by
  intro t h_t h_yield
  rw [LookupCall, ←AirLookupTerms.add'_eq_add] at h_t
  apply Or.resolve_left (AirLookupTerms.mem_add' t h_t)
  apply AirLookupTerms.yield_not_mem_NoYieldTerms h_yield
  apply NoYieldTerms_of_call
  apply AirLookupTerms.empty_NoYieldTerms

lemma empty_push_eq_singleton {a : AirLookupTerms} {x : LookupTerm rel_lengths} : a = #[] → a.push x = #[x] := by
    intro h_a ; simp [h_a]

lemma lookupCall_yield_term_filter [Fact (Nat.Prime Stwo.P)] :
    LookupCall.2.filter (fun t => t.useOrYield = .yield) =
      #[{
          rel := VERIFY_INSTR_REL_INDEX,
          tuple := p_tuple_expr VERIFY_INSTR_REL_INDEX (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).2,
          useOrYield := .yield
      }] := by
  --intro t h_t h_yield
  rw [LookupCall, AirLookupTerms.add, Array.filter_push]
  simp
  have h {a : AirLookupTerms} {x : LookupTerm rel_lengths} : a = #[] → a.push x = #[x] := by
    intro h_a ; simp [h_a]
  apply empty_push_eq_singleton
  rw [Array.filter_eq_empty_iff]
  intro t h_t_mem
  rw [decide_eq_true_eq]
  intro h_yield
  apply AirLookupTerms.yield_not_mem_NoYieldTerms h_yield _ h_t_mem
  apply NoYieldTerms_of_call
  apply AirLookupTerms.empty_NoYieldTerms

lemma lookupCall_yield_term_filter_eq [Fact (Nat.Prime Stwo.P)] :
    LookupCall.2.filter (fun t => t.useOrYield = .yield) =
      LookupCall.2.filter (fun t => t.rel = VERIFY_INSTR_REL_INDEX ∧ t.useOrYield = .yield) := by
  simp only [Bool.decide_and, ←Array.filter_filter]
  simp only [lookupCall_yield_term_filter]
  rw [Eq.comm]
  apply Array.filter_eq_self.mpr
  intro t h_t
  rw [Array.mem_singleton] at h_t
  simp [h_t]

lemma lookupCall_yield_term_filter' [Fact (Nat.Prime Stwo.P)] :
    LookupCall.2.filter (fun t => decide (t.rel = VERIFY_INSTR_REL_INDEX ∧ t.useOrYield = .yield)) =
      #[{
          rel := VERIFY_INSTR_REL_INDEX,
          tuple := p_tuple_expr VERIFY_INSTR_REL_INDEX (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).2,
          useOrYield := .yield
      }] := by
  rw [←lookupCall_yield_term_filter_eq]
  exact lookupCall_yield_term_filter

lemma lookupCall_input_agrees [Fact (Nat.Prime Stwo.P)] :
    ∀ t ∈ LookupCall.2, (t.useOrYield = .yield) →
        ∃ (h : t.rel = VERIFY_INSTR_REL_INDEX)
          (casmAddress : CasmAddress) (offset0 offset1 offset2 : FeltExpr) (flags : Fin 15 → FeltExpr),
          t.tuple = (p_tuple_expr VERIFY_INSTR_REL_INDEX (verifyInstrTuple casmAddress offset0 offset1 offset2 flags)) ∘ Fin.cast (by simp [h, rel_lengths])  ∧
          LookupCall.1 = (call (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).1 AirLookupTerms.empty
                                casmAddress offset0 offset1 offset2 flags).1 ∧
          LookupCall.2 = (call (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).1 AirLookupTerms.empty
                                casmAddress offset0 offset1 offset2 flags).2.add
                                  VERIFY_INSTR_REL_INDEX
                                  (p_tuple_expr VERIFY_INSTR_REL_INDEX  (verifyInstrTuple casmAddress offset0 offset1 offset2 flags))
                                  .yield := by
  intro t h_t h_yield
  have h_t_eq := lookupCall_yield_term t h_t h_yield
  use (show t.rel = VERIFY_INSTR_REL_INDEX by subst h_t_eq ; rfl)
  let tuple := (AirBuilder.empty.deduceN (raw_rel_lengths VERIFY_INSTR_REL_INDEX + 1)).2
  use tuple 0, tuple 1, tuple 2, tuple 3, (fun (i : Fin 15) => tuple (Fin.natAdd 4 i))
  constructor
  · subst h_t_eq
    simp only ; congr
    rw [←tuple_eq_verifyInstrTuple tuple]
  constructor
  · rfl
  unfold LookupCall ; simp
  congr 1
  unfold verifyInstrTuple
  exact List.ofFn_inj.mp rfl


end VerifyInstruction

namespace AirLookupTerms

protected def add_verify_instr
      (terms : AirLookupTerms)
      (casmAddress : CasmAddress)
      (offset0 offset1 offset2 : FeltExpr)
      (flags : Fin 15 → FeltExpr) :
  AirLookupTerms :=
    terms.add
      VERIFY_INSTR_REL_INDEX
      (p_tuple_expr VERIFY_INSTR_REL_INDEX (VerifyInstruction.verifyInstrTuple casmAddress offset0 offset1 offset2 flags))
      .use

-- Assume that every yield tuple for the verify instruction relation is the result of the evaluation
-- of an assignment on the input of the verify instruction component.

def VerifyInstrYieldAgrees [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
    {values : LookupValues t n_s NUM_PARTITIONS}
    {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
    (lookups : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))) : Prop :=
  ∀ t ∈ yield_tuples (lookups VERIFY_INSTR_REL_INDEX),
    ∃ term ∈ VerifyInstruction.LookupCall.2,
      ∃ (h_rel : term.rel = VERIFY_INSTR_REL_INDEX),
      term.useOrYield = .yield ∧
      ∃ (varAssign : VarAssign),
        VerifyInstruction.LookupCall.1.SatisfiedBy varAssign ∧
        VerifyInstruction.LookupCall.2.UseAgree varAssign values partitions lookups ∧
        t = (fun i : Fin (rel_lengths VERIFY_INSTR_REL_INDEX + 1) => ((term.tuple (Fin.cast (by rw [←h_rel]) i))).eval varAssign)

lemma add_verify_instr_SatisfiedBy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {casmAddress : CasmAddress}
      {offset0 offset1 offset2 : FeltExpr}
      {flags : Fin 15 → FeltExpr}
      {varAssign : VarAssign}
      {memAssign : Felt252IdMemoryAssign}
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_yield : VerifyInstrYieldAgrees h_satisfied.tuples)
      (h_agrees : UseAgrees (VerifyInstruction.verifyInstrUseTerm casmAddress offset0 offset1 offset2 flags)
                    varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples) :
    VerifyInstruction.spec memAssign
        (casmAddress.eval varAssign)
        (offset0.eval varAssign)
        (offset1.eval varAssign)
        (offset2.eval varAssign)
        (fun i => (flags i).eval varAssign) := by
  rcases mem_yield_of_mem_use h_satisfied VERIFY_INSTR_REL_INDEX verify_instr_not_chain_rel
            (fun i => (p_tuple_expr VERIFY_INSTR_REL_INDEX (VerifyInstruction.verifyInstrTuple casmAddress offset0 offset1 offset2 flags) i).eval varAssign)
            (h_agrees rfl) with
    ⟨y, h_y_mem, h_eq⟩
  rcases h_yield y h_y_mem with ⟨y_term, h_t_mem, h_rel, h_t_yield, y_varAssign, h_ab, h_lt, h_y_t_eq⟩
  rcases VerifyInstruction.lookupCall_input_agrees y_term h_t_mem h_t_yield with
    ⟨h_rel', y_addr, y_off0, y_off1, y_off2, y_flags, h_t_eq, h_ab_eq, h_lt_eq⟩
  rw [h_ab_eq] at h_ab
  rw [h_lt_eq] at h_lt
  replace h_lt := (UseAgree_add.mp h_lt).2
  simp only [h_t_eq] at h_y_t_eq
  simp only [h_y_t_eq] at h_eq
  rcases VerifyInstruction.verifyInstrTuple_embed_eval_inj h_eq with ⟨h_addr, h_off0, h_off1, h_off2, h_flags⟩
  rw [h_addr, h_off0, h_off1, h_off2, h_flags]
  exact (VerifyInstruction.sound_auto _ memAssign _ _ _ h_rc h_mem _ _ _ _ _ h_ab h_lt).2.2

lemma add_verify_instr_sound [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      (terms : AirLookupTerms)
      (varAssign : VarAssign)
      (memAssign : Felt252IdMemoryAssign)
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_yield : VerifyInstrYieldAgrees h_satisfied.tuples)
      (casmAddress : CasmAddress)
      (offset0 offset1 offset2 : FeltExpr)
      (flags : Fin 15 → FeltExpr) :
    UseAgree (terms.add_verify_instr casmAddress offset0 offset1 offset2 flags) varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      VerifyInstruction.spec memAssign
        (casmAddress.eval varAssign)
        (offset0.eval varAssign)
        (offset1.eval varAssign)
        (offset2.eval varAssign)
        (fun i => (flags i).eval varAssign)
      ∧ UseAgree terms varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
    intro h
    have h_agree := UseAgree_add.mp h
    simp_all only [and_true]
    apply add_verify_instr_SatisfiedBy h_satisfied h_rc h_mem h_yield h_agree.1

end AirLookupTerms
