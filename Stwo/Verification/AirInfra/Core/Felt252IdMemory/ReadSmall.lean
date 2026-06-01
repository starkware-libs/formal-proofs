--import Mathlib.Tactic.AssocRw
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Airs.Casm.CasmState
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.Felt252IdMemory.Memory

set_option maxHeartbeats 800000

/-
// The number of limbs that fit in an M31. When reading a "small" value into an M31
// we'll deduce that many limbs.
pub const LIMBS_IN_M31: usize = 3;
-/

def LIMBS_IN_M31 := 4

/-
// 9-bit limbs
//  limb ->   27  26  25  24  23  22  21  20  19 ...   5   4   3   2   1   0
// value
// 2 (+P)  0x100 000 000 000 000 000 088 000 000 ... 000 000 000 000 000 003
// 1 (+P)  0x100 000 000 000 000 000 088 000 000 ... 000 000 000 000 000 002
// 0 (+P)  0x100 000 000 000 000 000 088 000 000 ... 000 000 000 000 000 001
// 2       0x000 000 000 000 000 000 000 000 000 ... 000 000 000 000 000 002
// 1       0x000 000 000 000 000 000 000 000 000 ... 000 000 000 000 000 001
// 0       0x000 000 000 000 000 000 000 000 000 ... 000 000 000 000 000 000
// -1      0x100 000 000 000 000 000 088 000 000 ... 000 000 000 000 000 000
// -2      0x100 000 000 000 000 000 087 1ff 1ff ... 1ff 1ff 1ff 1ff 1ff 1ff
// -3      0x100 000 000 000 000 000 087 1ff 1ff ... 1ff 1ff 1ff 1ff 1ff 1fe
-/

-- Note: P = 2^251 + 17*2^192 + 1



-- `value` is not needed for soundness

namespace DecodeSmallSign -- local to this file?

def call -- no Felt252Expr input?
    (airBuilder : AirBuilder) :
    AirBuilder × FeltExpr × FeltExpr :=
  let (ab1, msb) := airBuilder.deduce
  let (ab2, mid_limbs_set) := ab1.deduce
  let ab3 := ab2.constrain (msb * (msb - FeltExpr.const 1))
  let ab4 := ab3.constrain (mid_limbs_set * (mid_limbs_set - FeltExpr.const 1))
  let ab5 := ab4.constrain (mid_limbs_set * (msb - FeltExpr.const 1))
  (ab5, msb, mid_limbs_set)

def spec_auto (msb mid_limbs_set : Felt) : Prop :=
  msb * (msb - 1) = 0 ∧
  mid_limbs_set * (mid_limbs_set - 1) = 0 ∧
  mid_limbs_set * (msb - 1) = 0

def spec (msb mid_limbs_set : Felt) : Prop :=
  (msb = 0 ∨ msb = 1) ∧
  (mid_limbs_set = 0 ∨ mid_limbs_set = 1) ∧
  (mid_limbs_set = 0 ∨ msb = 1)

variable [Fact (Nat.Prime Stwo.P)]

theorem sound {msb mid_limbs_set : Felt}
    (hspec : spec_auto msb mid_limbs_set) :
    spec msb mid_limbs_set := by
  simpa [spec_auto, mul_eq_zero, sub_eq_zero, or_assoc] using hspec

theorem sound_auto {varAssign : VarAssign} {ab : AirBuilder}:
    let ⟨newAirBuilder, msb, mid_limbs_set⟩ := call ab
    newAirBuilder.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (msb.eval varAssign) (mid_limbs_set.eval varAssign) := by
  simp only [call, AirBuilder.constrain_SatisfiedBy, AirBuilder.deduce_SatisfiedBy,
    FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const _ 1, and_imp]
  intro h1 h2 h3 h4
  use h1
  apply sound
  use h2, h3, h4

end DecodeSmallSign



namespace CondRangeCheck2

def call
    (airBuilder : AirBuilder)
    (msl condition : FeltExpr) :
    AirBuilder :=
    let (ab1, mslh) := airBuilder.deduce
    let ab2 := ab1.constrain (mslh * (FeltExpr.const 1 - mslh) * condition)
    let msll := msl - (mslh * FeltExpr.const 2)
    let ab3 := ab2.constrain (msll * (FeltExpr.const 1 - msll) * condition)
    ab3

def spec_auto (msl condition : Felt) : Prop :=
  ∃ mslh : Felt,
  mslh * (1 - mslh) * condition = 0 ∧ (msl - 2*mslh) * (1 - (msl - 2*mslh) ) * condition = 0

def spec (msl condition : Felt) : Prop :=
  (condition = 0) ∨ (msl.val < 4)

variable [Fact (Nat.Prime Stwo.P)]

theorem sound {msl condition : Felt} --  spec_of_spec_auto
    (hspec : spec_auto msl condition) :
    spec msl condition := by
  unfold spec
  by_cases h: (condition = 0)
  · left; exact h
  right
  unfold spec_auto at hspec
  rcases hspec with ⟨mslh, h1, h2⟩
  have h3_pre := mul_eq_zero.mp h1
  have h4_pre := mul_eq_zero.mp h2
  cases h3_pre <;> rename _ => h3 <;> cases h4_pre <;> rename _ => h4
  · have mslh_val : mslh.val ≤ 1 := by
      cases mul_eq_zero.mp h3 <;> rename _ => h5
      · rw [h5]
        simp
      · have : mslh = 1 := by
          have := sub_eq_zero.mp h5
          rw[this]
        rw[this]
        calc
          ZMod.val 1 = 1 := by
            apply ZMod.val_one
          _ ≤ 1 := by rfl
    have msll_val : (msl - 2 * mslh).val ≤ 1 := by
      cases mul_eq_zero.mp h4 <;> rename _ => h5
      · rw [h5]
        simp
      · have : msl - 2 * mslh = 1 := by
          have := sub_eq_zero.mp h5
          rw[this]
        rw[this]
        calc
          ZMod.val 1 = 1 := by
            apply ZMod.val_one
          _ ≤ 1 := by rfl
    calc
      msl.val = (2 * mslh + (msl - 2 * mslh)).val := by
        ring_nf
      _ ≤ (2 * mslh).val + (msl - 2 * mslh).val := by
        apply ZMod.val_add_le
      _ = (mslh + mslh).val + (msl - 2 * mslh).val := by
        ring_nf
      _ ≤ mslh.val + mslh.val + (msl - 2 * mslh).val := by
        apply add_le_add_right
        apply ZMod.val_add_le
      _ < 4 := by
        linarith
  · exfalso
    rw [h4] at h
    exact h rfl
  · exfalso
    rw [h3] at h
    exact h rfl
  · exfalso
    rw [h3] at h
    exact h rfl

theorem sound_auto {varAssign : VarAssign} {ab : AirBuilder} {msl condition : FeltExpr}:
    let newAirBuilder := call ab msl condition
    newAirBuilder.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (msl.eval varAssign) (condition.eval varAssign) := by

    simp only [call, AirBuilder.constrain_SatisfiedBy, AirBuilder.deduce_SatisfiedBy,
      FeltExpr.eval_mul, FeltExpr.eval_sub, FeltExpr.eval_const _ 1, FeltExpr.eval_const _ 2, and_imp]
    intro h1 h2 h3
    constructor
    · exact h1

    let mslh_val := (ab.deduce.2).eval varAssign
    have : (ab.deduce.2).eval varAssign = mslh_val := by rfl
    rw [this] at h2
    rw [this] at h3

    let msl_val := msl.eval varAssign
    have : msl.eval varAssign = msl_val := by rfl
    rw [this] at h3
    rw[this]

    let condition_val := condition.eval varAssign
    have : condition.eval varAssign = condition_val := by rfl
    rw [this] at h3
    rw [this] at h2
    rw[this]

    apply sound
    unfold spec_auto

    use mslh_val
    constructor
    exact h2
    rw [mul_comm 2 _]
    exact h3

end CondRangeCheck2



-- Is this right? It looks like felt252_to_m31 takes 4 limbs
def small_to_rel_imm (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : FeltExpr) : FeltExpr := -- local to this file?
  let low_limbs_value := low_limb0 + low_limb1 * FeltExpr.const (2^9) +
    low_limb2 * FeltExpr.const (2^18) + remainder_bits * FeltExpr.const (2^27)
  low_limbs_value - msb - FeltExpr.const (2^29) * mid_limbs_set

/-
Semantics.
-/

def small_to_rel_imm_val (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt) : Felt := -- local to this file?
  let low_limbs_value := low_limb0 + low_limb1 * 2^9 + low_limb2 * 2^18 + remainder_bits * 2^27
  low_limbs_value - msb - 2^29 * mid_limbs_set

@[simp] theorem small_to_rel_imm_val_eval [Fact (Nat.Prime Stwo.P)] (varAssign : VarAssign) -- local to this file?? low_limb3? remainder_bits?
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : FeltExpr):
   (small_to_rel_imm low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set |>.eval varAssign) =
     small_to_rel_imm_val (low_limb0.eval varAssign) (low_limb1.eval varAssign)
       (low_limb2.eval varAssign) (remainder_bits.eval varAssign) (msb.eval varAssign) (mid_limbs_set.eval varAssign) := by
  simp [small_to_rel_imm, small_to_rel_imm_val, FeltExpr.eval]

-- If the Felt252 value encodes a rel imm value, this returns the corresponding value.
open Fin.NatCast in
def Felt252_to_rel_imm_val (value : Felt252Words) : Felt :=
  small_to_rel_imm_val
    (value 0)
    (value 1)
    (value 2)
    (if value (20 : Nat) = ↑(0x1ff : Nat) then ((value 3) - 0x1fc) else (value 3))
    (if value (27 : Nat) = ↑(0x100 : Nat) then 1 else 0)
    (if value (20 : Nat) = ↑(0x1ff : Nat) then 1 else 0)



def small_to_felt252 (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : FeltExpr) : Felt252Expr :=
  let msb_limb := msb * FeltExpr.const 0x100
  let mid_limb_value := mid_limbs_set * FeltExpr.const 0x1ff
  fun i => match i with
    | 0 => low_limb0
    | 1 => low_limb1
    | 2 => low_limb2
    | 3 => remainder_bits + mid_limbs_set * FeltExpr.const 0x1fc
    | 21 => FeltExpr.const 0x88 * msb - mid_limbs_set
    | 27 => msb_limb
    | i  => if 4 ≤ i.val && i.val < 21 then mid_limb_value else FeltExpr.const 0

/-
Semantics.
-/

def small_to_felt252_val --
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt) : Felt252Words :=
  let msb_limb := msb * 0x100
  let mid_limb_value := mid_limbs_set * 0x1ff
  fun i => match i with
    | 0 => low_limb0
    | 1 => low_limb1
    | 2 => low_limb2
    | 3 => remainder_bits + mid_limbs_set * 0x1fc
    | 21 => 0x88 * msb - mid_limbs_set
    | 27 => msb_limb
    | i  => if 4 ≤ i.val && i.val < 21 then mid_limb_value else 0

@[simp] theorem small_to_felt252_eval [Fact (Nat.Prime Stwo.P)] (varAssign : VarAssign)
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : FeltExpr) :
   (small_to_felt252 low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set |>.eval varAssign) =
     small_to_felt252_val (low_limb0.eval varAssign) (low_limb1.eval varAssign)
       (low_limb2.eval varAssign) (remainder_bits.eval varAssign) (msb.eval varAssign) (mid_limbs_set.eval varAssign) := by
  dsimp [Felt252Words]
  ext i
  simp [small_to_felt252, small_to_felt252_val, Felt252Expr.eval]; split <;> try rfl
  split <;> simp_all [FeltExpr.eval]

@[simp] theorem small_to_felt252_eval' [Fact (Nat.Prime Stwo.P)] (varAssign : VarAssign)
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : FeltExpr)
    (i : Fin FELT252_N_WORDS):
   (small_to_felt252 low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set i |>.eval varAssign) =
     small_to_felt252_val (low_limb0.eval varAssign) (low_limb1.eval varAssign)
       (low_limb2.eval varAssign) (remainder_bits.eval varAssign) (msb.eval varAssign) (mid_limbs_set.eval varAssign) i := by
  simp [small_to_felt252, small_to_felt252_val]; split <;> try rfl
  split <;> simp_all [FeltExpr.eval]



open Fin.NatCast

namespace ReadSmall

variable [Fact (Nat.Prime Stwo.P)]

def call --
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × FeltExpr × FeltExpr :=
  let _state := airBuilder.deduce
  let ab1 := _state.1
  let id := _state.2
  let lt1 := lookupTerms.add_addr_to_id address id
  let _state := DecodeSmallSign.call ab1
  let ab2 := _state.1
  let msb := _state.2.1
  let mid_limbs_set := _state.2.2
  let _state := ab2.deduce
  let ab3 := _state.1
  let low_limb0 := _state.2
  let _state := ab3.deduce
  let ab4 := _state.1
  let low_limb1 := _state.2
  let _state := ab4.deduce
  let ab5 := _state.1
  let low_limb2 := _state.2
  let _state := ab5.deduce
  let ab6 := _state.1
  let remainder_bits := _state.2
  let ab7 := CondRangeCheck2.call ab6 remainder_bits (FeltExpr.const 1)
  let lt2 := lt1.add_id_to_value id (small_to_felt252 low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set)
  (ab7, lt2, small_to_rel_imm low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set, id)

def spec_auto (memoryAssign : Felt252IdMemoryAssign) (address : CasmAddressVal)
    (ρvalue ρid : Felt) : Prop :=
  ∃ id : Felt,
    memoryAssign.addressToId (fun _ => address) = some (fun _ => id) ∧
  ∃ msb mid_limbs_set,
    DecodeSmallSign.spec msb mid_limbs_set ∧
  ∃ low_limb0 low_limb1 low_limb2 remainder_bits,
    memoryAssign.idToValue (fun _ => id) =
      some (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set) ∧
    ρvalue = small_to_rel_imm_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set ∧
    ρid = id ∧ CondRangeCheck2.spec remainder_bits 1 --CondRangeCheck2.spec?

def spec (memoryAssign : Felt252IdMemoryAssign) (address : CasmAddressVal) --
    (ρvalue ρid : Felt) : Prop :=
  memoryAssign.addressToId (fun _ => address) = some (fun _ => ρid) ∧
  ∃ msb mid_limbs_set,
    DecodeSmallSign.spec msb mid_limbs_set ∧
  ∃ low_limb0 low_limb1 low_limb2 remainder_bits,
    memoryAssign.idToValue (fun _ => ρid) =
      some (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set) ∧
  ρvalue = small_to_rel_imm_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set ∧
  remainder_bits.val < 4

theorem sound {memoryAssign : Felt252IdMemoryAssign} {address : CasmAddressVal}
    {ρvalue ρid : Felt} (hspec : spec_auto memoryAssign address ρvalue ρid) :
    spec memoryAssign address ρvalue ρid := by
  rcases hspec with ⟨id, h1, msb, mid_limbs_set, h2, low_limb0, low_limb1, low_limb2, remainder_bits, h3, h4, ⟨ h5,h6 ⟩ ⟩
  rw [← h5] at h1
  rw [← h5] at h3
  unfold CondRangeCheck2.spec at h6
  simp at h6
  exact ⟨h1, msb, mid_limbs_set, h2, low_limb0, low_limb1, low_limb2, remainder_bits, h3, h4, h6⟩


theorem sound_auto {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (address : CasmAddress) :
    let ⟨newAirBuilder, new_lt, value, id⟩ := ReadSmall.call ab lt address
    newAirBuilder.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (address.eval varAssign) (value.eval varAssign) (id.eval varAssign) := by
  /-
  simp only [call, AirBuilder.deduce_SatisfiedBy, Felt252IdMemory.SatisfiedBy,
    Memory.add_SatisfiedBy, small_to_felt252_eval', small_to_rel_imm_val_eval, and_imp]
  rintro h1 h2 h3 h4 h5
  rcases CondRangeCheck2.sound_auto h1 with ⟨h1c, h1d⟩

  rcases DecodeSmallSign.sound_auto h1c with ⟨h1a, h1b⟩
  simp only [AirBuilder.deduce_SatisfiedBy] at h1a
  use h1a
  use ⟨h2, h4⟩
  apply sound
  refine ⟨_, h3, ?_⟩
  refine ⟨_, _, h1b, ?_⟩

  use ((DecodeSmallSign.call ab.deduce.1).1).deduce.2.eval varAssign
  use (((DecodeSmallSign.call ab.deduce.1).1).deduce.1).deduce.2.eval varAssign
  use ((((DecodeSmallSign.call ab.deduce.1).1).deduce.1).deduce.1).deduce.2.eval varAssign
  use (((((DecodeSmallSign.call ab.deduce.1).1).deduce.1).deduce.1).deduce.1).deduce.2.eval varAssign

  constructor
  · exact h5
  constructor
  · simp --sorry
    unfold DecodeSmallSign.call
    rfl
  constructor
  · rfl
  exact h1d
  --exact CondRangeCheck2.sound h1d

  -- sorry
  -- -- refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  -- -- rotate_left 3
  -- -- exact h5
  -- -- rfl
  -/
  unfold call ; lift_lets
  intro state1 ab1 id lt1 state2 ab2 msb mid_limbs_set state3 ab3 low_limb0
    state4 ab4 low_limb1 state5 ab5 low_limb2
    state6 ab6 remainder_bits ab7 lt2
  intros hab7 hlt2
  have ⟨h_id_to_value, hlt1⟩ := AirLookupTerms.mem_id_to_value_SatisfiedBy_add _ _ memAssign _ h_mem.2 _ _ hlt2
  have ⟨hab6, h_remainder_bits⟩ := CondRangeCheck2.sound_auto hab7
  have hab5 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab6
  have hab4 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab5
  have hab3 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab4
  have hab2 := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab3
  have ⟨h_addr_to_id, hlt⟩ := AirLookupTerms.mem_addr_to_id_SatisfiedBy_add _ _ memAssign _ h_mem.1 _ _ hlt1
  have ⟨hab1, h_decode_small⟩ := DecodeSmallSign.sound_auto hab2
  have hab := (AirBuilder.deduce_SatisfiedBy _ varAssign).mp hab1

  use hab, hlt
  apply sound

  use (id.eval varAssign)
  constructor
  · convert h_addr_to_id ; simp ; simp
  use (msb.eval varAssign), (mid_limbs_set.eval varAssign), h_decode_small
  use (low_limb0.eval varAssign), (low_limb1.eval varAssign), (low_limb2.eval varAssign)
  use (remainder_bits.eval varAssign)
  constructor
  · convert h_id_to_value ; simp ; simp
  simp [small_to_rel_imm_val_eval]
  exact h_remainder_bits


  theorem bounds
    {memory : Felt252IdMemoryAssign}
    {address : CasmAddressVal} --
    {ρvalue ρid : Felt}
    (h_mem_rc: memory.IsRangeChecked)
    (hspec: spec memory address ρvalue ρid):
      ρvalue.val ≤ (2^29 - 1) ∨ (ρvalue.val ≥ Stwo.P - 2^29 - 1) := by

      have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1

      rcases hspec with ⟨h1, msb, mid_limbs_set, h2, low_limb0, low_limb1, low_limb2, remainder_bits, h3, h4, h6⟩
      unfold DecodeSmallSign.spec at h2
      rcases h2 with ⟨h_msb, h_mid_limbs_set, h_msb_mls⟩

      have h_mem_hv : memory.HasValue address (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set) := by
        use ρid
        constructor
        · convert h1 <;> simp
        · convert h3 ; simp

      have := Felt252IdMemoryAssign.IsRangeChecked_of_HasValue h_mem_rc h_mem_hv
      rcases this with ⟨value_nats, h_value_nats_rc⟩

      unfold small_to_felt252_val at h_value_nats_rc
      have h_limb0 := h_value_nats_rc 0 ; simp at h_limb0
      have h_limb1 := h_value_nats_rc 1 ; simp at h_limb1
      have h_limb2 := h_value_nats_rc 2 ; simp at h_limb2
      have h_limb3 := h_value_nats_rc 3 ; simp at h_limb3

      rw[h4]
      unfold small_to_rel_imm_val
      lift_lets
      intro low_limbs_value

      have h_remainder_bits2 : ↑(value_nats 3) = remainder_bits + mid_limbs_set * 0x1FC := by
        rw [h_limb3.1]

      have h_remainder_bits3 : (↑(value_nats 3):Felt).val = value_nats 3 := by
        apply ZMod.val_natCast_of_lt
        unfold Stwo.P
        linarith [h_limb3.2]

      have h_remainder_bits4 : value_nats 3 = remainder_bits.val + mid_limbs_set.val * 0x1FC := by
        rw [← h_remainder_bits3]
        rw [h_remainder_bits2]
        rw [ZMod.val_add_of_lt]
        rw [ZMod.val_mul]
        norm_num

        rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
        unfold Felt
        unfold Stwo.P
        rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]

        norm_num
        cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
        · rw[ZMod.val_zero]
          norm_num
        · rw[ZMod.val_one'' h_ne_1]
          norm_num

        calc
          remainder_bits.val + (mid_limbs_set * 508).val < 4 + (mid_limbs_set * 508).val := by
            apply add_lt_add_right h6
          _ < Stwo.P := by
            unfold Stwo.P
            cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
            · rw[zero_mul, ZMod.val_zero]
              norm_num1
            · rw[one_mul]
              rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
              unfold Felt
              unfold Stwo.P
              rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]
              norm_num1

      -- have h_limbs_lt : value_nats 0 + value_nats 1 * 2 ^ 9 + value_nats 2 * 2 ^ 18 +
      --   (value_nats 3 - ZMod.val mid_limbs_set * 508) * 2 ^ 27 < 2^29 := by
      --   rw [h_remainder_bits4, Nat.add_sub_cancel]
      --   omega

      have h_limbs_lt : value_nats 0 + value_nats 1 * 2 ^ 9 + value_nats 2 * 2 ^ 18 +
        remainder_bits.val * 2 ^ 27 < 2^29 := by
        omega

      have h_triv1: (↑(remainder_bits.val):Felt) = remainder_bits := by
        simp
        apply ZMod.cast_id
      have h_triv2: (2:Felt)^27 = (↑((2:Nat)^27):Felt) := by
        simp
        norm_num
      have h_triv3: (2:Felt)^18 = (↑((2:Nat)^18):Felt) := by
        simp
        norm_num
      have h_triv4: (2:Felt)^9 = (↑((2:Nat)^9):Felt) := by
        simp
        norm_num

      have h_llv : low_limbs_value.val < 2^29 := by
        unfold low_limbs_value
        calc
          ZMod.val (low_limb0 + low_limb1 * 2 ^ 9 + low_limb2 * 2 ^ 18 + remainder_bits * 2 ^ 27) =
          ZMod.val (↑(value_nats 0) + ↑(value_nats 1) * 2 ^ 9 + ↑(value_nats 2) * 2 ^ 18 + (↑(remainder_bits.val):Felt) * 2 ^ 27) := by
            rw [h_limb0.1, h_limb1.1, h_limb2.1, h_triv1]
          _ = (↑(value_nats 0 + (value_nats 1) * (2:Nat) ^ 9 + (value_nats 2) * (2:Nat) ^ 18 + remainder_bits.val * (2:Nat) ^ 27):Felt).val := by
            --rw [ZMod.val_natCast_of_lt]
            rw[h_triv2, h_triv3, h_triv4]
            rw[← Nat.cast_mul,← Nat.cast_mul,← Nat.cast_mul]
            rw[← Nat.cast_add,← Nat.cast_add,← Nat.cast_add]
          _ = value_nats 0 + value_nats 1 * 2 ^ 9 + value_nats 2 * 2 ^ 18 + remainder_bits.val * 2 ^ 27 := by
            rw[ZMod.val_natCast_of_lt]
            unfold Stwo.P
            omega
          _ < 2^29 := by
            exact h_limbs_lt

      cases h_mid_limbs_set <;> rename _ => h7 <;> rw[h7] <;> simp only [mul_zero, mul_one, sub_zero]
      · cases h_msb <;> rename _ => h8 <;> rw[h8]
        · left
          rw[sub_zero]
          omega
        · by_cases h9 : low_limbs_value = 0
          · right
            rw [h9, zero_sub]
            rw [ZMod.val_neg_one]
            unfold Stwo.P ; norm_num1
          · left
            push_neg at h9
            have : low_limbs_value.val ≥ 1 := by
              have := (ZMod.val_ne_zero low_limbs_value).mpr h9
              have := Nat.pos_iff_ne_zero.mpr this
              have := Nat.succ_le_of_lt this
              omega
            rw[ZMod.val_sub, ZMod.val_one]
            omega
            rw[ZMod.val_one]
            omega

      · right
        rw[h7] at h_msb_mls
        simp at h_msb_mls
        rw[h_msb_mls]
        have : ZMod.val (low_limbs_value - 1 - 2 ^ 29) =
            ZMod.val (low_limbs_value + (↑(Stwo.P - ((1 + 2 ^ 29):Nat)) :Felt)) := by
          rw[sub_sub, sub_eq_add_neg]
          have : ((-(1 + 2 ^ 29)):Felt) = (↑(Stwo.P - ((1 + 2 ^ 29):Nat)) :Felt) := by
            unfold Felt
            unfold Stwo.P
            rw [Nat.cast_sub (by norm_num)]
            norm_num
            rfl
          rw [this]
        rw[this]
        rw[ZMod.val_add_of_lt]
        rw[ZMod.val_natCast_of_lt]
        rw[Nat.sub_sub]
        omega
        apply Nat.sub_lt
        unfold Stwo.P
        norm_num
        norm_num

        --rw[Nat.cast_sub]
        rw[ZMod.val_natCast_of_lt]
        unfold Stwo.P
        omega
        apply Nat.sub_lt
        unfold Stwo.P
        norm_num
        norm_num




      -- rw [← h5] at h1
      -- rw [← h5] at h3
      -- unfold CondRangeCheck2.spec at h6
      -- simp at h6


-- theorem bounds [Fact (Nat.Prime Stwo.P)]
--     (varAssign : VarAssign)
--     (memoryAssign : Felt252IdMemoryAssign)
--     (ab : AirBuilder)
--     (memory : Felt252IdMemory)
--     (address : CasmAddress) :
--     let ⟨newAirBuilder, newMemory, value, id⟩ := ReadSmall.call ab memory address
--     newAirBuilder.SatisfiedBy varAssign →
--     newMemory.SatisfiedBy varAssign memoryAssign →
--       b.val ≤ (2^29 - 1) ∨ (b.val ≥ Stwo.P - 2^29 - 1) := by

theorem add_small_vals
    {memory : Felt252IdMemoryAssign}
    {address1 address2 address3 : CasmAddressVal} --
    {ρvalue1 ρvalue2 ρvalue3 ρid1 ρid2 ρid3 : Felt}
    (h_mem_rc: memory.IsRangeChecked)
    (hspec1: spec memory address1 ρvalue1 ρid1)
    (hspec2: spec memory address2 ρvalue2 ρid2)
    (hspec3: spec memory address3 ρvalue3 ρid3)
    (hsum: ρvalue3 = ρvalue1 + ρvalue2) :
      ρvalue3.toFelt252 = ρvalue1.toFelt252 + ρvalue2.toFelt252 := by

      rw[hsum] at hspec3
      rw[hsum]
      have bounds1 := bounds h_mem_rc hspec1
      have bounds2 := bounds h_mem_rc hspec2
      have bounds3 := bounds h_mem_rc hspec3
      exact toFelt252_add_small bounds1 bounds2 bounds3

end ReadSmall

/-
In the Rust code, this is in `memory.rs` (corresponding to `Memory.Lean`).
-/

namespace Felt252IdMemory


variable [Fact (Nat.Prime Stwo.P)]

def read_rel_imm
    (airBuilder : AirBuilder)
    (lookupTerms : AirLookupTerms)
    (address : CasmAddress) :
    AirBuilder × AirLookupTerms × FeltExpr :=
  let (ab1, lt1, value, _) := ReadSmall.call airBuilder lookupTerms address
  (ab1, lt1, value)

namespace read_rel_imm

omit [Fact (Nat.Prime Stwo.P)] in
@[simp]
theorem Fin.val_three {n : ℕ} : (3 : Fin (n+4)).val = 3 :=
  rfl

def spec_auto
    (memory : Felt252IdMemoryAssign)
    (address : CasmAddressVal)
    (ρvalue : Felt) : Prop :=
  ∃ ρid, ReadSmall.spec memory address ρvalue ρid

def spec := spec_auto

theorem sound_auto {t n_s : Nat}
    (varAssign : VarAssign)
    (memAssign : Felt252IdMemoryAssign)
    (ab : AirBuilder)
    (lt : AirLookupTerms)
    (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)
    (h_mem : AirLookupTerms.MemYieldsAgree memAssign h_satisfied.values
        (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX) (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
    (address : CasmAddress) :
    let ⟨newAirBuilder, new_lt, value⟩ := read_rel_imm ab lt address
    newAirBuilder.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      ab.SatisfiedBy varAssign ∧
      lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples ∧
      spec memAssign (address.eval varAssign) (value.eval varAssign) := by
  let state := ReadSmall.call ab lt address
  let id := state.2.2.2
  intros new_ab new_lt
  rcases ReadSmall.sound_auto varAssign memAssign ab lt h_satisfied h_mem address new_ab new_lt with ⟨h1, h2, h_spec⟩
  use h1, h2
  use id.eval varAssign
  exact h_spec

end read_rel_imm

def small_to_felt252_val_nat
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Nat) : Fin FELT252_N_WORDS → Nat :=
  let msb_limb := msb * 0x100
  let mid_limb_value := mid_limbs_set * 0x1ff
  fun i => match i with
    | 0 => low_limb0
    | 1 => low_limb1
    | 2 => low_limb2
    | 3 => remainder_bits + mid_limbs_set * 0x1fc
    | 21 => 0x88 * msb - mid_limbs_set
    | 27 => msb_limb
    | i  => if 4 ≤ i.val && i.val < 21 then mid_limb_value else 0

def small_to_felt252_val_nat_aux
    (low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Nat) : Fin FELT252_N_WORDS → Nat :=
  let msb_limb := msb * 0x100
  let mid_limb_value := mid_limbs_set * 0x1ff
  fun i => match i.val with --
    | 0 => low_limb0
    | 1 => low_limb1
    | 2 => low_limb2
    | 3 => remainder_bits + mid_limbs_set * 0x1fc
    | 21 => 0x88 * msb - mid_limbs_set
    | 27 => msb_limb
    | i  => if 4 ≤ i && i < 21 then mid_limb_value else 0

omit [Fact (Nat.Prime Stwo.P)] in
lemma small_to_felt252_val_nat_aux_eq {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Nat} :
    small_to_felt252_val_nat low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set =
      small_to_felt252_val_nat_aux low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set := by
  apply funext
  intro x
  unfold small_to_felt252_val_nat small_to_felt252_val_nat_aux
  split <;> simp
  next h0 h1 h2 h3 h21 h27 =>
    rw [Eq.comm]
    split <;> rename _ => h
    · exfalso ; apply h0 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    · exfalso ; apply h1 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    · exfalso ; apply h2 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    · exfalso ; apply h3 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    · exfalso ; apply h21 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    · exfalso ; apply h27 ; exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
    have h_3_le : (3 : Nat) ≤ ↑x ↔ 3 ≤ x := by rfl --?
    have h_lt_21 : ↑x < (21 : Nat) ↔ x < 21 := by rfl --?
    simp only [h_lt_21]

lemma small_to_felt252_val_flags {value_n : Felt252Nats}
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set)) :
  ¬(msb = 0 ∧ mid_limbs_set = 1) := by
  by_contra h_c
  unfold small_to_felt252_val at h_rc
  have h_rc_21 := h_rc 21
  simp at h_rc_21
  simp [h_c.1, h_c.2] at h_rc_21
  have h_eq := congr_arg (fun x => x.val) h_rc_21.1
  simp only at h_eq
  rw [ZMod.val_neg_one] at h_eq
  rw [ZMod.val_natCast_of_lt (by apply lt_trans h_rc_21.2 ; unfold Stwo.P ; norm_num1 )] at h_eq
  rw [←h_eq] at h_rc_21
  apply not_lt_of_gt (by norm_num1) h_rc_21.2

lemma small_to_felt252_val_nat_eq {value_n : Felt252Nats}
      {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
      (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
      (h_remainder_bits : remainder_bits.val < 4) --
      (h_msb : msb = 0 ∨ msb = 1)
      (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
      (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
    value_n = small_to_felt252_val_nat low_limb0.val low_limb1.val low_limb2.val remainder_bits.val msb.val mid_limbs_set.val := by
  apply funext
  intro x
  unfold small_to_felt252_val at h_rc
  unfold small_to_felt252_val_nat
  simp only [←Felt252Nats.eq_val_of_IsRangeChecked _ _ h_rc x]
  have h_one : (1 : Felt) = (1 : Nat) := by rfl

  have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1

  have h_rb_plus_1 : (↑remainder_bits : Felt).val + (↑508 : Felt).val < Stwo.P := by
    rw [← ZMod.val_add_of_lt]
    calc
      (remainder_bits + 508).val ≤ remainder_bits.val + (508:Felt).val := by
        apply ZMod.val_add_le
      _ = remainder_bits.val + 508 := by
        rw[(show (508:Felt) = (508 : Nat) by rfl)]
        rw[ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
      _ < 4 + 508 := by
        apply add_lt_add_right h_remainder_bits
      _ < Stwo.P := by
        unfold Stwo.P ; norm_num1
    calc
      ZMod.val remainder_bits + ZMod.val 508 = remainder_bits.val + 508 := by
        rw[(show (508:Felt) = (508 : Nat) by rfl)]
        rw[ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
      _ < 4 + 508 := by
        apply add_lt_add_right h_remainder_bits
      _ < Stwo.P := by
        unfold Stwo.P ; norm_num1

  have h_obv1 : (↑508 : Felt).val = (↑1 : Felt).val * 508 := by
    rw[ZMod.val_one'' h_ne_1, one_mul]
    rw[(show (508:Felt) = (508 : Nat) by rfl)]
    rw[ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]

  have h_obv2 : (↑(136 - mid_limbs_set) : Felt).val = 136 * 1 - (↑mid_limbs_set : Felt).val := by
    cases h_mid_limbs_set <;> rename _ => h0 <;> simp [h0]
    · rw [(show (136 : Felt) = (↑(136 : Nat) : Felt) by rfl)]
      rw [ZMod.val_natCast_of_lt (show (136 : Nat) < Stwo.P by unfold Stwo.P ; norm_num1)]
    · rw [ZMod.val_one'' h_ne_1]
      norm_num
      rw [(show (135 : Felt) = (↑(135 : Nat) : Felt) by rfl)]
      rw [ZMod.val_natCast_of_lt (show (135 : Nat) < Stwo.P by unfold Stwo.P ; norm_num1)]

  have h_obv3 : (↑msb * 256 : Felt).val = (↑msb : Felt).val * 256 := by
    cases h_msb <;> rename _ => h0 <;> simp [h0]
    · rw [(show (256 : Felt) = (↑(256 : Nat) : Felt) by rfl)]
      rw [ZMod.val_natCast_of_lt (show (256 : Nat) < Stwo.P by unfold Stwo.P ; norm_num1)]
      rw [ZMod.val_one'' h_ne_1]

  split <;> try simp
  · by_cases h_c : msb = 0 ∧ mid_limbs_set = 1
    · exfalso
      apply small_to_felt252_val_flags h_rc h_c
    have h136 : (136 : Felt) = (136 : Nat) := by rfl
    have h135 : (135 : Felt) = (135 : Nat) := by rfl
    cases h_mid_limbs_set <;> rename _ => h0 <;> simp [h0] ;
    rw [ZMod.val_add_of_lt h_rb_plus_1]
    simp
    rw[h_obv1]

  · cases h_msb <;> rename _ => h0 <;> simp [h0]
    rw[h0] at h_msb_mls
    simp at h_msb_mls
    rw[h_msb_mls]
    rw [h_one, ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
    rw[h_obv2]

  rw[h_obv3]

  cases h_mid_limbs_set <;> rename _ => h0 <;> simp [h0]
  split <;> rename _ => h0
  have h511 : (511 : Felt) = (511 : Nat) := by rfl
  rw [h_one, ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
  rw [h511, ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
  simp

lemma small_to_felt252_eval_22_eq {value_n : Felt252Nats} -- ?
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 22, value_n i * 2^(FELT252_BITS_PER_WORD * i) + msb.val * 256 * 2^(FELT252_BITS_PER_WORD * 27) := by

  rw [small_to_felt252_val_nat_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  rw [Fin.sum_univ_castSucc]
  apply congr_arg₂
  swap
  · unfold small_to_felt252_val_nat ; simp
  rw [Fin.sum_univ_add (a := 22) (b := 5)]
  apply (show ∀ a b c, a = c ∧ b = 0 → a + b = c by intro a b c ⟨h1, h2⟩ ; simp [h1, h2])
  constructor
  · have h_add_5 : ∀ i : Fin 22, (Fin.castAdd 5 i).castSucc = (i.val : Fin 28) := by
      intro i ; unfold Fin.castSucc Fin.castAdd
      rw [Fin.mk.inj_iff] ; simp
      rw [Eq.comm, Nat.mod_eq_of_lt _]
      apply lt_trans i.isLt (by norm_num1)
    simp only [h_add_5]
    have h_val : ∀ x : Fin 22, (x.val : Fin 28).val = x.val := by
      intro x ; rw [Fin.val_natCast, Nat.mod_eq_of_lt]
      apply lt_trans x.isLt (by norm_num1)
    simp only [h_val]
  apply Finset.sum_eq_zero
  intro i h_i
  unfold small_to_felt252_val_nat
  have h_5 : 21 < (Fin.natAdd 22 i).castSucc.val ∧ (Fin.natAdd 22 i).castSucc.val < 27 := by
    simp
    constructor
    · apply lt_of_lt_of_le (by norm_num1) (Nat.le_add_right 22 _)
    apply lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _)
    norm_num1
  split <;> rename _ => h_eq
  · exfalso ; rw [h_eq] at h_5 ; simp at h_5
  · exfalso ; rw [h_eq] at h_5 ; simp at h_5
  · exfalso ; rw [h_eq] at h_5 ; simp at h_5
  · exfalso ; rw [h_eq] at h_5 ; simp at h_5
  · exfalso ; rw [h_eq] at h_5
    apply Eq.not_lt _ h_5.1
    rfl
  · exfalso ; rw [h_eq] at h_5
    apply Eq.not_lt _ h_5.2
    rfl
  have : (decide ((Fin.natAdd 22 i).castSucc.val < 21)) = false := by
    rw [decide_eq_false_iff_not]
    apply not_lt_of_gt
    convert h_5.1
  simp only [this, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp

lemma small_to_felt252_eval_21_eq {value_n : Felt252Nats}
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 21, value_n i * 2^(FELT252_BITS_PER_WORD * i)
      + (0x88 * msb.val - mid_limbs_set.val) * 2^(FELT252_BITS_PER_WORD * 21)
      + msb.val * 256 * 2^(FELT252_BITS_PER_WORD * 27) := by
  rw [small_to_felt252_eval_22_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  rw [Fin.sum_univ_castSucc]
  congr
  rw [small_to_felt252_val_nat_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  unfold small_to_felt252_val_nat
  simp

def mid_limb_value := ∑ i : Fin 17, 0x1ff * 2^(FELT252_BITS_PER_WORD * (i.val + 4))

omit [Fact (Nat.Prime Stwo.P)] in
lemma mid_limb_value_eq : mid_limb_value = 784637716923335095479473677900958302012794430489284837376 := by
  rfl

lemma small_to_felt252_eval_4_eq {value_n : Felt252Nats} -- ?
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 4, value_n i * 2^(FELT252_BITS_PER_WORD * i) --
      + mid_limbs_set.val * mid_limb_value
      + (0x88 * msb.val - mid_limbs_set.val) * 2^(FELT252_BITS_PER_WORD * 21)
      +  msb.val * 256 * 2^(FELT252_BITS_PER_WORD * 27) := by
  rw [small_to_felt252_eval_21_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  apply congr_arg₂ ; swap ; rfl
  apply congr_arg₂ ; swap ; rfl

  rw [Fin.sum_univ_add (a := 4) (b := 17)]
  apply congr_arg₂
  exact rfl
  rw [small_to_felt252_val_nat_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  rw [small_to_felt252_val_nat_aux_eq]
  unfold mid_limb_value
  unfold small_to_felt252_val_nat_aux
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  rfl
  intro i h_i
  --
  have h_4 : 4 ≤ (Fin.natAdd 4 i).val ∧ (Fin.natAdd 4 i).val < 21 := by
    simp ; apply lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _)
    norm_num1
  have h_natAdd_lt : (Fin.natAdd 4 i).val < FELT252_N_WORDS := by
    apply lt_trans h_4.2 ; simp [FELT252_N_WORDS]
  rw [Fin.val_cast_of_lt h_natAdd_lt]
  split <;> rename _ => h_eq
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.not_le_of_lt _ h_4.1 ; norm_num1
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.not_le_of_lt _ h_4.1 ; norm_num1
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.not_le_of_lt _ h_4.1 ; norm_num1
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.not_le_of_lt _ h_4.1 ; norm_num1
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.lt_irrefl 21 h_4.2
  · exfalso ; rw [h_eq] at h_4 ; apply Nat.not_lt_of_le _ h_4.2 ; norm_num1
  rw [decide_eq_true_iff.mpr h_4.1, decide_eq_true_iff.mpr h_4.2]
  simp [mul_assoc, add_comm]

lemma small_to_felt252_eval_4_eq_b {value_n : Felt252Nats} -- ?
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
    value_n 3 =
      remainder_bits.val + mid_limbs_set.val * 0x1fc := by
  rw [small_to_felt252_val_nat_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  dsimp [small_to_felt252_val_nat]

lemma small_to_felt252_eval_4_eq_c {value_n : Felt252Nats} -- ?
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 3, value_n i * 2^(FELT252_BITS_PER_WORD * i) --
      + (remainder_bits + mid_limbs_set * 0x1fc) * 2^(FELT252_BITS_PER_WORD * 3)
      + mid_limbs_set.val * mid_limb_value
      + (0x88 * msb.val - mid_limbs_set.val) * 2^(FELT252_BITS_PER_WORD * 21)
      +  msb.val * 256 * 2^(FELT252_BITS_PER_WORD * 27) := by
  rw [small_to_felt252_eval_4_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  rw [Fin.sum_univ_four]
  rw [Fin.sum_univ_three]
  have obv_1 : (↑(↑(3 : Fin 4):Nat):Fin FELT252_N_WORDS) = 3 := by rfl
  rw [obv_1]

  rw [small_to_felt252_eval_4_eq_b h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  simp

  have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1

  have obv_2 : (↑(136 * ZMod.val msb - ZMod.val mid_limbs_set):Felt) = 136 * ZMod.cast msb - ZMod.cast mid_limbs_set := by
    cases h_msb <;> rename _ => h1 <;> simp only [h1, ZMod.val_one'' h_ne_1] <;>
    cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1,
        ZMod.val_zero, ZMod.cast_zero, mul_zero, sub_zero, Nat.sub_zero, Nat.cast_zero, mul_one, ZMod.cast_one']
    · rw[h1] at h_msb_mls
      simp at h_msb_mls
      --have := h_msb_mls
      rw[h_msb_mls] at h2
      have : (1 : ZMod Stwo.P) = 0 := by
        unfold Felt at h2
        rw [h2]
      have := ZMod.one_eq_zero_iff.mp this
      unfold Stwo.P at this
      absurd this
      norm_num
    · rfl
    · rfl

  rw [obv_2]
  simp

  have obv_3: ZMod.cast remainder_bits = (remainder_bits : Felt) := by
    unfold Felt
    simp

  have obv_4: ZMod.cast mid_limbs_set = (mid_limbs_set : Felt) := by
    unfold Felt
    simp
  rw[obv_3, obv_4]
  left
  rfl

  lemma small_to_felt252_eval_4_eq_c2 {value_n : Felt252Nats} -- ?
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 3, value_n i * 2^(FELT252_BITS_PER_WORD * i) --
      + (remainder_bits.val + mid_limbs_set.val * 0x1fc) * 2^(FELT252_BITS_PER_WORD * 3)
      + mid_limbs_set.val * mid_limb_value
      + (0x88 * msb.val - mid_limbs_set.val) * 2^(FELT252_BITS_PER_WORD * 21)
      +  msb.val * 256 * 2^(FELT252_BITS_PER_WORD * 27) := by
  rw [small_to_felt252_eval_4_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  rw [Fin.sum_univ_four]
  rw [Fin.sum_univ_three]
  have obv_1 : (↑(↑(3 : Fin 4):Nat):Fin FELT252_N_WORDS) = 3 := by rfl
  rw [obv_1]
  -- have := small_to_felt252_eval_4_eq_b h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls
  rw [small_to_felt252_eval_4_eq_b h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  simp

lemma big_looparound {x: Nat} {mid_limbs_set remainder_bits: Felt}
(h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
(h_remainder_bits : remainder_bits = ↑x - mid_limbs_set * 0x1FC ∧ remainder_bits.val < 4):
  x ≥ (ZMod.val mid_limbs_set) * 508 := by

  have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1

  by_contra h_contra
  push_neg at h_contra

  have htmp1: (↑(Stwo.P):Felt)=0 := by
    unfold Stwo.P
    rfl

  have htmp2: ZMod.val ((↑(x):Felt) - mid_limbs_set * 508) = ZMod.val ((↑(Stwo.P):Felt) + (↑(x):Felt) - mid_limbs_set * 508) := by
    rw[htmp1, zero_add]
  have htmp3 : mid_limbs_set * 508 = (↑(mid_limbs_set.val * 508):Felt) := by --
    cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1, ZMod.val_zero, zero_mul, zero_mul, one_mul,one_mul] <;> rfl

  have h_for_contra : ZMod.val remainder_bits > 5 := by
    rw [h_remainder_bits.1]
    rw [htmp2, htmp3]
    rw[← Nat.cast_add]
    rw[← Nat.cast_sub]
    rw[ZMod.val_natCast_of_lt]
    cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1,
        ZMod.val_zero, zero_mul, zero_mul, one_mul,one_mul, Nat.sub_zero]
    · calc
        Stwo.P + x ≥ Stwo.P := by
          apply Nat.le_add_right
        _ > 5 := by
          unfold Stwo.P
          norm_num
    · calc
        Stwo.P + x - 508 ≥ Stwo.P - 508 := by
          apply Nat.sub_le_sub_right
          apply Nat.le_add_right
        _ > 5 := by
          unfold Stwo.P
          norm_num

    have htmp3 : ZMod.val mid_limbs_set * 508 ≤ Stwo.P + x := by
      calc
        ZMod.val mid_limbs_set * 508 ≤ Stwo.P := by
          unfold Stwo.P
          cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1, ZMod.val_zero, zero_mul, one_mul] <;> norm_num
        _ ≤ Stwo.P + x := by
          apply Nat.le_add_right

    calc
      Stwo.P + x - ZMod.val mid_limbs_set * 508 < Stwo.P + ZMod.val mid_limbs_set * 508 - ZMod.val mid_limbs_set * 508 := by
        apply Nat.sub_lt_sub_right htmp3
        apply add_lt_add_left h_contra
      _ = Stwo.P := by
        apply Nat.add_sub_cancel

    calc
      ZMod.val mid_limbs_set * 508 ≤ 508 := by
        cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_zero, ZMod.val_one'' h_ne_1, zero_mul, one_mul] <;> norm_num
      _ ≤ Stwo.P := by
        unfold Stwo.P ; norm_num
      _ ≤ Stwo.P + x := by
        apply Nat.le_add_right

  have : 4 > 5 := by
    calc
      4 > ZMod.val remainder_bits := h_remainder_bits.2
      _ > 5 := h_for_contra
  linarith[this]

lemma small_to_felt_eval_eq {value_n : Felt252Nats} -- ???
    {low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set : Felt}
    (h_rc : value_n.IsRangeChecked (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set))
    (h_remainder_bits : remainder_bits.val < 4)
    (h_msb : msb = 0 ∨ msb = 1)
    (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
    (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
  ∑ i : Fin FELT252_N_WORDS, value_n i * 2^(FELT252_BITS_PER_WORD * i) =
    ∑ i : Fin 3, value_n i * 2^(FELT252_BITS_PER_WORD * i) +
    remainder_bits.val * 2^(FELT252_BITS_PER_WORD * 3) + -- remainder_bits.val
    (msb.val * (Felt252Prime - 1) - mid_limbs_set.val * 2 ^ 29) := by --29

  rw [small_to_felt252_eval_4_eq_c2 h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  simp only [add_assoc]
  apply congr_arg₂
  rfl
  unfold Felt252Prime FELT252_BITS_PER_WORD Stwo.P ; norm_num
  cases h_msb <;> cases h_mid_limbs_set
  next h0 h1 => simp [h0, h1]
  next h0 h1 => exfalso ; apply small_to_felt252_val_flags h_rc ⟨h0, h1⟩
  next h0 h1 => simp [h0, h1] ; rw [ZMod.val_one'' (by norm_num1)] --rw [ZMod.cast_one' (by norm_num1)]
  next h0 h1 =>
    simp [h0, h1] ; rw [ZMod.val_one'' (by norm_num1)] --rw [ZMod.cast_one _] --
    rw [mid_limb_value_eq]
    rw[one_mul, one_mul,one_mul,one_mul, one_mul, mul_one, add_mul]
    rw[add_assoc]
    apply add_right_cancel_iff.mpr rfl


theorem toFelt_toFelt252_of_lt {n : Nat} (h_n : n < Stwo.P - 2^29 -1) : --
    (n : Felt).toFelt252 = ↑n := by -- ok?
  unfold Felt.toFelt252
  rw [ZMod.val_add]
  rw [ZMod.val_natCast_of_lt (by apply lt_trans h_n ; unfold Stwo.P ; norm_num1)]
  rw [ZMod.val_natCast_of_lt (by unfold Stwo.P ; norm_num1)]
  rw [Nat.mod_eq_of_lt _]
  rw [Nat.cast_add]
  ring_nf
  unfold Stwo.P at *
  simp at h_n
  norm_num[h_n]
  have := add_lt_add_right h_n 536870912
  linarith[this]

theorem toFelt252_of_isRangeChecked {x : Felt} {n : Nat} (h : IsRangeChecked n x) (h_n : n < 30) :
    x.toFelt252 = ↑x.val := by

  rcases h with ⟨nx, h_nx_lt, h_nx⟩
  have h_nx_lt' : nx < Stwo.P - 2^29 -1 := by
    calc
      nx < 2^n := h_nx_lt
      _ < 2^30 := by
        apply Nat.pow_lt_pow_of_lt (show 1 < 2 by norm_num1) h_n
      _ < Stwo.P - 2^29 -1 := by --
        unfold Stwo.P ; norm_num1
  have := toFelt_toFelt252_of_lt h_nx_lt'
  rw [← h_nx] at this
  rw [this, h_nx]
  have : nx < Stwo.P := by -- shorten
    calc
      nx < 2^n := h_nx_lt
      _ < 2^30 := by
        apply Nat.pow_lt_pow_of_lt (show 1 < 2 by norm_num1) h_n
      _ < Stwo.P := by
        unfold Stwo.P ; norm_num1
  rw[ZMod.val_natCast_of_lt this]

theorem toFelt252_neg {x : Felt} {nx : Nat} (h_nx : x = ↑nx) (h_ny_lt: nx ≤ 2 ^ 29 + 1): --
    (-x).toFelt252 = -x.toFelt252 := by

  unfold Felt.toFelt252
  rw [sub_eq_iff_eq_add]
  simp only [neg_add_eq_sub]

  rw[h_nx]
  rw[← Nat.cast_add]
  rw[← Nat.cast_sub h_ny_lt]
  have h1: nx + (2^29 + 1) < Stwo.P := by
    unfold Stwo.P
    linarith
  have h2: 2^29 + 1 - nx < Stwo.P := by
    calc
      2^29 + 1 - nx ≤ 2^29 +1 := by
        apply Nat.sub_le
      _ < Stwo.P := by
        unfold Stwo.P ; norm_num1
  rw[ZMod.val_natCast_of_lt h1]
  rw[ZMod.val_natCast_of_lt h2]
  rw[Nat.cast_sub h_ny_lt]
  ring_nf
  rw[Nat.cast_add]
  ring_nf


theorem toFelt252_add_sub {x y z : Felt}
      {nx: Nat}
      {ny: Nat}
      {nz: Nat}
      (h_nx : x = ↑nx)
      (h_nx_lt: nx < 2 ^ 30 - 1)
      (h_ny : y = ↑ny)
      (h_ny_lt: ny < 2 ^ 29)
      (h_nz : z = ↑nz)
      (h_nz_sub_ny_le : nz-ny ≤ 2^29 + 1): --
    (x + (y - z)).toFelt252 = x.toFelt252 + (y - z).toFelt252 := by

  simp only [h_nx, h_ny, h_nz]
  by_cases h_le : nz ≤ ny
  · rw [←Nat.cast_sub h_le]
    rw [toFelt.of_lt, toFelt.of_lt]
    apply toFelt252_add'
    · calc
        nx + (ny - nz) ≤ nx + ny := by
          apply Nat.add_le_add_left (Nat.sub_le _ _)
        _ ≤ 2^30 - 2 + ny := by
          apply Nat.add_le_add_right _ ny
          exact Nat.le_pred_of_lt h_nx_lt
        _ < 2^30 - 2 + 2^29 := by
          apply Nat.add_lt_add_left h_ny_lt (2^30 - 2)
        _ = Stwo.P - 2^29 -1 := by
          unfold Stwo.P ; norm_num1

    apply lt_of_le_of_lt (Nat.sub_le _ _)
    apply lt_trans h_ny_lt
    unfold Stwo.P ; norm_num1
    apply lt_trans h_nx_lt
    unfold Stwo.P ; norm_num1
  rw [←neg_sub, ←Nat.cast_sub]
  rw [toFelt252_neg _ _]

  rw [toFelt.of_lt, toFelt.of_lt]
  ring_nf
  apply toFelt252_sub'

  calc
    nz - ny ≤ 2 ^ 29 + 1 := h_nz_sub_ny_le
    _ ≤ nx + 2 ^ 29 + 1:= by
      apply Nat.le_add_left

  norm_num

  unfold Stwo.P
  calc
    nx < 2 ^ 30 -1 := h_nx_lt
    _ < 2147483647 - 2 ^ 29 -1 := by
      norm_num

  unfold Stwo.P
  calc
    nz - ny ≤ 2 ^ 29 + 1 := h_nz_sub_ny_le
    _ < 2147483647 - 2 ^ 29 -1 := by
      norm_num

  unfold Stwo.P
  calc
    nx < 2 ^ 30 -1 := h_nx_lt
    _ < 2147483647 - 2 ^ 29 - 1 := by
      norm_num
  use nz - ny
  simp

  linarith[h_nz_sub_ny_le]

  push_neg at h_le
  linarith


theorem small_to_felt252_eq_small_to_rel_imm --
      {limb0 limb1 limb2 remainder_bits msb mid_limbs_set : Felt}
      {value_n : Felt252Nats}
      (h_rc : value_n.IsRangeChecked (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set))
      (h_remainder_bits : remainder_bits.val < 4) --
      (h_msb : msb = 0 ∨ msb = 1)
      (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
      (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
      --
      (small_to_rel_imm_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set).toFelt252 = value_n.eval := by

  --sry
  have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1
  -- lhs
  unfold small_to_rel_imm_val
  unfold small_to_felt252_val at h_rc
  have h_limb0 := h_rc 0 ; simp at h_limb0
  have h_limb1 := h_rc 1 ; simp at h_limb1
  have h_limb2 := h_rc 2 ; simp at h_limb2
  have h_limb3 := h_rc 3 ; simp at h_limb3

  have h_remainder_bits2 : ↑(value_n 3) = remainder_bits + mid_limbs_set * 0x1FC := by
    rw [h_limb3.1]

  have h_remainder_bits3 : (↑(value_n 3):Felt).val = value_n 3 := by
    apply ZMod.val_natCast_of_lt
    unfold Stwo.P
    linarith [h_limb3.2]

  have h_remainder_bits4 : value_n 3 = remainder_bits.val + mid_limbs_set.val * 0x1FC := by
    rw [← h_remainder_bits3]
    rw [h_remainder_bits2]
    rw [ZMod.val_add_of_lt]
    rw [ZMod.val_mul]
    norm_num

    rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
    unfold Felt
    unfold Stwo.P
    rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]

    norm_num
    cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
    · rw[ZMod.val_zero]
      norm_num
    · rw[ZMod.val_one'' h_ne_1]
      norm_num

    calc
      remainder_bits.val + (mid_limbs_set * 508).val < 4 + (mid_limbs_set * 508).val := by
        apply add_lt_add_right h_remainder_bits
      _ < Stwo.P := by
        unfold Stwo.P
        cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
        · rw[zero_mul, ZMod.val_zero]
          norm_num1
        · rw[one_mul]
          rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
          unfold Felt
          unfold Stwo.P
          rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]
          norm_num1

  have h_limbs_lt : value_n 0 + value_n 1 * 2 ^ 9 + value_n 2 * 2 ^ 18 +
    (value_n 3 - ZMod.val mid_limbs_set * 508) * 2 ^ 27 < Stwo.P - 2^29 - 1 := by
    trans 512 + 512 * 2 ^ 9 + 512 * 2 ^ 18 + 4 * 2 ^ 27
    · gcongr
      exact h_limb0.2
      exact h_limb1.2
      exact h_limb2.2
      rw [h_remainder_bits4, Nat.add_sub_cancel]
      exact h_remainder_bits
    unfold Stwo.P ; norm_num1

  have h_remainder_bits_eq : remainder_bits = ↑(value_n 3) - mid_limbs_set * 508 := by
    rw [← h_limb3.1]
    ring
  rw [h_limb0.1, h_limb1.1, h_limb2.1, h_remainder_bits_eq]
  rw [sub_sub]

  have h_limb3_pos : value_n 3 ≥ ZMod.val mid_limbs_set * 508 := big_looparound h_mid_limbs_set ⟨h_remainder_bits_eq, h_remainder_bits⟩

  have h_cast_limbs : ((value_n 0) : Felt) + ((value_n 1) : Felt) * 2 ^ 9 + ((value_n 2) : Felt) * 2 ^ 18
  + (((value_n 3) : Felt) - mid_limbs_set * 508)* 2 ^ 27 =
      (((value_n 0) + (value_n 1) * 2 ^ 9 + (value_n 2) * 2 ^ 18 + ((value_n 3) - mid_limbs_set.val * 508) * 2 ^ 27) : Nat) := by

    rw[Nat.cast_add, Nat.cast_add, Nat.cast_add]
    rw[add_assoc, add_assoc, add_assoc, add_assoc]

    rw [add_left_cancel_iff]

    rw[Nat.cast_mul]
    have zxc : (2:Felt)^9 = (↑((2:Nat)^9):Felt) := by rfl
    rw [zxc]
    rw [add_left_cancel_iff]

    rw[Nat.cast_mul]
    have zxc : (2:Felt)^18 = (↑((2:Nat)^18):Felt) := by rfl
    rw [zxc]
    rw [add_left_cancel_iff]

    rw[Nat.cast_mul]
    have zxc : (2:Felt)^27 = (↑((2:Nat)^27):Felt) := by rfl
    rw [zxc]
    rw[Nat.cast_sub h_limb3_pos]

    have zxc : mid_limbs_set * 508 = ↑(ZMod.val mid_limbs_set * 508) := by
      cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1]
      · rw[zero_mul, ZMod.val_zero, zero_mul]
        rfl
      · rw[one_mul,one_mul]
        rfl
    rw [zxc]

  have h_cast_b : msb + 2 ^ 29 * mid_limbs_set = ((msb.val + 2 ^ 29 * mid_limbs_set.val) : Nat) := by
    simp only [Nat.cast_mul, Nat.cast_add] ; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] ; rfl
  rw [h_cast_limbs, h_cast_b]
  rw [toFelt252_sub]

  have h_cast_sum := small_to_felt_eval_eq h_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls --

  conv_rhs =>
    rw [Felt252Nats.eval_cast_add]
    rw[h_cast_sum]

    unfold FELT252_BITS_PER_WORD
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, pow_zero, mul_one]
    simp only [Fin.val_one, Nat.cast_one, mul_one]
    simp only [Fin.val_two, Nat.cast_two, Nat.reduceMul]
    rw [Nat.cast_add]

  rw [sub_eq_iff_eq_add]
  conv_rhs => rw [add_assoc]
  rw [toFelt_toFelt252_of_lt]

  rw [←Nat.cast_add]

  have h_val3 : (value_n 3 : Felt252) = ZMod.cast (value_n 3 :Felt) := by
    unfold ZMod.cast
    unfold Stwo.P
    simp only
    rw [ZMod.val_natCast_of_lt]
    linarith [(h_rc 3).2]

  have h_remainder_bits_eq : remainder_bits = ↑(value_n 3) - mid_limbs_set * 508 := by
    rw [← h_limb3.1]
    ring

  cases h_msb <;> rename _ => h1 <;> simp only [h1, ZMod.val_one'' h_ne_1] <;>
  cases h_mid_limbs_set <;> rename _ => h2 <;> simp only [h2, ZMod.val_one'' h_ne_1]
  · simp
    rw [Fin.sum_univ_three] --
    simp
    norm_num
    rw[h_remainder_bits_eq, h2]
    norm_num
    rw[h_val3]
  · exfalso ; exact small_to_felt252_val_flags h_rc ⟨h1, h2⟩

  · rw [ZMod.val_zero, zero_mul, mul_zero, add_zero, one_mul, Nat.sub_zero]
    simp only [Nat.reducePow, Nat.cast_add]

    rw [Nat.cast_sub]
    rw [Fin.sum_univ_three]
    rw[zero_mul, Nat.cast_zero, sub_zero, Nat.cast_sub]
    rw[sub_add_cancel]
    rw[h_remainder_bits_eq, h2, zero_mul, sub_zero]
    have : (↑Felt252Prime: Felt252) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
    rw [this]
    rw[add_zero]
    simp only [pow_mul, Nat.cast_add, Nat.cast_mul]

    apply congr_arg₂
    apply congr_arg₂
    apply congr_arg₂
    simp
    simp
    simp

    rw[ZMod.val_natCast_of_lt]
    unfold Stwo.P
    linarith [(h_rc 3).2]

    repeat
      unfold Felt252Prime
      norm_num




  · rw [Fin.sum_univ_three]
    simp only [pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rw [one_mul, one_mul, mul_one]
    rw[← add_assoc _ 1, Nat.sub_sub, add_comm 1, ←Nat.sub_sub, one_mul]
    have : 1 ≤ Felt252Prime - 2 ^ 29 := by --36
      unfold Felt252Prime
      norm_num
    rw [Nat.cast_sub this, Nat.cast_one, sub_add_cancel, ← (Nat.cast_add _ (2^29)), Nat.sub_add_cancel]
    have h_zero1 : (↑Felt252Prime : Felt252) = 0 := by
      unfold Felt252
      rw [ZMod.natCast_eq_zero_iff Felt252Prime Felt252Prime]

    rw[h_zero1, add_zero]

    rw[h_remainder_bits_eq, h2, one_mul]
    rw[Nat.cast_sub]

    apply congr_arg₂
    apply congr_arg₂
    apply congr_arg₂
    simp
    simp
    simp

    rw[← Nat.cast_sub]
    rw[(show (508:Felt) = ↑(508:Nat) by rfl)]
    rw[← Nat.cast_sub]
    rw[ZMod.val_natCast_of_lt]
    unfold Stwo.P

    calc
      value_n 3 - 508 ≤ 2 ^ 9 - 508 := by
        exact Nat.sub_le_sub_right (le_of_lt (h_rc 3).2) 508
      _ < Stwo.P := by
        unfold Stwo.P ; norm_num

    repeat
      rw [h2, ZMod.val_one'' h_ne_1, one_mul] at h_limb3_pos
      exact h_limb3_pos

    unfold Felt252Prime
    norm_num

  · exact h_limbs_lt

  · cases h_mid_limbs_set <;> rename _ => h1 <;> rw[h1]
    · rw[ZMod.val_zero, mul_zero, add_zero]
      calc
        ZMod.val msb ≤ 1 := by
          cases h_msb <;> rename _ => h2 <;> rw [h2] ;
          · rw[ZMod.val_zero]
            norm_num
          · rw[ZMod.val_one'' h_ne_1]
        _ ≤ (2 ^ 29 + 1) := by
          norm_num
        _ ≤ value_n 0 + value_n 1 * 2 ^ 9 + value_n 2 * 2 ^ 18 + (value_n 3 - 0 * 508) * 2 ^ 27 + (2 ^ 29 + 1) := by
          apply Nat.le_add_left

    · rw[ZMod.val_one'' h_ne_1, mul_one]
      calc
        ZMod.val msb + 2 ^ 29 * 1 ≤ 1 + 2 ^ 29 := by
          cases h_msb <;> rename _ => h2 <;> rw [h2] ;
          · rw[ZMod.val_zero]
            norm_num
          · rw[ZMod.val_one'' h_ne_1]
            norm_num
        _ ≤ value_n 0 + value_n 1 * 2 ^ 9 + value_n 2 * 2 ^ 18 + (value_n 3 - 1 * 508) * 2 ^ 27 + (2 ^ 29 + 1) := by
          apply Nat.le_add_left


  · rw[h_remainder_bits4]
    rw [Nat.add_sub_cancel]
    trans 512 + 512 * 2 ^ 9 + 512 * 2 ^ 18 + 4 * 2 ^ 27
    · gcongr
      exact h_limb0.2
      exact h_limb1.2
      exact h_limb2.2
    unfold Stwo.P ; norm_num1

-- {limb0 limb1 limb2 remainder_bits msb mid_limbs_set : Felt}
--       {value_n : Felt252Nats}
--       (h_rc : value_n.IsRangeChecked (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set))
--       (h_remainder_bits : remainder_bits.val < 4) --
--       (h_msb : msb = 0 ∨ msb = 1)
--       (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
--       (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
--       --
--       (small_to_rel_imm_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set).toFelt252 = value_n.eval := by

theorem read_small_mem [Fact (Nat.Prime Felt252Prime)]
   {address : CasmAddressVal}
   {value id : Felt}
   {mem : Felt252 → Felt252}
   {memoryAssign : Felt252IdMemoryAssign}
   (h_mem_rc: memoryAssign.IsRangeChecked) --
   (hmem: memoryAssign.Agrees mem)
   (h_read_small: ReadSmall.spec memoryAssign address value id):
  (mem address.toFelt252 = value.toFelt252) := by
  --sorry
  --have h_read_small2 := h_read_small
  --unfold ReadSmall.spec at h_read_small2
  unfold ReadSmall.spec at h_read_small
  rcases h_read_small with ⟨h1, msb, mid_limbs_set, h_decode,
                    low_limb0, low_limb1, low_limb2, remainder_bits,
                    h2, h_small_to_rel_imm_val, h_remainder_bits⟩
  --have h_decode2 := h_decode
  --unfold DecodeSmallSign.spec at h_decode
  rcases h_decode with ⟨h_msb, h_mid_limbs_set, h_msb_mls⟩
  --rw h1
  --have : memoryAssign.addressToId address = id
  have h_mem_hv : memoryAssign.HasValue address (small_to_felt252_val low_limb0 low_limb1 low_limb2 remainder_bits msb mid_limbs_set) := by
    use id
    constructor
    · convert h1 <;> simp
    · convert h2 ; simp

  have := Felt252IdMemoryAssign.IsRangeChecked_of_HasValue h_mem_rc h_mem_hv
  rcases this with ⟨value_nats, h_value_nats_rc⟩

  have h_value_nats_eval := small_to_felt252_eq_small_to_rel_imm h_value_nats_rc h_remainder_bits h_msb h_mid_limbs_set h_msb_mls
  rw[← h_small_to_rel_imm_val] at h_value_nats_eval
  rw[h_value_nats_eval]

  have := Felt252IdMemoryAssign.isRangeChecked_of_hasValue_of_agrees h_mem_rc h_mem_hv hmem
  rcases this with ⟨value_n, h_value_n_rc, h_mem_at_address⟩

  rw [h_mem_at_address]

  have := Felt252Nats.eq_of_IsRangeChecked_eq h_value_nats_rc h_value_n_rc
  rw[this]

  -- unfold Felt252Nats.eval
  -- apply Finset.sum_congr rfl
  -- intro i hi
  -- have : (value_n i) = (value_nats i) := by


  --rw[← h_small_to_rel_imm_val] at h_mem_hv

  --sorry


    -- ReadSmall.spec memory (casmStateVal.fp + offset_as_signed_Felt ρoffset0) dst_id (op0 + op1)
    -- ∀ mem : Felt252 → Felt252,
    --   memory.Agrees mem

theorem val_add_eq_add_eval_of_small
      {x : Felt}
      {nx : Nat}
      {limb0 limb1 limb2 remainder_bits msb mid_limbs_set : Felt}
      {value_n : Felt252Nats}
      (h_nx : x = ↑nx)
      (h_nx_lt : nx < 2 ^ 30 - 1)
      (h2 : value_n.IsRangeChecked (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set))
      (h_remainder_bits : remainder_bits.val < 4) --
      (h_msb : msb = 0 ∨ msb = 1)
      (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
      (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
    (x + small_to_rel_imm_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set).toFelt252 = x.toFelt252 + value_n.eval := by

  rw [small_to_rel_imm_val, sub_sub]

  unfold small_to_felt252_val at h2
  have h_limb0 := h2 0 ; simp at h_limb0
  have h_limb1 := h2 1 ; simp at h_limb1
  have h_limb2 := h2 2 ; simp at h_limb2
  have h_limb3 := h2 3 ; simp at h_limb3

  let lsb := (value_n 0 + value_n 1 * 2 ^ 9 + value_n 2 * 2 ^ 18 + (value_n 3 - mid_limbs_set.val * 0x1FC) * 2 ^ 27)

  have h_ne_1 : Stwo.P ≠ 1 := by unfold Stwo.P ; norm_num1

  have h_remainder_bits_eq : remainder_bits = ↑(value_n 3) - mid_limbs_set * 508 := by
    rw [← h_limb3.1]
    ring

  have h_remainder_bits2 : ↑(value_n 3) = remainder_bits + mid_limbs_set * 0x1FC := by
    rw [h_remainder_bits_eq]
    abel

  have h_remainder_bits3 : (↑(value_n 3):Felt).val = value_n 3 := by
    apply ZMod.val_natCast_of_lt
    unfold Stwo.P
    linarith [h_limb3.2]

  have h_remainder_bits4 : value_n 3 = remainder_bits.val + mid_limbs_set.val * 0x1FC := by
    rw [← h_remainder_bits3]
    rw [h_remainder_bits2]
    rw [ZMod.val_add_of_lt]
    rw [ZMod.val_mul]
    norm_num

    rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
    unfold Felt
    unfold Stwo.P
    rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]

    norm_num
    cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
    · rw[ZMod.val_zero]
      norm_num
    · rw[ZMod.val_one'' h_ne_1]
      norm_num

    calc
      remainder_bits.val + (mid_limbs_set * 508).val < 4 + (mid_limbs_set * 508).val := by
        apply add_lt_add_right h_remainder_bits
      _ < Stwo.P := by
        unfold Stwo.P
        cases h_mid_limbs_set <;> rename _ => h2 <;> rw [h2]
        · rw[zero_mul, ZMod.val_zero]
          norm_num1
        · rw[one_mul]
          rw [show (508 : Felt) = ↑ (508 : Nat) by rfl]
          unfold Felt
          unfold Stwo.P
          rw [ZMod.val_natCast_of_lt (show 508 < 2147483647 by norm_num)]
          norm_num1



  have h_limb3_pos : value_n 3 ≥ ZMod.val mid_limbs_set * 508 := by
    by_contra h_contra
    push_neg at h_contra
    have h_for_contra : ZMod.val remainder_bits > 5 := by
      rw [h_remainder_bits_eq]
      linarith -- really???
    linarith [h_limb3.2]

  --have := small_to_felt252_eval_4_eq_c2 h2 h_remainder_bits.2 h_msb h_mid_limbs_set h_msb_mls

  have obv1 : value_n 3 = ((value_n 3):Felt).val := by
    rw [ZMod.val_natCast_of_lt]
    unfold Stwo.P
    linarith

  have h4: (limb0 + limb1 * 2 ^ 9 + limb2 * 2 ^ 18 + remainder_bits * 2 ^ 27) = (↑ lsb : Felt) := by
    unfold lsb
    rw[h_limb0.1, h_limb1.1, h_limb2.1, h_remainder_bits_eq]
    simp
    norm_num

    rw[Nat.cast_sub]
    left
    cases h_mid_limbs_set <;> rename _ => h0 <;> rw [h0]
    · rw[ZMod.val_zero]
      norm_num
    · rw[ZMod.val_one'' h_ne_1]
      norm_num

    exact h_limb3_pos



  have h5_pre: (value_n 0 + value_n 1 * 2 ^ 9 + value_n 2 * 2 ^ 18 + (value_n 3 - mid_limbs_set.val * 0x1FC) * 2 ^ 27) ≤ 2^29 - 1 := by
    trans 511 + 511 * 2 ^ 9 + 511 * 2 ^ 18 + 3 * 2 ^ 27
    · gcongr
      exact Nat.le_of_lt_succ h_limb0.2
      exact Nat.le_of_lt_succ h_limb1.2
      exact Nat.le_of_lt_succ h_limb2.2
      rw [h_remainder_bits4, Nat.add_sub_cancel] --rw [← h_remainder_bits.1]
      exact Nat.le_of_lt_succ h_remainder_bits
    norm_num

  have h5 := Nat.lt_of_le_pred (show 0<2^29 by norm_num) h5_pre

  unfold lsb at h4

  let nz:= (msb + 2 ^ 29 * mid_limbs_set).val

  have h6 : (msb + 2 ^ 29 * mid_limbs_set) = ↑ nz := by --
    unfold nz
    cases h_mid_limbs_set <;> rename _ => htmp1 <;> rw [htmp1] <;>
    cases h_msb <;> rename _ => htmp2 <;> rw [htmp2] <;> norm_num <;> rfl

  have h7 : nz - lsb ≤ 2^29 + 1 := by -- !
    calc
      nz - lsb ≤ nz := by
        apply Nat.sub_le
      _ ≤ 2^29 + 1 := by
        unfold nz
        cases h_mid_limbs_set <;> rename _ => htmp1 <;> rw [htmp1] <;>
        cases h_msb <;> rename _ => htmp2 <;> rw [htmp2] <;> norm_num1
        · rw[ZMod.val_zero]
          norm_num
        · rw[ZMod.val_one'' h_ne_1]
          norm_num
        · rw [(show (536870912:Felt).val = 536870912 by rfl)]
          norm_num
        · rw [(show (536870913:Felt).val = 536870913 by rfl)]

  unfold lsb at h7


  rw [toFelt252_add_sub h_nx h_nx_lt h4 h5 h6 h7] -- !
  apply congr_arg₂ ; rfl

  rw [←small_to_felt252_eq_small_to_rel_imm h2 h_remainder_bits h_msb h_mid_limbs_set h_msb_mls]
  unfold small_to_rel_imm_val
  apply congr_arg
  ring


theorem val_add_eq_add_eval_of_small_bounded_steps
      {x : Felt}
      {limb0 limb1 limb2 remainder_bits msb mid_limbs_set : Felt}
      {value_n : Felt252Nats}
      {nx : Nat}
      (num_steps : Nat)
      (ns_lim : num_steps < 2^29) --
      (h_x_eq: x = ↑nx)
      --(h_nx_lt_pre : nx < 2 ^ 29 + 2 * num_steps)
      (h_nx_lt_pre : nx < 2 ^ 29 + num_steps) -- num_steps - 1? --
      (h2 : value_n.IsRangeChecked (small_to_felt252_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set))
      (h_remainder_bits : remainder_bits.val < 4) --
      (h_msb : msb = 0 ∨ msb = 1)
      (h_mid_limbs_set : mid_limbs_set = 0 ∨ mid_limbs_set = 1)
      (h_msb_mls: mid_limbs_set = 0 ∨ msb = 1):
    (x + small_to_rel_imm_val limb0 limb1 limb2 remainder_bits msb mid_limbs_set).toFelt252 = x.toFelt252 + value_n.eval := by

  have h_nx_lt : nx < 2 ^ 30 - 1 := by
    calc
      nx < 2 ^ 29 + num_steps := h_nx_lt_pre
      _ ≤ 2 ^ 29 + (2^29 - 1) := by
        apply Nat.add_le_add_left ((Nat.le_pred_iff_lt (show 0<2^29 by norm_num)).mpr ns_lim)
      _ = 2 ^ 30 -1 := by
        norm_num

  exact val_add_eq_add_eval_of_small h_x_eq h_nx_lt h2 h_remainder_bits h_msb h_mid_limbs_set h_msb_mls
