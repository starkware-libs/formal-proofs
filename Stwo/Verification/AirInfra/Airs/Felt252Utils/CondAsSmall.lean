import Verification.AirInfra.Core.Expressions.Expr
import Verification.AirInfra.Core.Expressions.Felt252Expr
import Verification.AirInfra.Core.AirFn
import Verification.AirInfra.Core.Felt252IdMemory.ReadSmall
import Verification.AirInfra.Airs.Casm.Opcodes.Util

open Fin.NatCast



namespace CondFelt252AsAddr

def call
    (airBuilder : AirBuilder)
    (value: Felt252Expr)
    (condition : FeltExpr) :
    AirBuilder × CasmAddress :=
      let ab := forLoop LIMBS_IN_M31 FELT252_N_WORDS airBuilder
        fun i ab => ab.constrain (condition * value i)
      let ab2 := CondRangeCheck2.call ab (value 3) (FeltExpr.const 1)
      (ab2, felt252_to_m31 value ADDRESS_BITS)

def spec_auto (value: Felt252Words) (condition : Felt) (ρm31_value : Felt) : Prop :=
  (∀ i : Fin FELT252_N_WORDS, LIMBS_IN_M31 ≤ i → condition * (value i) = 0) ∧
  ρm31_value = felt252_to_m31_val value ADDRESS_BITS ∧ (CondRangeCheck2.spec (value 3) condition) -- ?

def spec (value: Felt252Words) (condition : Felt) (ρm31_value : Felt) : Prop :=
  ρm31_value = felt252_to_m31_val value ADDRESS_BITS
  ∧ (condition ≠ 0 → ((Felt252Nats.ExistsIsRangeChecked value → ρm31_value.toFelt252 = value.eval) ∧ ((value 3).val < 4)))

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    (value: Felt252Words)
    (condition : Felt)
    (ρm31_value : Felt)
    (h_spec_auto : spec_auto value condition ρm31_value) :
    spec value condition ρm31_value := by
  use h_spec_auto.2.1
  intro h_condition
  constructor
  · intro h_rc
    rcases h_rc with ⟨n_value, h_value_rc⟩
    rw [h_spec_auto.2.1, Felt252Nats.eval_Felt252Words_eq h_value_rc]
    apply felt252_to_m31_eq _ _ _ h_value_rc
    simp [ReadPositive.has_num_bits, ADDRESS_BITS, FELT252_BITS_PER_WORD, Nat.div_ceil]
    constructor
    · unfold spec_auto at h_spec_auto
      have := h_spec_auto.2.2
      unfold CondRangeCheck2.spec at this
      simp[h_condition] at this
      use ZMod.val (value 3)
      simp only [Fin.isValue, Nat.reducePow, this, true_and]
      unfold Felt
      norm_num
    intro i h_le
    cases' mul_eq_zero.mp (h_spec_auto.1 i h_le) with h_eq h_eq
    · exfalso ; exact h_condition h_eq
    exact h_eq
  have := h_spec_auto.2.2
  unfold CondRangeCheck2.spec at this
  simp[h_condition] at this
  exact this


theorem sound_auto [Fact (Nat.Prime Stwo.P)]
      (varAssign : VarAssign)
      (ab : AirBuilder)
      (value: Felt252Expr)
      (condition : FeltExpr) :
    let ⟨new_ab, casmAddr⟩ := call ab value condition
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧ spec (fun i => (value i).eval varAssign) (condition.eval varAssign) (casmAddr.eval varAssign) := by
  unfold call ; lift_lets
  intro ab1
  intro ab2
  intro hab2
  rcases CondRangeCheck2.sound_auto hab2 with ⟨hab1, h_cond_rc⟩
  have ⟨hab, h_cond⟩ := (AirBuilder.constraint_loop_SatisfiedBy _ varAssign _ _ (by unfold LIMBS_IN_M31 ; norm_num) _).mp hab1
  use hab
  apply spec_of_spec_auto
  constructor
  · intro i h_i
    have h := h_cond i.val h_i (Fin.isLt i)
    simp only [Fin.cast_val_eq_self, FeltExpr.eval_mul] at h
    exact h
  constructor
  · rfl
  have := (CondRangeCheck2.sound_auto hab2).2
  simp
  unfold CondRangeCheck2.spec
  unfold CondRangeCheck2.spec at this
  simp at this
  right
  exact this

end CondFelt252AsAddr



namespace CondFelt252AsRelImm


def call
    (airBuilder : AirBuilder)
    (value: Felt252Expr)
    (condition : FeltExpr) :
    AirBuilder × FeltExpr :=
  let _state := DecodeSmallSign.call airBuilder
  let ab1 := _state.1
  let msb := _state.2.1
  let mid_limbs := _state.2.2
  let limb0 := value 0
  let limb1 := value 1
  let limb2 := value 2
  let limb3 := value 3
  let remainder_bits := limb3 - mid_limbs * FeltExpr.const (0x1FC)
  let expected_value := small_to_felt252 limb0 limb1 limb2 remainder_bits msb mid_limbs
  let ab2 := CondRangeCheck2.call ab1 remainder_bits (FeltExpr.const 1)
  let ab3 := forLoop LIMBS_IN_M31 FELT252_N_WORDS ab2
    fun i ab => ab.constrain (condition * (value i - expected_value i))
  (ab3, small_to_rel_imm limb0 limb1 limb2 remainder_bits msb mid_limbs)

def spec_auto
    (value: Felt252Words)
    (condition : Felt)
    (ρvalue : Felt) : Prop :=
  ∃ msb mid_limbs, DecodeSmallSign.spec msb mid_limbs ∧
    ∃ expected_value, expected_value =
      small_to_felt252_val (value 0) (value 1) (value 2) ((value 3) - mid_limbs * 0x1FC) msb mid_limbs ∧
      (∀ i : Fin FELT252_N_WORDS, LIMBS_IN_M31 ≤ i.val → condition * (value i - expected_value i) = 0) ∧
      ρvalue = small_to_rel_imm_val (value 0) (value 1) (value 2) ((value 3) - mid_limbs * 0x1FC) msb mid_limbs ∧
      CondRangeCheck2.spec ((value 3) - mid_limbs * 0x1FC) condition

def spec
    (value: Felt252Words)
    (condition : Felt)
    (ρvalue : Felt) : Prop :=
    condition ≠ 0 → -- num_steps < 2^29 → casmStateVal.strongly_bounded num_steps →
      ρvalue = Felt252_to_rel_imm_val value
      ∧ (Felt252Nats.ExistsIsRangeChecked value →
          ρvalue.toFelt252 = value.eval
          ∧ ∀ num_steps < 2^29, ∀(x:Felt), (∃ n : Nat, (n < 2^29 + num_steps) ∧ x = ↑n) → (x + ρvalue).toFelt252 = x.toFelt252 + ρvalue.toFelt252
      ) --∧
      --CondRangeCheck2.spec ((value 3) - mid_limbs * 0x1FC) condition

theorem spec_of_spec_auto [Fact (Nat.Prime Stwo.P)]
    (value: Felt252Words)
    (condition : Felt)
    (ρvalue : Felt)
    (h_spec_auto : spec_auto value condition ρvalue) :
    spec value condition ρvalue := by
  intro h_condition
  rcases h_spec_auto with ⟨msb, mid_limbs, small_sign_spec, expected_value, h_expected_value_eq, h_value_eq, h_ρvalue, h_cond_rc2⟩
  have h_n (n : Nat) (h1 : n < FELT252_N_WORDS) : value n = expected_value n := by
    by_cases h : n < (LIMBS_IN_M31 - 1)
    · unfold LIMBS_IN_M31 at h
      rw [h_expected_value_eq]
      have h_lt_3 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      cases' h_lt_3 with h h ; rw [h] ; rfl ; cases' h with h h <;> rw [h] <;> rfl
    by_cases h_b : n = (LIMBS_IN_M31 - 1)
    · unfold LIMBS_IN_M31 at h_b
      simp at h_b
      rw [h_b]
      rw [h_expected_value_eq]
      simp
      rw [small_to_felt252_val]
      simp
    have : n ≥ LIMBS_IN_M31 := by omega
    cases' mul_eq_zero.mp (h_value_eq n (by rw [Fin.val_cast_of_lt h1] ; exact this)) with h h
    · exfalso ; exact h_condition h
    exact sub_eq_zero.mp h
  constructor
  · rw [h_ρvalue]
    have h_mid_limbs : mid_limbs = if value (↑(20 : Nat):(Fin FELT252_N_WORDS)) = ↑511 then 1 else 0 := by
      rw [h_n 20 (by norm_num1)]
      simp [h_expected_value_eq, small_to_felt252_val]
      cases' small_sign_spec.2.1 with h h
      · simp [h]
        by_contra h'
        have : (511:Felt) = (↑(511:Nat):Felt) := by
          simp
        rw[this] at h'
        unfold Felt at h'
        have := (ZMod.natCast_eq_zero_iff 511 Stwo.P).mp h'.symm
        unfold Stwo.P at this
        have := Nat.le_of_dvd (show 0<511 by norm_num) this
        linarith

      rw [h, one_mul]
      rw [if_pos _] ; rw [if_pos _]
      constructor
      · trans 20 ; norm_num1 ; rfl
      apply lt_of_le_of_lt _ (show 20 < 21 by norm_num1)
      rfl

    congr
    · simp
      unfold small_to_rel_imm_val at h_ρvalue
      rw[h_mid_limbs]
      simp
      by_cases h : value 20 = 511
      · simp [h]
      · simp [h]

    · rw [h_n 27 (by norm_num1)]
      simp [h_expected_value_eq, small_to_felt252_val]
      cases' small_sign_spec.1 with h h <;> simp [h]
      decide

  have h_eq : value = expected_value := by
    apply funext ; intro n ; rw [←Fin.cast_val_eq_self n] ; apply h_n n.val (Fin.isLt n)
  intro h_rc
  rcases h_rc with ⟨value_n, h_rc⟩
  rw [←h_eq] at h_expected_value_eq
  rw [Felt252Nats.eval_Felt252Words_eq h_rc, h_ρvalue]
  rw [h_expected_value_eq] at h_rc
  have h_remainder_bits : ZMod.val (value 3 - mid_limbs * 508) < 4 := by
    unfold CondRangeCheck2.spec at h_cond_rc2
    simp[h_condition] at h_cond_rc2
    exact h_cond_rc2
  have h_eq_eval := Felt252IdMemory.small_to_felt252_eq_small_to_rel_imm h_rc h_remainder_bits small_sign_spec.1 small_sign_spec.2.1
  use h_eq_eval small_sign_spec.2.2
  intro ns hns
  intro x h_x
  rcases h_x with ⟨nx, h_nx_lt, h_nx_eq⟩
  rw [h_eq_eval]
  have h_nx_lt' : nx < 2 ^ 30 -1 := by
    omega
  apply Felt252IdMemory.val_add_eq_add_eval_of_small h_nx_eq h_nx_lt' h_rc h_remainder_bits small_sign_spec.1 small_sign_spec.2.1 small_sign_spec.2.2
  exact small_sign_spec.2.2


theorem sound_auto [Fact (Nat.Prime Stwo.P)]
      (varAssign : VarAssign)
      (ab : AirBuilder)
      (value: Felt252Expr)
      (condition : FeltExpr) :
    let ⟨new_ab, ρvalue_m31⟩ := call ab value condition
    new_ab.SatisfiedBy varAssign →
      ab.SatisfiedBy varAssign ∧
      spec (value.eval varAssign) (condition.eval varAssign) (ρvalue_m31.eval varAssign) := by
  unfold call ; lift_lets
  intro state1 ab2 msb mid_limbs
    limb0 limb1 limb2 limb3 remainder_bits expected_value
    ab3 ab4 hab4

  have ⟨hab3, h_cond⟩ := (AirBuilder.constraint_loop_SatisfiedBy _ varAssign _ _ (by unfold LIMBS_IN_M31 ; norm_num) _).mp hab4
  rcases CondRangeCheck2.sound_auto hab3 with ⟨hab2, h_cond_rc⟩
  have ⟨hab, h_decode_small_sign⟩ := DecodeSmallSign.sound_auto hab2

  use hab
  apply spec_of_spec_auto

  use msb.eval varAssign, mid_limbs.eval varAssign, h_decode_small_sign
  use expected_value.eval varAssign
  constructor
  · apply small_to_felt252_eval
  constructor
  · intro i h_i
    replace h_cond := h_cond i.val h_i (i.isLt)
    simp only [FeltExpr.eval_mul, FeltExpr.eval_sub, Fin.cast_val_eq_self] at h_cond
    exact h_cond
  constructor
  · apply small_to_rel_imm_val_eval
  have := (CondRangeCheck2.sound_auto hab3).2
  unfold CondRangeCheck2.spec
  unfold CondRangeCheck2.spec at this
  simp at this
  right
  exact this

end CondFelt252AsRelImm
