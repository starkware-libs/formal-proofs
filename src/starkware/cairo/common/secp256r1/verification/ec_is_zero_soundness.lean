/-
File: ec_is_zero_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
import .ec_verify_zero_soundness
import .ec_unreduced_mul_soundness
import .ec_nondet_bigint3_soundness
open tactic

open starkware.cairo.common.secp256r1.field
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.secp256r1.bigint

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.field.is_zero autogenerated soundness theorem -/

theorem auto_sound_is_zero
    -- arguments
    (range_check_ptr : F) (x : SumBigInt3 mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_is_zero σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 130))
    (h_mem_5 : mem_at mem code_unreduced_mul (σ.pc  - 117))
    (h_mem_7 : mem_at mem code_assert_165_bit (σ.pc  - 45))
    (h_mem_8 : mem_at mem code_verify_zero (σ.pc  - 34))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 6))
    (hin_x : x = cast_SumBigInt3 mem (σ.fp - 5))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 6)) (mem $ τ.ap - 2)
        (spec_is_zero mem κ range_check_ptr x (mem (τ.ap - 2)) (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_is_zero at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35⟩,
  -- if statement
  -- tempvar
  apply of_register_state,
  intros regstate_ιχ__temp53 regstateeq_ιχ__temp53,
  mkdef  hl_ιχ__temp53 : ιχ__temp53 = mem regstate_ιχ__temp53.ap,
  rw [regstateeq_ιχ__temp53] at hl_ιχ__temp53, try { dsimp at hl_ιχ__temp53 },
  -- ap += 1
  step_advance_ap hpc0 hpc1,
  step_jnz hpc2 hpc3 with hcond hcond,
  {
    -- if: positive branch
    have a0 : ιχ__temp53 = 0, {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53] },
      try { dsimp [cast_SumBigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- jump statement
    step_jump_imm hpc4 hpc5,
    -- function call
    step_assert_eq hpc15 with arg0,
    step_sub hpc16 (auto_sound_nondet_bigint3 mem _ range_check_ptr _ _),
    { rw hpc17, norm_num2, exact h_mem_4 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53] },
      try { dsimp [cast_SumBigInt3] },
      try { arith_simps }, try { simp only [arg0] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    intros κ_call18 ap18 h_call18,
    rcases h_call18 with ⟨h_call18_ap_offset, h_call18⟩,
    rcases h_call18 with ⟨rc_m18, rc_mle18, hl_range_check_ptr₁, h_call18⟩,
    mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap18 - 4)),
    simp only [←htv_range_check_ptr₁] at h_call18,
    mkdef htv_x_inv : x_inv = (cast_BigInt3 mem (ap18 - 3)),
    simp only [←htv_x_inv] at h_call18,
    try { simp only [arg0] at hl_range_check_ptr₁ },
    try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
    try { simp only [arg0] at h_call18 },
    rw [hin_range_check_ptr] at h_call18,
    clear arg0,
    -- function call
    step_assert_eq hpc18 with arg0,
    step_assert_eq hpc19 with arg1,
    step_assert_eq hpc20 with arg2,
    step_assert_eq hpc21 with arg3,
    step_assert_eq hpc22 with arg4,
    step_assert_eq hpc23 with arg5,
    step_sub hpc24 (auto_sound_unreduced_mul mem _ {
      d0 := x.d0,
      d1 := x.d1,
      d2 := x.d2
    } x_inv _ _ _),
    { rw hpc25, norm_num2, exact h_mem_5 },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁, htv_x_inv] },
        try { dsimp [cast_SumBigInt3, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
        try { simp only [h_call18_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁, htv_x_inv] },
        try { dsimp [cast_SumBigInt3, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
        try { simp only [h_call18_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call26 ap26 h_call26,
    rcases h_call26 with ⟨h_call26_ap_offset, h_call26⟩,
    mkdef htv_x_x_inv : x_x_inv = (cast_UnreducedBigInt3 mem (ap26 - 3)),
    simp only [←htv_x_x_inv] at h_call26,
    clear arg0 arg1 arg2 arg3 arg4 arg5,
    -- function call
    step_assert_eq hpc26 with arg0,
    step_assert_eq hpc27 hpc28 with arg1,
    step_assert_eq hpc29 with arg2,
    step_assert_eq hpc30 with arg3,
    step_sub hpc31 (auto_sound_verify_zero mem _ range_check_ptr₁ {
      d0 := x_x_inv.d0 - 1,
      d1 := x_x_inv.d1,
      d2 := x_x_inv.d2
    } _ _ _ _),
    { rw hpc32, norm_num2, exact h_mem_8 },
    { rw hpc32, norm_num2, exact h_mem_7 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁, htv_x_inv, htv_x_x_inv] },
      try { dsimp [cast_SumBigInt3, cast_BigInt3, cast_UnreducedBigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
      try { simp only [h_call18_ap_offset, h_call26_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁, htv_x_inv, htv_x_x_inv] },
        try { dsimp [cast_SumBigInt3, cast_BigInt3, cast_UnreducedBigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
        try { simp only [h_call18_ap_offset, h_call26_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call33 ap33 h_call33,
    rcases h_call33 with ⟨h_call33_ap_offset, h_call33⟩,
    rcases h_call33 with ⟨rc_m33, rc_mle33, hl_range_check_ptr₂, h_call33⟩,
    mkdef htv_range_check_ptr₂ : range_check_ptr₂ = (mem (ap33 - 1)),
    simp only [←htv_range_check_ptr₂] at h_call33,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3] at hl_range_check_ptr₂ },
    try { rw [h_call26_ap_offset] at hl_range_check_ptr₂ }, try { arith_simps at hl_range_check_ptr₂ },
    try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₂ }, try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₂ },
    try { simp only [arg0 ,arg1 ,arg2 ,arg3] at h_call33 },
    try { rw [h_call26_ap_offset] at h_call33 }, try { arith_simps at h_call33 },
    rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call33,
    clear arg0 arg1 arg2 arg3,
    -- return
    step_assert_eq hpc33 hpc34 with hret0,
    step_ret hpc35,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (rc_m18+rc_m33+0+0), split,
    linarith [rc_mle18, rc_mle33],
    split,
    { try { norm_num1 }, arith_simps, try { simp only [hret0] },
      try { rw [←htv_range_check_ptr₂] }, try { rw [hl_range_check_ptr₂] }, try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_is_zero mem _ range_check_ptr x _ _,
    { apply sound_is_zero, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_is_zero],
    try { norm_num1 }, try { arith_simps },
    use_only [ιχ__temp53],
    right,
    use_only [a0],
    use_only [κ_call18],
    use_only [range_check_ptr₁],
    use_only [x_inv],
    have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
    have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
    have spec18 := h_call18 rc_h_range_check_ptr',
      try { rw [←hin_range_check_ptr] at spec18 }, try { rw [←htv_range_check_ptr₁] at spec18 },
    try { dsimp at spec18, arith_simps at spec18 },
    use_only [spec18],
    use_only [κ_call26],
    use_only [x_x_inv],
    try { dsimp at h_call26, arith_simps at h_call26 },
    try { use_only [h_call26] },
    use_only [κ_call33],
    use_only [range_check_ptr₂],
    have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
    have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
    have spec33 := h_call33 rc_h_range_check_ptr₁',
      try { rw [←hin_range_check_ptr] at spec33 }, try { rw [←hl_range_check_ptr₁] at spec33 }, try { rw [←htv_range_check_ptr₂] at spec33 },
    try { dsimp at spec33, arith_simps at spec33 },
    use_only [spec33],
    try { split, trivial <|> linarith },
    try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁, htv_x_inv, htv_x_x_inv, htv_range_check_ptr₂] }, },
    try { dsimp [cast_SumBigInt3, cast_BigInt3, cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [hret0] },
    try { simp only [h_call18_ap_offset, h_call26_ap_offset, h_call33_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  {
    -- if: negative branch
    have a0 : ιχ__temp53 ≠ 0, {
      try { simp only [ne.def] },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53] },
      try { dsimp [cast_SumBigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- function call
    step_assert_eq hpc6 with arg0,
    step_assert_eq hpc7 with arg1,
    step_assert_eq hpc8 with arg2,
    step_assert_eq hpc9 with arg3,
    step_sub hpc10 (auto_sound_verify_zero mem _ range_check_ptr {
      d0 := x.d0,
      d1 := x.d1,
      d2 := x.d2
    } _ _ _ _),
    { rw hpc11, norm_num2, exact h_mem_8 },
    { rw hpc11, norm_num2, exact h_mem_7 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53] },
      try { dsimp [cast_SumBigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53] },
        try { dsimp [cast_SumBigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call12 ap12 h_call12,
    rcases h_call12 with ⟨h_call12_ap_offset, h_call12⟩,
    rcases h_call12 with ⟨rc_m12, rc_mle12, hl_range_check_ptr₁, h_call12⟩,
    mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap12 - 1)),
    simp only [←htv_range_check_ptr₁] at h_call12,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3] at hl_range_check_ptr₁ },
    try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
    try { simp only [arg0 ,arg1 ,arg2 ,arg3] at h_call12 },
    rw [hin_range_check_ptr] at h_call12,
    clear arg0 arg1 arg2 arg3,
    -- return
    step_assert_eq hpc12 hpc13 with hret0,
    step_ret hpc14,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (rc_m12+0+0), split,
    linarith [rc_mle12],
    split,
    { try { norm_num1 }, arith_simps, try { simp only [hret0] },
      try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_is_zero mem _ range_check_ptr x _ _,
    { apply sound_is_zero, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_is_zero],
    try { norm_num1 }, try { arith_simps },
    use_only [ιχ__temp53],
    left,
    use_only [a0],
    use_only [κ_call12],
    use_only [range_check_ptr₁],
    have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
    have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
    have spec12 := h_call12 rc_h_range_check_ptr',
      try { rw [←hin_range_check_ptr] at spec12 }, try { rw [←htv_range_check_ptr₁] at spec12 },
    try { dsimp at spec12, arith_simps at spec12 },
    use_only [spec12],
    try { split, trivial <|> linarith },
    try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, hl_ιχ__temp53, htv_range_check_ptr₁] }, },
    try { dsimp [cast_SumBigInt3] },
    try { arith_simps }, try { simp only [hret0] },
    try { simp only [h_call12_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  }
end

