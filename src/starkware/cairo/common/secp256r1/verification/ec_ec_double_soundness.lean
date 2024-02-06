/-
File: ec_ec_double_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
import .ec_compute_doubling_slope_soundness
open tactic

open starkware.cairo.common.secp256r1.ec
open starkware.cairo.common.secp256r1.bigint
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.cairo_secp.ec_point
open starkware.cairo.common.secp256r1.field

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.ec.ec_double autogenerated soundness theorem -/

theorem auto_sound_ec_double_block5
    -- An independent ap variable.
    (ap : F)
    -- arguments
    (range_check_ptr : F) (point : EcPoint mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_ec_double σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 289))
    (h_mem_5 : mem_at mem code_unreduced_mul (σ.pc  - 276))
    (h_mem_6 : mem_at mem code_unreduced_sqr (σ.pc  - 238))
    (h_mem_7 : mem_at mem code_assert_165_bit (σ.pc  - 204))
    (h_mem_8 : mem_at mem code_verify_zero (σ.pc  - 193))
    (h_mem_12 : mem_at mem code_compute_doubling_slope (σ.pc  - 70))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 9))
    (hin_point : point = cast_EcPoint mem (σ.fp - 8))
    (νbound : ℕ)
    -- conclusion
  : ensuresb_ret νbound mem
    {pc := σ.pc + 14, ap := ap, fp := σ.fp}
    (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 9)) (mem $ τ.ap - 7)
        (auto_spec_ec_double_block5 mem κ range_check_ptr point (mem (τ.ap - 7)) (cast_EcPoint  mem (τ.ap - 6)))) :=
begin
  have h_mem_rec := h_mem,
  unpack_memory code_ec_double at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37, hpc38, hpc39, hpc40, hpc41, hpc42, hpc43, hpc44, hpc45, hpc46, hpc47, hpc48, hpc49, hpc50, hpc51, hpc52, hpc53, hpc54, hpc55, hpc56, hpc57, hpc58, hpc59, hpc60, hpc61, hpc62, hpc63, hpc64, hpc65, hpc66, hpc67, hpc68, hpc69, hpc70, hpc71, hpc72⟩,
  -- function call
  step_assert_eq hpc14 with arg0,
  step_assert_eq hpc15 with arg1,
  step_assert_eq hpc16 with arg2,
  step_assert_eq hpc17 with arg3,
  step_assert_eq hpc18 with arg4,
  step_assert_eq hpc19 with arg5,
  step_assert_eq hpc20 with arg6,
  step_sub hpc21 (auto_sound_compute_doubling_slope mem _ range_check_ptr point _ _ _ _ _ _ _ _),
  { rw hpc22, norm_num2, exact h_mem_12 },
  { rw hpc22, norm_num2, exact h_mem_4 },
  { rw hpc22, norm_num2, exact h_mem_5 },
  { rw hpc22, norm_num2, exact h_mem_6 },
  { rw hpc22, norm_num2, exact h_mem_7 },
  { rw hpc22, norm_num2, exact h_mem_8 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
    try { dsimp [cast_EcPoint, cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call23 ap23 h_call23,
  rcases h_call23 with ⟨h_call23_ap_offset, h_call23⟩,
  rcases h_call23 with ⟨rc_m23, rc_mle23, hl_range_check_ptr₁, h_call23⟩,
  mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap23 - 4)),
  simp only [←htv_range_check_ptr₁] at h_call23,
  mkdef htv_slope : slope = (cast_BigInt3 mem (ap23 - 3)),
  simp only [←htv_slope] at h_call23,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at hl_range_check_ptr₁ },
  try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at h_call23 },
  rw [hin_range_check_ptr] at h_call23,
  clear arg0 arg1 arg2 arg3 arg4 arg5 arg6,
  -- function call
  step_sub hpc23 (auto_sound_unreduced_sqr mem _ slope _ _),
  { rw hpc24, norm_num2, exact h_mem_6 },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { simp only [h_call23_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call25 ap25 h_call25,
  rcases h_call25 with ⟨h_call25_ap_offset, h_call25⟩,
  mkdef htv_slope_sqr : slope_sqr = (cast_UnreducedBigInt3 mem (ap25 - 3)),
  simp only [←htv_slope_sqr] at h_call25,
  clear ,
  -- function call
  step_assert_eq hpc25 with arg0,
  step_sub hpc26 (auto_sound_nondet_bigint3 mem _ range_check_ptr₁ _ _),
  { rw hpc27, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr] },
    try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { simp only [h_call23_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call28 ap28 h_call28,
  rcases h_call28 with ⟨h_call28_ap_offset, h_call28⟩,
  rcases h_call28 with ⟨rc_m28, rc_mle28, hl_range_check_ptr₂, h_call28⟩,
  mkdef htv_range_check_ptr₂ : range_check_ptr₂ = (mem (ap28 - 4)),
  simp only [←htv_range_check_ptr₂] at h_call28,
  mkdef htv_new_x : new_x = (cast_BigInt3 mem (ap28 - 3)),
  simp only [←htv_new_x] at h_call28,
  try { simp only [arg0] at hl_range_check_ptr₂ },
  try { rw [h_call25_ap_offset] at hl_range_check_ptr₂ }, try { arith_simps at hl_range_check_ptr₂ },
  try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₂ }, try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₂ },
  try { simp only [arg0] at h_call28 },
  try { rw [h_call25_ap_offset] at h_call28 }, try { arith_simps at h_call28 },
  rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call28,
  clear arg0,
  -- function call
  step_assert_eq hpc28 with arg0,
  step_sub hpc29 (auto_sound_nondet_bigint3 mem _ range_check_ptr₂ _ _),
  { rw hpc30, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x] },
    try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call31 ap31 h_call31,
  rcases h_call31 with ⟨h_call31_ap_offset, h_call31⟩,
  rcases h_call31 with ⟨rc_m31, rc_mle31, hl_range_check_ptr₃, h_call31⟩,
  mkdef htv_range_check_ptr₃ : range_check_ptr₃ = (mem (ap31 - 4)),
  simp only [←htv_range_check_ptr₃] at h_call31,
  mkdef htv_new_y : new_y = (cast_BigInt3 mem (ap31 - 3)),
  simp only [←htv_new_y] at h_call31,
  try { simp only [arg0] at hl_range_check_ptr₃ },
  try { rw [←htv_range_check_ptr₃] at hl_range_check_ptr₃ }, try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₃ },
  try { simp only [arg0] at h_call31 },
  rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call31,
  clear arg0,
  -- function call
  step_assert_eq hpc31 with arg0,
  step_assert_eq hpc32 hpc33 with arg1,
  step_assert_eq hpc34 with arg2,
  step_assert_eq hpc35 with arg3,
  step_assert_eq hpc36 hpc37 with arg4,
  step_assert_eq hpc38 with arg5,
  step_assert_eq hpc39 with arg6,
  step_assert_eq hpc40 hpc41 with arg7,
  step_assert_eq hpc42 with arg8,
  step_assert_eq hpc43 with arg9,
  step_assert_eq hpc44 with arg10,
  step_assert_eq hpc45 with arg11,
  step_assert_eq hpc46 with arg12,
  step_sub hpc47 (auto_sound_verify_zero mem _ range_check_ptr₃ {
    d0 := slope_sqr.d0 - new_x.d0 - 2 * point.x.d0,
    d1 := slope_sqr.d1 - new_x.d1 - 2 * point.x.d1,
    d2 := slope_sqr.d2 - new_x.d2 - 2 * point.x.d2
  } _ _ _ _),
  { rw hpc48, norm_num2, exact h_mem_8 },
  { rw hpc48, norm_num2, exact h_mem_7 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y] },
    try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), arg1, arg2, (eq_sub_of_eq_add arg3), arg4, arg5, (eq_sub_of_eq_add arg6), arg7, arg8, arg9, (eq_sub_of_eq_add arg10), (eq_sub_of_eq_add arg11), (eq_sub_of_eq_add arg12)] },
    try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y] },
      try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), arg1, arg2, (eq_sub_of_eq_add arg3), arg4, arg5, (eq_sub_of_eq_add arg6), arg7, arg8, arg9, (eq_sub_of_eq_add arg10), (eq_sub_of_eq_add arg11), (eq_sub_of_eq_add arg12)] },
      try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call49 ap49 h_call49,
  rcases h_call49 with ⟨h_call49_ap_offset, h_call49⟩,
  rcases h_call49 with ⟨rc_m49, rc_mle49, hl_range_check_ptr₄, h_call49⟩,
  mkdef htv_range_check_ptr₄ : range_check_ptr₄ = (mem (ap49 - 1)),
  simp only [←htv_range_check_ptr₄] at h_call49,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12] at hl_range_check_ptr₄ },
  try { rw [←htv_range_check_ptr₄] at hl_range_check_ptr₄ }, try { rw [←htv_range_check_ptr₃] at hl_range_check_ptr₄ },
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12] at h_call49 },
  rw [←htv_range_check_ptr₃, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call49,
  clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12,
  -- function call
  step_assert_eq hpc49 with arg0,
  step_assert_eq hpc50 with arg1,
  step_assert_eq hpc51 with arg2,
  step_assert_eq hpc52 with arg3,
  step_assert_eq hpc53 with arg4,
  step_assert_eq hpc54 with arg5,
  step_sub hpc55 (auto_sound_unreduced_mul mem _ {
    d0 := point.x.d0 - new_x.d0,
    d1 := point.x.d1 - new_x.d1,
    d2 := point.x.d2 - new_x.d2
  } slope _ _ _),
  { rw hpc56, norm_num2, exact h_mem_5 },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y, htv_range_check_ptr₄] },
      try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), arg3, arg4, arg5] },
      try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset, h_call49_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y, htv_range_check_ptr₄] },
      try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), arg3, arg4, arg5] },
      try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset, h_call49_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call57 ap57 h_call57,
  rcases h_call57 with ⟨h_call57_ap_offset, h_call57⟩,
  mkdef htv_x_diff_slope : x_diff_slope = (cast_UnreducedBigInt3 mem (ap57 - 3)),
  simp only [←htv_x_diff_slope] at h_call57,
  clear arg0 arg1 arg2 arg3 arg4 arg5,
  -- function call
  step_assert_eq hpc57 with arg0,
  step_assert_eq hpc58 with arg1,
  step_assert_eq hpc59 with arg2,
  step_assert_eq hpc60 with arg3,
  step_assert_eq hpc61 with arg4,
  step_assert_eq hpc62 with arg5,
  step_assert_eq hpc63 with arg6,
  step_sub hpc64 (auto_sound_verify_zero mem _ range_check_ptr₄ {
    d0 := x_diff_slope.d0 - point.y.d0 - new_y.d0,
    d1 := x_diff_slope.d1 - point.y.d1 - new_y.d1,
    d2 := x_diff_slope.d2 - point.y.d2 - new_y.d2
  } _ _ _ _),
  { rw hpc65, norm_num2, exact h_mem_8 },
  { rw hpc65, norm_num2, exact h_mem_7 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y, htv_range_check_ptr₄, htv_x_diff_slope] },
    try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), arg3, (eq_sub_of_eq_add arg4), (eq_sub_of_eq_add arg5), (eq_sub_of_eq_add arg6)] },
    try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset, h_call49_ap_offset, h_call57_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y, htv_range_check_ptr₄, htv_x_diff_slope] },
      try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add arg0), (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), arg3, (eq_sub_of_eq_add arg4), (eq_sub_of_eq_add arg5), (eq_sub_of_eq_add arg6)] },
      try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset, h_call49_ap_offset, h_call57_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call66 ap66 h_call66,
  rcases h_call66 with ⟨h_call66_ap_offset, h_call66⟩,
  rcases h_call66 with ⟨rc_m66, rc_mle66, hl_range_check_ptr₅, h_call66⟩,
  mkdef htv_range_check_ptr₅ : range_check_ptr₅ = (mem (ap66 - 1)),
  simp only [←htv_range_check_ptr₅] at h_call66,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at hl_range_check_ptr₅ },
  try { rw [h_call57_ap_offset] at hl_range_check_ptr₅ }, try { arith_simps at hl_range_check_ptr₅ },
  try { rw [←htv_range_check_ptr₅] at hl_range_check_ptr₅ }, try { rw [←htv_range_check_ptr₄] at hl_range_check_ptr₅ },
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at h_call66 },
  try { rw [h_call57_ap_offset] at h_call66 }, try { arith_simps at h_call66 },
  rw [←htv_range_check_ptr₄, hl_range_check_ptr₄, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call66,
  clear arg0 arg1 arg2 arg3 arg4 arg5 arg6,
  -- return
  step_assert_eq hpc66 with hret0,
  step_assert_eq hpc67 with hret1,
  step_assert_eq hpc68 with hret2,
  step_assert_eq hpc69 with hret3,
  step_assert_eq hpc70 with hret4,
  step_assert_eq hpc71 with hret5,
  step_ret hpc72,
  -- finish
  step_done, use_only [rfl, rfl],
  -- range check condition
  use_only (rc_m23+rc_m28+rc_m31+rc_m49+rc_m66+0+0), split,
  linarith [rc_mle23, rc_mle28, rc_mle31, rc_mle49, rc_mle66],
  split,
  { try { norm_num1 }, arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5] },
    try { rw [←htv_range_check_ptr₅] }, try { rw [hl_range_check_ptr₅] }, try { rw [←htv_range_check_ptr₄] }, try { rw [hl_range_check_ptr₄] }, try { rw [←htv_range_check_ptr₃] }, try { rw [hl_range_check_ptr₃] }, try { rw [←htv_range_check_ptr₂] }, try { rw [hl_range_check_ptr₂] }, try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  dsimp [auto_spec_ec_double_block5],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call23],
  use_only [range_check_ptr₁],
  use_only [slope],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec23 := h_call23 rc_h_range_check_ptr',
    try { rw [←hin_range_check_ptr] at spec23 }, try { rw [←htv_range_check_ptr₁] at spec23 },
  try { dsimp at spec23, arith_simps at spec23 },
  use_only [spec23],
  use_only [κ_call25],
  use_only [slope_sqr],
  try { dsimp at h_call25, arith_simps at h_call25 },
  try { use_only [h_call25] },
  use_only [κ_call28],
  use_only [range_check_ptr₂],
  use_only [new_x],
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
  have spec28 := h_call28 rc_h_range_check_ptr₁',
    try { rw [←hin_range_check_ptr] at spec28 }, try { rw [←hl_range_check_ptr₁] at spec28 }, try { rw [←htv_range_check_ptr₂] at spec28 },
  try { dsimp at spec28, arith_simps at spec28 },
  use_only [spec28],
  use_only [κ_call31],
  use_only [range_check_ptr₃],
  use_only [new_y],
  have rc_h_range_check_ptr₃ := range_checked_offset' rc_h_range_check_ptr₂,
  have rc_h_range_check_ptr₃' := range_checked_add_right rc_h_range_check_ptr₃, try { norm_cast at rc_h_range_check_ptr₃' },
  have spec31 := h_call31 rc_h_range_check_ptr₂',
    try { rw [←hin_range_check_ptr] at spec31 }, try { rw [←hl_range_check_ptr₁] at spec31 }, try { rw [←hl_range_check_ptr₂] at spec31 }, try { rw [←htv_range_check_ptr₃] at spec31 },
  try { dsimp at spec31, arith_simps at spec31 },
  use_only [spec31],
  use_only [κ_call49],
  use_only [range_check_ptr₄],
  have rc_h_range_check_ptr₄ := range_checked_offset' rc_h_range_check_ptr₃,
  have rc_h_range_check_ptr₄' := range_checked_add_right rc_h_range_check_ptr₄, try { norm_cast at rc_h_range_check_ptr₄' },
  have spec49 := h_call49 rc_h_range_check_ptr₃',
    try { rw [←hin_range_check_ptr] at spec49 }, try { rw [←hl_range_check_ptr₁] at spec49 }, try { rw [←hl_range_check_ptr₂] at spec49 }, try { rw [←hl_range_check_ptr₃] at spec49 }, try { rw [←htv_range_check_ptr₄] at spec49 },
  try { dsimp at spec49, arith_simps at spec49 },
  use_only [spec49],
  use_only [κ_call57],
  use_only [x_diff_slope],
  try { dsimp at h_call57, arith_simps at h_call57 },
  try { use_only [h_call57] },
  use_only [κ_call66],
  use_only [range_check_ptr₅],
  have rc_h_range_check_ptr₅ := range_checked_offset' rc_h_range_check_ptr₄,
  have rc_h_range_check_ptr₅' := range_checked_add_right rc_h_range_check_ptr₅, try { norm_cast at rc_h_range_check_ptr₅' },
  have spec66 := h_call66 rc_h_range_check_ptr₄',
    try { rw [←hin_range_check_ptr] at spec66 }, try { rw [←hl_range_check_ptr₁] at spec66 }, try { rw [←hl_range_check_ptr₂] at spec66 }, try { rw [←hl_range_check_ptr₃] at spec66 }, try { rw [←hl_range_check_ptr₄] at spec66 }, try { rw [←htv_range_check_ptr₅] at spec66 },
  try { dsimp at spec66, arith_simps at spec66 },
  use_only [spec66],
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_slope, htv_slope_sqr, htv_range_check_ptr₂, htv_new_x, htv_range_check_ptr₃, htv_new_y, htv_range_check_ptr₄, htv_x_diff_slope, htv_range_check_ptr₅] }, },
  try { dsimp [cast_EcPoint, cast_BigInt3, cast_UnreducedBigInt3] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5] },
  try { simp only [h_call23_ap_offset, h_call25_ap_offset, h_call28_ap_offset, h_call31_ap_offset, h_call49_ap_offset, h_call57_ap_offset, h_call66_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

theorem auto_sound_ec_double
    -- arguments
    (range_check_ptr : F) (point : EcPoint mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_ec_double σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 289))
    (h_mem_5 : mem_at mem code_unreduced_mul (σ.pc  - 276))
    (h_mem_6 : mem_at mem code_unreduced_sqr (σ.pc  - 238))
    (h_mem_7 : mem_at mem code_assert_165_bit (σ.pc  - 204))
    (h_mem_8 : mem_at mem code_verify_zero (σ.pc  - 193))
    (h_mem_12 : mem_at mem code_compute_doubling_slope (σ.pc  - 70))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 9))
    (hin_point : point = cast_EcPoint mem (σ.fp - 8))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 9)) (mem $ τ.ap - 7)
        (spec_ec_double mem κ range_check_ptr point (mem (τ.ap - 7)) (cast_EcPoint  mem (τ.ap - 6)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_ec_double at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37, hpc38, hpc39, hpc40, hpc41, hpc42, hpc43, hpc44, hpc45, hpc46, hpc47, hpc48, hpc49, hpc50, hpc51, hpc52, hpc53, hpc54, hpc55, hpc56, hpc57, hpc58, hpc59, hpc60, hpc61, hpc62, hpc63, hpc64, hpc65, hpc66, hpc67, hpc68, hpc69, hpc70, hpc71, hpc72⟩,
  -- if statement
  step_jnz hpc0 hpc1 with hcond hcond,
  {
    -- if: positive branch
    have a0 : point.x.d0 = 0, {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- if statement
    step_jnz hpc2 hpc3 with hcond hcond,
    {
      -- if: positive branch
      have a2 : point.x.d1 = 0, {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [hcond] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      try { dsimp at a2 }, try { arith_simps at a2 },
      clear hcond,
      -- if statement
      step_jnz hpc4 hpc5 with hcond hcond,
      {
        -- if: positive branch
        have a4 : point.x.d2 = 0, {
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [hcond] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
        },
        try { dsimp at a4 }, try { arith_simps at a4 },
        clear hcond,
        -- return
        step_assert_eq hpc6 with hret0,
        step_assert_eq hpc7 with hret1,
        step_assert_eq hpc8 with hret2,
        step_assert_eq hpc9 with hret3,
        step_assert_eq hpc10 with hret4,
        step_assert_eq hpc11 with hret5,
        step_assert_eq hpc12 with hret6,
        step_ret hpc13,
        -- finish
        step_done, use_only [rfl, rfl],
        -- range check condition
        use_only (0+0), split,
        linarith [],
        split,
        { try { norm_num1 }, arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5 ,hret6] },
          try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
        intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
        have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
        -- Final Proof
        -- user-provided reduction
        suffices auto_spec: auto_spec_ec_double mem _ range_check_ptr point _ _,
        { apply sound_ec_double, apply auto_spec },
        -- prove the auto generated assertion
        dsimp [auto_spec_ec_double],
        try { norm_num1 }, try { arith_simps },
        left,
        use_only [a0],
        left,
        use_only [a2],
        left,
        use_only [a4],
        try { split, trivial <|> linarith },
        try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] }, },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      {
        -- if: negative branch
        have a4 : point.x.d2 ≠ 0, {
          try { simp only [ne.def] },
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [hcond] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
        },
        try { dsimp at a4 }, try { arith_simps at a4 },
        clear hcond,
        -- Use the block soundness theorem.
        apply ensuresb_ret_trans (auto_sound_ec_double_block5 mem σ _ range_check_ptr point h_mem_rec h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_8 h_mem_12 hin_range_check_ptr hin_point νbound),
        intros κ_block5 τ, try { arith_simps },
        intro h_block5,
        rcases h_block5 with ⟨rc_m_block5, rc_m_le_block5, hblk_range_check_ptr₁, h_block5⟩,
        -- range check condition
        use_only (rc_m_block5+0+0), split,
        linarith [rc_m_le_block5],
        split,
        { try { norm_num1 }, arith_simps, try { simp only [hblk_range_check_ptr₁] },
          try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
        intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
        have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
        -- Final Proof
        -- user-provided reduction
        suffices auto_spec: auto_spec_ec_double mem _ range_check_ptr point _ _,
        { apply sound_ec_double, apply auto_spec },
        -- prove the auto generated assertion
        dsimp [auto_spec_ec_double],
        try { norm_num1 }, try { arith_simps },
        left,
        use_only [a0],
        left,
        use_only [a2],
        right,
        use_only [a4],
        have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
        have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
        have h_block5' := h_block5 rc_h_range_check_ptr',
        try { rw [←hin_range_check_ptr] at h_block5' },
        try { dsimp at h_block5, arith_simps at h_block5' },
        have h_block5 := h_block5',
        use_only [κ_block5],
        use [h_block5],
        try { linarith }
      }
    },
    {
      -- if: negative branch
      have a2 : point.x.d1 ≠ 0, {
        try { simp only [ne.def] },
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [hcond] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      try { dsimp at a2 }, try { arith_simps at a2 },
      clear hcond,
      -- Use the block soundness theorem.
      apply ensuresb_ret_trans (auto_sound_ec_double_block5 mem σ _ range_check_ptr point h_mem_rec h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_8 h_mem_12 hin_range_check_ptr hin_point νbound),
      intros κ_block5 τ, try { arith_simps },
      intro h_block5,
      rcases h_block5 with ⟨rc_m_block5, rc_m_le_block5, hblk_range_check_ptr₁, h_block5⟩,
      -- range check condition
      use_only (rc_m_block5+0+0), split,
      linarith [rc_m_le_block5],
      split,
      { try { norm_num1 }, arith_simps, try { simp only [hblk_range_check_ptr₁] },
        try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
      intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
      have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
      -- Final Proof
      -- user-provided reduction
      suffices auto_spec: auto_spec_ec_double mem _ range_check_ptr point _ _,
      { apply sound_ec_double, apply auto_spec },
      -- prove the auto generated assertion
      dsimp [auto_spec_ec_double],
      try { norm_num1 }, try { arith_simps },
      left,
      use_only [a0],
      right,
      use_only [a2],
      have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
      have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
      have h_block5' := h_block5 rc_h_range_check_ptr',
      try { rw [←hin_range_check_ptr] at h_block5' },
      try { dsimp at h_block5, arith_simps at h_block5' },
      have h_block5 := h_block5',
      use_only [κ_block5],
      use [h_block5],
      try { linarith }
    }
  },
  {
    -- if: negative branch
    have a0 : point.x.d0 ≠ 0, {
      try { simp only [ne.def] },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- Use the block soundness theorem.
    apply ensuresb_ret_trans (auto_sound_ec_double_block5 mem σ _ range_check_ptr point h_mem_rec h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_8 h_mem_12 hin_range_check_ptr hin_point νbound),
    intros κ_block5 τ, try { arith_simps },
    intro h_block5,
    rcases h_block5 with ⟨rc_m_block5, rc_m_le_block5, hblk_range_check_ptr₁, h_block5⟩,
    -- range check condition
    use_only (rc_m_block5+0+0), split,
    linarith [rc_m_le_block5],
    split,
    { try { norm_num1 }, arith_simps, try { simp only [hblk_range_check_ptr₁] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_ec_double mem _ range_check_ptr point _ _,
    { apply sound_ec_double, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_ec_double],
    try { norm_num1 }, try { arith_simps },
    right,
    use_only [a0],
    have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
    have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
    have h_block5' := h_block5 rc_h_range_check_ptr',
    try { rw [←hin_range_check_ptr] at h_block5' },
    try { dsimp at h_block5, arith_simps at h_block5' },
    have h_block5 := h_block5',
    use_only [κ_block5],
    use [h_block5],
    try { linarith }
  }
end

