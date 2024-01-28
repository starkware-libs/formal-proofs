/-
File: signature_recover_public_key_reduce_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_nondet_bigint3_soundness
import .signature_recover_public_key_verify_zero_soundness
open tactic

open starkware.cairo.common.cairo_secp.field
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.cairo_secp.bigint

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.cairo_secp.field.reduce autogenerated soundness theorem -/

theorem auto_sound_reduce
    -- arguments
    (range_check_ptr : F) (x : UnreducedBigInt3 mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_reduce σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 107))
    (h_mem_7 : mem_at mem code_verify_zero (σ.pc  - 59))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 6))
    (hin_x : x = cast_UnreducedBigInt3 mem (σ.fp - 5))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 31 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 6)) (mem $ τ.ap - 4)
        (spec_reduce mem κ range_check_ptr x (mem (τ.ap - 4)) (cast_BigInt3  mem (τ.ap - 3)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_reduce at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12⟩,
  -- function call
  step_assert_eq hpc0 with arg0,
  step_sub hpc1 (auto_sound_nondet_bigint3 mem _ range_check_ptr _ _),
  { rw hpc2, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x] },
    try { dsimp [cast_UnreducedBigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call3 ap3 h_call3,
  rcases h_call3 with ⟨h_call3_ap_offset, h_call3⟩,
  rcases h_call3 with ⟨rc_m3, rc_mle3, hl_range_check_ptr₁, h_call3⟩,
  mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap3 - 4)),
  simp only [←htv_range_check_ptr₁] at h_call3,
  mkdef htv_reduced_x : reduced_x = (cast_BigInt3 mem (ap3 - 3)),
  simp only [←htv_reduced_x] at h_call3,
  try { simp only [arg0] at hl_range_check_ptr₁ },
  try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
  try { simp only [arg0] at h_call3 },
  rw [hin_range_check_ptr] at h_call3,
  clear arg0,
  -- function call
  step_assert_eq hpc3 with arg0,
  step_assert_eq hpc4 with arg1,
  step_assert_eq hpc5 with arg2,
  step_assert_eq hpc6 with arg3,
  step_sub hpc7 (auto_sound_verify_zero mem _ range_check_ptr₁ {
    d0 := x.d0 - reduced_x.d0,
    d1 := x.d1 - reduced_x.d1,
    d2 := x.d2 - reduced_x.d2
  } _ _ _),
  { rw hpc8, norm_num2, exact h_mem_7 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, htv_range_check_ptr₁, htv_reduced_x] },
    try { dsimp [cast_UnreducedBigInt3, cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0, (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), (eq_sub_of_eq_add arg3)] },
    try { simp only [h_call3_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, htv_range_check_ptr₁, htv_reduced_x] },
      try { dsimp [cast_UnreducedBigInt3, cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, (eq_sub_of_eq_add arg1), (eq_sub_of_eq_add arg2), (eq_sub_of_eq_add arg3)] },
      try { simp only [h_call3_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call9 ap9 h_call9,
  rcases h_call9 with ⟨h_call9_ap_offset, h_call9⟩,
  rcases h_call9 with ⟨rc_m9, rc_mle9, hl_range_check_ptr₂, h_call9⟩,
  mkdef htv_range_check_ptr₂ : range_check_ptr₂ = (mem (ap9 - 1)),
  simp only [←htv_range_check_ptr₂] at h_call9,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3] at hl_range_check_ptr₂ },
  try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₂ }, try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₂ },
  try { simp only [arg0 ,arg1 ,arg2 ,arg3] at h_call9 },
  rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call9,
  clear arg0 arg1 arg2 arg3,
  -- return
  step_assert_eq hpc9 with hret0,
  step_assert_eq hpc10 with hret1,
  step_assert_eq hpc11 with hret2,
  step_ret hpc12,
  -- finish
  step_done, use_only [rfl, rfl],
  split,
  { try { simp only [h_call3_ap_offset ,h_call9_ap_offset] },
    try { arith_simps }, try { refl } },
  -- range check condition
  use_only (rc_m3+rc_m9+0+0), split,
  linarith [rc_mle3, rc_mle9],
  split,
  { try { norm_num1 }, arith_simps, try { simp only [hret0 ,hret1 ,hret2] },
    try { rw [←htv_range_check_ptr₂] }, try { rw [hl_range_check_ptr₂] }, try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_reduce mem _ range_check_ptr x _ _,
  { apply sound_reduce, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_reduce],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call3],
  use_only [range_check_ptr₁],
  use_only [reduced_x],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec3 := h_call3 rc_h_range_check_ptr',
    try { rw [←hin_range_check_ptr] at spec3 }, try { rw [←htv_range_check_ptr₁] at spec3 },
  try { dsimp at spec3, arith_simps at spec3 },
  use_only [spec3],
  use_only [κ_call9],
  use_only [range_check_ptr₂],
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
  have spec9 := h_call9 rc_h_range_check_ptr₁',
    try { rw [←hin_range_check_ptr] at spec9 }, try { rw [←hl_range_check_ptr₁] at spec9 }, try { rw [←htv_range_check_ptr₂] at spec9 },
  try { dsimp at spec9, arith_simps at spec9 },
  use_only [spec9],
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_x, htv_range_check_ptr₁, htv_reduced_x, htv_range_check_ptr₂] }, },
  try { dsimp [cast_UnreducedBigInt3, cast_BigInt3] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2] },
  try { simp only [h_call3_ap_offset, h_call9_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

