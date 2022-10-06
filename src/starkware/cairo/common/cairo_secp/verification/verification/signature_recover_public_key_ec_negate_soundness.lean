/-
File: signature_recover_public_key_ec_negate_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_verify_zero_soundness
import .signature_recover_public_key_nondet_bigint3_soundness
open tactic

open starkware.cairo.common.cairo_secp.ec
open starkware.cairo.common.cairo_secp.bigint
open starkware.cairo.common.cairo_secp.field

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.cairo_secp.ec.ec_negate autogenerated soundness theorem -/

theorem auto_sound_ec_negate
    -- arguments
    (range_check_ptr : F) (point : EcPoint F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_ec_negate σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 160))
    (h_mem_7 : mem_at mem code_verify_zero (σ.pc  - 112))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 9))
    (hin_point : point = cast_EcPoint mem (σ.fp - 8))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 34 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 9)) (mem $ τ.ap - 7)
        (spec_ec_negate mem κ range_check_ptr point (mem (τ.ap - 7)) (cast_EcPoint mem (τ.ap - 6)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_ec_negate at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15⟩,
  -- function call
  step_assert_eq hpc0 with arg0,
  step_sub hpc1 (auto_sound_nondet_bigint3 mem _ range_check_ptr _ _),
  { rw hpc2, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point] },
    try { dsimp [cast_EcPoint, cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call3 ap3 h_call3,
  rcases h_call3 with ⟨h_call3_ap_offset, h_call3⟩,
  rcases h_call3 with ⟨rc_m3, rc_mle3, hl_range_check_ptr₁, h_call3⟩,
  generalize' hr_rev_range_check_ptr₁: mem (ap3 - 4) = range_check_ptr₁,
  have htv_range_check_ptr₁ := hr_rev_range_check_ptr₁.symm, clear hr_rev_range_check_ptr₁,
  generalize' hr_rev_minus_y: cast_BigInt3 mem (ap3 - 3) = minus_y,
  simp only [hr_rev_minus_y] at h_call3,
  have htv_minus_y := hr_rev_minus_y.symm, clear hr_rev_minus_y,
  try { simp only [arg0] at hl_range_check_ptr₁ },
  rw [←htv_range_check_ptr₁, ←hin_range_check_ptr] at hl_range_check_ptr₁,
  try { simp only [arg0] at h_call3 },
  rw [hin_range_check_ptr] at h_call3,
  clear arg0,
  -- function call
  step_assert_eq hpc3 with arg0,
  step_assert_eq hpc4 with arg1,
  step_assert_eq hpc5 with arg2,
  step_assert_eq hpc6 with arg3,
  step_sub hpc7 (auto_sound_verify_zero mem _ range_check_ptr₁ {
    d0 := minus_y.d0 + point.y.d0,
    d1 := minus_y.d1 + point.y.d1,
    d2 := minus_y.d2 + point.y.d2
  } _ _ _),
  { rw hpc8, norm_num2, exact h_mem_7 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_minus_y] },
    try { dsimp [cast_EcPoint, cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
    try { simp only [h_call3_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_minus_y] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3] },
      try { simp only [h_call3_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call9 ap9 h_call9,
  rcases h_call9 with ⟨h_call9_ap_offset, h_call9⟩,
  rcases h_call9 with ⟨rc_m9, rc_mle9, hl_range_check_ptr₂, h_call9⟩,
  generalize' hr_rev_range_check_ptr₂: mem (ap9 - 1) = range_check_ptr₂,
  have htv_range_check_ptr₂ := hr_rev_range_check_ptr₂.symm, clear hr_rev_range_check_ptr₂,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3] at hl_range_check_ptr₂ },
  rw [←htv_range_check_ptr₂, ←htv_range_check_ptr₁] at hl_range_check_ptr₂,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3] at h_call9 },
  rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call9,
  clear arg0 arg1 arg2 arg3,
  -- return
  step_assert_eq hpc9 with hret0,
  step_assert_eq hpc10 with hret1,
  step_assert_eq hpc11 with hret2,
  step_assert_eq hpc12 with hret3,
  step_assert_eq hpc13 with hret4,
  step_assert_eq hpc14 with hret5,
  step_ret hpc15,
  -- finish
  step_done, use_only [rfl, rfl],
  split,
  { try { simp only [h_call3_ap_offset ,h_call9_ap_offset] },
    try { arith_simps }, try { refl } },
  -- range check condition
  use_only (rc_m3+rc_m9+0+0), split,
  linarith [rc_mle3, rc_mle9],
  split,
  { arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5] },
    rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr],
    try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_ec_negate mem _ range_check_ptr point _ _,
  { apply sound_ec_negate, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_ec_negate],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call3],
  use_only [range_check_ptr₁],
  use_only [minus_y],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec3 := h_call3 rc_h_range_check_ptr',
  rw [←hin_range_check_ptr, ←htv_range_check_ptr₁] at spec3,
  try { dsimp at spec3, arith_simps at spec3 },
  use_only [spec3],
  use_only [κ_call9],
  use_only [range_check_ptr₂],
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
  have spec9 := h_call9 rc_h_range_check_ptr₁',
  rw [←hin_range_check_ptr, ←hl_range_check_ptr₁, ←htv_range_check_ptr₂] at spec9,
  try { dsimp at spec9, arith_simps at spec9 },
  use_only [spec9],
  try { split, linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, htv_range_check_ptr₁, htv_minus_y, htv_range_check_ptr₂] }, },
  try { dsimp [cast_EcPoint, cast_BigInt3] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5] },
  try { simp only [h_call3_ap_offset, h_call9_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

