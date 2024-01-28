/-
File: signature_recover_public_key_assert_le_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_assert_nn_soundness
open tactic

open starkware.cairo.common.math

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.math.assert_le autogenerated soundness theorem -/

theorem auto_sound_assert_le
    -- arguments
    (range_check_ptr a b : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_assert_le σ.pc)
    -- all dependencies are in memory
    (h_mem_0 : mem_at mem code_assert_nn (σ.pc  - 4))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 5))
    (hin_a : a = mem (σ.fp - 4))
    (hin_b : b = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 5 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 5)) (mem $ τ.ap - 1)
        (spec_assert_le mem κ range_check_ptr a b (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_assert_le at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4⟩,
  -- function call
  step_assert_eq hpc0 with arg0,
  step_assert_eq hpc1 with arg1,
  step_sub hpc2 (auto_sound_assert_nn mem _ range_check_ptr (b - a) _ _ _),
  { rw hpc3, norm_num2, exact h_mem_0 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b] },
    try { arith_simps }, try { simp only [arg0, (eq_sub_of_eq_add arg1)] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b] },
    try { arith_simps }, try { simp only [arg0, (eq_sub_of_eq_add arg1)] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call4 ap4 h_call4,
  rcases h_call4 with ⟨h_call4_ap_offset, h_call4⟩,
  rcases h_call4 with ⟨rc_m4, rc_mle4, hl_range_check_ptr₁, h_call4⟩,
  mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap4 - 1)),
  simp only [←htv_range_check_ptr₁] at h_call4,
  try { simp only [arg0 ,arg1] at hl_range_check_ptr₁ },
  try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
  try { simp only [arg0 ,arg1] at h_call4 },
  rw [hin_range_check_ptr] at h_call4,
  clear arg0 arg1,
  -- return
  step_ret hpc4,
  -- finish
  step_done, use_only [rfl, rfl],
  split,
  { try { simp only [h_call4_ap_offset] },
    try { arith_simps }, try { refl } },
  -- range check condition
  use_only (rc_m4+0+0), split,
  linarith [rc_mle4],
  split,
  { try { norm_num1 }, arith_simps,
    try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_assert_le mem _ range_check_ptr a b _,
  { apply sound_assert_le, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_assert_le],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call4],
  use_only [range_check_ptr₁],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec4 := h_call4 rc_h_range_check_ptr',
    try { rw [←hin_range_check_ptr] at spec4 }, try { rw [←htv_range_check_ptr₁] at spec4 },
  try { dsimp at spec4, arith_simps at spec4 },
  use_only [spec4],
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁] }, },
  try { simp only [h_call4_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

