/-
File: signature_recover_public_key_assert_nn_le_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_assert_le_soundness
open tactic

open starkware.cairo.common.math

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.math.assert_nn_le autogenerated soundness theorem -/

theorem auto_sound_assert_nn_le
    -- arguments
    (range_check_ptr a b : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_assert_nn_le σ.pc)
    -- all dependencies are in memory
    (h_mem_0 : mem_at mem code_assert_nn (σ.pc  - 9))
    (h_mem_1 : mem_at mem code_assert_le (σ.pc  - 5))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 5))
    (hin_a : a = mem (σ.fp - 4))
    (hin_b : b = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 14 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 5)) (mem $ τ.ap - 1)
        (spec_assert_nn_le mem κ range_check_ptr a b (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_assert_nn_le at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8⟩,
  -- function call
  step_assert_eq hpc0 with arg0,
  step_assert_eq hpc1 with arg1,
  step_sub hpc2 (auto_sound_assert_nn mem _ range_check_ptr a _ _ _),
  { rw hpc3, norm_num2, exact h_mem_0 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b] },
    try { arith_simps }, try { simp only [arg0, arg1] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b] },
    try { arith_simps }, try { simp only [arg0, arg1] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call4 ap4 h_call4,
  rcases h_call4 with ⟨h_call4_ap_offset, h_call4⟩,
  rcases h_call4 with ⟨rc_m4, rc_mle4, hl_range_check_ptr₁, h_call4⟩,
  generalize' hr_rev_range_check_ptr₁: mem (ap4 - 1) = range_check_ptr₁,
  have htv_range_check_ptr₁ := hr_rev_range_check_ptr₁.symm, clear hr_rev_range_check_ptr₁,
  try { simp only [arg0 ,arg1] at hl_range_check_ptr₁ },
  rw [←htv_range_check_ptr₁, ←hin_range_check_ptr] at hl_range_check_ptr₁,
  try { simp only [arg0 ,arg1] at h_call4 },
  rw [hin_range_check_ptr] at h_call4,
  clear arg0 arg1,
  -- function call
  step_assert_eq hpc4 with arg0,
  step_assert_eq hpc5 with arg1,
  step_sub hpc6 (auto_sound_assert_le mem _ range_check_ptr₁ a b _ _ _ _ _),
  { rw hpc7, norm_num2, exact h_mem_1 },
  { rw hpc7, norm_num2, exact h_mem_0 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁] },
    try { arith_simps }, try { simp only [arg0, arg1] },
    try { simp only [h_call4_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁] },
    try { arith_simps }, try { simp only [arg0, arg1] },
    try { simp only [h_call4_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁] },
    try { arith_simps }, try { simp only [arg0, arg1] },
    try { simp only [h_call4_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call8 ap8 h_call8,
  rcases h_call8 with ⟨h_call8_ap_offset, h_call8⟩,
  rcases h_call8 with ⟨rc_m8, rc_mle8, hl_range_check_ptr₂, h_call8⟩,
  generalize' hr_rev_range_check_ptr₂: mem (ap8 - 1) = range_check_ptr₂,
  have htv_range_check_ptr₂ := hr_rev_range_check_ptr₂.symm, clear hr_rev_range_check_ptr₂,
  try { simp only [arg0 ,arg1] at hl_range_check_ptr₂ },
  rw [←htv_range_check_ptr₂, ←htv_range_check_ptr₁] at hl_range_check_ptr₂,
  try { simp only [arg0 ,arg1] at h_call8 },
  rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call8,
  clear arg0 arg1,
  -- return
  step_ret hpc8,
  -- finish
  step_done, use_only [rfl, rfl],
  split,
  { try { simp only [h_call4_ap_offset ,h_call8_ap_offset] },
    try { arith_simps }, try { refl } },
  -- range check condition
  use_only (rc_m4+rc_m8+0+0), split,
  linarith [rc_mle4, rc_mle8],
  split,
  { arith_simps,
    rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr],
    try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_assert_nn_le mem _ range_check_ptr a b _,
  { apply sound_assert_nn_le, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_assert_nn_le],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call4],
  use_only [range_check_ptr₁],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec4 := h_call4 rc_h_range_check_ptr',
  rw [←hin_range_check_ptr, ←htv_range_check_ptr₁] at spec4,
  try { dsimp at spec4, arith_simps at spec4 },
  use_only [spec4],
  use_only [κ_call8],
  use_only [range_check_ptr₂],
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
  have spec8 := h_call8 rc_h_range_check_ptr₁',
  rw [←hin_range_check_ptr, ←hl_range_check_ptr₁, ←htv_range_check_ptr₂] at spec8,
  try { dsimp at spec8, arith_simps at spec8 },
  use_only [spec8],
  try { split, linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_range_check_ptr₂] }, },
  try { simp only [h_call4_ap_offset, h_call8_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

