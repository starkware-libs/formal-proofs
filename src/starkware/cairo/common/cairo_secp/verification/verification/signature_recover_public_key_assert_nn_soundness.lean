/-
File: signature_recover_public_key_assert_nn_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
open tactic

open starkware.cairo.common.math

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.math.assert_nn autogenerated soundness theorem -/

theorem auto_sound_assert_nn
    -- arguments
    (range_check_ptr a : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_assert_nn σ.pc)
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 4))
    (hin_a : a = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 1 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 4)) (mem $ τ.ap - 1)
        (spec_assert_nn mem κ range_check_ptr a (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_assert_nn at h_mem with ⟨hpc0, hpc1, hpc2, hpc3⟩,
  -- assert eq
  step_assert_eq hpc0 with temp0,
  have a0: a = mem range_check_ptr, {
    apply assert_eq_reduction temp0,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a0 }, try { arith_simps at a0 },
  clear temp0,
  -- let
  mkdef hl_range_check_ptr₁ : range_check_ptr₁ = (range_check_ptr + 1 : F),
  try { dsimp at hl_range_check_ptr₁ }, try { arith_simps at hl_range_check_ptr₁ },
  -- return
  step_assert_eq hpc1 hpc2 with hret0,
  step_ret hpc3,
  -- finish
  step_done, use_only [rfl, rfl],
  split, refl,
  -- range check condition
  use_only (1+0+0), split,
  linarith [],
  split,
  { try { norm_num1 }, arith_simps, try { simp only [hret0] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_assert_nn mem _ range_check_ptr a _,
  { apply sound_assert_nn, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_assert_nn],
  try { norm_num1 }, try { arith_simps },
  use_only [a0],
  cases rc_h_range_check_ptr' (0) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a0, hin_range_check_ptr], arith_simps, exact hn },
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁,
    try { norm_cast at rc_h_range_check_ptr₁' }, try { rw [add_zero] at rc_h_range_check_ptr₁' },
  use_only [range_check_ptr₁, hl_range_check_ptr₁],
  try { dsimp }, try { arith_simps },
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hl_range_check_ptr₁] }, },
  try { arith_simps }, try { simp only [hret0] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

