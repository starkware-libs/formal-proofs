/-
File: signature_recover_public_key_unreduced_sqr_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
open tactic

open starkware.cairo.common.cairo_secp.field
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.cairo_secp.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.cairo_secp.field.unreduced_sqr autogenerated soundness theorem -/

theorem auto_sound_unreduced_sqr
    -- arguments
    (a : BigInt3 mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_unreduced_sqr σ.pc)
    -- input arguments on the stack
    (hin_a : a = cast_BigInt3 mem (σ.fp - 5))
    -- conclusion
  : ensures_ret mem σ (λ κ τ, τ.ap = σ.ap + 12 ∧ spec_unreduced_sqr mem κ a (cast_UnreducedBigInt3  mem (τ.ap - 3))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_unreduced_sqr at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15⟩,
  -- tempvar
  step_assert_eq hpc0 hpc1 with tv_twice_d00,
  mkdef hl_twice_d0 : twice_d0 = (a.d0 * 2 : F),
  have htv_twice_d0: twice_d0 = _, {
    apply eq.symm, apply eq.trans tv_twice_d00,
      try { simp only [add_neg_eq_sub, hin_a, hl_twice_d0] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_twice_d00,
  try { dsimp at hl_twice_d0 }, try { arith_simps at hl_twice_d0 },
  -- return
  step_assert_eq hpc2 with hret0,
  step_assert_eq hpc3 hpc4 with hret1,
  step_assert_eq hpc5 with hret2,
  step_assert_eq hpc6 with hret3,
  step_assert_eq hpc7 hpc8 with hret4,
  step_assert_eq hpc9 with hret5,
  step_assert_eq hpc10 with hret6,
  step_assert_eq hpc11 with hret7,
  step_assert_eq hpc12 with hret8,
  step_assert_eq hpc13 with hret9,
  step_assert_eq hpc14 with hret10,
  step_ret hpc15,
  -- finish
  step_done, use_only [rfl, rfl],
  split, refl,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_unreduced_sqr mem _ a _,
  { apply sound_unreduced_sqr, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_unreduced_sqr],
  try { norm_num1 }, try { arith_simps },
  use_only [twice_d0, hl_twice_d0],
  try { dsimp }, try { arith_simps },
  try { split, trivial <|> linarith },
  try { ensures_simps; try { unfold SECP_REM }, },
  try { simp only [add_neg_eq_sub, hin_a, hl_twice_d0, htv_twice_d0] },
  try { dsimp [cast_BigInt3, cast_UnreducedBigInt3] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6, hret7, hret8, hret9, hret10] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

