/-
File: ec_unreduced_mul_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
open tactic

open starkware.cairo.common.secp256r1.field
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.secp256r1.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.field.unreduced_mul autogenerated soundness theorem -/

theorem auto_sound_unreduced_mul
    -- arguments
    (a b : BigInt3 mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_unreduced_mul σ.pc)
    -- input arguments on the stack
    (hin_a : a = cast_BigInt3 mem (σ.fp - 8))
    (hin_b : b = cast_BigInt3 mem (σ.fp - 5))
    -- conclusion
  : ensures_ret mem σ (λ κ τ, τ.ap = σ.ap + 31 ∧ spec_unreduced_mul mem κ a b (cast_UnreducedBigInt3  mem (τ.ap - 3))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_unreduced_mul at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37⟩,
  -- tempvar
  step_assert_eq hpc0 with tv_limb00,
  mkdef hl_limb0 : limb0 = (a.d0 * b.d0 : F),
  have htv_limb0: limb0 = _, {
    apply eq.symm, apply eq.trans tv_limb00,
      try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_limb00,
  try { dsimp at hl_limb0 }, try { arith_simps at hl_limb0 },
  -- tempvar
  step_assert_eq hpc1 with tv_limb10,
  step_assert_eq hpc2 with tv_limb11,
  step_assert_eq hpc3 with tv_limb12,
  mkdef hl_limb1 : limb1 = (a.d0 * b.d1 + a.d1 * b.d0 : F),
  have htv_limb1: limb1 = _, {
    apply eq.symm, apply eq.trans tv_limb12,
      try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0, htv_limb0, hl_limb1] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps }, try { simp only [tv_limb10, tv_limb11] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_limb10 tv_limb11 tv_limb12,
  try { dsimp at hl_limb1 }, try { arith_simps at hl_limb1 },
  -- tempvar
  step_assert_eq hpc4 with tv_limb20,
  step_assert_eq hpc5 with tv_limb21,
  step_assert_eq hpc6 with tv_limb22,
  step_assert_eq hpc7 with tv_limb23,
  step_assert_eq hpc8 with tv_limb24,
  mkdef hl_limb2 : limb2 = (a.d0 * b.d2 + a.d1 * b.d1 + a.d2 * b.d0 : F),
  have htv_limb2: limb2 = _, {
    apply eq.symm, apply eq.trans tv_limb24,
      try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0, htv_limb0, hl_limb1, htv_limb1, hl_limb2] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps }, try { simp only [tv_limb20, tv_limb21, tv_limb22, tv_limb23] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_limb20 tv_limb21 tv_limb22 tv_limb23 tv_limb24,
  try { dsimp at hl_limb2 }, try { arith_simps at hl_limb2 },
  -- tempvar
  step_assert_eq hpc9 with tv_limb30,
  step_assert_eq hpc10 with tv_limb31,
  step_assert_eq hpc11 with tv_limb32,
  mkdef hl_limb3 : limb3 = (a.d1 * b.d2 + a.d2 * b.d1 : F),
  have htv_limb3: limb3 = _, {
    apply eq.symm, apply eq.trans tv_limb32,
      try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0, htv_limb0, hl_limb1, htv_limb1, hl_limb2, htv_limb2, hl_limb3] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps }, try { simp only [tv_limb30, tv_limb31] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_limb30 tv_limb31 tv_limb32,
  try { dsimp at hl_limb3 }, try { arith_simps at hl_limb3 },
  -- tempvar
  step_assert_eq hpc12 with tv_limb40,
  mkdef hl_limb4 : limb4 = (a.d2 * b.d2 : F),
  have htv_limb4: limb4 = _, {
    apply eq.symm, apply eq.trans tv_limb40,
      try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0, htv_limb0, hl_limb1, htv_limb1, hl_limb2, htv_limb2, hl_limb3, htv_limb3, hl_limb4] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_limb40,
  try { dsimp at hl_limb4 }, try { arith_simps at hl_limb4 },
  -- return
  step_assert_eq hpc13 hpc14 with hret0,
  step_assert_eq hpc15 with hret1,
  step_assert_eq hpc16 with hret2,
  step_assert_eq hpc17 hpc18 with hret3,
  step_assert_eq hpc19 with hret4,
  step_assert_eq hpc20 hpc21 with hret5,
  step_assert_eq hpc22 with hret6,
  step_assert_eq hpc23 with hret7,
  step_assert_eq hpc24 hpc25 with hret8,
  step_assert_eq hpc26 with hret9,
  step_assert_eq hpc27 hpc28 with hret10,
  step_assert_eq hpc29 with hret11,
  step_assert_eq hpc30 with hret12,
  step_assert_eq hpc31 hpc32 with hret13,
  step_assert_eq hpc33 with hret14,
  step_assert_eq hpc34 with hret15,
  step_assert_eq hpc35 with hret16,
  step_assert_eq hpc36 with hret17,
  step_ret hpc37,
  -- finish
  step_done, use_only [rfl, rfl],
  split, refl,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_unreduced_mul mem _ a b _,
  { apply sound_unreduced_mul, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_unreduced_mul],
  try { norm_num1 }, try { arith_simps },
  use_only [limb0, hl_limb0],
  try { dsimp }, try { arith_simps },
  use_only [limb1, hl_limb1],
  try { dsimp }, try { arith_simps },
  use_only [limb2, hl_limb2],
  try { dsimp }, try { arith_simps },
  use_only [limb3, hl_limb3],
  try { dsimp }, try { arith_simps },
  use_only [limb4, hl_limb4],
  try { dsimp }, try { arith_simps },
  try { split, trivial <|> linarith },
  try { ensures_simps; try { unfold BASE3_MOD_P0 BASE4_MOD_P0 BASE3_MOD_P1 BASE4_MOD_P1 BASE3_MOD_P2 BASE4_MOD_P2 }, },
  try { simp only [add_neg_eq_sub, hin_a, hin_b, hl_limb0, htv_limb0, hl_limb1, htv_limb1, hl_limb2, htv_limb2, hl_limb3, htv_limb3, hl_limb4, htv_limb4] },
  try { dsimp [cast_BigInt3, cast_UnreducedBigInt3] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6, hret7, hret8, hret9, hret10, hret11, hret12, hret13, hret14, hret15, hret16, hret17] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

