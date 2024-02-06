/-
File: ec_nondet_bigint3_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
open tactic

open starkware.cairo.common.secp256r1.bigint
open starkware.cairo.common.cairo_secp.bigint3
open starkware.cairo.common.secp256r1.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.bigint.nondet_bigint3 autogenerated soundness theorem -/

theorem auto_sound_nondet_bigint3
    -- arguments
    (range_check_ptr : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_nondet_bigint3 σ.pc)
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 7 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 3)) (mem $ τ.ap - 4)
        (spec_nondet_bigint3 mem κ range_check_ptr (mem (τ.ap - 4)) (cast_BigInt3  mem (τ.ap - 3)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_nondet_bigint3 at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12⟩,
  -- let (ap reference)
  apply of_register_state,
  intros regstate_res regstateeq_res,
  mkdef  hl_res : res = cast_BigInt3 mem (regstate_res.ap + 4),
  rw [regstateeq_res] at hl_res, try { dsimp at hl_res },
  -- compound assert eq
  step_assert_eq hpc0 hpc1 with temp0,
  step_assert_eq hpc2 with temp1,
  step_assert_eq hpc3 with temp2,
  have a0: mem range_check_ptr = res.d0 + res.d1 + (2 ^ 128 - 2 * BASE), {
    apply assert_eq_reduction temp2.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps }, try { simp only [temp0, temp1] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a0 }, try { arith_simps at a0 },
  clear temp0 temp1 temp2,
  -- compound assert eq
  step_assert_eq hpc4 hpc5 with temp0,
  step_assert_eq hpc6 with temp1,
  have a4: mem (range_check_ptr + 1) = res.d2 + (2 ^ 128 - D2_BOUND), {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps }, try { simp only [temp0] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a4 }, try { arith_simps at a4 },
  clear temp0 temp1,
  -- let
  mkdef hl_range_check_ptr₁ : range_check_ptr₁ = (range_check_ptr + 2 : F),
  try { dsimp at hl_range_check_ptr₁ }, try { arith_simps at hl_range_check_ptr₁ },
  -- tempvar
  step_assert_eq hpc7 hpc8 with tv_range_check_ptr0,
  mkdef hl_range_check_ptr₂ : range_check_ptr₂ = (range_check_ptr₁ + 3 : F),
  have htv_range_check_ptr₂: range_check_ptr₂ = _, {
    apply eq.symm, apply eq.trans tv_range_check_ptr0,
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res, hl_range_check_ptr₁, hl_range_check_ptr₂] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_range_check_ptr0,
  try { dsimp at hl_range_check_ptr₂ }, try { arith_simps at hl_range_check_ptr₂ },
  -- assert eq
  step_assert_eq hpc9 with temp0,
  have a9: mem (range_check_ptr₂ - 3) = res.d0, {
    apply assert_eq_reduction temp0.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res, hl_range_check_ptr₁, hl_range_check_ptr₂, htv_range_check_ptr₂] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a9 }, try { arith_simps at a9 },
  clear temp0,
  -- assert eq
  step_assert_eq hpc10 with temp0,
  have a10: mem (range_check_ptr₂ - 2) = res.d1, {
    apply assert_eq_reduction temp0.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res, hl_range_check_ptr₁, hl_range_check_ptr₂, htv_range_check_ptr₂] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a10 }, try { arith_simps at a10 },
  clear temp0,
  -- assert eq
  step_assert_eq hpc11 with temp0,
  have a11: mem (range_check_ptr₂ - 1) = res.d2, {
    apply assert_eq_reduction temp0.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res, hl_range_check_ptr₁, hl_range_check_ptr₂, htv_range_check_ptr₂] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a11 }, try { arith_simps at a11 },
  clear temp0,
  -- return
  step_ret hpc12,
  -- finish
  step_done, use_only [rfl, rfl],
  split, refl,
  -- range check condition
  use_only (2+3+0+0), split,
  linarith [],
  split,
  { try { norm_num1 }, arith_simps,
    try { rw [←htv_range_check_ptr₂] }, try { rw [hl_range_check_ptr₂] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_nondet_bigint3 mem _ range_check_ptr _ _,
  { apply sound_nondet_bigint3, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_nondet_bigint3],
  try { norm_num1 }, try { arith_simps },
  use_only [res],
  use_only [a0],
  cases rc_h_range_check_ptr' (0) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a0.symm, hin_range_check_ptr], arith_simps, exact hn },
  use_only [a4],
  cases rc_h_range_check_ptr' (1) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a4.symm, hin_range_check_ptr], arith_simps, exact hn },
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁,
    try { norm_cast at rc_h_range_check_ptr₁' }, try { rw [add_zero] at rc_h_range_check_ptr₁' },
  use_only [range_check_ptr₁, hl_range_check_ptr₁],
  try { dsimp }, try { arith_simps },
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂,
    try { norm_cast at rc_h_range_check_ptr₂' }, try { rw [add_zero] at rc_h_range_check_ptr₂' },
  use_only [range_check_ptr₂, hl_range_check_ptr₂],
  try { dsimp }, try { arith_simps },
  use_only [a9],
  cases rc_h_range_check_ptr₁' (0) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a9.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [a10],
  cases rc_h_range_check_ptr₁' (1) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a10.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [a11],
  cases rc_h_range_check_ptr₁' (2) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a11.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hl_res, hl_range_check_ptr₁, hl_range_check_ptr₂, htv_range_check_ptr₂] }, },
  try { dsimp [cast_BigInt3] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

