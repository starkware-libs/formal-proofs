/-
File: signature_recover_public_key_div_mod_n_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_bigint_mul_soundness
import .signature_recover_public_key_nondet_bigint3_soundness
open tactic

open starkware.cairo.common.cairo_secp.signature
open starkware.cairo.common.cairo_secp.bigint
open starkware.cairo.common.cairo_secp.constants

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.cairo_secp.signature.div_mod_n autogenerated soundness theorem -/

theorem auto_sound_div_mod_n
    -- arguments
    (range_check_ptr : F) (a b : BigInt3 F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_div_mod_n σ.pc)
    -- all dependencies are in memory
    (h_mem_3 : mem_at mem code_bigint_mul (σ.pc  - 668))
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 654))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 9))
    (hin_a : a = cast_BigInt3 mem (σ.fp - 8))
    (hin_b : b = cast_BigInt3 mem (σ.fp - 5))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 88 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 9)) (mem $ τ.ap - 4)
        (spec_div_mod_n mem κ range_check_ptr a b (mem (τ.ap - 4)) (cast_BigInt3 mem (τ.ap - 3)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_div_mod_n at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37, hpc38, hpc39, hpc40, hpc41, hpc42, hpc43, hpc44, hpc45, hpc46, hpc47, hpc48, hpc49, hpc50, hpc51, hpc52, hpc53, hpc54, hpc55, hpc56, hpc57, hpc58, hpc59, hpc60, hpc61, hpc62, hpc63, hpc64⟩,
  -- function call
  step_assert_eq hpc0 with arg0,
  step_sub hpc1 (auto_sound_nondet_bigint3 mem _ range_check_ptr _ _),
  { rw hpc2, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call3 ap3 h_call3,
  rcases h_call3 with ⟨h_call3_ap_offset, h_call3⟩,
  rcases h_call3 with ⟨rc_m3, rc_mle3, hl_range_check_ptr₁, h_call3⟩,
  generalize' hr_rev_range_check_ptr₁: mem (ap3 - 4) = range_check_ptr₁,
  have htv_range_check_ptr₁ := hr_rev_range_check_ptr₁.symm, clear hr_rev_range_check_ptr₁,
  generalize' hr_rev_res: cast_BigInt3 mem (ap3 - 3) = res,
  simp only [hr_rev_res] at h_call3,
  have htv_res := hr_rev_res.symm, clear hr_rev_res,
  try { simp only [arg0] at hl_range_check_ptr₁ },
  rw [←htv_range_check_ptr₁, ←hin_range_check_ptr] at hl_range_check_ptr₁,
  try { simp only [arg0] at h_call3 },
  rw [hin_range_check_ptr] at h_call3,
  clear arg0,
  -- function call
  step_assert_eq hpc3 with arg0,
  step_sub hpc4 (auto_sound_nondet_bigint3 mem _ range_check_ptr₁ _ _),
  { rw hpc5, norm_num2, exact h_mem_4 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res] },
    try { dsimp [cast_BigInt3] },
    try { arith_simps }, try { simp only [arg0] },
    try { simp only [h_call3_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call6 ap6 h_call6,
  rcases h_call6 with ⟨h_call6_ap_offset, h_call6⟩,
  rcases h_call6 with ⟨rc_m6, rc_mle6, hl_range_check_ptr₂, h_call6⟩,
  generalize' hr_rev_range_check_ptr₂: mem (ap6 - 4) = range_check_ptr₂,
  have htv_range_check_ptr₂ := hr_rev_range_check_ptr₂.symm, clear hr_rev_range_check_ptr₂,
  generalize' hr_rev_k: cast_BigInt3 mem (ap6 - 3) = k,
  simp only [hr_rev_k] at h_call6,
  have htv_k := hr_rev_k.symm, clear hr_rev_k,
  try { simp only [arg0] at hl_range_check_ptr₂ },
  rw [←htv_range_check_ptr₂, ←htv_range_check_ptr₁] at hl_range_check_ptr₂,
  try { simp only [arg0] at h_call6 },
  rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call6,
  clear arg0,
  -- function call
  step_assert_eq hpc6 with arg0,
  step_assert_eq hpc7 with arg1,
  step_assert_eq hpc8 with arg2,
  step_assert_eq hpc9 with arg3,
  step_assert_eq hpc10 with arg4,
  step_assert_eq hpc11 with arg5,
  step_sub hpc12 (auto_sound_bigint_mul mem _ res b _ _ _),
  { rw hpc13, norm_num2, exact h_mem_3 },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k] },
      try { dsimp [cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call14 ap14 h_call14,
  rcases h_call14 with ⟨h_call14_ap_offset, h_call14⟩,
  generalize' hr_rev_res_b: cast_UnreducedBigInt5 mem (ap14 - 5) = res_b,
  simp only [hr_rev_res_b] at h_call14,
  have htv_res_b := hr_rev_res_b.symm, clear hr_rev_res_b,
  clear arg0 arg1 arg2 arg3 arg4 arg5,
  -- let
  generalize' hl_rev_n: ({
    d0 := N0,
    d1 := N1,
    d2 := N2
  } : BigInt3 F) = n,
  have hl_n := hl_rev_n.symm, clear hl_rev_n,
  try { dsimp at hl_n }, try { arith_simps at hl_n },
  -- function call
  step_assert_eq hpc14 with arg0,
  step_assert_eq hpc15 with arg1,
  step_assert_eq hpc16 with arg2,
  step_assert_eq hpc17 hpc18 with arg3,
  step_assert_eq hpc19 hpc20 with arg4,
  step_assert_eq hpc21 hpc22 with arg5,
  step_sub hpc23 (auto_sound_bigint_mul mem _ k n _ _ _),
  { rw hpc24, norm_num2, exact h_mem_3 },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  intros κ_call25 ap25 h_call25,
  rcases h_call25 with ⟨h_call25_ap_offset, h_call25⟩,
  generalize' hr_rev_k_n: cast_UnreducedBigInt5 mem (ap25 - 5) = k_n,
  simp only [hr_rev_k_n] at h_call25,
  have htv_k_n := hr_rev_k_n.symm, clear hr_rev_k_n,
  clear arg0 arg1 arg2 arg3 arg4 arg5,
  -- tempvar
  step_assert_eq hpc25 with tv_carry10,
  step_assert_eq hpc26 with tv_carry11,
  step_assert_eq hpc27 hpc28 with tv_carry12,
  generalize' hl_rev_carry1: ((res_b.d0 - k_n.d0 - a.d0) / (BASE : ℤ) : F) = carry1,
  have hl_carry1 := hl_rev_carry1.symm, clear hl_rev_carry1,
  have htv_carry1: carry1 = _, {
    have h_δ25_c0 : ∀ x : F, x / (BASE : ℤ) = x * (-46768052394588894761721767695234645457402928824320 : ℤ),
    { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
    apply eq.symm, apply eq.trans tv_carry12,
      try { simp only [h_δ25_c0] at hl_carry1 },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add tv_carry10), (eq_sub_of_eq_add tv_carry11)] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_carry10 tv_carry11 tv_carry12,
  try { dsimp at hl_carry1 }, try { arith_simps at hl_carry1 },
  -- compound assert eq
  step_assert_eq hpc29 hpc30 with temp0,
  step_assert_eq hpc31 with temp1,
  have a29: mem (range_check_ptr₂ + 0) = carry1 + 2 ^ 127, {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1] },
    try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
    try { arith_simps }, try { simp only [temp0] },
    try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a29 }, try { arith_simps at a29 },
  clear temp0 temp1,
  -- tempvar
  step_assert_eq hpc32 with tv_carry20,
  step_assert_eq hpc33 with tv_carry21,
  step_assert_eq hpc34 with tv_carry22,
  step_assert_eq hpc35 hpc36 with tv_carry23,
  generalize' hl_rev_carry2: ((res_b.d1 - k_n.d1 - a.d1 + carry1) / (BASE : ℤ) : F) = carry2,
  have hl_carry2 := hl_rev_carry2.symm, clear hl_rev_carry2,
  have htv_carry2: carry2 = _, {
    have h_δ32_c0 : ∀ x : F, x / (BASE : ℤ) = x * (-46768052394588894761721767695234645457402928824320 : ℤ),
    { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
    apply eq.symm, apply eq.trans tv_carry23,
      try { simp only [h_δ32_c0] at hl_carry2 },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add tv_carry20), (eq_sub_of_eq_add tv_carry21), tv_carry22] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_carry20 tv_carry21 tv_carry22 tv_carry23,
  try { dsimp at hl_carry2 }, try { arith_simps at hl_carry2 },
  -- compound assert eq
  step_assert_eq hpc37 hpc38 with temp0,
  step_assert_eq hpc39 with temp1,
  have a37: mem (range_check_ptr₂ + 1) = carry2 + 2 ^ 127, {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2] },
    try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
    try { arith_simps }, try { simp only [temp0] },
    try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a37 }, try { arith_simps at a37 },
  clear temp0 temp1,
  -- tempvar
  step_assert_eq hpc40 with tv_carry30,
  step_assert_eq hpc41 with tv_carry31,
  step_assert_eq hpc42 with tv_carry32,
  step_assert_eq hpc43 hpc44 with tv_carry33,
  generalize' hl_rev_carry3: ((res_b.d2 - k_n.d2 - a.d2 + carry2) / (BASE : ℤ) : F) = carry3,
  have hl_carry3 := hl_rev_carry3.symm, clear hl_rev_carry3,
  have htv_carry3: carry3 = _, {
    have h_δ40_c0 : ∀ x : F, x / (BASE : ℤ) = x * (-46768052394588894761721767695234645457402928824320 : ℤ),
    { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
    apply eq.symm, apply eq.trans tv_carry33,
      try { simp only [h_δ40_c0] at hl_carry3 },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add tv_carry30), (eq_sub_of_eq_add tv_carry31), tv_carry32] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_carry30 tv_carry31 tv_carry32 tv_carry33,
  try { dsimp at hl_carry3 }, try { arith_simps at hl_carry3 },
  -- compound assert eq
  step_assert_eq hpc45 hpc46 with temp0,
  step_assert_eq hpc47 with temp1,
  have a45: mem (range_check_ptr₂ + 2) = carry3 + 2 ^ 127, {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3, htv_carry3] },
    try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
    try { arith_simps }, try { simp only [temp0] },
    try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a45 }, try { arith_simps at a45 },
  clear temp0 temp1,
  -- tempvar
  step_assert_eq hpc48 with tv_carry40,
  step_assert_eq hpc49 with tv_carry41,
  step_assert_eq hpc50 hpc51 with tv_carry42,
  generalize' hl_rev_carry4: ((res_b.d3 - k_n.d3 + carry3) / (BASE : ℤ) : F) = carry4,
  have hl_carry4 := hl_rev_carry4.symm, clear hl_rev_carry4,
  have htv_carry4: carry4 = _, {
    have h_δ48_c0 : ∀ x : F, x / (BASE : ℤ) = x * (-46768052394588894761721767695234645457402928824320 : ℤ),
    { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
    apply eq.symm, apply eq.trans tv_carry42,
      try { simp only [h_δ48_c0] at hl_carry4 },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3, htv_carry3, hl_carry4] },
      try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
      try { arith_simps }, try { simp only [(eq_sub_of_eq_add tv_carry40), tv_carry41] },
      try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_carry40 tv_carry41 tv_carry42,
  try { dsimp at hl_carry4 }, try { arith_simps at hl_carry4 },
  -- compound assert eq
  step_assert_eq hpc52 hpc53 with temp0,
  step_assert_eq hpc54 with temp1,
  have a52: mem (range_check_ptr₂ + 3) = carry4 + 2 ^ 127, {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3, htv_carry3, hl_carry4, htv_carry4] },
    try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
    try { arith_simps }, try { simp only [temp0] },
    try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a52 }, try { arith_simps at a52 },
  clear temp0 temp1,
  -- compound assert eq
  step_assert_eq hpc55 with temp0,
  step_assert_eq hpc56 hpc57 with temp1,
  step_assert_eq hpc58 with temp2,
  have a55: res_b.d4 - k_n.d4 + carry4 = 0, {
    apply assert_eq_reduction temp2.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3, htv_carry3, hl_carry4, htv_carry4] },
    try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
    try { arith_simps }, try { simp only [(eq_sub_of_eq_add temp0), temp1] },
    try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a55 }, try { arith_simps at a55 },
  clear temp0 temp1 temp2,
  -- let
  generalize' hl_rev_range_check_ptr₃: (range_check_ptr₂ + 4 : F) = range_check_ptr₃,
  have hl_range_check_ptr₃ := hl_rev_range_check_ptr₃.symm, clear hl_rev_range_check_ptr₃,
  try { dsimp at hl_range_check_ptr₃ }, try { arith_simps at hl_range_check_ptr₃ },
  -- return
  step_assert_eq hpc59 hpc60 with hret0,
  step_assert_eq hpc61 with hret1,
  step_assert_eq hpc62 with hret2,
  step_assert_eq hpc63 with hret3,
  step_ret hpc64,
  -- finish
  step_done, use_only [rfl, rfl],
  split,
  { try { simp only [h_call3_ap_offset ,h_call6_ap_offset ,h_call14_ap_offset ,h_call25_ap_offset] },
    try { arith_simps }, try { refl } },
  -- range check condition
  use_only (rc_m3+rc_m6+4+0+0), split,
  linarith [rc_mle3, rc_mle6],
  split,
  { arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3] },
    try { simp only [h_call25_ap_offset ,h_call14_ap_offset] }, try { arith_simps },
    rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr],
    try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_div_mod_n mem _ range_check_ptr a b _ _,
  { apply sound_div_mod_n, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_div_mod_n],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call3],
  use_only [range_check_ptr₁],
  use_only [res],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec3 := h_call3 rc_h_range_check_ptr',
  rw [←hin_range_check_ptr, ←htv_range_check_ptr₁] at spec3,
  try { dsimp at spec3, arith_simps at spec3 },
  use_only [spec3],
  use_only [κ_call6],
  use_only [range_check_ptr₂],
  use_only [k],
  have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
  have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
  have spec6 := h_call6 rc_h_range_check_ptr₁',
  rw [←hin_range_check_ptr, ←hl_range_check_ptr₁, ←htv_range_check_ptr₂] at spec6,
  try { dsimp at spec6, arith_simps at spec6 },
  use_only [spec6],
  use_only [κ_call14],
  use_only [res_b],
  try { dsimp at h_call14, arith_simps at h_call14 },
  try { use_only [h_call14] },
  use_only [n, hl_n],
  use_only [κ_call25],
  use_only [k_n],
  try { dsimp at h_call25, arith_simps at h_call25 },
  try { use_only [h_call25] },
  use_only [carry1, hl_carry1],
  use_only [a29],
  cases rc_h_range_check_ptr₂' (0) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a29.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [carry2, hl_carry2],
  use_only [a37],
  cases rc_h_range_check_ptr₂' (1) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a37.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [carry3, hl_carry3],
  use_only [a45],
  cases rc_h_range_check_ptr₂' (2) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a45.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [carry4, hl_carry4],
  use_only [a52],
  cases rc_h_range_check_ptr₂' (3) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a52.symm, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr], arith_simps, exact hn },
  use_only [a55],
  have rc_h_range_check_ptr₃ := range_checked_offset' rc_h_range_check_ptr₂,
  have rc_h_range_check_ptr₃' := range_checked_add_right rc_h_range_check_ptr₃,try { norm_cast at rc_h_range_check_ptr₃' },
  use_only [range_check_ptr₃, hl_range_check_ptr₃],
  try { split, linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_a, hin_b, htv_range_check_ptr₁, htv_res, htv_range_check_ptr₂, htv_k, htv_res_b, hl_n, htv_k_n, hl_carry1, htv_carry1, hl_carry2, htv_carry2, hl_carry3, htv_carry3, hl_carry4, htv_carry4, hl_range_check_ptr₃] }, },
  try { dsimp [cast_BigInt3, cast_UnreducedBigInt5] },
  try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3] },
  try { simp only [h_call3_ap_offset, h_call6_ap_offset, h_call14_ap_offset, h_call25_ap_offset] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end
