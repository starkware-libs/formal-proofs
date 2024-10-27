/-
File: ec_fast_ec_mul_inner_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
import .ec_fast_ec_add_soundness
import .ec_assert_nn_le_soundness
import .ec_ec_double_soundness
open tactic

open starkware.cairo.common.secp256r1.ec
open starkware.cairo.common.cairo_secp.ec_point
open starkware.cairo.common.math
open starkware.cairo.common.secp256r1.field
open starkware.cairo.common.secp256r1.bigint
open starkware.cairo.common.cairo_secp.bigint3

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.ec.fast_ec_mul_inner autogenerated soundness theorem -/

theorem auto_sound_fast_ec_mul_inner
    -- arguments
    (range_check_ptr : F) (table : π_EcPoint mem) (point : EcPoint mem) (scalar m : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_fast_ec_mul_inner σ.pc)
    -- all dependencies are in memory
    (h_mem_1 : mem_at mem code_assert_nn (σ.pc  - 1187))
    (h_mem_2 : mem_at mem code_assert_le (σ.pc  - 1183))
    (h_mem_3 : mem_at mem code_assert_nn_le (σ.pc  - 1178))
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 1169))
    (h_mem_5 : mem_at mem code_unreduced_mul (σ.pc  - 1156))
    (h_mem_6 : mem_at mem code_unreduced_sqr (σ.pc  - 1118))
    (h_mem_7 : mem_at mem code_assert_165_bit (σ.pc  - 1084))
    (h_mem_8 : mem_at mem code_verify_zero (σ.pc  - 1073))
    (h_mem_12 : mem_at mem code_compute_doubling_slope (σ.pc  - 950))
    (h_mem_13 : mem_at mem code_compute_slope (σ.pc  - 904))
    (h_mem_14 : mem_at mem code_ec_double (σ.pc  - 880))
    (h_mem_15 : mem_at mem code_fast_ec_add (σ.pc  - 807))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 12))
    (hin_table : table = cast_π_EcPoint mem (mem (σ.fp - 11)))
    (hin_point : point = cast_EcPoint mem (σ.fp - 10))
    (hin_scalar : scalar = mem (σ.fp - 4))
    (hin_m : m = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 12)) (mem $ τ.ap - 8)
        (spec_fast_ec_mul_inner mem κ range_check_ptr table point scalar m (mem (τ.ap - 8)) (cast_EcPoint  mem (τ.ap - 7)) (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  revert σ range_check_ptr table point scalar m h_mem h_mem_1 h_mem_2 h_mem_3 h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_8 h_mem_12 h_mem_13 h_mem_14 h_mem_15 hin_range_check_ptr hin_table hin_point hin_scalar hin_m,
  induction νbound with νbound νih,
  { intros, intros n nlt, apply absurd nlt (nat.not_lt_zero _) },
  intros σ range_check_ptr table point scalar m h_mem h_mem_1 h_mem_2 h_mem_3 h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_8 h_mem_12 h_mem_13 h_mem_14 h_mem_15 hin_range_check_ptr hin_table hin_point hin_scalar hin_m,
  dsimp at νih,
  have h_mem_rec := h_mem,
  unpack_memory code_fast_ec_mul_inner at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37, hpc38, hpc39, hpc40, hpc41, hpc42, hpc43, hpc44, hpc45, hpc46, hpc47, hpc48, hpc49, hpc50, hpc51, hpc52, hpc53, hpc54, hpc55, hpc56, hpc57, hpc58, hpc59, hpc60, hpc61, hpc62, hpc63, hpc64, hpc65, hpc66, hpc67, hpc68, hpc69, hpc70, hpc71, hpc72, hpc73, hpc74, hpc75, hpc76, hpc77, hpc78, hpc79, hpc80, hpc81, hpc82, hpc83, hpc84, hpc85, hpc86, hpc87, hpc88, hpc89, hpc90, hpc91, hpc92, hpc93⟩,
  -- ap += 1
  step_advance_ap hpc0 hpc1,
  -- if statement
  step_jnz hpc2 hpc3 with hcond hcond,
  {
    -- if: positive branch
    have a2 : m = 0, {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a2 }, try { arith_simps at a2 },
    clear hcond,
    -- return
    step_assert_eq hpc4 with hret0,
    step_assert_eq hpc5 with hret1,
    step_assert_eq hpc6 with hret2,
    step_assert_eq hpc7 with hret3,
    step_assert_eq hpc8 with hret4,
    step_assert_eq hpc9 with hret5,
    step_assert_eq hpc10 with hret6,
    step_assert_eq hpc11 with hret7,
    step_ret hpc12,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (0+0), split,
    linarith [],
    split,
    { try { norm_num1 }, arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5 ,hret6 ,hret7] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_fast_ec_mul_inner mem _ range_check_ptr table point scalar m _ _ _,
    { apply sound_fast_ec_mul_inner, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_fast_ec_mul_inner],
    try { norm_num1 }, try { arith_simps },
    left,
    use_only [a2],
    try { split, trivial <|> linarith },
    try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m] }, },
    try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
    try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
    try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6, hret7] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  {
    -- if: negative branch
    have a2 : m ≠ 0, {
      try { simp only [ne.def] },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a2 }, try { arith_simps at a2 },
    clear hcond,
    -- function call
    step_assert_eq hpc13 with arg0,
    step_assert_eq hpc14 with arg1,
    step_assert_eq hpc15 with arg2,
    step_assert_eq hpc16 with arg3,
    step_assert_eq hpc17 with arg4,
    step_assert_eq hpc18 with arg5,
    step_assert_eq hpc19 with arg6,
    step_sub hpc20 (auto_sound_ec_double mem _ range_check_ptr point _ _ _ _ _ _ _ _ _),
    { rw hpc21, norm_num2, exact h_mem_14 },
    { rw hpc21, norm_num2, exact h_mem_4 },
    { rw hpc21, norm_num2, exact h_mem_5 },
    { rw hpc21, norm_num2, exact h_mem_6 },
    { rw hpc21, norm_num2, exact h_mem_7 },
    { rw hpc21, norm_num2, exact h_mem_8 },
    { rw hpc21, norm_num2, exact h_mem_12 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call22 ap22 h_call22,
    rcases h_call22 with ⟨rc_m22, rc_mle22, hl_range_check_ptr₁, h_call22⟩,
    mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap22 - 7)),
    simp only [←htv_range_check_ptr₁] at h_call22,
    mkdef htv_point₁ : point₁ = (cast_EcPoint mem (ap22 - 6)),
    simp only [←htv_point₁] at h_call22,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at hl_range_check_ptr₁ },
    try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at h_call22 },
    rw [hin_range_check_ptr] at h_call22,
    clear arg0 arg1 arg2 arg3 arg4 arg5 arg6,
    -- function call
    step_sub hpc22 (auto_sound_ec_double mem _ range_check_ptr₁ point₁ _ _ _ _ _ _ _ _ _),
    { rw hpc23, norm_num2, exact h_mem_14 },
    { rw hpc23, norm_num2, exact h_mem_4 },
    { rw hpc23, norm_num2, exact h_mem_5 },
    { rw hpc23, norm_num2, exact h_mem_6 },
    { rw hpc23, norm_num2, exact h_mem_7 },
    { rw hpc23, norm_num2, exact h_mem_8 },
    { rw hpc23, norm_num2, exact h_mem_12 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call24 ap24 h_call24,
    rcases h_call24 with ⟨rc_m24, rc_mle24, hl_range_check_ptr₂, h_call24⟩,
    mkdef htv_range_check_ptr₂ : range_check_ptr₂ = (mem (ap24 - 7)),
    simp only [←htv_range_check_ptr₂] at h_call24,
    mkdef htv_point₂ : point₂ = (cast_EcPoint mem (ap24 - 6)),
    simp only [←htv_point₂] at h_call24,
    try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₂ }, try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₂ },
    rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call24,
    clear ,
    -- function call
    step_sub hpc24 (auto_sound_ec_double mem _ range_check_ptr₂ point₂ _ _ _ _ _ _ _ _ _),
    { rw hpc25, norm_num2, exact h_mem_14 },
    { rw hpc25, norm_num2, exact h_mem_4 },
    { rw hpc25, norm_num2, exact h_mem_5 },
    { rw hpc25, norm_num2, exact h_mem_6 },
    { rw hpc25, norm_num2, exact h_mem_7 },
    { rw hpc25, norm_num2, exact h_mem_8 },
    { rw hpc25, norm_num2, exact h_mem_12 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call26 ap26 h_call26,
    rcases h_call26 with ⟨rc_m26, rc_mle26, hl_range_check_ptr₃, h_call26⟩,
    mkdef htv_range_check_ptr₃ : range_check_ptr₃ = (mem (ap26 - 7)),
    simp only [←htv_range_check_ptr₃] at h_call26,
    mkdef htv_point₃ : point₃ = (cast_EcPoint mem (ap26 - 6)),
    simp only [←htv_point₃] at h_call26,
    try { rw [←htv_range_check_ptr₃] at hl_range_check_ptr₃ }, try { rw [←htv_range_check_ptr₂] at hl_range_check_ptr₃ },
    rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call26,
    clear ,
    -- function call
    step_sub hpc26 (auto_sound_ec_double mem _ range_check_ptr₃ point₃ _ _ _ _ _ _ _ _ _),
    { rw hpc27, norm_num2, exact h_mem_14 },
    { rw hpc27, norm_num2, exact h_mem_4 },
    { rw hpc27, norm_num2, exact h_mem_5 },
    { rw hpc27, norm_num2, exact h_mem_6 },
    { rw hpc27, norm_num2, exact h_mem_7 },
    { rw hpc27, norm_num2, exact h_mem_8 },
    { rw hpc27, norm_num2, exact h_mem_12 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call28 ap28 h_call28,
    rcases h_call28 with ⟨rc_m28, rc_mle28, hl_range_check_ptr₄, h_call28⟩,
    mkdef htv_range_check_ptr₄ : range_check_ptr₄ = (mem (ap28 - 7)),
    simp only [←htv_range_check_ptr₄] at h_call28,
    mkdef htv_point₄ : point₄ = (cast_EcPoint mem (ap28 - 6)),
    simp only [←htv_point₄] at h_call28,
    try { rw [←htv_range_check_ptr₄] at hl_range_check_ptr₄ }, try { rw [←htv_range_check_ptr₃] at hl_range_check_ptr₄ },
    rw [←htv_range_check_ptr₃, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call28,
    clear ,
    -- local var
    mkdef lc_nibble : nibble = (mem (σ.fp)),
    -- function call
    step_assert_eq hpc28 with arg0,
    step_assert_eq hpc29 with arg1,
    step_assert_eq hpc30 hpc31 with arg2,
    step_sub hpc32 (auto_sound_assert_nn_le mem _ range_check_ptr₄ nibble 15 _ _ _ _ _ _),
    { rw hpc33, norm_num2, exact h_mem_3 },
    { rw hpc33, norm_num2, exact h_mem_1 },
    { rw hpc33, norm_num2, exact h_mem_2 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    intros κ_call34 ap34 h_call34,
    rcases h_call34 with ⟨h_call34_ap_offset, h_call34⟩,
    rcases h_call34 with ⟨rc_m34, rc_mle34, hl_range_check_ptr₅, h_call34⟩,
    mkdef htv_range_check_ptr₅ : range_check_ptr₅ = (mem (ap34 - 1)),
    simp only [←htv_range_check_ptr₅] at h_call34,
    try { simp only [arg0 ,arg1 ,arg2] at hl_range_check_ptr₅ },
    try { rw [←htv_range_check_ptr₅] at hl_range_check_ptr₅ }, try { rw [←htv_range_check_ptr₄] at hl_range_check_ptr₅ },
    try { simp only [arg0 ,arg1 ,arg2] at h_call34 },
    rw [←htv_range_check_ptr₄, hl_range_check_ptr₄, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call34,
    clear arg0 arg1 arg2,
    -- function call
    step_assert_eq hpc34 hpc35 with arg0,
    step_assert_eq hpc36 with arg1,
    step_assert_eq hpc37 hpc38 with arg2,
    step_assert_eq hpc39 hpc40 with arg3,
    step_assert_eq hpc41 with arg4,
    step_assert_eq hpc42 hpc43 with arg5,
    step_assert_eq hpc44 hpc45 with arg6,
    step_assert_eq hpc46 with arg7,
    step_assert_eq hpc47 hpc48 with arg8,
    step_assert_eq hpc49 hpc50 with arg9,
    step_assert_eq hpc51 with arg10,
    step_assert_eq hpc52 hpc53 with arg11,
    step_assert_eq hpc54 hpc55 with arg12,
    step_assert_eq hpc56 with arg13,
    step_assert_eq hpc57 hpc58 with arg14,
    step_assert_eq hpc59 hpc60 with arg15,
    step_assert_eq hpc61 with arg16,
    step_assert_eq hpc62 with arg17,
    step_assert_eq hpc63 with arg18,
    step_assert_eq hpc64 with arg19,
    step_assert_eq hpc65 with arg20,
    step_assert_eq hpc66 with arg21,
    step_assert_eq hpc67 with arg22,
    step_assert_eq hpc68 with arg23,
    step_assert_eq hpc69 with arg24,
    step_assert_eq hpc70 with arg25,
    step_assert_eq hpc71 with arg26,
    step_assert_eq hpc72 with arg27,
    step_assert_eq hpc73 with arg28,
    step_assert_eq hpc74 with arg29,
    step_sub hpc75 (auto_sound_fast_ec_add mem _ range_check_ptr₅ point₄ (cast_EcPoint mem (table.σ_ptr + nibble * 6)) _ _ _ _ _ _ _ _ _ _),
    { rw hpc76, norm_num2, exact h_mem_15 },
    { rw hpc76, norm_num2, exact h_mem_4 },
    { rw hpc76, norm_num2, exact h_mem_5 },
    { rw hpc76, norm_num2, exact h_mem_6 },
    { rw hpc76, norm_num2, exact h_mem_7 },
    { rw hpc76, norm_num2, exact h_mem_8 },
    { rw hpc76, norm_num2, exact h_mem_13 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16, arg17, arg18, arg19, arg20, arg21, arg22, arg23, arg24, arg25, arg26, arg27, arg28, arg29] },
      try { simp only [h_call34_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16, arg17, arg18, arg19, arg20, arg21, arg22, arg23, arg24, arg25, arg26, arg27, arg28, arg29] },
        try { simp only [h_call34_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16, arg17, arg18, arg19, arg20, arg21, arg22, arg23, arg24, arg25, arg26, arg27, arg28, arg29] },
        try { simp only [h_call34_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call77 ap77 h_call77,
    rcases h_call77 with ⟨rc_m77, rc_mle77, hl_range_check_ptr₆, h_call77⟩,
    mkdef htv_range_check_ptr₆ : range_check_ptr₆ = (mem (ap77 - 7)),
    simp only [←htv_range_check_ptr₆] at h_call77,
    mkdef htv_point₅ : point₅ = (cast_EcPoint mem (ap77 - 6)),
    simp only [←htv_point₅] at h_call77,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12 ,arg13 ,arg14 ,arg15 ,arg16 ,arg17 ,arg18 ,arg19 ,arg20 ,arg21 ,arg22 ,arg23 ,arg24 ,arg25 ,arg26 ,arg27 ,arg28 ,arg29] at hl_range_check_ptr₆ },
    try { rw [←htv_range_check_ptr₆] at hl_range_check_ptr₆ }, try { rw [←htv_range_check_ptr₅] at hl_range_check_ptr₆ },
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12 ,arg13 ,arg14 ,arg15 ,arg16 ,arg17 ,arg18 ,arg19 ,arg20 ,arg21 ,arg22 ,arg23 ,arg24 ,arg25 ,arg26 ,arg27 ,arg28 ,arg29] at h_call77 },
    rw [←htv_range_check_ptr₅, hl_range_check_ptr₅, hl_range_check_ptr₄, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call77,
    clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12 arg13 arg14 arg15 arg16 arg17 arg18 arg19 arg20 arg21 arg22 arg23 arg24 arg25 arg26 arg27 arg28 arg29,
    -- tail recursive function call
    step_assert_eq hpc77 hpc78 with arg0,
    step_assert_eq hpc79 with arg1,
    step_assert_eq hpc80 with arg2,
    step_assert_eq hpc81 with arg3,
    step_assert_eq hpc82 with arg4,
    step_assert_eq hpc83 with arg5,
    step_assert_eq hpc84 with arg6,
    step_assert_eq hpc85 with arg7,
    step_assert_eq hpc86 with arg8,
    step_assert_eq hpc87 with arg9,
    step_assert_eq hpc88 with arg10,
    step_assert_eq hpc89 hpc90 with arg11,
    step_rec_sub hpc91 (νih _ range_check_ptr₆ table point₅ (16 * scalar + nibble) (m - 4) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _),
    { rw hpc92, norm_num, exact h_mem_rec },
    { rw hpc92, norm_num2, exact h_mem_1 },
    { rw hpc92, norm_num2, exact h_mem_2 },
    { rw hpc92, norm_num2, exact h_mem_3 },
    { rw hpc92, norm_num2, exact h_mem_4 },
    { rw hpc92, norm_num2, exact h_mem_5 },
    { rw hpc92, norm_num2, exact h_mem_6 },
    { rw hpc92, norm_num2, exact h_mem_7 },
    { rw hpc92, norm_num2, exact h_mem_8 },
    { rw hpc92, norm_num2, exact h_mem_12 },
    { rw hpc92, norm_num2, exact h_mem_13 },
    { rw hpc92, norm_num2, exact h_mem_14 },
    { rw hpc92, norm_num2, exact h_mem_15 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅, htv_range_check_ptr₆, htv_point₅] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] },
      try { simp only [h_call34_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅, htv_range_check_ptr₆, htv_point₅] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] },
        try { simp only [h_call34_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅, htv_range_check_ptr₆, htv_point₅] },
        try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
        try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] },
        try { simp only [h_call34_ap_offset] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅, htv_range_check_ptr₆, htv_point₅] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] },
      try { simp only [h_call34_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_table, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_point₁, htv_range_check_ptr₂, htv_point₂, htv_range_check_ptr₃, htv_point₃, htv_range_check_ptr₄, htv_point₄, lc_nibble, htv_range_check_ptr₅, htv_range_check_ptr₆, htv_point₅] },
      try { simp only [eq_EcPoint_π_cast, coe_EcPoint_π_cast] },
      try { dsimp [cast_π_EcPoint, cast_BigInt3, cast_EcPoint] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] },
      try { simp only [h_call34_ap_offset] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    intros κ_call93 ap93 h_call93,
    rcases h_call93 with ⟨rc_m93, rc_mle93, hl_range_check_ptr₇, h_call93⟩,
    step_ret hpc93,
    mkdef htv_range_check_ptr₇ : range_check_ptr₇ = (mem (ap93 - 8)),
    simp only [←htv_range_check_ptr₇] at h_call93,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11] at hl_range_check_ptr₇ },
    try { rw [←htv_range_check_ptr₇] at hl_range_check_ptr₇ }, try { rw [←htv_range_check_ptr₆] at hl_range_check_ptr₇ },
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11] at h_call93 },
    rw [←htv_range_check_ptr₆, hl_range_check_ptr₆, hl_range_check_ptr₅, hl_range_check_ptr₄, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call93,
    clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (rc_m22+rc_m24+rc_m26+rc_m28+rc_m34+rc_m77+rc_m93+0+0), split,
    linarith [rc_mle22, rc_mle24, rc_mle26, rc_mle28, rc_mle34, rc_mle77, rc_mle93],
    split,
    { try { norm_num1 }, arith_simps,
      try { rw [←htv_range_check_ptr₇] }, try { rw [hl_range_check_ptr₇] }, try { rw [←htv_range_check_ptr₆] }, try { rw [hl_range_check_ptr₆] }, try { rw [←htv_range_check_ptr₅] }, try { rw [hl_range_check_ptr₅] }, try { rw [←htv_range_check_ptr₄] }, try { rw [hl_range_check_ptr₄] }, try { rw [←htv_range_check_ptr₃] }, try { rw [hl_range_check_ptr₃] }, try { rw [←htv_range_check_ptr₂] }, try { rw [hl_range_check_ptr₂] }, try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_fast_ec_mul_inner mem _ range_check_ptr table point scalar m _ _ _,
    { apply sound_fast_ec_mul_inner, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_fast_ec_mul_inner],
    try { norm_num1 }, try { arith_simps },
    right,
    use_only [a2],
    use_only [κ_call22],
    use_only [range_check_ptr₁],
    use_only [point₁],
    have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
    have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
    have spec22 := h_call22 rc_h_range_check_ptr',
      try { rw [←hin_range_check_ptr] at spec22 }, try { rw [←htv_range_check_ptr₁] at spec22 },
    try { dsimp at spec22, arith_simps at spec22 },
    use_only [spec22],
    use_only [κ_call24],
    use_only [range_check_ptr₂],
    use_only [point₂],
    have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
    have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
    have spec24 := h_call24 rc_h_range_check_ptr₁',
      try { rw [←hin_range_check_ptr] at spec24 }, try { rw [←hl_range_check_ptr₁] at spec24 }, try { rw [←htv_range_check_ptr₂] at spec24 },
    try { dsimp at spec24, arith_simps at spec24 },
    use_only [spec24],
    use_only [κ_call26],
    use_only [range_check_ptr₃],
    use_only [point₃],
    have rc_h_range_check_ptr₃ := range_checked_offset' rc_h_range_check_ptr₂,
    have rc_h_range_check_ptr₃' := range_checked_add_right rc_h_range_check_ptr₃, try { norm_cast at rc_h_range_check_ptr₃' },
    have spec26 := h_call26 rc_h_range_check_ptr₂',
      try { rw [←hin_range_check_ptr] at spec26 }, try { rw [←hl_range_check_ptr₁] at spec26 }, try { rw [←hl_range_check_ptr₂] at spec26 }, try { rw [←htv_range_check_ptr₃] at spec26 },
    try { dsimp at spec26, arith_simps at spec26 },
    use_only [spec26],
    use_only [κ_call28],
    use_only [range_check_ptr₄],
    use_only [point₄],
    have rc_h_range_check_ptr₄ := range_checked_offset' rc_h_range_check_ptr₃,
    have rc_h_range_check_ptr₄' := range_checked_add_right rc_h_range_check_ptr₄, try { norm_cast at rc_h_range_check_ptr₄' },
    have spec28 := h_call28 rc_h_range_check_ptr₃',
      try { rw [←hin_range_check_ptr] at spec28 }, try { rw [←hl_range_check_ptr₁] at spec28 }, try { rw [←hl_range_check_ptr₂] at spec28 }, try { rw [←hl_range_check_ptr₃] at spec28 }, try { rw [←htv_range_check_ptr₄] at spec28 },
    try { dsimp at spec28, arith_simps at spec28 },
    use_only [spec28],
    use_only [nibble],
    use_only [κ_call34],
    use_only [range_check_ptr₅],
    have rc_h_range_check_ptr₅ := range_checked_offset' rc_h_range_check_ptr₄,
    have rc_h_range_check_ptr₅' := range_checked_add_right rc_h_range_check_ptr₅, try { norm_cast at rc_h_range_check_ptr₅' },
    have spec34 := h_call34 rc_h_range_check_ptr₄',
      try { rw [←hin_range_check_ptr] at spec34 }, try { rw [←hl_range_check_ptr₁] at spec34 }, try { rw [←hl_range_check_ptr₂] at spec34 }, try { rw [←hl_range_check_ptr₃] at spec34 }, try { rw [←hl_range_check_ptr₄] at spec34 }, try { rw [←htv_range_check_ptr₅] at spec34 },
    try { dsimp at spec34, arith_simps at spec34 },
    use_only [spec34],
    use_only [κ_call77],
    use_only [range_check_ptr₆],
    use_only [point₅],
    have rc_h_range_check_ptr₆ := range_checked_offset' rc_h_range_check_ptr₅,
    have rc_h_range_check_ptr₆' := range_checked_add_right rc_h_range_check_ptr₆, try { norm_cast at rc_h_range_check_ptr₆' },
    have spec77 := h_call77 rc_h_range_check_ptr₅',
      try { rw [←hin_range_check_ptr] at spec77 }, try { rw [←hl_range_check_ptr₁] at spec77 }, try { rw [←hl_range_check_ptr₂] at spec77 }, try { rw [←hl_range_check_ptr₃] at spec77 }, try { rw [←hl_range_check_ptr₄] at spec77 }, try { rw [←hl_range_check_ptr₅] at spec77 }, try { rw [←htv_range_check_ptr₆] at spec77 },
    try { dsimp at spec77, arith_simps at spec77 },
    use_only [spec77],
    use_only [κ_call93],
    have rc_h_range_check_ptr₇ := range_checked_offset' rc_h_range_check_ptr₆,
    have rc_h_range_check_ptr₇' := range_checked_add_right rc_h_range_check_ptr₇, try { norm_cast at rc_h_range_check_ptr₇' },
    have spec93 := h_call93 rc_h_range_check_ptr₆',
      try { rw [←hin_range_check_ptr] at spec93 }, try { rw [←hl_range_check_ptr₁] at spec93 }, try { rw [←hl_range_check_ptr₂] at spec93 }, try { rw [←hl_range_check_ptr₃] at spec93 }, try { rw [←hl_range_check_ptr₄] at spec93 }, try { rw [←hl_range_check_ptr₅] at spec93 }, try { rw [←hl_range_check_ptr₆] at spec93 },
    try { dsimp at spec93, arith_simps at spec93 },
    use_only [spec93],
    try { linarith },
  }
end
