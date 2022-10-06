/-
File: signature_recover_public_key_ec_mul_inner_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .signature_recover_public_key_code
import ..signature_recover_public_key_spec
import .signature_recover_public_key_fast_ec_add_soundness
import .signature_recover_public_key_ec_double_soundness
open tactic

open starkware.cairo.common.cairo_secp.ec
open starkware.cairo.common.cairo_secp.bigint
open starkware.cairo.common.cairo_secp.field

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.cairo_secp.ec.ec_mul_inner autogenerated soundness theorem -/

theorem auto_sound_ec_mul_inner
    -- arguments
    (range_check_ptr : F) (point : EcPoint F) (scalar m : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_ec_mul_inner σ.pc)
    -- all dependencies are in memory
    (h_mem_4 : mem_at mem code_nondet_bigint3 (σ.pc  - 460))
    (h_mem_5 : mem_at mem code_unreduced_mul (σ.pc  - 448))
    (h_mem_6 : mem_at mem code_unreduced_sqr (σ.pc  - 428))
    (h_mem_7 : mem_at mem code_verify_zero (σ.pc  - 412))
    (h_mem_12 : mem_at mem code_compute_doubling_slope (σ.pc  - 284))
    (h_mem_13 : mem_at mem code_compute_slope (σ.pc  - 240))
    (h_mem_14 : mem_at mem code_ec_double (σ.pc  - 216))
    (h_mem_15 : mem_at mem code_fast_ec_add (σ.pc  - 143))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 11))
    (hin_point : point = cast_EcPoint mem (σ.fp - 10))
    (hin_scalar : scalar = mem (σ.fp - 4))
    (hin_m : m = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 11)) (mem $ τ.ap - 13)
        (spec_ec_mul_inner mem κ range_check_ptr point scalar m (mem (τ.ap - 13)) (cast_EcPoint mem (τ.ap - 12)) (cast_EcPoint mem (τ.ap - 6)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  revert σ range_check_ptr point scalar m h_mem h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_12 h_mem_13 h_mem_14 h_mem_15 hin_range_check_ptr hin_point hin_scalar hin_m,
  induction νbound with νbound νih,
  { intros, intros n nlt, apply absurd nlt (nat.not_lt_zero _) },
  intros σ range_check_ptr point scalar m h_mem h_mem_4 h_mem_5 h_mem_6 h_mem_7 h_mem_12 h_mem_13 h_mem_14 h_mem_15 hin_range_check_ptr hin_point hin_scalar hin_m,
  dsimp at νih,
  have h_mem_rec := h_mem,
  unpack_memory code_ec_mul_inner at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27, hpc28, hpc29, hpc30, hpc31, hpc32, hpc33, hpc34, hpc35, hpc36, hpc37, hpc38, hpc39, hpc40, hpc41, hpc42, hpc43, hpc44, hpc45, hpc46, hpc47, hpc48, hpc49, hpc50, hpc51, hpc52, hpc53, hpc54, hpc55, hpc56, hpc57, hpc58, hpc59, hpc60, hpc61, hpc62, hpc63, hpc64, hpc65, hpc66, hpc67, hpc68, hpc69, hpc70, hpc71, hpc72, hpc73, hpc74, hpc75, hpc76, hpc77, hpc78, hpc79, hpc80, hpc81, hpc82, hpc83, hpc84, hpc85, hpc86, hpc87, hpc88, hpc89, hpc90, hpc91, hpc92, hpc93, hpc94, hpc95, hpc96, hpc97, hpc98, hpc99, hpc100⟩,
  -- if statement
  step_jnz hpc0 hpc1 with hcond hcond,
  {
    -- if: positive branch
    have a0 : m = 0, {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- assert eq
    step_assert_eq hpc2 hpc3 with temp0,
    have a2: scalar = 0, {
      apply assert_eq_reduction temp0,
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a2 }, try { arith_simps at a2 },
    clear temp0,
    -- let
    generalize' hl_rev_ZERO_POINT: ({
      x := { d0 := 0, d1 := 0, d2 := 0 },
      y := { d0 := 0, d1 := 0, d2 := 0 }
    } : EcPoint F) = ZERO_POINT,
    have hl_ZERO_POINT := hl_rev_ZERO_POINT.symm, clear hl_rev_ZERO_POINT,
    try { dsimp at hl_ZERO_POINT }, try { arith_simps at hl_ZERO_POINT },
    -- return
    step_assert_eq hpc4 with hret0,
    step_assert_eq hpc5 with hret1,
    step_assert_eq hpc6 with hret2,
    step_assert_eq hpc7 with hret3,
    step_assert_eq hpc8 with hret4,
    step_assert_eq hpc9 with hret5,
    step_assert_eq hpc10 with hret6,
    step_assert_eq hpc11 hpc12 with hret7,
    step_assert_eq hpc13 hpc14 with hret8,
    step_assert_eq hpc15 hpc16 with hret9,
    step_assert_eq hpc17 hpc18 with hret10,
    step_assert_eq hpc19 hpc20 with hret11,
    step_assert_eq hpc21 hpc22 with hret12,
    step_ret hpc23,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (0+0), split,
    linarith [],
    split,
    { arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5 ,hret6 ,hret7 ,hret8 ,hret9 ,hret10 ,hret11 ,hret12] },
      try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_ec_mul_inner mem _ range_check_ptr point scalar m _ _ _,
    { apply sound_ec_mul_inner, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_ec_mul_inner],
    try { norm_num1 }, try { arith_simps },
    left,
    use_only [a0],
    use_only [a2],
    use_only [ZERO_POINT, hl_ZERO_POINT],
    try { split, linarith },
    try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, hl_ZERO_POINT] }, },
    try { dsimp [cast_EcPoint, cast_BigInt3] },
    try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6, hret7, hret8, hret9, hret10, hret11, hret12] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  {
    -- if: negative branch
    have a0 : m ≠ 0, {
      try { simp only [ne.def] },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a0 }, try { arith_simps at a0 },
    clear hcond,
    -- ap += 6
    step_advance_ap hpc24 hpc25,
    -- function call
    step_assert_eq hpc26 with arg0,
    step_assert_eq hpc27 with arg1,
    step_assert_eq hpc28 with arg2,
    step_assert_eq hpc29 with arg3,
    step_assert_eq hpc30 with arg4,
    step_assert_eq hpc31 with arg5,
    step_assert_eq hpc32 with arg6,
    step_sub hpc33 (auto_sound_ec_double mem _ range_check_ptr point _ _ _ _ _ _ _ _),
    { rw hpc34, norm_num2, exact h_mem_14 },
    { rw hpc34, norm_num2, exact h_mem_4 },
    { rw hpc34, norm_num2, exact h_mem_5 },
    { rw hpc34, norm_num2, exact h_mem_6 },
    { rw hpc34, norm_num2, exact h_mem_7 },
    { rw hpc34, norm_num2, exact h_mem_12 },
    { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m] },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    { try { ext } ; {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
    intros κ_call35 ap35 h_call35,
    rcases h_call35 with ⟨rc_m35, rc_mle35, hl_range_check_ptr₁, h_call35⟩,
    generalize' hr_rev_range_check_ptr₁: mem (ap35 - 7) = range_check_ptr₁,
    have htv_range_check_ptr₁ := hr_rev_range_check_ptr₁.symm, clear hr_rev_range_check_ptr₁,
    generalize' hr_rev_double_point: cast_EcPoint mem (ap35 - 6) = double_point,
    simp only [hr_rev_double_point] at h_call35,
    have htv_double_point := hr_rev_double_point.symm, clear hr_rev_double_point,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at hl_range_check_ptr₁ },
    rw [←htv_range_check_ptr₁, ←hin_range_check_ptr] at hl_range_check_ptr₁,
    try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6] at h_call35 },
    rw [hin_range_check_ptr] at h_call35,
    clear arg0 arg1 arg2 arg3 arg4 arg5 arg6,
    -- jnz
    apply of_register_state,
    intros regstate35 regstate35eq,
    have regstateapeq_a35 := congr_arg register_state.ap regstate35eq,
    try { dsimp at regstateapeq_a35 },
    step_jnz hpc35 hpc36 with a35 a35,
    {
      -- jnz: positive branch
      rw ←regstateapeq_a35 at a35,
      -- tail recursive function call
      step_assert_eq hpc37 with arg0,
      step_assert_eq hpc38 with arg1,
      step_assert_eq hpc39 with arg2,
      step_assert_eq hpc40 with arg3,
      step_assert_eq hpc41 with arg4,
      step_assert_eq hpc42 with arg5,
      step_assert_eq hpc43 with arg6,
      step_assert_eq hpc44 hpc45 with arg7,
      step_assert_eq hpc46 hpc47 with arg8,
      have h_δ37_c0 : ∀ x : F, x / (2 : ℤ) = x * (-1809251394333065606848661391547535052811553607665798349986546028067936010240 : ℤ),
      { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
      have h_δ37_c0_fz : ∀ x : F, x / 2 = x / (2 : ℤ), { intro x, norm_cast }, 
      step_rec_sub hpc48 (νih _ range_check_ptr₁ double_point (scalar / (2 : ℤ)) (m - 1) _ _ _ _ _ _ _ _ _ _ _ _ _),
      { rw hpc49, norm_num, exact h_mem_rec },
      { rw hpc49, norm_num2, exact h_mem_4 },
      { rw hpc49, norm_num2, exact h_mem_5 },
      { rw hpc49, norm_num2, exact h_mem_6 },
      { rw hpc49, norm_num2, exact h_mem_7 },
      { rw hpc49, norm_num2, exact h_mem_12 },
      { rw hpc49, norm_num2, exact h_mem_13 },
      { rw hpc49, norm_num2, exact h_mem_14 },
      { rw hpc49, norm_num2, exact h_mem_15 },
      { try { simp only [h_δ37_c0_fz, h_δ37_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [h_δ37_c0_fz, h_δ37_c0] }, try { ext } ; {
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
      { try { simp only [h_δ37_c0_fz, h_δ37_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [h_δ37_c0_fz, h_δ37_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      intros κ_call50 ap50 h_call50,
      rcases h_call50 with ⟨rc_m50, rc_mle50, hl_range_check_ptr₂, h_call50⟩,
      step_ret hpc50,
      generalize' hr_rev_range_check_ptr₂: mem (ap50 - 13) = range_check_ptr₂,
      have htv_range_check_ptr₂ := hr_rev_range_check_ptr₂.symm, clear hr_rev_range_check_ptr₂,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8] at hl_range_check_ptr₂ },
      rw [←htv_range_check_ptr₂, ←htv_range_check_ptr₁] at hl_range_check_ptr₂,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8] at h_call50 },
      rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call50,
      clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8,
      -- finish
      step_done, use_only [rfl, rfl],
      -- range check condition
      use_only (rc_m35+rc_m50+0+0), split,
      linarith [rc_mle35, rc_mle50],
      split,
      { arith_simps,
        rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr],
        try { arith_simps, refl <|> norm_cast }, try { refl } },
      intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
      have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
      -- Final Proof
      -- user-provided reduction
      suffices auto_spec: auto_spec_ec_mul_inner mem _ range_check_ptr point scalar m _ _ _,
      { apply sound_ec_mul_inner, apply auto_spec },
      -- prove the auto generated assertion
      dsimp [auto_spec_ec_mul_inner],
      try { norm_num1 }, try { arith_simps },
      right,
      use_only [a0],
      use_only [κ_call35],
      use_only [range_check_ptr₁],
      use_only [double_point],
      have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
      have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
      have spec35 := h_call35 rc_h_range_check_ptr',
      rw [←hin_range_check_ptr, ←htv_range_check_ptr₁] at spec35,
      try { dsimp at spec35, arith_simps at spec35 },
      use_only [spec35],
      use_only (mem regstate35.ap),
      left,
      use_only [a35],
      use_only [κ_call50],
      have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
      have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
      have spec50 := h_call50 rc_h_range_check_ptr₁',
      rw [←hin_range_check_ptr, ←hl_range_check_ptr₁] at spec50,
      try { dsimp at spec50, arith_simps at spec50 },
      use_only [spec50],
      try { linarith },
    },
    {
      -- jnz: negative branch
      rw ←regstateapeq_a35 at a35,
      -- recursive function call
      step_assert_eq hpc51 hpc52 with arg0,
      step_assert_eq hpc53 with arg1,
      step_assert_eq hpc54 with arg2,
      step_assert_eq hpc55 with arg3,
      step_assert_eq hpc56 with arg4,
      step_assert_eq hpc57 with arg5,
      step_assert_eq hpc58 with arg6,
      step_assert_eq hpc59 with arg7,
      step_assert_eq hpc60 hpc61 with arg8,
      step_assert_eq hpc62 hpc63 with arg9,
      have h_δ51_c0 : ∀ x : F, x / (2 : ℤ) = x * (-1809251394333065606848661391547535052811553607665798349986546028067936010240 : ℤ),
      { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
      have h_δ51_c0_fz : ∀ x : F, x / 2 = x / (2 : ℤ), { intro x, norm_cast }, 
      step_rec_sub hpc64 (νih _ range_check_ptr₁ double_point ((scalar - 1) / (2 : ℤ)) (m - 1) _ _ _ _ _ _ _ _ _ _ _ _ _),
      { rw hpc65, norm_num, exact h_mem_rec },
      { rw hpc65, norm_num2, exact h_mem_4 },
      { rw hpc65, norm_num2, exact h_mem_5 },
      { rw hpc65, norm_num2, exact h_mem_6 },
      { rw hpc65, norm_num2, exact h_mem_7 },
      { rw hpc65, norm_num2, exact h_mem_12 },
      { rw hpc65, norm_num2, exact h_mem_13 },
      { rw hpc65, norm_num2, exact h_mem_14 },
      { rw hpc65, norm_num2, exact h_mem_15 },
      { try { simp only [h_δ51_c0_fz, h_δ51_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [h_δ51_c0_fz, h_δ51_c0] }, try { ext } ; {
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
      { try { simp only [h_δ51_c0_fz, h_δ51_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [h_δ51_c0_fz, h_δ51_c0] }, try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      intros κ_call66 ap66 h_call66,
      rcases h_call66 with ⟨rc_m66, rc_mle66, hl_range_check_ptr₂, h_call66⟩,
      generalize' hr_rev_range_check_ptr₂: mem (ap66 - 13) = range_check_ptr₂,
      have htv_range_check_ptr₂ := hr_rev_range_check_ptr₂.symm, clear hr_rev_range_check_ptr₂,
      generalize' hr_rev_inner_pow2: cast_EcPoint mem (ap66 - 12) = inner_pow2,
      simp only [hr_rev_inner_pow2] at h_call66,
      have htv_inner_pow2 := hr_rev_inner_pow2.symm, clear hr_rev_inner_pow2,
      generalize' hr_rev_inner_res: cast_EcPoint mem (ap66 - 6) = inner_res,
      simp only [hr_rev_inner_res] at h_call66,
      have htv_inner_res := hr_rev_inner_res.symm, clear hr_rev_inner_res,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9] at hl_range_check_ptr₂ },
      rw [←htv_range_check_ptr₂, ←htv_range_check_ptr₁] at hl_range_check_ptr₂,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9] at h_call66 },
      rw [←htv_range_check_ptr₁, hl_range_check_ptr₁, hin_range_check_ptr] at h_call66,
      clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9,
      -- local var
      step_assert_eq hpc66 with temp0,
      step_assert_eq hpc67 with temp1,
      step_assert_eq hpc68 with temp2,
      step_assert_eq hpc69 with temp3,
      step_assert_eq hpc70 with temp4,
      step_assert_eq hpc71 with temp5,
      have lc_inner_pow2: inner_pow2 = cast_EcPoint mem σ.fp, {
        try { ext } ; {
          try { simp only [htv_inner_pow2] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [temp0, temp1, temp2, temp3, temp4, temp5] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
      clear temp0 temp1 temp2 temp3 temp4 temp5,
      -- function call
      step_assert_eq hpc72 with arg0,
      step_assert_eq hpc73 with arg1,
      step_assert_eq hpc74 with arg2,
      step_assert_eq hpc75 with arg3,
      step_assert_eq hpc76 with arg4,
      step_assert_eq hpc77 with arg5,
      step_assert_eq hpc78 with arg6,
      step_assert_eq hpc79 with arg7,
      step_assert_eq hpc80 with arg8,
      step_assert_eq hpc81 with arg9,
      step_assert_eq hpc82 with arg10,
      step_assert_eq hpc83 with arg11,
      step_assert_eq hpc84 with arg12,
      step_sub hpc85 (auto_sound_fast_ec_add mem _ range_check_ptr₂ point inner_res _ _ _ _ _ _ _ _ _),
      { rw hpc86, norm_num2, exact h_mem_15 },
      { rw hpc86, norm_num2, exact h_mem_4 },
      { rw hpc86, norm_num2, exact h_mem_5 },
      { rw hpc86, norm_num2, exact h_mem_6 },
      { rw hpc86, norm_num2, exact h_mem_7 },
      { rw hpc86, norm_num2, exact h_mem_13 },
      { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point, htv_range_check_ptr₂, htv_inner_pow2, htv_inner_res, lc_inner_pow2] },
        try { dsimp [cast_EcPoint, cast_BigInt3] },
        try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { ext } ; {
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point, htv_range_check_ptr₂, htv_inner_pow2, htv_inner_res, lc_inner_pow2] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
      { try { ext } ; {
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point, htv_range_check_ptr₂, htv_inner_pow2, htv_inner_res, lc_inner_pow2] },
          try { dsimp [cast_EcPoint, cast_BigInt3] },
          try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
      intros κ_call87 ap87 h_call87,
      rcases h_call87 with ⟨rc_m87, rc_mle87, hl_range_check_ptr₃, h_call87⟩,
      generalize' hr_rev_range_check_ptr₃: mem (ap87 - 7) = range_check_ptr₃,
      have htv_range_check_ptr₃ := hr_rev_range_check_ptr₃.symm, clear hr_rev_range_check_ptr₃,
      generalize' hr_rev_res: cast_EcPoint mem (ap87 - 6) = res,
      simp only [hr_rev_res] at h_call87,
      have htv_res := hr_rev_res.symm, clear hr_rev_res,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12] at hl_range_check_ptr₃ },
      rw [←htv_range_check_ptr₃, ←htv_range_check_ptr₂] at hl_range_check_ptr₃,
      try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5 ,arg6 ,arg7 ,arg8 ,arg9 ,arg10 ,arg11 ,arg12] at h_call87 },
      rw [←htv_range_check_ptr₂, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr] at h_call87,
      clear arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12,
      -- return
      step_assert_eq hpc87 with hret0,
      step_assert_eq hpc88 with hret1,
      step_assert_eq hpc89 with hret2,
      step_assert_eq hpc90 with hret3,
      step_assert_eq hpc91 with hret4,
      step_assert_eq hpc92 with hret5,
      step_assert_eq hpc93 with hret6,
      step_assert_eq hpc94 with hret7,
      step_assert_eq hpc95 with hret8,
      step_assert_eq hpc96 with hret9,
      step_assert_eq hpc97 with hret10,
      step_assert_eq hpc98 with hret11,
      step_assert_eq hpc99 with hret12,
      step_ret hpc100,
      -- finish
      step_done, use_only [rfl, rfl],
      -- range check condition
      use_only (rc_m35+rc_m66+rc_m87+0+0), split,
      linarith [rc_mle35, rc_mle66, rc_mle87],
      split,
      { arith_simps, try { simp only [hret0 ,hret1 ,hret2 ,hret3 ,hret4 ,hret5 ,hret6 ,hret7 ,hret8 ,hret9 ,hret10 ,hret11 ,hret12] },
        rw [←htv_range_check_ptr₃, hl_range_check_ptr₃, hl_range_check_ptr₂, hl_range_check_ptr₁, hin_range_check_ptr],
        try { arith_simps, refl <|> norm_cast }, try { refl } },
      intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
      have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
      -- Final Proof
      -- user-provided reduction
      suffices auto_spec: auto_spec_ec_mul_inner mem _ range_check_ptr point scalar m _ _ _,
      { apply sound_ec_mul_inner, apply auto_spec },
      -- prove the auto generated assertion
      dsimp [auto_spec_ec_mul_inner],
      try { norm_num1 }, try { arith_simps },
      right,
      use_only [a0],
      use_only [κ_call35],
      use_only [range_check_ptr₁],
      use_only [double_point],
      have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
      have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
      have spec35 := h_call35 rc_h_range_check_ptr',
      rw [←hin_range_check_ptr, ←htv_range_check_ptr₁] at spec35,
      try { dsimp at spec35, arith_simps at spec35 },
      use_only [spec35],
      use_only (mem regstate35.ap),
      right,
      use_only [a35],
      use_only [κ_call66],
      use_only [range_check_ptr₂],
      use_only [inner_pow2],
      use_only [inner_res],
      have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
      have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
      have spec66 := h_call66 rc_h_range_check_ptr₁',
      rw [←hin_range_check_ptr, ←hl_range_check_ptr₁, ←htv_range_check_ptr₂] at spec66,
      try { dsimp at spec66, arith_simps at spec66 },
      use_only [spec66],
      use_only [κ_call87],
      use_only [range_check_ptr₃],
      use_only [res],
      have rc_h_range_check_ptr₃ := range_checked_offset' rc_h_range_check_ptr₂,
      have rc_h_range_check_ptr₃' := range_checked_add_right rc_h_range_check_ptr₃, try { norm_cast at rc_h_range_check_ptr₃' },
      have spec87 := h_call87 rc_h_range_check_ptr₂',
      rw [←hin_range_check_ptr, ←hl_range_check_ptr₁, ←hl_range_check_ptr₂, ←htv_range_check_ptr₃] at spec87,
      try { dsimp at spec87, arith_simps at spec87 },
      use_only [spec87],
      try { split, linarith },
      try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_point, hin_scalar, hin_m, htv_range_check_ptr₁, htv_double_point, htv_range_check_ptr₂, htv_inner_pow2, htv_inner_res, lc_inner_pow2, htv_range_check_ptr₃, htv_res] }, },
      try { dsimp [cast_EcPoint, cast_BigInt3] },
      try { arith_simps }, try { simp only [hret0, hret1, hret2, hret3, hret4, hret5, hret6, hret7, hret8, hret9, hret10, hret11, hret12] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    }
  }
end

