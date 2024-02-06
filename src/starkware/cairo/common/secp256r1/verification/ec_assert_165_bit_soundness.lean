/-
File: ec_assert_165_bit_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .ec_code
import ..ec_spec
open tactic

open starkware.cairo.common.secp256r1.field

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.secp256r1.field.assert_165_bit autogenerated soundness theorem -/

theorem auto_sound_assert_165_bit
    -- arguments
    (range_check_ptr value : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_assert_165_bit σ.pc)
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 4))
    (hin_value : value = mem (σ.fp - 3))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      τ.ap = σ.ap + 5 ∧
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 4)) (mem $ τ.ap - 1)
        (spec_assert_165_bit mem κ range_check_ptr value (mem (τ.ap - 1)))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_assert_165_bit at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10⟩,
  -- const
  mkdef hc_UPPER_BOUND : UPPER_BOUND = (46768052394588893382517914646921056628989841375232 : F),
  -- const
  mkdef hc_SHIFT : SHIFT = (340282366920938463463374607431768211456 : F),
  -- const
  mkdef hc_HIGH_BOUND : HIGH_BOUND = (137438953472 : F),
  -- let
  mkdef hl_low : low = (mem range_check_ptr : F),
  try { dsimp at hl_low }, try { arith_simps at hl_low },
  -- let
  mkdef hl_high : high = (mem (range_check_ptr + 1) : F),
  try { dsimp at hl_high }, try { arith_simps at hl_high },
  -- tempvar
  step_assert_eq hpc0 with tv_high0,
  mkdef hl_high₁ : high₁ = (high : F),
  have htv_high₁: high₁ = _, {
    apply eq.symm, apply eq.trans tv_high0,
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_value, hc_UPPER_BOUND, hc_SHIFT, hc_HIGH_BOUND, hl_low, hl_high, hl_high₁] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  clear tv_high0,
  try { dsimp at hl_high₁ }, try { arith_simps at hl_high₁ },
  -- compound assert eq
  step_assert_eq hpc1 hpc2 with temp0,
  step_assert_eq hpc3 with temp1,
  have a1: mem (range_check_ptr + 2) = high₁ + (SHIFT - HIGH_BOUND), {
    apply assert_eq_reduction temp1.symm,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_value, hc_UPPER_BOUND, hc_SHIFT, hc_HIGH_BOUND, hl_low, hl_high, hl_high₁, htv_high₁] },
    try { arith_simps }, try { simp only [temp0] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a1 }, try { arith_simps at a1 },
  clear temp0 temp1,
  -- compound assert eq
  step_assert_eq hpc4 hpc5 with temp0,
  step_assert_eq hpc6 with temp1,
  step_assert_eq hpc7 with temp2,
  have a4: value = high₁ * SHIFT + low, {
    apply assert_eq_reduction temp2,
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_value, hc_UPPER_BOUND, hc_SHIFT, hc_HIGH_BOUND, hl_low, hl_high, hl_high₁, htv_high₁] },
    try { arith_simps }, try { simp only [temp0, temp1] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a4 }, try { arith_simps at a4 },
  clear temp0 temp1 temp2,
  -- let
  mkdef hl_range_check_ptr₁ : range_check_ptr₁ = (range_check_ptr + 3 : F),
  try { dsimp at hl_range_check_ptr₁ }, try { arith_simps at hl_range_check_ptr₁ },
  -- return
  step_assert_eq hpc8 hpc9 with hret0,
  step_ret hpc10,
  -- finish
  step_done, use_only [rfl, rfl],
  split, refl,
  -- range check condition
  use_only (3+0+0), split,
  linarith [],
  split,
  { try { norm_num1 }, arith_simps, try { simp only [hret0] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  -- user-provided reduction
  suffices auto_spec: auto_spec_assert_165_bit mem _ range_check_ptr value _,
  { apply sound_assert_165_bit, apply auto_spec },
  -- prove the auto generated assertion
  dsimp [auto_spec_assert_165_bit],
  try { norm_num1 }, try { arith_simps },
  use [UPPER_BOUND, hc_UPPER_BOUND],
  use [SHIFT, hc_SHIFT],
  use [HIGH_BOUND, hc_HIGH_BOUND],
  use_only [low, hl_low],
  try { dsimp }, try { arith_simps },
  cases rc_h_range_check_ptr' (0) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [hl_low, hin_range_check_ptr], arith_simps, exact hn },
  use_only [high, hl_high],
  try { dsimp }, try { arith_simps },
  cases rc_h_range_check_ptr' (1) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [hl_high, hin_range_check_ptr], arith_simps, exact hn },
  use_only [high₁, hl_high₁],
  try { dsimp }, try { arith_simps },
  use_only [a1],
  cases rc_h_range_check_ptr' (2) (by norm_num1) with n hn, arith_simps at hn,
  use_only [n], { simp only [a1.symm, hin_range_check_ptr], arith_simps, exact hn },
  use_only [a4],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁,
    try { norm_cast at rc_h_range_check_ptr₁' }, try { rw [add_zero] at rc_h_range_check_ptr₁' },
  use_only [range_check_ptr₁, hl_range_check_ptr₁],
  try { dsimp }, try { arith_simps },
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_value, hc_UPPER_BOUND, hc_SHIFT, hc_HIGH_BOUND, hl_low, hl_high, hl_high₁, htv_high₁, hl_range_check_ptr₁] }, },
  try { arith_simps }, try { simp only [hret0] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

