/-
File: squash_dict_squash_dict_soundness.lean

Autogenerated file.
-/
import starkware.cairo.lean.semantics.soundness.hoare
import .squash_dict_code
import ..squash_dict_spec
import .squash_dict_squash_dict_inner_soundness
open tactic

open starkware.cairo.common.squash_dict
open starkware.cairo.common.math
open starkware.cairo.common.dict_access

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]
variable  mem : F → F
variable  σ : register_state F

/- starkware.cairo.common.squash_dict.squash_dict autogenerated soundness theorem -/

theorem auto_sound_squash_dict_block14
    -- An independent ap variable.
    (ap : F)
    -- arguments
    (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem) (ptr_diff first_key big_keys n_accesses : F)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_squash_dict σ.pc)
    -- all dependencies are in memory
    (h_mem_0 : mem_at mem code_assert_le_felt (σ.pc  - 56))
    (h_mem_1 : mem_at mem code_assert_lt_felt (σ.pc  - 11))
    (h_mem_3 : mem_at mem code_squash_dict_inner (σ.pc  + 28))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (ap - 1))
    (hin_dict_accesses : dict_accesses = cast_π_DictAccess mem (mem (σ.fp - 5)))
    (hin_dict_accesses_end : dict_accesses_end = cast_π_DictAccess mem (mem (σ.fp - 4)))
    (hin_squashed_dict : squashed_dict = cast_π_DictAccess mem (mem (σ.fp - 3)))
    (hin_ptr_diff : ptr_diff = mem σ.fp)
    (hin_first_key : first_key = mem (σ.fp + 1))
    (hin_big_keys : big_keys = mem (σ.fp + 2))
    (hin_n_accesses : n_accesses = mem (ap - 2))
    (νbound : ℕ)
    -- conclusion
  : ensuresb_ret νbound mem
    {pc := σ.pc + 18, ap := ap, fp := σ.fp}
    (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (ap - 1)) (mem $ τ.ap - 2)
        (auto_spec_squash_dict_block14 mem κ range_check_ptr dict_accesses dict_accesses_end squashed_dict ptr_diff first_key big_keys n_accesses (mem (τ.ap - 2)) (cast_π_DictAccess  mem (mem (τ.ap - 1))))) :=
begin
  have h_mem_rec := h_mem,
  unpack_memory code_squash_dict at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27⟩,
  -- function call
  step_assert_eq hpc18 with arg0,
  step_assert_eq hpc19 hpc20 with arg1,
  step_assert_eq hpc21 with arg2,
  step_assert_eq hpc22 with arg3,
  step_assert_eq hpc23 with arg4,
  step_assert_eq hpc24 with arg5,
  step_sub hpc25 (auto_sound_squash_dict_inner mem _ range_check_ptr dict_accesses (dict_accesses_end - 1) first_key n_accesses squashed_dict big_keys _ _ _ _ _ _ _ _ _ _),
  { rw hpc26, norm_num2, exact h_mem_3 },
  { rw hpc26, norm_num2, exact h_mem_0 },
  { rw hpc26, norm_num2, exact h_mem_1 },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
      try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
      try { dsimp [cast_π_DictAccess] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  { try { ext } ; {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
      try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
      try { dsimp [cast_π_DictAccess] },
      try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },}, },
  { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [arg0, arg1, arg2, arg3, arg4, arg5] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
  intros κ_call27 ap27 h_call27,
  rcases h_call27 with ⟨rc_m27, rc_mle27, hl_range_check_ptr₁, h_call27⟩,
  mkdef htv_range_check_ptr₁ : range_check_ptr₁ = (mem (ap27 - 2)),
  simp only [←htv_range_check_ptr₁] at h_call27,
  mkdef htv_squashed_dict₁ : squashed_dict₁ = (cast_π_DictAccess mem (mem (ap27 - 1))),
  simp only [←htv_squashed_dict₁] at h_call27,
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5] at hl_range_check_ptr₁ },
  try { rw [←htv_range_check_ptr₁] at hl_range_check_ptr₁ }, try { rw [←hin_range_check_ptr] at hl_range_check_ptr₁ },
  try { simp only [arg0 ,arg1 ,arg2 ,arg3 ,arg4 ,arg5] at h_call27 },
  rw [hin_range_check_ptr] at h_call27,
  clear arg0 arg1 arg2 arg3 arg4 arg5,
  -- return
  step_ret hpc27,
  -- finish
  step_done, use_only [rfl, rfl],
  -- range check condition
  use_only (rc_m27+0+0), split,
  linarith [rc_mle27],
  split,
  { try { norm_num1 }, arith_simps,
    try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
    try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
  intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
  have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
  -- Final Proof
  dsimp [auto_spec_squash_dict_block14],
  try { norm_num1 }, try { arith_simps },
  use_only [κ_call27],
  use_only [range_check_ptr₁],
  use_only [squashed_dict₁],
  have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
  have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁, try { norm_cast at rc_h_range_check_ptr₁' },
  have spec27 := h_call27 rc_h_range_check_ptr',
    try { rw [←hin_range_check_ptr] at spec27 }, try { rw [←htv_range_check_ptr₁] at spec27 },
  try { dsimp at spec27, arith_simps at spec27 },
  use_only [spec27],
  try { split, trivial <|> linarith },
  try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, hin_ptr_diff, hin_first_key, hin_big_keys, hin_n_accesses, htv_range_check_ptr₁, htv_squashed_dict₁] }, },
  try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
  try { dsimp [cast_π_DictAccess] },
  try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
end

theorem auto_sound_squash_dict
    -- arguments
    (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem)
    -- code is in memory at σ.pc
    (h_mem : mem_at mem code_squash_dict σ.pc)
    -- all dependencies are in memory
    (h_mem_0 : mem_at mem code_assert_le_felt (σ.pc  - 56))
    (h_mem_1 : mem_at mem code_assert_lt_felt (σ.pc  - 11))
    (h_mem_3 : mem_at mem code_squash_dict_inner (σ.pc  + 28))
    -- input arguments on the stack
    (hin_range_check_ptr : range_check_ptr = mem (σ.fp - 6))
    (hin_dict_accesses : dict_accesses = cast_π_DictAccess mem (mem (σ.fp - 5)))
    (hin_dict_accesses_end : dict_accesses_end = cast_π_DictAccess mem (mem (σ.fp - 4)))
    (hin_squashed_dict : squashed_dict = cast_π_DictAccess mem (mem (σ.fp - 3)))
    -- conclusion
  : ensures_ret mem σ (λ κ τ,
      ∃ μ ≤ κ, rc_ensures mem (rc_bound F) μ (mem (σ.fp - 6)) (mem $ τ.ap - 2)
        (spec_squash_dict mem κ range_check_ptr dict_accesses dict_accesses_end squashed_dict (mem (τ.ap - 2)) (cast_π_DictAccess  mem (mem (τ.ap - 1))))) :=
begin
  apply ensures_of_ensuresb, intro νbound,
  have h_mem_rec := h_mem,
  unpack_memory code_squash_dict at h_mem with ⟨hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7, hpc8, hpc9, hpc10, hpc11, hpc12, hpc13, hpc14, hpc15, hpc16, hpc17, hpc18, hpc19, hpc20, hpc21, hpc22, hpc23, hpc24, hpc25, hpc26, hpc27⟩,
  -- ap += 3
  step_advance_ap hpc0 hpc1,
  -- local var
  mkdef lc_ptr_diff : ptr_diff = (mem (σ.fp)),
  -- compound assert eq
  step_assert_eq hpc2 with temp0,
  have a2: ptr_diff = dict_accesses_end - dict_accesses, {
    apply assert_eq_reduction (eq_sub_of_eq_add temp0),
    try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff] },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  try { dsimp at a2 }, try { arith_simps at a2 },
  clear temp0,
  -- if statement
  step_jnz hpc3 hpc4 with hcond hcond,
  {
    -- if: positive branch
    have a3 : ptr_diff = 0, {
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff] },
      try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
      try { dsimp [cast_π_DictAccess] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a3 }, try { arith_simps at a3 },
    clear hcond,
    -- return
    step_assert_eq hpc5 with hret0,
    step_assert_eq hpc6 with hret1,
    step_ret hpc7,
    -- finish
    step_done, use_only [rfl, rfl],
    -- range check condition
    use_only (0+0), split,
    linarith [],
    split,
    { try { norm_num1 }, arith_simps, try { simp only [hret0 ,hret1] },
      try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
    intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
    have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
    -- Final Proof
    -- user-provided reduction
    suffices auto_spec: auto_spec_squash_dict mem _ range_check_ptr dict_accesses dict_accesses_end squashed_dict _ _,
    { apply sound_squash_dict, apply auto_spec },
    -- prove the auto generated assertion
    dsimp [auto_spec_squash_dict],
    try { norm_num1 }, try { arith_simps },
    use_only [ptr_diff],
    use_only [a2],
    left,
    use_only [a3],
    try { split, trivial <|> linarith },
    try { ensures_simps; try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff] }, },
    try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
    try { dsimp [cast_π_DictAccess] },
    try { arith_simps }, try { simp only [hret0, hret1] },
    try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
  },
  {
    -- if: negative branch
    have a3 : ptr_diff ≠ 0, {
      try { simp only [ne.def] },
      try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff] },
      try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
      try { dsimp [cast_π_DictAccess] },
      try { arith_simps }, try { simp only [hcond] },
      try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
    },
    try { dsimp at a3 }, try { arith_simps at a3 },
    clear hcond,
    -- local var
    mkdef lc_first_key : first_key = (mem (σ.fp + 1)),
    -- local var
    mkdef lc_big_keys : big_keys = (mem (σ.fp + 2)),
    -- tempvar
    step_assert_eq hpc8 hpc9 with tv_n_accesses0,
    mkdef hl_n_accesses : n_accesses = (ptr_diff / (DictAccess.SIZE : ℤ) : F),
    have htv_n_accesses: n_accesses = _, {
      have h_δ8_c0 : ∀ x : F, x / (DictAccess.SIZE : ℤ) = x * (1206167596222043737899107594365023368541035738443865566657697352045290673494 : ℤ),
      { intro x,  apply div_eq_mul_inv', apply PRIME.int_cast_mul_eq_one, rw [PRIME], try { simp_int_casts }, norm_num1 },
      apply eq.symm, apply eq.trans tv_n_accesses0,
        try { simp only [h_δ8_c0] at hl_n_accesses },
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
    clear tv_n_accesses0,
    try { dsimp at hl_n_accesses }, try { arith_simps at hl_n_accesses },
    -- if statement
    step_jnz hpc10 hpc11 with hcond hcond,
    {
      -- if: positive branch
      have a10 : big_keys = 0, {
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps }, try { simp only [hcond] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      try { dsimp at a10 }, try { arith_simps at a10 },
      clear hcond,
      -- compound assert eq
      step_assert_eq hpc12 with temp0,
      have a12: first_key = mem range_check_ptr, {
        apply assert_eq_reduction temp0,
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      try { dsimp at a12 }, try { arith_simps at a12 },
      clear temp0,
      -- tempvar
      step_assert_eq hpc13 hpc14 with tv_range_check_ptr0,
      mkdef hl_range_check_ptr₁ : range_check_ptr₁ = (range_check_ptr + 1 : F),
      have htv_range_check_ptr₁: range_check_ptr₁ = _, {
        apply eq.symm, apply eq.trans tv_range_check_ptr0,
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁] },
          try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
          try { dsimp [cast_π_DictAccess] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      clear tv_range_check_ptr0,
      try { dsimp at hl_range_check_ptr₁ }, try { arith_simps at hl_range_check_ptr₁ },
      -- jump statement
      step_jump_imm hpc15 hpc16,
      -- Use the block soundness theorem.
      apply ensuresb_ret_trans (auto_sound_squash_dict_block14 mem σ _ range_check_ptr₁ dict_accesses dict_accesses_end squashed_dict ptr_diff first_key big_keys n_accesses h_mem_rec h_mem_0 h_mem_1 h_mem_3 _ hin_dict_accesses hin_dict_accesses_end hin_squashed_dict lc_ptr_diff lc_first_key lc_big_keys _ νbound),
      rotate,
      { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁, htv_range_check_ptr₁] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁, htv_range_check_ptr₁] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      intros κ_block14 τ, try { arith_simps },
      intro h_block14,
      rcases h_block14 with ⟨rc_m_block14, rc_m_le_block14, hblk_range_check_ptr₂, h_block14⟩,
        try { rw [←htv_range_check_ptr₁] at h_block14 }, try { rw [hl_range_check_ptr₁] at h_block14 }, try { rw [hin_range_check_ptr] at h_block14 },
      -- range check condition
      use_only (1+rc_m_block14+0+0), split,
      linarith [rc_m_le_block14],
      split,
      { try { norm_num1 }, arith_simps, try { simp only [hblk_range_check_ptr₂] },
        try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
        try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
      intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
      have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
      -- Final Proof
      -- user-provided reduction
      suffices auto_spec: auto_spec_squash_dict mem _ range_check_ptr dict_accesses dict_accesses_end squashed_dict _ _,
      { apply sound_squash_dict, apply auto_spec },
      -- prove the auto generated assertion
      dsimp [auto_spec_squash_dict],
      try { norm_num1 }, try { arith_simps },
      use_only [ptr_diff],
      use_only [a2],
      right,
      use_only [a3],
      use_only [first_key],
      use_only [big_keys],
      use_only [n_accesses, hl_n_accesses],
      try { dsimp }, try { arith_simps },
      right,
      use_only [a10],
      use_only [a12],
      cases rc_h_range_check_ptr' (0) (by norm_num1) with n hn, arith_simps at hn,
      use_only [n], { simp only [a12, hin_range_check_ptr], arith_simps, exact hn },
      have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
      have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁,
        try { norm_cast at rc_h_range_check_ptr₁' }, try { rw [add_zero] at rc_h_range_check_ptr₁' },
      use_only [range_check_ptr₁, hl_range_check_ptr₁],
      try { dsimp }, try { arith_simps },
      have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
      have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
      have h_block14' := h_block14 rc_h_range_check_ptr₁',
      try { rw [←hin_range_check_ptr] at h_block14' }, try { rw [←hl_range_check_ptr₁] at h_block14' },
      try { dsimp at h_block14, arith_simps at h_block14' },
      have h_block14 := h_block14',
      use_only [κ_block14],
      use [h_block14],
      try { linarith }
    },
    {
      -- if: negative branch
      have a10 : big_keys ≠ 0, {
        try { simp only [ne.def] },
        try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps }, try { simp only [hcond] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } },
      },
      try { dsimp at a10 }, try { arith_simps at a10 },
      clear hcond,
      -- tempvar
      step_assert_eq hpc17 with tv_range_check_ptr0,
      mkdef hl_range_check_ptr₁ : range_check_ptr₁ = (range_check_ptr : F),
      have htv_range_check_ptr₁: range_check_ptr₁ = _, {
        apply eq.symm, apply eq.trans tv_range_check_ptr0,
          try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁] },
          try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
          try { dsimp [cast_π_DictAccess] },
          try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      clear tv_range_check_ptr0,
      try { dsimp at hl_range_check_ptr₁ }, try { arith_simps at hl_range_check_ptr₁ },
      -- Use the block soundness theorem.
      apply ensuresb_ret_trans (auto_sound_squash_dict_block14 mem σ _ range_check_ptr₁ dict_accesses dict_accesses_end squashed_dict ptr_diff first_key big_keys n_accesses h_mem_rec h_mem_0 h_mem_1 h_mem_3 _ hin_dict_accesses hin_dict_accesses_end hin_squashed_dict lc_ptr_diff lc_first_key lc_big_keys _ νbound),
      rotate,
      { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁, htv_range_check_ptr₁] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      { try { simp only [add_neg_eq_sub, hin_range_check_ptr, hin_dict_accesses, hin_dict_accesses_end, hin_squashed_dict, lc_ptr_diff, lc_first_key, lc_big_keys, hl_n_accesses, htv_n_accesses, hl_range_check_ptr₁, htv_range_check_ptr₁] },
        try { simp only [eq_DictAccess_π_cast, coe_DictAccess_π_cast] },
        try { dsimp [cast_π_DictAccess] },
        try { arith_simps; try { split }; triv <|> refl <|> simp <|> abel; try { norm_num } }, },
      intros κ_block14 τ, try { arith_simps },
      intro h_block14,
      rcases h_block14 with ⟨rc_m_block14, rc_m_le_block14, hblk_range_check_ptr₂, h_block14⟩,
        try { rw [←htv_range_check_ptr₁] at h_block14 }, try { rw [hl_range_check_ptr₁] at h_block14 }, try { rw [hin_range_check_ptr] at h_block14 },
      -- range check condition
      use_only (0+rc_m_block14+0+0), split,
      linarith [rc_m_le_block14],
      split,
      { try { norm_num1 }, arith_simps, try { simp only [hblk_range_check_ptr₂] },
        try { rw [←htv_range_check_ptr₁] }, try { rw [hl_range_check_ptr₁] }, try { rw [hin_range_check_ptr] },
        try { ring_nf }, try { arith_simps, refl <|> norm_cast }, try { refl } },
      intro rc_h_range_check_ptr, repeat { rw [add_assoc] at rc_h_range_check_ptr },
      have rc_h_range_check_ptr' := range_checked_add_right rc_h_range_check_ptr,
      -- Final Proof
      -- user-provided reduction
      suffices auto_spec: auto_spec_squash_dict mem _ range_check_ptr dict_accesses dict_accesses_end squashed_dict _ _,
      { apply sound_squash_dict, apply auto_spec },
      -- prove the auto generated assertion
      dsimp [auto_spec_squash_dict],
      try { norm_num1 }, try { arith_simps },
      use_only [ptr_diff],
      use_only [a2],
      right,
      use_only [a3],
      use_only [first_key],
      use_only [big_keys],
      use_only [n_accesses, hl_n_accesses],
      try { dsimp }, try { arith_simps },
      left,
      use_only [a10],
      have rc_h_range_check_ptr₁ := range_checked_offset' rc_h_range_check_ptr,
      have rc_h_range_check_ptr₁' := range_checked_add_right rc_h_range_check_ptr₁,
        try { norm_cast at rc_h_range_check_ptr₁' }, try { rw [add_zero] at rc_h_range_check_ptr₁' },
      use_only [range_check_ptr₁, hl_range_check_ptr₁],
      try { dsimp }, try { arith_simps },
      have rc_h_range_check_ptr₂ := range_checked_offset' rc_h_range_check_ptr₁,
      have rc_h_range_check_ptr₂' := range_checked_add_right rc_h_range_check_ptr₂, try { norm_cast at rc_h_range_check_ptr₂' },
      have h_block14' := h_block14 rc_h_range_check_ptr₁',
      try { rw [←hin_range_check_ptr] at h_block14' }, try { rw [←hl_range_check_ptr₁] at h_block14' },
      try { dsimp at h_block14, arith_simps at h_block14' },
      have h_block14 := h_block14',
      use_only [κ_block14],
      use [h_block14],
      try { linarith }
    }
  }
end
