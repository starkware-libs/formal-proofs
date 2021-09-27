/-
The organization of information in the memory.
-/
import memory_aux constraints

noncomputable theory
open_locale classical
open_locale big_operators
open_locale disable_subsingleton_simps

/- the data -/

variables {F : Type*}

variable  {T : ℕ}    -- the number of steps in the execution

variables {pc       inst
           dst_addr dst
           op0_addr op0
           op1_addr op1  : fin T → F}

variables {mem_star : F → option F}

variables {n : ℕ}

variables {a v a' v' p   : fin (n + 1) → F}

variables {embed_inst
           embed_dst
           embed_op0
           embed_op1     : fin T → fin (n + 1)}

variables {embed_mem     : mem_dom mem_star → fin (n + 1)}

variables {alpha z : F}

/- the assumptions and constraints -/

variables [field F] [fintype F]

variable h_continuity :
  ∀ i : fin n, (a' i.succ - a' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0

variable h_single_valued :
  ∀ i : fin n, (v' i.succ - v' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0

variable h_initial : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0)

variable h_cumulative : ∀ i : fin n, (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
                                       (z - (a i.succ + alpha * v i.succ)) * p i.cast_succ

variable h_final : p (fin.last n) * ∏ a : mem_dom mem_star, (z - (a.val + alpha * mem_val a)) =
    z^(fintype.card (mem_dom mem_star))

variable h_embed_pc       : ∀ i, a (embed_inst i) = pc i
variable h_embed_inst     : ∀ i, v (embed_inst i) = inst i
variable h_embed_dst_addr : ∀ i, a (embed_dst i)  = dst_addr i
variable h_embed_dst      : ∀ i, v (embed_dst i)  = dst i
variable h_embed_op0_addr : ∀ i, a (embed_op0 i)  = op0_addr i
variable h_embed_op0      : ∀ i, v (embed_op0 i)  = op0 i
variable h_embed_op1_addr : ∀ i, a (embed_op1 i)  = op1_addr i
variable h_embed_op1      : ∀ i, v (embed_op1 i)  = op1 i

variable h_embed_dom      : ∀ i, a (embed_mem i) = 0
variable h_embed_val      : ∀ i, v (embed_mem i) = 0

variable h_embed_mem_inj       : function.injective embed_mem
variable h_embed_mem_disj_inst : ∀ i j, embed_mem i ≠ embed_inst j
variable h_embed_mem_disj_dst  : ∀ i j, embed_mem i ≠ embed_dst j
variable h_embed_mem_disj_op0  : ∀ i j, embed_mem i ≠ embed_op0 j
variable h_embed_mem_disj_op1  : ∀ i j, embed_mem i ≠ embed_op1 j

/-
The memory.
-/

def mem (a' v' : fin (n + 1) → F) : F → F :=
λ addr, if h : ∃ i, a' i = addr then v' (classical.some h) else 0

/-
Recovering the real a and v arrays from mem_star and the trace version in which
those values have been replaced by (0, 0) pairs.
-/

def real_a (mem_star : F → option F) (a : fin (n + 1) → F)
    (embed_mem : mem_dom mem_star → fin (n + 1)) :
  fin (n + 1) → F :=
λ i, if h : ∃ addr, embed_mem addr = i then (classical.some h).val else a i

def real_v (mem_star : F → option F) (v : fin (n + 1) → F)
    (embed_mem : mem_dom mem_star → fin (n + 1)) :
  fin (n + 1) → F :=
λ i, if h : ∃ addr, embed_mem addr = i then mem_val (classical.some h) else v i

/-
Requires messing around with finite products. Needs the fact that `embed_mem` is injective.
-/

section
include h_embed_mem_inj h_embed_dom h_embed_val

lemma real_prod_eq :
  let ra := real_a mem_star a embed_mem,
      rv := real_v mem_star v embed_mem in
  (∏ i, (z - (ra i + alpha * rv i))) * z^(fintype.card (mem_dom mem_star)) =
    (∏ i, (z - (a i + alpha * v i))) *
      ∏ a : mem_dom mem_star, (z - (a.val + alpha * mem_val a)) :=
begin
  dsimp,
  let s := finset.image embed_mem finset.univ,
  rw [←finset.prod_sdiff (finset.subset_univ s), ←finset.prod_sdiff (finset.subset_univ s),
        mul_right_comm _ _ (z ^ _)],
  congr' 2,
  { apply finset.prod_congr rfl,
    intro i, rw finset.mem_sdiff, rintros ⟨_, nsi⟩,
    simp [-not_exists, finset.mem_image] at nsi,
    rw [real_a, real_v], dsimp, rw [dif_neg nsi, dif_neg nsi] },
  { rw [finset.prod_image (λ x _ y _ h, @h_embed_mem_inj x y h), fintype.card, ←finset.prod_const],
    apply finset.prod_congr rfl,
    intros i _, dsimp,
    rw [h_embed_dom, h_embed_val, zero_add, mul_zero, sub_zero] },
  rw [finset.prod_image (λ x _ y _ h, @h_embed_mem_inj x y h)],
  apply finset.prod_congr rfl,
  intros i _, dsimp,
  have h : ∃ addr, embed_mem addr = embed_mem i := ⟨i, rfl⟩,
  have h' : classical.some h = i := h_embed_mem_inj (classical.some_spec h),
  rw [real_a, real_v], dsimp, rw [dif_pos h, dif_pos h, mem_val],
  congr; exact h'
end
end

/-
Moving from `a`, `v` to `real_a`, `real_v` preserves the pairs we care about.
-/

section
include h_embed_pc h_embed_mem_disj_inst

lemma real_a_embed_inst (i : fin T) : real_a mem_star a embed_mem (embed_inst i) = pc i :=
begin
  rw [real_a], dsimp, rw [dif_neg, h_embed_pc],
  apply not_exists_of_forall_not, intro j,
  apply h_embed_mem_disj_inst
end

end

section
include h_embed_inst h_embed_mem_disj_inst

lemma real_v_embed_inst (i : fin T) : real_v mem_star v embed_mem (embed_inst i) = inst i :=
begin
  rw [real_v], dsimp, rw [dif_neg, h_embed_inst],
  apply not_exists_of_forall_not, intro j,
  apply h_embed_mem_disj_inst
end

end

-- because these are so uniform, we can use the same proofs

lemma real_a_embed_dst (i : fin T) : real_a mem_star a embed_mem (embed_dst i) = dst_addr i :=
real_a_embed_inst h_embed_dst_addr h_embed_mem_disj_dst i

lemma real_v_embed_dst (i : fin T) : real_v mem_star v embed_mem (embed_dst i) = dst i :=
real_v_embed_inst h_embed_dst h_embed_mem_disj_dst i

lemma real_a_embed_op0 (i : fin T) : real_a mem_star a embed_mem (embed_op0 i) = op0_addr i :=
real_a_embed_inst h_embed_op0_addr h_embed_mem_disj_op0 i

lemma real_v_embed_op0 (i : fin T) : real_v mem_star v embed_mem (embed_op0 i) = op0 i :=
real_v_embed_inst h_embed_op0 h_embed_mem_disj_op0 i

lemma real_a_embed_op1 (i : fin T) : real_a mem_star a embed_mem (embed_op1 i) = op1_addr i :=
real_a_embed_inst h_embed_op1_addr h_embed_mem_disj_op1 i

lemma real_v_embed_op1 (i : fin T) : real_v mem_star v embed_mem (embed_op1 i) = op1 i :=
real_v_embed_inst h_embed_op1 h_embed_mem_disj_op1 i

section

variable h_z_ne_zero : z ≠ 0

include h_initial h_cumulative h_final h_embed_mem_inj h_embed_dom h_embed_val h_z_ne_zero

lemma real_permutation_prod_eq :
  let ra := real_a mem_star a embed_mem,
      rv := real_v mem_star v embed_mem in
  (∏ i, (z - (ra i + alpha * rv i))) = (∏ i, (z - (a' i + alpha * v' i))) :=
begin
  let ra := real_a mem_star a embed_mem,
  let rv := real_v mem_star v embed_mem,
  suffices : (∏ i, (z - (ra i + alpha * rv i))) * z^(fintype.card (mem_dom mem_star)) =
               (∏ i, (z - (a' i + alpha * v' i))) * z^(fintype.card (mem_dom mem_star)),
    from mul_right_cancel' (pow_ne_zero _ h_z_ne_zero) this,
  have := real_prod_eq h_embed_dom h_embed_val h_embed_mem_inj ,
  dsimp [-subtype.val_eq_coe] at this, rw this,
  rw [←fin.range_last, ←fin.succ_last, permutation_aux h_initial h_cumulative,
    mul_assoc, h_final]
end

variable hprob₁ : alpha ∉
  bad_set_1 (real_a mem_star a embed_mem) (real_v mem_star v embed_mem) a' v'

variable hprob₂ : z ∉
  bad_set_2 (real_a mem_star a embed_mem) (real_v mem_star v embed_mem) a' v' alpha

lemma real_perm :
  ∀ i, ∃ j, real_v mem_star v embed_mem i = v' j ∧
            real_a mem_star a embed_mem i = a' j :=
let ra := real_a mem_star a embed_mem,
    rv := real_v mem_star v embed_mem in
have h : ∏ (i : fin (n + 1)), (z - (ra i + alpha * rv i)) =
          ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i)) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
      h_z_ne_zero,
permutation hprob₁ hprob₂ h

lemma real_perm' :
  ∀ i, ∃ j, v' i = real_v mem_star v embed_mem j ∧
            a' i = real_a mem_star a embed_mem j :=
let ra := real_a mem_star a embed_mem,
    rv := real_v mem_star v embed_mem in
have h : ∏ (i : fin (n + 1)), (z - (ra i + alpha * rv i)) =
          ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i)) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
      h_z_ne_zero,
permutation' hprob₁ hprob₂ h

variable h_char_lt : n < ring_char F

include h_continuity h_single_valued hprob₁ hprob₂ h_char_lt

lemma real_a_single_valued :
  let ra := real_a mem_star a embed_mem,
      rv := real_v mem_star v embed_mem in
  ∀ i i', ra i = ra i' → rv i = rv i' :=
begin
  dsimp,
  intros i i' aieq,
  let ra := real_a mem_star a embed_mem,
  let rv := real_v mem_star v embed_mem,
  have h : ∏ (i : fin (n + 1)), (z - (ra i + alpha * rv i)) =
             ∏ (i : fin (n + 1)), (z - (a' i + alpha * v' i)) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
      h_z_ne_zero,
  have perm := permutation hprob₁ hprob₂ h,
  rcases perm i with ⟨j, veq, aeq⟩,
  rcases perm i' with ⟨j', veq', aeq'⟩,
  rw [veq, veq'],
  apply a'_single_valued h_continuity h_single_valued h_char_lt,
  rw [←aeq, ←aeq', aieq]
end

lemma mem_unique (i : fin (n + 1)) :
  mem a' v' (real_a mem_star a embed_mem i) = real_v mem_star v embed_mem i :=
begin
  have perm := real_perm h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
    h_z_ne_zero hprob₁ hprob₂,
  rcases perm i with ⟨i', v'eq, a'eq⟩,
  have h : ∃ i', a' i' = real_a mem_star a embed_mem i := ⟨i', a'eq.symm⟩,
  rw [mem], dsimp, rw [dif_pos h],
  rw v'eq,
  apply a'_single_valued h_continuity h_single_valued h_char_lt,
  exact (classical.some_spec h).trans a'eq
end

section
include h_embed_pc h_embed_inst h_embed_mem_disj_inst

theorem mem_pc (i : fin T) : mem a' v' (pc i) = inst i :=
begin
  rw [←@real_a_embed_inst _ T pc mem_star _ a embed_inst embed_mem _ _ h_embed_pc
          h_embed_mem_disj_inst],
  rw [←@real_v_embed_inst _ T inst mem_star _ v embed_inst embed_mem _ _
          h_embed_inst h_embed_mem_disj_inst],
  apply mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom
    h_embed_val h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt
end
end

theorem mem_dst_addr (i : fin T) : mem a' v' (dst_addr i) = dst i :=
mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dst_addr h_embed_dst
  h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_dst h_z_ne_zero hprob₁ hprob₂ h_char_lt i

theorem mem_op0_addr (i : fin T) : mem a' v' (op0_addr i) = op0 i :=
mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_op0_addr h_embed_op0
  h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_op0 h_z_ne_zero hprob₁ hprob₂ h_char_lt i

theorem mem_op1_addr (i : fin T) : mem a' v' (op1_addr i) = op1 i :=
mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_op1_addr h_embed_op1
  h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_op1 h_z_ne_zero hprob₁ hprob₂ h_char_lt i

theorem mem_extends : option.fn_extends (mem a' v') mem_star :=
begin
  intro addr,
  cases h : (mem_star addr) with val; simp only [option.agrees],
  have h' : (option.is_some (mem_star addr) : Prop), by { rw h, simp },
  let aelt : mem_dom mem_star := ⟨addr, h'⟩,
  have h₀ : ∃ i, embed_mem i = embed_mem aelt := ⟨aelt, rfl⟩,
  have h₁ : classical.some h₀ = aelt,
  { apply h_embed_mem_inj, apply classical.some_spec h₀ },
  have h₂ : real_a mem_star a embed_mem (embed_mem aelt) = addr,
  { rw real_a, dsimp, rw [dif_pos h₀, h₁], refl },
  have h₃ : real_v mem_star v embed_mem (embed_mem aelt) = val,
  { rw real_v, dsimp, rw [dif_pos h₀, h₁],
    apply option.some_inj.mp,
    rw [←h, mem_val, option.some_get] },
  rw [←h₂, ←h₃], symmetry,
  dsimp [aelt],
  exact mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom
    h_embed_val h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt (embed_mem ⟨addr, h'⟩)
end

end
