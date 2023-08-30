/-
The organization of information in the memory.
-/
import Verification.Semantics.AirEncoding.MemoryAux
import Verification.Semantics.AirEncoding.Constraints

noncomputable section

open scoped Classical BigOperators

-- the data
variable {F : Type _} {T : ℕ}

-- the number of steps in the execution
variable {rc_len : ℕ}

-- the number of range-checked elements for the range-check builtin
variable {pc inst dst_addr dst op0_addr op0 op1_addr op1 : Fin T → F}

variable {rc_addr rc_val : Fin rc_len → F} {mem_star : F → Option F}

variable {n : ℕ} {a v a' v' p : Fin (n + 1) → F}
  {embed_inst embed_dst embed_op0 embed_op1 : Fin T → Fin (n + 1)}
  {embed_rc : Fin rc_len → Fin (n + 1)}
  {embed_mem : MemDom mem_star → Fin (n + 1)}
  {alpha z : F}

-- the assumptions and constraints
variable [Field F] [Fintype F]

variable
  (h_continuity : ∀ i : Fin n, (a' i.succ - a' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)
  (h_single_valued :
    ∀ i : Fin n, (v' i.succ - v' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0)
  (h_initial : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0))
  (h_cumulative :
    ∀ i : Fin n,
      (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
        (z - (a i.succ + alpha * v i.succ)) * p (Fin.castSucc i))
  (h_final :
    (p (Fin.last n) * ∏ a : MemDom mem_star, (z - (a.val + alpha * memVal a))) =
      z ^ Fintype.card (MemDom mem_star))

variable (h_embed_pc : ∀ i, a (embed_inst i) = pc i)
  (h_embed_inst : ∀ i, v (embed_inst i) = inst i)
  (h_embed_dst_addr : ∀ i, a (embed_dst i) = dst_addr i)
  (h_embed_dst : ∀ i, v (embed_dst i) = dst i)
  (h_embed_op0_addr : ∀ i, a (embed_op0 i) = op0_addr i)
  (h_embed_op0 : ∀ i, v (embed_op0 i) = op0 i)
  (h_embed_op1_addr : ∀ i, a (embed_op1 i) = op1_addr i)
  (h_embed_op1 : ∀ i, v (embed_op1 i) = op1 i)
  (h_embed_rc_addr : ∀ i, a (embed_rc i) = rc_addr i)
  (h_embed_rc_val : ∀ i, v (embed_rc i) = rc_val i)
  (h_embed_dom : ∀ i, a (embed_mem i) = 0)
  (h_embed_val : ∀ i, v (embed_mem i) = 0)
  (h_embed_mem_inj : Function.Injective embed_mem)
  (h_embed_mem_disj_inst : ∀ i j, embed_mem i ≠ embed_inst j)
  (h_embed_mem_disj_dst : ∀ i j, embed_mem i ≠ embed_dst j)
  (h_embed_mem_disj_op0 : ∀ i j, embed_mem i ≠ embed_op0 j)
  (h_embed_mem_disj_op1 : ∀ i j, embed_mem i ≠ embed_op1 j)
  (h_embed_mem_disj_rc : ∀ i j, embed_mem i ≠ embed_rc j)

/- The memory.  -/
def mem (a' v' : Fin (n + 1) → F) : F → F := fun addr =>
  if h : ∃ i, a' i = addr then v' (Classical.choose h) else 0

/-
Recovering the real a and v arrays from mem_star and the trace version in which
those values have been replaced by (0, 0) pairs.
-/
def realA (mem_star : F → Option F) (a : Fin (n + 1) → F)
    (embed_mem : MemDom mem_star → Fin (n + 1)) : Fin (n + 1) → F := fun i =>
  if h : ∃ addr, embed_mem addr = i then (Classical.choose h).val else a i

def realV (mem_star : F → Option F) (v : Fin (n + 1) → F)
    (embed_mem : MemDom mem_star → Fin (n + 1)) : Fin (n + 1) → F := fun i =>
  if h : ∃ addr, embed_mem addr = i then memVal (Classical.choose h) else v i

/- Requires messing around with finite products. Needs the fact that `embed_mem` is injective.  -/
section

theorem real_prod_eq :
  let ra := realA mem_star a embed_mem
  let rv := realV mem_star v embed_mem
  (∏ i, (z - (ra i + alpha * rv i))) * z ^ Fintype.card (MemDom mem_star) =
    (∏ i, (z - (a i + alpha * v i))) * ∏ a : MemDom mem_star, (z - (a.val + alpha * memVal a)) := by
  dsimp
  let s := Finset.image embed_mem Finset.univ
  rw [← Finset.prod_sdiff (Finset.subset_univ s), ← Finset.prod_sdiff (Finset.subset_univ s),
    mul_right_comm _ _ (z ^ _)]
  congr 2
  · apply Finset.prod_congr rfl
    intro i; rw [Finset.mem_sdiff]; rintro ⟨_, nsi⟩
    simp [-not_exists, Finset.mem_image] at nsi
    rw [realA, realV, dif_neg nsi, dif_neg nsi]
  · rw [Finset.prod_image fun x _ y _ h => @h_embed_mem_inj x y h, Fintype.card, ←
      Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i _; dsimp
    rw [h_embed_dom, h_embed_val, zero_add, MulZeroClass.mul_zero, sub_zero]
  rw [Finset.prod_image fun x _ y _ h => @h_embed_mem_inj x y h]
  apply Finset.prod_congr rfl
  intro i _; dsimp
  have h : ∃ addr, embed_mem addr = embed_mem i := ⟨i, rfl⟩
  have h' : Classical.choose h = i := h_embed_mem_inj (Classical.choose_spec h)
  rw [realA, realV, dif_pos h, dif_pos h, memVal]
  congr
end

/- Moving from `a`, `v` to `real_a`, `real_v` preserves the pairs we care about.  -/
section

theorem realA_embed_inst (i : Fin T) : realA mem_star a embed_mem (embed_inst i) = pc i :=
  by
  rw [realA, dif_neg, h_embed_pc]
  apply not_exists_of_forall_not; intro j
  apply h_embed_mem_disj_inst

end

section

theorem realV_embed_inst (i : Fin T) : realV mem_star v embed_mem (embed_inst i) = inst i :=
  by
  rw [realV, dif_neg, h_embed_inst]
  apply not_exists_of_forall_not; intro j
  apply h_embed_mem_disj_inst

end

-- because these are so uniform, we can use the same proofs
theorem realA_embed_dst (i : Fin T) : realA mem_star a embed_mem (embed_dst i) = dst_addr i :=
  realA_embed_inst h_embed_dst_addr h_embed_mem_disj_dst i

theorem realV_embed_dst (i : Fin T) : realV mem_star v embed_mem (embed_dst i) = dst i :=
  realV_embed_inst h_embed_dst h_embed_mem_disj_dst i

theorem realA_embed_op0 (i : Fin T) : realA mem_star a embed_mem (embed_op0 i) = op0_addr i :=
  realA_embed_inst h_embed_op0_addr h_embed_mem_disj_op0 i

theorem realV_embed_op0 (i : Fin T) : realV mem_star v embed_mem (embed_op0 i) = op0 i :=
  realV_embed_inst h_embed_op0 h_embed_mem_disj_op0 i

theorem realA_embed_op1 (i : Fin T) : realA mem_star a embed_mem (embed_op1 i) = op1_addr i :=
  realA_embed_inst h_embed_op1_addr h_embed_mem_disj_op1 i

theorem realV_embed_op1 (i : Fin T) : realV mem_star v embed_mem (embed_op1 i) = op1 i :=
  realV_embed_inst h_embed_op1 h_embed_mem_disj_op1 i

section

theorem realA_embed_rc (i : Fin rc_len) : realA mem_star a embed_mem (embed_rc i) = rc_addr i := by
  rw [realA, dif_neg, h_embed_rc_addr]
  apply not_exists_of_forall_not; intro j
  apply h_embed_mem_disj_rc

end

section

theorem realV_embed_rc (i : Fin rc_len) : realV mem_star v embed_mem (embed_rc i) = rc_val i := by
  rw [realV, dif_neg, h_embed_rc_val]
  apply not_exists_of_forall_not; intro j
  apply h_embed_mem_disj_rc

end

section

variable (h_z_ne_zero : z ≠ 0)

theorem real_permutation_prod_eq :
    let ra := realA mem_star a embed_mem
    let rv := realV mem_star v embed_mem
    (∏ i, (z - (ra i + alpha * rv i))) = (∏ i, (z - (a' i + alpha * v' i))) := by
  let ra := realA mem_star a embed_mem
  let rv := realV mem_star v embed_mem
  suffices :
    (∏ i, (z - (ra i + alpha * rv i))) * z ^ Fintype.card (MemDom mem_star) =
      (∏ i, (z - (a' i + alpha * v' i))) * z ^ Fintype.card (MemDom mem_star)
  exact mul_right_cancel₀ (pow_ne_zero _ h_z_ne_zero) this
  have := @real_prod_eq F mem_star n a v embed_mem alpha z _ _ h_embed_dom h_embed_val h_embed_mem_inj
  dsimp at this; rw [this]
  rw [← Fin.range_last, ← Fin.succ_last, permutation_aux h_initial h_cumulative, mul_assoc, h_final]

variable (hprob₁ : alpha ∉ badSet1 (realA mem_star a embed_mem) (realV mem_star v embed_mem) a' v')
  (hprob₂ : z ∉ badSet2 (realA mem_star a embed_mem) (realV mem_star v embed_mem) a' v' alpha)

theorem real_perm :
    ∀ i, ∃ j, realV mem_star v embed_mem i = v' j ∧ realA mem_star a embed_mem i = a' j :=
  let ra := realA mem_star a embed_mem
  let rv := realV mem_star v embed_mem
  have h :
    (∏ i : Fin (n + 1), (z - (ra i + alpha * rv i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i))) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
      h_z_ne_zero
  permutation hprob₁ hprob₂ h

theorem real_perm' :
    ∀ i, ∃ j, v' i = realV mem_star v embed_mem j ∧ a' i = realA mem_star a embed_mem j :=
  let ra := realA mem_star a embed_mem
  let rv := realV mem_star v embed_mem
  have h :
    (∏ i : Fin (n + 1), (z - (ra i + alpha * rv i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i))) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj
      h_z_ne_zero
  permutation' hprob₁ hprob₂ h

variable (h_char_lt : n < ringChar F)

theorem realA_single_valued :
    let ra := realA mem_star a embed_mem
    let rv := realV mem_star v embed_mem
    ∀ i i', ra i = ra i' → rv i = rv i' := by
  dsimp
  intro i i' aieq
  let ra := realA mem_star a embed_mem
  let rv := realV mem_star v embed_mem
  have h :
    (∏ i : Fin (n + 1), (z - (ra i + alpha * rv i))) = (∏ i : Fin (n + 1), (z - (a' i + alpha * v' i))) :=
    real_permutation_prod_eq h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj h_z_ne_zero
  have perm := permutation hprob₁ hprob₂ h
  rcases perm i with ⟨j, veq, aeq⟩
  rcases perm i' with ⟨j', veq', aeq'⟩
  rw [veq, veq']
  apply a'_single_valued h_continuity h_single_valued h_char_lt
  rw [← aeq, ← aeq', aieq]

theorem mem_unique (i : Fin (n + 1)) :
    mem a' v' (realA mem_star a embed_mem i) = realV mem_star v embed_mem i := by
  have perm :=
    real_perm h_initial h_cumulative h_final h_embed_dom h_embed_val h_embed_mem_inj h_z_ne_zero
      hprob₁ hprob₂
  rcases perm i with ⟨i', v'eq, a'eq⟩
  have h : ∃ i', a' i' = realA mem_star a embed_mem i := ⟨i', a'eq.symm⟩
  rw [mem, dif_pos h]
  rw [v'eq]
  apply a'_single_valued h_continuity h_single_valued h_char_lt
  exact (Classical.choose_spec h).trans a'eq

section

theorem mem_pc (i : Fin T) : mem a' v' (pc i) = inst i := by
  rw [← @realA_embed_inst _ T pc mem_star _ a embed_inst embed_mem _ h_embed_pc h_embed_mem_disj_inst]
  rw [← @realV_embed_inst _ T inst mem_star _ v embed_inst embed_mem _ h_embed_inst h_embed_mem_disj_inst]
  apply mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom h_embed_val
      h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt

end

theorem mem_dst_addr (i : Fin T) : mem a' v' (dst_addr i) = dst i :=
  mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dst_addr h_embed_dst
    h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_dst h_z_ne_zero hprob₁ hprob₂ h_char_lt i

theorem mem_op0_addr (i : Fin T) : mem a' v' (op0_addr i) = op0 i :=
  mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_op0_addr h_embed_op0
    h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_op0 h_z_ne_zero hprob₁ hprob₂ h_char_lt i

theorem mem_op1_addr (i : Fin T) : mem a' v' (op1_addr i) = op1 i :=
  mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_op1_addr h_embed_op1
    h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_op1 h_z_ne_zero hprob₁ hprob₂ h_char_lt i

section

theorem mem_rc_addr (i : Fin rc_len) : mem a' v' (rc_addr i) = rc_val i :=
  by
  rw [← @realA_embed_rc _ _ rc_addr mem_star _ a embed_rc embed_mem _ h_embed_rc_addr h_embed_mem_disj_rc]
  rw [← @realV_embed_inst _ _ rc_val mem_star _ v embed_rc embed_mem _ h_embed_rc_val h_embed_mem_disj_rc]
  apply mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom h_embed_val
      h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt

end

theorem mem_extends : Option.FnExtends (mem a' v') mem_star := by
  intro addr
  cases' h : mem_star addr with val <;> simp only [Option.Agrees]
  have h' : (Option.isSome (mem_star addr) : Prop) := by rw [h]; simp
  let aelt : MemDom mem_star := ⟨addr, h'⟩
  have h₀ : ∃ i, embed_mem i = embed_mem aelt := ⟨aelt, rfl⟩
  have h₁ : Classical.choose h₀ = aelt := by apply h_embed_mem_inj; apply Classical.choose_spec h₀
  have h₂ : realA mem_star a embed_mem (embed_mem aelt) = addr := by
    rw [realA]; dsimp;
    rw [dif_pos h₀, h₁]
  have h₃ : realV mem_star v embed_mem (embed_mem aelt) = val := by
    rw [realV]; dsimp; rw [dif_pos h₀, h₁]
    apply Option.some_inj.mp
    rw [← h, memVal, Option.some_get]
  rw [← h₂, ← h₃]; symm
  dsimp
  exact
    mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom h_embed_val
      h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt (embed_mem ⟨addr, h'⟩)

end