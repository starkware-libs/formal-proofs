/-
  Specifications file for squash_dict_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.math_spec
import starkware.cairo.common.dict_access_spec

open starkware.cairo.common.math
open starkware.cairo.common.dict_access
namespace starkware.cairo.common.squash_dict

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

instance F_inhabited : inhabited F := ⟨0⟩

namespace squash_dict_inner

@[reducible] def φ_LoopLocals.value := 0
@[reducible] def φ_LoopLocals.access_ptr := 1
@[reducible] def φ_LoopLocals.range_check_ptr := 2
@[ext] structure LoopLocals (mem : F → F) :=
  (value : F) (access_ptr : π_DictAccess mem) (range_check_ptr : F)
@[reducible] def LoopLocals.SIZE := 3
@[ext] structure π_LoopLocals (mem : F → F) :=
  (σ_ptr : F) (value : F) (access_ptr : π_DictAccess mem) (range_check_ptr : F)
  (h_value : value = mem (σ_ptr + φ_LoopLocals.value))
  (h_access_ptr : access_ptr = cast_π_DictAccess mem (mem (σ_ptr + φ_LoopLocals.access_ptr)))
  (h_range_check_ptr : range_check_ptr = mem (σ_ptr + φ_LoopLocals.range_check_ptr))
@[reducible] def π_LoopLocals.SIZE := 3
@[reducible] def cast_LoopLocals (mem : F → F) (p : F) : LoopLocals mem := {
  value := mem (p + φ_LoopLocals.value),
  access_ptr := cast_π_DictAccess mem (mem (p + φ_LoopLocals.access_ptr)),
  range_check_ptr := mem (p + φ_LoopLocals.range_check_ptr)
}
@[reducible] def cast_π_LoopLocals (mem : F → F) (p : F) : π_LoopLocals mem := {
  σ_ptr := p,
  value := mem (p + φ_LoopLocals.value),
  access_ptr := cast_π_DictAccess mem (mem (p + φ_LoopLocals.access_ptr)),
  range_check_ptr := mem (p + φ_LoopLocals.range_check_ptr),
  h_value := rfl,
  h_access_ptr := rfl,
  h_range_check_ptr := rfl
}
instance π_LoopLocals_to_F {mem : F → F} : has_coe (π_LoopLocals mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_LoopLocals_ptr {mem : F → F} {x y : π_LoopLocals mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_value, y.h_value, h_p] },
  try { ext }, repeat { rw [x.h_access_ptr, y.h_access_ptr, h_p] },
  try { ext }, repeat { rw [x.h_range_check_ptr, y.h_range_check_ptr, h_p] }
end
lemma eq_LoopLocals_π_cast {mem : F → F} {x y : F} :
  cast_π_LoopLocals mem x = cast_π_LoopLocals mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_LoopLocals_π_ptr_cast {mem : F → F} {x : π_LoopLocals mem} {y : F} :
  x = cast_π_LoopLocals mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_LoopLocals_π_cast {mem : F → F} {x : F} :(↑(cast_π_LoopLocals mem x) : F) = x := rfl
@[reducible] def φ_LoopTemps.index_delta_minus1 := 0
@[reducible] def φ_LoopTemps.index_delta := 1
@[reducible] def φ_LoopTemps.ptr_delta := 2
@[reducible] def φ_LoopTemps.should_continue := 3
@[ext] structure LoopTemps (mem : F → F) :=
  (index_delta_minus1 : F) (index_delta : F) (ptr_delta : F) (should_continue : F)
@[reducible] def LoopTemps.SIZE := 4
@[ext] structure π_LoopTemps (mem : F → F) :=
  (σ_ptr : F) (index_delta_minus1 : F) (index_delta : F) (ptr_delta : F) (should_continue : F)
  (h_index_delta_minus1 : index_delta_minus1 = mem (σ_ptr + φ_LoopTemps.index_delta_minus1))
  (h_index_delta : index_delta = mem (σ_ptr + φ_LoopTemps.index_delta))
  (h_ptr_delta : ptr_delta = mem (σ_ptr + φ_LoopTemps.ptr_delta))
  (h_should_continue : should_continue = mem (σ_ptr + φ_LoopTemps.should_continue))
@[reducible] def π_LoopTemps.SIZE := 4
@[reducible] def cast_LoopTemps (mem : F → F) (p : F) : LoopTemps mem := {
  index_delta_minus1 := mem (p + φ_LoopTemps.index_delta_minus1),
  index_delta := mem (p + φ_LoopTemps.index_delta),
  ptr_delta := mem (p + φ_LoopTemps.ptr_delta),
  should_continue := mem (p + φ_LoopTemps.should_continue)
}
@[reducible] def cast_π_LoopTemps (mem : F → F) (p : F) : π_LoopTemps mem := {
  σ_ptr := p,
  index_delta_minus1 := mem (p + φ_LoopTemps.index_delta_minus1),
  index_delta := mem (p + φ_LoopTemps.index_delta),
  ptr_delta := mem (p + φ_LoopTemps.ptr_delta),
  should_continue := mem (p + φ_LoopTemps.should_continue),
  h_index_delta_minus1 := rfl,
  h_index_delta := rfl,
  h_ptr_delta := rfl,
  h_should_continue := rfl
}
instance π_LoopTemps_to_F {mem : F → F} : has_coe (π_LoopTemps mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_LoopTemps_ptr {mem : F → F} {x y : π_LoopTemps mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_index_delta_minus1, y.h_index_delta_minus1, h_p] },
  try { ext }, repeat { rw [x.h_index_delta, y.h_index_delta, h_p] },
  try { ext }, repeat { rw [x.h_ptr_delta, y.h_ptr_delta, h_p] },
  try { ext }, repeat { rw [x.h_should_continue, y.h_should_continue, h_p] }
end
lemma eq_LoopTemps_π_cast {mem : F → F} {x y : F} :
  cast_π_LoopTemps mem x = cast_π_LoopTemps mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_LoopTemps_π_ptr_cast {mem : F → F} {x : π_LoopTemps mem} {y : F} :
  x = cast_π_LoopTemps mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_LoopTemps_π_cast {mem : F → F} {x : F} :(↑(cast_π_LoopTemps mem x) : F) = x := rfl

end squash_dict_inner

-- Auxiliary list lemmas

lemma list_append_head { s t : list F } (h : s ≠ list.nil) :
  (s ++ t).head = s.head :=
begin
  rw [←(list.cons_head_tail h)], dsimp, refl,
end

lemma list_map_head {α : Type*} [inhabited α] {s : list F} (f : F → α) (h : s ≠ list.nil) :
  (list.map f s).head = f s.head :=
begin
  rw [←(list.cons_head_tail h)], dsimp, refl,
end

lemma list_tail_last {α : Type*} [inhabited α] {s : list α} (h_nnil : s ≠ list.nil) (h_tail_nnil : s.tail ≠ list.nil) :
  s.tail.last h_tail_nnil = s.last h_nnil :=
begin
  rw [←(@list.last_cons α s.head s.tail h_tail_nnil)], simp only [list.cons_head_tail h_nnil],
end

lemma list_map_append_head {α : Type*} [inhabited α] {s t : list F} {f : F → α} (h : s ≠ list.nil) :
  (list.map f (s ++ t)).head = f s.head :=
begin
  rw [list.map_append, ←(list.cons_head_tail h)], dsimp, refl,
end

lemma mem_of_mem_sublist {α : Type*} [inhabited α] {s t : list α} {a : α} (h_mem : a ∈ s) (h_sub : s <+ t):
  a ∈ t :=
begin
  rw [←list.singleton_sublist], apply list.sublist.trans _ h_sub, rwa [list.singleton_sublist],
end

lemma mem_of_head_sublist {α : Type*} [inhabited α] {s t : list α} (h_s_nnil : s ≠ list.nil) (h_sub : s <+ t):
  s.head ∈ t :=
begin
  apply mem_of_mem_sublist _ h_sub, apply list.head_mem_self h_s_nnil,
end

def pairwise_disjoint {α : Type*} (ls : list (list α)) : Prop := ls.pairwise list.disjoint

lemma length_map_filter_neg_filter {α : Type*} (p : list α → Prop) [decidable_pred p] (ls : list (list α)) :
  ((ls.filter p).map (λ l : list α, l.length)).sum + ((ls.filter (λ (l : list α), ¬p l)).map (λ l : list α, l.length)).sum =
    (ls.map (λ l : list α, l.length)).sum :=
begin
  induction ls with a lt ih,
  { simp only [list.filter_nil, list.map_nil, list.sum_nil],  },
  rw [list.filter, list.filter],
  rw [ite_not],
  cases em (p a),
  { rw [(ne.ite_eq_left_iff (list.cons_ne_self a (list.filter p lt))).mpr h],
    rw [(ne.ite_eq_left_iff (list.cons_ne_self a (list.filter (λ (l : list α), ¬p l) lt)).symm).mpr h],
    simp only [list.map_cons, list.sum_cons], rw [add_assoc, ih], },
  rw [(ne.ite_eq_right_iff (list.cons_ne_self a (list.filter p lt))).mpr h],
  rw [(ne.ite_eq_right_iff (list.cons_ne_self a (list.filter (λ (l : list α), ¬p l) lt)).symm).mpr h],
  simp only [list.map_cons, list.sum_cons],
  rw [←add_assoc, add_comm _ a.length, add_assoc, ih],
end

lemma disjoint_sublists_mem_filter {α : Type*} [decidable_eq α] (lb : list α) (ls : list (list α))
    (h_disjoint : pairwise_disjoint ls)
    (h_sub : ∀ s ∈ ls, s <+ lb) :
  ∀ a : α, ls.filter (λ l : list α, a ∈ l) = list.nil ∨ ∃ la ∈ ls, ls.filter (λ l : list α, a ∈ l) = [la] :=
begin
  intro a,
  generalize' h_f : ls.filter (λ l : list α, a ∈ l) = fl,
  cases fl with hd tl,
  { left, refl },
  right, use [hd],
  split, { apply @list.mem_of_mem_filter _ (λ (l : list α), a ∈ l), rw [h_f], apply list.mem_cons_self, },
  have h_hd : a ∈ hd,
  { apply @list.of_mem_filter _ (λ (l : list α), a ∈ l) _ _ ls, rw [h_f], apply list.mem_cons_self },
  have h_tl : ∀ l ∈ tl, a ∈ l,
  { intros l h_l, apply @list.of_mem_filter _ (λ (l : list α), a ∈ l) _ _ ls, rw [h_f], apply list.mem_cons_of_mem _ h_l },
  have h_not_tl: ∀ l ∈ tl, a ∉ l,
  { intros l h_l,
    suffices h_disjoint_hd_l : list.disjoint hd l, { apply h_disjoint_hd_l h_hd, },
    have h_f_disjoint := list.pairwise.filter (λ (l : list α), a ∈ l) h_disjoint,
    rw [h_f, list.pairwise_cons] at h_f_disjoint, apply h_f_disjoint.1 l h_l, },
  suffices h_tl_nil : tl = list.nil, { rw [h_tl_nil], },
  by_contradiction h_nnil,
  rcases list.exists_mem_of_ne_nil _ h_nnil with ⟨l, h_l⟩,
  exact h_not_tl l h_l (h_tl l h_l),
end

lemma list_symmetric_disjoint {α : Type*} : symmetric (list.disjoint : list α → list α → Prop) :=
begin
  intros l₁ l₂ h_d, apply list.disjoint.symm h_d,
end

lemma sublist_of_sublist_cons {α : Type*} { a b : α } { l₁ l₂ : list α } :
  a :: l₁ <+ b :: l₂ → l₁ <+ l₂ :=
begin
  intro h, cases h with _ _ _ h_cons _ _ _ h_cons2,
  apply list.sublist_of_cons_sublist h_cons, assumption,
end

lemma sublist_of_sublist_not_head {α : Type*} { a : α } { l₁ l₂ : list α } :
  l₁ <+ a :: l₂ → a ∉ l₁ → l₁ <+ l₂ :=
begin
  intros h_sub h_nin, cases h_sub with _ _ _ h_cons _ _ _ h_cons2,
  assumption, exfalso, exact h_nin (list.mem_cons_self _ _)
end

lemma disjoint_sublists_length {α : Type*} [decidable_eq α] {lb : list α} {ls : list (list α)}
    (h_disjoint : pairwise_disjoint ls)
    (h_sub : ∀ s ∈ ls, s <+ lb) :
  (ls.map (λ l : list α, l.length)).sum ≤ lb.length :=
begin
  revert ls h_disjoint h_sub,
  induction lb with b lt ih,
  { intros ls h_disjoint h_sub, rw [list.length], apply le_of_eq, apply list.sum_eq_zero,
    intros x h_x, rw list.mem_map at h_x, rcases h_x with ⟨l, h_l, h_eq⟩,
    rw [←h_eq, list.length_eq_zero], apply list.eq_nil_of_sublist_nil (h_sub l h_l), },
  intros ls h_disjoint h_sub,
  rw [←(length_map_filter_neg_filter (λ l : list α, b ∈ l) ls)],
  cases disjoint_sublists_mem_filter (b::lt) ls h_disjoint h_sub b with h_nil h_singleton,
  { rw [h_nil, list.map_nil, list.sum_nil, nat.zero_add, list.length_cons],
    apply le_of_lt (lt_of_le_of_lt _ (nat.lt_succ_self _)),
    apply @ih (list.filter (λ (l : list α), b ∉ l) ls) (list.pairwise.filter (λ (l : list α), b ∉ l) h_disjoint),
    intros s h_s, rw [list.mem_filter] at h_s,
    cases (h_sub s h_s.1),
    assumption, exfalso, exact h_s.2 (list.mem_cons_self _ _), },
  rcases h_singleton with ⟨la, h_la, h_singleton⟩,
  rw h_singleton,
  have h_b_mem_la : b ∈ la,
  { apply @list.of_mem_filter _ (λ (l : list α), b ∈ l) _ _ ls, rw h_singleton, apply list.mem_singleton_self },
  have h_la_disjoint : ∀ nb ∈ list.filter (λ (l : list α), ¬(λ (l : list α), b ∈ l) l) ls, la.disjoint nb,
  { intros nb h_nb, apply list.pairwise.forall list_symmetric_disjoint h_disjoint h_la (list.mem_of_mem_filter h_nb),
    intro h_eq, rw h_eq at h_b_mem_la, exact list.of_mem_filter h_nb h_b_mem_la },
  cases la,
  { exfalso, apply list.not_mem_nil b, apply h_b_mem_la, },
  rw [list.length_cons, list.map_singleton, list.length_cons, list.sum_singleton],
  rw [add_assoc, add_comm 1 _, ←add_assoc], apply nat.succ_le_succ,
  rw [←list.sum_cons, ←list.map_cons],
  apply @ih (la_tl :: (list.filter (λ (l : list α), b ∉ l) ls)),
  { rw [pairwise_disjoint, list.pairwise_cons], split,
    { intros a' h_a', apply @list.disjoint_of_disjoint_cons_left _ la_hd, apply h_la_disjoint a' h_a', },
    apply list.pairwise.filter (λ (l : list α), b ∉ l) h_disjoint, },
  intros s h_s, rw list.mem_cons_eq at h_s,
  cases h_s,
  { rw h_s, apply sublist_of_sublist_cons (h_sub _ h_la), },
  rw list.mem_filter at h_s, apply sublist_of_sublist_not_head (h_sub s h_s.1) h_s.2,
end

lemma disjoint_sublists_mem {α : Type*} [decidable_eq α] {l : list α} {ls : list (list α)}
    (h_disjoint : pairwise_disjoint ls)
    (h_sub : ∀ s ∈ ls, s <+ l)
    (len_eq : (ls.map (λ l : list α, l.length)).sum = l.length) :
  ∀ x ∈ l, ∃ s ∈ ls, x ∈ s :=
begin
  intros x h_x,
  by_contradiction h_not_mem,
  have h_c : ∀ s, s ∈ ls → x ∉ s, { intros s h_s h_x_mem, exact h_not_mem ⟨s, h_s, h_x_mem⟩, },
  rcases list.mem_split h_x with ⟨l₁, l₂, h_split⟩,
  have h_s : ∀ s ∈ ls, s <+ l₁ ++ l₂,
  { intros s h_s, rw [h_split] at h_sub, cases list.sublist_or_mem_of_sublist (h_sub s h_s),
    assumption, exfalso, exact h_c s h_s h, },
  have h_len_le := disjoint_sublists_length h_disjoint h_s,
  rw [len_eq] at h_len_le,
  apply @not_le_of_gt _ _ l.length (l₁++l₂).length _ h_len_le,
  rw [h_split, list.length_append, list.length_append, list.length_cons],
  rw [←add_assoc], apply nat.lt_succ_self,
end

lemma sublist_eq_of_length {α : Type*} {l₁ l₂ : list α} : l₁ <+ l₂ → list.length l₁ = list.length l₂ → l₁ = l₂ :=
begin
  intros h_sub h_len,
  induction h_sub with _ _ _ l₁_sub _ _ _ a, constructor,
  { rw [list.length_cons, nat.add_one] at h_len,
    exfalso, apply (@nat.not_succ_le_self h_sub_l₂.length), rw [←h_len],
    apply list.length_le_of_sublist l₁_sub, },
  rw list.cons_inj, apply h_sub_ih, apply nat.succ_inj'.mp,
  rw [list.length_cons, list.length_cons] at h_len,
  apply h_len,
end

-- Structures

-- Maps a pointer and a length into a list of data access pointer structures.
def π_array_to_list (mem : F → F) : F → ℕ → list (π_DictAccess mem)
| _ 0 := []
| array (n + 1) := (cast_π_DictAccess mem array) :: π_array_to_list (array + DictAccess.SIZE) n

lemma π_array_to_list_length {mem : F → F} {x : F} {n : ℕ} :
  (π_array_to_list mem x n).length = n :=
begin
  revert x,
  induction n with n ih, { intro x, rw [π_array_to_list], refl },
  intro x, rw [π_array_to_list, list.length_cons, @ih (x + ↑DictAccess.SIZE)],
end

lemma π_array_to_list_nil {mem : F → F} {x : F} :
  (π_array_to_list mem x 0) = list.nil :=
begin
  rw [←list.length_eq_zero, π_array_to_list_length],
end

def key_list {mem : F → F} (l : list (π_DictAccess mem)) : list F :=
  l.map (λ e : π_DictAccess mem, e.key)

def valid_access {mem : F → F} (dict_accesses : list (π_DictAccess mem)) (key : F) : Prop :=
  dict_accesses.all₂ (λ e, e.key = key) ∧
  dict_accesses.chain' (λ e₁ e₂, e₁.new_value = e₂.prev_value)

instance π_DictAccess_inhabited {mem : F → F} : inhabited (π_DictAccess mem) := ⟨cast_π_DictAccess mem 0⟩

def is_squashed {mem : F → F} [inhabited (π_DictAccess mem)] (l : list (π_DictAccess mem)) (squash : π_DictAccess mem) : Prop :=
  ∃ (h : l ≠ list.nil),
    l.head.key = squash.key ∧ l.head.prev_value = squash.prev_value ∧ (l.last h).new_value = squash.new_value ∧
    valid_access l squash.key

lemma key_of_valid_squashed {mem : F → F} [inhabited (π_DictAccess mem)] (key : F) (l : list (π_DictAccess mem)) (squash : π_DictAccess mem)
    (h_valid: valid_access l key)
    (h_squashed: is_squashed l squash) :
  key = squash.key :=
begin
  rcases h_squashed with ⟨l_nnil, h_head_key, _⟩,
  rw [←h_head_key], symmetry,
  apply (list.all₂_iff_forall.mp h_valid.1) l.head (list.head_mem_self l_nnil),
end

def sorted_keys {mem : F → F} (l : list (π_DictAccess mem)) : Prop :=
  l.length ≤ 1 ∨
  (∃ keys_n : list ℕ,
      keys_n.all₂ (λ n, n < PRIME) ∧
      keys_n.sorted (<) ∧
      keys_n.map (λ n, ↑n) = key_list l)

lemma sorted_keys_cons {mem : F → F} {key : F} {m : ℕ} (s : F)
    (h_key : key = (cast_π_DictAccess mem s).key)
    (h_key_lt: ∃ (k₁ k₂ : ℕ), k₁ < PRIME ∧ k₂ < PRIME ∧ key = ↑k₁ ∧ (cast_π_DictAccess mem (s + ↑π_DictAccess.SIZE)).key = ↑k₂ ∧ k₁ < k₂)
    (h_tail_sorted: sorted_keys (π_array_to_list mem (s + ↑π_DictAccess.SIZE) m)) :
  sorted_keys (π_array_to_list mem s (m + 1)) :=
begin
  rcases h_key_lt with ⟨k₁, k₂, k₁_lt, k₂_lt, eq_k₁, eq_k₂, k_lt⟩,
  cases m,
  { left, rw [π_array_to_list_length], },
  cases m,
  { simp only [π_array_to_list], right, use [[k₁, k₂]],
    split, { rw [list.all₂_cons], use [k₁_lt], rw [list.all₂_cons], use [k₂_lt], },
    split, { rw [list.sorted_cons], split, { intros b b_mem, rwa [list.mem_singleton.mp b_mem], }, apply list.sorted_singleton },
    rw [key_list], rw [list.map_cons, list.map_singleton, list.map_cons, list.map_singleton, ←h_key, eq_k₁, eq_k₂], },
  rw [π_array_to_list], right,
  cases h_tail_sorted,
  { exfalso, rw [π_array_to_list_length] at h_tail_sorted, exact nat.not_succ_le_zero _ (nat.le_of_succ_le_succ h_tail_sorted), },
  rcases h_tail_sorted with ⟨keys_m, keys_m_all, keys_m_sorted, keys_m_map⟩,
  have keys_m_len : keys_m.length = m.succ.succ,
  { rw [←list.length_map (λ (n : ℕ), ↑n), keys_m_map], rw [key_list, list.length_map, π_array_to_list_length], },
  have keys_m_nnil : keys_m ≠ list.nil, { rw [←list.length_pos_iff_ne_nil, keys_m_len], apply nat.zero_lt_succ },
  have keys_m_head_cast : (↑keys_m.head : F) = ↑k₂,
  { have h : (↑k₂ : F) = (list.map (λ (n : ℕ), ↑n) keys_m).head,
    { rw ←eq_k₂, rw [keys_m_map], rw [key_list], rw [π_array_to_list, list.map_cons, list.head_cons], },
    rw [h, ←(list.cons_head_tail keys_m_nnil), list.head_cons, list.map_cons, list.head_cons], },
  have keys_m_head : keys_m.head = k₂,
  { apply PRIME.nat_coe_field_inj _ k₂_lt keys_m_head_cast,
    apply list.all₂_iff_forall.mp keys_m_all keys_m.head (list.head_mem_self keys_m_nnil), },
  use [k₁::keys_m],
  split, { rw [list.all₂_cons], use [k₁_lt, keys_m_all] },
  split,
  { rw [list.sorted_cons], split,
    { rw [←(list.cons_head_tail keys_m_nnil)], rw [←(list.cons_head_tail keys_m_nnil)] at keys_m_sorted,
      intros b b_mem, apply lt_of_lt_of_le k_lt, rw [←keys_m_head],
      cases (list.mem_cons_iff _ _ _).mp b_mem with b_head b_tail, { rw [b_head] },
      apply le_of_lt, apply list.rel_of_sorted_cons keys_m_sorted b b_tail, },
    exact keys_m_sorted, },
  rw [key_list], simp only [list.map_cons, list.map_cons],
  split, { rw [←eq_k₁, h_key], }, apply keys_m_map,
end

lemma sort_keys_tail {mem : F → F} {a : π_DictAccess mem} {l : list (π_DictAccess mem)} (h : sorted_keys (a::l)) :
  sorted_keys l :=
begin
  cases h,
  { left, apply le_trans _ h, rw [list.length_cons], apply le_of_lt (nat.lt_succ_self _), },
  right,
  rcases h with ⟨keys, h_all_lt, h_sorted, h_keys_eq⟩,
  cases keys,
  { exfalso, rw [list.map_nil, key_list] at h_keys_eq, apply list.cons_ne_nil a l, apply list.map_eq_nil.mp h_keys_eq.symm, },
  use [keys_tl, ((list.all₂_cons _ _ _).mp h_all_lt).2, (list.sorted_cons.mp h_sorted).2],
  rw [list.map_cons, key_list, list.map_cons] at h_keys_eq, apply list.tail_eq_of_cons_eq h_keys_eq,
end

lemma sort_keys_head_ne_tail {mem : F → F} {a : π_DictAccess mem} {l : list (π_DictAccess mem)} {i : ℕ}
    (h_i_lt : i < l.length)
    (h_sorted : sorted_keys (a::l)) :
  a.key ≠ (l.nth_le i h_i_lt).key :=
begin
  cases h_sorted,
  { exfalso, apply not_le_of_gt _ h_sorted,  rw [list.length_cons], apply nat.succ_lt_succ,
    apply lt_of_le_of_lt (nat.zero_le _) h_i_lt, },
  rcases h_sorted with ⟨keys_n, keys_n_lt, keys_n_sorted, keys_n_eq⟩,
  cases keys_n,
  { exfalso, rw [list.map_nil, key_list] at keys_n_eq, apply list.cons_ne_nil a l, apply list.map_eq_nil.mp keys_n_eq.symm, },
  rw [list.map_cons, key_list, list.map_cons] at keys_n_eq,
  rw [←list.head_eq_of_cons_eq keys_n_eq],
  have h_i_lt_key_map_length : i < (list.map (λ (e : π_DictAccess mem), e.key) l).length,
  { rwa [list.length_map (λ (e : π_DictAccess mem), e.key) l] },
  have keys_n_tl_eq_l := (list.tail_eq_of_cons_eq keys_n_eq).symm,
  have h_i_lt_keys_n_length : i < keys_n_tl.length,
  { rwa [←(list.length_map (λ (n : ℕ), (↑n : F)) keys_n_tl), ←keys_n_tl_eq_l], },
  have h_ith_key_n := list.nth_le_of_eq keys_n_tl_eq_l h_i_lt_key_map_length,
  rw [list.nth_le_map _ _ h_i_lt] at h_ith_key_n,
  rw [h_ith_key_n, list.nth_le_map _ _ h_i_lt_keys_n_length],
  have h_keys_n_hd_lt : keys_n_hd < PRIME, { exact ((list.all₂_cons _ _ _).mp keys_n_lt).1, },
  have h_keys_n_ith_lt : keys_n_tl.nth_le i h_i_lt_keys_n_length < PRIME,
  { apply (list.all₂_iff_forall.mp ((list.all₂_cons _ _ _).mp keys_n_lt).2) (keys_n_tl.nth_le i h_i_lt_keys_n_length),
    apply list.nth_le_mem, },
  intro h_eq,
  have h_key_lt := (list.sorted_cons.mp keys_n_sorted).1 (keys_n_tl.nth_le i h_i_lt_keys_n_length) (list.nth_le_mem _ _ _),
  apply ne_of_lt h_key_lt,
  apply PRIME.nat_coe_field_inj h_keys_n_hd_lt h_keys_n_ith_lt h_eq,
end

lemma squashed_seq_disjoint {mem : F → F} {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_sorted : sorted_keys squashed)
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed) :
  pairwise_disjoint seqs :=
begin
  revert squashed h_sorted h_squashed,
  induction seqs with as ls ih, { intros _ _ _ , exact list.pairwise.nil, },
  intros squashed h_sorted h_squashed,
  cases squashed,
  { exfalso, have h := list.forall₂.length_eq h_squashed, dsimp [list.length] at h, apply nat.succ_ne_zero _ h, },
  rcases list.forall₂_cons.mp h_squashed with ⟨as_squashed, ls_squashed⟩,
  rw [pairwise_disjoint], rw list.pairwise_cons,
  split, {
    intros ld h_ld x h_x h_x_ld,
    rcases as_squashed with ⟨as_nnil, as_key_eq, _, _, as_valid_key, _⟩,
    rw list.all₂_iff_forall at as_valid_key,
    rcases list.mem_iff_nth_le.mp h_ld with ⟨i, h_i, h_ith_ld⟩,
    have h_i_lt_tl : i < squashed_tl.length, { rwa [←(list.forall₂.length_eq ls_squashed)], },
    rcases list.forall₂.nth_le ls_squashed h_i h_i_lt_tl with ⟨li_nnil, li_key_eq, _, _, li_valid_key, _⟩,
    rw [list.all₂_iff_forall, h_ith_ld] at li_valid_key,
    have h_x_key_eq := li_valid_key x h_x_ld,
    rw [as_valid_key x h_x] at h_x_key_eq,
    apply sort_keys_head_ne_tail h_i_lt_tl h_sorted h_x_key_eq, },
  exact ih (sort_keys_tail h_sorted) ls_squashed,
end

lemma squashed_seq_mem_key {mem : F → F} {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed) :
  ∀ (x : π_DictAccess mem) (seq : list (π_DictAccess mem)),
    x ∈ seq → seq ∈ seqs →
      ∃ (squash : π_DictAccess mem), squash ∈ squashed ∧ squash.key = x.key :=
begin
  intros x seq x_mem seq_mem,
  rcases list.mem_iff_nth_le.mp seq_mem with ⟨n, h_n_lt, h_n_eq⟩,
  rw ←h_n_eq at x_mem,
  have h_n_lt_squashed_len : n < squashed.length, { rwa [←(list.forall₂.length_eq h_squashed)], },
  rcases list.forall₂.nth_le h_squashed h_n_lt h_n_lt_squashed_len with ⟨_, h_key_eq, _, _, h_valid_key, _⟩,
  use [squashed.nth_le n h_n_lt_squashed_len, list.nth_le_mem _ _ _],
  exact (list.all₂_iff_forall.mp h_valid_key x x_mem).symm,
end

lemma squashed_key_filter_disjoint {mem : F → F} {accesses : list (π_DictAccess mem)} {squashed : list (π_DictAccess mem)}
    (h_sorted : sorted_keys squashed) :
  pairwise_disjoint (squashed.map (λ s, (accesses.filter (λ e : π_DictAccess mem, e.key = s.key)))) :=
begin
   revert h_sorted,
  induction squashed with as ls ih, { intros _ , exact list.pairwise.nil, },
  intros h_sorted,
  rw [pairwise_disjoint, list.map_cons, list.pairwise_cons],
  split,
  { intros ft ft_mem x h_x h_x_ft,
    rw [list.mem_filter] at h_x, rw [list.mem_map] at ft_mem,
    rcases ft_mem with ⟨sq, sq_mem, ft_eq⟩,
    rcases list.mem_iff_nth_le.mp sq_mem with ⟨i, h_i, h_ith_ls⟩,
    apply sort_keys_head_ne_tail h_i h_sorted,
    rw [h_ith_ls, ←h_x.2], rw [←ft_eq] at h_x_ft,
    apply (list.mem_filter.mp h_x_ft).2, },
  exact ih (sort_keys_tail h_sorted),
end

lemma squashed_seq_sublist_filtered {mem : F → F} {accesses : list (π_DictAccess mem)} {squash : π_DictAccess mem} {seq : list (π_DictAccess mem)}
    (h_subseq : seq <+ accesses)
    (h_squashed : is_squashed seq squash) :
  seq <+ accesses.filter (λ e : π_DictAccess mem, e.key = squash.key) :=
begin
  have h : seq.filter (λ e : π_DictAccess mem, e.key = squash.key) = seq,
  { apply list.filter_eq_self.mpr, intros a h_a,
    rcases h_squashed with ⟨_, _, _, _, h_valid_key, _⟩,
    rw [list.all₂_iff_forall] at h_valid_key, apply h_valid_key a h_a, },
  rw ←h, apply list.sublist.filter _ h_subseq,
end

lemma squashed_sublists_of_filtered {mem : F → F} {accesses : list (π_DictAccess mem)}
    {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_subseq : seqs.all₂ (λ seq, seq <+ accesses))
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed) :
  list.forall₂ (λ seq (squash : π_DictAccess mem),
    seq <+ accesses.filter (λ e : π_DictAccess mem, e.key = squash.key)) seqs squashed :=
begin
  induction h_squashed with _ _ _ _ h_squashed_hd, constructor,
  rw list.forall₂_cons, split,
  { apply squashed_seq_sublist_filtered ((list.all₂_cons _ _ _).mp h_subseq).1 h_squashed_hd, },
  apply h_squashed_ih ((list.all₂_cons _ _ _).mp h_subseq).2,
end

lemma squashed_sublists_of_filtered_eq_len {mem : F → F} {accesses : list (π_DictAccess mem)}
      {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_sorted : sorted_keys squashed)
    (h_subseq : seqs.all₂ (λ seq, seq <+ accesses))
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed)
    (h_sum_len : (seqs.map (λ seq : list (π_DictAccess mem), seq.length)).sum = accesses.length) :
  list.forall₂ (λ (seq : list (π_DictAccess mem)) (squash : π_DictAccess mem),
    seq.length = (accesses.filter (λ e : π_DictAccess mem, e.key = squash.key)).length) seqs squashed :=
begin
  -- Part 1: the sum of lengths of the filtered sequences is no smaller that the sum of lengths of the squashed sequences
  have h_len_eq := list.forall₂.length_eq h_squashed,
  let f := (λ x : list (π_DictAccess mem) × (π_DictAccess mem), x.fst.length),
  have h_f_sum : ((seqs.zip squashed).map f).sum = accesses.length,
  { rw [←(list.map_map (λ y : list (π_DictAccess mem), y.length) (λ x : list (π_DictAccess mem) × (π_DictAccess mem), x.fst) _)],
    rw [←list.unzip_left, list.unzip_zip_left (le_of_eq h_len_eq)], apply h_sum_len, },
  let g := (λ x : list (π_DictAccess mem) × (π_DictAccess mem),
    (accesses.filter (λ e : π_DictAccess mem, e.key = x.snd.key)).length),
  have h_g_sum : ((seqs.zip squashed).map g).sum ≤ accesses.length,
  { rw [←(list.map_map (λ y : π_DictAccess mem, (accesses.filter (λ e : π_DictAccess mem, e.key = y.key)).length) (λ x : list (π_DictAccess mem) × (π_DictAccess mem), x.snd) _)],
    rw [←list.unzip_right, list.unzip_zip_right (le_of_eq h_len_eq.symm)],
    rw [←list.map_map], apply disjoint_sublists_length,
    apply squashed_key_filter_disjoint h_sorted,
    intros s s_h, rw list.mem_map at s_h,
    rcases s_h with ⟨b, _, h_b⟩, rw ←h_b, apply list.filter_sublist, },
  have h_g_sum_le_f_sum : ((seqs.zip squashed).map g).sum ≤ ((seqs.zip squashed).map f).sum, { rwa h_f_sum, },

  -- Part 2 : the length of each squashed sequence is smaller than that of the corresponding filtered sequence.
  have h_forall_le_len : list.forall₂ (λ (seq : list (π_DictAccess mem)) (squash : π_DictAccess mem),
    seq.length ≤ (accesses.filter (λ e : π_DictAccess mem, e.key = squash.key)).length) seqs squashed,
  { apply list.forall₂.imp _ (squashed_sublists_of_filtered h_subseq h_squashed), intros a b h_sub, apply list.length_le_of_sublist h_sub, },
  have h_forall_le_len_zip := prod.forall'.mpr (list.forall₂_iff_zip.mp h_forall_le_len).2,
  simp only [prod.mk.eta] at h_forall_le_len_zip,

  -- Use the previous two parts to prove the lemma.
  rw [list.forall₂_iff_zip], use [list.forall₂.length_eq h_squashed], rw [←prod.forall'], simp only [prod.mk.eta],
  by_contradiction h_not_len_eq,
  apply (lt_self_iff_false ((seqs.zip squashed).map g).sum).mp,
  rcases not_forall.mp h_not_len_eq with ⟨x, h_not_len_eq⟩, rw not_imp at h_not_len_eq,
  have h_x_lt := ne.lt_of_le h_not_len_eq.2 (h_forall_le_len_zip x h_not_len_eq.1),
  have h_f_sum_lt_g_sum := list.sum_lt_sum _ _ h_forall_le_len_zip ⟨x, h_not_len_eq.1, h_x_lt⟩,
  apply lt_of_le_of_lt h_g_sum_le_f_sum h_f_sum_lt_g_sum,
end

lemma squashed_sublists_of_filtered_eq {mem : F → F} {accesses : list (π_DictAccess mem)}
      {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_sorted : sorted_keys squashed)
    (h_subseq : seqs.all₂ (λ seq, seq <+ accesses))
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed)
    (h_sum_len : (seqs.map (λ seq : list (π_DictAccess mem), seq.length)).sum = accesses.length) :
  list.forall₂ (λ (seq : list (π_DictAccess mem)) (squash : π_DictAccess mem),
    seq = (accesses.filter (λ e : π_DictAccess mem, e.key = squash.key))) seqs squashed :=
begin
  have h_sub_zip := prod.forall'.mpr (list.forall₂_iff_zip.mp (squashed_sublists_of_filtered h_subseq h_squashed)).2,
  have h_len_zip := prod.forall'.mpr
    (list.forall₂_iff_zip.mp
      (squashed_sublists_of_filtered_eq_len h_sorted h_subseq h_squashed h_sum_len)).2,
  rw list.forall₂_iff_zip, use [list.forall₂.length_eq h_squashed],
  rw [←prod.forall'],
  intros x h_x, apply sublist_eq_of_length,
  apply h_sub_zip x h_x, apply h_len_zip x h_x,
end

lemma filtered_squashed {mem : F → F} {accesses : list (π_DictAccess mem)}
      {squashed : list (π_DictAccess mem)} {seqs : list (list (π_DictAccess mem))}
    (h_sorted : sorted_keys squashed)
    (h_subseq : seqs.all₂ (λ seq, seq <+ accesses))
    (h_squashed : list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed)
    (h_sum_len : (seqs.map (λ seq : list (π_DictAccess mem), seq.length)).sum = accesses.length) :
  ∀ (squash : π_DictAccess mem), squash ∈ squashed →
    is_squashed (list.filter (λ (e : π_DictAccess mem), e.key = squash.key) accesses) squash :=
begin
  intros squash squash_mem,
  rw list.mem_iff_nth_le at squash_mem,
  rcases squash_mem with ⟨n, h_n_lt, squash_eq⟩,
  have h_n_lt_seqs_len : n < seqs.length, { rwa [list.forall₂.length_eq h_squashed], },
  have h_is_squashed := list.forall₂.nth_le h_squashed h_n_lt_seqs_len h_n_lt,
  rw [←squash_eq],
  rwa ←(list.forall₂.nth_le (squashed_sublists_of_filtered_eq h_sorted h_subseq h_squashed h_sum_len) h_n_lt_seqs_len h_n_lt),
end

-- You may change anything in this definition except the name and arguments.
def spec_squash_dict (mem : F → F) (κ : ℕ) (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem) (ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  κ < 2 ^ 50 →
    ∃ (n < κ) (m < κ),
      (dict_accesses_end : F) = dict_accesses + ↑(n * π_DictAccess.SIZE) ∧
      (ρ_squashed_dict : F) = squashed_dict + ↑(m * π_DictAccess.SIZE) ∧
      let squashed := π_array_to_list mem squashed_dict m,
          accesses := π_array_to_list mem dict_accesses n in
      -- The squashed list is sorted by key
      sorted_keys squashed ∧
      -- The set of keys is the same in the accesses and the squashed list
      (key_list squashed).to_finset = (key_list accesses).to_finset ∧
      -- every squashed entry is the squash of the key accesses for the squashed key.
      ∀ s : π_DictAccess mem, s ∈ squashed →
        is_squashed (accesses.filter (λ e : π_DictAccess mem, e.key = s.key)) s

-- This is the specification of the inner function, but with a simplified set of arguments.
-- Claims that the list of squashed entries is sorted by key and are squashes of valid sequences with the given total length.
def squashed_of_length {mem : F → F} (κ : ℕ) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 remaining_accesses : F) (squashed_dict : π_DictAccess mem) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ (m < κ) (r < κ),
    (ρ_squashed_dict : F) = squashed_dict + ↑(m * π_DictAccess.SIZE) ∧
    remaining_accesses = ↑r ∧
    (∀ n, n * π_DictAccess.SIZE < PRIME ∧ (dict_accesses_end_minus1 : F) + 1 = dict_accesses + ↑(n * π_DictAccess.SIZE) →
      let squashed := π_array_to_list mem squashed_dict m,
          accesses := π_array_to_list mem dict_accesses n in
      -- The squashes are sorted by key.
      sorted_keys squashed ∧
      -- For every key there is a sub-list of the accesses which is valid and squashed by the key entry.
      ∃ seqs : list (list (π_DictAccess mem)),
        seqs.all₂ (λ seq, seq <+ accesses) ∧
        list.forall₂ (λ seq squash, is_squashed seq squash) seqs squashed ∧
        r = (seqs.map (λ seq : list (π_DictAccess mem), seq.length)).sum)

lemma squashed_of_length_κ {mem : F → F} {κ₁ κ₂ : ℕ} (h_κ : κ₁ ≤ κ₂) {dict_accesses : π_DictAccess mem} {dict_accesses_end_minus1 remaining_accesses : F} {squashed_dict : π_DictAccess mem} {ρ_squashed_dict : π_DictAccess mem} :
  squashed_of_length κ₁ dict_accesses dict_accesses_end_minus1 remaining_accesses squashed_dict ρ_squashed_dict →
    squashed_of_length κ₂ dict_accesses dict_accesses_end_minus1 remaining_accesses squashed_dict ρ_squashed_dict :=
begin
  intro h, rcases h with ⟨m, h_m, r, h_r, h_squashed⟩,
  use [m], use [by { apply lt_of_lt_of_le h_m h_κ }],
  use [r], use [by { apply lt_of_lt_of_le h_r h_κ }],
  exact h_squashed
end

lemma key_bound_κ {κ₁ κ₂ : ℕ} (h_κ : κ₁ ≤ κ₂) {key : F} { big_keys : F} :
  (big_keys ≠ 0 ∨ ∃ k < PRIME - κ₂ * rc_bound F, key = ↑k) → (big_keys ≠ 0 ∨ ∃ k < PRIME - κ₁ * rc_bound F, key = ↑k) :=
begin
  intro h_key,
  cases h_key,
  left, exact h_key,
  right, rcases h_key with ⟨k, h_k_le, h_k_eq⟩,
  use k, split, apply nat.lt_of_lt_of_le h_k_le, apply nat.sub_le_sub_left, apply nat.mul_le_mul_right _ h_κ,
  exact h_k_eq,
end


-- You may change anything in this definition except the name and arguments.
def spec_squash_dict_inner (mem : F → F) (κ : ℕ) (range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  κ ≤ 2 ^ 50 →
    key = squashed_dict.key ∧ 0 < rc_bound F ∧
    ((big_keys ≠ 0 ∨ ∃ k < PRIME - κ * rc_bound F, key = ↑k) →
      squashed_of_length κ dict_accesses dict_accesses_end_minus1 remaining_accesses squashed_dict ρ_squashed_dict)

def access_i {mem : F → F} (dict_accesses : π_DictAccess mem) (i : F) : π_DictAccess mem :=
  cast_π_DictAccess mem (dict_accesses + i * π_DictAccess.SIZE)

def valid_access_i (mem : F → F) (key : F) (dict_accesses : π_DictAccess mem) (indxs : list F) : Prop :=
  (∃ m < rc_bound F, ↑m = indxs.head) ∧
  list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs ∧
  valid_access (indxs.map (λ i, access_i dict_accesses i)) key

lemma valid_indxs_lt (n : ℕ) {indxs : list F}
    (h_n_le : n ≤ 2 ^ 50)
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_indxs_len : indxs.length = n)
    (h_head : ∃ m ≤ rc_bound F, ↑m = indxs.head)
    (h_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs) :
  ∃ indxs_n : list ℕ,
    indxs_n.length = indxs.length ∧
    indxs_n.map (λ i, (↑i : F)) = indxs ∧
    indxs_n.all₂ (λ i, i ≤ rc_bound F * indxs.length) :=
  begin
    revert indxs h_n_le h_indxs_nnil h_indxs_len h_head h_steps,
    induction n with n ih,
    { intros _ _ h_indxs_nnil h_indxs_len, exfalso, exact h_indxs_nnil (list.eq_nil_of_length_eq_zero h_indxs_len), },
    intros indxs h_n_le h_indxs_nnil h_indxs_len h_head h_steps,
    rcases h_head with ⟨m, m_lt, m_eq_head⟩,
    cases eq_or_ne n 0 with n_eq_zero n_ne_zero,
    { have h_indxs : indxs = [indxs.head],
      { rw [n_eq_zero] at h_indxs_len, rw [list.eq_cons_of_length_one h_indxs_len], dsimp, refl },
      use [[m]],
      split, { rw [list.length_singleton, h_indxs_len, n_eq_zero], },
      split, { rw [list.map_singleton, m_eq_head, h_indxs], dsimp, refl },
      rw [list.all₂_iff_forall], intros x h_x, rw [list.mem_singleton] at h_x, rwa [h_x, h_indxs_len, n_eq_zero, mul_one] },
    -- longer than 1, need the induction hypothesis.
    have h_tail_nnil : indxs.tail ≠ list.nil,
    { rw [←list.length_pos_iff_ne_nil, list.length_tail, h_indxs_len, nat.succ_sub_one], exact nat.pos_of_ne_zero n_ne_zero },
    have h_init_head : indxs.init.head = indxs.head,
    { rw [←(list.cons_head_tail h_indxs_nnil)], rw [list.init_cons_of_ne_nil h_tail_nnil], dsimp, refl },
    have h1 : n ≤ 2 ^ 50, from nat.le_of_succ_le h_n_le,
    have h2 : indxs.init.length = n, { rw [list.length_init, h_indxs_len], apply nat.succ_sub_one, },
    have h3 : indxs.init ≠ list.nil, { rw [←list.length_pos_iff_ne_nil, h2], exact nat.pos_of_ne_zero n_ne_zero },
    have h4 : ∃ m ≤ rc_bound F, ↑m = indxs.init.head, { rw [h_init_head], use [m, m_lt, m_eq_head] },
    -- separate the last step
    rw [←(list.init_append_last h_indxs_nnil), ←(list.init_append_last h3), list.append_assoc] at h_steps,
    rw [list.singleton_append, list.chain'_split] at h_steps,
    rw [list.init_append_last h3] at h_steps,
    rcases ih h1 h3 h2 h4 h_steps.1 with ⟨i_indxs_n, i_indxs_n_len, i_indxs_n_map, i_indxs_n_all⟩,
    have last_step : ∃ t < rc_bound F, ↑(t + 1) = (indxs.last h_indxs_nnil) - (indxs.init.last h3),
    { have h_step := h_steps.2, dsimp [list.chain'] at h_step, rw [list.chain_singleton] at h_step, exact h_step,  },
    rcases last_step with ⟨t, t_lt, t_eq⟩,
    have h5 : i_indxs_n ≠ list.nil, { rwa [←list.length_pos_iff_ne_nil, i_indxs_n_len, list.length_pos_iff_ne_nil] },
    use [i_indxs_n ++ [i_indxs_n.last h5 + (t + 1)]],
    split, { rw [list.length_append, list.length_singleton, i_indxs_n_len, h2, h_indxs_len], },
    split,
    { rw [list.map_append, list.map_singleton], rw [←(list.init_append_last h_indxs_nnil), i_indxs_n_map],
      apply (list.append_right_inj _).mpr, congr' 1, rw [nat.cast_add, t_eq], rw [←add_sub_assoc, add_comm],
      rw [sub_eq_iff_eq_add, add_left_cancel_iff],
      rw [←(list.last_map coe h5)], simp only [i_indxs_n_map], },
    rw [list.all₂_iff_forall], intros x h_x, rw [list.mem_append] at h_x,
    cases h_x,
    { rw [list.all₂_iff_forall] at i_indxs_n_all, apply le_trans (i_indxs_n_all x h_x),
      apply nat.mul_le_mul_left, rw [list.length_init], apply nat.sub_le, },
    rw [list.mem_singleton] at h_x, rw [h_x],
    have h6 : i_indxs_n.last h5 ≤ rc_bound F * indxs.init.length,
    { rw [list.all₂_iff_forall] at i_indxs_n_all, exact i_indxs_n_all _ (list.last_mem _), },
    apply le_trans (nat.add_le_add_left (nat.succ_le_of_lt t_lt) _),
    apply le_trans (nat.add_le_add_right h6 _), rw [h_indxs_len, h2],
    rw [nat.succ_eq_add_one, left_distrib, nat.mul_one],
  end

lemma valid_indxs_sorted_lt {indxs : list F}
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_indxs_le : indxs.length ≤ 2 ^ 50)
    (h_head : ∃ m ≤ rc_bound F, ↑m = indxs.head)
    (h_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs) :
  ∃ indxs_n : list ℕ,
    indxs_n.length = indxs.length ∧
    indxs_n.map (λ i, (↑i : F)) = indxs ∧
    indxs_n.all₂ (λ i, i ≤ rc_bound F * indxs.length) ∧
    indxs_n.chain' (λ i₁ i₂, i₁ < i₂) :=
  begin
    rcases valid_indxs_lt (indxs.length) h_indxs_le h_indxs_nnil rfl h_head h_steps
    with ⟨indxs_n, indxs_n_len, indxs_n_map, indxs_n_all⟩,
    use [indxs_n, indxs_n_len, indxs_n_map, indxs_n_all],
    rw [←indxs_n_map] at h_steps, rw[list.chain'_map, list.chain'.iff_mem] at h_steps,
    rw [list.chain'.iff_mem],
    have h_s : (∀ (x y : ℕ),
      (x ∈ indxs_n ∧ y ∈ indxs_n ∧ ∃ (m : ℕ) (H : m < rc_bound F), (↑(m + 1) : F) = ↑y - ↑x) →
        x ∈ indxs_n ∧ y ∈ indxs_n ∧ x < y),
    { intros x y h, rcases h with ⟨h_x, h_y, m, h_m, h_eq⟩, use [h_x, h_y],
      have h_bound : rc_bound F * (1 + indxs.length) < PRIME,
      { apply lt_of_le_of_lt (nat.mul_le_mul_of_nonneg_right (rc_bound_hyp F)),
        rw [←nat.succ_eq_one_add],
        apply lt_of_le_of_lt (nat.mul_le_mul_left _ (nat.succ_le_succ h_indxs_le)), rw [PRIME], norm_num1, },
      rw [list.all₂_iff_forall] at indxs_n_all,
      apply nat.lt_of_succ_le, apply le_trans (nat.le_add_left x.succ m), apply le_of_eq,
      rw [eq_sub_iff_add_eq, ←nat.cast_add, nat.add_assoc, ←nat.succ_eq_one_add] at h_eq,
      apply PRIME.nat_coe_field_inj _ _ h_eq,
      { rw [←nat.succ_add_eq_succ_add], apply lt_of_le_of_lt _ h_bound, rw [nat.left_distrib, nat.mul_one],
        apply nat.add_le_add, exact nat.succ_le_of_lt h_m, exact indxs_n_all x h_x, },
      apply lt_of_le_of_lt _ h_bound, rw [←nat.succ_eq_one_add], apply le_trans (indxs_n_all y h_y),
      apply nat.mul_le_mul_left, exact le_of_lt (nat.lt_succ_self _), },
    apply list.chain'.imp h_s h_steps,
  end

lemma valid_of_valid_non_zero_start {mem : F → F} {key : F} {dict_accesses : π_DictAccess mem} {indxs : list F}
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_valid : valid_access_i mem key dict_accesses indxs)
    (h_non_zero_start : indxs.head ≠ 0) :
  valid_access_i mem key (cast_π_DictAccess mem (dict_accesses + π_DictAccess.SIZE)) (indxs.map (λ x : F, x - 1)) :=
begin
  rcases h_valid with ⟨⟨m, h_m_lt, h_m_eq_head⟩, h_chain, h_valid_access⟩,
  split,
  { use [m - 1], split, { apply lt_of_le_of_lt (nat.pred_le m) h_m_lt, },
    rw [←(list.cons_head_tail h_indxs_nnil), list.map_cons, list.head_cons], rw [nat.cast_sub _, h_m_eq_head, nat.cast_one],
    rw [nat.one_le_iff_ne_zero], intro h_nm, apply h_non_zero_start, rw [←h_m_eq_head, h_nm, nat.cast_zero], },
  split, { rw [list.chain'_map], simp only [sub_sub_sub_comm, sub_self, sub_zero], exact h_chain, },
  rw [list.map_map, function.comp], dsimp [access_i], rw[coe_DictAccess_π_cast], ring_nf, exact h_valid_access,
end

lemma valid_indxs_head_pair {indxs : list F}
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_indxs_le : indxs.length ≤ 2 ^ 50)
    (h_head : ∃ m ≤ rc_bound F, ↑m = indxs.head)
    (h_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs)
    (h_tail_nnil : indxs.tail ≠ list.nil) :
  ∃ i₁ i₂ : ℕ, i₁ < PRIME ∧ i₂ < PRIME ∧ indxs.head = ↑i₁ ∧ indxs.tail.head = ↑i₂ ∧ i₁ < i₂ ∧ i₂ - i₁ ≤ rc_bound F:=
begin
  rcases valid_indxs_sorted_lt h_indxs_nnil h_indxs_le h_head h_steps with ⟨indxs_n, indxs_n_len, indxs_n_cast, indxs_n_bound, indxs_n_sorted⟩,
  have indxs_n_nnil : indxs_n ≠ list.nil, { rwa [←list.length_pos_iff_ne_nil, indxs_n_len, list.length_pos_iff_ne_nil], },
  have indxs_n_tail_nnil : indxs_n.tail ≠ list.nil,
  { rwa [←list.length_pos_iff_ne_nil, list.length_tail, indxs_n_len, ←list.length_tail, list.length_pos_iff_ne_nil], },
  have h_lt_prime : rc_bound F * indxs.length < PRIME,
  { apply lt_of_le_of_lt (nat.mul_le_mul (rc_bound_hyp F) h_indxs_le), rw [PRIME], norm_num1 },
  use [indxs_n.head, indxs_n.tail.head],
  rw [list.all₂_iff_forall] at indxs_n_bound,
  split, { apply lt_of_le_of_lt _ h_lt_prime, apply indxs_n_bound indxs_n.head (list.head_mem_self indxs_n_nnil), },
  split, { apply lt_of_le_of_lt _ h_lt_prime, apply indxs_n_bound indxs_n.tail.head (list.mem_of_mem_tail (list.head_mem_self indxs_n_tail_nnil)), },
  rw [←(list.cons_head_tail h_indxs_nnil), ←(list.cons_head_tail indxs_n_nnil), list.map_cons] at indxs_n_cast,
  have h1 := list.head_eq_of_cons_eq indxs_n_cast,
  rw [h1, list.cons_inj _] at indxs_n_cast,
  use [h1.symm],
  rw [←(list.cons_head_tail h_tail_nnil), ←(list.cons_head_tail indxs_n_tail_nnil), list.map_cons] at indxs_n_cast,
  have h2 := list.head_eq_of_cons_eq indxs_n_cast,
  use [h2.symm],
  rw [←(list.cons_head_tail indxs_n_nnil), ←(list.cons_head_tail indxs_n_tail_nnil), list.chain'_cons] at indxs_n_sorted,
  split, { exact indxs_n_sorted.1 },
  rw [←(list.cons_head_tail h_indxs_nnil), ←(list.cons_head_tail h_tail_nnil),  list.chain'_cons] at h_steps,
  rcases h_steps with ⟨⟨m, m_lt, h_pair⟩, _⟩, rw [←h1, ←h2] at h_pair,
  rw [←(nat.cast_sub (le_of_lt indxs_n_sorted.1))] at h_pair,
  rw [←(PRIME.nat_coe_field_inj _ _ h_pair)], apply nat.lt_of_lt_of_le (nat.lt_succ_self _) m_lt,
  { apply lt_of_le_of_lt (nat.succ_le_of_lt m_lt), apply lt_of_le_of_lt (rc_bound_hyp F), rw [PRIME], norm_num1 },
  apply lt_of_le_of_lt (nat.sub_le _ _),
  apply lt_of_le_of_lt (indxs_n_bound indxs_n.tail.head (list.mem_of_mem_tail (list.head_mem_self indxs_n_tail_nnil))),
  exact h_lt_prime
end

lemma valid_indxs_tail_head_ne_zero {indxs : list F}
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_indxs_le : indxs.length ≤ 2 ^ 50)
    (h_head : ∃ m ≤ rc_bound F, ↑m = indxs.head)
    (h_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs)
    (h_tail_nnil : indxs.tail ≠ list.nil) :
  indxs.tail.head ≠ 0 :=
begin
  rcases valid_indxs_head_pair h_indxs_nnil h_indxs_le h_head h_steps h_tail_nnil with ⟨i₁, i₂, i₁_lt, i₂_lt, head_eq, tail_head_eq, i_lt, _⟩,
  rw tail_head_eq, intro h_i₂, apply nat.not_lt_zero i₁,
  have h_i₂_zero : i₂ = 0, from PRIME.nat_coe_field_zero i₂_lt rfl h_i₂,
  exact h_i₂_zero ▸ i_lt,
end

lemma access_i_shift {mem : F → F} {dict_accesses : π_DictAccess mem} {indxs : list F} :
  indxs.map (λ i, access_i dict_accesses i) =
    indxs.map (λ i, access_i (cast_π_DictAccess mem (dict_accesses + π_DictAccess.SIZE)) (i - 1)) :=
begin
  dsimp [access_i], rw[coe_DictAccess_π_cast], ring_nf,
end

lemma indxs_are_sublist {mem : F → F} (dict_accesses : π_DictAccess mem) {dict_accesses_end_minus1 : F} (indxs : list F) {n : ℕ}
    (h_indxs_nnil : indxs ≠ list.nil)
    (h_indxs_le : indxs.length ≤ 2 ^ 50)
    (h_head : ∃ m ≤ rc_bound F, ↑m = indxs.head)
    (h_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) indxs)
    (h_end :∃ t < rc_bound F, dict_accesses_end_minus1 = dict_accesses + (indxs.last h_indxs_nnil) * π_DictAccess.SIZE + ↑t)
    (h_accesses_len : n * π_DictAccess.SIZE < PRIME ∧ (dict_accesses_end_minus1 : F) + 1 = dict_accesses + ↑(n * π_DictAccess.SIZE)) :
  indxs.map (λ i, access_i dict_accesses i) <+ π_array_to_list mem dict_accesses n :=
begin
  revert dict_accesses indxs h_indxs_nnil h_indxs_le h_head h_steps h_end h_accesses_len,
  induction n with n ih,
  { intros dict_accesses indxs h_indxs_nnil h_indxs_le h_head h_steps h_end h_accesses_len,
    rcases valid_indxs_sorted_lt h_indxs_nnil h_indxs_le h_head h_steps
    with ⟨indxs_n, indxs_n_len, indxs_n_map, indxs_n_lt, _⟩,
    have indxs_n_nnil : indxs_n ≠ list.nil, { rwa [←list.length_pos_iff_ne_nil, indxs_n_len, list.length_pos_iff_ne_nil], },
    rw [list.all₂_iff_forall] at indxs_n_lt,
    exfalso,
    rcases h_end with ⟨t, t_lt, da_t⟩, rcases h_accesses_len with ⟨n_lt, da_n⟩,
    rw [zero_mul, nat.cast_zero, da_t] at da_n, rw [add_assoc, add_assoc, add_left_cancel_iff] at da_n,
    suffices h_ne_zero : indxs.last h_indxs_nnil * ↑π_DictAccess.SIZE + (↑t + 1) ≠ 0, { exact h_ne_zero da_n },
    simp only [←indxs_n_map], rw [list.last_map _ indxs_n_nnil], norm_cast, rw π_DictAccess.SIZE,
    intro h_eq_zero,
    apply (show indxs_n.last indxs_n_nnil * 3 + (t + 1) ≠ 0, { norm_num }),
    apply PRIME.nat_coe_field_zero _ _ h_eq_zero,
    have h_last_lt := indxs_n_lt (indxs_n.last indxs_n_nnil) (list.last_mem _),
    have h_last_le_n : indxs_n.last indxs_n_nnil ≤ 2 ^ 128 * 2 ^ 50,
    { calc
        indxs_n.last indxs_n_nnil ≤ (rc_bound F) * indxs.length : indxs_n_lt (indxs_n.last indxs_n_nnil) (list.last_mem _)
        ... ≤ 2 ^ 128 * indxs.length : nat.mul_le_mul_right _ (rc_bound_hyp F)
        ... ≤ 2 ^ 128 * 2 ^ 50 : nat.mul_le_mul_left _ h_indxs_le,
    },
    { calc
        indxs_n.last indxs_n_nnil * 3 + (t + 1) ≤ indxs_n.last indxs_n_nnil * 3 + rc_bound F : nat.add_le_add_left (nat.succ_le_of_lt t_lt) _
        ... ≤ indxs_n.last indxs_n_nnil * 3 +  2 ^ 128 : nat.add_le_add_left (rc_bound_hyp F) _
        ... ≤ 2 ^ 128 * 2 ^ 50 * 3 + 2 ^ 128 : nat.add_le_add_right (nat.mul_le_mul_of_nonneg_right h_last_le_n) _
        ... < PRIME : by { rw [PRIME], norm_num1 },
        }, refl },
  intros dict_accesses indxs h_indxs_nnil h_indxs_le h_head h_steps h_end h_accesses_len,
  rcases valid_indxs_sorted_lt h_indxs_nnil h_indxs_le h_head h_steps with ⟨indxs_n, indxs_n_len, indxs_n_map, indxs_n_lt, _⟩,
  have indxs_n_nnil : indxs_n ≠ list.nil, { rwa [←list.length_pos_iff_ne_nil, indxs_n_len, list.length_pos_iff_ne_nil], },
  rw [list.all₂_iff_forall] at indxs_n_lt,
  dsimp [access_i], rw [←(list.cons_head_tail h_indxs_nnil), list.map_cons],
  dsimp [π_array_to_list],
  let next_access := cast_π_DictAccess mem (dict_accesses + π_DictAccess.SIZE),
  have next_accesses_end :
    n * π_DictAccess.SIZE < PRIME ∧ dict_accesses_end_minus1 + 1 = next_access + ↑(n * π_DictAccess.SIZE),
  { split, { apply lt_of_le_of_lt _ h_accesses_len.1, apply nat.mul_le_mul_right _ (nat.le_succ _), },
    rw [h_accesses_len.2], dsimp [next_access], rw [coe_DictAccess_π_cast, add_assoc, add_left_cancel_iff],
      norm_cast, congr' 1, rw [nat.succ_eq_add_one], ring, },
  cases eq_or_ne indxs.head 0 with head_eq_zero head_ne_zero,
  { rw [head_eq_zero, access_i, zero_mul, add_zero],
    apply list.sublist.cons_cons,
    rw [access_i_shift, ←list.map_map],
    cases eq_or_ne indxs.tail list.nil with tail_nil indxs_tail_nnil,
    { rw tail_nil, simp only [list.map_nil], apply list.nil_sublist },
    -- hypotheses needed for the induction hypothesis
    let t_indxs := indxs.tail.map (λ i : F, i - 1),
    have tail_nnil : t_indxs ≠ list.nil, { intro h_t, exact indxs_tail_nnil (list.eq_nil_of_map_eq_nil h_t), },
    have tail_le : t_indxs.length ≤ 2 ^ 50,
    { rw [list.length_map, list.length_tail], apply le_trans _ h_indxs_le, apply nat.sub_le, },
    have tail_head : ∃ m ≤ rc_bound F, ↑m = t_indxs.head,
    { rw [list_map_head _ indxs_tail_nnil],
      rcases valid_indxs_head_pair h_indxs_nnil h_indxs_le h_head h_steps indxs_tail_nnil
      with ⟨i₁, i₂, i₁_lt, i₂_lt, i₁_eq, i₂_eq, i_lt, i_diff_le⟩,
      have h_i₁_zero : i₁ = 0, { rw [head_eq_zero] at i₁_eq, apply PRIME.nat_coe_field_zero i₁_lt rfl i₁_eq.symm,  },
      use [i₂ - 1], rw [i₂_eq],
      split, { apply le_trans (nat.sub_le _ _), rw [h_i₁_zero, nat.sub_zero] at i_diff_le,  exact i_diff_le },
      rw [nat.cast_sub (nat.one_le_of_lt i_lt), nat.cast_one], },
    have tail_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) t_indxs,
    { rw [list.chain'_map], ring_nf, apply list.chain'.tail, exact h_steps, },
    have tail_end : ∃ (t : ℕ) (H : t < rc_bound F),
      dict_accesses_end_minus1 = ↑next_access + t_indxs.last tail_nnil * ↑π_DictAccess.SIZE + ↑t,
    { rcases h_end with ⟨t, t_lt, t_eq⟩, use [t, t_lt], rw[t_eq], dsimp [next_access],
      have last_eq : t_indxs.last tail_nnil = indxs.last h_indxs_nnil - 1,
      { rw [list.last_map _ indxs_tail_nnil, sub_eq_add_neg, sub_eq_add_neg, add_right_cancel_iff], apply list_tail_last, },
      rw [last_eq], rw [coe_DictAccess_π_cast], ring_nf },
    have tail_accesses_end :
      n * π_DictAccess.SIZE < PRIME ∧ dict_accesses_end_minus1 + 1 = next_access + ↑(n * π_DictAccess.SIZE),
    { split, { apply lt_of_le_of_lt _ h_accesses_len.1, apply nat.mul_le_mul_right _ (nat.le_succ _), },
      rw [h_accesses_len.2], dsimp [next_access], rw [coe_DictAccess_π_cast, add_assoc, add_left_cancel_iff],
      norm_cast, congr' 1, rw [nat.succ_eq_add_one], ring, },
    exact ih next_access t_indxs tail_nnil tail_le tail_head tail_steps tail_end next_accesses_end },
  -- First index is not zero, the whole list is a sublist of the tail.
  rw [←list.map_cons, list.cons_head_tail h_indxs_nnil],
  let s_indxs := indxs.map (λ i : F, i - 1),
  have s_indxs_nnil : s_indxs ≠ list.nil, { intro h, apply h_indxs_nnil (list.map_eq_nil.mp h) },
  have s_head : ∃ m ≤ rc_bound F, ↑m = s_indxs.head,
  { rw [list_map_head _ h_indxs_nnil], rcases h_head with ⟨m, m_le, m_eq⟩, use [m - 1], split, apply le_trans (nat.sub_le _ _) m_le,
    rw [nat.cast_sub _], { rw [m_eq, nat.cast_one] },
    rw [nat.one_le_iff_ne_zero], intro h, rw [h, nat.cast_zero] at m_eq, apply head_ne_zero m_eq.symm },
  have s_steps : list.chain' (λ i₁ i₂, ∃ m < rc_bound F, ↑(m + 1) = i₂ - i₁) s_indxs,
  { rw [list.chain'_map], ring_nf, exact h_steps, },
  have s_end : ∃ (t : ℕ) (H : t < rc_bound F),
    dict_accesses_end_minus1 = ↑next_access + s_indxs.last s_indxs_nnil * ↑π_DictAccess.SIZE + ↑t,
  { rcases h_end with ⟨t, t_lt, t_eq⟩, use [t, t_lt], rw[t_eq], rw [list.last_map _ h_indxs_nnil, coe_DictAccess_π_cast], ring, },
  apply list.sublist_cons_of_sublist,
  rw [access_i_shift, ←list.map_map],
  exact ih next_access s_indxs s_indxs_nnil ((list.length_map (λ i : F, i - 1) indxs).symm ▸ h_indxs_le) s_head s_steps s_end next_accesses_end,
end

def squash_dict_inner_block17_invariant (mem : F → F) (n : ℕ) (prev_loop_locals : squash_dict_inner.π_LoopLocals mem) (range_check_ptr : F) (dict_accesses : π_DictAccess mem) (key : F) (squashed_dict dict_diff : π_DictAccess mem) : Prop :=
  dict_diff = squashed_dict ∧ key = dict_diff.key ∧
  ↑(n + 1) = prev_loop_locals.range_check_ptr - range_check_ptr ∧
  ∃ (indxs : list F) (h_len : indxs.length = n + 1),
    valid_access_i mem key dict_accesses indxs ∧
    (prev_loop_locals.access_ptr : F) = dict_accesses + (indxs.last (list.ne_nil_of_length_eq_succ h_len) * π_DictAccess.SIZE) ∧
    prev_loop_locals.value = (access_i dict_accesses (indxs.last (list.ne_nil_of_length_eq_succ h_len))).new_value ∧
    (access_i dict_accesses indxs.head).key = squashed_dict.key ∧
    (access_i dict_accesses indxs.head).prev_value = squashed_dict.prev_value

-- You may change anything in this definition except the name and arguments.
def spec_squash_dict_inner_block17 (mem : F → F) (κ : ℕ) (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  κ ≤ 2 ^ 50 →
    (big_keys ≠ 0 ∨ ∃ k < PRIME - κ * rc_bound F, key = ↑k) →
      ∀ prev_loop_locals : squash_dict_inner.π_LoopLocals mem,
        prev_loop_locals = squash_dict_inner.cast_π_LoopLocals mem (ap - squash_dict_inner.LoopLocals.SIZE) →
          ∀ n : ℕ,
            n + κ ≤ 2 ^ 50 →
            squash_dict_inner_block17_invariant mem n prev_loop_locals range_check_ptr dict_accesses key squashed_dict dict_diff →
              ∃ (indxs : list F) (h_nnil : indxs ≠ list.nil),
                valid_access_i mem key dict_accesses indxs ∧
                is_squashed (indxs.map (λ i, access_i dict_accesses i)) squashed_dict ∧
                ∃ t < rc_bound F, dict_accesses_end_minus1 = dict_accesses + (indxs.last h_nnil) * π_DictAccess.SIZE + ↑t ∧
                (∃ r : ℕ, remaining_accesses = ↑r ∧ r < (n + 1) + κ ∧ indxs.length ≤ r) ∧
                (remaining_accesses = ↑indxs.length ∧ (ρ_squashed_dict : F) = squashed_dict + ↑π_DictAccess.SIZE
                  ∨
                  (∃ k₁ k₂ : ℕ, k₁ < PRIME ∧ k₂ < PRIME ∧
                    key = ↑k₁ ∧ (cast_π_DictAccess mem (squashed_dict + π_DictAccess.SIZE)).key = ↑k₂ ∧ k₁ < k₂) ∧
                  squashed_of_length
                    κ
                    dict_accesses
                    dict_accesses_end_minus1
                    (remaining_accesses - indxs.length)
                    (cast_π_DictAccess mem (squashed_dict + π_DictAccess.SIZE))
                    ρ_squashed_dict)

/- squash_dict_inner block 54 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_squash_dict_inner_block54 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop next_key ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ (κ₁ : ℕ), spec_squash_dict_inner mem κ₁ range_check_ptr dict_accesses dict_accesses_end_minus1 next_key remaining_accesses (cast_π_DictAccess mem (squashed_dict + DictAccess.SIZE)) big_keys ρ_range_check_ptr ρ_squashed_dict ∧
  κ₁ + 4 ≤ κ

/- squash_dict_inner block 30 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_squash_dict_inner_block30 (mem : F → F) (κ : ℕ) (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ last_loop_locals : squash_dict_inner.π_LoopLocals mem, last_loop_locals = squash_dict_inner.cast_π_LoopLocals mem (ap - squash_dict_inner.LoopLocals.SIZE) ∧
  mem ap = dict_accesses_end_minus1 - last_loop_locals.access_ptr ∧
  mem ap = mem last_loop_locals.range_check_ptr ∧
  is_range_checked (rc_bound F) (mem ap) ∧
  ∃ n_used_accesses : F, n_used_accesses = last_loop_locals.range_check_ptr - range_check_ptr ∧
  last_loop_locals.value = dict_diff.new_value ∧
  ∃ range_check_ptr₁ : F, range_check_ptr₁ = last_loop_locals.range_check_ptr + 1 ∧
  ∃ remaining_accesses₁ : F, remaining_accesses₁ = remaining_accesses - n_used_accesses ∧
  ((remaining_accesses₁ = 0 ∧
    9 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr₁ ∧
    ρ_squashed_dict = cast_π_DictAccess mem (squashed_dict + DictAccess.SIZE)) ∨
   (remaining_accesses₁ ≠ 0 ∧
    ∃ next_key : F,
    ((big_keys ≠ 0 ∧
      ∃ (κ₁ : ℕ) (range_check_ptr₂ : F), spec_assert_lt_felt mem κ₁ range_check_ptr₁ key next_key range_check_ptr₂ ∧
      ∃ dict_accesses₁ : π_DictAccess mem, dict_accesses₁ = dict_accesses ∧
      ∃ dict_accesses_end_minus1₁ : F, dict_accesses_end_minus1₁ = dict_accesses_end_minus1 ∧
      ∃ next_key₁ : F, next_key₁ = next_key ∧
      ∃ remaining_accesses₂ : F, remaining_accesses₂ = remaining_accesses₁ ∧
      ∃ (κ₂ : ℕ), auto_spec_squash_dict_inner_block54 mem κ₂ range_check_ptr₂ dict_accesses₁ dict_accesses_end_minus1₁ key remaining_accesses₂ squashed_dict big_keys dict_diff first_value should_skip_loop next_key₁ ρ_range_check_ptr ρ_squashed_dict ∧
      κ₁ + κ₂ + 16 ≤ κ) ∨
     (big_keys = 0 ∧
      mem range_check_ptr₁ = next_key - (key + 1) ∧
      is_range_checked (rc_bound F) (next_key - (key + 1)) ∧
      ∃ range_check_ptr₂ : F, range_check_ptr₂ = range_check_ptr₁ + 1 ∧
      ∃ dict_accesses₁ : π_DictAccess mem, dict_accesses₁ = dict_accesses ∧
      ∃ dict_accesses_end_minus1₁ : F, dict_accesses_end_minus1₁ = dict_accesses_end_minus1 ∧
      ∃ next_key₁ : F, next_key₁ = next_key ∧
      ∃ remaining_accesses₂ : F, remaining_accesses₂ = remaining_accesses₁ ∧
      ∃ (κ₁ : ℕ), auto_spec_squash_dict_inner_block54 mem κ₁ range_check_ptr₂ dict_accesses₁ dict_accesses_end_minus1₁ key remaining_accesses₂ squashed_dict big_keys dict_diff first_value should_skip_loop next_key₁ ρ_range_check_ptr ρ_squashed_dict ∧
      κ₁ + 17 ≤ κ))))

/- squash_dict_inner block 17 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_squash_dict_inner_block17 (mem : F → F) (κ : ℕ) (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ prev_loop_locals : squash_dict_inner.π_LoopLocals mem, prev_loop_locals = squash_dict_inner.cast_π_LoopLocals mem (ap - squash_dict_inner.LoopLocals.SIZE) ∧
  ∃ loop_temps : squash_dict_inner.π_LoopTemps mem, loop_temps = squash_dict_inner.cast_π_LoopTemps mem ap ∧
  ∃ loop_locals : squash_dict_inner.π_LoopLocals mem, loop_locals = squash_dict_inner.cast_π_LoopLocals mem (ap + squash_dict_inner.LoopTemps.SIZE) ∧
  loop_temps.index_delta_minus1 = mem prev_loop_locals.range_check_ptr ∧
  is_range_checked (rc_bound F) (loop_temps.index_delta_minus1) ∧
  loop_temps.index_delta = loop_temps.index_delta_minus1 + 1 ∧
  loop_temps.ptr_delta = loop_temps.index_delta * DictAccess.SIZE ∧
  loop_locals.access_ptr = cast_π_DictAccess mem (prev_loop_locals.access_ptr + loop_temps.ptr_delta) ∧
  ∃ access : π_DictAccess mem, access = loop_locals.access_ptr ∧
  prev_loop_locals.value = access.prev_value ∧
  loop_locals.value = access.new_value ∧
  key = access.key ∧
  loop_locals.range_check_ptr = prev_loop_locals.range_check_ptr + 1 ∧
  ((loop_temps.should_continue = 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_squash_dict_inner_block30 mem κ₁ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict ∧
    κ₁ + 9 ≤ κ) ∨
   (loop_temps.should_continue ≠ 0 ∧
    ∃ (κ₁ : ℕ), spec_squash_dict_inner_block17 mem κ₁ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict ∧
    κ₁ + 9 ≤ κ))

/- squash_dict_inner block 17 soundness theorem -/

-- Same as the main soundness theorem for inner_block17, but assuming we arrived at the end of the loop.
theorem sound_squash_dict_inner_after_loop
    {mem : F → F}
    (κ : ℕ)
    (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem)
    -- auto spec after the loop.
    (h_cont : auto_spec_squash_dict_inner_block30 mem κ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict) :
  spec_squash_dict_inner_block17 mem κ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict :=
begin
  intro κ_bound,
  intros key_bound next_ll h_next_ll n n_le next_invariant,
  rcases next_invariant with ⟨dict_diff_eq, dict_diff_key, next_inv⟩,
  rcases h_cont with ⟨ll, h_ll, da_end_rc1, _, da_end_rc2, n_used_acc, n_use_acc_eq, ll_value_eq, h_cont⟩,
  have h_ll_eq : next_ll = ll, { rw [h_next_ll, h_ll] },
  rw [h_ll_eq] at next_inv,
  rcases next_inv with ⟨h_n_rc, indxs, h_indxs_len, h_valid_access, h_access_ptr, h_last_value, h_squashed_key, h_squashed_prev⟩,
  have h_indxs_ne_nil : indxs ≠ list.nil, { rw [←list.length_pos_iff_ne_nil, h_indxs_len], apply nat.succ_pos, },
  use [indxs, h_indxs_ne_nil],
  use [h_valid_access],
  have h_map_ne_nil : list.map (λ (i : F), access_i dict_accesses i) indxs ≠ list.nil,
  { intro h, exact h_indxs_ne_nil (list.map_eq_nil.mp h), },
  use h_map_ne_nil,
  split, { rw [list_map_head _ h_indxs_ne_nil], exact h_squashed_key, },
  split, { rw [list_map_head _ h_indxs_ne_nil], exact h_squashed_prev, },
  split, { rw [list.last_map _ h_indxs_ne_nil], rw [←h_last_value], rw [←dict_diff_eq, ←ll_value_eq], },
  { rw [←dict_diff_eq, ←dict_diff_key], apply h_valid_access.2.2, },
  rcases da_end_rc2 with ⟨t, h_t_rc, h_end_rc⟩, rw [da_end_rc1] at h_end_rc,
  use [t, h_t_rc], split,
  { rw [←h_access_ptr, ←h_end_rc], ring, },
  rcases h_cont with ⟨rc_ptr, rc_ptr_eq, rem, rem_eq, ⟨rem_zero, h_cont⟩|⟨rem_ne_zero, h_cont⟩⟩,
  { -- no remaining accesses to process
    rcases h_cont with ⟨h_κ, _, h_squashed_dict⟩,
    split,
    { use [n+1], split, { rw [h_n_rc, ←n_use_acc_eq, ←sub_eq_zero, ←rem_eq, rem_zero], },
      split, { apply nat.lt_add_of_zero_lt_left, apply lt_of_lt_of_le _ h_κ, norm_num1, }, rw [h_indxs_len] },
    left,
    rw [h_indxs_len, h_n_rc, ←n_use_acc_eq],
    rw [rem_zero] at rem_eq,
    use [sub_eq_zero.mp rem_eq.symm],
    rw [h_squashed_dict, coe_DictAccess_π_cast],
  },
  -- The recursive call to squash_dict_inner
  rw [n_use_acc_eq, ←h_n_rc, ←h_indxs_len] at rem_eq,
  rcases h_cont with ⟨next_key, ⟨big_keys_ne_zero, h_cont⟩|⟨big_keys_zero, h_cont⟩⟩,
  {-- has big keys
    rcases h_cont with ⟨κ₁, rc_ptr₂, lt_felt, acc₁, acc₁_eq, acc_end_minus1₁, acc_end_minus1₁_eq, next_key₁, next_key₁_eq, rem₂, rem₂_eq, κ₂, block54, h_κ⟩,
    rcases block54 with ⟨κ₃, h_inner, h_κ₃⟩,
    rcases h_inner (by { linarith [κ_bound] }) with ⟨h_key, _, h_squashed_of_length⟩,
    have h_squashed := squashed_of_length_κ (show κ₃ ≤ κ, by { linarith [h_κ] }) (h_squashed_of_length (or.intro_left _ big_keys_ne_zero)),
    split, {
      rcases h_squashed with ⟨_, _, r, h_r, _, r_eq, h_squashed⟩,
      use [n + 1 + r], split, { rw [nat.cast_add], rw [←r_eq, ←h_indxs_len, rem₂_eq, rem_eq], ring },
      split, { apply nat.add_lt_add_left, exact h_r }, rw [h_indxs_len], exact nat.le_add_right _ _, },
    right,
    split, { rw [←h_key, next_key₁_eq], exact lt_felt },
    rw [←acc₁_eq, ←acc_end_minus1₁_eq, ←rem_eq, ←rem₂_eq],
    apply squashed_of_length_κ _ (h_squashed_of_length (or.intro_left _ big_keys_ne_zero)), linarith [h_κ, h_κ₃],
  },
  -- no big keys
  rcases h_cont with ⟨_, rc_keys, _, _, acc₁, acc₁_eq, acc_end_minus1₁, acc_end_minus1₁_eq, next_key₁, next_key₁_eq, rem₂, rem₂_eq, κ₂, block54, h_κ⟩,
  rcases block54 with ⟨κ₃, h_inner, h_κ₃⟩,
  rcases h_inner (by { linarith [κ_bound] }) with ⟨h_key, _, h_squashed_of_length⟩,
  have h_next_key : (big_keys ≠ 0 ∨ ∃ (k : ℕ) (H : k < PRIME - κ₃ * rc_bound F), next_key₁ = ↑k),
  { right,
    rcases or.resolve_left key_bound (not_not.mpr big_keys_zero) with ⟨k, h_k_lt, h_k_eq⟩,
    rcases rc_keys with ⟨k₁, h_k₁_lt, h_k₁_eq⟩,
    use [k + k₁ + 1], split,
    have h_κ_le : κ₃ + 1 ≤ κ, { linarith [h_κ, h_κ₃] },
    { apply lt_of_lt_of_le (nat.add_succ_lt_add h_k_lt h_k₁_lt), rw [←(nat.le_sub_iff_right _)],
      { rw [nat.sub_sub], apply nat.sub_le_sub_left,
        apply le_trans _ (nat.mul_le_mul_right _ h_κ_le), rw [nat.right_distrib, nat.one_mul],  },
      have h_κ_rc_le_prime : κ * rc_bound F ≤ PRIME,
      { apply le_of_lt, apply nat.lt_of_sub_eq_succ (nat.succ_pred_eq_of_pos _).symm, exact lt_of_le_of_lt (zero_le _) h_k_lt, },
      rw [nat.le_sub_iff_right],
      { apply le_trans _ h_κ_rc_le_prime, apply le_trans _ (nat.mul_le_mul_right _ h_κ_le), linarith, },
      apply le_trans _ h_κ_rc_le_prime, apply nat.mul_le_mul_right, exact nat.le_of_succ_le h_κ_le, },
    rw [sub_eq_iff_eq_add] at h_k₁_eq, rw [next_key₁_eq, h_k₁_eq, h_k_eq, add_comm k k₁, add_assoc], norm_cast },
  have h_squashed := squashed_of_length_κ (show κ₃ ≤ κ, by { linarith [h_κ] }) (h_squashed_of_length h_next_key),
  split, {
      rcases h_squashed with ⟨_, _, r, h_r, _, r_eq, h_squashed⟩,
      use [n + 1 + r], split, { rw [nat.cast_add], rw [←r_eq, ←h_indxs_len, rem₂_eq, rem_eq], ring },
      split, { apply nat.add_lt_add_left, exact h_r }, rw [h_indxs_len], exact nat.le_add_right _ _, },
  right,
  split,
  { rw [←h_key, next_key₁_eq], dsimp [is_range_checked] at rc_keys,
    cases key_bound, { exfalso, exact key_bound big_keys_zero },
    rcases key_bound with ⟨k₁, h_k₁_le, h_k₁_eq⟩, rcases rc_keys with ⟨k, h_k_le, h_k_eq⟩,
    use [k₁, k₁ + k + 1], split, { apply lt_of_lt_of_le h_k₁_le, apply nat.sub_le, },
    split, {
      rw [add_assoc, ←(nat.sub_add_cancel (show rc_bound F ≤ PRIME, { exact le_of_lt rc_bound_lt_PRIME }))],
      apply lt_of_le_of_lt (nat.add_le_add_left (nat.succ_le_of_lt h_k_le) _),
      apply nat.add_lt_add_right,
      apply nat.lt_of_lt_of_le h_k₁_le,
      apply nat.sub_le_sub_left,
      apply nat.le_mul_of_pos_left, linarith [h_κ] },
    use h_k₁_eq, split, { rw [nat.cast_add, nat.cast_add, ←h_k₁_eq, ←h_k_eq, nat.cast_one], ring },
    linarith, },
  rw [←acc₁_eq, ←acc_end_minus1₁_eq, ←rem_eq, ←rem₂_eq],
  apply squashed_of_length_κ _  (h_squashed_of_length h_next_key), linarith [h_κ, h_κ₃],
end


-- Do not change the statement of this theorem. You may change the proof.
theorem sound_squash_dict_inner_block17
    {mem : F → F}
    (κ : ℕ)
    (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys : F) (dict_diff : π_DictAccess mem) (first_value should_skip_loop ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem)
    (h_auto : auto_spec_squash_dict_inner_block17 mem κ ap range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict) :
  spec_squash_dict_inner_block17 mem κ ap range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict :=
begin
  intro κ_bound,
  intros key_bound p_ll h_p_ll n_acc n_acc_le inv,
  rcases h_auto with
    ⟨prev_ll, h_prev_ll, ltemps, h_ltemps, ll, h_ll, h_lt_idm1, rc_lt_idm1, lt_id_eq, lt_pd_eq, h_ll_pa,
      access, h_access, access_pv_eq, access_nv_eq, access_key_eq, ll_rc_eq, h_cont⟩,
  have h_ll_eq : p_ll = prev_ll, { rw [h_p_ll, h_prev_ll] },
  rw [h_ll_eq] at inv,
  rcases inv with ⟨dict_diff_eq, dict_diff_key, n_acc_eq, indxs, h_indxs_len, h_prefix_valid, h_last_access, h_last_value, h_squashed_key, h_squashed_prev⟩,
  have h_indxs_nnil : indxs ≠ list.nil, from list.ne_nil_of_length_eq_succ h_indxs_len,
  -- one loop step, needed in both cases below.
  have h_next_i : valid_access_i mem key dict_accesses (indxs ++ [indxs.last h_indxs_nnil + ltemps.index_delta]),
  {
    rcases h_prefix_valid with ⟨⟨m, m_le, m_head⟩, h_chain, h_valid_key, h_valid_value⟩,
    split, { use [m, m_le], rw [m_head], apply (list.head_append _ _).symm, assumption },
    split,
    { apply list.chain'.append h_chain (list.chain'_singleton _),
      intros x h_x y h_y, simp only [list.head', option.mem_def] at h_y, rw [←h_y],
      rcases list.mem_last'_eq_last h_x with ⟨_, h_last⟩, rw [h_last], ring_nf, rw lt_id_eq,
      rcases rc_lt_idm1 with ⟨n, h_lt, h_eq⟩,
      use [n, h_lt], rw h_eq, norm_cast },
    split,
    { rw [list.all₂_iff_forall, list.map_append, list.forall_mem_append],
      split, rwa [←list.all₂_iff_forall], rw [list.map_singleton],
      intro x, rw [list.mem_singleton], intro h_x, rw [h_x, access_key_eq, h_access, h_ll_pa, lt_pd_eq],
      dsimp [access_i], rw [h_last_access], congr' 1, ring },
    rw [list.map_append], apply list.chain'.append h_valid_value (list.chain'_singleton _),
    intros x h_x y h_y, simp only [list.head', option.mem_def] at h_y, dsimp [access_i] at h_y, rw [←h_y],
    rw [right_distrib, ←add_assoc, ←h_last_access, ←lt_pd_eq, ←h_ll_pa, ←h_access, ←access_pv_eq],
    rcases list.mem_last'_eq_last h_x with ⟨_, h_last⟩, rw [h_last],
    rw [list.last_map _ h_indxs_nnil], rw [←h_last_value]
  },
  -- The loop variant for the next step holds at the end of the loop.
  have next_invariant: squash_dict_inner_block17_invariant mem (n_acc + 1) ll range_check_ptr dict_accesses key squashed_dict dict_diff,
  {
    use [dict_diff_eq, dict_diff_key],
    split, { rw [ll_rc_eq, nat.cast_add, n_acc_eq, nat.cast_one], ring },
    use indxs ++ [indxs.last h_indxs_nnil + ltemps.index_delta],
    split, rotate, { rw [list.length_append, list.length_singleton, h_indxs_len] },
    split, { exact h_next_i },
    split, { rw [list.last_append_singleton, h_ll_pa, coe_DictAccess_π_cast, lt_pd_eq, h_last_access], ring },
    split, { rw [list.last_append_singleton], rw [access_nv_eq], rw [h_access], rw [h_ll_pa], rw [lt_pd_eq, h_last_access],
      dsimp [access_i], ring_nf },
    split, { rwa [list_append_head h_indxs_nnil] },
    rwa [list_append_head h_indxs_nnil]
  },
  have next_ap : ap + ↑squash_dict_inner.LoopTemps.SIZE = ap + 7 - ↑squash_dict_inner.LoopLocals.SIZE,
      { rw [add_sub_assoc], norm_num, },
  rcases h_cont with ⟨_, κ₁, h_cont, h_κ⟩|⟨_, κ₁, h_ind⟩,
  { -- Loop terminated, continue to next block.
    have h_next_n_acc_le : n_acc + 1 + κ₁ ≤ 2 ^ 50,
    { rw [add_assoc], apply le_trans _ n_acc_le, apply nat.add_le_add_left, apply le_trans _ h_κ, rw [add_comm 1 _],
      apply nat.add_le_add_left, norm_num1, },
    rcases sound_squash_dict_inner_after_loop κ₁ _ _ _ _ _ _ _ _ _ _ _ _ _ h_cont (by { linarith [h_κ, κ_bound] }) _ ll (next_ap ▸ h_ll) (n_acc + 1) h_next_n_acc_le next_invariant
    with ⟨trm_indxs, trm_nnil, trm_valid, trm_squashed, trm_t, trm_t_le, trm_dict_accesses, trm_len, trm_cont⟩,
    -- first, get rid of the key bound goal introduced above.
    rotate, { apply key_bound_κ _ key_bound, linarith [h_κ], },
    use [trm_indxs, trm_nnil, trm_valid, trm_squashed, trm_t, trm_t_le, trm_dict_accesses],
    split,
    { rcases trm_len with ⟨r, h_r_eq, h_r_lt, h_indxs_le_r⟩, use [r, h_r_eq],
      split, { apply lt_trans h_r_lt, rw [add_assoc (n_acc + 1) _ _], apply nat.add_lt_add_left, linarith [h_κ], },
      use [h_indxs_le_r], },
    cases trm_cont,
    { left, exact trm_cont, },
    right,
    rcases trm_cont with ⟨trm_keys_sorted, trm_squashed_of_length⟩,
    use [trm_keys_sorted],
    apply squashed_of_length_κ _ trm_squashed_of_length, linarith [h_κ],
  },
  -- loop continues (induction step)
  rcases h_ind with ⟨h_ind, h_κ⟩,
  have h_next_n_acc_le : n_acc + 1 + κ₁ ≤ 2 ^ 50,
  { rw [add_assoc], apply le_trans _ n_acc_le, apply nat.add_le_add_left, apply le_trans _ h_κ, rw [add_comm 1 _],
    apply nat.add_le_add_left, norm_num1, },
  rcases h_ind (by { linarith [h_κ, κ_bound] }) _ ll (next_ap ▸ h_ll) (n_acc + 1) h_next_n_acc_le next_invariant
    with ⟨ind_indxs, ind_nnil, ind_valid, ind_squashed, ind_t, ind_t_le, ind_dict_accesses, ind_len, ind_cont⟩,
  -- first, get rid of the key bound goal introduced above.
  rotate, { apply key_bound_κ _ key_bound, linarith [h_κ], },
  use [ind_indxs, ind_nnil, ind_valid, ind_squashed, ind_t, ind_t_le, ind_dict_accesses],
  split,
  { rcases ind_len with ⟨r, h_r_eq, h_r_lt, h_indxs_le_r⟩, use [r, h_r_eq],
      split, { apply lt_trans h_r_lt, rw [add_assoc (n_acc + 1) _ _], apply nat.add_lt_add_left, linarith [h_κ], },
      use [h_indxs_le_r], },
  cases ind_cont,
  { left, exact ind_cont },
  right,
  rcases ind_cont with ⟨ind_keys_sorted, ind_squashed_of_length⟩,
    use [ind_keys_sorted],
  apply squashed_of_length_κ _ ind_squashed_of_length, linarith [h_κ],
end

/-
-- Function: squash_dict_inner
-/

/- squash_dict_inner autogenerated specification -/

-- Do not change this definition.
def auto_spec_squash_dict_inner (mem : F → F) (κ : ℕ) (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ dict_diff : π_DictAccess mem, dict_diff = squashed_dict ∧
  ∃ current_access_index : F, current_access_index = mem range_check_ptr ∧
  is_range_checked (rc_bound F) current_access_index ∧
  ∃ ptr_delta : F, ptr_delta = current_access_index * DictAccess.SIZE ∧
  ∃ first_loop_locals : squash_dict_inner.π_LoopLocals mem, first_loop_locals = squash_dict_inner.cast_π_LoopLocals mem (ap + 4) ∧
  first_loop_locals.access_ptr = cast_π_DictAccess mem (dict_accesses + ptr_delta) ∧
  ∃ first_access : π_DictAccess mem, first_access = first_loop_locals.access_ptr ∧
  first_loop_locals.value = first_access.new_value ∧
  first_loop_locals.range_check_ptr = range_check_ptr + 1 ∧
  key = first_access.key ∧
  key = dict_diff.key ∧
  ∃ first_value : F,
  first_value = first_access.prev_value ∧
  first_value = dict_diff.prev_value ∧
  ∃ should_skip_loop : F,
  ((should_skip_loop = 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_squash_dict_inner_block17 mem κ₁ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict ∧
    κ₁ + 11 ≤ κ) ∨
   (should_skip_loop ≠ 0 ∧
    ∃ (κ₁ : ℕ), auto_spec_squash_dict_inner_block30 mem κ₁ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip_loop ρ_range_check_ptr ρ_squashed_dict ∧
    κ₁ + 11 ≤ κ))

/- squash_dict_inner soundness theorem -/

lemma squashed_of_length_block17
  {mem : F → F}
  (κ κ₁ : ℕ)
  (ap range_check_ptr : F)
  (dict_accesses : π_DictAccess mem)
  (dict_accesses_end_minus1 key remaining_accesses : F)
  (squashed_dict : π_DictAccess mem)
  (big_keys ρ_range_check_ptr : F)
  (ρ_squashed_dict : π_DictAccess mem)
  (dict_diff : π_DictAccess mem)
  (h_dict_diff : dict_diff = squashed_dict)
  (cai : F)
  (cai_rc : is_range_checked (rc_bound F) cai)
  (ptr_delta : F)
  (ptr_delta_eq : ptr_delta = cai * ↑DictAccess.SIZE)
  (first_ll : squash_dict_inner.π_LoopLocals mem)
  (first_ll_eq : first_ll = squash_dict_inner.cast_π_LoopLocals mem (ap + 4))
  (h_fll_access_ptr : first_ll.access_ptr =
                        cast_π_DictAccess mem (↑dict_accesses + ptr_delta))
  (first_access : π_DictAccess mem)
  (first_access_eq : first_access = first_ll.access_ptr)
  (h_fll_value : first_ll.value = first_access.new_value)
  (fll_rc_eq : first_ll.range_check_ptr = range_check_ptr + 1)
  (key_fa_eq : key = first_access.key)
  (key_dd_eq : key = dict_diff.key)
  (first_value : F)
  (fv_fa_eq : first_value = first_access.prev_value)
  (fv_dd_eq : first_value = dict_diff.prev_value)
  (should_skip : F)
  (κ_bound : κ ≤ 2 ^ 50)
  (key_bound : big_keys ≠ 0 ∨
                 ∃ (k : ℕ) (H : k < PRIME - κ * rc_bound F), key = ↑k)
  (h_κ₁ : κ₁ + 11 ≤ κ)
  (h_spec17 : spec_squash_dict_inner_block17 mem κ₁ (ap + 7) range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys dict_diff first_value should_skip ρ_range_check_ptr ρ_squashed_dict) :
  squashed_of_length κ dict_accesses dict_accesses_end_minus1
    remaining_accesses
    squashed_dict
    ρ_squashed_dict :=
begin
  have h_zero_add_κ₁_le : 0 + κ₁ ≤ 2 ^ 50,
  { rw [zero_add], apply le_trans _ κ_bound, apply le_trans _ h_κ₁, apply nat.le_add_right, },
  have spec_block17 := h_spec17
                        (by { linarith only [κ_bound, h_κ₁] })
                        (key_bound_κ (show κ₁ ≤ κ, { linarith only [h_κ₁] }) key_bound)
                        first_ll (by { rw first_ll_eq, rw [add_sub_assoc], norm_num, })
                        0
                        h_zero_add_κ₁_le,
  have first_inv : squash_dict_inner_block17_invariant mem 0 first_ll range_check_ptr dict_accesses key squashed_dict dict_diff,
  { split, assumption, use [key_dd_eq], split, { rw [fll_rc_eq, zero_add, nat.cast_one], ring },
    use [[cai]], split, rotate, { rw [zero_add, list.length_singleton] },
    split,
    { split, rw [list.head], rcases cai_rc with ⟨m, m_le, m_cai_eq⟩, use [m, m_le, m_cai_eq.symm],
      split, apply list.chain'_singleton,
      split,
      { rw [list.map_singleton], rw [list.all₂_cons],
        split, { dsimp [access_i], rw [key_fa_eq, first_access_eq, h_fll_access_ptr, ptr_delta_eq] },
        rw [list.all₂_iff_forall], intros x mem_nil, exfalso, exact list.not_mem_nil x mem_nil, },
      apply list.chain'_singleton },
    rw [list.last_singleton, list.head],
    split, { rw [h_fll_access_ptr, ptr_delta_eq, coe_DictAccess_π_cast], },
    dsimp [access_i],
    split, { rw [h_fll_value, first_access_eq, h_fll_access_ptr, ptr_delta_eq], },
    split, { rw [←h_dict_diff, ←key_dd_eq, key_fa_eq, first_access_eq, h_fll_access_ptr, ptr_delta_eq], },
    rw [←h_dict_diff, ←fv_dd_eq, fv_fa_eq, first_access_eq, h_fll_access_ptr, ptr_delta_eq] },
  rcases spec_block17 first_inv
  with ⟨indxs, indxs_ne_nil, ⟨⟨m, m_lt, m_eq⟩, h_chain, h_valid⟩, squashed_indxs, t, t_rc, dict_access_len_t, ⟨r, r_eq, r_lt, indxs_le_r⟩, h_cont⟩,
  have r_lt_prime : r < PRIME,
  { apply lt_trans r_lt, rw [add_assoc, add_comm 1 _, ←add_assoc],
    apply lt_of_le_of_lt (nat.succ_le_succ h_zero_add_κ₁_le), rw [PRIME], norm_num1, },
  rcases h_cont with ⟨ra_eq_indxs, ret_value⟩|⟨key_lt, h_squashed_of_len⟩,
  { -- reached the last key
    use [1], split, { linarith only [h_κ₁] }, use [r], split, { linarith only [r_lt, h_κ₁], }, split, { rw [ret_value, one_mul], }, use [r_eq],
    intros n h_n,
    have h_subseq : list.map (λ (i : F), access_i dict_accesses i) indxs <+ π_array_to_list mem ↑dict_accesses n,
    { exact indxs_are_sublist dict_accesses indxs indxs_ne_nil (by { linarith }) ⟨m, le_of_lt m_lt, m_eq⟩ h_chain ⟨t, t_rc, dict_access_len_t⟩ h_n, },
    split, { apply or.intro_left, dsimp [π_array_to_list], apply le_of_eq, refl, },
    use [[(indxs.map (λ i, access_i dict_accesses i))]],
    split,
    { rw [list.all₂_iff_forall], intros x h_x, rw [list.mem_singleton] at h_x, rw [h_x], exact h_subseq },
    split,
    { dsimp [π_array_to_list], rw [list.forall₂_iff], right,
      use [list.map (access_i dict_accesses) indxs, cast_π_DictAccess mem ↑squashed_dict, list.nil, list.nil],
      split, { rw [coe_cast_π_DictAccess], exact squashed_indxs, },
      split, { rw [list.forall₂_nil_left_iff], }, use [rfl, rfl], },
    rw [list.map_singleton, list.length_map, list.sum_singleton],
    rw [r_eq] at ra_eq_indxs, apply PRIME.nat_coe_field_inj r_lt_prime (lt_of_le_of_lt indxs_le_r r_lt_prime) ra_eq_indxs,
  },
  -- There are more keys
  rcases h_squashed_of_len with ⟨m', m'_lt, r', r'_lt, ret_value, r'_eq, h_squashed⟩,
  use [m' + 1, (by linarith), r' + indxs.length],
  have r_eq_r'_add_indxs : r = r' + indxs.length,
  { rw [sub_eq_iff_eq_add, ←nat.cast_add, r_eq] at r'_eq, apply PRIME.nat_coe_field_inj _ _ r'_eq,
    { rw [PRIME], apply lt_trans r_lt, rw [nat.zero_add], apply lt_trans (nat.add_lt_add_right (show 1 < 11, by { norm_num1 }) _),
      rw [nat.add_comm], apply lt_of_le_of_lt h_κ₁, apply lt_of_le_of_lt κ_bound, norm_num1, },
    have h_κ₁_bound : κ₁ < 2 ^ 50,
      { apply lt_of_lt_of_le _ κ_bound, apply lt_of_lt_of_le _ h_κ₁, apply nat.lt_add_of_pos_right, norm_num1, },
    rw [PRIME], apply lt_trans (nat.add_lt_add_right r'_lt _), apply lt_trans (nat.add_lt_add_left (lt_of_le_of_lt indxs_le_r r_lt) _),
    rw [nat.zero_add], apply lt_trans (nat.add_lt_add_right h_κ₁_bound _), rw [←add_assoc], apply lt_trans (nat.add_lt_add_left h_κ₁_bound _),
    norm_num1, },
  split, { rw [←r_eq_r'_add_indxs], linarith only [r_lt, κ_bound, h_κ₁], },
  split, { rw [ret_value, coe_DictAccess_π_cast, add_assoc, ←nat.cast_add], ring_nf, },
  split, { rw [←r_eq_r'_add_indxs, r_eq], },
  intros n h_n,
  rcases h_squashed n h_n with ⟨h_sorted_keys, seqs, s_subseq, s_squashed, s_sum_remains⟩,
  split, { apply sorted_keys_cons _ _ key_lt h_sorted_keys, rw [key_dd_eq, ←h_dict_diff, coe_cast_π_DictAccess], },
  use [(indxs.map (λ i, access_i dict_accesses i))::seqs],
  split,
  { rw [list.all₂_cons], split,
    { exact indxs_are_sublist dict_accesses indxs indxs_ne_nil (by { linarith }) ⟨m, le_of_lt m_lt, m_eq⟩ h_chain ⟨t, t_rc, dict_access_len_t⟩ h_n, },
    apply s_subseq, },
  split,
  { rw [π_array_to_list], rw [list.forall₂_cons],
    split, { rwa [coe_cast_π_DictAccess], }, exact s_squashed },
  rw [list.map_cons, list.sum_cons, list.length_map, ←s_sum_remains, add_comm],
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_squash_dict_inner
    {mem : F → F}
    (κ : ℕ)
    (ap range_check_ptr : F) (dict_accesses : π_DictAccess mem) (dict_accesses_end_minus1 key remaining_accesses : F) (squashed_dict : π_DictAccess mem) (big_keys ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem)
    (h_auto : auto_spec_squash_dict_inner mem κ ap range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys ρ_range_check_ptr ρ_squashed_dict) :
  spec_squash_dict_inner mem κ range_check_ptr dict_accesses dict_accesses_end_minus1 key remaining_accesses squashed_dict big_keys ρ_range_check_ptr ρ_squashed_dict :=
begin
  rcases h_auto
  with ⟨dict_diff, h_dict_diff, cai, _, cai_rc, ptr_delta, ptr_delta_eq, first_ll, first_ll_eq, h_fll_access_ptr, first_access, first_access_eq,
    h_fll_value, fll_rc_eq, key_fa_eq, key_dd_eq, first_value, fv_fa_eq, fv_dd_eq, should_skip, h_cont⟩,
  intro κ_bound,
  split, { rw [key_dd_eq, h_dict_diff], },
  split, { rcases cai_rc with ⟨m, m_lt, _⟩, apply lt_of_le_of_lt (nat.zero_le _) m_lt, },
  intro key_bound,
  cases h_cont,
  { rcases h_cont with ⟨should_not_skip, κ₁, auto_block17, h_κ₁⟩,
    have spec_block17 := sound_squash_dict_inner_block17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ auto_block17,
    exact squashed_of_length_block17 κ κ₁ _ _ _ _ _ _ _ _ _ _ _ h_dict_diff cai cai_rc ptr_delta ptr_delta_eq first_ll first_ll_eq
            h_fll_access_ptr first_access first_access_eq h_fll_value fll_rc_eq key_fa_eq key_dd_eq first_value fv_fa_eq fv_dd_eq
            should_skip κ_bound key_bound h_κ₁ spec_block17, },
  -- Skipped the loop
  rcases h_cont with ⟨_, κ₁, auto_block30, h_κ₁⟩,
  have spec_block17 := sound_squash_dict_inner_after_loop κ₁ _ _ _ _ _ _ _ _ _ _ _ _ _ auto_block30,
    exact squashed_of_length_block17 κ κ₁ _ _ _ _ _ _ _ _ _ _ _ h_dict_diff cai cai_rc ptr_delta ptr_delta_eq first_ll first_ll_eq
            h_fll_access_ptr first_access first_access_eq h_fll_value fll_rc_eq key_fa_eq key_dd_eq first_value fv_fa_eq fv_dd_eq
            should_skip κ_bound key_bound h_κ₁ spec_block17,
end

/- squash_dict block 14 autogenerated block specification -/

-- Do not change this definition.
def auto_spec_squash_dict_block14 (mem : F → F) (κ : ℕ) (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem) (ptr_diff first_key big_keys n_accesses ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ (κ₁ : ℕ) (range_check_ptr₁ : F) (squashed_dict₁ : π_DictAccess mem), spec_squash_dict_inner mem κ₁ range_check_ptr dict_accesses (dict_accesses_end - 1) first_key n_accesses squashed_dict big_keys range_check_ptr₁ squashed_dict₁ ∧
  κ₁ + 8 ≤ κ ∧
  ρ_range_check_ptr = range_check_ptr₁ ∧
  ρ_squashed_dict = squashed_dict₁

/-
-- Function: squash_dict
-/

/- squash_dict autogenerated specification -/

-- Do not change this definition.
def auto_spec_squash_dict (mem : F → F) (κ : ℕ) (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem) (ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem) : Prop :=
  ∃ ptr_diff : F,
  ptr_diff = dict_accesses_end - dict_accesses ∧
  ((ptr_diff = 0 ∧
    6 ≤ κ ∧
    ρ_range_check_ptr = range_check_ptr ∧
    ρ_squashed_dict = squashed_dict) ∨
   (ptr_diff ≠ 0 ∧
    ∃ first_key : F,
    ∃ big_keys : F,
    ∃ n_accesses : F, n_accesses = ptr_diff / (DictAccess.SIZE : ℤ) ∧
    ((big_keys ≠ 0 ∧
      ∃ range_check_ptr₁ : F, range_check_ptr₁ = range_check_ptr ∧
      ∃ (κ₁ : ℕ), auto_spec_squash_dict_block14 mem κ₁ range_check_ptr₁ dict_accesses dict_accesses_end squashed_dict ptr_diff first_key big_keys n_accesses ρ_range_check_ptr ρ_squashed_dict ∧
      κ₁ + 6 ≤ κ) ∨
     (big_keys = 0 ∧
      first_key = mem range_check_ptr ∧
      is_range_checked (rc_bound F) (first_key) ∧
      ∃ range_check_ptr₁ : F, range_check_ptr₁ = range_check_ptr + 1 ∧
      ∃ (κ₁ : ℕ), auto_spec_squash_dict_block14 mem κ₁ range_check_ptr₁ dict_accesses dict_accesses_end squashed_dict ptr_diff first_key big_keys n_accesses ρ_range_check_ptr ρ_squashed_dict ∧
      κ₁ + 8 ≤ κ))))

/- squash_dict soundness theorem -/

lemma squash_dict_from_inner
    {mem : F → F}
    (κ κ₁': ℕ)
    (range_check_ptr : F)
    (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem)
    (ρ_range_check_ptr : F)
    (ρ_squashed_dict : π_DictAccess mem)
    (n_accesses : F)
    (h_rc_bound : 0 < rc_bound F)
    (h_κ₁' : κ₁' ≤ κ)
    (n_accesses_eq: n_accesses = (↑dict_accesses_end - ↑dict_accesses) / ↑DictAccess.SIZE)
    (h_squashed : squashed_of_length κ₁' dict_accesses (↑dict_accesses_end - 1) n_accesses squashed_dict ρ_squashed_dict):
  spec_squash_dict mem κ range_check_ptr dict_accesses dict_accesses_end squashed_dict ρ_range_check_ptr ρ_squashed_dict :=
begin
  intro κ_bound,
  rcases h_squashed with ⟨m, m_lt, r, r_lt, h_squashed_ret, r_eq, h_squashed⟩,
  have r_lt_κ := lt_of_lt_of_le r_lt h_κ₁',
  have r_mul_lt_prime : r * π_DictAccess.SIZE < PRIME,
  { rw [π_DictAccess.SIZE, PRIME],
    apply lt_of_le_of_lt (nat.mul_le_mul_right _ (le_of_lt (lt_trans r_lt_κ κ_bound))), norm_num1, },
  have r_eq_len : (↑dict_accesses_end : F) - 1 + 1 = ↑dict_accesses + ↑(r * π_DictAccess.SIZE),
  { rw [sub_add_cancel], rw [nat.cast_mul, ←r_eq, n_accesses_eq], rw [DictAccess.SIZE, π_DictAccess.SIZE],
    rw [div_mul_cancel], ring,
    exact PRIME.nat_coe_field_ne_zero (show 3 < PRIME, by { rw [PRIME], norm_num1 }) rfl (show 3 ≠ 0, by { norm_num1 }), },
  use [r, r_lt_κ],
  use [m], split, { apply lt_of_lt_of_le m_lt h_κ₁' },
  split, { rwa [sub_add_cancel] at r_eq_len, },
  rcases h_squashed r ⟨r_mul_lt_prime, r_eq_len⟩ with ⟨sorted_keys, seqs, h_sublists, h_seq_squashed, h_seq_len_sum⟩,
  use [h_squashed_ret, sorted_keys],
  split,
  { rw [finset.ext_iff], intro key, simp only [list.mem_to_finset],
    simp only [key_list, list.mem_map],
    split,
    { intro h_squashed_key, rcases h_squashed_key with ⟨sq, h_sq⟩,
      rw [list.mem_iff_nth_le] at h_sq, rcases h_sq with ⟨⟨i, i_lt, h_i⟩, h_key⟩,
      have i_lt_seqs_len : i < seqs.length, { rwa [list.forall₂.length_eq h_seq_squashed] },
      rcases list.forall₂.nth_le h_seq_squashed i_lt_seqs_len i_lt with ⟨seq_i_nnil, seq_i_key, _⟩,
      use [(seqs.nth_le i i_lt_seqs_len).head],
      split,
      { apply mem_of_head_sublist seq_i_nnil, rw [list.all₂_iff_forall] at h_sublists,
        apply h_sublists (seqs.nth_le i i_lt_seqs_len), rw [list.mem_iff_nth_le], use [i, i_lt_seqs_len], },
      rwa [←h_key, ←h_i], },
    intro h_key_accessed,
    rcases h_key_accessed with ⟨a, a_mem, a_key⟩,
    rw [←(@π_array_to_list_length _ _ _ _ mem (↑dict_accesses : F) r)] at h_seq_len_sum,
    rcases disjoint_sublists_mem
        (squashed_seq_disjoint sorted_keys h_seq_squashed)
        (list.all₂_iff_forall.mp h_sublists)
        h_seq_len_sum.symm
        a
        a_mem
      with ⟨seq, seq_mem, a_mem_seq⟩,
    rw ←a_key, apply squashed_seq_mem_key h_seq_squashed  a seq a_mem_seq seq_mem, },
  intros sq h_sq_mem,

  apply filtered_squashed sorted_keys h_sublists h_seq_squashed _ sq h_sq_mem,
  rw π_array_to_list_length, apply h_seq_len_sum.symm,
end

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_squash_dict
    {mem : F → F}
    (κ : ℕ)
    (range_check_ptr : F) (dict_accesses dict_accesses_end squashed_dict : π_DictAccess mem) (ρ_range_check_ptr : F) (ρ_squashed_dict : π_DictAccess mem)
    (h_auto : auto_spec_squash_dict mem κ range_check_ptr dict_accesses dict_accesses_end squashed_dict ρ_range_check_ptr ρ_squashed_dict) :
  spec_squash_dict mem κ range_check_ptr dict_accesses dict_accesses_end squashed_dict ρ_range_check_ptr ρ_squashed_dict :=
begin
  intro κ_bound,
  rcases h_auto with ⟨ptr_diff, ptr_diff_eq, ptr_diff_zero|ptr_diff_ne_zero⟩,
  { rcases ptr_diff_zero with ⟨ptr_diff_eq_zero, h_κ, _, ρ_squashed_dict_eq⟩,
    use [0], split, { apply lt_of_lt_of_le _ h_κ, norm_num1, },
    use [0], split, { apply lt_of_lt_of_le _ h_κ, norm_num1 },
    split, { rw [zero_mul, nat.cast_zero, add_comm, ←sub_eq_iff_eq_add], rw [←ptr_diff_eq, ptr_diff_eq_zero], },
    split, { rw [zero_mul, nat.cast_zero, add_zero, ρ_squashed_dict_eq] },
    split, { left, rw [π_array_to_list_length], exact nat.zero_le _ },
    split, { rw [π_array_to_list_nil, π_array_to_list_nil], },
    intros s s_mem, rw [π_array_to_list_nil] at s_mem, exfalso, apply list.not_mem_nil s s_mem, },
  rcases ptr_diff_ne_zero with ⟨ptr_diff_ne_zero, first_key, big_keys, n_accesses, n_accesses_eq, with_big_keys|no_big_keys⟩,
  { rcases with_big_keys with ⟨big_keys_ne_zero, range_check_ptr₁, rc_eq, κ₁, h_block14, h_κ₁⟩,
    rcases h_block14 with ⟨κ₁', ret_range_check_ptr, ret_squashed_dict, spec_inner, h_κ₁', h_ret_rc, h_ret_squashed_dict⟩,
    have h_κ₁'_le : κ₁' ≤ κ, { apply le_trans (le_trans (nat.le_add_right _ _) h_κ₁') (le_trans (nat.le_add_right _ _) h_κ₁), },
    have κ₁'_bound : κ₁' < 2 ^ 50, { apply lt_of_le_of_lt _ κ_bound, apply  h_κ₁'_le },
    rcases spec_inner (le_of_lt κ₁'_bound) with ⟨h_first_key, h_rc_bound, h_squashed_if_keys⟩,
    have h_squashed := h_squashed_if_keys (or.intro_left _ big_keys_ne_zero),
    rw [←h_ret_squashed_dict] at h_squashed,
    norm_cast at n_accesses_eq, rw [ptr_diff_eq] at n_accesses_eq,
    apply squash_dict_from_inner κ κ₁' range_check_ptr _ _ _ ρ_range_check_ptr _ _ h_rc_bound h_κ₁'_le n_accesses_eq h_squashed κ_bound, },
  rcases no_big_keys with ⟨big_keys_eq_zero, _, first_key_rc, range_check_ptr₁, _, κ₁, h_block14, h_κ₁⟩,
  rcases h_block14 with ⟨κ₁', ret_range_check_ptr, ret_squashed_dict, spec_inner, h_κ₁', h_ret_rc, h_ret_squashed_dict⟩,
  have h_κ₁'_le : κ₁' ≤ κ, { apply le_trans (le_trans (nat.le_add_right _ _) h_κ₁') (le_trans (nat.le_add_right _ _) h_κ₁), },
  have κ₁'_bound : κ₁' < 2 ^ 50, { apply lt_of_le_of_lt _ κ_bound, apply  h_κ₁'_le },
  rcases first_key_rc with ⟨k, k_lt, k_eq⟩,
  have k_bound : k < PRIME - κ₁' * rc_bound F,
  { have κ₁'_mul_rc_le : κ₁' * rc_bound F ≤ 2 ^ 50 * 2 ^ 128,
    { apply le_trans (nat.mul_le_mul_right _ (le_of_lt κ₁'_bound)), apply le_trans (nat.mul_le_mul_left _ (rc_bound_hyp F)), apply le_of_eq, refl, },
    rw PRIME, apply lt_of_lt_of_le k_lt, rw [nat.le_sub_iff_right _], apply le_trans (nat.add_le_add_right (rc_bound_hyp F) _),
    apply le_trans (nat.add_le_add_left κ₁'_mul_rc_le _), norm_num1,
    apply le_trans κ₁'_mul_rc_le, norm_num1, },
  rcases spec_inner (le_of_lt κ₁'_bound) with ⟨h_first_key, h_rc_bound, h_squashed_if_keys⟩,
  have h_squashed := h_squashed_if_keys (or.intro_right _ ⟨k, k_bound, k_eq⟩),
  rw [←h_ret_squashed_dict] at h_squashed,
  norm_cast at n_accesses_eq, rw [ptr_diff_eq] at n_accesses_eq,
  apply squash_dict_from_inner κ κ₁' range_check_ptr _ _ _ ρ_range_check_ptr _ _ h_rc_bound h_κ₁'_le n_accesses_eq h_squashed κ_bound,
end


end starkware.cairo.common.squash_dict
