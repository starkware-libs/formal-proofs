import field_theory.finite.basic
import data.bitvec.basic
import algebra.group_with_zero
import tactic.omega

open_locale big_operators

/-
some generic simplifier rules
-/

lemma add_neg_eq_sub {G : Type*} [add_group G] (a b : G) : a + -b = a - b := by rw sub_eq_add_neg

lemma sub_add_eq_add_neg_add {G : Type*} [add_group G] (a b c : G) :
  a - b + c = a + (-b + c) := by rw [sub_eq_add_neg, add_assoc]

/-
bool
-/

attribute [simp] bool.to_nat

/-
int
-/

namespace int

lemma abs_le_of_dvd {i j : int} (h : i ∣ j) (h' : 0 < j) : abs i ≤ j :=
int.le_of_dvd h' ((abs_dvd _ _).mpr h)

theorem modeq_iff_sub_mod_eq_zero {i j m : ℤ} : i ≡ j [ZMOD m] ↔ (i - j) % m = 0 :=
by rw [int.modeq_iff_dvd, ←neg_sub, dvd_neg, int.dvd_iff_mod_eq_zero]

theorem modeq_zero_iff {i m : ℤ} : i ≡ 0 [ZMOD m] ↔ i % m = 0 :=
by rw [modeq_iff_sub_mod_eq_zero, sub_zero]

end int

/-
For casts from `nat` to `int`, `push_neg` does not always do the right thing on
large numbers. This is a more restricted version.
-/

mk_simp_attribute int_cast_simps "rules for pushing integer casts downwards"

attribute [int_cast_simps] int.coe_nat_zero int.coe_nat_one int.coe_nat_bit0 int.coe_nat_bit1
  int.coe_nat_add int.coe_nat_pow
  int.cast_add int.cast_mul int.cast_sub int.cast_bit0 int.cast_bit1 int.cast_zero int.cast_one

meta def simp_int_casts : tactic unit := `[ simp only with int_cast_simps ]

/-
option
-/

namespace option

def agrees {α : Type*} : option α → α → Prop
| (some a) b := a = b
| none     _ := true

def fn_extends {α β : Type*} (f : α → β) (f' : α → option β) : Prop :=
∀ x, (f' x).agrees (f x)

theorem eq_of_fn_extends {α β : Type*} {f : α → β} {f' : α → option β}
  (h : fn_extends f f') {a : α} {b : β} (h' : f' a = some b) : f a = b :=
by { symmetry, have := h a, rwa h' at this }

lemma agrees_iff_of_eq_some {T : Type*} {a : option T} {b : T} (h : a = some b) (c : T) :
  a.agrees c ↔ c = b :=
by { rw h, simp [option.agrees], split; apply eq.symm }

lemma some_if {T : Type*} (P : Prop) [decidable P] (a b : T) :
  option.some (if P then a else b) = if P then option.some a else option.some b :=
by { by_cases h : P, { simp [if_pos h] }, simp [if_neg h] }

end option

/-
vector
-/

namespace vector

variables {α : Type*}

theorem reverse_cons {n : ℕ} (a : α) (v : vector α n) :
  reverse (cons a v) = append (reverse v) (cons a nil) :=
by { apply to_list_injective, simp [reverse] }

theorem append_nil {n : ℕ} (v : vector α n) :
  append v nil = v :=
by { apply to_list_injective, simp }

end vector

/-
fin
-/

namespace fin

theorem eq_cast_succ_or_eq_last {n : ℕ} (i : fin (n + 1)) :
  (∃ j, i = cast_succ j) ∨ i = last n :=
begin
  cases (lt_or_eq_of_le (le_last i)) with h h,
  { use ⟨i.1, h⟩, ext, refl },
  right, exact h
end

lemma exists_fin_cast_succ {n : ℕ} {P : fin (n + 1) → Prop} :
  (∃ i, P i) ↔ ((∃ i : fin n, P i.cast_succ) ∨ P (fin.last n)) :=
begin
  split,
  { rintros ⟨i, hi⟩,
    rcases eq_cast_succ_or_eq_last i with ⟨j, rfl⟩ | rfl,
    { left, use j, assumption },
    right, assumption },
  rintros (⟨i, h⟩ | h); exact exists.intro _ h
end

@[simp] def rev {n : ℕ} : fin n → fin n
| ⟨i, h⟩ := ⟨n - i.succ, by omega⟩

@[simp] theorem rev_rev {n : ℕ} (i : fin n) : rev (rev i) = i :=
by { cases i with i h, unfold rev, ext, dsimp, omega }

@[simp] theorem coe_rev {n : ℕ} (i : fin n) : (i.rev : ℕ) = n - i.succ :=
by { cases i with i h, refl }

@[simp] theorem rev_zero {n : ℕ} : (0 : fin (n + 1)).rev = last n :=
by refl

@[simp] theorem rev_last {n : ℕ} : (last n).rev = 0 :=
by { rw [←rev_zero, rev_rev] }

theorem cast_succ_add_one_rev {n : ℕ} {i : fin n} :
  (cast_succ i + 1).rev + 1 = (cast_succ i).rev :=
begin
  cases i with i' h',
  ext,
  simp [coe_add, coe_rev, coe_one'],
  rw [@nat.mod_eq_of_lt (i' + 1), nat.mod_eq_of_lt]; omega
end

theorem cast_succ_rev {n : ℕ} (i : fin n) :
  i.rev.cast_succ = i.succ.rev :=
by { cases i with i' h', ext, simp }

theorem rev_cast_succ {n : ℕ} (i : fin n) :
  i.cast_succ.rev = i.rev.succ :=
by conv { to_lhs, rw [← rev_rev i, cast_succ_rev, rev_rev] }

theorem rev_lt_rev_iff {n : ℕ} (i j : fin n) : rev i < rev j ↔ j < i :=
begin
  cases i with i ih, cases j with j jh, rw [rev, rev],
  transitivity,
  apply tsub_lt_tsub_iff_left_of_le (nat.succ_le_of_lt ih),
  exact ⟨nat.lt_of_succ_lt_succ, nat.succ_lt_succ⟩
end

theorem rev_le_rev_iff {n : ℕ} (i j : fin n) : rev i ≤ rev j ↔ j ≤ i :=
begin
  cases i with i ih, cases j with j jh, rw [rev, rev],
  transitivity,
  apply tsub_le_tsub_iff_left (nat.succ_le_of_lt jh),
  apply nat.succ_le_succ_iff
end

theorem add_one_le_of_lt {n : ℕ} {i j : fin (n + 1)} (h : i < j) : i + 1 ≤ j :=
begin
  cases i with i hi,
  cases j with j hj,
  simp [fin.le_def, fin.coe_add, fin.coe_one'],
  rw nat.mod_eq_of_lt,
  { apply nat.succ_le_of_lt h },
  apply lt_of_le_of_lt (nat.succ_le_of_lt h) hj
end

theorem eq_zero_of_le_zero {n : ℕ} {i : fin (n + 1)} (h : i ≤ 0) : i = 0 :=
by { cases i, ext, apply nat.eq_zero_of_le_zero h }

theorem of_le_succ {n : ℕ} {i : fin (n + 1)} {j : fin n} (h : i ≤ j.succ) :
  i ≤ j.cast_succ ∨ i = j.succ :=
begin
  cases i, cases j,
  simp [fin.succ] at *,
  exact nat.of_le_succ h
end

theorem le_of_lt_succ {n : ℕ} {i : fin (n + 1)} {j : fin n} (h : i < j.succ) : i ≤ j.cast_succ :=
by { cases i, cases j, exact nat.le_of_lt_succ h}

theorem cast_succ_lt_succ_iff {n : ℕ} (i j : fin n) :
  i.cast_succ < j.succ ↔ i.cast_succ ≤ j.cast_succ :=
by { cases i, cases j, apply nat.lt_succ_iff }

@[simp] theorem cast_succ_le_cast_succ_iff {n : ℕ} (i j : fin n) :
  i.cast_succ ≤ j.cast_succ ↔ i ≤ j :=
by { cases i, cases j, refl }

theorem one_eq_succ_zero {n : ℕ} : (1 : fin (n + 2)) = fin.succ 0 := rfl

theorem le_zero_iff {n : ℕ} (i : fin (n + 1)) : i ≤ 0 ↔ i = 0 :=
by { rw [fin.ext_iff, fin.le_def], cases i, apply le_zero_iff }

lemma last_zero : fin.last 0 = 0 :=
by { ext, refl }

/-- This lemma is useful for rewriting `fin (n + 1)` as `fin (m + j + 1)`,
    given `i : fin (n + 1)` and `m = ↑i`. -/
lemma exists_eq_add {n : ℕ} (i : fin (n + 1)) : ∃ m j, m = ↑i ∧ n = m + j :=
begin
  cases nat.exists_eq_add_of_le (nat.le_of_lt_succ i.2) with j hj,
  use [↑i, j, rfl, hj]
end

def cast_offset {n : ℕ} (m : ℕ) (i : fin n) : fin (m + n) :=
⟨m + ↑i, add_lt_add_left i.is_lt _⟩

def cast_offset' {n : ℕ} (m : ℕ) (j : fin (n + 1)) : fin (m + n + 1) :=
@cast_offset (n + 1) m j

theorem cast_succ_cast_offset {n m : ℕ} (i : fin n) :
  fin.cast_offset m i.cast_succ = (fin.cast_offset m i).cast_succ :=
by { cases i, refl }

theorem succ_cast_offset {n m : ℕ} (i : fin n) :
  fin.cast_offset m i.succ = (fin.cast_offset m i).succ :=
by {cases i, refl }

section

variable {n : ℕ}

def range (i : fin (n + 1)) : finset (fin n) :=
finset.univ.filter (λ j, j.cast_succ < i)

@[simp] theorem mem_range (i : fin n) (j : fin (n + 1)) : i ∈ range j ↔ i.cast_succ < j :=
by simp [range]

@[simp] theorem range_zero : range (0 : fin (n + 1)) = ∅ :=
by { ext i, simp [range, fin.zero_le] }

@[simp] theorem range_one : range (1 : fin (n + 2)) = {(0 : fin (n + 1))} :=
begin
  ext i,
  rw [mem_range, finset.mem_singleton, one_eq_succ_zero, cast_succ_lt_succ_iff,
       cast_succ_le_cast_succ_iff, le_zero_iff]
end

theorem range_succ (i : fin n) : range i.succ = insert i (range i.cast_succ) :=
begin
  ext j,
  rw [mem_range, finset.mem_insert, mem_range, cast_succ_lt_succ_iff, le_iff_lt_or_eq,
       cast_succ_inj, or.comm]
end

theorem range_last : range (fin.last n) = finset.univ :=
by { ext i, simp [mem_range, cast_succ_lt_last] }

@[simp] theorem not_mem_range_self (i : fin n) : i ∉ range i.cast_succ :=
by { rw mem_range, apply lt_irrefl }

@[simp] theorem self_mem_range_succ (i: fin n) : i ∈ range (i.succ) :=
by { rw mem_range, apply cast_succ_lt_succ }

@[simp] theorem range_subset {i j : fin (n + 1)} : range i ⊆ range j ↔ i ≤ j :=
begin
  rw [finset.subset_iff], split,
  { intro h,
    by_cases h' : i = 0, { rw h', apply zero_le },
    have : i.pred h' ∈ range i,
    { rw mem_range, conv {to_rhs, rw ←succ_pred i h'},
      rw cast_succ_lt_succ_iff },
    specialize h this,
    rwa [mem_range, cast_succ_lt_iff_succ_le, succ_pred i h'] at h },
  intros h k,
  rw [mem_range, mem_range],
  intro h',
  exact lt_of_lt_of_le h' h
end

section

variables {β : Type*} [comm_monoid β]

lemma prod_range_zero (f : fin n → β) :
 (∏ k in range 0, f k) = 1 :=
by rw [range_zero, finset.prod_empty]

lemma sum_range_zero {β : Type*} [add_comm_monoid β] (f : fin n → β) :
 (∑ k in range 0, f k) = 0 :=
by rw [range_zero, finset.sum_empty]

@[to_additive]
lemma prod_range_one (f : fin (n + 1) → β) :
  (∏ k in range 1, f k) = f 0 :=
by { rw [range_one], rw finset.prod_singleton }

@[to_additive]
lemma prod_range_succ (f : fin n → β) (i : fin n) :
  (∏ x in range i.succ, f x) = f i * (∏ x in range i.cast_succ, f x) :=
by rw [range_succ, finset.prod_insert (not_mem_range_self i)]

lemma prod_range_succ' (f : fin (n + 1) → β) (i : fin (n + 1)) :
  (∏ k in range i.succ, f k) = (∏ k in range i, f k.succ) * f 0 :=
begin
  apply fin.induction_on i,
  { rw [prod_range_succ, cast_succ_zero, prod_range_zero, prod_range_zero, mul_comm] },
  intros i' ih,
  rw [prod_range_succ (λ k, f (k.succ)), mul_assoc, ←ih, succ_cast_succ, prod_range_succ]
end

lemma sum_range_succ'  {β : Type*} [add_comm_monoid β] (f : fin (n + 1) → β) (i : fin (n + 1)) :
  (∑ k in range i.succ, f k) = (∑ k in range i, f k.succ) + f 0 :=
begin
  apply fin.induction_on i,
  { rw [sum_range_succ, cast_succ_zero, sum_range_zero, sum_range_zero, add_comm] },
  intros i' ih,
  rw [sum_range_succ (λ k, f (k.succ)), add_assoc, ←ih, succ_cast_succ, sum_range_succ]
end

end

/- currently not used, but maybe useful?

theorem add_one_eq_of_lt_last {n : ℕ} {i : fin (n + 1)} (h : i < last n) :
  i + 1 = ⟨i.1 + 1, nat.succ_lt_succ h⟩ :=
begin
  cases i with i' h', ext,
  simp [fin.coe_add, fin.coe_one'],
  apply nat.mod_eq_of_lt,
  apply nat.succ_lt_succ,
  apply h
end

theorem lt_of_add_one_le {n : ℕ} {i j : fin (n + 1)} (h : i < last n) (h' : i + 1 ≤ j) :
  i < j :=
begin
  cases i with i hi,
  cases j with j hj,
  simp [fin.le_def, fin.coe_add, fin.coe_one'],
  rw add_one_eq_of_lt_last h at h',
  apply nat.lt_of_succ_le h'
end

theorem add_one_rev_lt_last {n : ℕ} {i : fin (n + 1)} (h : i < fin.last n) :
  (i + 1).rev < fin.last n :=
begin
  rw [add_one_eq_of_lt_last h, rev, lt_def],
  dsimp [fin.last],
  rw nat.succ_sub_succ,
  apply nat.sub_lt,
  { apply lt_of_le_of_lt (nat.zero_le _) h },
  apply nat.zero_lt_succ
end
-/

end

end fin

/-
bitvec
-/

namespace bitvec

variables {n : ℕ} (b : bitvec n)

/-- bitvec's `to_nat` has bit 0 as msb, but the Cairo convention is the reverse. -/
def to_natr : ℕ := bitvec.to_nat b.reverse

def to_biased_16 : ℤ := (b.to_natr : int) - 2^15

theorem to_natr_lt : b.to_natr < 2^n := to_nat_lt _

theorem to_nat_le : b.to_nat ≤ 2^n - 1 :=
begin
  apply le_tsub_of_add_le_right,
  apply nat.succ_le_of_lt,
  apply to_nat_lt
end

theorem to_natr_le : b.to_natr ≤ 2^n - 1 := to_nat_le _

theorem to_nat_inj {n : ℕ} {b1 b2 : bitvec n} (h : b1.to_nat = b2.to_nat) : b1 = b2 :=
by rw [←of_nat_to_nat b1, h, of_nat_to_nat b2]

theorem to_natr_inj {n : ℕ} {b1 b2 : bitvec n} (h : b1.to_natr = b2.to_natr) : b1 = b2 :=
begin
  suffices : b1.reverse.reverse = b2.reverse.reverse,
    by rwa [vector.reverse_reverse, vector.reverse_reverse] at this,
  rw to_nat_inj h,
end

def of_natr (n k : ℕ) : bitvec n := (bitvec.of_nat n k).reverse

theorem to_natr_of_natr {k n : ℕ} : (bitvec.of_natr k n).to_natr = n % 2 ^ k :=
by rw [of_natr, to_natr, vector.reverse_reverse, to_nat_of_nat]

theorem singleton_to_nat (u : bool) : bitvec.to_nat (u ::ᵥ vector.nil) = u.to_nat :=
by simp [bitvec.to_nat, bits_to_nat, add_lsb]

end bitvec

/-
Casting nat and int to a ring with positive characteristic.
-/

namespace nat

variables {R : Type*} [ring R]

theorem cast_inj_of_lt_char' {a b : ℕ} (hlt : a ≤ b) (h : b < ring_char R)
  (h : (a : R) = (b : R)) : a = b :=
begin
  suffices : b - a = 0,
  { apply le_antisymm hlt, rwa ←nat.sub_eq_zero_iff_le },
  have h1 : ((b - a : ℕ) : R) = 0,
  { rw [nat.cast_sub hlt, h, sub_self] },
  rw [ring_char.spec] at h1,
  suffices : ¬ b - a > 0, linarith,
  assume : b - a > 0,
  have : ring_char R ≤ b - a, from nat.le_of_dvd this h1,
  have : b - a ≤ b, from tsub_le_self,
  linarith
end

theorem cast_inj_of_lt_char {a b : ℕ} (ha : a < ring_char R) (hb : b < ring_char R)
  (h : (a : R) = (b : R)) : a = b :=
begin
  wlog h' : a ≤ b,
  exact cast_inj_of_lt_char' h' hb h
end

end nat

namespace int

theorem cast_ne_zero_of_abs_lt_char {R : Type*} [ring R]
    {x : ℤ} (h0 : abs x ≠ 0) (h1 : abs x < ring_char R) :
  (x : R) ≠ 0 :=
begin
  have h3 : (abs x).to_nat < ring_char R,
  { rwa [←int.to_nat_of_nonneg (abs_nonneg x), int.coe_nat_lt_coe_nat_iff] at h1 },
  intro h, apply h0,
  suffices : (abs x).to_nat = 0,
  { rw [←int.to_nat_of_nonneg (abs_nonneg x), this], refl },
  apply nat.cast_inj_of_lt_char h3 (lt_of_le_of_lt (nat.zero_le _) h3),
  have : ((abs x).to_nat : R) = (((abs x).to_nat : ℤ) : R), by simp [-int.to_nat_of_nonneg],
  apply eq.trans this,
  rw [int.to_nat_of_nonneg (abs_nonneg x)],
  cases (le_or_gt 0 x) with h4 h4,
  { rw [abs_of_nonneg h4, h, nat.cast_zero] },
  rw abs_of_neg h4, simp [h]
end

lemma cast_inj_of_lt_char {R : Type*} [ring R] {i j : ℤ} {p : ℕ}
  (charR : char_p R p) (h : (i : R) = (j : R)) (h' : abs (j - i) < p) : i = j :=
begin
  symmetry,
  apply eq_of_sub_eq_zero,
  rw ←abs_eq_zero,
  by_contradiction nez,
  apply not_le_of_lt h',
  apply int.le_of_dvd,
  apply lt_of_le_of_ne (abs_nonneg _) (ne.symm nez),
  rw dvd_abs,
  have: (↑(j - i) : R) = 0, by simp [h],
  exact (char_p.int_cast_eq_zero_iff R p _).mp this
end

lemma cast_eq_zero_of_lt_char (R : Type*) [ring R] {i : ℤ} (p : ℕ)
  [charR : char_p R p] (h : (i : R) = 0) (h' : abs i < p) : i = 0 :=
begin
  have := @int.cast_inj_of_lt_char _ _  i 0 p charR,
  simp at this,
  apply this; assumption
end

end int

/-
Ring theory.
-/

open finset polynomial

section

variables {R : Type*} [comm_semiring R]

@[simp] lemma eval_multiset_prod (m : multiset (polynomial R)) (z : R) :
  eval z m.prod = (m.map (eval z)).prod :=
(@multiset.prod_hom _ R _ _ m _ _ (eval_ring_hom z)).symm

lemma nat_degree_add (p q : polynomial R) :
  nat_degree (p + q) ≤ max (nat_degree p) (nat_degree q) :=
begin
  by_cases hp : p = 0, { simp [hp] },
  by_cases hq : q = 0, { simp [hq] },
  by_cases hpq : p + q = 0, { simp [hpq] },
  have := degree_add_le p q,
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq, degree_eq_nat_degree hpq] at this,
  simp only [with_bot.coe_le_coe, le_max_iff] at this ⊢,
  exact this
end

end

section

variables {R : Type*} [comm_ring R] [is_domain R]

private lemma multiset_prod_X_sub_C_aux (m : multiset R) :
  (m.map (λ r, X - C r)).prod ≠ 0 ∧ (m.map (λ r, X - C r)).prod.nat_degree = m.card :=
begin
  apply multiset.induction_on m, { simp },
  intros a m ih,
  have h : X - C a ≠ 0 := X_sub_C_ne_zero a,
  rw [multiset.map_cons, multiset.prod_cons, multiset.card_cons],
  split, { exact mul_ne_zero h ih.1 },
  rw [nat_degree_mul h ih.1, ih.2], simp [add_comm]
end

lemma multiset_prod_X_sub_C_ne_zero (m : multiset R) :
  (m.map (λ r, X - C r)).prod ≠ 0
:= (multiset_prod_X_sub_C_aux m).1

lemma nat_degree_multiset_prod_X_sub_C (m : multiset R) :
  (m.map (λ r, X - C r)).prod.nat_degree = m.card
:= (multiset_prod_X_sub_C_aux m).2

lemma degree_multiset_prod_X_sub_C_ne_zero (m : multiset R) :
  (m.map (λ r, X - C r)).prod.degree = m.card :=
by { rw [degree_eq_nat_degree (multiset_prod_X_sub_C_ne_zero m),
           (nat_degree_multiset_prod_X_sub_C m)] }

lemma multiset_prod_X_sub_C_roots (m : multiset R) : (m.map (λ r, X - C r)).prod.roots = m :=
begin
  have h' : (0 : polynomial R) ∉ multiset.map (λ (r : R), X - C r) m,
  { rw [multiset.mem_map], rintros ⟨r, _, h''⟩, apply X_sub_C_ne_zero _ h'' },
  rw [roots_multiset_prod _ h', multiset.bind, multiset.join], simp
end

end

namespace tactic
setup_tactic_parser

def loc_target : loc := loc.ns [none]

meta def mk_simp_arg_list : list pexpr → list simp_arg_type
| []        := []
| (p :: ps) := simp_arg_type.expr p :: mk_simp_arg_list ps

end tactic
