/-
  Specifications file for dict_access_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.dict_access

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def φ_DictAccess.key := 0
@[reducible] def φ_DictAccess.prev_value := 1
@[reducible] def φ_DictAccess.new_value := 2
@[ext] structure DictAccess (mem : F → F) :=
  (key : F) (prev_value : F) (new_value : F)
@[reducible] def DictAccess.SIZE := 3
@[ext] structure π_DictAccess (mem : F → F) :=
  (σ_ptr : F) (key : F) (prev_value : F) (new_value : F)
  (h_key : key = mem (σ_ptr + φ_DictAccess.key))
  (h_prev_value : prev_value = mem (σ_ptr + φ_DictAccess.prev_value))
  (h_new_value : new_value = mem (σ_ptr + φ_DictAccess.new_value))
@[reducible] def π_DictAccess.SIZE := 3
@[reducible] def cast_DictAccess (mem : F → F) (p : F) : DictAccess mem := {
  key := mem (p + φ_DictAccess.key),
  prev_value := mem (p + φ_DictAccess.prev_value),
  new_value := mem (p + φ_DictAccess.new_value)
}
@[reducible] def cast_π_DictAccess (mem : F → F) (p : F) : π_DictAccess mem := {
  σ_ptr := p,
  key := mem (p + φ_DictAccess.key),
  prev_value := mem (p + φ_DictAccess.prev_value),
  new_value := mem (p + φ_DictAccess.new_value),
  h_key := rfl,
  h_prev_value := rfl,
  h_new_value := rfl
}
instance π_DictAccess_to_F {mem : F → F} : has_coe (π_DictAccess mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_DictAccess_ptr {mem : F → F} {x y : π_DictAccess mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_key, y.h_key, h_p] },
  try { ext }, repeat { rw [x.h_prev_value, y.h_prev_value, h_p] },
  try { ext }, repeat { rw [x.h_new_value, y.h_new_value, h_p] }
end
lemma eq_DictAccess_π_cast {mem : F → F} {x y : F} :
  cast_π_DictAccess mem x = cast_π_DictAccess mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_DictAccess_π_ptr_cast {mem : F → F} {x : π_DictAccess mem} {y : F} :
  x = cast_π_DictAccess mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_DictAccess_π_cast {mem : F → F} {x : F} :(↑(cast_π_DictAccess mem x) : F) = x := rfl
-- End of automatically generated lemmas
lemma coe_cast_π_DictAccess {mem : F → F} { x : π_DictAccess mem } : cast_π_DictAccess mem ↑x = x :=
begin
  apply eq_DictAccess_ptr, dsimp [cast_π_DictAccess], refl,
end
instance decidable_eq_π_DictAccess {mem : F → F} : decidable_eq (π_DictAccess mem)
:= by tactic.mk_dec_eq_instance

-- End of main scope definitions.


end starkware.cairo.common.dict_access
