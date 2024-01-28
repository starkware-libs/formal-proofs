/-
  Specifications file for bigint3_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.cairo_secp.bigint3

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def φ_BigInt3.d0 := 0
@[reducible] def φ_BigInt3.d1 := 1
@[reducible] def φ_BigInt3.d2 := 2
@[ext] structure BigInt3 (mem : F → F) :=
  (d0 : F) (d1 : F) (d2 : F)
attribute [derive decidable_eq] BigInt3
@[reducible] def BigInt3.SIZE := 3
@[ext] structure π_BigInt3 (mem : F → F) :=
  (σ_ptr : F) (d0 : F) (d1 : F) (d2 : F)
  (h_d0 : d0 = mem (σ_ptr + φ_BigInt3.d0))
  (h_d1 : d1 = mem (σ_ptr + φ_BigInt3.d1))
  (h_d2 : d2 = mem (σ_ptr + φ_BigInt3.d2))
@[reducible] def π_BigInt3.SIZE := 3
@[reducible] def cast_BigInt3 (mem : F → F) (p : F) : BigInt3 mem := {
  d0 := mem (p + φ_BigInt3.d0),
  d1 := mem (p + φ_BigInt3.d1),
  d2 := mem (p + φ_BigInt3.d2)
}
@[reducible] def cast_π_BigInt3 (mem : F → F) (p : F) : π_BigInt3 mem := {
  σ_ptr := p,
  d0 := mem (p + φ_BigInt3.d0),
  d1 := mem (p + φ_BigInt3.d1),
  d2 := mem (p + φ_BigInt3.d2),
  h_d0 := rfl,
  h_d1 := rfl,
  h_d2 := rfl
}
instance π_BigInt3_to_F {mem : F → F} : has_coe (π_BigInt3 mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_BigInt3_ptr {mem : F → F} {x y : π_BigInt3 mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_d0, y.h_d0, h_p] },
  try { ext }, repeat { rw [x.h_d1, y.h_d1, h_p] },
  try { ext }, repeat { rw [x.h_d2, y.h_d2, h_p] }
end
lemma eq_BigInt3_π_cast {mem : F → F} {x y : F} :
  cast_π_BigInt3 mem x = cast_π_BigInt3 mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_BigInt3_π_ptr_cast {mem : F → F} {x : π_BigInt3 mem} {y : F} :
  x = cast_π_BigInt3 mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_BigInt3_π_cast {mem : F → F} {x : F} :(↑(cast_π_BigInt3 mem x) : F) = x := rfl
@[reducible] def φ_UnreducedBigInt3.d0 := 0
@[reducible] def φ_UnreducedBigInt3.d1 := 1
@[reducible] def φ_UnreducedBigInt3.d2 := 2
@[ext] structure UnreducedBigInt3 (mem : F → F) :=
  (d0 : F) (d1 : F) (d2 : F)
@[reducible] def UnreducedBigInt3.SIZE := 3
@[ext] structure π_UnreducedBigInt3 (mem : F → F) :=
  (σ_ptr : F) (d0 : F) (d1 : F) (d2 : F)
  (h_d0 : d0 = mem (σ_ptr + φ_UnreducedBigInt3.d0))
  (h_d1 : d1 = mem (σ_ptr + φ_UnreducedBigInt3.d1))
  (h_d2 : d2 = mem (σ_ptr + φ_UnreducedBigInt3.d2))
@[reducible] def π_UnreducedBigInt3.SIZE := 3
@[reducible] def cast_UnreducedBigInt3 (mem : F → F) (p : F) : UnreducedBigInt3 mem := {
  d0 := mem (p + φ_UnreducedBigInt3.d0),
  d1 := mem (p + φ_UnreducedBigInt3.d1),
  d2 := mem (p + φ_UnreducedBigInt3.d2)
}
@[reducible] def cast_π_UnreducedBigInt3 (mem : F → F) (p : F) : π_UnreducedBigInt3 mem := {
  σ_ptr := p,
  d0 := mem (p + φ_UnreducedBigInt3.d0),
  d1 := mem (p + φ_UnreducedBigInt3.d1),
  d2 := mem (p + φ_UnreducedBigInt3.d2),
  h_d0 := rfl,
  h_d1 := rfl,
  h_d2 := rfl
}
instance π_UnreducedBigInt3_to_F {mem : F → F} : has_coe (π_UnreducedBigInt3 mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_UnreducedBigInt3_ptr {mem : F → F} {x y : π_UnreducedBigInt3 mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_d0, y.h_d0, h_p] },
  try { ext }, repeat { rw [x.h_d1, y.h_d1, h_p] },
  try { ext }, repeat { rw [x.h_d2, y.h_d2, h_p] }
end
lemma eq_UnreducedBigInt3_π_cast {mem : F → F} {x y : F} :
  cast_π_UnreducedBigInt3 mem x = cast_π_UnreducedBigInt3 mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_UnreducedBigInt3_π_ptr_cast {mem : F → F} {x : π_UnreducedBigInt3 mem} {y : F} :
  x = cast_π_UnreducedBigInt3 mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_UnreducedBigInt3_π_cast {mem : F → F} {x : F} :(↑(cast_π_UnreducedBigInt3 mem x) : F) = x := rfl
@[reducible] def φ_SumBigInt3.d0 := 0
@[reducible] def φ_SumBigInt3.d1 := 1
@[reducible] def φ_SumBigInt3.d2 := 2
@[ext] structure SumBigInt3 (mem : F → F) :=
  (d0 : F) (d1 : F) (d2 : F)
@[reducible] def SumBigInt3.SIZE := 3
@[ext] structure π_SumBigInt3 (mem : F → F) :=
  (σ_ptr : F) (d0 : F) (d1 : F) (d2 : F)
  (h_d0 : d0 = mem (σ_ptr + φ_SumBigInt3.d0))
  (h_d1 : d1 = mem (σ_ptr + φ_SumBigInt3.d1))
  (h_d2 : d2 = mem (σ_ptr + φ_SumBigInt3.d2))
@[reducible] def π_SumBigInt3.SIZE := 3
@[reducible] def cast_SumBigInt3 (mem : F → F) (p : F) : SumBigInt3 mem := {
  d0 := mem (p + φ_SumBigInt3.d0),
  d1 := mem (p + φ_SumBigInt3.d1),
  d2 := mem (p + φ_SumBigInt3.d2)
}
@[reducible] def cast_π_SumBigInt3 (mem : F → F) (p : F) : π_SumBigInt3 mem := {
  σ_ptr := p,
  d0 := mem (p + φ_SumBigInt3.d0),
  d1 := mem (p + φ_SumBigInt3.d1),
  d2 := mem (p + φ_SumBigInt3.d2),
  h_d0 := rfl,
  h_d1 := rfl,
  h_d2 := rfl
}
instance π_SumBigInt3_to_F {mem : F → F} : has_coe (π_SumBigInt3 mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_SumBigInt3_ptr {mem : F → F} {x y : π_SumBigInt3 mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_d0, y.h_d0, h_p] },
  try { ext }, repeat { rw [x.h_d1, y.h_d1, h_p] },
  try { ext }, repeat { rw [x.h_d2, y.h_d2, h_p] }
end
lemma eq_SumBigInt3_π_cast {mem : F → F} {x y : F} :
  cast_π_SumBigInt3 mem x = cast_π_SumBigInt3 mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_SumBigInt3_π_ptr_cast {mem : F → F} {x : π_SumBigInt3 mem} {y : F} :
  x = cast_π_SumBigInt3 mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_SumBigInt3_π_cast {mem : F → F} {x : F} :(↑(cast_π_SumBigInt3 mem x) : F) = x := rfl

-- End of main scope definitions.


end starkware.cairo.common.cairo_secp.bigint3
