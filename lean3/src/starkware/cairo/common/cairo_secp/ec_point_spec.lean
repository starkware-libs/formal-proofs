/-
  Specifications file for ec_point_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude
import starkware.cairo.common.cairo_secp.bigint3_spec

open starkware.cairo.common.cairo_secp.bigint3
namespace starkware.cairo.common.cairo_secp.ec_point

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def φ_EcPoint.x := 0
@[reducible] def φ_EcPoint.y := 3
@[ext] structure EcPoint (mem : F → F) :=
  (x : BigInt3 mem) (y : BigInt3 mem)
@[reducible] def EcPoint.SIZE := 6
@[ext] structure π_EcPoint (mem : F → F) :=
  (σ_ptr : F) (x : BigInt3 mem) (y : BigInt3 mem)
  (h_x : x = cast_BigInt3 mem (σ_ptr + φ_EcPoint.x))
  (h_y : y = cast_BigInt3 mem (σ_ptr + φ_EcPoint.y))
@[reducible] def π_EcPoint.SIZE := 6
@[reducible] def cast_EcPoint (mem : F → F) (p : F) : EcPoint mem := {
  x := cast_BigInt3 mem (p + φ_EcPoint.x),
  y := cast_BigInt3 mem (p + φ_EcPoint.y)
}
@[reducible] def cast_π_EcPoint (mem : F → F) (p : F) : π_EcPoint mem := {
  σ_ptr := p,
  x := cast_BigInt3 mem (p + φ_EcPoint.x),
  y := cast_BigInt3 mem (p + φ_EcPoint.y),
  h_x := rfl,
  h_y := rfl
}
instance π_EcPoint_to_F {mem : F → F} : has_coe (π_EcPoint mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_EcPoint_ptr {mem : F → F} {x y : π_EcPoint mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_x, y.h_x, h_p] },
  try { ext }, repeat { rw [x.h_y, y.h_y, h_p] }
end
lemma eq_EcPoint_π_cast {mem : F → F} {x y : F} :
  cast_π_EcPoint mem x = cast_π_EcPoint mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_EcPoint_π_ptr_cast {mem : F → F} {x : π_EcPoint mem} {y : F} :
  x = cast_π_EcPoint mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_EcPoint_π_cast {mem : F → F} {x : F} :(↑(cast_π_EcPoint mem x) : F) = x := rfl

-- End of main scope definitions.


end starkware.cairo.common.cairo_secp.ec_point
