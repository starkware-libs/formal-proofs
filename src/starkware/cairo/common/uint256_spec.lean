/-
  Specifications file for uint256_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.uint256

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def SHIFT := 2 ^ 128
@[reducible] def ALL_ONES := 2 ^ 128 - 1
@[reducible] def HALF_SHIFT := 2 ^ 64
@[reducible] def φ_Uint256.low := 0
@[reducible] def φ_Uint256.high := 1
@[ext] structure Uint256 (mem : F → F) :=
  (low : F) (high : F)
@[reducible] def Uint256.SIZE := 2
@[ext] structure π_Uint256 (mem : F → F) :=
  (σ_ptr : F) (low : F) (high : F)
  (h_low : low = mem (σ_ptr + φ_Uint256.low))
  (h_high : high = mem (σ_ptr + φ_Uint256.high))
@[reducible] def π_Uint256.SIZE := 2
@[reducible] def cast_Uint256 (mem : F → F) (p : F) : Uint256 mem := {
  low := mem (p + φ_Uint256.low),
  high := mem (p + φ_Uint256.high)
}
@[reducible] def cast_π_Uint256 (mem : F → F) (p : F) : π_Uint256 mem := {
  σ_ptr := p,
  low := mem (p + φ_Uint256.low),
  high := mem (p + φ_Uint256.high),
  h_low := rfl,
  h_high := rfl
}
instance π_Uint256_to_F {mem : F → F} : has_coe (π_Uint256 mem) F := ⟨λ s, s.σ_ptr⟩
@[ext] lemma eq_Uint256_ptr {mem : F → F} {x y : π_Uint256 mem} : x.σ_ptr = y.σ_ptr → x = y :=
begin
  intros h_p, ext,
  exact h_p,
  try { ext }, repeat { rw [x.h_low, y.h_low, h_p] },
  try { ext }, repeat { rw [x.h_high, y.h_high, h_p] }
end
lemma eq_Uint256_π_cast {mem : F → F} {x y : F} :
  cast_π_Uint256 mem x = cast_π_Uint256 mem y ↔ x = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, rw [h],
end
lemma eq_Uint256_π_ptr_cast {mem : F → F} {x : π_Uint256 mem} {y : F} :
  x = cast_π_Uint256 mem y ↔ x.σ_ptr = y :=
begin
  apply iff.intro, intro h, cases h, refl, intro h, ext, rw [←h]
end
lemma coe_Uint256_π_cast {mem : F → F} {x : F} :(↑(cast_π_Uint256 mem x) : F) = x := rfl

-- End of main scope definitions.

end starkware.cairo.common.uint256
