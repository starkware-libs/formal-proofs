/-
  Specifications file for alloc_spec.cairo

  Do not modify the constant definitions, structure definitions, or automatic specifications.
  Do not change the name or arguments of the user specifications and soundness theorems.

  You may freely move the definitions around in the file.
  You may add definitions and theorems wherever you wish in this file.
-/
import starkware.cairo.lean.semantics.soundness.prelude

namespace starkware.cairo.common.alloc

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- You may change anything in this definition except the name and arguments.
def spec_alloc (mem : F → F) (κ : ℕ) (ρ_ptr : F) : Prop :=
  true

/-
-- Function: alloc
-/

/- alloc autogenerated specification -/

-- Do not change this definition.
def auto_spec_alloc (mem : F → F) (κ : ℕ) (ap ρ_ptr : F) : Prop :=
  2 ≤ κ ∧
  ρ_ptr = mem (ap + 1 - 1)

/- alloc soundness theorem -/

-- Do not change the statement of this theorem. You may change the proof.
theorem sound_alloc
    {mem : F → F}
    (κ : ℕ)
    (ap ρ_ptr : F)
    (h_auto : auto_spec_alloc mem κ ap ρ_ptr) :
  spec_alloc mem κ ρ_ptr :=
begin
  trivial
end


end starkware.cairo.common.alloc
