import Mathlib.Tactic.Attr.Register

-- According to Attr.Register, simp attributes cannot be used in the same
-- file in which they are declared. So we declare it here.

/-- rules for pushing integer casts downwards -/
register_simp_attr int_cast_simps

register_simp_attr int_nat_offset_simps
