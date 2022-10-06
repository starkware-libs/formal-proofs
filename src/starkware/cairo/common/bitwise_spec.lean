/-
File: bitwise_spec.lean

Use this file to write specifications for functions, and prove that the compiler-generated
  specifications imply them.

User input should be between comment lines that begin USER_INPUT and USER_END.
-/
import .verification.bitwise_prelude

namespace starkware.cairo.common.bitwise

variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]

-- End of automatically generated prelude.

-- Main scope definitions.

@[reducible] def ALL_ONES := 2 ^ 251 - 1

-- End of main scope definitions.


end starkware.cairo.common.bitwise
