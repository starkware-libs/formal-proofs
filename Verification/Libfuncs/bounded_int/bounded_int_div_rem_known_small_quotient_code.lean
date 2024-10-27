import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def bounded_int_div_rem_known_small_quotient_code := {
  -- %{ (memory[ap + 4], memory[ap + 5]) = divmod(memory[fp + -4], memory[fp + -3]) %}
  [ap + 4] = [[fp + -5] + 0], ap++;
  [ap + 4] = [[fp + -5] + 1], ap++;
  [ap + -2] = [ap + 3] + 1, ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -5] + 2], ap++;
  --[ap + -3] = [ap + -1] + u128_bound_minus_q_upper, ap++;
  [ap + -3] = [ap + -1] + 340282366920938463463374607431768211440, ap++;
  [ap + -4] = [[fp + -5] + 3];
  [ap + -3] = [fp + -3] * [ap + -2];
  [fp + -4] = [ap + -3] + [ap + -1];
  [ap + 0] = [fp + -5] + 4, ap++;
  [ap + 0] = [ap + -3], ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_bounded_int_div_rem_known_small_quotient_code := {
  -- %{ (memory[ap + 4], memory[ap + 5]) = divmod(memory[fp + -4], memory[fp + -3]) %}
  [ap + 4] = [[fp + -5] + 0], ap++;
  [ap + 4] = [[fp + -5] + 1], ap++;
  [ap + -2] = [ap + 3] + 1, ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -5] + 2], ap++;
  [ap + -3] = [ap + -1] + 340282366920938463463374607431768211440, ap++;
  [ap + -4] = [[fp + -5] + 3];
  [ap + -3] = [fp + -3] * [ap + -2];
  [fp + -4] = [ap + -3] + [ap + -1];
  [ap + 0] = [fp + -5] + 4, ap++;
  [ap + 0] = [ap + -3], ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}
