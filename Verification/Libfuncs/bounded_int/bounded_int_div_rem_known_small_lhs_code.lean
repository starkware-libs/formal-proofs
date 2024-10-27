import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def bounded_int_div_rem_known_small_lhs_code := {
  -- %{ (memory[ap + 5], memory[ap + 6]) = divmod(memory[fp + -4], memory[fp + -3]) %}
  [ap + 5] = [[fp + -5] + 0], ap++;
  [ap + 5] = [[fp + -5] + 1], ap++;
  [ap + -2] = [ap + 4] + 1, ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -5] + 2], ap++;
  -- %{ memory[ap + -3] = memory[ap + 0] < 18446744073709551616 %}
  jmp rel 6 if [ap + -3] != 0, ap++;
  [ap + -3] = [fp + -3] + 340282366920938463444927863358058659840, ap++;
  jmp rel 4;
  [ap + -3] = [ap + -1] + 340282366920938463444927863358058659840, ap++;
  [ap + -4] = [[fp + -5] + 3];
  [ap + -3] = [fp + -3] * [ap + -2];
  [fp + -4] = [ap + -3] + [ap + -1];
  [ap + 0] = [fp + -5] + 4, ap++;
  [ap + 0] = [ap + -3], ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_bounded_int_div_rem_known_small_lhs_code := {
  -- %{ (memory[ap + 5], memory[ap + 6]) = divmod(memory[fp + -4], memory[fp + -3]) %}
  [ap + 5] = [[fp + -5] + 0], ap++;
  [ap + 5] = [[fp + -5] + 1], ap++;
  [ap + -2] = [ap + 4] + 1, ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -5] + 2], ap++;
  -- %{ memory[ap + -3] = memory[ap + 0] < 18446744073709551616 %}
  jmp rel 6 if [ap + -3] != 0, ap++;
  [ap + -3] = [fp + -3] + 340282366920938463444927863358058659840, ap++;
  jmp rel 4;
  [ap + -3] = [ap + -1] + 340282366920938463444927863358058659840, ap++;
  [ap + -4] = [[fp + -5] + 3];
  [ap + -3] = [fp + -3] * [ap + -2];
  [fp + -4] = [ap + -3] + [ap + -1];
  [ap + 0] = [fp + -5] + 4, ap++;
  [ap + 0] = [ap + -3], ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}
