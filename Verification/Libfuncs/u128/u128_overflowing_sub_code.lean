import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u128_overflowing_sub_code := {
  [fp + -4] = [ap + 1] + [fp + -3], ap++;
  -- %{ memory[ap + -1] = memory[ap + 0] < 340282366920938463463374607431768211456 %}
  jmp rel 7 if [ap + -1] != 0, ap++;
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -5] + 0];
  jmp rel 11;
  [ap + -1] = [[fp + -5] + 0];
  ap += 1;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 0, ap++;
  [ap + 0] = [ap + -4], ap++;
  ret;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 1, ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_u128_overflowing_sub_code := {
  [fp + -4] = [ap + 1] + [fp + -3], ap++;
  -- %{ memory[ap + -1] = memory[ap + 0] < 340282366920938463463374607431768211456 %}
  jmp rel 7 if [ap + -1] != 0, ap++;
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -5] + 0];
  jmp rel 11;
  [ap + -1] = [[fp + -5] + 0];
  ap += 1;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 0, ap++;
  [ap + 0] = [ap + -4], ap++;
  ret;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 1, ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}
