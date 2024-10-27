import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u128_sqrt_code := {
  -- %{
  -- import math
  -- memory[ap + 5] = math.isqrt(memory[fp + -3])
  -- %}
  [ap + 0] = [ap + 5] + 297747071055821155530452781502797185024, ap++;
  [ap + 4] = [[fp + -4] + 0], ap++;
  [ap + -2] = [[fp + -4] + 1], ap++;
  [ap + -2] = [ap + 2] * [ap + 2], ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -4] + 2], ap++;
  [ap + -3] = [ap + -1] + [ap + -1];
  [ap + -3] = [ap + -2] + [ap + -4];
  [ap + -2] = [[fp + -4] + 3];
  [ap + 0] = [fp + -4] + 4, ap++;
  [ap + 0] = [ap + -2], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_u128_sqrt_code := {
  -- %{
  -- import math
  -- memory[ap + 5] = math.isqrt(memory[fp + -3])
  -- %}
  [ap + 0] = [ap + 5] + 297747071055821155530452781502797185024, ap++;
  [ap + 4] = [[fp + -4] + 0], ap++;
  [ap + -2] = [[fp + -4] + 1], ap++;
  [ap + -2] = [ap + 2] * [ap + 2], ap++;
  [fp + -3] = [ap + -2] + [ap + -3], ap++;
  [ap + -3] = [[fp + -4] + 2], ap++;
  [ap + -3] = [ap + -1] + [ap + -1];
  [ap + -3] = [ap + -2] + [ap + -4];
  [ap + -2] = [[fp + -4] + 3];
  [ap + 0] = [fp + -4] + 4, ap++;
  [ap + 0] = [ap + -2], ap++;
  ret;
}
