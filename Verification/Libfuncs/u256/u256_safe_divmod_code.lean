import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u256_safe_divmod_code := {
  -- %{
  -- dividend = memory[fp + -6] + memory[fp + -5] * 2**128
  -- divisor = memory[fp + -4] + memory[fp + -3] * 2**128
  -- quotient, remainder = divmod(dividend, divisor)
  -- memory[ap + 0] = quotient & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = quotient >> 128
  -- memory[ap + 2] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = remainder >> 128
  -- %}
  [ap + 0] = [[fp + -7] + 0], ap++;
  [ap + 0] = [[fp + -7] + 1], ap++;
  [ap + 0] = [[fp + -7] + 2], ap++;
  [ap + 0] = [[fp + -7] + 3], ap++;
  [fp + -3] = [ap + 0] + [ap + -1], ap++;
  jmp rel 8 if [ap + -1] != 0, ap++;
  [fp + -4] = [ap + -1] + [ap + -4], ap++;
  [ap + -2] = [ap + -1] + 1;
  [ap + -1] = [[fp + -7] + 4];
  jmp rel 5;
  ap += 1;
  [ap + -3] = [[fp + -7] + 4];
  -- %{ (memory[ap + 1], memory[ap + 0]) = divmod(memory[ap + -7] * memory[fp + -4], 2**128) %}
  [ap + 2] = [ap + 0] + [ap + -5], ap++;
  [ap + 1] = [ap + 2] + [fp + -6], ap++;
  [ap + 1] = [ap + 2] * 340282366920938463463374607431768211456, ap++;
  [ap + 1] = [ap + 1] * [ap + 1], ap++;
  jmp rel 12 if [ap + -10] != 0, ap++;
  -- %{ memory[ap + 2] = memory[ap + -12] < memory[fp + -3] %}
  jmp rel 6 if [ap + 2] != 0, ap++;
  [ap + -1] = [fp + -3], ap++;
  [ap + -1] = [ap + -14], ap++;
  jmp rel 16;
  [ap + -1] = [ap + -13], ap++;
  [ap + -1] = [fp + -3], ap++;
  jmp rel 12;
  [fp + -3] = 0, ap++;
  -- %{ memory[ap + 1] = memory[ap + -12] < memory[fp + -4] %}
  jmp rel 6 if [ap + 1] != 0, ap++;
  [ap + -2] = [fp + -4], ap++;
  [ap + -2] = [ap + -14];
  jmp rel 4;
  [ap + -2] = [ap + -13], ap++;
  [ap + -2] = [fp + -4];
  [ap + 0] = [ap + -3] + 340282366920938463444927863358058659840, ap++;
  [ap + -1] = [[fp + -7] + 5];
  [ap + 0] = [ap + -4] * [ap + -3], ap++;
  [ap + 0] = [ap + -6] + [ap + -9], ap++;
  [ap + 0] = [ap + -1] + [ap + -15], ap++;
  [fp + -5] = [ap + -1] + [ap + -3];
  [ap + 0] = [fp + -7] + 6, ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -24], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -18], ap++;
  [ap + 0] = [ap + -20], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_u256_safe_divmod_code := {
  -- %{
  -- dividend = memory[fp + -6] + memory[fp + -5] * 2**128
  -- divisor = memory[fp + -4] + memory[fp + -3] * 2**128
  -- quotient, remainder = divmod(dividend, divisor)
  -- memory[ap + 0] = quotient & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = quotient >> 128
  -- memory[ap + 2] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = remainder >> 128
  -- %}
  [ap + 0] = [[fp + -7] + 0], ap++;
  [ap + 0] = [[fp + -7] + 1], ap++;
  [ap + 0] = [[fp + -7] + 2], ap++;
  [ap + 0] = [[fp + -7] + 3], ap++;
  [fp + -3] = [ap + 0] + [ap + -1], ap++;
  jmp rel 8 if [ap + -1] != 0, ap++;
  [fp + -4] = [ap + -1] + [ap + -4], ap++;
  [ap + -2] = [ap + -1] + 1;
  [ap + -1] = [[fp + -7] + 4];
  jmp rel 5;
  ap += 1;
  [ap + -3] = [[fp + -7] + 4];
  -- %{ (memory[ap + 1], memory[ap + 0]) = divmod(memory[ap + -7] * memory[fp + -4], 2**128) %}
  [ap + 2] = [ap + 0] + [ap + -5], ap++;
  [ap + 1] = [ap + 2] + [fp + -6], ap++;
  [ap + 1] = [ap + 2] * 340282366920938463463374607431768211456, ap++;
  [ap + 1] = [ap + 1] * [ap + 1], ap++;
  jmp rel 12 if [ap + -10] != 0, ap++;
  -- %{ memory[ap + 2] = memory[ap + -12] < memory[fp + -3] %}
  jmp rel 6 if [ap + 2] != 0, ap++;
  [ap + -1] = [fp + -3], ap++;
  [ap + -1] = [ap + -14], ap++;
  jmp rel 16;
  [ap + -1] = [ap + -13], ap++;
  [ap + -1] = [fp + -3], ap++;
  jmp rel 12;
  [fp + -3] = 0, ap++;
  -- %{ memory[ap + 1] = memory[ap + -12] < memory[fp + -4] %}
  jmp rel 6 if [ap + 1] != 0, ap++;
  [ap + -2] = [fp + -4], ap++;
  [ap + -2] = [ap + -14];
  jmp rel 4;
  [ap + -2] = [ap + -13], ap++;
  [ap + -2] = [fp + -4];
  [ap + 0] = [ap + -3] + 340282366920938463444927863358058659840, ap++;
  [ap + -1] = [[fp + -7] + 5];
  [ap + 0] = [ap + -4] * [ap + -3], ap++;
  [ap + 0] = [ap + -6] + [ap + -9], ap++;
  [ap + 0] = [ap + -1] + [ap + -15], ap++;
  [fp + -5] = [ap + -1] + [ap + -3];
  [ap + 0] = [fp + -7] + 6, ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -20], ap++;
  [ap + 0] = [ap + -24], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -18], ap++;
  [ap + 0] = [ap + -20], ap++;
  ret;
}
