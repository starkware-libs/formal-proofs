import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u512_safe_divmod_by_u256_code := {
  -- %{
  -- dividend = memory[fp + -8] + memory[fp + -7] * 2**128 + memory[fp + -6] * 2**256 + memory[fp + -5] * 2**384
  -- divisor = memory[fp + -4] + memory[fp + -3] * 2**128
  -- quotient, remainder = divmod(dividend, divisor)
  -- memory[ap + 0] = quotient & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = (quotient >> 128) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 2] = (quotient >> 256) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = quotient >> 384
  -- memory[ap + 4] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 5] = remainder >> 128
  -- %}
  [ap + 0] = [[fp + -9] + 0], ap++;
  [ap + 0] = [[fp + -9] + 1], ap++;
  [ap + 0] = [[fp + -9] + 2], ap++;
  [ap + 0] = [[fp + -9] + 3], ap++;
  [ap + 0] = [[fp + -9] + 4], ap++;
  [ap + 0] = [[fp + -9] + 5], ap++;
  [fp + -3] = [ap + 0] + [ap + -1], ap++;
  ap += 12;
  jmp rel 8 if [ap + -13] != 0;
  [fp + -4] = [ap + -12] + [ap + -15];
  [ap + -12] = [ap + -11] + 1;
  [ap + -11] = [[fp + -9] + 6];
  jmp rel 3;
  [ap + -13] = [[fp + -9] + 6];
  -- %{ (memory[ap + -9], memory[ap + -10]) = divmod(memory[ap + -19] * memory[fp + -4], 2**128) %}
  -- %{ (memory[ap + -7], memory[ap + -8]) = divmod(memory[ap + -18] * memory[fp + -4], 2**128) %}
  -- %{ (memory[ap + -5], memory[ap + -6]) = divmod(memory[ap + -19] * memory[fp + -3], 2**128) %}
  -- %{ (memory[ap + -3], memory[ap + -4]) = divmod(memory[ap + -18] * memory[fp + -3], 2**128) %}
  -- %{ (memory[ap + -1], memory[ap + -2]) = divmod(memory[ap + -17] * memory[fp + -4], 2**128) %}
  [ap + 0] = [ap + -10] + [ap + -15], ap++;
  [ap + -1] = [ap + 0] + [fp + -8], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [ap + -1] * [ap + -1];
  [ap + 0] = [ap + -1] + [ap + -12], ap++;
  [ap + 0] = [ap + -1] + [ap + -12], ap++;
  [ap + 0] = [ap + -1] + [ap + -11], ap++;
  [ap + 0] = [ap + -1] + [ap + -20], ap++;
  [ap + -1] = [ap + 0] + [fp + -7], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -9] + 7];
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211452, ap++;
  [ap + -1] = [[fp + -9] + 8];
  [ap + 0] = [ap + -2] + [ap + -17], ap++;
  [ap + 0] = [ap + -1] + [ap + -16], ap++;
  [ap + 0] = [ap + -1] + [ap + -16], ap++;
  [ap + 0] = [ap + -1] + [ap + -15], ap++;
  [ap + -1] = [ap + 0] + [fp + -6], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -9] + 9];
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211452, ap++;
  [ap + -1] = [[fp + -9] + 10];
  jmp rel 12 if [ap + -33] != 0, ap++;
  -- %{ memory[ap + 1] = memory[ap + -35] < memory[fp + -3] %}
  jmp rel 6 if [ap + 1] != 0, ap++;
  [ap + -2] = [fp + -3], ap++;
  [ap + -2] = [ap + -37];
  jmp rel 16;
  [ap + -2] = [ap + -36], ap++;
  [ap + -2] = [fp + -3];
  jmp rel 12;
  [fp + -3] = 0, ap++;
  -- %{ memory[ap + 0] = memory[ap + -35] < memory[fp + -4] %}
  jmp rel 6 if [ap + 0] != 0, ap++;
  [ap + -3] = [fp + -4];
  [ap + -2] = [ap + -36];
  jmp rel 4;
  [ap + -3] = [ap + -36];
  [ap + -2] = [fp + -4];
  [ap + 0] = [ap + -3] + 340282366920938463444927863358058659840, ap++;
  [ap + -1] = [[fp + -9] + 11];
  [ap + 0] = [ap + -4] * [ap + -3], ap++;
  [ap + 0] = [ap + -7] + [ap + -23], ap++;
  [ap + 0] = [ap + -1] + [ap + -26], ap++;
  [fp + -5] = [ap + -1] + [ap + -3];
  [ap + 0] = [fp + -9] + 12, ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -42], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -54], ap++;
  [ap + 0] = [fp + -3], ap++;
  [ap + 0] = [ap + -42], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -57], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -48], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -61], ap++;
  [ap + 0] = [fp + -3], ap++;
  [ap + 0] = [ap + -48], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -64], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -52], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_u512_safe_divmod_by_u256_code := {
  -- %{
  -- dividend = memory[fp + -8] + memory[fp + -7] * 2**128 + memory[fp + -6] * 2**256 + memory[fp + -5] * 2**384
  -- divisor = memory[fp + -4] + memory[fp + -3] * 2**128
  -- quotient, remainder = divmod(dividend, divisor)
  -- memory[ap + 0] = quotient & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = (quotient >> 128) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 2] = (quotient >> 256) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = quotient >> 384
  -- memory[ap + 4] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 5] = remainder >> 128
  -- %}
  [ap + 0] = [[fp + -9] + 0], ap++;
  [ap + 0] = [[fp + -9] + 1], ap++;
  [ap + 0] = [[fp + -9] + 2], ap++;
  [ap + 0] = [[fp + -9] + 3], ap++;
  [ap + 0] = [[fp + -9] + 4], ap++;
  [ap + 0] = [[fp + -9] + 5], ap++;
  [fp + -3] = [ap + 0] + [ap + -1], ap++;
  ap += 12;
  jmp rel 8 if [ap + -13] != 0;
  [fp + -4] = [ap + -12] + [ap + -15];
  [ap + -12] = [ap + -11] + 1;
  [ap + -11] = [[fp + -9] + 6];
  jmp rel 3;
  [ap + -13] = [[fp + -9] + 6];
  -- %{ (memory[ap + -9], memory[ap + -10]) = divmod(memory[ap + -19] * memory[fp + -4], 2**128) %}
  -- %{ (memory[ap + -7], memory[ap + -8]) = divmod(memory[ap + -18] * memory[fp + -4], 2**128) %}
  -- %{ (memory[ap + -5], memory[ap + -6]) = divmod(memory[ap + -19] * memory[fp + -3], 2**128) %}
  -- %{ (memory[ap + -3], memory[ap + -4]) = divmod(memory[ap + -18] * memory[fp + -3], 2**128) %}
  -- %{ (memory[ap + -1], memory[ap + -2]) = divmod(memory[ap + -17] * memory[fp + -4], 2**128) %}
  [ap + 0] = [ap + -10] + [ap + -15], ap++;
  [ap + -1] = [ap + 0] + [fp + -8], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [ap + -1] * [ap + -1];
  [ap + 0] = [ap + -1] + [ap + -12], ap++;
  [ap + 0] = [ap + -1] + [ap + -12], ap++;
  [ap + 0] = [ap + -1] + [ap + -11], ap++;
  [ap + 0] = [ap + -1] + [ap + -20], ap++;
  [ap + -1] = [ap + 0] + [fp + -7], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -9] + 7];
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211452, ap++;
  [ap + -1] = [[fp + -9] + 8];
  [ap + 0] = [ap + -2] + [ap + -17], ap++;
  [ap + 0] = [ap + -1] + [ap + -16], ap++;
  [ap + 0] = [ap + -1] + [ap + -16], ap++;
  [ap + 0] = [ap + -1] + [ap + -15], ap++;
  [ap + -1] = [ap + 0] + [fp + -6], ap++;
  [ap + -1] = [ap + 0] * 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -9] + 9];
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211452, ap++;
  [ap + -1] = [[fp + -9] + 10];
  jmp rel 12 if [ap + -33] != 0, ap++;
  -- %{ memory[ap + 1] = memory[ap + -35] < memory[fp + -3] %}
  jmp rel 6 if [ap + 1] != 0, ap++;
  [ap + -2] = [fp + -3], ap++;
  [ap + -2] = [ap + -37];
  jmp rel 16;
  [ap + -2] = [ap + -36], ap++;
  [ap + -2] = [fp + -3];
  jmp rel 12;
  [fp + -3] = 0, ap++;
  -- %{ memory[ap + 0] = memory[ap + -35] < memory[fp + -4] %}
  jmp rel 6 if [ap + 0] != 0, ap++;
  [ap + -3] = [fp + -4];
  [ap + -2] = [ap + -36];
  jmp rel 4;
  [ap + -3] = [ap + -36];
  [ap + -2] = [fp + -4];
  [ap + 0] = [ap + -3] + 340282366920938463444927863358058659840, ap++;
  [ap + -1] = [[fp + -9] + 11];
  [ap + 0] = [ap + -4] * [ap + -3], ap++;
  [ap + 0] = [ap + -7] + [ap + -23], ap++;
  [ap + 0] = [ap + -1] + [ap + -26], ap++;
  [fp + -5] = [ap + -1] + [ap + -3];
  [ap + 0] = [fp + -9] + 12, ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -42], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -54], ap++;
  [ap + 0] = [fp + -3], ap++;
  [ap + 0] = [ap + -42], ap++;
  [ap + 0] = [ap + -44], ap++;
  [ap + 0] = [ap + -57], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -48], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -61], ap++;
  [ap + 0] = [fp + -3], ap++;
  [ap + 0] = [ap + -48], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -64], ap++;
  [ap + 0] = [fp + -4], ap++;
  [ap + 0] = [ap + -50], ap++;
  [ap + 0] = [ap + -52], ap++;
  ret;
}
