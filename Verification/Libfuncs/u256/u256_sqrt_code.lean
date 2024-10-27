import Verification.Semantics.Assembly
import Verification.Semantics.Completeness.VmAssembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u256_sqrt_code := {
  -- %{
  -- import math;
  -- value = memory[fp + -4] + memory[fp + -3] * 2**128
  -- root = math.isqrt(value)
  -- remainder = value - root ** 2
  -- memory[ap + 0] = root & 0xFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = root >> 64
  -- memory[ap + 2] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = remainder >> 128
  -- memory[ap + 4] = root * 2 - remainder >= 2**128
  -- %}
  [ap + 0] = [[fp + -5] + 0], ap++;
  [ap + 0] = [[fp + -5] + 1], ap++;
  [ap + 3] = [ap + -2] + [ap + -1], ap++;
  [ap + 3] = [ap + 2] + 340282366920938463426481119284349108224, ap++;
  [ap + 2] = [[fp + -5] + 2], ap++;
  [ap + -3] = [[fp + -5] + 3], ap++;
  [ap + -3] = [ap + -3] * [ap + -3], ap++;
  [ap + 0] = [ap + -7] * [ap + -7], ap++;
  [ap + 0] = [ap + -6] + [ap + -1], ap++;
  [ap + -1] = [ap + 0] + [fp + -4], ap++;
  [ap + -1] = [ap + 0] * 18446744073709551616, ap++;
  [ap + 0] = [ap + -1] + 170141183460469231731687303715884105728, ap++;
  [ap + -1] = [[fp + -5] + 4];
  [ap + 0] = [ap + -12] * [ap + -11], ap++;
  [ap + 0] = [ap + -3] + [ap + -1], ap++;
  [ap + 0] = [ap + -1] + [ap + -2], ap++;
  [ap + -1] = [ap + 0] * 18446744073709551616, ap++;
  [ap + -1] = [[fp + -5] + 5];
  [ap + 0] = [ap + -1] + [ap + -13], ap++;
  [ap + 0] = [ap + -16] * [ap + -16], ap++;
  [fp + -3] = [ap + -2] + [ap + -1];
  [ap + 0] = [ap + -17] * 18446744073709551616, ap++;
  [ap + 0] = [ap + -19] + [ap + -1], ap++;
  [ap + 0] = [ap + -17] * 340282366920938463463374607431768211456, ap++;
  [ap + 0] = [ap + -19] + [ap + -1], ap++;
  [ap + 0] = [ap + -3] + [ap + -3], ap++;
  [ap + -1] = [ap + 0] + [ap + -2], ap++;
  jmp rel 5 if [ap + -20] != 0, ap++;
  [ap + -2] = [[fp + -5] + 6];
  jmp rel 5;
  [ap + -2] = [ap + -1] + 340282366920938463463374607431768211456;
  [ap + -1] = [[fp + -5] + 6];
  [ap + 0] = [fp + -5] + 7, ap++;
  [ap + 0] = [ap + -7], ap++;
  ret;
}

open Casm in
vm_casm_code_def vm_u256_sqrt_code := {
  -- %{
  -- import math;
  -- value = memory[fp + -4] + memory[fp + -3] * 2**128
  -- root = math.isqrt(value)
  -- remainder = value - root ** 2
  -- memory[ap + 0] = root & 0xFFFFFFFFFFFFFFFF
  -- memory[ap + 1] = root >> 64
  -- memory[ap + 2] = remainder & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  -- memory[ap + 3] = remainder >> 128
  -- memory[ap + 4] = root * 2 - remainder >= 2**128
  -- %}
  [ap + 0] = [[fp + -5] + 0], ap++;
  [ap + 0] = [[fp + -5] + 1], ap++;
  [ap + 3] = [ap + -2] + [ap + -1], ap++;
  [ap + 3] = [ap + 2] + 340282366920938463426481119284349108224, ap++;
  [ap + 2] = [[fp + -5] + 2], ap++;
  [ap + -3] = [[fp + -5] + 3], ap++;
  [ap + -3] = [ap + -3] * [ap + -3], ap++;
  [ap + 0] = [ap + -7] * [ap + -7], ap++;
  [ap + 0] = [ap + -6] + [ap + -1], ap++;
  [ap + -1] = [ap + 0] + [fp + -4], ap++;
  [ap + -1] = [ap + 0] * 18446744073709551616, ap++;
  [ap + 0] = [ap + -1] + 170141183460469231731687303715884105728, ap++;
  [ap + -1] = [[fp + -5] + 4];
  [ap + 0] = [ap + -12] * [ap + -11], ap++;
  [ap + 0] = [ap + -3] + [ap + -1], ap++;
  [ap + 0] = [ap + -1] + [ap + -2], ap++;
  [ap + -1] = [ap + 0] * 18446744073709551616, ap++;
  [ap + -1] = [[fp + -5] + 5];
  [ap + 0] = [ap + -1] + [ap + -13], ap++;
  [ap + 0] = [ap + -16] * [ap + -16], ap++;
  [fp + -3] = [ap + -2] + [ap + -1];
  [ap + 0] = [ap + -17] * 18446744073709551616, ap++;
  [ap + 0] = [ap + -19] + [ap + -1], ap++;
  [ap + 0] = [ap + -17] * 340282366920938463463374607431768211456, ap++;
  [ap + 0] = [ap + -19] + [ap + -1], ap++;
  [ap + 0] = [ap + -3] + [ap + -3], ap++;
  [ap + -1] = [ap + 0] + [ap + -2], ap++;
  jmp rel 5 if [ap + -20] != 0, ap++;
  [ap + -2] = [[fp + -5] + 6];
  jmp rel 5;
  [ap + -2] = [ap + -1] + 340282366920938463463374607431768211456;
  [ap + -1] = [[fp + -5] + 6];
  [ap + 0] = [fp + -5] + 7, ap++;
  [ap + 0] = [ap + -7], ap++;
  ret;
}
