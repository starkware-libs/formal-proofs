import Verification.Semantics.Assembly

open Casm in
casm_code_def u32_overflowing_sub_code := {
  [fp + -4] = [ap + 1] + [fp + -3], ap++;
  -- %{ memory[ap + -1] = memory[fp + -3] <= memory[fp + -4] %}
  jmp rel 7 if [ap + -1] != 0, ap++;
  [ap + 0] = [ap + -1] + 340282366920938463463374607431768211456, ap++;
  [ap + -1] = [[fp + -5] + 0];
  jmp rel 12;
  [ap + -1] = [[fp + -5] + 0];
  ap += 1;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 0, ap++;
  [ap + 0] = [ap + -4], ap++;
  jmp rel 8;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 1, ap++;
  [ap + 0] = [ap + -4] + 4294967296, ap++;
  ret;
}