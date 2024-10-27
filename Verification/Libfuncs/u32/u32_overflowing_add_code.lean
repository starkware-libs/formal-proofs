import Verification.Semantics.Assembly

open Casm in
casm_code_def u32_overflowing_add_code := {
  -- %{ memory[ap + 0] = memory[fp + -4] + memory[fp + -3] < 4294967296 %}
  jmp rel 8 if [ap + 0] != 0, ap++;
  [ap + 0] = [fp + -4] + [fp + -3], ap++;
  [ap + -1] = [ap + 0] + 4294967296, ap++;
  [ap + -1] = [[fp + -5] + 0];
  jmp rel 13;
  [ap + 1] = [fp + -4] + [fp + -3], ap++;
  [ap + -1] = [ap + 0] + 340282366920938463463374607427473244160, ap++;
  [ap + -2] = [[fp + -5] + 0];
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 0, ap++;
  [ap + 0] = [ap + -3], ap++;
  jmp rel 7;
  [ap + 0] = [fp + -5] + 1, ap++;
  [ap + 0] = 1, ap++;
  [ap + 0] = [ap + -3], ap++;
  ret;
}