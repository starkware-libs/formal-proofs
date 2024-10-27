import Verification.Semantics.Assembly

set_option maxRecDepth 1024

open Casm in
casm_code_def u64_try_from_felt252_code := {
  -- %{ memory[ap + 0] = memory[fp + -3] < 18446744073709551616 %}
  jmp rel 18 if [ap + 0] != 0, ap++;
  [fp + -3] = [ap + 0] + 18446744073709551616, ap++;
  -- %{
  -- (value, scalar) = (memory[ap + -1], 10633823966279327296825105735305134080)
  -- x = min(value // scalar, 340282366920938463463374607431768211454)
  -- y = value - x * scalar
  -- memory[ap + 0] = x
  -- memory[ap + 1] = y
  -- %}
  [ap + 2] = [ap + 0] * 10633823966279327296825105735305134080, ap++;
  [ap + -2] = [ap + 1] + [ap + 0], ap++;
  [ap + -1] = [[fp + -4] + 0], ap++;
  [ap + 0] = [ap + -2] + 319014718988379808888171140034867494911, ap++;
  [ap + -1] = [[fp + -4] + 1], ap++;
  [ap + -5] = [[fp + -4] + 2];
  [ap + -5] = [ap + -1] + 340282366920938463463374607431768211455;
  jmp rel 17 if [ap + -1] != 0;
  [fp + -1] = [fp + -1] + 1;
  [fp + -3] = [[fp + -4] + 0];
  [ap + 0] = [fp + -3] + 340282366920938463444927863358058659840, ap++;
  [ap + -1] = [[fp + -4] + 1];
  ap += 5;
  [ap + 0] = [fp + -4] + 2, ap++;
  [ap + 0] = 0, ap++;
  [ap + 0] = [fp + -3], ap++;
  jmp rel 8;
  [ap + 0] = [fp + -4] + 3, ap++;
  [ap + 0] = 1, ap++;
  [ap + 0] = 0, ap++;
  ret;
}
