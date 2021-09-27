/-
The constraints specifying the trace of a Cairo execution.
-/
import algebra.field data.nat.basic data.fin tactic.norm_num
import cpu -- for names of flags

open_locale big_operators

structure input_data_aux (F : Type*) :=
(T        : nat)
(pc_I     : F)
(pc_F     : F)
(ap_I     : F)
(ap_F     : F)
(mem_star : F → option F)
(rc_min   : nat)
(rc_max   : nat)
/- constraints -/
(h_rc_lt  : rc_max < 2^16)
(h_rc_le  : rc_min ≤ rc_max)

/- functions for accessing `mem_star` -/

/-- the domain of the partial memory specification -/
def mem_dom {F : Type*} (mem_star : F → option F) :=
{ x // option.is_some (mem_star x) }

/-- the value of the memory -/
def mem_val {F : Type*} {mem_star : F → option F} (a : mem_dom mem_star) : F :=
option.get a.property

instance {F : Type*} [fintype F] (mem_star : F → option F) : fintype (mem_dom mem_star) :=
by {rw mem_dom, apply_instance}

/- auxiliary functions for talking about flags extracted from f_tilde -/

/-- a sequence of trace cells for storing a bitvector of flags -/
def tilde_type (F : Type*) := fin 16 → F

namespace tilde_type

variables {F : Type*} [field F] (f_tilde : tilde_type F)

def to_f := λ i : fin 15, f_tilde i.cast_succ - 2 * f_tilde i.succ

def f_dst_reg          := f_tilde.to_f DST_REG
def f_op0_reg          := f_tilde.to_f OP0_REG
def f_op1_imm          := f_tilde.to_f OP1_IMM
def f_op1_fp           := f_tilde.to_f OP1_FP
def f_op1_ap           := f_tilde.to_f OP1_AP
def f_res_add          := f_tilde.to_f RES_ADD
def f_res_mul          := f_tilde.to_f RES_MUL
def f_pc_jump_abs      := f_tilde.to_f PC_JUMP_ABS
def f_pc_jump_rel      := f_tilde.to_f PC_JUMP_REL
def f_pc_jnz           := f_tilde.to_f PC_JNZ
def f_ap_add           := f_tilde.to_f AP_ADD
def f_ap_add1          := f_tilde.to_f AP_ADD1
def f_opcode_call      := f_tilde.to_f OPCODE_CALL
def f_opcode_ret       := f_tilde.to_f OPCODE_RET
def f_opcode_assert_eq := f_tilde.to_f OPCODE_ASSERT_EQ

def instruction_size := f_tilde.f_op1_imm + 1

end tilde_type

/-
The constraints on how information is stored in memory.

For some reason, elaboration was too slow (and timed out) before I split this into smaller
structures.
-/

structure memory_embedding_constraints {F : Type*} [field F] [fintype F]
  (T        : nat)
  (pc       : fin T → F)
  (inst     : fin T → F)
  (dst_addr : fin T → F)
  (dst      : fin T → F)
  (op0_addr : fin T → F)
  (op0      : fin T → F)
  (op1_addr : fin T → F)
  (op1      : fin T → F)
  (mem_star : F → option F)
  (n        : nat)
  (a        : fin (n + 1) → F)
  (v        : fin (n + 1) → F) :=
/- embedding of data -/
(embed_inst            : fin T → fin (n + 1))
(embed_dst             : fin T → fin (n + 1))
(embed_op0             : fin T → fin (n + 1))
(embed_op1             : fin T → fin (n + 1))
(embed_mem             : mem_dom mem_star → fin (n + 1))
(h_embed_pc            : ∀ i, a (embed_inst i) = pc i)
(h_embed_inst          : ∀ i, v (embed_inst i) = inst i)
(h_embed_dst_addr      : ∀ i, a (embed_dst i)  = dst_addr i)
(h_embed_dst           : ∀ i, v (embed_dst i)  = dst i)
(h_embed_op0_addr      : ∀ i, a (embed_op0 i)  = op0_addr i)
(h_embed_op0           : ∀ i, v (embed_op0 i)  = op0 i)
(h_embed_op1_addr      : ∀ i, a (embed_op1 i)  = op1_addr i)
(h_embed_op1           : ∀ i, v (embed_op1 i)  = op1 i)
(h_embed_dom           : ∀ i : mem_dom mem_star, a (embed_mem i) = 0)
(h_embed_val           : ∀ i : mem_dom mem_star, v (embed_mem i) = 0)
(h_embed_mem_inj       : function.injective embed_mem)
(h_embed_mem_disj_inst : ∀ i j, embed_mem i ≠ embed_inst j)
(h_embed_mem_disj_dst  : ∀ i j, embed_mem i ≠ embed_dst j)
(h_embed_mem_disj_op0  : ∀ i j, embed_mem i ≠ embed_op0 j)
(h_embed_mem_disj_op1  : ∀ i j, embed_mem i ≠ embed_op1 j)

structure memory_block_constraints {F : Type*} [field F] [fintype F]
  (n        : nat)
  (a        : fin (n + 1) → F)
  (v        : fin (n + 1) → F)
  (mem_star : F → option F) :=
(a'      : fin (n + 1) → F)
(v'      : fin (n + 1) → F)
(p       : fin (n + 1) → F)
(alpha   : F)
(z       : F)
(h_continuity    : ∀ i : fin n, (a' i.succ - a' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0)
(h_single_valued : ∀ i : fin n, (v' i.succ - v' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0)
(h_initial       : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0))
(h_cumulative    : ∀ i : fin n, (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
                                    (z - (a i.succ + alpha * v i.succ)) * p i.cast_succ)
(h_final         : p (fin.last n) * ∏ a : mem_dom mem_star, (z - (a.val + alpha * mem_val a)) =
                     z^(fintype.card (mem_dom mem_star)))

structure memory_constraints {F : Type*} [field F] [fintype F]
  (T        : nat)
  (pc       : fin T → F)
  (inst     : fin T → F)
  (dst_addr : fin T → F)
  (dst      : fin T → F)
  (op0_addr : fin T → F)
  (op0      : fin T → F)
  (op1_addr : fin T → F)
  (op1      : fin T → F)
  (mem_star : F → option F) :=
(n       : nat)
(a       : fin (n + 1) → F)
(v       : fin (n + 1) → F)
(em      : memory_embedding_constraints T pc inst dst_addr dst op0_addr op0 op1_addr op1 mem_star
              n a v)
(mb      : memory_block_constraints n a v mem_star)
(h_n_lt  : n < ring_char F)

/-
Range check constraints.
-/

structure range_check_constraints {F : Type*} [field F]
  (T              : nat)
  (off_op0_tilde  : fin T → F)
  (off_op1_tilde  : fin T → F)
  (off_dst_tilde  : fin T → F)
  (rc_min         : nat)
  (rc_max         : nat) :=
(n  : nat)
(a  : fin (n + 1) → F)
(a' : fin (n + 1) → F)
(p  : fin (n + 1) → F)
(z  : F)
/- embedding of `op0`, `op1`, and `dst` data in `a` -/
(embed_off_op0 : fin T → fin (n + 1))
(embed_off_op1 : fin T → fin (n + 1))
(embed_off_dst : fin T → fin (n + 1))
(h_embed_op0   : ∀ i, a (embed_off_op0 i) = off_op0_tilde i)
(h_embed_op1   : ∀ i, a (embed_off_op1 i) = off_op1_tilde i)
(h_embed_dst   : ∀ i, a (embed_off_dst i) = off_dst_tilde i)
/- constraints -/
(h_continuity  : ∀ i : fin n, (a' i.succ - a' i.cast_succ) * (a' i.succ - a' i.cast_succ - 1) = 0)
(h_initial     : (z - a' 0) * p 0 = z - a 0)
(h_cumulative  : ∀ i : fin n, (z - a' i.succ) * p i.succ = (z - a i.succ) * p i.cast_succ)
(h_final       : p (fin.last n) = 1)
(h_rc_min      : a' 0 = rc_min)
(h_rc_max      : a' (fin.last n) = rc_max)
(h_n_lt        : n < ring_char F)

/-
Constraints for each instruction.
-/

structure instruction_constraints {F : Type*} [field F]
  (inst          : F)
  (off_op0_tilde : F)
  (off_op1_tilde : F)
  (off_dst_tilde : F)
  (f_tilde       : tilde_type F) :=
(h_instruction   : inst = off_dst_tilde + 2^16 * off_op0_tilde + 2^32 * off_op1_tilde +
                            2^48 * f_tilde 0)
(h_bit           : ∀ i : fin 15, f_tilde.to_f i * (f_tilde.to_f i - 1) = 0)
(h_last_value    : f_tilde ⟨15, by norm_num⟩ = 0)

/-
Constraints relating each state to the next one.
-/

structure step_constraints {F : Type*} [field F]
  (off_op0_tilde : F)
  (off_op1_tilde : F)
  (off_dst_tilde : F)
  (f_tilde       : tilde_type F)
  (fp            : F)
  (ap            : F)
  (pc            : F)
  (next_fp       : F)
  (next_ap       : F)
  (next_pc       : F)
  (dst_addr      : F)
  (op0_addr      : F)
  (op1_addr      : F)
  (dst           : F)
  (op0           : F)
  (op1           : F) :=
(mul             : F)
(res             : F)
(t0              : F)
(t1              : F)
(h_dst_addr      : dst_addr = f_tilde.f_dst_reg * fp + (1 - f_tilde.f_dst_reg) * ap +
                                (off_dst_tilde - 2^15))
(h_op0_addr      : op0_addr = f_tilde.f_op0_reg * fp + (1 - f_tilde.f_op0_reg) * ap +
                               (off_op0_tilde - 2^15))
(h_op1_addr      : op1_addr = f_tilde.f_op1_imm * pc + f_tilde.f_op1_ap * ap +
                               f_tilde.f_op1_fp * fp +
                               (1 - f_tilde.f_op1_imm - f_tilde.f_op1_ap - f_tilde.f_op1_fp) * op0 +
                               (off_op1_tilde - 2^15))
(h_mul           : mul = op0 * op1)
(h_res           : (1 - f_tilde.f_pc_jnz) * res =
                     f_tilde.f_res_add * (op0 + op1) +  f_tilde.f_res_mul * mul +
                       (1 - f_tilde.f_res_add - f_tilde.f_res_mul - f_tilde.f_pc_jnz) * op1)
(h_t0_eq         : t0 = f_tilde.f_pc_jnz * dst)
(h_t1_eq         : t1 = t0 * res)
(h_next_pc_eq    : (t1 - f_tilde.f_pc_jnz) * (next_pc - (pc + (f_tilde.f_op1_imm + 1))) = 0)
(h_next_pc_eq'   : t0 * (next_pc - (pc + op1)) + (1 - f_tilde.f_pc_jnz) * next_pc -
                       ((1 - f_tilde.f_pc_jump_abs - f_tilde.f_pc_jump_rel - f_tilde.f_pc_jnz) *
                           (pc + (f_tilde.f_op1_imm + 1)) +
                         f_tilde.f_pc_jump_abs * res + f_tilde.f_pc_jump_rel * (pc + res))
                     = 0)
(h_opcode_call   : f_tilde.f_opcode_call * (dst - fp) = 0)
(h_opcode_call'  : f_tilde.f_opcode_call * (op0 - (pc + (f_tilde.f_op1_imm + 1))) = 0)
(h_opcode_assert_eq : f_tilde.f_opcode_assert_eq * (dst - res) = 0)
(h_next_ap       : next_ap = ap + f_tilde.f_ap_add * res + f_tilde.f_ap_add1 +
                               f_tilde.f_opcode_call * 2)
(h_next_fp       : next_fp = f_tilde.f_opcode_ret * dst + f_tilde.f_opcode_call * (ap + 2) +
                               (1 - f_tilde.f_opcode_ret - f_tilde.f_opcode_call) * fp)

/-
All the trace data and constraints (except for the probabilistic assumptions, and assumption
  `char F > 2^16`)
-/

structure constraints {F : Type*} [field F] [fintype F] (inp : input_data_aux F) :=
/- the execution trace -/
(fp             : fin (inp.T + 1) → F)
(ap             : fin (inp.T + 1) → F)
(pc             : fin (inp.T + 1) → F)
/- the sequence of instructions -/
(inst           : fin inp.T → F)
(off_op0_tilde  : fin inp.T → F)
(off_op1_tilde  : fin inp.T → F)
(off_dst_tilde  : fin inp.T → F)
(f_tilde        : fin inp.T → tilde_type F)
/- the memory accesses-/
(dst_addr       : fin inp.T → F)
(dst            : fin inp.T → F)
(op0_addr       : fin inp.T → F)
(op0            : fin inp.T → F)
(op1_addr       : fin inp.T → F)
(op1            : fin inp.T → F)
/- starting and ending constraints -/
(h_pc_I         : pc 0 = inp.pc_I)
(h_ap_I         : ap 0 = inp.ap_I)
(h_fp_I         : fp 0 = inp.ap_I)
(h_pc_F         : pc (fin.last inp.T) = inp.pc_F)
(h_ap_F         : ap (fin.last inp.T) = inp.ap_F)
/- the main constraints -/
(mc             : memory_constraints inp.T (λ i : fin inp.T, pc (i.cast_succ)) inst
                    dst_addr dst op0_addr op0 op1_addr op1 inp.mem_star)
(rc             : range_check_constraints inp.T off_op0_tilde off_op1_tilde off_dst_tilde
                    inp.rc_min inp.rc_max)
(ic             : ∀ i : fin inp.T, instruction_constraints
                          (inst i)
                          (off_op0_tilde i)
                          (off_op1_tilde i)
                          (off_dst_tilde i)
                          (f_tilde i))
(sc             : ∀ i : fin inp.T, step_constraints
                          (off_op0_tilde i)
                          (off_op1_tilde i)
                          (off_dst_tilde i)
                          (f_tilde i)
                          (fp i.cast_succ)
                          (ap i.cast_succ)
                          (pc i.cast_succ)
                          (fp i.succ)
                          (ap i.succ)
                          (pc i.succ)
                          (dst_addr i)
                          (op0_addr i)
                          (op1_addr i)
                          (dst i)
                          (op0 i)
                          (op1 i))
