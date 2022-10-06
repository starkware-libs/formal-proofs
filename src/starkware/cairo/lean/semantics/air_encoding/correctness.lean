/-
A proof of the main theorem of the whitepaper:

Given a collection of data meeting all the constraints in `constraints`, assuming the extra
probabilistic assumptions hold, there is an execution trace according to the semantics given in
`cpu`, with the given length, start state, and final value of the program counter.
-/
import starkware.cairo.lean.semantics.cpu
import starkware.cairo.lean.semantics.air_encoding.constraints
import starkware.cairo.lean.semantics.air_encoding.memory
import starkware.cairo.lean.semantics.air_encoding.range_check
import starkware.cairo.lean.semantics.air_encoding.instruction
import starkware.cairo.lean.semantics.air_encoding.step

open_locale classical

/- assume F is a sufficiently large finite field -/
variables {F : Type} [field F] [fintype F]

/-
The probabilistic assumptions.
-/

structure hprob {inp : input_data_aux F} (c : constraints inp) :=
(hprob₁ : c.mc.mb.alpha ∉ bad_set_1 (real_a inp.mem_star c.mc.a c.mc.em.embed_mem)
                            (real_v inp.mem_star c.mc.v c.mc.em.embed_mem) c.mc.mb.a' c.mc.mb.v')
(hprob₂ : c.mc.mb.z ∉ bad_set_2 (real_a inp.mem_star c.mc.a c.mc.em.embed_mem)
                            (real_v inp.mem_star c.mc.v c.mc.em.embed_mem) c.mc.mb.a' c.mc.mb.v'
                            c.mc.mb.alpha)
(hprob₃ : c.mc.mb.z ≠ 0)
(hprob₄ : c.rc.z ∉ bad_set_3 c.rc.a c.rc.a')

/--
The main theorem: if the constraints hold for the trace data, then for any memory assignment
that agrees with the input data, there is an execution trace that agrees with the input data.
-/

theorem execution_exists (char_ge : ring_char F ≥ 2^63)
    (inp : input_data_aux F) (c : constraints inp) (hp : hprob c) :
  ∃ mem : F → F, option.fn_extends mem inp.mem_star ∧
    ∃ exec : fin (inp.T + 1) → register_state F,
      (exec 0).pc = inp.pc_I ∧
      (exec 0).ap = inp.ap_I ∧
      (exec 0).fp = inp.ap_I ∧
      (exec (fin.last inp.T)).pc = inp.pc_F ∧
      (exec (fin.last inp.T)).ap = inp.ap_F ∧
    ∀ i : fin inp.T, next_state mem (exec i.cast_succ) (exec i.succ) :=
begin
  have char_gt : ring_char F > 2^16,
  { apply lt_of_lt_of_le _ char_ge, apply pow_lt_pow; norm_num },
  let m := mem c.mc.mb.a' c.mc.mb.v',
  have mem_extends : option.fn_extends m inp.mem_star :=
         mem_extends c.mc.mb.h_continuity c.mc.mb.h_single_valued
           c.mc.mb.h_initial c.mc.mb.h_cumulative c.mc.mb.h_final c.mc.em.h_embed_dom
           c.mc.em.h_embed_val c.mc.em.h_embed_mem_inj hp.hprob₃ hp.hprob₁ hp.hprob₂ c.mc.h_n_lt,
  have mem_pc_addr : ∀ i : fin inp.T, m (c.pc i.cast_succ) = c.inst i :=
         mem_pc c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial
           c.mc.mb.h_cumulative c.mc.mb.h_final c.mc.em.h_embed_pc c.mc.em.h_embed_inst
           c.mc.em.h_embed_dom c.mc.em.h_embed_val c.mc.em.h_embed_mem_inj
           c.mc.em.h_embed_mem_disj_inst hp.hprob₃ hp.hprob₁ hp.hprob₂ c.mc.h_n_lt,
  have mem_dst_addr : ∀ i, m (c.dst_addr i) = c.dst i :=
         mem_dst_addr
           c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
           c.mc.mb.h_final c.mc.em.h_embed_dst_addr c.mc.em.h_embed_dst c.mc.em.h_embed_dom
           c.mc.em.h_embed_val c.mc.em.h_embed_mem_inj c.mc.em.h_embed_mem_disj_dst
           hp.hprob₃ hp.hprob₁ hp.hprob₂ c.mc.h_n_lt,
  have mem_op0_addr : ∀ i, m (c.op0_addr i) = c.op0 i :=
        mem_op0_addr
          c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
          c.mc.mb.h_final c.mc.em.h_embed_op0_addr c.mc.em.h_embed_op0 c.mc.em.h_embed_dom
          c.mc.em.h_embed_val c.mc.em.h_embed_mem_inj c.mc.em.h_embed_mem_disj_op0
          hp.hprob₃ hp.hprob₁ hp.hprob₂ c.mc.h_n_lt,
  have mem_op1_addr : ∀ i, m (c.op1_addr i) = c.op1 i :=
        mem_op1_addr
          c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
          c.mc.mb.h_final c.mc.em.h_embed_op1_addr c.mc.em.h_embed_op1 c.mc.em.h_embed_dom
          c.mc.em.h_embed_val c.mc.em.h_embed_mem_inj c.mc.em.h_embed_mem_disj_op1
          hp.hprob₃ hp.hprob₁ hp.hprob₂ c.mc.h_n_lt,
  have off_op0_in_range : ∀ i, ∃ k : ℕ, k < 2^16 ∧ c.off_op0_tilde i = ↑k :=
        off_op0_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final
        c.rc.h_rc_min c.rc.h_rc_max c.rc.h_embed_op0 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt
        hp.hprob₄,
  have off_op1_in_range : ∀ i, ∃ k : ℕ, k < 2^16 ∧ c.off_op1_tilde i = ↑k :=
        off_op1_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final
        c.rc.h_rc_min c.rc.h_rc_max c.rc.h_embed_op1 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt
        hp.hprob₄,
  have off_dst_in_range : ∀ i, ∃ k : ℕ, k < 2^16 ∧ c.off_dst_tilde i = ↑k :=
        off_dst_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final
        c.rc.h_rc_min c.rc.h_rc_max c.rc.h_embed_dst c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt
        hp.hprob₄,
  use [m, mem_extends],
  let e := λ i : fin (inp.T + 1), register_state.mk (c.pc i) (c.ap i) (c.fp i),
  use [e, c.h_pc_I, c.h_ap_I, c.h_fp_I, c.h_pc_F, c.h_ap_F],
  intro i,
  show next_state m (e i.cast_succ) (e i.succ),
  let inst' := the_instruction (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i)
                (off_dst_in_range i),
  have inst_eq : c.inst i = ↑(inst'.to_nat) :=
        inst_eq (c.ic i).h_instruction (c.ic i).h_bit (c.ic i).h_last_value
        (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i),
  have off_dst_tilde_eq : c.off_dst_tilde i = ↑(inst'.off_dst.to_natr) :=
        off_dst_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i)
          (off_dst_in_range i),
  have off_op0_tilde_eq : c.off_op0_tilde i = ↑(inst'.off_op0.to_natr) :=
        off_op0_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i)
          (off_dst_in_range i),
  have off_op1_tilde_eq : c.off_op1_tilde i = ↑(inst'.off_op1.to_natr) :=
        off_op1_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i)
          (off_dst_in_range i),
  have f_tilde_to_f_eq : ∀ j, (c.f_tilde i).to_f j = ↑((inst'.flags.nth j).to_nat) :=
      f_tilde_to_f_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i)
        (off_dst_in_range i),
  exact next_state_eq off_dst_tilde_eq off_op0_tilde_eq off_op1_tilde_eq f_tilde_to_f_eq
    ((mem_pc_addr i).trans inst_eq) (mem_dst_addr i) (mem_op0_addr i) (mem_op1_addr i)
    (c.sc i).h_dst_addr (c.sc i).h_op0_addr (c.sc i).h_op1_addr (c.sc i).h_mul
    (c.sc i).h_res (c.sc i).h_t0_eq (c.sc i).h_t1_eq (c.sc i).h_next_pc_eq (c.sc i).h_next_pc_eq'
    (c.sc i).h_opcode_call (c.sc i).h_opcode_call' (c.sc i).h_opcode_assert_eq
    (c.sc i).h_next_ap (c.sc i).h_next_fp
end

