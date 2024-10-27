/-
A proof of the main theorem of the whitepaper:

Given a collection of data meeting all the constraints in `constraints`, assuming the extra
probabilistic assumptions hold, there is an execution trace according to the semantics given in
`cpu`, with the given length, start state, and final value of the program counter.
-/
import Verification.Semantics.Cpu
import Verification.Semantics.AirEncoding.Constraints
import Verification.Semantics.AirEncoding.Memory
import Verification.Semantics.AirEncoding.RangeCheck
import Verification.Semantics.AirEncoding.Instruction
import Verification.Semantics.AirEncoding.Step
import Verification.Semantics.AirEncoding.RangeCheckBuiltin

open scoped Classical

-- assume F is a finite field
variable {F : Type} [Field F] [Fintype F]

/- The probabilistic assumptions.  -/

structure Hprob {inp : InputDataAux F} (c : Constraints inp) where
  hprob₁ :
    (c.mc).mb.alpha ∉
      badSet1 (realA inp.memStar c.mc.a c.mc.em.embedMem)
        (realV inp.memStar c.mc.v c.mc.em.embedMem) c.mc.mb.a' c.mc.mb.v'
  hprob₂ :
    c.mc.mb.z ∉
      badSet2 (realA inp.memStar c.mc.a c.mc.em.embedMem)
        (realV inp.memStar c.mc.v c.mc.em.embedMem) c.mc.mb.a' c.mc.mb.v' c.mc.mb.alpha
  hprob₃ : ((c.mc).mb).z ≠ 0
  hprob₄ : c.rc.z ∉ badSet3 c.rc.a c.rc.a'

/-- The main theorem: if the constraints hold for the trace data, then for any memory assignment
that agrees with the input data, the memory locations associated with the range check builtin
have been range checked, and there is an execution trace that agrees with the input data.
-/
theorem execution_exists (char_ge : ringChar F ≥ 2 ^ 63) (inp : InputDataAux F)
    (c : Constraints inp) (hp : Hprob c) :
    ∃ mem : F → F,
      Option.FnExtends mem inp.memStar ∧
        (∀ i < inp.rcLen, ∃ (n : ℕ), n < 2 ^ 128 ∧ mem (inp.initialRcAddr + i) = (↑n : F)) ∧
          ∃ exec : Fin (inp.t + 1) → RegisterState F,
            (exec 0).pc = inp.pcI ∧
              (exec 0).ap = inp.apI ∧
                (exec 0).fp = inp.apI ∧
                  (exec (Fin.last inp.t)).pc = inp.pcF ∧
                    (exec (Fin.last inp.t)).ap = inp.apF ∧
                      ∀ i : Fin inp.t, NextState mem (exec i.castSucc) (exec i.succ) := by
  have char_gt : ringChar F > 2 ^ 16 := by
    apply lt_of_lt_of_le _ char_ge
    apply pow_lt_pow_right <;> norm_num
  let m := mem c.mc.mb.a' c.mc.mb.v'
  have mem_extends : Option.FnExtends m inp.memStar :=
    mem_extends c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedDom c.mc.em.h_embedVal c.mc.em.h_embedMem_inj hp.hprob₃
      hp.hprob₁ hp.hprob₂ c.mc.h_n_lt
  have mem_pcAddr : ∀ i : Fin inp.t, m (c.pc i.castSucc) = c.inst i :=
    mem_pc c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embed_pc c.mc.em.h_embedInst c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_inst hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_dst_addr : ∀ i, m (c.dstAddr i) = c.dst i :=
    mem_dst_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedDstAddr c.mc.em.h_embedDst c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_dst hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_op0Addr : ∀ i, m (c.op0Addr i) = c.op0 i :=
    mem_op0_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedOp0Addr c.mc.em.h_embedOp0 c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_op0 hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_op1Addr : ∀ i, m (c.op1Addr i) = c.op1 i :=
    mem_op1_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedOp1Addr c.mc.em.h_embedOp1 c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_op1 hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_rcAddr : ∀ i, m (c.rcAddr i) = c.rcVal i :=
    mem_rc_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedRcAddr c.mc.em.h_embedRc c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_rc hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have off_op0_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offOp0Tilde i = ↑k :=
    off_op0_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedOp0 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have off_op1_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offOp1Tilde i = ↑k :=
    off_op1_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedOp1 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have off_dst_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offDstTilde i = ↑k :=
    off_dst_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedDst c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have rc16Vals_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.rc16Val i = ↑k :=
    rc16_vals_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedRc16 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have range_checked : ∀ i < inp.rcLen, ∃ n : ℕ,n < 2 ^ 128 ∧ m (inp.initialRcAddr + i) = ↑n := by
    intro i hi
    rcases rc_val_checked rc16Vals_in_range c.rcb.h_rcValue ⟨i, hi⟩ with ⟨n, nlt, neq⟩
    use n, nlt
    rw [← neq, ←mem_rcAddr]
    rw [rc_addr_eq c.rcb.h_rc_init_addr c.rcb.h_rcAddr_step ⟨i, hi⟩]
  use m, mem_extends, range_checked
  let e := fun i : Fin (inp.t + 1) => RegisterState.mk (c.pc i) (c.ap i) (c.fp i)
  use e, c.h_pcI, c.h_apI, c.h_fpI, c.h_pcF, c.h_apF
  intro i
  show NextState m (e i.castSucc) (e i.succ)
  let inst' :=
    theInstruction (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have inst_eq : c.inst i = ↑inst'.toNat :=
    inst_eq (c.ic i).h_instruction (c.ic i).h_bit (c.ic i).h_last_value (off_op0_in_range i)
      (off_op1_in_range i) (off_dst_in_range i)
  have offDstTilde_eq : c.offDstTilde i = ↑inst'.offDst.toNat :=
    offDst_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have offOp0Tilde_eq : c.offOp0Tilde i = ↑inst'.offOp0.toNat :=
    offOp0_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have offOp1Tilde_eq : c.offOp1Tilde i = ↑inst'.offOp1.toNat :=
    offOp1_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have f_tilde_to_f_eq : ∀ j, (c.fTilde i).toF j = ↑(Bool.toNat (BitVec.getLsbD inst'.flags j)) :=
    f_tilde_toF_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  exact
    nextState_eq offDstTilde_eq offOp0Tilde_eq offOp1Tilde_eq f_tilde_to_f_eq
      ((mem_pcAddr i).trans inst_eq) (mem_dst_addr i) (mem_op0Addr i) (mem_op1Addr i)
      (c.sc i).h_dstAddr (c.sc i).h_op0Addr (c.sc i).h_op1Addr (c.sc i).h_mul (c.sc i).h_res
      (c.sc i).h_t0_eq (c.sc i).h_t1_eq (c.sc i).h_nextPc_eq (c.sc i).h_nextPc_eq'
      (c.sc i).h_opcode_call (c.sc i).h_opcode_call' (c.sc i).h_opcode_assert_eq (c.sc i).h_nextAp
      (c.sc i).h_nextFp
