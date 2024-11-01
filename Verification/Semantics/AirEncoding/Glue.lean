/-
This file translates the autogenerated data and constraints to the form used in the formalization.
-/
import Verification.Semantics.AirEncoding.ConstraintsAutogen
import Verification.Semantics.AirEncoding.Constraints
import Verification.Semantics.AirEncoding.Memory
import Verification.Semantics.AirEncoding.RangeCheck
import Verification.Semantics.Soundness.Hoare

open scoped Classical BigOperators

noncomputable section

variable {F : Type _} [Field F] [Fintype F]

theorem fin2_15_val : @Fin.val 15 2 = 2 := rfl
theorem fin3_15_val : @Fin.val 15 3 = 3 := rfl
theorem fin4_15_val : @Fin.val 15 4 = 4 := rfl
theorem fin5_15_val : @Fin.val 15 5 = 5 := rfl
theorem fin6_15_val : @Fin.val 15 6 = 6 := rfl
theorem fin7_15_val : @Fin.val 15 7 = 7 := rfl
theorem fin8_15_val : @Fin.val 15 8 = 8 := rfl
theorem fin9_15_val : @Fin.val 15 9 = 9 := rfl
theorem fin10_15_val : @Fin.val 15 10 = 10 := rfl
theorem fin11_15_val : @Fin.val 15 11 = 11 := rfl
theorem fin12_15_val : @Fin.val 15 12 = 12 := rfl
theorem fin13_15_val : @Fin.val 15 13 = 13 := rfl
theorem fin2_8_val : @Fin.val 8 2 = 2 := rfl
theorem fin3_8_val : @Fin.val 8 3 = 3 := rfl
theorem fin4_8_val : @Fin.val 8 4 = 4 := rfl
theorem fin5_8_val : @Fin.val 8 5 = 5 := rfl
theorem fin6_8_val : @Fin.val 8 6 = 6 := rfl
theorem fin7_8_val : @Fin.val 8 7 = 7 := rfl

attribute [local simp] fin2_15_val fin3_15_val fin4_15_val fin5_15_val fin6_15_val fin7_15_val
  fin8_15_val fin9_15_val fin10_15_val fin11_15_val fin12_15_val fin13_15_val
  fin2_8_val fin3_8_val fin4_8_val fin5_8_val fin6_8_val fin7_8_val

-- interpreting instruction constraints
def CpuDecode.toInstructionConstraints {c : Columns F} (cd : CpuDecode c) (j : Nat) :
    InstructionConstraints
      (c.cpuDecodeInstruction (j * 16))                 -- inst
      (c.cpuDecodeOff1 (j * 16))                        -- off_op0_tilde
      (c.cpuDecodeOff2 (j * 16))                        -- off_op1_tilde
      (c.cpuDecodeOff0 (j * 16))                        -- off_dst_tilde
    fun k : Fin 16 => c.cpuDecodeOpcodeRcColumn (j * 16 + k) where
  -- f_tilde
  h_instruction := by
    dsimp
    have := cd.opcode_rc_input (j * 16) (by simp)
    rw [eq_of_sub_eq_zero this]
    ring
  h_bit := by
    intro k; dsimp [TildeType.toF, Column.off]
    simp [mul_sub, ← add_assoc]
    have : ¬(j * 16 + ↑k) % 16 = 15 :=
      by
      rw [add_comm, Nat.add_mul_mod_self_right]; apply ne_of_lt
      have kprop := k.prop
      rw [← Nat.mod_eq_of_lt (lt_trans k.prop (Nat.lt_succ_self _))] at kprop
      exact kprop
    have h := cd.opcode_rc__bit (j * 16 + k) this
    unfold Column.off at h
    simp [← two_mul, mul_sub, ← add_assoc] at h
    exact h
  h_last_value := by
    dsimp
    have : (j * 16 + 15) % 16 = 15 := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.lt_succ_self _)]
    exact cd.opcode_rc__zero (j * 16 + 15) this

-- interpreting execution step constraints
def CpuOperands.toStepConstraints {c : Columns F} {inp : InputData F} (ops : CpuOperands c)
    (upd : CpuUpdateRegisters inp c) (opcodes : CpuOpcodes c) (j : ℕ)
    (hj : j ≠ inp.traceLength / 16 - 1) :
    StepConstraints (c.cpuDecodeOff1 (j * 16))                -- off_op0_tilde
      (c.cpuDecodeOff2 (j * 16))                              -- off_op1_tilde
      (c.cpuDecodeOff0 (j * 16))                              -- off_dst_tilde
      (fun k : Fin 16 => c.cpuDecodeOpcodeRcColumn (j * 16 + k))  -- f_tilde
      (c.cpuRegistersFp (j * 16))                             -- fp
      (c.cpuRegistersAp (j * 16))                             -- ap
      (c.cpuDecodePc (j * 16))                                -- pc
      (c.cpuRegistersFp ((j + 1) * 16))                       -- next fp
      (c.cpuRegistersAp ((j + 1) * 16))                       -- next ap
      (c.cpuDecodePc ((j + 1) * 16))                          -- next pc
      (c.cpuOperandsMemDstAddr (j * 16))                      -- dst_addr
      (c.cpuOperandsMemOp0Addr (j * 16))                      -- op0_addr
      (c.cpuOperandsMemOp1Addr (j * 16))                      -- op1_addr
      (c.cpuOperandsMemDstValue (j * 16))                     -- dst
      (c.cpuOperandsMemOp0Value (j * 16))                     -- op0
      (c.cpuOperandsMemOp1Value (j * 16))                     -- op1
      :=
  have h0 : j * 16 % 16 = 0 := by simp
  have h1 : ¬j * 16 = 16 * (inp.traceLength / 16 - 1) := by
    rwa [mul_comm, mul_right_inj' _]
    norm_num
  { mul := c.cpuOperandsOpsMul (j * 16)
    res := c.cpuOperandsRes (j * 16)
    t0 := c.cpuUpdateRegistersUpdatePcTmp0 (j * 16)
    t1 := c.cpuUpdateRegistersUpdatePcTmp1 (j * 16)
    h_dstAddr := by
      simp [TildeType.fDstReg, TildeType.toF, Column.off, two_mul]
      have h := ops.mem_dst_addr _ h0
      simp [Column.off] at h
      rw [sub_eq_zero] at h
      rw [← sub_eq_iff_eq_add.mpr h.symm]
      ring
    h_op0Addr := by
      simp [TildeType.fOp0Reg, TildeType.toF, Column.off, two_mul]
      have h := ops.mem0_addr _ h0
      simp [Column.off] at h
      rw [sub_eq_zero] at h
      rw [← sub_eq_iff_eq_add.mpr h.symm]
      ring
    h_op1Addr := by
      simp [TildeType.fOp1Imm, TildeType.fOp1Ap, TildeType.fOp1Fp, TildeType.toF, Column.off, two_mul]
      have h := ops.mem1_addr _ h0
      simp [Column.off] at h
      rw [sub_eq_zero] at h
      rw [← sub_eq_iff_eq_add.mpr h.symm]
      ring
    h_mul := eq_of_sub_eq_zero (ops.ops_mul _ h0)
    h_res := by
      simp [TildeType.fPcJnz, TildeType.fResAdd, TildeType.fResMul, TildeType.toF, Column.off, two_mul]
      have h := ops.res _ h0
      rw [sub_eq_zero] at h
      trans
      apply h
      repeat rw [Column.off]
      ring
    h_t0_eq := by
      simp [TildeType.fPcJnz, TildeType.toF, Column.off, two_mul]
      exact eq_of_sub_eq_zero (upd.update_pc__tmp0 _ ⟨h0, h1⟩)
    h_t1_eq := eq_of_sub_eq_zero (upd.update_pc__tmp1 _ ⟨h0, h1⟩)
    h_nextPc_eq := by
      dsimp
      simp only [TildeType.fPcJnz, TildeType.fOp1Imm, TildeType.toF, Column.off, two_mul,
        add_zero, Fin.val_two, Fin.val_succ, Fin.coe_castSucc, add_mul]
      have h := upd.update_pc__pc_cond_positive _ ⟨h0, h1⟩
      convert h using 2
      simp [Column.off]
      ring
    h_nextPc_eq' := by
      dsimp
      rw [← upd.update_pc__pc_cond_negative _ ⟨h0, h1⟩]
      simp [TildeType.fPcJnz, TildeType.fPcJumpAbs, TildeType.fPcJumpRel, TildeType.fOp1Imm,
        TildeType.toF, Column.off, two_mul, add_zero, add_mul, Fin.val_two,
        Fin.val_succ, Fin.coe_castSucc]
      ring
    h_opcode_call := by
      rw [← opcodes.call__push_fp _ h0]
      dsimp
      simp only [TildeType.fOpcodeCall, TildeType.toF, Column.off, add_zero, Fin.val_succ,
        Fin.coe_castSucc, ← two_mul]
      rfl
    h_opcode_call' := by
      rw [← opcodes.call__push_pc _ h0]
      simp [TildeType.fOpcodeCall, TildeType.fOp1Imm, TildeType.toF, Column.off, add_zero,
        Fin.val_succ, Fin.coe_castSucc, ← two_mul]
      left
      ring
    h_opcode_assert_eq := by
      rw [← opcodes.assert_eq__assert_eq _ h0]
      dsimp
      simp only [TildeType.fOpcodeAssertEq, TildeType.toF, Column.off, add_zero, Fin.val_succ,
        Fin.coe_castSucc, ← two_mul]
      rfl
    h_nextAp := by
      dsimp
      simp only [add_mul, one_mul, Column.off, add_zero]
      trans
      · exact eq_of_sub_eq_zero (upd.update_ap__ap_update _ ⟨h0, h1⟩)
      simp only [TildeType.fOpcodeCall, TildeType.fApAdd, TildeType.fApAdd1, TildeType.toF,
        Column.off, Fin.val_succ, Fin.coe_castSucc, ← two_mul]
      norm_num
      ring
    h_nextFp := by
      dsimp
      simp only [add_mul, one_mul, Column.off, add_zero]
      trans
      · exact eq_of_sub_eq_zero (upd.update_fp__fp_update _ ⟨h0, h1⟩)
      simp [TildeType.fOpcodeCall, TildeType.fOpcodeRet, TildeType.toF, Column.off,
        Fin.val_succ, Fin.coe_castSucc, ← two_mul]
      ring
  }

/-
interpreting range check constraints

Note: there are inp.traceLength / 16 - 1 steps (so the execution trace, including
the last step, has length inp.traceLength / 16), but there are inp.traceLength / 16
many 16-bit range-checked elements.
-/
def Rc16.toRangeCheckConstraints {c : Columns F} {ci : ColumnsInter F} {inp : InputData F}
    {pd : PublicData F} (rc16 : Rc16 inp pd c ci) (traceLength_pos : inp.traceLength > 0)
    (public_memory_prod_eq_one : pd.rc16PermPublicMemoryProd = 1)
    (traceLength_le_char : inp.traceLength ≤ ringChar F) :
    RangeCheckConstraints (inp.traceLength / 16 - 1) -- T
      (inp.traceLength / 16) -- rc16_len
      (fun j => c.cpuDecodeOff1 (j * 16))  -- off_op0_tilde : fin T → F
      (fun j => c.cpuDecodeOff2 (j * 16)) -- off_op1_tilde : fin T → F
      (fun j => c.cpuDecodeOff0 (j * 16))  -- off_dst_tilde : fin T → F
      (fun j => c.rcBuiltinInnerRc (j * 16))  -- rc16_val : fin rc16_len → F
      pd.rcMin
      pd.rcMax :=
  have h :
    ∀ j : ℕ, ∀ i : Fin (inp.traceLength / 16 - 1), j < 16 → ↑i * 16 + j < inp.traceLength - 1 + 1 := by
     rintro j ⟨i, ilt⟩ jlt
     rw [Nat.sub_add_cancel traceLength_pos]
     apply lt_of_lt_of_le (add_lt_add_left jlt _)
     suffices (i + 1) * 16 ≤ inp.traceLength by
       rwa [add_mul] at this
     apply le_trans (Nat.mul_le_mul_right _ _) (Nat.div_mul_le_self _ 16)
     exact lt_of_lt_of_le ilt (Nat.pred_le _)
  have h' :
    ∀ j : ℕ, ∀ i : Fin (inp.traceLength / 16), j < 16 → ↑i * 16 + j < inp.traceLength - 1 + 1 := by
     rintro j ⟨i, ilt⟩ jlt
     rw [Nat.sub_add_cancel traceLength_pos]
     apply lt_of_lt_of_le (add_lt_add_left jlt _)
     suffices (i + 1) * 16 ≤ inp.traceLength by rwa [add_mul] at this
     apply le_trans (Nat.mul_le_mul_right _ _) (Nat.div_mul_le_self _ 16)
     exact Nat.succ_le_of_lt ilt
  { n := inp.traceLength - 1
    a := fun i => c.rc16Pool i
    a' := fun i => c.rc16Sorted i
    p := fun i => ci.rc16PermCumProd0 i
    z := pd.rc16PermInteractionElm
    embedOffOp0 := fun i => by use (i.val) * 16 + 8; apply h 8 i; norm_num1
    embedOffOp1 := fun i => by use (i.val) * 16 + 4; apply h 4 i; norm_num1
    embedOffDst := fun i => by use (i.val) * 16; apply h 0 i; norm_num1
    embedRc16Vals := fun i => by use (i.val) * 16 + 12; apply h' 12 i; norm_num1
    h_embedOp0 := fun i => by simp only [Columns.cpuDecodeOff1, Column.off]; rfl
    h_embedOp1 := fun i => by simp only [Columns.cpuDecodeOff2, Column.off]; rfl
    h_embedDst := fun i => by simp only [Columns.cpuDecodeOff0, Column.off]; rfl
    h_embedRc16 := fun i => by dsimp [Column.off]
    h_continuity := by
      intro i
      rw [← Rc16.diff_is_bit rc16 _ (ne_of_lt i.is_lt), mul_sub, mul_one]
      simp; rfl
    h_initial := by
      rw [← sub_eq_zero, ← Rc16.perm__init0 rc16 _ rfl]
      simp [Column.off]; abel
    h_cumulative := by
      intro i
      rw [← sub_eq_zero, ← Rc16.perm__step0 rc16 _ (ne_of_lt i.is_lt)]
      simp [Column.off]
    h_final := (eq_of_sub_eq_zero (Rc16.perm__last rc16 _ rfl)).trans public_memory_prod_eq_one
    h_rc_min := eq_of_sub_eq_zero <| Rc16.minimum rc16 _ rfl
    h_rcMax := eq_of_sub_eq_zero <| Rc16.maximum rc16 _ rfl
    h_n_lt := by
      apply Nat.lt_of_succ_le
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel traceLength_pos]
      exact traceLength_le_char }

-- interpreting memory constraints
def Memory.toMemoryBlockConstraints {inp : InputData F} {pd : PublicData F} {c : Columns F}
    {ci : ColumnsInter F}
    (h_mem_star :
      let z := pd.memoryMultiColumnPermPermInteractionElm
      let alpha := pd.memoryMultiColumnPermHashInteractionElm0
      let p := pd.memoryMultiColumnPermPermPublicMemoryProd
      let dom_m_star := { x // Option.isSome (inp.mStar x) }
      (p * ∏ a : dom_m_star, (z - (a.val + alpha * memVal a))) = z ^ Fintype.card dom_m_star)
    (m : Memory inp pd c ci) :
    MemoryBlockConstraints (inp.traceLength / 2 - 1)           -- n
      (fun i => c.memPoolAddr (2 * i))                         -- a
      (fun i => c.memPoolValue (2 * i))                        -- v
      inp.mStar :=
  have h0 : ∀ j : Fin (inp.traceLength / 2 - 1), (↑j : ℕ) * 2 % 2 = 0 := by intro j; simp
  have h1 : ∀ j : Fin (inp.traceLength / 2 - 1), ¬↑j * 2 = 2 * (inp.traceLength / 2 - 1) := by
    rintro ⟨j, jlt⟩
    have hj : j ≠ inp.traceLength / 2 - 1 := ne_of_lt jlt
    rwa [mul_comm, mul_right_inj' _]; norm_num
  { a' := fun j => c.column20 (2 * j)
    v' := fun j => c.column20 (2 * j + 1)
    p := fun j => ci.column24Inter1 (2 * j)
    alpha := pd.memoryMultiColumnPermHashInteractionElm0
    z := pd.memoryMultiColumnPermPermInteractionElm
    h_continuity := by
      intro j
      rw [← m.diff_is_bit (↑j * 2) ⟨h0 j, h1 j⟩]
      simp [Column.off, add_mul, mul_comm 2]; ring
    h_single_valued := by
      intro j
      apply neg_inj.mp
      rw [neg_zero, ← m.is_func (↑j * 2) ⟨h0 j, h1 j⟩]
      simp [Column.off, add_mul, mul_add, mul_comm 2, add_assoc]
      ring
    h_initial := by
      rw [← sub_eq_zero, ← m.multi_column_perm__perm__init0 _ rfl]
      simp [Column.off]; ring
    h_cumulative := by
      intro j
      rw [← sub_eq_zero, ← m.multi_column_perm__perm__step0 (↑j * 2) ⟨h0 j, h1 j⟩]
      simp [Column.off, add_mul, mul_add, mul_comm 2, add_assoc]
    h_final := by
      simp only
      apply Eq.trans _ h_mem_star
      rw [← eq_of_sub_eq_zero (m.multi_column_perm__perm__last _ rfl), Column.off]
      simp only [add_zero, Fin.val_last]
      rfl }

-- interpreting range check builtin constraints
/-- Use 8 16-bit range-checked elements for each 128-bit range-checked element -/
def rcToRc16 {inp : InputData F} :
    Fin (inp.traceLength / 128) → Fin 8 → Fin (inp.traceLength / 16) := fun i j =>
  ⟨i * 8 + j, by
    cases' i with i hi
    cases' j with j hj
    calc
      ↑i * 8 + ↑j < (i + 1) * 8 := by rw [add_mul, one_mul]; apply add_lt_add_left hj
      _ = (i + 1) * 8 * 16 / 16 := by rw [Nat.mul_div_cancel]; norm_num
      _ ≤ inp.traceLength / 16 := by
        apply Nat.div_le_div_right; rw [mul_assoc]; norm_num
        rw [← Nat.le_div_iff_mul_le]; exact Nat.succ_le_of_lt hi; norm_num
      ⟩

def RcBuiltin.toRcBuiltinConstraints {inp : InputData F} {pd : PublicData F} {c : Columns F}
    (rcb : RcBuiltin inp pd c) :
    RcBuiltinConstraints (inp.traceLength / 16) pd.initialRcAddr (inp.traceLength / 128)
      (fun j => c.rcBuiltinInnerRc (j * 16)) (fun j => c.rcBuiltinMemAddr (j * 128))
      (fun j => c.rcBuiltinMemValue (j * 128)) rcToRc16
    where
  h_rc_init_addr h := eq_of_sub_eq_zero (rcb.init_addr _ rfl)
  h_rcAddr_step := by
    intro i hi
    have := rcb.addr_step (i * 128)
    simp [Column.off, Nat.succ_eq_add_one, add_mul, one_mul, add_assoc]
    apply eq_of_sub_eq_zero (this _)
    constructor
    . apply Nat.mul_mod_left
    rw [mul_comm _ 128, mul_left_cancel_iff_of_pos (show 0 < 128 by norm_num)]
    contrapose! hi
    rw [hi, Nat.succ_eq_add_one]
    apply le_tsub_add
  h_rcValue := by
    intro i
    have := rcb.value (i * 128)
    simp at this
    rw [Columns.rcBuiltinMemValue, ← eq_of_sub_eq_zero this]
    simp only [rcToRc16, Columns.rcBuiltinInnerRc]
    simp [Fin.val_zero, add_zero, Fin.val_one, Fin.val_two, add_mul, mul_assoc, Column.off]

omit [Field F] in
theorem card_dom_aux {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength) :
    4 * Fintype.card { x // Option.isSome (inp.mStar x) } ≤ inp.traceLength / 2 - 1 := by
  apply Nat.le_pred_of_lt
  apply Nat.lt_of_succ_le
  simp only [Nat.sub_eq, tsub_zero]
  rw [Nat.le_div_iff_mul_le' (show 0 < 2 by norm_num), Nat.succ_mul, mul_comm, ← mul_assoc]
  norm_num
  exact h_card

def embedMem {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (a : MemDom inp.mStar) : Fin (inp.traceLength / 2 - 1 + 1) :=
  let i := (Fintype.equivFin { x // Option.isSome (inp.mStar x) }).toFun a
  ⟨4 * i.val + 1, Nat.succ_lt_succ
    (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left i.is_lt (by norm_num)) (card_dom_aux h_card))⟩

def PublicMemory.toMemoryEmbeddingConstraints {c : Columns F} {inp : InputData F}
    (pm : PublicMemory c)
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength) :
    MemoryEmbeddingConstraints (inp.traceLength / 16 - 1)       -- T
      (inp.traceLength / 128)                                   -- rc_len
      (fun j => c.cpuDecodePc (j * 16))                         -- pc
      (fun j => c.cpuDecodeInstruction (j * 16))                -- inst
      (fun j => c.cpuOperandsMemDstAddr (j * 16))               -- dst_addr
      (fun j => c.cpuOperandsMemDstValue (j * 16))              -- dst
      (fun j => c.cpuOperandsMemOp0Addr (j * 16))               -- op0_addr
      (fun j => c.cpuOperandsMemOp0Value (j * 16))              -- op0
      (fun j => c.cpuOperandsMemOp1Addr (j * 16))               -- op1_addr
      (fun j => c.cpuOperandsMemOp1Value (j * 16))              -- op1
      (fun j => c.rcBuiltinMemAddr (j * 128))                   -- rc_addr
      (fun j => c.rcBuiltinMemValue (j * 128))                  -- rc
      inp.mStar                                                 -- mem_star
      (inp.traceLength / 2 - 1)                                 -- n
      (fun i => c.memPoolAddr (2 * i))                          -- a
    fun i => c.memPoolValue (2 * i)                             -- v
  :=
  have
    h :
    ∀ j : ℕ,
      ∀ i : Fin (inp.traceLength / 16 - 1), j < 8 → ↑i * 8 + j < inp.traceLength / 2 - 1 + 1 := by
    rintro j ⟨i, ilt⟩ jlt
    apply Nat.lt_succ_of_le
    apply Nat.le_pred_of_lt
    have : i * 8 + j < (i + 1) * 8 := by rw [add_mul, one_mul]; exact add_lt_add_left jlt _
    apply lt_of_lt_of_le this
    simp only [Nat.sub_eq, tsub_zero]
    rw [Nat.le_div_iff_mul_le' (show 0 < 2 by norm_num), mul_assoc]
    norm_num
    rw [← Nat.le_div_iff_mul_le' (show 0 < 16 by norm_num)]
    apply Nat.succ_le_of_lt
    exact lt_of_lt_of_le ilt (Nat.pred_le _)
  have h1 : ∀ i : Fin (inp.traceLength / 128), ↑i * 64 + 51 < inp.traceLength / 2 - 1 + 1 := by
    rintro ⟨i, ilt⟩
    apply Nat.lt_succ_of_le
    apply Nat.le_pred_of_lt
    have : i * 64 + 51 < (i + 1) * 64 := by rw [add_mul]; apply add_lt_add_left; norm_num
    apply lt_of_lt_of_le this
    apply le_trans (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ilt))
    simp only [Nat.sub_eq, tsub_zero]
    rw [Nat.le_div_iff_mul_le' (show 0 < 2 by norm_num), mul_assoc]
    norm_num
    apply Nat.div_mul_le_self
  have jaux : ∀ j : Fin (inp.traceLength / 16 - 1), (j : ℕ) * 8 = 4 * (2 * j) := by
    intro j; rw [← mul_assoc, mul_comm (4 * 2)]; norm_num
  { embedInst := fun i => by use (i.val) * 8 + 0; apply h 0 i; norm_num1
    embedDst := fun i => by use (i.val) * 8 + 4; apply h 4 i; norm_num1
    embedOp0 := fun i => by use (i.val) * 8 + 2; apply h 2 i; norm_num1
    embedOp1 := fun i => by use (i.val) * 8 + 6; apply h 6 i; norm_num1
    embedRc := fun i => by use (i.val) * 64 + 51; exact h1 i
    embedMem := embedMem h_card
    h_embed_pc := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedInst := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedDstAddr := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedDst := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedOp0Addr := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedOp0 := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedOp1Addr := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedOp1 := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedRcAddr := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedRc := by intro i; dsimp [Column.off]; congr 1; ring
    h_embedDom := by
      intro a; simp [Column.off]
      apply pm.addr_zero; simp; rw [← mul_assoc]
      exact Nat.mul_mod_right _ _
    h_embedVal := by
      intro a; simp [Column.off]
      apply pm.value_zero; simp; rw [← mul_assoc]
      exact Nat.mul_mod_right _ _
    h_embedMem_inj := by
      intro a1 a2; dsimp [embedMem]
      rw [Fin.ext_iff, add_left_inj 1, mul_right_inj' (show 4 ≠ 0 by norm_num), ← Fin.ext_iff]
      apply Equiv.injective
    h_embedMem_disj_inst := by
      intro a j h'
      rw [Fin.ext_iff] at h' ; dsimp at h'
      have := congr_arg (fun n => n % 4) h'; dsimp [embedMem] at this
      rw [add_comm, jaux, Nat.add_mul_mod_self_left] at this
      simp [Nat.mul_mod_right] at this
    h_embedMem_disj_dst := by
      intro a j h'
      rw [Fin.ext_iff] at h' ; dsimp [embedMem] at h'
      have := congr_arg (fun n => n % 4) h'; dsimp at this
      rw [add_comm, add_comm _ 4, jaux, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at this
      norm_num at this
    h_embedMem_disj_op0 := by
      intro a j h'
      rw [Fin.ext_iff] at h' ; dsimp [embedMem] at h'
      have := congr_arg (fun n => n % 4) h'; dsimp at this
      rw [add_comm, add_comm _ 2, jaux, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at this
      norm_num at this
    h_embedMem_disj_op1 := by
      intro a j h'
      rw [Fin.ext_iff] at h' ; dsimp [embedMem] at h'
      have := congr_arg (fun n => n % 4) h'; dsimp at this
      rw [add_comm, add_comm _ 6, jaux, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at this
      norm_num at this
    h_embedMem_disj_rc := by
      intro a j h'
      rw [Fin.ext_iff] at h' ; dsimp [embedMem] at h'
      have jaux' : 64 = 16 * 4 := by norm_num
      have := congr_arg (fun n => n % 4) h'; dsimp at this
      rw [add_comm, add_comm _ 51, Nat.add_mul_mod_self_left] at this
      simp only [jaux', ← mul_assoc] at this
      norm_num at this  }

-- putting it all together
def InputData.toInputDataAux (inp : InputData F) (pd : PublicData F) (rc_max_lt : pd.rcMax < 2 ^ 16)
    (rc_min_le : pd.rcMin ≤ pd.rcMax) : InputDataAux F
    where
  t := inp.traceLength / 16 - 1
  rc16Len := inp.traceLength / 16
  rcLen := inp.traceLength / 128
  pcI := inp.initialPc
  pcF := inp.finalPc
  apI := inp.initialAp
  apF := inp.finalAp
  memStar := inp.mStar
  rcMin := pd.rcMin
  rcMax := pd.rcMax
  initialRcAddr := pd.initialRcAddr
  rcToRc16 := rcToRc16
  h_rc_lt := rc_max_lt
  h_rc_le := rc_min_le

def toConstraints {inp : InputData F} {pd : PublicData F} {c : Columns F} {ci : ColumnsInter F}
    -- autogenerated constraints
    (cd : CpuDecode c)
    (ops : CpuOperands c) (upd : CpuUpdateRegisters inp c) (opcodes : CpuOpcodes c)
    (m : Memory inp pd c ci) (rc : Rc16 inp pd c ci) (pm : PublicMemory c)
    (rcb : RcBuiltin inp pd c) (iandf : ToplevelConstraints inp c)
    -- extra assumptions
    (h_mem_star :
      let z := pd.memoryMultiColumnPermPermInteractionElm
      let alpha := pd.memoryMultiColumnPermHashInteractionElm0
      let p := pd.memoryMultiColumnPermPermPublicMemoryProd
      let dom_m_star := { x // Option.isSome (inp.mStar x) }
      (p * ∏ a : dom_m_star, (z - (a.val + alpha * memVal a))) = z ^ Fintype.card dom_m_star)
    (h_card_dom : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (public_memory_prod_eq_one : pd.rc16PermPublicMemoryProd = 1) (rc_max_lt : pd.rcMax < 2 ^ 16)
    (rc_min_le : pd.rcMin ≤ pd.rcMax) (traceLength_le_char : inp.traceLength ≤ ringChar F) :
    Constraints (inp.toInputDataAux pd rc_max_lt rc_min_le) :=
  have traceLength_pos : inp.traceLength > 0 := lt_of_lt_of_le (Nat.zero_lt_succ _) h_card_dom
  { fp := fun j => c.cpuRegistersFp (j * 16)
    ap := fun j => c.cpuRegistersAp (j * 16)
    pc := fun j => c.cpuDecodePc (j * 16)
    inst := fun j => c.cpuDecodeInstruction (j * 16)
    offOp0Tilde := fun j => c.cpuDecodeOff1 (j * 16)
    offOp1Tilde := fun j => c.cpuDecodeOff2 (j * 16)
    offDstTilde := fun j => c.cpuDecodeOff0 (j * 16)
    rc16Val := fun j => c.rcBuiltinInnerRc (j * 16)
    fTilde := fun j k => c.cpuDecodeOpcodeRcColumn (j * 16 + k)
    dstAddr := fun j => c.cpuOperandsMemDstAddr (j * 16)
    dst := fun j => c.cpuOperandsMemDstValue (j * 16)
    op0Addr := fun j => c.cpuOperandsMemOp0Addr (j * 16)
    op0 := fun j => c.cpuOperandsMemOp0Value (j * 16)
    op1Addr := fun j => c.cpuOperandsMemOp1Addr (j * 16)
    op1 := fun j => c.cpuOperandsMemOp1Value (j * 16)
    rcAddr := fun j => c.rcBuiltinMemAddr (j * 128)
    rcVal := fun j => c.rcBuiltinMemValue (j * 128)
    h_pcI := eq_of_sub_eq_zero (iandf.initialPc _ rfl)
    h_apI := eq_of_sub_eq_zero (iandf.initialAp _ rfl)
    h_fpI := eq_of_sub_eq_zero (iandf.initial_fp _ rfl)
    h_pcF := by simp only; rw [mul_comm _ 16]; exact eq_of_sub_eq_zero (iandf.finalPc _ rfl)
    h_apF := by simp only; rw [mul_comm _ 16]; exact eq_of_sub_eq_zero (iandf.finalAp _ rfl)
    mc :=
      { n := inp.traceLength / 2 - 1
        a := fun i => c.memPoolAddr (2 * i)
        v := fun i => c.memPoolValue (2 * i)
        em := pm.toMemoryEmbeddingConstraints h_card_dom
        mb := m.toMemoryBlockConstraints h_mem_star
        h_n_lt := by
          apply lt_of_lt_of_le _ traceLength_le_char
          apply Nat.lt_of_succ_le
          rw [Nat.sub_one, Nat.succ_pred_eq_of_pos]
          · apply Nat.div_le_self
          apply Nat.div_pos _ (show 0 < 2 by norm_num)
          apply le_trans _ h_card_dom
          apply le_add_left (le_refl _) }
    rc := rc.toRangeCheckConstraints traceLength_pos public_memory_prod_eq_one traceLength_le_char
    ic := fun i => cd.toInstructionConstraints i
    sc := fun i => by
      simp only; rw [Fin.val_succ]
      exact ops.toStepConstraints upd opcodes i (ne_of_lt i.is_lt)
    rcb := rcb.toRcBuiltinConstraints }

-- probabilistic constraints
def bad1 {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (c19 c20 : Column F) : Finset F :=
  badSet1 (realA inp.mStar (fun i => c19 (2 * i)) (embedMem h_card))
    (realV inp.mStar (fun i => c19 (2 * i + 1)) (embedMem h_card)) (fun j => c20 (2 * ↑j)) fun j =>
    c20 (2 * ↑j + 1)

def bad2 {inp : InputData F} (pd : PublicData F)
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (c19 c20 : Column F) : Finset F :=
  badSet2 (realA inp.mStar (fun i => c19 (2 * i)) (embedMem h_card))
    (realV inp.mStar (fun i => c19 (2 * i + 1)) (embedMem h_card)) (fun j => c20 (2 * ↑j))
    (fun j => c20 (2 * ↑j + 1)) pd.memoryMultiColumnPermHashInteractionElm0

def bad3 (inp : InputData F) (c0 c2 : Column F) : Finset F :=
  badSet3 (fun i : Fin (inp.traceLength - 1 + 1) => c0 i) fun i : Fin (inp.traceLength - 1 + 1) =>
    c2 i

set_option linter.unusedSectionVars false in
theorem traceLength_div_two_pos {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength) :
    inp.traceLength / 2 > 0 := by
  apply Nat.div_pos _ (show 0 < 2 by norm_num)
  apply le_trans _ h_card
  apply le_add_left (le_refl _)

theorem bad1_bound {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (c19 c20 : Column F) : (bad1 h_card c19 c20).card ≤ (inp.traceLength / 2) ^ 2 := by
  trans
  apply card_badSet1_le
  rw [Nat.sub_add_cancel, pow_two]
  apply traceLength_div_two_pos h_card

theorem bad2_bound {inp : InputData F} (pd : PublicData F)
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (c19 c20 : Column F) : (bad2 pd h_card c19 c20).card ≤ inp.traceLength / 2 := by
  trans
  apply card_badSet2_le
  rw [Nat.sub_add_cancel]
  apply traceLength_div_two_pos h_card

theorem bad3_bound {inp : InputData F}
    (h_card : 8 * Fintype.card { x // Option.isSome (inp.mStar x) } + 2 ≤ inp.traceLength)
    (c0 c2 : Column F) : (bad3 inp c0 c2).card ≤ inp.traceLength := by
  trans
  apply card_badSet3_le
  rw [Nat.sub_add_cancel]
  exact lt_of_lt_of_le (Nat.zero_lt_succ _) h_card
