/-
The constraints specifying the trace of a Cairo execution.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Verification.Semantics.Cpu

-- for names of flags
open scoped BigOperators

structure InputDataAux (F : Type _) where
  t : Nat
  -- number of 16-bit range-checked elements
  rc16Len : Nat
  pcI : F
  pcF : F
  apI : F
  apF : F
  memStar : F → Option F
  rcMin : Nat
  rcMax : Nat
  -- for range check builtin, first range-checked address
  initialRcAddr : Nat
  -- for range check builtin, number of range-checked values
  rcLen : Nat
  -- constraints
  rcToRc16 : Fin rcLen → Fin 8 → Fin rc16Len
  h_rc_lt : rcMax < 2 ^ 16
  h_rc_le : rcMin ≤ rcMax

-- functions for accessing `memStar`
/-- the domain of the partial memory specification -/
def MemDom {F : Type _} (memStar : F → Option F) :=
  { x // Option.isSome (memStar x) }

/-- the value of the memory -/
def memVal {F : Type _} {memStar : F → Option F} (a : MemDom memStar) : F :=
  Option.get _ (a.property)

instance {F : Type _} [Fintype F] (memStar : F → Option F) : Fintype (MemDom memStar) := by
  rw [MemDom]; infer_instance

-- auxiliary functions for talking about flags extracted from f_tilde
/-- a sequence of trace cells for storing a bitvector of flags -/
def TildeType (F : Type _) := Fin 16 → F

namespace TildeType

variable {F : Type _} [Field F] (f_tilde : TildeType F)

def toF := fun i : Fin 15 => f_tilde (Fin.castSucc i) - 2 * f_tilde i.succ
def fDstReg := f_tilde.toF DST_REG
def fOp0Reg := f_tilde.toF OP0_REG
def fOp1Imm := f_tilde.toF OP1_IMM
def fOp1Fp := f_tilde.toF OP1_FP
def fOp1Ap := f_tilde.toF OP1_AP
def fResAdd := f_tilde.toF RES_ADD
def fResMul := f_tilde.toF RES_MUL
def fPcJumpAbs := f_tilde.toF PC_JUMP_ABS
def fPcJumpRel := f_tilde.toF PC_JUMP_REL
def fPcJnz := f_tilde.toF PC_JNZ
def fApAdd := f_tilde.toF AP_ADD
def fApAdd1 := f_tilde.toF AP_ADD1
def fOpcodeCall := f_tilde.toF OPCODE_CALL
def fOpcodeRet := f_tilde.toF OPCODE_RET
def fOpcodeAssertEq := f_tilde.toF OPCODE_ASSERT_EQ
def instructionSize := f_tilde.fOp1Imm + 1

end TildeType

/-
The constraints on how information is stored in memory.

For some reason, elaboration was too slow (and timed out) before I split this into smaller
structures.
-/
structure MemoryEmbeddingConstraints {F : Type _} [Field F] [Fintype F] (T : Nat) (rcLen : Nat)
    (pc : Fin T → F) (inst : Fin T → F) (dstAddr : Fin T → F) (dst : Fin T → F)
    (op0Addr : Fin T → F) (op0 : Fin T → F) (op1Addr : Fin T → F) (op1 : Fin T → F)
    (rcAddr : Fin rcLen → F)
    -- range check builtin
    (rcVal : Fin rcLen → F)
    (memStar : F → Option F) (n : Nat) (a : Fin (n + 1) → F) (v : Fin (n + 1) → F) where
  -- embedding of data
  embedInst : Fin T → Fin (n + 1)
  embedDst : Fin T → Fin (n + 1)
  embedOp0 : Fin T → Fin (n + 1)
  embedOp1 : Fin T → Fin (n + 1)
  embedRc : Fin rcLen → Fin (n + 1)
  embedMem : MemDom memStar → Fin (n + 1)
  h_embed_pc : ∀ i, a (embedInst i) = pc i
  h_embedInst : ∀ i, v (embedInst i) = inst i
  h_embedDstAddr : ∀ i, a (embedDst i) = dstAddr i
  h_embedDst : ∀ i, v (embedDst i) = dst i
  h_embedOp0Addr : ∀ i, a (embedOp0 i) = op0Addr i
  h_embedOp0 : ∀ i, v (embedOp0 i) = op0 i
  h_embedOp1Addr : ∀ i, a (embedOp1 i) = op1Addr i
  h_embedOp1 : ∀ i, v (embedOp1 i) = op1 i
  h_embedRcAddr : ∀ i, a (embedRc i) = rcAddr i
  h_embedRc : ∀ i, v (embedRc i) = rcVal i
  h_embedDom : ∀ i : MemDom memStar, a (embedMem i) = 0
  h_embedVal : ∀ i : MemDom memStar, v (embedMem i) = 0
  h_embedMem_inj : Function.Injective embedMem
  h_embedMem_disj_inst : ∀ i j, embedMem i ≠ embedInst j
  h_embedMem_disj_dst : ∀ i j, embedMem i ≠ embedDst j
  h_embedMem_disj_op0 : ∀ i j, embedMem i ≠ embedOp0 j
  h_embedMem_disj_op1 : ∀ i j, embedMem i ≠ embedOp1 j
  h_embedMem_disj_rc : ∀ i j, embedMem i ≠ embedRc j

structure MemoryBlockConstraints {F : Type _} [Field F] [Fintype F] (n : Nat) (a : Fin (n + 1) → F)
    (v : Fin (n + 1) → F) (memStar : F → Option F) where
  a' : Fin (n + 1) → F
  v' : Fin (n + 1) → F
  p : Fin (n + 1) → F
  alpha : F
  z : F
  h_continuity : ∀ i : Fin n, (a' i.succ - a' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0
  h_single_valued : ∀ i : Fin n, (v' i.succ - v' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0
  h_initial : (z - (a' 0 + alpha * v' 0)) * p 0 = z - (a 0 + alpha * v 0)
  h_cumulative :
    ∀ i : Fin n,
      (z - (a' i.succ + alpha * v' i.succ)) * p i.succ =
        (z - (a i.succ + alpha * v i.succ)) * p (Fin.castSucc i)
  h_final :
    (p (Fin.last n) * ∏ b : MemDom memStar, (z - (b.val + alpha * memVal b))) = z ^ Fintype.card (MemDom memStar)

structure MemoryConstraints {F : Type _} [Field F] [Fintype F] (T : Nat) (rcLen : Nat)
    (pc : Fin T → F) (inst : Fin T → F) (dstAddr : Fin T → F) (dst : Fin T → F)
    (op0Addr : Fin T → F) (op0 : Fin T → F) (op1Addr : Fin T → F) (op1 : Fin T → F)
    (rcAddr : Fin rcLen → F)
    -- range check builtin
    (rcVal : Fin rcLen → F)
    (memStar : F → Option F) where
  n : Nat
  a : Fin (n + 1) → F
  v : Fin (n + 1) → F
  em :
    MemoryEmbeddingConstraints T rcLen pc inst dstAddr dst op0Addr op0 op1Addr op1 rcAddr
      rcVal memStar n a v
  mb : MemoryBlockConstraints n a v memStar
  h_n_lt : n < ringChar F

/-
Range check constraints.
-/
structure RangeCheckConstraints {F : Type _} [Field F] (T : Nat) (rc16Len : Nat)
    (offOp0Tilde : Fin T → F) (offOp1Tilde : Fin T → F) (offDstTilde : Fin T → F)
    (rc16Val : Fin rc16Len → F) (rc_min : Nat) (rcMax : Nat) where
  n : Nat
  a : Fin (n + 1) → F
  a' : Fin (n + 1) → F
  p : Fin (n + 1) → F
  z : F
  -- embedding of `op0`, `op1`, and `dst` data in `a`
  embedOffOp0 : Fin T → Fin (n + 1)
  embedOffOp1 : Fin T → Fin (n + 1)
  embedOffDst : Fin T → Fin (n + 1)
  embedRc16Vals : Fin rc16Len → Fin (n + 1)
  h_embedOp0 : ∀ i, a (embedOffOp0 i) = offOp0Tilde i
  h_embedOp1 : ∀ i, a (embedOffOp1 i) = offOp1Tilde i
  h_embedDst : ∀ i, a (embedOffDst i) = offDstTilde i
  h_embedRc16 : ∀ i, a (embedRc16Vals i) = rc16Val i
  -- constraints
  h_continuity : ∀ i : Fin n, (a' i.succ - a' (Fin.castSucc i)) * (a' i.succ - a' (Fin.castSucc i) - 1) = 0
  h_initial : (z - a' 0) * p 0 = z - a 0
  h_cumulative : ∀ i : Fin n, (z - a' i.succ) * p i.succ = (z - a i.succ) * p (Fin.castSucc i)
  h_final : p (Fin.last n) = 1
  h_rc_min : a' 0 = rc_min
  h_rcMax : a' (Fin.last n) = rcMax
  h_n_lt : n < ringChar F

/- Constraints for each instruction.  -/
structure InstructionConstraints {F : Type _} [Field F] (inst : F) (offOp0Tilde : F)
    (offOp1Tilde : F) (offDstTilde : F) (f_tilde : TildeType F) where
  h_instruction :
    inst = offDstTilde + 2 ^ 16 * offOp0Tilde + 2 ^ 32 * offOp1Tilde + 2 ^ 48 * f_tilde 0
  h_bit : ∀ i : Fin 15, f_tilde.toF i * (f_tilde.toF i - 1) = 0
  h_last_value : f_tilde ⟨15, by norm_num⟩ = 0

/- Constraints relating each state to the next one.  -/
structure StepConstraints {F : Type _} [Field F] (offOp0Tilde : F) (offOp1Tilde : F)
    (offDstTilde : F) (f_tilde : TildeType F) (fp : F) (ap : F) (pc : F) (nextFp : F)
    (nextAp : F) (nextPc : F) (dstAddr : F) (op0Addr : F) (op1Addr : F) (dst : F) (op0 : F)
    (op1 : F) where
  mul : F
  res : F
  t0 : F
  t1 : F
  h_dstAddr :
    dstAddr = f_tilde.fDstReg * fp + (1 - f_tilde.fDstReg) * ap + (offDstTilde - 2 ^ 15)
  h_op0Addr :
    op0Addr = f_tilde.fOp0Reg * fp + (1 - f_tilde.fOp0Reg) * ap + (offOp0Tilde - 2 ^ 15)
  h_op1Addr :
    op1Addr =
      f_tilde.fOp1Imm * pc + f_tilde.fOp1Ap * ap + f_tilde.fOp1Fp * fp +
          (1 - f_tilde.fOp1Imm - f_tilde.fOp1Ap - f_tilde.fOp1Fp) * op0 +
        (offOp1Tilde - 2 ^ 15)
  h_mul : mul = op0 * op1
  h_res :
    (1 - f_tilde.fPcJnz) * res =
      f_tilde.fResAdd * (op0 + op1) + f_tilde.fResMul * mul +
        (1 - f_tilde.fResAdd - f_tilde.fResMul - f_tilde.fPcJnz) * op1
  h_t0_eq : t0 = f_tilde.fPcJnz * dst
  h_t1_eq : t1 = t0 * res
  h_nextPc_eq : (t1 - f_tilde.fPcJnz) * (nextPc - (pc + (f_tilde.fOp1Imm + 1))) = 0
  h_nextPc_eq' :
    t0 * (nextPc - (pc + op1)) + (1 - f_tilde.fPcJnz) * nextPc -
        ((1 - f_tilde.fPcJumpAbs - f_tilde.fPcJumpRel - f_tilde.fPcJnz) *
              (pc + (f_tilde.fOp1Imm + 1)) +
            f_tilde.fPcJumpAbs * res +
          f_tilde.fPcJumpRel * (pc + res)) =
      0
  h_opcode_call : f_tilde.fOpcodeCall * (dst - fp) = 0
  h_opcode_call' : f_tilde.fOpcodeCall * (op0 - (pc + (f_tilde.fOp1Imm + 1))) = 0
  h_opcode_assert_eq : f_tilde.fOpcodeAssertEq * (dst - res) = 0
  h_nextAp : nextAp = ap + f_tilde.fApAdd * res + f_tilde.fApAdd1 + f_tilde.fOpcodeCall * 2
  h_nextFp :
    nextFp =
      f_tilde.fOpcodeRet * dst + f_tilde.fOpcodeCall * (ap + 2) +
        (1 - f_tilde.fOpcodeRet - f_tilde.fOpcodeCall) * fp

/- Constraints defining the range check builtin.  -/
structure RcBuiltinConstraints {F : Type _} [Field F] (rc16Len : ℕ) (initial_rcAddr : ℕ)
    (rcLen : ℕ) (rc16Val : Fin rc16Len → F) (rcAddr : Fin rcLen → F)
    -- rc_builtin__mem__addr
    (rcVal : Fin rcLen → F)
    -- rc_builtin__mem__value
    (rc_to_rc16 : Fin rcLen → Fin 8 → Fin rc16Len) where
  h_rc_init_addr : ∀ h : 0 < rcLen, rcAddr ⟨0, h⟩ = initial_rcAddr
  h_rcAddr_step :
    ∀ i : ℕ,
      ∀ h : i.succ < rcLen, rcAddr ⟨i.succ, h⟩ = rcAddr ⟨i, (Nat.lt_succ_self _).trans h⟩ + 1
  h_rcValue :
    ∀ i : Fin rcLen,
      rcVal i =
        ((((((rc16Val (rc_to_rc16 i 0) * 2 ^ 16 + rc16Val (rc_to_rc16 i 1)) * 2 ^ 16 +
                              rc16Val (rc_to_rc16 i 2)) *
                            2 ^ 16 +
                          rc16Val (rc_to_rc16 i 3)) *
                        2 ^ 16 +
                      rc16Val (rc_to_rc16 i 4)) *
                    2 ^ 16 +
                  rc16Val (rc_to_rc16 i 5)) *
                2 ^ 16 +
              rc16Val (rc_to_rc16 i 6)) *
            2 ^ 16 +
          rc16Val (rc_to_rc16 i 7)

/-
All the trace data and constraints (except for the probabilistic assumptions, and assumption
  `char F > 2^16`)
-/
structure Constraints {F : Type _} [Field F] [Fintype F] (inp : InputDataAux F) where
  -- the execution trace
  fp : Fin (inp.t + 1) → F
  ap : Fin (inp.t + 1) → F
  pc : Fin (inp.t + 1) → F
  -- the sequence of instructions
  inst : Fin inp.t → F
  offOp0Tilde : Fin inp.t → F
  offOp1Tilde : Fin inp.t → F
  offDstTilde : Fin inp.t → F
  rc16Val : Fin inp.rc16Len → F
  fTilde : Fin inp.t → TildeType F
  -- the memory accesses
  dstAddr : Fin inp.t → F
  dst : Fin inp.t → F
  op0Addr : Fin inp.t → F
  op0 : Fin inp.t → F
  op1Addr : Fin inp.t → F
  op1 : Fin inp.t → F
  rcAddr : Fin inp.rcLen → F
  rcVal : Fin inp.rcLen → F
  -- starting and ending constraints
  h_pcI : pc 0 = inp.pcI
  h_apI : ap 0 = inp.apI
  h_fpI : fp 0 = inp.apI
  h_pcF : pc (Fin.last inp.t) = inp.pcF
  h_apF : ap (Fin.last inp.t) = inp.apF
  -- the main constraints
  mc :
    @MemoryConstraints F _ _ inp.t inp.rcLen (fun i : Fin inp.t => pc (Fin.castSucc i)) inst dstAddr dst
      op0Addr op0 op1Addr op1 rcAddr rcVal inp.memStar
  rc :
    RangeCheckConstraints inp.t inp.rc16Len offOp0Tilde offOp1Tilde offDstTilde rc16Val
      inp.rcMin inp.rcMax
  ic :
    ∀ i : Fin inp.t,
      InstructionConstraints (inst i) (offOp0Tilde i) (offOp1Tilde i) (offDstTilde i)
        (fTilde i)
  sc :
    ∀ i : Fin inp.t,
      StepConstraints (offOp0Tilde i) (offOp1Tilde i) (offDstTilde i) (fTilde i)
        (fp (Fin.castSucc i)) (ap (Fin.castSucc i)) (pc (Fin.castSucc i)) (fp i.succ) (ap i.succ) (pc i.succ)
        (dstAddr i) (op0Addr i) (op1Addr i) (dst i) (op0 i) (op1 i)
  rcb :
    RcBuiltinConstraints inp.rc16Len inp.initialRcAddr inp.rcLen rc16Val rcAddr rcVal inp.rcToRc16
