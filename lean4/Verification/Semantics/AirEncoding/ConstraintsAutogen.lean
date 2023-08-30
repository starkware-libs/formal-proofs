/- 
This file is generated automatically by generate_constraints.py. 
-/
import Mathlib.Algebra.Field.Power

-- mathport name: exproffset_size
notation "offset_size" => 2 ^ 16

-- mathport name: exprhalf_offset_size
notation "half_offset_size" => 2 ^ 15

def Column (F : Type _) :=
  Nat → F

def Column.off {F : Type _} (c : Column F) (i j : Nat) :=
  c (i + j)

structure InputData (F : Type _) where
  traceLength : Nat
  initialAp : Nat
  initialPc : Nat
  finalAp : Nat
  finalPc : Nat
  mStar : F → Option F

structure PublicData (F : Type _) where
  initialEcdsaAddr : F
  initialPedersenAddr : Nat
  initialRcAddr : Nat
  memoryMultiColumnPermHashInteractionElm0 : F
  memoryMultiColumnPermPermInteractionElm : F
  memoryMultiColumnPermPermPublicMemoryProd : F
  rc16PermInteractionElm : F
  rc16PermPublicMemoryProd : F
  rcMax : Nat
  rcMin : Nat

structure Columns (F : Type _) where
  column0 : Column F
  column1 : Column F
  column10 : Column F
  column11 : Column F
  column12 : Column F
  column13 : Column F
  column14 : Column F
  column15 : Column F
  column16 : Column F
  column17 : Column F
  column18 : Column F
  column19 : Column F
  column2 : Column F
  column20 : Column F
  column21 : Column F
  column22 : Column F
  column3 : Column F
  column4 : Column F
  column5 : Column F
  column6 : Column F
  column7 : Column F
  column8 : Column F
  column9 : Column F

structure ColumnsInter (F : Type _) where
  column23Inter1 : Column F
  column24Inter1 : Column F

namespace Columns

variable {F : Type _} (c : Columns F) (i : Nat)

@[simp] def cpuDecodeInstruction := c.column19.off i 1
@[simp] def cpuDecodeMemInstAddr := c.column19.off i 0
@[simp] def cpuDecodeMemInstValue := c.column19.off i 1
@[simp] def cpuDecodeOff0 := c.column0.off i 0
@[simp] def cpuDecodeOff1 := c.column0.off i 8
@[simp] def cpuDecodeOff2 := c.column0.off i 4
@[simp] def cpuDecodeOpcodeRcColumn := c.column1.off i 0
@[simp] def cpuDecodePc := c.column19.off i 0
@[simp] def cpuOperandsMemDstAddr := c.column19.off i 8
@[simp] def cpuOperandsMemDstValue := c.column19.off i 9
@[simp] def cpuOperandsMemOp0Addr := c.column19.off i 4
@[simp] def cpuOperandsMemOp0Value := c.column19.off i 5
@[simp] def cpuOperandsMemOp1Addr := c.column19.off i 12
@[simp] def cpuOperandsMemOp1Value := c.column19.off i 13
@[simp] def cpuOperandsOpsMul := c.column21.off i 4
@[simp] def cpuOperandsRes := c.column21.off i 12
@[simp] def cpuRegistersAp := c.column21.off i 0
@[simp] def cpuRegistersFp := c.column21.off i 8
@[simp] def cpuUpdateRegistersUpdatePcTmp0 := c.column21.off i 2
@[simp] def cpuUpdateRegistersUpdatePcTmp1 := c.column21.off i 10
@[simp] def memPoolAddr := c.column19.off i 0
@[simp] def memPoolValue := c.column19.off i 1
@[simp] def memorySortedAddr := c.column20.off i 0
@[simp] def memorySortedValue := c.column20.off i 1
@[simp] def origPublicMemoryAddr := c.column19.off i 2
@[simp] def origPublicMemoryValue := c.column19.off i 3
@[simp] def rc16Sorted := c.column2.off i 0
@[simp] def rc16Pool := c.column0.off i 0
@[simp] def rcBuiltinInnerRc := c.column0.off i 12
@[simp] def rcBuiltinMemAddr := c.column19.off i 102
@[simp] def rcBuiltinMemValue := c.column19.off i 103

end Columns

namespace ColumnsInter

variable {F : Type _} (ci : ColumnsInter F) (i : Nat)

@[simp] def memoryMultiColumnPermPermCumProd0 := ci.column24Inter1.off i 0
@[simp] def rc16PermCumProd0 := ci.column23Inter1.off i 0

end ColumnsInter

variable {F : Type _} [Field F]

structure CpuDecode (c : Columns F) : Prop where
  flag_op1_base_op0_bit :
    ∀ i : Nat,
      i % 16 = 0 →
        (1 - (c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + c.column1.off i 4 -
          (c.column1.off i 5 + c.column1.off i 5) + c.column1.off i 3 -
          (c.column1.off i 4 + c.column1.off i 4))) *
        (1 - (c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + c.column1.off i 4 -
          (c.column1.off i 5 + c.column1.off i 5) + c.column1.off i 3 -
          (c.column1.off i 4 + c.column1.off i 4))) -
        (1 - (c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + c.column1.off i 4 -
          (c.column1.off i 5 + c.column1.off i 5) + c.column1.off i 3 -
          (c.column1.off i 4 + c.column1.off i 4))) = 0
  flag_pc_update_regular_bit :
    ∀ i : Nat,
      i % 16 = 0 →
        (1 - (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) + c.column1.off i 8 -
          (c.column1.off i 9 + c.column1.off i 9) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) *
        (1 - (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) + c.column1.off i 8 -
          (c.column1.off i 9 + c.column1.off i 9) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) -
        (1 - (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) + c.column1.off i 8 -
          (c.column1.off i 9 + c.column1.off i 9) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) = 0
  flag_res_op1_bit :
    ∀ i : Nat,
      i % 16 = 0 →
        (1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 -
          (c.column1.off i 7 + c.column1.off i 7) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) *
        (1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 -
          (c.column1.off i 7 + c.column1.off i 7) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) -
        (1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 -
          (c.column1.off i 7 + c.column1.off i 7) + c.column1.off i 9 -
          (c.column1.off i 10 + c.column1.off i 10))) = 0
  fp_update_regular_bit :
    ∀ i : Nat,
      i % 16 = 0 →
        (1 - (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) + c.column1.off i 13 -
          (c.column1.off i 14 + c.column1.off i 14))) *
        (1 - (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) +
          c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14))) -
        (1 - (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) + c.column1.off i 13 -
          (c.column1.off i 14 + c.column1.off i 14))) = 0
  opcode_rc__bit :
    ∀ i : Nat,
      ¬i % 16 = 15 →
        (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) *
          (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) -
          (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) = 0
  opcode_rc__zero : ∀ i : Nat, i % 16 = 15 → c.column1.off i 0 = 0
  opcode_rc_input :
    ∀ i : Nat,
      i % 16 = 0 →
        c.column19.off i 1 - (((c.column1.off i 0 * offset_size + c.column0.off i 4) * offset_size +
          c.column0.off i 8) * offset_size + c.column0.off i 0) = 0

structure CpuOpcodes (c : Columns F) : Prop where
  assert_eq__assert_eq :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 14 - (c.column1.off i 15 + c.column1.off i 15)) *
            (c.column19.off i 9 - c.column21.off i 12) = 0
  call__flags :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
            (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) + c.column1.off i 12 -
                    (c.column1.off i 13 + c.column1.off i 13) + 1 + 1 -
              (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1) + c.column1.off i 1 -
                  (c.column1.off i 2 + c.column1.off i 2) + 4)) = 0
  call__off0 :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
            (c.column0.off i 0 - half_offset_size) = 0
  call__off1 :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
            (c.column0.off i 8 - (half_offset_size + 1)) = 0
  call__push_fp :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
            (c.column19.off i 9 - c.column21.off i 8) = 0
  call__push_pc :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
          (c.column19.off i 5 -
            (c.column19.off i 0 + c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + 1)) = 0
  ret__flags :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14)) *
          (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) + c.column1.off i 0 -
            (c.column1.off i 1 + c.column1.off i 1) +
            c.column1.off i 3 - (c.column1.off i 4 + c.column1.off i 4) +
            1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 -
            (c.column1.off i 7 + c.column1.off i 7) +
            c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10)) - 4) = 0
  ret__off0 :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14)) *
            (c.column0.off i 0 + 2 - half_offset_size) = 0
  ret__off2 :
    ∀ i : Nat,
      i % 16 = 0 →
        (c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14)) *
            (c.column0.off i 4 + 1 - half_offset_size) = 0

structure CpuOperands (c : Columns F) : Prop where
  mem0_addr :
    ∀ i : Nat,
      i % 16 = 0 →
        c.column19.off i 4 + half_offset_size -
            ((c.column1.off i 1 - (c.column1.off i 2 + c.column1.off i 2)) * c.column21.off i 8 +
                (1 - (c.column1.off i 1 - (c.column1.off i 2 + c.column1.off i 2))) *
                  c.column21.off i 0 + c.column0.off i 8) = 0
  mem1_addr :
    ∀ i : Nat,
      i % 16 = 0 →
        c.column19.off i 12 + half_offset_size -
            ((c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3)) * c.column19.off i 0 +
                    (c.column1.off i 4 - (c.column1.off i 5 + c.column1.off i 5)) *
                      c.column21.off i 0 +
                  (c.column1.off i 3 - (c.column1.off i 4 + c.column1.off i 4)) *
                    c.column21.off i 8 +
                (1 - (c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) +
                            c.column1.off i 4 -
                          (c.column1.off i 5 + c.column1.off i 5) +
                        c.column1.off i 3 -
                      (c.column1.off i 4 + c.column1.off i 4))) *
                  c.column19.off i 5 + c.column0.off i 4) = 0
  mem_dst_addr :
    ∀ i : Nat,
      i % 16 = 0 →
        c.column19.off i 8 + half_offset_size -
            ((c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) * c.column21.off i 8 +
                (1 - (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1))) *
                  c.column21.off i 0 + c.column0.off i 0) = 0
  ops_mul :
    ∀ i : Nat, i % 16 = 0 → c.column21.off i 4 - c.column19.off i 5 * c.column19.off i 13 = 0
  res :
    ∀ i : Nat,
      i % 16 = 0 →
        (1 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) *
              c.column21.off i 12 -
            ((c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6)) *
                  (c.column19.off i 5 + c.column19.off i 13) +
                (c.column1.off i 6 - (c.column1.off i 7 + c.column1.off i 7)) * c.column21.off i 4 +
              (1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 -
                (c.column1.off i 7 + c.column1.off i 7) + c.column1.off i 9 -
                (c.column1.off i 10 + c.column1.off i 10))) * c.column19.off i 13) = 0

structure CpuUpdateRegisters (inp : InputData F) (c : Columns F) : Prop where
  update_ap__ap_update :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        c.column21.off i 16 -
            (c.column21.off i 0 +
                    (c.column1.off i 10 - (c.column1.off i 11 + c.column1.off i 11)) *
                      c.column21.off i 12 + c.column1.off i 11 -
                (c.column1.off i 12 + c.column1.off i 12) +
              (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) * 2) = 0
  update_fp__fp_update :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        c.column21.off i 24 -
            ((1 - (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) +
                c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14))) *
                  c.column21.off i 8 +
                (c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14)) *
                  c.column19.off i 9 +
              (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) *
                (c.column21.off i 0 + 2)) = 0
  update_pc__pc_cond_negative :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        (1 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) *
                c.column19.off i 16 +
              c.column21.off i 2 *
                (c.column19.off i 16 - (c.column19.off i 0 + c.column19.off i 13)) -
            ((1 -
                    (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) +
                            c.column1.off i 8 -
                          (c.column1.off i 9 + c.column1.off i 9) +
                        c.column1.off i 9 -
                      (c.column1.off i 10 + c.column1.off i 10))) *
                  (c.column19.off i 0 + c.column1.off i 2 -
                      (c.column1.off i 3 + c.column1.off i 3) +
                    1) +
                (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8)) *
                  c.column21.off i 12 +
              (c.column1.off i 8 - (c.column1.off i 9 + c.column1.off i 9)) *
                (c.column19.off i 0 + c.column21.off i 12)) = 0
  update_pc__pc_cond_positive :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        (c.column21.off i 10 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) *
            (c.column19.off i 16 -
              (c.column19.off i 0 + c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) +
                1)) = 0
  update_pc__tmp0 :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        c.column21.off i 2 -
            (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10)) * c.column19.off i 9 = 0
  update_pc__tmp1 :
    ∀ i : Nat,
      i % 16 = 0 ∧ ¬i = 16 * (inp.traceLength / 16 - 1) →
        c.column21.off i 10 - c.column21.off i 2 * c.column21.off i 12 = 0

structure Memory (inp : InputData F) (pd : PublicData F) (c : Columns F) (ci : ColumnsInter F) :
    Prop where
  diff_is_bit :
    ∀ i : Nat,
      i % 2 = 0 ∧ ¬i = 2 * (inp.traceLength / 2 - 1) →
        (c.column20.off i 2 - c.column20.off i 0) * (c.column20.off i 2 - c.column20.off i 0) -
            (c.column20.off i 2 - c.column20.off i 0) = 0
  initial_addr : ∀ i : Nat, i = 0 → c.column20.off i 0 - 1 = 0
  is_func :
    ∀ i : Nat,
      i % 2 = 0 ∧ ¬i = 2 * (inp.traceLength / 2 - 1) →
        (c.column20.off i 2 - c.column20.off i 0 - 1) * (c.column20.off i 1 - c.column20.off i 3) = 0
  multi_column_perm__perm__init0 :
    ∀ i : Nat,
      i = 0 →
        (pd.memoryMultiColumnPermPermInteractionElm -
                    (c.column20.off i 0 +
                      pd.memoryMultiColumnPermHashInteractionElm0 * c.column20.off i 1)) *
                  ci.column24Inter1.off i 0 +
                c.column19.off i 0 +
              pd.memoryMultiColumnPermHashInteractionElm0 * c.column19.off i 1 -
            pd.memoryMultiColumnPermPermInteractionElm = 0
  multi_column_perm__perm__last :
    ∀ i : Nat,
      i = 2 * (inp.traceLength / 2 - 1) →
        ci.column24Inter1.off i 0 - pd.memoryMultiColumnPermPermPublicMemoryProd = 0
  multi_column_perm__perm__step0 :
    ∀ i : Nat,
      i % 2 = 0 ∧ ¬i = 2 * (inp.traceLength / 2 - 1) →
        (pd.memoryMultiColumnPermPermInteractionElm -
                (c.column20.off i 2 +
                  pd.memoryMultiColumnPermHashInteractionElm0 * c.column20.off i 3)) *
              ci.column24Inter1.off i 2 -
            (pd.memoryMultiColumnPermPermInteractionElm -
                (c.column19.off i 2 +
                  pd.memoryMultiColumnPermHashInteractionElm0 * c.column19.off i 3)) *
              ci.column24Inter1.off i 0 = 0

structure PublicMemory (c : Columns F) : Prop where
  addr_zero : ∀ i : Nat, i % 8 = 0 → c.column19.off i 2 = 0
  value_zero : ∀ i : Nat, i % 8 = 0 → c.column19.off i 3 = 0

structure Rc16 (inp : InputData F) (pd : PublicData F) (c : Columns F) (ci : ColumnsInter F) :
    Prop where
  diff_is_bit :
    ∀ i : Nat,
      ¬i = inp.traceLength - 1 →
        (c.column2.off i 1 - c.column2.off i 0) * (c.column2.off i 1 - c.column2.off i 0) -
            (c.column2.off i 1 - c.column2.off i 0) = 0
  maximum : ∀ i : Nat, i = inp.traceLength - 1 → c.column2.off i 0 - pd.rcMax = 0
  minimum : ∀ i : Nat, i = 0 → c.column2.off i 0 - pd.rcMin = 0
  perm__init0 :
    ∀ i : Nat,
      i = 0 →
        (pd.rc16PermInteractionElm - c.column2.off i 0) * ci.column23Inter1.off i 0 +
              c.column0.off i 0 - pd.rc16PermInteractionElm = 0
  perm__last :
    ∀ i : Nat, i = inp.traceLength - 1 → ci.column23Inter1.off i 0 - pd.rc16PermPublicMemoryProd = 0
  perm__step0 :
    ∀ i : Nat,
      ¬i = inp.traceLength - 1 →
        (pd.rc16PermInteractionElm - c.column2.off i 1) * ci.column23Inter1.off i 1 -
            (pd.rc16PermInteractionElm - c.column0.off i 1) * ci.column23Inter1.off i 0 = 0

structure RcBuiltin (inp : InputData F) (pd : PublicData F) (c : Columns F) : Prop where
  addr_step :
    ∀ i : Nat,
      i % 128 = 0 ∧ ¬i = 128 * (inp.traceLength / 128 - 1) →
        c.column19.off i 230 - (c.column19.off i 102 + 1) = 0
  init_addr : ∀ i : Nat, i = 0 → c.column19.off i 102 - pd.initialRcAddr = 0
  value :
    ∀ i : Nat,
      i % 128 = 0 →
        ((((((c.column0.off i 12 * offset_size + c.column0.off i 28) * offset_size +
                                  c.column0.off i 44) *
                                offset_size +
                              c.column0.off i 60) *
                            offset_size +
                          c.column0.off i 76) *
                        offset_size +
                      c.column0.off i 92) *
                    offset_size +
                  c.column0.off i 108) *
                offset_size +
              c.column0.off i 124 -
            c.column19.off i 103 = 0

structure ToplevelConstraints (inp : InputData F) (c : Columns F) : Prop where
  finalAp : ∀ i : Nat, i = 16 * (inp.traceLength / 16 - 1) → c.column21.off i 0 - inp.finalAp = 0
  final_fp : ∀ i : Nat, i = 16 * (inp.traceLength / 16 - 1) → c.column21.off i 8 - inp.initialAp = 0
  finalPc : ∀ i : Nat, i = 16 * (inp.traceLength / 16 - 1) → c.column19.off i 0 - inp.finalPc = 0
  initialAp : ∀ i : Nat, i = 0 → c.column21.off i 0 - inp.initialAp = 0
  initial_fp : ∀ i : Nat, i = 0 → c.column21.off i 8 - inp.initialAp = 0
  initialPc : ∀ i : Nat, i = 0 → c.column19.off i 0 - inp.initialPc = 0

