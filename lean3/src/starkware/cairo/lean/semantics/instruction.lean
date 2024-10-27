/-
Cairo machine instructions.
-/
import starkware.cairo.lean.semantics.util

@[derive decidable_eq, ext]
structure instruction :=
(off_dst : bitvec 16)
(off_op0 : bitvec 16)
(off_op1 : bitvec 16)
(flags   : bitvec 15)

-- flag bits
notation `DST_REG`          := 0
notation `OP0_REG`          := 1
notation `OP1_IMM`          := 2
notation `OP1_FP`           := 3
notation `OP1_AP`           := 4
notation `RES_ADD`          := 5
notation `RES_MUL`          := 6
notation `PC_JUMP_ABS`      := 7
notation `PC_JUMP_REL`      := 8
notation `PC_JNZ`           := 9
notation `AP_ADD`           := 10
notation `AP_ADD1`          := 11
notation `OPCODE_CALL`      := 12
notation `OPCODE_RET`       := 13
notation `OPCODE_ASSERT_EQ` := 14

namespace instruction

variable i : instruction

def dst_reg     := i.flags.nth DST_REG
def op0_reg     := i.flags.nth OP0_REG
def op1_imm     := i.flags.nth OP1_IMM                  -- op1 src
def op1_fp      := i.flags.nth OP1_FP                   -- op1 src
def op1_ap      := i.flags.nth OP1_AP                   -- op1 src
def res_add     := i.flags.nth RES_ADD                  -- res logic
def res_mul     := i.flags.nth RES_MUL                  -- res logic
def pc_jump_abs := i.flags.nth PC_JUMP_ABS              -- pc update
def pc_jump_rel := i.flags.nth PC_JUMP_REL              -- pc update
def pc_jnz      := i.flags.nth PC_JNZ                   -- pc update
def ap_add      := i.flags.nth AP_ADD                   -- ap update
def ap_add1     := i.flags.nth AP_ADD1                  -- ap update
def opcode_call := i.flags.nth OPCODE_CALL              -- opcode
def opcode_ret  := i.flags.nth OPCODE_RET               -- opcode
def opcode_assert_eq := i.flags.nth OPCODE_ASSERT_EQ    -- opcode

def to_nat (inst : instruction) : ℕ :=
           inst.off_dst.to_natr +
    2^16 * inst.off_op0.to_natr +
    2^32 * inst.off_op1.to_natr +
    2^48 * inst.flags.to_natr

end instruction
