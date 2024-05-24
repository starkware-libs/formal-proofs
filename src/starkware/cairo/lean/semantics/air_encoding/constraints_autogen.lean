/- This file is generated automatically by generate_constraints.py. -/

import algebra.field.power

notation `offset_size` := 2^16
notation `half_offset_size` := 2^15

def column (F : Type*) := nat → F
def column.off {F : Type*} (c : column F) (i j : nat) := c (i + j)

structure input_data (F : Type*) :=
(trace_length : nat)
(initial_ap : nat)
(initial_pc : nat)
(final_ap : nat)
(final_pc : nat)
(m_star : F → option F)

structure public_data (F : Type*) :=
(initial_ecdsa_addr : F)
(initial_pedersen_addr : nat)
(initial_rc_addr : nat)
(memory__multi_column_perm__hash_interaction_elm0 : F)
(memory__multi_column_perm__perm__interaction_elm : F)
(memory__multi_column_perm__perm__public_memory_prod : F)
(rc16__perm__interaction_elm : F)
(rc16__perm__public_memory_prod : F)
(rc_max : nat)
(rc_min : nat)

structure columns (F : Type*) :=
(column0 : column F)
(column1 : column F)
(column10 : column F)
(column11 : column F)
(column12 : column F)
(column13 : column F)
(column14 : column F)
(column15 : column F)
(column16 : column F)
(column17 : column F)
(column18 : column F)
(column19 : column F)
(column2 : column F)
(column20 : column F)
(column21 : column F)
(column22 : column F)
(column3 : column F)
(column4 : column F)
(column5 : column F)
(column6 : column F)
(column7 : column F)
(column8 : column F)
(column9 : column F)

structure columns_inter (F : Type*) :=
(column23_inter1 : column F)
(column24_inter1 : column F)

namespace columns

variables {F : Type*} (c : columns F) (i : nat)
@[simp] def cpu__decode__instruction := c.column19.off i 1
@[simp] def cpu__decode__mem_inst__addr := c.column19.off i 0
@[simp] def cpu__decode__mem_inst__value := c.column19.off i 1
@[simp] def cpu__decode__off0 := c.column0.off i 0
@[simp] def cpu__decode__off1 := c.column0.off i 8
@[simp] def cpu__decode__off2 := c.column0.off i 4
@[simp] def cpu__decode__opcode_rc__column := c.column1.off i 0
@[simp] def cpu__decode__pc := c.column19.off i 0
@[simp] def cpu__operands__mem_dst__addr := c.column19.off i 8
@[simp] def cpu__operands__mem_dst__value := c.column19.off i 9
@[simp] def cpu__operands__mem_op0__addr := c.column19.off i 4
@[simp] def cpu__operands__mem_op0__value := c.column19.off i 5
@[simp] def cpu__operands__mem_op1__addr := c.column19.off i 12
@[simp] def cpu__operands__mem_op1__value := c.column19.off i 13
@[simp] def cpu__operands__ops_mul := c.column21.off i 4
@[simp] def cpu__operands__res := c.column21.off i 12
@[simp] def cpu__registers__ap := c.column21.off i 0
@[simp] def cpu__registers__fp := c.column21.off i 8
@[simp] def cpu__update_registers__update_pc__tmp0 := c.column21.off i 2
@[simp] def cpu__update_registers__update_pc__tmp1 := c.column21.off i 10
@[simp] def mem_pool__addr := c.column19.off i 0
@[simp] def mem_pool__value := c.column19.off i 1
@[simp] def memory__sorted__addr := c.column20.off i 0
@[simp] def memory__sorted__value := c.column20.off i 1
@[simp] def orig__public_memory__addr := c.column19.off i 2
@[simp] def orig__public_memory__value := c.column19.off i 3
@[simp] def rc16__sorted := c.column2.off i 0
@[simp] def rc16_pool := c.column0.off i 0
@[simp] def rc_builtin__inner_rc := c.column0.off i 12
@[simp] def rc_builtin__mem__addr := c.column19.off i 102
@[simp] def rc_builtin__mem__value := c.column19.off i 103

end columns

namespace columns_inter

variables {F : Type*} (ci : columns_inter F) (i : nat)

@[simp] def memory__multi_column_perm__perm__cum_prod0 := ci.column24_inter1.off i 0
@[simp] def rc16__perm__cum_prod0 := ci.column23_inter1.off i 0

end columns_inter

variables {F: Type*} [field F]

structure cpu__decode (c : columns F) : Prop :=
(flag_op1_base_op0_bit : ∀ i: nat, (((i % 16 = 0))) → (1 - ((c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + (c.column1.off i 4) - ((c.column1.off i 5) + (c.column1.off i 5)) + (c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4)))) * (1 - ((c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + (c.column1.off i 4) - ((c.column1.off i 5) + (c.column1.off i 5)) + (c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4)))) - (1 - ((c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + (c.column1.off i 4) - ((c.column1.off i 5) + (c.column1.off i 5)) + (c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4)))) = 0)
(flag_pc_update_regular_bit : ∀ i: nat, (((i % 16 = 0))) → (1 - ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8)) + (c.column1.off i 8) - ((c.column1.off i 9) + (c.column1.off i 9)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * (1 - ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8)) + (c.column1.off i 8) - ((c.column1.off i 9) + (c.column1.off i 9)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) - (1 - ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8)) + (c.column1.off i 8) - ((c.column1.off i 9) + (c.column1.off i 9)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) = 0)
(flag_res_op1_bit : ∀ i: nat, (((i % 16 = 0))) → (1 - ((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6)) + (c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * (1 - ((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6)) + (c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) - (1 - ((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6)) + (c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) = 0)
(fp_update_regular_bit : ∀ i: nat, (((i % 16 = 0))) → (1 - ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + (c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14)))) * (1 - ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + (c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14)))) - (1 - ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + (c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14)))) = 0)
(opcode_rc__bit : ∀ i: nat, (¬ ((i % 16 = 15))) → ((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1))) * ((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1))) - ((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1))) = 0)
(opcode_rc__zero : ∀ i: nat, (((i % 16 = 15))) → c.column1.off i 0 = 0)
(opcode_rc_input : ∀ i: nat, (((i % 16 = 0))) → (c.column19.off i 1) - ((((c.column1.off i 0) * offset_size + (c.column0.off i 4)) * offset_size + (c.column0.off i 8)) * offset_size + (c.column0.off i 0)) = 0)

structure cpu__opcodes (c : columns F) : Prop :=
(assert_eq__assert_eq : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 14) - ((c.column1.off i 15) + (c.column1.off i 15))) * ((c.column19.off i 9) - (c.column21.off i 12)) = 0)
(call__flags : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + (c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + 1 + 1 - ((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1)) + (c.column1.off i 1) - ((c.column1.off i 2) + (c.column1.off i 2)) + 4)) = 0)
(call__off0 : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column0.off i 0) - half_offset_size) = 0)
(call__off1 : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column0.off i 8) - (half_offset_size + 1)) = 0)
(call__push_fp : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column19.off i 9) - (c.column21.off i 8)) = 0)
(call__push_pc : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column19.off i 5) - ((c.column19.off i 0) + (c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + 1)) = 0)
(ret__flags : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14))) * ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8)) + (c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1)) + (c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4)) + 1 - ((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6)) + (c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10))) - 4) = 0)
(ret__off0 : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14))) * ((c.column0.off i 0) + 2 - half_offset_size) = 0)
(ret__off2 : ∀ i: nat, (((i % 16 = 0))) → ((c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14))) * ((c.column0.off i 4) + 1 - half_offset_size) = 0)

structure cpu__operands (c : columns F) : Prop :=
(mem0_addr : ∀ i: nat, (((i % 16 = 0))) → (c.column19.off i 4) + half_offset_size - (((c.column1.off i 1) - ((c.column1.off i 2) + (c.column1.off i 2))) * (c.column21.off i 8) + (1 - ((c.column1.off i 1) - ((c.column1.off i 2) + (c.column1.off i 2)))) * (c.column21.off i 0) + (c.column0.off i 8)) = 0)
(mem1_addr : ∀ i: nat, (((i % 16 = 0))) → (c.column19.off i 12) + half_offset_size - (((c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3))) * (c.column19.off i 0) + ((c.column1.off i 4) - ((c.column1.off i 5) + (c.column1.off i 5))) * (c.column21.off i 0) + ((c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4))) * (c.column21.off i 8) + (1 - ((c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + (c.column1.off i 4) - ((c.column1.off i 5) + (c.column1.off i 5)) + (c.column1.off i 3) - ((c.column1.off i 4) + (c.column1.off i 4)))) * (c.column19.off i 5) + (c.column0.off i 4)) = 0)
(mem_dst_addr : ∀ i: nat, (((i % 16 = 0))) → (c.column19.off i 8) + half_offset_size - (((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1))) * (c.column21.off i 8) + (1 - ((c.column1.off i 0) - ((c.column1.off i 1) + (c.column1.off i 1)))) * (c.column21.off i 0) + (c.column0.off i 0)) = 0)
(ops_mul : ∀ i: nat, (((i % 16 = 0))) → (c.column21.off i 4) - (c.column19.off i 5) * (c.column19.off i 13) = 0)
(res : ∀ i: nat, (((i % 16 = 0))) → (1 - ((c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * (c.column21.off i 12) - (((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6))) * ((c.column19.off i 5) + (c.column19.off i 13)) + ((c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7))) * (c.column21.off i 4) + (1 - ((c.column1.off i 5) - ((c.column1.off i 6) + (c.column1.off i 6)) + (c.column1.off i 6) - ((c.column1.off i 7) + (c.column1.off i 7)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * (c.column19.off i 13)) = 0)

structure cpu__update_registers (inp : input_data F) (c : columns F) : Prop :=
(update_ap__ap_update : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 16) - ((c.column21.off i 0) + ((c.column1.off i 10) - ((c.column1.off i 11) + (c.column1.off i 11))) * (c.column21.off i 12) + (c.column1.off i 11) - ((c.column1.off i 12) + (c.column1.off i 12)) + ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * 2) = 0)
(update_fp__fp_update : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 24) - ((1 - ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13)) + (c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14)))) * (c.column21.off i 8) + ((c.column1.off i 13) - ((c.column1.off i 14) + (c.column1.off i 14))) * (c.column19.off i 9) + ((c.column1.off i 12) - ((c.column1.off i 13) + (c.column1.off i 13))) * ((c.column21.off i 0) + 2)) = 0)
(update_pc__pc_cond_negative : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (1 - ((c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * (c.column19.off i 16) + (c.column21.off i 2) * ((c.column19.off i 16) - ((c.column19.off i 0) + (c.column19.off i 13))) - ((1 - ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8)) + (c.column1.off i 8) - ((c.column1.off i 9) + (c.column1.off i 9)) + (c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * ((c.column19.off i 0) + (c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + 1) + ((c.column1.off i 7) - ((c.column1.off i 8) + (c.column1.off i 8))) * (c.column21.off i 12) + ((c.column1.off i 8) - ((c.column1.off i 9) + (c.column1.off i 9))) * ((c.column19.off i 0) + (c.column21.off i 12))) = 0)
(update_pc__pc_cond_positive : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → ((c.column21.off i 10) - ((c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10)))) * ((c.column19.off i 16) - ((c.column19.off i 0) + (c.column1.off i 2) - ((c.column1.off i 3) + (c.column1.off i 3)) + 1)) = 0)
(update_pc__tmp0 : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 2) - ((c.column1.off i 9) - ((c.column1.off i 10) + (c.column1.off i 10))) * (c.column19.off i 9) = 0)
(update_pc__tmp1 : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 10) - (c.column21.off i 2) * (c.column21.off i 12) = 0)

structure memory (inp : input_data F) (pd : public_data F) (c : columns F) (ci : columns_inter F) : Prop :=
(diff_is_bit : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → ((c.column20.off i 2) - (c.column20.off i 0)) * ((c.column20.off i 2) - (c.column20.off i 0)) - ((c.column20.off i 2) - (c.column20.off i 0)) = 0)
(initial_addr : ∀ i: nat, ((i = 0)) → (c.column20.off i 0) - 1 = 0)
(is_func : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → ((c.column20.off i 2) - (c.column20.off i 0) - 1) * ((c.column20.off i 1) - (c.column20.off i 3)) = 0)
(multi_column_perm__perm__init0 : ∀ i: nat, ((i = 0)) → (pd.memory__multi_column_perm__perm__interaction_elm - ((c.column20.off i 0) + pd.memory__multi_column_perm__hash_interaction_elm0 * (c.column20.off i 1))) * (ci.column24_inter1.off i 0) + (c.column19.off i 0) + pd.memory__multi_column_perm__hash_interaction_elm0 * (c.column19.off i 1) - pd.memory__multi_column_perm__perm__interaction_elm = 0)
(multi_column_perm__perm__last : ∀ i: nat, ((i = 2 * (inp.trace_length / 2 - 1))) → (ci.column24_inter1.off i 0) - pd.memory__multi_column_perm__perm__public_memory_prod = 0)
(multi_column_perm__perm__step0 : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → (pd.memory__multi_column_perm__perm__interaction_elm - ((c.column20.off i 2) + pd.memory__multi_column_perm__hash_interaction_elm0 * (c.column20.off i 3))) * (ci.column24_inter1.off i 2) - (pd.memory__multi_column_perm__perm__interaction_elm - ((c.column19.off i 2) + pd.memory__multi_column_perm__hash_interaction_elm0 * (c.column19.off i 3))) * (ci.column24_inter1.off i 0) = 0)

structure public_memory (c : columns F) : Prop :=
(addr_zero : ∀ i: nat, (((i % 8 = 0))) → c.column19.off i 2 = 0)
(value_zero : ∀ i: nat, (((i % 8 = 0))) → c.column19.off i 3 = 0)

structure rc16 (inp : input_data F) (pd : public_data F) (c : columns F) (ci : columns_inter F) : Prop :=
(diff_is_bit : ∀ i: nat, (¬ (i = inp.trace_length - 1)) → ((c.column2.off i 1) - (c.column2.off i 0)) * ((c.column2.off i 1) - (c.column2.off i 0)) - ((c.column2.off i 1) - (c.column2.off i 0)) = 0)
(maximum : ∀ i: nat, ((i = inp.trace_length - 1)) → (c.column2.off i 0) - pd.rc_max = 0)
(minimum : ∀ i: nat, ((i = 0)) → (c.column2.off i 0) - pd.rc_min = 0)
(perm__init0 : ∀ i: nat, ((i = 0)) → (pd.rc16__perm__interaction_elm - (c.column2.off i 0)) * (ci.column23_inter1.off i 0) + (c.column0.off i 0) - pd.rc16__perm__interaction_elm = 0)
(perm__last : ∀ i: nat, ((i = inp.trace_length - 1)) → (ci.column23_inter1.off i 0) - pd.rc16__perm__public_memory_prod = 0)
(perm__step0 : ∀ i: nat, (¬ (i = inp.trace_length - 1)) → (pd.rc16__perm__interaction_elm - (c.column2.off i 1)) * (ci.column23_inter1.off i 1) - (pd.rc16__perm__interaction_elm - (c.column0.off i 1)) * (ci.column23_inter1.off i 0) = 0)

structure rc_builtin (inp : input_data F) (pd : public_data F) (c : columns F) : Prop :=
(addr_step : ∀ i: nat, (((i % 128 = 0)) ∧ ¬ (i = 128 * (inp.trace_length / 128 - 1))) → (c.column19.off i 230) - ((c.column19.off i 102) + 1) = 0)
(init_addr : ∀ i: nat, ((i = 0)) → (c.column19.off i 102) - pd.initial_rc_addr = 0)
(value : ∀ i: nat, (((i % 128 = 0))) → (((((((c.column0.off i 12) * offset_size + (c.column0.off i 28)) * offset_size + (c.column0.off i 44)) * offset_size + (c.column0.off i 60)) * offset_size + (c.column0.off i 76)) * offset_size + (c.column0.off i 92)) * offset_size + (c.column0.off i 108)) * offset_size + (c.column0.off i 124) - (c.column19.off i 103) = 0)

structure toplevel_constraints (inp : input_data F) (c : columns F) : Prop :=
(final_ap : ∀ i: nat, ((i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 0) - inp.final_ap = 0)
(final_fp : ∀ i: nat, ((i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 8) - inp.initial_ap = 0)
(final_pc : ∀ i: nat, ((i = 16 * (inp.trace_length / 16 - 1))) → (c.column19.off i 0) - inp.final_pc = 0)
(initial_ap : ∀ i: nat, ((i = 0)) → (c.column21.off i 0) - inp.initial_ap = 0)
(initial_fp : ∀ i: nat, ((i = 0)) → (c.column21.off i 8) - inp.initial_ap = 0)
(initial_pc : ∀ i: nat, ((i = 0)) → (c.column19.off i 0) - inp.initial_pc = 0)
