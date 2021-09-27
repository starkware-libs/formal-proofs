/- This file is generated automatically. -/

import algebra.field_power

notation `offset_size`      := 2^16
notation `half_offset_size` := 2^15

/- data available to verifier -/

structure input_data (F : Type*) :=
(trace_length : nat)
(initial_ap   : nat)
(initial_pc   : nat)
(final_ap     : nat)
(final_pc     : nat)
(m_star       : F → option F)

structure public_data (F : Type*) :=
(memory__multi_column_perm__perm__interaction_elm    : F)
(memory__multi_column_perm__hash_interaction_elm0    : F)
(memory__multi_column_perm__perm__public_memory_prod : F)
(rc16__perm__interaction_elm                         : F)
(rc16__perm__public_memory_prod                      : F)
(rc_min                                              : nat)
(rc_max                                              : nat)
(initial_rc_addr                                     : nat)
(pedersen__points__x                                 : F)
(pedersen__points__y                                 : F)
(pedersen__shift_point_x                             : F)
(pedersen__shift_point_y                             : F)
(initial_pedersen_addr                               : nat)
(ecdsa__sig_config_alpha                             : F)
(ecdsa__sig_config_beta                              : F)
(ecdsa__generator_points__x                          : F)
(ecdsa__generator_points__y                          : F)
(ecdsa__sig_config_shift_point_x                     : F)
(ecdsa__sig_config_shift_point_y                     : F)
(initial_ecdsa_addr                                  : F)
(initial_checkpoints_addr                            : F)
(final_checkpoints_addr                              : F)

/- prover's data -/

def column (F : Type*) := nat → F

def column.off {F : Type*} (c : column F) (i j : nat) := c (i + j)

structure columns (F  : Type*) :=
(column0  : column F)
(column1  : column F)
(column2  : column F)
(column3  : column F)
(column4  : column F)
(column5  : column F)
(column6  : column F)
(column7  : column F)
(column8  : column F)
(column9  : column F)
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
(column20 : column F)
(column21 : column F)
(column22 : column F)

structure columns_inter (F  : Type*) :=
(column23_inter1 : column F)
(column24_inter1 : column F)

/- accessors -/

namespace columns

variables {F : Type*} (c : columns F) (i : nat)

@[simp] def rc16_pool := c.column0.off i 0
@[simp] def cpu__decode__opcode_rc__column := c.column1.off i 0
@[simp] def rc16__sorted := c.column2.off i 0
@[simp] def pedersen__hash0__ec_subset_sum__partial_sum__x := c.column3.off i 0
@[simp] def pedersen__hash0__ec_subset_sum__partial_sum__y := c.column4.off i 0
@[simp] def pedersen__hash0__ec_subset_sum__slope := c.column5.off i 0
@[simp] def pedersen__hash0__ec_subset_sum__selector := c.column6.off i 0
@[simp] def pedersen__hash1__ec_subset_sum__partial_sum__x := c.column7.off i 0
@[simp] def pedersen__hash1__ec_subset_sum__partial_sum__y := c.column8.off i 0
@[simp] def pedersen__hash1__ec_subset_sum__slope := c.column9.off i 0
@[simp] def pedersen__hash1__ec_subset_sum__selector := c.column10.off i 0
@[simp] def pedersen__hash2__ec_subset_sum__partial_sum__x := c.column11.off i 0
@[simp] def pedersen__hash2__ec_subset_sum__partial_sum__y := c.column12.off i 0
@[simp] def pedersen__hash2__ec_subset_sum__slope := c.column13.off i 0
@[simp] def pedersen__hash2__ec_subset_sum__selector := c.column14.off i 0
@[simp] def pedersen__hash3__ec_subset_sum__partial_sum__x := c.column15.off i 0
@[simp] def pedersen__hash3__ec_subset_sum__partial_sum__y := c.column16.off i 0
@[simp] def pedersen__hash3__ec_subset_sum__slope := c.column17.off i 0
@[simp] def pedersen__hash3__ec_subset_sum__selector := c.column18.off i 0
@[simp] def mem_pool__addr := c.column19.off i 0
@[simp] def mem_pool__value := c.column19.off i 1
@[simp] def memory__sorted__addr := c.column20.off i 0
@[simp] def memory__sorted__value := c.column20.off i 1
@[simp] def cpu__registers__ap := c.column21.off i 0
@[simp] def cpu__registers__fp := c.column21.off i 8
@[simp] def cpu__operands__ops_mul := c.column21.off i 4
@[simp] def cpu__operands__res := c.column21.off i 12
@[simp] def cpu__update_registers__update_pc__tmp0 := c.column21.off i 2
@[simp] def cpu__update_registers__update_pc__tmp1 := c.column21.off i 10
@[simp] def ecdsa__signature0__key_points__x := c.column21.off i 6
@[simp] def ecdsa__signature0__key_points__y := c.column21.off i 14
@[simp] def ecdsa__signature0__doubling_slope := c.column21.off i 1
@[simp] def ecdsa__signature0__exponentiate_key__partial_sum__x := c.column21.off i 9
@[simp] def ecdsa__signature0__exponentiate_key__partial_sum__y := c.column21.off i 5
@[simp] def ecdsa__signature0__exponentiate_key__slope := c.column21.off i 13
@[simp] def ecdsa__signature0__exponentiate_key__selector := c.column21.off i 3
@[simp] def ecdsa__signature0__exponentiate_key__x_diff_inv := c.column21.off i 11
@[simp] def ecdsa__signature0__exponentiate_generator__partial_sum__x := c.column21.off i 7
@[simp] def ecdsa__signature0__exponentiate_generator__partial_sum__y := c.column21.off i 23
@[simp] def ecdsa__signature0__exponentiate_generator__slope := c.column21.off i 15
@[simp] def ecdsa__signature0__exponentiate_generator__selector := c.column21.off i 31
@[simp] def ecdsa__signature0__exponentiate_generator__x_diff_inv := c.column22.off i 0
@[simp] def ecdsa__signature0__r_w_inv := c.column21.off i 4091
@[simp] def ecdsa__signature0__add_results_slope := c.column22.off i 8160
@[simp] def ecdsa__signature0__add_results_inv := c.column21.off i 8175
@[simp] def ecdsa__signature0__extract_r_slope := c.column21.off i 4093
@[simp] def ecdsa__signature0__extract_r_inv := c.column21.off i 8189
@[simp] def ecdsa__signature0__z_inv := c.column21.off i 4081
@[simp] def ecdsa__signature0__q_x_squared := c.column21.off i 8177
@[simp] def cpu__decode__mem_inst__addr := c.column19.off i 0
@[simp] def cpu__decode__mem_inst__value := c.column19.off i 1
@[simp] def cpu__decode__pc := c.column19.off i 0
@[simp] def cpu__decode__instruction := c.column19.off i 1
@[simp] def cpu__decode__off0 := c.column0.off i 0
@[simp] def cpu__decode__off1 := c.column0.off i 8
@[simp] def cpu__decode__off2 := c.column0.off i 4
@[simp] def cpu__operands__mem_dst__addr := c.column19.off i 8
@[simp] def cpu__operands__mem_dst__value := c.column19.off i 9
@[simp] def cpu__operands__mem_op0__addr := c.column19.off i 4
@[simp] def cpu__operands__mem_op0__value := c.column19.off i 5
@[simp] def cpu__operands__mem_op1__addr := c.column19.off i 12
@[simp] def cpu__operands__mem_op1__value := c.column19.off i 13
@[simp] def orig__public_memory__addr := c.column19.off i 2
@[simp] def orig__public_memory__value := c.column19.off i 3
@[simp] def pedersen__input0__addr := c.column19.off i 6
@[simp] def pedersen__input0__value := c.column19.off i 7
@[simp] def pedersen__input1__addr := c.column19.off i 70
@[simp] def pedersen__input1__value := c.column19.off i 71
@[simp] def pedersen__output__addr := c.column19.off i 38
@[simp] def pedersen__output__value := c.column19.off i 39
@[simp] def rc_builtin__mem__addr := c.column19.off i 102
@[simp] def rc_builtin__mem__value := c.column19.off i 103
@[simp] def rc_builtin__inner_rc := c.column0.off i 12
@[simp] def ecdsa__pubkey__addr := c.column19.off i 22
@[simp] def ecdsa__pubkey__value := c.column19.off i 23
@[simp] def ecdsa__message__addr := c.column19.off i 4118
@[simp] def ecdsa__message__value := c.column19.off i 4119
@[simp] def checkpoints__req_pc__addr := c.column19.off i 150
@[simp] def checkpoints__req_pc__value := c.column19.off i 151
@[simp] def checkpoints__req_fp__addr := c.column19.off i 86
@[simp] def checkpoints__req_fp__value := c.column19.off i 87

end columns

namespace columns_inter

variables {F : Type*} (ci : columns_inter F) (i : nat)

@[simp] def rc16__perm__cum_prod0 := ci.column23_inter1.off i 0
@[simp] def memory__multi_column_perm__perm__cum_prod0 := ci.column24_inter1.off i 0

end columns_inter

/- constraints -/

variables {F: Type*} [field F]

structure cpu__decode (c : columns F) : Prop :=
(opcode_rc__bit : ∀ i: nat, (¬ ((i % 16 = 15))) → (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) * (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) - (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) = 0)
(opcode_rc__zero : ∀ i: nat, (((i % 16 = 15))) → c.column1.off i 0 = 0)
(opcode_rc_input : ∀ i: nat, (((i % 16 = 0))) → c.column19.off i 1 - (((c.column1.off i 0 * 2^16 + c.column0.off i 4) * offset_size + c.column0.off i 8) * offset_size + c.column0.off i 0) = 0)

structure cpu__operands (c : columns F) : Prop :=
(mem_dst_addr : ∀ i: nat, (((i % 16 = 0))) → c.column19.off i 8 + half_offset_size - ((c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1)) * c.column21.off i 8 + (1 - (c.column1.off i 0 - (c.column1.off i 1 + c.column1.off i 1))) * c.column21.off i 0 + c.column0.off i 0) = 0)
(mem0_addr : ∀ i: nat, (((i % 16 = 0))) → c.column19.off i 4 + half_offset_size - ((c.column1.off i 1 - (c.column1.off i 2 + c.column1.off i 2)) * c.column21.off i 8 + (1 - (c.column1.off i 1 - (c.column1.off i 2 + c.column1.off i 2))) * c.column21.off i 0 + c.column0.off i 8) = 0)
(mem1_addr : ∀ i: nat, (((i % 16 = 0))) → c.column19.off i 12 + half_offset_size - ((c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3)) * c.column19.off i 0 + (c.column1.off i 4 - (c.column1.off i 5 + c.column1.off i 5)) * c.column21.off i 0 + (c.column1.off i 3 - (c.column1.off i 4 + c.column1.off i 4)) * c.column21.off i 8 + (1 - (c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + c.column1.off i 4 - (c.column1.off i 5 + c.column1.off i 5) + c.column1.off i 3 - (c.column1.off i 4 + c.column1.off i 4))) * c.column19.off i 5 + c.column0.off i 4) = 0)
(ops_mul : ∀ i: nat, (((i % 16 = 0))) → c.column21.off i 4 - c.column19.off i 5 * c.column19.off i 13 = 0)
(res : ∀ i: nat, (((i % 16 = 0))) → (1 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) * c.column21.off i 12 - ((c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6)) * (c.column19.off i 5 + c.column19.off i 13) + (c.column1.off i 6 - (c.column1.off i 7 + c.column1.off i 7)) * c.column21.off i 4 + (1 - (c.column1.off i 5 - (c.column1.off i 6 + c.column1.off i 6) + c.column1.off i 6 - (c.column1.off i 7 + c.column1.off i 7) + c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) * c.column19.off i 13) = 0)

structure cpu__update_registers (c : columns F) (inp : input_data F) : Prop :=
(update_pc__tmp0 : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → c.column21.off i 2 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10)) * c.column19.off i 9 = 0)
(update_pc__tmp1 : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → c.column21.off i 10 - c.column21.off i 2 * c.column21.off i 12 = 0)
(update_pc__pc_cond_negative : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (1 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) * c.column19.off i 16 + c.column21.off i 2 * (c.column19.off i 16 - (c.column19.off i 0 + c.column19.off i 13)) - ((1 - (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8) + c.column1.off i 8 - (c.column1.off i 9 + c.column1.off i 9) + c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) * (c.column19.off i 0 + c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + 1) + (c.column1.off i 7 - (c.column1.off i 8 + c.column1.off i 8)) * c.column21.off i 12 + (c.column1.off i 8 - (c.column1.off i 9 + c.column1.off i 9)) * (c.column19.off i 0 + c.column21.off i 12)) = 0)
(update_pc__pc_cond_positive : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → (c.column21.off i 10 - (c.column1.off i 9 - (c.column1.off i 10 + c.column1.off i 10))) * (c.column19.off i 16 - (c.column19.off i 0 + c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + 1)) = 0)
(update_ap__ap_update : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → c.column21.off i 16 - (c.column21.off i 0 + (c.column1.off i 10 - (c.column1.off i 11 + c.column1.off i 11)) * c.column21.off i 12 + c.column1.off i 11 - (c.column1.off i 12 + c.column1.off i 12) + (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) * 2) = 0)
(update_fp__fp_update : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ (i = 16 * (inp.trace_length / 16 - 1))) → c.column21.off i 24 - ((1 - (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13) + c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14))) * c.column21.off i 8 + (c.column1.off i 13 - (c.column1.off i 14 + c.column1.off i 14)) * c.column19.off i 9 + (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) * (c.column21.off i 0 + 2)) = 0)

structure cpu__opcodes (c : columns F) : Prop :=
(call__push_fp : ∀ i: nat, (((i % 16 = 0))) → (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) * (c.column19.off i 9 - c.column21.off i 8) = 0)
(call__push_pc : ∀ i: nat, (((i % 16 = 0))) → (c.column1.off i 12 - (c.column1.off i 13 + c.column1.off i 13)) * (c.column19.off i 5 - (c.column19.off i 0 + c.column1.off i 2 - (c.column1.off i 3 + c.column1.off i 3) + 1)) = 0)
(assert_eq__assert_eq : ∀ i: nat, (((i % 16 = 0))) → (c.column1.off i 14 - (c.column1.off i 15 + c.column1.off i 15)) * (c.column19.off i 9 - c.column21.off i 12) = 0)

structure initial_and_final (inp : input_data F) (c : columns F) : Prop :=
(initial_ap : ∀ i: nat, ((i = 0)) → c.column21.off i 0 - inp.initial_ap = 0)
(initial_fp : ∀ i: nat, ((i = 0)) → c.column21.off i 8 - inp.initial_ap = 0)
(initial_pc : ∀ i: nat, ((i = 0)) → c.column19.off i 0 - inp.initial_pc = 0)
(final_ap : ∀ i: nat, ((i = 16 * (inp.trace_length / 16 - 1))) → c.column21.off i 0 - inp.final_ap = 0)
(final_pc : ∀ i: nat, ((i = 16 * (inp.trace_length / 16 - 1))) → c.column19.off i 0 - inp.final_pc = 0)

structure memory (inp : input_data F) (pd : public_data F) (c : columns F) (ci : columns_inter F) : Prop :=
(multi_column_perm__perm__init0 : ∀ i: nat, ((i = 0)) → (pd.memory__multi_column_perm__perm__interaction_elm - (c.column20.off i 0 + pd.memory__multi_column_perm__hash_interaction_elm0 * c.column20.off i 1)) * ci.column24_inter1.off i 0 + c.column19.off i 0 + pd.memory__multi_column_perm__hash_interaction_elm0 * c.column19.off i 1 - pd.memory__multi_column_perm__perm__interaction_elm = 0)
(multi_column_perm__perm__step0 : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → (pd.memory__multi_column_perm__perm__interaction_elm - (c.column20.off i 2 + pd.memory__multi_column_perm__hash_interaction_elm0 * c.column20.off i 3)) * ci.column24_inter1.off i 2 - (pd.memory__multi_column_perm__perm__interaction_elm - (c.column19.off i 2 + pd.memory__multi_column_perm__hash_interaction_elm0 * c.column19.off i 3)) * ci.column24_inter1.off i 0 = 0)
(multi_column_perm__perm__last : ∀ i: nat, ((i = 2 * (inp.trace_length / 2 - 1))) → ci.column24_inter1.off i 0 - pd.memory__multi_column_perm__perm__public_memory_prod = 0)
(diff_is_bit : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → (c.column20.off i 2 - c.column20.off i 0) * (c.column20.off i 2 - c.column20.off i 0) - (c.column20.off i 2 - c.column20.off i 0) = 0)
(is_func : ∀ i: nat, (((i % 2 = 0)) ∧ ¬ (i = 2 * (inp.trace_length / 2 - 1))) → (c.column20.off i 2 - c.column20.off i 0 - 1) * (c.column20.off i 1 - c.column20.off i 3) = 0)

structure public_memory (c : columns F) : Prop :=
(memory_addr_zero : ∀ i: nat, (((i % 8 = 0))) → c.column19.off i 2 = 0)
(memory_value_zero : ∀ i: nat, (((i % 8 = 0))) → c.column19.off i 3 = 0)

structure rc16 (inp : input_data F) (pd : public_data F) (c : columns F) (ci : columns_inter F): Prop :=
(perm__init0 : ∀ i: nat, ((i = 0)) → (pd.rc16__perm__interaction_elm - c.column2.off i 0) * ci.column23_inter1.off i 0 + c.column0.off i 0 - pd.rc16__perm__interaction_elm = 0)
(perm__step0 : ∀ i: nat, (¬ (i = inp.trace_length - 1)) → (pd.rc16__perm__interaction_elm - c.column2.off i 1) * ci.column23_inter1.off i 1 - (pd.rc16__perm__interaction_elm - c.column0.off i 1) * ci.column23_inter1.off i 0 = 0)
(perm__last : ∀ i: nat, ((i = inp.trace_length - 1)) → ci.column23_inter1.off i 0 - pd.rc16__perm__public_memory_prod = 0)
(diff_is_bit : ∀ i: nat, (¬ (i = inp.trace_length - 1)) → (c.column2.off i 1 - c.column2.off i 0) * (c.column2.off i 1 - c.column2.off i 0) - (c.column2.off i 1 - c.column2.off i 0) = 0)
(minimum : ∀ i: nat, ((i = 0)) → c.column2.off i 0 - pd.rc_min = 0)
(maximum : ∀ i: nat, ((i = inp.trace_length - 1)) → c.column2.off i 0 - pd.rc_max = 0)

structure rc_builtin (inp : input_data F) (pd : public_data F) (c : columns F) : Prop :=
(value : ∀ i: nat, (((i % 128 = 0))) → ((((((c.column0.off i 12 * offset_size + c.column0.off i 28) * offset_size + c.column0.off i 44) * offset_size + c.column0.off i 60) * offset_size + c.column0.off i 76) * offset_size + c.column0.off i 92) * offset_size + c.column0.off i 108) * offset_size + c.column0.off i 124 - c.column19.off i 103 = 0)
(addr_step : ∀ i: nat, (((i % 128 = 0)) ∧ ¬ (i = 128 * (inp.trace_length / 128 - 1))) → c.column19.off i 230 - (c.column19.off i 102 + 1) = 0)
(init_addr : ∀ i: nat, ((i = 0)) → c.column19.off i 102 - pd.initial_rc_addr = 0)

structure pedersen (inp : input_data F) (pd : public_data F) (c : columns F) : Prop :=
(pedersen__hash0__ec_subset_sum__booleanity_test : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1)) * (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1) - 1) = 0)
(pedersen__hash0__ec_subset_sum__bit_extraction_end : ∀ i: nat, (((i % 256 = 252))) → c.column6.off i 0 = 0)
(pedersen__hash0__ec_subset_sum__zeros_tail : ∀ i: nat, (((i % 256 = 255))) → c.column6.off i 0 = 0)
(pedersen__hash0__ec_subset_sum__add_points__slope : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1)) * (c.column4.off i 0 - pd.pedersen__points__y) - c.column5.off i 0 * (c.column3.off i 0 - pd.pedersen__points__x) = 0)
(pedersen__hash0__ec_subset_sum__add_points__x : ∀ i: nat, (¬ ((i % 256 = 255))) → c.column5.off i 0 * c.column5.off i 0 - (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1)) * (c.column3.off i 0 + pd.pedersen__points__x + c.column3.off i 1) = 0)
(pedersen__hash0__ec_subset_sum__add_points__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1)) * (c.column4.off i 0 + c.column4.off i 1) - c.column5.off i 0 * (c.column3.off i 0 - c.column3.off i 1) = 0)
(pedersen__hash0__ec_subset_sum__copy_point__x : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1))) * (c.column3.off i 1 - c.column3.off i 0) = 0)
(pedersen__hash0__ec_subset_sum__copy_point__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column6.off i 0 - (c.column6.off i 1 + c.column6.off i 1))) * (c.column4.off i 1 - c.column4.off i 0) = 0)
(pedersen__hash0__copy_point__x : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column3.off i 256 - c.column3.off i 255 = 0)
(pedersen__hash0__copy_point__y : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column4.off i 256 - c.column4.off i 255 = 0)
(pedersen__hash0__init__x : ∀ i: nat, (((i % 512 = 0))) → c.column3.off i 0 - pd.pedersen__shift_point_x = 0)
(pedersen__hash0__init__y : ∀ i: nat, (((i % 512 = 0))) → c.column4.off i 0 - pd.pedersen__shift_point_y = 0)
(pedersen__hash1__ec_subset_sum__booleanity_test : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1)) * (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1) - 1) = 0)
(pedersen__hash1__ec_subset_sum__bit_extraction_end : ∀ i: nat, (((i % 256 = 252))) → c.column10.off i 0 = 0)
(pedersen__hash1__ec_subset_sum__zeros_tail : ∀ i: nat, (((i % 256 = 255))) → c.column10.off i 0 = 0)
(pedersen__hash1__ec_subset_sum__add_points__slope : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1)) * (c.column8.off i 0 - pd.pedersen__points__y) - c.column9.off i 0 * (c.column7.off i 0 - pd.pedersen__points__x) = 0)
(pedersen__hash1__ec_subset_sum__add_points__x : ∀ i: nat, (¬ ((i % 256 = 255))) → c.column9.off i 0 * c.column9.off i 0 - (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1)) * (c.column7.off i 0 + pd.pedersen__points__x + c.column7.off i 1) = 0)
(pedersen__hash1__ec_subset_sum__add_points__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1)) * (c.column8.off i 0 + c.column8.off i 1) - c.column9.off i 0 * (c.column7.off i 0 - c.column7.off i 1) = 0)
(pedersen__hash1__ec_subset_sum__copy_point__x : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1))) * (c.column7.off i 1 - c.column7.off i 0) = 0)
(pedersen__hash1__ec_subset_sum__copy_point__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column10.off i 0 - (c.column10.off i 1 + c.column10.off i 1))) * (c.column8.off i 1 - c.column8.off i 0) = 0)
(pedersen__hash1__copy_point__x : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column7.off i 256 - c.column7.off i 255 = 0)
(pedersen__hash1__copy_point__y : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column8.off i 256 - c.column8.off i 255 = 0)
(pedersen__hash1__init__x : ∀ i: nat, (((i % 512 = 0))) → c.column7.off i 0 - pd.pedersen__shift_point_x = 0)
(pedersen__hash1__init__y : ∀ i: nat, (((i % 512 = 0))) → c.column8.off i 0 - pd.pedersen__shift_point_y = 0)
(pedersen__hash2__ec_subset_sum__booleanity_test : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1)) * (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1) - 1) = 0)
(pedersen__hash2__ec_subset_sum__bit_extraction_end : ∀ i: nat, (((i % 256 = 252))) → c.column14.off i 0 = 0)
(pedersen__hash2__ec_subset_sum__zeros_tail : ∀ i: nat, (((i % 256 = 255))) → c.column14.off i 0 = 0)
(pedersen__hash2__ec_subset_sum__add_points__slope : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1)) * (c.column12.off i 0 - pd.pedersen__points__y) - c.column13.off i 0 * (c.column11.off i 0 - pd.pedersen__points__x) = 0)
(pedersen__hash2__ec_subset_sum__add_points__x : ∀ i: nat, (¬ ((i % 256 = 255))) → c.column13.off i 0 * c.column13.off i 0 - (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1)) * (c.column11.off i 0 + pd.pedersen__points__x + c.column11.off i 1) = 0)
(pedersen__hash2__ec_subset_sum__add_points__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1)) * (c.column12.off i 0 + c.column12.off i 1) - c.column13.off i 0 * (c.column11.off i 0 - c.column11.off i 1) = 0)
(pedersen__hash2__ec_subset_sum__copy_point__x : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1))) * (c.column11.off i 1 - c.column11.off i 0) = 0)
(pedersen__hash2__ec_subset_sum__copy_point__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column14.off i 0 - (c.column14.off i 1 + c.column14.off i 1))) * (c.column12.off i 1 - c.column12.off i 0) = 0)
(pedersen__hash2__copy_point__x : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column11.off i 256 - c.column11.off i 255 = 0)
(pedersen__hash2__copy_point__y : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column12.off i 256 - c.column12.off i 255 = 0)
(pedersen__hash2__init__x : ∀ i: nat, (((i % 512 = 0))) → c.column11.off i 0 - pd.pedersen__shift_point_x = 0)
(pedersen__hash2__init__y : ∀ i: nat, (((i % 512 = 0))) → c.column12.off i 0 - pd.pedersen__shift_point_y = 0)
(pedersen__hash3__ec_subset_sum__booleanity_test : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1)) * (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1) - 1) = 0)
(pedersen__hash3__ec_subset_sum__bit_extraction_end : ∀ i: nat, (((i % 256 = 252))) → c.column18.off i 0 = 0)
(pedersen__hash3__ec_subset_sum__zeros_tail : ∀ i: nat, (((i % 256 = 255))) → c.column18.off i 0 = 0)
(pedersen__hash3__ec_subset_sum__add_points__slope : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1)) * (c.column16.off i 0 - pd.pedersen__points__y) - c.column17.off i 0 * (c.column15.off i 0 - pd.pedersen__points__x) = 0)
(pedersen__hash3__ec_subset_sum__add_points__x : ∀ i: nat, (¬ ((i % 256 = 255))) → c.column17.off i 0 * c.column17.off i 0 - (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1)) * (c.column15.off i 0 + pd.pedersen__points__x + c.column15.off i 1) = 0)
(pedersen__hash3__ec_subset_sum__add_points__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1)) * (c.column16.off i 0 + c.column16.off i 1) - c.column17.off i 0 * (c.column15.off i 0 - c.column15.off i 1) = 0)
(pedersen__hash3__ec_subset_sum__copy_point__x : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1))) * (c.column15.off i 1 - c.column15.off i 0) = 0)
(pedersen__hash3__ec_subset_sum__copy_point__y : ∀ i: nat, (¬ ((i % 256 = 255))) → (1 - (c.column18.off i 0 - (c.column18.off i 1 + c.column18.off i 1))) * (c.column16.off i 1 - c.column16.off i 0) = 0)
(pedersen__hash3__copy_point__x : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column15.off i 256 - c.column15.off i 255 = 0)
(pedersen__hash3__copy_point__y : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ ((i % 512 = 256))) → c.column16.off i 256 - c.column16.off i 255 = 0)
(pedersen__hash3__init__x : ∀ i: nat, (((i % 512 = 0))) → c.column15.off i 0 - pd.pedersen__shift_point_x = 0)
(pedersen__hash3__init__y : ∀ i: nat, (((i % 512 = 0))) → c.column16.off i 0 - pd.pedersen__shift_point_y = 0)
(pedersen__input0_value0 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 7 - c.column6.off i 0 = 0)
(pedersen__input0_value1 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 135 - c.column10.off i 0 = 0)
(pedersen__input0_value2 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 263 - c.column14.off i 0 = 0)
(pedersen__input0_value3 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 391 - c.column18.off i 0 = 0)
(pedersen__input0_addr : ∀ i: nat, (((i % 128 = 0)) ∧ ¬ (i = 128 * (inp.trace_length / 128 - 1))) → c.column19.off i 134 - (c.column19.off i 38 + 1) = 0)
(pedersen__init_addr : ∀ i: nat, ((i = 0)) → c.column19.off i 6 - pd.initial_pedersen_addr = 0)
(pedersen__input1_value0 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 71 - c.column6.off i 256 = 0)
(pedersen__input1_value1 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 199 - c.column10.off i 256 = 0)
(pedersen__input1_value2 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 327 - c.column14.off i 256 = 0)
(pedersen__input1_value3 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 455 - c.column18.off i 256 = 0)
(pedersen__input1_addr : ∀ i: nat, (((i % 128 = 0))) → c.column19.off i 70 - (c.column19.off i 6 + 1) = 0)
(pedersen__output_value0 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 39 - c.column3.off i 511 = 0)
(pedersen__output_value1 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 167 - c.column7.off i 511 = 0)
(pedersen__output_value2 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 295 - c.column11.off i 511 = 0)
(pedersen__output_value3 : ∀ i: nat, (((i % 512 = 0))) → c.column19.off i 423 - c.column15.off i 511 = 0)
(pedersen__output_addr : ∀ i: nat, (((i % 128 = 0))) → c.column19.off i 38 - (c.column19.off i 70 + 1) = 0)

structure ecdsa (inp : input_data F) (pd : public_data F) (c : columns F) : Prop :=
(ecdsa__signature0__doubling_key__slope : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → c.column21.off i 6 * c.column21.off i 6 + c.column21.off i 6 * c.column21.off i 6 + c.column21.off i 6 * c.column21.off i 6 + pd.ecdsa__sig_config_alpha - (c.column21.off i 14 + c.column21.off i 14) * c.column21.off i 1 = 0)
(ecdsa__signature0__doubling_key__x : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → c.column21.off i 1 * c.column21.off i 1 - (c.column21.off i 6 + c.column21.off i 6 + c.column21.off i 22) = 0)
(ecdsa__signature0__doubling_key__y : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → c.column21.off i 14 + c.column21.off i 30 - c.column21.off i 1 * (c.column21.off i 6 - c.column21.off i 22) = 0)
(ecdsa__signature0__exponentiate_generator__booleanity_test : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63)) * (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63) - 1) = 0)
(ecdsa__signature0__exponentiate_generator__bit_extraction_end : ∀ i: nat, (((i % 8192 = 8032))) → c.column21.off i 31 = 0)
(ecdsa__signature0__exponentiate_generator__zeros_tail : ∀ i: nat, (((i % 8192 = 8160))) → c.column21.off i 31 = 0)
(ecdsa__signature0__exponentiate_generator__add_points__slope : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63)) * (c.column21.off i 23 - pd.ecdsa__generator_points__y) - c.column21.off i 15 * (c.column21.off i 7 - pd.ecdsa__generator_points__x) = 0)
(ecdsa__signature0__exponentiate_generator__add_points__x : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → c.column21.off i 15 * c.column21.off i 15 - (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63)) * (c.column21.off i 7 + pd.ecdsa__generator_points__x + c.column21.off i 39) = 0)
(ecdsa__signature0__exponentiate_generator__add_points__y : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63)) * (c.column21.off i 23 + c.column21.off i 55) - c.column21.off i 15 * (c.column21.off i 7 - c.column21.off i 39) = 0)
(ecdsa__signature0__exponentiate_generator__add_points__x_diff_inv : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → c.column22.off i 0 * (c.column21.off i 7 - pd.ecdsa__generator_points__x) - 1 = 0)
(ecdsa__signature0__exponentiate_generator__copy_point__x : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → (1 - (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63))) * (c.column21.off i 39 - c.column21.off i 7) = 0)
(ecdsa__signature0__exponentiate_generator__copy_point__y : ∀ i: nat, (((i % 32 = 0)) ∧ ¬ ((i % 8192 = 8160))) → (1 - (c.column21.off i 31 - (c.column21.off i 63 + c.column21.off i 63))) * (c.column21.off i 55 - c.column21.off i 23) = 0)
(ecdsa__signature0__exponentiate_key__booleanity_test : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19)) * (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19) - 1) = 0)
(ecdsa__signature0__exponentiate_key__bit_extraction_end : ∀ i: nat, (((i % 4096 = 4016))) → c.column21.off i 3 = 0)
(ecdsa__signature0__exponentiate_key__zeros_tail : ∀ i: nat, (((i % 4096 = 4080))) → c.column21.off i 3 = 0)
(ecdsa__signature0__exponentiate_key__add_points__slope : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19)) * (c.column21.off i 5 - c.column21.off i 14) - c.column21.off i 13 * (c.column21.off i 9 - c.column21.off i 6) = 0)
(ecdsa__signature0__exponentiate_key__add_points__x : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → c.column21.off i 13 * c.column21.off i 13 - (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19)) * (c.column21.off i 9 + c.column21.off i 6 + c.column21.off i 25) = 0)
(ecdsa__signature0__exponentiate_key__add_points__y : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19)) * (c.column21.off i 5 + c.column21.off i 21) - c.column21.off i 13 * (c.column21.off i 9 - c.column21.off i 25) = 0)
(ecdsa__signature0__exponentiate_key__add_points__x_diff_inv : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → c.column21.off i 11 * (c.column21.off i 9 - c.column21.off i 6) - 1 = 0)
(ecdsa__signature0__exponentiate_key__copy_point__x : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → (1 - (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19))) * (c.column21.off i 25 - c.column21.off i 9) = 0)
(ecdsa__signature0__exponentiate_key__copy_point__y : ∀ i: nat, (((i % 16 = 0)) ∧ ¬ ((i % 4096 = 4080))) → (1 - (c.column21.off i 3 - (c.column21.off i 19 + c.column21.off i 19))) * (c.column21.off i 21 - c.column21.off i 5) = 0)
(ecdsa__signature0__init_gen__x : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 7 - pd.ecdsa__sig_config_shift_point_x = 0)
(ecdsa__signature0__init_gen__y : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 23 + pd.ecdsa__sig_config_shift_point_y = 0)
(ecdsa__signature0__init_key__x : ∀ i: nat, (((i % 4096 = 0))) → c.column21.off i 9 - pd.ecdsa__sig_config_shift_point_x = 0)
(ecdsa__signature0__init_key__y : ∀ i: nat, (((i % 4096 = 0))) → c.column21.off i 5 - pd.ecdsa__sig_config_shift_point_y = 0)
(ecdsa__signature0__add_results__slope : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8183 - (c.column21.off i 4085 + c.column22.off i 8160 * (c.column21.off i 8167 - c.column21.off i 4089)) = 0)
(ecdsa__signature0__add_results__x : ∀ i: nat, (((i % 8192 = 0))) → c.column22.off i 8160 * c.column22.off i 8160 - (c.column21.off i 8167 + c.column21.off i 4089 + c.column21.off i 4102) = 0)
(ecdsa__signature0__add_results__y : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8183 + c.column21.off i 4110 - c.column22.off i 8160 * (c.column21.off i 8167 - c.column21.off i 4102) = 0)
(ecdsa__signature0__add_results__x_diff_inv : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8175 * (c.column21.off i 8167 - c.column21.off i 4089) - 1 = 0)
(ecdsa__signature0__extract_r__slope : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8181 + pd.ecdsa__sig_config_shift_point_y - c.column21.off i 4093 * (c.column21.off i 8185 - pd.ecdsa__sig_config_shift_point_x) = 0)
(ecdsa__signature0__extract_r__x : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 4093 * c.column21.off i 4093 - (c.column21.off i 8185 + pd.ecdsa__sig_config_shift_point_x + c.column21.off i 3) = 0)
(ecdsa__signature0__extract_r__x_diff_inv : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8189 * (c.column21.off i 8185 - pd.ecdsa__sig_config_shift_point_x) - 1 = 0)
(ecdsa__signature0__z_nonzero : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 31 * c.column21.off i 4081 - 1 = 0)
(ecdsa__signature0__r_and_w_nonzero : ∀ i: nat, (((i % 4096 = 0))) → c.column21.off i 3 * c.column21.off i 4091 - 1 = 0)
(ecdsa__signature0__q_on_curve__x_squared : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 8177 - c.column21.off i 6 * c.column21.off i 6 = 0)
(ecdsa__signature0__q_on_curve__on_curve : ∀ i: nat, (((i % 8192 = 0))) → c.column21.off i 14 * c.column21.off i 14 - (c.column21.off i 6 * c.column21.off i 8177 + pd.ecdsa__sig_config_alpha * c.column21.off i 6 + pd.ecdsa__sig_config_beta) = 0)
(ecdsa__init_addr : ∀ i: nat, ((i = 0)) → c.column19.off i 22 - pd.initial_ecdsa_addr = 0)
(ecdsa__message_addr : ∀ i: nat, (((i % 8192 = 0))) → c.column19.off i 4118 - (c.column19.off i 22 + 1) = 0)
(ecdsa__pubkey_addr : ∀ i: nat, (((i % 8192 = 0)) ∧ ¬ (i = 8192 * (inp.trace_length / 8192 - 1))) → c.column19.off i 8214 - (c.column19.off i 4118 + 1) = 0)
(ecdsa__message_value0 : ∀ i: nat, (((i % 8192 = 0))) → c.column19.off i 4119 - c.column21.off i 31 = 0)
(ecdsa__pubkey_value0 : ∀ i: nat, (((i % 8192 = 0))) → c.column19.off i 23 - c.column21.off i 6 = 0)

structure checkpoints (c : columns F) (inp : input_data F) (pd : public_data F) : Prop :=
(checkpoints__req_pc_init_addr : ∀ i: nat, ((i = 0)) → c.column19.off i 150 - pd.initial_checkpoints_addr = 0)
(checkpoints__req_pc_final_addr : ∀ i: nat, ((i = 256 * (inp.trace_length / 256 - 1))) → c.column19.off i 150 - pd.final_checkpoints_addr = 0)
(checkpoints__required_fp_addr : ∀ i: nat, (((i % 256 = 0))) → c.column19.off i 86 - (c.column19.off i 150 + 1) = 0)
(checkpoints__required_pc_next_addr : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ (i = 256 * (inp.trace_length / 256 - 1))) → (c.column19.off i 406 - c.column19.off i 150) * (c.column19.off i 406 - (c.column19.off i 150 + 2)) = 0)
(checkpoints__req_pc : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ (i = 256 * (inp.trace_length / 256 - 1))) → (c.column19.off i 406 - c.column19.off i 150) * (c.column19.off i 151 - c.column19.off i 0) = 0)
(checkpoints__req_fp : ∀ i: nat, (((i % 256 = 0)) ∧ ¬ (i = 256 * (inp.trace_length / 256 - 1))) → (c.column19.off i 406 - c.column19.off i 150) * (c.column19.off i 87 - c.column21.off i 8) = 0)
