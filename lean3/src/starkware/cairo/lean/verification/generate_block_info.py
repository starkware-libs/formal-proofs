from starkware.cairo.lang.compiler.preprocessor.flow import FlowTrackingDataActual
from starkware.cairo.lean.verification.expr_to_lean import LeanDescContext, LeanExprSimplifier
from starkware.cairo.lean.verification.lean_processed_info import (
    LeanBlockInfo,
    LeanFunctionInfo,
    LeanProgramInfo,
)
from starkware.cairo.lean.verification.lean_raw_info import (
    LeanPreprocessedAssertEq,
    LeanPreprocessedCompoundAssertEq,
    LeanPreprocessedConst,
    LeanPreprocessedFuncCall,
    LeanPreprocessedIf,
    LeanPreprocessedJumpToLabelInstruction,
    LeanPreprocessedReference,
    LeanPreprocessedReturn,
    LeanPreprocessedTailCall,
    LeanPreprocessedTempVar,
)


def process_block(lean_info: LeanProgramInfo, func: LeanFunctionInfo, lean_desc_num: int):
    """
    This processes a block of instructions, ending with a function return, a conditional, or
    a jump, or encountering a label.
    """
    if lean_desc_num in func.block_list:
        # block has already been processed
        return
    first_instr = func.lean_desc[lean_desc_num]
    assert isinstance(
        first_instr.flow_tracking_data, FlowTrackingDataActual
    ), "Expected actual tracking data on instruction."
    this_block = LeanBlockInfo(first_instr.flow_tracking_data)
    simplifier = LeanExprSimplifier(lean_info.preprocessor)
    simplifier.set_instr(first_instr)
    desc_ctx = LeanDescContext(
        simplifier=simplifier,
        cairo_type=None,
        struct_defs=lean_info.struct_defs,
        identifiers=lean_info.identifiers,
        func_scope=func.func_scope,
        open_namespaces=func.open_namespaces,
    )
    this_block.add_var_info(
        func_scope=func.func_scope,
        open_namespaces=lean_info.open_namespaces,
        func_args=func.arg_names,
        identifiers=func.identifiers,
        references=lean_info.reference_manager,
        desc_ctx=desc_ctx,
    )
    for label in func.label_dict:
        if func.label_dict[label] == lean_desc_num:
            this_block.label = label
    func.block_list[lean_desc_num] = this_block
    labeled_desc_nums = func.label_dict.values()
    while lean_desc_num < len(func.lean_desc):
        instr = func.lean_desc[lean_desc_num]
        if isinstance(instr, LeanPreprocessedAssertEq):
            pass
        elif isinstance(instr, LeanPreprocessedCompoundAssertEq):
            pass
        elif (isinstance(instr, LeanPreprocessedReference) and not instr.asserts) or isinstance(
            instr, LeanPreprocessedTempVar
        ):
            pass
        elif isinstance(instr, LeanPreprocessedConst):
            pass
        elif isinstance(instr, LeanPreprocessedTailCall):
            # This is also a return, so terminate the block.
            return
        elif isinstance(instr, LeanPreprocessedFuncCall):
            pass
        elif isinstance(instr, LeanPreprocessedIf):
            assert instr.jump_instr is not None, "Missing jump in if statement."
            neg_lean_desc_num = func.label_dict[instr.jump_instr.label_name]
            this_block.flows_to = [lean_desc_num + 1, neg_lean_desc_num]
            process_block(lean_info, func, lean_desc_num + 1)
            process_block(lean_info, func, neg_lean_desc_num)
            return
        elif isinstance(instr, LeanPreprocessedJumpToLabelInstruction) and instr.condition is None:
            next_lean_desc_num = func.label_dict[instr.label_name]
            this_block.flows_to = [next_lean_desc_num]
            process_block(lean_info, func, next_lean_desc_num)
            return
        elif (
            isinstance(instr, LeanPreprocessedJumpToLabelInstruction)
            and instr.condition is not None
        ):
            neg_lean_desc_num = func.label_dict[instr.label_name]
            this_block.flows_to = [lean_desc_num + 1, neg_lean_desc_num]
            process_block(lean_info, func, lean_desc_num + 1)
            process_block(lean_info, func, neg_lean_desc_num)
            return
        elif isinstance(instr, LeanPreprocessedReturn):
            return
        # Advance to next instruction.
        lean_desc_num += 1
        if lean_desc_num in labeled_desc_nums:
            # Flow to a label.
            this_block.flows_to = [lean_desc_num]
            process_block(lean_info, func, lean_desc_num)
            return
    # This shouldn't happen.
    raise Exception("Expected a return to end the block")


def analyze_func_blocks(func: LeanFunctionInfo):
    # Determine the immediate predecessors:
    for block1 in func.block_list:
        func.block_list[block1].flows_from = []
        for block2 in func.block_list:
            if block1 in func.block_list[block2].flows_to:
                func.block_list[block1].flows_from.append(block2)

    # Sort the blocks so that earlier ones don't depend on later ones.
    func.dependency_order = []
    done = False
    while not done:
        done = True
        for block in func.block_list:
            if block not in func.dependency_order:
                flows_to = func.block_list[block].flows_to
                if all(i in func.dependency_order for i in flows_to):
                    func.dependency_order.append(block)
                    done = False
    func.join_points = [
        block for block in func.dependency_order if len(func.block_list[block].flows_from) > 1
    ]
    func.has_loop = len(func.dependency_order) < len(func.block_list)
    if func.has_loop:
        print(f"Loop detected in function {func.name}.")


def print_block_info(func):
    for key in func.block_list:
        block = func.block_list[key]
        print("Block at instruction {}".format(key))
        print(
            "  ap: group {}, offset {}".format(
                block.flow_at_start.ap_tracking.group, block.flow_at_start.ap_tracking.offset
            )
        )
        if block.flow_at_start.reference_ids:
            print("  Identifiers:")
            for ident in block.flow_at_start.reference_ids:
                print("    ", ident)
        if block.label:
            print("  Label: ", block.label)
        if block.flows_to:
            print("  Flows to: ", ", ".join(map(str, block.flows_to)))
        if block.flows_from:
            print("  Flows from: ", ", ".join(map(str, block.flows_from)))
    print("Dependency order:", ", ".join(map(str, func.dependency_order)))


def analyze_blocks(lean_info: LeanProgramInfo):
    """
    Perform the block analysis for all functions.
    """

    for func in lean_info.function_dict.values():
        process_block(lean_info, func, 0)
        analyze_func_blocks(func)
