import dataclasses
from typing import List

from starkware.cairo.lang.compiler.preprocessor.preprocessor import PreprocessedProgram
from starkware.cairo.lean.verification.lean_instruction_builder import (
    LeanCodeElement,
    build_lean_instruction,
)

# Information from the preprocessed instructions.


@dataclasses.dataclass
class LeanAssemblyInfo:
    """
    Stores information needed for Lean verification, extracted from the preprocessed
    Instructions.
    """

    pc = 0
    lean_pc = 0
    lean_code: List[LeanCodeElement] = dataclasses.field(default_factory=lambda: [])
    pc_lookup: List[int] = dataclasses.field(default_factory=lambda: [])

    def add_instruction(self, instr):
        lean_instr = build_lean_instruction(instr)
        self.lean_code.append(lean_instr)
        for _ in range(len(lean_instr.code)):
            self.pc_lookup.append(self.lean_pc)
            self.pc += 1
        self.lean_pc += 1

    def close_pc_lookup(self):
        self.pc_lookup.append(self.lean_pc)

    def build_from_preprocessed(self, preprocessed_program: PreprocessedProgram):
        for inst in preprocessed_program.instructions:
            self.add_instruction(inst.instruction)
