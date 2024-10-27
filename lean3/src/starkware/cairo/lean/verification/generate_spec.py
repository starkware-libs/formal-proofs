import dataclasses
import re
from typing import Dict, List, Optional, Tuple

from starkware.cairo.lang.compiler.cairo_compile import get_codes
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.expr_to_lean import LeanExprSimplifier
from starkware.cairo.lean.verification.generate_block_spec import (
    LeanSpecBlockGenerator,
    LeanTraceCount,
)
from starkware.cairo.lean.verification.generate_defs import add_lean_defs_to_file
from starkware.cairo.lean.verification.generate_prelude import (
    insert_additional_imports,
    insert_lean_prelude,
    insert_open_import_namespaces,
)
from starkware.cairo.lean.verification.generate_rc import SpecRCSteps
from starkware.cairo.lean.verification.generate_soundness import (
    LEAN_CODE_INDENT,
    mk_lean_auto_spec_name,
    mk_lean_user_soundness_name,
    mk_lean_user_spec_name,
)
from starkware.cairo.lean.verification.lean_file_names import (
    LeanFileNames,
    mk_lean_core_import_path,
    mk_lean_spec_import_path,
)
from starkware.cairo.lean.verification.lean_processed_info import LeanFunctionInfo, LeanProgramInfo
from starkware.cairo.lean.verification.rebinding import name_with_sub
from starkware.cairo.lean.verification.scope_to_lean import get_name_in_scope
from starkware.cairo.lean.verification.type_to_lean import create_arg_defs


@dataclasses.dataclass
class LeanSpecGenerator:
    """
    Generates the Lean specification file for a set of preprocessed Cairo functions.
    If a specification file already exists, the new specifications will be added
    to the existing file as follows:
    1. The automatic specifications are replaced.
    2. A user specification placeholder is added if no user specification is
       found in the file.
    Except for the automatic specifications, nothing in the existing specification
    file is discarded.
    """

    file_names: LeanFileNames
    lean_info: LeanProgramInfo
    simplifier: LeanExprSimplifier
    # True if an existing spec file was read (this file is then used to initialize
    # the new spec file).
    spec_file_exists: bool = False
    # The specification file, split into lines. The strings should not end
    # with an EOL character (these are added when writing to the file).
    # An entry in this list may contain EOL characters, resulting in
    # multiple lines in the specification file.
    specs: List[str] = dataclasses.field(default_factory=lambda: [])
    # The current function being processed.
    func: Optional[LeanFunctionInfo] = None

    @property
    def main_scope(self) -> ScopedName:
        return self.lean_info.main_scope

    def get_existing_specs(self):
        """
        Reads the specification file if it exists and stores it on the object.
        """
        try:
            codes = get_codes([self.file_names.spec_filename])
            if len(codes) == 0:
                return
            self.spec_file_exists = True
            self.specs = codes[0][0].splitlines()
        except:
            pass

    def find_auto_spec_in_existing(self, func: LeanFunctionInfo) -> Optional[Tuple[int, int]]:
        """
        Returns the start and end line of the auto specifications for the given
        function in the existing specification file. Returns None if not found.
        The second line is the line just after the last character of the
        auto specification.
        """
        if not self.spec_file_exists:
            return None
        # The auto spec starts with 'def <auto spec name> (' or
        # or 'def <auto spec name>_block<number> ('
        start_exp = re.compile(
            r"\s*def " + mk_lean_auto_spec_name(func.name, [self.main_scope]) + r"(_block\d*)?\s*\("
        )
        for start, line in enumerate(self.specs):
            if start_exp.match(line) is not None:
                break
        else:
            return None

        # Go over all definitions which belong to the auto spec of this function.
        end = start
        def_end: Optional[int] = start

        while def_end is not None:
            end = def_end
            def_end = self.check_auto_spec_def(func=func, start=def_end, skip_ws=True)

        return (start, end)

    def check_auto_spec_def(
        self,
        func: LeanFunctionInfo,
        start: int,
        skip_ws: bool,
    ) -> Optional[int]:
        """
        Checks whether a definition belonging to the auto spec of the given function
        begins at the given start line (optionally skipping empty lines). Returns
        None if not. If a definition is found, return the line number following the
        last line of the definition.
        """
        if not self.spec_file_exists:
            return None
        if skip_ws:
            while start < len(self.specs):
                if self.specs[start] and not self.specs[start].isspace():
                    break
                start += 1
        # All auto spec definitions start with 'def <auto spec name>'.
        start_str = "def " + mk_lean_auto_spec_name(func.name, [self.main_scope])
        if start == len(self.specs) or not self.specs[start].startswith(start_str):
            return None
        # The auto spec ends with an empty (whitespace) line (or the end of the file).
        for end in range(start + 1, len(self.specs)):
            if not self.specs[end] or self.specs[end].isspace():
                end += 1  # Include the empty line as well.
                break

        return end

    def find_prelude_comment_in_existing(self, before: int) -> int:
        """
        Returns the beginning of the comments that precede a given line (which
        is assumed not to be part of a comment)
        """
        in_comment = False
        start_prelude = before
        for pos in reversed(range(0, before)):
            line = self.specs[pos]
            if in_comment:
                if line.lstrip().startswith("/-"):
                    start_prelude = pos
                    in_comment = False
            elif line == "" or line.isspace():
                continue
            elif line.lstrip().startswith("--"):
                start_prelude = pos
            elif line.rstrip().endswith("-/"):
                in_comment = True
            else:
                break

        return start_prelude

    def find_first_auto_spec_in_existing(
        self,
        funcs: List[LeanFunctionInfo],
    ) -> Optional[Tuple[int, int, int, LeanFunctionInfo]]:
        """
        Returns the start and end line of the auto specification for the first function
        in the given list for which the auto specification was found in the existing
        specification file. Three line numbers are returned: the beginning of any comment which
        is a prelude to the specification, the start of the specification itself and the
        end of the specification. In addition to the line numbers, it returns the information
        object of the function.
        Returns None if the auto specifications of none of the functions could be found.
        """
        if not self.spec_file_exists:
            return None

        for func in funcs:
            lines = self.find_auto_spec_in_existing(func)
            if lines is not None:
                comment_start = self.find_prelude_comment_in_existing(lines[0])
                return (comment_start, lines[0], lines[1], func)
        else:
            return None

    def find_user_spec_in_existing(
        self,
        func: LeanFunctionInfo,
        with_prelude: bool = True,
    ) -> Optional[Tuple[int, int]]:
        """
        Returns a pair which is the line range (first, last) at which an existing user
        specification for this function appears. By default, this includes any prelude comment.
        The specification ends at the first empty line (or the end of the file).
        If the user specification doe snot appear in the file, None is returned.
        """
        if not self.spec_file_exists:
            return None
        # The user spec starts with 'def <user spec name> ('.
        start_str = "def " + mk_lean_user_spec_name(func.name, [self.main_scope]) + " ("
        for line_num, line in enumerate(self.specs):
            if line.strip().startswith(start_str):
                # The user spec ends with an empty (whitespace) line (or the end of the file).
                for end in range(line_num + 1, len(self.specs)):
                    if not self.specs[end] or self.specs[end].isspace():
                        break
                return (
                    self.find_prelude_comment_in_existing(line_num) if with_prelude else line_num,
                    end,
                )

        return None

    def has_user_spec_in_existing(self, func: LeanFunctionInfo) -> bool:
        """
        Checks whether the user specification of the given function is defined
        in the existing specification file
        """
        return self.find_user_spec_in_existing(func) is not None

    def find_user_soundness_in_existing(
        self,
        func: LeanFunctionInfo,
        with_prelude: bool = True,
    ) -> Optional[int]:
        """
        Find the first line of the user soundness theorem (including prelude comment)
        of the given function in the existing specification file. Returns
        the line number or None, if not found.
        """
        if not self.spec_file_exists:
            return None
        # The soundness theorem starts with the line 'theorem <user soundness name>'.
        start_line = "theorem " + mk_lean_user_soundness_name(func.name, [self.main_scope])
        for line_num, line in enumerate(self.specs):
            if line.strip() == start_line:
                return self.find_prelude_comment_in_existing(line_num) if with_prelude else line_num
        return None

    def has_user_soundness_in_existing(self, func: LeanFunctionInfo) -> bool:
        """
        Checks whether the user soundness theorem of the given function is defined
        in the existing specification file
        """
        return self.find_user_soundness_in_existing(func) is not None

    def get_func_spec_arg_list(self, func: LeanFunctionInfo) -> List[str]:
        arg_types = func.get_args_with_type(with_ret=True)
        return create_arg_defs(arg_types)

    def get_block_spec_args(self, func: LeanFunctionInfo, block_desc_num: int) -> Dict[str, str]:
        assert block_desc_num in func.block_list
        arg_types = func.block_list[block_desc_num].get_args_with_type()
        arg_types.update(func.get_ret_args_with_type())
        return arg_types

    def get_block_spec_arg_list(self, func: LeanFunctionInfo, block_desc_num: int) -> List[str]:
        """
        Returns the list of arguments of a block, as they should appear in the spec
        definition, with their Lean type indications (e.g. "(a b : F)").
        """
        return create_arg_defs(self.get_block_spec_args(func, block_desc_num))

    def get_block_spec_arg_names(
        self,
        func: LeanFunctionInfo,
        block_desc_num: int,
        name_sub: Optional[Dict[str, int]],
    ) -> List[str]:
        """
        Returns the list of names of arguments of a block (without types). When
        a list of subscripts is provided, those subscripts are used for the variable.
        """
        base_names = list(self.get_block_spec_args(func, block_desc_num))
        return (
            [name_with_sub(name, name_sub) for name in base_names]
            if name_sub is not None
            else base_names
        )

    def mk_lean_function_auto_spec(self, func: LeanFunctionInfo) -> str:
        """
        Generates the auto specifications for the given function and returns
        the result as a single string (without an EOL character at the end)
        """

        # HACK: for now, just add the blocks here.
        specs = ""
        for block_desc_num in func.join_points:
            specs += self.mk_lean_block_auto_spec(func, block_desc_num) + "\n\n"

        self.func = func
        # Subscript to use for each name (for rebinding). 0 means no subscript.
        name_sub = {name: 0 for name in func.arg_names}

        auto_spec_name = mk_lean_auto_spec_name(func.name, [self.main_scope])
        arg_defs = self.get_func_spec_arg_list(func)

        specs += (
            f"def {auto_spec_name} (mem : F → F) (κ : ℕ)"
            + (" " + " ".join(arg_defs) if arg_defs else "")
            + " : Prop :=\n"
        )

        if self.func.has_loop:
            specs += " " * LEAN_CODE_INDENT + "true\n"
            return specs

        block_ctx = LeanSpecBlockGenerator(
            func=func,
            lean_info=self.lean_info,
            simplifier=self.simplifier,
            spec_start_lean_desc=0,
            lean_desc_num=0,
            name_sub=name_sub,
            trace_count=LeanTraceCount(),
            rc_steps=SpecRCSteps(rc_builtin=func.rc) if func.rc is not None else None,
            num_func_calls=0,
        )
        block_ctx.indent()
        asserts = block_ctx.mk_block_specs()
        specs += " " * LEAN_CODE_INDENT + "".join(asserts)

        return specs

    def mk_lean_block_auto_spec(self, func: LeanFunctionInfo, block_desc_num: int) -> str:
        """
        Generates the auto specifications for the given function and block and returns
        the result as a single string (without an EOL character at the end)
        """
        self.func = func
        # Subscript to use for each name (for rebinding). 0 means no subscript.
        name_sub = {name: 0 for name in self.get_block_spec_arg_names(func, block_desc_num, None)}

        auto_spec_name = (
            mk_lean_auto_spec_name(func.name, [self.main_scope]) + "_block" + str(block_desc_num)
        )
        arg_defs = self.get_block_spec_arg_list(func, block_desc_num)

        specs = (
            f"def {auto_spec_name} (mem : F → F) (κ : ℕ)"
            + (" " + " ".join(arg_defs) if arg_defs else "")
            + " : Prop :=\n"
        )

        if self.func.has_loop:
            specs += " " * LEAN_CODE_INDENT + "true\n"
            return specs

        block_ctx = LeanSpecBlockGenerator(
            func=func,
            lean_info=self.lean_info,
            simplifier=self.simplifier,
            spec_start_lean_desc=block_desc_num,
            lean_desc_num=block_desc_num,
            name_sub=name_sub,
            trace_count=LeanTraceCount(),
            rc_steps=SpecRCSteps(rc_builtin=func.rc) if func.rc is not None else None,
            num_func_calls=0,
        )
        block_ctx.indent()
        asserts = block_ctx.mk_block_specs()
        specs += " " * LEAN_CODE_INDENT + "".join(asserts)

        return specs

    def mk_lean_function_user_spec(
        self, func: LeanFunctionInfo, with_comment: bool = True
    ) -> List[str]:
        """
        Returns a string which is the default user specification for the given function.
        """
        user_spec_name = mk_lean_user_spec_name(func.name, [self.main_scope])
        auto_spec_name = mk_lean_auto_spec_name(func.name, self.lean_info.open_namespaces)
        arg_defs = self.get_func_spec_arg_list(func)
        arg_names = " ".join(func.arg_names + func.get_ret_arg_names())

        specs = (
            ["-- You may change anything in this definition except the name and arguments."]
            if with_comment
            else []
        )

        specs += [
            f"def {user_spec_name} (mem : F → F) (κ : ℕ)"
            + (" " + " ".join(arg_defs) if arg_defs else "")
            + " : Prop :="
        ]

        if not func.is_recursive:
            spec_def = " " * LEAN_CODE_INDENT + f"{auto_spec_name} mem κ"
            if arg_names:
                spec_def += " " + arg_names
            specs.append(spec_def)
        else:
            specs.append(" " * LEAN_CODE_INDENT + "true")

        return specs

    def mk_lean_function_user_soundness_theorem(
        self,
        func: LeanFunctionInfo,
        with_comment: bool = True,
        with_proof: bool = True,
    ) -> List[str]:
        """
        Returns a list of string which is the soundness proof for the default user specifications.
        """
        arg_defs = self.get_func_spec_arg_list(func)
        arg_names = " ".join(func.arg_names + func.get_ret_arg_names())
        auto_spec_name = mk_lean_auto_spec_name(func.name, self.lean_info.open_namespaces)
        user_spec_name = mk_lean_user_spec_name(func.name, self.lean_info.open_namespaces)
        theorem_name = mk_lean_user_soundness_name(func.name, [self.main_scope])

        if with_comment:
            specs = [
                "/- {} soundness theorem -/".format(
                    get_name_in_scope(func.func_scope, self.main_scope)
                ),
                "",
            ]
            specs.append(
                "-- Do not change the statement of this theorem. You may change the proof."
            )
        else:
            specs = []

        specs.append(f"theorem {theorem_name}")
        indent = " " * LEAN_CODE_INDENT * 2
        specs.append(indent + "{mem : F → F}")
        specs.append(indent + "(κ : ℕ)")
        if arg_defs:
            specs.append(indent + " ".join(arg_defs))
        if arg_names:
            specs.append(indent + f"(h_auto : {auto_spec_name} mem κ {arg_names}) :")
        else:
            specs.append(indent + f"(h_auto : {auto_spec_name} mem κ) :")
        indent = " " * LEAN_CODE_INDENT
        if arg_names:
            specs.append(indent + f"{user_spec_name} mem κ {arg_names} :=")
        else:
            specs.append(indent + f"{user_spec_name} mem κ :=")

        if not with_proof:
            return specs

        return specs + self.mk_lean_function_user_soundness_proof(func)

    def mk_lean_function_user_soundness_proof(self, func: LeanFunctionInfo) -> List[str]:
        return [
            "begin",
            " " * LEAN_CODE_INDENT + "exact h_auto" if not func.is_recursive else "trivial",
            "end",
        ]

    def make_lean_func_prelude(self, func: LeanFunctionInfo) -> str:
        return "\n".join(
            [
                "/-",
                f"-- Function: {get_name_in_scope(func.func_scope, self.main_scope)}",
                "-/",
                "",
                "/- {} autogenerated specification -/".format(
                    get_name_in_scope(func.func_scope, self.main_scope)
                ),
                "",
                "-- Do not change this definition.",
            ]
        )

    def add_spec_prelude(self):
        """
        Adds the prelude of the specifications (if needed).
        """
        if not self.spec_file_exists:
            # Add the initial comment.
            self.specs = [
                "/-",
                f"  Specifications file for {self.file_names.spec_base_filename}.cairo",
                "",
                "  Do not modify the constant definitions, "
                + "structure definitions, or automatic specifications.",
                "  Do not change the name or arguments of "
                + "the user specifications and soundness theorems.",
                "",
                "  You may freely move the definitions around in the file.",
                "  You may add definitions and theorems wherever you wish in this file.",
                "-/",
            ]
        prelude = [
            ["import " + mk_lean_core_import_path("prelude")],
            [f"namespace {str(self.main_scope)}", ""],
            ["variables {F : Type} [field F] [decidable_eq F] [prelude_hyps F]"],
        ]
        self.specs = insert_lean_prelude(prelude, self.specs)

    def add_const_and_struct_defs(self):
        """
        Adds structure definitions for structures used in the functions.
        Replaces existing definitions (as these are considered automatic).
        """
        self.specs = add_lean_defs_to_file(self.specs, self.lean_info)

    def add_first_func_specs(self, funcs: List[LeanFunctionInfo]):
        """
        Adds the specs of the first function in the list to the lines of the
        spec file. If the auto specs of the function already exist in the file,
        they are replaced. Otherwise, they are inserted before the auto specs
        of the first following function which is found in the file. If auto specs
        of none of the functions in the list are found in the file, the specs
        of the function are appended at the end of the file.
        """
        found = self.find_first_auto_spec_in_existing(funcs)
        had_user_spec = self.has_user_soundness_in_existing(funcs[0])
        # Auto spec must appear before user soundness proof.
        soundness = self.find_user_soundness_in_existing(funcs[0])
        if found is None:
            if soundness is None:
                self.append_specs(funcs[0])
            else:
                self.insert_specs_before(funcs[0], soundness)
        else:
            prelude_start, start, end, func = found
            if func == funcs[0]:
                self.replace_specs(funcs[0], start, end)
            else:
                # Auto spec must appear before user soundness proof.
                start = prelude_start if soundness is None else min(prelude_start, soundness)
                self.insert_specs_before(funcs[0], start)

        if had_user_spec:
            self.fix_existing_user_spec(funcs[0])
        if soundness is not None:
            self.fix_existing_user_soundness(funcs[0])

    def append_specs(self, func: LeanFunctionInfo):
        if not func.is_recursive:
            # append auto spec
            self.append_in_main_namespace(
                [self.make_lean_func_prelude(func), self.mk_lean_function_auto_spec(func), ""]
            )
            # append user spec
            if not self.has_user_spec_in_existing(func):
                self.append_in_main_namespace(self.mk_lean_function_user_spec(func) + [""])
        else:
            # append user spec
            if not self.has_user_spec_in_existing(func):
                self.append_in_main_namespace(self.mk_lean_function_user_spec(func) + [""])
            # append auto spec
            self.append_in_main_namespace(
                [self.make_lean_func_prelude(func), self.mk_lean_function_auto_spec(func), ""]
            )
        # append user soundness
        if not self.has_user_soundness_in_existing(func):
            self.append_in_main_namespace(self.mk_lean_function_user_soundness_theorem(func) + [""])

    def replace_specs(self, func: LeanFunctionInfo, start: int, end: int):
        if not func.is_recursive:
            # Auto spec followed by user spec.
            spec_aux = [self.mk_lean_function_auto_spec(func), ""] + (
                self.mk_lean_function_user_spec(func)
                if not self.has_user_spec_in_existing(func)
                else []
            )
        else:
            # User spec followed by auto spec.
            spec_aux = (
                self.mk_lean_function_user_spec(func)
                if not self.has_user_spec_in_existing(func)
                else []
            ) + [self.mk_lean_function_auto_spec(func), ""]
        self.specs = (
            self.specs[:start]
            + spec_aux
            + (
                self.mk_lean_function_user_soundness_theorem(func) + [""]
                if not self.has_user_soundness_in_existing(func)
                else []
            )
            + self.specs[end:]
        )

    def insert_specs_before(self, func: LeanFunctionInfo, before: int):
        if not func.is_recursive:
            # Auto spec followed by user spec.
            spec_aux = [
                self.make_lean_func_prelude(func),
                self.mk_lean_function_auto_spec(func),
                "",
            ] + (
                self.mk_lean_function_user_spec(func)
                if not self.has_user_spec_in_existing(func)
                else []
            )
        else:
            # User spec followed by auto spec.
            spec_aux = (
                self.mk_lean_function_user_spec(func)
                if not self.has_user_spec_in_existing(func)
                else []
            ) + [self.make_lean_func_prelude(func), self.mk_lean_function_auto_spec(func), ""]
        self.specs = (
            self.specs[:before]
            + spec_aux
            + (
                self.mk_lean_function_user_soundness_theorem(func) + [""]
                if not self.has_user_soundness_in_existing(func)
                else []
            )
            + self.specs[before:]
        )

    def fix_existing_user_spec(self, func: LeanFunctionInfo):
        """
        Modifies the arguments of an existing user specification in case the arguments
        of the existing user specification no longer agree with those of the Cairo function.
        Unless the existing specification is the trivial specification, the existing arguments
        are not removed, but commented out, to help the user update the body of the specification.
        """
        start_and_end = self.find_user_spec_in_existing(func, False)
        if start_and_end is None:
            return
        start_line, end_line = start_and_end
        new_user_spec = self.mk_lean_function_user_spec(func, False)
        if self.specs[start_line].strip() == new_user_spec[0].strip():
            return  # Arguments are unchanged.
        if (
            end_line - start_line == 2
            and self.specs[start_line + 1].split()[0] == new_user_spec[1].split()[0]
        ):
            # This is the trivial specification, can replace.
            self.specs = self.specs[:start_line] + new_user_spec + self.specs[end_line:]
        else:
            self.specs[start_line] = "-- " + self.specs[start_line]
            self.specs = (
                self.specs[:start_line]
                + [new_user_spec[0], "-- ARGS CHANGED, PREVIOUS ARGS:"]
                + self.specs[start_line:]
            )

    def fix_existing_user_soundness(self, func: LeanFunctionInfo):
        """
        Modifies the arguments of an existing user soundness theorem in case the arguments
        of the existing user soundness theorem no longer agree with those of the Cairo function.
        Unless the existing theorem is trivial, the existing arguments
        are not removed, but commented out, to help the user update the proof.
        """
        start_line = self.find_user_soundness_in_existing(func, False)
        if start_line is None:
            return

        new_statement = self.mk_lean_function_user_soundness_theorem(func, False, False)
        first_diff = 0

        for first_diff in range(0, len(new_statement)):
            if len(self.specs) <= start_line + first_diff:
                # Only a prefix of the soundness theorem was found. Replace it.
                self.specs = self.specs[:start_line] + self.mk_lean_function_user_soundness_theorem(
                    func, False, True
                )
                return
            if new_statement[first_diff].strip() != self.specs[start_line + first_diff].strip():
                break
        else:
            return  # No difference found.

        for end_statement in range(start_line + first_diff, len(self.specs)):
            if ":=" in self.specs[end_statement]:
                end_statement += 1
                break

        # Is the current proof the trivial proof?
        trivial_proof = self.mk_lean_function_user_soundness_proof(func)
        for proof_line in range(0, len(trivial_proof)):
            if (
                len(self.specs) <= end_statement + proof_line
                or self.specs[end_statement + proof_line].strip()
                != trivial_proof[proof_line].strip()
            ):
                # Not a trivial proof, comment out the lines which differ.
                for line in range(start_line + first_diff, end_statement):
                    self.specs[line] = "-- " + self.specs[line]
                self.specs = (
                    self.specs[: start_line + first_diff]
                    + new_statement[first_diff:]
                    + ["-- STATEMENT CHANGED, PREVIOUS STATEMENT:"]
                    + self.specs[start_line + first_diff :]
                )
                return

        self.specs = (
            self.specs[: start_line + first_diff]
            + new_statement[first_diff:]
            + self.specs[end_statement:]
        )

    def add_out_of_main_scope_imports(self):
        import_names = self.lean_info.imported_scopes
        self.specs = insert_additional_imports(
            [f"import {mk_lean_spec_import_path(name)}" for name in import_names], self.specs
        )
        self.specs = insert_open_import_namespaces([str(name) for name in import_names], self.specs)

    def close_main_namespace(self):
        close_line = f"end {str(self.main_scope)}"
        if close_line not in self.specs:
            self.specs += ["", close_line]

    def find_main_namespace_end(self) -> Optional[int]:
        close_line = f"end {str(self.main_scope)}"
        return self.specs.index(close_line) if close_line in self.specs else None

    def append_in_main_namespace(self, lines: List[str]):
        before = self.find_main_namespace_end()
        if before is None:
            self.specs += lines
        else:
            self.specs = self.specs[:before] + lines + self.specs[before:]

    def mk_lean_spec_file(self):
        """
        Generates the specification file for the Cairo functions whose information
        is stored on this object. If a specification file already exists for
        the base file name, the generated specifications are merged with the existing
        specifications: the automatic specifications are replaced while the user
        specification (and soundness) are added only if they do not already exist
        in the file.
        """
        self.get_existing_specs()
        self.add_spec_prelude()
        self.add_const_and_struct_defs()

        funcs = self.lean_info.main_scope_funcs
        for first in range(0, len(funcs)):
            self.add_first_func_specs(funcs[first:])

        self.add_out_of_main_scope_imports()
        self.close_main_namespace()

        with open(self.file_names.spec_filename, "w") as out:
            for line in self.specs:
                print(line, file=out)
