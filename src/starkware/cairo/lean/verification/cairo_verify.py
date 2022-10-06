"""
This file provides a convenient way to run the compiler and experiment with it.

It assumes the files are in the same directory.
"""
import argparse
import os
import subprocess
import sys
from datetime import datetime
from typing import List, Optional

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../../../.."))
sys.path.insert(0, os.path.dirname(__file__))

from starkware.cairo.lang.cairo_constants import DEFAULT_PRIME
from starkware.cairo.lang.compiler.cairo_compile import compile_cairo_ex, get_codes
from starkware.cairo.lang.compiler.constants import LIBS_DIR_ENVVAR
from starkware.cairo.lang.compiler.error_handling import LocationError
from starkware.cairo.lang.compiler.scoped_name import ScopedName
from starkware.cairo.lean.verification.expr_to_lean import LeanExprSimplifier
from starkware.cairo.lean.verification.generate_block_info import analyze_blocks
from starkware.cairo.lean.verification.generate_soundness import (
    mk_lean_code_file,
    mk_lean_soundness,
)
from starkware.cairo.lean.verification.generate_spec import LeanSpecGenerator
from starkware.cairo.lean.verification.lean_assembly_info import LeanAssemblyInfo
from starkware.cairo.lean.verification.lean_file_names import LeanFileNames
from starkware.cairo.lean.verification.lean_processed_info import LeanProgramInfo
from starkware.cairo.lean.verification.lean_raw_info import LeanRawProgramInfo


def verify_file(
    basename: str,
    func_select: Optional[List[str]],
    soundness_select: Optional[List[str]] = None,
) -> List[str]:
    """
    Generates the Lean verification code for the functions in a single file, whose name is
    given as a path relative to the current working directory. If a list of soundness selection
    strings is provided (and is not empty) only the automatic soundness files for functions
    whose name contains one of the given strings will be generated.
    """
    file_names = LeanFileNames(basename=basename)
    codes = get_codes([file_names.cairo_filename])
    cairo_path = list(filter(None, os.getenv(LIBS_DIR_ENVVAR, "").split(":")))
    main_scope = ScopedName(tuple(file_names.get_lean_path()))
    _, preprocessed_program = compile_cairo_ex(
        code=codes,
        prime=DEFAULT_PRIME,
        cairo_path=cairo_path,
        debug_info=False,
        main_scope=main_scope,
        auxiliary_info_cls=LeanRawProgramInfo,
    )
    if not isinstance(preprocessed_program.auxiliary_info, LeanRawProgramInfo):
        return []

    lean_assembly_info = LeanAssemblyInfo()
    lean_assembly_info.build_from_preprocessed(preprocessed_program)
    lean_assembly_info.close_pc_lookup()

    lean_info = LeanProgramInfo(
        prime=preprocessed_program.auxiliary_info.prime,
        main_scope=main_scope,
        preprocessor=preprocessed_program.auxiliary_info.preprocessor,
        identifiers=preprocessed_program.identifiers,
        reference_manager=preprocessed_program.reference_manager,
        program_info=preprocessed_program.auxiliary_info,
        func_select=func_select,
    )

    # Analyze block structure of all functions for spec generator and soundness proofs.
    analyze_blocks(lean_info)

    # Generate the specifications and prelude files.
    gen_spec_for_scope(lean_info=lean_info, file_names=file_names)

    mk_lean_code_file(file_names=file_names, lean_info=lean_info, assembly_info=lean_assembly_info)

    soundness_files = mk_lean_soundness(
        file_names=file_names,
        soundness_select=soundness_select,
        lean_info=lean_info,
        assembly_info=lean_assembly_info,
    )

    # Generate the spec of the imported files.

    to_import = set(lean_info.imported_scopes)
    spec_generated = set([main_scope])
    while len(to_import) > 0:
        for imported_scope in set(to_import):
            # Set the file and main scope to the imported scope.
            import_basename = file_names.get_cwd_path_of_scoped_name(imported_scope)
            lean_info.reset_main_scope(main_scope=imported_scope)

            print(
                "Generating the specifications for {} (file {}).".format(
                    str(imported_scope), import_basename
                )
            )

            gen_spec_for_scope(
                lean_info=lean_info, file_names=LeanFileNames(basename=import_basename)
            )
            spec_generated.add(imported_scope)
            to_import = to_import.union(lean_info.imported_scopes)

        to_import = to_import - spec_generated

    return soundness_files


def gen_spec_for_scope(lean_info: LeanProgramInfo, file_names: LeanFileNames):
    """
    Generates the spec file for those functions and definitions which appear in
    Lean information object and are in the indicated file.
    """
    file_names.make_verification_directory()
    specGenerator = LeanSpecGenerator(
        file_names=file_names,
        lean_info=lean_info,
        simplifier=LeanExprSimplifier(lean_info.preprocessor),
    )
    specGenerator.mk_lean_spec_file()


def run_lean_make(soundness_files: List[str], out_name: str, lean_make_timeout: int):

    lean_make_out = open(out_name, "w")

    for filename in soundness_files:
        start_time = datetime.now()
        try:
            print("lean --make {}".format(filename))
            print("lean --make {} at {}".format(filename, start_time), file=lean_make_out)
            subprocess.run(
                ["lean", "--make", filename],
                stderr=subprocess.STDOUT,
                stdout=lean_make_out,
                timeout=lean_make_timeout if lean_make_timeout else None,
            )
            end_time = datetime.now()
            print(
                "completed at {} (after {})".format(end_time, end_time - start_time),
                file=lean_make_out,
            )
        except subprocess.TimeoutExpired:
            end_time = datetime.now()
            print(
                "lean --make {}: terminated at {} (after {}) on timeout ({} sec.)".format(
                    filename, end_time, end_time - start_time, lean_make_timeout
                ),
                file=lean_make_out,
            )
        except:
            end_time = datetime.now()
            print(
                "lean --make {}: failed with exception at {} (after {})".format(
                    filename, end_time, end_time - start_time
                ),
                file=lean_make_out,
            )

    lean_make_out.close()


def main():

    parser = argparse.ArgumentParser(description="A tool to compile Cairo code.")
    parser.add_argument(
        "basename", metavar="base name", type=str, nargs="?", default="test", help="Base name"
    )
    parser.add_argument("--compile_lean", action="store_true")
    parser.add_argument(
        "--lean_timeout",
        metavar="lean timeout",
        type=int,
        nargs="?",
        default=None,
        help="Lean make timeout (for a single proof)",
    )
    parser.add_argument(
        "--soundness",
        metavar="soundness",
        type=str,
        nargs="*",
    )

    args = parser.parse_args()
    basename = args.basename
    compile_lean = args.compile_lean
    lean_make_timeout = args.lean_timeout
    soundness_select = args.soundness

    erred: bool = False

    try:
        soundness_files = verify_file(
            basename=basename,
            func_select=None,
            soundness_select=soundness_select,
        )

        # Optionally compile the Lean files.

        if compile_lean and soundness_files:
            file_names = LeanFileNames(basename=basename)
            lean_make_out_name = (
                file_names.verification_directory_path
                + "/"
                + "lean_make_{}_{}.txt".format(basename, datetime.now().strftime("%Y%b%d-%H:%M:%S"))
            )
            run_lean_make(soundness_files, lean_make_out_name, lean_make_timeout)

    except LocationError as err:
        print(err, file=sys.stderr)
        erred = True

    return 1 if erred else 0


if __name__ == "__main__":
    sys.exit(main())
