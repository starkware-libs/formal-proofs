import dataclasses
import os
from typing import List

from starkware.cairo.lang.compiler.scoped_name import ScopedName

LEAN_VERIFICATION_DIRECTORY_NAME = "verification"
LEAN_SPEC_FILE_SUFFIX = "_spec"


@dataclasses.dataclass
class LeanFileNames:
    """
    This class provides the paths and file names for the different Cairo files
    that need to be read and the Lean files that need to be read and generated.
    All paths are relative to the current working directory.
    The class is constructed based on the given base name, which is the path
    to the Cairo file to be verified (including the Cairo file name, either with
    or without the '.cairo' suffix).
    """

    basename: str
    base_directory_path: str = ""
    verification_directory_path: str = ""
    base_file_name: str = ""

    def __post_init__(self):
        self.basename = self.basename.strip()
        if self.basename.lower().endswith(".cairo"):
            self.basename = self.basename[: -len(".cairo")]
        self.base_directory_path, self.base_file_name = os.path.split(self.basename)
        self.verification_directory_path = os.path.join(
            self.base_directory_path, LEAN_VERIFICATION_DIRECTORY_NAME
        )

    @property
    def cairo_filename(self) -> str:
        return os.path.join(self.base_directory_path, self.base_file_name + ".cairo")

    @property
    def code_base_filename(self) -> str:
        return self.base_file_name + "_code"

    @property
    def code_filename(self) -> str:
        return os.path.join(self.verification_directory_path, self.code_base_filename + ".lean")

    @property
    def prelude_base_filename(self) -> str:
        return self.base_file_name + "_prelude"

    @property
    def prelude_filename(self) -> str:
        return os.path.join(self.verification_directory_path, self.prelude_base_filename + ".lean")

    @property
    def spec_base_filename(self) -> str:
        return self.base_file_name + LEAN_SPEC_FILE_SUFFIX

    @property
    def spec_filename(self) -> str:
        return os.path.join(self.base_directory_path, self.spec_base_filename + ".lean")

    def soundness_base_filename(self, funcname: str) -> str:
        return mk_lean_soundness_filename(self.base_file_name, funcname)

    def soundness_filename(self, funcname: str) -> str:
        return os.path.join(
            self.verification_directory_path, self.soundness_base_filename(funcname) + ".lean"
        )

    def make_verification_directory(self):
        os.makedirs(self.verification_directory_path, exist_ok=True)

    def get_lean_path(self) -> List[str]:
        """
        Returns the normalized path of the base Cairo file (including the file itself) relative
        to the Lean root, which is the lowest 'src' directory above the cairo file.
        The file suffix is not included (but the file name is).
        """
        abs_path = os.path.abspath(self.basename).split("/")

        if not "src" in abs_path:
            raise Exception("File not inside a Lean project (no 'src' directory in path).")

        return abs_path[len(abs_path) - list(reversed(abs_path)).index("src") :]

    def get_cwd_path_of_scoped_name(self, scoped_name: ScopedName) -> str:
        """
        Returns the path, as a string, relative to the current working directory
        of the file with the given scoped name. We use the base name as a reference
        to determine the absolute path associated with the scoped name.
        """
        base_path = os.path.abspath(self.basename).split("/")

        if not "src" in base_path:
            raise Exception("File not inside a Lean project (no 'src' directory in path).")

        lean_prefix_path = base_path[: len(base_path) - list(reversed(base_path)).index("src")]

        return os.path.relpath("/".join(lean_prefix_path + list(scoped_name.path)))


def mk_lean_soundness_filename(filename: str, funcname: str):
    return filename + "_" + funcname.rpartition(".")[2] + "_soundness"


def mk_lean_core_import_path(file_name: str):
    """
    Import path in Lean for a Lean file which is in the core verification directory.
    """
    if file_name[0] == ".":
        return file_name
    return "starkware.cairo.lean.semantics.soundness." + file_name


def mk_lean_rel_import_path(import_file: str, from_file: str):
    """
    Returns the path to be used in a Lean import in order to import the import
    file from the other file. The files are assumed to be given as strings
    relative to the current working directory.
    """
    rel_path = os.path.relpath(import_file, os.path.dirname(from_file))
    if rel_path.endswith(".lean"):
        rel_path = rel_path[: -len(".lean")]
    import_path = ".".join(["" if name == ".." else name for name in rel_path.split("/")])
    return "." + import_path


def mk_lean_spec_import_path(scoped_name: ScopedName) -> str:
    """
    Returns the absolute import path for the Lean spec file whose scope is given.
    We assume here that the root of the Cairo scope is the same as the Lean root.
    """
    return str(scoped_name) + LEAN_SPEC_FILE_SUFFIX


def mk_lean_dependency_soundness_import_path(main_scope: ScopedName, dep_scope: ScopedName) -> str:
    return "." + mk_lean_soundness_filename(
        str(main_scope[-1:]),  # Main file name.
        str(dep_scope[-1:]),  # Function name.
    )
