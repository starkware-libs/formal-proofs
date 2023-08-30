Verification
============

This folder is a Lean 4 project for StarkWare verification. You should have Lean 4 and the VS Code
extension [installed](https://leanprover-community.github.io/get_started.html). If you open the
whole the `formal-proofs` repository in VS Code, choose `Add Folder to Workspace` from the `File`
menu and add this folder, so that Lean will know where to look for the configuration files.

After fetching the repository, type
```
lake exe cache get
```
in this folder to get the precompiled Mathlib files.

Use
```
lake build
```
to compile all the files listed in `Verification.lean`.