# Cairo Verification

This repository contains formal verification of various aspects of the Cairo programming
language using the Lean programming language and proof assistant.

## Contents

The folder [Verification/Semantics](Verification/Semantics) contains a specification of the Cairo
virtual machine semantics and a proof of the correctness of the Cairo STARK encoding.

- The file [Cpu.lean](Verification/Semantics/Cpu.lean) contains a specification of the execution
semantics of the Cairo CPU, used to prove soundness of Cairo programs and the correctness of the
STARK encoding.

- The file [Vm.lean](Verification/Semantics/Vm.lean) contains a slightly abstracted semantics of the
Cairo virtual machine, used to prove completeness of Cairo programs.

- The [AirEncoding](Verification/Semantics/AirEncoding) folder contains a proof of the correctness
of the algebraic encoding of execution traces of Cairo programs that are used to generate STARK
certificates.

- The [Soundness](Verification/Semantics/Soundness) folder contains infrastructure used to prove the
soundness of Cairo programs and library functions.

- The [Completeness](Verification/Semantics/Completeness) folder contains infrastructure used to
prove the soundness of Cairo programs and library functions.

The folder [Verification/Libfuncs](Verification/Libfuncs) contains verifications of the
soundness and completeness of a number of Cairo library functions, also known as *libfuncs*.

The [lean3](lean3) folder contains older Lean 3 verifications of parts of the CairoZero library,
including:

- basic mathematical calculations
- operations on the secp256k1 and  secp256r1 elliptic curves
- digital signature validation
- procedures for simulating dictionary access in a read-only enviroment.

Details can be found in the file [README.md](lean3/README.md) in that folder.


## Publications

- Our verification of the algebraic encoding of Cairo execution traces is described in the paper
  [A verified algebraic representation of Cairo program execution](https://dl.acm.org/doi/10.1145/3497775.3503675).

- Our verification tools and our verification of CairoZero code used for elliptic curve operations
  and to validate cryptographic signatures are described in the paper
  [A proof-producing compiler for blockchain applications](https://doi.org/10.4230/LIPIcs.ITP.2023.7).


## Build

The main folder is a Lean 4 project. You should have Lean 4 and the VS Code
extension [installed](https://docs.lean-lang.org/lean4/doc/quickstart.html).

Once you have Lean 4 installed, you can fetch this repository by choosing `Open Project`
on the Lean VS Code menu or in the usual way with `git clone`. In the latter case, you
should run

```
lake exe cache get
```
in this folder to get the precompiled Mathlib files.

Use
```
lake build
```
to compile all the files listed above `Verification.lean`. One completeness proof in the
`Libfuncs` folder is commented out because it is slow to build and requires a lot of memory;
the remaining files take only a few minutes to compile.