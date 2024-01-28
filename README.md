Cairo verification using Lean
=============================

Contents
--------

This repository contains a number of related items.

- The folder [src/starkware/cairo/lean/semantics](src/starkware/cairo/lean/semantics)
  contains a Lean formalization of the semantics of Cairo, as described by the
  [README](src/starkware/cairo/lean/semantics/README.md) file in that directory.

- The folder [src/starkware/cairo/lean/verification](src/starkware/cairo/lean/verification)
  contains a Python application, `cairo_verify.py`, that extends the ordinary Cairo compiler to
  make it *proof producing*. The verifier generates a Lean description of the compiled code,
  Hoare-style specifications of the source code, and proofs that the compiled code meets the
  specifications relative to the execution semantics above. Users can add their own
  specifications, prove that they follow from the specifications, and then use Lean to verify
  that the compiled code satisfies their specifications as well.

- The folder [src/starkware/cairo/common](src/starkware/cairo/common)
  contains formal specifications of core components of the Cairo's
  [common library](https://docs.cairo-lang.org/reference/common_library.html),
  including the mathematics library and the `squash_dict()` procedure.
  It also contains proofs that these specifications are correct relative to the
  specifications produced by the verifier.

- The folder [src/starkware/cairo/common/cairo_secp](src/starkware/cairo/common/cairo_secp)
  contains a formal specification of Cairo code used to check cryptographic signatures
  using the Secp256k1 elliptic curve,
  as well as proofs that these specifications are correct relative to the specifications
  produced by the verifier. See in particular `spec_recover_public_key` in
  [signature_spec.lean](src/starkware/cairo/common/cairo_secp/signature_spec.lean).
  You can find the corresponding Cairo code in the
  [cairo-lang repository](https://github.com/starkware-libs/cairo-lang/tree/master/src/starkware/cairo/common/cairo_secp).
  We have not yet verified the associativity of elliptic curve addition in Lean, so that has to be
  trusted.

- The folder [src/starkware/cairo/common/cairo_secp/verification](src/starkware/cairo/common/cairo_secp/verification)
  contains [signature_recover_public_key.cairo](src/starkware/cairo/common/cairo_secp/verification/signature_recover_public_key.cairo),
  whose only purpose is to send `recover_public_key` and the code it depends on to the verifier.
  The directory also contains all the Lean files that are generated automatically by the verifier.
  Using Lean to check these files, which import the specifications in the previous item, results in
  a complete verification that the machine code for `recover_public_key` meets its high-level
  specification.

- The folder [src/starkware/cairo/common/secp256r1](src/starkware/cairo/common/secp256r1)
  contains a formal specification of operations for the Secp256r1 elliptic curve,
  as well as proofs that these specifications are correct relative to the specifications
  produced by the verifier.

- The folder [lean4](lean4) contains a port of the Cairo semantics to Lean 4. Follow the
  instructions in the [README](lean4/README.md) file there to use them. Our verification
  infrastructure for Lean 4 is still a work in progress and these files may change.

Publications
------------

- Our verification of the algebraic encoding of Cairo execution traces is described in the paper
  [A verified algebraic representation of Cairo program execution](https://dl.acm.org/doi/10.1145/3497775.3503675).

- Our verification tools and our verification of Cairo code used to validate cryptographic signatures
  are described in the paper [A proof-producing compiler for blockchain applications](https://doi.org/10.4230/LIPIcs.ITP.2023.7).


Setup
-----

To use Lean to verify the correctness of proofs (either those generated automatically by the
verifier or those written manually for the AIR encoding or secp signatures), you need to have
Lean 3 installed:

>  https://leanprover-community.github.io/get_started.html

If you fetched this repository using `git clone` rather than  `leanproject get`, use
```
  leanproject get-mathlib-cache
```
to fetch a compiled version of the math library.

To run the Cairo verifier, you need to have the Cairo compiler installed:

>  https://www.cairo-lang.org/docs/quickstart.html

The verifier here is designed to work with version `v.0.10.1`, so you should use
```
  pip install cairo-lang==0.10.1
```
to make sure you are installing the right version. Alternatively, you can download a zip file from
the [cairo-lang](https://github.com/starkware-libs/cairo-lang/releases/tag/v0.10.1) repository
and install from that:
```
  pip install cairo-lang-0.10.1.zip
```


Usage
-----

To check the correctness of the algebraic encoding of the Cairo execution semantics, run
```
  lean --make *.lean
```
in [src/starkware/cairo/lean/semantics/air_encoding](src/starkware/cairo/lean/semantics/air_encoding).

To verify the correctness of core functions in the common library relative to the
specifications produced by the verifier, run
```
  lean --make *.lean
```
in [src/starkware/cairo/common](src/starkware/cairo/common).

To verify the correctness of the Secp256k1 signature validation procedures relative
to the specifications produced by the verifier, run
```
  lean --make signature_spec.lean
```
in [src/starkware/cairo/common/cairo_secp](src/starkware/cairo/common/cairo_secp). For a complete
verification of the correctness of the compiled code with respect to the CPU execution semantics,
run
```
  lean --make *.lean
```
in [src/starkware/cairo/common/cairo_secp/verification/verification](src/starkware/cairo/common/cairo_secp/verification/verification). You will get warnings that the file `elliptic_curves.lean`
uses `sorry`. That refers to the associativity of the elliptic curve law, which we assert without
proof.

To verify the correctness of the Cairo Secp256r1 operations relative to the specifications produced by the verifier, run
```
  lean --make ec_spec.lean
```
in [src/starkware/cairo/common/secp256r1](src/starkware/cairo/common/secp256r1).

To try out the verifier, follow the instructions in the
[README](src/starkware/cairo/lean/verification/examples/math/README.md) file in
[src/starkware/cairo/lean/verification/examples/math](src/starkware/cairo/lean/verification/examples/math).

