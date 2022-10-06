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
  Hoare specifications of the source code, and proofs that the compiled code meets the Hoare
  specifications relative to the execution semantics above. Users can add their own
  specifications, prove that they follow from the Hoare specifications, and then use Lean to verify
  that the compiled code satisfies their specifications as well.

- The folder [src/starkware/cairo/common/cairo_secp](src/starkware/cairo/common/cairo_secp)
  contains a formal specification of Cairo code used to check cryptographic signatures,
  as well as proofs that these specifications are correct relative to the Hoare descriptions
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

Setup
-----

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

To use Lean to verify the correctness of proofs (either those generated automatically by the
verifier or those written manually for the AIR encoding or secp signatures), you need to have
Lean 3 installed:

>  https://leanprover-community.github.io/get_started.html

If you fetched this repository using `git clone` rather than  `leanproject get`, use
```
  leanproject get-mathlib-cache
```
to fetch a compiled version of the math library.


Usage
-----

To check the correctness of the algebraic encoding of the Cairo execution semantics, run
```
  lean --make *.lean
```
in [src/starkware/cairo/lean/semantics/air_encoding](src/starkware/cairo/lean/semantics/air_encoding).

To try out the verifier on an example, follow the instructions in the
[README](src/starkware/cairo/lean/verification/examples/math/README.md) file
in [src/starkware/cairo/lean/verification/examples/math](src/starkware/cairo/lean/verification/examples/math).

To verify the correctness of `recover_public_key` relative to the Hoare specifications, run
```
  lean --make signature_spec.lean
```
in [src/starkware/cairo/common/cairo_secp](src/starkware/cairo/common/cairo_secp). For a complete
verification of the correctness of the compiled code with respect to the CPU execution semantics,
run
```
  lean --make *.lean
```
in [src/starkware/cairo/common/cairo_secp/verification/verification](src/starkware/cairo/common/cairo_secp/verification/verification). You will get warnings that the file `elliptic_curves.lean` uses `sorry`.
That refers to the associativity of the elliptic curve law, which we assert without proof.

You can use the verifier to (re)generate the Lean correctness proofs, and also to (re)generate
the Hoare specifications in the `*_spec.lean` files that are alongside the relevant Cairo files,
without changing the parts of the specification files that we have written by hand. To do this,
activate the Python environment with version `v.0.10.1` of the compiler and execute the following
in [src/starkware/cairo/common/cairo_secp/verification](src/starkware/cairo/common/cairo_secp/verification):

```
  python ../../../lean/verification/cairo_verify.py signature_recover_public_key.cairo
```
This runs the verifier on
[signature_recover_public_key.cairo](src/starkware/cairo/common/cairo_secp/verification/signature_recover_public_key.cairo).
The Cairo compiler, and hence the verifier, finds the required imports in the `cairo-lang` package.
The generated files should be identical to the ones that were originally in this repository. You can
then run
```
  lean --make verification/*.lean
```
in the same directory to check the results with Lean.



