Cairo semantics in Lean
=======================

This folder contains a Lean formalization of the semantics of Cairo.

- The file [cpu.lean](src/starkware/cairo/lean/semantics/cpu.lean) defines the CPU execution
  semantics.

- The folder [air_encoding](src/starkware/cairo/lean/air_encoding) contains a formal proof of the
  correctness of an algebraic encoding of this execution model that is used by STARK proofs.
  This is described in the paper
  [A verified algebraic representation of Cairo program execution](https://dl.acm.org/doi/10.1145/3497775.3503675).

- The folder [soundness](src/starkware/cairo/lean/air_encoding) contains a Lean representation of
  Cairo's assembly language, Hoare semantics, and tactics that step through the effects of
  executing each instruction. These are all used by the Lean Cairo verifier.

- The file [util.lean](src/starkware/cairo/lean/semantics/util.lean) contains generally useful
  definitions and theorems, some of which should eventually be moved to Lean's `mathlib`.

The Lean files in this folder are released under an Apache license.
