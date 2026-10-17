# Standalone Formal Conjectures style draft

`CalabiSmallEnergy.lean` fixes the geometric definitions and states the primary
small-energy singularity target and its energy specialization. The only holes
are the two intended theorem proofs. The mathematical definitions and theorem
bodies are identical to the independently checked Comparator reference.

```sh
lake exe cache get
lake build
```

This directory is a proposed statement-only draft. It is not an accepted or
submitted upstream Formal Conjectures entry, and it does not claim compatibility
with an untested FC checkout. It uses the same pinned Lean 4.34.1 and Mathlib
as the complete proof. The completed proofs are in `../lean/FCSolution.lean`.
See `../lean/comparator/TARGET-CORRESPONDENCE.md` for the maximal-flow limitation.
