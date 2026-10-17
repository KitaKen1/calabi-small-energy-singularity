# Canonical Lean project

Lean 4.34.1 and the Mathlib commit in `lake-manifest.json` are fixed.

```sh
lake exe cache get
lake build
lake build Calabi FCAudit
lake env lean FCAudit.lean
```

The default target is `FCSolution`, which imports the completed `Calabi.Main`.
`Calabi.lean` also imports `Calabi.Main`. `Challenge` imports only fixed
Mathlib-based definitions and is never imported by the solution.

See [the verification guide](comparator/README.md),
[the statement correspondence](comparator/TARGET-CORRESPONDENCE.md), and
[the original proof guide](PROOF-GUIDE.md).
