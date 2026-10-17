# Complete proof without Comparator

The Lean proof and FCSolution bridge are byte-identical to the canonical project.
Comparator-only reference, audit and tool files are omitted.

```sh
lake exe cache get
lake build
```

Lean 4.34.1 and the Mathlib manifest are pinned. See the repository README
for the exact mathematical scope, including the smooth-uniqueness limitation.
