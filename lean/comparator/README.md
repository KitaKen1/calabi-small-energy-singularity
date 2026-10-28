# Reproducible theorem verification

From the repository root run:

```sh
python3 lean/comparator/check-inputs.py
```

This verifies fixed input hashes, unchanged original proof sources, both proof
copies, the standalone draft and the original 448-module closure digest.
`FCTargetDefinitions.lean` imports only Mathlib; `Challenge.lean` contains the
two intended statement holes. `FCSolution` imports the actual completed proof
and no reference module. The two environments are compared independently.

The single-file FC draft has two statements: OpenAI’s CP10 counterexample
`calabi_flow`, and the CP7 variant `calabi_flow.variants.dimension_seven`.
The independent reference and solution retain the two stronger small-energy
declarations. To check the CP7 connection, run from `lean/`:

```sh
lake env python3 comparator/check-fc-draft.py --receipt-dir ../fc-draft-receipt
```

This compiles both statements in a fresh draft environment. In the Lean kernel,
it proves that the dimension-seven flow predicate agrees with the independent
coordinate geometry after the initial-form normalization, that `answer(False) ↔ P` is equivalent to `¬ P`, and that the independent
main reference implies the CP7 variant and the projective corollary
`¬ ∀ n, CalabiFlowConjecture n`. A smooth extension would have a continuous time
derivative at the origin; the Calabi equation and positive scalar blow-up
contradict this. The proof uses neither draft placeholder and is audited against
the same three permitted axioms. The instantiated proof and source hashes are
saved with the receipt.

The normalization writes `ω₀ = ω_FS + ddbar (F 0)` and
`φ t = F t - F 0`, so the initial condition is explicitly zero. The proof
checks both directions of this change, including linearity of the Hessian,
preservation of curvature and transfer of extensions. These coordinate
lemmas do not certify the complete intrinsic differential geometry of the
original equation on arbitrary Kähler manifolds.

The main CP10 proof is explicitly excluded: the repository records the cited
OpenAI statement and does not certify its proof. The template filename retains
`equivalence` for compatibility; only the flow predicates are equivalent, while
the small-energy connection is an implication.

The workflow builds the trusted reference before restoring solution products,
then uses the unmodified pinned Comparator to compare dependent definitions,
audit allowed axioms and replay the exported proof in the builtin kernel.
A separate job runs `leanchecker --fresh FCSolution` on the complete environment.
Six principal declarations also receive explicit transitive axiom audits.

All components use Lean 4.34.1. Comparator and Lean4export are pinned to the last
4.34 source revisions; their only working-tree edit is `lean-toolchain`, changing
4.34.0 to 4.34.1. Landrun is pinned separately. No checker Lean code is patched.
The Linux job uses a non-root user, Landrun, `NoNewPrivileges=yes` and the
AF_UNIX address-family restriction recommended by upstream Comparator.

On Linux, set `COMPARATOR_TOOLS` to a fresh directory, run `install-tools.sh`,
and run `run-check.sh` on an appropriately prepared systemd host.
The supplied workflow prepares a disposable GitHub-hosted runner.

The public `Lean proof` workflow builds the completed proof and checks its
allowed axioms. It does not run Comparator or fresh environment replay. Both
workflows accept manual dispatch only. Status files must record completed
results and exact commits; failed or pending runs must not be reported as
passing. Historical development audits are kept under
`verification/original-audit/` and retain their original scope.

The draft uses the standard `FormalConjecturesUtil` import. The standalone
build compiles a local entry point and the two unchanged official FC attribute
modules from `FClikelean/vendor/` before compiling the mathematical statement.
Their sources and commit are pinned in `FClikelean/vendor-lock.json`; input
checks distinguish those upstream sources from the local entry point.
The complete upstream FC linter suite is not run by this checker.
