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

The publication sequence is local review, private Linux CI, then public Linux
CI. Status files must record completed results and exact commits. A failed or
pending run must never be reported as passing. Historical development audits
are kept under `verification/original-audit/` and retain their original scope.
