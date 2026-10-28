# Verification evidence

`local/` contains preflight compilation, statement review, axiom and replay
records for the publication candidate. `original-audit/` contains historical
development records for the original 448-module proof closure; its digest is
checked against the current source. `numerics/` retains the original rational
certificate checking material. Historical records keep their original scope.

Private and public CI results are recorded separately, including repository,
tested commit, run ID, attempt, visibility and individual job conclusions.
Only completed successful runs may be marked `PASS`.

Logs and artifacts expire on GitHub after 90 days. Archived runs include the
original artifact ZIPs, complete job logs, API metadata and SHA-256 checksums.
Source and workflow hashes bind those receipts to the tested configuration.

The original manuscript files `check_identities.py`, `identity-checks.json`,
`manuscript-checks.json` and `profile7/` are retained byte-for-byte at their
original paths. They are historical numerical/manuscript records. The current
Lean results are in `local/`, the private/public CI records and the CI archives.

Current stage: **Lean proof published without CI on 28 October 2026**, at the
user’s explicit request. Automatic CI is disabled; the workflow supports manual
dispatch only. A historical private repository and CI run were started prematurely;
that run was cancelled and is not a successful private-CI receipt. Public CI has
not run for this release.

The current FC file contains OpenAI’s CP10 counterexample `calabi_flow` and
the CP7 variant `calabi_flow.variants.dimension_seven`. The
[current receipt](local/fc-original-equation-20261020/verification.json) checks compilation
of both, both directions of the change from the fixed-Fubini–Study potential
to the initial form and zero-initialized potential, and a Lean kernel proof
from the independent small-energy reference to the CP7 variant. It also proves the projective corollary
`¬ ∀ n, CalabiFlowConjecture n`. The main CP10 theorem is a statement-only check;
the cited OpenAI proof is not certified here. Earlier receipts preserve their
original target types and hashes, including former general-conjecture targets.

Both current FC statements use `answer(False) ↔ P`. The official answer
implementation is vendored unchanged at the separate pre-migration commit in
`FClikelean/vendor-lock.json`.

The FC-style file imports `FormalConjecturesUtil` once. Its standalone entry
point imports Mathlib and the official category/AMS implementation, vendored
unchanged at the commit in `FClikelean/vendor-lock.json`. This local check does
not run the complete upstream Formal Conjectures linter suite.
