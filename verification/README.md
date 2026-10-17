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
