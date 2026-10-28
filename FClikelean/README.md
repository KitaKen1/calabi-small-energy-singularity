# Finite-time singularities of Calabi flow

[`CalabiSmallEnergy.lean`](CalabiSmallEnergy.lean) contains two theorem statements:

1. `calabi_flow`: OpenAI’s counterexample on `CP¹⁰` [OAI26].
2. `calabi_flow.variants.dimension_seven`: the present seven-dimensional variant [Ki26].

Both use `answer(False) ↔ CalabiFlowConjecture n`. The predicate asks whether
every smooth Calabi flow in the Fubini–Study class of `CPⁿ` extends past each
finite endpoint, agreeing throughout its original interval. Dimension means
complex dimension. The file concerns these projective counterexamples; it does
not formalize the original conjecture on arbitrary Kähler manifolds.

The flow definition follows equation (1.1) of [OAI26] explicitly: an initial
form `ω₀`, `ωₜ t = ω₀ + ddbar (φ t)`, the condition `φ 0 = 0`, positivity,
and `∂ₜφ = scal (ωₜ t) - S_avg`. Here `S_avg = n * (n + 1)` in the fixed class.
`Form` stores local coefficients; `IsKahlerForm` requires a compatible smooth
positive form `fubiniStudy n + ddbar f`. The spatial operator `ddbar` uses the
actual complex Hessian `levi`. All definitions stay in one file, with one
`public import FormalConjecturesUtil`.

The two FC theorem bodies are intentional `sorry` placeholders. The CP10 proof
is cited from OpenAI and is not included in this repository’s verification.
The stronger CP7 small-energy theorem is proved in
[`lean/FCSolution.lean`](../lean/FCSolution.lean).
[`check-fc-draft.py`](../lean/comparator/check-fc-draft.py) proves in the Lean
kernel that the independent small-energy reference implies the CP7 variant,
and consequently `¬ ∀ n, CalabiFlowConjecture n`. It also checks that the
initial-form and fixed-Fubini–Study descriptions agree under the change
`ω₀ = ω_FS + ddbar (F 0)`, `φ t = F t - F 0`. See the
[correspondence notes](../lean/comparator/TARGET-CORRESPONDENCE.md).

The standalone entry point imports the needed Mathlib modules and the unchanged
official FC category/AMS and `answer` implementations. The user-requested
`answer(False)` format uses the official implementation from before FC’s
2026-10-15 migration, pinned separately in `vendor-lock.json`. The full upstream
FC linter suite is not part of this local check.

```sh
lake build
```
