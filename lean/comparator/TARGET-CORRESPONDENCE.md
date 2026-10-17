# Natural-language / Lean correspondence

Reviewed on 17 October 2026 against Theorem 1.1, equations (1.1)-(1.5), on the
first page of the unchanged manuscript. This is a mathematical review, supported
by independently compiled Lean definitions and Comparator. It is not an
automatic proof that prose and formal code have the same meaning.

Primary target: `CalabiFC.small_energy_singularity` in `Challenge.lean` and
`FCSolution.lean`. Energy target: `CalabiFC.small_calabi_energy`.

| Natural-language clause | Fixed formal expression / definition | Review |
|---|---|---|
| Complex projective seven-space | `Hom = Fin 8 → ℂ`; homogeneous scaling invariance; eight charts with `Aff = EuclideanSpace ℂ (Fin 7)` | Smooth functions are represented on nonzero homogeneous coordinates. No arbitrary abstract substitute for the geometry. |
| Smooth Kähler metric in the fixed Fubini-Study class | `pot F j = log (1 + ‖Z‖²) + F (chart j Z)`; `IsKahlerPotential` requires positivity of the complex Hessian on every chart | The fixed class is encoded by adding a global potential. |
| Smooth flow on `[0,T)` | `IsCalabiFlow T F`, joint `ContDiffOn ℝ ∞` and pointwise Kähler positivity | Includes the initial time. |
| Calabi flow with average scalar curvature 56 | `HasDerivWithinAt ... (scal (pot (F t) 0) Z - 56)` | Actual derivative and scalar-curvature definitions, not a hypothesis carrying the desired result. |
| Scalar convention | `scal u = -tr ((gmat u)⁻¹ * gmat (log detg u))` | Matches `tr_ω Ric(ω)`; the proof checks the Fubini-Study value 56. |
| Every `2 ≤ p < 7`, `ε,τ > 0` | Quantifiers and inequalities appear explicitly in the primary target | The Sobolev constant is quantified before all four parameters. |
| `0 < T < τ` | Explicit conjunction | Real `T`, with no degenerate zero interval. |
| `U(7)` invariance | `IsU7Invariant` quantifies all complex linear isometries of `Aff` | Fixed origin in chart zero. |
| Initial uniform potential less than `ε` | `∀ v ≠ 0, |F 0 v| < ε` | Every projective point is represented. |
| Evolving probability volume | `nu u = (volMeasure u univ)⁻¹ • volMeasure u`; `IsProbabilityMeasure` also required | Density is the actual determinant of the metric. |
| `sup_t ‖S-56‖_Lp < ε` | One real `η` with `0 < η < ε`, and `eLpNorm ... ≤ ENNReal.ofReal η` at every time | The bridge applies the original theorem with `ε/2`. This avoids replacing a strict supremum bound by only pointwise strict bounds. |
| Sobolev exponent and gradient | `HasSobolevBound`: squared `L^(7/3)` norm, squared `L²` gradient and function norms | Real dimension 14; `gradSq` includes the factor 2 for the stated Riemannian convention. |
| One common finite Sobolev constant | `∃ CS : ℝ` precedes `∀ p,ε,τ` | A real constant is finite; the bound holds throughout the flow. |
| Fixed-point blow-up `S(o) ∼ a/√(T-t)`, `a > 0` | Positive `a` and `Tendsto (sqrt (T-t) * scal ... 0) (𝓝[<] T) (𝓝 a)` | Precisely the asymptotic equation, with a nonzero positive coefficient. |
| Arbitrarily small Calabi energy | `MainTheoremEnergy`, the case `p=2` | The target bounds the `L²` norm. Its square is the energy; arbitrary smallness of either gives arbitrary smallness of the other. |
| Maximal smooth flow from the same initial metric | **Not a formal conclusion** | The manuscript uses smooth uniqueness here. That theorem and identification are not formalized. The public statement explicitly concerns the constructed flow and its curvature blow-up. |

## Boundaries of this check

All target definitions are fixed, without definition holes, and import only
Mathlib. Only the two challenge theorem proofs and the corresponding draft
proofs contain intended holes. No such holes are admitted in the solution.
Comparator checks types and their dependent definitions against this independent
reference. The correspondence review is necessary because Lean and Comparator
do not check the interpretation of natural-language text.

The unchanged PDF retains its original maximal-flow wording. The README states
the exact formal result and discloses the additional smooth-uniqueness step.
No claim is made that every intermediate proof follows the manuscript's route.
