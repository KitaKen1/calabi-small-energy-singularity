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
Mathlib. Only the two challenge theorem proofs and the two FC draft theorem
proofs contain intended holes. No such holes are admitted in the solution.
Comparator checks types and their dependent definitions against this independent
reference. The correspondence review is necessary because Lean and Comparator
do not check the interpretation of natural-language text.

The unchanged PDF retains its original maximal-flow wording. The README states
the exact formal result and discloses the additional smooth-uniqueness step.
No claim is made that every intermediate proof follows the manuscript's route.

## OpenAI counterexample and seven-dimensional variant

`FClikelean/CalabiSmallEnergy.lean` has two targets:

- `CalabiFC.calabi_flow`: `answer(False) ↔ CalabiFlowConjecture 10`, the cited
  OpenAI counterexample.
- `CalabiFC.calabi_flow.variants.dimension_seven`:
  `answer(False) ↔ CalabiFlowConjecture 7`, the present variant.

`CalabiFlowConjecture n` asks for extension of every finite-interval smooth
Calabi flow in the Fubini–Study class of CPⁿ, agreeing throughout its original
interval. The file is restricted to these projective counterexamples. It does
not state the original conjecture for arbitrary Kähler manifolds.

The CP10 theorem is checked as a statement only; the OpenAI proof is not
included in local certification. For the CP7 variant, `check-fc-draft.py` proves
an implication from the independent small-energy reference, with only
`propext`, `Classical.choice` and `Quot.sound`. The small-energy, symmetry and
common Sobolev bounds are stronger conclusions in the independent targets.
A further kernel-checked corollary gives `¬ ∀ n, CalabiFlowConjecture n`.

The bridge uses the Calabi equation at the origin. A smooth extension makes
the time derivative of its potential continuous there. On the original
interval this derivative equals `S - 56`, so `sqrt(T - t) * S` would tend to
zero. The reference theorem gives its limit as a positive number. No uniqueness
of flows from initial data is needed for this extension contradiction.

The FC flow predicate uses the initial-form normalization of [OAI26], equation
(1.1): `ωₜ t = ω₀ + ddbar (φ t)`, `φ 0 = 0`, positivity and the Calabi equation.
`Form` is local coefficient data; `IsKahlerForm` requires a positive form of the
shape `fubiniStudy n + ddbar f`, where `f` is a smooth projective function.
For CP7, `flow_iff` proves equivalence with the unchanged reference after
choosing this `f` and writing `F t = f + φ t`. Conversely,
`flow_from_reference` sets `f = F 0` and `φ t = F t - F 0`.
The bridge proves linearity of the complex Hessian on smooth functions,
preservation of the metric coefficients and scalar curvature, joint and slice
smoothness, positivity, and the time derivative under this change.
The normalized extension keeps the same initial form.

This is an equivalence of the two coordinate descriptions. The equation is
still imposed on chart zero, with smoothness and positivity on all charts.
A full equivalence with an intrinsic manifold/differential-form development,
including coordinate invariance and extension from the dense chart, is not
kernel-certified here. Both descriptions specialize the original equation to
CPn in the Fubini–Study class; neither formalizes arbitrary Kähler manifolds.

Both problem-file proof bodies are intentional placeholders. The category and
AMS attributes are metadata and do not enter the mathematical target types or
axiom audit. `answer(False) ↔ P` is equivalent to `¬ P`, which is also checked
in the Lean kernel. Historical three-theorem receipts preserve their original
scope; their `calabi_flow` types differ from the current CP10 target.
