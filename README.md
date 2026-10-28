# Lean proof of small-energy finite-time singularities of Calabi flow

[![Lean proof](https://github.com/KitaKen1/calabi-small-energy-singularity/actions/workflows/lean-proof.yml/badge.svg)](https://github.com/KitaKen1/calabi-small-energy-singularity/actions/workflows/lean-proof.yml)

The manuscript [*Small-energy finite-time singularities of Calabi flow*](PDF/calabi-small-energy.pdf#page=1)
considers Calabi flow on complex projective seven-space. The result formalized here is:

> **Small-energy finite-time singularities.** There is a real constant $`C_S`$ such that,
> for every $`2\le p<7`$ and $`\varepsilon,\tau>0`$, there are $`0<T<\tau`$ and a smooth
> $`U(7)`$-invariant Calabi flow $`\omega(t)`$ in the Fubini–Study class of $`\mathbb{CP}^7`$
> on $`[0,T)`$, with initial global potential $`\|\varphi_0\|_{C^0}<\varepsilon`$ and
>
> $$\sup_{0\le t<T}\|S(\omega(t))-56\|_{L^p(\nu_t)}<\varepsilon.$$
>
> The same flow satisfies the Sobolev bound
>
> $$\|f\|_{L^{7/3}(\nu_t)}^2\le C_S\bigl(\|\nabla f\|_{L^2(\nu_t)}^2+\|f\|_{L^2(\nu_t)}^2\bigr)$$
>
> at every time, and, at the fixed origin $`o`$,
>
> $$\sqrt{T-t}\,S(\omega(t))(o)\longrightarrow a>0\qquad(t\uparrow T).$$

Here $`\nu_t`$ is the volume normalized to total mass one. The Fubini–Study normalization
has scalar curvature $`56`$, and the same $`C_S`$ works for every $`p,\varepsilon,\tau`$ and $`t`$.
Taking $`p=2`$ gives arbitrarily small Calabi energy.

This repository contains a Lean 4.34.1 proof of the displayed statement, using pinned
Mathlib dependencies. The manuscript additionally identifies the constructed flow with
the maximal smooth flow from its initial metric. Smooth uniqueness, needed for that
identification, is not formalized; the [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md)
records the precise scope.

The two main components are:

1. **A Formal Conjectures style statement.**
   [FClikelean/](FClikelean/) states OpenAI’s counterexample on complex projective
   ten-space and the present seven-dimensional variant.
2. **The full Lean proof.**
   [Main.lean](lean/Calabi/Main.lean) combines the shrinking profile, localized correction,
   geometric construction and Sobolev bound.
   [FCSolution.lean](lean/FCSolution.lean) connects this proof to the independent small-energy targets.

## Formal Conjectures like targets

### FClikelean

[CalabiSmallEnergy.lean](FClikelean/CalabiSmallEnergy.lean) has two theorem statements:
`calabi_flow` for OpenAI’s counterexample on $`\mathbb{CP}^{10}`$, and
`calabi_flow.variants.dimension_seven` for the present variant on $`\mathbb{CP}^{7}`$.
Both use `answer(False) ↔ CalabiFlowConjecture n`, where the positive question
asks whether every smooth Calabi flow in the Fubini–Study class extends past
every finite endpoint. The extension agrees with the original flow throughout
its original interval. These are projective statements; the original conjecture
on arbitrary Kähler manifolds is not a target of this file.

The flow predicate explicitly displays equation (1.1) of [OAI26]: the initial
form `ω₀`, `ωₜ t = ω₀ + ddbar (φ t)`, `φ 0 = 0`, positivity, and the equation
`∂ₜφ = scal (ωₜ t) - S_avg`, where `S_avg = n * (n + 1)` in the fixed class.
Local form coefficients, the actual complex Hessian and smoothness conditions
are defined in the same file. There is one standard
`public import FormalConjecturesUtil` entry point and one `CalabiFC` namespace.
Each theorem carries `category research solved` and AMS tags; its docstring
gives the question, negative answer and source.

Both FC proof bodies are intentional `sorry` placeholders. The CP10 proof is
cited from OpenAI and is outside this repository’s proof verification.
The stronger CP7 theorem is proved in [FCSolution.lean](lean/FCSolution.lean).
A separate kernel proof connects its independent reference to the CP7 variant
and the corollary `¬ ∀ n, CalabiFlowConjecture n`.

### Comparator target

[Challenge.lean](lean/Challenge.lean) supplies the independent reference statements,
and [FCSolution.lean](lean/FCSolution.lean) proves them. The two targets are
`CalabiFC.small_energy_singularity` and `CalabiFC.small_calabi_energy`.
The reference [definitions](lean/FCTargetDefinitions.lean) import only Mathlib.
The [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md) identifies each
natural-language clause and its formal statement.

The primary target uses one $`0<\eta<\varepsilon`$ to bound the curvature norm by $`\eta`$
at every time. Applying the underlying theorem with $`\varepsilon/2`$ gives this uniform
margin and hence the strict supremum bound in the statement above.

## Mathematical explanation (AI generated)

The idea is to concentrate curvature near one point while keeping the Kähler class
fixed. In a radial momentum coordinate $`x`$, the curvature will have size
$`(x+\sqrt{-t})^{-1}`$ near the singular point, whereas normalized volume has density
$`7x^6\,dx`$. Thus a sufficiently small neighborhood can carry unbounded pointwise
curvature and arbitrarily small $`L^p`$ curvature for $`p<7`$. The work is to realize
this concentration by an exact Calabi flow and retain a common Sobolev bound.
We place the singular time at $`t=0`$ during the construction.

**1. Reduce the geometric flow to a scalar equation.** A $`U(7)`$-invariant metric
in the Fubini–Study class is described by the inverse Hessian $`v=1/u''`$ of its
symplectic potential. Write

```math
v_*=x(1-x),\qquad v=v_*b,\qquad b=1+v_*H,\qquad 0\le x\le1.
```

Smoothness of $`H`$ at both endpoints and positivity of $`b`$ give a smooth Kähler
metric on $`\mathbb{CP}^7`$ in the prescribed class. Direct calculation gives

```math
S=56-K(H),\qquad K(H)=x^{-6}\partial_x^2\bigl(x^8(1-x)^2H\bigr),
\qquad H_t+b^2\partial_x^2K(H)=0.
```

The apparent singularity of $`K`$ at $`x=0`$ is removable for smooth $`H`$.
To recover the flow in fixed complex coordinates, choose the affine part of
$`u`$ so that $`u_t=K(H)`$. The scalar equation ensures compatibility with
$`u''=1/v`$, and the Legendre dual Kähler potential then satisfies
$`\Phi_t=-u_t=S-56`$. The pushforward of normalized volume under $`x`$ is always
$`7x^6\,dx`$, independently of $`H`$.

**2. Find a shrinking solution for the equation near the point orbit.** Replace
$`v_*`$ by its leading term $`x`$ near $`x=0`$ and seek a self-similar solution

```math
F(t,x)=\rho^{-1}h(x/\rho),\qquad
\rho=\sqrt{-t},\qquad h(y)=\frac{G(y)-1}{y}.
```

Substitution reduces this flat model equation to the third-order ODE

```math
(D-1)(D+6)(D+7)(G-1)
=\frac{y^2}{2}\left(\frac1G-\frac1c\right),\qquad D=y\partial_y.
```

The required solution has $`G(0)=1`$, $`G'(0)<0`$, $`0<c<1`$, and
$`G(y)\to c`$, with positive upper and lower bounds on the whole half-line.
Its existence is a boundary-value problem: a contraction constructs a two-parameter
family of regular solutions at the origin; after a change of variable, the
linearization at infinity has one decaying mode and two growing modes. A second
contraction constructs the bounded tails with a prescribed decaying coordinate.
Rational enclosures of the intervening ODE trajectories give bounds on the
two-coordinate matching error. After a linear change of the origin parameters,
this error has the form $`z+R(z)`$ on a small parameter box, with $`-R`$ mapping
the box into itself. Brouwer's fixed-point theorem makes the error vanish and
joins an origin solution to a bounded tail, preserving positivity throughout.
Bootstrapping the tail equation gives an expansion in powers of $`y^{-2}`$, with
estimates for all derivatives. This expansion will also control the model away
from the shrinking center.

**3. Localize the model and solve away its error.** Choose $`0\le\chi\le1`$,
equal to one on $`[0,1]`$ and zero on $`[2,\infty)`$, and set
$`F_\lambda=\chi(x/\lambda)F`$. Its metric multiplier is

```math
1+v_*F_\lambda
=1-\chi(x/\lambda)+\chi(x/\lambda)\bigl[x+(1-x)G(x/\rho)\bigr].
```

This is bounded above and away from zero by constants depending only on the
fixed profile. It describes the shrinking core joined to the Fubini–Study metric
outside $`x\le2\lambda`$.

The error comes from both the compact geometry and the cutoff. The analytic
step is to correct it by $`H=F_\lambda+V`$ on an arbitrarily short interval
ending at zero. Linearize the equation at $`F_\lambda`$ and use weighted
parabolic Hölder norms adapted to the spatial scale $`(x+\rho)^{1/2}`$.
In the inner region, an inverse for the linearized shrinking solution solves
the equation on all past times. In the outer region, a uniformly parabolic
solver with zero initial data supplies the correction. Joining these solvers
cancels the inner cutoff commutator; shrinking the inner region and then the
time interval gives an approximate right inverse with defect at most $`1/2`$.
Its norm stays bounded as these two parameters decrease.

The important estimate is smallness of the *first correction* at fixed
$`\lambda`$: the cutoff residual itself need not become small as
$`\lambda\to0`$. Its inner contribution is small in the weighted source norm;
the outer contribution produces a small solution on a short time interval.
The nonlinear remainder is quadratic in the correction, so iteration gives an
exact smooth solution. For a fixed $`0<\delta<1`$ it satisfies

```math
|V|+|K(V)|\le Ce(x+\rho)^{-1+\delta},\qquad
0<\kappa_1\le 1+v_*H\le\kappa_2.
```

Here $`e`$ can be arbitrarily small after $`\lambda`$ is fixed, and the
positivity constants are independent of the localization and time parameters.
The gain $`\delta>0`$ makes the correction lower order at the singular point.

**4. Estimate the curvature norm and the initial potential.** The profile and
correction bounds give

```math
|K(F_\lambda)|\le\frac{C\mathbf1_{\{x\le2\lambda\}}}{x+\rho},\qquad
|K(V)|\le Ce(x+\rho)^{-1+\delta}.
```

For $`p<7`$, the two relevant integrals obey

```math
\int_0^{2\lambda}\frac{x^6}{(x+\rho)^p}\,dx
\le\frac{(2\lambda)^{7-p}}{7-p},\qquad
\int_0^1x^6(x+\rho)^{-p+p\delta}\,dx
\le\frac1{7-p+p\delta}.
```

Since $`S-56=-K(H)`$, Minkowski's inequality therefore yields, uniformly in time,
$`\|S-56\|_{L^p(\nu_t)}\le C_p\lambda^{7/p-1}+C_pe`$.
This is where the subcritical restriction $`p<7`$ enters.

For the initial potential, let $`u_*`$ be the Fubini–Study symplectic potential,
write $`u=u_*+\psi`$ at an interior time slice and normalize
$`\psi(1)=\psi'(1)=0`$. Then

```math
\psi''=-\frac{H}{1+v_*H},\qquad
\|\psi\|_\infty\le C\int_0^1x|H|\,dx\le C(\lambda+e).
```

The Legendre transform does not increase the uniform distance between two
potentials: this follows by comparing the suprema defining their duals.
Consequently the initial potential in the original complex coordinates satisfies
$`\|\varphi_0\|_{C^0}\le C(\lambda+e)`$ as well.

**5. Obtain the common Sobolev bound and the singularity.** Identify the momentum
and angular coordinates of the constructed metric with those of Fubini–Study.
The radial, Hopf-circle and horizontal metric components then have respective
ratios $`b^{-1},b,1`$. The bounds on $`b`$ give
$`\Lambda^{-1}g_*\le g(t)\le\Lambda g_*`$ under this diffeomorphism, with
one $`\Lambda`$ determined by the profile. The volume forms agree, since the
radial and circle factors cancel. Applying the Fubini–Study Sobolev inequality
to the pulled-back function thus gives
$`C_S(g(t))\le\Lambda C_S(g_*)`$, independently of every small parameter.

At the center, $`K(H)(0)=56H(t,0)`$ and
$`F_\lambda(t,0)=\rho^{-1}G'(0)`$. Hence

```math
\rho S(t,o)=-56G'(0)+O\bigl(\rho+e\rho^\delta\bigr)
\longrightarrow-56G'(0)>0.
```

Finally, given $`p,\varepsilon,\tau`$, first choose $`\lambda`$ so that the
model curvature norm and potential bound are sufficiently small, then choose
$`e`$ to control the correction. The construction allows the time interval to
be shortened afterwards. Taking an interior slice as the initial time and
translating time gives $`[0,T)`$ with $`T<\tau`$ and the requested uniform
smallness. The displayed curvature divergence prevents smooth extension
through $`T`$. Together these estimates prove the stated result for the
constructed flow.

The [proof note](PDF/calabi-small-energy.pdf), Sections 2–7, gives the full
argument. The [proof guide](lean/PROOF-GUIDE.md) records the alternative analytic
constructions used in the formal proof.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Canonical proof, pinned dependencies, Challenge and FCSolution. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.34.1` | The same proof for browsing and building, with Comparator-only files removed. |
| [FClikelean/](FClikelean/) | `v4.34.1` | Compact FC-style problem and geometric definitions; local build passed. |
| [lean/comparator/](lean/comparator/) | `v4.34.1` | Input pins, statement correspondence, verification scripts and guide. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Manual build, Comparator, axiom audit and fresh kernel replay. Automatic CI is disabled. |
| [PDF/](PDF/) | — | Original manuscript and its existing timestamp evidence. |
| [verification/](verification/) | — | Local checks, historical audits and CI status records. |

The 466 common Lean sources in the canonical and supplementary projects are byte-identical.
All three projects pin Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) records the candidate and its verification status.

## Verification

### Lean execution results

The full proof and independent reference compiled locally on Lean 4.34.1.
[FCAudit.lean](lean/FCAudit.lean) checks six principal declarations, including both
FC connections, both main theorems, the profile and the localized correction.
All six use only `[propext, Classical.choice, Quot.sound]`;
see the [axiom record](verification/local/axioms.json).
The complete proof contains no `sorry`, `admit`, custom axiom or `native_decide`.

The two single-file FC statements also compile. A separate Lean kernel proof
shows that the independent small-energy reference implies the CP7 variant
`answer(False) ↔ CalabiFlowConjecture 7` and the projective corollary
`¬ ∀ n, CalabiFlowConjecture n`, using only the same three permitted axioms.
It checks both directions of the change from the fixed-Fubini–Study potential
`F` to the initial form `ω₀` and `φ t = F t - F 0`, then derives nonextension
from scalar blow-up and the Calabi equation. See the
[implication record](verification/local/fc-original-equation-20261020/verification.json).
The main CP10 theorem is checked as a statement only; its cited OpenAI proof is
not audited here. Historical receipts retain their original target types and hashes.

### Lean Comparator check

The reference, proof, Comparator and Lean4export all use Lean 4.34.1.
Comparator and Lean4export are pinned to their last 4.34 source revisions;
only their toolchain declarations are changed from 4.34.0 to 4.34.1.
Their Lean source code is unchanged.

The local comparison passed for both targets using the unmodified `Comparator.compareAt`
and `checkAxioms` APIs over independently exported environments.
A separate `leanchecker --fresh FCSolution` replay also passed.
These are macOS development checks; the Linux sandbox check has not been run for this release.
See the [comparison record](verification/local/comparator-library.json),
[fresh replay record](verification/local/fresh-replay.json) and
[statement review](verification/local/statement-review.json).

The public [Lean proof workflow](https://github.com/KitaKen1/calabi-small-energy-singularity/actions/workflows/lean-proof.yml)
builds `FCSolution`, `FCAudit` and `Calabi`, then checks the permitted axioms.
Its result is shown by the badge above. This build is separate from the full
Comparator and fresh environment replay workflow, which has not run publicly.
The historical private full-verification attempt was cancelled.

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| 1982 | Eugenio Calabi | Introduced extremal Kähler metrics and Calabi flow in the study of scalar curvature within a fixed Kähler class ([chapter](https://doi.org/10.1515/9781400881918-016)). |
| 2008 | Xiuxiong Chen and Weiyong He | Established short-time existence, stability near constant-scalar-curvature Kähler metrics and continuation under a uniform Ricci-curvature bound ([paper](https://arxiv.org/abs/math/0603523), [journal version](https://doi.org/10.1353/ajm.2008.0018)). |
| October 2026 | Kenta Kitamura | Prepared the [small-energy singularity manuscript](PDF/calabi-small-energy.pdf), the Lean proof and the compact FC-style statement in this repository. |

The earlier work provides the variational, existence and regularity setting for
Calabi flow. The construction here gives finite-time scalar-curvature blow-up on
$`\mathbb{CP}^7`$ while every prescribed subcritical $`L^p`$ curvature norm,
$`2\le p<7`$, stays arbitrarily small and one Sobolev constant works throughout.

## Appendix: Verification by Lean Comparator on GitHub CI runner

The [workflow](.github/workflows/comparator.yml) can be run manually to build the full proof on Linux.
Automatic runs on pushes are disabled. The separate [Lean proof build](.github/workflows/lean-proof.yml)
does not run Comparator or fresh environment replay.
A separate job compiles the trusted reference before restoring proof products,
compares dependent definitions in an unprivileged Landrun sandbox, audits permitted
axioms and requires builtin Lean-kernel acceptance. Another job performs a fresh
replay of the complete proof environment.

### Certification Within 90 days: CI results

The workflow retains logs and artifacts for 90 days. The private attempt's build
succeeded, but the run was [cancelled](verification/private-ci-verification.json)
before full verification finished. Public CI has not run.
The public Lean proof build is tracked separately by the badge above; this
full-verification workflow has not been run publicly.

### Certification After 90 days: archive

There is no completed CI certification archive for this candidate yet.
[archive-run.py](lean/comparator/archive-run.py) can preserve successful runs as
original artifact ZIPs, complete job logs, run metadata, extracted receipts and
SHA-256 checksums. It records the tested commit, run and attempt and checks artifact
ZIP hashes against the GitHub API digests.

### Reproduce the verification

```sh
python3 lean/comparator/check-inputs.py
cd lean
lake exe cache get
lake build
lake build Calabi FCAudit
lake env lean FCAudit.lean
lake env python3 comparator/check-fc-draft.py --receipt-dir ../fc-draft-receipt
lake env leanchecker --fresh FCSolution
```

See the [verification guide](lean/comparator/README.md) for the pinned tools
and Linux sandbox checks. Historical development records retain their original scope.
