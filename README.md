# Lean proof of small-energy finite-time singularities of Calabi flow

This repository formalizes the existence of smooth Calabi flows on complex
projective seven-space with arbitrarily small curvature norms, one common
Sobolev bound, and finite-time scalar-curvature blow-up.

> **Formalized statement.** There is a real constant $C_S$ such that, for every
> $2\le p<7$ and $\varepsilon,\tau>0$, there are $0<T<\tau$ and a smooth
> $U(7)$-invariant Calabi flow in the Fubini-Study class of $\mathbb{CP}^7$ on
> $[0,T)$ with initial global potential $\|\phi_0\|_{C^0}<\varepsilon$,
> a single constant $0<\eta<\varepsilon$ such that
>
> $$\|S(\omega(t))-56\|_{L^p(\nu_t)}\le\eta\qquad(0\le t<T),$$
>
> Sobolev bound
>
> $$\|f\|_{L^{7/3}(\nu_t)}^2\le C_S\bigl(\|\nabla f\|_{L^2(\nu_t)}^2+\|f\|_{L^2(\nu_t)}^2\bigr),$$
>
> and, at the fixed origin $o$, $\sqrt{T-t}\,S(\omega(t))(o)\to a>0$.

Here $\nu_t$ is the volume normalized to total mass one, and the reference
Fubini-Study potential is $\log(1+|Z|^2)$, with scalar curvature $56$.
The same $C_S$ works for every $p,\varepsilon,\tau$ and $t$.
Taking $p=2$ gives arbitrarily small Calabi energy.

**Scope of the formalization.** The manuscript describes the *maximal smooth
flow from the initial metric*. Lean constructs a smooth flow and proves the
displayed positive curvature blow-up. Smooth uniqueness, which identifies
this flow with every flow from the same initial metric, is not formalized.
No such uniqueness or maximal-flow conclusion is claimed by the target above.
The [statement correspondence](lean/comparator/TARGET-CORRESPONDENCE.md)
records this distinction explicitly.

## Files

| Directory | Purpose |
|---|---|
| [lean/](lean/) | Canonical complete proof, independent Challenge, FCSolution and Comparator configuration. |
| [leanWithoutComparator/](leanWithoutComparator/) | Identical proof sources and solution bridge, without Comparator-only files. |
| [FClikelean/](FClikelean/) | Standalone Formal Conjectures style draft: fixed definitions and two statement holes. Not an upstream FC submission. |
| [lean/comparator/](lean/comparator/) | Pinned tools, source hashes, correspondence review and verification scripts. |
| [.github/workflows/comparator.yml](.github/workflows/comparator.yml) | Linux build, Comparator, axiom audit and independent fresh kernel replay. |
| [PDF/](PDF/) | Original manuscript and its existing timestamp evidence, unchanged. |
| [verification/](verification/) | Local review and CI receipts, with historical audits clearly separated. |

All three projects pin Lean **4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The common proof sources in the first two projects are byte-identical and
checked against a source manifest.

## Build and verify

```sh
cd lean
lake exe cache get
lake build
lake build Calabi FCAudit
lake env lean FCAudit.lean
lake env leanchecker --fresh FCSolution
```

Unlike the original development project, the ordinary default build includes
the final theorem. The proof entry is
[Calabi/Main.lean](lean/Calabi/Main.lean); the public target is
[FCSolution.lean](lean/FCSolution.lean).

The independent reference imports only Mathlib. Its two intentional `sorry`
proofs are statement placeholders; the submitted solution and all its proof
sources contain no `sorry`, `admit`, custom axiom or `native_decide`.
The permitted transitive axioms are exactly `propext`, `Classical.choice` and
`Quot.sound`.

Comparator and Lean4export are pinned at their Lean 4.34.0 revisions and built
with a recorded toolchain-only change to 4.34.1. Their Lean source code is
unchanged. Linux CI uses real Landrun sandboxing and the upstream-recommended
AF_UNIX restriction; local macOS checks are development checks.

Natural-language correspondence is a clause-by-clause mathematical review.
Comparator checks the Lean statements and their dependent definitions against
the independently compiled reference; it does not interpret English or certify
an arbitrary PDF-to-Lean translation.

See [PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) for actual verification
status. Historical success records are not evidence that a new CI run passed.

## Proof route

The positive shrinking profile is constructed with exact finite-interval
certificates, origin and tail arguments, and a fixed-point matching argument.
A weighted inverse from the pinned [OpenAI math sources](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)
is specialized to the needed dimension. Two flat charts and an approximate
right-inverse iteration correct the localized profile to an exact solution.
The geometric bridge constructs the flow on $\mathbb{CP}^7$, the small curvature
norms and the common Sobolev bound. The latter is derived from the Euclidean
Sobolev inequality.

Several arguments differ from the manuscript. The detailed original development
guide is retained as [PROOF-GUIDE.md](lean/PROOF-GUIDE.md); its `audit/` paths refer
to the original workspace. The publication verification instructions above are
the current entry points.

## Verification records

The local review, private CI and public CI are recorded separately under
[verification/](verification/). CI artifacts are retained for 90 days. Completed
run logs, artifacts and SHA-256 checksums should be preserved beyond that window.
The latest completed run receipts, rather than a badge alone, fix the exact
tested commit and repository visibility.
