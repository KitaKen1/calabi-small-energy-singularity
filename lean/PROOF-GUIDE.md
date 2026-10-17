> Historical development guide. This publication uses `Calabi.Main` through both
> `Calabi.lean` and the default `FCSolution` target. The original `audit/` paths and
> older build-entry descriptions below refer to the development workspace.
> Use the repository README and `lean/comparator/README.md` for current verification.

# Calabi small-energy singularity: Lean implementation

Lean 4.34.1. Mathlib is fixed at `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The OpenAI source extraction is fixed at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## The main theorem

Theorem 1.1 of the manuscript *Small-energy finite-time singularities of Calabi
flow* is proved, with no hypothesis (`Calabi/Main.lean`):

```lean
theorem Calabi.mainTheorem : Calabi.Geometry.MainTheorem
theorem Calabi.mainTheoremEnergy : Calabi.Geometry.MainTheoremEnergy   -- the case p = 2
```

`Calabi.Geometry.MainTheorem` (`Calabi/Geometry/Statement.lean`, definitions
and statements only) says: there is a constant `CS` such that for every
`2 ≤ p < 7` and `ε, τ > 0` there are `0 < T < τ` and a smooth `U(7)`-invariant
Calabi flow `∂ₜφ = S - 56` on `[0, T)` in the Fubini–Study class of `CP⁷`, with
initial potential smaller than `ε` in the uniform norm, with
`‖S - 56‖_{L^p(ν)} < ε` and the Sobolev inequality (1.1) with the constant
`CS` at every time, and with `√(T - t) S(o) → a > 0` at the fixed point `o`.

`#print axioms Calabi.mainTheorem` gives `propext`, `Classical.choice`,
`Quot.sound` and nothing else (`audit/main-axioms.log`). The local closure of
`Calabi.Main` has 448 modules (153 of this project, 295 of the reused library
in `vendor/OAI`); `audit/clean-rebuild.json` records a compilation of all of
them from scratch into an empty directory (448 compiled, none reused), and
`audit/main-axioms-clean.log` the same axiom lists for those artifacts.

```sh
python3 scripts/build_parallel.py Calabi.Main --jobs 3
python3 scripts/run_lean.py audit/MainAxioms.lean
```

The library root `Calabi.lean` lists only the earlier modules (last section), so
`lake build Calabi` does not compile `Calabi.Main`; the two commands above do.

What the formal statement does not contain: the manuscript speaks of *the
maximal smooth Calabi flow* from the initial metric. `MainTheorem` expresses the
singular time by the blow-up (1.5) of the scalar curvature at `o`, which rules
out a smooth extension of the constructed flow beyond `T`; the identification
of the constructed flow with every smooth flow from the same initial metric
(uniqueness of smooth Calabi flows, end of Lemma 2.3) is not formalized.

The proof has the three parts of the manuscript, but several of them are proved
by a different route (the statements are those of the manuscript):

| Part | Result | Route |
| --- | --- | --- |
| Theorem 3.1 (profile) | `Calabi.exists_profile` | a new kernel-checked a-posteriori certificate on `1 ≤ s ≤ 56`, a contraction at the origin, a tail solved around a certified approximation, matching by Brouwer's theorem |
| Sections 4–5 (inner inverse) | `OAI.FlatSimilarity.exact_weighted_inverse` | reused upstream library, specialized to dimension 18 |
| Proposition 6.1 (correction) | `Calabi.Weighted.localizedCorrection` | two flat charts `ℝ¹⁸`, `ℝ⁶` instead of the sphere `S²³`; outer problems with coefficients frozen at the singular time; an iteration with an approximate right inverse; smoothness by difference quotients and the interior Schauder estimate; Whitney's theorem on even functions at the two ends |
| Sections 2 and 7 (geometry) | `Calabi.Geometry.mainTheorem_of_forall_localizedCorrection` | as in the manuscript; the Sobolev inequality of the Fubini–Study metric, quoted in the manuscript, is derived from the Euclidean one |

Checked results are recorded in `audit/status.json`.

## The profile theorem (Theorem 3.1 of the manuscript)

`Calabi.exists_profile` and `Calabi.shrinking_profile`
(`Calabi/ShrinkingProfile.lean`) are Theorem 3.1: there are `0 < c < 1` and a
smooth `G` on `[0, ∞)` (`Calabi.IsProfile c G`) with

* `y³ G‴ + 15 y² G″ + 42 y G′ - 42 (G - 1) = (y²/2)(1/G - 1/c)` for `y > 0`
  (the left-hand side is `(D - 1)(D + 6)(D + 7)(G - 1)`, `D = y d/dy`);
* `G(0) = 1`, `G′(0) < 0`, and positive lower and upper bounds for `G`;
* `H(u) = G(u^{-1/2})` extends to a smooth function on `[0, ∞)` with
  `H(0) = c`.

`Calabi.Flat.flat_equation` (`Calabi/Flat/SelfSimilar.lean`) is the last
assertion of Theorem 3.1: with `h(y) = (G(y) - 1)/y` and `ρ = √(-t)`, the
function `F(t, x) = ρ⁻¹ h(x/ρ)` solves
`F_t + (1 + x F)² (x² F_xxxx + 20 x F_xxx + 90 F_xx) = 0` for `t < 0`, `x ≥ 0`,
including `x = 0`.

The last item of the list is the expansion (3.3) of the manuscript in the form consumed by
the reused inverse: `Calabi.Reuse.profile_with_inverse`
(`Integration/ProfileInverse.lean`) applies
`Calabi.Reuse.dimension_eighteen_inverse` to this profile. The expansion with
remainders `O(y^{-2(J+1)-ℓ})` is not stated separately.

The proof does not follow the manuscript step by step:

* `Calabi/Shot`: a new a-posteriori certificate for the finite interval
  `1 ≤ s ≤ 56`, checked by the Lean kernel. 576 blocks carry integer
  polynomials; the kernel recomputes their exact residuals (`ok0` … `ok575`)
  and the propagation of the remainder along the chain (`chain_ok`).
  `Calabi.Shot.finite_shot` encloses every trajectory of the profile system
  for every parameter of the box `|z₁|, |z₂| ≤ 2^-56`.
* `Calabi/Tail`: bounded solutions of the profile equation on `[56, ∞)` with
  a prescribed stable coordinate, around an approximate tail whose residual
  the kernel recomputes (`tail_ok`). The a priori bound uses rational
  coordinates for `∂³ + 1` and no Green function.
* `Calabi/Match`: Brouwer's theorem matches the two at `s = 56`.
* `Calabi/Origin`: the regular solution at the origin as a contraction for
  `P = d + k r - (8/27) r² K0(N ∘ P)`, compared a posteriori with a certified
  polynomial of degree 60 (`origin_ok`); its jet at `s = 1`
  (`Calabi.Origin.startOk`), the trajectory on the whole half-line
  (`Calabi.Origin.exists_profile_jet`) and smoothness at `r = 0`
  (`Calabi.Origin.contDiffOn_oP_infty`).
* `Calabi/Infinity`: the formal solution in `σ = s⁻³` (`tailPoly_dvd`), decay
  of every remainder by a dyadic bootstrap of the a priori bound
  (`exists_decay`), all derivatives by induction in the class `Bd`
  (`wjet_bd`), and smoothness in the variable `σ` up to `σ = 0`
  (`contDiffOn_ext_profile`).

```sh
python3 scripts/build_parallel.py Calabi.Flat.SelfSimilar --jobs 3
python3 scripts/build_parallel.py Integration.ProfileInverse --jobs 3
python3 scripts/run_lean.py audit/ProfileAxioms.lean
python3 scripts/run_lean.py audit/ProfileInverseAxioms.lean
```

`scripts/gen_shot_certificate.py`, `scripts/gen_tail_certificate.py` and
`scripts/gen_origin_certificate.py` regenerate the data from untrusted
numerics; `scripts/shot_checks.py`, `scripts/shot_lohner.py`,
`scripts/tail_checks.py` and `scripts/origin_checks.py` mirror the kernel
computations in exact integer arithmetic.

## The momentum coordinate and the statement on CP⁷

* `Calabi/Radial`: the Calabi flow of `U(7)`-invariant metrics in the momentum
  coordinate `x ∈ [0, 1]` (`Kop`, `Aop`, `IsRadialFlow`; `Kop_eq_div` identifies
  `Kop` with `x⁻⁶ (x⁸ (1 - x)² H)″`), the localized profile `Flam` with the
  bounds `Flam_bounds`, and `radialMain_of_correction`: the conclusion of
  Proposition 6.1 (`LocalizedCorrection`) implies the main theorem in the
  momentum coordinate for `p = 2` (`RadialMain`): Sections 7.1, 7.2 and 7.4.
  `LocalizedCorrection` is a hypothesis of that theorem; it is proved in
  `Calabi/Correction/Assembly.lean` (see below).
* `Calabi/Geometry/Statement.lean`: definitions and the statement
  `Calabi.Geometry.MainTheorem` of Theorem 1.1 on `CP⁷` (statement only), with
  the case `p = 2` as `MainTheoremEnergy`.
* `Calabi/Geometry/RadialPotential.lean`, `FubiniStudy.lean`,
  `RadialScalar.lean`: the complex Hessian, metric matrix, determinant and
  scalar curvature of a radial potential `φ(‖Z‖²)` (`scal_radial`); the
  derivatives of `φ` are taken within `[0, ∞)`, so that the point `Z = 0` is
  included. As a check of the definitions, the Fubini–Study metric is a Kähler
  potential of the class with scalar curvature `56` (`isKahlerPotential_zero`,
  `scal_fubiniStudy`).

## The geometric reduction (Proposition 2.1, Lemma 2.3, Sections 7.1–7.2)

`Calabi.Geometry.mainTheoremCore_of_radialMainP` turns the solutions of the
momentum equation of `RadialMainP` into Calabi flows on `CP⁷`: for every
`2 ≤ p < 7` and `ε, τ > 0` a smooth `U(7)`-invariant Calabi flow on `[0, T)`,
`T < τ`, in the Fubini–Study class, with initial potential smaller than `ε` in
the uniform norm, `‖S - 56‖_{L^p(ν)} < ε` at every time, and
`√(T - t) S(o) → -56 G′(0) > 0`. This is `MainTheorem` without the uniform
Sobolev bound (`MainTheoremCore`). Together with `radialMainP_of_correction`
(Sections 7.1, 7.2, 7.4 for all `2 ≤ p < 7`):

```lean
theorem Calabi.Geometry.mainTheoremCore_of_correction {c : ℝ} {G : ℝ → ℝ}
    (hP : IsProfile c G) (h : LocalizedCorrection G) : MainTheoremCore
```

So the only hypothesis left for `MainTheoremCore` is `LocalizedCorrection`
(Proposition 6.1).

The uniform Sobolev bound (Section 7.3, inequality (7.8)) is proved relative to
the Fubini–Study metric: `MomentumData.hasSobolevBound` shows that the Sobolev
constant of the metric of `H` is at most `Λ = max (1, sup b, sup b⁻¹)` times
that of the Fubini–Study metric, `b = 1 + v∗ H`. Hence

```lean
theorem Calabi.Geometry.mainTheorem_of_correction {c : ℝ} {G : ℝ → ℝ}
    (hP : IsProfile c G) (h : LocalizedCorrection G) (hFS : FubiniStudySobolev) :
    MainTheorem
```

where `FubiniStudySobolev` is the Sobolev inequality (1.1) for the
Fubini–Study metric of `CP⁷` with some constant. This inequality is proved
(`Calabi.Geometry.fubiniStudySobolev`, next section), so `MainTheorem` is
reduced to `LocalizedCorrection` (Proposition 6.1), which is proved in the
section after it:

```lean
theorem Calabi.Geometry.mainTheorem_of_forall_localizedCorrection
    (h : ∀ (c : ℝ) (G : ℝ → ℝ), IsProfile c G → LocalizedCorrection G) : MainTheorem
```

The proof follows Section 2 of the manuscript:

* `Calabi/Radial/Strip.lean`: calculus on the closed strip `J × [0, 1]`
  (partial derivatives, the primitive in `x`, and the inverse function theorem
  for the fibrewise inverse, all up to the endpoints `x = 0, 1`);
* `Calabi/Geometry/Momentum.lean`: for a radial potential described in the
  momentum coordinate (`MomentumData`), `det (u_{j k̄}) = (1 - x)⁸ b e^{-7a}`,
  positivity, and **`S = 56 - K(H)`** (`MomentumData.scal_eq`);
* `Calabi/Geometry/Legendre.lean`: the symplectic potential `ψ` with
  `ψ″ = -H / (1 + v∗ H)`, `ψ_t = K(H)` (equation (2.13)), the Legendre
  transform, and `∂_t Φ = -K(H)` at a fixed point (equation (2.14));
* `Calabi/Geometry/Potential.lean`: the potential `Fhat` on `ℂ⁸ ∖ {0}`, smooth
  in time and space including the point orbit and the divisor at infinity, and
  the Calabi flow `∂_t Fhat = S - 56`;
* `Calabi/Geometry/ChartInfinity.lean`, `Kahler.lean`: positivity of the metric
  on the charts meeting the divisor at infinity, hence
  `Flow.isKahlerPotential_Fhat`;
* `Calabi/Geometry/Volume.lean`: the volume measure is `7 x⁶ dx` in the
  momentum coordinate, so `ν` is a probability measure and
  `∫ |S - 56|^p dν = ∫₀¹ |K(H)|^p 7x⁶ dx`;
* `Calabi/Geometry/PotentialBound.lean`: the uniform bound (7.5) of the initial
  potential (the Legendre transform does not increase the uniform norm);
* `Calabi/Geometry/Gradient.lean`, `Dilation.lean`, `SobolevTransfer.lean`:
  the gradient norm as a dual norm, the radial map `θ(Z) = e^{a(ξ)/2} Z` that
  matches the momenta (it pushes the Fubini–Study volume to the volume of the
  metric, and the pulled-back metric has the ratios `1`, `1/b`, `b`), and the
  resulting comparison of Sobolev constants;
* `Calabi/Geometry/Bridge.lean`: the flow `flowOf` of a solution `H` and the
  combination, with the blow-up `S(o) = 56 (1 - H(t, 0))` of Lemma 2.3.

```sh
python3 scripts/build_parallel.py Calabi.Geometry.Bridge --jobs 3
python3 scripts/run_lean.py audit/RadialAxioms.lean
python3 scripts/run_lean.py audit/GeometryAxioms.lean
python3 scripts/run_lean.py audit/BridgeAxioms.lean
```

## The Sobolev inequality of the Fubini–Study metric

`Calabi.Geometry.hasSobolevBound_fubiniStudy` is the inequality (1.1) of the
manuscript for the Fubini–Study metric of `CP⁷`,
`‖f‖²_{L^{7/3}} ≤ C₀ (‖∇f‖²_{L²} + ‖f‖²_{L²})` for the normalized volume, with
some constant `C₀`. The manuscript uses it as a known fact; Mathlib has only
the Euclidean Gagliardo–Nirenberg–Sobolev inequality, so it is derived here:

* `Calabi/Geometry/ChartSwap.lean`: the exchange of the homogeneous coordinates
  `0` and `m + 1` is, in the chart `0`, the map
  `τ_m(Z) = Z_m⁻¹ (Z + (1 - Z_m) e_m)`. It is an involution of `{Z_m ≠ 0}` with
  complex Jacobian `-Z_m⁻⁸`, it preserves the Fubini–Study volume
  (`lintegral_tau`) and the Fubini–Study quadratic form (`quad_tau`), hence
  `|∇(F ∘ τ_m)|² ≤ |∇F|² ∘ τ_m` (`gradSq_tau_le`);
* `Calabi/Geometry/LocalSobolev.lean`: on the unit polydisc `P = {|Z_k| ≤ 1}`
  the Fubini–Study metric is uniformly equivalent to the flat one; with a
  cut-off function and Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_eq` in real
  dimension `14` (`1/2 - 1/14 = 3/7`) this gives
  `‖1_P G‖_{L^{7/3}} ≤ C (‖∇G‖_{L²} + ‖G‖_{L²})` (`local_sobolev`);
* `Calabi/Geometry/FubiniStudySobolev.lean`: `CP⁷` is covered by the eight sets
  `{|v_j| = max_i |v_i|}`; in the chart `0` they are `P` and the sets
  `Q_m = {|Z_m| ≥ 1, |Z_k| ≤ |Z_m|}`, and `τ_m` maps `Q_m` into `P`. A smooth
  function `f` on `CP⁷` composed with the exchange of coordinates is again
  smooth, so the local inequality applies to each piece.

```sh
python3 scripts/build_parallel.py Calabi.Geometry.FubiniStudySobolev --jobs 3
python3 scripts/run_lean.py audit/SobolevAxioms.lean
```

## The localized correction (Proposition 6.1, Sections 4 and 6)

```lean
theorem Calabi.Weighted.localizedCorrection {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) :
    LocalizedCorrection G
```

(`Calabi/Correction/Assembly.lean`): for a profile `G` there are `δ, κ₁, κ₂, C`
such that for every cut-off radius `0 < λ < 1/8`, every small `e > 0` and every
`T₀ > 0` there are `0 < T < T₀` and a smooth solution `H = F_λ + V` on
`(-T, 0) × [0, 1]` of the Calabi flow in the momentum coordinate with
`κ₁ ≤ 1 + v∗ H ≤ κ₂`, `|V| ≤ C e ς^{-1+δ}` and `|K(H) - K(F_λ)| ≤ C e ς^{-1+δ}`,
`ς = x + √(-t)`. This is the form of Proposition 6.1 that Section 7 uses.

The route differs from Section 6 of the manuscript in the following points.

* **Two flat charts instead of the sphere `S²³`.** A function of the momentum
  coordinate is represented by a pair of radial functions on the charts `ℝ¹⁸`
  (`x = |z|²`, near the point orbit) and `ℝ⁶` (`x = 1 - |w|²`, near the divisor),
  `V(x) = U⁰(√x e) + U¹(√(1 - x) e)`, so that every linear problem is a problem
  on a flat space, where the reused library applies.
* **Outer problems with time-independent coefficients.** The outer blocks solve
  `∂ₜZ + a Δ²Z = f`, `Z(-T) = 0`, with the multiplier frozen at the singular
  time; the difference with the true coefficient is `O(T/θ²)` and is treated as
  an error.
* **An iteration with an approximate right inverse** (`‖g - P S g‖ ≤ ‖g‖/2`)
  replaces the Neumann series for an exact inverse and the contraction of
  Section 6.4. The first step uses the outer solver only.
* **Smoothness** of the solution, which the manuscript takes from classical
  interior parabolic regularity, is proved by difference quotients and the
  reused interior Schauder estimate, in each chart.
* **The two ends `x = 0, 1`.** A radial function that is smooth on a chart is a
  smooth function of `x` up to the end, by Whitney's theorem on even functions
  with a parameter.

The inner mismatch is `O(√θ)` (`θ` the inner radius in the momentum
coordinate) instead of the power of the manuscript; any positive power
suffices.

### The compact operator in the two charts

The compact operator is a product of two shifted Laplacians of the sphere `S²³`,

```lean
theorem Calabi.Radial.sixteen_Aop (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) (hx : x ∈ Icc (0 : ℝ) 1) :
    16 * Aop f x = LSd 18 (LSd 18 f) x - 112 * LSd 18 f x + 2880 * f x
```

(`16 A = (Δ_S - 40) (Δ_S - 72)`, `Δ_S f = 4 x (1 - x) f″ + (36 - 48 x) f′`), and
in the two flat charts `x = |z|²`, `z ∈ ℝ¹⁸`, and `x = 1 - |w|²`, `w ∈ ℝ⁶`, it
is the operator `chartOp` (`sixteen_Aop_chart0`, `sixteen_Aop_chart1`):
`(1 - |z|²)²` times the flat bilaplacian plus terms of order at most three.
This is the form of Lemma 2.2 that lets the outer problem be treated on flat
spaces. `lowBound_lowOp` (`ChartJets`) bounds the terms of order at most three
by the jets of order at most three.

### The linear solvers on a flat space

**The forward problem** (`FlatZero`, `WindowEstimate`, `OuterEstimate`,
`OuterGap`, `ForwardBlock`; Lemmas 4.4 and 4.5 of the manuscript on `ℝᵈ`).
For `u_t + a Δ² u = f`, `u(0) = 0`, with a coefficient that equals one outside
a ball:

* `Calabi.FlatZero.exists_zero_data_jets`: a classical solution exists on
  `[0, R]`, `R ≤ 1/4`, with finite parabolic Hölder norms of `Dʲu`, `j ≤ 4`, and
  `u_t` down to the initial time; it is radial for radial data and real for a
  real source. The reused existence theorem bounds the fourth derivatives only
  away from the initial time; the gap is closed with the solution of the
  constant-coefficient problem with the same source
  (`constant_fourth_estimate`) and uniqueness.
* `outer_estimate`: for a scale `s` and a time `R ≤ (a₁ inf s)⁴ / C`, the
  jets on the boxes of size `a₁ s` are bounded by the weighted norm of the
  source, with a constant that does not depend on `R` (Lemma 4.4).
* `outer_lower_small`: the jets of order at most three are small,
  `(ε + C_ε η)` times the same bound, `η = R / (a₁ inf s)⁴` ((4.16)).
* `outer_gap_small`: with a larger Hölder exponent for the source, all spatial
  jets are small in the smaller exponent ((4.17)). The main theorem uses this
  in the box-free form `WJ.gap` (`RealSolvers`); `OuterGap.lean` itself is not in
  the import closure of `Calabi.Main`.
* `Calabi.Weighted.exists_forward_solution`: the same in the box-free form
  below, for a time-independent coefficient and a `1`-Lipschitz scale
  `s_min ≤ s ≤ s_max ≤ 16`.

**Real functions on `[-T, 0)`** (`Extension`, `RealSolvers`).
`exists_forward_real` is the forward block for a real source on the interval
that ends at the singular time; `exists_ancient_real` is the reused ancient
inverse `OAI.FlatSimilarity.exact_weighted_inverse` on `ℝ¹⁸ × (-∞, 0)` for a
real radial source on `[-T, 0)` with a weighted two-point bound for the scale
`σ`, with its exact norm converted into weighted bounds for the jets.

### Weighted bounds without boxes

(`TwoPoint`, `TwoPointJets`, `TwoPointMore`, `WindowConvert`.)
`WH α a s Ω w M f` says `|f| ≤ M s^w` and
`|f(P) - f(Q)| ≤ M s(P)^{w-α} d(P, Q)^α` for `d(P, Q) ≤ a s(P)`; `WJ` is the
same for the jets `Dʲu` with the weights `w - j`. Sums, products, cut-offs
(`WJ.smul`), the commutator of `D⁴` with a cut-off in terms of the jets of
order at most three (`commutator_WH`), comparison of scales, interpolation
between Hölder exponents (`WH.interp`), composition with Lipschitz maps
(`WH.comp_map`), and the translation to and from the boxes of the reused
library (`yBound_of_WH`, `WJ_of_xBound`) and of the forward problem
(`sSource_of_WH`, `sCoeff_of_WH`, `WJ_of_sJet`). The scale
`σ = (|z|² + √(-t))^{1/2}` is `1`-Lipschitz for the parabolic distance
(`abs_sigma_sub_le`).

### Lemma 6.2

**In the momentum coordinate** (`ProfileJets`, `Osc`, `ProfileOsc`,
`CutoffOsc`, `ResidualOsc`, `FrozenOsc`, `OuterOsc`). With `ς = x + √(-t) = σ²`,
`Osc T n M c cx ct` says `|c| ≤ M ςⁿ`, `|c_x| ≤ M ς^{n-1}`, `|c_t| ≤ M ς^{n-2}` on
`[-T, 0) × [0, 1]`, and `UOsc n c` that this holds with a constant independent
of the cut-off radius `λ` and of `T ≤ min(λ², 1)`:

* `hfun_jet_decay`, `profile_jet_decay`: `|h^{(k)}(y)| ≤ C (1+y)^{-1-k}` and
  `|G^{(k+1)}(y)| ≤ C (1+y)^{-3-k}`, from the smoothness of `G(u^{-1/2})` at
  `u = 0`;
* `tower_Fss`: `∂ₓʲF` has order `-1-j`, with time derivative
  `ρ^{-3-j} G^{(j+1)}(x/ρ)/2`; `tower_Flam`: the same for `F_λ = χ(x/λ) F`
  (Leibniz rule `Tower.mul`);
* `uosc_AFlam`: `A F_λ` has order `-3` (`A F_λ = Osc(σ⁻⁶)`);
* `uosc_Elam`, `uosc_Ein`, `Elam_eq_Ein`, `Elam_eq_zero`: the residual
  `E_λ = (F_λ)_t + b_λ² A F_λ` has order `-3`, equals a function of order `-2`
  for `x < λ` and vanishes for `x > 2λ` ((6.6));
* `uosc_Pmis`, `uosc_cmis`: the differences between the coefficients of
  `P_λ` and of the flat linearized operator have the orders `1` and `-1`;
  `two_x_G_AhatF` identifies the flat potential with the one of the reused
  inverse;
* `blam_mem`: `min(1, inf G) ≤ b_λ ≤ max(1, sup G)` ((6.1));
* `frozen_bounds`, `bdiff_small`: for `ρ ≤ x`, `|G(x/ρ) - c| ≤ C (−t)/x²` with
  the corresponding bounds for the derivatives, so that the multiplier of the
  outer problem can be frozen at the singular time.

**In the charts** (`OscChart`, `ProfileChart`, `ChartMaps`, `TwoCharts`,
`RayBounds`, `Coefficients`). `OscE.toWH`: a function of order `n` in the
momentum coordinate has, in the chart `x = |z|²`, a weighted two-point bound of
weight `2n` for the scale `σ`. `B0 α T v M g` is the two-chart bound of a
quantity of order zero (weight `v` for `σ` in the chart at `x = 0`, constant
scale in the chart at `x = 1`); `coef_bounds` gives it for `b_λ`, `c_λ`,
`A F_λ`, `v∗` (weights `0`, `-4`, `-6`, `2`), uniformly in `λ` and
`T ≤ min(λ², 1)`, and `elam_bound` for the residual.

### The approximate right inverse (Lemma 6.3)

The unknown is a pair `(U⁰, U⁰ₜ, U¹, U¹ₜ)` of chart functions with their time
derivatives (`PairSpace`: `Pair`, `Reg`, the norms `XJ`, `XT` of the jets and of
the time derivatives with the weight `w = -2 + 4γ`).

* `exists_localized` (`LocalSolve`): a cut-off times a zero-data solution in a
  chart, with the three error terms (terms of order at most three, jets of
  order at most three, commutator with the cut-off) small on a short interval;
* `outer_chart1` (`OuterOne`), `outer_chart0` (`SigmaTheta`, `OuterZero`,
  `OuterZeroBlock`): the outer blocks in the two charts, uniformly in the inner
  radius `θ` and in `T ≤ η θ²`; `outer_pair` (`OuterPair`): together they solve
  `P_λ U = g + err` for a source that vanishes for `x ≤ θ`;
* `inner_block`, `inner_pair` (`InnerBlock`): `U = χ_b D̂(χ_i g)` with the reused
  ancient inverse, `P_λ U = χ_i g + J + err`, where `J` is the commutator and
  `err = O(√θ)`;
* `approx_inverse` (`ApproxInverse`): for a source `g` with the two-chart bound
  `F` of weight `w - 4` there is a pair `U` with `‖U‖_X ≤ C_S F` and
  `‖g - P_λ U‖_Y ≤ F/2`. The commutator `J` cancels exactly between the inner
  and the outer part.

### The iteration (Lemma 6.4 and Section 6.4)

* `newton_iteration` (`Newton`): for abstract bound predicates, an approximate
  right inverse and a nonlinearity that is Lipschitz with constant `C_N e` on
  the ball of radius `e`, the scheme `u_{n+1} = u_n + S(r_n)` has residuals
  `≤ ε₁ (3/4)ⁿ` and increments `≤ C_S ε₁ (3/4)ⁿ`, and stays in the ball;
* `first_step` (`FirstStep`): the starting point, from the outer solver applied
  to `-(1 - χ(x/(2θ))) E_λ`; the residual `χ(x/(2θ)) E_λ` is small because of
  its weight;
* `pairLim_spec` (`PairLimit`): the limit of a sequence of pairs with
  geometrically decaying increments is a pair with the same bounds, and the
  values, time derivatives and the operator `A` converge pointwise;
* `exists_correction` (`Iteration`): for every small `e` and short `T` there is
  a pair `U` with `‖U‖_X ≤ e` and `P_λ U + N_λ(U) = -E_λ` on
  `(-T, 0) × [0, 1]`.

### Smoothness of the solution

The pair of `exists_correction` has four spatial derivatives and one time
derivative with Hölder bounds. `chart_smooth` (`JointSmooth`) shows that a
solution of this regularity of `h_t + (1 + v h)² chartOp(h)/16 = 0` on an open
set of a chart is smooth in space and time:

* `interior_real` (`InteriorReal`, `ParabolicBox`): the reused interior Schauder
  estimate for real functions on a small cylinder;
* `Sm α Ω k g` (`SmoothClass`, `SmoothOps`, `SmoothBase`, `Compose`,
  `JointClass`): local classes of functions whose spatial jets of order at most
  `k` are Hölder continuous, with sums, products, the operators of the chart
  and composition with smooth maps;
* `Sm.diffquot` (`DiffQuot`, `DiffQuotStep`): if `u ∈ Sm 4` solves
  `u_t + a Δ²u = f` with `a, f ∈ Sm 1`, then every `∂_e u ∈ Sm 4`: the
  difference quotients satisfy an equation of the same form and form a Cauchy
  sequence by the dyadic identity `dq h - dq (h/2) = (h/4) dq (h/2) (dq (h/2))`;
* `chart_space_smooth` (`Commute`, `Ladder`): all spatial derivatives, by
  induction; `chart_time_smooth`, `JS.contDiffOn`, `chart_smooth`
  (`JointSmooth`): all mixed derivatives, from the equation.

In the chart at `x = 1` the solution is the chart function `U¹`
(`chart1_smooth`). In the chart at `x = 0` it is `F_λ + U⁰ + U¹ ∘ Ψ`, where `Ψ`
maps the chart to the other one on their overlap (`Transfer`, `ChartSymmetry`:
`chartOp_transfer`, by rotation invariance and a Taylor polynomial of order
four); `chart0_equation`, `chart0_smooth` (`ChartPieces`, `ChartFlow`).

### The solution in the momentum coordinate

* `whitney_chart` (`Whitney`): a function that is smooth on
  `(-T, 0) × {|z|² < R}` and even along a ray is a smooth function of
  `(t, |z|²)` on `(-T, 0) × [0, R)`;
* `Hsol_smooth`, `Hsol_eqn` (`Solution`): `H = F_λ + V` is smooth on
  `(-T, 0) × [0, 1]` and solves `H_t + (1 + v∗ H)² A H = 0` there;
* `kop_diff_formula` (`KopBound`): `K(f + V) - K(f)` in terms of the Euler
  operators of the two chart functions; `kop_point`, `valOf_point`,
  `localizedCorrection` (`Assembly`): the bounds of Proposition 6.1.

```sh
python3 scripts/build_parallel.py Calabi.Correction.Assembly --jobs 3
python3 scripts/run_lean.py audit/FlatZeroAxioms.lean
python3 scripts/run_lean.py audit/WeightedAxioms.lean
python3 scripts/run_lean.py audit/BlockAxioms.lean
python3 scripts/run_lean.py audit/InverseAxioms.lean
python3 scripts/run_lean.py audit/MainAxioms.lean
```

## Earlier modules

The remaining source (`Calabi/Profile`, `Calabi/Certificate`,
`Calabi/Analysis/Energy.lean`, `Calabi/Analysis/DefectEnclosure.lean`,
`Integration`) implements dimension-seven identities, existence and uniqueness
of the tail root, quantitative transfer-error bounds, sound integer interval
operations, and the localized small-energy estimate; the integration target
specializes the OpenAI inverse to auxiliary dimension 18 and fixes the Hölder
exponents at 1/4 and 1/2. These modules belong to the first approach to the
profile, which followed the recorded ledger of the manuscript; they are not in
the import closure of `Calabi.Main`.

`Calabi/Certificate/KernelChecks.lean` checks ten inequalities for the recorded
rational ledger, two signs bracketing a tail root, and positivity of the 384-bit
integer scale. All thirteen checks compile and depend on no axioms.
These checks do not establish that the ledger was computed correctly or that it
encloses a solution of the profile ODE.

To prepare the fixed dependencies and build:

```sh
python3 scripts/fetch_dependencies.py
python3 scripts/vendor_openai.py
lake exe cache get
lake build Calabi
lake build Integration
lake env lean audit/Axioms.lean
lake env lean audit/IntegrationAxioms.lean
```

For a small independent check:

```sh
lake build Calabi.Certificate.KernelChecks
lake env lean audit/KernelAxioms.lean
```

`scripts/build_local.py` is an alternative that compiles one module at a time
using the same pinned Lean and local dependency paths. It records build times
and exit codes. `scripts/generate_recorded_bounds.py` regenerates the finite
arithmetic statements from the exact rational JSON in `githubPDF/verification`.

The extracted upstream files stay in the ignored `vendor` directory. Their
hashes are recorded in `vendor-lock.json`; extraction does not alter the source.
