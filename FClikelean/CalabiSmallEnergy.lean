/- Proposed Formal Conjectures style statement. Not an upstream FC submission.
The only holes below are the two intended theorem statements.
Pinned completed proof source (Lean 4.34.1):
https://github.com/KitaKen1/calabi-small-energy-singularity/blob/b9465fa781c8cf12697e29a8d666dc43b79d2b8b/lean/FCSolution.lean
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The statement of the main theorem on `CP⁷`

This file contains definitions and statements only.

`CP⁷` is described by homogeneous coordinates `v ∈ ℂ⁸ ∖ {0}` and by its eight
affine charts `chart j : ℂ⁷ → ℂ⁸ ∖ {0}`. The affine coordinate space `ℂ⁷` is
`EuclideanSpace ℂ (Fin 7)`, so that `‖Z‖² = ∑ |Z_i|²` and `U(7)` is the group
of complex linear isometries.

* A smooth real function on `CP⁷` is a smooth function on `ℂ⁸ ∖ {0}` that is
  invariant under `v ↦ c v`, `c ≠ 0` (`IsSmoothCP`).
* The Kähler form `ω_FS + i∂∂̄F` has the local potential
  `pot F j = log (1 + |Z|²) + F ∘ chart j` on the `j`-th chart. It is positive
  when the complex Hessian `levi` of every `pot F j` is positive definite
  (`IsKahlerPotential`).
* On a chart, for `ω = i∂∂̄u`: `gmat u` is the matrix `(u_{j k̄})`, `scal u` is
  the scalar curvature `S = tr_ω Ric(ω) = -g^{j k̄} ∂_j ∂_k̄ log det g` (so that
  the Fubini–Study metric has `S = 56`), `nu u` is the normalized volume
  measure `ω⁷ / ∫ ω⁷`, and `gradSq u f = 2 g^{j k̄} f_j f_k̄` is `|∇f|²` for the
  Riemannian metric `g(X, Y) = ω(X, JY)`.
* The complex derivatives are expressed by real Fréchet derivatives on `ℂ⁷`:
  `∂_j ∂_k̄ u` is the sesquilinear form `levi u` evaluated on coordinate
  vectors.

Scalar curvature, measures and norms are written on the first chart
`chart 0`, whose complement is a hyperplane: a set of measure zero with dense
complement. The point `o` of the theorem is the origin `Z = 0` of that chart,
fixed by the action of `U(7)`.

`MainTheorem` is Theorem 1.1 of the manuscript, with the maximal existence
interval expressed by the blow-up (1.5) of the scalar curvature at `o`: a
smooth Calabi flow that extends the constructed one beyond `T` would have
bounded scalar curvature at `o` near `T`. Identifying the constructed flow
with every smooth flow from the same initial metric needs in addition the
uniqueness of smooth Calabi flows, which is not part of this statement.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Calabi.Geometry

/-- Affine coordinates on a chart of `CP⁷`. -/
abbrev Aff : Type := EuclideanSpace ℂ (Fin 7)

/-- Homogeneous coordinates on `CP⁷`. -/
abbrev Hom : Type := Fin 8 → ℂ

/-- The `j`-th affine chart: the homogeneous coordinate `j` is one. -/
def chart (j : Fin 8) (Z : Aff) : Hom := Fin.insertNth (α := fun _ => ℂ) j 1 (Z : Fin 7 → ℂ)

/-- A smooth real function on `CP⁷`, in homogeneous coordinates. -/
structure IsSmoothCP (F : Hom → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ F {v | v ≠ 0}
  invariant : ∀ (c : ℂ) (v : Hom), c ≠ 0 → F (c • v) = F v

/-- Invariance under `U(7)`, which acts on the first chart and fixes its
origin. -/
def IsU7Invariant (F : Hom → ℝ) : Prop :=
  ∀ (U : Aff ≃ₗᵢ[ℂ] Aff) (Z : Aff), F (chart 0 (U Z)) = F (chart 0 Z)

/-! ### Kähler metrics on a chart -/

/-- The real Hessian `D²u(Z)(a, b)`. -/
noncomputable def hess (u : Aff → ℝ) (Z a b : Aff) : ℝ := iteratedFDeriv ℝ 2 u Z ![a, b]

/-- The complex Hessian `∑ u_{j k̄} a_j conj(b_k)` of a real function. -/
noncomputable def levi (u : Aff → ℝ) (Z a b : Aff) : ℂ :=
  (((hess u Z a b + hess u Z (Complex.I • a) (Complex.I • b) : ℝ) : ℂ)
    + Complex.I * ((hess u Z a (Complex.I • b) - hess u Z (Complex.I • a) b : ℝ) : ℂ)) / 4

/-- The matrix `(u_{j k̄})` of the metric `ω = i∂∂̄u`. -/
noncomputable def gmat (u : Aff → ℝ) (Z : Aff) : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.of fun j k => levi u Z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)

/-- `det (u_{j k̄})`. -/
noncomputable def detg (u : Aff → ℝ) (Z : Aff) : ℝ := (gmat u Z).det.re

/-- The scalar curvature `S = tr_ω Ric(ω) = -g^{j k̄} ∂_j ∂_k̄ log det g` of
`ω = i∂∂̄u`. -/
noncomputable def scal (u : Aff → ℝ) (Z : Aff) : ℝ :=
  -((gmat u Z)⁻¹ * gmat (fun W => Real.log (detg u W)) Z).trace.re

/-- `∂f/∂z_j`. -/
noncomputable def dz (f : Aff → ℝ) (Z : Aff) (j : Fin 7) : ℂ :=
  (((fderiv ℝ f Z (EuclideanSpace.single j 1) : ℝ) : ℂ)
    - Complex.I * ((fderiv ℝ f Z (EuclideanSpace.single j Complex.I) : ℝ) : ℂ)) / 2

/-- `|∇f|² = 2 g^{j k̄} f_j f_k̄` for the Riemannian metric of `ω = i∂∂̄u`. -/
noncomputable def gradSq (u f : Aff → ℝ) (Z : Aff) : ℝ :=
  2 * (∑ j, ∑ k, (gmat u Z)⁻¹ k j * dz f Z j * star (dz f Z k)).re

/-- The volume measure of `ω = i∂∂̄u` on the chart, up to a constant factor. -/
noncomputable def volMeasure (u : Aff → ℝ) : Measure Aff :=
  volume.withDensity fun Z => ENNReal.ofReal (detg u Z)

/-- The normalized volume measure `ν_ω = ω⁷ / ∫ ω⁷`. -/
noncomputable def nu (u : Aff → ℝ) : Measure Aff := (volMeasure u univ)⁻¹ • volMeasure u

/-! ### Metrics in the Fubini–Study class and the Calabi flow -/

/-- The local potential of `ω_FS + i∂∂̄F` on the `j`-th chart. -/
noncomputable def pot (F : Hom → ℝ) (j : Fin 8) (Z : Aff) : ℝ :=
  Real.log (1 + ‖Z‖ ^ 2) + F (chart j Z)

/-- `F` is a smooth function on `CP⁷` with `ω_FS + i∂∂̄F > 0`. -/
structure IsKahlerPotential (F : Hom → ℝ) : Prop where
  smoothCP : IsSmoothCP F
  pos : ∀ (j : Fin 8) (Z a : Aff), a ≠ 0 → 0 < (levi (pot F j) Z a a).re

/-- A smooth Calabi flow `∂_t φ = S(ω_φ) - 56` on `[0, T)` in the Fubini–Study
class of `CP⁷`. -/
structure IsCalabiFlow (T : ℝ) (F : ℝ → Hom → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × Hom => F p.1 p.2) (Ico 0 T ×ˢ {v | v ≠ 0})
  kahler : ∀ t ∈ Ico 0 T, IsKahlerPotential (F t)
  flow : ∀ t ∈ Ico 0 T, ∀ Z : Aff,
    HasDerivWithinAt (fun s => F s (chart 0 Z)) (scal (pot (F t) 0) Z - 56) (Ico 0 T) t

/-- The Sobolev inequality (1.1) of the manuscript for the metric `ω = i∂∂̄u`
with the constant `C`: for every smooth function `f` on `CP⁷`,
`‖f‖²_{L^{7/3}} ≤ C (‖∇f‖²_{L²} + ‖f‖²_{L²})` with respect to `ν_ω`. -/
def HasSobolevBound (u : Aff → ℝ) (C : ℝ) : Prop :=
  ∀ f : Hom → ℝ, IsSmoothCP f →
    eLpNorm (fun Z => f (chart 0 Z)) (7 / 3) (nu u) ^ 2 ≤
      ENNReal.ofReal C *
        (eLpNorm (fun Z => Real.sqrt (gradSq u (fun W => f (chart 0 W)) Z)) 2 (nu u) ^ 2
          + eLpNorm (fun Z => f (chart 0 Z)) 2 (nu u) ^ 2)

/-- **Theorem 1.1 of the manuscript.** There is a constant `CS` such that for
every `2 ≤ p < 7` and `ε, τ > 0` there is a smooth `U(7)`-invariant Calabi flow
on `[0, T)`, `T < τ`, in the Fubini–Study class of `CP⁷`, with

* initial potential smaller than `ε` in the uniform norm;
* `‖S - 56‖_{L^p(ν)} < ε` at every time;
* the Sobolev constant at most `CS` at every time;
* `S(o) ∼ a (T - t)^{-1/2}` at the origin `o` of the first chart, `a > 0`. -/
def MainTheorem : Prop :=
  ∃ CS : ℝ, ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (F : ℝ → Hom → ℝ), 0 < T ∧ T < τ ∧ IsCalabiFlow T F ∧
      (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
      (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
      (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
        eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) (ENNReal.ofReal p) (nu (pot (F t) 0))
          < ENNReal.ofReal ε ∧
        HasSobolevBound (pot (F t) 0) CS) ∧
      ∃ a : ℝ, 0 < a ∧
        Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

/-- The case `p = 2` of the main theorem: arbitrarily small Calabi energy
`∫ (S - 56)² dν` throughout the flow, one Sobolev constant, and blow-up of the
scalar curvature in finite time. -/
def MainTheoremEnergy : Prop :=
  ∃ CS : ℝ, ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (F : ℝ → Hom → ℝ), 0 < T ∧ T < τ ∧ IsCalabiFlow T F ∧
      (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
      (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
      (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
        eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) 2 (nu (pot (F t) 0)) < ENNReal.ofReal ε ∧
        HasSobolevBound (pot (F t) 0) CS) ∧
      ∃ a : ℝ, 0 < a ∧
        Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

theorem MainTheorem.energy (h : MainTheorem) : MainTheoremEnergy := by
  obtain ⟨CS, hCS⟩ := h
  refine ⟨CS, fun ε hε τ hτ => ?_⟩
  have h2 := hCS 2 le_rfl (by norm_num) ε hε τ hτ
  simpa using h2

end Calabi.Geometry


open Set Filter MeasureTheory
open scoped Topology ENNReal
open Calabi.Geometry

namespace CalabiFC

theorem small_energy_singularity :
    ∃ CS : ℝ, ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
      ∃ (T : ℝ) (F : ℝ → Hom → ℝ) (η : ℝ),
        0 < T ∧ T < τ ∧ 0 < η ∧ η < ε ∧ IsCalabiFlow T F ∧
        (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
        (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
        (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
          eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) (ENNReal.ofReal p)
            (nu (pot (F t) 0)) ≤ ENNReal.ofReal η ∧
          HasSobolevBound (pot (F t) 0) CS) ∧
        ∃ a : ℝ, 0 < a ∧
          Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a) := by
  sorry

theorem small_calabi_energy : Calabi.Geometry.MainTheoremEnergy := by
  sorry

end CalabiFC
