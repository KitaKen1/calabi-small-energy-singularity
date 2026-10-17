import Calabi.Geometry.Statement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Radial potentials on a chart

For a potential `u(Z) = φ(‖Z‖²)` on `ℂ⁷` (the derivatives of `φ` are taken within
`[0, ∞)`, so that the statements include the point `Z = 0`):

* `hess_radial`: `D²u(a, b) = 2 φ′ inner ℝ a b + 4 φ″ inner ℝ Z a inner ℝ Z b`;
* `levi_radial`: `∑ u_{j k̄} a_j conj(b_k) = φ′ inner ℂ b a + φ″ inner ℂ Z a inner ℂ b Z`;
* `gmat_radial`: `(u_{j k̄}) = φ′ 1 + φ″ (conj Z_j Z_k)`;
* `detg_radial`: `det (u_{j k̄}) = φ′⁶ (φ′ + ‖Z‖² φ″)`.

As a check of the definitions of `Calabi.Geometry.Statement`, the Fubini–Study
metric `φ = log (1 + q)` is a Kähler metric with scalar curvature `56`
(`isKahlerPotential_zero`, `scal_fubiniStudy`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

/-- The real inner product of `ℂ⁷` is the real part of the complex one. -/
theorem real_inner_eq_re (a b : Aff) : inner ℝ a b = (inner ℂ a b).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, RCLike.inner_apply]

theorem hasFDerivAt_norm_sq (W : Aff) :
    HasFDerivAt (fun W : Aff => ‖W‖ ^ 2) ((2 : ℝ) • innerSL ℝ W) W := by
  have h := (hasStrictFDerivAt_norm_sq W).hasFDerivAt
  convert h using 1
  ext y
  simp [two_smul]

/-- The derivative of a radial function. The derivative of the profile is taken
within `[0, ∞)`, where `‖W‖²` takes its values, so that the point `W = 0` is
included. -/
theorem hasFDerivAt_radial {φ : ℝ → ℝ} {φ' : ℝ} (W : Aff)
    (h : HasDerivWithinAt φ φ' (Ici 0) (‖W‖ ^ 2)) :
    HasFDerivAt (fun W : Aff => φ (‖W‖ ^ 2)) (φ' • ((2 : ℝ) • innerSL ℝ W)) W :=
  (h.comp_hasFDerivWithinAt W (hasFDerivAt_norm_sq W).hasFDerivWithinAt
    (fun V _ => mem_Ici.2 (sq_nonneg ‖V‖))).hasFDerivAt univ_mem

theorem tendsto_norm_sq (Z : Aff) :
    Tendsto (fun W : Aff => ‖W‖ ^ 2) (𝓝 Z) (𝓝[Ici 0] (‖Z‖ ^ 2)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hasFDerivAt_norm_sq Z).continuousAt (Eventually.of_forall fun W => mem_Ici.2 (sq_nonneg ‖W‖))

variable {φ φ1 : ℝ → ℝ} {φ2 : ℝ} {Z : Aff}

/-- The real Hessian of a radial function. -/
theorem hess_radial (h1 : ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : HasDerivWithinAt φ1 φ2 (Ici 0) (‖Z‖ ^ 2)) (a b : Aff) :
    hess (fun W : Aff => φ (‖W‖ ^ 2)) Z a b
      = 2 * φ1 (‖Z‖ ^ 2) * inner ℝ a b + 4 * φ2 * inner ℝ Z a * inner ℝ Z b := by
  unfold hess
  rw [iteratedFDeriv_two_apply]
  have hfd : fderiv ℝ (fun W : Aff => φ (‖W‖ ^ 2))
      =ᶠ[𝓝 Z] fun W => φ1 (‖W‖ ^ 2) • ((2 : ℝ) • innerSL ℝ W) := by
    filter_upwards [(tendsto_norm_sq Z).eventually h1] with W hW
    exact (hasFDerivAt_radial W hW).fderiv
  have hc : HasFDerivAt (fun W : Aff => φ1 (‖W‖ ^ 2)) (φ2 • ((2 : ℝ) • innerSL ℝ Z)) Z :=
    hasFDerivAt_radial Z h2
  have hl : HasFDerivAt (fun W : Aff => ((2 : ℝ) • innerSL ℝ W : Aff →L[ℝ] ℝ))
      ((2 : ℝ) • (innerSL ℝ : Aff →L[ℝ] Aff →L[ℝ] ℝ)) Z :=
    ((2 : ℝ) • (innerSL ℝ : Aff →L[ℝ] Aff →L[ℝ] ℝ)).hasFDerivAt
  have hprod := hc.smul hl
  have hfd2 : fderiv ℝ (fun W : Aff => φ1 (‖W‖ ^ 2) • ((2 : ℝ) • innerSL ℝ W)) Z = _ :=
    hprod.fderiv
  rw [hfd.fderiv_eq, hfd2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  erw [innerSL_apply_apply]
  ring

/-- The complex Hessian of a radial function. -/
theorem levi_radial (h1 : ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : HasDerivWithinAt φ1 φ2 (Ici 0) (‖Z‖ ^ 2)) (a b : Aff) :
    levi (fun W : Aff => φ (‖W‖ ^ 2)) Z a b
      = (φ1 (‖Z‖ ^ 2) : ℂ) * inner ℂ b a + (φ2 : ℂ) * (inner ℂ Z a * inner ℂ b Z) := by
  unfold levi
  rw [hess_radial h1 h2, hess_radial h1 h2, hess_radial h1 h2, hess_radial h1 h2]
  simp only [real_inner_eq_re, inner_smul_left, inner_smul_right, Complex.conj_I]
  rw [← inner_conj_symm b a, ← inner_conj_symm b Z]
  generalize (inner ℂ a b : ℂ) = s
  generalize (inner ℂ Z a : ℂ) = α
  generalize (inner ℂ Z b : ℂ) = β
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- The metric matrix of a radial potential. -/
theorem gmat_radial (h1 : ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : HasDerivWithinAt φ1 φ2 (Ici 0) (‖Z‖ ^ 2)) :
    gmat (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = (φ1 (‖Z‖ ^ 2) : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        + (φ2 : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k) := by
  ext j k
  simp only [gmat, Matrix.of_apply, levi_radial h1 h2, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_one, one_mul]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk]

/-- The determinant of `a 1 + b (w_j v_k)`. -/
theorem det_rank_one {a : ℂ} (ha : a ≠ 0) (b : ℂ) (w v : Fin 7 → ℂ) :
    (a • (1 : Matrix (Fin 7) (Fin 7) ℂ) + b • Matrix.vecMulVec w v).det
      = a ^ 6 * (a + b * (v ⬝ᵥ w)) := by
  have e : a • (1 : Matrix (Fin 7) (Fin 7) ℂ) + b • Matrix.vecMulVec w v
      = a • (1 + Matrix.replicateCol Unit ((b / a) • w) * Matrix.replicateRow Unit v) := by
    rw [← Matrix.vecMulVec_eq Unit]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Pi.smul_apply]
    field_simp
  rw [e, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin,
    dotProduct_smul, smul_eq_mul]
  field_simp

end Calabi.Geometry
