import Calabi.Geometry.RadialPotential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Fubini–Study metric: a check of the definitions

With the definitions of `Calabi.Geometry.Statement`, the potential
`log (1 + ‖Z‖²)` of the Fubini–Study metric of `CP⁷` satisfies:

* `detg_fubiniStudy`: `det (u_{j k̄}) = (1 + ‖Z‖²)⁻⁸`;
* `scal_fubiniStudy`: the scalar curvature is `56`;
* `isKahlerPotential_zero`: the metric is positive on every chart, so that
  `F = 0` is a Kähler potential of the class.

This fixes the conventions of the statement of the main theorem: `S(ω_FS) = 56`
for the affine potential `log (1 + |Z|²)`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

/-- `∑ Z_k conj(Z_k) = ‖Z‖²`. -/
theorem dot_star (Z : Aff) :
    (fun k => Z k) ⬝ᵥ (fun j => star (Z j)) = ((‖Z‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The derivatives of `c log (1 + q)` at `q = ‖Z‖²`. -/
theorem log_radial_data (c : ℝ) (Z : Aff) :
    (∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2),
        HasDerivWithinAt (fun q : ℝ => c * Real.log (1 + q)) (c * (1 + q)⁻¹) (Ici 0) q) ∧
      HasDerivWithinAt (fun q : ℝ => c * (1 + q)⁻¹) (c * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) (Ici 0)
        (‖Z‖ ^ 2) := by
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  constructor
  · have hc : ContinuousAt (fun q : ℝ => 1 + q) (‖Z‖ ^ 2) :=
      (continuous_const.add continuous_id).continuousAt
    filter_upwards [nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds hpos))] with q hq
    have h := (Real.hasDerivAt_log hq.ne').comp q ((hasDerivAt_id' q).const_add 1)
    have h' : HasDerivAt (fun q : ℝ => Real.log (1 + q)) ((1 + q)⁻¹) q :=
      h.congr_deriv (mul_one _)
    exact (h'.const_mul c).hasDerivWithinAt
  · have h := ((hasDerivAt_id' (‖Z‖ ^ 2)).const_add 1).fun_inv hpos.ne'
    exact (h.const_mul c).hasDerivWithinAt

/-- The metric matrix of `c log (1 + ‖Z‖²)`. -/
theorem gmat_log (c : ℝ) (Z : Aff) :
    gmat (fun W : Aff => c * Real.log (1 + ‖W‖ ^ 2)) Z
      = ((c * (1 + ‖Z‖ ^ 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        + ((c * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) : ℝ) : ℂ)
          • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k) := by
  have h := gmat_radial (φ := fun q : ℝ => c * Real.log (1 + q))
    (φ1 := fun q : ℝ => c * (1 + q)⁻¹) (φ2 := c * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) (Z := Z)
    (log_radial_data c Z).1 (log_radial_data c Z).2
  exact h

theorem gmat_log_smul (c : ℝ) (Z : Aff) :
    gmat (fun W : Aff => c * Real.log (1 + ‖W‖ ^ 2)) Z
      = (c : ℂ) • gmat (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z := by
  rw [gmat_log, gmat_log]
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The potential of the Fubini–Study metric on every chart. -/
theorem pot_zero (j : Fin 8) :
    pot (fun _ => 0) j = fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2) := by
  funext W
  simp [pot]

/-- `det (u_{j k̄}) = (1 + ‖Z‖²)⁻⁸` for the Fubini–Study metric. -/
theorem det_gmat_fubiniStudy (Z : Aff) :
    (gmat (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z).det
      = (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹ : ℝ) := by
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  have hne : ((1 + ‖Z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have ha : (((1 : ℝ) * (1 + ‖Z‖ ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (1 : ℝ) * (1 + ‖Z‖ ^ 2)⁻¹ ≠ 0 := by positivity
    exact_mod_cast this
  rw [gmat_log, det_rank_one ha, dot_star]
  push_cast
  push_cast at hne
  field_simp
  ring

theorem detg_fubiniStudy (Z : Aff) :
    detg (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z = ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹ := by
  unfold detg
  rw [det_gmat_fubiniStudy, Complex.ofReal_re]

/-- **The Fubini–Study metric has scalar curvature `56`.** -/
theorem scal_fubiniStudy (Z : Aff) : scal (pot (fun _ => 0) 0) Z = 56 := by
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  have hlog : (fun W : Aff => Real.log (detg (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) W))
      = fun W : Aff => (-8 : ℝ) * Real.log (1 + ‖W‖ ^ 2) := by
    funext W
    rw [detg_fubiniStudy, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hunit : IsUnit (gmat (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z).det := by
    rw [det_gmat_fubiniStudy, isUnit_iff_ne_zero]
    have : ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹ ≠ (0 : ℝ) := by positivity
    exact_mod_cast this
  unfold scal
  rw [pot_zero, hlog, gmat_log_smul (-8) Z, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hunit,
    Matrix.trace_smul, Matrix.trace_one]
  simp
  norm_num

/-- **The Fubini–Study metric is a Kähler metric**: `F = 0` is a Kähler
potential of the class. -/
theorem isKahlerPotential_zero : IsKahlerPotential (fun _ => 0) := by
  refine ⟨⟨contDiffOn_const, fun _ _ _ => rfl⟩, fun j Z a ha => ?_⟩
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hl := levi_radial (φ := fun q : ℝ => 1 * Real.log (1 + q))
    (φ1 := fun q : ℝ => 1 * (1 + q)⁻¹) (φ2 := 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) (Z := Z)
    (log_radial_data 1 Z).1 (log_radial_data 1 Z).2 a a
  rw [pot_zero, show levi (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z a a = _ from hl]
  have e1 : (inner ℂ a a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e2 : (inner ℂ Z a : ℂ) * inner ℂ a Z = ((‖(inner ℂ Z a : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm a Z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcs : ‖(inner ℂ Z a : ℂ)‖ ^ 2 ≤ ‖Z‖ ^ 2 * ‖a‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) Z a
    have h0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ := norm_nonneg _
    nlinarith [mul_nonneg (norm_nonneg Z) (norm_nonneg a)]
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re]
  have hq2 : 0 < (1 + ‖Z‖ ^ 2) ^ 2 := by positivity
  have key : 1 * (1 + ‖Z‖ ^ 2)⁻¹ * ‖a‖ ^ 2 + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖(inner ℂ Z a : ℂ)‖ ^ 2
      = ((1 + ‖Z‖ ^ 2) * ‖a‖ ^ 2 - ‖(inner ℂ Z a : ℂ)‖ ^ 2) / (1 + ‖Z‖ ^ 2) ^ 2 := by
    field_simp
    ring
  rw [key]
  refine div_pos ?_ hq2
  nlinarith [pow_pos ha0 2]

end Calabi.Geometry
