import Calabi.Geometry.Momentum
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The volume measure in the momentum coordinate

For a radial potential described by `MomentumData`, the volume density on the
chart is `det (u_{j k̄}) = (x / q)⁶ dx/dq`, so that, in polar coordinates,
`det (u_{j k̄}) q⁶ dq = x⁶ dx`: the pushforward of the volume measure under the
momentum coordinate is a constant multiple of `x⁶ dx` on `(0, 1)`, whatever the
metric (`integral_radial`). Consequently

* `volMeasure_univ`: the total volume is the volume of the unit ball of `ℂ⁷`;
* `isProbabilityMeasure_nu`: the normalized measure `ν` is a probability
  measure;
* `eLpNorm_scal`: the Calabi energy is `∫ (S - 56)² dν = ∫₀¹ K(H)² 7x⁶ dx`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Calabi.Geometry

open Calabi.Radial Momentum

theorem finrank_aff : Module.finrank ℝ Aff = 14 := by
  have h := Module.finrank_mul_finrank ℝ ℂ Aff
  rw [Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin] at h
  omega

namespace MomentumData

variable {H a xq φ : ℝ → ℝ} (M : MomentumData H a xq φ)
  (hsurj : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ q, 0 < q ∧ xq q = x)

include M hsurj

/-- **Integration in the momentum coordinate.** -/
theorem integral_radial {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    Integrable (fun Z : Aff => g (xq (‖Z‖ ^ 2)) * detg (fun W : Aff => φ (‖W‖ ^ 2)) Z) ∧
      ∫ Z : Aff, g (xq (‖Z‖ ^ 2)) * detg (fun W : Aff => φ (‖W‖ ^ 2)) Z
        = volume.real (Metric.ball (0 : Aff) 1) * ∫ x in (0 : ℝ)..1, g x * (7 * x ^ 6) := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun r : ℝ =>
      g (xq (r ^ 2)) * (f1 a (xq (r ^ 2)) ^ 6 * f3 H a (xq (r ^ 2))) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun x : ℝ => 1 / 2 * (g x * x ^ 6) := ⟨_, rfl⟩
  have hfun : (fun Z : Aff => g (xq (‖Z‖ ^ 2)) * detg (fun W : Aff => φ (‖W‖ ^ 2)) Z)
      = fun Z : Aff => F ‖Z‖ := by
    funext Z
    rw [M.detg_eq, hF]
  have hρd : ∀ r ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun r : ℝ => xq (r ^ 2))
      (f3 H a (xq (r ^ 2)) * (2 * r)) (Ioi 0) r := by
    intro r _
    have h2 : HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioi 0) r := by
      have h := (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Ioi 0)
      simpa using h
    exact HasDerivWithinAt.comp (h := fun r : ℝ => r ^ 2) r (M.dx (r ^ 2) (sq_nonneg r)) h2
      fun s _ => mem_Ici.2 (sq_nonneg s)
  have hρinj : InjOn (fun r : ℝ => xq (r ^ 2)) (Ioi 0) := by
    intro r₁ h₁ r₂ h₂ h
    have hx : xq (r₁ ^ 2) = xq (r₂ ^ 2) := h
    have e1 := M.rel (r₁ ^ 2) (sq_nonneg _)
    have e2 := M.rel (r₂ ^ 2) (sq_nonneg _)
    rw [hx] at e1
    have h1x : (1 - xq (r₂ ^ 2)) ≠ 0 := (sub_pos.2 (M.mem _ (sq_nonneg _)).2).ne'
    have hsq : r₁ ^ 2 = r₂ ^ 2 := mul_right_cancel₀ h1x (e1.trans e2.symm)
    exact (sq_eq_sq₀ (mem_Ioi.1 h₁).le (mem_Ioi.1 h₂).le).1 hsq
  have himg : (fun r : ℝ => xq (r ^ 2)) '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hm := M.mem (r ^ 2) (sq_nonneg r)
      refine ⟨lt_of_le_of_ne hm.1 fun h0 => ?_, hm.2⟩
      have e := M.rel (r ^ 2) (sq_nonneg r)
      have h0' : xq (r ^ 2) = 0 := h0.symm
      rw [h0'] at e
      simp at e
      exact (mem_Ioi.1 hr).ne' e
    · intro hx
      obtain ⟨q, hq, rfl⟩ := hsurj x hx
      refine ⟨Real.sqrt q, Real.sqrt_pos.2 hq, ?_⟩
      show xq (Real.sqrt q ^ 2) = xq q
      rw [Real.sq_sqrt hq.le]
  have hGint : IntegrableOn G (Ioo 0 1) := by
    have hc : ContinuousOn G (Icc 0 1) := by
      rw [hG]
      exact continuousOn_const.mul (hg.mul (continuousOn_id.pow 6))
    exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint : ∀ r ∈ Ioi (0 : ℝ),
      r ^ 13 • F r = |f3 H a (xq (r ^ 2)) * (2 * r)| • G (xq (r ^ 2)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hq := M.q_mul_f1 (q := r ^ 2) (sq_nonneg r)
    have hf3 := M.f3_pos (q := r ^ 2) (sq_nonneg r)
    rw [abs_of_pos (mul_pos hf3 (by positivity)), hF, hG]
    simp only [smul_eq_mul]
    have e : xq (r ^ 2) ^ 6 = (r ^ 2 * f1 a (xq (r ^ 2))) ^ 6 := by rw [hq]
    rw [e]
    ring
  have hIntOn : IntegrableOn (fun r : ℝ => r ^ 13 • F r) (Ioi 0) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hρd hρinj
      G).1 (by rw [himg]; exact hGint)
    exact h.congr_fun (fun r hr => (hint r hr).symm) measurableSet_Ioi
  have hval : ∫ r in Ioi (0 : ℝ), r ^ 13 • F r = ∫ x in Ioo (0 : ℝ) 1, G x := by
    rw [setIntegral_congr_fun measurableSet_Ioi hint,
      ← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hρd hρinj G, himg]
  have hdim : Module.finrank ℝ Aff - 1 = 13 := by rw [finrank_aff]
  constructor
  · rw [hfun]
    refine (integrable_fun_norm_addHaar (volume : Measure Aff) (f := F)).2 ?_
    rw [hdim]
    exact hIntOn
  · rw [hfun, integral_fun_norm_addHaar (volume : Measure Aff) F, hdim, hval, finrank_aff,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have e : ∫ x in Ioo (0 : ℝ) 1, g x * (7 * x ^ 6) = 14 * ∫ x in Ioo (0 : ℝ) 1, G x := by
      rw [← integral_const_mul, hG]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show g x * (7 * x ^ 6) = 14 * (1 / 2 * (g x * x ^ 6))
      ring
    rw [e]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

theorem integrable_detg : Integrable (fun Z : Aff => detg (fun W : Aff => φ (‖W‖ ^ 2)) Z) := by
  have h := (M.integral_radial hsurj (g := fun _ => 1) continuousOn_const).1
  simpa using h

theorem integral_detg :
    ∫ Z : Aff, detg (fun W : Aff => φ (‖W‖ ^ 2)) Z = volume.real (Metric.ball (0 : Aff) 1) := by
  have h := (M.integral_radial hsurj (g := fun _ => 1) continuousOn_const).2
  have e : ∫ x in (0 : ℝ)..1, (1 : ℝ) * (7 * x ^ 6) = 1 := by
    simp only [one_mul]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [e, mul_one] at h
  simpa using h

/-- The total volume does not depend on the metric. -/
theorem volMeasure_univ :
    volMeasure (fun W : Aff => φ (‖W‖ ^ 2)) univ = volume (Metric.ball (0 : Aff) 1) := by
  unfold volMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (M.integrable_detg hsurj)
      (Eventually.of_forall fun Z => (M.detg_pos Z).le), M.integral_detg hsurj]
  exact ENNReal.ofReal_toReal measure_ball_lt_top.ne

theorem isProbabilityMeasure_nu : IsProbabilityMeasure (nu (fun W : Aff => φ (‖W‖ ^ 2))) := by
  constructor
  unfold nu
  rw [Measure.smul_apply, smul_eq_mul, M.volMeasure_univ hsurj]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

theorem continuous_xq : Continuous fun Z : Aff => xq (‖Z‖ ^ 2) := by
  refine continuous_iff_continuousAt.2 fun Z => ?_
  have h : ContinuousWithinAt xq (Ici 0) (‖Z‖ ^ 2) :=
    (M.dx (‖Z‖ ^ 2) (sq_nonneg _)).continuousWithinAt
  exact h.tendsto.comp (tendsto_norm_sq Z)

/-- **The Calabi energy in the momentum coordinate.** -/
theorem eLpNorm_scal (hK : ContinuousOn (Kop H) (Icc 0 1)) :
    eLpNorm (fun Z : Aff => scal (fun W : Aff => φ (‖W‖ ^ 2)) Z - 56) 2
        (nu (fun W : Aff => φ (‖W‖ ^ 2))) ^ (2 : ℝ)
      = ENNReal.ofReal (∫ x in (0 : ℝ)..1, Kop H x ^ 2 * (7 * x ^ 6)) := by
  have hI := M.integral_radial hsurj (g := fun x => Kop H x ^ 2) (hK.pow 2)
  have hc0 : volume (Metric.ball (0 : Aff) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hct : volume (Metric.ball (0 : Aff) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hfun : (fun Z : Aff => scal (fun W : Aff => φ (‖W‖ ^ 2)) Z - 56)
      = fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)) := by
    funext Z
    rw [M.scal_eq]
    ring
  have hcont : Continuous fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)) :=
    (hK.comp_continuous (M.continuous_xq hsurj) fun Z => M.mapsTo (sq_nonneg ‖Z‖)).neg
  rw [hfun]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)))
    (μ := nu (fun W : Aff => φ (‖W‖ ^ 2))) (p := 2) two_ne_zero hcont.aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  rw [h]
  unfold nu
  rw [lintegral_smul_measure, M.volMeasure_univ hsurj]
  unfold volMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume
    ((M.integrable_detg hsurj).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top)]
  have hpt : ∀ Z : Aff,
      ((fun Z : Aff => ENNReal.ofReal (detg (fun W : Aff => φ (‖W‖ ^ 2)) Z))
        * fun Z : Aff => ‖-Kop H (xq (‖Z‖ ^ 2))‖ₑ ^ (2 : ℝ)) Z
      = ENNReal.ofReal (Kop H (xq (‖Z‖ ^ 2)) ^ 2 * detg (fun W : Aff => φ (‖W‖ ^ 2)) Z) := by
    intro Z
    rw [Pi.mul_apply, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      ← ENNReal.ofReal_mul (M.detg_pos Z).le]
    congr 1
    rw [Real.rpow_two, abs_neg, sq_abs]
    ring
  have e2 : ∀ E : ℝ, ENNReal.ofReal (volume.real (Metric.ball (0 : Aff) 1) * E)
      = volume (Metric.ball (0 : Aff) 1) * ENNReal.ofReal E := by
    intro E
    rw [ENNReal.ofReal_mul measureReal_nonneg]
    congr 1
    exact ENNReal.ofReal_toReal hct
  rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hI.1
    (Eventually.of_forall fun Z => mul_nonneg (sq_nonneg _) (M.detg_pos Z).le), hI.2, e2,
    smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- **The `L^p` norm of `S - 56` in the momentum coordinate**, `p > 0`. -/
theorem eLpNorm_scal_rpow (hK : ContinuousOn (Kop H) (Icc 0 1)) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun Z : Aff => scal (fun W : Aff => φ (‖W‖ ^ 2)) Z - 56) (ENNReal.ofReal p)
        (nu (fun W : Aff => φ (‖W‖ ^ 2))) ^ p
      = ENNReal.ofReal (∫ x in (0 : ℝ)..1, |Kop H x| ^ p * (7 * x ^ 6)) := by
  have hI := M.integral_radial hsurj (g := fun x => |Kop H x| ^ p)
    (hK.abs.rpow_const fun _ _ => Or.inr hp.le)
  have hc0 : volume (Metric.ball (0 : Aff) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hct : volume (Metric.ball (0 : Aff) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hfun : (fun Z : Aff => scal (fun W : Aff => φ (‖W‖ ^ 2)) Z - 56)
      = fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)) := by
    funext Z
    rw [M.scal_eq]
    ring
  have hcont : Continuous fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)) :=
    (hK.comp_continuous (M.continuous_xq hsurj) fun Z => M.mapsTo (sq_nonneg ‖Z‖)).neg
  rw [hfun]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := fun Z : Aff => -Kop H (xq (‖Z‖ ^ 2)))
    (μ := nu (fun W : Aff => φ (‖W‖ ^ 2))) (p := p.toNNReal) (Real.toNNReal_pos.2 hp).ne'
    hcont.aestronglyMeasurable
  rw [Real.coe_toNNReal p hp.le] at h
  have hofReal : ENNReal.ofReal p = (p.toNNReal : ℝ≥0∞) := rfl
  rw [hofReal, h]
  unfold nu
  rw [lintegral_smul_measure, M.volMeasure_univ hsurj]
  unfold volMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume
    ((M.integrable_detg hsurj).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top)]
  have hpt : ∀ Z : Aff,
      ((fun Z : Aff => ENNReal.ofReal (detg (fun W : Aff => φ (‖W‖ ^ 2)) Z))
        * fun Z : Aff => ‖-Kop H (xq (‖Z‖ ^ 2))‖ₑ ^ p) Z
      = ENNReal.ofReal (|Kop H (xq (‖Z‖ ^ 2))| ^ p * detg (fun W : Aff => φ (‖W‖ ^ 2)) Z) := by
    intro Z
    rw [Pi.mul_apply, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
      ← ENNReal.ofReal_mul (M.detg_pos Z).le]
    congr 1
    rw [abs_neg]
    ring
  have e2 : ∀ E : ℝ, ENNReal.ofReal (volume.real (Metric.ball (0 : Aff) 1) * E)
      = volume (Metric.ball (0 : Aff) 1) * ENNReal.ofReal E := by
    intro E
    rw [ENNReal.ofReal_mul measureReal_nonneg]
    congr 1
    exact ENNReal.ofReal_toReal hct
  rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hI.1
    (Eventually.of_forall fun Z =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (M.detg_pos Z).le), hI.2, e2,
    smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end MomentumData

end Calabi.Geometry
