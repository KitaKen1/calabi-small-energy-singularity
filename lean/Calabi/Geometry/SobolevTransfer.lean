import Calabi.Geometry.Dilation
import Calabi.Geometry.Potential

/-!
# The Sobolev constant of a radial metric

Section 7.3 of the manuscript, inequality (7.8): if the Fubini–Study metric
satisfies the Sobolev inequality with the constant `C₀`, then the metric of a
function `H` in the momentum coordinate satisfies it with the constant `Λ C₀`,

  `Λ = max (1, sup b, sup b⁻¹)`,   `b = 1 + v∗ H`

(`MomentumData.hasSobolevBound`). The proof transports a function `f` on `CP⁷`
by the map `Θ` that matches the momenta: `f ∘ Θ` is again a smooth function on
`CP⁷`, its `L^q` norms for the Fubini–Study measure are those of `f` for the
measure of the metric, and its Fubini–Study Dirichlet integral is at most `Λ`
times the Dirichlet integral of `f`.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Calabi.Geometry

open Calabi.Radial Momentum

/-! ### The chart and the lift of `θ` -/

theorem chart_zero_succ (Z : Aff) (j : Fin 7) : chart 0 Z j.succ = Z j := by
  simp [chart]

theorem contDiff_chart_zero : ContDiff ℝ ∞ (chart 0) := by
  refine contDiff_pi' fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [chart_zero_zero]
    exact contDiff_const
  · simp only [chart_zero_succ]
    exact ((EuclideanSpace.proj j : Aff →L[ℂ] ℂ).restrictScalars ℝ).contDiff

/-- The lift of `θ` to homogeneous coordinates. -/
noncomputable def Theta (a : ℝ → ℝ) (v : Hom) : Hom :=
  fun i => if i = 0 then v 0 else ((Real.exp (a (xi v) / 2) : ℝ) : ℂ) * v i

theorem Theta_chart (a : ℝ → ℝ) (Z : Aff) : Theta a (chart 0 Z) = chart 0 (theta a Z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Theta, chart_zero_zero]
  · rw [chart_zero_succ]
    simp only [Theta, Fin.succ_ne_zero, if_false, chart_zero_succ, xi_chart_zero]
    rfl

theorem Theta_smul (a : ℝ → ℝ) {c : ℂ} (hc : c ≠ 0) (v : Hom) :
    Theta a (c • v) = c • Theta a v := by
  funext i
  by_cases hi : i = 0
  · simp [Theta, hi]
  · simp only [Theta, hi, if_false, xi_smul hc, Pi.smul_apply, smul_eq_mul]
    ring

theorem Theta_ne_zero (a : ℝ → ℝ) {v : Hom} (hv : v ≠ 0) : Theta a v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrFun h i
  by_cases h0 : i = 0
  · simpa [Theta, h0] using hi
  · simp only [Theta, h0, if_false, Pi.zero_apply] at hi
    have he : ((Real.exp (a (xi v) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    exact (mul_eq_zero.1 hi).resolve_left he

theorem contDiffOn_Theta {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a (Icc 0 1)) :
    ContDiffOn ℝ ∞ (Theta a) {v : Hom | v ≠ 0} := by
  refine contDiffOn_pi' fun i => ?_
  by_cases hi : i = 0
  · have h : ContDiffOn ℝ ∞ (fun v : Hom => v 0) {v : Hom | v ≠ 0} :=
      (contDiff_apply ℝ ℂ (0 : Fin 8)).contDiffOn
    refine h.congr fun v _ => ?_
    simp [Theta, hi]
  · have h1 : ContDiffOn ℝ ∞ (fun v : Hom => a (xi v)) {v : Hom | v ≠ 0} :=
      ha.comp contDiffOn_xi fun v _ => xi_mem v
    have h2 : ContDiffOn ℝ ∞ (fun v : Hom => Real.exp (a (xi v) / 2)) {v : Hom | v ≠ 0} :=
      (h1.div_const 2).exp
    have h3 : ContDiffOn ℝ ∞ (fun v : Hom => ((Real.exp (a (xi v) / 2) : ℝ) : ℂ))
        {v : Hom | v ≠ 0} := Complex.ofRealCLM.contDiff.comp_contDiffOn h2
    have h4 : ContDiffOn ℝ ∞ (fun v : Hom => ((Real.exp (a (xi v) / 2) : ℝ) : ℂ) * v i)
        {v : Hom | v ≠ 0} := h3.mul (contDiff_apply ℝ ℂ i).contDiffOn
    refine h4.congr fun v _ => ?_
    simp [Theta, hi]

theorem isSmoothCP_Theta {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a (Icc 0 1)) {f : Hom → ℝ}
    (hf : IsSmoothCP f) : IsSmoothCP fun v => f (Theta a v) := by
  refine ⟨?_, fun c v hc => ?_⟩
  · exact hf.smooth.comp (contDiffOn_Theta ha) fun v hv => Theta_ne_zero a hv
  · show f (Theta a (c • v)) = f (Theta a v)
    rw [Theta_smul a hc]
    exact hf.invariant c _ hc

theorem contDiff_comp_chart {f : Hom → ℝ} (hf : IsSmoothCP f) :
    ContDiff ℝ ∞ fun Z : Aff => f (chart 0 Z) :=
  hf.smooth.comp_contDiff contDiff_chart_zero fun Z => chart_ne_zero 0 Z

/-! ### Continuity of the Fubini–Study gradient norm -/

theorem continuous_dz {G : Aff → ℝ} (hG : ContDiff ℝ 1 G) (j : Fin 7) :
    Continuous fun Z => dz G Z j := by
  have h1 : Continuous fun Z => fderiv ℝ G Z := hG.continuous_fderiv one_ne_zero
  have e1 : Continuous fun Z => fderiv ℝ G Z (EuclideanSpace.single j (1 : ℂ)) :=
    h1.clm_apply continuous_const
  have e2 : Continuous fun Z => fderiv ℝ G Z (EuclideanSpace.single j Complex.I) :=
    h1.clm_apply continuous_const
  unfold dz
  exact ((Complex.continuous_ofReal.comp e1).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp e2))).div_const 2

theorem continuous_gradSq_fubiniStudy {G : Aff → ℝ} (hG : ContDiff ℝ 1 G) :
    Continuous fun Z => gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) G Z := by
  have hform : (fun Z => gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) G Z)
      = fun Z : Aff => 2 * ((1 * (1 + ‖Z‖ ^ 2)⁻¹)⁻¹ * ∑ j, ‖dz G Z j‖ ^ 2
        - 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) / ((1 * (1 + ‖Z‖ ^ 2)⁻¹)
          * (1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2))
          * ‖pdot (dz G Z) Z‖ ^ 2) := by
    funext Z
    have hα0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ := by positivity
    have hαβ0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2 := by
      have e : 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2
          = 1 / (1 + ‖Z‖ ^ 2) ^ 2 := by
        field_simp
        ring
      rw [e]
      positivity
    rw [gradSq_rank_one (gmat_log 1 Z) hα0 hαβ0]
    rfl
  rw [hform]
  have hn : Continuous fun Z : Aff => ‖Z‖ ^ 2 := (continuous_norm.pow 2)
  have hs : Continuous fun Z : Aff => 1 + ‖Z‖ ^ 2 := continuous_const.add hn
  have hs0 : ∀ Z : Aff, 1 + ‖Z‖ ^ 2 ≠ 0 := fun Z => by positivity
  have hα : Continuous fun Z : Aff => 1 * (1 + ‖Z‖ ^ 2)⁻¹ := continuous_const.mul (hs.inv₀ hs0)
  have hβ : Continuous fun Z : Aff => 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) :=
    continuous_const.mul (continuous_const.div (hs.pow 2) fun Z => pow_ne_zero 2 (hs0 Z))
  have hα0 : ∀ Z : Aff, 1 * (1 + ‖Z‖ ^ 2)⁻¹ ≠ 0 := fun Z => by positivity
  have hden : ∀ Z : Aff, (1 * (1 + ‖Z‖ ^ 2)⁻¹)
      * (1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2) ≠ 0 := by
    intro Z
    have e : 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2
        = 1 / (1 + ‖Z‖ ^ 2) ^ 2 := by
      field_simp
      ring
    rw [e]
    positivity
  have hsum : Continuous fun Z : Aff => ∑ j, ‖dz G Z j‖ ^ 2 :=
    continuous_finsetSum _ fun j _ => (continuous_dz hG j).norm.pow 2
  have hp : Continuous fun Z : Aff => pdot (dz G Z) Z := by
    unfold pdot
    exact continuous_finsetSum _ fun j _ =>
      (continuous_dz hG j).mul ((EuclideanSpace.proj j : Aff →L[ℂ] ℂ).continuous)
  exact continuous_const.mul (((hα.inv₀ hα0).mul hsum).sub
    ((hβ.div (hα.mul (hα.add (hβ.mul hn))) hden).mul (hp.norm.pow 2)))

/-! ### Two facts on `L^p` norms -/

theorem eLpNorm_two_sq {μ : Measure Aff} {g : Aff → ℝ} (hg : AEStronglyMeasurable g μ) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ Z, ‖g Z‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := μ) (p := 2) two_ne_zero hg
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  rw [← h, ENNReal.rpow_two]

theorem eLpNorm_comp_of_lintegral {μ μ₀ : Measure Aff} {θ : Aff → Aff}
    (h : ∀ g : Aff → ENNReal, ∫⁻ W, g W ∂μ = ∫⁻ Z, g (θ Z) ∂μ₀) {G : Aff → ℝ}
    (hG : Continuous G) (hθ : Continuous θ) {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm G p μ = eLpNorm (fun Z => G (θ Z)) p μ₀ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (f := fun Z => G (θ Z))
      (hG.comp hθ).aestronglyMeasurable, h]

/-! ### The transfer -/

namespace MomentumData

variable {H a xq φ : ℝ → ℝ} (M : MomentumData H a xq φ)
  (hQ : ∀ x ∈ Ico (0 : ℝ) 1, xq (x * Real.exp (a x) / (1 - x)) = x)

include M hQ

theorem surj_of_inverse : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ q, 0 < q ∧ xq q = x := fun x hx =>
  ⟨x * Real.exp (a x) / (1 - x), div_pos (mul_pos hx.1 (Real.exp_pos _)) (sub_pos.2 hx.2),
    hQ x ⟨hx.1.le, hx.2⟩⟩

theorem continuous_theta : Continuous (theta a) :=
  continuous_iff_continuousAt.2 fun Z => (M.hasFDerivAt_theta Z).continuousAt

/-- `θ` pushes the normalized Fubini–Study measure to the normalized measure of
the metric. -/
theorem lintegral_nu (g : Aff → ENNReal) :
    ∫⁻ W, g W ∂(nu (fun V : Aff => φ (‖V‖ ^ 2)))
      = ∫⁻ Z, g (theta a Z) ∂(nu (fun V : Aff => 1 * Real.log (1 + ‖V‖ ^ 2))) := by
  have hsurj := M.surj_of_inverse hQ
  have hdet0 : (fun Z : Aff => ENNReal.ofReal (detg (fun V : Aff => 1 * Real.log (1 + ‖V‖ ^ 2)) Z))
      = fun Z : Aff => ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) := by
    funext Z
    rw [detg_fubiniStudy]
  have hmeas0 : AEMeasurable (fun Z : Aff => ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹)) volume := by
    have hc : Continuous fun Z : Aff => ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹ :=
      ((continuous_const.add (continuous_norm.pow 2)).pow 8).inv₀ fun Z : Aff =>
        (pow_pos (by positivity : (0 : ℝ) < 1 + ‖Z‖ ^ 2) 8).ne'
    exact hc.measurable.ennreal_ofReal.aemeasurable
  have hmeas1 : AEMeasurable
      (fun Z : Aff => ENNReal.ofReal (detg (fun V : Aff => φ (‖V‖ ^ 2)) Z)) volume :=
    (M.integrable_detg hsurj).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hvol1 := M.volMeasure_univ hsurj
  have hvol0 : volMeasure (fun V : Aff => 1 * Real.log (1 + ‖V‖ ^ 2)) univ
      = volume (Metric.ball (0 : Aff) 1) := by
    rw [← hvol1]
    unfold volMeasure
    rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, hdet0]
    have h := M.lintegral_theta hQ (fun _ => 1)
    simp only [mul_one] at h
    exact h.symm
  unfold nu
  rw [hvol1, hvol0, lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  unfold volMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume hmeas1
      (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top), hdet0,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume hmeas0
      (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top)]
  exact M.lintegral_theta hQ g

/-- **Inequality (7.8)**: the Sobolev constant of the metric is at most `Λ`
times the Sobolev constant of the Fubini–Study metric. -/
theorem hasSobolevBound (ha : ContDiffOn ℝ ∞ a (Icc 0 1)) {Λ C₀ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x ∈ Icc (0 : ℝ) 1, bfun H x ≤ Λ ∧ (bfun H x)⁻¹ ≤ Λ) (hC₀ : 0 < C₀)
    (hFS : HasSobolevBound (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) C₀) :
    HasSobolevBound (fun W : Aff => φ (‖W‖ ^ 2)) (Λ * C₀) := by
  intro f hf
  have hΛ0 : 0 < Λ := by linarith
  have hFc := contDiff_comp_chart hf
  have hFcont : Continuous fun Z : Aff => f (chart 0 Z) := hFc.continuous
  have hθc := M.continuous_theta hQ
  have htr := M.lintegral_nu hQ
  have hf' := isSmoothCP_Theta ha hf
  have hFS' := hFS (fun v => f (Theta a v)) hf'
  have hcomp : (fun Z : Aff => (fun v => f (Theta a v)) (chart 0 Z))
      = fun Z : Aff => (fun W : Aff => f (chart 0 W)) (theta a Z) := by
    funext Z
    show f (Theta a (chart 0 Z)) = f (chart 0 (theta a Z))
    rw [Theta_chart]
  have hG1 : ContDiff ℝ 1 fun Z : Aff => (fun v => f (Theta a v)) (chart 0 Z) :=
    (contDiff_comp_chart hf').of_le (by simp)
  rw [hcomp] at hFS' hG1
  -- the norms of `f`
  have h73 : ((7 : ENNReal) / 3) ≠ 0 := by simp
  have h73' : ((7 : ENNReal) / 3) ≠ ⊤ := by
    simp [ENNReal.div_eq_top]
  have e73 := eLpNorm_comp_of_lintegral htr hFcont hθc h73 h73'
  have e2 := eLpNorm_comp_of_lintegral htr hFcont hθc (two_ne_zero) (ENNReal.ofNat_ne_top)
  rw [← e73, ← e2] at hFS'
  -- the Dirichlet integrals
  have hgrad : eLpNorm (fun Z => Real.sqrt (gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2))
        (fun W => (fun W : Aff => f (chart 0 W)) (theta a W)) Z)) 2
        (nu (fun V : Aff => 1 * Real.log (1 + ‖V‖ ^ 2))) ^ 2
      ≤ ENNReal.ofReal Λ * eLpNorm (fun Z => Real.sqrt (gradSq (fun W : Aff => φ (‖W‖ ^ 2))
        (fun W : Aff => f (chart 0 W)) Z)) 2 (nu (fun V : Aff => φ (‖V‖ ^ 2))) ^ 2 := by
    by_cases hmeas : AEStronglyMeasurable (fun Z => Real.sqrt (gradSq
        (fun W : Aff => φ (‖W‖ ^ 2)) (fun W : Aff => f (chart 0 W)) Z))
        (nu (fun V : Aff => φ (‖V‖ ^ 2)))
    · have hmeas0 : AEStronglyMeasurable (fun Z => Real.sqrt (gradSq
          (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2))
          (fun W => (fun W : Aff => f (chart 0 W)) (theta a W)) Z))
          (nu (fun V : Aff => 1 * Real.log (1 + ‖V‖ ^ 2))) :=
        (Real.continuous_sqrt.comp (continuous_gradSq_fubiniStudy hG1)).aestronglyMeasurable
      rw [eLpNorm_two_sq hmeas0, eLpNorm_two_sq hmeas, htr, ← lintegral_const_mul']
      · refine lintegral_mono fun Z => ?_
        have hdiff : DifferentiableAt ℝ (fun W : Aff => f (chart 0 W)) (theta a Z) :=
          (hFc.differentiable (by simp)).differentiableAt
        have hle := M.gradSq_theta_le hQ hΛ1 hΛ Z hdiff
        have hqθ : (0 : ℝ) ≤ ‖theta a Z‖ ^ 2 := sq_nonneg _
        have hg1 := M.gmat_eq (theta a Z)
        have hnn1 : 0 ≤ gradSq (fun W : Aff => φ (‖W‖ ^ 2)) (fun W : Aff => f (chart 0 W))
            (theta a Z) :=
          gradSq_nonneg hg1 (M.f1_pos hqθ) (by
            have h := M.f1_add hqθ
            have h3 := M.f3_pos hqθ
            linarith)
        have hnn0 : 0 ≤ gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2))
            (fun W => (fun W : Aff => f (chart 0 W)) (theta a W)) Z := by
          have hα0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ := by positivity
          have hαβ0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹
              + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2 := by
            have e : 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2
                = 1 / (1 + ‖Z‖ ^ 2) ^ 2 := by
              field_simp
              ring
            rw [e]
            positivity
          exact gradSq_nonneg (gmat_log 1 Z) hα0 hαβ0
        have esq : ∀ x : ℝ, 0 ≤ x → ‖Real.sqrt x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal x := by
          intro x hx
          rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg x),
            ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg x) (by norm_num), Real.rpow_two,
            Real.sq_sqrt hx]
        rw [esq _ hnn0, esq _ hnn1, ← ENNReal.ofReal_mul hΛ0.le]
        exact ENNReal.ofReal_le_ofReal hle
      · exact ENNReal.ofReal_ne_top
    · rw [eLpNorm_of_not_aestronglyMeasurable hmeas]
      have h : ENNReal.ofReal Λ * (⊤ : ENNReal) ^ 2 = ⊤ := by
        rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.2 hΛ0).ne'
      rw [h]
      exact le_top
  -- the combination
  have h1Λ : (1 : ENNReal) ≤ ENNReal.ofReal Λ := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hΛ1
  refine hFS'.trans ?_
  rw [mul_comm Λ C₀, ENNReal.ofReal_mul hC₀.le, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [mul_add]
  refine add_le_add hgrad ?_
  calc eLpNorm (fun Z => f (chart 0 Z)) 2 (nu (fun V : Aff => φ (‖V‖ ^ 2))) ^ 2
      = 1 * eLpNorm (fun Z => f (chart 0 Z)) 2 (nu (fun V : Aff => φ (‖V‖ ^ 2))) ^ 2 :=
        (one_mul _).symm
    _ ≤ ENNReal.ofReal Λ * eLpNorm (fun Z => f (chart 0 Z)) 2
        (nu (fun V : Aff => φ (‖V‖ ^ 2))) ^ 2 := mul_le_mul' h1Λ le_rfl

end MomentumData

end Calabi.Geometry
