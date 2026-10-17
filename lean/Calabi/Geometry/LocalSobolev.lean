import Calabi.Geometry.ChartSwap
import Calabi.Geometry.SobolevTransfer
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The Sobolev inequality on the unit polydisc of the chart

On the closed unit polydisc `P = {|Z_k| ≤ 1}` of the chart `0` the
Fubini–Study metric is uniformly equivalent to the flat one. With a cut-off
function, the Gagliardo–Nirenberg–Sobolev inequality of Mathlib in real
dimension `14` (`1/2 - 1/14 = 3/7`) gives

  `‖1_P G‖_{L^{7/3}(ν)} ≤ C (‖∇G‖_{L²(ν)} + ‖G‖_{L²(ν)})`

for the normalized Fubini–Study measure `ν` (`local_sobolev`).
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace Calabi.Geometry

local notation "uFS" => (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2))

/-! ### The Fubini–Study volume against the Lebesgue measure -/

/-- The density of the Fubini–Study volume in the chart. -/
noncomputable def rho (Z : Aff) : ℝ := ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹

theorem rho_pos (Z : Aff) : 0 < rho Z := by
  unfold rho
  positivity

theorem rho_le_one (Z : Aff) : rho Z ≤ 1 := by
  unfold rho
  have h : (1 : ℝ) ≤ (1 + ‖Z‖ ^ 2) ^ 8 := one_le_pow₀ (by nlinarith [sq_nonneg ‖Z‖])
  exact inv_le_one_of_one_le₀ h

theorem rho_ge {Z : Aff} (hZ : ‖Z‖ ≤ 4) : ((17 : ℝ) ^ 8)⁻¹ ≤ rho Z := by
  unfold rho
  have h0 : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  have h1 : 1 + ‖Z‖ ^ 2 ≤ 17 := by nlinarith [norm_nonneg Z]
  have h2 : (1 + ‖Z‖ ^ 2) ^ 8 ≤ (17 : ℝ) ^ 8 := pow_le_pow_left₀ h0.le h1 8
  exact inv_anti₀ (pow_pos h0 8) h2

theorem volMeasure_fs :
    volMeasure uFS = (volume : Measure Aff).withDensity fun Z => ENNReal.ofReal (rho Z) := by
  unfold volMeasure
  congr 1
  funext Z
  rw [detg_fubiniStudy]
  rfl

theorem integrable_rho : Integrable rho (volume : Measure Aff) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Aff) (μ := (volume : Measure Aff))
    (r := 16) (by rw [finrank_aff]; norm_num)
  refine h.congr (Eventually.of_forall fun Z => ?_)
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  show (1 + ‖Z‖ ^ 2) ^ (-(16 : ℝ) / 2) = ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹
  rw [show (-(16 : ℝ) / 2) = -((8 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le,
    Real.rpow_natCast]

theorem volMeasure_fs_ne_top : volMeasure uFS univ ≠ ⊤ := by
  rw [volMeasure_fs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_rho
      (Eventually.of_forall fun Z => (rho_pos Z).le)]
  exact ENNReal.ofReal_ne_top

/-- On the ball of radius `4` the Lebesgue measure is at most `17⁸` times the
Fubini–Study volume. -/
theorem volume_inter_le {s : Set Aff} (hs : MeasurableSet s) :
    volume (s ∩ closedBall (0 : Aff) 4) ≤ ENNReal.ofReal (17 ^ 8) * volMeasure uFS s := by
  have hm : MeasurableSet (s ∩ closedBall (0 : Aff) 4) := hs.inter measurableSet_closedBall
  have h1 : ENNReal.ofReal ((17 ^ 8)⁻¹) * volume (s ∩ closedBall (0 : Aff) 4)
      ≤ volMeasure uFS s := by
    rw [volMeasure_fs, withDensity_apply _ hs, ← setLIntegral_const]
    calc ∫⁻ _ in s ∩ closedBall (0 : Aff) 4, ENNReal.ofReal ((17 ^ 8)⁻¹)
        ≤ ∫⁻ Z in s ∩ closedBall (0 : Aff) 4, ENNReal.ofReal (rho Z) :=
          setLIntegral_mono' hm fun Z hZ => ENNReal.ofReal_le_ofReal
            (rho_ge (by simpa using hZ.2))
      _ ≤ ∫⁻ Z in s, ENNReal.ofReal (rho Z) := lintegral_mono_set inter_subset_left
  calc volume (s ∩ closedBall (0 : Aff) 4)
      = ENNReal.ofReal (17 ^ 8) * (ENNReal.ofReal ((17 ^ 8)⁻¹)
        * volume (s ∩ closedBall (0 : Aff) 4)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (17 ^ 8) * volMeasure uFS s := mul_le_mul' le_rfl h1

theorem volMeasure_fs_ne_zero : volMeasure uFS univ ≠ 0 := by
  intro h0
  have h := volume_inter_le (s := univ) MeasurableSet.univ
  rw [h0, mul_zero, univ_inter] at h
  exact (Metric.measure_closedBall_pos (volume : Measure Aff) 0
    (by norm_num : (0 : ℝ) < 4)).ne' (nonpos_iff_eq_zero.1 h)

/-- The normalized Fubini–Study measure is at most a multiple of the Lebesgue
measure. -/
theorem nu_fs_le : nu uFS ≤ (volMeasure uFS univ)⁻¹ • (volume : Measure Aff) := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold nu
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul' le_rfl ?_
  rw [volMeasure_fs, withDensity_apply _ hs]
  calc ∫⁻ Z in s, ENNReal.ofReal (rho Z) ≤ ∫⁻ _ in s, 1 :=
        lintegral_mono fun Z => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (rho_le_one Z)
    _ = volume s := setLIntegral_one s

/-- On the ball of radius `4` the Lebesgue measure is at most a multiple of
the normalized Fubini–Study measure. -/
theorem volume_restrict_le : (volume : Measure Aff).restrict (closedBall (0 : Aff) 4)
    ≤ (ENNReal.ofReal (17 ^ 8) * volMeasure uFS univ) • nu uFS := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul]
  unfold nu
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc, ← mul_assoc (volMeasure uFS univ),
    ENNReal.mul_inv_cancel volMeasure_fs_ne_zero volMeasure_fs_ne_top, one_mul]
  exact volume_inter_le hs

/-! ### The Euclidean and the Fubini–Study gradients -/

/-- The Euclidean norm of the differential is at most `√2 |∇G|` for the
Fubini–Study metric. -/
theorem norm_fderiv_le (G : Aff → ℝ) (Z : Aff) :
    ‖fderiv ℝ G Z‖ ≤ Real.sqrt 2 * Real.sqrt (gradSq uFS G Z) := by
  have hpos := fubiniStudy_pos Z
  have hg := gmat_log 1 Z
  have hnn := gradSq_nonneg (F := G) hg hpos.1 hpos.2
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun a => ?_
  have h := sq_fderiv_le (F := G) hg hpos.1 hpos.2 a
  have hq : quad (1 * (1 + ‖Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z a ≤ ‖a‖ ^ 2 := by
    unfold quad
    have h1 : (1 : ℝ) * (1 + ‖Z‖ ^ 2)⁻¹ ≤ 1 := by
      rw [one_mul]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖Z‖])
    have h2 : (1 : ℝ) * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) ≤ 0 := by
      rw [one_mul]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    have h3 : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 h3, mul_nonpos_of_nonpos_of_nonneg h2 h4]
  have h5 : (fderiv ℝ G Z a) ^ 2 ≤ (Real.sqrt (2 * gradSq uFS G Z) * ‖a‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hnn)]
    nlinarith [mul_le_mul_of_nonneg_left hq hnn]
  rw [Real.norm_eq_abs]
  exact abs_le_of_sq_le_sq h5 (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-! ### The polydisc -/

/-- The closed unit polydisc of the chart. -/
def polydisc : Set Aff := {Z | ∀ k, ‖Z k‖ ≤ 1}

theorem polydisc_subset : polydisc ⊆ closedBall (0 : Aff) 3 := by
  intro Z hZ
  have h : ‖Z‖ ^ 2 ≤ 7 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ k, ‖Z k‖ ^ 2 ≤ ∑ _k : Fin 7, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by
            have h1 := hZ k
            nlinarith [norm_nonneg (Z k)]
      _ = 7 := by simp
  have h3 : ‖Z‖ ≤ 3 := by nlinarith [norm_nonneg Z]
  simpa using h3

theorem measurableSet_polydisc : MeasurableSet polydisc := by
  have h : polydisc = ⋂ k : Fin 7, {Z : Aff | ‖Z k‖ ≤ 1} := by
    ext Z
    simp [polydisc]
  rw [h]
  exact MeasurableSet.iInter fun k => (isClosed_le
    ((EuclideanSpace.proj k : Aff →L[ℂ] ℂ).continuous.norm) continuous_const).measurableSet

/-! ### The Gagliardo–Nirenberg–Sobolev inequality in real dimension `14` -/

theorem gns_aff : ∃ A : ℝ≥0, ∀ u : Aff → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
    eLpNorm u (7 / 3) (volume : Measure Aff)
      ≤ A * eLpNorm (fderiv ℝ u) 2 (volume : Measure Aff) := by
  refine ⟨SNormLESNormFDerivOfEqConst ℝ (volume : Measure Aff) ((2 : ℝ≥0) : ℝ),
    fun u hu hucs => ?_⟩
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq (μ := (volume : Measure Aff)) (F := ℝ) hu hucs
    (p := 2) (p' := 7 / 3) (by norm_num) (by rw [finrank_aff]; norm_num)
    (by rw [finrank_aff]; push_cast; norm_num)
  have e1 : ((7 / 3 : ℝ≥0) : ℝ≥0∞) = 7 / 3 := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  have e2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
  rw [e1, e2] at h
  exact h

/-! ### The local inequality -/

/-- **The Sobolev inequality on the unit polydisc**, for the normalized
Fubini–Study measure. -/
theorem local_sobolev : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ G : Aff → ℝ, ContDiff ℝ 1 G →
    eLpNorm (polydisc.indicator G) (7 / 3) (nu uFS)
      ≤ C * (eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
        + eLpNorm G 2 (nu uFS)) := by
  -- the cut-off
  obtain ⟨χ, hχ⟩ : ∃ χ : ContDiffBump (0 : Aff), χ.rIn = 3 ∧ χ.rOut = 4 :=
    ⟨⟨3, 4, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hχsmooth : ContDiff ℝ 1 (χ : Aff → ℝ) := (χ.contDiff (n := ⊤)).of_le (by simp)
  have hχcs : HasCompactSupport (χ : Aff → ℝ) := χ.hasCompactSupport
  obtain ⟨K, hK⟩ := (hχsmooth.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hχcs.fderiv ℝ)
  obtain ⟨A, hA⟩ := gns_aff
  -- the constants
  have hV0 := volMeasure_fs_ne_zero
  have hVt := volMeasure_fs_ne_top
  have hc0 : (volMeasure uFS univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hVt
  have hct : (volMeasure uFS univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hV0
  have hk0 : ENNReal.ofReal (17 ^ 8) * volMeasure uFS univ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hV0
  have hkt : ENNReal.ofReal (17 ^ 8) * volMeasure uFS univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ≥0∞,
      A₁ = (volMeasure uFS univ)⁻¹ ^ (1 / (7 / 3 : ℝ≥0∞)).toReal := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A₃ : ℝ≥0∞,
      A₃ = (ENNReal.ofReal (17 ^ 8) * volMeasure uFS univ) ^ (1 / (2 : ℝ≥0∞)).toReal :=
    ⟨_, rfl⟩
  have hA₁t : A₁ ≠ ⊤ := by
    rw [hA₁]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hct
  have hA₃t : A₃ ≠ ⊤ := by
    rw [hA₃]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hkt
  refine ⟨A₁ * ((A : ℝ≥0∞) * (A₃ * (‖Real.sqrt 2‖ₑ + ‖K‖ₑ))),
    ENNReal.mul_ne_top hA₁t (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top hA₃t (ENNReal.add_ne_top.2 ⟨enorm_ne_top, enorm_ne_top⟩))),
    fun G hG => ?_⟩
  -- the cut-off function `u = χ G`
  obtain ⟨u, hu⟩ : ∃ u : Aff → ℝ, u = fun W => χ W * G W := ⟨_, rfl⟩
  have huC : ContDiff ℝ 1 u := by
    rw [hu]
    exact hχsmooth.mul hG
  have hucs : HasCompactSupport u := by
    rw [hu]
    exact hχcs.mul_right
  -- `|1_P G| ≤ |u|`
  have hpt : ∀ Z, ‖polydisc.indicator G Z‖ ≤ ‖u Z‖ := by
    intro Z
    by_cases hZ : Z ∈ polydisc
    · have h1 : χ Z = 1 := χ.one_of_mem_closedBall (by rw [hχ.1]; exact polydisc_subset hZ)
      rw [indicator_of_mem hZ, hu]
      show ‖G Z‖ ≤ ‖χ Z * G Z‖
      rw [h1, one_mul]
    · rw [indicator_of_notMem hZ, norm_zero]
      exact norm_nonneg _
  -- the differential of `u`
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : Aff → ℝ, h₁ = fun W =>
      Real.sqrt 2 * Real.sqrt (gradSq uFS G W) + K * ‖G W‖ := ⟨_, rfl⟩
  have hfd : ∀ Z, ‖fderiv ℝ u Z‖ ≤ (closedBall (0 : Aff) 4).indicator h₁ Z := by
    intro Z
    by_cases hZ : Z ∈ closedBall (0 : Aff) 4
    · rw [indicator_of_mem hZ, hh₁]
      have hχd : DifferentiableAt ℝ (χ : Aff → ℝ) Z :=
        (hχsmooth.differentiable one_ne_zero).differentiableAt
      have hGd : DifferentiableAt ℝ G Z := (hG.differentiable one_ne_zero).differentiableAt
      have e : fderiv ℝ (fun W => χ W * G W) Z
          = χ Z • fderiv ℝ G Z + G Z • fderiv ℝ (χ : Aff → ℝ) Z :=
        (hχd.hasFDerivAt.mul hGd.hasFDerivAt).fderiv
      rw [hu, e]
      have hχ1 : |χ Z| ≤ 1 := by
        rw [abs_of_nonneg χ.nonneg]
        exact χ.le_one
      calc ‖χ Z • fderiv ℝ G Z + G Z • fderiv ℝ (χ : Aff → ℝ) Z‖
          ≤ ‖χ Z • fderiv ℝ G Z‖ + ‖G Z • fderiv ℝ (χ : Aff → ℝ) Z‖ := norm_add_le _ _
        _ = |χ Z| * ‖fderiv ℝ G Z‖ + ‖G Z‖ * ‖fderiv ℝ (χ : Aff → ℝ) Z‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs (χ Z)]
        _ ≤ 1 * (Real.sqrt 2 * Real.sqrt (gradSq uFS G Z)) + ‖G Z‖ * K :=
            add_le_add (mul_le_mul hχ1 (norm_fderiv_le G Z) (norm_nonneg _) zero_le_one)
              (mul_le_mul_of_nonneg_left (hK Z) (norm_nonneg _))
        _ = Real.sqrt 2 * Real.sqrt (gradSq uFS G Z) + K * ‖G Z‖ := by ring
    · rw [indicator_of_notMem hZ]
      have hts : Z ∉ tsupport u := by
        intro h
        apply hZ
        have h1 : tsupport (fun W => χ W * G W) ⊆ tsupport (χ : Aff → ℝ) :=
          tsupport_mul_subset_left
        rw [hu] at h
        have h2 := h1 h
        rw [χ.tsupport_eq, hχ.2] at h2
        exact h2
      rw [fderiv_of_notMem_tsupport ℝ hts, norm_zero]
  -- measurability
  have hGc : Continuous G := hG.continuous
  have hmeasP : AEStronglyMeasurable (polydisc.indicator G) (volume : Measure Aff) :=
    hGc.aestronglyMeasurable.indicator measurableSet_polydisc
  have hmeasfd : AEStronglyMeasurable (fderiv ℝ u) (volume : Measure Aff) :=
    (huC.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hgc : Continuous fun Z => Real.sqrt (gradSq uFS G Z) :=
    Real.continuous_sqrt.comp (continuous_gradSq_fubiniStudy hG)
  -- the `L²` norm of `h₁`
  have hh₁le : eLpNorm h₁ 2 (nu uFS)
      ≤ (‖Real.sqrt 2‖ₑ + ‖K‖ₑ) * (eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
        + eLpNorm G 2 (nu uFS)) := by
    have e : h₁ = (Real.sqrt 2 • fun Z => Real.sqrt (gradSq uFS G Z))
        + (K • fun Z => ‖G Z‖) := by
      rw [hh₁]
      rfl
    have hadd := eLpNorm_add_le (μ := nu uFS)
      (f := Real.sqrt 2 • fun Z => Real.sqrt (gradSq uFS G Z)) (g := K • fun Z => ‖G Z‖)
      (p := 2) (by norm_num)
    rw [eLpNorm_const_smul, eLpNorm_const_smul,
      eLpNorm_norm G hGc.aestronglyMeasurable] at hadd
    rw [e]
    refine hadd.trans ?_
    calc ‖Real.sqrt 2‖ₑ * eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
          + ‖K‖ₑ * eLpNorm G 2 (nu uFS)
        ≤ (‖Real.sqrt 2‖ₑ + ‖K‖ₑ) * eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
          + (‖Real.sqrt 2‖ₑ + ‖K‖ₑ) * eLpNorm G 2 (nu uFS) :=
          add_le_add (mul_le_mul' le_self_add le_rfl) (mul_le_mul' le_add_self le_rfl)
      _ = _ := (mul_add _ _ _).symm
  -- the chain of inequalities
  calc eLpNorm (polydisc.indicator G) (7 / 3) (nu uFS)
      ≤ eLpNorm (polydisc.indicator G) (7 / 3)
          ((volMeasure uFS univ)⁻¹ • (volume : Measure Aff)) := eLpNorm_mono_measure _ nu_fs_le
    _ = A₁ * eLpNorm (polydisc.indicator G) (7 / 3) (volume : Measure Aff) := by
        rw [eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul, hA₁]
    _ ≤ A₁ * eLpNorm u (7 / 3) (volume : Measure Aff) :=
        mul_le_mul' le_rfl (eLpNorm_mono hmeasP hpt)
    _ ≤ A₁ * ((A : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 2 (volume : Measure Aff)) :=
        mul_le_mul' le_rfl (hA u huC hucs)
    _ ≤ A₁ * ((A : ℝ≥0∞) * eLpNorm ((closedBall (0 : Aff) 4).indicator h₁) 2
          (volume : Measure Aff)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (eLpNorm_mono_real hmeasfd hfd))
    _ = A₁ * ((A : ℝ≥0∞) * eLpNorm h₁ 2
          ((volume : Measure Aff).restrict (closedBall (0 : Aff) 4))) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
    _ ≤ A₁ * ((A : ℝ≥0∞) * eLpNorm h₁ 2
          ((ENNReal.ofReal (17 ^ 8) * volMeasure uFS univ) • nu uFS)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (eLpNorm_mono_measure _ volume_restrict_le))
    _ = A₁ * ((A : ℝ≥0∞) * (A₃ * eLpNorm h₁ 2 (nu uFS))) := by
        rw [eLpNorm_smul_measure_of_ne_zero hk0, smul_eq_mul, hA₃]
    _ ≤ A₁ * ((A : ℝ≥0∞) * (A₃ * ((‖Real.sqrt 2‖ₑ + ‖K‖ₑ)
          * (eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
            + eLpNorm G 2 (nu uFS))))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hh₁le))
    _ = A₁ * ((A : ℝ≥0∞) * (A₃ * (‖Real.sqrt 2‖ₑ + ‖K‖ₑ)))
          * (eLpNorm (fun Z => Real.sqrt (gradSq uFS G Z)) 2 (nu uFS)
            + eLpNorm G 2 (nu uFS)) := by
        simp only [mul_assoc]

end Calabi.Geometry
