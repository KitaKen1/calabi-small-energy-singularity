import Calabi.Geometry.LocalSobolev
import Calabi.Geometry.Bridge

/-!
# The Sobolev inequality of the Fubini–Study metric of `CP⁷`

`CP⁷` is covered by the eight sets `{|v_j| = max_i |v_i|}`. In the chart `0`
they are the unit polydisc `P` and the sets `Q_m = {|Z_m| ≥ 1, |Z_k| ≤ |Z_m|}`,
and the exchange `τ_m` of the homogeneous coordinates `0` and `m + 1` maps
`Q_m` into `P`. Since `τ_m` is an isometry of the Fubini–Study metric, the
local inequality on `P` (`local_sobolev`) applies to each of the eight pieces:

* `hasSobolevBound_fubiniStudy`, `fubiniStudySobolev`: the inequality (1.1) of
  the manuscript for the Fubini–Study metric;
* `mainTheorem_of_localizedCorrection`: Theorem 1.1 of the manuscript, with
  Proposition 6.1 as the only hypothesis.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace Calabi.Geometry

open Calabi.Radial

local notation "uFS" => (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2))

/-! ### The invariance of the normalized measure -/

theorem continuous_rho : Continuous rho := by
  show Continuous fun Z : Aff => ((1 + ‖Z‖ ^ 2) ^ 8)⁻¹
  exact ((continuous_const.add (continuous_norm.pow 2)).pow 8).inv₀ fun Z : Aff =>
    (pow_pos (by positivity : (0 : ℝ) < 1 + ‖Z‖ ^ 2) 8).ne'

/-- `τ_m` preserves the normalized Fubini–Study measure. -/
theorem lintegral_tau_nu (m : Fin 7) (g : Aff → ℝ≥0∞) :
    ∫⁻ Z, g (tau m Z) ∂(nu uFS) = ∫⁻ W, g W ∂(nu uFS) := by
  have hmeas : AEMeasurable (fun Z : Aff => ENNReal.ofReal (rho Z)) volume :=
    continuous_rho.measurable.ennreal_ofReal.aemeasurable
  unfold nu
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  rw [volMeasure_fs,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume hmeas
      (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top),
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume hmeas
      (Eventually.of_forall fun Z => ENNReal.ofReal_lt_top)]
  exact lintegral_tau m g

theorem ae_coord_ne_zero (m : Fin 7) : ∀ᵐ Z ∂(nu uFS), Z m ≠ 0 := by
  rw [ae_iff]
  have e : {Z : Aff | ¬Z m ≠ 0} = {Z : Aff | Z m = 0} := by
    ext Z
    simp
  rw [e]
  have h := Measure.le_iff'.1 nu_fs_le {Z : Aff | Z m = 0}
  rw [Measure.smul_apply, measure_coord_zero, smul_zero] at h
  exact nonpos_iff_eq_zero.1 h

/-- Monotonicity of the `L^p` norms under `τ_m`. -/
theorem eLpNorm_le_of_tau {m : Fin 7} {h₁ h₂ : Aff → ℝ}
    (hm₁ : AEStronglyMeasurable h₁ (nu uFS)) (hm₂ : AEStronglyMeasurable h₂ (nu uFS))
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (h : ∀ Z : Aff, Z m ≠ 0 → ‖h₁ Z‖ ≤ ‖h₂ (tau m Z)‖) :
    eLpNorm h₁ p (nu uFS) ≤ eLpNorm h₂ p (nu uFS) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm₁,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm₂]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.2 ENNReal.toReal_nonneg)
  calc ∫⁻ Z, ‖h₁ Z‖ₑ ^ p.toReal ∂(nu uFS)
      ≤ ∫⁻ Z, ‖h₂ (tau m Z)‖ₑ ^ p.toReal ∂(nu uFS) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_coord_ne_zero m] with Z hZ
        exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.2 (h Z hZ)) ENNReal.toReal_nonneg
    _ = ∫⁻ W, ‖h₂ W‖ₑ ^ p.toReal ∂(nu uFS) :=
        lintegral_tau_nu m fun W => ‖h₂ W‖ₑ ^ p.toReal

/-! ### The exchange of two homogeneous coordinates -/

/-- The exchange of the homogeneous coordinates `0` and `m + 1`. -/
def swapHom (m : Fin 7) (v : Hom) : Hom := fun i => v (Equiv.swap 0 m.succ i)

theorem swapHom_smul (m : Fin 7) (c : ℂ) (v : Hom) :
    swapHom m (c • v) = c • swapHom m v := rfl

theorem swapHom_ne_zero (m : Fin 7) {v : Hom} (hv : v ≠ 0) : swapHom m v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrFun h (Equiv.swap 0 m.succ i)
  simpa [swapHom] using hi

theorem contDiff_swapHom (m : Fin 7) {n : WithTop ℕ∞} : ContDiff ℝ n (swapHom m) :=
  contDiff_pi' fun i => contDiff_apply ℝ ℂ (Equiv.swap 0 m.succ i)

theorem isSmoothCP_swap (m : Fin 7) {f : Hom → ℝ} (hf : IsSmoothCP f) :
    IsSmoothCP fun v => f (swapHom m v) := by
  refine ⟨?_, fun c v hc => ?_⟩
  · exact hf.smooth.comp (contDiff_swapHom m).contDiffOn fun v hv => swapHom_ne_zero m hv
  · show f (swapHom m (c • v)) = f (swapHom m v)
    rw [swapHom_smul]
    exact hf.invariant c _ hc

/-- In the chart `0` the exchange is the map `τ_m`. -/
theorem swapHom_chart {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) :
    swapHom m (chart 0 Z) = (Z m) • chart 0 (tau m Z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show chart 0 Z (Equiv.swap 0 m.succ 0) = Z m * chart 0 (tau m Z) 0
    rw [Equiv.swap_apply_left, chart_zero_succ, chart_zero_zero, mul_one]
  · show chart 0 Z (Equiv.swap 0 m.succ j.succ) = Z m * chart 0 (tau m Z) j.succ
    rw [chart_zero_succ]
    by_cases hj : j = m
    · rw [hj, Equiv.swap_apply_right, chart_zero_zero, tau_apply_self, mul_inv_cancel₀ hZ]
    · have h1 : (j.succ : Fin 8) ≠ 0 := Fin.succ_ne_zero j
      have h2 : (j.succ : Fin 8) ≠ m.succ := fun h => hj (Fin.succ_injective _ h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, chart_zero_succ, tau_apply_ne hj, ← mul_assoc,
        mul_inv_cancel₀ hZ, one_mul]

theorem comp_swap_chart {f : Hom → ℝ} (hf : IsSmoothCP f) {m : Fin 7} {Z : Aff}
    (hZ : Z m ≠ 0) : f (swapHom m (chart 0 Z)) = f (chart 0 (tau m Z)) := by
  rw [swapHom_chart hZ]
  exact hf.invariant _ _ hZ

/-! ### The covering -/

/-- The part of the chart where the coordinate `m` is the largest one and is
at least one. -/
def qset (m : Fin 7) : Set Aff := {Z | 1 ≤ ‖Z m‖ ∧ ∀ k, ‖Z k‖ ≤ ‖Z m‖}

theorem measurableSet_qset (m : Fin 7) : MeasurableSet (qset m) := by
  have hc : ∀ k : Fin 7, Continuous fun Z : Aff => ‖Z k‖ := fun k =>
    (EuclideanSpace.proj k : Aff →L[ℂ] ℂ).continuous.norm
  have h : qset m = {Z : Aff | 1 ≤ ‖Z m‖} ∩ ⋂ k : Fin 7, {Z : Aff | ‖Z k‖ ≤ ‖Z m‖} := by
    ext Z
    simp [qset]
  rw [h]
  exact (isClosed_le continuous_const (hc m)).measurableSet.inter
    (MeasurableSet.iInter fun k => (isClosed_le (hc k) (hc m)).measurableSet)

theorem tau_mem_polydisc {m : Fin 7} {Z : Aff} (hZ : Z ∈ qset m) : tau m Z ∈ polydisc := by
  have hn : 0 < ‖Z m‖ := lt_of_lt_of_le one_pos hZ.1
  show ∀ k, ‖tau m Z k‖ ≤ 1
  intro k
  by_cases hk : k = m
  · rw [hk, tau_apply_self, norm_inv]
    exact inv_le_one_of_one_le₀ hZ.1
  · rw [tau_apply_ne hk, norm_mul, norm_inv, inv_mul_le_iff₀ hn, mul_one]
    exact hZ.2 k

theorem cover (Z : Aff) : Z ∈ polydisc ∨ ∃ m, Z ∈ qset m := by
  by_cases hZ : Z ∈ polydisc
  · exact Or.inl hZ
  · right
    obtain ⟨m, hm⟩ := Finite.exists_max fun k : Fin 7 => ‖Z k‖
    refine ⟨m, ?_, hm⟩
    have h : ∃ k, 1 < ‖Z k‖ := by
      by_contra hcon
      exact hZ fun k => not_lt.1 fun hk => hcon ⟨k, hk⟩
    obtain ⟨k, hk⟩ := h
    exact hk.le.trans (hm k)

/-! ### The Sobolev inequality -/

/-- **The Sobolev inequality (1.1) for the Fubini–Study metric of `CP⁷`.** -/
theorem hasSobolevBound_fubiniStudy : ∃ C₀ : ℝ, 0 < C₀ ∧ HasSobolevBound uFS C₀ := by
  obtain ⟨C, hCt, hC⟩ := local_sobolev
  have hKt : (8 * C) ^ 2 * 4 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) hCt)) (by simp)
  refine ⟨((8 * C) ^ 2 * 4).toReal + 1, by positivity, fun f hf => ?_⟩
  have hofReal : (8 * C) ^ 2 * 4 ≤ ENNReal.ofReal (((8 * C) ^ 2 * 4).toReal + 1) :=
    (ENNReal.ofReal_toReal hKt).symm.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  -- the function on the chart
  obtain ⟨F, hF⟩ : ∃ F : Aff → ℝ, F = fun Z => f (chart 0 Z) := ⟨_, rfl⟩
  have hFsm : ContDiff ℝ 1 F := by
    rw [hF]
    exact (contDiff_comp_chart hf).of_le (by simp)
  have hFc : Continuous F := hFsm.continuous
  have hFd : Differentiable ℝ F := hFsm.differentiable one_ne_zero
  have hgF : Continuous fun Z => Real.sqrt (gradSq uFS F Z) :=
    Real.continuous_sqrt.comp (continuous_gradSq_fubiniStudy hFsm)
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0∞,
      X = eLpNorm (fun Z => Real.sqrt (gradSq uFS F Z)) 2 (nu uFS) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ≥0∞, Y = eLpNorm F 2 (nu uFS) := ⟨_, rfl⟩
  have h73 : ((7 : ℝ≥0∞) / 3) ≠ 0 := by simp
  have h73' : ((7 : ℝ≥0∞) / 3) ≠ ⊤ := by simp [ENNReal.div_eq_top]
  -- the polydisc
  have h0 : eLpNorm (polydisc.indicator F) (7 / 3) (nu uFS) ≤ C * (X + Y) := by
    rw [hX, hY]
    exact hC F hFsm
  -- the other seven pieces
  have hm : ∀ m : Fin 7, eLpNorm ((qset m).indicator F) (7 / 3) (nu uFS) ≤ C * (X + Y) := by
    intro m
    obtain ⟨Fm, hFm⟩ : ∃ Fm : Aff → ℝ, Fm = fun Z => f (swapHom m (chart 0 Z)) := ⟨_, rfl⟩
    have hFmsm : ContDiff ℝ 1 Fm := by
      rw [hFm]
      exact (contDiff_comp_chart (isSmoothCP_swap m hf)).of_le (by simp)
    have hFmeq : ∀ Z : Aff, Z m ≠ 0 → Fm Z = F (tau m Z) := by
      intro Z hZ
      rw [hFm, hF]
      exact comp_swap_chart hf hZ
    have hloc := hC Fm hFmsm
    have hb : eLpNorm ((qset m).indicator F) (7 / 3) (nu uFS)
        ≤ eLpNorm (polydisc.indicator Fm) (7 / 3) (nu uFS) := by
      refine eLpNorm_le_of_tau (m := m)
        (hFc.aestronglyMeasurable.indicator (measurableSet_qset m))
        (hFmsm.continuous.aestronglyMeasurable.indicator measurableSet_polydisc) h73 h73'
        fun Z hZ => ?_
      by_cases hq : Z ∈ qset m
      · have ht := tau_mem_polydisc hq
        have e : Fm (tau m Z) = F Z := by
          rw [hFmeq _ (tau_coord_ne_zero hZ), tau_tau hZ]
        exact le_of_eq (by rw [indicator_of_mem hq, indicator_of_mem ht, e])
      · rw [indicator_of_notMem hq, norm_zero]
        exact norm_nonneg _
    have hd : eLpNorm Fm 2 (nu uFS) ≤ eLpNorm F 2 (nu uFS) :=
      eLpNorm_le_of_tau (m := m) hFmsm.continuous.aestronglyMeasurable hFc.aestronglyMeasurable
        two_ne_zero ENNReal.ofNat_ne_top fun Z hZ => le_of_eq (by rw [hFmeq Z hZ])
    have he : eLpNorm (fun Z => Real.sqrt (gradSq uFS Fm Z)) 2 (nu uFS)
        ≤ eLpNorm (fun Z => Real.sqrt (gradSq uFS F Z)) 2 (nu uFS) := by
      refine eLpNorm_le_of_tau (m := m)
        (Real.continuous_sqrt.comp (continuous_gradSq_fubiniStudy hFmsm)).aestronglyMeasurable
        hgF.aestronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top fun Z hZ => ?_
      have hopen : IsOpen {W : Aff | W m ≠ 0} :=
        isOpen_ne_fun ((EuclideanSpace.proj m : Aff →L[ℂ] ℂ).continuous) continuous_const
      have hev : Fm =ᶠ[𝓝 Z] fun W => F (tau m W) := by
        filter_upwards [hopen.mem_nhds hZ] with W hW
        exact hFmeq W hW
      have hgs : gradSq uFS Fm Z = gradSq uFS (fun W => F (tau m W)) Z := by
        unfold gradSq dz
        rw [hev.fderiv_eq]
      show ‖Real.sqrt (gradSq uFS Fm Z)‖ ≤ ‖Real.sqrt (gradSq uFS F (tau m Z))‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _), hgs]
      exact Real.sqrt_le_sqrt (gradSq_tau_le hZ hFd.differentiableAt)
    calc eLpNorm ((qset m).indicator F) (7 / 3) (nu uFS)
        ≤ eLpNorm (polydisc.indicator Fm) (7 / 3) (nu uFS) := hb
      _ ≤ C * (eLpNorm (fun Z => Real.sqrt (gradSq uFS Fm Z)) 2 (nu uFS)
          + eLpNorm Fm 2 (nu uFS)) := hloc
      _ ≤ C * (X + Y) := by
          rw [hX, hY]
          exact mul_le_mul' le_rfl (add_le_add he hd)
  -- the decomposition
  have hFle : ∀ Z, ‖F Z‖ ≤ ‖polydisc.indicator F Z‖
      + ∑ m : Fin 7, ‖(qset m).indicator F Z‖ := by
    intro Z
    have hsum : 0 ≤ ∑ m : Fin 7, ‖(qset m).indicator F Z‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    rcases cover Z with hP | ⟨m, hq⟩
    · rw [indicator_of_mem hP]
      linarith
    · have h1 : ‖(qset m).indicator F Z‖ ≤ ∑ m : Fin 7, ‖(qset m).indicator F Z‖ :=
        Finset.single_le_sum (f := fun m : Fin 7 => ‖(qset m).indicator F Z‖)
          (fun i _ => norm_nonneg _) (Finset.mem_univ m)
      have h2 : ‖(qset m).indicator F Z‖ = ‖F Z‖ := by rw [indicator_of_mem hq]
      have h3 : 0 ≤ ‖polydisc.indicator F Z‖ := norm_nonneg _
      linarith
  have h1 : (1 : ℝ≥0∞) ≤ 7 / 3 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
    norm_num
  have hsplit : eLpNorm F (7 / 3) (nu uFS) ≤ eLpNorm (polydisc.indicator F) (7 / 3) (nu uFS)
      + ∑ m : Fin 7, eLpNorm ((qset m).indicator F) (7 / 3) (nu uFS) := by
    have hstep := eLpNorm_mono_real (p := 7 / 3) (μ := nu uFS) hFc.aestronglyMeasurable hFle
    have hfun : (fun Z => ‖polydisc.indicator F Z‖ + ∑ m : Fin 7, ‖(qset m).indicator F Z‖)
        = (fun Z => ‖polydisc.indicator F Z‖)
          + ∑ m : Fin 7, fun Z => ‖(qset m).indicator F Z‖ := by
      funext Z
      rw [Pi.add_apply, Finset.sum_apply]
    rw [hfun] at hstep
    refine hstep.trans ((eLpNorm_add_le h1).trans (add_le_add ?_ ?_))
    · exact (eLpNorm_norm _ (hFc.aestronglyMeasurable.indicator measurableSet_polydisc)).le
    · refine (eLpNorm_sum_le h1).trans (Finset.sum_le_sum fun m _ => ?_)
      exact (eLpNorm_norm _ (hFc.aestronglyMeasurable.indicator (measurableSet_qset m))).le
  have hE : eLpNorm F (7 / 3) (nu uFS) ≤ 8 * C * (X + Y) := by
    refine hsplit.trans ?_
    calc eLpNorm (polydisc.indicator F) (7 / 3) (nu uFS)
          + ∑ m : Fin 7, eLpNorm ((qset m).indicator F) (7 / 3) (nu uFS)
        ≤ C * (X + Y) + ∑ _m : Fin 7, C * (X + Y) :=
          add_le_add h0 (Finset.sum_le_sum fun m _ => hm m)
      _ = 8 * C * (X + Y) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hsq : (X + Y) ^ 2 ≤ 4 * (X ^ 2 + Y ^ 2) := by
    have e1 : X + Y ≤ 2 * max X Y := by
      rw [two_mul]
      exact add_le_add (le_max_left _ _) (le_max_right _ _)
    have e2 : max X Y ^ 2 ≤ X ^ 2 + Y ^ 2 := by
      rcases le_total X Y with h | h
      · rw [max_eq_right h]
        exact le_add_self
      · rw [max_eq_left h]
        exact le_self_add
    calc (X + Y) ^ 2 ≤ (2 * max X Y) ^ 2 := pow_le_pow_left' e1 2
      _ = 4 * max X Y ^ 2 := by
          rw [mul_pow]
          norm_num
      _ ≤ 4 * (X ^ 2 + Y ^ 2) := mul_le_mul' le_rfl e2
  subst hF
  rw [← hX, ← hY]
  -- `‖f‖² ≤ (8 C (X + Y))² ≤ (8 C)² · 4 (X² + Y²)`
  refine (pow_le_pow_left' hE 2).trans ?_
  rw [mul_pow]
  refine (mul_le_mul' le_rfl hsq).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul' hofReal le_rfl

/-- The Sobolev inequality of the Fubini–Study metric, in the form used in
`Calabi.Geometry.mainTheorem_of_correction`. -/
theorem fubiniStudySobolev : FubiniStudySobolev := by
  obtain ⟨C₀, hC₀, h⟩ := hasSobolevBound_fubiniStudy
  refine ⟨C₀, hC₀, ?_⟩
  rw [pot_zero 0]
  exact h

/-- **Theorem 1.1 of the manuscript follows from the localized correction**
(Proposition 6.1) for one profile. -/
theorem mainTheorem_of_localizedCorrection {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G)
    (h : LocalizedCorrection G) : MainTheorem :=
  mainTheorem_of_correction hP h fubiniStudySobolev

/-- **Theorem 1.1 of the manuscript, with Proposition 6.1 as the only
hypothesis**: the profile exists by `Calabi.exists_profile`. -/
theorem mainTheorem_of_forall_localizedCorrection
    (h : ∀ (c : ℝ) (G : ℝ → ℝ), IsProfile c G → LocalizedCorrection G) : MainTheorem := by
  obtain ⟨c, G, hP⟩ := exists_profile
  exact mainTheorem_of_correction hP (h c G hP) fubiniStudySobolev

end Calabi.Geometry
