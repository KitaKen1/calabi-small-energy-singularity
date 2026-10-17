import Calabi.Correction.Compose
import Calabi.Correction.ChartCutoff

/-!
# Functions that are smooth in space and time are in the local classes

The localized profile `F_λ(t, |z|²)` is a smooth function of space and time
for `t < 0`. `Sm.of_joint` puts such functions in the local classes `Sm` of
all orders; `hasDerivAt_time_of_joint` gives their time derivative.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A function that is smooth on an open set of space-time coincides near a
given point with a function that is smooth everywhere. -/
theorem exists_global_rep {W : Set (V × ℝ)} (hW : IsOpen W) {F : V × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F W) {p₀ : V × ℝ} (hp₀ : p₀ ∈ W) :
    ∃ (Ft : V × ℝ → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ∞ Ft ∧
      ∀ p : V × ℝ, ‖p.1 - p₀.1‖ < r → |p.2 - p₀.2| < r → Ft p = F p ∧ p ∈ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p₀ hp₀
  have hμ : 0 < (ε / 4) ^ 2 := by positivity
  have hmemW : ∀ p : V × ℝ, ‖p.1 - p₀.1‖ < ε → |p.2 - p₀.2| < ε → p ∈ W := by
    intro p h1 h2
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by rwa [dist_eq_norm], by rwa [Real.dist_eq]⟩
  have hζs : ContDiff ℝ ∞ (fun p : V × ℝ => chiV ((ε / 4) ^ 2) (p.1 - p₀.1)) :=
    (contDiff_chiV _).comp (contDiff_fst.sub contDiff_const)
  have hηs : ContDiff ℝ ∞ (fun p : V × ℝ => chiV (V := ℝ) ((ε / 4) ^ 2) (p.2 - p₀.2)) :=
    (contDiff_chiV _).comp (contDiff_snd.sub contDiff_const)
  refine ⟨fun p => chiV ((ε / 4) ^ 2) (p.1 - p₀.1) * chiV (V := ℝ) ((ε / 4) ^ 2) (p.2 - p₀.2)
    * F p, ε / 4, by positivity, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases h1 : ‖p.1 - p₀.1‖ < ε
    · by_cases h2 : |p.2 - p₀.2| < ε
      · exact (hζs.contDiffAt.mul hηs.contDiffAt).mul
          (hF.contDiffAt (hW.mem_nhds (hmemW p h1 h2)))
      · have hopen : IsOpen {q : V × ℝ | 2 * (ε / 4) ^ 2 < ‖q.2 - p₀.2‖ ^ 2} :=
          isOpen_lt continuous_const ((continuous_snd.sub continuous_const).norm.pow 2)
        have hmem : p ∈ {q : V × ℝ | 2 * (ε / 4) ^ 2 < ‖q.2 - p₀.2‖ ^ 2} := by
          have h3 : ε ≤ |p.2 - p₀.2| := not_lt.1 h2
          have h4 := pow_le_pow_left₀ hε.le h3 2
          show 2 * (ε / 4) ^ 2 < ‖p.2 - p₀.2‖ ^ 2
          rw [Real.norm_eq_abs]
          nlinarith
        refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hopen.mem_nhds hmem] with q hq
        rw [chiV_of_ge hμ hq.le, mul_zero, zero_mul]
    · have hopen : IsOpen {q : V × ℝ | 2 * (ε / 4) ^ 2 < ‖q.1 - p₀.1‖ ^ 2} :=
        isOpen_lt continuous_const ((continuous_fst.sub continuous_const).norm.pow 2)
      have hmem : p ∈ {q : V × ℝ | 2 * (ε / 4) ^ 2 < ‖q.1 - p₀.1‖ ^ 2} := by
        have h3 : ε ≤ ‖p.1 - p₀.1‖ := not_lt.1 h1
        have h4 := pow_le_pow_left₀ hε.le h3 2
        show 2 * (ε / 4) ^ 2 < ‖p.1 - p₀.1‖ ^ 2
        nlinarith
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with q hq
      rw [chiV_of_ge hμ hq.le, zero_mul, zero_mul]
  · intro p h1 h2
    refine ⟨?_, hmemW p (by linarith) (by linarith)⟩
    have e1 : chiV ((ε / 4) ^ 2) (p.1 - p₀.1) = 1 :=
      chiV_of_le hμ (pow_le_pow_left₀ (norm_nonneg _) h1.le 2)
    have e2 : chiV (V := ℝ) ((ε / 4) ^ 2) (p.2 - p₀.2) = 1 :=
      chiV_of_le hμ (by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h2.le 2)
    show chiV ((ε / 4) ^ 2) (p.1 - p₀.1) * chiV (V := ℝ) ((ε / 4) ^ 2) (p.2 - p₀.2) * F p = F p
    rw [e1, e2, one_mul, one_mul]

omit [FiniteDimensional ℝ V] in
/-- The spatial jets of a smooth function of space and time. -/
theorem iteratedFDeriv_slice {F : V × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (j : ℕ) (z : V) (t : ℝ) :
    iteratedFDeriv ℝ j (fun y => F (y, t)) z
      = ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ) (iteratedFDeriv ℝ j F (z, t)) := by
  have e : (fun y => F (y, t))
      = (fun q : V × ℝ => F (q + (0, t))) ∘ ⇑(ContinuousLinearMap.inl ℝ V ℝ) := by
    funext y
    simp
  have hs : ContDiff ℝ ∞ (fun q : V × ℝ => F (q + (0, t))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs z (i := j) (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  simp

set_option maxHeartbeats 1600000 in
/-- **A function that is smooth in space and time is in the local classes.** -/
theorem Sm.of_joint {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {W : Set (V × ℝ)} (hW : IsOpen W)
    {F : V × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F W) (k : ℕ) : Sm α W k (fun t z => F (z, t)) := by
  intro p₀ hp₀
  obtain ⟨Ft, r, hr, hFt, hagree⟩ := exists_global_rep hW hF hp₀
  -- the jets as smooth functions of space and time
  have hJs : ∀ j : ℕ, ContDiff ℝ 1 (fun p : V × ℝ =>
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ) (iteratedFDeriv ℝ j Ft p)) := fun j =>
    ContDiff.continuousLinearMap_comp
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ))
      (hFt.iteratedFDeriv_right (m := 1) (i := j) (by exact_mod_cast le_top))
  have hb0 : ∀ j : ℕ, ∃ A : ℝ, ∀ p ∈ Metric.closedBall p₀ 1,
      ‖ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ) (iteratedFDeriv ℝ j Ft p)‖ ≤ A :=
    fun j => (isCompact_closedBall p₀ 1).exists_bound_of_continuousOn
      (hJs j).continuous.continuousOn
  have hb1 : ∀ j : ℕ, ∃ A : ℝ, ∀ p ∈ Metric.closedBall p₀ 1,
      ‖fderiv ℝ (fun p : V × ℝ => ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ) (iteratedFDeriv ℝ j Ft p)) p‖ ≤ A :=
    fun j => (isCompact_closedBall p₀ 1).exists_bound_of_continuousOn
      ((hJs j).continuous_fderiv one_ne_zero).continuousOn
  choose A₀ hA₀ using hb0
  choose A₁ hA₁ using hb1
  obtain ⟨At, hAtdef⟩ : ∃ At : ℝ, At = ∑ i ∈ Finset.range (k + 1), (|A₀ i| + |A₁ i|) := ⟨_, rfl⟩
  have hAt0 : 0 ≤ At := by
    rw [hAtdef]
    exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hAle : ∀ j : ℕ, j ≤ k → |A₀ j| + |A₁ j| ≤ At := fun j hj => by
    rw [hAtdef]
    exact Finset.single_le_sum (f := fun i => |A₀ i| + |A₁ i|)
      (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_range.2 (by omega))
  have hρ : 0 < min r 1 := lt_min hr one_pos
  have hsub : Metric.ball p₀ (min r 1) ⊆ Metric.closedBall p₀ 1 := fun p hp =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hp)
  have hcoord : ∀ p ∈ Metric.ball p₀ (min r 1), ‖p.1 - p₀.1‖ < r ∧ |p.2 - p₀.2| < r := by
    intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq] at hp
    exact ⟨hp.1.trans_le (min_le_left _ _), hp.2.trans_le (min_le_left _ _)⟩
  refine ⟨Metric.ball p₀ (min r 1), fun t z => Ft (z, t), 2 * At, Metric.isOpen_ball,
    Metric.mem_ball_self hρ, by positivity, fun p hp => ?_, fun t => ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2⟩ := hcoord p hp
    exact (hagree p h1 h2).1
  · exact (hFt.of_le (by exact_mod_cast le_top)).comp (contDiff_id.prodMk contDiff_const)
  · have h1 : WH α 1 (fun _ : V × ℝ => (1 : ℝ)) (Metric.ball p₀ (min r 1)) ((0 : ℝ) - (j : ℝ))
        (2 * At) (fun p => ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin j => ContinuousLinearMap.inl ℝ V ℝ) (iteratedFDeriv ℝ j Ft p)) := by
      refine WH.of_lipschitz (fun _ _ => one_pos) hAt0 le_rfl hα hα1 (fun p hp => ?_)
        (fun p hp q hq _ => ?_)
      · rw [Real.one_rpow, mul_one]
        exact (hA₀ j p (hsub hp)).trans ((le_abs_self _).trans
          ((le_add_of_nonneg_right (abs_nonneg _)).trans (hAle j hj)))
      · have hmv := (convex_closedBall p₀ 1).norm_image_sub_le_of_norm_fderiv_le
          (fun y _ => ((hJs j).differentiable one_ne_zero) y)
          (fun y hy => (hA₁ j y hy).trans ((le_abs_self _).trans
            ((le_add_of_nonneg_left (abs_nonneg _)).trans (hAle j hj)))) (hsub hq) (hsub hp)
        have hnorm : ‖p - q‖ ≤ ‖p.1 - q.1‖ + |p.2 - q.2| := by
          rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
          exact max_le (le_add_of_nonneg_right (abs_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))
        rw [Real.one_rpow, mul_one, Real.one_rpow, mul_one]
        calc _ ≤ At * ‖p - q‖ := hmv
          _ ≤ At * (‖p.1 - q.1‖ + |p.2 - q.2|) := mul_le_mul_of_nonneg_left hnorm hAt0
          _ = At * ‖p.1 - q.1‖ + At * |p.2 - q.2| := by ring
    refine h1.congr fun p _ => ?_
    exact iteratedFDeriv_slice hFt j p.1 p.2

omit [FiniteDimensional ℝ V] in
/-- The time derivative of a function that is smooth in space and time. -/
theorem hasDerivAt_time_of_joint {W : Set (V × ℝ)} (hW : IsOpen W) {F : V × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F W) {p : V × ℝ} (hp : p ∈ W) :
    HasDerivAt (fun t => F (p.1, t)) (fderiv ℝ F p ((0 : V), (1 : ℝ))) p.2 := by
  have h1 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) :=
    ((hF.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((p.1, t) : V × ℝ)) ((0 : V), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact h1.comp_hasDerivAt p.2 hline

omit [FiniteDimensional ℝ V] in
/-- The time derivative of a smooth function of space and time is smooth. -/
theorem contDiffOn_time_deriv {W : Set (V × ℝ)} (hW : IsOpen W) {F : V × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F W) :
    ContDiffOn ℝ ∞ (fun p : V × ℝ => fderiv ℝ F p ((0 : V), (1 : ℝ))) W :=
  (hF.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const

end Calabi.Weighted
