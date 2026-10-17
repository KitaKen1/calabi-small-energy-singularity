import Calabi.Correction.ChartPieces

/-!
# The Calabi flow in the two charts and the smoothness of the solution

For the correction pair `U` of `exists_correction`, the function
`H = F_λ + V`, `V = valOf U`, satisfies the Calabi flow in the momentum
coordinate. In the two flat charts it becomes the chart equation of
`JointSmooth.lean`:

* in the chart `ℝ⁶` at `x = 1`, on `|w|² < 1/2`, where `H(t, 1 - |w|²)` is the
  second chart function `U¹(t, w)` alone (`chart1_equation`);
* in the chart `ℝ¹⁸` at `x = 0`, on `|z|² < 5/8`, for the chart function
  `h0 = F_λ(t, |z|²) + U⁰(t, z) + U¹(t, Ψ z)` with the transfer map `Ψ` of
  `Transfer.lean` (`chart0_equation`).

Hence both chart functions are smooth in space and time (`chart1_smooth`,
`chart0_smooth`), by `chart_smooth`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

variable {c : ℝ} {G : ℝ → ℝ} {lam α T w e M : ℝ} {U : Pair}

/-! ### The chart at `x = 1` -/

theorem chart1_val (hU : IsCorrection G lam α T w e M U) (t : ℝ) {v : Flat6}
    (hv : ‖v‖ ^ 2 < 1 / 2) : valOf U t (1 - ‖v‖ ^ 2) = U.2.2.1 t v := by
  have h0 : (1 / 2 : ℝ) < ‖Real.sqrt (1 - ‖v‖ ^ 2) • e18‖ ^ 2 := by
    rw [norm_sq_ray18 (by linarith)]
    linarith
  unfold valOf
  rw [hU.reg.supp0 _ _ h0, zero_add, sub_sub_cancel, Real.sqrt_sq (norm_nonneg _), hU.sol.eval1]

set_option maxHeartbeats 1600000 in
/-- **The Calabi flow in the chart at `x = 1`.** -/
theorem chart1_equation (hP : IsProfile c G) (hlam : 0 < lam) (hlam8 : lam < 1 / 8)
    (hU : IsCorrection G lam α T w e M U) :
    ∀ p ∈ {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 1 / 2},
      U.2.2.2 p.2 p.1 + (1 + vstar (1 - ‖p.1‖ ^ 2) * U.2.2.1 p.2 p.1) ^ 2
        * (chartOp 18 (U.2.2.1 p.2) p.1 / 16) = 0 := by
  intro p hp
  obtain ⟨ht, hw⟩ := hp
  have hx : 1 - ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [sq_nonneg ‖p.1‖]⟩
  have hxl : 2 * lam < 1 - ‖p.1‖ ^ 2 := by linarith
  have hE := hU.eqn p.2 ht _ hx
  have hsq : Real.sqrt (1 - (1 - ‖p.1‖ ^ 2)) = ‖p.1‖ := by
    rw [sub_sub_cancel, Real.sqrt_sq (norm_nonneg _)]
  have h0 : (1 / 2 : ℝ) < ‖Real.sqrt (1 - ‖p.1‖ ^ 2) • e18‖ ^ 2 := by
    rw [norm_sq_ray18 hx.1]
    linarith
  have hvt0 : U.2.1 p.2 (Real.sqrt (1 - ‖p.1‖ ^ 2) • e18) = 0 := hU.reg.supp0t _ _ h0
  have hA0 : chartOp 6 (U.1 p.2) (Real.sqrt (1 - ‖p.1‖ ^ 2) • e18) = 0 := by
    apply chartOp_eq_zero_of_eventually
    have hopen : IsOpen {z : Flat18 | 1 / 2 < ‖z‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    filter_upwards [hopen.mem_nhds h0] with z hz using hU.reg.supp0 p.2 z hz
  have hval := chart1_val hU p.2 hw
  have hdt : dtOf U p.2 (1 - ‖p.1‖ ^ 2) = U.2.2.2 p.2 p.1 := by
    unfold dtOf
    rw [hvt0, zero_add, hsq, hU.sol.evalt1 ht]
  have hAO : AOf U p.2 (1 - ‖p.1‖ ^ 2) = chartOp 18 (U.2.2.1 p.2) p.1 / 16 := by
    unfold AOf
    rw [hA0, zero_div, zero_add, hsq,
      chartOp_eq_of_norm_eq 18 (hU.reg.smooth1 p.2) (hU.sol.radial1 p.2) (a := ‖p.1‖ • e6)
        (b := p.1) (by rw [norm_smul, norm_e6, mul_one, norm_norm])]
  have hb : blam G lam p.2 (1 - ‖p.1‖ ^ 2) = 1 := blam_of_ge hlam p.2 hxl.le
  have hc : clam G lam p.2 (1 - ‖p.1‖ ^ 2) = 0 := clam_of_gt hP hlam ht.2 hx hxl
  have haf : aflam G lam p.2 (1 - ‖p.1‖ ^ 2) = 0 := Aop_Flam_of_gt hP hlam ht.2 hx hxl
  have hEl : Elam G lam p.2 (1 - ‖p.1‖ ^ 2) = 0 := Elam_eq_zero hP hlam ht.2 hx hxl
  unfold POf NOf at hE
  rw [hval, hdt, hAO, hb, hc, haf, hEl] at hE
  linear_combination hE

/-- **The second chart function is smooth in space and time** on `|w|² < 1/2`. -/
theorem chart1_smooth (hP : IsProfile c G) (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (hlam8 : lam < 1 / 8) (he : 0 ≤ e) (hM : 0 ≤ M) (hU : IsCorrection G lam α T w e M U) :
    ContDiffOn ℝ ∞ (fun p : Flat6 × ℝ => U.2.2.1 p.2 p.1)
      {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 1 / 2} := by
  have hsub : {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 1 / 2}
      ⊆ {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0} := fun p hp => hp.1
  have hn : ContDiff ℝ ∞ (fun v : Flat6 => 1 - ‖v‖ ^ 2) :=
    contDiff_const.sub (contDiff_norm_sq ℝ)
  have hv : ContDiff ℝ ∞ (fun v : Flat6 => vstar (1 - ‖v‖ ^ 2)) := by
    show ContDiff ℝ ∞ (fun v : Flat6 => (1 - ‖v‖ ^ 2) * (1 - (1 - ‖v‖ ^ 2)))
    exact hn.mul (contDiff_const.sub hn)
  refine chart_smooth hα hα1 (isOpen_slab T (1 / 2)) (fun p hp => ?_) 18 hv
    ((sm_U1 hα.le he hU.reg hU.xj).mono_set hsub) ((sm_U1t hα hM hU.reg hU.xt).mono_set hsub)
    (fun p hp => hU.sol.deriv1 p.2 hp.1 p.1) (fun p hp => ?_) (chart1_equation hP hlam hlam8 hU)
  · have h1 : ‖p.1‖ ^ 2 < 1 / 2 := hp.2
    nlinarith [norm_nonneg p.1]
  · have hx : 1 - ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hp.2], by linarith [sq_nonneg ‖p.1‖]⟩
    have h1 := hU.pos p.2 hp.1 _ hx
    rw [Flam_of_ge hlam p.2 (by linarith [hp.2]), zero_add, chart1_val hU p.2 hp.2] at h1
    exact h1

/-! ### The chart at `x = 0` -/

/-- The chart function at `x = 0`: `H(t, |z|²)` for `|z|² ≤ 3/4`. -/
noncomputable def h0 (G : ℝ → ℝ) (lam : ℝ) (U : Pair) (t : ℝ) (z : Flat18) : ℝ :=
  Flam G lam t (‖z‖ ^ 2) + U.1 t z + U.2.2.1 t (PsiT z)

/-- The time derivative of the localized profile in the chart. -/
noncomputable def FlamT (G : ℝ → ℝ) (lam : ℝ) (p : Flat18 × ℝ) : ℝ :=
  fderiv ℝ (fun q : Flat18 × ℝ => Flam G lam q.2 (‖q.1‖ ^ 2)) p ((0 : Flat18), (1 : ℝ))

/-- The time derivative of the chart function at `x = 0`. -/
noncomputable def h0t (G : ℝ → ℝ) (lam : ℝ) (U : Pair) (t : ℝ) (z : Flat18) : ℝ :=
  FlamT G lam (z, t) + U.2.1 t z + U.2.2.2 t (PsiT z)

theorem isOpen_neg_time {V : Type} [NormedAddCommGroup V] : IsOpen {q : V × ℝ | q.2 < 0} :=
  isOpen_lt continuous_snd continuous_const

theorem hasDerivAt_Flam_chart (hP : IsProfile c G) (lam : ℝ) {t : ℝ} (ht : t < 0) (z : Flat18) :
    HasDerivAt (fun τ => Flam G lam τ (‖z‖ ^ 2)) (FlamT G lam (z, t)) t :=
  hasDerivAt_time_of_joint isOpen_neg_time (contDiffOn_Flam_chart hP lam) (p := (z, t)) ht

theorem contDiff_Flam_slice (hP : IsProfile c G) (lam : ℝ) {t : ℝ} (ht : t < 0) :
    ContDiff ℝ ∞ (fun z : Flat18 => Flam G lam t (‖z‖ ^ 2)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have h1 := (contDiffOn_Flam_chart (V := Flat18) hP lam).contDiffAt
    (isOpen_neg_time.mem_nhds (show ((z, t) : Flat18 × ℝ).2 < 0 from ht))
  exact h1.comp z (contDiffAt_id.prodMk contDiffAt_const)

theorem chart0_val (hU : IsCorrection G lam α T w e M U) (t : ℝ) {z : Flat18}
    (hz : ‖z‖ ^ 2 ≤ 3 / 4) : valOf U t (‖z‖ ^ 2) = U.1 t z + U.2.2.1 t (PsiT z) := by
  unfold valOf
  rw [Real.sqrt_sq (norm_nonneg z), hU.sol.eval0, PsiT_of_le hz]

theorem chart0_dt (hU : IsCorrection G lam α T w e M U) {t : ℝ} (ht : t ∈ Ioo (-T) 0)
    {z : Flat18} (hz : ‖z‖ ^ 2 ≤ 3 / 4) :
    dtOf U t (‖z‖ ^ 2) = U.2.1 t z + U.2.2.2 t (PsiT z) := by
  unfold dtOf
  rw [Real.sqrt_sq (norm_nonneg z), hU.sol.evalt0 ht, PsiT_of_le hz]

theorem chart0_AOf (hU : IsCorrection G lam α T w e M U) (t : ℝ) {z : Flat18}
    (hz : ‖z‖ ^ 2 < 3 / 4) :
    AOf U t (‖z‖ ^ 2)
      = chartOp 6 (U.1 t) z / 16 + chartOp 6 (fun y => U.2.2.1 t (PsiT y)) z / 16 := by
  unfold AOf
  rw [Real.sqrt_sq (norm_nonneg z),
    chartOp_eq_of_norm_eq 6 (hU.reg.smooth0 t) (hU.sol.radial0 t) (a := ‖z‖ • e18) (b := z)
      (by rw [norm_smul, norm_e18, mul_one, norm_norm]),
    chartOp_transfer (hU.reg.smooth1 t) (hU.sol.radial1 t) (hU.reg.supp1 t) hz]

set_option maxHeartbeats 3200000 in
/-- **The Calabi flow in the chart at `x = 0`.** -/
theorem chart0_equation (hP : IsProfile c G) (hU : IsCorrection G lam α T w e M U) :
    ∀ p ∈ {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8},
      h0t G lam U p.2 p.1 + (1 + vstar (‖p.1‖ ^ 2) * h0 G lam U p.2 p.1) ^ 2
        * (chartOp 6 (h0 G lam U p.2) p.1 / 16) = 0 := by
  intro p hp
  obtain ⟨ht, hz⟩ := hp
  have hx : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by linarith⟩
  have hE := hU.eqn p.2 ht _ hx
  have hFs : ContDiff ℝ 4 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2)) := by
    exact_mod_cast contDiff_infty.1 (contDiff_Flam_slice hP lam ht.2) 4
  have hΨ4 : ContDiff ℝ 4 PsiT := by exact_mod_cast contDiff_infty.1 contDiff_PsiT 4
  have hu1 : ContDiff ℝ 4 (fun y : Flat18 => U.2.2.1 p.2 (PsiT y)) :=
    (hU.reg.smooth1 p.2).comp hΨ4
  have hF : chartOp 6 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2)) p.1
      = 16 * Aop (Flam G lam p.2) (‖p.1‖ ^ 2) :=
    (sixteen_Aop_chart0 (V := Flat18) (by simp) (contDiffOn_Flam_Icc hP lam ht.2)
      (by linarith)).symm
  have hadd : chartOp 6 (h0 G lam U p.2) p.1
      = chartOp 6 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2)) p.1 + chartOp 6 (U.1 p.2) p.1
        + chartOp 6 (fun y => U.2.2.1 p.2 (PsiT y)) p.1 := by
    have e1 : h0 G lam U p.2 = fun y => (Flam G lam p.2 (‖y‖ ^ 2) + U.1 p.2 y)
        + U.2.2.1 p.2 (PsiT y) := rfl
    have h1 : chartOp 6 (fun y : Flat18 => (Flam G lam p.2 (‖y‖ ^ 2) + U.1 p.2 y)
        + U.2.2.1 p.2 (PsiT y)) p.1
        = chartOp 6 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2) + U.1 p.2 y) p.1
          + chartOp 6 (fun y => U.2.2.1 p.2 (PsiT y)) p.1 :=
      chartOp_add 6 (u := fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2) + U.1 p.2 y)
        (v := fun y => U.2.2.1 p.2 (PsiT y)) (hFs.add (hU.reg.smooth0 p.2)) hu1 p.1
    have h2 : chartOp 6 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2) + U.1 p.2 y) p.1
        = chartOp 6 (fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2)) p.1 + chartOp 6 (U.1 p.2) p.1 :=
      chartOp_add 6 (u := fun y : Flat18 => Flam G lam p.2 (‖y‖ ^ 2)) (v := U.1 p.2) hFs
        (hU.reg.smooth0 p.2) p.1
    rw [e1, h1, h2]
  have hd : deriv (fun τ => Flam G lam τ (‖p.1‖ ^ 2)) p.2 = FlamT G lam (p.1, p.2) :=
    (hasDerivAt_Flam_chart hP lam ht.2 p.1).deriv
  unfold POf NOf Elam clam aflam at hE
  unfold blam at hE
  rw [chart0_val hU p.2 (by linarith), chart0_dt hU ht (by linarith),
    chart0_AOf hU p.2 (by linarith), hd] at hE
  rw [hadd, hF]
  unfold h0t h0
  linear_combination hE

/-- The chart function at `x = 0` is in the local class of order four. -/
theorem sm_h0 (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (he : 0 ≤ e) (hT1 : T ≤ 1)
    (hU : IsCorrection G lam α T w e M U) :
    Sm α {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8} 4 (h0 G lam U) := by
  have hsub : {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8}
      ⊆ {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0} := fun p hp => hp.1
  have hsubW : {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8}
      ⊆ {q : Flat18 × ℝ | q.2 < 0} := fun p hp => hp.1.2
  have h1 := (Sm.of_joint hα hα1 isOpen_neg_time
    (contDiffOn_Flam_chart (V := Flat18) hP lam) 4).mono_set hsubW
  have h2 := (sm_U0 hα he hT1 hU.reg hU.xj).mono_set hsub
  have h3 := Sm.comp_map hα hα1 contDiff_PsiT
    (Ω := {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8})
    (Ω' := {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0}) (fun p hp => hp.1)
    (sm_U1 hα he hU.reg hU.xj)
  exact (h1.add h2).add h3

/-- Its time derivative is in the local class of order zero. -/
theorem sm_h0t (hP : IsProfile c G) (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hT1 : T ≤ 1)
    (hU : IsCorrection G lam α T w e M U) :
    Sm α {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8} 0 (h0t G lam U) := by
  have hsub : {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8}
      ⊆ {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0} := fun p hp => hp.1
  have hsubW : {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8}
      ⊆ {q : Flat18 × ℝ | q.2 < 0} := fun p hp => hp.1.2
  have h1 := (Sm.of_joint hα.le hα1 isOpen_neg_time
    (contDiffOn_time_deriv isOpen_neg_time (contDiffOn_Flam_chart (V := Flat18) hP lam))
    0).mono_set hsubW
  have h2 := (sm_U0t hα hM hT1 hU.reg hU.xt).mono_set hsub
  have h3 := Sm.comp_map hα.le hα1 contDiff_PsiT
    (Ω := {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8})
    (Ω' := {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0}) (fun p hp => hp.1)
    (sm_U1t hα hM hU.reg hU.xt)
  exact (h1.add h2).add h3

/-- **The chart function at `x = 0` is smooth in space and time** on
`|z|² < 5/8`. -/
theorem chart0_smooth (hP : IsProfile c G) (hα : 0 < α) (hα1 : α < 1) (he : 0 ≤ e)
    (hM : 0 ≤ M) (hT1 : T ≤ 1) (hU : IsCorrection G lam α T w e M U) :
    ContDiffOn ℝ ∞ (fun p : Flat18 × ℝ => h0 G lam U p.2 p.1)
      {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 5 / 8} := by
  have hn : ContDiff ℝ ∞ (fun z : Flat18 => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hv : ContDiff ℝ ∞ (fun z : Flat18 => vstar (‖z‖ ^ 2)) := by
    show ContDiff ℝ ∞ (fun z : Flat18 => ‖z‖ ^ 2 * (1 - ‖z‖ ^ 2))
    exact hn.mul (contDiff_const.sub hn)
  refine chart_smooth hα hα1 (isOpen_slab T (5 / 8)) (fun p hp => ?_) 6 hv
    (sm_h0 hP hα.le hα1.le he hT1 hU) (sm_h0t hP hα hα1.le hM hT1 hU) (fun p hp => ?_)
    (fun p hp => ?_) (chart0_equation hP hU)
  · have h1 : ‖p.1‖ ^ 2 < 5 / 8 := hp.2
    nlinarith [norm_nonneg p.1]
  · exact ((hasDerivAt_Flam_chart hP lam hp.1.2 p.1).add (hU.sol.deriv0 p.2 hp.1 p.1)).add
      (hU.sol.deriv1 p.2 hp.1 (PsiT p.1))
  · have hx : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by linarith [hp.2]⟩
    have h1 := hU.pos p.2 hp.1 _ hx
    rw [chart0_val hU p.2 (by linarith [hp.2])] at h1
    have e1 : h0 G lam U p.2 p.1
        = Flam G lam p.2 (‖p.1‖ ^ 2) + (U.1 p.2 p.1 + U.2.2.1 p.2 (PsiT p.1)) := by
      unfold h0
      ring
    rw [e1]
    exact h1

end Calabi.Weighted
