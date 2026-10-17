import Calabi.Correction.ChartFlow
import Calabi.Correction.Whitney

/-!
# The solution in the momentum coordinate

`Hsol = F_λ + V` is the function of Proposition 6.1 of the manuscript, with
the correction `V = valOf U` of `exists_correction`.

* `Hsol_eq_h0`, `Hsol_eq_U1`: near the point orbit it is the chart function
  `h0` along a ray, near the other end the second chart function;
* `Hsol_smooth`: it is smooth on `(-T, 0) × [0, 1]`, including the endpoints
  `x = 0` and `x = 1`: the chart functions are smooth in space and time
  (`chart0_smooth`, `chart1_smooth`) and radial, hence smooth functions of the
  square of the radius (`whitney_chart`);
* `Hsol_eqn`: it solves the Calabi flow in the momentum coordinate,
  `H_t + (1 + v∗ H)² A H = 0`, on `(-T, 0) × [0, 1]`: by `sixteen_Aop_chart0`
  and `sixteen_Aop_chart1` the operator `A` on the smooth function `H(t, ·)` is
  the chart operator, and the chart equations are `chart0_equation` and
  `chart1_equation`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat Calabi.Whitney

variable {c : ℝ} {G : ℝ → ℝ} {lam α T w e M : ℝ} {U : Pair}

/-- The solution in the momentum coordinate: the localized profile plus the
correction. -/
noncomputable def Hsol (G : ℝ → ℝ) (lam : ℝ) (U : Pair) (t x : ℝ) : ℝ :=
  Flam G lam t x + valOf U t x

theorem Hsol_eq_h0 (G : ℝ → ℝ) (lam : ℝ) (U : Pair) (t : ℝ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 3 / 4) : Hsol G lam U t x = h0 G lam U t (Real.sqrt x • e18) := by
  have hz : ‖Real.sqrt x • e18‖ ^ 2 = x := norm_sq_ray18 hx0
  unfold Hsol h0 valOf
  rw [PsiT_of_le (by rw [hz]; exact hx), hz]
  ring

theorem Hsol_eq_U1 (hlam : 0 < lam) (hlam8 : lam < 1 / 8) (hR : Reg U) (t : ℝ) {x : ℝ}
    (hx : 1 / 2 < x) (hx1 : x ≤ 1) :
    Hsol G lam U t x = U.2.2.1 t (Real.sqrt (1 - x) • e6) := by
  have hz : (1 / 2 : ℝ) < ‖Real.sqrt x • e18‖ ^ 2 := by
    rw [norm_sq_ray18 (by linarith)]
    exact hx
  unfold Hsol valOf
  rw [Flam_of_ge hlam t (by linarith), hR.supp0 t _ hz]
  ring

set_option maxHeartbeats 1600000 in
/-- **The solution is smooth on `(-T, 0) × [0, 1]`.** -/
theorem Hsol_smooth (hP : IsProfile c G) (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (hlam8 : lam < 1 / 8) (he : 0 ≤ e) (hM : 0 ≤ M) (hT1 : T ≤ 1)
    (hU : IsCorrection G lam α T w e M U) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Hsol G lam U p.1 p.2) (Ioo (-T) 0 ×ˢ Icc (0 : ℝ) 1) := by
  -- the two chart functions as functions of the square of the radius
  have hc0 := whitney_chart (V := Flat18) (T := T) (R := 5 / 8)
    (Fc := fun p : Flat18 × ℝ => h0 G lam U p.2 p.1) (chart0_smooth hP hα hα1 he hM hT1 hU)
    norm_e18 (fun t s => by
      have hn : ‖(-s) • e18‖ = ‖s • e18‖ := by rw [norm_smul, norm_smul, norm_neg]
      show h0 G lam U t ((-s) • e18) = h0 G lam U t (s • e18)
      unfold h0 PsiT
      rw [hn, radial_eq_of_norm_eq (hU.sol.radial0 t) hn])
  have hc1 := whitney_chart (V := Flat6) (T := T) (R := 1 / 2)
    (Fc := fun p : Flat6 × ℝ => U.2.2.1 p.2 p.1)
    (chart1_smooth hP hα hα1 hlam hlam8 he hM hU) norm_e6 (fun t s => by
      have hn : ‖(-s) • e6‖ = ‖s • e6‖ := by rw [norm_smul, norm_smul, norm_neg]
      exact radial_eq_of_norm_eq (hU.sol.radial1 t) hn)
  intro p hp
  rcases lt_or_ge p.2 (5 / 8) with hx | hx
  · -- near the point orbit
    have h1 : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => h0 G lam U q.1 (Real.sqrt q.2 • e18))
        (Ioo (-T) 0 ×ˢ Ico (0 : ℝ) (5 / 8)) p := hc0 p ⟨hp.1, hp.2.1, hx⟩
    have h2 : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => Hsol G lam U q.1 q.2)
        (Ioo (-T) 0 ×ˢ Ico (0 : ℝ) (5 / 8)) p := by
      refine h1.congr_of_eventuallyEq ?_ (Hsol_eq_h0 G lam U p.1 hp.2.1 (by linarith))
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact Hsol_eq_h0 G lam U q.1 hq.2.1 (by linarith [hq.2.2])
    refine h2.mono_of_mem_nhdsWithin ?_
    have hnb : {q : ℝ × ℝ | q.2 < 5 / 8} ∈ 𝓝 p :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnb, self_mem_nhdsWithin] with q hq hqS
    exact ⟨hqS.1, hqS.2.1, hq⟩
  · -- near the other end
    have hmap : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ((q.1, 1 - q.2) : ℝ × ℝ))
        (Ioo (-T) 0 ×ˢ Ioc (1 / 2 : ℝ) 1) :=
      (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)).contDiffOn
    have h1 := hc1.comp hmap (fun q hq => ⟨hq.1, by
      show (0 : ℝ) ≤ 1 - q.2
      linarith [hq.2.2], by
      show 1 - q.2 < 1 / 2
      linarith [hq.2.1]⟩)
    have hpS : p ∈ Ioo (-T) 0 ×ˢ Ioc (1 / 2 : ℝ) 1 := ⟨hp.1, by linarith, hp.2.2⟩
    have h2 : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => Hsol G lam U q.1 q.2)
        (Ioo (-T) 0 ×ˢ Ioc (1 / 2 : ℝ) 1) p := by
      refine (h1 p hpS).congr_of_eventuallyEq ?_
        (Hsol_eq_U1 hlam hlam8 hU.reg p.1 (by linarith) hp.2.2)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact Hsol_eq_U1 hlam hlam8 hU.reg q.1 hq.2.1 hq.2.2
    refine h2.mono_of_mem_nhdsWithin ?_
    have hnb : {q : ℝ × ℝ | 1 / 2 < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds (by
        show 1 / 2 < p.2
        linarith)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnb, self_mem_nhdsWithin] with q hq hqS
    exact ⟨hqS.1, hq, hqS.2.2⟩

set_option maxHeartbeats 1600000 in
/-- **The solution satisfies the Calabi flow in the momentum coordinate.** -/
theorem Hsol_eqn (hP : IsProfile c G) (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (hlam8 : lam < 1 / 8) (he : 0 ≤ e) (hM : 0 ≤ M) (hT1 : T ≤ 1)
    (hU : IsCorrection G lam α T w e M U) :
    ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun τ => Hsol G lam U τ x) t
        + (1 + vstar x * Hsol G lam U t x) ^ 2 * Aop (Hsol G lam U t) x = 0 := by
  intro t ht x hx
  have hsm := Hsol_smooth hP hα hα1 hlam hlam8 he hM hT1 hU
  have hsl : ContDiffOn ℝ ∞ (Hsol G lam U t) (Icc 0 1) := by
    have hi : ContDiffOn ℝ ∞ (fun y : ℝ => ((t, y) : ℝ × ℝ)) (Icc 0 1) :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact hsm.comp hi fun y hy => ⟨ht, hy⟩
  rcases lt_or_ge x (5 / 8) with hx58 | hx58
  · -- the chart at `x = 0`
    have hz : ‖Real.sqrt x • e18‖ ^ 2 = x := norm_sq_ray18 hx.1
    have hA := sixteen_Aop_chart0 (V := Flat18) (by simp) hsl (z := Real.sqrt x • e18)
      (by rw [hz]; linarith)
    have hev : (fun y : Flat18 => Hsol G lam U t (‖y‖ ^ 2))
        =ᶠ[𝓝 (Real.sqrt x • e18)] h0 G lam U t := by
      have hopen : IsOpen {y : Flat18 | ‖y‖ ^ 2 < 3 / 4} :=
        isOpen_lt (continuous_norm.pow 2) continuous_const
      have hmem : Real.sqrt x • e18 ∈ {y : Flat18 | ‖y‖ ^ 2 < 3 / 4} := by
        show ‖Real.sqrt x • e18‖ ^ 2 < 3 / 4
        rw [hz]
        linarith
      filter_upwards [hopen.mem_nhds hmem] with y hy
      have hy' : ‖y‖ ^ 2 < 3 / 4 := hy
      show Flam G lam t (‖y‖ ^ 2) + valOf U t (‖y‖ ^ 2)
        = Flam G lam t (‖y‖ ^ 2) + U.1 t y + U.2.2.1 t (PsiT y)
      rw [chart0_val hU t hy'.le]
      ring
    rw [chartOp_congr 6 hev, hz] at hA
    have hE := chart0_equation hP hU (Real.sqrt x • e18, t) ⟨ht, by
      show ‖Real.sqrt x • e18‖ ^ 2 < 5 / 8
      rw [hz]
      exact hx58⟩
    have hfun : (fun τ => Hsol G lam U τ x) = fun τ => h0 G lam U τ (Real.sqrt x • e18) :=
      funext fun τ => Hsol_eq_h0 G lam U τ hx.1 (by linarith)
    have hd : HasDerivAt (fun τ => h0 G lam U τ (Real.sqrt x • e18))
        (h0t G lam U t (Real.sqrt x • e18)) t :=
      ((hasDerivAt_Flam_chart hP lam ht.2 _).add (hU.sol.deriv0 t ht _)).add
        (hU.sol.deriv1 t ht (PsiT (Real.sqrt x • e18)))
    rw [hfun, hd.deriv, Hsol_eq_h0 G lam U t hx.1 (by linarith)]
    dsimp only at hE
    rw [hz] at hE
    have e1 : Aop (Hsol G lam U t) x = chartOp 6 (h0 G lam U t) (Real.sqrt x • e18) / 16 := by
      rw [← hA]
      ring
    rw [e1]
    exact hE
  · -- the chart at `x = 1`
    have hw : ‖Real.sqrt (1 - x) • e6‖ ^ 2 = 1 - x := norm_sq_ray6 (by linarith [hx.2])
    have hA := sixteen_Aop_chart1 (V := Flat6) (by simp) hsl (w := Real.sqrt (1 - x) • e6)
      (by rw [hw]; linarith)
    have hev : (fun v : Flat6 => Hsol G lam U t (1 - ‖v‖ ^ 2))
        =ᶠ[𝓝 (Real.sqrt (1 - x) • e6)] U.2.2.1 t := by
      have hopen : IsOpen {v : Flat6 | ‖v‖ ^ 2 < 1 / 2} :=
        isOpen_lt (continuous_norm.pow 2) continuous_const
      have hmem : Real.sqrt (1 - x) • e6 ∈ {v : Flat6 | ‖v‖ ^ 2 < 1 / 2} := by
        show ‖Real.sqrt (1 - x) • e6‖ ^ 2 < 1 / 2
        rw [hw]
        linarith
      filter_upwards [hopen.mem_nhds hmem] with v hv
      have hv' : ‖v‖ ^ 2 < 1 / 2 := hv
      show Flam G lam t (1 - ‖v‖ ^ 2) + valOf U t (1 - ‖v‖ ^ 2) = U.2.2.1 t v
      rw [Flam_of_ge hlam t (by linarith), zero_add, chart1_val hU t hv']
    have h1x : 1 - ‖Real.sqrt (1 - x) • e6‖ ^ 2 = x := by
      rw [hw]
      ring
    rw [chartOp_congr 18 hev, h1x] at hA
    have hE := chart1_equation hP hlam hlam8 hU (Real.sqrt (1 - x) • e6, t) ⟨ht, by
      show ‖Real.sqrt (1 - x) • e6‖ ^ 2 < 1 / 2
      rw [hw]
      linarith⟩
    have hfun : (fun τ => Hsol G lam U τ x) = fun τ => U.2.2.1 τ (Real.sqrt (1 - x) • e6) :=
      funext fun τ => Hsol_eq_U1 hlam hlam8 hU.reg τ (by linarith) hx.2
    rw [hfun, (hU.sol.deriv1 t ht _).deriv, Hsol_eq_U1 hlam hlam8 hU.reg t (by linarith) hx.2]
    dsimp only at hE
    rw [h1x] at hE
    have e1 : Aop (Hsol G lam U t) x
        = chartOp 18 (U.2.2.1 t) (Real.sqrt (1 - x) • e6) / 16 := by
      rw [← hA]
      ring
    rw [e1]
    exact hE

end Calabi.Weighted
