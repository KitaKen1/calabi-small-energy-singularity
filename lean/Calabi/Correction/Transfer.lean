import Calabi.Correction.ChartSymmetry

/-!
# Transfer between the two charts

On the overlap of the two charts the piece of the solution that lives in the
chart `ℝ⁶` at `x = 1` is transferred to the chart `ℝ¹⁸` at `x = 0` by the map

  `Ψ(z) = ψ(|z|²) e`,   `ψ(s) = √(1 - s)` for `s ≤ 3/4`,

where `ψ` is smooth and positive on the whole line (`PsiT`). For a radial
function `u` on `ℝ⁶` that vanishes for `|w|² > 3/4`,

  `chartOp 6 (u ∘ Ψ)(z) = chartOp 18 u (√(1 - |z|²) e)`   for `|z|² < 3/4`

(`chartOp_transfer`): the two chart operators are the same operator `16 A` in
the momentum coordinate. For smooth profiles this is `sixteen_Aop_chart0` and
`sixteen_Aop_chart1`; for a profile of class `C⁴` it follows by subtracting
the Taylor polynomial of degree four, since both operators have order four.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial

/-- `1 - s` for `s ≤ 3/4`, at least `3/16` everywhere. -/
noncomputable def qT (s : ℝ) : ℝ :=
  1 - (chi (16 * s - 11) * s + (1 - chi (16 * s - 11)) * (13 / 16))

theorem qT_of_le {s : ℝ} (hs : s ≤ 3 / 4) : qT s = 1 - s := by
  unfold qT
  rw [chi_of_le (by linarith)]
  ring

theorem qT_ge (s : ℝ) : 3 / 16 ≤ qT s := by
  unfold qT
  rcases le_or_gt s (13 / 16) with h | h
  · have h0 := chi_nonneg (16 * s - 11)
    have h1 := chi_le_one (16 * s - 11)
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 13 / 16 - s)]
  · rw [chi_of_ge (by linarith)]
    norm_num

theorem contDiff_qT : ContDiff ℝ ∞ qT := by
  have hc : ContDiff ℝ ∞ (fun s : ℝ => chi (16 * s - 11)) :=
    contDiff_chi.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact contDiff_const.sub ((hc.mul contDiff_id).add ((contDiff_const.sub hc).mul contDiff_const))

/-- `√(1 - s)` for `s ≤ 3/4`, smooth and positive everywhere. -/
noncomputable def psiT (s : ℝ) : ℝ := Real.sqrt (qT s)

theorem contDiff_psiT : ContDiff ℝ ∞ psiT :=
  contDiff_qT.sqrt fun s => by
    have := qT_ge s
    linarith

theorem psiT_of_le {s : ℝ} (hs : s ≤ 3 / 4) : psiT s = Real.sqrt (1 - s) := by
  unfold psiT
  rw [qT_of_le hs]

/-- The transfer map from the chart at `x = 0` to the chart at `x = 1`. -/
noncomputable def PsiT (z : Flat18) : Flat6 := psiT (‖z‖ ^ 2) • e6

theorem contDiff_PsiT : ContDiff ℝ ∞ PsiT :=
  (contDiff_psiT.comp (contDiff_norm_sq ℝ)).smul contDiff_const

theorem PsiT_of_le {z : Flat18} (hz : ‖z‖ ^ 2 ≤ 3 / 4) :
    PsiT z = Real.sqrt (1 - ‖z‖ ^ 2) • e6 := by
  unfold PsiT
  rw [psiT_of_le hz]

theorem norm_sq_PsiT (z : Flat18) : ‖PsiT z‖ ^ 2 = qT (‖z‖ ^ 2) := by
  unfold PsiT psiT
  rw [norm_smul, norm_e6, mul_one, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by linarith [qT_ge (‖z‖ ^ 2)])]

set_option maxHeartbeats 3200000 in
/-- **The chart operators of the two charts agree on a transferred radial
function.** -/
theorem chartOp_transfer {u : Flat6 → ℝ} (hu : ContDiff ℝ 4 u)
    (hrad : ∀ (Q : Flat6 ≃ₗᵢ[ℝ] Flat6) (w : Flat6), u (Q w) = u w)
    (hsupp : ∀ w : Flat6, 3 / 4 < ‖w‖ ^ 2 → u w = 0) {z : Flat18} (hz : ‖z‖ ^ 2 < 3 / 4) :
    chartOp 6 (fun y => u (PsiT y)) z = chartOp 18 u (Real.sqrt (1 - ‖z‖ ^ 2) • e6) := by
  rcases lt_or_ge (‖z‖ ^ 2) (1 / 4) with hx | hx
  · -- both sides vanish
    have hL : chartOp 6 (fun y => u (PsiT y)) z = 0 := by
      apply chartOp_eq_zero_of_eventually
      have hopen : IsOpen {y : Flat18 | ‖y‖ ^ 2 < 1 / 4} :=
        isOpen_lt (continuous_norm.pow 2) continuous_const
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hy' : ‖y‖ ^ 2 < 1 / 4 := hy
      apply hsupp
      rw [norm_sq_PsiT, qT_of_le (by linarith)]
      linarith
    have hR : chartOp 18 u (Real.sqrt (1 - ‖z‖ ^ 2) • e6) = 0 := by
      apply chartOp_eq_zero_of_eventually
      have hopen : IsOpen {w : Flat6 | 3 / 4 < ‖w‖ ^ 2} :=
        isOpen_lt continuous_const (continuous_norm.pow 2)
      have hmem : Real.sqrt (1 - ‖z‖ ^ 2) • e6 ∈ {w : Flat6 | 3 / 4 < ‖w‖ ^ 2} := by
        show 3 / 4 < ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2
        rw [norm_sq_ray6 (by linarith)]
        linarith
      filter_upwards [hopen.mem_nhds hmem] with w hw using hsupp w hw
    rw [hL, hR]
  · -- the Taylor polynomial of the profile
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = ‖z‖ ^ 2 := ⟨_, rfl⟩
    have hx34 : x < 3 / 4 := by rw [hxdef]; exact hz
    have hx14 : 1 / 4 ≤ x := by rw [hxdef]; exact hx
    have hpsi4 : ContDiff ℝ 4 psiT := by exact_mod_cast contDiff_infty.1 contDiff_psiT 4
    have hφ : ContDiff ℝ 4 (fun y : ℝ => u (psiT y • e6)) :=
      hu.comp (hpsi4.smul contDiff_const)
    obtain ⟨p, hp, hrem⟩ := exists_taylor_remainder hφ x
    have hp4 : ContDiff ℝ 4 p := by exact_mod_cast contDiff_infty.1 hp 4
    have hr4 : ContDiff ℝ 4 (fun y : ℝ => u (psiT y • e6) - p y) := hφ.sub hp4
    have hr4' : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (fun y : ℝ => u (psiT y • e6) - p y) := by
      exact_mod_cast hr4
    have hρ0 : ContDiff ℝ ∞ (fun y : Flat18 => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
    have hρ1 : ContDiff ℝ ∞ (fun w : Flat6 => 1 - ‖w‖ ^ 2) :=
      contDiff_const.sub (contDiff_norm_sq ℝ)
    have hρ04 : ContDiff ℝ 4 (fun y : Flat18 => ‖y‖ ^ 2) := by
      exact_mod_cast contDiff_infty.1 hρ0 4
    have hρ14 : ContDiff ℝ 4 (fun w : Flat6 => 1 - ‖w‖ ^ 2) := by
      exact_mod_cast contDiff_infty.1 hρ1 4
    obtain ⟨C0, hC0, H0⟩ := chartOp_point_bound (V := Flat18) 6
    obtain ⟨C1, hC1, H1⟩ := chartOp_point_bound (V := Flat6) 18
    -- the chart at `x = 0`
    have hz1 : ‖z‖ ≤ 1 := by nlinarith [norm_nonneg z]
    have hrem0 : chartOp 6 (fun y : Flat18 => u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2)) z = 0 := by
      have hjets := iteratedFDeriv_comp_eq_zero hρ0 z 4 (fun y : ℝ => u (psiT y • e6) - p y) hr4'
        (fun j hj => by
          show iteratedDeriv j (fun y : ℝ => u (psiT y • e6) - p y) (‖z‖ ^ 2) = 0
          rw [← hxdef]
          exact hrem j hj)
      have hb := H0 (fun y : Flat18 => u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2)) z 0
        (hr4.comp hρ04) hz1 le_rfl (fun j hj => by
          have := hjets j hj
          rw [this, norm_zero])
      rw [mul_zero] at hb
      exact abs_eq_zero.1 (le_antisymm hb (abs_nonneg _))
    have hpol0 : chartOp 6 (fun y : Flat18 => p (‖y‖ ^ 2)) z = 16 * Aop p x := by
      rw [hxdef]
      exact (sixteen_Aop_chart0 (V := Flat18) (by simp) hp.contDiffOn (by linarith)).symm
    have hL : chartOp 6 (fun y => u (PsiT y)) z = 16 * Aop p x := by
      have e : (fun y : Flat18 => u (PsiT y))
          = fun y => p (‖y‖ ^ 2) + (u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2)) := by
        funext y
        show u (psiT (‖y‖ ^ 2) • e6) = _
        ring
      have hadd0 : chartOp 6 (fun y : Flat18 => p (‖y‖ ^ 2)
            + (u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2))) z
          = chartOp 6 (fun y : Flat18 => p (‖y‖ ^ 2)) z
            + chartOp 6 (fun y : Flat18 => u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2)) z :=
        chartOp_add 6 (u := fun y : Flat18 => p (‖y‖ ^ 2))
          (v := fun y : Flat18 => u (psiT (‖y‖ ^ 2) • e6) - p (‖y‖ ^ 2)) (hp4.comp hρ04)
          (hr4.comp hρ04) z
      rw [e, hadd0, hpol0, hrem0, add_zero]
    -- the chart at `x = 1`
    have hw0sq : ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2 = 1 - ‖z‖ ^ 2 := norm_sq_ray6 (by linarith)
    have hw1 : ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ≤ 1 := by
      have h1 : ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2 ≤ 1 := by
        rw [hw0sq]
        linarith [sq_nonneg ‖z‖]
      nlinarith [norm_nonneg (Real.sqrt (1 - ‖z‖ ^ 2) • e6)]
    have hρw : 1 - ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2 = x := by
      rw [hw0sq, hxdef]
      ring
    have hrem1 : chartOp 18 (fun w : Flat6 => u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2))
        (Real.sqrt (1 - ‖z‖ ^ 2) • e6) = 0 := by
      have hjets := iteratedFDeriv_comp_eq_zero hρ1 (Real.sqrt (1 - ‖z‖ ^ 2) • e6) 4
        (fun y : ℝ => u (psiT y • e6) - p y) hr4' (fun j hj => by
          show iteratedDeriv j (fun y : ℝ => u (psiT y • e6) - p y)
            (1 - ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2) = 0
          rw [hρw]
          exact hrem j hj)
      have hb := H1 (fun w : Flat6 => u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2))
        (Real.sqrt (1 - ‖z‖ ^ 2) • e6) 0 (hr4.comp hρ14) hw1 le_rfl (fun j hj => by
          have := hjets j hj
          rw [this, norm_zero])
      rw [mul_zero] at hb
      exact abs_eq_zero.1 (le_antisymm hb (abs_nonneg _))
    have hpol1 : chartOp 18 (fun w : Flat6 => p (1 - ‖w‖ ^ 2)) (Real.sqrt (1 - ‖z‖ ^ 2) • e6)
        = 16 * Aop p x := by
      have h1 := sixteen_Aop_chart1 (V := Flat6) (by simp) hp.contDiffOn
        (w := Real.sqrt (1 - ‖z‖ ^ 2) • e6) (by rw [hw0sq]; linarith)
      rw [hρw] at h1
      exact h1.symm
    have hev : u =ᶠ[𝓝 (Real.sqrt (1 - ‖z‖ ^ 2) • e6)]
        fun w : Flat6 => p (1 - ‖w‖ ^ 2) + (u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2)) := by
      have hopen : IsOpen {w : Flat6 | 1 / 4 < ‖w‖ ^ 2} :=
        isOpen_lt continuous_const (continuous_norm.pow 2)
      have hmem : Real.sqrt (1 - ‖z‖ ^ 2) • e6 ∈ {w : Flat6 | 1 / 4 < ‖w‖ ^ 2} := by
        show 1 / 4 < ‖Real.sqrt (1 - ‖z‖ ^ 2) • e6‖ ^ 2
        rw [hw0sq]
        linarith
      filter_upwards [hopen.mem_nhds hmem] with w hw
      have hw' : 1 / 4 < ‖w‖ ^ 2 := hw
      have e1 : psiT (1 - ‖w‖ ^ 2) = ‖w‖ := by
        rw [psiT_of_le (by linarith), sub_sub_cancel, Real.sqrt_sq (norm_nonneg w)]
      have e2 : u (‖w‖ • e6) = u w :=
        radial_eq_of_norm_eq hrad (by rw [norm_smul, norm_e6, mul_one, norm_norm])
      rw [e1, e2]
      ring
    have hadd1 : chartOp 18 (fun w : Flat6 => p (1 - ‖w‖ ^ 2)
          + (u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2))) (Real.sqrt (1 - ‖z‖ ^ 2) • e6)
        = chartOp 18 (fun w : Flat6 => p (1 - ‖w‖ ^ 2)) (Real.sqrt (1 - ‖z‖ ^ 2) • e6)
          + chartOp 18 (fun w : Flat6 => u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2))
            (Real.sqrt (1 - ‖z‖ ^ 2) • e6) :=
      chartOp_add 18 (u := fun w : Flat6 => p (1 - ‖w‖ ^ 2))
        (v := fun w : Flat6 => u (psiT (1 - ‖w‖ ^ 2) • e6) - p (1 - ‖w‖ ^ 2)) (hp4.comp hρ14)
        (hr4.comp hρ14) _
    rw [hL, chartOp_congr 18 hev, hadd1, hpol1, hrem1, add_zero]

end Calabi.Weighted
