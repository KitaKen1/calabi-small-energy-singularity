import Calabi.Correction.TwoCharts

/-!
# Chart functions as quantities of order zero

A function `h` on the chart at `x = 0` gives the function
`ray0 h (t, x) = h(√x e, t)` of the time and of the momentum coordinate, and
similarly `ray1 h (t, x) = h(√(1 - x) e, t)` for the chart at `x = 1`. If `h`
has a weighted two-point bound on its chart domain and vanishes near the
boundary of the chart (`|z|² > 1/2`, respectively `|w|² > 3/4`), then the
resulting quantity of order zero has the two-chart bound `B0`
(`B0.ray0`, `B0.ray1`). No symmetry of `h` is assumed: in its own chart the
function is evaluated along the ray (`WH.ray`), and it is transferred to the
other chart by the change of chart (`WH.swap`).
-/

open Set
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted

/-- A function on the chart at `x = 0` as a function of the time and of the
momentum coordinate. -/
noncomputable def ray0 (h : Flat18 × ℝ → ℝ) (t x : ℝ) : ℝ := h (Real.sqrt x • e18, t)

/-- A function on the chart at `x = 1` as a function of the time and of the
momentum coordinate. -/
noncomputable def ray1 (h : Flat6 × ℝ → ℝ) (t x : ℝ) : ℝ := h (Real.sqrt (1 - x) • e6, t)

theorem ray0_chart0 (h : Flat18 × ℝ → ℝ) (p : Flat18 × ℝ) :
    ray0 h p.2 (‖p.1‖ ^ 2) = h (rayMap e18 p) := by
  unfold ray0 rayMap
  rw [Real.sqrt_sq (norm_nonneg _)]

theorem ray0_chart1 (h : Flat18 × ℝ → ℝ) (p : Flat6 × ℝ) :
    ray0 h p.2 (1 - ‖p.1‖ ^ 2) = h (swapPt e18 p) := rfl

theorem ray1_chart1 (h : Flat6 × ℝ → ℝ) (p : Flat6 × ℝ) :
    ray1 h p.2 (1 - ‖p.1‖ ^ 2) = h (rayMap e6 p) := by
  unfold ray1 rayMap
  rw [sub_sub_cancel, Real.sqrt_sq (norm_nonneg _)]

theorem ray1_chart0 (h : Flat6 × ℝ → ℝ) (p : Flat18 × ℝ) :
    ray1 h p.2 (‖p.1‖ ^ 2) = h (swapPt e6 p) := rfl

/-- **A function on the chart at `x = 0` as a quantity of order zero.** -/
theorem B0.ray0 (α v : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (T M : ℝ) (h : Flat18 × ℝ → ℝ),
    T ≤ 1 → 0 ≤ M → WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) v M h →
    (∀ p : Flat18 × ℝ, 1 / 2 < ‖p.1‖ ^ 2 → h p = 0) → B0 α T v (K * M) (Weighted.ray0 h) := by
  have hA : 0 ≤ (3 : ℝ) ^ (|v| + |v - α|) := Real.rpow_nonneg (by norm_num) _
  have hB : 0 ≤ (1 / (1 / 3) : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hD : 0 ≤ 1 + (1 + (1 : ℝ) ^ |v|) * (1 / 64 / (3 * (1 / (1 / 3)))) ^ (-α) := by
    have h1 : 0 ≤ (1 : ℝ) ^ |v| := Real.rpow_nonneg zero_le_one _
    have h2 : 0 ≤ (1 / 64 / (3 * (1 / (1 / 3))) : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (1 : ℝ) ^ |v|) h2
    linarith
  have hK : 0 ≤ (3 : ℝ) ^ (|v| + |v - α|) * (1 / (1 / 3)) ^ α
      * (1 + (1 + (1 : ℝ) ^ |v|) * (1 / 64 / (3 * (1 / (1 / 3)))) ^ (-α)) :=
    mul_nonneg (mul_nonneg hA hB) hD
  refine ⟨1 + (3 : ℝ) ^ (|v| + |v - α|) * (1 / (1 / 3)) ^ α
      * (1 + (1 + (1 : ℝ) ^ |v|) * (1 / 64 / (3 * (1 / (1 / 3)))) ^ (-α)), by linarith, ?_⟩
  intro T M h hT hM hf hsupp
  have hKM := mul_nonneg hK hM
  constructor
  · have h1 := hf.ray (e := e18) norm_e18 hM (by norm_num) hα (isScale0 T).pos
      (fun p hp => ⟨hp.1, by rw [norm_rayMap norm_e18]; exact hp.2⟩)
      (fun p _ => sigma_rayMap norm_e18 p)
    refine (h1.congr fun p _ => ray0_chart0 h p).mono (isScale0 T).pos ?_
    linarith
  · have hext := hf.extend_zero0 hM (by norm_num) le_rfl hT
      (fun p hp => hsupp p (by linarith))
    have hsw := hext.swap (e := e18) (s' := fun _ : Flat6 × ℝ => (1 : ℝ)) (Ω' := dom1 T)
      (k := 3) (δ := 1 / 3) norm_e18 hM (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hα (fun p hp => hp.1)
      (fun p hp => by
        have := hp.2
        norm_num
        linarith)
      (fun p hp => sigma_pos p hp.2) (fun _ _ => zero_lt_one)
      (fun p hp => by
        have h1 : sigma (swapPt e18 p) ≤ 2 := sigma_le_two hT hp.1 (by
          rw [norm_sq_swapPt norm_e18 (by linarith [hp.2])]
          linarith [sq_nonneg ‖p.1‖])
        linarith)
      (fun p hp => by
        have h1 := norm_le_sigma (swapPt e18 p)
        rw [norm_swapPt norm_e18] at h1
        have h2 := Real.sqrt_le_sqrt (by linarith [hp.2] : ((1 : ℝ) / 3) ^ 2 ≤ 1 - ‖p.1‖ ^ 2)
        rw [Real.sqrt_sq (by norm_num)] at h2
        linarith)
    have hrg := hsw.radius_ge (isScale1 T) (mul_nonneg (mul_nonneg hM hA) hB) (by norm_num) hα
    refine (hrg.congr fun p _ => ray0_chart1 h p).mono (isScale1 T).pos ?_
    linarith

/-- **A function on the chart at `x = 1` as a quantity of order zero.** -/
theorem B0.ray1 (α v : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (T M : ℝ) (h : Flat6 × ℝ → ℝ),
    T ≤ 1 → 0 ≤ M → WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) v M h →
    (∀ p : Flat6 × ℝ, 3 / 4 < ‖p.1‖ ^ 2 → h p = 0) → B0 α T v (K * M) (Weighted.ray1 h) := by
  have hA : 0 ≤ (1 : ℝ) ^ (|v| + |v - α|) := Real.rpow_nonneg zero_le_one _
  have hB : 0 ≤ (1 / (1 / 2) : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hC : 0 ≤ ((2 : ℝ) * 2) ^ (|v| + |v - α|) := Real.rpow_nonneg (by norm_num) _
  have hD : 0 ≤ 1 + (1 + (2 : ℝ) ^ |v|)
      * (min (1 / 64) (1 / 64 / (1 * (1 / (1 / 2))) / (2 * 2)) : ℝ) ^ (-α) := by
    have h1 : 0 ≤ (2 : ℝ) ^ |v| := Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ (min (1 / 64) (1 / 64 / (1 * (1 / (1 / 2))) / (2 * 2)) : ℝ) ^ (-α) :=
      Real.rpow_nonneg (le_min (by norm_num) (by norm_num)) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ |v|) h2
    linarith
  have hK : 0 ≤ (1 : ℝ) ^ (|v| + |v - α|) * (1 / (1 / 2)) ^ α * ((2 : ℝ) * 2) ^ (|v| + |v - α|)
      * (1 + (1 + (2 : ℝ) ^ |v|)
        * (min (1 / 64) (1 / 64 / (1 * (1 / (1 / 2))) / (2 * 2)) : ℝ) ^ (-α)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD
  refine ⟨1 + (1 : ℝ) ^ (|v| + |v - α|) * (1 / (1 / 2)) ^ α * ((2 : ℝ) * 2) ^ (|v| + |v - α|)
      * (1 + (1 + (2 : ℝ) ^ |v|)
        * (min (1 / 64) (1 / 64 / (1 * (1 / (1 / 2))) / (2 * 2)) : ℝ) ^ (-α)),
    by linarith, ?_⟩
  intro T M h hT hM hf hsupp
  have hKM := mul_nonneg hK hM
  constructor
  · have hext := hf.extend_zero1 hM (by norm_num) le_rfl (fun p hp => hsupp p (by linarith))
    have hsw := hext.swap (e := e6) (s' := fun _ : Flat18 × ℝ => (1 : ℝ)) (Ω' := dom0 T)
      (k := 1) (δ := 1 / 2) norm_e6 hM le_rfl (by norm_num) (by norm_num) (by norm_num) hα
      (fun p hp => hp.1)
      (fun p hp => by
        have := hp.2
        norm_num
        linarith)
      (fun _ _ => zero_lt_one) (fun _ _ => zero_lt_one) (fun _ _ => by norm_num)
      (fun _ _ => by norm_num)
    have hM1 : 0 ≤ M * (1 : ℝ) ^ (|v| + |v - α|) * (1 / (1 / 2)) ^ α :=
      mul_nonneg (mul_nonneg hM hA) hB
    have hss := hsw.scale_supp (s' := sigma (V := Flat18)) (k := 2) (isScale0 T) hM1
      (by norm_num) (by norm_num) (fun _ _ => zero_lt_one)
      (fun p hp hne => by
        have hle : ‖(swapPt e6 p).1‖ ^ 2 ≤ 3 / 4 := by
          by_contra hcon
          exact hne (hsupp _ (not_le.1 hcon))
        rw [norm_sq_swapPt norm_e6 (by linarith [hp.2])] at hle
        have h1 := norm_le_sigma p
        have h2 : (1 : ℝ) / 2 ≤ ‖p.1‖ := by
          have := norm_nonneg p.1
          nlinarith
        have h3 := sigma_le_two0 hT p hp
        constructor <;> linarith)
    have hrg := hss.radius_ge (isScale0 T) (mul_nonneg hM1 hC)
      (lt_min (by norm_num) (by norm_num)) hα
    refine (hrg.congr fun p _ => ray1_chart0 h p).mono (isScale0 T).pos ?_
    linarith
  · have h1 := hf.ray (e := e6) norm_e6 hM (by norm_num) hα (isScale1 T).pos
      (fun p hp => ⟨hp.1, by rw [norm_rayMap norm_e6]; exact hp.2⟩) (fun _ _ => rfl)
    refine (h1.congr fun p _ => ray1_chart1 h p).mono (isScale1 T).pos ?_
    linarith

end Calabi.Weighted
