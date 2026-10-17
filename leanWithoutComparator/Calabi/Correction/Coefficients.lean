import Calabi.Correction.RayBounds
import Calabi.Correction.OuterOsc

/-!
# The coefficients of the linearized equation in the two charts

With `H = F_λ + V`, the Calabi flow in the momentum coordinate reads
`P_λ V = -E_λ - N_λ(V)`, where (Section 6 of the manuscript)

  `P_λ = ∂ₜ + b_λ² A + c_λ`,   `b_λ = 1 + v∗ F_λ`,   `c_λ = 2 v∗ b_λ A F_λ`,
  `N_λ(V) = v∗² V² A F_λ + (2 v∗ b_λ V + v∗² V²) A V`.

This file gives the two-chart bounds `B0` of the coefficients, uniformly in the
cut-off radius `λ` and in the time `T ≤ min(λ², 1)` (`coef_bounds`), and of the
residual `E_λ` for a fixed `λ` (`elam_bound`). The weights are those of
Lemma 6.2: `b_λ` has the weight `0`, `c_λ` the weight `-4`, `A F_λ` the weight
`-6`, `v∗` the weight `2`.
-/

open Set
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Osc Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-- The multiplier `b_λ = 1 + v∗ F_λ`. -/
noncomputable def blam (G : ℝ → ℝ) (lam t x : ℝ) : ℝ := 1 + vstar x * Flam G lam t x

/-- The zeroth-order coefficient `c_λ = 2 v∗ b_λ A F_λ`. -/
noncomputable def clam (G : ℝ → ℝ) (lam t x : ℝ) : ℝ :=
  2 * vstar x * blam G lam t x * Aop (Flam G lam t) x

/-- `A F_λ`. -/
noncomputable def aflam (G : ℝ → ℝ) (lam t x : ℝ) : ℝ := Aop (Flam G lam t) x

/-! ### The coefficients near and away from the point orbit -/

theorem blam_of_ge {lam : ℝ} (hlam : 0 < lam) (t : ℝ) {x : ℝ} (hx : 2 * lam ≤ x) :
    blam G lam t x = 1 := by
  unfold blam
  rw [Flam_of_ge hlam t hx, mul_zero, add_zero]

theorem clam_of_gt (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : 2 * lam < x) : clam G lam t x = 0 := by
  unfold clam
  rw [Aop_Flam_of_gt hP hlam ht hx hxl, mul_zero]

theorem blam_of_lt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) {x : ℝ} (hxl : x < lam) :
    blam G lam t x = 1 + vstar x * Fss G t x := by
  unfold blam
  rw [Flam_of_lt hlam t hxl]

theorem clam_of_lt (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : x < lam) :
    clam G lam t x = 2 * vstar x * (1 + vstar x * Fss G t x) * Aop (Fss G t) x := by
  unfold clam
  rw [blam_of_lt hlam t hxl, Aop_Flam_of_lt hP hlam ht hx hxl]

/-- A uniform scaled bound in the momentum coordinate gives a uniform
two-chart bound. -/
theorem B0.of_uosc {n : ℤ} {a : ℝ → ℝ → ℝ → ℝ} (h : UOsc n a) (α : ℝ) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (v : ℝ) (hv : ((2 * n : ℤ) : ℝ) = v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 → B0 α T v K (a lam) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨K, hK, hB⟩ := B0.of_oscE α n hα hα1
  refine ⟨K * M, mul_nonneg hK hM, fun lam T hlam hT hT1 => ?_⟩
  have h1 := hB T M (a lam) (h lam T hlam hT hT1) hM hT1
  rwa [hv] at h1

/-- **The coefficients in the two charts**, uniformly in `λ` and `T`. -/
theorem coef_bounds (hP : IsProfile c G) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      B0 α T 0 K (blam G lam) ∧ B0 α T (-4) K (clam G lam) ∧ B0 α T (-6) K (aflam G lam) ∧
        B0 α T 2 K (fun _ x => vstar x) := by
  obtain ⟨K₁, hK₁, h₁⟩ := B0.of_uosc (uosc_blam hP) α hα hα1 0 (by norm_num)
  obtain ⟨K₂, hK₂, h₂⟩ := B0.of_uosc (uosc_clam hP) α hα hα1 (-4) (by norm_num)
  obtain ⟨K₃, hK₃, h₃⟩ := B0.of_uosc (uosc_AFlam hP) α hα hα1 (-6) (by norm_num)
  obtain ⟨K₄, hK₄, h₄⟩ := B0.of_uosc uosc_vstar α hα hα1 2 (by norm_num)
  refine ⟨K₁ + K₂ + K₃ + K₄, by positivity, fun lam T hlam hT hT1 => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (h₁ lam T hlam hT hT1).mono (by linarith)
  · exact (h₂ lam T hlam hT hT1).mono (by linarith)
  · exact (h₃ lam T hlam hT hT1).mono (by linarith)
  · exact (h₄ lam T hlam hT hT1).mono (by linarith)

/-- **The residual in the two charts**, for a fixed cut-off radius. -/
theorem elam_bound (hP : IsProfile c G) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam T : ℝ), 0 < lam → lam ≤ 1 → T ≤ (lam / 2) ^ 2 → T ≤ 1 →
      B0 α T (-4) (K / lam) (Elam G lam) := by
  obtain ⟨C, hC, h⟩ := elam_osc hP
  obtain ⟨K, hK, hB⟩ := B0.of_oscE α (-2) hα hα1
  refine ⟨K * C, mul_nonneg hK hC, fun lam T hlam hlam1 hT hT1 => ?_⟩
  have h1 := hB T (C / lam) (Elam G lam) (h lam T hlam hlam1 hT hT1) (div_nonneg hC hlam.le) hT1
  have e : ((2 * (-2) : ℤ) : ℝ) = -4 := by norm_num
  rw [e] at h1
  refine h1.mono (le_of_eq ?_)
  ring

/-- The inner form of the residual in the two charts. -/
theorem ein_bound (hP : IsProfile c G) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), T ≤ 1 → B0 α T (-4) K (Ein G) := by
  obtain ⟨K, hK, h⟩ := B0.of_uosc (uosc_Ein hP) α hα hα1 (-4) (by norm_num)
  refine ⟨K, hK, fun T hT1 => ?_⟩
  exact h 1 T one_pos (by rw [one_pow]; exact hT1) hT1

end Calabi.Weighted
