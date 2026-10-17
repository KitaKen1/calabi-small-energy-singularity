import Calabi.Correction.OscChart
import Calabi.Correction.FrozenOsc

/-!
# Lemma 6.2 in the flat chart

The scaled bounds of `ResidualOsc.lean` in the chart `x = |z|²`, as weighted
two-point bounds for the scale `σ = (|z|² + √(-t))^{1/2}` on
`{|z| ≤ 1} × [-T, 0)`, with constants that do not depend on the cut-off radius
`λ` or on the time `T ≤ min(λ², 1)` (`UOsc.toWH`). The weights are twice the
orders: `A F_λ` and the residual `E_λ` have the weight `-6`, the inner form of
the residual `-4`, the multiplier `b_λ` the weight `0`, and the mismatch of the
principal and of the zeroth-order coefficient the weights `2` and `-2`
(`Osc(σ⁻⁶)`, `Osc(σ⁻⁴)`, `Osc(1)`, `σ⁴⁻|ν| d_ν = Osc(σ²)` in the notation of the
manuscript).
-/

open Set

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Osc Calabi.Flat Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Uniform scaled bounds in the momentum coordinate give uniform weighted
two-point bounds in the flat chart.** -/
theorem _root_.Calabi.Osc.UOsc.toWH {n : ℤ} {c : ℝ → ℝ → ℝ → ℝ} (h : UOsc n c) {α a : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1}
        ((2 * n : ℤ) : ℝ) M (fun p => c lam p.2 (‖p.1‖ ^ 2)) := by
  obtain ⟨M, hM, h⟩ := h
  refine ⟨2 * ((1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M),
    by positivity, fun lam T hlam hT hT1 => ?_⟩
  exact OscE.toWH (h lam T hlam hT hT1) hM hα hα1 ha

variable {c : ℝ} {G : ℝ → ℝ} {α a : ℝ}

/-- `A F_λ = Osc(σ⁻⁶)` in the chart. -/
theorem chart_AFlam (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} (-6) M
        (fun p => Aop (Flam G lam p.2) (‖p.1‖ ^ 2)) := by
  have h := (uosc_AFlam hP).toWH (V := V) hα hα1 ha
  have e : (((2 * (-3) : ℤ)) : ℝ) = -6 := by norm_num
  rwa [e] at h

/-- The residual `E_λ` has the weight `-6` in the chart. -/
theorem chart_Elam (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} (-6) M
        (fun p => Elam G lam p.2 (‖p.1‖ ^ 2)) := by
  have h := (uosc_Elam hP).toWH (V := V) hα hα1 ha
  have e : (((2 * (-3) : ℤ)) : ℝ) = -6 := by norm_num
  rwa [e] at h

/-- The inner form of the residual has the weight `-4` in the chart. -/
theorem chart_Ein (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} (-4) M
        (fun p => Ein G p.2 (‖p.1‖ ^ 2)) := by
  have h := (uosc_Ein hP).toWH (V := V) hα hα1 ha
  have e : (((2 * (-2) : ℤ)) : ℝ) = -4 := by norm_num
  rwa [e] at h

/-- The multiplier `b_λ` has the weight `0` in the chart. -/
theorem chart_blam (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} 0 M
        (fun p => 1 + vstar (‖p.1‖ ^ 2) * Flam G lam p.2 (‖p.1‖ ^ 2)) := by
  have h := (uosc_blam hP).toWH (V := V) hα hα1 ha
  have e : (((2 * 0 : ℤ)) : ℝ) = 0 := by norm_num
  rwa [e] at h

/-- The mismatch of the principal coefficient has the weight `2` in the chart. -/
theorem chart_Pmis (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} 2 M
        (fun p => (1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2)) ^ 2 * (1 - ‖p.1‖ ^ 2) ^ 2
          - G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) ^ 2) := by
  have h := (uosc_Pmis hP).toWH (V := V) hα hα1 ha
  have e : (((2 * 1 : ℤ)) : ℝ) = 2 := by norm_num
  rwa [e] at h

/-- The mismatch of the zeroth-order coefficient has the weight `-2` in the
chart. -/
theorem chart_cmis (hP : IsProfile c G) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha : a ≤ 1 / 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 →
      WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} (-2) M
        (fun p => 2 * vstar (‖p.1‖ ^ 2) * (1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2))
            * Aop (Fss G p.2) (‖p.1‖ ^ 2)
          - 2 * ‖p.1‖ ^ 2 * G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) * AhatF G p.2 (‖p.1‖ ^ 2)) := by
  have h := (uosc_cmis hP).toWH (V := V) hα hα1 ha
  have e : (((2 * (-1) : ℤ)) : ℝ) = -2 := by norm_num
  rwa [e] at h

end Calabi.Weighted
