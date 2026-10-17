import Calabi.Correction.ResidualOsc

/-!
# Freezing the profile at the singular time

Away from the concentrating point, `G(x/ρ)` is close to its limit `c` at the
singular time: for `ρ = √(-t) ≤ x`,

  `|G(x/ρ) - c| ≤ C (−t)/x²`,  `|∂ₓ G(x/ρ)| ≤ C (−t)/x³`,  `|∂ₜ G(x/ρ)| ≤ C/x²`

(`frozen_bounds`). In the outer region `x ≥ β²/4` of Section 6.2 of the
manuscript and for `-t ≤ T = η β⁴` the first two are `O(η)`. This is what
allows the outer problem to be solved with the time-independent multiplier
`1 + (1 - x) χ(x/λ) (c - 1)`, the difference being an error term.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Osc

open Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-- **The profile converges to `c` at the rate `y⁻²`.** -/
theorem profile_sub_limit (hP : IsProfile c G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → |G y - c| ≤ C / y ^ 2 := by
  obtain ⟨H, hH, hH0, hm⟩ := hP.compact
  obtain ⟨Mu, hMu⟩ := hP.upper
  obtain ⟨κ, hκ, hlow⟩ := hP.lower
  have hGH : ∀ y : ℝ, 0 < y → G y = H ((y ^ 2)⁻¹) := by
    intro y hy
    have h := hm ((y ^ 2)⁻¹) (inv_pos.2 (pow_pos hy 2))
    rw [inv_sq_rpow hy] at h
    exact h.symm
  have hd : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (halfDeriv H 1 v) (Icc 0 1) v := by
    intro v hv
    have h1 : DifferentiableWithinAt ℝ H (Ici 0) v := hH.differentiableOn (by simp) v hv.1
    exact h1.hasDerivWithinAt.mono Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiffOn_halfDeriv hH 1).continuousOn.mono Icc_subset_Ici_self)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨B + |Mu| + |c|, by positivity, fun y hy => ?_⟩
  have hy2 : 0 < y ^ 2 := pow_pos hy 2
  rw [le_div_iff₀ hy2]
  rcases le_total 1 y with h1 | h1
  · -- `u = y⁻² ≤ 1`: the mean value theorem for `H`
    have hu0 : 0 ≤ (y ^ 2)⁻¹ := (inv_pos.2 hy2).le
    have hu1 : (y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun v hv => hB v hv) ⟨le_rfl, zero_le_one⟩ ⟨hu0, hu1⟩
    rw [hH0, ← hGH y hy, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0] at hmv
    calc |G y - c| * y ^ 2 ≤ B * (y ^ 2)⁻¹ * y ^ 2 := mul_le_mul_of_nonneg_right hmv hy2.le
      _ = B := by rw [mul_assoc, inv_mul_cancel₀ hy2.ne', mul_one]
      _ ≤ B + |Mu| + |c| := by linarith [abs_nonneg Mu, abs_nonneg c]
  · -- `y ≤ 1`: boundedness
    have hGy : |G y| ≤ |Mu| := by
      rw [abs_of_pos (hκ.trans_le (hlow y hy.le))]
      exact (hMu y hy.le).trans (le_abs_self Mu)
    have h2 : |G y - c| ≤ |Mu| + |c| := (abs_sub _ _).trans (add_le_add hGy le_rfl)
    have h3 : y ^ 2 ≤ 1 := pow_le_one₀ hy.le h1
    calc |G y - c| * y ^ 2 ≤ (|Mu| + |c|) * 1 :=
          mul_le_mul h2 h3 hy2.le (by positivity)
      _ ≤ B + |Mu| + |c| := by linarith

/-- **The profile and its derivatives away from the concentrating point.** -/
theorem frozen_bounds (hP : IsProfile c G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ, t < 0 →
    Real.sqrt (-t) ≤ x →
    |G (x / Real.sqrt (-t)) - c| ≤ C * (-t) / x ^ 2 ∧
      |deriv G (x / Real.sqrt (-t)) / Real.sqrt (-t)| ≤ C * (-t) / x ^ 3 ∧
      |deriv G (x / Real.sqrt (-t)) * (x / (2 * Real.sqrt (-t) ^ 3))| ≤ C / x ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := profile_sub_limit hP
  obtain ⟨C1, hC1, hd1⟩ := profile_jet_decay hP 0
  refine ⟨C0 + C1, add_nonneg hC0 hC1, fun t x ht hρx => ?_⟩
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hx : 0 < x := hρ.trans_le hρx
  have hsq : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt (by linarith)
  have hy : 0 < x / Real.sqrt (-t) := div_pos hx hρ
  have hG1 : |deriv G (x / Real.sqrt (-t))| ≤ C1 / (x / Real.sqrt (-t)) ^ 3 := by
    have h := hd1 _ hy.le
    rw [zero_add, iteratedDeriv_one, add_zero] at h
    refine h.trans (div_le_div_of_nonneg_left hC1 (pow_pos hy 3) ?_)
    exact pow_le_pow_left₀ hy.le (by linarith) 3
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hρ3 : 0 < Real.sqrt (-t) ^ 3 := pow_pos hρ 3
  have e3 : Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * (-t) := by
    calc Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * Real.sqrt (-t) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) := by rw [hsq]
  -- `C1 / y³ = C1 ρ³ / x³`
  have ey : C1 / (x / Real.sqrt (-t)) ^ 3 = C1 * Real.sqrt (-t) ^ 3 / x ^ 3 := by
    rw [div_pow, div_div_eq_mul_div]
  rw [ey] at hG1
  have hnt : 0 < -t := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := h0 _ hy
    have e : C0 / (x / Real.sqrt (-t)) ^ 2 = C0 * (-t) / x ^ 2 := by
      rw [div_pow, div_div_eq_mul_div, hsq]
    rw [e] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ hx2.le)
    exact mul_le_mul_of_nonneg_right (by linarith) hnt.le
  · rw [abs_div, abs_of_pos hρ, div_le_div_iff₀ hρ hx3]
    have h1 : |deriv G (x / Real.sqrt (-t))| * x ^ 3 ≤ C1 * Real.sqrt (-t) ^ 3 := by
      rwa [le_div_iff₀ hx3] at hG1
    calc |deriv G (x / Real.sqrt (-t))| * x ^ 3 ≤ C1 * Real.sqrt (-t) ^ 3 := h1
      _ = C1 * (-t) * Real.sqrt (-t) := by
        rw [e3]
        ring
      _ ≤ (C0 + C1) * (-t) * Real.sqrt (-t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hnt.le) hρ.le
  · have h2 : 0 < 2 * Real.sqrt (-t) ^ 3 := by positivity
    rw [abs_mul, abs_of_pos (div_pos hx h2)]
    have h1 : |deriv G (x / Real.sqrt (-t))| * x ^ 3 ≤ C1 * Real.sqrt (-t) ^ 3 := by
      rwa [le_div_iff₀ hx3] at hG1
    rw [le_div_iff₀ hx2]
    calc |deriv G (x / Real.sqrt (-t))| * (x / (2 * Real.sqrt (-t) ^ 3)) * x ^ 2
        = |deriv G (x / Real.sqrt (-t))| * x ^ 3 / (2 * Real.sqrt (-t) ^ 3) := by
          field_simp
      _ ≤ C1 * Real.sqrt (-t) ^ 3 / (2 * Real.sqrt (-t) ^ 3) :=
          div_le_div_of_nonneg_right h1 h2.le
      _ = C1 / 2 := by
          field_simp
      _ ≤ C0 + C1 := by linarith

end Calabi.Osc
