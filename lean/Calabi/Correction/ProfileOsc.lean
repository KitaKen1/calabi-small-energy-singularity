import Calabi.Correction.ProfileJets
import Calabi.Correction.Osc
import Calabi.Radial.Cutoff

/-!
# Scaled bounds for the self-similar solution

The building blocks of Lemma 6.2 of the manuscript in the calculus of
`Osc.lean`, with `ρ = √(-t)`, `y = x/ρ` and `ς = x + ρ = ρ (1 + y)`:

* `osc_G`: `G(x/ρ)` has order zero;
* `osc_Fss`, `tower_Fss`: `∂ₓʲ F = ρ^{-1-j} h^{(j)}(y)` has order `-1 - j`, with
  the time derivative `ρ^{-3-j} G^{(j+1)}(y) / 2` (the cancellation
  `(1 + j) h^{(j)} + y h^{(j+1)} = G^{(j+1)}` is what makes the time derivative
  two orders smaller instead of blowing up like `ρ⁻²`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Osc

open Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-! ### The variables `ρ` and `y` -/

/-- `ς = ρ (1 + y)`. -/
theorem vs_eq {t : ℝ} (ht : t < 0) (x : ℝ) :
    vs t x = Real.sqrt (-t) * (1 + x / Real.sqrt (-t)) := by
  have hρ : Real.sqrt (-t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  unfold vs
  rw [mul_add, mul_one, mul_div_cancel₀ _ hρ]
  ring

theorem hasDerivAt_sqrt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun τ : ℝ => Real.sqrt (-τ)) (-(1 / (2 * Real.sqrt (-t)))) t := by
  have h := (Real.hasDerivAt_sqrt (by linarith : -t ≠ 0)).comp t (hasDerivAt_id' t).neg
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_div_sqrt_neg {t : ℝ} (ht : t < 0) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => x / Real.sqrt (-τ)) (x / (2 * Real.sqrt (-t) ^ 3)) t := by
  have hρ : Real.sqrt (-t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have h := (hasDerivAt_const t x).fun_div (hasDerivAt_sqrt_neg ht) hρ
  refine h.congr_deriv ?_
  field_simp
  ring

/-- A quantity that decays like `(1 + y)^{-m}`, divided by `ρ^k` with `k ≤ m`,
has order `-k`. -/
theorem decay_bound {C ρ y v : ℝ} (hρ : 0 < ρ) (hy : 0 ≤ y) (hC : 0 ≤ C) {m k : ℕ}
    (hkm : k ≤ m) (hv : |v| ≤ C / (1 + y) ^ m) :
    |v / ρ ^ k| ≤ C * (ρ * (1 + y)) ^ (-(k : ℤ)) := by
  have h1y : (1 : ℝ) ≤ 1 + y := by linarith
  have hρk : 0 < ρ ^ k := pow_pos hρ k
  have hyk : 0 < (1 + y) ^ k := pow_pos (by linarith) k
  have h2 : (1 + y) ^ k ≤ (1 + y) ^ m := pow_le_pow_right₀ h1y hkm
  rw [abs_div, abs_of_pos hρk, zpow_neg, zpow_natCast, mul_pow]
  calc |v| / ρ ^ k ≤ C / (1 + y) ^ m / ρ ^ k := div_le_div_of_nonneg_right hv hρk.le
    _ ≤ C / (1 + y) ^ k / ρ ^ k :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hC hyk h2) hρk.le
    _ = C * (ρ ^ k * (1 + y) ^ k)⁻¹ := by
      rw [div_div, div_eq_mul_inv, mul_comm ((1 + y) ^ k)]

/-! ### The profile in the variable `y = x/ρ` -/

/-- **`G(x/ρ)` has order zero.** -/
theorem osc_G (hP : IsProfile c G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
    Osc T 0 C (fun t x => G (x / Real.sqrt (-t)))
      (fun t x => deriv G (x / Real.sqrt (-t)) / Real.sqrt (-t))
      (fun t x => deriv G (x / Real.sqrt (-t)) * (x / (2 * Real.sqrt (-t) ^ 3))) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  obtain ⟨Mu, hMu⟩ := hP.upper
  obtain ⟨κ, hκ, hlow⟩ := hP.lower
  obtain ⟨C1, hC1, hd1⟩ := profile_jet_decay hP 0
  have hG1 : ∀ y : ℝ, 0 ≤ y → |deriv G y| ≤ C1 / (1 + y) ^ 3 := by
    intro y hy
    have h := hd1 y hy
    rwa [zero_add, iteratedDeriv_one, add_zero] at h
  have dG : ∀ y : ℝ, 0 ≤ y → HasDerivAt G (deriv G y) y := by
    intro y hy
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hsm 0 (show y ∈ Ioi (-δ) from by
      rw [mem_Ioi]
      linarith)
    rwa [iteratedDeriv_zero, zero_add, iteratedDeriv_one] at h
  refine ⟨|Mu| + C1, by positivity, fun T => ?_⟩
  have hC : C1 ≤ |Mu| + C1 := by linarith [abs_nonneg Mu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith [ht.2])
    have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
    rw [zpow_zero, mul_one, abs_of_pos (hκ.trans_le (hlow _ hy))]
    exact (hMu _ hy).trans ((le_abs_self Mu).trans (by linarith))
  · intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
    have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
    have h := (dG _ hy).comp x ((hasDerivAt_id' x).div_const (Real.sqrt (-t)))
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  · intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith [ht.2])
    have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
    have h := decay_bound hρ hy hC1 (by norm_num : 1 ≤ 3) (hG1 _ hy)
    rw [pow_one, ← vs_eq ht.2 x] at h
    have e : (0 : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
    rw [e]
    exact h.trans (mul_le_mul_of_nonneg_right hC (zpow_nonneg (vs_pos ht hx).le _))
  · intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
    have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
    exact (dG _ hy).comp t (hasDerivAt_div_sqrt_neg ht x)
  · intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith [ht.2])
    have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
    have h1y : 0 < 1 + x / Real.sqrt (-t) := by linarith
    -- `G′(y) y` decays like `(1 + y)⁻²`
    have hv : |deriv G (x / Real.sqrt (-t)) * (x / Real.sqrt (-t))|
        ≤ C1 / (1 + x / Real.sqrt (-t)) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hy]
      have h3 := hG1 _ hy
      have h4 : C1 / (1 + x / Real.sqrt (-t)) ^ 3 * (x / Real.sqrt (-t))
          ≤ C1 / (1 + x / Real.sqrt (-t)) ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos h1y 3) (pow_pos h1y 2)]
        have h5 : 0 ≤ C1 * (1 + x / Real.sqrt (-t)) ^ 2 :=
          mul_nonneg hC1 (pow_nonneg h1y.le 2)
        nlinarith
      exact (mul_le_mul_of_nonneg_right h3 hy).trans h4
    have h := decay_bound hρ hy hC1 (le_refl 2) hv
    rw [← vs_eq ht.2 x] at h
    have e : (0 : ℤ) - 2 = -((2 : ℕ) : ℤ) := by norm_num
    have e2 : deriv G (x / Real.sqrt (-t)) * (x / (2 * Real.sqrt (-t) ^ 3))
        = deriv G (x / Real.sqrt (-t)) * (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 2 / 2 := by
      field_simp
    have hz : 0 ≤ vs t x ^ (-((2 : ℕ) : ℤ)) := zpow_nonneg (vs_pos ht hx).le _
    rw [e, e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc |deriv G (x / Real.sqrt (-t)) * (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 2| / 2
        ≤ C1 * vs t x ^ (-((2 : ℕ) : ℤ)) / 2 := div_le_div_of_nonneg_right h (by norm_num)
      _ ≤ C1 * vs t x ^ (-((2 : ℕ) : ℤ)) :=
        div_le_self (mul_nonneg hC1 hz) (by norm_num)
      _ ≤ (|Mu| + C1) * vs t x ^ (-((2 : ℕ) : ℤ)) := mul_le_mul_of_nonneg_right hC hz

/-- **The `x`-derivatives of the self-similar solution**: `∂ₓʲ F` has order
`-1 - j`, and its time derivative is `ρ^{-3-j} G^{(j+1)}(y) / 2`. -/
theorem osc_Fss (hP : IsProfile c G) (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
    Osc T (-1 - j) C (fun t x => iteratedDeriv j (Fss G t) x)
      (fun t x => iteratedDeriv (j + 1) (Fss G t) x)
      (fun t x => iteratedDeriv (j + 1) G (x / Real.sqrt (-t))
        / (2 * Real.sqrt (-t) ^ (j + 3))) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  obtain ⟨A0, hA0, ha0⟩ := hfun_jet_decay hP j
  obtain ⟨A1, hA1, ha1⟩ := hfun_jet_decay hP (j + 1)
  obtain ⟨B, hB, hb⟩ := profile_jet_decay hP j
  refine ⟨A0 + A1 + B, by positivity, fun T => ?_⟩
  -- common facts at a point of the domain
  have hpt : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, 0 < Real.sqrt (-t) ∧
      0 ≤ x / Real.sqrt (-t) ∧ -δ * Real.sqrt (-t) < x := by
    intro t ht x hx
    have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
    exact ⟨hρ, div_nonneg hx.1 hρ.le, by nlinarith [hx.1]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    obtain ⟨hρ, hy, hx'⟩ := hpt t ht.2 x hx
    have h := decay_bound hρ hy hA0 (by omega : j + 1 ≤ 1 + j) (ha0 _ hy)
    rw [← vs_eq ht.2 x] at h
    have e : (-1 : ℤ) - j = -((j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [iteratedDeriv_Fss hh ht.2 j hx', e]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (zpow_nonneg (vs_pos ht hx).le _))
  · intro t ht x hx
    obtain ⟨hρ, hy, hx'⟩ := hpt t ht x hx
    exact (hasDerivAt_iteratedDeriv isOpen_Ioi (contDiffOn_Fss hh ht) j hx').hasDerivWithinAt
  · intro t ht x hx
    obtain ⟨hρ, hy, hx'⟩ := hpt t ht.2 x hx
    have h := decay_bound hρ hy hA1 (by omega : j + 2 ≤ 1 + (j + 1)) (ha1 _ hy)
    rw [← vs_eq ht.2 x] at h
    have e : (-1 : ℤ) - j - 1 = -((j + 2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [iteratedDeriv_Fss hh ht.2 (j + 1) hx', e]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (zpow_nonneg (vs_pos ht hx).le _))
  · intro t ht x hx
    obtain ⟨hρ, hy, hx'⟩ := hpt t ht x hx
    have hρ0 := hρ.ne'
    have hymem : x / Real.sqrt (-t) ∈ Ioi (-δ) := by
      rw [mem_Ioi]
      linarith
    have hφ := hasDerivAt_iteratedDeriv isOpen_Ioi hh j hymem
    have hnum := hφ.comp t (hasDerivAt_div_sqrt_neg ht x)
    have hden := (hasDerivAt_sqrt_neg ht).fun_pow (j + 1)
    have hq := hnum.fun_div hden (pow_ne_zero (j + 1) hρ0)
    have hev : (fun τ => iteratedDeriv j (Fss G τ) x) =ᶠ[𝓝 t] fun τ =>
        iteratedDeriv j (hfun G) (x / Real.sqrt (-τ)) / Real.sqrt (-τ) ^ (j + 1) := by
      filter_upwards [Iio_mem_nhds ht] with τ hτ
      have hρτ : 0 < Real.sqrt (-τ) := Real.sqrt_pos.2 (by
        have : τ < 0 := hτ
        linarith)
      exact iteratedDeriv_Fss hh hτ j (by nlinarith [hx.1])
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [← hrel hP hδ hsm j _ hymem]
    simp only [Function.comp_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  · intro t ht x hx
    obtain ⟨hρ, hy, hx'⟩ := hpt t ht.2 x hx
    have h := decay_bound hρ hy hB (by omega : j + 3 ≤ 3 + j) (hb _ hy)
    rw [← vs_eq ht.2 x] at h
    have e : (-1 : ℤ) - j - 2 = -((j + 3 : ℕ) : ℤ) := by
      push_cast
      ring
    have e2 : iteratedDeriv (j + 1) G (x / Real.sqrt (-t)) / (2 * Real.sqrt (-t) ^ (j + 3))
        = iteratedDeriv (j + 1) G (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ (j + 3) / 2 := by
      rw [div_div, mul_comm]
    have hz : 0 ≤ vs t x ^ (-((j + 3 : ℕ) : ℤ)) := zpow_nonneg (vs_pos ht hx).le _
    rw [e, e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc |iteratedDeriv (j + 1) G (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ (j + 3)| / 2
        ≤ B * vs t x ^ (-((j + 3 : ℕ) : ℤ)) / 2 := div_le_div_of_nonneg_right h (by norm_num)
      _ ≤ B * vs t x ^ (-((j + 3 : ℕ) : ℤ)) := div_le_self (mul_nonneg hB hz) (by norm_num)
      _ ≤ (A0 + A1 + B) * vs t x ^ (-((j + 3 : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hz

/-- **The tower of the self-similar solution.** -/
theorem tower_Fss (hP : IsProfile c G) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
    Tower T (-1) C K (fun j t x => iteratedDeriv j (Fss G t) x)
      (fun j t x => iteratedDeriv (j + 1) G (x / Real.sqrt (-t))
        / (2 * Real.sqrt (-t) ^ (j + 3))) := by
  choose C hC hO using fun j => osc_Fss (c := c) (G := G) hP j
  refine ⟨∑ j ∈ Finset.range K, C j, Finset.sum_nonneg fun j _ => hC j, fun T j hj => ?_⟩
  exact (hO j T).mono
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.2 hj))

end Calabi.Osc
