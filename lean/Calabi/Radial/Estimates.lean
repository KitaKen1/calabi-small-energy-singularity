import Calabi.Radial.Cutoff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# From the localized correction to the radial statement

`LocalizedCorrection G` is the conclusion of Proposition 6.1 of the manuscript
in the pointwise form used in Section 7: for every cutoff radius `λ` and every
small `e`, on arbitrarily short time intervals there is a solution `H` of the
Calabi flow in the momentum coordinate with uniform positivity bounds and

  `|H - F_λ| ≤ C e (x + ρ)^{-1+δ}`,   `|K(H) - K(F_λ)| ≤ C e (x + ρ)^{-1+δ}`.

`RadialMain G` is the main theorem in the momentum coordinate for `p = 2`:
solutions on arbitrarily short intervals with uniform positivity bounds,
arbitrarily small Calabi energy `∫ K(H)² 7 x⁶ dx`, arbitrarily small first
moment `∫ x |H| dx` (which bounds the initial potential), and
`√(-t) H(t, 0) → G′(0)`, the blow-up of the scalar curvature `56 (1 - H(t, 0))`
at the point orbit.

`radialMain_of_correction` derives the second from the first: Sections 7.1,
7.2 and the choice of parameters of Section 7.4. The localized correction
itself (Sections 4 to 6) is not proved here.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-- The conclusion of Proposition 6.1 in the pointwise form used in Section 7. -/
def LocalizedCorrection (G : ℝ → ℝ) : Prop :=
  ∃ δ κ₁ κ₂ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ₁ ∧ 0 ≤ C ∧
    ∀ lam : ℝ, 0 < lam → lam < 1 / 8 → ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e ≤ e₀ →
      ∀ T₀ : ℝ, 0 < T₀ → ∃ (T : ℝ) (H : ℝ → ℝ → ℝ), 0 < T ∧ T < T₀ ∧ IsRadialFlow T H ∧
        ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
          κ₁ ≤ 1 + vstar x * H t x ∧ 1 + vstar x * H t x ≤ κ₂ ∧
          |H t x - Flam G lam t x| ≤ C * e * (x + Real.sqrt (-t)) ^ (-1 + δ) ∧
          |Kop (H t) x - Kop (Flam G lam t) x| ≤ C * e * (x + Real.sqrt (-t)) ^ (-1 + δ)

/-- The main theorem in the momentum coordinate, for `p = 2`. -/
def RadialMain (G : ℝ → ℝ) : Prop :=
  ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (H : ℝ → ℝ → ℝ), 0 < T ∧ T < τ ∧ IsRadialFlow T H ∧
      (∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
        κ₁ ≤ 1 + vstar x * H t x ∧ 1 + vstar x * H t x ≤ κ₂) ∧
      (∀ t ∈ Ioo (-T) 0, ∫ x in (0 : ℝ)..1, Kop (H t) x ^ 2 * (7 * x ^ 6) < ε) ∧
      (∀ t ∈ Ioo (-T) 0, ∫ x in (0 : ℝ)..1, x * |H t x| < ε) ∧
      Tendsto (fun t => Real.sqrt (-t) * H t 0) (𝓝[<] 0) (𝓝 (deriv G 0))

theorem IsRadialFlow.slice {T : ℝ} {H : ℝ → ℝ → ℝ} (h : IsRadialFlow T H) {t : ℝ}
    (ht : t ∈ Ioo (-T) 0) : ContDiffOn ℝ ∞ (H t) (Icc 0 1) := by
  have hi : ContDiffOn ℝ ∞ (fun x : ℝ => ((t, x) : ℝ × ℝ)) (Icc 0 1) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  exact h.smooth.comp hi fun x hx => ⟨ht, hx⟩

/-- `(x + ρ)^{-1+δ} ≤ 2 / x` for `0 < x ≤ 1`, `0 < ρ ≤ 1`, `0 ≤ δ ≤ 1`. -/
theorem weight_le {x ρ δ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : (x + ρ) ^ (-1 + δ) ≤ 2 / x := by
  have hs : 0 < x + ρ := by linarith
  rw [Real.rpow_add hs, Real.rpow_neg_one]
  have h1 : (x + ρ) ^ δ ≤ 2 := by
    calc (x + ρ) ^ δ ≤ (2 : ℝ) ^ δ := Real.rpow_le_rpow hs.le (by linarith) hδ
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := Real.rpow_one 2
  have h2 : (x + ρ)⁻¹ ≤ x⁻¹ := inv_anti₀ hx (by linarith)
  calc (x + ρ)⁻¹ * (x + ρ) ^ δ ≤ x⁻¹ * 2 :=
        mul_le_mul h2 h1 (Real.rpow_nonneg hs.le δ) (inv_pos.2 hx).le
    _ = 2 / x := by ring

/-- The curvature integral, Section 7.1 with `p = 2`. -/
theorem energy_le {K K₀ : ℝ → ℝ} {C₁ C e ρ δ lam : ℝ} (hK : ContinuousOn K (Icc 0 1))
    (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C) (he : 0 ≤ e) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : 2 * lam ≤ 1)
    (h₀ : ∀ x ∈ Icc (0 : ℝ) 1, |K₀ x| ≤ C₁ / (x + ρ))
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 2 * lam < x → K₀ x = 0)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, |K x - K₀ x| ≤ C * e * (x + ρ) ^ (-1 + δ)) :
    ∫ x in (0 : ℝ)..1, K x ^ 2 * (7 * x ^ 6)
      ≤ 14 * C₁ ^ 2 * (2 * lam) ^ 5 / 5 + 56 * C ^ 2 * e ^ 2 / 5 := by
  have hf : ContinuousOn (fun x : ℝ => K x ^ 2 * (7 * x ^ 6)) (Icc 0 1) :=
    (hK.pow 2).mul (continuousOn_const.mul (continuousOn_id.pow 6))
  have h2l : (0 : ℝ) ≤ 2 * lam := by linarith
  have hi1 : IntervalIntegrable (fun x : ℝ => K x ^ 2 * (7 * x ^ 6)) MeasureTheory.volume 0
      (2 * lam) := (hf.mono (Icc_subset_Icc le_rfl hlam1)).intervalIntegrable_of_Icc h2l
  have hi2 : IntervalIntegrable (fun x : ℝ => K x ^ 2 * (7 * x ^ 6)) MeasureTheory.volume
      (2 * lam) 1 := (hf.mono (Icc_subset_Icc h2l le_rfl)).intervalIntegrable_of_Icc hlam1
  have key : ∀ x ∈ Icc (0 : ℝ) 1, ∀ B : ℝ, |K₀ x| * x ≤ B →
      K x ^ 2 * (7 * x ^ 6) ≤ 7 * (B + 2 * C * e) ^ 2 * x ^ 4 := by
    intro x hx B hB0
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rw [← h0]
      simp
    · have hw := weight_le h0 hx.2 hρ hρ1 hδ hδ1
      have hdx := hd x hx
      have hx0 := h0.ne'
      have h1 : |K x - K₀ x| * x ≤ 2 * C * e := by
        have hm : C * e * (x + ρ) ^ (-1 + δ) ≤ C * e * (2 / x) :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg hC he)
        calc |K x - K₀ x| * x ≤ C * e * (2 / x) * x :=
              mul_le_mul_of_nonneg_right (hdx.trans hm) h0.le
          _ = 2 * C * e := by field_simp
      have h2 : |K x| * x ≤ B + 2 * C * e := by
        have htri : |K x| ≤ |K₀ x| + |K x - K₀ x| := by
          have h := abs_add_le (K₀ x) (K x - K₀ x)
          rwa [add_sub_cancel] at h
        nlinarith [mul_le_mul_of_nonneg_right htri h0.le]
      have h3 : 0 ≤ |K x| * x := mul_nonneg (abs_nonneg _) h0.le
      have h4 : (|K x| * x) ^ 2 ≤ (B + 2 * C * e) ^ 2 := pow_le_pow_left₀ h3 h2 2
      have e1 : K x ^ 2 * (7 * x ^ 6) = 7 * (|K x| * x) ^ 2 * x ^ 4 := by
        rw [mul_pow, sq_abs]
        ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num))
        (by positivity)
  have hB1 : ∀ x ∈ Icc (0 : ℝ) 1, |K₀ x| * x ≤ C₁ := by
    intro x hx
    have hpos : 0 < x + ρ := by linarith [hx.1]
    calc |K₀ x| * x ≤ C₁ / (x + ρ) * x := mul_le_mul_of_nonneg_right (h₀ x hx) hx.1
      _ ≤ C₁ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        nlinarith [mul_nonneg hC₁ hρ.le]
  have b1 : ∫ x in (0 : ℝ)..(2 * lam), K x ^ 2 * (7 * x ^ 6)
      ≤ ∫ x in (0 : ℝ)..(2 * lam), 7 * (C₁ + 2 * C * e) ^ 2 * x ^ 4 := by
    refine intervalIntegral.integral_mono_on h2l hi1
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx => ?_
    exact key x ⟨hx.1, hx.2.trans hlam1⟩ C₁ (hB1 x ⟨hx.1, hx.2.trans hlam1⟩)
  have b2 : ∫ x in (2 * lam)..(1 : ℝ), K x ^ 2 * (7 * x ^ 6)
      ≤ ∫ x in (2 * lam)..(1 : ℝ), 7 * (0 + 2 * C * e) ^ 2 * x ^ 4 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hlam1 hi2
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx => ?_
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
    exact key x hxI 0 (by rw [hz x hxI hx.1, abs_zero, zero_mul])
  have e1 : ∫ x in (0 : ℝ)..(2 * lam), 7 * (C₁ + 2 * C * e) ^ 2 * x ^ 4
      = 7 * (C₁ + 2 * C * e) ^ 2 * ((2 * lam) ^ 5 / 5) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have e2 : ∫ x in (2 * lam)..(1 : ℝ), 7 * (0 + 2 * C * e) ^ 2 * x ^ 4
      = 7 * (0 + 2 * C * e) ^ 2 * ((1 - (2 * lam) ^ 5) / 5) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hsum := add_le_add b1 b2
  rw [e1, e2] at hsum
  refine hsum.trans ?_
  have hq : (C₁ + 2 * C * e) ^ 2 ≤ 2 * C₁ ^ 2 + 8 * C ^ 2 * e ^ 2 := by
    nlinarith [sq_nonneg (C₁ - 2 * C * e)]
  have hL : (0 : ℝ) ≤ (2 * lam) ^ 5 := by positivity
  have hL1 : (2 * lam) ^ 5 ≤ 1 := pow_le_one₀ h2l hlam1
  nlinarith [mul_le_mul_of_nonneg_right hq hL,
    mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg e)) (by linarith : (0 : ℝ) ≤ 1 - (2 * lam) ^ 5)]

/-- The first moment, which bounds the potential: Section 7.2. -/
theorem moment_le {F F₀ : ℝ → ℝ} {C₁ C e ρ δ lam : ℝ} (hF : ContinuousOn F (Icc 0 1))
    (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C) (he : 0 ≤ e) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : 2 * lam ≤ 1)
    (h₀ : ∀ x ∈ Icc (0 : ℝ) 1, |F₀ x| ≤ C₁ / (x + ρ))
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 2 * lam ≤ x → F₀ x = 0)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, |F x - F₀ x| ≤ C * e * (x + ρ) ^ (-1 + δ)) :
    ∫ x in (0 : ℝ)..1, x * |F x| ≤ 2 * lam * C₁ + 2 * C * e := by
  have hf : ContinuousOn (fun x : ℝ => x * |F x|) (Icc 0 1) :=
    continuousOn_id.mul (continuous_abs.comp_continuousOn hF)
  have h2l : (0 : ℝ) ≤ 2 * lam := by linarith
  have hi1 : IntervalIntegrable (fun x : ℝ => x * |F x|) MeasureTheory.volume 0 (2 * lam) :=
    (hf.mono (Icc_subset_Icc le_rfl hlam1)).intervalIntegrable_of_Icc h2l
  have hi2 : IntervalIntegrable (fun x : ℝ => x * |F x|) MeasureTheory.volume (2 * lam) 1 :=
    (hf.mono (Icc_subset_Icc h2l le_rfl)).intervalIntegrable_of_Icc hlam1
  have hCe : 0 ≤ 2 * C * e := by positivity
  have key : ∀ x ∈ Icc (0 : ℝ) 1, ∀ B : ℝ, 0 ≤ B → |F₀ x| * x ≤ B →
      x * |F x| ≤ B + 2 * C * e := by
    intro x hx B hB hB0
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rw [← h0, zero_mul]
      linarith
    · have hw := weight_le h0 hx.2 hρ hρ1 hδ hδ1
      have hdx := hd x hx
      have hx0 := h0.ne'
      have h1 : |F x - F₀ x| * x ≤ 2 * C * e := by
        have hm : C * e * (x + ρ) ^ (-1 + δ) ≤ C * e * (2 / x) :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg hC he)
        calc |F x - F₀ x| * x ≤ C * e * (2 / x) * x :=
              mul_le_mul_of_nonneg_right (hdx.trans hm) h0.le
          _ = 2 * C * e := by field_simp
      have htri : |F x| ≤ |F₀ x| + |F x - F₀ x| := by
        have h := abs_add_le (F₀ x) (F x - F₀ x)
        rwa [add_sub_cancel] at h
      nlinarith [mul_le_mul_of_nonneg_right htri h0.le]
  have hB1 : ∀ x ∈ Icc (0 : ℝ) 1, |F₀ x| * x ≤ C₁ := by
    intro x hx
    have hpos : 0 < x + ρ := by linarith [hx.1]
    calc |F₀ x| * x ≤ C₁ / (x + ρ) * x := mul_le_mul_of_nonneg_right (h₀ x hx) hx.1
      _ ≤ C₁ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        nlinarith [mul_nonneg hC₁ hρ.le]
  have b1 : ∫ x in (0 : ℝ)..(2 * lam), x * |F x|
      ≤ ∫ _ in (0 : ℝ)..(2 * lam), (C₁ + 2 * C * e) := by
    refine intervalIntegral.integral_mono_on h2l hi1
      (Continuous.intervalIntegrable continuous_const _ _) fun x hx => ?_
    exact key x ⟨hx.1, hx.2.trans hlam1⟩ C₁ hC₁ (hB1 x ⟨hx.1, hx.2.trans hlam1⟩)
  have b2 : ∫ x in (2 * lam)..(1 : ℝ), x * |F x|
      ≤ ∫ _ in (2 * lam)..(1 : ℝ), (0 + 2 * C * e) := by
    refine intervalIntegral.integral_mono_on hlam1 hi2
      (Continuous.intervalIntegrable continuous_const _ _) fun x hx => ?_
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨h2l.trans hx.1, hx.2⟩
    exact key x hxI 0 le_rfl (by rw [hz x hxI hx.1, abs_zero, zero_mul])
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hsum := add_le_add b1 b2
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul] at hsum
  refine hsum.trans (le_of_eq ?_)
  ring

/-- **Sections 7.1, 7.2 and 7.4 in the momentum coordinate.** The localized
correction gives the radial form of the main theorem. -/
theorem radialMain_of_correction (hP : IsProfile c G) (h : LocalizedCorrection G) :
    RadialMain G := by
  obtain ⟨δ, κ₁, κ₂, C, hδ, hδ1, hκ₁, hC, hLC⟩ := h
  obtain ⟨C₁, hC₁, hFl⟩ := Flam_bounds hP
  refine ⟨κ₁, κ₂, hκ₁, fun ε hε τ hτ => ?_⟩
  -- the cutoff radius
  have hD : 0 < 200 * C₁ ^ 2 + 4 * C₁ + 1 := by positivity
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, lam = min (1 / 16) (ε / (200 * C₁ ^ 2 + 4 * C₁ + 1)) :=
    ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam_def]
    exact lt_min (by norm_num) (div_pos hε hD)
  have hlam16 : lam ≤ 1 / 16 := by
    rw [hlam_def]
    exact min_le_left _ _
  have hlamε : lam * (200 * C₁ ^ 2 + 4 * C₁ + 1) ≤ ε := by
    have h1 : lam ≤ ε / (200 * C₁ ^ 2 + 4 * C₁ + 1) := by
      rw [hlam_def]
      exact min_le_right _ _
    rwa [le_div_iff₀ hD] at h1
  obtain ⟨e₀, he₀, hE⟩ := hLC lam hlam0 (by linarith)
  -- the size of the correction
  have hD2 : 0 < 24 * C ^ 2 + 4 * C + 1 := by positivity
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = min e₀ (min 1 (ε / (24 * C ^ 2 + 4 * C + 1))) := ⟨_, rfl⟩
  have he0 : 0 < e := by
    rw [he_def]
    exact lt_min he₀ (lt_min one_pos (div_pos hε hD2))
  have hee₀ : e ≤ e₀ := by
    rw [he_def]
    exact min_le_left _ _
  have he1 : e ≤ 1 := by
    rw [he_def]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have heε : e * (24 * C ^ 2 + 4 * C + 1) ≤ ε := by
    have h1 : e ≤ ε / (24 * C ^ 2 + 4 * C + 1) := by
      rw [he_def]
      exact (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hD2] at h1
  -- the time interval
  obtain ⟨T, H, hT, hTlt, hflow, hprop⟩ := hE e he0 hee₀ (min τ 1) (lt_min hτ one_pos)
  have hTτ : T < τ := hTlt.trans_le (min_le_left _ _)
  have hT1 : T ≤ 1 := (hTlt.trans_le (min_le_right _ _)).le
  have hρ : ∀ t ∈ Ioo (-T) 0, 0 < Real.sqrt (-t) ∧ Real.sqrt (-t) ≤ 1 := fun t ht =>
    ⟨Real.sqrt_pos.2 (by linarith [ht.2]), Real.sqrt_le_one.2 (by linarith [ht.1])⟩
  refine ⟨T, H, hT, hTτ, hflow,
    fun t ht x hx => ⟨(hprop t ht x hx).1, (hprop t ht x hx).2.1⟩, ?_, ?_, ?_⟩
  · -- the Calabi energy
    intro t ht
    obtain ⟨hρ0, hρ1⟩ := hρ t ht
    have hb := energy_le (K := Kop (H t)) (K₀ := Kop (Flam G lam t))
      (continuousOn_Kop (hflow.slice ht)) hC₁.le hC he0.le hρ0 hρ1 hδ.le hδ1 hlam0 (by linarith)
      (fun x hx => (hFl lam hlam0 t ht.2 x hx).2.1)
      (fun x hx hlt => (hFl lam hlam0 t ht.2 x hx).2.2 hlt)
      (fun x hx => (hprop t ht x hx).2.2.2)
    refine hb.trans_lt ?_
    have hl5 : lam ^ 5 ≤ lam := pow_le_of_le_one hlam0.le (by linarith) (by norm_num)
    have he2 : e ^ 2 ≤ e := pow_le_of_le_one he0.le he1 (by norm_num)
    have hc1 := mul_le_mul_of_nonneg_left hl5 (sq_nonneg C₁)
    have hc2 := mul_le_mul_of_nonneg_left he2 (sq_nonneg C)
    have hp1 : 0 < C₁ * lam := mul_pos hC₁ hlam0
    have hp2 : 0 ≤ C * e := mul_nonneg hC he0.le
    have e5 : (2 * lam) ^ 5 = 32 * lam ^ 5 := by ring
    rw [e5]
    nlinarith [mul_nonneg (sq_nonneg C₁) hlam0.le, mul_nonneg (sq_nonneg C) he0.le]
  · -- the first moment
    intro t ht
    obtain ⟨hρ0, hρ1⟩ := hρ t ht
    have hb := moment_le (F := H t) (F₀ := Flam G lam t) (hflow.slice ht).continuousOn hC₁.le hC
      he0.le hρ0 hρ1 hδ.le hδ1 hlam0 (by linarith)
      (fun x hx => (hFl lam hlam0 t ht.2 x hx).1)
      (fun x _ hle => Flam_of_ge hlam0 t hle)
      (fun x hx => (hprop t ht x hx).2.2.1)
    refine hb.trans_lt ?_
    have hp1 : 0 < C₁ * lam := mul_pos hC₁ hlam0
    have hp2 : 0 ≤ C * e := mul_nonneg hC he0.le
    nlinarith [mul_nonneg (sq_nonneg C₁) hlam0.le, mul_nonneg (sq_nonneg C) he0.le]
  · -- the blow-up at the point orbit
    have hlim : Tendsto (fun t : ℝ => C * e * Real.sqrt (-t) ^ δ) (𝓝[<] 0) (𝓝 0) := by
      have h1 : ContinuousAt (fun t : ℝ => Real.sqrt (-t)) 0 :=
        (Real.continuous_sqrt.comp continuous_neg).continuousAt
      have h2 : ContinuousAt (fun t : ℝ => Real.sqrt (-t) ^ δ) 0 :=
        h1.rpow_const (Or.inr hδ.le)
      have hc : ContinuousAt (fun t : ℝ => C * e * Real.sqrt (-t) ^ δ) 0 :=
        continuousAt_const.mul h2
      have h0 : C * e * Real.sqrt (-0) ^ δ = 0 := by
        rw [neg_zero, Real.sqrt_zero, Real.zero_rpow hδ.ne', mul_zero]
      have ht := hc.tendsto
      rw [h0] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        ‖Real.sqrt (-t) * H t 0 - deriv G 0‖ ≤ C * e * Real.sqrt (-t) ^ δ := by
      filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.2 hT)] with t ht
      obtain ⟨hρ0, -⟩ := hρ t ht
      have hb := (hprop t ht 0 ⟨le_rfl, zero_le_one⟩).2.2.1
      rw [Flam_zero, zero_add] at hb
      have e1 : Real.sqrt (-t) * H t 0 - deriv G 0
          = Real.sqrt (-t) * (H t 0 - deriv G 0 / Real.sqrt (-t)) := by
        field_simp
      have e2 : Real.sqrt (-t) * Real.sqrt (-t) ^ (-1 + δ) = Real.sqrt (-t) ^ δ := by
        rw [Real.rpow_add hρ0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
      rw [Real.norm_eq_abs, e1, abs_mul, abs_of_pos hρ0]
      calc Real.sqrt (-t) * |H t 0 - deriv G 0 / Real.sqrt (-t)|
          ≤ Real.sqrt (-t) * (C * e * Real.sqrt (-t) ^ (-1 + δ)) :=
            mul_le_mul_of_nonneg_left hb hρ0.le
        _ = C * e * Real.sqrt (-t) ^ δ := by
          rw [← e2]
          ring
    have hdiff := squeeze_zero_norm' hev hlim
    have hadd := hdiff.add_const (deriv G 0)
    simpa using hadd

/-! ### General exponents -/

/-- The main theorem in the momentum coordinate for the exponents `2 ≤ p < 7`. -/
def RadialMainP (G : ℝ → ℝ) : Prop :=
  ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (H : ℝ → ℝ → ℝ), 0 < T ∧ T < τ ∧ IsRadialFlow T H ∧
      (∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
        κ₁ ≤ 1 + vstar x * H t x ∧ 1 + vstar x * H t x ≤ κ₂) ∧
      (∀ t ∈ Ioo (-T) 0, ∫ x in (0 : ℝ)..1, |Kop (H t) x| ^ p * (7 * x ^ 6) < ε) ∧
      (∀ t ∈ Ioo (-T) 0, ∫ x in (0 : ℝ)..1, x * |H t x| < ε) ∧
      Tendsto (fun t => Real.sqrt (-t) * H t 0) (𝓝[<] 0) (𝓝 (deriv G 0))

/-- The curvature integral, Section 7.1: `∫ |K|^p 7 x⁶ dx` for `1 ≤ p < 7`. -/
theorem energy_le_rpow {K K₀ : ℝ → ℝ} {C₁ C e ρ δ lam p : ℝ} (hK : ContinuousOn K (Icc 0 1))
    (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C) (he : 0 ≤ e) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : 2 * lam ≤ 1) (hp : 1 ≤ p) (hp7 : p < 7)
    (h₀ : ∀ x ∈ Icc (0 : ℝ) 1, |K₀ x| ≤ C₁ / (x + ρ))
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 2 * lam < x → K₀ x = 0)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, |K x - K₀ x| ≤ C * e * (x + ρ) ^ (-1 + δ)) :
    ∫ x in (0 : ℝ)..1, |K x| ^ p * (7 * x ^ 6)
      ≤ 7 * (C₁ + 2 * C * e) ^ p * ((2 * lam) ^ (7 - p) / (7 - p))
        + 7 * (0 + 2 * C * e) ^ p * (1 / (7 - p)) := by
  have hp0 : 0 ≤ p := by linarith
  have h7p : 0 < 7 - p := by linarith
  have hf : ContinuousOn (fun x : ℝ => |K x| ^ p * (7 * x ^ 6)) (Icc 0 1) :=
    (hK.abs.rpow_const fun _ _ => Or.inr hp0).mul
      (continuousOn_const.mul (continuousOn_id.pow 6))
  have h2l : (0 : ℝ) ≤ 2 * lam := by linarith
  have hi1 : IntervalIntegrable (fun x : ℝ => |K x| ^ p * (7 * x ^ 6)) MeasureTheory.volume 0
      (2 * lam) := (hf.mono (Icc_subset_Icc le_rfl hlam1)).intervalIntegrable_of_Icc h2l
  have hi2 : IntervalIntegrable (fun x : ℝ => |K x| ^ p * (7 * x ^ 6)) MeasureTheory.volume
      (2 * lam) 1 := (hf.mono (Icc_subset_Icc h2l le_rfl)).intervalIntegrable_of_Icc hlam1
  have hrp : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x ^ (6 - p)) MeasureTheory.volume a b :=
    fun a b => intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have key : ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ B : ℝ, 0 ≤ B → |K₀ x| * x ≤ B →
      |K x| ^ p * (7 * x ^ 6) ≤ 7 * (B + 2 * C * e) ^ p * x ^ (6 - p) := by
    intro x h0 hx1 B hB hB0
    have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h0.le, hx1⟩
    have hw := weight_le h0 hx.2 hρ hρ1 hδ hδ1
    have hdx := hd x hx
    have hx0 := h0.ne'
    have h1 : |K x - K₀ x| * x ≤ 2 * C * e := by
      have hm : C * e * (x + ρ) ^ (-1 + δ) ≤ C * e * (2 / x) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hC he)
      calc |K x - K₀ x| * x ≤ C * e * (2 / x) * x :=
            mul_le_mul_of_nonneg_right (hdx.trans hm) h0.le
        _ = 2 * C * e := by field_simp
    have h2 : |K x| * x ≤ B + 2 * C * e := by
      have htri : |K x| ≤ |K₀ x| + |K x - K₀ x| := by
        have h := abs_add_le (K₀ x) (K x - K₀ x)
        rwa [add_sub_cancel] at h
      nlinarith [mul_le_mul_of_nonneg_right htri h0.le]
    have h3 : 0 ≤ |K x| * x := mul_nonneg (abs_nonneg _) h0.le
    have h4 : (|K x| * x) ^ p ≤ (B + 2 * C * e) ^ p := Real.rpow_le_rpow h3 h2 hp0
    rw [Real.mul_rpow (abs_nonneg _) h0.le] at h4
    have e6 : x ^ 6 = x ^ p * x ^ (6 - p) := by
      rw [← Real.rpow_add h0, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have e1 : |K x| ^ p * (7 * x ^ 6) = 7 * (|K x| ^ p * x ^ p) * x ^ (6 - p) := by
      rw [e6]
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num))
      (Real.rpow_nonneg h0.le _)
  have hB1 : ∀ x ∈ Icc (0 : ℝ) 1, |K₀ x| * x ≤ C₁ := by
    intro x hx
    have hpos : 0 < x + ρ := by linarith [hx.1]
    calc |K₀ x| * x ≤ C₁ / (x + ρ) * x := mul_le_mul_of_nonneg_right (h₀ x hx) hx.1
      _ ≤ C₁ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        nlinarith [mul_nonneg hC₁ hρ.le]
  have b1 : ∫ x in (0 : ℝ)..(2 * lam), |K x| ^ p * (7 * x ^ 6)
      ≤ ∫ x in (0 : ℝ)..(2 * lam), 7 * (C₁ + 2 * C * e) ^ p * x ^ (6 - p) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo h2l hi1 ((hrp _ _).const_mul _)
      fun x hx => ?_
    exact key x hx.1 (hx.2.le.trans hlam1) C₁ hC₁
      (hB1 x ⟨hx.1.le, hx.2.le.trans hlam1⟩)
  have b2 : ∫ x in (2 * lam)..(1 : ℝ), |K x| ^ p * (7 * x ^ 6)
      ≤ ∫ x in (2 * lam)..(1 : ℝ), 7 * (0 + 2 * C * e) ^ p * x ^ (6 - p) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hlam1 hi2 ((hrp _ _).const_mul _)
      fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx.2.le⟩
    exact key x hx0 hx.2.le 0 le_rfl (by rw [hz x hxI hx.1, abs_zero, zero_mul])
  have e76 : (6 - p + 1 : ℝ) = 7 - p := by ring
  have e1 : ∫ x in (0 : ℝ)..(2 * lam), 7 * (C₁ + 2 * C * e) ^ p * x ^ (6 - p)
      = 7 * (C₁ + 2 * C * e) ^ p * ((2 * lam) ^ (7 - p) / (7 - p)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), e76,
      Real.zero_rpow h7p.ne', sub_zero]
  have e2 : ∫ x in (2 * lam)..(1 : ℝ), 7 * (0 + 2 * C * e) ^ p * x ^ (6 - p)
      = 7 * (0 + 2 * C * e) ^ p * ((1 - (2 * lam) ^ (7 - p)) / (7 - p)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), e76,
      Real.one_rpow]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hsum := add_le_add b1 b2
  rw [e1, e2] at hsum
  refine hsum.trans ?_
  have hL : (0 : ℝ) ≤ (2 * lam) ^ (7 - p) := Real.rpow_nonneg h2l _
  have hCe : (0 : ℝ) ≤ (0 + 2 * C * e) ^ p := Real.rpow_nonneg (by positivity) _
  have hfrac : (1 - (2 * lam) ^ (7 - p)) / (7 - p) ≤ 1 / (7 - p) :=
    div_le_div_of_nonneg_right (by linarith) h7p.le
  have hmul := mul_le_mul_of_nonneg_left hfrac (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hCe)
  linarith

/-- **Sections 7.1, 7.2 and 7.4 in the momentum coordinate, for `2 ≤ p < 7`.** -/
theorem radialMainP_of_correction (hP : IsProfile c G) (h : LocalizedCorrection G) :
    RadialMainP G := by
  obtain ⟨δ, κ₁, κ₂, C, hδ, hδ1, hκ₁, hC, hLC⟩ := h
  obtain ⟨C₁, hC₁, hFl⟩ := Flam_bounds hP
  refine ⟨κ₁, κ₂, hκ₁, fun p hp2 hp7 ε hε τ hτ => ?_⟩
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have h7p : 0 < 7 - p := by linarith
  -- the constants of the two contributions
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = 7 * (C₁ + 2 * C) ^ p / (7 - p) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : ℝ, A₂ = 7 * (2 * C) ^ p / (7 - p) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) h7p.le
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) h7p.le
  -- the cutoff radius
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (4 * (A₁ + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos hε (by positivity)
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ,
      lam = min (1 / 16) (min (η ^ (1 / (7 - p)) / 2) (ε / (8 * (C₁ + 1)))) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam_def]
    exact lt_min (by norm_num) (lt_min (by positivity) (div_pos hε (by positivity)))
  have hlam16 : lam ≤ 1 / 16 := by
    rw [hlam_def]
    exact min_le_left _ _
  have hlamη : 2 * lam ≤ η ^ (1 / (7 - p)) := by
    have h1 : lam ≤ η ^ (1 / (7 - p)) / 2 := by
      rw [hlam_def]
      exact (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hlamε : lam * (8 * (C₁ + 1)) ≤ ε := by
    have h1 : lam ≤ ε / (8 * (C₁ + 1)) := by
      rw [hlam_def]
      exact (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have hpow : (2 * lam) ^ (7 - p) ≤ η := by
    have h1 : (2 * lam) ^ (7 - p) ≤ (η ^ (1 / (7 - p))) ^ (7 - p) :=
      Real.rpow_le_rpow (by positivity) hlamη h7p.le
    rwa [← Real.rpow_mul hη0.le, one_div, inv_mul_cancel₀ h7p.ne', Real.rpow_one] at h1
  obtain ⟨e₀, he₀, hE⟩ := hLC lam hlam0 (by linarith)
  -- the size of the correction
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = min e₀ (min 1 (ε / (4 * (A₂ + 2 * C + 1)))) := ⟨_, rfl⟩
  have hD2 : 0 < 4 * (A₂ + 2 * C + 1) := by positivity
  have he0 : 0 < e := by
    rw [he_def]
    exact lt_min he₀ (lt_min one_pos (div_pos hε hD2))
  have hee₀ : e ≤ e₀ := by
    rw [he_def]
    exact min_le_left _ _
  have he1 : e ≤ 1 := by
    rw [he_def]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have heε : e * (4 * (A₂ + 2 * C + 1)) ≤ ε := by
    have h1 : e ≤ ε / (4 * (A₂ + 2 * C + 1)) := by
      rw [he_def]
      exact (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hD2] at h1
  -- the time interval
  obtain ⟨T, H, hT, hTlt, hflow, hprop⟩ := hE e he0 hee₀ (min τ 1) (lt_min hτ one_pos)
  have hTτ : T < τ := hTlt.trans_le (min_le_left _ _)
  have hT1 : T ≤ 1 := (hTlt.trans_le (min_le_right _ _)).le
  have hρ : ∀ t ∈ Ioo (-T) 0, 0 < Real.sqrt (-t) ∧ Real.sqrt (-t) ≤ 1 := fun t ht =>
    ⟨Real.sqrt_pos.2 (by linarith [ht.2]), Real.sqrt_le_one.2 (by linarith [ht.1])⟩
  refine ⟨T, H, hT, hTτ, hflow,
    fun t ht x hx => ⟨(hprop t ht x hx).1, (hprop t ht x hx).2.1⟩, ?_, ?_, ?_⟩
  · -- the curvature integral
    intro t ht
    obtain ⟨hρ0, hρ1⟩ := hρ t ht
    have hb := energy_le_rpow (K := Kop (H t)) (K₀ := Kop (Flam G lam t)) (p := p)
      (continuousOn_Kop (hflow.slice ht)) hC₁.le hC he0.le hρ0 hρ1 hδ.le hδ1 hlam0
      (by linarith) hp1 hp7
      (fun x hx => (hFl lam hlam0 t ht.2 x hx).2.1)
      (fun x hx hlt => (hFl lam hlam0 t ht.2 x hx).2.2 hlt)
      (fun x hx => (hprop t ht x hx).2.2.2)
    refine hb.trans_lt ?_
    have hCe : 0 ≤ C * e := mul_nonneg hC he0.le
    -- first term
    have h1 : (C₁ + 2 * C * e) ^ p ≤ (C₁ + 2 * C) ^ p :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hp0
    have t1 : 7 * (C₁ + 2 * C * e) ^ p * ((2 * lam) ^ (7 - p) / (7 - p)) ≤ A₁ * η := by
      have h2 : 7 * (C₁ + 2 * C * e) ^ p * ((2 * lam) ^ (7 - p) / (7 - p))
          = 7 * (C₁ + 2 * C * e) ^ p / (7 - p) * (2 * lam) ^ (7 - p) := by
        field_simp
      rw [h2, hA₁]
      have h3 : 7 * (C₁ + 2 * C * e) ^ p / (7 - p) ≤ 7 * (C₁ + 2 * C) ^ p / (7 - p) :=
        div_le_div_of_nonneg_right (by linarith) h7p.le
      exact mul_le_mul h3 hpow (Real.rpow_nonneg (by positivity) _)
        (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) h7p.le)
    -- second term
    have h4 : (0 + 2 * C * e) ^ p ≤ (2 * C) ^ p * e := by
      have h5 : (0 + 2 * C * e) ^ p = (2 * C) ^ p * e ^ p := by
        rw [zero_add, Real.mul_rpow (by positivity) he0.le]
      have h6 : e ^ p ≤ e := by
        have h7 := Real.rpow_le_rpow_of_exponent_ge he0 he1 hp1
        rwa [Real.rpow_one] at h7
      rw [h5]
      exact mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg (by positivity) _)
    have t2 : 7 * (0 + 2 * C * e) ^ p * (1 / (7 - p)) ≤ A₂ * e := by
      have h8 : 7 * (0 + 2 * C * e) ^ p * (1 / (7 - p)) ≤ 7 * ((2 * C) ^ p * e) * (1 / (7 - p)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h9 : 7 * ((2 * C) ^ p * e) * (1 / (7 - p)) = A₂ * e := by
        rw [hA₂]
        field_simp
      linarith
    have t3 : A₁ * η ≤ ε / 4 := by
      rw [hη]
      have h10 : A₁ * (ε / (4 * (A₁ + 1))) = ε / 4 * (A₁ / (A₁ + 1)) := by
        field_simp
      rw [h10]
      have h11 : A₁ / (A₁ + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      nlinarith
    have t4 : A₂ * e ≤ ε / 4 := by nlinarith [mul_nonneg hA₂0 he0.le, mul_nonneg hC he0.le]
    linarith
  · -- the first moment
    intro t ht
    obtain ⟨hρ0, hρ1⟩ := hρ t ht
    have hb := moment_le (F := H t) (F₀ := Flam G lam t) (hflow.slice ht).continuousOn hC₁.le hC
      he0.le hρ0 hρ1 hδ.le hδ1 hlam0 (by linarith)
      (fun x hx => (hFl lam hlam0 t ht.2 x hx).1)
      (fun x _ hle => Flam_of_ge hlam0 t hle)
      (fun x hx => (hprop t ht x hx).2.2.1)
    refine hb.trans_lt ?_
    have hp1' : 0 < C₁ * lam := mul_pos hC₁ hlam0
    have hp2' : 0 ≤ C * e := mul_nonneg hC he0.le
    nlinarith [mul_nonneg hA₂0 he0.le]
  · -- the blow-up at the point orbit
    have hlim : Tendsto (fun t : ℝ => C * e * Real.sqrt (-t) ^ δ) (𝓝[<] 0) (𝓝 0) := by
      have h1 : ContinuousAt (fun t : ℝ => Real.sqrt (-t)) 0 :=
        (Real.continuous_sqrt.comp continuous_neg).continuousAt
      have h2 : ContinuousAt (fun t : ℝ => Real.sqrt (-t) ^ δ) 0 :=
        h1.rpow_const (Or.inr hδ.le)
      have hc : ContinuousAt (fun t : ℝ => C * e * Real.sqrt (-t) ^ δ) 0 :=
        continuousAt_const.mul h2
      have h0 : C * e * Real.sqrt (-0) ^ δ = 0 := by
        rw [neg_zero, Real.sqrt_zero, Real.zero_rpow hδ.ne', mul_zero]
      have ht := hc.tendsto
      rw [h0] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        ‖Real.sqrt (-t) * H t 0 - deriv G 0‖ ≤ C * e * Real.sqrt (-t) ^ δ := by
      filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.2 hT)] with t ht
      obtain ⟨hρ0, -⟩ := hρ t ht
      have hb := (hprop t ht 0 ⟨le_rfl, zero_le_one⟩).2.2.1
      rw [Flam_zero, zero_add] at hb
      have e1 : Real.sqrt (-t) * H t 0 - deriv G 0
          = Real.sqrt (-t) * (H t 0 - deriv G 0 / Real.sqrt (-t)) := by
        field_simp
      have e2 : Real.sqrt (-t) * Real.sqrt (-t) ^ (-1 + δ) = Real.sqrt (-t) ^ δ := by
        rw [Real.rpow_add hρ0, Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
      rw [Real.norm_eq_abs, e1, abs_mul, abs_of_pos hρ0]
      calc Real.sqrt (-t) * |H t 0 - deriv G 0 / Real.sqrt (-t)|
          ≤ Real.sqrt (-t) * (C * e * Real.sqrt (-t) ^ (-1 + δ)) :=
            mul_le_mul_of_nonneg_left hb hρ0.le
        _ = C * e * Real.sqrt (-t) ^ δ := by
          rw [← e2]
          ring
    have hdiff := squeeze_zero_norm' hev hlim
    have hadd := hdiff.add_const (deriv G 0)
    simpa using hadd

end Calabi.Radial
