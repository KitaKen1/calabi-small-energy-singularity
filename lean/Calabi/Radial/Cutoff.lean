import Calabi.Radial.Basic
import Calabi.Flat.ProfileDecay
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The localized profile

`chi` is a cutoff, equal to one on `(-∞, 1]` and to zero on `[2, ∞)`, and
`Flam G lam t x = chi (x / lam) * F(t, x)` is the localized self-similar
solution `F_λ = χ_λ F` of Section 6 of the manuscript.

`Flam_bounds` is the first half of (7.2): for `t < 0` and `0 ≤ x ≤ 1`,

  `|F_λ| ≤ C / (x + ρ)`,   `|K(F_λ)| ≤ C / (x + ρ)`,   `K(F_λ) = 0` for `x > 2λ`,

with `ρ = √(-t)` and a constant that does not depend on `λ` or `t`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Radial

open Calabi.Flat (hfun Fss Fss_zero hfun_decay iteratedDeriv_Fss contDiffOn_hfun)

/-! ### The cutoff -/

/-- A smooth cutoff: one on `(-∞, 1]`, zero on `[2, ∞)`. -/
noncomputable def chi (x : ℝ) : ℝ := Real.smoothTransition (2 - x)

theorem chi_of_le {x : ℝ} (hx : x ≤ 1) : chi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem chi_of_ge {x : ℝ} (hx : 2 ≤ x) : chi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem chi_nonneg (x : ℝ) : 0 ≤ chi x := Real.smoothTransition.nonneg _

theorem chi_le_one (x : ℝ) : chi x ≤ 1 := Real.smoothTransition.le_one _

theorem abs_chi_le (x : ℝ) : |chi x| ≤ 1 := by
  rw [abs_of_nonneg (chi_nonneg x)]
  exact chi_le_one x

theorem contDiff_chi : ContDiff ℝ ∞ chi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem deriv_chi_eq_zero {x : ℝ} (hx : x < 1 ∨ 2 < x) : deriv chi x = 0 := by
  rcases hx with h | h
  · have he : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using chi_of_le (le_of_lt hy)
    rw [he.deriv_eq]
    exact (hasDerivAt_const x (1 : ℝ)).deriv
  · have he : chi =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy using chi_of_ge (le_of_lt hy)
    rw [he.deriv_eq]
    exact (hasDerivAt_const x (0 : ℝ)).deriv

theorem deriv2_chi_eq_zero {x : ℝ} (hx : x < 1 ∨ 2 < x) : deriv (deriv chi) x = 0 := by
  have he : deriv chi =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    rcases hx with h | h
    · filter_upwards [Iio_mem_nhds h] with y hy using deriv_chi_eq_zero (Or.inl hy)
    · filter_upwards [Ioi_mem_nhds h] with y hy using deriv_chi_eq_zero (Or.inr hy)
  rw [he.deriv_eq]
  exact (hasDerivAt_const x (0 : ℝ)).deriv

/-- `x χ′(x)` and `x² χ″(x)` are bounded. -/
theorem chi_deriv_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
    |x * deriv chi x| ≤ C ∧ |x ^ 2 * deriv (deriv chi) x| ≤ C := by
  have h1 : ContDiff ℝ ∞ (deriv chi) := (contDiff_infty_iff_deriv.1 contDiff_chi).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv chi)) := (contDiff_infty_iff_deriv.1 h1).2
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    h1.continuous.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    h2.continuous.continuousOn
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 1 ⟨le_rfl, by norm_num⟩)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 1 ⟨le_rfl, by norm_num⟩)
  refine ⟨2 * B1 + 4 * B2, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · have b1 := hB1 x hx
    have b2 := hB2 x hx
    rw [Real.norm_eq_abs] at b1 b2
    have hx0 : 0 ≤ x := by linarith [hx.1]
    constructor
    · rw [abs_mul, abs_of_nonneg hx0]
      nlinarith [mul_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 2 - x) (abs_nonneg (deriv chi x))]
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
      have hx2 : x ^ 2 ≤ 4 := by nlinarith [hx.1, hx.2]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - x ^ 2)
        (abs_nonneg (deriv (deriv chi) x))]
  · have hx' : x < 1 ∨ 2 < x := by
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      exact hx ⟨hcon.1, hcon.2⟩
    rw [deriv_chi_eq_zero hx', deriv2_chi_eq_zero hx']
    simp only [mul_zero, abs_zero]
    exact ⟨by positivity, by positivity⟩

theorem hasDerivAt_chi_scaled (lam x : ℝ) :
    HasDerivAt (fun x : ℝ => chi (x / lam)) (deriv chi (x / lam) / lam) x := by
  have h1 : HasDerivAt chi (deriv chi (x / lam)) (x / lam) :=
    (contDiff_chi.differentiable (by simp)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x / lam) (1 / lam) x := (hasDerivAt_id' x).div_const lam
  have h := h1.comp x h2
  exact h.congr_deriv (by ring)

theorem hasDerivAt_dchi_scaled (lam x : ℝ) :
    HasDerivAt (fun x : ℝ => deriv chi (x / lam) / lam)
      (deriv (deriv chi) (x / lam) / lam ^ 2) x := by
  have hc1 : ContDiff ℝ ∞ (deriv chi) := (contDiff_infty_iff_deriv.1 contDiff_chi).2
  have h1 : HasDerivAt (deriv chi) (deriv (deriv chi) (x / lam)) (x / lam) :=
    (hc1.differentiable (by simp)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x / lam) (1 / lam) x := (hasDerivAt_id' x).div_const lam
  have h := (h1.comp x h2).div_const lam
  exact h.congr_deriv (by ring)

/-! ### The self-similar solution in the variable `x` -/

variable {c : ℝ} {G : ℝ → ℝ}

theorem contDiffOn_Fss {δ : ℝ} (hh : ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ))) {t : ℝ} (ht : t < 0) :
    ContDiffOn ℝ ∞ (Fss G t) (Ioi (-δ * Real.sqrt (-t))) := by
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ => x / Real.sqrt (-t)) (Ioi (-δ * Real.sqrt (-t))) :=
    contDiffOn_id.div_const _
  have hmaps : MapsTo (fun x : ℝ => x / Real.sqrt (-t)) (Ioi (-δ * Real.sqrt (-t)))
      (Ioi (-δ)) := fun x hx => by
    rw [mem_Ioi, lt_div_iff₀ hρ]
    exact hx
  exact (hh.comp h1 hmaps).div_const _

/-- `F`, `x F_x` and `x² F_xx` are at most `C / (x + ρ)`. -/
theorem Fss_bounds (hP : IsProfile c G) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t < 0 → ∀ x : ℝ, 0 ≤ x →
    |Fss G t x| ≤ C / (x + Real.sqrt (-t)) ∧
      |x * deriv (Fss G t) x| ≤ C / (x + Real.sqrt (-t)) ∧
      |x ^ 2 * deriv (deriv (Fss G t)) x| ≤ C / (x + Real.sqrt (-t)) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  obtain ⟨C, hC, hdec⟩ := hfun_decay hP
  refine ⟨C, hC, fun t ht x hx => ?_⟩
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hρ0 := hρ.ne'
  have hx' : -δ * Real.sqrt (-t) < x := by
    have := mul_pos hδ hρ
    linarith
  have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx hρ.le
  obtain ⟨d0, d1, d2⟩ := hdec _ hy
  have i1 : deriv (Fss G t) x
      = deriv (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 2 := by
    have h := iteratedDeriv_Fss hh ht 1 hx'
    rw [iteratedDeriv_one, iteratedDeriv_one] at h
    exact h
  have i2 : deriv (deriv (Fss G t)) x
      = iteratedDeriv 2 (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 3 := by
    have h := iteratedDeriv_Fss hh ht 2 hx'
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h
    exact h
  have hmul : (1 + x / Real.sqrt (-t)) * Real.sqrt (-t) = x + Real.sqrt (-t) := by
    rw [add_mul, one_mul, div_mul_cancel₀ x hρ0]
    ring
  have hQ : C / (1 + x / Real.sqrt (-t)) / Real.sqrt (-t) = C / (x + Real.sqrt (-t)) := by
    rw [div_div, hmul]
  refine ⟨?_, ?_, ?_⟩
  · have e : Fss G t x = hfun G (x / Real.sqrt (-t)) / Real.sqrt (-t) := rfl
    rw [e, abs_div, abs_of_pos hρ, ← hQ]
    exact div_le_div_of_nonneg_right d0 hρ.le
  · have e : x * deriv (Fss G t) x
        = x / Real.sqrt (-t) * deriv (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) := by
      rw [i1]
      ring
    rw [e, abs_div, abs_of_pos hρ, ← hQ]
    exact div_le_div_of_nonneg_right d1 hρ.le
  · have e : x ^ 2 * deriv (deriv (Fss G t)) x
        = (x / Real.sqrt (-t)) ^ 2 * iteratedDeriv 2 (hfun G) (x / Real.sqrt (-t))
          / Real.sqrt (-t) := by
      rw [i2]
      ring
    rw [e, abs_div, abs_of_pos hρ, ← hQ]
    exact div_le_div_of_nonneg_right d2 hρ.le

/-! ### The localized profile -/

/-- The localized self-similar solution `F_λ = χ(x/λ) F`. -/
noncomputable def Flam (G : ℝ → ℝ) (lam t x : ℝ) : ℝ := chi (x / lam) * Fss G t x

theorem Flam_of_ge {lam : ℝ} (hlam : 0 < lam) (t : ℝ) {x : ℝ} (hx : 2 * lam ≤ x) :
    Flam G lam t x = 0 := by
  unfold Flam
  rw [chi_of_ge ((le_div_iff₀ hlam).2 hx), zero_mul]

/-- At the concentrating point the cutoff is one. -/
theorem Flam_zero (lam t : ℝ) : Flam G lam t 0 = deriv G 0 / Real.sqrt (-t) := by
  unfold Flam
  rw [zero_div, chi_of_le zero_le_one, one_mul, Fss_zero]

theorem contDiffOn_Flam {δ : ℝ} (hh : ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ))) {lam t : ℝ}
    (ht : t < 0) : ContDiffOn ℝ ∞ (Flam G lam t) (Ioi (-δ * Real.sqrt (-t))) :=
  (contDiff_chi.comp (contDiff_id.div_const lam)).contDiffOn.mul (contDiffOn_Fss hh ht)

section Derivs

variable {δ : ℝ} (hh : ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ))) {lam t : ℝ} (ht : t < 0)

include hh ht

theorem hasDerivAt_Flam {x : ℝ} (hx : x ∈ Ioi (-δ * Real.sqrt (-t))) :
    HasDerivAt (Flam G lam t)
      (deriv chi (x / lam) / lam * Fss G t x + chi (x / lam) * deriv (Fss G t) x) x := by
  obtain ⟨hd, -⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 (contDiffOn_Fss hh ht)
  have dF : HasDerivAt (Fss G t) (deriv (Fss G t) x) x :=
    ((hd x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  exact (hasDerivAt_chi_scaled lam x).fun_mul dF

theorem deriv_Flam {x : ℝ} (hx : x ∈ Ioi (-δ * Real.sqrt (-t))) :
    deriv (Flam G lam t) x
      = deriv chi (x / lam) / lam * Fss G t x + chi (x / lam) * deriv (Fss G t) x :=
  (hasDerivAt_Flam hh ht hx).deriv

theorem deriv2_Flam {x : ℝ} (hx : x ∈ Ioi (-δ * Real.sqrt (-t))) :
    deriv (deriv (Flam G lam t)) x
      = deriv (deriv chi) (x / lam) / lam ^ 2 * Fss G t x
        + 2 * (deriv chi (x / lam) / lam) * deriv (Fss G t) x
        + chi (x / lam) * deriv (deriv (Fss G t)) x := by
  obtain ⟨hd, hd'⟩ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 (contDiffOn_Fss hh ht)
  have hd2 := ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hd').1
  have dF : HasDerivAt (Fss G t) (deriv (Fss G t) x) x :=
    ((hd x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have dF1 : HasDerivAt (deriv (Fss G t)) (deriv (deriv (Fss G t)) x) x :=
    ((hd2 x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have d2 := ((hasDerivAt_dchi_scaled lam x).fun_mul dF).fun_add
    ((hasDerivAt_chi_scaled lam x).fun_mul dF1)
  have heq : deriv (Flam G lam t) =ᶠ[𝓝 x] fun y =>
      deriv chi (y / lam) / lam * Fss G t y + chi (y / lam) * deriv (Fss G t) y := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using deriv_Flam hh ht hy
  rw [heq.deriv_eq, d2.deriv]
  ring

end Derivs

theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

/-- The bound of `K(ψ F)` from the bounds of `F` and of the cutoff `ψ`. -/
theorem kop_bound_algebra {x Q Cx F F1 F2 ψ ψ1 ψ2 : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hF : |F| ≤ Q) (hF1 : |x * F1| ≤ Q) (hF2 : |x ^ 2 * F2| ≤ Q) (hψ : |ψ| ≤ 1)
    (hψ1 : |x * ψ1| ≤ Cx) (hψ2 : |x ^ 2 * ψ2| ≤ Cx) :
    |x ^ 2 * (1 - x) ^ 2 * (ψ2 * F + 2 * ψ1 * F1 + ψ * F2)
      + 4 * x * (1 - x) * (4 - 5 * x) * (ψ1 * F + ψ * F1)
      + (56 - 144 * x + 90 * x ^ 2) * (ψ * F)| ≤ (19 * Cx + 73) * Q := by
  obtain ⟨hx0, hx1⟩ := hx
  have k1 : |(1 - x) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 2 - x)]
  have k1' : |2 * (1 - x) ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 2 - x)]
  have k2 : |4 * (1 - x) * (4 - 5 * x)| ≤ 16 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x - 9 / 10)]
    · nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 36 - 20 * x)]
  have k3 : |56 - 144 * x + 90 * x ^ 2| ≤ 56 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x - 4 / 5)]
    · nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 144 - 90 * x)]
  have u1 := abs_mul_le_of k1 (abs_mul_le_of hψ2 hF)
  have u2 := abs_mul_le_of k1' (abs_mul_le_of hψ1 hF1)
  have u3 := abs_mul_le_of k1 (abs_mul_le_of hψ hF2)
  have u4 := abs_mul_le_of k2 (abs_mul_le_of hψ1 hF)
  have u5 := abs_mul_le_of k2 (abs_mul_le_of hψ hF1)
  have u6 := abs_mul_le_of k3 (abs_mul_le_of hψ hF)
  have e : x ^ 2 * (1 - x) ^ 2 * (ψ2 * F + 2 * ψ1 * F1 + ψ * F2)
      + 4 * x * (1 - x) * (4 - 5 * x) * (ψ1 * F + ψ * F1)
      + (56 - 144 * x + 90 * x ^ 2) * (ψ * F)
      = (1 - x) ^ 2 * (x ^ 2 * ψ2 * F) + 2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1))
        + (1 - x) ^ 2 * (ψ * (x ^ 2 * F2)) + 4 * (1 - x) * (4 - 5 * x) * (x * ψ1 * F)
        + 4 * (1 - x) * (4 - 5 * x) * (ψ * (x * F1))
        + (56 - 144 * x + 90 * x ^ 2) * (ψ * F) := by ring
  rw [e]
  have a5 := abs_add_le ((1 - x) ^ 2 * (x ^ 2 * ψ2 * F) + 2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1))
    + (1 - x) ^ 2 * (ψ * (x ^ 2 * F2)) + 4 * (1 - x) * (4 - 5 * x) * (x * ψ1 * F)
    + 4 * (1 - x) * (4 - 5 * x) * (ψ * (x * F1))) ((56 - 144 * x + 90 * x ^ 2) * (ψ * F))
  have a4 := abs_add_le ((1 - x) ^ 2 * (x ^ 2 * ψ2 * F) + 2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1))
    + (1 - x) ^ 2 * (ψ * (x ^ 2 * F2)) + 4 * (1 - x) * (4 - 5 * x) * (x * ψ1 * F))
    (4 * (1 - x) * (4 - 5 * x) * (ψ * (x * F1)))
  have a3 := abs_add_le ((1 - x) ^ 2 * (x ^ 2 * ψ2 * F) + 2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1))
    + (1 - x) ^ 2 * (ψ * (x ^ 2 * F2))) (4 * (1 - x) * (4 - 5 * x) * (x * ψ1 * F))
  have a2 := abs_add_le ((1 - x) ^ 2 * (x ^ 2 * ψ2 * F) + 2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1)))
    ((1 - x) ^ 2 * (ψ * (x ^ 2 * F2)))
  have a1 := abs_add_le ((1 - x) ^ 2 * (x ^ 2 * ψ2 * F)) (2 * (1 - x) ^ 2 * (x * ψ1 * (x * F1)))
  linarith

/-- **The localized profile and its curvature term**, the first half of (7.2). -/
theorem Flam_bounds (hP : IsProfile c G) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ lam : ℝ, 0 < lam →
    ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1,
      |Flam G lam t x| ≤ C₁ / (x + Real.sqrt (-t)) ∧
        |Kop (Flam G lam t) x| ≤ C₁ / (x + Real.sqrt (-t)) ∧
        (2 * lam < x → Kop (Flam G lam t) x = 0) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  obtain ⟨CF, hCF, hF⟩ := Fss_bounds hP
  obtain ⟨Cx, hCx, hχ⟩ := chi_deriv_bounds
  refine ⟨(19 * Cx + 73) * CF, by positivity, fun lam hlam t ht x hx => ?_⟩
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hden : 0 < x + Real.sqrt (-t) := by linarith [hx.1]
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioi (-δ * Real.sqrt (-t)) := fun y hy => by
    have := mul_pos hδ hρ
    exact mem_Ioi.2 (by linarith [hy.1])
  have hsmF := contDiffOn_Flam (lam := lam) hh ht
  obtain ⟨e1, e2⟩ := D_D_eq isOpen_Ioi hsub hsmF hx
  obtain ⟨f0, f1, f2⟩ := hF t ht x hx.1
  obtain ⟨c1, c2⟩ := hχ (x / lam)
  have hψ1 : |x * (deriv chi (x / lam) / lam)| ≤ Cx := by
    have e : x * (deriv chi (x / lam) / lam) = x / lam * deriv chi (x / lam) := by ring
    rw [e]
    exact c1
  have hψ2 : |x ^ 2 * (deriv (deriv chi) (x / lam) / lam ^ 2)| ≤ Cx := by
    have e : x ^ 2 * (deriv (deriv chi) (x / lam) / lam ^ 2)
        = (x / lam) ^ 2 * deriv (deriv chi) (x / lam) := by ring
    rw [e]
    exact c2
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_mul_le_of (abs_chi_le (x / lam)) f0
    rw [one_mul] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ hden.le)
    nlinarith [mul_nonneg hCx hCF.le]
  · have key := kop_bound_algebra hx f0 f1 f2 (abs_chi_le (x / lam)) hψ1 hψ2
    unfold Kop
    rw [e1, e2, deriv_Flam hh ht (hsub hx), deriv2_Flam hh ht (hsub hx)]
    exact key.trans (le_of_eq (by ring))
  · intro hlt
    have hz : ∀ y : ℝ, 2 * lam < y → deriv (Flam G lam t) y = 0 := by
      intro y hy
      have he : Flam G lam t =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hy] with u hu using Flam_of_ge hlam t (le_of_lt hu)
      rw [he.deriv_eq]
      exact (hasDerivAt_const y (0 : ℝ)).deriv
    have he1 : deriv (Flam G lam t) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hlt] with u hu using hz u hu
    have z2 : deriv (deriv (Flam G lam t)) x = 0 := by
      rw [he1.deriv_eq]
      exact (hasDerivAt_const x (0 : ℝ)).deriv
    unfold Kop
    rw [e1, e2, hz x hlt, z2, Flam_of_ge hlam t hlt.le]
    ring

end Calabi.Radial
