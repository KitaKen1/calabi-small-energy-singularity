import Calabi.Geometry.Potential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The uniform bound of the initial potential

Section 7.2 of the manuscript. At the time `t₀` the affine part of the
symplectic potential is normalized by `ψ(1) = ψ′(1) = 0`, so that

  `|ψ| ≤ 2 ∫₀¹ s |H / (1 + v∗ H)| ds`              (`abs_psi_le`).

The Legendre transform does not increase the uniform norm: with `u = u∗ + ψ`
convex and `ξ` the Fubini–Study momentum of the point of momentum `x`,

  `-ψ(ξ) ≤ Φ - Φ∗ ≤ -ψ(x)`                          (`Pfun_ge`, `Pfun_le`),

the two inequalities being the convexity of `u` and of `u∗`. Hence the
potential of the metric of `H(t₀)` relative to the Fubini–Study metric is
bounded by `2 ∫₀¹ s |H / (1 + v∗ H)| ds` on `CP⁷` (`abs_Fhat_le`).
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Calabi.Legendre

open Calabi.Geometry Calabi.Strip Calabi.Radial

theorem alpha_self (H : ℝ → ℝ → ℝ) (t₀ : ℝ) : alpha H t₀ t₀ = 0 := by
  simp [alpha]

theorem beta_self (H : ℝ → ℝ → ℝ) (t₀ : ℝ) : beta H t₀ t₀ = 0 := by
  simp [beta]

/-- Two elementary bounds of integrals over `[x, 1]` by `∫₀¹ s |f|`. -/
theorem integral_bounds {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |∫ s in (1 : ℝ)..x, s * f s| ≤ ∫ s in (0 : ℝ)..1, s * |f s| ∧
      |x * ∫ s in (1 : ℝ)..x, f s| ≤ ∫ s in (0 : ℝ)..1, s * |f s| := by
  have hsub : Icc x 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left hx.1
  have hu01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hux1 : uIcc x 1 = Icc x 1 := uIcc_of_le hx.2
  have hg : ContinuousOn (fun s : ℝ => s * |f s|) (Icc 0 1) := continuousOn_id.mul hf.abs
  have hgi : IntervalIntegrable (fun s : ℝ => s * |f s|) volume 0 1 :=
    (hg.mono hu01.le).intervalIntegrable
  have hgx : IntervalIntegrable (fun s : ℝ => s * |f s|) volume x 1 :=
    (hg.mono (hux1.le.trans hsub)).intervalIntegrable
  have hfx : IntervalIntegrable (fun s : ℝ => |f s|) volume x 1 :=
    (hf.abs.mono (hux1.le.trans hsub)).intervalIntegrable
  have hmono : ∫ s in x..1, s * |f s| ≤ ∫ s in (0 : ℝ)..1, s * |f s| :=
    intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => mul_nonneg hs.1.le (abs_nonneg _))
      hgi
  constructor
  · rw [intervalIntegral.integral_symm, abs_neg]
    refine (intervalIntegral.abs_integral_le_integral_abs hx.2).trans ?_
    have e : ∫ s in x..1, |s * f s| = ∫ s in x..1, s * |f s| := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hux1] at hs
      show |s * f s| = s * |f s|
      rw [abs_mul, abs_of_nonneg (hx.1.trans hs.1)]
    rw [e]
    exact hmono
  · rw [intervalIntegral.integral_symm, mul_neg, abs_neg, abs_mul, abs_of_nonneg hx.1]
    have h1 : x * |∫ s in x..1, f s| ≤ x * ∫ s in x..1, |f s| :=
      mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs hx.2) hx.1
    have h2 : x * ∫ s in x..1, |f s| = ∫ s in x..1, x * |f s| := by
      rw [intervalIntegral.integral_const_mul]
    have h3 : ∫ s in x..1, x * |f s| ≤ ∫ s in x..1, s * |f s| :=
      intervalIntegral.integral_mono_on hx.2 (hfx.const_mul x) hgx
        fun s hs => mul_le_mul_of_nonneg_right hs.1 (abs_nonneg _)
    linarith

namespace Flow

variable {J : Set ℝ} {H : ℝ → ℝ → ℝ} {t₀ t x : ℝ}

/-- `Φ - Φ∗ ≤ -ψ(x)`: the convexity of the exponential. -/
theorem Pfun_le (hx : x ∈ Icc (0 : ℝ) 1) : Pfun H t₀ t x ≤ -psi H t₀ t x := by
  have hD := Dhat_pos (H := H) (t₀ := t₀) (t := t) hx
  have hconv := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (afun H t₀ t x))
    (sub_nonneg.2 hx.2) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have h1 : Real.exp (x * afun H t₀ t x) ≤ Dhat H t₀ t x := hconv
  have h2 : x * afun H t₀ t x ≤ Real.log (Dhat H t₀ t x) := by
    have h := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h
  unfold Pfun
  linarith

/-- `-ψ(ξ) ≤ Φ - Φ∗`: the convexity of the symplectic potential `u = u∗ + ψ`. -/
theorem Pfun_ge (hF : Flow J H) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    -psi H t₀ t (Xi H t₀ t x) ≤ Pfun H t₀ t x := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, Xi_zero]
    unfold Pfun Dhat
    simp
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · rw [h1, Xi_one]
    unfold Pfun Dhat
    simp
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hE := Real.exp_pos (afun H t₀ t x)
  have hD : 0 < Dhat H t₀ t x := Dhat_pos hx
  have hDdef : Dhat H t₀ t x = 1 - x + x * Real.exp (afun H t₀ t x) := rfl
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = Xi H t₀ t x := ⟨_, rfl⟩
  have hξ' : ξ = x * Real.exp (afun H t₀ t x) / Dhat H t₀ t x := hξdef
  have hξ0 : 0 < ξ := by
    rw [hξ']
    exact div_pos (mul_pos h0 hE) hD
  have h1ξ : 1 - ξ = (1 - x) / Dhat H t₀ t x := by
    rw [hξ', eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne', hDdef]
    ring
  have hξ1 : ξ < 1 := by
    have h : 0 < 1 - ξ := by
      rw [h1ξ]
      exact div_pos (sub_pos.2 h1) hD
    linarith
  have hlogξ : Real.log ξ = Real.log x + afun H t₀ t x - Real.log (Dhat H t₀ t x) := by
    rw [hξ', Real.log_div (mul_pos h0 hE).ne' hD.ne', Real.log_mul h0.ne' hE.ne', Real.log_exp]
  have hlog1ξ : Real.log (1 - ξ) = Real.log (1 - x) - Real.log (Dhat H t₀ t x) := by
    rw [h1ξ, Real.log_div (sub_pos.2 h1).ne' hD.ne']
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log x - Real.log (1 - x) + afun H t₀ t x := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → ℝ,
      w = fun y => Real.log y - Real.log (1 - y) + afun H t₀ t y - ℓ := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ → ℝ, h = fun y =>
      y * Real.log y + (1 - y) * Real.log (1 - y) + psi H t₀ t y - ℓ * y := ⟨_, rfl⟩
  have hh : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt h (w y) y := by
    intro y hy
    have hyI := Ioo_subset_Icc_self hy
    have hy0 : y ≠ 0 := hy.1.ne'
    have hy1 : 1 - y ≠ 0 := (sub_pos.2 hy.2).ne'
    have a1 : HasDerivAt (fun y : ℝ => y * Real.log y) (1 * Real.log y + y * y⁻¹) y :=
      (hasDerivAt_id y).mul (Real.hasDerivAt_log hy0)
    have a2 : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        (-1 * Real.log (1 - y) + (1 - y) * (-1 / (1 - y))) y :=
      ((hasDerivAt_id y).const_sub 1).mul (((hasDerivAt_id y).const_sub 1).log hy1)
    have a3 : HasDerivAt (psi H t₀ t) (afun H t₀ t y) y :=
      (hF.hasDerivWithinAt_psi ht hyI).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have a4 : HasDerivAt (fun y : ℝ => ℓ * y) (ℓ * 1) y := (hasDerivAt_id y).const_mul ℓ
    have a5 : HasDerivAt (fun y => y * Real.log y + (1 - y) * Real.log (1 - y)
        + psi H t₀ t y - ℓ * y)
        (1 * Real.log y + y * y⁻¹ + (-1 * Real.log (1 - y) + (1 - y) * (-1 / (1 - y)))
          + afun H t₀ t y - ℓ * 1) y := ((a1.add a2).add a3).sub a4
    rw [hhdef, hwdef]
    refine a5.congr_deriv ?_
    have e1 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    have e2 : (1 - y) * (-1 / (1 - y)) = -1 := by
      rw [mul_div_assoc', mul_neg_one, neg_div, div_self hy1]
    rw [e1, e2]
    ring
  have hw : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt w (y⁻¹ - -1 / (1 - y) + -(hq H t y) - 0) y := by
    intro y hy
    have hyI := Ioo_subset_Icc_self hy
    have a1 := Real.hasDerivAt_log hy.1.ne'
    have a2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - y)) y :=
      ((hasDerivAt_id y).const_sub 1).log (sub_pos.2 hy.2).ne'
    have a3 : HasDerivAt (afun H t₀ t) (-(hq H t y)) y :=
      (hF.hasDerivWithinAt_afun ht hyI).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have a4 : HasDerivAt (fun y => Real.log y - Real.log (1 - y) + afun H t₀ t y - ℓ)
        (y⁻¹ - -1 / (1 - y) + -(hq H t y) - 0) y :=
      ((a1.sub a2).add a3).sub (hasDerivAt_const y ℓ)
    rw [hwdef]
    exact a4
  have hwpos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < y⁻¹ - -1 / (1 - y) + -(hq H t y) - 0 := by
    intro y hy
    have hb := hF.pos t ht y (Ioo_subset_Icc_self hy)
    have hy0 := hy.1
    have hy1 : 0 < 1 - y := sub_pos.2 hy.2
    have e : y⁻¹ - -1 / (1 - y) + -(hq H t y) - 0
        = 1 / (y * (1 - y) * (1 + vstar y * H t y)) := by
      unfold hq vstar
      have hb' : (1 + y * (1 - y) * H t y) ≠ 0 := hb.ne'
      have hy0' : y ≠ 0 := hy0.ne'
      have hy1' : (1 - y) ≠ 0 := hy1.ne'
      generalize hbd : 1 + y * (1 - y) * H t y = b at hb' ⊢
      generalize hzd : 1 - y = z at hy1' hbd ⊢
      field_simp
      rw [← hbd]
      have hyz : y = 1 - z := by linarith
      rw [hyz]
      ring
    rw [e]
    exact one_div_pos.2 (mul_pos (mul_pos hy0 hy1) hb)
  have hwmono : StrictMonoOn w (Ioo 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
      (fun y hy => (hw y hy).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Ioo] at hy
    rw [(hw y hy).deriv]
    exact hwpos y hy
  have hwx : w x = 0 := by
    rw [hwdef, hℓ]
    ring
  have hmain : h x ≤ h ξ := by
    rcases le_total x ξ with hle | hle
    · have hsub : Icc x ξ ⊆ Ioo (0 : ℝ) 1 :=
        fun y hy => ⟨lt_of_lt_of_le h0 hy.1, lt_of_le_of_lt hy.2 hξ1⟩
      have hmono := monotoneOn_of_deriv_nonneg (convex_Icc x ξ)
        (fun y hy => (hh y (hsub hy)).continuousAt.continuousWithinAt)
        (fun y hy => (hh y (hsub (interior_subset hy))).differentiableAt.differentiableWithinAt)
        (fun y hy => by
          rw [interior_Icc] at hy
          have hyI := hsub (Ioo_subset_Icc_self hy)
          rw [(hh y hyI).deriv]
          have h2 := hwmono.monotoneOn hxI hyI hy.1.le
          rwa [hwx] at h2)
      exact hmono (left_mem_Icc.2 hle) (right_mem_Icc.2 hle) hle
    · have hsub : Icc ξ x ⊆ Ioo (0 : ℝ) 1 :=
        fun y hy => ⟨lt_of_lt_of_le hξ0 hy.1, lt_of_le_of_lt hy.2 h1⟩
      have hanti := antitoneOn_of_deriv_nonpos (convex_Icc ξ x)
        (fun y hy => (hh y (hsub hy)).continuousAt.continuousWithinAt)
        (fun y hy => (hh y (hsub (interior_subset hy))).differentiableAt.differentiableWithinAt)
        (fun y hy => by
          rw [interior_Icc] at hy
          have hyI := hsub (Ioo_subset_Icc_self hy)
          rw [(hh y hyI).deriv]
          have h2 := hwmono.monotoneOn hyI hxI hy.2.le
          rwa [hwx] at h2)
      exact hanti (left_mem_Icc.2 hle) (right_mem_Icc.2 hle) hle
  have hid : h ξ - h x = Pfun H t₀ t x + psi H t₀ t ξ := by
    rw [hhdef]
    show ξ * Real.log ξ + (1 - ξ) * Real.log (1 - ξ) + psi H t₀ t ξ - ℓ * ξ
        - (x * Real.log x + (1 - x) * Real.log (1 - x) + psi H t₀ t x - ℓ * x)
      = Pfun H t₀ t x + psi H t₀ t ξ
    rw [hlogξ, hlog1ξ, hℓ]
    unfold Pfun
    ring
  rw [← hξdef]
  linarith

/-- `|ψ(t₀, ·)| ≤ 2 ∫₀¹ s |H / (1 + v∗ H)| ds`. -/
theorem abs_psi_le (hF : Flow J H) (ht₀ : t₀ ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    |psi H t₀ t₀ x| ≤ 2 * ∫ s in (0 : ℝ)..1, s * |hq H t₀ s| := by
  have hJ := hF.isOpen
  have hk : Smooth J (fun t s => s * hq H t s) := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 * hq H p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
      contDiffOn_snd.mul hF.smooth_hq
    exact h
  have hder : ∀ y ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun y => psi H t₀ t₀ y - y * afun H t₀ t₀ y - Jx (fun t s => s * hq H t s) t₀ y) 0
      (Icc 0 1) y := by
    intro y hy
    have h1 := hF.hasDerivWithinAt_psi (t₀ := t₀) ht₀ hy
    have h2 : HasDerivWithinAt (fun y => y * afun H t₀ t₀ y)
        (1 * afun H t₀ t₀ y + y * -(hq H t₀ y)) (Icc 0 1) y :=
      (hasDerivWithinAt_id y _).mul (hF.hasDerivWithinAt_afun ht₀ hy)
    have h3 := hk.hasDerivWithinAt_Jx ht₀ hy
    have h4 : HasDerivWithinAt
        (fun y => psi H t₀ t₀ y - y * afun H t₀ t₀ y - Jx (fun t s => s * hq H t s) t₀ y)
        (afun H t₀ t₀ y - (1 * afun H t₀ t₀ y + y * -(hq H t₀ y)) - y * hq H t₀ y)
        (Icc 0 1) y := (h1.sub h2).sub h3
    refine h4.congr_deriv ?_
    ring
  have hconst := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    hder (fun y _ => by simp) (x := 1) (y := x) ⟨zero_le_one, le_rfl⟩ hx
  have hp1 : psi H t₀ t₀ 1 = 0 := by
    unfold psi
    rw [alpha_self, Jx_one]
    ring
  have ha1 : afun H t₀ t₀ 1 = 0 := by
    unfold afun
    rw [beta_self, Jx_one]
    ring
  rw [zero_mul, norm_le_zero_iff, hp1, ha1, Jx_one] at hconst
  have hax : afun H t₀ t₀ x = -Jx (hq H) t₀ x := by
    unfold afun
    rw [beta_self]
    ring
  have hb := integral_bounds (hF.smooth_hq.continuousOn_x ht₀) hx
  have hb1 : |Jx (fun t s => s * hq H t s) t₀ x| ≤ ∫ s in (0 : ℝ)..1, s * |hq H t₀ s| := hb.1
  have hb2 : |x * Jx (hq H) t₀ x| ≤ ∫ s in (0 : ℝ)..1, s * |hq H t₀ s| := hb.2
  have hpsi : psi H t₀ t₀ x = Jx (fun t s => s * hq H t s) t₀ x - x * Jx (hq H) t₀ x := by
    rw [hax] at hconst
    linarith
  rw [hpsi]
  have h5 := abs_sub (Jx (fun t s => s * hq H t s) t₀ x) (x * Jx (hq H) t₀ x)
  linarith

/-- **The potential at the time `t₀` is uniformly small** on `CP⁷`. -/
theorem abs_Fhat_le (hF : Flow J H) (ht₀ : t₀ ∈ J) (v : Hom) :
    |Fhat H t₀ t₀ v| ≤ 2 * ∫ s in (0 : ℝ)..1, s * |hq H t₀ s| := by
  have hX := hF.hX ht₀ ht₀ (xi_mem v)
  have hu := Pfun_le (H := H) (t₀ := t₀) (t := t₀) hX.1
  have hl := hF.Pfun_ge (t₀ := t₀) ht₀ hX.1
  have hξ : Xi H t₀ t₀ (Xinv H t₀ t₀ (xi v)) ∈ Icc (0 : ℝ) 1 := by
    rw [hX.2]
    exact xi_mem v
  have b1 := abs_le.1 (hF.abs_psi_le ht₀ hX.1)
  have b2 := abs_le.1 (hF.abs_psi_le ht₀ hξ)
  unfold Fhat
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- The bound in terms of `H` and of a lower bound of the positivity
multiplier. -/
theorem integral_hq_le (hF : Flow J H) (ht₀ : t₀ ∈ J) {κ : ℝ} (hκ : 0 < κ)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ 1 + vstar x * H t₀ x) :
    ∫ s in (0 : ℝ)..1, s * |hq H t₀ s| ≤ κ⁻¹ * ∫ s in (0 : ℝ)..1, s * |H t₀ s| := by
  have hu01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have h1 : IntervalIntegrable (fun s : ℝ => s * |hq H t₀ s|) volume 0 1 :=
    ((continuousOn_id.mul (hF.smooth_hq.continuousOn_x ht₀).abs).mono hu01.le).intervalIntegrable
  have h2 : IntervalIntegrable (fun s : ℝ => κ⁻¹ * (s * |H t₀ s|)) volume 0 1 :=
    ((continuousOn_const.mul (continuousOn_id.mul
      (hF.smooth.continuousOn_x ht₀).abs)).mono hu01.le).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one h1 h2 fun s hs => ?_
  have hb := hpos s hs
  have hb0 : 0 < 1 + vstar s * H t₀ s := lt_of_lt_of_le hκ hb
  have e : |hq H t₀ s| = |H t₀ s| / (1 + vstar s * H t₀ s) := by
    unfold hq
    rw [abs_div, abs_of_pos hb0]
  rw [e]
  have h3 : |H t₀ s| / (1 + vstar s * H t₀ s) ≤ κ⁻¹ * |H t₀ s| := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hκ hb) (abs_nonneg _)
  calc s * (|H t₀ s| / (1 + vstar s * H t₀ s)) ≤ s * (κ⁻¹ * |H t₀ s|) :=
        mul_le_mul_of_nonneg_left h3 hs.1
    _ = κ⁻¹ * (s * |H t₀ s|) := by ring

end Flow

end Calabi.Legendre
