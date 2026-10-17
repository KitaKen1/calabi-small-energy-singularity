import Calabi.Geometry.Potential
import Calabi.Geometry.ChartInfinity

/-!
# The metric of a solution of the momentum equation is a Kähler metric

For a smooth positive solution `H` of the momentum equation, the potential
`Fhat H t₀ t` of `Calabi.Geometry.Potential` is a Kähler potential of the
Fubini–Study class: `Flow.isKahlerPotential_Fhat`.

On the affine chart this is `MomentumData.levi_pos`. On the charts meeting the
divisor at infinity, the potential is `log (1 + ‖Z‖²) + Ψ(ξ)` with
`Ψ(ξ) = Pfun (Xinv ξ)`, and `levi_chart_infinity_pos` applies with

* `1 + (1 - ξ) Ψ′ = D / e^a > 0` (`Psi_posA`), the ratio `x / ξ` of the momenta;
* `1 + (1 - 2 ξ) Ψ′ + ξ (1 - ξ) Ψ″ = dx/dξ > 0` (`Psi_posB`), which follows by
  differentiating the identity `ξ + ξ (1 - ξ) Ψ′(ξ) = x(ξ)` (`Psi_identity`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Legendre

open Calabi.Geometry Calabi.Strip Calabi.Radial

/-- The potential relative to the Fubini–Study metric as a function of the
Fubini–Study momentum `ξ`. -/
noncomputable def Psi (H : ℝ → ℝ → ℝ) (t₀ t ξ : ℝ) : ℝ := Pfun H t₀ t (Xinv H t₀ t ξ)

namespace Flow

variable {J : Set ℝ} {H : ℝ → ℝ → ℝ} {t₀ t ξ : ℝ}

theorem smooth_Psi (hF : Flow J H) (ht₀ : t₀ ∈ J) : Smooth J (Psi H t₀) := by
  have h := (hF.smooth_P ht₀).comp (hF.smooth_Xinv ht₀) fun t ht ξ hξ => (hF.hX ht₀ ht hξ).1
  exact h

/-- `Ψ′ = (1 - e^a) D / e^a`. -/
theorem Dx_Psi (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Dx (Psi H t₀) t ξ
      = (1 - Real.exp (afun H t₀ t (Xinv H t₀ t ξ))) * Dhat H t₀ t (Xinv H t₀ t ξ)
        / Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) := by
  have hx := (hF.hX ht₀ ht hξ).1
  have hXd := (hF.smooth_Xinv ht₀).hasDerivWithinAt_x ht hξ
  have h : HasDerivWithinAt (fun ξ => Pfun H t₀ t (Xinv H t₀ t ξ))
      ((1 - Real.exp (afun H t₀ t (Xinv H t₀ t ξ)))
          / (Dhat H t₀ t (Xinv H t₀ t ξ)
            * (1 + vstar (Xinv H t₀ t ξ) * H t (Xinv H t₀ t ξ)))
        * Dx (Xinv H t₀) t ξ) (Icc 0 1) ξ :=
    (hF.hasDerivWithinAt_P ht hx).comp ξ hXd fun y hy => (hF.hX ht₀ ht hy).1
  have e : Dx (Psi H t₀) t ξ = _ := h.derivWithin (uniqueDiffOn_Icc_zero_one ξ hξ)
  rw [e, hF.Dx_Xinv ht₀ ht hξ, hF.Dx_Xi ht hx]
  have hD0 : Dhat H t₀ t (Xinv H t₀ t ξ) ≠ 0 := (Dhat_pos hx).ne'
  have hb : (1 + vstar (Xinv H t₀ t ξ) * H t (Xinv H t₀ t ξ)) ≠ 0 := (hF.pos t ht _ hx).ne'
  have hE : Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) ≠ 0 := Real.exp_ne_zero _
  generalize Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) = E at hE ⊢
  generalize 1 + vstar (Xinv H t₀ t ξ) * H t (Xinv H t₀ t ξ) = b at hb ⊢
  generalize Dhat H t₀ t (Xinv H t₀ t ξ) = D at hD0 ⊢
  field_simp

/-- `1 + (1 - ξ) Ψ′ = D / e^a`. -/
theorem Psi_A (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    1 + (1 - ξ) * Dx (Psi H t₀) t ξ
      = Dhat H t₀ t (Xinv H t₀ t ξ) / Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) := by
  have hx := (hF.hX ht₀ ht hξ).1
  have hval : Xinv H t₀ t ξ * Real.exp (afun H t₀ t (Xinv H t₀ t ξ))
      / Dhat H t₀ t (Xinv H t₀ t ξ) = ξ := (hF.hX ht₀ ht hξ).2
  rw [hF.Dx_Psi ht₀ ht hξ]
  have hD0 : Dhat H t₀ t (Xinv H t₀ t ξ) ≠ 0 := (Dhat_pos hx).ne'
  have hDd : Dhat H t₀ t (Xinv H t₀ t ξ)
      = 1 - Xinv H t₀ t ξ + Xinv H t₀ t ξ * Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) := rfl
  have hE : Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) ≠ 0 := Real.exp_ne_zero _
  generalize Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) = E at hE hDd hval ⊢
  generalize Dhat H t₀ t (Xinv H t₀ t ξ) = D at hD0 hDd hval ⊢
  generalize Xinv H t₀ t ξ = x at hDd hval ⊢
  rw [← hval]
  field_simp
  rw [hDd]
  ring

theorem Psi_posA (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    0 < 1 + (1 - ξ) * Dx (Psi H t₀) t ξ := by
  rw [hF.Psi_A ht₀ ht hξ]
  exact div_pos (Dhat_pos (hF.hX ht₀ ht hξ).1) (Real.exp_pos _)

/-- `ξ + ξ (1 - ξ) Ψ′(ξ) = x(ξ)`: the momentum of the metric in terms of the
potential. -/
theorem Psi_identity (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    ξ + ξ * (1 - ξ) * Dx (Psi H t₀) t ξ = Xinv H t₀ t ξ := by
  have hA := hF.Psi_A ht₀ ht hξ
  have hx := (hF.hX ht₀ ht hξ).1
  have hval : Xinv H t₀ t ξ * Real.exp (afun H t₀ t (Xinv H t₀ t ξ))
      / Dhat H t₀ t (Xinv H t₀ t ξ) = ξ := (hF.hX ht₀ ht hξ).2
  have hD0 : Dhat H t₀ t (Xinv H t₀ t ξ) ≠ 0 := (Dhat_pos hx).ne'
  have hE : Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) ≠ 0 := Real.exp_ne_zero _
  have e : ξ + ξ * (1 - ξ) * Dx (Psi H t₀) t ξ = ξ * (1 + (1 - ξ) * Dx (Psi H t₀) t ξ) := by
    ring
  rw [e, hA]
  generalize Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) = E at hE hval ⊢
  generalize Dhat H t₀ t (Xinv H t₀ t ξ) = D at hD0 hval ⊢
  generalize Xinv H t₀ t ξ = x at hval ⊢
  rw [← hval]
  field_simp

theorem Psi_posB (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    0 < 1 + (1 - 2 * ξ) * Dx (Psi H t₀) t ξ + ξ * (1 - ξ) * Dx (Dx (Psi H t₀)) t ξ := by
  have hΨs := hF.smooth_Psi ht₀
  have h1 := (hΨs.dx hF.isOpen).hasDerivWithinAt_x ht hξ
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) ξ := hasDerivWithinAt_id ξ _
  have hlhs : HasDerivWithinAt (fun y => y + y * (1 - y) * Dx (Psi H t₀) t y)
      (1 + ((1 * (1 - ξ) + ξ * -1) * Dx (Psi H t₀) t ξ
        + ξ * (1 - ξ) * Dx (Dx (Psi H t₀)) t ξ)) (Icc 0 1) ξ :=
    hid.fun_add ((hid.fun_mul (hid.const_sub 1)).fun_mul h1)
  have hrhs := (hF.smooth_Xinv ht₀).hasDerivWithinAt_x ht hξ
  have hcongr : HasDerivWithinAt (fun y => y + y * (1 - y) * Dx (Psi H t₀) t y)
      (Dx (Xinv H t₀) t ξ) (Icc 0 1) ξ :=
    hrhs.congr (fun y hy => hF.Psi_identity ht₀ ht hy) (hF.Psi_identity ht₀ ht hξ)
  have e := (uniqueDiffOn_Icc_zero_one ξ hξ).eq_deriv _ hlhs hcongr
  have hpos : 0 < Dx (Xinv H t₀) t ξ := by
    rw [hF.Dx_Xinv ht₀ ht hξ]
    exact inv_pos.2 (hF.Dx_Xi_pos ht (hF.hX ht₀ ht hξ).1)
  have e2 : 1 + (1 - 2 * ξ) * Dx (Psi H t₀) t ξ + ξ * (1 - ξ) * Dx (Dx (Psi H t₀)) t ξ
      = 1 + ((1 * (1 - ξ) + ξ * -1) * Dx (Psi H t₀) t ξ
        + ξ * (1 - ξ) * Dx (Dx (Psi H t₀)) t ξ) := by ring
  rw [e2, e]
  exact hpos

/-- **The metric of `H(t)` is a Kähler metric on `CP⁷`** in the Fubini–Study
class: its potential is smooth on `CP⁷`, and the metric is positive on every
chart. -/
theorem isKahlerPotential_Fhat (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    IsKahlerPotential (Fhat H t₀ t) := by
  refine ⟨hF.isSmoothCP_Fhat ht₀ ht, fun j Z a ha => ?_⟩
  by_cases hj : j = 0
  · subst hj
    exact hF.levi_Fhat_zero_pos ht₀ ht Z ha
  · have hpot : pot (Fhat H t₀ t) j = fun W : Aff => Real.log (1 + ‖W‖ ^ 2)
        + Psi H t₀ t (1 - ‖W 0‖ ^ 2 / (1 + ‖W‖ ^ 2)) := by
      funext W
      unfold pot Fhat Psi
      rw [xi_chart_succ hj]
    rw [hpot]
    exact levi_chart_infinity_pos (Ψ := Psi H t₀ t) (Ψ1 := Dx (Psi H t₀) t)
      (Ψ2 := Dx (Dx (Psi H t₀)) t)
      (fun ξ hξ => (hF.smooth_Psi ht₀).hasDerivWithinAt_x ht hξ)
      (fun ξ hξ => ((hF.smooth_Psi ht₀).dx hF.isOpen).hasDerivWithinAt_x ht hξ)
      (fun ξ hξ => hF.Psi_posA ht₀ ht hξ) (fun ξ hξ => hF.Psi_posB ht₀ ht hξ) Z ha

end Flow

end Calabi.Legendre
