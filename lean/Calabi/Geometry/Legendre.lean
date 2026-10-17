import Calabi.Radial.Strip
import Calabi.Geometry.Momentum

/-!
# The Legendre transform of a solution of the momentum equation

Let `H` be a smooth positive solution of `H_t + (1 + v∗ H)² A H = 0` on
`J × [0, 1]`, `J` an open interval. Following the proof of Proposition 2.1 of
the manuscript, we construct:

* `psi`: the correction `ψ = u - u∗` of the symplectic potential, with
  `ψ″ = -H / (1 + v∗ H)` and `ψ_t = K(H)` (`hasDerivWithinAt_afun`,
  `hasDerivWithinAt_psi`, `hasDerivAt_psi`); its affine part is fixed at the
  time `t₀` by `ψ(1) = ψ′(1) = 0` and evolves by `ψ_t = K(H)`;
* `Xi`: the Fubini–Study momentum `ξ = x e^a / (1 - x + x e^a)` as a function
  of the momentum `x`, `a = ψ′`, and its inverse `Xinv`, smooth on the closed
  strip;
* `Pfun`: the Kähler potential relative to the Fubini–Study metric, as a
  function of `x`. Its time derivative at fixed `ξ` is `-K(H)`
  (`hasDerivAt_Psi`), which is the Calabi flow.

`momentumData` shows that at each time the potential
`log (1 + q) + Pfun (Xinv (q / (1 + q)))` on the affine chart is described by
`H` in the sense of `Calabi.Geometry.MomentumData`, so that its scalar
curvature is `56 - K(H)`.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Calabi.Legendre

open Calabi.Radial Calabi.Strip Calabi.Geometry

/-- `H / (1 + v∗ H) = -ψ″`. -/
noncomputable def hq (H : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := H t x / (1 + vstar x * H t x)

/-- `K(H)` as a function on the strip. -/
noncomputable def KH (H : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := Kop (H t) x

/-- The value `ψ(t, 1)`. -/
noncomputable def alpha (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t₀..t, KH H s 1

/-- The value `ψ′(t, 1)`. -/
noncomputable def beta (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t₀..t, Dx (KH H) s 1

/-- `a = ψ′`. -/
noncomputable def afun (H : ℝ → ℝ → ℝ) (t₀ t x : ℝ) : ℝ := beta H t₀ t - Jx (hq H) t x

/-- The correction `ψ = u - u∗` of the symplectic potential. -/
noncomputable def psi (H : ℝ → ℝ → ℝ) (t₀ t x : ℝ) : ℝ :=
  alpha H t₀ t + beta H t₀ t * (x - 1) - Jx (Jx (hq H)) t x

/-- `1 - x + x e^a`. -/
noncomputable def Dhat (H : ℝ → ℝ → ℝ) (t₀ t x : ℝ) : ℝ :=
  1 - x + x * Real.exp (afun H t₀ t x)

/-- The Fubini–Study momentum as a function of the momentum `x`. -/
noncomputable def Xi (H : ℝ → ℝ → ℝ) (t₀ t x : ℝ) : ℝ :=
  x * Real.exp (afun H t₀ t x) / Dhat H t₀ t x

/-- The potential relative to the Fubini–Study metric, as a function of `x`. -/
noncomputable def Pfun (H : ℝ → ℝ → ℝ) (t₀ t x : ℝ) : ℝ :=
  -Real.log (Dhat H t₀ t x) + x * afun H t₀ t x - psi H t₀ t x

/-- The momentum `x` as a function of the Fubini–Study momentum. -/
noncomputable def Xinv (H : ℝ → ℝ → ℝ) (t₀ t ξ : ℝ) : ℝ :=
  Function.invFunOn (Xi H t₀ t) (Icc 0 1) ξ

/-- The momentum as a function of `q = ‖Z‖²`. -/
noncomputable def xq (H : ℝ → ℝ → ℝ) (t₀ t q : ℝ) : ℝ := Xinv H t₀ t (q / (1 + q))

/-- The potential of the chart as a function of `q = ‖Z‖²`. -/
noncomputable def phi (H : ℝ → ℝ → ℝ) (t₀ t q : ℝ) : ℝ :=
  Real.log (1 + q) + Pfun H t₀ t (xq H t₀ t q)

/-- A smooth positive solution of the momentum equation on `J × [0, 1]`. -/
structure Flow (J : Set ℝ) (H : ℝ → ℝ → ℝ) : Prop where
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  smooth : Smooth J H
  pos : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, 0 < 1 + vstar x * H t x
  eqn : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1,
    deriv (fun τ => H τ x) t + (1 + vstar x * H t x) ^ 2 * Aop (H t) x = 0

section Elementary

variable {H : ℝ → ℝ → ℝ} {t₀ t x : ℝ}

theorem Dhat_pos (hx : x ∈ Icc (0 : ℝ) 1) : 0 < Dhat H t₀ t x := by
  unfold Dhat
  have hE := Real.exp_pos (afun H t₀ t x)
  rcases le_total x (1 / 2) with h | h
  · have h0 : 0 ≤ x * Real.exp (afun H t₀ t x) := mul_nonneg hx.1 hE.le
    linarith
  · have h0 : 0 < x * Real.exp (afun H t₀ t x) := mul_pos (by linarith) hE
    linarith [hx.2]

theorem Xi_zero : Xi H t₀ t 0 = 0 := by
  simp [Xi]

theorem Xi_one : Xi H t₀ t 1 = 1 := by
  unfold Xi Dhat
  rw [sub_self, zero_add, one_mul]
  exact div_self (Real.exp_ne_zero _)

end Elementary

namespace Flow

variable {J : Set ℝ} {H : ℝ → ℝ → ℝ} (hF : Flow J H) {t₀ t x : ℝ}

include hF

/-! ### The data of the equation -/

theorem smooth_KH : Smooth J (KH H) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_snd
  have h1x : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 1 - p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
    contDiffOn_const.sub hx
  have h1 : Smooth J (Dx H) := hF.smooth.dx hF.isOpen
  have h2 : Smooth J (Dx (Dx H)) := h1.dx hF.isOpen
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 ^ 2 * (1 - p.2) ^ 2 * Dx (Dx H) p.1 p.2
      + 4 * p.2 * (1 - p.2) * (4 - 5 * p.2) * Dx H p.1 p.2
      + (56 - 144 * p.2 + 90 * p.2 ^ 2) * H p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
    ((((hx.pow 2).mul (h1x.pow 2)).mul h2).add
      ((((contDiffOn_const.mul hx).mul h1x).mul
        (contDiffOn_const.sub (contDiffOn_const.mul hx))).mul h1)).add
      (((contDiffOn_const.sub (contDiffOn_const.mul hx)).add
        (contDiffOn_const.mul (hx.pow 2))).mul hF.smooth)
  exact h

theorem smooth_hq : Smooth J (hq H) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_snd
  have hden : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 1 + p.2 * (1 - p.2) * H p.1 p.2)
      (J ×ˢ Icc (0 : ℝ) 1) :=
    contDiffOn_const.add ((hx.mul (contDiffOn_const.sub hx)).mul hF.smooth)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2 / (1 + p.2 * (1 - p.2) * H p.1 p.2))
      (J ×ˢ Icc (0 : ℝ) 1) :=
    ContDiffOn.div hF.smooth hden fun p hp => (hF.pos p.1 hp.1 p.2 hp.2).ne'
  exact h

/-- `∂_t (H / (1 + v∗ H)) = -A H`: the momentum equation. -/
theorem Dt_hq (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) : Dt (hq H) t x = -Aop (H t) x := by
  have hH := hF.smooth.hasDerivAt_t hF.isOpen ht hx
  have hb := (hF.pos t ht x hx).ne'
  have hden : HasDerivAt (fun s => 1 + vstar x * H s x) (vstar x * Dt H t x) t :=
    (hH.const_mul (vstar x)).const_add 1
  have h : HasDerivAt (fun s => H s x / (1 + vstar x * H s x))
      ((Dt H t x * (1 + vstar x * H t x) - H t x * (vstar x * Dt H t x))
        / (1 + vstar x * H t x) ^ 2) t := hH.fun_div hden hb
  have e := hF.eqn t ht x hx
  have e' : Dt H t x = -((1 + vstar x * H t x) ^ 2 * Aop (H t) x) := by
    have e0 : Dt H t x = deriv (fun τ => H τ x) t := rfl
    rw [e0]
    linarith
  have hd : Dt (hq H) t x = (Dt H t x * (1 + vstar x * H t x) - H t x * (vstar x * Dt H t x))
      / (1 + vstar x * H t x) ^ 2 := h.deriv
  rw [hd, e']
  field_simp
  ring

/-! ### The symplectic potential -/

theorem hasDerivAt_alpha (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    HasDerivAt (alpha H t₀) (KH H t 1) t :=
  hasDerivAt_primitive hF.isOpen hF.ordConnected
    (hF.smooth_KH.slice_t ⟨zero_le_one, le_rfl⟩).continuousOn ht₀ ht

theorem hasDerivAt_beta (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    HasDerivAt (beta H t₀) (Dx (KH H) t 1) t :=
  hasDerivAt_primitive hF.isOpen hF.ordConnected
    ((hF.smooth_KH.dx hF.isOpen).slice_t ⟨zero_le_one, le_rfl⟩).continuousOn ht₀ ht

theorem smooth_alpha (ht₀ : t₀ ∈ J) : Smooth J (fun t _ => alpha H t₀ t) :=
  smooth_of_t (contDiffOn_primitive hF.isOpen hF.ordConnected
    (hF.smooth_KH.slice_t ⟨zero_le_one, le_rfl⟩) ht₀)

theorem smooth_beta (ht₀ : t₀ ∈ J) : Smooth J (fun t _ => beta H t₀ t) :=
  smooth_of_t (contDiffOn_primitive hF.isOpen hF.ordConnected
    ((hF.smooth_KH.dx hF.isOpen).slice_t ⟨zero_le_one, le_rfl⟩) ht₀)

theorem smooth_afun (ht₀ : t₀ ∈ J) : Smooth J (afun H t₀) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => beta H t₀ p.1 - Jx (hq H) p.1 p.2)
      (J ×ˢ Icc (0 : ℝ) 1) := (hF.smooth_beta ht₀).sub (hF.smooth_hq.jx hF.isOpen)
  exact h

theorem smooth_psi (ht₀ : t₀ ∈ J) : Smooth J (psi H t₀) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 - 1) (J ×ˢ Icc (0 : ℝ) 1) :=
    contDiffOn_snd.sub contDiffOn_const
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      alpha H t₀ p.1 + beta H t₀ p.1 * (p.2 - 1) - Jx (Jx (hq H)) p.1 p.2)
      (J ×ˢ Icc (0 : ℝ) 1) :=
    ((hF.smooth_alpha ht₀).add ((hF.smooth_beta ht₀).mul hx)).sub
      ((hF.smooth_hq.jx hF.isOpen).jx hF.isOpen)
  exact h

/-- `a′ = ψ″ = -H / (1 + v∗ H)`. -/
theorem hasDerivWithinAt_afun (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (afun H t₀ t) (-(hq H t x)) (Icc 0 1) x := by
  have h : HasDerivWithinAt (fun y => beta H t₀ t - Jx (hq H) t y) (-(hq H t x)) (Icc 0 1) x :=
    (hF.smooth_hq.hasDerivWithinAt_Jx ht hx).const_sub (beta H t₀ t)
  exact h

/-- `ψ′ = a`. -/
theorem hasDerivWithinAt_psi (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (psi H t₀ t) (afun H t₀ t x) (Icc 0 1) x := by
  have h1 : HasDerivWithinAt (fun y : ℝ => beta H t₀ t * (y - 1)) (beta H t₀ t * 1)
      (Icc 0 1) x := ((hasDerivWithinAt_id x _).sub_const 1).const_mul _
  have h2 := (hF.smooth_hq.jx hF.isOpen).hasDerivWithinAt_Jx ht hx
  have h : HasDerivWithinAt
      (fun y => alpha H t₀ t + beta H t₀ t * (y - 1) - Jx (Jx (hq H)) t y)
      (beta H t₀ t * 1 - Jx (hq H) t x) (Icc 0 1) x := (h1.const_add _).fun_sub h2
  refine h.congr_deriv ?_
  rw [mul_one]
  rfl

/-- `ψ_t = K(H)`: equation (2.13) of the manuscript. -/
theorem hasDerivAt_psi (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => psi H t₀ s x) (KH H t x) t := by
  have hJ := hF.isOpen
  have hk := hF.smooth_KH
  have hk1 := hk.dx hJ
  have hJJ := (hF.smooth_hq.jx hJ).hasDerivAt_Jx hJ ht hx
  have h : HasDerivAt (fun s => alpha H t₀ s + beta H t₀ s * (x - 1) - Jx (Jx (hq H)) s x)
      (KH H t 1 + Dx (KH H) t 1 * (x - 1) - Jx (Dt (Jx (hq H))) t x) t :=
    ((hF.hasDerivAt_alpha ht₀ ht).fun_add ((hF.hasDerivAt_beta ht₀ ht).mul_const (x - 1))).fun_sub
      hJJ
  refine h.congr_deriv ?_
  have e1 : ∀ y ∈ Icc (0 : ℝ) 1,
      Dt (Jx (hq H)) t y = -(Dx (KH H) t y - Dx (KH H) t 1) := by
    intro y hy
    have a1 : Dt (Jx (hq H)) t y = Jx (Dt (hq H)) t y :=
      (hF.smooth_hq.hasDerivAt_Jx hJ ht hy).deriv
    have a2 : Jx (Dt (hq H)) t y = -Jx (Dx (Dx (KH H))) t y := by
      show (∫ z in (1 : ℝ)..y, Dt (hq H) t z) = -∫ z in (1 : ℝ)..y, Dx (Dx (KH H)) t z
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun z hz => ?_
      exact hF.Dt_hq ht (uIcc_one_subset hy hz)
    rw [a1, a2, hk1.Jx_Dx hJ ht hy]
  have e2 : Jx (Dt (Jx (hq H))) t x = -(KH H t x - KH H t 1) + (x - 1) * Dx (KH H) t 1 := by
    have a1 : Jx (Dt (Jx (hq H))) t x
        = ∫ y in (1 : ℝ)..x, (-(Dx (KH H) t y) + Dx (KH H) t 1) := by
      show (∫ y in (1 : ℝ)..x, Dt (Jx (hq H)) t y) = _
      refine intervalIntegral.integral_congr fun y hy => ?_
      show Dt (Jx (hq H)) t y = -(Dx (KH H) t y) + Dx (KH H) t 1
      rw [e1 y (uIcc_one_subset hx hy)]
      ring
    have a3 : (∫ y in (1 : ℝ)..x, Dx (KH H) t y) = KH H t x - KH H t 1 := hk.Jx_Dx hJ ht hx
    have a4 : (∫ y in (1 : ℝ)..x, (-(Dx (KH H) t y) + Dx (KH H) t 1))
        = (∫ y in (1 : ℝ)..x, -(Dx (KH H) t y)) + ∫ _y in (1 : ℝ)..x, Dx (KH H) t 1 :=
      intervalIntegral.integral_add (f := fun y => -(Dx (KH H) t y))
        (g := fun _ => Dx (KH H) t 1) (hk1.intervalIntegrable ht hx).neg intervalIntegrable_const
    rw [a1, a4, intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul, a3]
  rw [e2]
  ring

/-! ### The Fubini–Study momentum as a function of the momentum -/

theorem smooth_exp (ht₀ : t₀ ∈ J) : Smooth J (fun t x => Real.exp (afun H t₀ t x)) :=
  ContDiffOn.exp (hF.smooth_afun ht₀)

theorem smooth_Dhat (ht₀ : t₀ ∈ J) : Smooth J (Dhat H t₀) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_snd
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 1 - p.2 + p.2 * Real.exp (afun H t₀ p.1 p.2))
      (J ×ˢ Icc (0 : ℝ) 1) := (contDiffOn_const.sub hx).add (hx.mul (hF.smooth_exp ht₀))
  exact h

theorem smooth_Xi (ht₀ : t₀ ∈ J) : Smooth J (Xi H t₀) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_snd
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      p.2 * Real.exp (afun H t₀ p.1 p.2) / Dhat H t₀ p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
    ContDiffOn.div (hx.mul (hF.smooth_exp ht₀)) (hF.smooth_Dhat ht₀)
      fun p hp => (Dhat_pos hp.2).ne'
  exact h

theorem smooth_P (ht₀ : t₀ ∈ J) : Smooth J (Pfun H t₀) := by
  have hx : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_snd
  have hlog : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.log (Dhat H t₀ p.1 p.2))
      (J ×ˢ Icc (0 : ℝ) 1) :=
    ContDiffOn.log (hF.smooth_Dhat ht₀) fun p hp => (Dhat_pos hp.2).ne'
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      -Real.log (Dhat H t₀ p.1 p.2) + p.2 * afun H t₀ p.1 p.2 - psi H t₀ p.1 p.2)
      (J ×ˢ Icc (0 : ℝ) 1) :=
    (hlog.neg.add (hx.mul (hF.smooth_afun ht₀))).sub (hF.smooth_psi ht₀)
  exact h

theorem hasDerivWithinAt_xE (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun y => y * Real.exp (afun H t₀ t y))
      (1 * Real.exp (afun H t₀ t x) + x * (Real.exp (afun H t₀ t x) * -(hq H t x)))
      (Icc 0 1) x := by
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) x := hasDerivWithinAt_id x _
  have hE : HasDerivWithinAt (fun y => Real.exp (afun H t₀ t y))
      (Real.exp (afun H t₀ t x) * -(hq H t x)) (Icc 0 1) x :=
    (hF.hasDerivWithinAt_afun ht hx).exp
  exact hid.fun_mul hE

theorem hasDerivWithinAt_Dhat (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (Dhat H t₀ t)
      (-1 + (1 * Real.exp (afun H t₀ t x) + x * (Real.exp (afun H t₀ t x) * -(hq H t x))))
      (Icc 0 1) x := by
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) x := hasDerivWithinAt_id x _
  have h : HasDerivWithinAt (fun y => 1 - y + y * Real.exp (afun H t₀ t y))
      (-1 + (1 * Real.exp (afun H t₀ t x) + x * (Real.exp (afun H t₀ t x) * -(hq H t x))))
      (Icc 0 1) x := (hid.const_sub 1).fun_add (hF.hasDerivWithinAt_xE ht hx)
  exact h

/-- `∂_x ξ = e^a / (D² b)`. -/
theorem hasDerivWithinAt_Xi (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (Xi H t₀ t)
      (Real.exp (afun H t₀ t x) / (Dhat H t₀ t x ^ 2 * (1 + vstar x * H t x))) (Icc 0 1) x := by
  have hD0 : Dhat H t₀ t x ≠ 0 := (Dhat_pos hx).ne'
  have h : HasDerivWithinAt (fun y => y * Real.exp (afun H t₀ t y) / Dhat H t₀ t y)
      (((1 * Real.exp (afun H t₀ t x) + x * (Real.exp (afun H t₀ t x) * -(hq H t x)))
          * Dhat H t₀ t x
        - x * Real.exp (afun H t₀ t x)
          * (-1 + (1 * Real.exp (afun H t₀ t x)
            + x * (Real.exp (afun H t₀ t x) * -(hq H t x))))) / Dhat H t₀ t x ^ 2)
      (Icc 0 1) x := (hF.hasDerivWithinAt_xE ht hx).fun_div (hF.hasDerivWithinAt_Dhat ht hx) hD0
  refine h.congr_deriv ?_
  have hb : (1 + x * (1 - x) * H t x) ≠ 0 := (hF.pos t ht x hx).ne'
  unfold hq vstar
  unfold Dhat at hD0 ⊢
  generalize Real.exp (afun H t₀ t x) = E at hD0 ⊢
  generalize hbd : 1 + x * (1 - x) * H t x = b at hb ⊢
  generalize hDd : 1 - x + x * E = D at hD0 ⊢
  field_simp
  subst hbd hDd
  ring

/-- `∂_x P = (1 - e^a) / (D b)`. -/
theorem hasDerivWithinAt_P (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (Pfun H t₀ t)
      ((1 - Real.exp (afun H t₀ t x)) / (Dhat H t₀ t x * (1 + vstar x * H t x)))
      (Icc 0 1) x := by
  have hD0 : Dhat H t₀ t x ≠ 0 := (Dhat_pos hx).ne'
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) x := hasDerivWithinAt_id x _
  have hlog : HasDerivWithinAt (fun y => Real.log (Dhat H t₀ t y))
      ((-1 + (1 * Real.exp (afun H t₀ t x) + x * (Real.exp (afun H t₀ t x) * -(hq H t x))))
        / Dhat H t₀ t x) (Icc 0 1) x := (hF.hasDerivWithinAt_Dhat ht hx).log hD0
  have hxa : HasDerivWithinAt (fun y => y * afun H t₀ t y)
      (1 * afun H t₀ t x + x * -(hq H t x)) (Icc 0 1) x :=
    hid.fun_mul (hF.hasDerivWithinAt_afun ht hx)
  have h : HasDerivWithinAt
      (fun y => -Real.log (Dhat H t₀ t y) + y * afun H t₀ t y - psi H t₀ t y)
      (-((-1 + (1 * Real.exp (afun H t₀ t x)
          + x * (Real.exp (afun H t₀ t x) * -(hq H t x)))) / Dhat H t₀ t x)
        + (1 * afun H t₀ t x + x * -(hq H t x)) - afun H t₀ t x) (Icc 0 1) x :=
    (hlog.neg.fun_add hxa).fun_sub (hF.hasDerivWithinAt_psi ht hx)
  refine h.congr_deriv ?_
  have hb : (1 + x * (1 - x) * H t x) ≠ 0 := (hF.pos t ht x hx).ne'
  unfold hq vstar
  unfold Dhat at hD0 ⊢
  generalize Real.exp (afun H t₀ t x) = E at hD0 ⊢
  generalize hbd : 1 + x * (1 - x) * H t x = b at hb ⊢
  generalize hDd : 1 - x + x * E = D at hD0 ⊢
  field_simp
  subst hbd hDd
  ring

theorem Dx_Xi (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dx (Xi H t₀) t x
      = Real.exp (afun H t₀ t x) / (Dhat H t₀ t x ^ 2 * (1 + vstar x * H t x)) :=
  (hF.hasDerivWithinAt_Xi ht hx).derivWithin (uniqueDiffOn_Icc_zero_one x hx)

theorem Dx_P (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dx (Pfun H t₀) t x
      = (1 - Real.exp (afun H t₀ t x)) / (Dhat H t₀ t x * (1 + vstar x * H t x)) :=
  (hF.hasDerivWithinAt_P ht hx).derivWithin (uniqueDiffOn_Icc_zero_one x hx)

theorem Dx_Xi_pos (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < Dx (Xi H t₀) t x := by
  rw [hF.Dx_Xi ht hx]
  exact div_pos (Real.exp_pos _) (mul_pos (pow_pos (Dhat_pos hx) 2) (hF.pos t ht x hx))

/-! ### The inverse -/

theorem hX (ht₀ : t₀ ∈ J) (ht : t ∈ J) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Xinv H t₀ t ξ ∈ Icc (0 : ℝ) 1 ∧ Xi H t₀ t (Xinv H t₀ t ξ) = ξ := by
  have hc := (hF.smooth_Xi ht₀).continuousOn_x ht
  have h := intermediate_value_Icc (zero_le_one' ℝ) hc
  rw [Xi_zero, Xi_one] at h
  obtain ⟨y, hy, hyξ⟩ := h hξ
  exact Function.invFunOn_pos ⟨y, hy, hyξ⟩

theorem smooth_Xinv (ht₀ : t₀ ∈ J) : Smooth J (Xinv H t₀) :=
  smooth_inverse hF.isOpen (hF.smooth_Xi ht₀) (fun _ ht _ hx => hF.Dx_Xi_pos ht hx)
    (fun _ ht _ hξ => hF.hX ht₀ ht hξ)

theorem Xinv_Xi (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Xinv H t₀ t (Xi H t₀ t x) = x := by
  have hmono := (hF.smooth_Xi ht₀).strictMonoOn (fun _ ht _ hx => hF.Dx_Xi_pos ht hx) ht
  have hξ : Xi H t₀ t x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have h := hmono.monotoneOn ⟨le_rfl, zero_le_one⟩ hx hx.1
      rwa [Xi_zero] at h
    · have h := hmono.monotoneOn hx ⟨zero_le_one, le_rfl⟩ hx.2
      rwa [Xi_one] at h
  have h := hF.hX ht₀ ht hξ
  exact hmono.injOn h.1 hx h.2

theorem Xinv_zero (ht₀ : t₀ ∈ J) (ht : t ∈ J) : Xinv H t₀ t 0 = 0 := by
  have h := hF.Xinv_Xi ht₀ ht (x := 0) ⟨le_rfl, zero_le_one⟩
  rwa [Xi_zero] at h

theorem Xinv_one (ht₀ : t₀ ∈ J) (ht : t ∈ J) : Xinv H t₀ t 1 = 1 := by
  have h := hF.Xinv_Xi ht₀ ht (x := 1) ⟨zero_le_one, le_rfl⟩
  rwa [Xi_one] at h

theorem Dx_Xinv (ht₀ : t₀ ∈ J) (ht : t ∈ J) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Dx (Xinv H t₀) t ξ = (Dx (Xi H t₀) t (Xinv H t₀ t ξ))⁻¹ :=
  inverse_Dx hF.isOpen (hF.smooth_Xi ht₀) (fun _ ht _ hx => hF.Dx_Xi_pos ht hx)
    (fun _ ht _ hξ => hF.hX ht₀ ht hξ) ht hξ

theorem Dt_Xinv (ht₀ : t₀ ∈ J) (ht : t ∈ J) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Dt (Xinv H t₀) t ξ
      = -(Dt (Xi H t₀) t (Xinv H t₀ t ξ)) / Dx (Xi H t₀) t (Xinv H t₀ t ξ) :=
  inverse_Dt hF.isOpen (hF.smooth_Xi ht₀) (fun _ ht _ hx => hF.Dx_Xi_pos ht hx)
    (fun _ ht _ hξ => hF.hX ht₀ ht hξ) ht hξ

/-! ### Derivatives in time -/

theorem hasDerivAt_exp_t (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Real.exp (afun H t₀ s x))
      (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) t :=
  ((hF.smooth_afun ht₀).hasDerivAt_t hF.isOpen ht hx).exp

theorem hasDerivAt_Dhat_t (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Dhat H t₀ s x)
      (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x)) t := by
  have h : HasDerivAt (fun s => 1 - x + x * Real.exp (afun H t₀ s x))
      (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x)) t :=
    ((hF.hasDerivAt_exp_t ht₀ ht hx).const_mul x).const_add (1 - x)
  exact h

theorem Dt_Xi (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dt (Xi H t₀) t x
      = (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) * Dhat H t₀ t x
          - x * Real.exp (afun H t₀ t x)
            * (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x))) / Dhat H t₀ t x ^ 2 := by
  have h : HasDerivAt (fun s => x * Real.exp (afun H t₀ s x) / Dhat H t₀ s x)
      ((x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) * Dhat H t₀ t x
          - x * Real.exp (afun H t₀ t x)
            * (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x))) / Dhat H t₀ t x ^ 2) t :=
    ((hF.hasDerivAt_exp_t ht₀ ht hx).const_mul x).fun_div (hF.hasDerivAt_Dhat_t ht₀ ht hx)
      (Dhat_pos hx).ne'
  exact h.deriv

theorem Dt_P (ht₀ : t₀ ∈ J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dt (Pfun H t₀) t x
      = -(x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) / Dhat H t₀ t x)
        + x * Dt (afun H t₀) t x - KH H t x := by
  have ha := (hF.smooth_afun ht₀).hasDerivAt_t hF.isOpen ht hx
  have hlog : HasDerivAt (fun s => Real.log (Dhat H t₀ s x))
      (x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) / Dhat H t₀ t x) t :=
    (hF.hasDerivAt_Dhat_t ht₀ ht hx).log (Dhat_pos hx).ne'
  have h : HasDerivAt
      (fun s => -Real.log (Dhat H t₀ s x) + x * afun H t₀ s x - psi H t₀ s x)
      (-(x * (Real.exp (afun H t₀ t x) * Dt (afun H t₀) t x) / Dhat H t₀ t x)
        + x * Dt (afun H t₀) t x - KH H t x) t :=
    (hlog.neg.fun_add (ha.const_mul x)).fun_sub (hF.hasDerivAt_psi ht₀ ht hx)
  exact h.deriv

/-- **The Calabi flow for the potential at a fixed point**: the time derivative
of the potential at fixed Fubini–Study momentum `ξ` is `-K(H)`, equation (2.14)
of the manuscript. -/
theorem hasDerivAt_Psi (ht₀ : t₀ ∈ J) (ht : t ∈ J) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Pfun H t₀ s (Xinv H t₀ s ξ)) (-(KH H t (Xinv H t₀ t ξ))) t := by
  have hJ := hF.isOpen
  have hx := (hF.hX ht₀ ht hξ).1
  have hc' := (hF.smooth_Xinv ht₀).hasDerivAt_t hJ ht hξ
  have h := (hF.smooth_P ht₀).hasDerivAt_comp hJ ht (fun s hs => (hF.hX ht₀ hs hξ).1) hc'
  refine h.congr_deriv ?_
  rw [hF.Dt_P ht₀ ht hx, hF.Dx_P ht hx, hF.Dt_Xinv ht₀ ht hξ, hF.Dt_Xi ht₀ ht hx,
    hF.Dx_Xi ht hx]
  have hD0 : Dhat H t₀ t (Xinv H t₀ t ξ) ≠ 0 := (Dhat_pos hx).ne'
  have hb : (1 + vstar (Xinv H t₀ t ξ) * H t (Xinv H t₀ t ξ)) ≠ 0 :=
    (hF.pos t ht _ hx).ne'
  have hE : Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) ≠ 0 := Real.exp_ne_zero _
  unfold Dhat at hD0 ⊢
  generalize Real.exp (afun H t₀ t (Xinv H t₀ t ξ)) = E at hD0 hE ⊢
  generalize 1 + vstar (Xinv H t₀ t ξ) * H t (Xinv H t₀ t ξ) = b at hb ⊢
  field_simp
  ring

/-! ### The chart at a fixed time -/

theorem xq_mem (ht₀ : t₀ ∈ J) (ht : t ∈ J) {q : ℝ} (hq : 0 ≤ q) :
    xq H t₀ t q ∈ Ico (0 : ℝ) 1 := by
  have h1q : 0 < 1 + q := by linarith
  have hlt : q / (1 + q) < 1 := (div_lt_one h1q).2 (by linarith)
  have hξ : q / (1 + q) ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hq h1q.le, hlt.le⟩
  obtain ⟨hmem, hval⟩ := hF.hX ht₀ ht hξ
  refine ⟨hmem.1, lt_of_le_of_ne hmem.2 fun h1 => ?_⟩
  have h1' : Xinv H t₀ t (q / (1 + q)) = 1 := h1
  rw [h1', Xi_one] at hval
  linarith

theorem xq_rel (ht₀ : t₀ ∈ J) (ht : t ∈ J) {q : ℝ} (hq : 0 ≤ q) :
    q * (1 - xq H t₀ t q) = xq H t₀ t q * Real.exp (afun H t₀ t (xq H t₀ t q)) := by
  have h1q : 0 < 1 + q := by linarith
  have hlt : q / (1 + q) < 1 := (div_lt_one h1q).2 (by linarith)
  have hξ : q / (1 + q) ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hq h1q.le, hlt.le⟩
  obtain ⟨hmem, hval⟩ := hF.hX ht₀ ht hξ
  have hD0 : Dhat H t₀ t (xq H t₀ t q) ≠ 0 := (Dhat_pos hmem).ne'
  have hval' : xq H t₀ t q * Real.exp (afun H t₀ t (xq H t₀ t q)) / Dhat H t₀ t (xq H t₀ t q)
      = q / (1 + q) := hval
  rw [div_eq_div_iff hD0 h1q.ne'] at hval'
  unfold Dhat at hval'
  linear_combination -hval'

/-- At each time, the potential of the chart is described by `H` in the
momentum coordinate. -/
theorem momentumData (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    MomentumData (H t) (afun H t₀ t) (xq H t₀ t) (phi H t₀ t) := by
  have hJ := hF.isOpen
  have hmaps : MapsTo (fun q : ℝ => q / (1 + q)) (Ici 0) (Icc (0 : ℝ) 1) := by
    intro q hq
    have h1q : 0 < 1 + q := by linarith [mem_Ici.1 hq]
    exact ⟨div_nonneg hq h1q.le, ((div_lt_one h1q).2 (by linarith)).le⟩
  have hξd : ∀ q : ℝ, 0 ≤ q →
      HasDerivWithinAt (fun q : ℝ => q / (1 + q)) (1 / (1 + q) ^ 2) (Ici 0) q := by
    intro q hq
    have h1q : (1 + q) ≠ 0 := by linarith
    have h : HasDerivAt (fun q : ℝ => q / (1 + q)) ((1 * (1 + q) - q * 1) / (1 + q) ^ 2) q :=
      (hasDerivAt_id q).fun_div ((hasDerivAt_id q).const_add 1) h1q
    refine (h.congr_deriv ?_).hasDerivWithinAt
    ring
  have hdx : ∀ q : ℝ, 0 ≤ q → HasDerivWithinAt (xq H t₀ t)
      (Momentum.f3 (H t) (afun H t₀ t) (xq H t₀ t q)) (Ici 0) q := by
    intro q hq
    have hmem := hF.xq_mem ht₀ ht hq
    have hx := Ico_subset_Icc_self hmem
    have hXd := (hF.smooth_Xinv ht₀).hasDerivWithinAt_x ht (hmaps hq)
    have h : HasDerivWithinAt (fun q => Xinv H t₀ t (q / (1 + q)))
        (Dx (Xinv H t₀) t (q / (1 + q)) * (1 / (1 + q) ^ 2)) (Ici 0) q :=
      hXd.comp q (hξd q hq) hmaps
    refine h.congr_deriv ?_
    have hrel := hF.xq_rel ht₀ ht hq
    have e1 : Dx (Xinv H t₀) t (q / (1 + q))
        = (Real.exp (afun H t₀ t (xq H t₀ t q))
          / (Dhat H t₀ t (xq H t₀ t q) ^ 2 * (1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q))))⁻¹ := by
      rw [hF.Dx_Xinv ht₀ ht (hmaps hq)]
      exact congrArg _ (hF.Dx_Xi ht hx)
    rw [e1]
    have h1x : (1 - xq H t₀ t q) ≠ 0 := (sub_pos.2 hmem.2).ne'
    have h1q : (1 + q) ≠ 0 := by linarith
    have hD : Dhat H t₀ t (xq H t₀ t q) = (1 + q) * (1 - xq H t₀ t q) := by
      unfold Dhat
      linear_combination -hrel
    have hb : (1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q)) ≠ 0 := (hF.pos t ht _ hx).ne'
    have hE : Real.exp (afun H t₀ t (xq H t₀ t q)) ≠ 0 := Real.exp_ne_zero _
    rw [hD]
    unfold Momentum.f3 Momentum.bfun
    rw [Real.exp_neg]
    generalize Real.exp (afun H t₀ t (xq H t₀ t q)) = E at hE ⊢
    generalize 1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q) = b at hb ⊢
    field_simp
  refine ⟨fun x hx => hF.smooth.hasDerivWithinAt_x ht hx,
    fun x hx => (hF.smooth.dx hJ).hasDerivWithinAt_x ht hx, fun x hx => hF.pos t ht x hx,
    fun x hx => ?_, fun q hq => hF.xq_mem ht₀ ht hq, fun q hq => hF.xq_rel ht₀ ht hq, hdx,
    fun q hq => ?_⟩
  · refine (hF.hasDerivWithinAt_afun ht hx).congr_deriv ?_
    unfold hq Momentum.bfun
    rw [neg_div]
  · have hmem := hF.xq_mem ht₀ ht hq
    have hx := Ico_subset_Icc_self hmem
    have h1q : (1 + q) ≠ 0 := by linarith
    have hlog : HasDerivWithinAt (fun q : ℝ => Real.log (1 + q)) (1 / (1 + q)) (Ici 0) q :=
      (((hasDerivAt_id q).const_add 1).log h1q).hasDerivWithinAt
    have hP : HasDerivWithinAt (fun q => Pfun H t₀ t (xq H t₀ t q))
        ((1 - Real.exp (afun H t₀ t (xq H t₀ t q)))
            / (Dhat H t₀ t (xq H t₀ t q) * (1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q)))
          * Momentum.f3 (H t) (afun H t₀ t) (xq H t₀ t q)) (Ici 0) q :=
      (hF.hasDerivWithinAt_P ht hx).comp q (hdx q hq)
        fun q' hq' => Ico_subset_Icc_self (hF.xq_mem ht₀ ht hq')
    have h : HasDerivWithinAt (fun q => Real.log (1 + q) + Pfun H t₀ t (xq H t₀ t q))
        (1 / (1 + q) + (1 - Real.exp (afun H t₀ t (xq H t₀ t q)))
            / (Dhat H t₀ t (xq H t₀ t q) * (1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q)))
          * Momentum.f3 (H t) (afun H t₀ t) (xq H t₀ t q)) (Ici 0) q := hlog.fun_add hP
    refine h.congr_deriv ?_
    have hrel := hF.xq_rel ht₀ ht hq
    have h1x : (1 - xq H t₀ t q) ≠ 0 := (sub_pos.2 hmem.2).ne'
    have hD : Dhat H t₀ t (xq H t₀ t q) = (1 + q) * (1 - xq H t₀ t q) := by
      unfold Dhat
      linear_combination -hrel
    have hb : (1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q)) ≠ 0 := (hF.pos t ht _ hx).ne'
    have hE : Real.exp (afun H t₀ t (xq H t₀ t q)) ≠ 0 := Real.exp_ne_zero _
    have hpw : (1 + q) * (1 - xq H t₀ t q) = Real.exp (afun H t₀ t (xq H t₀ t q))
        + (1 - Real.exp (afun H t₀ t (xq H t₀ t q))) * (1 - xq H t₀ t q) := by
      linear_combination hrel
    rw [hD]
    unfold Momentum.f3 Momentum.f1 Momentum.bfun
    rw [Real.exp_neg]
    generalize Real.exp (afun H t₀ t (xq H t₀ t q)) = E at hE hpw ⊢
    generalize 1 + vstar (xq H t₀ t q) * H t (xq H t₀ t q) = b at hb ⊢
    generalize 1 - xq H t₀ t q = w at h1x hpw ⊢
    generalize 1 + q = p at h1q hpw ⊢
    field_simp
    linear_combination -hpw

end Flow

end Calabi.Legendre
