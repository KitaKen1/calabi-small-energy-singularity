import Calabi.Geometry.RadialScalar
import Calabi.Radial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The momentum coordinate on the affine chart

A `U(7)`-invariant potential `u(Z) = φ(‖Z‖²)` on `ℂ⁷` is described in the
momentum coordinate `x = q φ′(q)`, `q = ‖Z‖²`, by a function `H` on `[0, 1]`
and a primitive `a` of `-H / (1 + v∗ H)`: the relation between the two
coordinates is

  `q = x exp (a x) / (1 - x)`        (equation (2.8) of the manuscript).

`MomentumData H a xq φ` records this relation together with the derivatives
`dx/dq = (1 - x)² b exp (-a)`, `b = 1 + v∗ H`, and `φ′ = (1 - x) exp (-a)`.
All the quantities of the metric are then regular functions of `x`, including
at the point orbit `x = 0`:

* `MomentumData.detg_eq`: `det (u_{j k̄}) = (1 - x)⁸ b exp (-7 a)`;
* `MomentumData.levi_pos`: the metric is positive;
* `MomentumData.scal_eq`: **the scalar curvature is `56 - K(H)(x)`**, the
  formula (2.4) of the manuscript.

The computation is `S = -(7 T + x T′)` with
`T = (1 - x) b (log det)′ = -8 b + (1 - x) b′ + 7 (1 - x) H`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

open Calabi.Radial

namespace Momentum

/-- `b = 1 + v∗ H`, the positivity multiplier. -/
def bfun (H : ℝ → ℝ) (x : ℝ) : ℝ := 1 + vstar x * H x

/-- `b′`. -/
noncomputable def b1 (H : ℝ → ℝ) (x : ℝ) : ℝ := (1 - 2 * x) * H x + x * (1 - x) * D H x

/-- `b″`. -/
noncomputable def b2 (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * H x + 2 * (1 - 2 * x) * D H x + x * (1 - x) * D (D H) x

/-- `T = (1 - x) b (log det)′`. -/
noncomputable def Tfun (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  -8 * bfun H x + (1 - x) * b1 H x + 7 * (1 - x) * H x

/-- `T′`. -/
noncomputable def T1 (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  -9 * b1 H x + (1 - x) * b2 H x - 7 * H x + 7 * (1 - x) * D H x

/-- `φ′ = x / q`, the tangential eigenvalue. -/
noncomputable def f1 (a : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x) * Real.exp (-(a x))

/-- `φ′ + q φ″ = dx/dq`, the radial eigenvalue. -/
noncomputable def f3 (H a : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x) ^ 2 * bfun H x * Real.exp (-(a x))

/-- `φ″`. -/
noncomputable def f2 (H a : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(a x)) ^ 2 * (1 - x) ^ 2 * (-(bfun H x) + (1 - x) * H x)

/-- `log det (u_{j k̄})`. -/
noncomputable def Rfun (H a : ℝ → ℝ) (x : ℝ) : ℝ :=
  8 * Real.log (1 - x) + Real.log (bfun H x) - 7 * a x

/-- `-(7 T + x T′) = 56 - K(H)`. -/
theorem seven_T (H : ℝ → ℝ) (x : ℝ) : 7 * Tfun H x + x * T1 H x = Kop H x - 56 := by
  unfold Tfun T1 b1 b2 bfun Kop vstar
  ring

theorem f1'_mul_f3 {H a : ℝ → ℝ} {x : ℝ} (hb : bfun H x ≠ 0) :
    (-Real.exp (-(a x)) + (1 - x) * (Real.exp (-(a x)) * (H x / bfun H x))) * f3 H a x
      = f2 H a x := by
  unfold f3 f2
  field_simp

theorem R'_mul_f3 {H a : ℝ → ℝ} {x : ℝ} (h1 : 1 - x ≠ 0) (hb : bfun H x ≠ 0) :
    (8 * (-1 / (1 - x)) + b1 H x / bfun H x - 7 * (-(H x) / bfun H x)) * f3 H a x
      = Tfun H x * f1 a x := by
  unfold f3 f1 Tfun
  field_simp
  ring

end Momentum

open Momentum

/-- The description of a radial potential `φ(‖Z‖²)` on the chart `ℂ⁷` in the
momentum coordinate `x = xq q`. -/
structure MomentumData (H a xq φ : ℝ → ℝ) : Prop where
  dH : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (D H x) (Icc 0 1) x
  ddH : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (D H) (D (D H) x) (Icc 0 1) x
  pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < bfun H x
  da : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt a (-(H x) / bfun H x) (Icc 0 1) x
  mem : ∀ q, 0 ≤ q → xq q ∈ Ico (0 : ℝ) 1
  rel : ∀ q, 0 ≤ q → q * (1 - xq q) = xq q * Real.exp (a (xq q))
  dx : ∀ q, 0 ≤ q → HasDerivWithinAt xq (f3 H a (xq q)) (Ici 0) q
  dφ : ∀ q, 0 ≤ q → HasDerivWithinAt φ (f1 a (xq q)) (Ici 0) q

namespace MomentumData

variable {H a xq φ : ℝ → ℝ} (M : MomentumData H a xq φ)

include M

/-! ### Derivatives in the momentum coordinate -/

theorem hasDerivWithinAt_b {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (bfun H) (b1 H x) (Icc 0 1) x := by
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) x := hasDerivWithinAt_id x _
  have h1x : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) x := hid.const_sub 1
  have hv : HasDerivWithinAt (fun y : ℝ => y * (1 - y)) (1 * (1 - x) + x * -1) (Icc 0 1) x :=
    hid.fun_mul h1x
  have h : HasDerivWithinAt (fun y => 1 + y * (1 - y) * H y)
      ((1 * (1 - x) + x * -1) * H x + x * (1 - x) * D H x) (Icc 0 1) x :=
    (hv.fun_mul (M.dH x hx)).const_add 1
  refine h.congr_deriv ?_
  unfold b1
  ring

theorem hasDerivWithinAt_b1 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (b1 H) (b2 H x) (Icc 0 1) x := by
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc 0 1) x := hasDerivWithinAt_id x _
  have h1x : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) x := hid.const_sub 1
  have h12 : HasDerivWithinAt (fun y : ℝ => 1 - 2 * y) (-(2 * 1)) (Icc 0 1) x :=
    (hid.const_mul 2).const_sub 1
  have hv : HasDerivWithinAt (fun y : ℝ => y * (1 - y)) (1 * (1 - x) + x * -1) (Icc 0 1) x :=
    hid.fun_mul h1x
  have h : HasDerivWithinAt (fun y => (1 - 2 * y) * H y + y * (1 - y) * D H y)
      (-(2 * 1) * H x + (1 - 2 * x) * D H x
        + ((1 * (1 - x) + x * -1) * D H x + x * (1 - x) * D (D H) x)) (Icc 0 1) x :=
    (h12.fun_mul (M.dH x hx)).fun_add (hv.fun_mul (M.ddH x hx))
  refine h.congr_deriv ?_
  unfold b2
  ring

theorem hasDerivWithinAt_T {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (Tfun H) (T1 H x) (Icc 0 1) x := by
  have h1x : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) x :=
    (hasDerivWithinAt_id x _).const_sub 1
  have h : HasDerivWithinAt (fun y => -8 * bfun H y + (1 - y) * b1 H y + 7 * (1 - y) * H y)
      (-8 * b1 H x + (-1 * b1 H x + (1 - x) * b2 H x)
        + (7 * -1 * H x + 7 * (1 - x) * D H x)) (Icc 0 1) x :=
    (((M.hasDerivWithinAt_b hx).const_mul (-8)).fun_add
      (h1x.fun_mul (M.hasDerivWithinAt_b1 hx))).fun_add
      ((h1x.const_mul 7).fun_mul (M.dH x hx))
  refine h.congr_deriv ?_
  unfold T1
  ring

theorem hasDerivWithinAt_exp {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun y => Real.exp (-(a y)))
      (Real.exp (-(a x)) * (H x / bfun H x)) (Icc 0 1) x := by
  have h : HasDerivWithinAt (fun y => -(a y)) (-(-(H x) / bfun H x)) (Icc 0 1) x :=
    (M.da x hx).neg
  refine h.exp.congr_deriv ?_
  rw [neg_div, neg_neg]

theorem hasDerivWithinAt_f1 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (f1 a)
      (-Real.exp (-(a x)) + (1 - x) * (Real.exp (-(a x)) * (H x / bfun H x))) (Icc 0 1) x := by
  have h1x : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) x :=
    (hasDerivWithinAt_id x _).const_sub 1
  have h : HasDerivWithinAt (fun y => (1 - y) * Real.exp (-(a y)))
      (-1 * Real.exp (-(a x)) + (1 - x) * (Real.exp (-(a x)) * (H x / bfun H x)))
      (Icc 0 1) x := h1x.fun_mul (M.hasDerivWithinAt_exp hx)
  refine h.congr_deriv ?_
  ring

theorem hasDerivWithinAt_R {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (Rfun H a)
      (8 * (-1 / (1 - x)) + b1 H x / bfun H x - 7 * (-(H x) / bfun H x)) (Icc 0 1) x := by
  have hx' := Ico_subset_Icc_self hx
  have h1x : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) x :=
    (hasDerivWithinAt_id x _).const_sub 1
  have hl1 : HasDerivWithinAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) (Icc 0 1) x :=
    h1x.log (sub_pos.2 hx.2).ne'
  have hl2 : HasDerivWithinAt (fun y : ℝ => Real.log (bfun H y)) (b1 H x / bfun H x)
      (Icc 0 1) x := (M.hasDerivWithinAt_b hx').log (M.pos x hx').ne'
  have h : HasDerivWithinAt (fun y => 8 * Real.log (1 - y) + Real.log (bfun H y) - 7 * a y)
      (8 * (-1 / (1 - x)) + b1 H x / bfun H x - 7 * (-(H x) / bfun H x)) (Icc 0 1) x :=
    ((hl1.const_mul 8).fun_add hl2).fun_sub ((M.da x hx').const_mul 7)
  exact h

/-! ### Composition with the momentum coordinate -/

theorem mapsTo : MapsTo xq (Ici 0) (Icc (0 : ℝ) 1) :=
  fun q hq => Ico_subset_Icc_self (M.mem q hq)

theorem comp {g : ℝ → ℝ} {g' q : ℝ} (hq : 0 ≤ q) (hg : HasDerivWithinAt g g' (Icc 0 1) (xq q)) :
    HasDerivWithinAt (fun q => g (xq q)) (g' * f3 H a (xq q)) (Ici 0) q :=
  hg.comp q (M.dx q hq) M.mapsTo

theorem xq_zero : xq 0 = 0 := by
  have h := M.rel 0 le_rfl
  rw [zero_mul] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _)

theorem q_mul_f1 {q : ℝ} (hq : 0 ≤ q) : q * f1 a (xq q) = xq q := by
  have h := M.rel q hq
  have he : Real.exp (a (xq q)) ≠ 0 := Real.exp_ne_zero _
  unfold f1
  rw [Real.exp_neg, ← mul_assoc, mul_inv_eq_iff_eq_mul₀ he]
  exact h

theorem f1_add {q : ℝ} (hq : 0 ≤ q) : f1 a (xq q) + q * f2 H a (xq q) = f3 H a (xq q) := by
  have h := M.q_mul_f1 hq
  unfold f1 at h
  unfold f1 f2 f3 bfun vstar
  linear_combination (Real.exp (-(a (xq q))) * (1 - xq q)
    * (-(1 + xq q * (1 - xq q) * H (xq q)) + (1 - xq q) * H (xq q))) * h

theorem f1_pos {q : ℝ} (hq : 0 ≤ q) : 0 < f1 a (xq q) :=
  mul_pos (sub_pos.2 (M.mem q hq).2) (Real.exp_pos _)

theorem f3_pos {q : ℝ} (hq : 0 ≤ q) : 0 < f3 H a (xq q) :=
  mul_pos (mul_pos (pow_pos (sub_pos.2 (M.mem q hq).2) 2) (M.pos _ (M.mapsTo hq)))
    (Real.exp_pos _)

theorem hasDerivWithinAt_phi1 {q : ℝ} (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => f1 a (xq q)) (f2 H a (xq q)) (Ici 0) q :=
  (M.comp hq (M.hasDerivWithinAt_f1 (M.mapsTo hq))).congr_deriv
    (f1'_mul_f3 (M.pos _ (M.mapsTo hq)).ne')

theorem log_eq {q : ℝ} (hq : 0 ≤ q) :
    Real.log (f1 a (xq q) ^ 6 * (f1 a (xq q) + q * f2 H a (xq q))) = Rfun H a (xq q) := by
  rw [M.f1_add hq]
  have h1 : (1 - xq q) ≠ 0 := (sub_pos.2 (M.mem q hq).2).ne'
  have hb : bfun H (xq q) ≠ 0 := (M.pos _ (M.mapsTo hq)).ne'
  have hE : Real.exp (-(a (xq q))) ≠ 0 := Real.exp_ne_zero _
  unfold f1 f3 Rfun
  rw [Real.log_mul (pow_ne_zero 6 (mul_ne_zero h1 hE))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h1) hb) hE),
    Real.log_pow, Real.log_mul h1 hE, Real.log_mul (mul_ne_zero (pow_ne_zero 2 h1) hb) hE,
    Real.log_mul (pow_ne_zero 2 h1) hb, Real.log_pow, Real.log_exp]
  push_cast
  ring

theorem hasDerivWithinAt_rho {q : ℝ} (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => Real.log (f1 a (xq q) ^ 6 * (f1 a (xq q) + q * f2 H a (xq q))))
      (Tfun H (xq q) * f1 a (xq q)) (Ici 0) q := by
  have hx := M.mem q hq
  have h := (M.comp hq (M.hasDerivWithinAt_R hx)).congr_deriv
    (R'_mul_f3 (sub_pos.2 hx.2).ne' (M.pos _ (M.mapsTo hq)).ne')
  exact h.congr (fun q' hq' => M.log_eq hq') (M.log_eq hq)

theorem hasDerivWithinAt_rho1 {q : ℝ} (hq : 0 ≤ q) :
    HasDerivWithinAt (fun q => Tfun H (xq q) * f1 a (xq q))
      (T1 H (xq q) * f1 a (xq q) * f3 H a (xq q) + Tfun H (xq q) * f2 H a (xq q))
      (Ici 0) q := by
  have hx := M.mapsTo hq
  have hprod : HasDerivWithinAt (fun y => Tfun H y * f1 a y)
      (T1 H (xq q) * f1 a (xq q) + Tfun H (xq q)
        * (-Real.exp (-(a (xq q)))
          + (1 - xq q) * (Real.exp (-(a (xq q))) * (H (xq q) / bfun H (xq q)))))
      (Icc 0 1) (xq q) := (M.hasDerivWithinAt_T hx).fun_mul (M.hasDerivWithinAt_f1 hx)
  refine (M.comp hq hprod).congr_deriv ?_
  have e := f1'_mul_f3 (H := H) (a := a) (x := xq q) (M.pos _ hx).ne'
  linear_combination (Tfun H (xq q)) * e

/-! ### The metric on the chart -/

theorem eventually_dφ (Z : Aff) :
    ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (f1 a (xq q)) (Ici 0) q :=
  eventually_mem_nhdsWithin.mono fun q hq => M.dφ q hq

/-- The metric matrix: `φ′ 1 + φ″ (conj Z_j Z_k)`. -/
theorem gmat_eq (Z : Aff) :
    gmat (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = (f1 a (xq (‖Z‖ ^ 2)) : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        + (f2 H a (xq (‖Z‖ ^ 2)) : ℂ)
          • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k) :=
  gmat_radial (φ := φ) (φ1 := fun q => f1 a (xq q)) (φ2 := f2 H a (xq (‖Z‖ ^ 2))) (Z := Z)
    (M.eventually_dφ Z) (M.hasDerivWithinAt_phi1 (sq_nonneg _))

/-- `det (u_{j k̄}) = (φ′)⁶ (φ′ + q φ″)`. -/
theorem detg_eq (Z : Aff) :
    detg (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = f1 a (xq (‖Z‖ ^ 2)) ^ 6 * f3 H a (xq (‖Z‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have h : detg (fun W : Aff => φ (‖W‖ ^ 2)) Z = f1 a (xq (‖Z‖ ^ 2)) ^ 6
      * (f1 a (xq (‖Z‖ ^ 2)) + ‖Z‖ ^ 2 * f2 H a (xq (‖Z‖ ^ 2))) :=
    detg_radial (φ := φ) (φ1 := fun q => f1 a (xq q)) (φ2 := f2 H a (xq (‖Z‖ ^ 2))) (Z := Z)
      (M.eventually_dφ Z) (M.hasDerivWithinAt_phi1 hq) (M.f1_pos hq).ne'
  rw [h, M.f1_add hq]

theorem detg_pos (Z : Aff) : 0 < detg (fun W : Aff => φ (‖W‖ ^ 2)) Z := by
  rw [M.detg_eq]
  exact mul_pos (pow_pos (M.f1_pos (sq_nonneg _)) 6) (M.f3_pos (sq_nonneg _))

/-- The metric of the chart is positive. -/
theorem levi_pos (Z : Aff) {c : Aff} (hc : c ≠ 0) :
    0 < (levi (fun W : Aff => φ (‖W‖ ^ 2)) Z c c).re := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  refine levi_radial_pos (φ := φ) (φ1 := fun q => f1 a (xq q))
    (φ2 := f2 H a (xq (‖Z‖ ^ 2))) (M.eventually_dφ Z) (M.hasDerivWithinAt_phi1 hq)
    (M.f1_pos hq) ?_ hc
  show 0 < f1 a (xq (‖Z‖ ^ 2)) + ‖Z‖ ^ 2 * f2 H a (xq (‖Z‖ ^ 2))
  rw [M.f1_add hq]
  exact M.f3_pos hq

/-- **The scalar curvature in the momentum coordinate**: `S = 56 - K(H)`. -/
theorem scal_eq (Z : Aff) :
    scal (fun W : Aff => φ (‖W‖ ^ 2)) Z = 56 - Kop H (xq (‖Z‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have hs : scal (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = -(6 * (Tfun H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2))) / f1 a (xq (‖Z‖ ^ 2))
        + (Tfun H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2))
            + ‖Z‖ ^ 2 * (T1 H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2)) * f3 H a (xq (‖Z‖ ^ 2))
              + Tfun H (xq (‖Z‖ ^ 2)) * f2 H a (xq (‖Z‖ ^ 2))))
          / (f1 a (xq (‖Z‖ ^ 2)) + ‖Z‖ ^ 2 * f2 H a (xq (‖Z‖ ^ 2)))) :=
    scal_radial (φ := φ) (φ1 := fun q => f1 a (xq q)) (φ2 := fun q => f2 H a (xq q))
      (ρ1 := fun q => Tfun H (xq q) * f1 a (xq q)) isOpen_univ (mem_univ _)
      (fun q _ hq => M.dφ q hq) (fun q _ hq => M.hasDerivWithinAt_phi1 hq)
      (fun q _ hq => M.f1_pos hq)
      (fun q _ hq => by
        show 0 < f1 a (xq q) + q * f2 H a (xq q)
        rw [M.f1_add hq]
        exact M.f3_pos hq)
      (fun q _ hq => M.hasDerivWithinAt_rho hq) (M.hasDerivWithinAt_rho1 hq)
  rw [hs]
  have hden := M.f1_add hq
  have hqf := M.q_mul_f1 hq
  have hf1 : f1 a (xq (‖Z‖ ^ 2)) ≠ 0 := (M.f1_pos hq).ne'
  have hf3 : f3 H a (xq (‖Z‖ ^ 2)) ≠ 0 := (M.f3_pos hq).ne'
  rw [hden]
  have e1 : 6 * (Tfun H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2))) / f1 a (xq (‖Z‖ ^ 2))
      = 6 * Tfun H (xq (‖Z‖ ^ 2)) := by
    rw [← mul_assoc, mul_div_assoc, div_self hf1, mul_one]
  have e2 : (Tfun H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2))
      + ‖Z‖ ^ 2 * (T1 H (xq (‖Z‖ ^ 2)) * f1 a (xq (‖Z‖ ^ 2)) * f3 H a (xq (‖Z‖ ^ 2))
        + Tfun H (xq (‖Z‖ ^ 2)) * f2 H a (xq (‖Z‖ ^ 2)))) / f3 H a (xq (‖Z‖ ^ 2))
      = Tfun H (xq (‖Z‖ ^ 2)) + xq (‖Z‖ ^ 2) * T1 H (xq (‖Z‖ ^ 2)) := by
    rw [div_eq_iff hf3]
    linear_combination (Tfun H (xq (‖Z‖ ^ 2))) * hden
      + (T1 H (xq (‖Z‖ ^ 2)) * f3 H a (xq (‖Z‖ ^ 2))) * hqf
  rw [e1, e2]
  have e3 := seven_T H (xq (‖Z‖ ^ 2))
  linarith

/-- At the point orbit, `S = 56 (1 - H(0))`: equation (2.28) of the manuscript. -/
theorem scal_zero : scal (fun W : Aff => φ (‖W‖ ^ 2)) 0 = 56 * (1 - H 0) := by
  rw [M.scal_eq, norm_zero, zero_pow two_ne_zero, M.xq_zero, Kop_zero]
  ring

end MomentumData

end Calabi.Geometry
