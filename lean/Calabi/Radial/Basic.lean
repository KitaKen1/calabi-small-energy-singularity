import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The momentum coordinate

`U(7)`-invariant Kähler metrics on `CP⁷` in the Fubini–Study class are
described by a function `H` of the momentum coordinate `x ∈ [0, 1]`
(Proposition 2.1 of the manuscript, with `n = 7`):

* `v∗(x) = x (1 - x)` is the momentum profile of the Fubini–Study metric and
  `v = v∗ (1 + v∗ H)` that of the metric of `H`, positive when `1 + v∗ H > 0`;
* `K(H) = w⁻¹ (w v∗² H)″` with `w = x⁶`, and the scalar curvature is
  `56 - K(H)`;
* `A H = K(H)″`, and the Calabi flow is `H_t + (1 + v∗ H)² A H = 0`.

`Kop` is `K` with the derivatives expanded as in (7.1) of the manuscript, so
that it is defined on `[0, 1]` including the endpoints; `Kop_eq_div` identifies
it with the divergence form in the interior. Derivatives are taken within
`[0, 1]`.
-/

open Set
open scoped ContDiff

namespace Calabi.Radial

/-- The momentum profile of the Fubini–Study metric. -/
def vstar (x : ℝ) : ℝ := x * (1 - x)

/-- The derivative of a function on the closed interval `[0, 1]`. -/
noncomputable def D (H : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin H (Icc 0 1) x

/-- `K(H) = x⁻⁶ (x⁸ (1 - x)² H)″`, expanded. The scalar curvature of the metric
of `H` is `56 - K(H)`. -/
noncomputable def Kop (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ 2 * (1 - x) ^ 2 * D (D H) x + 4 * x * (1 - x) * (4 - 5 * x) * D H x
    + (56 - 144 * x + 90 * x ^ 2) * H x

/-- `A H = K(H)″`. -/
noncomputable def Aop (H : ℝ → ℝ) (x : ℝ) : ℝ := D (D (Kop H)) x

/-- At the point orbit `x = 0`, `K(H) = 56 H`. -/
theorem Kop_zero (H : ℝ → ℝ) : Kop H 0 = 56 * H 0 := by
  simp [Kop]

/-- `H` is a smooth solution on `(-T, 0) × [0, 1]` of the Calabi flow in the
momentum coordinate, equation (2.5) of the manuscript. -/
structure IsRadialFlow (T : ℝ) (H : ℝ → ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2) (Ioo (-T) 0 ×ˢ Icc 0 1)
  eqn : ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
    deriv (fun τ => H τ x) t + (1 + vstar x * H t x) ^ 2 * Aop (H t) x = 0

/-! ### Derivatives within `[0, 1]` -/

theorem D_eq_deriv {H : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : DifferentiableAt ℝ H x) :
    D H x = deriv H x :=
  h.derivWithin (uniqueDiffOn_Icc_zero_one x hx)

/-- For a function that is smooth on an open set containing `[0, 1]`, the
derivatives within `[0, 1]` are the ordinary derivatives. -/
theorem D_D_eq {H : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ⊆ U)
    (hH : ContDiffOn ℝ ∞ H U) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    D H x = deriv H x ∧ D (D H) x = deriv (deriv H) x := by
  obtain ⟨hd, hd'⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hU).1 hH
  have hd2 := ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hd').1
  have e1 : ∀ y ∈ Icc (0 : ℝ) 1, D H y = deriv H y := fun y hy =>
    D_eq_deriv hy ((hd y (hsub hy)).differentiableAt (hU.mem_nhds (hsub hy)))
  refine ⟨e1 x hx, ?_⟩
  have e2 : D (D H) x = derivWithin (deriv H) (Icc 0 1) x := derivWithin_congr e1 (e1 x hx)
  rw [e2]
  exact ((hd2 x (hsub hx)).differentiableAt (hU.mem_nhds (hsub hx))).derivWithin
    (uniqueDiffOn_Icc_zero_one x hx)

theorem contDiffOn_D {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Icc 0 1)) :
    ContDiffOn ℝ ∞ (D H) (Icc 0 1) :=
  hH.derivWithin uniqueDiffOn_Icc_zero_one (by simp)

/-- `K(H)` is continuous on `[0, 1]` for `H ∈ C^∞[0, 1]`. -/
theorem continuousOn_Kop {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Icc 0 1)) :
    ContinuousOn (Kop H) (Icc 0 1) := by
  have h1 := (contDiffOn_D hH).continuousOn
  have h2 := (contDiffOn_D (contDiffOn_D hH)).continuousOn
  have hx : ContinuousOn (fun x : ℝ => x) (Icc 0 1) := continuousOn_id
  have h1x : ContinuousOn (fun x : ℝ => 1 - x) (Icc 0 1) := continuousOn_const.sub hx
  exact ((((hx.pow 2).mul (h1x.pow 2)).mul h2).add
    ((((continuousOn_const.mul hx).mul h1x).mul
      (continuousOn_const.sub (continuousOn_const.mul hx))).mul h1)).add
    (((continuousOn_const.sub (continuousOn_const.mul hx)).add
      (continuousOn_const.mul (hx.pow 2))).mul hH.continuousOn)

/-! ### The divergence form -/

/-- In the interior, `K(H) = x⁻⁶ (x⁸ (1 - x)² H)″`: equation (2.3) of the
manuscript with `w = x⁶` and `v∗ = x (1 - x)`. -/
theorem Kop_eq_div {H : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ⊆ U)
    (hH : ContDiffOn ℝ ∞ H U) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Kop H x = (x ^ 6)⁻¹ * deriv (deriv fun x => x ^ 8 * (1 - x) ^ 2 * H x) x := by
  obtain ⟨hd, hd'⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hU).1 hH
  have hd2 := ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hd').1
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  obtain ⟨e1, e2⟩ := D_D_eq hU hsub hH hxI
  have dH : ∀ y ∈ U, HasDerivAt H (deriv H y) y := fun y hy =>
    ((hd y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have dH1 : ∀ y ∈ U, HasDerivAt (deriv H) (deriv (deriv H) y) y := fun y hy =>
    ((hd2 y hy).differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have p0 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 8 * (1 - y) ^ 2)
      (8 * y ^ 7 * (1 - y) ^ 2 - 2 * y ^ 8 * (1 - y)) y := by
    intro y
    have a : HasDerivAt (fun y : ℝ => y ^ 8) (8 * y ^ 7) y :=
      (hasDerivAt_pow 8 y).congr_deriv (by norm_num)
    have b : HasDerivAt (fun y : ℝ => (1 - y) ^ 2) (-(2 * (1 - y))) y := by
      have h := ((hasDerivAt_id' y).const_sub 1).fun_pow 2
      refine h.congr_deriv ?_
      norm_num
    refine (a.fun_mul b).congr_deriv ?_
    ring
  have p1 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 8 * y ^ 7 * (1 - y) ^ 2 - 2 * y ^ 8 * (1 - y))
      (56 * y ^ 6 * (1 - y) ^ 2 - 32 * y ^ 7 * (1 - y) + 2 * y ^ 8) y := by
    intro y
    have a7 : HasDerivAt (fun y : ℝ => 8 * y ^ 7) (56 * y ^ 6) y :=
      ((hasDerivAt_pow 7 y).const_mul 8).congr_deriv (by norm_num; ring)
    have a8 : HasDerivAt (fun y : ℝ => 2 * y ^ 8) (16 * y ^ 7) y :=
      ((hasDerivAt_pow 8 y).const_mul 2).congr_deriv (by norm_num; ring)
    have b : HasDerivAt (fun y : ℝ => (1 - y) ^ 2) (-(2 * (1 - y))) y := by
      have h := ((hasDerivAt_id' y).const_sub 1).fun_pow 2
      refine h.congr_deriv ?_
      norm_num
    have b1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := (hasDerivAt_id' y).const_sub 1
    refine ((a7.fun_mul b).fun_sub (a8.fun_mul b1)).congr_deriv ?_
    ring
  have f1 : ∀ y ∈ U, HasDerivAt (fun y => y ^ 8 * (1 - y) ^ 2 * H y)
      ((8 * y ^ 7 * (1 - y) ^ 2 - 2 * y ^ 8 * (1 - y)) * H y
        + y ^ 8 * (1 - y) ^ 2 * deriv H y) y := fun y hy => (p0 y).fun_mul (dH y hy)
  have f2 : HasDerivAt (fun y => (8 * y ^ 7 * (1 - y) ^ 2 - 2 * y ^ 8 * (1 - y)) * H y
      + y ^ 8 * (1 - y) ^ 2 * deriv H y)
      ((56 * x ^ 6 * (1 - x) ^ 2 - 32 * x ^ 7 * (1 - x) + 2 * x ^ 8) * H x
        + (8 * x ^ 7 * (1 - x) ^ 2 - 2 * x ^ 8 * (1 - x)) * deriv H x
        + ((8 * x ^ 7 * (1 - x) ^ 2 - 2 * x ^ 8 * (1 - x)) * deriv H x
          + x ^ 8 * (1 - x) ^ 2 * deriv (deriv H) x)) x :=
    ((p1 x).fun_mul (dH x (hsub hxI))).fun_add ((p0 x).fun_mul (dH1 x (hsub hxI)))
  have heq : deriv (fun y => y ^ 8 * (1 - y) ^ 2 * H y) =ᶠ[nhds x] fun y =>
      (8 * y ^ 7 * (1 - y) ^ 2 - 2 * y ^ 8 * (1 - y)) * H y
        + y ^ 8 * (1 - y) ^ 2 * deriv H y := by
    filter_upwards [hU.mem_nhds (hsub hxI)] with y hy using (f1 y hy).deriv
  rw [heq.deriv_eq, f2.deriv]
  unfold Kop
  rw [e1, e2]
  have hx0 : x ≠ 0 := hx.1.ne'
  field_simp
  ring

end Calabi.Radial
