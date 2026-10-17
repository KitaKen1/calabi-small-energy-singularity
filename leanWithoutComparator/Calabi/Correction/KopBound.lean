import Calabi.Correction.ChartJets

/-!
# The curvature operator `K` on a function given in the two charts

For the scalar curvature the main theorem needs a bound of
`K(H) - K(F_λ) = K(V)`, where `K` is the second-order operator of
`Radial/Basic.lean` and `V` is given by its two chart functions,

  `V(x) = u⁰(√x e⁰) + u¹(√(1 - x) e¹)`.

`kop_diff_formula` computes `K(f + V) - K(f)` at an interior point in terms of
the Euler operator `E = z · ∇` of the chart functions:

  `(1 - x)² (E² u⁰ - 2 E u⁰)/4 + 2 (1 - x)(4 - 5x) E u⁰
    + x² (E² u¹ - 2 E u¹)/4 - 2 x (4 - 5x) E u¹ + (56 - 144 x + 90 x²) (u⁰ + u¹)`.

This is the statement "the coefficients of orders two, one and zero of `K` in
the radial coordinates have sizes `O(r²)`, `O(r)`, `O(1)`" of Section 7.1 of
the manuscript, at both ends. `abs_eulerE_le` and `abs_eulerE_eulerE_le` bound
the Euler operators by the jets.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open Calabi.Radial Calabi.Chart

section Ray

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivative along a ray in the coordinate `y = |z|²`. -/
theorem hasDerivAt_ray {v : V → ℝ} (hv : Differentiable ℝ v) (e : V) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => v (Real.sqrt y • e)) (eulerE v (Real.sqrt y • e) / (2 * y)) y := by
  have hr : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt y • e) ((1 / (2 * Real.sqrt y)) • e) y :=
    (Real.hasDerivAt_sqrt hy.ne').smul_const e
  have h1 := (hv (Real.sqrt y • e)).hasFDerivAt.comp_hasDerivAt y hs
  refine h1.congr_deriv ?_
  have e2 : (1 / (2 * Real.sqrt y)) • e = (1 / (2 * y)) • (Real.sqrt y • e) := by
    rw [smul_smul]
    congr 1
    have h2 := Real.mul_self_sqrt hy.le
    field_simp
    nlinarith
  rw [e2, map_smul, smul_eq_mul]
  unfold eulerE
  ring

/-- The second derivative along a ray. -/
theorem hasDerivAt_ray_two {u : V → ℝ} (hu : ContDiff ℝ 2 u) (e : V) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => eulerE u (Real.sqrt y • e) / (2 * y))
      (eulerE (eulerE u) (Real.sqrt y • e) / (4 * y ^ 2)
        - eulerE u (Real.sqrt y • e) / (2 * y ^ 2)) y := by
  have h1c : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hE : Differentiable ℝ (eulerE u) :=
    (h1c.differentiable one_ne_zero).clm_apply differentiable_id
  have h1 := hasDerivAt_ray hE e hy
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
    simpa using (hasDerivAt_id y).const_mul 2
  have h3 := h1.div h2 (by positivity)
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem abs_eulerE_le (u : V → ℝ) (z : V) :
    |eulerE u z| ≤ ‖fderiv ℝ u z‖ * ‖z‖ := by
  unfold eulerE
  rw [← Real.norm_eq_abs]
  exact ContinuousLinearMap.le_opNorm _ _

theorem abs_eulerE_eulerE_le {u : V → ℝ} (hu : ContDiff ℝ 2 u) (z : V) :
    |eulerE (eulerE u) z| ≤ ‖iteratedFDeriv ℝ 2 u z‖ * ‖z‖ ^ 2 + ‖fderiv ℝ u z‖ * ‖z‖ := by
  rw [eulerE_eulerE hu z]
  have h1 : ‖iteratedFDeriv ℝ 2 u z ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 u z‖ * ‖z‖ ^ 2 := by
    have h := (iteratedFDeriv ℝ 2 u z).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two, sq] using h
  rw [Real.norm_eq_abs] at h1
  exact (abs_add_le _ _).trans (add_le_add h1 (abs_eulerE_le u z))

end Ray

theorem Kop_one (H : ℝ → ℝ) : Kop H 1 = 2 * H 1 := by
  unfold Kop
  ring

/-- The derivatives within `[0, 1]` of a function with given derivatives in
the interior. -/
theorem D_D_of_hasDerivAt {f a b : ℝ → ℝ}
    (ha : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (a y) (Icc 0 1) y)
    (hb : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt a (b y) (Icc 0 1) y) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : D f x = a x ∧ D (D f) x = b x := by
  have hI : ∀ y ∈ Ioo (0 : ℝ) 1, y ∈ Icc (0 : ℝ) 1 := fun y hy => ⟨hy.1.le, hy.2.le⟩
  have e1 : ∀ y ∈ Ioo (0 : ℝ) 1, D f y = a y := fun y hy =>
    (ha y hy).derivWithin (uniqueDiffOn_Icc_zero_one y (hI y hy))
  refine ⟨e1 x hx, ?_⟩
  have hev : D f =ᶠ[𝓝[Icc (0 : ℝ) 1] x] a := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)] with y hy
    exact e1 y hy
  show derivWithin (D f) (Icc 0 1) x = b x
  rw [hev.derivWithin_eq (e1 x hx)]
  exact (hb x hx).derivWithin (uniqueDiffOn_Icc_zero_one x (hI x hx))

set_option maxHeartbeats 1600000 in
/-- **The operator `K` on a function given in the two charts.** -/
theorem kop_diff_formula {V₀ V₁ : Type} [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
    [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] {u0 : V₀ → ℝ} {u1 : V₁ → ℝ}
    (h0 : ContDiff ℝ 2 u0) (h1 : ContDiff ℝ 2 u1) (e0 : V₀) (e1 : V₁) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Kop (fun y => f y + (u0 (Real.sqrt y • e0) + u1 (Real.sqrt (1 - y) • e1))) x - Kop f x
      = (1 - x) ^ 2 * (eulerE (eulerE u0) (Real.sqrt x • e0) / 4
            - eulerE u0 (Real.sqrt x • e0) / 2)
        + 2 * (1 - x) * (4 - 5 * x) * eulerE u0 (Real.sqrt x • e0)
        + x ^ 2 * (eulerE (eulerE u1) (Real.sqrt (1 - x) • e1) / 4
            - eulerE u1 (Real.sqrt (1 - x) • e1) / 2)
        - 2 * x * (4 - 5 * x) * eulerE u1 (Real.sqrt (1 - x) • e1)
        + (56 - 144 * x + 90 * x ^ 2)
          * (u0 (Real.sqrt x • e0) + u1 (Real.sqrt (1 - x) • e1)) := by
  have hI : ∀ y ∈ Ioo (0 : ℝ) 1, y ∈ Icc (0 : ℝ) 1 := fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hd0 : Differentiable ℝ u0 := h0.differentiable (by norm_num)
  have hd1 : Differentiable ℝ u1 := h1.differentiable (by norm_num)
  -- the chart at `x = 1`, reflected
  have hr1 : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => u1 (Real.sqrt (1 - y) • e1))
      (-(eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y)))) y := by
    intro y hy
    have h2 := hasDerivAt_ray hd1 e1 (y := 1 - y) (by linarith [hy.2])
    have h3 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h4 := h2.comp y h3
    refine h4.congr_deriv ?_
    ring
  have hr2 : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => -(eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y))))
      (eulerE (eulerE u1) (Real.sqrt (1 - y) • e1) / (4 * (1 - y) ^ 2)
        - eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y) ^ 2)) y := by
    intro y hy
    have h2 := hasDerivAt_ray_two h1 e1 (y := 1 - y) (by linarith [hy.2])
    have h3 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h4 := (h2.comp y h3).neg
    refine h4.congr_deriv ?_
    ring
  -- the first and second derivatives of the sum
  have hA : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt
      (fun y => f y + (u0 (Real.sqrt y • e0) + u1 (Real.sqrt (1 - y) • e1)))
      (D f y + (eulerE u0 (Real.sqrt y • e0) / (2 * y)
        + -(eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y))))) (Icc 0 1) y := fun y hy =>
    (hasDerivWithinAt_D hf (hI y hy)).add
      (((hasDerivAt_ray hd0 e0 hy.1).add (hr1 y hy)).hasDerivWithinAt)
  have hB : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt
      (fun y => D f y + (eulerE u0 (Real.sqrt y • e0) / (2 * y)
        + -(eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y)))))
      (D (D f) y + ((eulerE (eulerE u0) (Real.sqrt y • e0) / (4 * y ^ 2)
          - eulerE u0 (Real.sqrt y • e0) / (2 * y ^ 2))
        + (eulerE (eulerE u1) (Real.sqrt (1 - y) • e1) / (4 * (1 - y) ^ 2)
          - eulerE u1 (Real.sqrt (1 - y) • e1) / (2 * (1 - y) ^ 2)))) (Icc 0 1) y := fun y hy =>
    (hasDerivWithinAt_D (contDiffOn_D hf) (hI y hy)).add
      (((hasDerivAt_ray_two h0 e0 hy.1).add (hr2 y hy)).hasDerivWithinAt)
  obtain ⟨e1', e2'⟩ := D_D_of_hasDerivAt hA hB hx
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold Kop
  rw [e1', e2']
  field_simp
  ring

end Calabi.Weighted
