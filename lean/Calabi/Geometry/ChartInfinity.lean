import Calabi.Geometry.RadialScalar

/-!
# Positivity on the charts that meet the divisor at infinity

On the chart `j ≠ 0` of `CP⁷` the Fubini–Study momentum is
`ξ = 1 - η`, `η = |Z₀|² / (1 + ‖Z‖²)`, and a potential of the class has the
form

  `u(Z) = log (1 + ‖Z‖²) + Ψ(1 - η(Z))`

with `Ψ` smooth on the closed interval `[0, 1]`; the divisor at infinity is
`{Z₀ = 0} = {ξ = 1}`. With `FS` the Fubini–Study form and
`N = |a₀ - Z₀ ⟨Z, a⟩ / s|² / s`, `s = 1 + ‖Z‖²`, the Levi form is

  `u_{j k̄} a_j conj(a_k) = (1 + η Ψ′) FS + (η Ψ″ - Ψ′) N`,   `0 ≤ N ≤ ξ FS`,

so that it is bounded below by `min (A, B) FS` with

  `A = 1 + (1 - ξ) Ψ′`,   `B = 1 + (1 - 2 ξ) Ψ′ + ξ (1 - ξ) Ψ″`.

In the momentum coordinate `A = x / ξ` and `B = dx/dξ`.
`levi_chart_infinity_pos` is the resulting positivity statement; the
derivatives of `Ψ` are taken within `[0, 1]`, which includes the divisor.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

/-! ### Hessians -/

theorem hess_eq (u : Aff → ℝ) (Z a b : Aff) : hess u Z a b = fderiv ℝ (fderiv ℝ u) Z a b := by
  unfold hess
  rw [iteratedFDeriv_two_apply]
  rfl

theorem levi_re (u : Aff → ℝ) (Z a : Aff) :
    (levi u Z a a).re = (hess u Z a a + hess u Z (Complex.I • a) (Complex.I • a)) / 4 := by
  unfold levi
  simp

theorem eventually_differentiableAt {f : Aff → ℝ} {Z : Aff} (hf : ContDiffAt ℝ 2 f Z) :
    ∀ᶠ W in 𝓝 Z, DifferentiableAt ℝ f W := by
  filter_upwards [hf.eventually (by simp)] with W hW using hW.differentiableAt two_ne_zero

theorem hasFDerivAt_fderiv {f : Aff → ℝ} {Z : Aff} (hf : ContDiffAt ℝ 2 f Z) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) Z) Z :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

/-- The Hessian of `f + Ψ ∘ ξ`, where the derivatives of `Ψ` are taken within a
set containing the values of `ξ`. -/
theorem hess_add_comp {f ξ : Aff → ℝ} {Ψ Ψ1 : ℝ → ℝ} {Ψ2 : ℝ} {S : Set ℝ} {Z : Aff}
    (hf : ContDiffAt ℝ 2 f Z) (hξ : ContDiffAt ℝ 2 ξ Z) (hmaps : ∀ W, ξ W ∈ S)
    (h1 : ∀ᶠ y in 𝓝[S] (ξ Z), HasDerivWithinAt Ψ (Ψ1 y) S y)
    (h2 : HasDerivWithinAt Ψ1 Ψ2 S (ξ Z)) (a b : Aff) :
    hess (fun W => f W + Ψ (ξ W)) Z a b
      = hess f Z a b + Ψ1 (ξ Z) * hess ξ Z a b
        + Ψ2 * (fderiv ℝ ξ Z a * fderiv ℝ ξ Z b) := by
  rw [hess_eq, hess_eq, hess_eq]
  have hξd := eventually_differentiableAt hξ
  have hfd' := eventually_differentiableAt hf
  have htend : Tendsto ξ (𝓝 Z) (𝓝[S] (ξ Z)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hξ.continuousAt
      (Eventually.of_forall hmaps)
  have hcomp : ∀ {g : ℝ → ℝ} {g' : ℝ} {W : Aff}, HasDerivWithinAt g g' S (ξ W) →
      DifferentiableAt ℝ ξ W → HasFDerivAt (fun W => g (ξ W)) (g' • fderiv ℝ ξ W) W := by
    intro g g' W hg hW
    exact (hg.comp_hasFDerivWithinAt W hW.hasFDerivAt.hasFDerivWithinAt
      (fun V _ => hmaps V)).hasFDerivAt univ_mem
  have hfd : fderiv ℝ (fun W => f W + Ψ (ξ W))
      =ᶠ[𝓝 Z] fun W => fderiv ℝ f W + Ψ1 (ξ W) • fderiv ℝ ξ W := by
    filter_upwards [htend.eventually h1, hξd, hfd'] with W hW hWd hWf
    exact (hWf.hasFDerivAt.add (hcomp hW hWd)).fderiv
  have hc : HasFDerivAt (fun W => Ψ1 (ξ W)) (Ψ2 • fderiv ℝ ξ Z) Z :=
    hcomp h2 hξd.self_of_nhds
  have hsum : HasFDerivAt (fun W => fderiv ℝ f W + Ψ1 (ξ W) • fderiv ℝ ξ W)
      (fderiv ℝ (fderiv ℝ f) Z + (Ψ1 (ξ Z) • fderiv ℝ (fderiv ℝ ξ) Z
        + (Ψ2 • fderiv ℝ ξ Z).smulRight (fderiv ℝ ξ Z))) Z :=
    (hasFDerivAt_fderiv hf).add (hc.smul (hasFDerivAt_fderiv hξ))
  rw [hfd.fderiv_eq, hsum.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- The Hessian of a product. -/
theorem hess_mul {f g : Aff → ℝ} {Z : Aff} (hf : ContDiffAt ℝ 2 f Z) (hg : ContDiffAt ℝ 2 g Z)
    (a b : Aff) :
    hess (fun W => f W * g W) Z a b
      = f Z * hess g Z a b + g Z * hess f Z a b
        + fderiv ℝ f Z a * fderiv ℝ g Z b + fderiv ℝ f Z b * fderiv ℝ g Z a := by
  rw [hess_eq, hess_eq, hess_eq]
  have hfd' := eventually_differentiableAt hf
  have hgd' := eventually_differentiableAt hg
  have hfd : fderiv ℝ (fun W => f W * g W)
      =ᶠ[𝓝 Z] fun W => f W • fderiv ℝ g W + g W • fderiv ℝ f W := by
    filter_upwards [hfd', hgd'] with W hWf hWg
    exact (hWf.hasFDerivAt.mul hWg.hasFDerivAt).fderiv
  have hsum : HasFDerivAt (fun W => f W • fderiv ℝ g W + g W • fderiv ℝ f W)
      ((f Z • fderiv ℝ (fderiv ℝ g) Z + (fderiv ℝ f Z).smulRight (fderiv ℝ g Z))
        + (g Z • fderiv ℝ (fderiv ℝ f) Z + (fderiv ℝ g Z).smulRight (fderiv ℝ f Z))) Z :=
    (hfd'.self_of_nhds.hasFDerivAt.smul (hasFDerivAt_fderiv hg)).add
      (hgd'.self_of_nhds.hasFDerivAt.smul (hasFDerivAt_fderiv hf))
  rw [hfd.fderiv_eq, hsum.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem fderiv_mul_apply {f g : Aff → ℝ} {Z : Aff} (hf : ContDiffAt ℝ 2 f Z)
    (hg : ContDiffAt ℝ 2 g Z) (a : Aff) :
    fderiv ℝ (fun W => f W * g W) Z a = f Z * fderiv ℝ g Z a + g Z * fderiv ℝ f Z a := by
  have h : fderiv ℝ (fun W => f W * g W) Z = f Z • fderiv ℝ g Z + g Z • fderiv ℝ f Z :=
    ((hf.differentiableAt two_ne_zero).hasFDerivAt.mul
      (hg.differentiableAt two_ne_zero).hasFDerivAt).fderiv
  rw [h]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-! ### The functions `|Z₀|²` and `(1 + ‖Z‖²)⁻¹` -/

/-- `Z ↦ Re Z₀`. -/
noncomputable def reL : Aff →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (0 : Fin 7) : Aff →L[ℂ] ℂ).restrictScalars ℝ)

/-- `Z ↦ Im Z₀`. -/
noncomputable def imL : Aff →L[ℝ] ℝ :=
  Complex.imCLM.comp ((EuclideanSpace.proj (0 : Fin 7) : Aff →L[ℂ] ℂ).restrictScalars ℝ)

theorem reL_apply (a : Aff) : reL a = (a 0).re := rfl

theorem imL_apply (a : Aff) : imL a = (a 0).im := rfl

/-- `|Z₀|²`. -/
noncomputable def N0 (W : Aff) : ℝ := reL W * reL W + imL W * imL W

/-- `(1 + ‖Z‖²)⁻¹`. -/
noncomputable def Rinv (W : Aff) : ℝ := (1 + ‖W‖ ^ 2)⁻¹

theorem N0_eq (W : Aff) : N0 W = ‖W 0‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rfl

theorem contDiff_N0 : ContDiff ℝ ∞ N0 :=
  (reL.contDiff.mul reL.contDiff).add (imL.contDiff.mul imL.contDiff)

theorem hasFDerivAt_N0 (W : Aff) :
    HasFDerivAt N0 ((2 * reL W) • reL + (2 * imL W) • imL) W := by
  have h := ((reL.hasFDerivAt (x := W)).mul (reL.hasFDerivAt (x := W))).add
    ((imL.hasFDerivAt (x := W)).mul (imL.hasFDerivAt (x := W)))
  refine h.congr_fderiv ?_
  ext a
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem fderiv_N0 (Z a : Aff) : fderiv ℝ N0 Z a = 2 * reL Z * reL a + 2 * imL Z * imL a := by
  rw [(hasFDerivAt_N0 Z).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem hess_N0 (Z a b : Aff) : hess N0 Z a b = 2 * reL a * reL b + 2 * imL a * imL b := by
  rw [hess_eq]
  have h1 : fderiv ℝ N0 = fun W => (2 * reL W) • reL + (2 * imL W) • imL :=
    funext fun W => (hasFDerivAt_N0 W).fderiv
  have h2 : HasFDerivAt (fun W => (2 * reL W) • reL + (2 * imL W) • imL)
      (((2 : ℝ) • reL).smulRight reL + ((2 : ℝ) • imL).smulRight imL) Z :=
    (((reL.hasFDerivAt (x := Z)).const_smul (2 : ℝ)).smul_const reL).add
      (((imL.hasFDerivAt (x := Z)).const_smul (2 : ℝ)).smul_const imL)
  rw [h1, h2.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem contDiff_Rinv : ContDiff ℝ ∞ Rinv :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).inv fun W => by positivity

theorem Rinv_data (Z : Aff) :
    (∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2),
        HasDerivWithinAt (fun q : ℝ => (1 + q)⁻¹) (-1 / (1 + q) ^ 2) (Ici 0) q) ∧
      HasDerivWithinAt (fun q : ℝ => -1 / (1 + q) ^ 2) (2 / (1 + ‖Z‖ ^ 2) ^ 3) (Ici 0)
        (‖Z‖ ^ 2) := by
  have hpos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  constructor
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : (1 + q) ≠ 0 := by linarith [mem_Ici.1 hq]
    exact (((hasDerivAt_id' q).const_add 1).fun_inv hq').hasDerivWithinAt
  · have h := ((hasDerivAt_id' (‖Z‖ ^ 2)).const_add 1).fun_pow 2
    have h' := (hasDerivAt_const (‖Z‖ ^ 2) (-1 : ℝ)).fun_div h (pow_ne_zero 2 hpos.ne')
    refine (h'.congr_deriv ?_).hasDerivWithinAt
    field_simp
    ring

theorem fderiv_Rinv (Z a : Aff) :
    fderiv ℝ Rinv Z a = -1 / (1 + ‖Z‖ ^ 2) ^ 2 * (2 * inner ℝ Z a) := by
  have hpos : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
  have h := hasFDerivAt_radial (φ := fun q : ℝ => (1 + q)⁻¹) Z
    (((hasDerivAt_id' (‖Z‖ ^ 2)).const_add 1).fun_inv hpos).hasDerivWithinAt
  have h' : fderiv ℝ Rinv Z = _ := h.fderiv
  rw [h']
  rfl

theorem hess_Rinv (Z a b : Aff) :
    hess Rinv Z a b = 2 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * inner ℝ a b
      + 4 * (2 / (1 + ‖Z‖ ^ 2) ^ 3) * inner ℝ Z a * inner ℝ Z b :=
  hess_radial (φ := fun q : ℝ => (1 + q)⁻¹) (φ1 := fun q : ℝ => -1 / (1 + q) ^ 2)
    (Rinv_data Z).1 (Rinv_data Z).2 a b

theorem contDiff_logFS : ContDiff ℝ ∞ fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2) :=
  contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).log fun W => by positivity)

theorem hess_logFS (Z a b : Aff) :
    hess (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z a b
      = 2 * (1 * (1 + ‖Z‖ ^ 2)⁻¹) * inner ℝ a b
        + 4 * (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) * inner ℝ Z a * inner ℝ Z b :=
  hess_radial (φ := fun q : ℝ => 1 * Real.log (1 + q)) (φ1 := fun q : ℝ => 1 * (1 + q)⁻¹)
    (log_radial_data 1 Z).1 (log_radial_data 1 Z).2 a b

/-! ### Rotation by `i` -/

theorem inner_I_smul (Z a : Aff) : inner ℝ Z (Complex.I • a) = -(inner ℂ Z a : ℂ).im := by
  rw [real_inner_eq_re, inner_smul_right]
  simp

theorem inner_I_smul_self (a : Aff) : inner ℝ (Complex.I • a) (Complex.I • a) = ‖a‖ ^ 2 := by
  rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]

theorem reL_I_smul (a : Aff) : reL (Complex.I • a) = -(a 0).im := by
  show (Complex.I * a 0).re = _
  simp

theorem imL_I_smul (a : Aff) : imL (Complex.I • a) = (a 0).re := by
  show (Complex.I * a 0).im = _
  simp

/-! ### The algebra -/

/-- The inequality behind the positivity of the Levi form: with
`FS = (s A₂ - X) / s²` and `N = (s² α - 2 s M + n₀ X) / s³`, the form is
`(1 + η P₁) FS + (η P₂ - P₁) N` and `0 ≤ N ≤ (1 - η) FS`. -/
theorem chart_algebra {u v p q c₁ c₂ A₂ s P1 P2 : ℝ} (hs : 1 ≤ s)
    (hα : p ^ 2 + q ^ 2 ≤ A₂) (hA2 : 0 < A₂)
    (hCS : (c₁ - (u * p + v * q)) ^ 2 + (c₂ + (v * p - u * q)) ^ 2
      ≤ (s - 1 - (u ^ 2 + v ^ 2)) * (A₂ - (p ^ 2 + q ^ 2)))
    (hCS0 : c₁ ^ 2 + c₂ ^ 2 ≤ (s - 1) * A₂)
    (hposA : 0 < 1 + (u ^ 2 + v ^ 2) / s * P1)
    (hposB : 0 < 1 + (1 - 2 * (1 - (u ^ 2 + v ^ 2) / s)) * P1
      + (1 - (u ^ 2 + v ^ 2) / s) * ((u ^ 2 + v ^ 2) / s) * P2) :
    0 < (A₂ / s - (c₁ ^ 2 + c₂ ^ 2) / s ^ 2)
        + (-P1) * (-(u ^ 2 + v ^ 2) * A₂ / s ^ 2 + 2 * (u ^ 2 + v ^ 2) * (c₁ ^ 2 + c₂ ^ 2) / s ^ 3
          + (p ^ 2 + q ^ 2) / s - 2 * ((u * p + v * q) * c₁ - (v * p - u * q) * c₂) / s ^ 2)
        + P2 * (((u * p + v * q) - (u ^ 2 + v ^ 2) / s * c₁) ^ 2
          + ((v * p - u * q) + (u ^ 2 + v ^ 2) / s * c₂) ^ 2) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  set n₀ := u ^ 2 + v ^ 2 with hn₀
  set α := p ^ 2 + q ^ 2 with hα'
  set X := c₁ ^ 2 + c₂ ^ 2 with hX
  set M := (u * p + v * q) * c₁ - (v * p - u * q) * c₂ with hM
  obtain ⟨FS, hFS⟩ : ∃ FS : ℝ, FS = (s * A₂ - X) / s ^ 2 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (s ^ 2 * α - 2 * s * M + n₀ * X) / s ^ 3 := ⟨_, rfl⟩
  have e : (A₂ / s - X / s ^ 2)
      + (-P1) * (-n₀ * A₂ / s ^ 2 + 2 * n₀ * X / s ^ 3 + α / s - 2 * M / s ^ 2)
      + P2 * (((u * p + v * q) - n₀ / s * c₁) ^ 2 + ((v * p - u * q) + n₀ / s * c₂) ^ 2) / s ^ 2
      = (1 + n₀ / s * P1) * FS + (n₀ / s * P2 - P1) * N := by
    rw [hFS, hN, hn₀, hα', hX, hM]
    field_simp
    ring
  rw [e]
  have hFSpos : 0 < FS := by
    rw [hFS]
    refine div_pos ?_ (pow_pos hs0 2)
    nlinarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    refine div_nonneg ?_ (pow_pos hs0 3).le
    have e2 : s ^ 2 * α - 2 * s * M + n₀ * X
        = (s * p - (u * c₁ - v * c₂)) ^ 2 + (s * q - (u * c₂ + v * c₁)) ^ 2 := by
      rw [hn₀, hα', hX, hM]
      ring
    rw [e2]
    positivity
  have hNle : N ≤ (1 - n₀ / s) * FS := by
    have key : (1 - n₀ / s) * FS - N
        = ((s - n₀) * (A₂ - α) - ((c₁ - (u * p + v * q)) ^ 2 + (c₂ + (v * p - u * q)) ^ 2))
          / s ^ 2 := by
      rw [hFS, hN, hn₀, hα', hX, hM]
      field_simp
      ring
    have hnum : 0 ≤ (s - n₀) * (A₂ - α)
        - ((c₁ - (u * p + v * q)) ^ 2 + (c₂ + (v * p - u * q)) ^ 2) := by
      have h1 : 0 ≤ A₂ - α := by linarith
      nlinarith
    have h2 : 0 ≤ (1 - n₀ / s) * FS - N := by
      rw [key]
      exact div_nonneg hnum (pow_pos hs0 2).le
    linarith
  by_cases hc : 0 ≤ n₀ / s * P2 - P1
  · have h1 : 0 < (1 + n₀ / s * P1) * FS := mul_pos hposA hFSpos
    have h2 : 0 ≤ (n₀ / s * P2 - P1) * N := mul_nonneg hc hN0
    linarith
  · have hc' : n₀ / s * P2 - P1 ≤ 0 := (not_le.1 hc).le
    have h1 : (n₀ / s * P2 - P1) * ((1 - n₀ / s) * FS) ≤ (n₀ / s * P2 - P1) * N :=
      mul_le_mul_of_nonpos_left hNle hc'
    have h2 : 0 < (1 + (1 - 2 * (1 - n₀ / s)) * P1 + (1 - n₀ / s) * (n₀ / s) * P2) * FS :=
      mul_pos hposB hFSpos
    have h3 : (1 + (1 - 2 * (1 - n₀ / s)) * P1 + (1 - n₀ / s) * (n₀ / s) * P2) * FS
        = (1 + n₀ / s * P1) * FS + (n₀ / s * P2 - P1) * ((1 - n₀ / s) * FS) := by ring
    linarith

/-! ### The Cauchy–Schwarz inequalities -/

theorem normSq_inner_le (Z a : Aff) :
    (inner ℂ Z a : ℂ).re ^ 2 + (inner ℂ Z a : ℂ).im ^ 2 ≤ ‖Z‖ ^ 2 * ‖a‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) Z a
  have h0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ := norm_nonneg _
  have h1 : ‖(inner ℂ Z a : ℂ)‖ ^ 2 ≤ ‖Z‖ ^ 2 * ‖a‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg Z) (norm_nonneg a)]
  rw [Complex.sq_norm, Complex.normSq_apply] at h1
  linarith

/-- The vector with its coordinate `0` removed. -/
noncomputable def tail0 (a : Aff) : Aff := a - EuclideanSpace.single 0 (a 0)

theorem norm_tail0 (a : Aff) : ‖tail0 a‖ ^ 2 = ‖a‖ ^ 2 - ‖a 0‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ,
    Fin.sum_univ_succ (f := fun i => ‖a i‖ ^ 2)]
  simp [tail0, Fin.succ_ne_zero]

theorem inner_tail0 (Z a : Aff) :
    (inner ℂ (tail0 Z) (tail0 a) : ℂ) = inner ℂ Z a - (starRingEnd ℂ) (Z 0) * a 0 := by
  unfold tail0
  rw [inner_sub_left, inner_sub_right, inner_sub_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp
  ring

/-! ### Positivity -/

/-- **Positivity on the charts meeting the divisor at infinity.** -/
theorem levi_chart_infinity_pos {Ψ Ψ1 Ψ2 : ℝ → ℝ}
    (d1 : ∀ ξ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ψ (Ψ1 ξ) (Icc 0 1) ξ)
    (d2 : ∀ ξ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ψ1 (Ψ2 ξ) (Icc 0 1) ξ)
    (posA : ∀ ξ ∈ Icc (0 : ℝ) 1, 0 < 1 + (1 - ξ) * Ψ1 ξ)
    (posB : ∀ ξ ∈ Icc (0 : ℝ) 1, 0 < 1 + (1 - 2 * ξ) * Ψ1 ξ + ξ * (1 - ξ) * Ψ2 ξ)
    (Z : Aff) {a : Aff} (ha : a ≠ 0) :
    0 < (levi (fun W : Aff => Real.log (1 + ‖W‖ ^ 2)
      + Ψ (1 - ‖W 0‖ ^ 2 / (1 + ‖W‖ ^ 2))) Z a a).re := by
  have hspos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  -- the potential as a composition
  have hfun : (fun W : Aff => Real.log (1 + ‖W‖ ^ 2) + Ψ (1 - ‖W 0‖ ^ 2 / (1 + ‖W‖ ^ 2)))
      = fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)
        + (fun y : ℝ => Ψ (1 - y)) (N0 W * Rinv W) := by
    funext W
    rw [one_mul, N0_eq, Rinv, div_eq_mul_inv]
  have hηmem : ∀ W : Aff, N0 W * Rinv W ∈ Icc (0 : ℝ) 1 := by
    intro W
    have h1 : (0 : ℝ) < 1 + ‖W‖ ^ 2 := by positivity
    have h2 : ‖W 0‖ ^ 2 ≤ ‖W‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.single_le_sum (f := fun i => ‖W i‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ 0)
    rw [N0_eq, Rinv, ← div_eq_mul_inv]
    exact ⟨div_nonneg (sq_nonneg _) h1.le, (div_le_one h1).2 (by linarith)⟩
  have hsub : MapsTo (fun y : ℝ => 1 - y) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro y hy
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hΨ1 : ∀ y ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => Ψ (1 - y)) (-Ψ1 (1 - y)) (Icc 0 1) y := by
    intro y hy
    have h := (d1 (1 - y) (hsub hy)).comp y ((hasDerivWithinAt_id y (Icc 0 1)).const_sub 1) hsub
    refine h.congr_deriv ?_
    ring
  have hΨ2 : ∀ y ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => -Ψ1 (1 - y)) (Ψ2 (1 - y)) (Icc 0 1) y := by
    intro y hy
    have h := ((d2 (1 - y) (hsub hy)).comp y
      ((hasDerivWithinAt_id y (Icc 0 1)).const_sub 1) hsub).neg
    refine h.congr_deriv ?_
    ring
  have hf2 : ContDiffAt ℝ 2 (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z :=
    (contDiff_logFS.of_le (by simp)).contDiffAt
  have hN2 : ContDiffAt ℝ 2 N0 Z := (contDiff_N0.of_le (by simp)).contDiffAt
  have hR2 : ContDiffAt ℝ 2 Rinv Z := (contDiff_Rinv.of_le (by simp)).contDiffAt
  have hη2 : ContDiffAt ℝ 2 (fun W : Aff => N0 W * Rinv W) Z := hN2.mul hR2
  have hH : ∀ b : Aff, hess (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)
        + (fun y : ℝ => Ψ (1 - y)) (N0 W * Rinv W)) Z b b
      = hess (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) Z b b
        + (-Ψ1 (1 - N0 Z * Rinv Z)) * hess (fun W : Aff => N0 W * Rinv W) Z b b
        + Ψ2 (1 - N0 Z * Rinv Z) * (fderiv ℝ (fun W : Aff => N0 W * Rinv W) Z b
          * fderiv ℝ (fun W : Aff => N0 W * Rinv W) Z b) := fun b =>
    hess_add_comp (Ψ := fun y : ℝ => Ψ (1 - y)) (Ψ1 := fun y : ℝ => -Ψ1 (1 - y)) hf2 hη2 hηmem
      (eventually_mem_nhdsWithin.mono fun y hy => hΨ1 y hy) (hΨ2 _ (hηmem Z)) b b
  -- the real coordinates
  have hRZ : Rinv Z = (1 + ‖Z‖ ^ 2)⁻¹ := rfl
  have hNZ : N0 Z = (Z 0).re ^ 2 + (Z 0).im ^ 2 := by
    unfold N0
    rw [reL_apply, imL_apply]
    ring
  have hA2 : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 ha) 2
  have hα : (a 0).re ^ 2 + (a 0).im ^ 2 ≤ ‖a‖ ^ 2 := by
    have h2 : ‖a 0‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.single_le_sum (f := fun i => ‖a i‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ 0)
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    linarith
  have hCS0 := normSq_inner_le Z a
  have hCS := normSq_inner_le (tail0 Z) (tail0 a)
  rw [inner_tail0, norm_tail0, norm_tail0, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply] at hCS
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at hCS
  have hηZ : N0 Z * Rinv Z = ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2) := by
    rw [hNZ, hRZ, div_eq_mul_inv]
  have hpA := posA _ (hsub (hηmem Z))
  have hpB := posB _ (hsub (hηmem Z))
  rw [hηZ] at hpA hpB
  have key := chart_algebra (u := (Z 0).re) (v := (Z 0).im) (p := (a 0).re) (q := (a 0).im)
    (c₁ := (inner ℂ Z a : ℂ).re) (c₂ := (inner ℂ Z a : ℂ).im) (A₂ := ‖a‖ ^ 2)
    (s := 1 + ‖Z‖ ^ 2) (P1 := Ψ1 (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2)))
    (P2 := Ψ2 (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2)))
    (by linarith [sq_nonneg ‖Z‖]) hα hA2 (by nlinarith [hCS]) (by nlinarith [hCS0])
    (by
      have e : 1 - (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2))
          = ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2) := by ring
      rw [e] at hpA
      exact hpA)
    (by
      have e : 1 - (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2))
          = ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2) := by ring
      rw [e] at hpB
      exact hpB)
  rw [hfun, levi_re, hH a, hH (Complex.I • a)]
  simp only [hess_logFS, hess_mul hN2 hR2, fderiv_mul_apply hN2 hR2, hess_Rinv, hess_N0,
    fderiv_N0, fderiv_Rinv]
  simp only [inner_I_smul_self]
  simp only [inner_I_smul, reL_I_smul, imL_I_smul]
  simp only [real_inner_self_eq_norm_sq, real_inner_eq_re Z a, reL_apply, imL_apply, hηZ]
  rw [hNZ, hRZ]
  refine lt_of_lt_of_eq key ?_
  have hsne : (1 + ‖Z‖ ^ 2) ≠ 0 := hspos.ne'
  generalize Ψ1 (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2)) = P1
  generalize Ψ2 (1 - ((Z 0).re ^ 2 + (Z 0).im ^ 2) / (1 + ‖Z‖ ^ 2)) = P2
  generalize 1 + ‖Z‖ ^ 2 = s at hsne ⊢
  field_simp
  ring

end Calabi.Geometry
