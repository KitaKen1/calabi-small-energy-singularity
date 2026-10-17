import Calabi.Radial.Cutoff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth even functions are smooth functions of the square

A smooth radial function on a ball is a smooth function of the square of the
radius, up to the centre (Whitney). This is needed with a parameter (the
time): `whitney_even` states that for a smooth function `g(t, s)` on the plane
that is even in `s`, the function `(t, x) ↦ g(t, √x)` is smooth on the closed
half plane `x ≥ 0`.

The proof is by induction on the order of differentiability. The derivative of
`(t, x) ↦ g(t, √x)` is `(∂ₜ g)(t, √x) dt + ½ (T g)(t, √x) dx` with

  `(T g)(t, r) = ∫₀¹ ∂ₛ² g(t, σ r) dσ = ∂ₛ g(t, r) / r`,

and `∂ₜ g` and `T g` are again smooth and even. The smoothness of `T g` is the
smoothness of an integral with a parameter (`contDiff_integral_param`); the
derivative at the boundary `x = 0` is obtained from the limit of the
derivatives in the interior.

`whitney_chart` is the form used for the chart functions of the solution.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Calabi.Whitney

open Calabi.Radial

/-! ### Integrals with a parameter -/

section Param

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **An integral over `[0, 1]` of a smooth function with a parameter is smooth
in the parameter.** -/
theorem contDiff_integral_param (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : E × ℝ → F),
      ContDiff ℝ ∞ K → ContDiff ℝ n (fun p : E => ∫ σ in (0 : ℝ)..1, K (p, σ)) := by
  induction n with
  | zero =>
    intro F _ _ _ K hK
    have hc : Continuous (Function.uncurry fun (p : E) (σ : ℝ) => K (p, σ)) := hK.continuous
    exact_mod_cast contDiff_zero.2
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1)
  | succ n ih =>
    intro F _ _ _ K hK
    have hK₁ : ContDiff ℝ ∞ (fun q : E × ℝ =>
        (fderiv ℝ K q).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
      (hK.fderiv_right (by simp)).clm_comp contDiff_const
    have hder : ∀ p₀ : E, HasFDerivAt (fun p : E => ∫ σ in (0 : ℝ)..1, K (p, σ))
        (∫ σ in (0 : ℝ)..1, (fderiv ℝ K (p₀, σ)).comp (ContinuousLinearMap.inl ℝ E ℝ)) p₀ := by
      intro p₀
      have hcpt : IsCompact (Metric.closedBall p₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
        (isCompact_closedBall p₀ 1).prod isCompact_Icc
      obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hK₁.continuous.continuousOn
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun (p : E) (σ : ℝ) => K (p, σ))
        (F' := fun (p : E) (σ : ℝ) => (fderiv ℝ K (p, σ)).comp (ContinuousLinearMap.inl ℝ E ℝ))
        (bound := fun _ => C) (s := Metric.ball p₀ 1) (Metric.ball_mem_nhds p₀ one_pos)
        ?_ ?_ ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun p =>
          (hK.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hK.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · exact (hK₁.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · refine ae_of_all _ fun σ hσ p hp => ?_
        rw [uIoc_of_le zero_le_one] at hσ
        exact hC (p, σ) ⟨Metric.ball_subset_closedBall hp, hσ.1.le, hσ.2⟩
      · exact intervalIntegrable_const
      · refine ae_of_all _ fun σ _ p _ => ?_
        have h1 : HasFDerivAt K (fderiv ℝ K (p, σ)) (p, σ) :=
          (hK.differentiable (by simp) _).hasFDerivAt
        exact h1.comp p (hasFDerivAt_prodMk_left p σ)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hder p).differentiableAt, fun h => absurd h (by simp), ?_⟩
    have e : fderiv ℝ (fun p : E => ∫ σ in (0 : ℝ)..1, K (p, σ))
        = fun p => ∫ σ in (0 : ℝ)..1, (fderiv ℝ K (p, σ)).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
      funext fun p => (hder p).fderiv
    rw [e]
    exact ih _ hK₁

end Param

/-! ### Parity -/

/-- The reflection in the second variable. -/
noncomputable def refl2 : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem refl2_apply (q : ℝ × ℝ) : refl2 q = (q.1, -q.2) := rfl

/-- The derivative of a function with a parity under the reflection. -/
theorem fderiv_parity {h : ℝ × ℝ → ℝ} (hh : Differentiable ℝ h) {ε : ℝ}
    (hpar : ∀ q, h (refl2 q) = ε * h q) (q v : ℝ × ℝ) :
    fderiv ℝ h (refl2 q) (refl2 v) = ε * fderiv ℝ h q v := by
  have h1 : HasFDerivAt (fun q => h (refl2 q)) ((fderiv ℝ h (refl2 q)).comp refl2) q :=
    (hh (refl2 q)).hasFDerivAt.comp q refl2.hasFDerivAt
  have h2 : HasFDerivAt (fun q => ε * h q) (ε • fderiv ℝ h q) q :=
    (hh q).hasFDerivAt.const_mul ε
  have e : (fun q => h (refl2 q)) = fun q => ε * h q := funext hpar
  rw [e] at h1
  have h3 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L v) (h1.unique h2)
  simpa using h3

/-! ### The even function theorem -/

set_option maxHeartbeats 3200000 in
/-- **Whitney's theorem for even functions, with a parameter.** -/
theorem whitney_even (n : ℕ) : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → (∀ q, g (refl2 q) = g q) →
    ContDiffOn ℝ n (fun p : ℝ × ℝ => g (p.1, Real.sqrt p.2)) (univ ×ˢ Ici (0 : ℝ)) := by
  induction n with
  | zero =>
    intro g hg _
    have hc : Continuous fun p : ℝ × ℝ => g (p.1, Real.sqrt p.2) :=
      hg.continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))
    exact_mod_cast contDiffOn_zero.2 hc.continuousOn
  | succ n ih =>
    intro g hg hev
    have hgd : Differentiable ℝ g := hg.differentiable (by simp)
    -- the partial derivatives
    have hgt : ContDiff ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ g q ((1 : ℝ), (0 : ℝ))) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have hgs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ g q ((0 : ℝ), (1 : ℝ))) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have hgss : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
        fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) q ((0 : ℝ), (1 : ℝ))) :=
      (hgs.fderiv_right (by simp)).clm_apply contDiff_const
    have hpar1 : ∀ q, g (refl2 q) = 1 * g q := fun q => by rw [one_mul, hev q]
    -- parity of the partial derivatives
    have hgt_even : ∀ q : ℝ × ℝ, fderiv ℝ g (refl2 q) ((1 : ℝ), (0 : ℝ))
        = fderiv ℝ g q ((1 : ℝ), (0 : ℝ)) := by
      intro q
      have h1 := fderiv_parity hgd hpar1 q ((1 : ℝ), (0 : ℝ))
      rw [one_mul] at h1
      have e : refl2 ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ)) := by
        rw [refl2_apply]
        simp
      rwa [e] at h1
    have hgs_odd : ∀ q : ℝ × ℝ, fderiv ℝ g (refl2 q) ((0 : ℝ), (1 : ℝ))
        = -1 * fderiv ℝ g q ((0 : ℝ), (1 : ℝ)) := by
      intro q
      have h1 := fderiv_parity hgd hpar1 q ((0 : ℝ), (1 : ℝ))
      rw [one_mul] at h1
      have e : refl2 ((0 : ℝ), (1 : ℝ)) = -((0 : ℝ), (1 : ℝ)) := by
        rw [refl2_apply]
        simp
      rw [e, map_neg] at h1
      linarith
    have hgss_even : ∀ q : ℝ × ℝ,
        fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (refl2 q) ((0 : ℝ), (1 : ℝ))
        = fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) q ((0 : ℝ), (1 : ℝ)) := by
      intro q
      have h1 := fderiv_parity (hgs.differentiable (by simp)) hgs_odd q ((0 : ℝ), (1 : ℝ))
      have e : refl2 ((0 : ℝ), (1 : ℝ)) = -((0 : ℝ), (1 : ℝ)) := by
        rw [refl2_apply]
        simp
      rw [e, map_neg] at h1
      linarith
    have hgs0 : ∀ t : ℝ, fderiv ℝ g (t, 0) ((0 : ℝ), (1 : ℝ)) = 0 := by
      intro t
      have h1 := hgs_odd (t, 0)
      have e : refl2 ((t, 0) : ℝ × ℝ) = (t, 0) := by
        rw [refl2_apply]
        simp
      rw [e] at h1
      linarith
    -- the average of the second derivative
    obtain ⟨Tg, hTgdef⟩ : ∃ Tg : ℝ × ℝ → ℝ, Tg = fun q => ∫ σ in (0 : ℝ)..1,
        fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (q.1, σ * q.2)
          ((0 : ℝ), (1 : ℝ)) := ⟨_, rfl⟩
    have hTg : ContDiff ℝ ∞ Tg := by
      rw [hTgdef]
      refine contDiff_infty.2 fun m => ?_
      exact contDiff_integral_param (E := ℝ × ℝ) m
        (fun r : (ℝ × ℝ) × ℝ =>
          fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (r.1.1, r.2 * r.1.2)
            ((0 : ℝ), (1 : ℝ)))
        (hgss.comp ((contDiff_fst.comp contDiff_fst).prodMk
          (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))))
    have hTg_even : ∀ q, Tg (refl2 q) = Tg q := by
      intro q
      rw [hTgdef]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      have e : ((refl2 q).1, σ * (refl2 q).2) = refl2 (q.1, σ * q.2) := by
        rw [refl2_apply, refl2_apply]
        simp
      show fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ)))
        ((refl2 q).1, σ * (refl2 q).2) ((0 : ℝ), (1 : ℝ)) = _
      rw [e, hgss_even]
    -- the derivative in `s` is `s` times the average
    have hgsT : ∀ t r : ℝ, fderiv ℝ g (t, r) ((0 : ℝ), (1 : ℝ)) = r * Tg (t, r) := by
      intro t r
      have hd : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt
          (fun σ : ℝ => fderiv ℝ g (t, σ * r) ((0 : ℝ), (1 : ℝ)))
          (r * fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (t, σ * r)
            ((0 : ℝ), (1 : ℝ))) σ := by
        intro σ _
        have hline : HasDerivAt (fun σ : ℝ => ((t, σ * r) : ℝ × ℝ)) ((0 : ℝ), r) σ := by
          have h1 := (hasDerivAt_const σ t).prodMk ((hasDerivAt_id σ).mul_const r)
          simpa using h1
        have h1 : HasFDerivAt (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ)))
            (fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (t, σ * r))
            (t, σ * r) := (hgs.differentiable (by simp) _).hasFDerivAt
        have h2 := h1.comp_hasDerivAt σ hline
        have e : (((0 : ℝ), r) : ℝ × ℝ) = r • ((0 : ℝ), (1 : ℝ)) := by
          ext <;> simp
        rw [e, map_smul, smul_eq_mul] at h2
        exact h2
      have hint : IntervalIntegrable (fun σ : ℝ =>
          r * fderiv ℝ (fun q' : ℝ × ℝ => fderiv ℝ g q' ((0 : ℝ), (1 : ℝ))) (t, σ * r)
            ((0 : ℝ), (1 : ℝ))) volume 0 1 :=
        (continuous_const.mul (hgss.continuous.comp
          (continuous_const.prodMk (continuous_id.mul continuous_const)))).intervalIntegrable _ _
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
      rw [intervalIntegral.integral_const_mul, one_mul, zero_mul, hgs0 t, sub_zero] at hftc
      rw [hTgdef]
      exact hftc.symm
    -- the candidate for the derivative
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ), L = fun p =>
        (fderiv ℝ g (p.1, Real.sqrt p.2) ((1 : ℝ), (0 : ℝ))) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (1 / 2 * Tg (p.1, Real.sqrt p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ := ⟨_, rfl⟩
    have hLapp : ∀ (p v : ℝ × ℝ), L p v
        = fderiv ℝ g (p.1, Real.sqrt p.2) ((1 : ℝ), (0 : ℝ)) * v.1
          + 1 / 2 * Tg (p.1, Real.sqrt p.2) * v.2 := by
      intro p v
      rw [hLdef]
      simp
    have hm : Continuous fun p : ℝ × ℝ => ((p.1, Real.sqrt p.2) : ℝ × ℝ) :=
      continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)
    have hLc : Continuous L := by
      rw [continuous_clm_apply]
      intro v
      have e : (fun p => L p v) = fun p : ℝ × ℝ =>
          fderiv ℝ g (p.1, Real.sqrt p.2) ((1 : ℝ), (0 : ℝ)) * v.1
            + 1 / 2 * Tg (p.1, Real.sqrt p.2) * v.2 := funext fun p => hLapp p v
      rw [e]
      exact ((hgt.continuous.comp hm).mul continuous_const).add
        ((continuous_const.mul (hTg.continuous.comp hm)).mul continuous_const)
    -- the derivative in the interior
    have hint : ∀ y : ℝ × ℝ, 0 < y.2 →
        HasFDerivAt (fun p : ℝ × ℝ => g (p.1, Real.sqrt p.2)) (L y) y := by
      intro y hy
      have hr : 0 < Real.sqrt y.2 := Real.sqrt_pos.2 hy
      have h1 : HasFDerivAt g (fderiv ℝ g (y.1, Real.sqrt y.2)) (y.1, Real.sqrt y.2) :=
        (hgd _).hasFDerivAt
      have h2 : HasFDerivAt (fun p : ℝ × ℝ => ((p.1, Real.sqrt p.2) : ℝ × ℝ))
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
            ((1 / (2 * Real.sqrt y.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)) y :=
        hasFDerivAt_fst.prodMk ((Real.hasDerivAt_sqrt hy.ne').comp_hasFDerivAt y hasFDerivAt_snd)
      have h3 := h1.comp y h2
      refine h3.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      rw [hLapp]
      have e : ((v.1, 1 / (2 * Real.sqrt y.2) * v.2) : ℝ × ℝ)
          = v.1 • ((1 : ℝ), (0 : ℝ)) + (1 / (2 * Real.sqrt y.2) * v.2) • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      show fderiv ℝ g (y.1, Real.sqrt y.2) (v.1, 1 / (2 * Real.sqrt y.2) * v.2) = _
      rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hgsT y.1 (Real.sqrt y.2)]
      field_simp
    -- the derivative up to the boundary
    have hS : UniqueDiffOn ℝ (univ ×ˢ Ici (0 : ℝ) : Set (ℝ × ℝ)) :=
      uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)
    have hcf : Continuous fun p : ℝ × ℝ => g (p.1, Real.sqrt p.2) := hg.continuous.comp hm
    have hder : ∀ p ∈ (univ ×ˢ Ici (0 : ℝ) : Set (ℝ × ℝ)),
        HasFDerivWithinAt (fun p : ℝ × ℝ => g (p.1, Real.sqrt p.2)) (L p) (univ ×ˢ Ici 0) p := by
      intro p _
      have hcl : closure (univ ×ˢ Ioi (0 : ℝ) : Set (ℝ × ℝ)) = univ ×ˢ Ici 0 := by
        rw [closure_prod_eq, closure_univ, closure_Ioi]
      rw [← hcl]
      refine hasFDerivWithinAt_closure_of_tendsto_fderiv
        (fun y hy => (hint y hy.2).differentiableAt.differentiableWithinAt)
        (convex_univ.prod (convex_Ioi 0)) (isOpen_univ.prod isOpen_Ioi)
        (fun y _ => hcf.continuousAt.continuousWithinAt) ?_
      refine (hLc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact ((hint y hy.2).fderiv).symm
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderivWithin hS]
    refine ⟨fun p hp => (hder p hp).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    have hLn : ContDiffOn ℝ n L (univ ×ˢ Ici (0 : ℝ)) := by
      rw [contDiffOn_clm_apply]
      intro v
      have h1 := ih _ hgt hgt_even
      have h2 := ih Tg hTg hTg_even
      have e : (fun p => L p v) = fun p : ℝ × ℝ =>
          fderiv ℝ g (p.1, Real.sqrt p.2) ((1 : ℝ), (0 : ℝ)) * v.1
            + 1 / 2 * Tg (p.1, Real.sqrt p.2) * v.2 := funext fun p => hLapp p v
      rw [e]
      exact (h1.mul contDiffOn_const).add ((contDiffOn_const.mul h2).mul contDiffOn_const)
    exact hLn.congr fun p hp => (hder p hp).fderivWithin (hS p hp)

/-! ### Radial functions in a chart -/

set_option maxHeartbeats 3200000 in
/-- **A smooth function on a chart that is even along a ray is a smooth
function of the square of the radius, up to the centre**, with the time as a
parameter. -/
theorem whitney_chart {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {T R : ℝ}
    {Fc : V × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ Fc {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}) {e : V}
    (he : ‖e‖ = 1) (hev : ∀ t s : ℝ, Fc ((-s) • e, t) = Fc (s • e, t)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Fc (Real.sqrt p.2 • e, p.1))
      (Ioo (-T) 0 ×ˢ Ico (0 : ℝ) R) := by
  intro p₀ hp₀
  obtain ⟨ht₀, hx₀⟩ := hp₀
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (R - p₀.2) / 3 := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    linarith [hx₀.2]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (p₀.1 + T) (-p₀.1) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  have hρ1 : ρ ≤ p₀.1 + T := by
    rw [hρdef]
    exact min_le_left _ _
  have hρ2 : ρ ≤ -p₀.1 := by
    rw [hρdef]
    exact min_le_right _ _
  -- the chart function on the plane
  have hWopen : IsOpen {q : ℝ × ℝ | q.1 ∈ Ioo (-T) 0 ∧ q.2 ^ 2 < R} :=
    (isOpen_Ioo.preimage continuous_fst).inter (isOpen_lt (continuous_snd.pow 2) continuous_const)
  have hg₀ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => Fc (q.2 • e, q.1))
      {q : ℝ × ℝ | q.1 ∈ Ioo (-T) 0 ∧ q.2 ^ 2 < R} := by
    refine hF.comp ((contDiff_snd.smul contDiff_const).prodMk contDiff_fst).contDiffOn
      fun q hq => ⟨hq.1, ?_⟩
    show ‖q.2 • e‖ ^ 2 < R
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    exact hq.2
  -- the cut-offs
  have hζs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => chi (((q.1 - p₀.1) / (ρ / 2)) ^ 2)) :=
    contDiff_chi.comp (((contDiff_fst.sub contDiff_const).div_const _).pow 2)
  have hηs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => chi ((q.2 ^ 2 - (p₀.2 + δ)) / δ + 1)) :=
    contDiff_chi.comp ((((contDiff_snd.pow 2).sub contDiff_const).div_const _).add contDiff_const)
  obtain ⟨gt, hgtdef⟩ : ∃ gt : ℝ × ℝ → ℝ, gt = fun q => chi (((q.1 - p₀.1) / (ρ / 2)) ^ 2)
      * chi ((q.2 ^ 2 - (p₀.2 + δ)) / δ + 1) * Fc (q.2 • e, q.1) := ⟨_, rfl⟩
  have hgts : ContDiff ℝ ∞ gt := by
    rw [hgtdef, contDiff_iff_contDiffAt]
    intro q
    by_cases h1 : |q.1 - p₀.1| < ρ
    · by_cases h2 : q.2 ^ 2 < R
      · have hq : q ∈ {q : ℝ × ℝ | q.1 ∈ Ioo (-T) 0 ∧ q.2 ^ 2 < R} := by
          have h3 := abs_lt.1 h1
          exact ⟨⟨by linarith [h3.1], by linarith [h3.2]⟩, h2⟩
        exact (hζs.contDiffAt.mul hηs.contDiffAt).mul (hg₀.contDiffAt (hWopen.mem_nhds hq))
      · have hopen : IsOpen {q : ℝ × ℝ | p₀.2 + 2 * δ < q.2 ^ 2} :=
          isOpen_lt continuous_const (continuous_snd.pow 2)
        have hmem : q ∈ {q : ℝ × ℝ | p₀.2 + 2 * δ < q.2 ^ 2} := by
          show p₀.2 + 2 * δ < q.2 ^ 2
          have h3 : R ≤ q.2 ^ 2 := not_lt.1 h2
          rw [hδdef]
          linarith [hx₀.2]
        refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hopen.mem_nhds hmem] with y hy
        have hy' : p₀.2 + 2 * δ < y.2 ^ 2 := hy
        have h4 : 2 ≤ (y.2 ^ 2 - (p₀.2 + δ)) / δ + 1 := by
          rw [← sub_le_iff_le_add, le_div_iff₀ hδ]
          linarith
        rw [chi_of_ge h4, mul_zero, zero_mul]
    · have hopen : IsOpen {q : ℝ × ℝ | 2 < ((q.1 - p₀.1) / (ρ / 2)) ^ 2} :=
        isOpen_lt continuous_const (((continuous_fst.sub continuous_const).div_const _).pow 2)
      have hmem : q ∈ {q : ℝ × ℝ | 2 < ((q.1 - p₀.1) / (ρ / 2)) ^ 2} := by
        show 2 < ((q.1 - p₀.1) / (ρ / 2)) ^ 2
        have h3 : ρ ≤ |q.1 - p₀.1| := not_lt.1 h1
        have h4 : ((q.1 - p₀.1) / (ρ / 2)) ^ 2 = (|q.1 - p₀.1| / (ρ / 2)) ^ 2 := by
          rw [← sq_abs ((q.1 - p₀.1) / (ρ / 2)), abs_div, abs_of_pos (by positivity : (0 : ℝ) < ρ / 2)]
        rw [h4]
        have h5 : 2 ≤ |q.1 - p₀.1| / (ρ / 2) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        nlinarith
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with y hy
      rw [chi_of_ge (le_of_lt hy), zero_mul, zero_mul]
  have hgte : ∀ q, gt (refl2 q) = gt q := by
    intro q
    rw [hgtdef]
    show chi ((((refl2 q).1 - p₀.1) / (ρ / 2)) ^ 2)
        * chi (((refl2 q).2 ^ 2 - (p₀.2 + δ)) / δ + 1) * Fc ((refl2 q).2 • e, (refl2 q).1)
      = chi (((q.1 - p₀.1) / (ρ / 2)) ^ 2) * chi ((q.2 ^ 2 - (p₀.2 + δ)) / δ + 1)
        * Fc (q.2 • e, q.1)
    rw [refl2_apply]
    simp only [neg_sq]
    rw [hev q.1 q.2]
  have hW : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gt (p.1, Real.sqrt p.2)) (univ ×ˢ Ici (0 : ℝ)) :=
    contDiffOn_infty.2 fun n => whitney_even n gt hgts hgte
  have hval : ∀ p : ℝ × ℝ, |p.1 - p₀.1| < ρ / 2 → p.2 < p₀.2 + δ → 0 ≤ p.2 →
      gt (p.1, Real.sqrt p.2) = Fc (Real.sqrt p.2 • e, p.1) := by
    intro p h1 h2 h3
    have e1 : chi (((p.1 - p₀.1) / (ρ / 2)) ^ 2) = 1 := by
      apply chi_of_le
      have h4 : ((p.1 - p₀.1) / (ρ / 2)) ^ 2 = (|p.1 - p₀.1| / (ρ / 2)) ^ 2 := by
        rw [← sq_abs ((p.1 - p₀.1) / (ρ / 2)), abs_div, abs_of_pos (by positivity : (0 : ℝ) < ρ / 2)]
      rw [h4]
      have h5 : |p.1 - p₀.1| / (ρ / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h1.le
      have h6 : 0 ≤ |p.1 - p₀.1| / (ρ / 2) := div_nonneg (abs_nonneg _) (by positivity)
      nlinarith
    have e2 : chi ((Real.sqrt p.2 ^ 2 - (p₀.2 + δ)) / δ + 1) = 1 := by
      apply chi_of_le
      rw [Real.sq_sqrt h3]
      have h4 : (p.2 - (p₀.2 + δ)) / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      linarith
    rw [hgtdef]
    show chi (((p.1 - p₀.1) / (ρ / 2)) ^ 2) * chi ((Real.sqrt p.2 ^ 2 - (p₀.2 + δ)) / δ + 1)
      * Fc (Real.sqrt p.2 • e, p.1) = _
    rw [e1, e2, one_mul, one_mul]
  have hpmem : p₀ ∈ (univ ×ˢ Ici (0 : ℝ) : Set (ℝ × ℝ)) := ⟨mem_univ _, hx₀.1⟩
  have h1 := (hW p₀ hpmem).mono (show Ioo (-T) 0 ×ˢ Ico (0 : ℝ) R ⊆ univ ×ˢ Ici (0 : ℝ) from
    fun p hp => ⟨mem_univ _, hp.2.1⟩)
  refine h1.congr_of_eventuallyEq ?_ ?_
  · have hnb : {p : ℝ × ℝ | |p.1 - p₀.1| < ρ / 2 ∧ p.2 < p₀.2 + δ} ∈ 𝓝 p₀ := by
      refine IsOpen.mem_nhds ((isOpen_lt (continuous_fst.sub continuous_const).abs
        continuous_const).inter (isOpen_lt continuous_snd continuous_const)) ⟨?_, ?_⟩
      · show |p₀.1 - p₀.1| < ρ / 2
        rw [sub_self, abs_zero]
        positivity
      · show p₀.2 < p₀.2 + δ
        linarith
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnb, self_mem_nhdsWithin] with p hp hpS
    exact (hval p hp.1 hp.2 hpS.2.1).symm
  · exact (hval p₀ (by rw [sub_self, abs_zero]; positivity) (by linarith) hx₀.1).symm

end Calabi.Whitney
