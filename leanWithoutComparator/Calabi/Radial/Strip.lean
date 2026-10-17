import Calabi.Radial.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus on a closed strip `J × [0, 1]`

The functions of the momentum coordinate are smooth on the closed interval
`[0, 1]`, and depend smoothly on time. This file collects what is needed to
integrate and to invert such functions without leaving the closed strip
`J ×ˢ Icc 0 1`, `J` open:

* `Smooth.dx`, `Smooth.dt`: the partial derivatives (within the strip) of a
  smooth function are smooth;
* `hasFDerivWithinAt_of_partials`: a function with a continuous partial
  derivative in `x` and a partial derivative in `t` at one point is
  differentiable within the strip at that point;
* `Smooth.jx`: the primitive `∫_1^x k(t, y) dy` is smooth on the strip, with
  partial derivatives `k` and `∫_1^x ∂_t k`;
* `contDiffOn_of_inverse`: a right inverse of a smooth map with invertible
  derivatives on a set with unique derivatives is smooth as soon as it is
  continuous;
* `smooth_inverse`: the fibrewise inverse of `(t, x) ↦ Ξ(t, x)` with
  `∂_x Ξ > 0` is smooth on the strip.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Calabi.Strip

/-- Smoothness on the closed strip `J × [0, 1]`. -/
abbrev Smooth (J : Set ℝ) (k : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1)

/-- The partial derivative in `x`, within `[0, 1]`. -/
noncomputable def Dx (k : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := derivWithin (k t) (Icc 0 1) x

/-- The partial derivative in `t`. -/
noncomputable def Dt (k : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => k s x) t

/-- The primitive in `x`, from the endpoint `1`. -/
noncomputable def Jx (k : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := ∫ y in (1 : ℝ)..x, k t y

theorem uniqueDiffOn_strip {J : Set ℝ} (hJ : IsOpen J) : UniqueDiffOn ℝ (J ×ˢ Icc (0 : ℝ) 1) :=
  hJ.uniqueDiffOn.prod uniqueDiffOn_Icc_zero_one

/-! ### Slices -/

section Slices

variable {J : Set ℝ} {f : ℝ × ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ} {t x : ℝ}

theorem hasDerivWithinAt_slice (ht : t ∈ J)
    (hf : HasFDerivWithinAt f f' (J ×ˢ Icc (0 : ℝ) 1) (t, x)) :
    HasDerivWithinAt (fun y => f (t, y)) (f' (0, 1)) (Icc 0 1) x := by
  have hc : HasDerivWithinAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (Icc 0 1) x :=
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x)).hasDerivWithinAt
  have hm : MapsTo (fun y : ℝ => ((t, y) : ℝ × ℝ)) (Icc 0 1) (J ×ˢ Icc (0 : ℝ) 1) :=
    fun y hy => ⟨ht, hy⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt x hf hc hm

theorem hasDerivAt_slice (hJ : IsOpen J) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1)
    (hf : HasFDerivWithinAt f f' (J ×ˢ Icc (0 : ℝ) 1) (t, x)) :
    HasDerivAt (fun s => f (s, x)) (f' (1, 0)) t := by
  have hc : HasDerivWithinAt (fun s : ℝ => ((s, x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ => ((s, x) : ℝ × ℝ)) J (J ×ˢ Icc (0 : ℝ) 1) :=
    fun s hs => ⟨hs, hx⟩
  exact (HasFDerivWithinAt.comp_hasDerivWithinAt t hf hc hm).hasDerivAt (hJ.mem_nhds ht)

end Slices

/-! ### Partial derivatives of smooth functions -/

section Partial

variable {J : Set ℝ} {k : ℝ → ℝ → ℝ} {t x : ℝ}

theorem Smooth.hasFDerivWithinAt' (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => k p.1 p.2)
      (fderivWithin ℝ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) (t, x))
      (J ×ˢ Icc (0 : ℝ) 1) (t, x) :=
  ((ContDiffOn.differentiableOn hk (by simp)) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt

theorem Smooth.hasDerivWithinAt_x (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (k t) (Dx k t x) (Icc 0 1) x := by
  have h : HasDerivWithinAt (k t) _ (Icc 0 1) x :=
    hasDerivWithinAt_slice ht (hk.hasFDerivWithinAt' ht hx)
  exact h.differentiableWithinAt.hasDerivWithinAt

theorem Smooth.Dx_eq (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dx k t x
      = fderivWithin ℝ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) (t, x) (0, 1) := by
  have h : HasDerivWithinAt (k t) _ (Icc 0 1) x :=
    hasDerivWithinAt_slice ht (hk.hasFDerivWithinAt' ht hx)
  exact h.derivWithin (uniqueDiffOn_Icc_zero_one x hx)

theorem Smooth.hasDerivAt_t (hJ : IsOpen J) (hk : Smooth J k) (ht : t ∈ J)
    (hx : x ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun s => k s x) (Dt k t x) t := by
  have h : HasDerivAt (fun s => k s x) _ t :=
    hasDerivAt_slice hJ ht hx (hk.hasFDerivWithinAt' ht hx)
  exact h.differentiableAt.hasDerivAt

theorem Smooth.Dt_eq (hJ : IsOpen J) (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Dt k t x
      = fderivWithin ℝ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) (t, x) (1, 0) := by
  have h : HasDerivAt (fun s => k s x) _ t :=
    hasDerivAt_slice hJ ht hx (hk.hasFDerivWithinAt' ht hx)
  exact h.deriv

theorem Smooth.continuousOn_x (hk : Smooth J k) (ht : t ∈ J) : ContinuousOn (k t) (Icc 0 1) :=
  fun _ hx => (hk.hasDerivWithinAt_x ht hx).continuousWithinAt

theorem Smooth.continuousOn_t (hJ : IsOpen J) (hk : Smooth J k) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun s => k s x) J :=
  fun _ ht => (hk.hasDerivAt_t hJ ht hx).continuousAt.continuousWithinAt

/-- The partial derivative in `x` of a smooth function is smooth. -/
theorem Smooth.dx (hJ : IsOpen J) (hk : Smooth J k) : Smooth J (Dx k) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      fderivWithin ℝ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) p ((0 : ℝ), (1 : ℝ)))
      (J ×ˢ Icc (0 : ℝ) 1) :=
    (ContDiffOn.fderivWithin hk (uniqueDiffOn_strip hJ) (by simp)).clm_apply contDiffOn_const
  exact h.congr fun p hp => hk.Dx_eq hp.1 hp.2

/-- The partial derivative in `t` of a smooth function is smooth. -/
theorem Smooth.dt (hJ : IsOpen J) (hk : Smooth J k) : Smooth J (Dt k) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      fderivWithin ℝ (fun p : ℝ × ℝ => k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) p ((1 : ℝ), (0 : ℝ)))
      (J ×ˢ Icc (0 : ℝ) 1) :=
    (ContDiffOn.fderivWithin hk (uniqueDiffOn_strip hJ) (by simp)).clm_apply contDiffOn_const
  exact h.congr fun p hp => hk.Dt_eq hJ hp.1 hp.2

/-- The derivative of a smooth function along a curve `s ↦ (s, c s)` of the
strip. -/
theorem Smooth.hasDerivAt_comp (hJ : IsOpen J) (hk : Smooth J k) {c : ℝ → ℝ} {c' : ℝ}
    (ht : t ∈ J) (hc : ∀ s ∈ J, c s ∈ Icc (0 : ℝ) 1) (hc' : HasDerivAt c c' t) :
    HasDerivAt (fun s => k s (c s)) (Dt k t (c t) + Dx k t (c t) * c') t := by
  have hF := hk.hasFDerivWithinAt' ht (hc t ht)
  have hcurve : HasDerivWithinAt (fun s : ℝ => ((s, c s) : ℝ × ℝ)) ((1 : ℝ), c') J t :=
    ((hasDerivAt_id t).prodMk hc').hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ => ((s, c s) : ℝ × ℝ)) J (J ×ˢ Icc (0 : ℝ) 1) :=
    fun s hs => ⟨hs, hc s hs⟩
  have h0 := HasFDerivWithinAt.comp_hasDerivWithinAt t hF hcurve hm
  have h : HasDerivAt (fun s => k s (c s)) _ t := h0.hasDerivAt (hJ.mem_nhds ht)
  refine h.congr_deriv ?_
  have e : ((1 : ℝ), c') = (1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + c' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul, ← hk.Dt_eq hJ ht (hc t ht), ← hk.Dx_eq ht (hc t ht),
    smul_eq_mul, smul_eq_mul, one_mul, mul_comm c']

/-- Composition with a smooth map of the strip into itself preserving `t`. -/
theorem Smooth.comp (hk : Smooth J k) {c : ℝ → ℝ → ℝ} (hc : Smooth J c)
    (hmaps : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, c t x ∈ Icc (0 : ℝ) 1) :
    Smooth J (fun t x => k t (c t x)) :=
  ContDiffOn.comp (g := fun p : ℝ × ℝ => k p.1 p.2) hk (contDiffOn_fst.prodMk hc)
    fun p hp => ⟨hp.1, hmaps p.1 hp.1 p.2 hp.2⟩

end Partial

/-! ### Differentiability from partial derivatives -/

/-- A function on the strip with a partial derivative in `x` that is continuous
at `p`, and a partial derivative in `t` at `p`, is differentiable at `p` within
the strip. -/
theorem hasFDerivWithinAt_of_partials {J : Set ℝ} {F Fx : ℝ → ℝ → ℝ} {Ft : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ J ×ˢ Icc (0 : ℝ) 1)
    (hx : ∀ q ∈ J ×ˢ Icc (0 : ℝ) 1, HasDerivWithinAt (F q.1) (Fx q.1 q.2) (Icc 0 1) q.2)
    (hc : ContinuousWithinAt (fun q : ℝ × ℝ => Fx q.1 q.2) (J ×ˢ Icc (0 : ℝ) 1) p)
    (ht : HasDerivAt (fun s => F s p.2) Ft p.1) :
    HasFDerivWithinAt (fun q : ℝ × ℝ => F q.1 q.2)
      (Ft • ContinuousLinearMap.fst ℝ ℝ ℝ + Fx p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (J ×ˢ Icc (0 : ℝ) 1) p := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have h1 := Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 ht) hε2
  have h1' : ∀ᶠ q : ℝ × ℝ in 𝓝[J ×ˢ Icc (0 : ℝ) 1] p,
      ‖F q.1 p.2 - F p.1 p.2 - (q.1 - p.1) • Ft‖ ≤ ε / 2 * ‖q.1 - p.1‖ :=
    (continuous_fst.continuousAt.eventually h1).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc (ε / 2) hε2
  filter_upwards [h1', eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds p hδ)] with q hq1 hqS hqd
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hqd
  have hconv : Convex ℝ (Icc (0 : ℝ) 1 ∩ Metric.ball p.2 δ) :=
    (convex_Icc 0 1).inter (convex_ball p.2 δ)
  have hder : ∀ y ∈ Icc (0 : ℝ) 1 ∩ Metric.ball p.2 δ,
      HasDerivWithinAt (fun y => F q.1 y - Fx p.1 p.2 * y) (Fx q.1 y - Fx p.1 p.2)
        (Icc (0 : ℝ) 1 ∩ Metric.ball p.2 δ) y := by
    intro y hy
    have h := (hx (q.1, y) ⟨hqS.1, hy.1⟩).mono (inter_subset_left (t := Metric.ball p.2 δ))
    have h' : HasDerivWithinAt (fun y => F q.1 y - Fx p.1 p.2 * y)
        (Fx q.1 y - Fx p.1 p.2 * 1) (Icc (0 : ℝ) 1 ∩ Metric.ball p.2 δ) y :=
      h.sub ((hasDerivWithinAt_id y _).const_mul (Fx p.1 p.2))
    rwa [mul_one] at h'
  have hbound : ∀ y ∈ Icc (0 : ℝ) 1 ∩ Metric.ball p.2 δ, ‖Fx q.1 y - Fx p.1 p.2‖ ≤ ε / 2 := by
    intro y hy
    have hd : dist ((q.1, y) : ℝ × ℝ) p < δ := by
      rw [Prod.dist_eq]
      exact max_lt hqd.1 (Metric.mem_ball.1 hy.2)
    have h := hδc (x := (q.1, y)) ⟨hqS.1, hy.1⟩ hd
    rw [Real.dist_eq] at h
    exact h.le
  have hmv := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (x := p.2) (y := q.2) ⟨hp.2, Metric.mem_ball_self hδ⟩ ⟨hqS.2, Metric.mem_ball.2 hqd.2⟩
  show ‖F q.1 q.2 - F p.1 p.2 - (Ft * (q.1 - p.1) + Fx p.1 p.2 * (q.2 - p.2))‖ ≤ ε * ‖q - p‖
  have e : F q.1 q.2 - F p.1 p.2 - (Ft * (q.1 - p.1) + Fx p.1 p.2 * (q.2 - p.2))
      = ((F q.1 q.2 - Fx p.1 p.2 * q.2) - (F q.1 p.2 - Fx p.1 p.2 * p.2))
        + (F q.1 p.2 - F p.1 p.2 - (q.1 - p.1) • Ft) := by
    simp only [smul_eq_mul]
    ring
  rw [e]
  calc ‖((F q.1 q.2 - Fx p.1 p.2 * q.2) - (F q.1 p.2 - Fx p.1 p.2 * p.2))
        + (F q.1 p.2 - F p.1 p.2 - (q.1 - p.1) • Ft)‖
      ≤ ‖(F q.1 q.2 - Fx p.1 p.2 * q.2) - (F q.1 p.2 - Fx p.1 p.2 * p.2)‖
        + ‖F q.1 p.2 - F p.1 p.2 - (q.1 - p.1) • Ft‖ := norm_add_le _ _
    _ ≤ ε / 2 * ‖q.2 - p.2‖ + ε / 2 * ‖q.1 - p.1‖ := add_le_add hmv hq1
    _ ≤ ε / 2 * ‖q - p‖ + ε / 2 * ‖q - p‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_snd_le (q - p)) hε2.le)
          (mul_le_mul_of_nonneg_left (norm_fst_le (q - p)) hε2.le)
    _ = ε * ‖q - p‖ := by ring

/-! ### The primitive in `x` -/

section Primitive

variable {J : Set ℝ} {k : ℝ → ℝ → ℝ} {t x : ℝ}

theorem uIcc_one_subset (hx : x ∈ Icc (0 : ℝ) 1) : uIcc (1 : ℝ) x ⊆ Icc 0 1 := by
  rw [uIcc_of_ge hx.2]
  exact Icc_subset_Icc_left hx.1

theorem uIoc_one_subset (hx : x ∈ Icc (0 : ℝ) 1) : Ι (1 : ℝ) x ⊆ Icc 0 1 :=
  fun _ hy => uIcc_one_subset hx (uIoc_subset_uIcc hy)

theorem Smooth.intervalIntegrable (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (k t) volume 1 x :=
  ((hk.continuousOn_x ht).mono (uIcc_one_subset hx)).intervalIntegrable

/-- `∂_x ∫_1^x k = k`. -/
theorem Smooth.hasDerivWithinAt_Jx (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (Jx k t) (k t x) (Icc 0 1) x := by
  have hc := hk.continuousOn_x ht
  have : Fact (x ∈ Icc (0 : ℝ) 1) := ⟨hx⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (hk.intervalIntegrable ht hx)
    (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hc x hx)

/-- `∂_t ∫_1^x k = ∫_1^x ∂_t k`. -/
theorem Smooth.hasDerivAt_Jx (hJ : IsOpen J) (hk : Smooth J k) (ht : t ∈ J)
    (hx : x ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun s => Jx k s x) (Jx (Dt k) t x) t := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJ t ht
  have hsub : Icc (t - r / 2) (t + r / 2) ⊆ J := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hK : IsCompact (Icc (t - r / 2) (t + r / 2) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hdt : Smooth J (Dt k) := hk.dt hJ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((ContDiffOn.continuousOn hdt).mono (prod_mono hsub subset_rfl))
  have hnhds : Icc (t - r / 2) (t + r / 2) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 1) (b := x) (F := fun s y => k s y) (F' := fun s y => Dt k s y) (x₀ := t)
    (bound := fun _ => C) hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hJ.mem_nhds ht] with s hs
    exact ((hk.continuousOn_x hs).mono (uIoc_one_subset hx)).aestronglyMeasurable
      measurableSet_uIoc
  · exact hk.intervalIntegrable ht hx
  · exact ((hdt.continuousOn_x ht).mono (uIoc_one_subset hx)).aestronglyMeasurable
      measurableSet_uIoc
  · exact Eventually.of_forall fun y hy s hs => hC (s, y) ⟨hs, uIoc_one_subset hx hy⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun y hy s hs =>
      hk.hasDerivAt_t hJ (hsub hs) (uIoc_one_subset hx hy)

/-- The primitive in `x` is differentiable within the strip. -/
theorem Smooth.hasFDerivWithinAt_Jx (hJ : IsOpen J) (hk : Smooth J k) {p : ℝ × ℝ}
    (hp : p ∈ J ×ˢ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun q : ℝ × ℝ => Jx k q.1 q.2)
      (Jx (Dt k) p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
        + k p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) (J ×ˢ Icc (0 : ℝ) 1) p :=
  hasFDerivWithinAt_of_partials (F := Jx k) (Fx := k) hp
    (fun q hq => hk.hasDerivWithinAt_Jx hq.1 hq.2) (ContDiffOn.continuousOn hk p hp)
    (hk.hasDerivAt_Jx hJ hp.1 hp.2)

/-- The primitive in `x` of a smooth function is smooth on the strip. -/
theorem Smooth.jx (hJ : IsOpen J) (hk : Smooth J k) : Smooth J (Jx k) := by
  have hS := uniqueDiffOn_strip hJ
  have main : ∀ n : ℕ, ∀ k : ℝ → ℝ → ℝ, Smooth J k →
      ContDiffOn ℝ n (fun p : ℝ × ℝ => Jx k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have h0 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => Jx k p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
        contDiffOn_zero.2 fun p hp => (hk.hasFDerivWithinAt_Jx hJ hp).continuousWithinAt
      exact_mod_cast h0
    | succ n ih =>
      intro k hk
      rw [Nat.cast_add_one, contDiffOn_succ_iff_fderivWithin hS]
      refine ⟨fun p hp => (hk.hasFDerivWithinAt_Jx hJ hp).differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
          Jx (Dt k) p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
            + k p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) (J ×ˢ Icc (0 : ℝ) 1) :=
        ((ih (Dt k) (hk.dt hJ)).smul contDiffOn_const).add
          ((contDiffOn_infty.1 hk n).smul contDiffOn_const)
      exact h1.congr fun p hp => (hk.hasFDerivWithinAt_Jx hJ hp).fderivWithin (hS p hp)
  exact contDiffOn_infty.2 fun n => main n k hk

theorem Jx_one (k : ℝ → ℝ → ℝ) (t : ℝ) : Jx k t 1 = 0 := by
  simp [Jx]

/-- The fundamental theorem of calculus on the strip: `∫_1^x ∂_x k = k(x) - k(1)`. -/
theorem Smooth.Jx_Dx (hJ : IsOpen J) (hk : Smooth J k) (ht : t ∈ J) (hx : x ∈ Icc (0 : ℝ) 1) :
    Jx (Dx k) t x = k t x - k t 1 := by
  have hder : ∀ y ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y => Jx (Dx k) t y - k t y) 0 (Icc 0 1) y := by
    intro y hy
    have h : HasDerivWithinAt (fun y => Jx (Dx k) t y - k t y) (Dx k t y - Dx k t y)
        (Icc 0 1) y := ((hk.dx hJ).hasDerivWithinAt_Jx ht hy).sub (hk.hasDerivWithinAt_x ht hy)
    rwa [sub_self] at h
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hder
    (fun y _ => by simp) (x := 1) (y := x) ⟨zero_le_one, le_rfl⟩ hx
  rw [zero_mul, norm_le_zero_iff, Jx_one] at h
  linarith

end Primitive

/-! ### Functions of one variable -/

section OneVariable

variable {J : Set ℝ} {k : ℝ → ℝ → ℝ} {x : ℝ}

theorem Smooth.slice_t (hk : Smooth J k) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ ∞ (fun s => k s x) J :=
  ContDiffOn.comp (g := fun p : ℝ × ℝ => k p.1 p.2) hk (contDiffOn_id.prodMk contDiffOn_const)
    fun s hs => ⟨hs, hx⟩

theorem smooth_of_t {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g J) : Smooth J (fun t _ => g t) :=
  ContDiffOn.comp hg contDiffOn_fst fun _ hp => hp.1

theorem smooth_of_x {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Icc 0 1)) :
    Smooth J (fun _ x => g x) :=
  ContDiffOn.comp hg contDiffOn_snd fun _ hp => hp.2

/-- The primitive in time of a continuous function on an open interval. -/
theorem hasDerivAt_primitive (hJ : IsOpen J) (hJc : J.OrdConnected) {g : ℝ → ℝ}
    (hg : ContinuousOn g J) {t₀ t : ℝ} (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    HasDerivAt (fun t => ∫ s in t₀..t, g s) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hg.mono (hJc.uIcc_subset ht₀ ht)).intervalIntegrable)
    (hg.stronglyMeasurableAtFilter hJ t ht) (hg.continuousAt (hJ.mem_nhds ht))

theorem contDiffOn_primitive (hJ : IsOpen J) (hJc : J.OrdConnected) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ContDiffOn ℝ ∞ (fun t => ∫ s in t₀..t, g s) J := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen hJ]
  refine ⟨fun t ht => (hasDerivAt_primitive hJ hJc hg.continuousOn ht₀
    ht).differentiableAt.differentiableWithinAt, ?_⟩
  exact hg.congr fun t ht => (hasDerivAt_primitive hJ hJc hg.continuousOn ht₀ ht).deriv

end OneVariable

/-! ### Inverses -/

/-- A continuous right inverse `g` of a smooth map `f` with invertible
derivatives, on a set with unique derivatives that `g` preserves, is smooth. -/
theorem contDiffOn_of_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : E → E} {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContinuousOn g S) (hmaps : MapsTo g S S)
    (hfg : ∀ y ∈ S, f (g y) = y)
    (hinv : ∀ x ∈ S, ∃ e : E ≃L[ℝ] E, HasFDerivWithinAt f (e : E →L[ℝ] E) S x) :
    ContDiffOn ℝ ∞ g S := by
  have hder : ∀ y ∈ S, ∃ e : E ≃L[ℝ] E, HasFDerivWithinAt f (e : E →L[ℝ] E) S (g y) ∧
      HasFDerivWithinAt g (e.symm : E →L[ℝ] E) S y := by
    intro y hy
    obtain ⟨e, he⟩ := hinv (g y) (hmaps hy)
    refine ⟨e, he, ?_⟩
    refine HasFDerivWithinAt.of_local_left_inverse ?_ he hy ?_
    · exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hg y hy)
        (eventually_mem_nhdsWithin.mono fun z hz => hmaps hz)
    · filter_upwards [self_mem_nhdsWithin] with z hz using hfg z hz
  have hfd : ∀ y ∈ S, fderivWithin ℝ g S y
      = ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) := by
    intro y hy
    obtain ⟨e, he, hge⟩ := hder y hy
    rw [hge.fderivWithin (hS y hy), he.fderivWithin (hS _ (hmaps hy)),
      ContinuousLinearMap.inverse_equiv]
  have hfinv : ∀ n : ℕ, ContDiffOn ℝ n
      (fun x => ContinuousLinearMap.inverse (fderivWithin ℝ f S x)) S := by
    intro n x hx
    obtain ⟨e, he⟩ := hinv x hx
    have h1 : ContDiffWithinAt ℝ n (fderivWithin ℝ f S) S x :=
      ((contDiffOn_infty.1 hf (n + 1)).fderivWithin hS (Nat.cast_add_one n).ge) x hx
    have h2 : ContDiffAt ℝ n ContinuousLinearMap.inverse (fderivWithin ℝ f S x) := by
      rw [he.fderivWithin (hS x hx)]
      exact contDiffAt_map_inverse e
    exact h2.comp_contDiffWithinAt x h1
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    have h0 : ContDiffOn ℝ 0 g S := contDiffOn_zero.2 hg
    exact_mod_cast h0
  | succ n ih =>
    rw [Nat.cast_add_one, contDiffOn_succ_iff_fderivWithin hS]
    refine ⟨fun y hy => ?_, fun h => absurd h (by simp), ?_⟩
    · obtain ⟨e, -, hge⟩ := hder y hy
      exact hge.differentiableWithinAt
    · exact ((hfinv n).comp ih hmaps).congr fun y hy => hfd y hy

section Inverse

variable {J : Set ℝ} {Ξ X : ℝ → ℝ → ℝ}

/-- The fibrewise inverse of a family of increasing maps of `[0, 1]` that is
continuous in the parameter is continuous on the strip. -/
theorem continuousOn_inverse (hcont : ∀ y ∈ Icc (0 : ℝ) 1, ContinuousOn (fun t => Ξ t y) J)
    (hmono : ∀ t ∈ J, StrictMonoOn (Ξ t) (Icc 0 1))
    (hX : ∀ t ∈ J, ∀ ξ ∈ Icc (0 : ℝ) 1, X t ξ ∈ Icc (0 : ℝ) 1 ∧ Ξ t (X t ξ) = ξ) :
    ContinuousOn (fun p : ℝ × ℝ => X p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp
  have hXp := hX p.1 hp.1 p.2 hp.2
  have hslice : ∀ y ∈ Icc (0 : ℝ) 1,
      Tendsto (fun q : ℝ × ℝ => Ξ q.1 y) (𝓝[J ×ˢ Icc (0 : ℝ) 1] p) (𝓝 (Ξ p.1 y)) := by
    intro y hy
    have h := (hcont y hy p.1 hp.1).comp (continuousWithinAt_fst (s := J ×ˢ Icc (0 : ℝ) 1))
      (fun q hq => (hq : q ∈ J ×ˢ Icc (0 : ℝ) 1).1)
    exact h
  have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝[J ×ˢ Icc (0 : ℝ) 1] p) (𝓝 p.2) :=
    continuous_snd.continuousWithinAt
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · by_cases ha0 : a < 0
    · filter_upwards [eventually_mem_nhdsWithin] with q hq
      exact lt_of_lt_of_le ha0 (hX q.1 hq.1 q.2 hq.2).1.1
    · have haI : a ∈ Icc (0 : ℝ) 1 := ⟨not_lt.1 ha0, ha.le.trans hXp.1.2⟩
      have hlt : Ξ p.1 a < p.2 := by
        have h := hmono p.1 hp.1 haI hXp.1 ha
        rwa [hXp.2] at h
      filter_upwards [(hslice a haI).eventually_lt hsnd hlt, eventually_mem_nhdsWithin]
        with q hq hqS
      have hXq := hX q.1 hqS.1 q.2 hqS.2
      by_contra hcon
      have hle : Ξ q.1 (X q.1 q.2) ≤ Ξ q.1 a :=
        (hmono q.1 hqS.1).monotoneOn hXq.1 haI (not_lt.1 hcon)
      rw [hXq.2] at hle
      exact absurd hq (not_lt.2 hle)
  · by_cases ha1 : 1 < a
    · filter_upwards [eventually_mem_nhdsWithin] with q hq
      exact lt_of_le_of_lt (hX q.1 hq.1 q.2 hq.2).1.2 ha1
    · have haI : a ∈ Icc (0 : ℝ) 1 := ⟨hXp.1.1.trans ha.le, not_lt.1 ha1⟩
      have hlt : p.2 < Ξ p.1 a := by
        have h := hmono p.1 hp.1 hXp.1 haI ha
        rwa [hXp.2] at h
      filter_upwards [hsnd.eventually_lt (hslice a haI) hlt, eventually_mem_nhdsWithin]
        with q hq hqS
      have hXq := hX q.1 hqS.1 q.2 hqS.2
      by_contra hcon
      have hle : Ξ q.1 a ≤ Ξ q.1 (X q.1 q.2) :=
        (hmono q.1 hqS.1).monotoneOn haI hXq.1 (not_lt.1 hcon)
      rw [hXq.2] at hle
      exact absurd hq (not_lt.2 hle)

theorem Smooth.strictMonoOn (hΞ : Smooth J Ξ) (hpos : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, 0 < Dx Ξ t x)
    {t : ℝ} (ht : t ∈ J) : StrictMonoOn (Ξ t) (Icc 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) (hΞ.continuousOn_x ht) fun x hx => ?_
  rw [interior_Icc] at hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have h := (hΞ.hasDerivWithinAt_x ht hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  rw [h.deriv]
  exact hpos t ht x hx'

/-- **The inverse function theorem on the strip.** The fibrewise inverse of a
smooth family of maps of `[0, 1]` onto itself with positive derivative is
smooth on the closed strip. -/
theorem smooth_inverse (hJ : IsOpen J) (hΞ : Smooth J Ξ)
    (hpos : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, 0 < Dx Ξ t x)
    (hX : ∀ t ∈ J, ∀ ξ ∈ Icc (0 : ℝ) 1, X t ξ ∈ Icc (0 : ℝ) 1 ∧ Ξ t (X t ξ) = ξ) :
    Smooth J X := by
  have hS := uniqueDiffOn_strip hJ
  have hcontX : ContinuousOn (fun p : ℝ × ℝ => X p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_inverse (fun y hy => hΞ.continuousOn_t hJ hy)
      (fun t ht => hΞ.strictMonoOn hpos ht) hX
  have hfS : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ((p.1, Ξ p.1 p.2) : ℝ × ℝ))
      (J ×ˢ Icc (0 : ℝ) 1) := contDiffOn_fst.prodMk hΞ
  have hgc : ContinuousOn (fun p : ℝ × ℝ => ((p.1, X p.1 p.2) : ℝ × ℝ))
      (J ×ˢ Icc (0 : ℝ) 1) := continuousOn_fst.prodMk hcontX
  have hmaps : MapsTo (fun p : ℝ × ℝ => ((p.1, X p.1 p.2) : ℝ × ℝ)) (J ×ˢ Icc (0 : ℝ) 1)
      (J ×ˢ Icc (0 : ℝ) 1) := fun p hp => ⟨hp.1, (hX p.1 hp.1 p.2 hp.2).1⟩
  have hfg : ∀ p ∈ J ×ˢ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => ((p.1, Ξ p.1 p.2) : ℝ × ℝ)) ((p.1, X p.1 p.2) : ℝ × ℝ) = p :=
    fun p hp => Prod.ext rfl (hX p.1 hp.1 p.2 hp.2).2
  have hinv : ∀ p ∈ J ×ˢ Icc (0 : ℝ) 1, ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivWithinAt (fun p : ℝ × ℝ => ((p.1, Ξ p.1 p.2) : ℝ × ℝ))
        (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) (J ×ˢ Icc (0 : ℝ) 1) p := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hLd := hΞ.hasFDerivWithinAt' ht hx
    set L := fderivWithin ℝ (fun p : ℝ × ℝ => Ξ p.1 p.2) (J ×ˢ Icc (0 : ℝ) 1) (t, x) with hL
    have hc : L (0, 1) ≠ 0 := by
      rw [hL, ← hΞ.Dx_eq ht hx]
      exact (hpos t ht x hx).ne'
    have hlin : ∀ z : ℝ × ℝ, L z = z.1 * L (1, 0) + z.2 * L (0, 1) := by
      intro z
      have e : z = z.1 • ((1 : ℝ), (0 : ℝ)) + z.2 • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      conv_lhs => rw [e]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    let A : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod L
    let B : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((L (0, 1))⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ - L (1, 0) • ContinuousLinearMap.fst ℝ ℝ ℝ))
    have hA : ∀ z, A z = (z.1, L z) := fun _ => rfl
    have hB : ∀ z, B z = (z.1, (L (0, 1))⁻¹ * (z.2 - L (1, 0) * z.1)) := fun _ => rfl
    have h1 : Function.LeftInverse B A := by
      intro z
      rw [hA, hB]
      refine Prod.ext rfl ?_
      show (L (0, 1))⁻¹ * (L z - L (1, 0) * z.1) = z.2
      have e : L z - L (1, 0) * z.1 = L (0, 1) * z.2 := by
        rw [hlin z]
        ring
      rw [e, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have h2 : Function.RightInverse B A := by
      intro z
      rw [hB, hA]
      refine Prod.ext rfl ?_
      show L (z.1, (L (0, 1))⁻¹ * (z.2 - L (1, 0) * z.1)) = z.2
      rw [hlin]
      show z.1 * L (1, 0) + (L (0, 1))⁻¹ * (z.2 - L (1, 0) * z.1) * L (0, 1) = z.2
      rw [mul_comm ((L (0, 1))⁻¹), mul_assoc, inv_mul_cancel₀ hc, mul_one]
      ring
    refine ⟨ContinuousLinearEquiv.equivOfInverse A B h1 h2, ?_⟩
    have hd : HasFDerivWithinAt (fun p : ℝ × ℝ => ((p.1, Ξ p.1 p.2) : ℝ × ℝ)) A
        (J ×ˢ Icc (0 : ℝ) 1) (t, x) := hasFDerivWithinAt_fst.prodMk hLd
    exact hd.congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  exact (contDiffOn_of_inverse hS hfS hgc hmaps hfg hinv).snd

/-- The `x`-derivative of the inverse. -/
theorem inverse_Dx (hJ : IsOpen J) (hΞ : Smooth J Ξ)
    (hpos : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, 0 < Dx Ξ t x)
    (hX : ∀ t ∈ J, ∀ ξ ∈ Icc (0 : ℝ) 1, X t ξ ∈ Icc (0 : ℝ) 1 ∧ Ξ t (X t ξ) = ξ)
    {t ξ : ℝ} (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Dx X t ξ = (Dx Ξ t (X t ξ))⁻¹ := by
  have hXs := smooth_inverse hJ hΞ hpos hX
  have h1 := hXs.hasDerivWithinAt_x ht hξ
  have h2 := hΞ.hasDerivWithinAt_x ht (hX t ht ξ hξ).1
  have h3 : HasDerivWithinAt (fun y => Ξ t (X t y)) (Dx Ξ t (X t ξ) * Dx X t ξ) (Icc 0 1) ξ :=
    h2.comp ξ h1 fun y hy => (hX t ht y hy).1
  have h4 : HasDerivWithinAt (fun y => Ξ t (X t y)) 1 (Icc 0 1) ξ :=
    (hasDerivWithinAt_id ξ _).congr (fun y hy => (hX t ht y hy).2) (hX t ht ξ hξ).2
  have h5 := (uniqueDiffOn_Icc_zero_one ξ hξ).eq_deriv _ h3 h4
  exact eq_inv_of_mul_eq_one_right h5

/-- The `t`-derivative of the inverse. -/
theorem inverse_Dt (hJ : IsOpen J) (hΞ : Smooth J Ξ)
    (hpos : ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) 1, 0 < Dx Ξ t x)
    (hX : ∀ t ∈ J, ∀ ξ ∈ Icc (0 : ℝ) 1, X t ξ ∈ Icc (0 : ℝ) 1 ∧ Ξ t (X t ξ) = ξ)
    {t ξ : ℝ} (ht : t ∈ J) (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    Dt X t ξ = -(Dt Ξ t (X t ξ)) / Dx Ξ t (X t ξ) := by
  have hXs := smooth_inverse hJ hΞ hpos hX
  have h1 := hXs.hasDerivAt_t hJ ht hξ
  have h2 := hΞ.hasDerivAt_comp hJ ht (fun s hs => (hX s hs ξ hξ).1) h1
  have h3 : HasDerivAt (fun s => Ξ s (X s ξ)) 0 t :=
    (hasDerivAt_const t ξ).congr_of_eventuallyEq
      (by filter_upwards [hJ.mem_nhds ht] with s hs using (hX s hs ξ hξ).2)
  have h4 := h2.unique h3
  have hne : Dx Ξ t (X t ξ) ≠ 0 := (hpos t ht _ (hX t ht ξ hξ).1).ne'
  field_simp
  linarith

end Inverse

end Calabi.Strip
