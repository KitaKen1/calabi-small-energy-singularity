import Calabi.Geometry.Legendre

/-!
# The potential on `CP⁷`

For a smooth positive solution `H` of the momentum equation, the function

  `Fhat H t₀ t v = Pfun t (Xinv t (ξ(v)))`,   `ξ(v) = 1 - |v₀|² / |v|²`,

is the Kähler potential, relative to the Fubini–Study metric, of the metric of
`H(t)`. Here `ξ` is the momentum of the Fubini–Study metric: a smooth function
on `CP⁷` with values in `[0, 1]`, equal to `0` at the point orbit and to `1` on
the divisor at infinity. Smoothness of `Fhat` on `ℂ⁸ ∖ {0}` therefore follows
from smoothness of `Pfun ∘ Xinv` on the closed strip.

* `Flow.contDiffOn_Fhat`: `Fhat` is smooth in `(t, v)`;
* `Flow.hasDerivAt_Fhat`: `∂_t Fhat = -K(H)`;
* `Flow.scal_Fhat`: on the affine chart the scalar curvature is `56 - K(H)`,
  so that `∂_t Fhat = S - 56`: the Calabi flow.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

open Calabi.Legendre Calabi.Strip Calabi.Radial

/-- `η = |v₀|² / |v|²`. -/
noncomputable def eta (v : Hom) : ℝ := ‖v 0‖ ^ 2 / ∑ i, ‖v i‖ ^ 2

/-- The Fubini–Study momentum `ξ = 1 - |v₀|² / |v|²` of a point of `CP⁷`. -/
noncomputable def xi (v : Hom) : ℝ := 1 - eta v

theorem sum_norm_sq_pos {v : Hom} (hv : v ≠ 0) : 0 < ∑ i, ‖v i‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.2 hi) 2⟩

theorem eta_mem (v : Hom) : eta v ∈ Icc (0 : ℝ) 1 := by
  unfold eta
  refine ⟨div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _), ?_⟩
  refine div_le_one_of_le₀ ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _)
  exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ 0)

theorem xi_mem (v : Hom) : xi v ∈ Icc (0 : ℝ) 1 := by
  have h := eta_mem v
  unfold xi
  constructor <;> linarith [h.1, h.2]

theorem eta_smul {c : ℂ} (hc : c ≠ 0) (v : Hom) : eta (c • v) = eta v := by
  unfold eta
  have h : ∀ i, ‖(c • v) i‖ ^ 2 = ‖c‖ ^ 2 * ‖v i‖ ^ 2 := fun i => by
    rw [Pi.smul_apply, norm_smul, mul_pow]
  simp only [h, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc))]

theorem xi_smul {c : ℂ} (hc : c ≠ 0) (v : Hom) : xi (c • v) = xi v := by
  unfold xi
  rw [eta_smul hc]

theorem contDiffOn_eta : ContDiffOn ℝ ∞ eta {v : Hom | v ≠ 0} := by
  have h : ∀ i : Fin 8, ContDiff ℝ ∞ fun v : Hom => ‖v i‖ ^ 2 := fun i =>
    (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ i)
  have hsum : ContDiff ℝ ∞ fun v : Hom => ∑ i, ‖v i‖ ^ 2 := ContDiff.sum fun i _ => h i
  exact (h 0).contDiffOn.div hsum.contDiffOn fun v hv => (sum_norm_sq_pos hv).ne'

theorem contDiffOn_xi : ContDiffOn ℝ ∞ xi {v : Hom | v ≠ 0} :=
  contDiffOn_const.sub contDiffOn_eta

/-! ### The charts -/

theorem sum_chart (j : Fin 8) (Z : Aff) : ∑ i, ‖chart j Z i‖ ^ 2 = 1 + ‖Z‖ ^ 2 := by
  rw [Fin.sum_univ_succAbove _ j, EuclideanSpace.norm_sq_eq]
  simp [chart]

theorem chart_ne_zero (j : Fin 8) (Z : Aff) : chart j Z ≠ 0 := by
  intro h
  have h1 := sum_chart j Z
  rw [h] at h1
  have h2 : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  simp at h1
  linarith

theorem chart_zero_zero (Z : Aff) : chart 0 Z 0 = 1 := by
  simp [chart]

theorem chart_succ_zero {j : Fin 8} (hj : j ≠ 0) (Z : Aff) : chart j Z 0 = Z 0 := by
  have h := Fin.insertNth_apply_succAbove (α := fun _ => ℂ) j (1 : ℂ) (Z : Fin 7 → ℂ) 0
  rwa [Fin.succAbove_ne_zero_zero hj] at h

theorem xi_chart_zero (Z : Aff) : xi (chart 0 Z) = ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2) := by
  unfold xi eta
  rw [sum_chart, chart_zero_zero, norm_one, one_pow]
  have h : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem xi_chart_succ {j : Fin 8} (hj : j ≠ 0) (Z : Aff) :
    xi (chart j Z) = 1 - ‖Z 0‖ ^ 2 / (1 + ‖Z‖ ^ 2) := by
  unfold xi eta
  rw [sum_chart, chart_succ_zero hj]

/-! ### The potential -/

/-- The Kähler potential of the metric of `H(t)` relative to the Fubini–Study
metric, as a function of homogeneous coordinates. -/
noncomputable def Fhat (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) (v : Hom) : ℝ :=
  Pfun H t₀ t (Xinv H t₀ t (xi v))

theorem Fhat_smul (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) {c : ℂ} (hc : c ≠ 0) (v : Hom) :
    Fhat H t₀ t (c • v) = Fhat H t₀ t v := by
  unfold Fhat
  rw [xi_smul hc]

theorem pot_Fhat_zero (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) :
    pot (Fhat H t₀ t) 0 = fun Z : Aff => phi H t₀ t (‖Z‖ ^ 2) := by
  funext Z
  unfold pot Fhat phi xq
  rw [xi_chart_zero]

theorem isU7Invariant_Fhat (H : ℝ → ℝ → ℝ) (t₀ t : ℝ) : IsU7Invariant (Fhat H t₀ t) := by
  intro U Z
  unfold Fhat
  rw [xi_chart_zero, xi_chart_zero, LinearIsometryEquiv.norm_map]

end Calabi.Geometry

namespace Calabi.Legendre.Flow

open Calabi.Geometry Calabi.Strip Calabi.Radial

variable {J : Set ℝ} {H : ℝ → ℝ → ℝ} {t₀ t : ℝ}

/-- The potential is smooth in time and in the point of `CP⁷`. -/
theorem contDiffOn_Fhat (hF : Flow J H) (ht₀ : t₀ ∈ J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Hom => Fhat H t₀ p.1 p.2) (J ×ˢ {v : Hom | v ≠ 0}) := by
  have hΨ := (hF.smooth_P ht₀).comp (hF.smooth_Xinv ht₀)
    fun t ht ξ hξ => (hF.hX ht₀ ht hξ).1
  have hxi : ContDiffOn ℝ ∞ (fun p : ℝ × Hom => xi p.2) (J ×ˢ {v : Hom | v ≠ 0}) :=
    contDiffOn_xi.comp contDiffOn_snd fun p hp => hp.2
  have hpair : ContDiffOn ℝ ∞ (fun p : ℝ × Hom => ((p.1, xi p.2) : ℝ × ℝ))
      (J ×ˢ {v : Hom | v ≠ 0}) := contDiffOn_fst.prodMk hxi
  have h := ContDiffOn.comp hΨ hpair fun p hp => ⟨hp.1, xi_mem p.2⟩
  show ContDiffOn ℝ ∞ (fun p : ℝ × Hom => Pfun H t₀ p.1 (Xinv H t₀ p.1 (xi p.2))) _
  exact h

theorem isSmoothCP_Fhat (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    IsSmoothCP (Fhat H t₀ t) := by
  refine ⟨?_, fun c v hc => Fhat_smul H t₀ t hc v⟩
  have hpair : ContDiffOn ℝ ∞ (fun v : Hom => ((t, v) : ℝ × Hom)) {v : Hom | v ≠ 0} :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := ContDiffOn.comp (hF.contDiffOn_Fhat ht₀) hpair fun v hv => ⟨ht, hv⟩
  exact h

/-- `∂_t Fhat = -K(H)` at a fixed point of `CP⁷`. -/
theorem hasDerivAt_Fhat (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (v : Hom) :
    HasDerivAt (fun s => Fhat H t₀ s v) (-(KH H t (Xinv H t₀ t (xi v)))) t :=
  hF.hasDerivAt_Psi ht₀ ht (xi_mem v)

/-- The scalar curvature of the metric of `H(t)` on the affine chart. -/
theorem scal_Fhat (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (Z : Aff) :
    scal (pot (Fhat H t₀ t) 0) Z = 56 - Kop (H t) (xq H t₀ t (‖Z‖ ^ 2)) := by
  rw [pot_Fhat_zero]
  exact (hF.momentumData ht₀ ht).scal_eq Z

/-- **The Calabi flow** on the affine chart: `∂_t Fhat = S - 56`. -/
theorem hasDerivAt_Fhat_chart (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (Z : Aff) :
    HasDerivAt (fun s => Fhat H t₀ s (chart 0 Z)) (scal (pot (Fhat H t₀ t) 0) Z - 56) t := by
  have h := hF.hasDerivAt_Fhat ht₀ ht (chart 0 Z)
  refine h.congr_deriv ?_
  rw [hF.scal_Fhat ht₀ ht, xi_chart_zero]
  unfold KH xq
  ring

/-- The scalar curvature at the point orbit: `S = 56 (1 - H(t, 0))`. -/
theorem scal_Fhat_origin (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    scal (pot (Fhat H t₀ t) 0) 0 = 56 * (1 - H t 0) := by
  rw [pot_Fhat_zero]
  exact (hF.momentumData ht₀ ht).scal_zero

/-- The metric of `H(t)` is positive on the affine chart. -/
theorem levi_Fhat_zero_pos (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) (Z : Aff) {a : Aff}
    (ha : a ≠ 0) : 0 < (levi (pot (Fhat H t₀ t) 0) Z a a).re := by
  rw [pot_Fhat_zero]
  exact (hF.momentumData ht₀ ht).levi_pos Z ha

end Calabi.Legendre.Flow
