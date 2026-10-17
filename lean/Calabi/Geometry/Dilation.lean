import Calabi.Geometry.Gradient
import Calabi.Geometry.Volume
import Calabi.Geometry.ChartInfinity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The radial map that matches the momenta

Section 7.3 of the manuscript. For a radial metric described by `MomentumData`,
the map

  `θ(Z) = exp (a(ξ) / 2) Z`,   `ξ = ‖Z‖² / (1 + ‖Z‖²)`,

sends the point of Fubini–Study momentum `ξ` to the point of momentum `ξ` of
the metric (`xq_theta`). It is a bijection of `ℂ⁷` (`theta_bijective`), and

* `lintegral_theta`: it pushes the Fubini–Study volume to the volume of the
  metric: the Jacobian is `exp (7 a) / b` and the two volume densities are
  `(1 - ξ)⁸` and `(1 - ξ)⁸ b exp (-7 a)`;
* `quad_theta_le`: the pulled-back metric is at most `Λ` times the
  Fubini–Study metric, `Λ = max (1, 1 / b, b)`: in the momentum and angular
  coordinates the two metrics have the ratios `1`, `1 / b`, `b`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Calabi.Geometry

open Calabi.Radial Momentum

/-! ### A determinant -/

theorem det_smul_one_add_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ}
    (hc : c ≠ 0) (w v : ι → ℝ) :
    (c • (1 : Matrix ι ι ℝ) + Matrix.vecMulVec w v).det
      = c ^ Fintype.card ι * (1 + c⁻¹ * (v ⬝ᵥ w)) := by
  have e : c • (1 : Matrix ι ι ℝ) + Matrix.vecMulVec w v
      = c • (1 + Matrix.replicateCol Unit (c⁻¹ • w) * Matrix.replicateRow Unit v) := by
    rw [← Matrix.vecMulVec_eq Unit]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Pi.smul_apply]
    field_simp
  rw [e, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul]

/-- The determinant of `c + w ⊗ φ` on the real vector space `ℂ⁷`. -/
theorem det_smul_id_add_smulRight {c : ℝ} (hc : c ≠ 0) (φ : Aff →L[ℝ] ℝ) (w : Aff) :
    (c • ContinuousLinearMap.id ℝ Aff + φ.smulRight w).det = c ^ 14 * (1 + c⁻¹ * φ w) := by
  have hdet : (c • ContinuousLinearMap.id ℝ Aff + φ.smulRight w).det
      = LinearMap.det ((c • ContinuousLinearMap.id ℝ Aff + φ.smulRight w : Aff →L[ℝ] Aff)
        : Aff →ₗ[ℝ] Aff) := rfl
  have hd := LinearMap.det_toMatrix (Module.finBasis ℝ Aff)
    ((c • ContinuousLinearMap.id ℝ Aff + φ.smulRight w : Aff →L[ℝ] Aff) : Aff →ₗ[ℝ] Aff)
  have hcard : Fintype.card (Fin (Module.finrank ℝ Aff)) = 14 := by
    rw [Fintype.card_fin, finrank_aff]
  have hmat : LinearMap.toMatrix (Module.finBasis ℝ Aff) (Module.finBasis ℝ Aff)
      ((c • ContinuousLinearMap.id ℝ Aff + φ.smulRight w : Aff →L[ℝ] Aff) : Aff →ₗ[ℝ] Aff)
      = c • (1 : Matrix _ _ ℝ) + Matrix.vecMulVec
        (fun i => (Module.finBasis ℝ Aff).repr w i) (fun j => φ (Module.finBasis ℝ Aff j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [Matrix.vecMulVec_apply, Matrix.one_apply, Finsupp.single_apply, mul_comm, eq_comm]
  have hdot : (fun j => φ ((Module.finBasis ℝ Aff) j))
      ⬝ᵥ (fun i => (Module.finBasis ℝ Aff).repr w i) = φ w := by
    have hw := (Module.finBasis ℝ Aff).sum_repr w
    calc (fun j => φ ((Module.finBasis ℝ Aff) j)) ⬝ᵥ (fun i => (Module.finBasis ℝ Aff).repr w i)
        = ∑ i, (Module.finBasis ℝ Aff).repr w i * φ ((Module.finBasis ℝ Aff) i) := by
          simp [dotProduct, mul_comm]
      _ = φ (∑ i, (Module.finBasis ℝ Aff).repr w i • (Module.finBasis ℝ Aff) i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = φ w := by rw [hw]
  rw [hdet, ← hd, hmat, det_smul_one_add_vecMulVec hc, hcard, hdot]

/-! ### The map -/

/-- The radial factor `exp (a(ξ) / 2)`. -/
noncomputable def mfun (a : ℝ → ℝ) (q : ℝ) : ℝ := Real.exp (a (q / (1 + q)) / 2)

/-- The radial map matching the momenta. -/
noncomputable def theta (a : ℝ → ℝ) (Z : Aff) : Aff := mfun a (‖Z‖ ^ 2) • Z

theorem mfun_pos (a : ℝ → ℝ) (q : ℝ) : 0 < mfun a q := Real.exp_pos _

theorem mfun_sq (a : ℝ → ℝ) (q : ℝ) : mfun a q ^ 2 = Real.exp (a (q / (1 + q))) := by
  unfold mfun
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem xi_mem_Ico {q : ℝ} (hq : 0 ≤ q) : q / (1 + q) ∈ Ico (0 : ℝ) 1 := by
  have h1 : 0 < 1 + q := by linarith
  exact ⟨div_nonneg hq h1.le, (div_lt_one h1).2 (by linarith)⟩

theorem one_sub_xi {q : ℝ} (hq : 0 ≤ q) : 1 - q / (1 + q) = (1 + q)⁻¹ := by
  have h1 : (1 + q) ≠ 0 := by linarith
  field_simp
  ring

theorem norm_theta_sq (a : ℝ → ℝ) (Z : Aff) :
    ‖theta a Z‖ ^ 2 = Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) * ‖Z‖ ^ 2 := by
  unfold theta
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mfun_sq]

namespace MomentumData

variable {H a xq φ : ℝ → ℝ} (M : MomentumData H a xq φ)
  (hQ : ∀ x ∈ Ico (0 : ℝ) 1, xq (x * Real.exp (a x) / (1 - x)) = x)

include M

theorem hasDerivWithinAt_mfun {q : ℝ} (hq : 0 ≤ q) :
    HasDerivWithinAt (mfun a)
      (mfun a q * (-(H (q / (1 + q))) / bfun H (q / (1 + q)) * (1 / (1 + q) ^ 2) / 2))
      (Ici 0) q := by
  have h1q : (1 + q) ≠ 0 := by linarith
  have hmaps : MapsTo (fun q : ℝ => q / (1 + q)) (Ici 0) (Icc (0 : ℝ) 1) :=
    fun q' hq' => Ico_subset_Icc_self (xi_mem_Ico hq')
  have hξ : HasDerivWithinAt (fun q : ℝ => q / (1 + q)) (1 / (1 + q) ^ 2) (Ici 0) q := by
    have h : HasDerivAt (fun q : ℝ => q / (1 + q)) ((1 * (1 + q) - q * 1) / (1 + q) ^ 2) q :=
      (hasDerivAt_id q).fun_div ((hasDerivAt_id q).const_add 1) h1q
    refine (h.congr_deriv ?_).hasDerivWithinAt
    ring
  have h2 : HasDerivWithinAt (fun q : ℝ => a (q / (1 + q)))
      (-(H (q / (1 + q))) / bfun H (q / (1 + q)) * (1 / (1 + q) ^ 2)) (Ici 0) q :=
    (M.da _ (hmaps hq)).comp q hξ hmaps
  have h3 : HasDerivWithinAt (fun q : ℝ => a (q / (1 + q)) / 2)
      (-(H (q / (1 + q))) / bfun H (q / (1 + q)) * (1 / (1 + q) ^ 2) / 2) (Ici 0) q :=
    h2.div_const 2
  exact h3.exp

theorem hasFDerivAt_theta (Z : Aff) :
    HasFDerivAt (theta a) (mfun a (‖Z‖ ^ 2) • ContinuousLinearMap.id ℝ Aff
      + ((mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
          / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2))
        • ((2 : ℝ) • innerSL ℝ Z)).smulRight Z) Z := by
  have h1 := hasFDerivAt_radial (φ := mfun a) Z (M.hasDerivWithinAt_mfun (sq_nonneg ‖Z‖))
  exact h1.smul (hasFDerivAt_id Z)

/-- The Jacobian of `θ`: `exp (7 a) / b`. -/
theorem det_theta (Z : Aff) :
    (mfun a (‖Z‖ ^ 2) • ContinuousLinearMap.id ℝ Aff
      + ((mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
          / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2))
        • ((2 : ℝ) • innerSL ℝ Z)).smulRight Z).det
      = Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) ^ 7 / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have hm := (mfun_pos a (‖Z‖ ^ 2)).ne'
  have hb := (M.pos _ (Ico_subset_Icc_self (xi_mem_Ico hq))).ne'
  rw [det_smul_id_add_smulRight hm]
  have e1 : ((mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
      / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2))
      • ((2 : ℝ) • innerSL ℝ Z) : Aff →L[ℝ] ℝ) Z
      = mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
        / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2) * (2 * ‖Z‖ ^ 2) := by
    show _ * (2 * inner ℝ Z Z) = _
    rw [real_inner_self_eq_norm_sq]
  rw [e1]
  have e14 : mfun a (‖Z‖ ^ 2) ^ 14 = Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) ^ 7 := by
    rw [← mfun_sq, ← pow_mul]
  rw [e14]
  have hbdef : bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
      = 1 + ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2) * (1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
        * H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) := rfl
  have h1q : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
  generalize hbd : bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) = b at hb hbdef ⊢
  generalize H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) = h at hbdef ⊢
  generalize Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) = E
  generalize mfun a (‖Z‖ ^ 2) = m at hm ⊢
  generalize ‖Z‖ ^ 2 = q at h1q hbdef ⊢
  have hb' : b * (1 + q) ^ 2 = (1 + q) ^ 2 + q * h := by
    rw [hbdef]
    field_simp
    ring
  field_simp
  linear_combination E ^ 7 * hb'

include hQ

/-- `θ` matches the momenta. -/
theorem xq_theta (Z : Aff) : xq (‖theta a Z‖ ^ 2) = ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2) := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have h := hQ _ (xi_mem_Ico hq)
  have e : ‖theta a Z‖ ^ 2 = ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)
      * Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) / (1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) := by
    rw [norm_theta_sq, one_sub_xi hq]
    have h1q : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
    field_simp
  rw [e]
  exact h

theorem theta_injective : Function.Injective (theta a) := by
  intro Z₁ Z₂ h
  have h1 := M.xq_theta hQ Z₁
  have h2 := M.xq_theta hQ Z₂
  rw [h] at h1
  have hq : ‖Z₁‖ ^ 2 = ‖Z₂‖ ^ 2 := by
    have e := h1.symm.trans h2
    have p1 : (1 + ‖Z₁‖ ^ 2) ≠ 0 := by positivity
    have p2 : (1 + ‖Z₂‖ ^ 2) ≠ 0 := by positivity
    rw [div_eq_div_iff p1 p2] at e
    linarith
  unfold theta at h
  rw [hq] at h
  exact smul_right_injective Aff (mfun_pos a _).ne' h

theorem theta_surjective : Function.Surjective (theta a) := by
  intro W
  have hx := M.mem (‖W‖ ^ 2) (sq_nonneg _)
  have hrel := M.rel (‖W‖ ^ 2) (sq_nonneg _)
  have h1x : 0 < 1 - xq (‖W‖ ^ 2) := sub_pos.2 hx.2
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = xq (‖W‖ ^ 2) / (1 - xq (‖W‖ ^ 2)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    exact div_nonneg hx.1 h1x.le
  have hξ : q / (1 + q) = xq (‖W‖ ^ 2) := by
    rw [hqdef]
    field_simp
    ring
  have hWq : ‖W‖ ^ 2 = Real.exp (a (q / (1 + q))) * q := by
    rw [hξ, hqdef]
    field_simp
    linarith
  have hnorm : ‖(mfun a q)⁻¹ • W‖ ^ 2 = q := by
    rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, mfun_sq, hWq]
    field_simp
  refine ⟨(mfun a q)⁻¹ • W, ?_⟩
  unfold theta
  rw [hnorm, smul_smul, mul_inv_cancel₀ (mfun_pos a q).ne', one_smul]

/-- **`θ` pushes the Fubini–Study volume to the volume of the metric.** -/
theorem lintegral_theta (g : Aff → ℝ≥0∞) :
    ∫⁻ W : Aff, ENNReal.ofReal (detg (fun V : Aff => φ (‖V‖ ^ 2)) W) * g W
      = ∫⁻ Z : Aff, ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) * g (theta a Z) := by
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure Aff)
    MeasurableSet.univ (fun Z _ => (M.hasFDerivAt_theta Z).hasFDerivWithinAt)
    ((M.theta_injective hQ).injOn)
    (fun W => ENNReal.ofReal (detg (fun V : Aff => φ (‖V‖ ^ 2)) W) * g W)
  rw [image_univ, (M.theta_surjective hQ).range_eq, Measure.restrict_univ] at hcv
  rw [hcv]
  refine lintegral_congr fun Z => ?_
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have hξ := xi_mem_Ico hq
  have hbpos := M.pos _ (Ico_subset_Icc_self hξ)
  have hEpos := Real.exp_pos (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
  rw [M.det_theta Z, M.detg_eq, M.xq_theta hQ Z, abs_of_pos (div_pos (pow_pos hEpos 7) hbpos),
    ← mul_assoc, ← ENNReal.ofReal_mul (div_pos (pow_pos hEpos 7) hbpos).le]
  congr 2
  unfold f1 f3
  rw [one_sub_xi hq, Real.exp_neg]
  have h1q : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
  have hb := hbpos.ne'
  have hE := hEpos.ne'
  generalize bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) = b at hb ⊢
  generalize Real.exp (a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) = E at hE ⊢
  generalize 1 + ‖Z‖ ^ 2 = s at h1q ⊢
  field_simp

end MomentumData

/-! ### The comparison of the metrics -/

set_option maxHeartbeats 1600000 in
/-- The algebra of the comparison: in the decomposition of a vector into its
part orthogonal to `Z` and its components along `Z` and `i Z`, the two
quadratic forms have the ratios `1`, `1 / b`, `b`. -/
theorem quad_compare {ξ Einv H A₂ c₁ c₂ m q b Λ α β k nb nc : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1)
    (hm : m ^ 2 * Einv = 1) (hmpos : 0 < m) (hq : q * (1 - ξ) = ξ)
    (hb : b = 1 + ξ * (1 - ξ) * H) (hbpos : 0 < b) (hΛ1 : 1 ≤ Λ) (hΛb : b ≤ Λ)
    (hΛb' : b⁻¹ ≤ Λ) (hCS : c₁ ^ 2 + c₂ ^ 2 ≤ q * A₂) (hA : 0 ≤ A₂)
    (hα : α = (1 - ξ) * Einv) (hβ : β = Einv ^ 2 * (1 - ξ) ^ 2 * (-b + (1 - ξ) * H))
    (hk : k = m * (-H / b * (1 - ξ) ^ 2 / 2) * (2 * c₁))
    (hnb : nb = m ^ 2 * A₂ + 2 * m * k * c₁ + k ^ 2 * q)
    (hnc : nc = m ^ 2 * ((m * c₁ + k * q) ^ 2 + (m * c₂) ^ 2)) :
    α * nb + β * nc ≤ Λ * ((1 - ξ) * A₂ + -(1 - ξ) ^ 2 * (c₁ ^ 2 + c₂ ^ 2)) := by
  have h1ξ : 0 < 1 - ξ := by linarith
  have hE : Einv = (m ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hm
  have hmne : m ≠ 0 := hmpos.ne'
  have hbne : b ≠ 0 := hbpos.ne'
  rcases eq_or_lt_of_le hξ0 with h0 | h0
  · -- the point orbit
    have hξ : ξ = 0 := h0.symm
    have hq0 : q = 0 := by
      rw [hξ] at hq
      linarith
    have hc : c₁ ^ 2 + c₂ ^ 2 ≤ 0 := by
      rw [hq0, zero_mul] at hCS
      exact hCS
    have hc1 : c₁ = 0 := by nlinarith [sq_nonneg c₁, sq_nonneg c₂]
    have hc2 : c₂ = 0 := by nlinarith [sq_nonneg c₁, sq_nonneg c₂]
    have hk0 : k = 0 := by
      rw [hk, hc1]
      ring
    have hnb' : nb = m ^ 2 * A₂ := by
      rw [hnb, hk0, hc1]
      ring
    have hnc' : nc = 0 := by
      rw [hnc, hk0, hc1, hc2]
      ring
    rw [hα, hnb', hnc', hξ, hc1, hc2]
    have e : (1 - 0) * Einv * (m ^ 2 * A₂) + β * 0 = A₂ := by
      linear_combination A₂ * hm
    rw [e]
    have e2 : Λ * ((1 - 0) * A₂ + -(1 - 0) ^ 2 * ((0 : ℝ) ^ 2 + 0 ^ 2)) = Λ * A₂ := by ring
    rw [e2]
    calc A₂ = 1 * A₂ := (one_mul _).symm
      _ ≤ Λ * A₂ := mul_le_mul_of_nonneg_right hΛ1 hA
  · -- away from the point orbit
    have hξne : ξ ≠ 0 := h0.ne'
    have hqpos : 0 < q := by
      have h : q = ξ / (1 - ξ) := eq_div_of_mul_eq h1ξ.ne' hq
      rw [h]
      exact div_pos h0 h1ξ
    have hL : q * (α * nb + β * nc)
        = (1 - ξ) * (q * A₂ - (c₁ ^ 2 + c₂ ^ 2)) + (1 - ξ) ^ 2 * (c₁ ^ 2 / b + b * c₂ ^ 2) := by
      have hq' : q = ξ / (1 - ξ) := eq_div_of_mul_eq h1ξ.ne' hq
      have hH : H = (b - 1) / (ξ * (1 - ξ)) := by
        rw [eq_div_iff (mul_ne_zero hξne h1ξ.ne')]
        rw [hb]
        ring
      rw [hα, hβ, hnb, hnc, hk, hE, hq', hH]
      have hwne : (1 - ξ) ≠ 0 := h1ξ.ne'
      generalize hwd : 1 - ξ = w at hwne ⊢
      field_simp
      subst hwd
      ring
    have hR : q * ((1 - ξ) * A₂ + -(1 - ξ) ^ 2 * (c₁ ^ 2 + c₂ ^ 2))
        = (1 - ξ) * (q * A₂ - (c₁ ^ 2 + c₂ ^ 2)) + (1 - ξ) ^ 2 * (c₁ ^ 2 + c₂ ^ 2) := by
      linear_combination (-(1 - ξ) * (c₁ ^ 2 + c₂ ^ 2)) * hq
    have hdiff : q * (Λ * ((1 - ξ) * A₂ + -(1 - ξ) ^ 2 * (c₁ ^ 2 + c₂ ^ 2)) - (α * nb + β * nc))
        = (Λ - 1) * (1 - ξ) * (q * A₂ - (c₁ ^ 2 + c₂ ^ 2))
          + (1 - ξ) ^ 2 * ((Λ - b⁻¹) * c₁ ^ 2 + (Λ - b) * c₂ ^ 2) := by
      linear_combination Λ * hR - hL
    have hnonneg : 0 ≤ q * (Λ * ((1 - ξ) * A₂ + -(1 - ξ) ^ 2 * (c₁ ^ 2 + c₂ ^ 2))
        - (α * nb + β * nc)) := by
      rw [hdiff]
      have t1 : 0 ≤ (Λ - 1) * (1 - ξ) * (q * A₂ - (c₁ ^ 2 + c₂ ^ 2)) :=
        mul_nonneg (mul_nonneg (by linarith) h1ξ.le) (by linarith)
      have t2 : 0 ≤ (1 - ξ) ^ 2 * ((Λ - b⁻¹) * c₁ ^ 2 + (Λ - b) * c₂ ^ 2) :=
        mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
          (mul_nonneg (by linarith) (sq_nonneg _)))
      linarith
    have h := nonneg_of_mul_nonneg_right hnonneg hqpos
    linarith

namespace MomentumData

variable {H a xq φ : ℝ → ℝ} (M : MomentumData H a xq φ)
  (hQ : ∀ x ∈ Ico (0 : ℝ) 1, xq (x * Real.exp (a x) / (1 - x)) = x)

include M

/-- **The pulled-back metric is at most `Λ` times the Fubini–Study metric.** -/
theorem quad_theta_le {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x ∈ Icc (0 : ℝ) 1, bfun H x ≤ Λ ∧ (bfun H x)⁻¹ ≤ Λ) (Z c : Aff) :
    quad (f1 a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (f2 H a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (theta a Z)
        (mfun a (‖Z‖ ^ 2) • c
          + (mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
            / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2)
            * (2 * inner ℝ Z c)) • Z)
      ≤ Λ * quad (1 * (1 + ‖Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z c := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have hξ := xi_mem_Ico hq
  have hξI := Ico_subset_Icc_self hξ
  have h1q : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
  have hone := one_sub_xi hq
  have hbpos := M.pos _ hξI
  have hmpos := mfun_pos a (‖Z‖ ^ 2)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
      / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2)
      * (2 * inner ℝ Z c) := ⟨_, rfl⟩
  rw [← hk]
  -- the two norms
  have hnb : ‖mfun a (‖Z‖ ^ 2) • c + k • Z‖ ^ 2
      = mfun a (‖Z‖ ^ 2) ^ 2 * ‖c‖ ^ 2 + 2 * mfun a (‖Z‖ ^ 2) * k * (inner ℂ Z c : ℂ).re
        + k ^ 2 * ‖Z‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm, real_inner_eq_re Z c]
    ring
  have hin : (inner ℂ (theta a Z) (mfun a (‖Z‖ ^ 2) • c + k • Z) : ℂ)
      = (mfun a (‖Z‖ ^ 2) : ℂ) * ((mfun a (‖Z‖ ^ 2) : ℂ) * inner ℂ Z c
        + (k : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ)) := by
    have hZZ : (inner ℂ Z Z : ℂ) = ((‖Z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    unfold theta
    rw [← Complex.coe_smul (mfun a (‖Z‖ ^ 2)) Z, ← Complex.coe_smul (mfun a (‖Z‖ ^ 2)) c,
      ← Complex.coe_smul k Z, inner_smul_left, inner_add_right, inner_smul_right,
      inner_smul_right, Complex.conj_ofReal, hZZ]
  have hnc : ‖(inner ℂ (theta a Z) (mfun a (‖Z‖ ^ 2) • c + k • Z) : ℂ)‖ ^ 2
      = mfun a (‖Z‖ ^ 2) ^ 2 * ((mfun a (‖Z‖ ^ 2) * (inner ℂ Z c : ℂ).re + k * ‖Z‖ ^ 2) ^ 2
        + (mfun a (‖Z‖ ^ 2) * (inner ℂ Z c : ℂ).im) ^ 2) := by
    rw [hin, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hCS := normSq_inner_le Z c
  have hΛb := hΛ _ hξI
  have hbdef : bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
      = 1 + ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2) * (1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
        * H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) := rfl
  have hqrel : ‖Z‖ ^ 2 * (1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) = ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2) := by
    rw [hone]
    field_simp
  have hmE : mfun a (‖Z‖ ^ 2) ^ 2 * Real.exp (-(a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))) = 1 := by
    rw [mfun_sq, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hk' : k = mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
      / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) ^ 2 / 2)
      * (2 * (inner ℂ Z c : ℂ).re) := by
    rw [hk, hone, real_inner_eq_re Z c]
    field_simp
  have key := quad_compare (ξ := ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
    (Einv := Real.exp (-(a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))))) (H := H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
    (A₂ := ‖c‖ ^ 2) (c₁ := (inner ℂ Z c : ℂ).re) (c₂ := (inner ℂ Z c : ℂ).im)
    (m := mfun a (‖Z‖ ^ 2)) (q := ‖Z‖ ^ 2) (b := bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (Λ := Λ)
    (α := f1 a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (β := f2 H a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (k := k)
    hξ.1 hξ.2 hmE hmpos hqrel hbdef hbpos hΛ1 hΛb.1 hΛb.2 hCS (sq_nonneg _) rfl rfl hk' hnb hnc
  unfold quad
  rw [Complex.sq_norm (inner ℂ Z c), Complex.normSq_apply]
  have e : Λ * (1 * (1 + ‖Z‖ ^ 2)⁻¹ * ‖c‖ ^ 2 + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)
      * ((inner ℂ Z c : ℂ).re * (inner ℂ Z c : ℂ).re
        + (inner ℂ Z c : ℂ).im * (inner ℂ Z c : ℂ).im))
      = Λ * ((1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * ‖c‖ ^ 2
        + -(1 - ‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) ^ 2
          * ((inner ℂ Z c : ℂ).re ^ 2 + (inner ℂ Z c : ℂ).im ^ 2)) := by
    rw [hone]
    field_simp
  rw [e]
  exact key

include hQ

/-- **The gradient norms**: `|∇(F ∘ θ)|²` for the Fubini–Study metric is at most
`Λ |∇F|² ∘ θ` for the metric. -/
theorem gradSq_theta_le {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x ∈ Icc (0 : ℝ) 1, bfun H x ≤ Λ ∧ (bfun H x)⁻¹ ≤ Λ) {F : Aff → ℝ} (Z : Aff)
    (hF : DifferentiableAt ℝ F (theta a Z)) :
    gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z
      ≤ Λ * gradSq (fun W : Aff => φ (‖W‖ ^ 2)) F (theta a Z) := by
  have hq : (0 : ℝ) ≤ ‖Z‖ ^ 2 := sq_nonneg _
  have hspos : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
  -- the Fubini–Study metric at `Z`
  have hg0 := gmat_log 1 Z
  have hα0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ := by positivity
  have hαβ0 : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2 := by
    have e : 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2
        = 1 / (1 + ‖Z‖ ^ 2) ^ 2 := by
      field_simp
      ring
    rw [e]
    positivity
  -- the metric at `θ Z`
  have hxq := M.xq_theta hQ Z
  have hqθ : (0 : ℝ) ≤ ‖theta a Z‖ ^ 2 := sq_nonneg _
  have hg1 := M.gmat_eq (theta a Z)
  rw [hxq] at hg1
  have hα1 : 0 < f1 a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) := by
    have h := M.f1_pos hqθ
    rwa [hxq] at h
  have hαβ1 : 0 < f1 a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))
      + f2 H a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * ‖theta a Z‖ ^ 2 := by
    have h := M.f1_add hqθ
    have h3 := M.f3_pos hqθ
    rw [hxq] at h h3
    linarith
  -- the chain rule
  have hchain : ∀ c : Aff, fderiv ℝ (fun W => F (theta a W)) Z c
      = fderiv ℝ F (theta a Z) (mfun a (‖Z‖ ^ 2) • c
        + (mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
          / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2)
          * (2 * inner ℝ Z c)) • Z) := by
    intro c
    have h := (hF.hasFDerivAt.comp Z (M.hasFDerivAt_theta Z)).fderiv
    have h' : fderiv ℝ (fun W => F (theta a W)) Z = _ := h
    rw [h']
    rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Aff, c₀ = gradVec (1 * (1 + ‖Z‖ ^ 2)⁻¹)
      (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z (dz (fun W => F (theta a W)) Z) := ⟨_, rfl⟩
  have e1 : fderiv ℝ (fun W => F (theta a W)) Z c₀
      = gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z := by
    rw [hc₀]
    exact fderiv_gradVec hg0 hα0 hαβ0
  have e2 : 2 * quad (1 * (1 + ‖Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z c₀
      = gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z := by
    rw [hc₀, quad_gradVec hα0 hαβ0, gradSq_rank_one hg0 hα0 hαβ0]
  have hcs := sq_fderiv_le (F := F) hg1 hα1 hαβ1 (mfun a (‖Z‖ ^ 2) • c₀
    + (mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
      / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2)
      * (2 * inner ℝ Z c₀)) • Z)
  rw [← hchain c₀, e1] at hcs
  have hcmp := M.quad_theta_le hΛ1 hΛ Z c₀
  have hg0nn := gradSq_nonneg (F := fun W => F (theta a W)) hg0 hα0 hαβ0
  have hg1nn := gradSq_nonneg (F := F) hg1 hα1 hαβ1
  -- `S₀² ≤ S₁ · 2 Q₁ ≤ S₁ · Λ · S₀`
  have hfin : gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z ^ 2
      ≤ Λ * gradSq (fun W : Aff => φ (‖W‖ ^ 2)) F (theta a Z)
        * gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z := by
    have h3 : gradSq (fun W : Aff => φ (‖W‖ ^ 2)) F (theta a Z) * (2 * quad
        (f1 a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (f2 H a (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2))) (theta a Z)
        (mfun a (‖Z‖ ^ 2) • c₀ + (mfun a (‖Z‖ ^ 2) * (-(H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)))
          / bfun H (‖Z‖ ^ 2 / (1 + ‖Z‖ ^ 2)) * (1 / (1 + ‖Z‖ ^ 2) ^ 2) / 2)
          * (2 * inner ℝ Z c₀)) • Z))
        ≤ gradSq (fun W : Aff => φ (‖W‖ ^ 2)) F (theta a Z) * (2 * (Λ * quad
          (1 * (1 + ‖Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z c₀)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg1nn
    calc _ ≤ _ := hcs
      _ ≤ _ := h3
      _ = _ := by
        rw [← e2]
        ring
  rcases eq_or_lt_of_le hg0nn with h0 | h0
  · rw [← h0]
    exact mul_nonneg (by linarith) hg1nn
  · have h4 : gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z
        * gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z
        ≤ Λ * gradSq (fun W : Aff => φ (‖W‖ ^ 2)) F (theta a Z)
          * gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (theta a W)) Z := by
      rw [← pow_two]
      exact hfin
    exact le_of_mul_le_mul_right h4 h0

end MomentumData

end Calabi.Geometry
