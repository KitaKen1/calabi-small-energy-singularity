import Calabi.Geometry.RadialScalar
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The gradient norm as a dual norm

For a metric matrix of the form `α 1 + β (conj Z_j Z_k)` (a radial potential),
`gradSq u F Z = 2 g^{j k̄} F_j F_k̄` is the square of the norm of the real
differential `dF` that is dual to the real quadratic form

  `2 Q(a)`,   `Q(a) = α ‖a‖² + β |⟨Z, a⟩|² = u_{j k̄} a_j conj(a_k)`.

* `fderiv_eq_pdot`: `dF(a) = 2 Re (∑ F_j a_j)`;
* `gradSq_rank_one`: the explicit value of `gradSq`;
* `sq_fderiv_le`: `dF(a)² ≤ gradSq · 2 Q(a)` (Cauchy–Schwarz);
* `gradVec`, `fderiv_gradVec`, `quad_gradVec`: the vector `a₀` with
  `dF(a₀) = gradSq = 2 Q(a₀)`, where the inequality is an equality.

These are used to compare the gradient norms of two metrics related by a
diffeomorphism that is not holomorphic.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

/-- `∑ p_j a_j`. -/
noncomputable def pdot (p : Fin 7 → ℂ) (a : Aff) : ℂ := ∑ j, p j * a j

/-- The quadratic form of the metric `α 1 + β (conj Z_j Z_k)`. -/
noncomputable def quad (α β : ℝ) (Z a : Aff) : ℝ := α * ‖a‖ ^ 2 + β * ‖(inner ℂ Z a : ℂ)‖ ^ 2

theorem aff_decomp (a : Aff) : a = ∑ j, ((a j).re • EuclideanSpace.single j (1 : ℂ)
    + (a j).im • EuclideanSpace.single j Complex.I) := by
  ext k
  simp [Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]

/-- The real differential in terms of the complex derivatives `F_j`. -/
theorem fderiv_eq_pdot (F : Aff → ℝ) (Z a : Aff) :
    fderiv ℝ F Z a = 2 * (pdot (dz F Z) a).re := by
  conv_lhs => rw [aff_decomp a]
  rw [map_sum]
  unfold pdot
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  unfold dz
  simp only [Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  ring

theorem inner_eq_sum (a b : Aff) : (inner ℂ a b : ℂ) = ∑ j, (starRingEnd ℂ) (a j) * b j := by
  simp [PiLp.inner_apply, mul_comm]

theorem quad_nonneg {α β : ℝ} {Z : Aff} (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2) (a : Aff) :
    0 ≤ quad α β Z a := by
  unfold quad
  have hcs : ‖(inner ℂ Z a : ℂ)‖ ^ 2 ≤ ‖Z‖ ^ 2 * ‖a‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) Z a
    have h0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ := norm_nonneg _
    nlinarith [mul_nonneg (norm_nonneg Z) (norm_nonneg a)]
  have ha2 : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  have hc0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ ^ 2 := sq_nonneg _
  by_cases h : 0 ≤ β
  · have h3 : 0 ≤ β * ‖(inner ℂ Z a : ℂ)‖ ^ 2 := mul_nonneg h hc0
    have h4 : 0 ≤ α * ‖a‖ ^ 2 := mul_nonneg hα.le ha2
    linarith
  · have h3 : β * (‖Z‖ ^ 2 * ‖a‖ ^ 2) ≤ β * ‖(inner ℂ Z a : ℂ)‖ ^ 2 :=
      mul_le_mul_of_nonpos_left hcs (not_le.1 h).le
    have h4 : 0 ≤ (α + β * ‖Z‖ ^ 2) * ‖a‖ ^ 2 := mul_nonneg hαβ.le ha2
    nlinarith

/-- The value `g^{j k̄} p_j conj(p_k)` for the metric `α 1 + β (conj Z_j Z_k)`. -/
noncomputable def gradVal (α β : ℝ) (Z : Aff) (p : Fin 7 → ℂ) : ℝ :=
  α⁻¹ * ∑ j, ‖p j‖ ^ 2 - β / (α * (α + β * ‖Z‖ ^ 2)) * ‖pdot p Z‖ ^ 2

/-- The explicit value of the gradient norm. -/
theorem gradSq_rank_one {u F : Aff → ℝ} {Z : Aff} {α β : ℝ}
    (hg : gmat u Z = (α : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k))
    (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2) :
    gradSq u F Z = 2 * gradVal α β Z (dz F Z) := by
  have ha : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hab : (α : ℂ) + (β : ℂ) * ((fun k => Z k) ⬝ᵥ fun j => star (Z j)) ≠ 0 := by
    rw [dot_star]
    have h : ((α + β * ‖Z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hαβ.ne'
    simpa using h
  unfold gradSq gradVal
  rw [hg, inv_rank_one _ _ ha hab, dot_star]
  have hsum : ∑ j, ∑ k, ((α : ℂ)⁻¹ • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      - ((β : ℂ) / ((α : ℂ) * ((α : ℂ) + (β : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))))
        • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k)) k j
        * dz F Z j * star (dz F Z k)
      = ((α⁻¹ * ∑ j, ‖dz F Z j‖ ^ 2
        - β / (α * (α + β * ‖Z‖ ^ 2)) * ‖pdot (dz F Z) Z‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ∀ j k : Fin 7, ((α : ℂ)⁻¹ • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        - ((β : ℂ) / ((α : ℂ) * ((α : ℂ) + (β : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))))
          • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k)) k j
          * dz F Z j * star (dz F Z k)
        = (α : ℂ)⁻¹ * ((1 : Matrix (Fin 7) (Fin 7) ℂ) k j * dz F Z j * star (dz F Z k))
          - ((β : ℂ) / ((α : ℂ) * ((α : ℂ) + (β : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))))
            * ((Z j * dz F Z j) * star (Z k * dz F Z k)) := by
      intro j k
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
        star_mul']
      ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h2 : ∑ j : Fin 7, ∑ k : Fin 7,
        (1 : Matrix (Fin 7) (Fin 7) ℂ) k j * dz F Z j * star (dz F Z k)
        = ((∑ j, ‖dz F Z j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single j]
      · rw [Matrix.one_apply_eq, one_mul, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        push_cast
        rfl
      · intro k _ hk
        rw [Matrix.one_apply_ne hk, zero_mul, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h3 : ∑ j : Fin 7, Z j * dz F Z j * ∑ k : Fin 7, star (Z k * dz F Z k)
        = ((‖pdot (dz F Z) Z‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Finset.sum_mul, ← star_sum]
      have e : ∑ j, Z j * dz F Z j = pdot (dz F Z) Z := by
        unfold pdot
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [e, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h2, h3]
    push_cast
    ring
  rw [hsum, Complex.ofReal_re]

/-- The vector at which the Cauchy–Schwarz inequality is an equality. -/
noncomputable def gradVec (α β : ℝ) (Z : Aff) (p : Fin 7 → ℂ) : Aff :=
  WithLp.toLp 2 fun j => ((starRingEnd ℂ) (p j)
    - ((β / (α + β * ‖Z‖ ^ 2) : ℝ) : ℂ) * Z j * (starRingEnd ℂ) (pdot p Z)) / (α : ℂ)

theorem gradVec_apply (α β : ℝ) (Z : Aff) (p : Fin 7 → ℂ) (j : Fin 7) :
    gradVec α β Z p j = ((starRingEnd ℂ) (p j)
      - ((β / (α + β * ‖Z‖ ^ 2) : ℝ) : ℂ) * Z j * (starRingEnd ℂ) (pdot p Z)) / (α : ℂ) := rfl

section Dual

variable {α β : ℝ} {Z : Aff} (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2)

include hα hαβ

/-- `⟨a₀, a⟩ α + β ⟨Z, a⟩ ⟨a₀, Z⟩ = ∑ p_j a_j`: the metric pairs `a₀` with `p`. -/
theorem pairing_gradVec (p : Fin 7 → ℂ) (a : Aff) :
    (α : ℂ) * inner ℂ (gradVec α β Z p) a
      + (β : ℂ) * ((inner ℂ Z a : ℂ) * inner ℂ (gradVec α β Z p) Z) = pdot p a := by
  have ha : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hs : ((α + β * ‖Z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hαβ.ne'
  have hq : ∑ j, (starRingEnd ℂ) (Z j) * Z j = ((‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h1 : ∀ a : Aff, (inner ℂ (gradVec α β Z p) a : ℂ)
      = (pdot p a - ((β / (α + β * ‖Z‖ ^ 2) : ℝ) : ℂ) * pdot p Z * inner ℂ Z a) / (α : ℂ) := by
    intro a
    rw [inner_eq_sum, inner_eq_sum]
    unfold pdot
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gradVec_apply]
    simp only [map_div₀, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    unfold pdot
    ring
  have h2 : (inner ℂ (gradVec α β Z p) Z : ℂ) = pdot p Z / ((α + β * ‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [h1 Z, inner_eq_sum, hq]
    push_cast
    push_cast at hs
    field_simp
    ring
  rw [h1 a, h2]
  push_cast
  push_cast at hs
  field_simp
  ring

theorem pdot_gradVec (p : Fin 7 → ℂ) :
    pdot p (gradVec α β Z p) = ((gradVal α β Z p : ℝ) : ℂ) := by
  have ha : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hs : ((α + β * ‖Z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hαβ.ne'
  unfold gradVal
  have e1 : pdot p (gradVec α β Z p)
      = ((∑ j, p j * (starRingEnd ℂ) (p j))
        - ((β / (α + β * ‖Z‖ ^ 2) : ℝ) : ℂ) * (pdot p Z * (starRingEnd ℂ) (pdot p Z)))
        / (α : ℂ) := by
    have hterm : ∀ j, p j * gradVec α β Z p j
        = p j * (starRingEnd ℂ) (p j) / (α : ℂ)
          - ((β / (α + β * ‖Z‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) (pdot p Z) / (α : ℂ)
            * (p j * Z j) := by
      intro j
      rw [gradVec_apply]
      ring
    have hd : ∑ j, p j * Z j = pdot p Z := rfl
    show ∑ j, p j * gradVec α β Z p j = _
    simp only [hterm, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, hd]
    ring
  have e2 : ∑ j, p j * (starRingEnd ℂ) (p j) = ((∑ j, ‖p j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have e3 : pdot p Z * (starRingEnd ℂ) (pdot p Z) = ((‖pdot p Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, e2, e3]
  push_cast
  push_cast at hs
  field_simp

/-- The quadratic form along the line through `a` in the direction `a₀`. -/
theorem quad_sub_smul (p : Fin 7 → ℂ) (a : Aff) (t : ℝ) :
    quad α β Z (a - t • gradVec α β Z p)
      = gradVal α β Z p * (t * t) + -(2 * (pdot p a).re) * t + quad α β Z a := by
  have hpair := pairing_gradVec hα hαβ p a
  have hself := pairing_gradVec hα hαβ p (gradVec α β Z p)
  rw [pdot_gradVec hα hαβ] at hself
  -- the two real expansions
  have n1 : ‖a - t • gradVec α β Z p‖ ^ 2 = ‖a‖ ^ 2
      - 2 * t * (inner ℂ (gradVec α β Z p) a : ℂ).re + t ^ 2 * ‖gradVec α β Z p‖ ^ 2 := by
    have h := norm_sub_sq_real a (t • gradVec α β Z p)
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_eq_re, ← inner_conj_symm, Complex.conj_re] at h
    rw [h]
    ring
  have n2 : ‖(inner ℂ Z (a - t • gradVec α β Z p) : ℂ)‖ ^ 2 = ‖(inner ℂ Z a : ℂ)‖ ^ 2
      - 2 * t * ((inner ℂ Z a : ℂ) * inner ℂ (gradVec α β Z p) Z).re
      + t ^ 2 * ‖(inner ℂ Z (gradVec α β Z p) : ℂ)‖ ^ 2 := by
    have e : (inner ℂ Z (a - t • gradVec α β Z p) : ℂ)
        = inner ℂ Z a - (t : ℂ) * inner ℂ Z (gradVec α β Z p) := by
      rw [inner_sub_right, inner_smul_right_eq_smul, Complex.real_smul]
    rw [e, ← inner_conj_symm (gradVec α β Z p) Z]
    generalize (inner ℂ Z a : ℂ) = x
    generalize (inner ℂ Z (gradVec α β Z p) : ℂ) = y
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have r1 := congrArg Complex.re hpair
  have r2 := congrArg Complex.re hself
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at r1 r2
  rw [Complex.ofReal_re] at r2
  have r3 : (inner ℂ (gradVec α β Z p) (gradVec α β Z p) : ℂ).re = ‖gradVec α β Z p‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have r4 : ((inner ℂ Z (gradVec α β Z p) : ℂ) * inner ℂ (gradVec α β Z p) Z).re
      = ‖(inner ℂ Z (gradVec α β Z p) : ℂ)‖ ^ 2 := by
    rw [← inner_conj_symm (gradVec α β Z p) Z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [r3, r4] at r2
  unfold quad
  rw [n1, n2]
  linear_combination (-(2 * t)) * r1 + t ^ 2 * r2

/-- `Q(a₀) = g^{j k̄} p_j conj(p_k)`. -/
theorem quad_gradVec (p : Fin 7 → ℂ) : quad α β Z (gradVec α β Z p) = gradVal α β Z p := by
  have h := quad_sub_smul hα hαβ p (0 : Aff) (-1)
  have e : (0 : Aff) - (-1 : ℝ) • gradVec α β Z p = gradVec α β Z p := by simp
  have e0 : quad α β Z (0 : Aff) = 0 := by simp [quad]
  have e1 : pdot p (0 : Aff) = 0 := by simp [pdot]
  rw [e, e0, e1] at h
  rw [h]
  simp

theorem gradVal_nonneg (p : Fin 7 → ℂ) : 0 ≤ gradVal α β Z p := by
  rw [← quad_gradVec hα hαβ p]
  exact quad_nonneg hα hαβ _

/-- **Cauchy–Schwarz**: `(Re ∑ p_j a_j)² ≤ g^{j k̄} p_j conj(p_k) · Q(a)`. -/
theorem sq_re_pdot_le (p : Fin 7 → ℂ) (a : Aff) :
    (pdot p a).re ^ 2 ≤ gradVal α β Z p * quad α β Z a := by
  have h : ∀ t : ℝ, 0 ≤ gradVal α β Z p * (t * t) + -(2 * (pdot p a).re) * t + quad α β Z a :=
    fun t => by
      rw [← quad_sub_smul hα hαβ p a t]
      exact quad_nonneg hα hαβ _
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

end Dual

/-- `dF(a)² ≤ |∇F|² · 2 Q(a)` for a metric `α 1 + β (conj Z_j Z_k)`. -/
theorem sq_fderiv_le {u F : Aff → ℝ} {Z : Aff} {α β : ℝ}
    (hg : gmat u Z = (α : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k))
    (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2) (a : Aff) :
    (fderiv ℝ F Z a) ^ 2 ≤ gradSq u F Z * (2 * quad α β Z a) := by
  rw [gradSq_rank_one hg hα hαβ, fderiv_eq_pdot]
  have h := sq_re_pdot_le hα hαβ (dz F Z) a
  nlinarith

/-- The differential at the extremal vector: `dF(a₀) = |∇F|²`. -/
theorem fderiv_gradVec {u F : Aff → ℝ} {Z : Aff} {α β : ℝ}
    (hg : gmat u Z = (α : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k))
    (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2) :
    fderiv ℝ F Z (gradVec α β Z (dz F Z)) = gradSq u F Z := by
  rw [gradSq_rank_one hg hα hαβ, fderiv_eq_pdot, pdot_gradVec hα hαβ, Complex.ofReal_re]

theorem gradSq_nonneg {u F : Aff → ℝ} {Z : Aff} {α β : ℝ}
    (hg : gmat u Z = (α : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k))
    (hα : 0 < α) (hαβ : 0 < α + β * ‖Z‖ ^ 2) : 0 ≤ gradSq u F Z := by
  rw [gradSq_rank_one hg hα hαβ]
  have h := gradVal_nonneg hα hαβ (dz F Z)
  linarith

end Calabi.Geometry
