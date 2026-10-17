import Calabi.Geometry.FubiniStudy

/-!
# The scalar curvature of a radial potential

For `u(Z) = φ(q)`, `q = ‖Z‖²`, the metric matrix is `a 1 + b P` with `a = φ′`,
`b = φ″` and `P = (conj Z_j Z_k)`, and `log det (u_{j k̄}) = ρ(q)` with
`ρ = log (φ′⁶ (φ′ + q φ″))`. Hence

  `S = -(6 ρ′ / φ′ + (ρ′ + q ρ″) / (φ′ + q φ″))`

(`scal_radial`). With the momentum coordinate `x = q φ′` and the momentum
profile `v = q (φ′ + q φ″)` this is `S = 42 / x - x⁻⁶ (x⁶ v)″`, the formula of
Proposition 2.1 of the manuscript for `n = 7`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Geometry

theorem vecMulVec_sq (w v : Fin 7 → ℂ) :
    Matrix.vecMulVec w v * Matrix.vecMulVec w v = (v ⬝ᵥ w) • Matrix.vecMulVec w v := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

/-- The inverse of `a 1 + b (w_j v_k)`. -/
theorem inv_rank_one {a b : ℂ} (w v : Fin 7 → ℂ) (ha : a ≠ 0)
    (hab : a + b * (v ⬝ᵥ w) ≠ 0) :
    (a • (1 : Matrix (Fin 7) (Fin 7) ℂ) + b • Matrix.vecMulVec w v)⁻¹
      = a⁻¹ • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        - (b / (a * (a + b * (v ⬝ᵥ w)))) • Matrix.vecMulVec w v := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, vecMulVec_sq,
    smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  generalize (1 : Matrix (Fin 7) (Fin 7) ℂ) i j = e
  generalize Matrix.vecMulVec w v i j = p
  generalize v ⬝ᵥ w = q at hab ⊢
  field_simp
  ring

/-- The trace of `(a 1 + b P)⁻¹ (α 1 + β P)` for `P = (w_j v_k)`. -/
theorem trace_inv_mul_rank_one {a b α β : ℂ} (w v : Fin 7 → ℂ) (ha : a ≠ 0)
    (hab : a + b * (v ⬝ᵥ w) ≠ 0) :
    ((a • (1 : Matrix (Fin 7) (Fin 7) ℂ) + b • Matrix.vecMulVec w v)⁻¹
      * (α • (1 : Matrix (Fin 7) (Fin 7) ℂ) + β • Matrix.vecMulVec w v)).trace
      = 6 * α / a + (α + β * (v ⬝ᵥ w)) / (a + b * (v ⬝ᵥ w)) := by
  rw [inv_rank_one w v ha hab, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, vecMulVec_sq,
    smul_smul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec, Fintype.card_fin, smul_eq_mul]
  rw [dotProduct_comm w v]
  generalize v ⬝ᵥ w = q at hab ⊢
  have hab2 : q * b + a ≠ 0 := by
    rw [mul_comm, add_comm]
    exact hab
  have hab3 : b * q + a ≠ 0 := by
    rw [add_comm]
    exact hab
  have hab4 : a + q * b ≠ 0 := by
    rw [mul_comm]
    exact hab
  push_cast
  field_simp
  ring

/-- The metric matrix depends only on the germ of the potential. -/
theorem gmat_congr {f g : Aff → ℝ} {Z : Aff} (h : f =ᶠ[𝓝 Z] g) : gmat f Z = gmat g Z := by
  have hh : iteratedFDeriv ℝ 2 f Z = iteratedFDeriv ℝ 2 g Z := (h.iteratedFDeriv ℝ 2).eq_of_nhds
  ext j k
  simp only [gmat, Matrix.of_apply, levi, hess, hh]

/-- The determinant of the metric of a radial potential. -/
theorem detg_radial {φ φ1 : ℝ → ℝ} {φ2 : ℝ} {Z : Aff}
    (h1 : ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : HasDerivWithinAt φ1 φ2 (Ici 0) (‖Z‖ ^ 2)) (hpos : φ1 (‖Z‖ ^ 2) ≠ 0) :
    detg (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = φ1 (‖Z‖ ^ 2) ^ 6 * (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2) := by
  have ha : ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
  have e : ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) ^ 6
      * (((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) + ((φ2 : ℝ) : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))
      = ((φ1 (‖Z‖ ^ 2) ^ 6 * (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2) : ℝ) : ℂ) := by
    push_cast
    ring
  unfold detg
  rw [gmat_radial h1 h2, det_rank_one ha, dot_star, e, Complex.ofReal_re]

/-- The Levi form of a radial potential is positive as soon as `φ′ > 0` and
`φ′ + q φ″ > 0`: these are the tangential and the radial eigenvalues. -/
theorem levi_radial_pos {φ φ1 : ℝ → ℝ} {φ2 : ℝ} {Z : Aff}
    (h1 : ∀ᶠ q in 𝓝[Ici 0] (‖Z‖ ^ 2), HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : HasDerivWithinAt φ1 φ2 (Ici 0) (‖Z‖ ^ 2)) (hpos1 : 0 < φ1 (‖Z‖ ^ 2))
    (hpos2 : 0 < φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2) {a : Aff} (ha : a ≠ 0) :
    0 < (levi (fun W : Aff => φ (‖W‖ ^ 2)) Z a a).re := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [levi_radial h1 h2]
  have e1 : (inner ℂ a a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e2 : (inner ℂ Z a : ℂ) * inner ℂ a Z = ((‖(inner ℂ Z a : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm a Z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcs : ‖(inner ℂ Z a : ℂ)‖ ^ 2 ≤ ‖Z‖ ^ 2 * ‖a‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) Z a
    have h0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ := norm_nonneg _
    nlinarith [mul_nonneg (norm_nonneg Z) (norm_nonneg a)]
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re]
  have ha2 : 0 < ‖a‖ ^ 2 := pow_pos ha0 2
  have hc0 : 0 ≤ ‖(inner ℂ Z a : ℂ)‖ ^ 2 := sq_nonneg _
  by_cases h : 0 ≤ φ2
  · have h3 : 0 ≤ φ2 * ‖(inner ℂ Z a : ℂ)‖ ^ 2 := mul_nonneg h hc0
    have h4 : 0 < φ1 (‖Z‖ ^ 2) * ‖a‖ ^ 2 := mul_pos hpos1 ha2
    linarith
  · have h3 : φ2 * (‖Z‖ ^ 2 * ‖a‖ ^ 2) ≤ φ2 * ‖(inner ℂ Z a : ℂ)‖ ^ 2 :=
      mul_le_mul_of_nonpos_left hcs (not_le.1 h).le
    have h4 : 0 < (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2) * ‖a‖ ^ 2 := mul_pos hpos2 ha2
    have h5 : (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2) * ‖a‖ ^ 2
        = φ1 (‖Z‖ ^ 2) * ‖a‖ ^ 2 + φ2 * (‖Z‖ ^ 2 * ‖a‖ ^ 2) := by ring
    linarith

/-- **The scalar curvature of a radial potential.** The derivatives of the
profile are taken within `[0, ∞)`, so that the point `Z = 0` is included. -/
theorem scal_radial {φ φ1 φ2 ρ1 : ℝ → ℝ} {ρ2 : ℝ} {I : Set ℝ} (hI : IsOpen I) {Z : Aff}
    (hZ : ‖Z‖ ^ 2 ∈ I) (h1 : ∀ q ∈ I, 0 ≤ q → HasDerivWithinAt φ (φ1 q) (Ici 0) q)
    (h2 : ∀ q ∈ I, 0 ≤ q → HasDerivWithinAt φ1 (φ2 q) (Ici 0) q)
    (hpos1 : ∀ q ∈ I, 0 ≤ q → 0 < φ1 q)
    (hpos2 : ∀ q ∈ I, 0 ≤ q → 0 < φ1 q + q * φ2 q)
    (hρ1 : ∀ q ∈ I, 0 ≤ q →
      HasDerivWithinAt (fun q => Real.log (φ1 q ^ 6 * (φ1 q + q * φ2 q))) (ρ1 q) (Ici 0) q)
    (hρ2 : HasDerivWithinAt ρ1 ρ2 (Ici 0) (‖Z‖ ^ 2)) :
    scal (fun W : Aff => φ (‖W‖ ^ 2)) Z
      = -(6 * ρ1 (‖Z‖ ^ 2) / φ1 (‖Z‖ ^ 2)
        + (ρ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * ρ2) / (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2 (‖Z‖ ^ 2))) := by
  have hev : ∀ {f f' : ℝ → ℝ}, (∀ q ∈ I, 0 ≤ q → HasDerivWithinAt f (f' q) (Ici 0) q) →
      ∀ W : Aff, ‖W‖ ^ 2 ∈ I →
        ∀ᶠ q in 𝓝[Ici 0] (‖W‖ ^ 2), HasDerivWithinAt f (f' q) (Ici 0) q := by
    intro f f' hf W hW
    filter_upwards [nhdsWithin_le_nhds (hI.mem_nhds hW), self_mem_nhdsWithin] with q hq hq0
      using hf q hq hq0
  have hgm : ∀ W : Aff, ‖W‖ ^ 2 ∈ I → gmat (fun W : Aff => φ (‖W‖ ^ 2)) W
      = (φ1 (‖W‖ ^ 2) : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
        + (φ2 (‖W‖ ^ 2) : ℂ) • Matrix.vecMulVec (fun j => star (W j)) (fun k => W k) := by
    intro W hW
    exact gmat_radial (φ := φ) (φ1 := φ1) (φ2 := φ2 (‖W‖ ^ 2)) (Z := W) (hev h1 W hW)
      (h2 _ hW (sq_nonneg _))
  have hdet : ∀ W : Aff, ‖W‖ ^ 2 ∈ I → detg (fun W : Aff => φ (‖W‖ ^ 2)) W
      = φ1 (‖W‖ ^ 2) ^ 6 * (φ1 (‖W‖ ^ 2) + ‖W‖ ^ 2 * φ2 (‖W‖ ^ 2)) := by
    intro W hW
    exact detg_radial (φ := φ) (φ1 := φ1) (φ2 := φ2 (‖W‖ ^ 2)) (Z := W) (hev h1 W hW)
      (h2 _ hW (sq_nonneg _)) (hpos1 _ hW (sq_nonneg _)).ne'
  have hcont : ContinuousAt (fun W : Aff => ‖W‖ ^ 2) Z := (hasFDerivAt_norm_sq Z).continuousAt
  have hnear : ∀ᶠ W in 𝓝 Z, ‖W‖ ^ 2 ∈ I := hcont.eventually (hI.mem_nhds hZ)
  have heq : (fun W : Aff => Real.log (detg (fun W : Aff => φ (‖W‖ ^ 2)) W))
      =ᶠ[𝓝 Z] fun W : Aff =>
        (fun q : ℝ => Real.log (φ1 q ^ 6 * (φ1 q + q * φ2 q))) (‖W‖ ^ 2) := by
    filter_upwards [hnear] with W hW
    rw [hdet W hW]
  have hR := gmat_radial (φ := fun q : ℝ => Real.log (φ1 q ^ 6 * (φ1 q + q * φ2 q)))
    (φ1 := ρ1) (φ2 := ρ2) (Z := Z) (hev hρ1 Z hZ) hρ2
  have ha : ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (hpos1 _ hZ (sq_nonneg _)).ne'
  have hab : ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ)
      + ((φ2 (‖Z‖ ^ 2) : ℝ) : ℂ) * ((fun k => Z k) ⬝ᵥ fun j => star (Z j)) ≠ 0 := by
    have h := (hpos2 _ hZ (sq_nonneg _)).ne'
    have e : ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) + ((φ2 (‖Z‖ ^ 2) : ℝ) : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ)
        = ((φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2 (‖Z‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [dot_star, e]
    exact_mod_cast h
  have e : 6 * ((ρ1 (‖Z‖ ^ 2) : ℝ) : ℂ) / ((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ)
      + (((ρ1 (‖Z‖ ^ 2) : ℝ) : ℂ) + ((ρ2 : ℝ) : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))
        / (((φ1 (‖Z‖ ^ 2) : ℝ) : ℂ) + ((φ2 (‖Z‖ ^ 2) : ℝ) : ℂ) * ((‖Z‖ ^ 2 : ℝ) : ℂ))
      = ((6 * ρ1 (‖Z‖ ^ 2) / φ1 (‖Z‖ ^ 2)
        + (ρ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * ρ2) / (φ1 (‖Z‖ ^ 2) + ‖Z‖ ^ 2 * φ2 (‖Z‖ ^ 2)) : ℝ) : ℂ) := by
    push_cast
    ring
  unfold scal
  rw [gmat_congr heq, hR, hgm Z hZ, trace_inv_mul_rank_one _ _ ha hab, dot_star, e,
    Complex.ofReal_re]

end Calabi.Geometry
