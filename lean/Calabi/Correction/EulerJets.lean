import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The operators of the chart in terms of jets

The chart form `chartOp` of the compact operator (`RadialChart.lean`) is built
from the Laplacian `Δ` and the Euler operator `E u (z) = Du(z) z`. For the
estimates each of the operators of order at most three is written as a jet of
`u` evaluated at a tuple made of the point `z` and of vectors of a fixed
orthonormal basis `eᵢ`:

* `eulerE_eq`: `E u (z) = D¹u(z)[z]`;
* `laplacian_eq_sum`: `Δ u (z) = Σᵢ D²u(z)[eᵢ, eᵢ]`;
* `eulerE_eulerE`: `E (E u) (z) = D²u(z)[z, z] + E u (z)`;
* `eulerE_laplacian`: `E (Δ u) (z) = Σᵢ D³u(z)[z, eᵢ, eᵢ]`.

`norm_apply_le_of_le_one` and `norm_apply_sub_le_of_le_one` bound a
multilinear map on tuples of vectors of norm at most one.
-/

open scoped ContDiff Laplacian
open InnerProductSpace

namespace Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euler operator `E u (z) = Du(z) z` on vector-valued functions. -/
noncomputable def eulerE (u : V → E) (z : V) : E := fderiv ℝ u z z

omit [FiniteDimensional ℝ V] in
theorem eulerE_eq (u : V → E) (z : V) : eulerE u z = iteratedFDeriv ℝ 1 u z (fun _ => z) := by
  rw [iteratedFDeriv_one_apply]
  rfl

theorem laplacian_eq_sum (u : V → E) (z : V) :
    Δ u z = ∑ i, iteratedFDeriv ℝ 2 u z
      ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i] :=
  congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis u) z

omit [FiniteDimensional ℝ V] in
theorem eulerE_eulerE {u : V → E} (hu : ContDiff ℝ 2 u) (z : V) :
    eulerE (eulerE u) z = iteratedFDeriv ℝ 2 u z ![z, z] + eulerE u z := by
  have hc1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
    (hc1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have h := hd.clm_apply (hasFDerivAt_id z)
  have e : fderiv ℝ (fun y => fderiv ℝ u y y) z
      = (fderiv ℝ u z).comp (ContinuousLinearMap.id ℝ V)
        + (fderiv ℝ (fderiv ℝ u) z).flip z := h.fderiv
  show fderiv ℝ (fun y => fderiv ℝ u y y) z z = _
  rw [e, iteratedFDeriv_two_apply]
  simp [eulerE, add_comm]

theorem eulerE_laplacian {u : V → E} (hu : ContDiff ℝ 3 u) (z : V) :
    eulerE (Δ u) z = ∑ i, iteratedFDeriv ℝ 3 u z
      ![z, stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i] := by
  have hd : HasFDerivAt (iteratedFDeriv ℝ 2 u) (fderiv ℝ (iteratedFDeriv ℝ 2 u) z) z :=
    ((hu.differentiable_iteratedFDeriv (m := 2) (by exact_mod_cast (by norm_num : (2 : ℕ) < 3)))
      z).hasFDerivAt
  have hterm : ∀ i, HasFDerivAt
      (fun y => iteratedFDeriv ℝ 2 u y ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i])
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) E
        ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i]).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 u) z)) z := fun i =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) E
      ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i]).hasFDerivAt.comp z hd
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  show fderiv ℝ (Δ u) z z = _
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hsum.fderiv]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_succ_apply_left]
  rfl

/-! ### Multilinear maps on tuples of small vectors -/

omit [FiniteDimensional ℝ V] in
theorem norm_apply_le_of_le_one {k : ℕ} (φ : V [×k]→L[ℝ] E) {m : Fin k → V}
    (h : ∀ i, ‖m i‖ ≤ 1) : ‖φ m‖ ≤ ‖φ‖ := by
  refine (φ.le_opNorm m).trans ?_
  have h1 : ∏ i, ‖m i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h i)
  exact mul_le_of_le_one_right (norm_nonneg φ) h1

omit [FiniteDimensional ℝ V] in
theorem norm_apply_sub_le_of_le_one {k : ℕ} (φ : V [×k]→L[ℝ] E) {m₁ m₂ : Fin k → V}
    (h₁ : ∀ i, ‖m₁ i‖ ≤ 1) (h₂ : ∀ i, ‖m₂ i‖ ≤ 1) :
    ‖φ m₁ - φ m₂‖ ≤ ‖φ‖ * k * ‖m₁ - m₂‖ := by
  have h := φ.norm_image_sub_le m₁ m₂
  rw [Fintype.card_fin] at h
  have hm : max ‖m₁‖ ‖m₂‖ ≤ 1 :=
    max_le ((pi_norm_le_iff_of_nonneg zero_le_one).2 h₁)
      ((pi_norm_le_iff_of_nonneg zero_le_one).2 h₂)
  have hp : max ‖m₁‖ ‖m₂‖ ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (norm_nonneg _)) hm
  refine h.trans ?_
  have h0 : 0 ≤ ‖φ‖ * k := mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  calc ‖φ‖ * k * max ‖m₁‖ ‖m₂‖ ^ (k - 1) * ‖m₁ - m₂‖
      ≤ ‖φ‖ * k * 1 * ‖m₁ - m₂‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp h0) (norm_nonneg _)
    _ = ‖φ‖ * k * ‖m₁ - m₂‖ := by rw [mul_one]

end Calabi.Chart
