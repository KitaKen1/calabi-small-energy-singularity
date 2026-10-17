import Calabi.Correction.DiffQuotStep
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Commutation of derivatives

* `laplacian_fderiv_apply`, `bilaplacian_fderiv_apply`: a derivative in a
  direction commutes with the Laplacian and with its square;
* `fderiv_bilaplacian_equation`: the derivative in a direction of the equation
  `u_t + a Δ² u = f`;
* `timeDeriv_fderiv_apply`: for a function of the local class of order one
  whose time derivative is of the class of order one, the derivative in a
  direction has a time derivative, which is the derivative in that direction
  of the time derivative.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem fderiv_fderiv_apply {f : V → ℝ} {y : V} (hf : ContDiffAt ℝ 2 f y) (c v : V) :
    fderiv ℝ (fun x => fderiv ℝ f x c) y v = fderiv ℝ (fderiv ℝ f) y v c := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun x => fderiv ℝ f x c)
      ((ContinuousLinearMap.apply ℝ ℝ c).comp (fderiv ℝ (fderiv ℝ f) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ c).hasFDerivAt.comp y hd.hasFDerivAt
  rw [h1.fderiv]
  rfl

omit [FiniteDimensional ℝ V] in
theorem contDiffAt_fderiv_apply {f : V → ℝ} {y : V} {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f y)
    (c : V) : ContDiffAt ℝ n (fun x => fderiv ℝ f x c) y :=
  (hf.fderiv_right (m := n) (by exact_mod_cast le_rfl)).clm_apply contDiffAt_const

/-- The Laplacian of a function that is `C^{n+2}` at a point is `C^n` there. -/
theorem contDiffAt_laplacian {g : V → ℝ} {z : V} {n : ℕ} (hg : ContDiffAt ℝ (n + 2 : ℕ) g z) :
    ContDiffAt ℝ n (Δ g) z := by
  have h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 g y :=
    (hg.of_le (by exact_mod_cast (by omega : 2 ≤ n + 2))).eventually (by simp)
  have hev : Δ g =ᶠ[𝓝 z] fun y => ∑ i,
      fderiv ℝ (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) y
        (stdOrthonormalBasis ℝ V i) := by
    filter_upwards [h2] with y hy using laplacian_eq_sum_of_contDiffAt hy
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine ContDiffAt.sum fun i _ => ?_
  exact contDiffAt_fderiv_apply (contDiffAt_fderiv_apply (n := n + 1) hg _) _

/-- **A derivative in a direction commutes with the Laplacian.** -/
theorem laplacian_fderiv_apply {g : V → ℝ} {z : V} (hg : ContDiffAt ℝ 3 g z) (e : V) :
    Δ (fun y => fderiv ℝ g y e) z = fderiv ℝ (Δ g) z e := by
  have hg3 : ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) g z := by exact_mod_cast hg
  have h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 g y := (hg.of_le (by norm_num)).eventually (by simp)
  -- the right-hand side
  have hevL : Δ g =ᶠ[𝓝 z] fun y => ∑ i,
      fderiv ℝ (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) y
        (stdOrthonormalBasis ℝ V i) := by
    filter_upwards [h2] with y hy using laplacian_eq_sum_of_contDiffAt hy
  have hG2 : ∀ i, ContDiffAt ℝ 2 (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) z :=
    fun i => contDiffAt_fderiv_apply (n := 2) hg3 _
  have hGd : ∀ i, DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) y
        (stdOrthonormalBasis ℝ V i)) z := fun i =>
    (contDiffAt_fderiv_apply (n := 1) (by exact_mod_cast hG2 i) _).differentiableAt one_ne_zero
  have hR : fderiv ℝ (Δ g) z e = ∑ i,
      fderiv ℝ (fun y => fderiv ℝ (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) y
        (stdOrthonormalBasis ℝ V i)) z e := by
    rw [hevL.fderiv_eq, fderiv_fun_sum fun i _ => hGd i]
    simp
  -- the left-hand side
  have hE2 : ContDiffAt ℝ 2 (fun y => fderiv ℝ g y e) z := contDiffAt_fderiv_apply (n := 2) hg3 e
  rw [laplacian_eq_sum_of_contDiffAt hE2, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the mixed derivatives of `g` commute near `z`
  have hev1 : (fun y => fderiv ℝ (fun x => fderiv ℝ g x e) y (stdOrthonormalBasis ℝ V i))
      =ᶠ[𝓝 z] fun y => fderiv ℝ (fun x => fderiv ℝ g x (stdOrthonormalBasis ℝ V i)) y e := by
    filter_upwards [h2] with y hy
    rw [fderiv_fderiv_apply hy, fderiv_fderiv_apply hy]
    exact (hy.isSymmSndFDerivAt (by simp)) _ _
  rw [hev1.fderiv_eq, fderiv_fderiv_apply (hG2 i), fderiv_fderiv_apply (hG2 i)]
  exact ((hG2 i).isSymmSndFDerivAt (by simp)) _ _

/-- **A derivative in a direction commutes with the bilaplacian.** -/
theorem bilaplacian_fderiv_apply {g : V → ℝ} {z : V} (hg : ContDiffAt ℝ 5 g z) (e : V) :
    Δ (Δ (fun y => fderiv ℝ g y e)) z = fderiv ℝ (Δ (Δ g)) z e := by
  have h3 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 3 g y := (hg.of_le (by norm_num)).eventually (by simp)
  have hev : Δ (fun y => fderiv ℝ g y e) =ᶠ[𝓝 z] fun y => fderiv ℝ (Δ g) y e := by
    filter_upwards [h3] with y hy using laplacian_fderiv_apply hy e
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  have hL3 : ContDiffAt ℝ 3 (Δ g) z := by
    have h5 : ContDiffAt ℝ ((3 + 2 : ℕ) : WithTop ℕ∞) g z := by exact_mod_cast hg
    exact_mod_cast contDiffAt_laplacian (n := 3) h5
  exact laplacian_fderiv_apply hL3 e

end Calabi.Weighted
