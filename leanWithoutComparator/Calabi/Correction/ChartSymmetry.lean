import Calabi.Correction.PairLimit
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Radial functions in a chart

* `radial_eq_of_norm_eq`: a function that is invariant under the linear
  isometries depends on the norm only (a reflection exchanges two vectors of
  the same norm);
* `chartOp_eq_of_norm_eq`: for a radial function of class `C⁴`, so does the
  value of the chart operator;
* `radial_timeDeriv`: the time derivative of a radial function is radial;
* `iteratedFDeriv_comp_eq_zero`: if the derivatives of order at most `k` of a
  function of one variable vanish at a point, the jets of order at most `k` of
  its composition with a smooth function vanish at the corresponding points;
* `exists_taylor_remainder`: a `C⁴` function of one variable is a polynomial
  plus a function whose derivatives of order at most four vanish at a given
  point.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Radial functions -/

/-- A function that is invariant under the linear isometries depends on the
norm only. -/
theorem radial_eq_of_norm_eq {X : Type*} {u : V → X}
    (hrad : ∀ (Q : V ≃ₗᵢ[ℝ] V) (z : V), u (Q z) = u z) {a b : V} (hab : ‖a‖ = ‖b‖) :
    u a = u b := by
  have h := hrad ((ℝ ∙ (a - b))ᗮ.reflection) a
  rw [Submodule.reflection_sub hab] at h
  exact h.symm

/-- The Laplacian commutes with the linear isometries. -/
theorem laplacian_rotate_real (R : V ≃ₗᵢ[ℝ] V) (f : V → ℝ) (hf : ContDiff ℝ 2 f) :
    Δ (fun x => f (R x)) = fun x => Δ f (R x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ V),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((stdOrthonormalBasis ℝ V).map R)]
  funext x
  have he := R.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (i := 2) le_rfl
  change iteratedFDeriv ℝ 2 (fun x => f (R x)) x = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [FiniteDimensional ℝ V] in
/-- The Euler operator of a function that is invariant under an isometry. -/
theorem euler_rotate {f : V → ℝ} (hf : Differentiable ℝ f) (Q : V ≃ₗᵢ[ℝ] V)
    (hrad : ∀ z, f (Q z) = f z) (z : V) : euler f (Q z) = euler f z := by
  have h1 : HasFDerivAt (fun x => f (Q x))
      ((fderiv ℝ f (Q z)).comp (Q.toContinuousLinearEquiv : V →L[ℝ] V)) z :=
    (hf (Q z)).hasFDerivAt.comp z (Q.toContinuousLinearEquiv : V →L[ℝ] V).hasFDerivAt
  have e : (fun x => f (Q x)) = f := funext hrad
  rw [e] at h1
  unfold euler
  rw [h1.fderiv]
  rfl

/-- **The chart operator of a radial function is radial.** -/
theorem chartOp_radial_invariant (m : ℝ) {u : V → ℝ} (hu : ContDiff ℝ 4 u)
    (hrad : ∀ (Q : V ≃ₗᵢ[ℝ] V) (z : V), u (Q z) = u z) (Q : V ≃ₗᵢ[ℝ] V) (z : V) :
    chartOp m u (Q z) = chartOp m u z := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hL2 : ContDiff ℝ 2 (Δ u) := contDiff_two_laplacian hu
  -- the Laplacian of a radial function is radial
  have hLrad : ∀ {f : V → ℝ}, ContDiff ℝ 2 f → (∀ y, f (Q y) = f y) →
      ∀ y, Δ f (Q y) = Δ f y := by
    intro f hf hfr y
    have h1 := congrFun (laplacian_rotate_real Q f hf) y
    have e : (fun x => f (Q x)) = f := funext hfr
    rw [e] at h1
    exact h1.symm
  have r1 : ∀ y, Δ u (Q y) = Δ u y := hLrad hu2 (hrad Q)
  have r2 : ∀ y, Δ (Δ u) (Q y) = Δ (Δ u) y := hLrad hL2 r1
  have r3 : ∀ y, euler u (Q y) = euler u y := euler_rotate hu1 Q (hrad Q)
  have r4 : ∀ y, euler (Δ u) (Q y) = euler (Δ u) y :=
    euler_rotate (hL2.differentiable (by norm_num)) Q r1
  have r5 : ∀ y, euler (euler u) (Q y) = euler (euler u) y :=
    euler_rotate (differentiable_euler hu2) Q r3
  unfold chartOp
  rw [r1 z, r2 z, r3 z, r4 z, r5 z, hrad Q z, LinearIsometryEquiv.norm_map]

/-- The chart operator of a radial function at two points of the same norm. -/
theorem chartOp_eq_of_norm_eq (m : ℝ) {u : V → ℝ} (hu : ContDiff ℝ 4 u)
    (hrad : ∀ (Q : V ≃ₗᵢ[ℝ] V) (z : V), u (Q z) = u z) {a b : V} (hab : ‖a‖ = ‖b‖) :
    chartOp m u a = chartOp m u b :=
  radial_eq_of_norm_eq (u := chartOp m u) (chartOp_radial_invariant m hu hrad) hab

/-- The time derivative of a function that is invariant under a map is
invariant. -/
theorem invariant_timeDeriv {X : Type*} {u ut : ℝ → X → ℝ} {Q : X → X} (hrad : ∀ t z, u t (Q z) = u t z)
    {t : ℝ} (hd : ∀ z, HasDerivAt (fun r => u r z) (ut t z) t) (z : X) :
    ut t (Q z) = ut t z := by
  have h1 := hd (Q z)
  have e : (fun r => u r (Q z)) = fun r => u r z := funext fun r => hrad r z
  rw [e] at h1
  exact h1.unique (hd z)

/-! ### Jets of a composition -/

omit [FiniteDimensional ℝ V] in
/-- If the derivatives of order at most `k` of a function of one variable
vanish at a point, the jets of order at most `k` of its composition with a
smooth function vanish at the corresponding points. -/
theorem iteratedFDeriv_comp_eq_zero {ρ : V → ℝ} (hρ : ContDiff ℝ ∞ ρ) (z : V) (k : ℕ) :
    ∀ r : ℝ → ℝ, ContDiff ℝ k r → (∀ j : ℕ, j ≤ k → iteratedDeriv j r (ρ z) = 0) →
      ∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j (fun y => r (ρ y)) z = 0 := by
  induction k with
  | zero =>
    intro r _ hz j hj
    have hj0 : j = 0 := Nat.le_zero.1 hj
    subst hj0
    have h0 := hz 0 le_rfl
    rw [iteratedDeriv_zero] at h0
    ext m
    simp [iteratedFDeriv_zero_apply, h0]
  | succ k ih =>
    intro r hr hz j hj
    have hrk : ContDiff ℝ k r := hr.of_le (by exact_mod_cast Nat.le_succ k)
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact ih r hrk (fun i hi => hz i (by omega)) j (by omega)
    · have hjk : j = k + 1 := by omega
      subst hjk
      have hr1 : ContDiff ℝ ((k : WithTop ℕ∞) + 1) r := by exact_mod_cast hr
      obtain ⟨hrd, -, hdr⟩ := contDiff_succ_iff_deriv.1 hr1
      have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
      -- the derivative of the composition
      have hfd : fderiv ℝ (fun y => r (ρ y)) = fun y => deriv r (ρ y) • fderiv ℝ ρ y := by
        funext y
        have h1 : HasFDerivAt (fun y => r (ρ y)) (deriv r (ρ y) • fderiv ℝ ρ y) y :=
          ((hrd (ρ y)).hasDerivAt.comp_hasFDerivAt y (hρd y).hasFDerivAt)
        exact h1.fderiv
      have hz' : ∀ i : ℕ, i ≤ k → iteratedDeriv i (deriv r) (ρ z) = 0 := fun i hi => by
        rw [← iteratedDeriv_succ']
        exact hz (i + 1) (by omega)
      have hih := ih (deriv r) hdr hz'
      have hc1 : ContDiff ℝ k (fun y => deriv r (ρ y)) :=
        hdr.comp (hρ.of_le (by exact_mod_cast le_top))
      have hc2 : ContDiff ℝ k (fderiv ℝ ρ) := hρ.fderiv_right (by exact_mod_cast le_top)
      have hbound := norm_iteratedFDeriv_smul_le hc1 hc2 z (n := k) le_rfl
      have hzero : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun y => deriv r (ρ y)) z‖
          * ‖iteratedFDeriv ℝ (k - i) (fderiv ℝ ρ) z‖ = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hih i (by have := Finset.mem_range.1 hi; omega), norm_zero, mul_zero, zero_mul]
      rw [hzero] at hbound
      have h0 : iteratedFDeriv ℝ k (fun y => deriv r (ρ y) • fderiv ℝ ρ y) z = 0 :=
        norm_le_zero_iff.1 hbound
      rw [iteratedFDeriv_succ_eq_comp_right]
      show (continuousMultilinearCurryRightEquiv' ℝ k V ℝ).symm
        (iteratedFDeriv ℝ k (fun y => fderiv ℝ (fun y => r (ρ y)) y) z) = 0
      have e2 : (fun y => fderiv ℝ (fun y => r (ρ y)) y) = fun y => deriv r (ρ y) • fderiv ℝ ρ y :=
        hfd
      rw [e2, h0]
      exact (continuousMultilinearCurryRightEquiv' ℝ k V ℝ).symm.map_zero

/-! ### Taylor polynomials of degree four -/

theorem deriv_pol_shift (c0 c1 c2 c3 c4 x : ℝ) :
    deriv (fun y : ℝ => pol c0 c1 c2 c3 c4 (y - x))
      = fun y => pol c1 (2 * c2) (3 * c3) (4 * c4) 0 (y - x) := by
  funext y
  have h := (hasDerivAt_pol c0 c1 c2 c3 c4 (y - x)).comp y ((hasDerivAt_id' y).sub_const x)
  rw [mul_one] at h
  exact h.deriv

theorem pol_zero (c0 c1 c2 c3 c4 : ℝ) : pol c0 c1 c2 c3 c4 0 = c0 := by
  unfold pol
  ring

/-- **A `C⁴` function is a polynomial plus a function whose derivatives of
order at most four vanish at a given point.** -/
theorem exists_taylor_remainder {φ : ℝ → ℝ} (hφ : ContDiff ℝ 4 φ) (x : ℝ) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧
      ∀ j : ℕ, j ≤ 4 → iteratedDeriv j (fun y => φ y - p y) x = 0 := by
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℝ, a = fun j => iteratedDeriv j φ x := ⟨_, rfl⟩
  have hps : ContDiff ℝ ∞ (fun y : ℝ => pol (a 0) (a 1) (a 2 / 2) (a 3 / 6) (a 4 / 24) (y - x)) :=
    (contDiff_pol _ _ _ _ _).comp (contDiff_id.sub contDiff_const)
  refine ⟨fun y => pol (a 0) (a 1) (a 2 / 2) (a 3 / 6) (a 4 / 24) (y - x), hps, ?_⟩
  -- the derivatives of the polynomial at the point
  have hp : ∀ j : ℕ, j ≤ 4 → iteratedDeriv j
      (fun y : ℝ => pol (a 0) (a 1) (a 2 / 2) (a 3 / 6) (a 4 / 24) (y - x)) x = a j := by
    intro j hj
    interval_cases j
    · rw [iteratedDeriv_zero, sub_self, pol_zero]
    · rw [iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_zero, sub_self, pol_zero]
    · rw [iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_succ', deriv_pol_shift,
        iteratedDeriv_zero, sub_self, pol_zero]
      ring
    · rw [iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_succ', deriv_pol_shift,
        iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_zero, sub_self, pol_zero]
      ring
    · rw [iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_succ', deriv_pol_shift,
        iteratedDeriv_succ', deriv_pol_shift, iteratedDeriv_succ', deriv_pol_shift,
        iteratedDeriv_zero, sub_self, pol_zero]
      ring
  intro j hj
  have hj4 : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
  have h1 := iteratedDeriv_sub (n := j) (x := x) ((hφ.of_le hj4).contDiffAt)
    ((hps.of_le (by exact_mod_cast le_top)).contDiffAt (n := (j : WithTop ℕ∞)))
  have e : (fun y => φ y - pol (a 0) (a 1) (a 2 / 2) (a 3 / 6) (a 4 / 24) (y - x))
      = φ - fun y => pol (a 0) (a 1) (a 2 / 2) (a 3 / 6) (a 4 / 24) (y - x) := rfl
  rw [e, h1, hp j hj, hadef]
  ring

end Calabi.Weighted
