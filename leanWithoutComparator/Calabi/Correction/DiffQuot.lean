import Calabi.Correction.SmoothOps
import Calabi.Correction.PairLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Difference quotients

Tools for the method of difference quotients:

* `dq h e u`: the difference quotient of `u` in the direction `e` with the
  step `h`; its jets (`iteratedFDeriv_dq`), the dyadic identity
  `dq_sub_dq_half` and its convergence to the derivative (`tendsto_dq`);
* `holderBound_dq`: the difference quotients of a function whose first
  derivative has a parabolic Hölder bound have the same bound, uniformly in
  the step;
* `contDiff_of_seq`: the pointwise limit of a sequence of `C⁴` functions whose
  increments have summable uniform bounds of the jets is `C⁴`, and the jets
  converge.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The difference quotient in the direction `e` with the step `h`. -/
noncomputable def dq (h : ℝ) (e : V) (u : V → ℝ) (z : V) : ℝ := h⁻¹ * (u (z + h • e) - u z)

omit [FiniteDimensional ℝ V] in
theorem contDiff_dq {n : WithTop ℕ∞} {u : V → ℝ} (hu : ContDiff ℝ n u) (h : ℝ) (e : V) :
    ContDiff ℝ n (dq h e u) :=
  contDiff_const.mul ((hu.comp (contDiff_id.add contDiff_const)).sub hu)

omit [FiniteDimensional ℝ V] in
/-- The jets of a difference quotient. -/
theorem iteratedFDeriv_dq {u : V → ℝ} {j : ℕ} (hu : ContDiff ℝ j u) (h : ℝ) (e : V) (z : V) :
    iteratedFDeriv ℝ j (dq h e u) z
      = h⁻¹ • (iteratedFDeriv ℝ j u (z + h • e) - iteratedFDeriv ℝ j u z) := by
  have hs : ContDiff ℝ j (fun y => u (y + h • e)) := hu.comp (contDiff_id.add contDiff_const)
  have e1 : dq h e u = fun y => h⁻¹ • ((fun y => u (y + h • e)) y - u y) := by
    funext y
    rfl
  have e2 : iteratedFDeriv ℝ j (fun y => (fun y => u (y + h • e)) y - u y) z
      = iteratedFDeriv ℝ j (fun y => u (y + h • e)) z - iteratedFDeriv ℝ j u z :=
    iteratedFDeriv_sub_apply (f := fun y => u (y + h • e)) (g := u) hs.contDiffAt hu.contDiffAt
  rw [e1, iteratedFDeriv_const_smul_apply' (hs.sub hu).contDiffAt, e2,
    iteratedFDeriv_comp_add_right]

omit [FiniteDimensional ℝ V] in
theorem dq_congr_fun {u v : V → ℝ} (h : ℝ) (e : V) (z : V) (h1 : u (z + h • e) = v (z + h • e))
    (h2 : u z = v z) : dq h e u z = dq h e v z := by
  unfold dq
  rw [h1, h2]

omit [FiniteDimensional ℝ V] in
/-- **The dyadic identity** for difference quotients. -/
theorem dq_sub_dq_half (u : V → ℝ) {h : ℝ} (hh : h ≠ 0) (e : V) (z : V) :
    dq h e u z - dq (h / 2) e u z = h / 4 * dq (h / 2) e (dq (h / 2) e u) z := by
  have e1 : z + (h / 2) • e + (h / 2) • e = z + h • e := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  unfold dq
  rw [e1]
  field_simp
  ring

omit [FiniteDimensional ℝ V] in
/-- The difference quotients converge to the derivative. -/
theorem tendsto_dq {u : V → ℝ} {z : V} (hu : DifferentiableAt ℝ u z) (e : V) {h : ℕ → ℝ}
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    Tendsto (fun n => dq (h n) e u z) atTop (𝓝 (fderiv ℝ u z e)) := by
  have hline : HasDerivAt (fun r : ℝ => z + r • e) e 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
    simpa using h1
  have hφ : HasDerivAt (fun r : ℝ => u (z + r • e)) (fderiv ℝ u z e) 0 := by
    have h1 : HasFDerivAt u (fderiv ℝ u z) (z + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact hu.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℝ) hline
  have h2 := hφ.tendsto_slope_zero
  have h3 : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hh, Eventually.of_forall fun n => hne n⟩
  have h4 := h2.comp h3
  refine h4.congr fun n => ?_
  show (h n)⁻¹ • (u (z + (0 + h n) • e) - u (z + (0 : ℝ) • e)) = dq (h n) e u z
  rw [zero_add, zero_smul, add_zero]
  rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem pdist_shift (p q : V × ℝ) (v : V) :
    pdist ((p.1 + v, p.2) : V × ℝ) (q.1 + v, q.2) = pdist p q := by
  unfold pdist
  simp

omit [FiniteDimensional ℝ V] in
/-- **The difference quotients of a function with a Hölder first derivative.** -/
theorem holderBound_dq {α M : ℝ} {S S' : Set (V × ℝ)} {g : ℝ → V → ℝ}
    (hg : ∀ t, ContDiff ℝ 1 (g t)) (hα : 0 ≤ α)
    (hS : HolderBound α S (fun p => fderiv ℝ (g p.2) p.1) M) {h : ℝ} (hh : h ≠ 0) (e : V)
    (hseg : ∀ p ∈ S', ∀ s ∈ Icc (0 : ℝ) 1, ((p.1 + (s * h) • e, p.2) : V × ℝ) ∈ S) :
    HolderBound α S' (fun p => dq h e (g p.2) p.1) (M * ‖e‖) := by
  have hderiv : ∀ (t : ℝ) (z : V) (s : ℝ), HasDerivAt (fun r : ℝ => g t (z + (r * h) • e))
      (h * fderiv ℝ (g t) (z + (s * h) • e) e) s := by
    intro t z s
    have hline : HasDerivAt (fun r : ℝ => z + (r * h) • e) (h • e) s := by
      have h1 := (((hasDerivAt_id s).mul_const h).smul_const e).const_add z
      simpa using h1
    have h1 : HasFDerivAt (g t) (fderiv ℝ (g t) (z + (s * h) • e)) (z + (s * h) • e) :=
      ((hg t).differentiable one_ne_zero _).hasFDerivAt
    have h2 := h1.comp_hasDerivAt s hline
    rw [map_smul, smul_eq_mul] at h2
    exact h2
  constructor
  · intro p hp
    have hmv := exists_hasDerivAt_eq_slope (fun r : ℝ => g p.2 (p.1 + (r * h) • e))
      (fun s => h * fderiv ℝ (g p.2) (p.1 + (s * h) • e) e) zero_lt_one
      (fun s _ => (hderiv p.2 p.1 s).continuousAt.continuousWithinAt)
      (fun s _ => hderiv p.2 p.1 s)
    obtain ⟨ξ, hξ, hξe⟩ := hmv
    have hval : dq h e (g p.2) p.1 = fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) e := by
      have h1 : h * fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) e
          = g p.2 (p.1 + h • e) - g p.2 p.1 := by
        rw [hξe]
        simp
      unfold dq
      rw [← h1]
      field_simp
    show ‖dq h e (g p.2) p.1‖ ≤ M * ‖e‖
    rw [hval]
    have h2 := hS.1 _ (hseg p hp ξ ⟨hξ.1.le, hξ.2.le⟩)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg e))
  · intro p hp q hq
    have hmv := exists_hasDerivAt_eq_slope
      (fun r : ℝ => g p.2 (p.1 + (r * h) • e) - g q.2 (q.1 + (r * h) • e))
      (fun s => h * fderiv ℝ (g p.2) (p.1 + (s * h) • e) e
        - h * fderiv ℝ (g q.2) (q.1 + (s * h) • e) e) zero_lt_one
      (fun s _ => ((hderiv p.2 p.1 s).sub (hderiv q.2 q.1 s)).continuousAt.continuousWithinAt)
      (fun s _ => (hderiv p.2 p.1 s).sub (hderiv q.2 q.1 s))
    obtain ⟨ξ, hξ, hξe⟩ := hmv
    have hval : dq h e (g p.2) p.1 - dq h e (g q.2) q.1
        = (fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) - fderiv ℝ (g q.2) (q.1 + (ξ * h) • e)) e := by
      have h1 : h * fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) e
            - h * fderiv ℝ (g q.2) (q.1 + (ξ * h) • e) e
          = g p.2 (p.1 + h • e) - g q.2 (q.1 + h • e) - (g p.2 p.1 - g q.2 q.1) := by
        rw [hξe]
        simp
      have h2 : dq h e (g p.2) p.1 - dq h e (g q.2) q.1
          = h⁻¹ * (g p.2 (p.1 + h • e) - g q.2 (q.1 + h • e) - (g p.2 p.1 - g q.2 q.1)) := by
        unfold dq
        ring
      rw [h2, ← h1, ContinuousLinearMap.sub_apply]
      field_simp
    show ‖dq h e (g p.2) p.1 - dq h e (g q.2) q.1‖ ≤ M * ‖e‖ * pdist p q ^ α
    rw [hval]
    have h2 := hS.2 _ (hseg p hp ξ ⟨hξ.1.le, hξ.2.le⟩) _ (hseg q hq ξ ⟨hξ.1.le, hξ.2.le⟩)
    rw [pdist_shift p q ((ξ * h) • e)] at h2
    calc ‖(fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) - fderiv ℝ (g q.2) (q.1 + (ξ * h) • e)) e‖
        ≤ ‖fderiv ℝ (g p.2) (p.1 + (ξ * h) • e) - fderiv ℝ (g q.2) (q.1 + (ξ * h) • e)‖ * ‖e‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * pdist p q ^ α * ‖e‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg e)
      _ = M * ‖e‖ * pdist p q ^ α := by ring

/-- **The limit of a sequence of `C⁴` functions** whose increments have
summable uniform bounds of the jets. -/
theorem contDiff_of_seq {v : ℕ → V → ℝ} {g : V → ℝ} {b : ℕ → ℝ} (hv : ∀ n, ContDiff ℝ 4 (v n))
    (hb : Summable b)
    (hbd : ∀ n z, ∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j (fun y => v (n + 1) y - v n y) z‖ ≤ b n)
    (hlim : ∀ z, Tendsto (fun n => v n z) atTop (𝓝 (g z))) :
    ContDiff ℝ 4 g ∧ ∀ j : ℕ, j ≤ 4 → ∀ z,
      Tendsto (fun n => iteratedFDeriv ℝ j (v n) z) atTop (𝓝 (iteratedFDeriv ℝ j g z)) := by
  obtain ⟨hcd, hhs⟩ := tsum_jets (g := fun n y => v (n + 1) y - v n y)
    (fun n => (hv (n + 1)).sub (hv n)) hb hbd
  -- the limit is the series
  have hg : g = fun z => v 0 z + ∑' n, (v (n + 1) z - v n z) := by
    funext z
    have hsum : Summable fun n => v (n + 1) z - v n z := by
      refine Summable.of_norm_bounded hb fun n => ?_
      have h := hbd n z 0 (by norm_num)
      rwa [norm_iteratedFDeriv_zero] at h
    have h1 := (hsum.hasSum.tendsto_sum_nat).const_add (v 0 z)
    have h2 : Tendsto (fun n => v n z) atTop (𝓝 (v 0 z + ∑' n, (v (n + 1) z - v n z))) := by
      refine h1.congr fun n => ?_
      rw [Finset.sum_range_sub (fun m => v m z) n]
      ring
    exact tendsto_nhds_unique (hlim z) h2
  have hg4 : ContDiff ℝ 4 g := by
    rw [hg]
    exact (hv 0).add hcd
  refine ⟨hg4, fun j hj z => ?_⟩
  have hj4 : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
  have hpart : ∀ n, iteratedFDeriv ℝ j (v n) z = iteratedFDeriv ℝ j (v 0) z
      + ∑ m ∈ Finset.range n, iteratedFDeriv ℝ j (fun y => v (m + 1) y - v m y) z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : v (n + 1) = fun y => v n y + (v (n + 1) y - v n y) := by
        funext y
        ring
      have h1 : iteratedFDeriv ℝ j (fun y => v n y + (v (n + 1) y - v n y)) z
          = iteratedFDeriv ℝ j (v n) z
            + iteratedFDeriv ℝ j (fun y => v (n + 1) y - v n y) z :=
        iteratedFDeriv_add_apply (f := v n) (g := fun y => v (n + 1) y - v n y)
          ((hv n).of_le hj4).contDiffAt (((hv (n + 1)).sub (hv n)).of_le hj4).contDiffAt
      rw [e, h1, ih, Finset.sum_range_succ, add_assoc]
  have hlim' : iteratedFDeriv ℝ j g z = iteratedFDeriv ℝ j (v 0) z
      + iteratedFDeriv ℝ j (fun z => ∑' n, (v (n + 1) z - v n z)) z := by
    rw [hg]
    exact iteratedFDeriv_add_apply (f := v 0) (g := fun z => ∑' n, (v (n + 1) z - v n z))
      ((hv 0).of_le hj4).contDiffAt (hcd.of_le hj4).contDiffAt
  rw [hlim']
  have h2 := ((hhs j hj z).tendsto_sum_nat).const_add (iteratedFDeriv ℝ j (v 0) z)
  refine h2.congr fun n => ?_
  rw [hpart n]

end Calabi.Weighted
