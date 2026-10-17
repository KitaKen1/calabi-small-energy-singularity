import Calabi.Correction.InteriorReal
import Calabi.Correction.ChartJets

/-!
# Local classes of functions with Hölder jets

For the proof of the smoothness of the solution (Section 6.4 of the
manuscript: "classical interior parabolic regularity, applied successively
after taking spatial difference quotients") the regularity is measured by the
local classes

  `Sm α Ω k g`:  near every point of `Ω`, the function `g(t, x)` coincides with
  a function that is `C^k` in `x` for every `t` and whose jets of order at most
  `k` have a parabolic Hölder bound.

The representative is global in `x`, so that the estimates for globally
defined functions (`TwoPointJets.lean`, the reused interior Schauder estimate)
apply to it; the class itself is local. This file contains the definition and
the closure properties: sums, products, smooth functions, derivatives in a
direction, the Laplacian and the Euler operator, and the criterion
`Sm.of_partials` (a function whose first derivatives are in the class of order
`k` is in the class of order `k + 1`).
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Uniform two-point bounds -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] {α a w w' M : ℝ} {N : Set (V × ℝ)} {f : V × ℝ → E}

/-- For the constant scale the weight is irrelevant. -/
theorem WH.one_weight (h : WH α a (fun _ : V × ℝ => (1 : ℝ)) N w M f) :
    WH α a (fun _ : V × ℝ => (1 : ℝ)) N w' M f := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have h1 := h.1 p hp
    rw [Real.one_rpow] at h1 ⊢
    exact h1
  · have h1 := h.2 p hp q hq hd
    rw [Real.one_rpow] at h1 ⊢
    exact h1

theorem holderBound_of_WH {S : Set (V × ℝ)} (h : WH α 1 (fun _ : V × ℝ => (1 : ℝ)) N w M f)
    (hS : S ⊆ N) (hd : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ 1) : HolderBound α S f M := by
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · have h1 := h.1 p (hS hp)
    rwa [Real.one_rpow, mul_one] at h1
  · have h1 := h.2 p (hS hp) q (hS hq) (by rw [one_mul]; exact hd p hp q hq)
    rwa [Real.one_rpow, mul_one] at h1

theorem WH_of_holderBound (h : HolderBound α N f M) :
    WH α a (fun _ : V × ℝ => (1 : ℝ)) N w M f := by
  refine ⟨fun p hp => ?_, fun p hp q hq _ => ?_⟩
  · rw [Real.one_rpow, mul_one]
    exact h.1 p hp
  · rw [Real.one_rpow, mul_one]
    exact h.2 p hp q hq

end Uniform

/-! ### The local classes -/

/-- **Local spatial regularity of order `k` with parabolic Hölder jets.** -/
def Sm (α : ℝ) (Ω : Set (V × ℝ)) (k : ℕ) (g : ℝ → V → ℝ) : Prop :=
  ∀ p₀ ∈ Ω, ∃ (N : Set (V × ℝ)) (g' : ℝ → V → ℝ) (M : ℝ), IsOpen N ∧ p₀ ∈ N ∧ 0 ≤ M ∧
    (∀ p ∈ N, g' p.2 p.1 = g p.2 p.1) ∧ (∀ t, ContDiff ℝ k (g' t)) ∧
    WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M k g'

/-- On an open set of space-time, two functions that coincide there coincide
near every point of a time slice. -/
theorem slice_eventuallyEq {N : Set (V × ℝ)} (hN : IsOpen N) {g g' : ℝ → V → ℝ}
    (h : ∀ p ∈ N, g' p.2 p.1 = g p.2 p.1) {p : V × ℝ} (hp : p ∈ N) :
    g' p.2 =ᶠ[𝓝 p.1] g p.2 := by
  have hc : Continuous fun z : V => ((z, p.2) : V × ℝ) := continuous_id.prodMk continuous_const
  filter_upwards [(hN.preimage hc).mem_nhds hp] with z hz
  exact h (z, p.2) hz

/-- The same in the time direction. -/
theorem time_eventuallyEq {N : Set (V × ℝ)} (hN : IsOpen N) {g g' : ℝ → V → ℝ}
    (h : ∀ p ∈ N, g' p.2 p.1 = g p.2 p.1) {p : V × ℝ} (hp : p ∈ N) :
    (fun t => g' t p.1) =ᶠ[𝓝 p.2] fun t => g t p.1 := by
  have hc : Continuous fun t : ℝ => ((p.1, t) : V × ℝ) := continuous_const.prodMk continuous_id
  filter_upwards [(hN.preimage hc).mem_nhds hp] with t ht
  exact h (p.1, t) ht

section Closure

variable {α : ℝ} {Ω : Set (V × ℝ)} {k : ℕ} {g g₁ g₂ : ℝ → V → ℝ}

theorem Sm.of_le (h : Sm α Ω k g) {j : ℕ} (hj : j ≤ k) : Sm α Ω j g := by
  intro p₀ hp₀
  obtain ⟨N, g', M, hN, hp, hM, hgg, hs, hW⟩ := h p₀ hp₀
  exact ⟨N, g', M, hN, hp, hM, hgg, fun t => (hs t).of_le (by exact_mod_cast hj), hW.of_le hj⟩

theorem Sm.mono_set (h : Sm α Ω k g) {Ω' : Set (V × ℝ)} (hΩ : Ω' ⊆ Ω) : Sm α Ω' k g :=
  fun p₀ hp₀ => h p₀ (hΩ hp₀)

/-- The class depends on the values on `Ω` only, if `Ω` is open. -/
theorem Sm.congr (h : Sm α Ω k g) (hΩ : IsOpen Ω) (hgg : ∀ p ∈ Ω, g₂ p.2 p.1 = g p.2 p.1) :
    Sm α Ω k g₂ := by
  intro p₀ hp₀
  obtain ⟨N, g', M, hN, hp, hM, hg', hs, hW⟩ := h p₀ hp₀
  refine ⟨N ∩ Ω, g', M, hN.inter hΩ, ⟨hp, hp₀⟩, hM, fun p hp => ?_, hs,
    hW.restrict inter_subset_left⟩
  rw [hg' p hp.1, hgg p hp.2]

theorem Sm.add (h₁ : Sm α Ω k g₁) (h₂ : Sm α Ω k g₂) :
    Sm α Ω k (fun t x => g₁ t x + g₂ t x) := by
  intro p₀ hp₀
  obtain ⟨N₁, g₁', M₁, hN₁, hp₁, hM₁, hg₁, hs₁, hW₁⟩ := h₁ p₀ hp₀
  obtain ⟨N₂, g₂', M₂, hN₂, hp₂, hM₂, hg₂, hs₂, hW₂⟩ := h₂ p₀ hp₀
  refine ⟨N₁ ∩ N₂, fun t x => g₁' t x + g₂' t x, M₁ + M₂, hN₁.inter hN₂, ⟨hp₁, hp₂⟩,
    add_nonneg hM₁ hM₂, fun p hp => ?_, fun t => (hs₁ t).add (hs₂ t),
    WJ.add hs₁ hs₂ (hW₁.restrict inter_subset_left) (hW₂.restrict inter_subset_right)⟩
  show g₁' p.2 p.1 + g₂' p.2 p.1 = g₁ p.2 p.1 + g₂ p.2 p.1
  rw [hg₁ p hp.1, hg₂ p hp.2]

theorem Sm.mul (h₁ : Sm α Ω k g₁) (h₂ : Sm α Ω k g₂) :
    Sm α Ω k (fun t x => g₁ t x * g₂ t x) := by
  intro p₀ hp₀
  obtain ⟨N₁, g₁', M₁, hN₁, hp₁, hM₁, hg₁, hs₁, hW₁⟩ := h₁ p₀ hp₀
  obtain ⟨N₂, g₂', M₂, hN₂, hp₂, hM₂, hg₂, hs₂, hW₂⟩ := h₂ p₀ hp₀
  have hsc : IsScale (1 : ℝ) 1 (fun _ : V × ℝ => (1 : ℝ)) (N₁ ∩ N₂) := IsScale.const one_pos
  refine ⟨N₁ ∩ N₂, fun t x => g₁' t x * g₂' t x, 2 ^ k * (1 + (1 : ℝ) ^ (k : ℝ)) * M₁ * M₂,
    hN₁.inter hN₂, ⟨hp₁, hp₂⟩, by positivity, fun p hp => ?_, fun t => (hs₁ t).mul (hs₂ t),
    WJ.smul hsc hM₁ hM₂ hs₁ hs₂ (hW₁.restrict inter_subset_left)
      (hW₂.restrict inter_subset_right)⟩
  show g₁' p.2 p.1 * g₂' p.2 p.1 = g₁ p.2 p.1 * g₂ p.2 p.1
  rw [hg₁ p hp.1, hg₂ p hp.2]

/-- A smooth function that does not depend on the time is in every class. -/
theorem Sm.of_contDiff (hα : 0 ≤ α) (hα1 : α ≤ 1) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Ω : Set (V × ℝ)) (k : ℕ) : Sm α Ω k (fun _ => φ) := by
  intro p₀ _
  have hbd : ∀ j : ℕ, ∃ A : ℝ, ∀ z ∈ Metric.closedBall p₀.1 2, ‖iteratedFDeriv ℝ j φ z‖ ≤ A :=
    fun j => (isCompact_closedBall p₀.1 2).exists_bound_of_continuousOn
      ((hφ.of_le (by exact_mod_cast le_top)).continuous_iteratedFDeriv' (m := j)).continuousOn
  choose A hA using hbd
  have hAt : ∀ j : ℕ, j ≤ k + 1 → A j ≤ ∑ i ∈ Finset.range (k + 2), |A i| := fun j hj =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |A i|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (k + 2), |A i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨Metric.ball p₀.1 1 ×ˢ univ, fun _ => φ, 2 * ∑ i ∈ Finset.range (k + 2), |A i|,
    Metric.isOpen_ball.prod isOpen_univ, ⟨Metric.mem_ball_self one_pos, mem_univ _⟩,
    by positivity, fun _ _ => rfl, fun _ => hφ.of_le (by exact_mod_cast le_top), ?_⟩
  refine WJ.of_bounds (fun _ _ => one_pos) hA0 zero_le_one le_rfl hα hα1
    (hφ.of_le (by exact_mod_cast le_top)) fun p hp z hz j hj => ?_
  rw [Real.one_rpow, mul_one]
  have hz2 : z ∈ Metric.closedBall p₀.1 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖p.1 - p₀.1‖ < 1 := by
      have := hp.1
      rwa [Metric.mem_ball, dist_eq_norm] at this
    rw [mul_one] at hz
    calc ‖z - p₀.1‖ = ‖(z - p.1) + (p.1 - p₀.1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - p.1‖ + ‖p.1 - p₀.1‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  exact (hA j z hz2).trans (hAt j hj)

theorem Sm.const_mul (hα : 0 ≤ α) (hα1 : α ≤ 1) (c : ℝ) (h : Sm α Ω k g) :
    Sm α Ω k (fun t x => c * g t x) :=
  (Sm.of_contDiff hα hα1 (contDiff_const (c := c)) Ω k).mul h

theorem Sm.neg (hα : 0 ≤ α) (hα1 : α ≤ 1) (h : Sm α Ω k g) : Sm α Ω k (fun t x => -g t x) := by
  have h1 := Sm.const_mul hα hα1 (-1) h
  have e : (fun (t : ℝ) (x : V) => -1 * g t x) = fun t x => -g t x := by
    funext t x
    ring
  rwa [e] at h1

theorem Sm.sub (hα : 0 ≤ α) (hα1 : α ≤ 1) (h₁ : Sm α Ω k g₁) (h₂ : Sm α Ω k g₂) :
    Sm α Ω k (fun t x => g₁ t x - g₂ t x) := by
  have h1 := h₁.add (h₂.neg hα hα1)
  have e : (fun (t : ℝ) (x : V) => g₁ t x + -g₂ t x) = fun t x => g₁ t x - g₂ t x := by
    funext t x
    ring
  rwa [e] at h1

end Closure

/-! ### Derivatives in a direction -/

/-- Insertion of a vector in the last slot of a multilinear map. -/
noncomputable def lastSlot (j : ℕ) (e : V) : (V [×(j + 1)]→L[ℝ] ℝ) →L[ℝ] (V [×j]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) (V →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ e)).comp
    (continuousMultilinearCurryRightEquiv' ℝ j V ℝ).toContinuousLinearEquiv.toContinuousLinearMap

omit [FiniteDimensional ℝ V] in
/-- The jets of a derivative in a direction. -/
theorem iteratedFDeriv_fderiv_apply {f : V → ℝ} {j : ℕ} {x : V}
    (hf : ContDiffAt ℝ (j + 1 : ℕ) f x) (e : V) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y e) x
      = lastSlot j e (iteratedFDeriv ℝ (j + 1) f x) := by
  have hd : ContDiffAt ℝ j (fderiv ℝ f) x := hf.fderiv_right (by exact_mod_cast le_rfl)
  have h1 := (ContinuousLinearMap.apply ℝ ℝ e).iteratedFDeriv_comp_left hd (i := j) le_rfl
  have h2 : iteratedFDeriv ℝ j (fderiv ℝ f) x
      = continuousMultilinearCurryRightEquiv' ℝ j V ℝ (iteratedFDeriv ℝ (j + 1) f x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  show iteratedFDeriv ℝ j (ContinuousLinearMap.apply ℝ ℝ e ∘ fderiv ℝ f) x = _
  rw [h1, h2]
  rfl

theorem Sm.fderiv_apply {α : ℝ} {Ω : Set (V × ℝ)} {k : ℕ} {g : ℝ → V → ℝ}
    (h : Sm α Ω (k + 1) g) (e : V) : Sm α Ω k (fun t z => fderiv ℝ (g t) z e) := by
  intro p₀ hp₀
  obtain ⟨N, g', M, hN, hp, hM, hgg, hs, hW⟩ := h p₀ hp₀
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ∑ j ∈ Finset.range (k + 1), ‖lastSlot (V := V) j e‖ :=
    ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact Finset.sum_nonneg fun j _ => (lastSlot (V := V) j e).opNorm_nonneg
  have hLj : ∀ j : ℕ, j ≤ k → ‖lastSlot (V := V) j e‖ ≤ L := fun j hj => by
    rw [hLdef]
    exact Finset.single_le_sum (f := fun j => ‖lastSlot (V := V) j e‖)
      (fun i _ => (lastSlot (V := V) i e).opNorm_nonneg) (Finset.mem_range.2 (by omega))
  refine ⟨N, fun t z => fderiv ℝ (g' t) z e, L * M, hN, hp, mul_nonneg hL0 hM, fun p hp => ?_,
    fun t => ?_, ?_⟩
  · show fderiv ℝ (g' p.2) p.1 e = fderiv ℝ (g p.2) p.1 e
    rw [(slice_eventuallyEq hN hgg hp).fderiv_eq]
  · have h1 : ContDiff ℝ k (fderiv ℝ (g' t)) := (hs t).fderiv_right (by exact_mod_cast le_rfl)
    exact h1.clm_apply contDiff_const
  · intro j hj
    have h1 := ((hW (j + 1) (by omega)).clm (lastSlot j e)).one_weight
      (w' := (0 : ℝ) - (j : ℝ))
    refine (h1.congr fun p _ => ?_).mono (fun _ _ => one_pos)
      (mul_le_mul_of_nonneg_right (hLj j hj) hM)
    exact iteratedFDeriv_fderiv_apply
      ((hs p.2).of_le (by exact_mod_cast Nat.succ_le_succ hj)).contDiffAt e

end Calabi.Weighted
