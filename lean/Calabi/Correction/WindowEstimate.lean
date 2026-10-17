import OAI.Analysis.AncientFlat.Regularity.InitialSchauder
import OAI.Analysis.AncientFlat.Geometry.WindowJets

/-!
# The initial Schauder estimate on a window

`window_initial_estimate` is the a priori estimate
`OAI.ParabolicInitial.initial_schauder` for the equation `u_t + a Δ² u = f`
with zero initial data, written on a parabolic window with centre `x₀` and
scale `q`: for the rescaled functions `u(q⁴ θ, x₀ + q y)` on the slab
`{|y| < 2} × [0, R / q⁴]`, with the coefficient and the source measured in the
same units. The constant does not depend on the centre, the scale or the time
`R ≤ q⁴`. The qualitative hypothesis of the estimate (finite Hölder norms down
to the initial time) is the conclusion of `exists_zero_data_jets` in
`Calabi/Correction/FlatZero.lean`.
-/

open Set Filter
open scoped Topology ContDiff Laplacian

namespace Calabi.FlatZero

open OAI OAI.ParabolicInterior OAI.ParabolicInitial OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The time derivative given by the equation `u_t + a Δ² u = f`. -/
noncomputable def utOf (a : ℝ → V → ℝ) (f u : ℝ → V → ℂ) (t : ℝ) (x : V) : ℂ :=
  f t x - (a t x : ℂ) * Δ (Δ (u t)) x

theorem window_mem_slab {x₀ : V} {q R ρ : ℝ} (hq : 0 < q) {p : V × ℝ}
    (hp : p ∈ slab ρ (R / q ^ 4)) : (window (x₀, 0) q p).2 ∈ Icc (0 : ℝ) R := by
  have hq4 : 0 < q ^ 4 := pow_pos hq 4
  have h1 := hp.2.1
  have h2 := hp.2.2
  refine ⟨?_, ?_⟩
  · show 0 ≤ 0 + q ^ 4 * p.2
    have := mul_nonneg hq4.le h1
    linarith
  · show 0 + q ^ 4 * p.2 ≤ R
    have h3 : q ^ 4 * p.2 ≤ q ^ 4 * (R / q ^ 4) := mul_le_mul_of_nonneg_left h2 hq4.le
    rw [mul_div_cancel₀ R hq4.ne'] at h3
    linarith

/-- The time derivative on a window, within the time interval of the window. -/
theorem window_hasDerivWithinAt {x₀ : V} {q R ρ : ℝ} (hq : 0 < q) {u ut : ℝ → V → ℂ}
    (hd : ∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Icc 0 R) t)
    {p : V × ℝ} (hp : p ∈ slab ρ (R / q ^ 4)) :
    HasDerivWithinAt (fun t => windowValue (x₀, 0) q u t p.1)
      (windowTime (x₀, 0) q ut p.2 p.1) (Icc 0 (R / q ^ 4)) p.2 := by
  have hmem := window_mem_slab (x₀ := x₀) hq hp
  have h1 := hd (window (x₀, 0) q p).2 hmem (window (x₀, 0) q p).1
  have h2 : HasDerivWithinAt (fun θ : ℝ => 0 + q ^ 4 * θ) (q ^ 4) (Icc 0 (R / q ^ 4)) p.2 := by
    have h3 := ((hasDerivAt_id' p.2).const_mul (q ^ 4)).const_add 0
    rw [mul_one] at h3
    exact h3.hasDerivWithinAt
  have hmt : MapsTo (fun θ : ℝ => 0 + q ^ 4 * θ) (Icc 0 (R / q ^ 4)) (Icc 0 R) := by
    intro θ hθ
    exact window_mem_slab (x₀ := x₀) (ρ := 2) (p := ((0 : V), θ)) hq ⟨by simp, hθ⟩
  exact h1.scomp p.2 h2 hmt

/-- **The initial Schauder estimate on a window.** -/
theorem window_initial_estimate (α κ K : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ)
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (a : ℝ → V → ℝ) (f u : ℝ → V → ℂ),
      (∀ t, ContDiff ℝ 4 (u t)) → (∀ x, u 0 x = 0) →
      (∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun s => u s x) (utOf a f u t x) (Icc 0 R) t) →
      (∃ M : ℝ, 0 ≤ M ∧ JetBound α {p : V × ℝ | p.2 ∈ Icc 0 R} u (utOf a f u) M) →
      ∀ (x₀ : V) (q : ℝ), 0 < q → q ≤ 1 → R ≤ q ^ 4 →
      HolderBound α (slab 2 (R / q ^ 4))
        (fun p => a (window (x₀, 0) q p).2 (window (x₀, 0) q p).1) K →
      (∀ p ∈ slab 2 (R / q ^ 4), κ ≤ a (window (x₀, 0) q p).2 (window (x₀, 0) q p).1) →
      ∀ (F U : ℝ), 0 ≤ F → 0 ≤ U →
      HolderBound α (slab 2 (R / q ^ 4)) (fun p => windowTime (x₀, 0) q f p.2 p.1) F →
      (∀ p ∈ slab 2 (R / q ^ 4), ‖windowValue (x₀, 0) q u p.2 p.1‖ ≤ U) →
      JetBound α (slab 1 (R / q ^ 4)) (windowValue (x₀, 0) q u)
        (windowTime (x₀, 0) q (utOf a f u)) (C * (F + U)) := by
  obtain ⟨C, hC, HS⟩ := initial_schauder (V := V) α κ K hα hα1 hκ hK
  refine ⟨C, hC, ?_⟩
  intro R hR a f u hs hu0 hd hj x₀ q hq hq1 hRq ha hκa F U hF hU hf hU'
  have hq4 : 0 < q ^ 4 := pow_pos hq 4
  have hh : 0 < R / q ^ 4 := div_pos hR hq4
  have hh1 : R / q ^ 4 ≤ 1 := (div_le_one hq4).2 hRq
  obtain ⟨M, hM, hJ⟩ := hj
  have hmaps : MapsTo (window (x₀, 0) q) (slab 2 (R / q ^ 4)) {p : V × ℝ | p.2 ∈ Icc 0 R} :=
    fun p hp => window_mem_slab hq hp
  refine HS (R / q ^ 4) hh hh1 (fun p => a (window (x₀, 0) q p).2 (window (x₀, 0) q p).1)
    (fun _ => 0) ha ⟨fun p _ => by simpa using hK, fun p _ z _ => by
      simp only [sub_self, norm_zero]
      exact mul_nonneg hK (Real.rpow_nonneg (pdist_nonneg p z) _)⟩ hκa
    (windowValue (x₀, 0) q u) (windowTime (x₀, 0) q (utOf a f u)) (windowTime (x₀, 0) q f)
    F U hF hU (windowValue_contDiff (x₀, 0) q u hs) ?_ ?_
    ⟨M, hM, window_jet_bound hα.le hM hq hq1 (x₀, 0) u (utOf a f u) hs hJ hmaps⟩ hf hU' ?_
  · -- the time derivative on the window
    intro p hp
    exact window_hasDerivWithinAt hq hd hp
  · -- zero initial data
    intro x _
    show u (0 + q ^ 4 * 0) (x₀ + q • x) = 0
    rw [mul_zero, add_zero]
    exact hu0 _
  · -- the equation
    intro p _
    have he := window_equation (x₀, 0) q (fun p : V × ℝ => a p.2 p.1) (fun _ => 0)
      u (utOf a f u) f hs p (by
        simp only [utOf]
        ring)
    simpa using he

end Calabi.FlatZero
