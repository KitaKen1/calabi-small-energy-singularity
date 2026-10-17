import Calabi.Correction.TwoPointMore

/-!
# Evaluation along a ray and change of chart

A quantity of order zero of the construction is a function of the time and of
the momentum coordinate `x`. In the chart at `x = 0` it is evaluated at
`|z|² = x`, in the chart at `x = 1` at `|w|² = 1 - x`. A function on one chart
that is radial, or that is evaluated along a fixed ray, is transferred to the
other chart by the map `swapPt`. This file gives the weighted two-point bounds
for these compositions; they are instances of `WH.comp_map`.

* `rayMap e p = (|p.1| e, p.2)`, `WH.ray`: evaluation along the ray of the unit
  vector `e`, for a scale that depends on `|z|` and `t` only;
* `swapPt e p = (√(1 - |p.1|²) e, p.2)`, `WH.swap`: the change of chart, on a
  region `|p.1|² ≤ 1 - δ²` where the map is Lipschitz, between two scales that
  are comparable there.
-/

open Set
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
variable {E : Type*} [NormedAddCommGroup E]

/-! ### The ray of a unit vector -/

/-- The point of the ray of `e` at the distance `|p.1|` from the origin. -/
def rayMap (e : V) (p : V × ℝ) : V × ℝ := (‖p.1‖ • e, p.2)

theorem norm_rayMap {e : V} (he : ‖e‖ = 1) (p : V × ℝ) : ‖(rayMap e p).1‖ = ‖p.1‖ := by
  show ‖‖p.1‖ • e‖ = ‖p.1‖
  rw [norm_smul, he, mul_one, norm_norm]

theorem pdist_rayMap_le {e : V} (he : ‖e‖ = 1) (p q : V × ℝ) :
    pdist (rayMap e p) (rayMap e q) ≤ pdist p q := by
  show ‖‖p.1‖ • e - ‖q.1‖ • e‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4)
    ≤ ‖p.1 - q.1‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4)
  have h : ‖‖p.1‖ • e - ‖q.1‖ • e‖ ≤ ‖p.1 - q.1‖ := by
    rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    exact abs_norm_sub_norm_le _ _
  linarith

theorem sigma_rayMap {e : V} (he : ‖e‖ = 1) (p : V × ℝ) : sigma (rayMap e p) = sigma p := by
  unfold sigma
  rw [norm_rayMap he]
  rfl

/-- **Evaluation along a ray.** -/
theorem WH.ray {α a v M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E} {e : V}
    (hf : WH α a s Ω v M f) (he : ‖e‖ = 1) (hM : 0 ≤ M) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hpos : ∀ p ∈ Ω, 0 < s p) (hΩ : ∀ p ∈ Ω, rayMap e p ∈ Ω)
    (hs : ∀ p ∈ Ω, s (rayMap e p) = s p) :
    WH α a s Ω v M (fun p => f (rayMap e p)) := by
  have h := hf.comp_map (k := 1) (L := 1) (s' := s) (Ω' := Ω) (Φ := rayMap e) hM le_rfl le_rfl
    ha hα hΩ hpos hpos (fun p hp => by rw [hs p hp, one_mul])
    (fun p hp => by rw [hs p hp, one_mul])
    (fun p _ q _ => by rw [one_mul]; exact pdist_rayMap_le he p q)
  rw [mul_one, div_one, Real.one_rpow, Real.one_rpow, mul_one, mul_one] at h
  exact h

/-! ### The change of chart -/

/-- The point of the other chart, on the ray of `e`, with the same momentum
coordinate. -/
noncomputable def swapPt (e : V) (p : V' × ℝ) : V × ℝ :=
  (Real.sqrt (1 - ‖p.1‖ ^ 2) • e, p.2)

theorem norm_swapPt {e : V} (he : ‖e‖ = 1) (p : V' × ℝ) :
    ‖(swapPt e p).1‖ = Real.sqrt (1 - ‖p.1‖ ^ 2) := by
  show ‖Real.sqrt (1 - ‖p.1‖ ^ 2) • e‖ = _
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_sq_swapPt {e : V} (he : ‖e‖ = 1) {p : V' × ℝ} (hp : ‖p.1‖ ^ 2 ≤ 1) :
    ‖(swapPt e p).1‖ ^ 2 = 1 - ‖p.1‖ ^ 2 := by
  rw [norm_swapPt he, Real.sq_sqrt (by linarith)]

theorem abs_sqrt_sub_sqrt_le {x y δ : ℝ} (hδ : 0 < δ) (hx : δ ^ 2 ≤ x) (hy : δ ^ 2 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / (2 * δ) := by
  have hx0 : 0 ≤ x := (sq_nonneg δ).trans hx
  have hy0 : 0 ≤ y := (sq_nonneg δ).trans hy
  have h1 : δ ≤ Real.sqrt x := by
    have := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_sq hδ.le] at this
  have h2 : δ ≤ Real.sqrt y := by
    have := Real.sqrt_le_sqrt hy
    rwa [Real.sqrt_sq hδ.le] at this
  have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    have e1 := Real.sq_sqrt hx0
    have e2 := Real.sq_sqrt hy0
    nlinarith
  rw [le_div_iff₀ (by positivity), e, abs_mul,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt x + Real.sqrt y)]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

theorem pdist_swapPt_le {e : V} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ) {p q : V' × ℝ}
    (hp : ‖p.1‖ ^ 2 ≤ 1 - δ ^ 2) (hq : ‖q.1‖ ^ 2 ≤ 1 - δ ^ 2) :
    pdist (swapPt e p) (swapPt e q) ≤ 1 / δ * pdist p q := by
  show ‖Real.sqrt (1 - ‖p.1‖ ^ 2) • e - Real.sqrt (1 - ‖q.1‖ ^ 2) • e‖
    + |p.2 - q.2| ^ ((1 : ℝ) / 4) ≤ 1 / δ * (‖p.1 - q.1‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4))
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hpn := norm_nonneg p.1
  have hqn := norm_nonneg q.1
  have hp1 : ‖p.1‖ ≤ 1 := by nlinarith
  have hq1 : ‖q.1‖ ≤ 1 := by nlinarith
  have hδ1 : δ ≤ 1 := by nlinarith [sq_nonneg ‖p.1‖]
  have h1 := abs_sqrt_sub_sqrt_le hδ (by linarith : δ ^ 2 ≤ 1 - ‖p.1‖ ^ 2)
    (by linarith : δ ^ 2 ≤ 1 - ‖q.1‖ ^ 2)
  have h2 : |1 - ‖p.1‖ ^ 2 - (1 - ‖q.1‖ ^ 2)| ≤ 2 * ‖p.1 - q.1‖ := by
    have e : 1 - ‖p.1‖ ^ 2 - (1 - ‖q.1‖ ^ 2) = (‖q.1‖ - ‖p.1‖) * (‖q.1‖ + ‖p.1‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖q.1‖ + ‖p.1‖), abs_sub_comm]
    calc |‖p.1‖ - ‖q.1‖| * (‖q.1‖ + ‖p.1‖) ≤ ‖p.1 - q.1‖ * 2 :=
          mul_le_mul (abs_norm_sub_norm_le _ _) (by linarith) (by linarith) (norm_nonneg _)
      _ = 2 * ‖p.1 - q.1‖ := by ring
  have h3 : ‖Real.sqrt (1 - ‖p.1‖ ^ 2) • e - Real.sqrt (1 - ‖q.1‖ ^ 2) • e‖
      ≤ 1 / δ * ‖p.1 - q.1‖ := by
    rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / δ * ‖p.1 - q.1‖ * (2 * δ) = 2 * ‖p.1 - q.1‖ := by
      field_simp
    rw [e]
    exact h2
  have h4 : (1 : ℝ) ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have h5 : 0 ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
  have h6 : |p.2 - q.2| ^ ((1 : ℝ) / 4) ≤ 1 / δ * |p.2 - q.2| ^ ((1 : ℝ) / 4) :=
    le_mul_of_one_le_left h5 h4
  linarith

/-- **The change of chart.** -/
theorem WH.swap {α a v M k δ : ℝ} {s : V × ℝ → ℝ} {s' : V' × ℝ → ℝ} {D : Set (V × ℝ)}
    {Ω' : Set (V' × ℝ)} {f : V × ℝ → E} {e : V} (hf : WH α a s D v M f) (he : ‖e‖ = 1)
    (hM : 0 ≤ M) (hk : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hΦ : ∀ p ∈ Ω', swapPt e p ∈ D) (hball : ∀ p ∈ Ω', ‖p.1‖ ^ 2 ≤ 1 - δ ^ 2)
    (hs : ∀ p ∈ D, 0 < s p) (hs' : ∀ p ∈ Ω', 0 < s' p)
    (h1 : ∀ p ∈ Ω', s (swapPt e p) ≤ k * s' p) (h2 : ∀ p ∈ Ω', s' p ≤ k * s (swapPt e p)) :
    WH α (a / (k * (1 / δ))) s' Ω' v (M * k ^ (|v| + |v - α|) * (1 / δ) ^ α)
      (fun p => f (swapPt e p)) := by
  have hL : (1 : ℝ) ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  exact hf.comp_map (Φ := swapPt e) hM hk hL ha hα hΦ hs hs' h1 h2
    (fun p hp q hq => pdist_swapPt_le he hδ (hball p hp) (hball q hq))

end Calabi.Weighted
