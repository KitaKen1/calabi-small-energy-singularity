import Integration.Reuse
import Calabi.ShrinkingProfile

/-!
# The ancient inverse for the profile of Theorem 3.1

`Calabi.shrinking_profile` supplies exactly the hypotheses of the reused
weighted inverse `Calabi.Reuse.dimension_eighteen_inverse`: smoothness of `G`
on `[0, ∞)`, a positive lower bound, and the smooth extension of
`H(u) = G(u^{-1/2})` to `u = 0` with `H(0) = c`. This file records the
combination, so that the interface between the profile and the inner inverse
is checked by the compiler.
-/

open Set
open scoped ContDiff

namespace Calabi.Reuse

noncomputable section

open OAI.FlatWeighted OAI.FlatSimilarity

/-- The conclusion of `dimension_eighteen_inverse` as a property of the
profile `G`. -/
def HasAncientInverse (G : ℝ → ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
    ∃ D : sourceSpace (V := FlatSpace) (1 / 4) (-2 + 4 * γ) (1 / 16) →ₗ[ℝ]
      (FlatSpace × ℝ → ℂ),
    ∀ f : sourceSpace (V := FlatSpace) (1 / 4) (-2 + 4 * γ) (1 / 16),
      (∀ t : ℝ, ContDiff ℝ 4 (fun x => D f (x, t))) ∧
      (∀ t : ℝ, t < 0 → ∀ x : FlatSpace,
        HasDerivAt (fun r => D f (x, r)) (profileTime G f.val (D f) t x) t) ∧
      xNorm (EuclideanSpace.basisFun (Fin 18) ℝ) (1 / 4) (-2 + 4 * γ) (1 / 16)
        (fun t x => D f (x, t)) (profileTime G f.val (D f)) ≤
        ENNReal.ofReal (C * sourceNorm (1 / 4) (-2 + 4 * γ) (1 / 16) f) ∧
      (∀ t, Radial (fun x => D f (x, t))) ∧
      (∀ t, RealValued (fun x => D f (x, t)))

/-- **The profile of Theorem 3.1 together with its ancient inverse.** -/
theorem profile_with_inverse :
    ∃ (c : ℝ) (G : ℝ → ℝ), 0 < c ∧ c < 1 ∧ ContDiffOn ℝ ∞ G (Ici 0) ∧
      (∀ y, 0 < y → y ^ 3 * iteratedDeriv 3 G y + 15 * y ^ 2 * iteratedDeriv 2 G y
        + 42 * y * deriv G y - 42 * (G y - 1) = y ^ 2 / 2 * ((G y)⁻¹ - c⁻¹)) ∧
      G 0 = 1 ∧ (∃ g, g < 0 ∧ HasDerivWithinAt G g (Ici 0) 0) ∧
      (∃ κ, 0 < κ ∧ ∀ y, 0 ≤ y → κ ≤ G y) ∧ (∃ M, ∀ y, 0 ≤ y → G y ≤ M) ∧
      HasAncientInverse G := by
  obtain ⟨c, G, H, hc0, hc1, hG, hode, hG0, hG', ⟨κ, hκ, hpos⟩, hM, hH, hH0, hmatch⟩ :=
    Calabi.shrinking_profile
  exact ⟨c, G, hc0, hc1, hG, hode, hG0, hG', ⟨κ, hκ, hpos⟩, hM,
    dimension_eighteen_inverse G H c κ hc0 hκ hG hH hH0 hmatch hpos⟩

end

end Calabi.Reuse
