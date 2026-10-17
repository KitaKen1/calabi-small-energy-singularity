import OAI.Analysis.AncientFlat.Weighted.ExactWeightedInverse
import OAI.Analysis.AncientFlat.Regularity.ShortHolder
import OAI.Analysis.SphereIsometry.CompactConvexFixedPoint

open Set
open scoped ContDiff

namespace Calabi.Reuse

noncomputable section

abbrev FlatSpace := EuclideanSpace ℝ (Fin 18)

open OAI.FlatWeighted OAI.FlatSimilarity

/-- The generic OpenAI inverse specialized to the auxiliary dimension 18.
All profile assumptions remain explicit here; this is an analytic building block. -/
theorem dimension_eighteen_inverse
    (G H : ℝ → ℝ) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0 = c) (hmatch : ∀ u : ℝ, 0 < u → H u = G (u ^ (-(1 : ℝ) / 2)))
    (hpos : ∀ y : ℝ, 0 ≤ y → κ ≤ G y) :
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
        (∀ t, RealValued (fun x => D f (x, t))) := by
  obtain ⟨γ, hγ, hγ1, hinv⟩ := exact_weighted_inverse
    (EuclideanSpace.basisFun (Fin 18) ℝ) G H c κ hc hκ hG hH hH0 hmatch hpos
  obtain ⟨C, hC, D, hD⟩ := hinv (1 / 4) (1 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨γ, hγ, hγ1, C, hC, D, hD⟩

open OAI.ParabolicInterior OAI.ParabolicInitial

/-- Fixed rational Hölder exponents keep later localization statements small. -/
theorem short_time_jets :
    ∃ C : ℝ, 0 < C ∧ ∀ h M : ℝ, 0 < h → h ≤ 1 → 0 ≤ M →
      ∀ u : ℝ → FlatSpace → ℝ,
      (∀ x : FlatSpace, ‖x‖ < 2 → u 0 x = 0) →
      (∀ j : ℕ, j ≤ 4 → HolderBound (1 / 2) (slab 2 h)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) M) →
      ∀ j : ℕ, j ≤ 4 → HolderBound (1 / 4) (slab 1 h)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (C * h ^ ((1 : ℝ) / 16) * M) := by
  convert OAI.ParabolicShort.spatial_small (V := FlatSpace) (E := ℝ)
    (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

/-- The two shooting parameters live in a compact convex subset of ℝ². -/
theorem shooting_fixed_point {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {g : ℝ × ℝ → ℝ × ℝ}
    (hg : ContinuousOn g K) (hmap : MapsTo g K K) :
    ∃ x ∈ K, g x = x :=
  OAI.Tingley.exists_fixedPoint_of_isCompact_convex hK hne hconv hg hmap

end

end Calabi.Reuse
