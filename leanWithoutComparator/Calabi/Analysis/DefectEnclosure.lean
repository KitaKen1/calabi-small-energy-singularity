import Mathlib.Analysis.ODE.Gronwall

open Set
open scoped NNReal

namespace Calabi.Certificate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A checked polynomial residual can control a true trajectory on a tube.
Existence and continuation of the true trajectory are separate obligations. -/
theorem residual_enclosure
    {v : ℝ → E → E} {tube : ℝ → Set E} {K : ℝ≥0}
    {P P' u : ℝ → E} {a b δ ε : ℝ}
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (tube t))
    (hP : ContinuousOn P (Icc a b))
    (hP' : ∀ t ∈ Ico a b, HasDerivWithinAt P (P' t) (Ici t) t)
    (hdefect : ∀ t ∈ Ico a b, dist (P' t) (v t (P t)) ≤ ε)
    (hPtube : ∀ t ∈ Ico a b, P t ∈ tube t)
    (hu : ContinuousOn u (Icc a b))
    (hu' : ∀ t ∈ Ico a b, HasDerivWithinAt u (v t (u t)) (Ici t) t)
    (hutube : ∀ t ∈ Ico a b, u t ∈ tube t)
    (hinitial : dist (P a) (u a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (P t) (u t) ≤ gronwallBound δ K ε (t - a) := by
  have hexact : ∀ t ∈ Ico a b, dist (v t (u t)) (v t (u t)) ≤ (0 : ℝ) := by
    intro t ht
    simp
  simpa only [add_zero] using dist_le_of_approx_trajectories_ODE_of_mem
    hv hP hP' hdefect hPtube hu hu' hexact hutube hinitial

end Calabi.Certificate
