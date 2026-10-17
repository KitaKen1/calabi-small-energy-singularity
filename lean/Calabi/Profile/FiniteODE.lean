import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace Calabi.ProfileSeven

noncomputable section

/-- In logarithmic radius: `(G, DG, D²G, y²)`, where `D = y ∂y`. -/
abbrev LogState := ℝ × ℝ × ℝ × ℝ

/-- The dimension-seven profile equation as an autonomous first-order system.
The last coordinate incorporates the otherwise time-dependent factor `y²`. -/
def logVectorField (c : ℝ) (z : LogState) : LogState :=
  (z.2.1, z.2.2.1,
    -12 * z.2.2.1 - 29 * z.2.1 + 42 * (z.1 - 1) +
      (z.2.2.2 / 2) * (z.1⁻¹ - c⁻¹),
    2 * z.2.2.2)

/-- The third component has exactly the expanded profile-ODE residual. -/
theorem logVectorField_profile_equation (c : ℝ) (z : LogState) :
    (logVectorField c z).2.2.1 + 12 * z.2.2.1 + 29 * z.2.1 -
      42 * (z.1 - 1) = (z.2.2.2 / 2) * (z.1⁻¹ - c⁻¹) := by
  dsimp [logVectorField]
  ring

theorem logVectorField_contDiffAt (c : ℝ) {z : LogState} (hz : z.1 ≠ 0) :
    ContDiffAt ℝ 1 (logVectorField c) z := by
  unfold logVectorField
  fun_prop (disch := assumption)

/-- A genuine local trajectory exists at every positive state and stays away
from the singular denominator. This is a local theorem; the finite certificate
must still establish continuation and bounds on the whole shooting interval. -/
theorem local_positive_log_solution (c t₀ : ℝ) {z₀ : LogState} (hz : 0 < z₀.1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ u : ℝ → LogState, u t₀ = z₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt u (logVectorField c (u t)) t ∧ z₀.1 / 2 < (u t).1 := by
  obtain ⟨u, hu₀, ε, hε, hu⟩ :=
    (logVectorField_contDiffAt c (ne_of_gt hz)).
      exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  have hc : ContinuousAt (fun t => (u t).1) t₀ := (hu t₀ ht₀).continuousAt.fst
  have hp : ∀ᶠ t in 𝓝 t₀, z₀.1 / 2 < (u t).1 :=
    continuousAt_const.eventually_lt hc (by rw [hu₀]; linarith)
  obtain ⟨l, r, hlr, hpos⟩ := hp.exists_Ioo_subset
  let η := min ε (min (t₀ - l) (r - t₀))
  have hη : 0 < η := lt_min hε (lt_min (sub_pos.mpr hlr.1) (sub_pos.mpr hlr.2))
  refine ⟨η, hη, u, hu₀, ?_⟩
  intro t ht
  have hηε : η ≤ ε := min_le_left _ _
  have hηl : η ≤ t₀ - l := (min_le_right _ _).trans (min_le_left _ _)
  have hηr : η ≤ r - t₀ := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨hu t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    hpos ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

end

end Calabi.ProfileSeven
