import FCTargetDefinitions

open Set Filter MeasureTheory
open scoped Topology ENNReal
open Calabi.Geometry

namespace CalabiFC

theorem small_energy_singularity :
    ∃ CS : ℝ, ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
      ∃ (T : ℝ) (F : ℝ → Hom → ℝ) (η : ℝ),
        0 < T ∧ T < τ ∧ 0 < η ∧ η < ε ∧ IsCalabiFlow T F ∧
        (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
        (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
        (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
          eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) (ENNReal.ofReal p)
            (nu (pot (F t) 0)) ≤ ENNReal.ofReal η ∧
          HasSobolevBound (pot (F t) 0) CS) ∧
        ∃ a : ℝ, 0 < a ∧
          Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a) := by
  sorry

theorem small_calabi_energy : Calabi.Geometry.MainTheoremEnergy := by
  sorry

end CalabiFC
