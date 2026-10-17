import Calabi.Main

open Set Filter MeasureTheory
open scoped Topology ENNReal
open Calabi.Geometry

namespace CalabiFC

/-- Small curvature with one uniform margin below the prescribed tolerance.
The constructed flow has the scalar-curvature blow-up of manuscript (1.5).
Uniqueness among all smooth flows with the same initial metric is not asserted. -/
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
  obtain ⟨CS, hCS⟩ := Calabi.mainTheorem
  refine ⟨CS, fun p hp hp7 ε hε τ hτ => ?_⟩
  obtain ⟨T, F, hT, hTτ, hflow, hinv, hpot, hbounds, a, ha, hlim⟩ :=
    hCS p hp hp7 (ε / 2) (by positivity) τ hτ
  refine ⟨T, F, ε / 2, hT, hTτ, by positivity, by linarith, hflow, hinv, ?_, ?_,
    a, ha, hlim⟩
  · intro v hv
    exact lt_trans (hpot v hv) (by linarith)
  · intro t ht
    obtain ⟨hν, hn, hS⟩ := hbounds t ht
    exact ⟨hν, le_of_lt hn, hS⟩

/-- The energy case, with all geometric definitions expanded in the reference. -/
theorem small_calabi_energy : Calabi.Geometry.MainTheoremEnergy :=
  Calabi.mainTheoremEnergy

end CalabiFC
