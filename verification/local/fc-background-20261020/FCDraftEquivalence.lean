import FCTargetDefinitions
import CalabiSmallEnergy

open Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 0
local notation "ℂ⁷" => EuclideanSpace ℂ (Fin 7)
local notation "ℂ⁸" => (Fin 8 → ℂ)

namespace CalabiFC

def DraftMain : Prop := 
    ∃ CS : ℝ, ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
      ∃ (T : ℝ) (F : ℝ → ℂ⁸ → ℝ) (η : ℝ),
        0 < T ∧ T < τ ∧ 0 < η ∧ η < ε ∧ IsCalabiFlow T F ∧
        (∀ v : ℂ⁸, v ≠ 0 → |F 0 v| < ε) ∧
        (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
          eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) (ENNReal.ofReal p)
            (nu (pot (F t) 0)) ≤ ENNReal.ofReal η ∧ HasSobolevBound (pot (F t) 0) CS) ∧
        ∃ a : ℝ, 0 < a ∧
          Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

end CalabiFC

namespace CalabiFCDraftCheck
open Calabi.Geometry

def ReferenceMain : Prop := 
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
          Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

theorem gmat_eq : CalabiFC.gmat = gmat := rfl

theorem scal_eq : CalabiFC.scal = scal := by
  funext u Z
  simp only [CalabiFC.scal, gmat_eq, scal, detg]

theorem nu_eq : CalabiFC.nu = nu := by
  funext u
  simp only [CalabiFC.nu, gmat_eq, nu, volMeasure, detg]

theorem pot_eq : CalabiFC.pot = pot := rfl

theorem smooth_iff (F : ℂ⁸ → ℝ) : CalabiFC.IsSmoothCP F ↔ IsSmoothCP F :=
  ⟨fun h => ⟨h.smooth, h.invariant⟩, fun h => ⟨h.smooth, h.invariant⟩⟩

theorem flow_iff (T : ℝ) (F : ℝ → ℂ⁸ → ℝ) :
    CalabiFC.IsCalabiFlow T F ↔
      IsCalabiFlow T F ∧ (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) := by
  constructor
  · intro h
    refine ⟨⟨h.smooth, ?_, h.flow⟩, h.invariant⟩
    intro t ht
    exact ⟨(smooth_iff (F t)).mp (h.kahler t ht).1, (h.kahler t ht).2⟩
  · rintro ⟨h, hi⟩
    refine ⟨h.smooth, ?_, hi, h.flow⟩
    intro t ht
    exact ⟨(smooth_iff (F t)).mpr (h.kahler t ht).smoothCP, (h.kahler t ht).pos⟩

theorem sobolev_iff (u : ℂ⁷ → ℝ) (C : ℝ) :
    CalabiFC.HasSobolevBound u C ↔ HasSobolevBound u C := by
  constructor
  · intro h f hf
    exact h f ((smooth_iff f).mpr hf)
  · intro h f hf
    exact h f ((smooth_iff f).mp hf)

theorem main_equivalence : CalabiFC.DraftMain ↔ ReferenceMain := by
  simp only [CalabiFC.DraftMain, ReferenceMain, flow_iff, sobolev_iff, scal_eq, nu_eq, pot_eq, and_assoc]

#print axioms main_equivalence

end CalabiFCDraftCheck
