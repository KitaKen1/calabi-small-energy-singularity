import FCTargetDefinitions
import CalabiSmallEnergy
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
set_option maxRecDepth 4096
set_option maxHeartbeats 0
local notation "ℂ⁷" => EuclideanSpace ℂ (Fin 7)
local notation "ℂ⁸" => (Fin 8 → ℂ)

namespace CalabiFC

def DraftMain : Prop :=  ¬ ∀ n : ℕ, CalabiFlowConjecture n
def DraftTen : Prop :=  ¬ CalabiFlowConjecture 10
def DraftSeven : Prop :=  ¬ CalabiFlowConjecture 7

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

theorem scal_eq : @CalabiFC.scal 7 = scal := rfl

theorem flow_iff (T : ℝ) (F : ℝ → ℂ⁸ → ℝ) :
    CalabiFC.IsCalabiFlow 7 T F ↔ IsCalabiFlow T F := by
  have hu (t : ℝ) (j : Fin 8) :
      (fun Z : Aff => Real.log (1 + ‖Z‖ ^ 2) + F t (CalabiFC.chart j Z)) = pot (F t) j := rfl
  constructor
  · rintro ⟨hs, hk, hf⟩
    refine ⟨hs, ?_, ?_⟩
    · intro t ht
      refine ⟨⟨?_, (hk t ht).1⟩, (hk t ht).2⟩
      exact hs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun v hv => ⟨ht, hv⟩)
    · simpa only [scal_eq, hu, CalabiFC.chart, chart, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, show (7 : ℝ) * (7 + 1) = 56 by norm_num] using hf
  · intro h
    refine ⟨h.smooth, ?_, ?_⟩
    · intro t ht
      exact ⟨(h.kahler t ht).smoothCP.invariant, (h.kahler t ht).pos⟩
    · simpa only [scal_eq, hu, CalabiFC.chart, chart, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, show (7 : ℝ) * (7 + 1) = 56 by norm_num] using h.flow

/-- Smooth extension makes the time derivative at the origin continuous. The
Calabi equation identifies that derivative with scalar curvature minus 56. -/
theorem blowup_prevents_extension {T : ℝ} {F : ℝ → ℂ⁸ → ℝ}
    (hT : 0 < T) (hF : IsCalabiFlow T F) {a : ℝ} (ha : 0 < a)
    (hblow : Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0)
      (𝓝[<] T) (𝓝 a)) : ¬ CalabiFC.CalabiFlowConjecture 7 := by
  intro h
  obtain ⟨T', G, hTT', hG, hmatch⟩ := h T F hT ((flow_iff T F).mpr hF)
  let v : ℂ⁸ := chart 0 0
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    simpa [v, chart] using hh
  have hcurve : ContDiffOn ℝ ∞ (fun t => G t v) (Ico 0 T') :=
    hG.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht, hv⟩)
  have hc : ContinuousAt (fun t => deriv (fun s => G s v) t + 56) T :=
    ((hcurve.contDiffAt (Ico_mem_nhds_iff.mpr ⟨hT, hTT'⟩)).derivWithin
      (m := 0) (by simp)).continuousAt.add continuousAt_const
  have heq : (fun t => deriv (fun s => G s v) t + 56) =ᶠ[𝓝[<] T]
      (fun t => scal (pot (F t) 0) 0) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hT).filter_mono inf_le_left] with t ht hpos
    have hnhds : Ico 0 T ∈ 𝓝 t := Ico_mem_nhds_iff.mpr ⟨hpos, ht⟩
    have heq' : (fun s => G s v) =ᶠ[𝓝 t] (fun s => F s v) := by
      filter_upwards [hnhds] with s hs
      exact hmatch s hs v hv
    have hd := ((hF.flow t ⟨hpos.le, ht⟩ 0).hasDerivAt hnhds).congr_of_eventuallyEq heq'
    have hd' := hd.deriv
    change deriv (fun s => G s v) t = scal (pot (F t) 0) 0 - 56 at hd'
    linarith
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (T - t)) (𝓝[<] T) (𝓝 0) := by
    have hs : Continuous (fun t : ℝ => Real.sqrt (T - t)) :=
      Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
    simpa using (hs.tendsto T).mono_left (show 𝓝[<] T ≤ 𝓝 T from inf_le_left)
  have hz : Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0)
      (𝓝[<] T) (𝓝 0) := by
    have hh := hsqrt.mul (hc.tendsto.mono_left inf_le_left)
    simp only [zero_mul] at hh
    exact hh.congr' (heq.mono fun t ht => congrArg (fun x => Real.sqrt (T - t) * x) ht)
  exact (ne_of_gt ha) (tendsto_nhds_unique hblow hz)

theorem reference_implies_seven : ReferenceMain → CalabiFC.DraftSeven := by
  rintro ⟨CS, h⟩
  obtain ⟨T, F, η, hT, _, _, _, hF, _, _, _, a, ha, hblow⟩ :=
    h 2 le_rfl (by norm_num) 1 (by norm_num) 1 (by norm_num)
  exact blowup_prevents_extension hT hF ha hblow

theorem reference_implies_calabi_flow : ReferenceMain → CalabiFC.DraftMain := by
  intro h hglobal
  exact reference_implies_seven h (hglobal 7)

#print axioms reference_implies_calabi_flow
#print axioms flow_iff
#print axioms reference_implies_seven

end CalabiFCDraftCheck
