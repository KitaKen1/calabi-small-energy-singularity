import Calabi.Correction.RealSolvers
import OAI.Analysis.AncientFlat.Geometry.WindowSchauder

/-!
# The interior Schauder estimate for real functions on a small cylinder

The reused interior estimate `OAI.ParabolicInterior.interior_schauder` is
stated for complex functions on the unit configuration (cylinder of radius
two, estimate on the cylinder of radius one). `interior_real` is the same
estimate

* for real functions,
* on the image of the unit configuration under a parabolic window
  `(x, t) ↦ (x₀ + q x, t₀ + q⁴ t)` of an arbitrary centre and scale `q ≤ 1`,
* with the conclusion stated for the jets of order at most four on the image
  of the smaller cylinder.

It is used as an a priori estimate for difference quotients in the proof of
the smoothness of the solution.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem norm_ofRealJet_le (j : ℕ) :
    ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℝ ℂ
      Complex.ofRealCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
  rw [one_mul, ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  have h := Complex.ofRealCLM.norm_compContinuousMultilinearMap_le φ
  rwa [Complex.ofRealCLM_norm, one_mul] at h

theorem iteratedFDeriv_ofReal {u : V → ℝ} {j : ℕ} (hu : ContDiff ℝ 4 u) (hj : j ≤ 4) (x : V) :
    iteratedFDeriv ℝ j (fun y => (u y : ℂ)) x
      = ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℝ ℂ
        Complex.ofRealCLM (iteratedFDeriv ℝ j u x) := by
  rw [ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  exact Complex.ofRealCLM.iteratedFDeriv_comp_left hu.contDiffAt (by exact_mod_cast hj)

/-- The bilaplacian of a real function regarded as a complex function. -/
theorem bilaplacian_ofReal {u : V → ℝ} (hu : ContDiff ℝ 4 u) (x : V) :
    Δ (Δ (fun y => (u y : ℂ))) x = ((Δ (Δ u) x : ℝ) : ℂ) := by
  have e1 := (hu.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)).contDiffAt.laplacian_CLM_comp_left_nhds
    (l := Complex.ofRealCLM) (x := x)
  have h2 := (contDiff_two_laplacian hu).contDiffAt.laplacian_CLM_comp_left
    (l := Complex.ofRealCLM) (x := x)
  show Δ (Δ (Complex.ofRealCLM ∘ u)) x = _
  rw [(InnerProductSpace.laplacian_congr_nhds e1).eq_of_nhds, h2]
  rfl

/-- The parabolic Hölder bounds of the jets of order at most four and of the
time derivative of a real function. -/
def RJet (α : ℝ) (Ω : Set (V × ℝ)) (u ut : ℝ → V → ℝ) (K : ℝ) : Prop :=
  (∀ j : ℕ, j ≤ 4 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (u p.2) p.1) K) ∧
    HolderBound α Ω (fun p => ut p.2 p.1) K

set_option maxHeartbeats 1600000 in
/-- **The interior Schauder estimate for real functions on a window.** -/
theorem interior_real (α κ K : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ (p0 : V × ℝ) (Ω : Set (V × ℝ)),
      MapsTo (window p0 q) (cylinder 2) Ω → ∀ a : V × ℝ → ℝ, HolderBound α Ω a K →
      (∀ p ∈ Ω, κ ≤ a p) → ∀ (u ut f : ℝ → V → ℝ) (F U : ℝ), 0 ≤ F → 0 ≤ U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p ∈ Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M : ℝ, 0 ≤ M ∧ RJet α Ω u ut M) →
      HolderBound α Ω (fun p => f p.2 p.1) F → (∀ p ∈ Ω, |u p.2 p.1| ≤ U) →
      (∀ p ∈ Ω, ut p.2 p.1 + a p * Δ (Δ (u p.2)) p.1 = f p.2 p.1) →
      ∀ j : ℕ, j ≤ 4 → HolderBound α (window p0 q '' cylinder 1)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (C / q ^ 5 * (F + U)) := by
  obtain ⟨C, hC, Hlocal⟩ := interior_schauder (V := V) α κ K hα hα1 hκ hK
  refine ⟨C, hC, ?_⟩
  intro q hq hq1 p0 Ω hm a ha hell u ut f F U hF hU hu hd hj hf hU' he j hj4
  obtain ⟨M, hM, hjr⟩ := hj
  -- the complex functions
  have hs : ∀ t, ContDiff ℝ 4 (fun x => (u t x : ℂ)) := fun t =>
    Complex.ofRealCLM.contDiff.comp (hu t)
  have hb : HolderBound α Ω (fun _ : V × ℝ => (0 : ℂ)) K :=
    ⟨fun _ _ => by rw [norm_zero]; exact hK, fun p _ q _ => by
      rw [sub_self, norm_zero]
      exact mul_nonneg hK (Real.rpow_nonneg (pdist_nonneg p q) _)⟩
  have hjc : JetBound α Ω (fun t x => (u t x : ℂ)) (fun t x => (ut t x : ℂ)) M := by
    constructor
    · intro n hn
      have h1 := ((hjr.1 n hn).clm (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin n => V) ℝ ℂ Complex.ofRealCLM)).mono
        (mul_le_of_le_one_left hM (norm_ofRealJet_le (V := V) n))
      have e : (fun p : V × ℝ => iteratedFDeriv ℝ n (fun x => (u p.2 x : ℂ)) p.1)
          = fun p => ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => V) ℝ ℂ
            Complex.ofRealCLM (iteratedFDeriv ℝ n (u p.2) p.1) :=
        funext fun p => iteratedFDeriv_ofReal (hu p.2) hn p.1
      rw [e]
      exact h1
    · have h1 := (hjr.2.clm Complex.ofRealCLM).mono
        (by rw [Complex.ofRealCLM_norm, one_mul])
      exact h1
  have hfc : HolderBound α Ω (fun p => (fun t x => (f t x : ℂ)) p.2 p.1) F := by
    have h1 := (hf.clm Complex.ofRealCLM).mono (by rw [Complex.ofRealCLM_norm, one_mul])
    exact h1
  have Hloc := Hlocal (fun p => a (window p0 q p)) (fun p => q ^ 4 • (0 : ℂ))
    (holder_window hα.le hq hq1 p0 ha hm) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm)
    (fun p hp => hell _ (hm hp))
    (windowValue p0 q (fun t x => (u t x : ℂ))) (windowTime p0 q (fun t x => (ut t x : ℂ)))
    (windowTime p0 q (fun t x => (f t x : ℂ))) F U hF hU
    (windowValue_contDiff p0 q _ hs)
    (fun p hp => window_hasDerivAt p0 q _ _ p ((hd _ (hm hp)).ofReal_comp))
    ⟨M, hM, window_jet_bound hα.le hM hq hq1 p0 _ _ hs hjc hm⟩
    (holder_window_smul hα.le hF hq hq1 p0 4 hfc hm)
    (fun p hp => by
      show ‖((u (p0.2 + q ^ 4 * p.2) (p0.1 + q • p.1) : ℝ) : ℂ)‖ ≤ U
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hU' _ (hm hp))
    (fun p hp => window_equation p0 q a (fun _ => 0) _ _ _ hs p (by
      have h1 := he _ (hm hp)
      rw [bilaplacian_ofReal (hu _), zero_mul, add_zero]
      exact_mod_cast h1))
  -- back to the real function on the image of the small cylinder
  have hq5 : 0 < q ^ 5 := pow_pos hq 5
  have hS : 0 ≤ C * (F + U) := mul_nonneg hC.le (add_nonneg hF hU)
  have hqj : q ^ 5 ≤ q ^ j := pow_le_pow_of_le_one hq.le hq1 (by omega)
  have hqj0 : 0 < q ^ j := pow_pos hq j
  have hre : ∀ P : V × ℝ, iteratedFDeriv ℝ j (u P.2) P.1
      = ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
        Complex.reCLM (iteratedFDeriv ℝ j (fun x => (u P.2 x : ℂ)) P.1) := by
    intro P
    have h1 := iteratedFDeriv_re (hs P.2) hj4 P.1
    simp only [Complex.ofReal_re] at h1
    exact h1
  have hwj : ∀ p : V × ℝ, iteratedFDeriv ℝ j (fun x => (u (window p0 q p).2 x : ℂ))
      (window p0 q p).1 = (q ^ j)⁻¹ • iteratedFDeriv ℝ j
        (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1 := by
    intro p
    rw [window_jet p0 q _ hs j hj4 p, smul_smul, inv_mul_cancel₀ hqj0.ne', one_smul]
  have hinv : (q ^ j)⁻¹ ≤ (q ^ 5)⁻¹ := inv_anti₀ hq5 hqj
  have hinv0 : 0 ≤ (q ^ j)⁻¹ := inv_nonneg.2 hqj0.le
  have hCq : C / q ^ 5 * (F + U) = (q ^ 5)⁻¹ * (C * (F + U)) := by
    field_simp
  constructor
  · rintro P ⟨p, hp, rfl⟩
    beta_reduce
    rw [hre, hwj]
    have h1 := (Hloc.1 j hj4).1 p hp
    calc ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
          Complex.reCLM ((q ^ j)⁻¹ • iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1)‖
        ≤ 1 * ‖(q ^ j)⁻¹ • iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_reJet_le (V := V) j) (norm_nonneg _))
      _ = (q ^ j)⁻¹ * ‖iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1‖ := by
          rw [one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
      _ ≤ (q ^ 5)⁻¹ * (C * (F + U)) := mul_le_mul hinv h1 (norm_nonneg _) (inv_nonneg.2 hq5.le)
      _ = C / q ^ 5 * (F + U) := hCq.symm
  · rintro P ⟨p, hp, rfl⟩ P' ⟨p', hp', rfl⟩
    beta_reduce
    have hdiff : iteratedFDeriv ℝ j (u (window p0 q p).2) (window p0 q p).1
        - iteratedFDeriv ℝ j (u (window p0 q p').2) (window p0 q p').1
        = ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
          Complex.reCLM ((q ^ j)⁻¹ • (iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1 - iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p'.2) p'.1)) := by
      rw [hre, hre, hwj, hwj, smul_sub, map_sub]
    rw [hdiff]
    have h1 := (Hloc.1 j hj4).2 p hp p' hp'
    have hpd : pdist (window p0 q p) (window p0 q p') = q * pdist p p' :=
      pdist_window p0 hq.le p p'
    have hpd0 := pdist_nonneg p p'
    have hqα : q ≤ q ^ α := by
      calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ α := Real.rpow_le_rpow_of_exponent_ge hq hq1 hα1.le
    have hqα0 : 0 < q ^ α := Real.rpow_pos_of_pos hq α
    have hpow : pdist p p' ^ α ≤ q⁻¹ * (q * pdist p p') ^ α := by
      rw [Real.mul_rpow hq.le hpd0, ← mul_assoc]
      have h2 : 1 ≤ q⁻¹ * q ^ α := by
        rw [← div_eq_inv_mul, one_le_div hq]
        exact hqα
      calc pdist p p' ^ α = 1 * pdist p p' ^ α := (one_mul _).symm
        _ ≤ q⁻¹ * q ^ α * pdist p p' ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hpd0 _)
    rw [hpd]
    have hinv4 : (q ^ j)⁻¹ ≤ (q ^ 4)⁻¹ :=
      inv_anti₀ (pow_pos hq 4) (pow_le_pow_of_le_one hq.le hq1 hj4)
    calc ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
          Complex.reCLM ((q ^ j)⁻¹ • (iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1 - iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p'.2) p'.1))‖
        ≤ 1 * ‖(q ^ j)⁻¹ • (iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1 - iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p'.2) p'.1)‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_reJet_le (V := V) j) (norm_nonneg _))
      _ = (q ^ j)⁻¹ * ‖iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p.2) p.1 - iteratedFDeriv ℝ j
            (windowValue p0 q (fun t x => (u t x : ℂ)) p'.2) p'.1‖ := by
          rw [one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
      _ ≤ (q ^ 4)⁻¹ * (C * (F + U) * pdist p p' ^ α) :=
          mul_le_mul hinv4 h1 (norm_nonneg _) (inv_nonneg.2 (pow_pos hq 4).le)
      _ ≤ (q ^ 4)⁻¹ * (C * (F + U) * (q⁻¹ * (q * pdist p p') ^ α)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hS)
            (inv_nonneg.2 (pow_pos hq 4).le)
      _ = C / q ^ 5 * (F + U) * (q * pdist p p') ^ α := by
          field_simp

end Calabi.Weighted
