import Calabi.Correction.Coefficients
import Calabi.Correction.SigmaTheta
import Calabi.Correction.RealSolvers

/-!
# The inner block

Near the point orbit, on `x ≤ 4θ` in the chart `x = |z|²`, the linearized
operator `P_λ = ∂ₜ + b_λ² A + c_λ` is close to the operator of the flat
self-similar profile, whose ancient inverse is reused from the upstream
library (`exists_ancient_real`). For a source `g` with a weighted bound in the
chart, Section 6.2 of the manuscript sets

  `W = D̂ (extension of χ_i g)`,   `U = χ_b W`,

with the cut-offs `χ_i = χ(x/θ)` and `χ_b = χ(x/(2θ))`. Then

  `P_λ U = χ_i g + J + err`,

where `J = b_λ² [A, χ_b] W` is the commutator, supported in `2θ ≤ x ≤ 4θ` and
bounded by the source (it is cancelled by the outer block), and `err` collects
the mismatch between `P_λ` and the flat operator on the support of `χ_b`: it is
`O(√θ)` times the source, because every mismatch term has a weight that is
higher by at least one than the weight of a source (Lemma 6.2 and (6.11)).

`inner_block` is this statement with constants that do not depend on `θ` and
`T ≤ (θ/4)²`. The weight is `w = -2 + 4γ` with the exponent `γ` of the reused
inverse, which depends on the profile only (not on the cut-off radius `λ`).
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted OAI.ParabolicAnnular Calabi.Chart Calabi.Radial
  Calabi.Osc Calabi.Flat

theorem rpow_le_self_of_one_le {x e : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (he : 1 ≤ e) :
    x ^ e ≤ x := by
  rcases hx0.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith)]
  · calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hx1 he
      _ = x := Real.rpow_one x

set_option maxHeartbeats 6400000 in
/-- **The inner block.** -/
theorem inner_block {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∀ lam : ℝ, 0 < lam → lam < 1 / 8 → ∀ α : ℝ, 0 < α → α < 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (θ T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ lam / 8 → 0 < T →
        T ≤ (θ / 4) ^ 2 → 0 ≤ F →
        WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4) F
          (fun p => g p.2 (‖p.1‖ ^ 2)) →
        ∃ (u ut : ℝ → Flat18 → ℝ) (J err : Flat18 × ℝ → ℝ),
          (∀ t, ContDiff ℝ 4 (u t)) ∧ (∀ t z, 4 * θ ≤ ‖z‖ ^ 2 → u t z = 0) ∧
          (∀ t z, 4 * θ ≤ ‖z‖ ^ 2 → ut t z = 0) ∧
          (∀ t : ℝ, t < 0 → ∀ z, HasDerivAt (fun r => u r z) (ut t z) t) ∧
          (∀ t (Q : Flat18 ≃ₗᵢ[ℝ] Flat18) z, u t (Q z) = u t z) ∧
          WJ α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ) (C * F) 4 u ∧
          WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4) (C * F)
            (fun p => ut p.2 p.1) ∧
          WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4) (C * F) J ∧
          (∀ p : Flat18 × ℝ, ‖p.1‖ ^ 2 < 2 * θ ∨ 4 * θ < ‖p.1‖ ^ 2 → J p = 0) ∧
          WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4)
            (C * Real.sqrt θ * F) err ∧
          (∀ p : Flat18 × ℝ, 4 * θ ≤ ‖p.1‖ ^ 2 → err p = 0) ∧
          ∀ t ∈ Ico (-T) 0, ∀ z : Flat18,
            ut t z + blam G lam t (‖z‖ ^ 2) ^ 2 * (chartOp 6 (u t) z / 16)
                + clam G lam t (‖z‖ ^ 2) * u t z
              = chiV θ z * g t (‖z‖ ^ 2) + J (z, t) + err (z, t) := by
  obtain ⟨H, hH, hH0, hmatch⟩ := hP.compact
  obtain ⟨κ, hκ, hpos⟩ := hP.lower
  obtain ⟨δ₀, hδ₀, hsmG⟩ := hP.smooth
  have hG : ContDiffOn ℝ ∞ G (Ici 0) := hsmG.mono fun y hy => by
    have : (0 : ℝ) ≤ y := hy
    show -δ₀ < y
    linarith
  obtain ⟨γ, hγ, hγ1, Hanc⟩ := exists_ancient_real hP.c_pos hκ hG hH hH0 hmatch hpos
  refine ⟨γ, hγ, hγ1, fun lam hlam hlam8 α hα hα1 => ?_⟩
  obtain ⟨Ca, hCa, Ha⟩ := Hanc α (1 / 64) hα hα1 (by norm_num) (by norm_num)
  obtain ⟨Aχ, hAχ, HAχ⟩ := WJ_chiV_sigma (V := Flat18)
  obtain ⟨C₁, hC₁, H₁⟩ := lowBound_lowOp (V := Flat18) 2 (-2 + 4 * γ) 2 6 (by norm_num)
  obtain ⟨C₂, hC₂, H₂⟩ := chartOp_comm_WH (V := Flat18) 2 (-2 + 4 * γ) 2 6 (by norm_num)
    (by norm_num)
  obtain ⟨Kc, hKc, HKc⟩ := coef_bounds hP α hα.le hα1.le
  obtain ⟨Mp, hMp, HMp⟩ := chart_Pmis (V := Flat18) (a := 1 / 64) hP hα.le hα1.le (by norm_num)
  obtain ⟨Mc, hMc, HMc⟩ := chart_cmis (V := Flat18) (a := 1 / 64) hP hα.le hα1.le (by norm_num)
  -- the constants
  obtain ⟨Bl, hBldef⟩ : ∃ Bl : ℝ, Bl = ‖(bilapL : (Flat18 [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hBl : 0 ≤ Bl := by
    rw [hBldef]
    exact norm_nonneg (bilapL : (Flat18 [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)
  obtain ⟨Kb, hKbdef⟩ : ∃ Kb : ℝ,
      Kb = |(1 / 16 : ℝ)| * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kc * Kc) := ⟨_, rfl⟩
  have hKb : 0 ≤ Kb := by rw [hKbdef]; positivity
  obtain ⟨cJ, hcJdef⟩ : ∃ cJ : ℝ, cJ = 2 ^ 4 * (1 + (2 : ℝ) ^ ((4 : ℕ) : ℝ)) * Aχ := ⟨_, rfl⟩
  have hcJ : 0 ≤ cJ := by rw [hcJdef]; positivity
  obtain ⟨ct, hctdef⟩ : ∃ ct : ℝ, ct = (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Aχ := ⟨_, rfl⟩
  have hct : 0 ≤ ct := by rw [hctdef]; positivity
  obtain ⟨cJ', hcJ'def⟩ : ∃ cJ' : ℝ, cJ' = (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (C₂ * Aχ) := ⟨_, rfl⟩
  have hcJ' : 0 ≤ cJ' := by rw [hcJ'def]; positivity
  obtain ⟨ce1, hce1def⟩ : ∃ ce1 : ℝ,
      ce1 = (1 + (2 : ℝ) ^ |(2 : ℝ)|) * (|(1 / 16 : ℝ)| * Mp) * (ct * Bl) := ⟨_, rfl⟩
  have hce1 : 0 ≤ ce1 := by rw [hce1def]; positivity
  obtain ⟨ce2, hce2def⟩ : ∃ ce2 : ℝ, ce2 = (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (ct * C₁) := ⟨_, rfl⟩
  have hce2 : 0 ≤ ce2 := by rw [hce2def]; positivity
  obtain ⟨ce3, hce3def⟩ : ∃ ce3 : ℝ, ce3 = (1 + (2 : ℝ) ^ |(-2 : ℝ)|) * Mc * cJ := ⟨_, rfl⟩
  have hce3 : 0 ≤ ce3 := by rw [hce3def]; positivity
  obtain ⟨Ctot, hCtotdef⟩ : ∃ Ctot : ℝ, Ctot = cJ + ct + cJ' + 6 * (ce1 + ce2 + ce3) := ⟨_, rfl⟩
  have hCtot : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  have hCaM : 0 ≤ Ca * ct := by positivity
  refine ⟨Ctot * (Ca * ct) + 1, by
    have : 0 ≤ Ctot * (Ca * ct) := by positivity
    linarith, ?_⟩
  intro θ T F g hθ hθlam hT hTθ hF hg
  -- the parameters
  have hθ4 : θ ≤ 1 / 4 := by linarith
  have hθsq : θ ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hθ.le hθ4 2
    norm_num at this
    linarith
  have hT1 : T ≤ 1 := by nlinarith
  have hTlam : T ≤ lam ^ 2 := by
    have h1 := pow_le_pow_left₀ hθ.le hθlam 2
    nlinarith [sq_nonneg lam]
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hs6 : 2 * (3 * Real.sqrt θ) ≤ 1 := by
    have h1 : Real.sqrt θ ≤ 1 / 6 := by
      have h2 := Real.sqrt_le_sqrt (show θ ≤ ((1 : ℝ) / 6) ^ 2 by norm_num; linarith)
      rwa [Real.sqrt_sq (by norm_num)] at h2
    linarith
  have hσpos := (isScale0 T).pos
  have hsub : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} := fun p hp => hp.1
  have hneg : dom0 T ⊆ {p : Flat18 × ℝ | p.2 < 0} := fun p hp => hp.1.2
  have hunit : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} := fun p hp =>
    ⟨hp.1, by linarith [hp.2]⟩
  have hball : ∀ p ∈ dom0 T, ‖p.1‖ ≤ 1 := fun p hp => by
    have := norm_nonneg p.1
    nlinarith [hp.2]
  -- the cut-offs
  have hχiW := HAχ α θ θ T (dom0 T) hθ le_rfl hTθ hsub hα.le hα1.le
  have hχbW := HAχ α θ (2 * θ) T (dom0 T) hθ (by linarith) hTθ hsub hα.le hα1.le
  have hχb4 : ContDiff ℝ 4 (chiV (V := Flat18) (2 * θ)) := contDiff_infty.1 (contDiff_chiV _) 4
  have hχb0 : ∀ z : Flat18, 4 * θ ≤ ‖z‖ ^ 2 → chiV (2 * θ) z = 0 := fun z hz =>
    chiV_of_ge (by positivity) (by linarith)
  have hχb1 : ∀ z : Flat18, ‖z‖ ^ 2 ≤ 2 * θ → chiV (2 * θ) z = 1 := fun z hz =>
    chiV_of_le (by positivity) hz
  -- the source and its extension by zero
  have hprod := WH.mul (isScale0 T) hAχ hF hχiW.value hg
  rw [zero_add] at hprod
  have hext := hprod.extend_zero0 (by positivity) (by norm_num) le_rfl hT1
    (fun p hp => by
      show chiV θ p.1 * g p.2 (‖p.1‖ ^ 2) = 0
      rw [chiV_of_ge hθ (by linarith), zero_mul])
  obtain ⟨W, Wt, hW4, hWd, hWeq, hWJ, hWtB, hWrad⟩ := Ha T _
    (fun p => chiV θ p.1 * g p.2 (‖p.1‖ ^ 2)) hT (by positivity) hext
    (fun Q p _ => by
      show chiV θ (Q p.1) * g p.2 (‖Q p.1‖ ^ 2) = chiV θ p.1 * g p.2 (‖p.1‖ ^ 2)
      rw [chiV_rotate, Q.norm_map])
  obtain ⟨WF, hWFdef⟩ : ∃ WF : ℝ, WF = Ca * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Aχ * F) := ⟨_, rfl⟩
  rw [← hWFdef] at hWJ hWtB
  have hWF : 0 ≤ WF := by rw [hWFdef]; positivity
  have hWFF : WF = Ca * ct * F := by
    rw [hWFdef, hctdef]
    ring
  have hW3 : ∀ t, ContDiff ℝ 3 (W t) := fun t => (hW4 t).of_le (by norm_num)
  have hWJ0 := (hWJ.restrict hneg).mono hσpos le_rfl
  have hWJ' : WJ α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ) WF 4 W := fun j hj =>
    (hWJ0 j hj).radius_le hσpos (by norm_num)
  have hWt' : WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4) WF
      (fun p => Wt p.2 p.1) := (hWtB.restrict hneg).radius_le hσpos (by norm_num)
  -- the bounds of `U = χ_b W`
  have hUJ := WJ.smul (isScale0 T) hAχ hWF (fun _ => hχb4) hW4 hχbW hWJ'
  rw [← hcJdef] at hUJ
  have hUt := WH.smul (isScale0 T) hAχ hWF hχbW.value hWt'
  rw [zero_add, ← hctdef] at hUt
  -- the coefficients
  obtain ⟨hbl, hcl, -, -⟩ := HKc lam T hlam hTlam hT1
  have hbl2 := (WH.mul (isScale0 T) hKc hKc hbl.1 hbl.1).const_smul (1 / 16)
  rw [zero_add, ← hKbdef] at hbl2
  have hPm := ((HMp 1 T one_pos (by rw [one_pow]; exact hT1) hT1).restrict hunit).const_smul
    (1 / 16)
  have hCm := (HMc 1 T one_pos (by rw [one_pow]; exact hT1) hT1).restrict hunit
  -- the commutator
  have hcomm := H₂ α (1 / 64) Aχ WF (sigma (V := Flat18)) (dom0 T) (fun _ => chiV (2 * θ)) W
    (isScale0 T) hAχ hWF (by norm_num) hα.le hα1.le (sigma_le_two0 hT1) hball (fun _ => hχb4)
    hW4 hχbW (hWJ'.of_le (by norm_num))
  have hJ := WH.mul (isScale0 T) hKb (by positivity) hbl2 hcomm
  rw [zero_add] at hJ
  -- the three mismatch terms
  have e4 : (-2 + 4 * γ : ℝ) - ((4 : ℕ) : ℝ) = -2 + 4 * γ - 4 := by norm_num
  have h4 := (hWJ' 4 le_rfl).clm bilapL
  rw [e4, ← hBldef] at h4
  have h4' : WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (-2 + 4 * γ - 4) (Bl * WF)
      (fun p => Δ (Δ (W p.2)) p.1) :=
    h4.congr fun p _ => bilaplacian_eq_bilapL (hW4 p.2) p.1
  have hq1 := WH.smul (isScale0 T) hAχ (mul_nonneg hBl hWF) hχbW.value h4'
  rw [zero_add, ← hctdef] at hq1
  have hlow := H₁ α (1 / 64) WF (sigma (V := Flat18)) (dom0 T) W (isScale0 T) hWF (by norm_num)
    hα.le hα1.le (sigma_le_two0 hT1) hball hW3 (hWJ'.of_le (by norm_num))
  have hq2 := WH.smul (isScale0 T) hAχ (mul_nonneg hC₁ hWF) hχbW.value hlow
  rw [zero_add, ← hctdef] at hq2
  have hq3 := hUJ.value
  have hE1 := WH.mul (isScale0 T) (by positivity : 0 ≤ |(1 / 16 : ℝ)| * Mp)
    (by positivity : 0 ≤ ct * (Bl * WF)) hPm hq1
  have hE2 := WH.mul (isScale0 T) hKb (by positivity : 0 ≤ ct * (C₁ * WF)) hbl2 hq2
  rw [zero_add] at hE2
  have hE3 := WH.mul (isScale0 T) hMc (by positivity : 0 ≤ cJ * WF) hCm hq3
  -- the scale on the support of `χ_b`
  have hS : ∀ p ∈ dom0 T, chiV (2 * θ) p.1 ≠ 0 → sigma p ≤ 3 * Real.sqrt θ := by
    intro p hp hne
    have hlt : ‖p.1‖ ^ 2 < 4 * θ := by
      by_contra hcon
      exact hne (hχb0 p.1 (not_lt.1 hcon))
    have h1 := sigma_le_norm_add hθ hTθ hp.1
    have h2 : ‖p.1‖ ≤ 2 * Real.sqrt θ := by
      have h3 : ‖p.1‖ ^ 2 ≤ (2 * Real.sqrt θ) ^ 2 := by
        rw [mul_pow, hsq]
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
    linarith
  have h6 : (0 : ℝ) ≤ 2 * (3 * Real.sqrt θ) := by positivity
  have hE1' := hE1.weight_supp (w' := -2 + 4 * γ - 4) (isScale0 T) (by positivity)
    (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt θ)
    (fun p hp hne => hS p hp fun h0 => hne (by
      show _ * (chiV (2 * θ) p.1 • _) = 0
      rw [h0, zero_smul, mul_zero])) (by linarith)
  have hE2' := hE2.weight_supp (w' := -2 + 4 * γ - 4) (isScale0 T) (by positivity)
    (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt θ)
    (fun p hp hne => hS p hp fun h0 => hne (by
      show _ * (chiV (2 * θ) p.1 • _) = 0
      rw [h0, zero_smul, mul_zero])) (by linarith)
  have hE3' := hE3.weight_supp (w' := -2 + 4 * γ - 4) (isScale0 T) (by positivity)
    (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt θ)
    (fun p hp hne => hS p hp fun h0 => hne (by
      show _ * (chiV (2 * θ) p.1 • _) = 0
      rw [h0, zero_smul, mul_zero])) (by linarith)
  have hErr := (hE1'.add hE2').add hE3'
  -- the constants
  have hCle : ∀ k : ℝ, k ≤ Ctot → k * WF ≤ (Ctot * (Ca * ct) + 1) * F := by
    intro k hk
    rw [hWFF]
    have h1 : 0 ≤ Ca * ct * F := by positivity
    have h2 := mul_le_mul_of_nonneg_right hk h1
    linarith
  have hk1 : cJ ≤ Ctot := by rw [hCtotdef]; linarith
  have hk2 : ct ≤ Ctot := by rw [hCtotdef]; linarith
  have hk3 : cJ' ≤ Ctot := by rw [hCtotdef]; linarith
  -- the supports
  have hcontN : Continuous fun y : Flat18 => ‖y‖ ^ 2 := continuous_norm.pow 2
  have hcomm0 : ∀ p : Flat18 × ℝ, ‖p.1‖ ^ 2 < 2 * θ ∨ 4 * θ < ‖p.1‖ ^ 2 →
      chartOp 6 (fun z => chiV (2 * θ) z • W p.2 z) p.1
        - chiV (2 * θ) p.1 • chartOp 6 (W p.2) p.1 = 0 := by
    intro p hp
    rcases hp with h | h
    · have hev : (fun z => chiV (2 * θ) z • W p.2 z) =ᶠ[𝓝 p.1] W p.2 := by
        filter_upwards [(isOpen_lt hcontN continuous_const).mem_nhds h] with z hz
        rw [hχb1 z (le_of_lt hz), one_smul]
      rw [chartOp_congr 6 hev, hχb1 p.1 h.le, one_smul, sub_self]
    · have hev : (fun z => chiV (2 * θ) z • W p.2 z) =ᶠ[𝓝 p.1] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const hcontN).mem_nhds h] with z hz
        rw [hχb0 z (le_of_lt hz), zero_smul]
      rw [chartOp_eq_zero_of_eventually 6 hev, hχb0 p.1 h.le, zero_smul, sub_zero]
  refine ⟨fun t z => chiV (2 * θ) z • W t z, fun t z => chiV (2 * θ) z • Wt t z,
    fun p => (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
      * (chartOp 6 (fun z => chiV (2 * θ) z • W p.2 z) p.1
        - chiV (2 * θ) p.1 • chartOp 6 (W p.2) p.1),
    fun p => (1 / 16 : ℝ) • ((1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2)) ^ 2
          * (1 - ‖p.1‖ ^ 2) ^ 2 - G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) ^ 2)
        * (chiV (2 * θ) p.1 • Δ (Δ (W p.2)) p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (chiV (2 * θ) p.1 • lowOp 6 (W p.2) p.1)
      + (2 * vstar (‖p.1‖ ^ 2) * (1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2))
            * Aop (Fss G p.2) (‖p.1‖ ^ 2)
          - 2 * ‖p.1‖ ^ 2 * G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) * AhatF G p.2 (‖p.1‖ ^ 2))
        * (chiV (2 * θ) p.1 • W p.2 p.1),
    fun t => hχb4.smul (hW4 t), fun t z hz => ?_, fun t z hz => ?_,
    fun t ht z => (hWd t ht z).const_smul (chiV (2 * θ) z), fun t Q z => ?_, ?_, ?_, ?_,
    fun p hp => ?_, ?_, fun p hp => ?_, fun t ht z => ?_⟩
  · show chiV (2 * θ) z • W t z = 0
    rw [hχb0 z hz, zero_smul]
  · show chiV (2 * θ) z • Wt t z = 0
    rw [hχb0 z hz, zero_smul]
  · show chiV (2 * θ) (Q z) • W t (Q z) = chiV (2 * θ) z • W t z
    rw [chiV_rotate, hWrad t Q z]
  · exact hUJ.mono hσpos (hCle cJ hk1)
  · exact hUt.mono hσpos (hCle ct hk2)
  · refine hJ.mono hσpos ?_
    have e : (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (C₂ * (Aχ * WF)) = cJ' * WF := by
      rw [hcJ'def]
      ring
    rw [e]
    exact hCle cJ' hk3
  · show (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
      * (chartOp 6 (fun z => chiV (2 * θ) z • W p.2 z) p.1
        - chiV (2 * θ) p.1 • chartOp 6 (W p.2) p.1) = 0
    rw [hcomm0 p hp, mul_zero]
  · refine hErr.mono hσpos ?_
    have hx1 := rpow_le_self_of_one_le (x := 2 * (3 * Real.sqrt θ))
      (e := 2 + (-2 + 4 * γ - 4) - (-2 + 4 * γ - 4)) h6 hs6 (by linarith)
    have hx2 := rpow_le_self_of_one_le (x := 2 * (3 * Real.sqrt θ))
      (e := -2 + 4 * γ - 3 - (-2 + 4 * γ - 4)) h6 hs6 (by linarith)
    have hx3 := rpow_le_self_of_one_le (x := 2 * (3 * Real.sqrt θ))
      (e := -2 + (-2 + 4 * γ) - (-2 + 4 * γ - 4)) h6 hs6 (by linarith)
    have hm1 := mul_le_mul_of_nonneg_left hx1
      (by positivity : 0 ≤ (1 + (2 : ℝ) ^ |(2 : ℝ)|) * (|(1 / 16 : ℝ)| * Mp) * (ct * (Bl * WF)))
    have hm2 := mul_le_mul_of_nonneg_left hx2
      (by positivity : 0 ≤ (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (ct * (C₁ * WF)))
    have hm3 := mul_le_mul_of_nonneg_left hx3
      (by positivity : 0 ≤ (1 + (2 : ℝ) ^ |(-2 : ℝ)|) * Mc * (cJ * WF))
    have hsum : (1 + (2 : ℝ) ^ |(2 : ℝ)|) * (|(1 / 16 : ℝ)| * Mp) * (ct * (Bl * WF))
          * (2 * (3 * Real.sqrt θ))
        + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (ct * (C₁ * WF)) * (2 * (3 * Real.sqrt θ))
        + (1 + (2 : ℝ) ^ |(-2 : ℝ)|) * Mc * (cJ * WF) * (2 * (3 * Real.sqrt θ))
        = 6 * (ce1 + ce2 + ce3) * WF * Real.sqrt θ := by
      rw [hce1def, hce2def, hce3def]
      ring
    have hk4 : 6 * (ce1 + ce2 + ce3) ≤ Ctot := by rw [hCtotdef]; linarith
    have h7 := mul_le_mul_of_nonneg_right (hCle _ hk4) hsθ.le
    calc _ ≤ (1 + (2 : ℝ) ^ |(2 : ℝ)|) * (|(1 / 16 : ℝ)| * Mp) * (ct * (Bl * WF))
            * (2 * (3 * Real.sqrt θ))
          + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb * (ct * (C₁ * WF)) * (2 * (3 * Real.sqrt θ))
          + (1 + (2 : ℝ) ^ |(-2 : ℝ)|) * Mc * (cJ * WF) * (2 * (3 * Real.sqrt θ)) :=
          add_le_add (add_le_add hm1 hm2) hm3
      _ = 6 * (ce1 + ce2 + ce3) * WF * Real.sqrt θ := hsum
      _ ≤ (Ctot * (Ca * ct) + 1) * Real.sqrt θ * F := by linarith [h7]
  · show (1 / 16 : ℝ) • ((1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2)) ^ 2
          * (1 - ‖p.1‖ ^ 2) ^ 2 - G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) ^ 2)
        * (chiV (2 * θ) p.1 • Δ (Δ (W p.2)) p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (chiV (2 * θ) p.1 • lowOp 6 (W p.2) p.1)
      + (2 * vstar (‖p.1‖ ^ 2) * (1 + vstar (‖p.1‖ ^ 2) * Fss G p.2 (‖p.1‖ ^ 2))
            * Aop (Fss G p.2) (‖p.1‖ ^ 2)
          - 2 * ‖p.1‖ ^ 2 * G (‖p.1‖ ^ 2 / Real.sqrt (-p.2)) * AhatF G p.2 (‖p.1‖ ^ 2))
        * (chiV (2 * θ) p.1 • W p.2 p.1) = 0
    rw [hχb0 p.1 hp]
    simp
  · -- the identity
    have ht0 : t < 0 := ht.2
    have hx0 : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
    have hWz := hWeq t ht z
    have ha := chartOp_eq_lowOp 6 (W t) z
    have hb : chiV (2 * θ) z * chiV θ z = chiV θ z := by
      rcases le_or_gt (‖z‖ ^ 2) (2 * θ) with h | h
      · rw [hχb1 z h, one_mul]
      · rw [chiV_of_ge hθ h.le, mul_zero]
    have hpP : profilePrincipal G (z, t) = G (‖z‖ ^ 2 / Real.sqrt (-t)) ^ 2 / 16 := rfl
    have hpV : profilePotential G (z, t)
        = 2 * ‖z‖ ^ 2 * G (‖z‖ ^ 2 / Real.sqrt (-t)) * AhatF G t (‖z‖ ^ 2) := by
      rw [two_x_G_AhatF hP ht0 hx0]
      rfl
    have hc' : (blam G lam t (‖z‖ ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 16 - profilePrincipal G (z, t))
          * chiV (2 * θ) z
        = (1 / 16 : ℝ) * ((1 + vstar (‖z‖ ^ 2) * Fss G t (‖z‖ ^ 2)) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2
          - G (‖z‖ ^ 2 / Real.sqrt (-t)) ^ 2) * chiV (2 * θ) z := by
      rcases lt_or_ge (‖z‖ ^ 2) (4 * θ) with h | h
      · rw [hpP, blam_of_lt hlam t (by linarith : ‖z‖ ^ 2 < lam)]
        ring
      · rw [hχb0 z h, mul_zero, mul_zero]
    have hd' : (clam G lam t (‖z‖ ^ 2) - profilePotential G (z, t)) * chiV (2 * θ) z
        = (2 * vstar (‖z‖ ^ 2) * (1 + vstar (‖z‖ ^ 2) * Fss G t (‖z‖ ^ 2))
            * Aop (Fss G t) (‖z‖ ^ 2)
          - 2 * ‖z‖ ^ 2 * G (‖z‖ ^ 2 / Real.sqrt (-t)) * AhatF G t (‖z‖ ^ 2))
          * chiV (2 * θ) z := by
      rcases lt_or_ge (‖z‖ ^ 2) (4 * θ) with h | h
      · rw [hpV, clam_of_lt hP hlam ht0 ⟨hx0, by linarith⟩ (by linarith : ‖z‖ ^ 2 < lam)]
      · rw [hχb0 z h, mul_zero, mul_zero]
    show chiV (2 * θ) z • Wt t z
        + blam G lam t (‖z‖ ^ 2) ^ 2 * (chartOp 6 (fun y => chiV (2 * θ) y • W t y) z / 16)
        + clam G lam t (‖z‖ ^ 2) * (chiV (2 * θ) z • W t z)
      = chiV θ z * g t (‖z‖ ^ 2)
        + (1 / 16 : ℝ) • (blam G lam t (‖z‖ ^ 2) * blam G lam t (‖z‖ ^ 2))
          * (chartOp 6 (fun y => chiV (2 * θ) y • W t y) z
            - chiV (2 * θ) z • chartOp 6 (W t) z)
        + ((1 / 16 : ℝ) • ((1 + vstar (‖z‖ ^ 2) * Fss G t (‖z‖ ^ 2)) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2
              - G (‖z‖ ^ 2 / Real.sqrt (-t)) ^ 2) * (chiV (2 * θ) z • Δ (Δ (W t)) z)
          + (1 / 16 : ℝ) • (blam G lam t (‖z‖ ^ 2) * blam G lam t (‖z‖ ^ 2))
            * (chiV (2 * θ) z • lowOp 6 (W t) z)
          + (2 * vstar (‖z‖ ^ 2) * (1 + vstar (‖z‖ ^ 2) * Fss G t (‖z‖ ^ 2))
                * Aop (Fss G t) (‖z‖ ^ 2)
              - 2 * ‖z‖ ^ 2 * G (‖z‖ ^ 2 / Real.sqrt (-t)) * AhatF G t (‖z‖ ^ 2))
            * (chiV (2 * θ) z • W t z))
    rw [hWz]
    simp only [smul_eq_mul]
    linear_combination g t (‖z‖ ^ 2) * hb + Δ (Δ (W t)) z * hc' + W t z * hd'
      + (1 / 16 : ℝ) * (blam G lam t (‖z‖ ^ 2) * blam G lam t (‖z‖ ^ 2)) * chiV (2 * θ) z * ha

end Calabi.Weighted
