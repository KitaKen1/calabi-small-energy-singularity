import Calabi.Correction.FlatZero
import Calabi.Correction.WindowConvert
import Calabi.Correction.Extension

/-!
# The forward block

`exists_forward_solution` packages the flat forward theory for use in the
approximate inverse of Section 6 of the manuscript, in the two-point form of
`TwoPoint.lean`. For a time-independent coefficient `a₀` (equal to one outside
a ball) and a `1`-Lipschitz scale `s` with `0 < s_min ≤ s ≤ s_max ≤ 16`, the
problem

  `u_t + a₀ Δ² u = f`,  `u(0) = 0`  on `[0, R]`,  `R ≤ (s_min/16)⁴ / C`,

has a solution whose jets satisfy the weighted bound `C F` in terms of the
weighted bound `F` of the source (Lemma 4.4), and whose jets of order at most
three are smaller by the factor `ε + C_ε R / (s_min/16)⁴` (Lemma 4.5, (4.16)).
The constants depend only on the Hölder exponent, the ellipticity bounds, the
two-point bound of the coefficient and the weight.
-/

open Set
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicInitial OAI.ParabolicLocalization Calabi.FlatZero

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A power of a number between two positive bounds, from below. -/
theorem rpow_ge_min {x lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ x) (h2 : x ≤ hi) (v : ℝ) :
    min (lo ^ v) (hi ^ v) ≤ x ^ v := by
  rcases le_or_gt 0 v with hv | hv
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow hlo.le h1 hv)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hlo.trans_le h1) h2 hv.le)

/-- A `1`-Lipschitz scale changes at most by the factor two on the boxes of
size `s/16`. -/
theorem scale_comparable {s : V → ℝ} (hs : ∀ x, 0 < s x) (hl : ∀ x y, |s x - s y| ≤ ‖x - y‖)
    (x₀ x : V) (h : ‖x - x₀‖ < 2 * (1 / 16 * s x₀)) : s x ≤ 2 * s x₀ ∧ s x₀ ≤ 2 * s x := by
  have h1 := abs_le.1 (hl x x₀)
  have h2 := hs x₀
  constructor <;> linarith [h1.1, h1.2]

variable [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1600000 in
/-- **The forward block**: existence and weighted estimates for the forward
problem with a time-independent coefficient. -/
theorem exists_forward_solution (α κ Λ K w : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ)
    (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (s : V → ℝ) (smin smax ρ₀ L J R F : ℝ) (a₀ : V → ℝ) (f : ℝ → V → ℂ),
        0 < smin → (∀ x, smin ≤ s x) → (∀ x, s x ≤ smax) → smax ≤ 16 →
        (∀ x y, |s x - s y| ≤ ‖x - y‖) →
        (∀ x, a₀ x ∈ Icc κ Λ) → (∀ x, ρ₀ ≤ ‖x‖ → a₀ x = 1) → 0 ≤ L →
        (∀ x z, |a₀ x - a₀ z| ≤ L * ‖x - z‖) → ContDiff ℝ ∞ a₀ → 0 ≤ J →
        (∀ n : ℕ, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n a₀ x‖ ≤ J) →
        WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} 0 K
          (fun p => a₀ p.1) →
        0 < R → R ≤ (smin / 16) ^ 4 / C → R ≤ 1 / 4 →
        (∀ t x, ρ₀ ≤ ‖x‖ → f t x = 0) → 0 < F →
        WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4) F
          (fun p => f p.2 p.1) →
        ∃ u : ℝ → V → ℂ, (∀ x, u 0 x = 0) ∧ (∀ t, ContDiff ℝ 4 (u t)) ∧
          (∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun r => u r x)
            (f t x - (a₀ x : ℂ) * Δ (Δ (u t)) x) (Icc 0 R) t) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} w (C * F) 4 u ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4) (C * F)
            (fun p => f p.2 p.1 - (a₀ p.1 : ℂ) * Δ (Δ (u p.2)) p.1) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} w
            ((ε + Cε * (R / (smin / 16) ^ 4)) * (C * F)) 3 u ∧
          ((∀ (Q : V ≃ₗᵢ[ℝ] V) x, a₀ (Q x) = a₀ x) →
            (∀ (Q : V ≃ₗᵢ[ℝ] V) t x, f t (Q x) = f t x) →
            ∀ t (Q : V ≃ₗᵢ[ℝ] V) x, u t (Q x) = u t x) ∧
          ((∀ t x, star (f t x) = f t x) → ∀ t x, star (u t x) = u t x) := by
  -- the constants
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = (2 ^ |(0 : ℝ)| + 2 ^ |0 - α| * (1 / 16 : ℝ) ^ α
      + 2 * 2 ^ |(0 : ℝ)| * (2 * (1 / 16) / (1 / 4)) ^ α) * K := ⟨_, rfl⟩
  have hKc : 0 ≤ Kc := by
    rw [hKcdef]
    positivity
  obtain ⟨C₀, hC₀, HE⟩ := outer_estimate (V := V) α κ Kc hα hα1 hκ hKc
  obtain ⟨C₁, hC₁, HL⟩ := outer_lower_small (V := V) α κ Kc hα hα1 hκ hKc
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = (1 / 16 : ℝ) ^ 4 * (2 ^ |w - 4|
      + 2 ^ |w - 4 - α| * (1 / 16 : ℝ) ^ α + 2 * 2 ^ |w - 4| * (2 * (1 / 16) / (1 / 4)) ^ α) :=
    ⟨_, rfl⟩
  have hCs : 0 < Cs := by
    rw [hCsdef]
    positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α) := ⟨_, rfl⟩
  have hA : 0 < A := by
    rw [hAdef]
    positivity
  obtain ⟨cw, hcwdef⟩ : ∃ cw : ℝ, cw = (2 : ℝ) ^ |w| := ⟨_, rfl⟩
  have hcw1 : 1 ≤ cw := by
    rw [hcwdef]
    exact Real.one_le_rpow (by norm_num) (abs_nonneg w)
  have hcw0 : 0 < cw := by linarith
  have hC₀0 : 0 < C₀ := by linarith
  have hC₁0 : 0 < C₁ := by linarith
  have hm0 : C₀ ≤ max C₀ C₁ := le_max_left _ _
  have hm1 : C₁ ≤ max C₀ C₁ := le_max_right _ _
  have hmpos : 0 < max C₀ C₁ := hC₀0.trans_le hm0
  have hCsA : 0 < Cs * A := mul_pos hCs hA
  refine ⟨(2 * max C₀ C₁ + 1) * (Cs * A) + 2 * max C₀ C₁ * cw + 1, ?_, fun ε hε => ?_⟩
  · have h1 : 0 ≤ (2 * max C₀ C₁ + 1) * (Cs * A) := mul_nonneg (by linarith) hCsA.le
    have h2 : 0 ≤ 2 * max C₀ C₁ * cw := mul_nonneg (by linarith) hcw0.le
    linarith
  obtain ⟨Cε, hCε, HLε⟩ := HL ε hε
  refine ⟨Cε * cw, mul_pos hCε hcw0, ?_⟩
  intro s smin smax ρ₀ L J R F a₀ f hsmin hs1 hs2 hsmax hl ha ha1 hL haL haS hJ haJ hcoef hR hRC
    hR4 hf0 hF hf
  obtain ⟨Ct, hCtdef⟩ : ∃ Ct : ℝ,
      Ct = (2 * max C₀ C₁ + 1) * (Cs * A) + 2 * max C₀ C₁ * cw + 1 := ⟨_, rfl⟩
  rw [← hCtdef] at hRC ⊢
  have hCt1 : (2 * max C₀ C₁ + 1) * (Cs * A) ≤ Ct := by
    rw [hCtdef]
    have h2 : 0 ≤ 2 * max C₀ C₁ * cw := mul_nonneg (by linarith) hcw0.le
    linarith
  have hCt2 : 2 * max C₀ C₁ * cw ≤ Ct := by
    rw [hCtdef]
    have h1 : 0 ≤ (2 * max C₀ C₁ + 1) * (Cs * A) := mul_nonneg (by linarith) hCsA.le
    linarith
  have hs : ∀ x, 0 < s x := fun x => hsmin.trans_le (hs1 x)
  have hq1 : ∀ x, 1 / 16 * s x ≤ 1 := fun x => by
    have := hs2 x
    linarith
  have hcompS : ∀ x₀ x, ‖x - x₀‖ < 2 * (1 / 16 * s x₀) → s x ≤ 2 * s x₀ ∧ s x₀ ≤ 2 * s x :=
    scale_comparable hs hl
  have hmw : 0 < min (smin ^ w) (smax ^ w) :=
    lt_min (Real.rpow_pos_of_pos hsmin _) (Real.rpow_pos_of_pos (hsmin.trans_le ((hs1 0).trans (hs2 0))) _)
  have hmws : ∀ x, min (smin ^ w) (smax ^ w) ≤ s x ^ w := fun x =>
    rpow_ge_min hsmin (hs1 x) (hs2 x) w
  have hcompw : ∀ x₀ x, ‖x - x₀‖ < 2 * (1 / 16 * s x₀) → s x ^ w ≤ cw * s x₀ ^ w := by
    intro x₀ x hx
    rw [hcwdef]
    exact rpow_le_of_comparable (hs x) (hs x₀) (by norm_num) (hcompS x₀ x hx).1
      (hcompS x₀ x hx).2 w
  -- the time is short enough for both estimates
  have hX0 : 0 ≤ (1 / 16 * smin) ^ 4 := by positivity
  have eX : (smin / 16) ^ 4 = (1 / 16 * smin) ^ 4 := by ring
  have hRX : R ≤ (1 / 16 * smin) ^ 4 / Ct := by rwa [eX] at hRC
  have hR0 : R ≤ (1 / 16 * smin) ^ 4 / (2 * C₀ * cw) := by
    refine hRX.trans (div_le_div_of_nonneg_left hX0
      (mul_pos (mul_pos two_pos hC₀0) hcw0) ?_)
    exact (mul_le_mul_of_nonneg_right (by linarith) hcw0.le).trans hCt2
  have hR1 : R ≤ (1 / 16 * smin) ^ 4 / (2 * C₁ * cw) := by
    refine hRX.trans (div_le_div_of_nonneg_left hX0
      (mul_pos (mul_pos two_pos hC₁0) hcw0) ?_)
    exact (mul_le_mul_of_nonneg_right (by linarith) hcw0.le).trans hCt2
  -- the solution with the source clamped in time
  obtain ⟨hgB, hgH⟩ := hf.global_holder hF.le (by norm_num : (0 : ℝ) < 1 / 4) hα.le hα1.le hR.le
    hsmin hs1 hs2
  have hH0 : 0 ≤ F * max (smin ^ (w - 4 - α)) (smax ^ (w - 4 - α))
      + 2 * (F * max (smin ^ (w - 4)) (smax ^ (w - 4))) * (1 / 4 * smin) ^ (-α) := by
    have h1 : 0 ≤ max (smin ^ (w - 4 - α)) (smax ^ (w - 4 - α)) :=
      le_max_of_le_left (Real.rpow_nonneg hsmin.le _)
    have h2 : 0 ≤ max (smin ^ (w - 4)) (smax ^ (w - 4)) :=
      le_max_of_le_left (Real.rpow_nonneg hsmin.le _)
    have h3 : 0 ≤ (1 / 4 * smin) ^ (-α) := Real.rpow_nonneg (by positivity) _
    exact add_nonneg (mul_nonneg hF.le h1)
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hF.le h2)) h3)
  obtain ⟨u, hu0, hu4, hd, -, ⟨M, hM, hJet⟩, hrad, hreal⟩ :=
    exists_zero_data_jets hκ hΛ hL hJ hR hR4 hα hα1 hH0 (fun _ => a₀) (fun _ x => ha x)
      (fun _ x hx => ha1 x hx)
      (fun t r x z => (haL x z).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hL))
      (fun _ => haS) (fun _ n hn x => haJ n hn x) (fun t x => f (clampT R t) x)
      (fun t x hx => hf0 _ x hx) hgB hgH
  -- the hypotheses of the uniform estimates
  have hSC : SCoeff s (1 / 16) R α Kc (fun _ => a₀) := by
    rw [hKcdef]
    exact sCoeff_of_WH (coef := fun _ => a₀) hcoef hK (by norm_num) hα.le (by norm_num)
      (by norm_num) hs hcompS
  have hfc : WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4) F
      (fun p => f (clampT R p.2) p.1) :=
    hf.congr fun p hp => by
      show f (clampT R p.2) p.1 = f p.2 p.1
      rw [clampT_of_mem hp]
  have hSS : SSource s (1 / 16) R α w (Cs * F) (fun t x => f (clampT R t) x) := by
    rw [hCsdef]
    exact sSource_of_WH (f := fun t x => f (clampT R t) x) hfc hF.le (by norm_num) hα.le
      (by norm_num) (by norm_num) hs hcompS
  have hCsF : 0 < Cs * F := mul_pos hCs hF
  have hκa : ∀ (t : ℝ) (x : V), κ ≤ (fun _ : ℝ => a₀) t x := fun _ x => (ha x).1
  obtain ⟨hSJ, -⟩ := HE s (1 / 16) w cw (min (smin ^ w) (smax ^ w)) smin R (by norm_num) hsmin
    hmw hcw1 hs1 hq1 hmws hcompw hR hR0 (fun _ => a₀) (fun t x => f (clampT R t) x) u hu4 hu0
    hd ⟨M, hM, hJet⟩ hSC hκa (Cs * F) hCsF hSS
  have hlow := HLε s (1 / 16) w cw (min (smin ^ w) (smax ^ w)) smin R (by norm_num) hsmin
    hmw hcw1 hs1 hq1 hmws hcompw hR hR1 (fun _ => a₀) (fun t x => f (clampT R t) x) u hu4 hu0
    hd ⟨M, hM, hJet⟩ hSC hκa (Cs * F) hCsF hSS
  have hpos : ∀ p ∈ {p : V × ℝ | p.2 ∈ Icc (0 : ℝ) R}, 0 < (fun p : V × ℝ => s p.1) p :=
    fun p _ => hs p.1
  have hN0 : 0 ≤ (2 * C₀ + 1) * (Cs * F) := by positivity
  obtain ⟨hWJ, hWt⟩ := WJ_of_sJet (a := 1 / 64) (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num)
    hs hα.le hN0 (by norm_num) hu4 hSJ
  have hconst : (2 * C₀ + 1) * (Cs * F) * (1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α)
      ≤ Ct * F := by
    have e : (2 * C₀ + 1) * (Cs * F) * (1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α)
        = (2 * C₀ + 1) * (Cs * A) * F := by
      rw [hAdef]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ hCt1) hF.le
    exact mul_le_mul_of_nonneg_right (by linarith) hCsA.le
  refine ⟨u, hu0, hu4, ?_, hWJ.mono hpos hconst, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    have h : HasDerivWithinAt (fun r => u r x)
        (f (clampT R t) x - (a₀ x : ℂ) * Δ (Δ (u t)) x) (Icc 0 R) t := hd t ht x
    rw [clampT_of_mem ht] at h
    exact h
  · refine (hWt.mono hpos hconst).congr fun p hp => ?_
    show f p.2 p.1 - (a₀ p.1 : ℂ) * Δ (Δ (u p.2)) p.1
      = f (clampT R p.2) p.1 - (a₀ p.1 : ℂ) * Δ (Δ (u p.2)) p.1
    rw [clampT_of_mem hp]
  · -- the jets of order at most three
    intro j hj
    have hNl : 0 ≤ (ε + Cε * cw * (R / (1 / 16 * smin) ^ 4)) * ((2 * C₁ + 1) * (Cs * F)) := by
      have h1 : 0 ≤ R / (1 / 16 * smin) ^ 4 := div_nonneg hR.le hX0
      positivity
    have h1 := WH_of_window_jets (a := 1 / 64) (b := 1 / 16) (ρ := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num) hs hα.le hNl (by norm_num) hu4 (hj.trans (by norm_num))
      (fun x₀ => hlow x₀ j hj)
    refine h1.mono hpos ?_
    have h2 : (1 / 16 : ℝ) ^ (-(j : ℝ)) ≤ (1 / 16 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
        have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
        linarith)
    have hα0 : 0 ≤ (1 / 16 : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
    have hj0 : 0 ≤ (1 / 16 : ℝ) ^ (-(j : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hη : 0 ≤ ε + Cε * cw * (R / (1 / 16 * smin) ^ 4) := by
      have h1 : 0 ≤ R / (1 / 16 * smin) ^ 4 := div_nonneg hR.le hX0
      positivity
    have hstep : (2 * C₁ + 1) * (Cs * F) * ((1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α))
        ≤ Ct * F := by
      have e : (2 * C₁ + 1) * (Cs * F) * ((1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α))
          = (2 * C₁ + 1) * (Cs * A) * F := by
        rw [hAdef]
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_right (le_trans ?_ hCt1) hF.le
      exact mul_le_mul_of_nonneg_right (by linarith) hCsA.le
    have hN1 : 0 ≤ (2 * C₁ + 1) * (Cs * F) := by positivity
    calc (ε + Cε * cw * (R / (1 / 16 * smin) ^ 4)) * ((2 * C₁ + 1) * (Cs * F))
          * (1 / 16 : ℝ) ^ (-(j : ℝ)) * (1 / 16 : ℝ) ^ (-α)
        = (ε + Cε * cw * (R / (1 / 16 * smin) ^ 4))
          * ((2 * C₁ + 1) * (Cs * F) * ((1 / 16 : ℝ) ^ (-(j : ℝ)) * (1 / 16 : ℝ) ^ (-α))) := by
          ring
      _ ≤ (ε + Cε * cw * (R / (1 / 16 * smin) ^ 4))
          * ((2 * C₁ + 1) * (Cs * F) * ((1 / 16 : ℝ) ^ (-(4 : ℝ)) * (1 / 16 : ℝ) ^ (-α))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hα0) hN1) hη
      _ ≤ (ε + Cε * cw * (R / (1 / 16 * smin) ^ 4)) * (Ct * F) :=
          mul_le_mul_of_nonneg_left hstep hη
      _ = (ε + Cε * cw * (R / (smin / 16) ^ 4)) * (Ct * F) := by rw [eX]
  · intro hra hrf t Q x
    exact hrad (fun Q _ x => hra Q x) (fun Q t x => hrf Q _ x) t Q x
  · intro hre t x
    exact hreal (fun t x => hre _ x) t x

end Calabi.Weighted
