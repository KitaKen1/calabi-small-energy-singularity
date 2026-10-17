import Calabi.Correction.LocalSolve
import Calabi.Correction.TwoCharts
import Calabi.Correction.ChartCutoff

/-!
# The outer block in the chart at `x = 1`

Near the divisor at infinity (`x = 1`) the localized profile vanishes, so that
the linearized operator is `∂ₜ + A`, and `16 A = chartOp 18` in the chart
`x = 1 - |w|²` on `ℝ⁶`. This file solves `∂ₜ U + A U = ψ¹ g` approximately for
a source `g` given in this chart, with the cut-off `ψ¹ = 1 - χ(4x)` (which is
supported in `x ≥ 1/4`, that is `|w|² ≤ 3/4`):

  `U = ψ¹ Z`,   `∂ₜ Z + a¹ Δ² Z = ψ̃¹ g`,   `Z(-T) = 0`,

where `a¹` equals the principal coefficient `(1 - |w|²)²/16` on the support of
`ψ¹` and is cut off to `1` near and beyond the boundary of the chart, and `ψ̃¹`
is a cut-off equal to one on the support of `ψ¹`.

`outer_chart1`: `U` is bounded by the source in the weighted norms, and
`∂ₜ U + A U = ψ¹ g + err` with an error that is small when `T` is small.
The scale of this chart is constant.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial

/-! ### The coefficient and the cut-offs -/

/-- The profile of the coefficient of the forward problem in the chart at
`x = 1`: `(1 - s)²/16` for `s ≤ 3/4`, and `1` for `s ≥ 7/8`. -/
noncomputable def phi1 (s : ℝ) : ℝ :=
  chi (8 * s - 5) * ((1 - s) ^ 2 / 16) + (1 - chi (8 * s - 5))

theorem contDiff_phi1 : ContDiff ℝ ∞ phi1 := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => chi (8 * s - 5)) :=
    contDiff_chi.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (h1.mul (((contDiff_const.sub contDiff_id).pow 2).div_const 16)).add
    (contDiff_const.sub h1)

theorem phi1_of_gt {s : ℝ} (hs : 7 / 8 < s) : phi1 s = 1 := by
  unfold phi1
  rw [chi_of_ge (by linarith)]
  ring

theorem phi1_of_le {s : ℝ} (hs : s ≤ 3 / 4) : phi1 s = (1 - s) ^ 2 / 16 := by
  unfold phi1
  rw [chi_of_le (by linarith)]
  ring

theorem phi1_mem {s : ℝ} (hs : 0 ≤ s) : phi1 s ∈ Icc (1 / 1024 : ℝ) 1 := by
  rcases le_or_gt s (7 / 8) with h | h
  · have h1 := chi_nonneg (8 * s - 5)
    have h2 := chi_le_one (8 * s - 5)
    have hq1 : (1 : ℝ) / 1024 ≤ (1 - s) ^ 2 / 16 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s - 1 / 8)
        (by linarith : (0 : ℝ) ≤ 1 - s + 1 / 8)]
    have hq2 : (1 - s) ^ 2 / 16 ≤ 1 := by
      nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 2 - s)]
    have h3 := mul_nonneg h1 (sub_nonneg.2 hq1)
    have h4 := mul_nonneg h1 (sub_nonneg.2 hq2)
    unfold phi1
    constructor <;> nlinarith
  · rw [phi1_of_gt h]
    constructor <;> norm_num

/-- The coefficient of the forward problem in the chart at `x = 1`. -/
noncomputable def acoef1 : Flat6 → ℝ := radFn phi1

/-- The profile of the cut-off `ψ¹ = 1 - χ(4x)` in the variable `s = 1 - x`. -/
noncomputable def psiP1 (s : ℝ) : ℝ := 1 - chi (4 * (1 - s))

theorem contDiff_psiP1 : ContDiff ℝ ∞ psiP1 :=
  contDiff_const.sub (contDiff_chi.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

theorem psiP1_of_ge {s : ℝ} (hs : 3 / 4 ≤ s) : psiP1 s = 0 := by
  unfold psiP1
  rw [chi_of_le (by linarith), sub_self]

/-- The cut-off `ψ¹` on the chart at `x = 1`. -/
noncomputable def psi1 : Flat6 → ℝ := radFn psiP1

/-- The profile of the cut-off of the source in the chart at `x = 1`: one for
`s ≤ 3/4`, zero for `s ≥ 13/16`. -/
noncomputable def psitP1 (s : ℝ) : ℝ := chi (16 * s - 11)

theorem contDiff_psitP1 : ContDiff ℝ ∞ psitP1 :=
  contDiff_chi.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem psitP1_of_ge {s : ℝ} (hs : 13 / 16 ≤ s) : psitP1 s = 0 := by
  unfold psitP1
  exact chi_of_ge (by linarith)

/-- The cut-off of the source on the chart at `x = 1`. -/
noncomputable def psit1 : Flat6 → ℝ := radFn psitP1

theorem psi1_mul_psit1 (z : Flat6) : psi1 z * psit1 z = psi1 z := by
  rcases le_or_gt (‖z‖ ^ 2) (3 / 4) with h | h
  · have e : psit1 z = 1 := by
      show chi (16 * ‖z‖ ^ 2 - 11) = 1
      exact chi_of_le (by linarith)
    rw [e, mul_one]
  · have e : psi1 z = 0 := psiP1_of_ge h.le
    rw [e, zero_mul]

theorem acoef1_mul_psi1 (z : Flat6) : ((1 - ‖z‖ ^ 2) ^ 2 / 16 - acoef1 z) * psi1 z = 0 := by
  rcases le_or_gt (‖z‖ ^ 2) (3 / 4) with h | h
  · have e : acoef1 z = (1 - ‖z‖ ^ 2) ^ 2 / 16 := phi1_of_le h
    rw [e, sub_self, zero_mul]
  · have e : psi1 z = 0 := psiP1_of_ge h.le
    rw [e, mul_zero]

/-! ### The outer block -/

set_option maxHeartbeats 3200000 in
/-- **The outer block in the chart at `x = 1`.** -/
theorem outer_chart1 (α w : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ T₁ : ℝ, 0 < T₁ ∧
      ∀ (T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < T → T ≤ T₁ → 0 < F →
        WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) (w - 4) F
          (fun p => g p.2 (1 - ‖p.1‖ ^ 2)) →
        ∃ (u ut : ℝ → Flat6 → ℝ) (err : Flat6 × ℝ → ℝ),
          (∀ t, ContDiff ℝ 4 (u t)) ∧ (∀ t z, 3 / 4 < ‖z‖ ^ 2 → u t z = 0) ∧
          (∀ t z, 3 / 4 < ‖z‖ ^ 2 → ut t z = 0) ∧ (∀ z, u (-T) z = 0) ∧
          (∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => u r z) (ut t z) t) ∧
          (∀ t (Q : Flat6 ≃ₗᵢ[ℝ] Flat6) z, u t (Q z) = u t z) ∧
          WJ α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) {p : Flat6 × ℝ | p.2 ∈ Icc (-T) 0} w
            (C * F) 4 u ∧
          WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) (w - 4) (C * F)
            (fun p => ut p.2 p.1) ∧
          WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) (w - 4) (ε * F) err ∧
          (∀ p : Flat6 × ℝ, 3 / 4 < ‖p.1‖ ^ 2 → err p = 0) ∧
          ∀ t ∈ Ico (-T) 0, ∀ z : Flat6,
            ut t z + chartOp 18 (u t) z / 16
              = (1 - chi (4 * (1 - ‖z‖ ^ 2))) * g t (1 - ‖z‖ ^ 2) + err (z, t) := by
  -- the constants of the coefficient and of the cut-offs
  obtain ⟨Ba, hBa, hBaj, hBaL⟩ := radFn_data (V := Flat6) contDiff_phi1 (s₁ := 7 / 8) (c₀ := 1)
    (fun s hs => phi1_of_gt hs)
  obtain ⟨Bp, hBp, hBpj, -⟩ := radFn_data (V := Flat6) contDiff_psiP1 (s₁ := 3 / 4) (c₀ := 0)
    (fun s hs => psiP1_of_ge hs.le)
  obtain ⟨Bt, hBt, hBtj, -⟩ := radFn_data (V := Flat6) contDiff_psitP1 (s₁ := 13 / 16)
    (c₀ := 0) (fun s hs => psitP1_of_ge hs.le)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * (Bp * 1 ^ (4 + 1)) := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : ℝ, A₁ = 2 * (Bt * 1 ^ (0 + 1)) := ⟨_, rfl⟩
  have hA₁ : 0 ≤ A₁ := by rw [hA₁def]; positivity
  obtain ⟨Ksrc, hKsrcdef⟩ : ∃ Ksrc : ℝ, Ksrc = (1 + (1 : ℝ) ^ |(0 : ℝ)|) * A₁
      * (1 + (1 + (1 : ℝ) ^ |w - 4|) * (1 / 64 : ℝ) ^ (-α)) + 1 := ⟨_, rfl⟩
  have hKsrc : 1 ≤ Ksrc := by
    rw [hKsrcdef]
    have : 0 ≤ (1 + (1 : ℝ) ^ |(0 : ℝ)|) * A₁
        * (1 + (1 + (1 : ℝ) ^ |w - 4|) * (1 / 64 : ℝ) ^ (-α)) := by positivity
    linarith
  obtain ⟨C₀, hC₀, H⟩ := exists_localized (V := Flat6) α (1 / 1024) 1 (2 * (Ba * 2 ^ (0 + 1)))
    w 18 hα hα1 (by norm_num) le_rfl (by positivity)
  have hC₀0 : 0 < C₀ := by linarith
  have hCAK : 0 ≤ C₀ * (A * Ksrc) := by positivity
  refine ⟨C₀ * (A * Ksrc) + 1, by linarith, fun ε hε => ?_⟩
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = ε / (C₀ * (A * Ksrc) + 1) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by
    rw [hε'def]
    positivity
  obtain ⟨Cε, hCε, H⟩ := H ε' hε'
  refine ⟨min (min ((1 / 16) ^ 4 / C₀) (1 / 4)) (ε' / (Cε * 16 ^ 4)), by positivity, ?_⟩
  intro T F g hT hTT hF hg
  have hTC : T ≤ (1 / 16) ^ 4 / C₀ := (hTT.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hT4 : T ≤ 1 / 4 := (hTT.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hTε : T ≤ ε' / (Cε * 16 ^ 4) := hTT.trans (min_le_right _ _)
  -- the coefficient
  have ha₀ : ∀ x : Flat6, acoef1 x ∈ Icc (1 / 1024 : ℝ) 1 := fun x => phi1_mem (sq_nonneg _)
  have ha₀1 : ∀ x : Flat6, 1 ≤ ‖x‖ → acoef1 x = 1 := fun x hx =>
    phi1_of_gt (by nlinarith)
  have hsm : ContDiff ℝ ∞ acoef1 := contDiff_radFn contDiff_phi1
  have ha₀W : ∀ Ω : Set (Flat6 × ℝ), WH α (1 / 4)
      (fun p : Flat6 × ℝ => (fun _ : Flat6 => (1 : ℝ)) p.1) Ω 0 (2 * (Ba * 2 ^ (0 + 1)))
      (fun p => acoef1 p.1) := fun Ω =>
    (WJ_of_global (s := fun _ : Flat6 × ℝ => (1 : ℝ)) (Ω := Ω) (S := 2) (n := 0)
      (fun _ _ => one_pos) (fun _ _ => by norm_num) (by norm_num) hBa (by norm_num)
      (by norm_num) hα.le hα1.le (contDiff_infty.1 hsm _)
      (fun j hj z => hBaj j (by omega) z)).value
  -- the source
  have hψt : WJ α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) 0 A₁ 0 (fun _ => psit1) := by
    rw [hA₁def]
    exact WJ_of_global (S := 1) (n := 0) (fun _ _ => one_pos) (fun _ _ => le_rfl) le_rfl hBt
      (by norm_num) (by norm_num) hα.le hα1.le (contDiff_infty.1 (contDiff_radFn contDiff_psitP1) _)
      (fun j hj z => hBtj j (by omega) z)
  have hprod := WH.mul (isScale1 T) hA₁ hF.le hψt.value hg
  rw [zero_add] at hprod
  have hext := hprod.extend_zero1 (by positivity) (by norm_num) le_rfl
    (fun p hp => by
      show psit1 p.1 * g p.2 (1 - ‖p.1‖ ^ 2) = 0
      have e : psit1 p.1 = 0 := psitP1_of_ge hp.le
      rw [e, zero_mul])
  have hrg := hext.radius_ge
    (IsScale.const one_pos : IsScale (1 / 4) 1 (fun _ : Flat6 × ℝ => (1 : ℝ))
      {p : Flat6 × ℝ | p.2 ∈ Ico (-T) 0}) (by positivity) (by norm_num) hα.le
  have hfW : WH α (1 / 4) (fun p : Flat6 × ℝ => (fun _ : Flat6 => (1 : ℝ)) p.1)
      {p : Flat6 × ℝ | p.2 ∈ Ico (-T) 0} (w - 4) (Ksrc * F)
      (fun p => psit1 p.1 * g p.2 (1 - ‖p.1‖ ^ 2)) := by
    refine hrg.mono (fun _ _ => one_pos) ?_
    rw [hKsrcdef]
    linarith
  -- the cut-off
  have hχ4 : ContDiff ℝ 4 psi1 := contDiff_infty.1 (contDiff_radFn contDiff_psiP1) 4
  have hχW : WJ α (1 / 64) (fun p : Flat6 × ℝ => (fun _ : Flat6 => (1 : ℝ)) p.1)
      {p : Flat6 × ℝ | p.2 ∈ Icc (-T) 0} 0 A 4 (fun _ => psi1) := by
    rw [hAdef]
    exact WJ_of_global (S := 1) (n := 4) (fun _ _ => one_pos) (fun _ _ => le_rfl) le_rfl hBp
      (by norm_num) (by norm_num) hα.le hα1.le (contDiff_infty.1 (contDiff_radFn contDiff_psiP1) _)
      (fun j hj z => hBpj j (by omega) z)
  -- the solution
  obtain ⟨Z, hZ0, hZ4, hZd, hUJ, hUt, -, hQ2, -, hQ4, hZrad⟩ := H (fun _ => 1) 1 1 Ba Ba T
    (Ksrc * F) A acoef1 psi1 (fun t z => psit1 z * g t (1 - ‖z‖ ^ 2)) (by norm_num)
    (fun _ => le_rfl) (fun _ => by norm_num) (fun x y => by simp) ha₀ ha₀1 hBa hBaL hsm hBa
    (fun n hn x => hBaj n (by omega) x) ha₀W hT hTC hT4
    (fun t _ x hx => by
      have e : psit1 x = 0 := psitP1_of_ge (by nlinarith)
      show psit1 x * g t (1 - ‖x‖ ^ 2) = 0
      rw [e, zero_mul])
    (by positivity) hfW hχ4 hA hχW
  have hpos1 : ∀ (Ω : Set (Flat6 × ℝ)), ∀ p ∈ Ω, 0 < (fun _ : Flat6 × ℝ => (1 : ℝ)) p :=
    fun _ _ _ => one_pos
  have hsub : dom1 T ⊆ {p : Flat6 × ℝ | p.2 ∈ Ico (-T) 0} := fun p hp => hp.1
  have hsubb : dom1 T ⊆ {p : Flat6 × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} := fun p hp =>
    ⟨hp.1, by
      have := norm_nonneg p.1
      nlinarith [hp.2]⟩
  have hopen : IsOpen {z : Flat6 | 3 / 4 < ‖z‖ ^ 2} :=
    isOpen_lt continuous_const (continuous_norm.pow 2)
  have hpsi0 : ∀ z : Flat6, 3 / 4 < ‖z‖ ^ 2 → psi1 z = 0 := fun z hz => psiP1_of_ge hz.le
  -- the smallness of the error
  have hδ : (ε' + Cε * (T / (1 / 16) ^ 4)) ≤ 2 * ε' := by
    have h1 : T / (1 / 16) ^ 4 = T * 16 ^ 4 := by
      field_simp
    rw [h1]
    have h2 : Cε * (T * 16 ^ 4) ≤ ε' := by
      have h3 := mul_le_mul_of_nonneg_left hTε (by positivity : (0 : ℝ) ≤ Cε * 16 ^ 4)
      rw [mul_div_cancel₀ ε' (by positivity)] at h3
      linarith
    linarith
  have hε'C : ε' * (C₀ * (A * Ksrc) + 1) = ε := by
    rw [hε'def]
    field_simp
  refine ⟨fun t z => psi1 z • Z t z,
    fun t z => psi1 z • (psit1 z * g t (1 - ‖z‖ ^ 2) - acoef1 z * Δ (Δ (Z t)) z),
    fun p => (1 / 16 : ℝ) • (psi1 p.1 • lowOp 18 (Z p.2) p.1)
      + (1 / 16 : ℝ) • (chartOp 18 (fun z => psi1 z • Z p.2 z) p.1
        - psi1 p.1 • chartOp 18 (Z p.2) p.1),
    fun t => hχ4.smul (hZ4 t), fun t z hz => ?_, fun t z hz => ?_, fun z => ?_,
    fun t ht z => (hZd t ht z).const_smul (psi1 z), fun t Q z => ?_, ?_, ?_, ?_,
    fun p hp => ?_, fun t ht z => ?_⟩
  · show psi1 z • Z t z = 0
    rw [hpsi0 z hz, zero_smul]
  · show psi1 z • (psit1 z * g t (1 - ‖z‖ ^ 2) - acoef1 z * Δ (Δ (Z t)) z) = 0
    rw [hpsi0 z hz, zero_smul]
  · show psi1 z • Z (-T) z = 0
    rw [hZ0 z, smul_zero]
  · show psi1 (Q z) • Z t (Q z) = psi1 z • Z t z
    have e1 : psi1 (Q z) = psi1 z := radFn_rotate psiP1 Q z
    have e2 := hZrad (fun Q x => radFn_rotate phi1 Q x)
      (fun t _ Q x => by
        show psit1 (Q x) * g t (1 - ‖Q x‖ ^ 2) = psit1 x * g t (1 - ‖x‖ ^ 2)
        have e3 : psit1 (Q x) = psit1 x := radFn_rotate psitP1 Q x
        rw [e3, Q.norm_map]) t Q z
    rw [e1, e2]
  · refine hUJ.mono (hpos1 _) ?_
    have hF0 := hF.le
    nlinarith [mul_nonneg hCAK hF0]
  · refine (hUt.restrict hsub).mono (hpos1 _) ?_
    have hF0 := hF.le
    nlinarith [mul_nonneg hCAK hF0]
  · have h2 := ((hQ2.const_smul (1 / 16)).add (hQ4.const_smul (1 / 16))).restrict hsubb
    refine h2.mono (hpos1 _) ?_
    have e16 : |(1 / 16 : ℝ)| = 1 / 16 := abs_of_nonneg (by norm_num)
    rw [e16]
    have hKF : 0 ≤ Ksrc * F := by positivity
    have h3 : (ε' + Cε * (T / (1 / 16) ^ 4)) * (Ksrc * F) ≤ 2 * ε' * (Ksrc * F) :=
      mul_le_mul_of_nonneg_right hδ hKF
    have h4 : C₀ * (A * ((ε' + Cε * (T / (1 / 16) ^ 4)) * (Ksrc * F)))
        ≤ C₀ * (A * (2 * ε' * (Ksrc * F))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hA) hC₀0.le
    have h5 : C₀ * (A * (2 * ε' * (Ksrc * F))) = 2 * (ε' * (C₀ * (A * Ksrc))) * F := by ring
    have h6 : ε' * (C₀ * (A * Ksrc)) ≤ ε := by
      rw [← hε'C]
      nlinarith [hε'.le]
    have h7 : 2 * (ε' * (C₀ * (A * Ksrc))) * F ≤ 2 * ε * F :=
      mul_le_mul_of_nonneg_right (by linarith) hF.le
    have h8 : 0 ≤ ε * F := by positivity
    linarith
  · show (1 / 16 : ℝ) • (psi1 p.1 • lowOp 18 (Z p.2) p.1)
      + (1 / 16 : ℝ) • (chartOp 18 (fun z => psi1 z • Z p.2 z) p.1
        - psi1 p.1 • chartOp 18 (Z p.2) p.1) = 0
    have hev : (fun z => psi1 z • Z p.2 z) =ᶠ[𝓝 p.1] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hp] with z hz
      rw [hpsi0 z hz, zero_smul]
    rw [chartOp_eq_zero_of_eventually 18 hev, hpsi0 p.1 hp]
    simp
  · have hid := localized_identity (V := Flat6) 18 1 0 (acoef1 z)
      (psit1 z * g t (1 - ‖z‖ ^ 2)) (psi1 z) (fun y => psi1 y • Z t y) (Z t) z
    have h1 := psi1_mul_psit1 z
    have h2 := acoef1_mul_psi1 z
    have e : (1 - chi (4 * (1 - ‖z‖ ^ 2))) = psi1 z := rfl
    rw [e]
    show psi1 z • (psit1 z * g t (1 - ‖z‖ ^ 2) - acoef1 z * Δ (Δ (Z t)) z)
        + chartOp 18 (fun y => psi1 y • Z t y) z / 16
      = psi1 z * g t (1 - ‖z‖ ^ 2) + ((1 / 16 : ℝ) • (psi1 z • lowOp 18 (Z t) z)
        + (1 / 16 : ℝ) • (chartOp 18 (fun y => psi1 y • Z t y) z
          - psi1 z • chartOp 18 (Z t) z))
    simp only [smul_eq_mul] at hid ⊢
    linear_combination hid + g t (1 - ‖z‖ ^ 2) * h1 + Δ (Δ (Z t)) z * h2

end Calabi.Weighted
