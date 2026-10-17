import Calabi.Correction.OuterZero

/-!
# The outer block in the chart at the point orbit: the estimate

`outer_chart0` (see `OuterZero.lean` for the construction): for a source `g`
with a weighted bound in the chart `x = |z|²` that vanishes for `x ≤ θ`, the
function `U = χ⁰ Z` satisfies

  `∂ₜ U + b_λ² A U + c_λ U = χ(4x) g + err`,

where `U` and `∂ₜ U` are bounded by the source with a constant that does not
depend on the inner radius `θ` or on the time `T ≤ η θ²`, and the error is at
most `ε` times the source when `η` is small. The jets of `U` are also small in
a smaller Hölder exponent.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

set_option maxHeartbeats 6400000 in
/-- **The outer block in the chart at the point orbit.** -/
theorem outer_chart0 {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) (α α₀ w lam : ℝ) (hα : 0 < α)
    (hα1 : α < 1) (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hlam : 0 < lam) (hlam8 : lam < 1 / 8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ 1 / 16 ∧
      ∀ (θ T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ lam / 8 → 0 < T → T ≤ η₁ * θ ^ 2 → 0 < F →
        WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (w - 4) F (fun p => g p.2 (‖p.1‖ ^ 2)) →
        (∀ t ∈ Ico (-T) 0, ∀ x, x ≤ θ → g t x = 0) →
        ∃ (u ut : ℝ → Flat18 → ℝ) (err : Flat18 × ℝ → ℝ),
          (∀ t, ContDiff ℝ 4 (u t)) ∧ (∀ t z, 1 / 2 < ‖z‖ ^ 2 → u t z = 0) ∧
          (∀ t z, 1 / 2 < ‖z‖ ^ 2 → ut t z = 0) ∧ (∀ z, u (-T) z = 0) ∧
          (∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => u r z) (ut t z) t) ∧
          (∀ t (Q : Flat18 ≃ₗᵢ[ℝ] Flat18) z, u t (Q z) = u t z) ∧
          WJ α (1 / 64) (sigma (V := Flat18)) (dom0 T) w (C * F) 4 u ∧
          WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (w - 4) (C * F) (fun p => ut p.2 p.1) ∧
          WJ α₀ (1 / 64) (sigma (V := Flat18)) (dom0 T) w
            (C * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) 4 u ∧
          WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (w - 4) (ε * F) err ∧
          (∀ p : Flat18 × ℝ, 1 / 2 < ‖p.1‖ ^ 2 → err p = 0) ∧
          ∀ t ∈ Ico (-T) 0, ∀ z : Flat18,
            ut t z + blam G lam t (‖z‖ ^ 2) ^ 2 * (chartOp 6 (u t) z / 16)
                + clam G lam t (‖z‖ ^ 2) * u t z
              = chi (4 * ‖z‖ ^ 2) * g t (‖z‖ ^ 2) + err (z, t) := by
  have hc0 := hP.c_pos
  have hc1 := hP.c_lt_one
  -- the constants
  obtain ⟨Ba, hBa, hBaj, hBaL⟩ := radFn_data (V := Flat18) (contDiff_phi0 c lam) (s₁ := 3 / 4)
    (c₀ := 1) (fun s hs => phi0_of_gt hs)
  obtain ⟨Bt, hBt, hBtj, -⟩ := radFn_data (V := Flat18) contDiff_psitP0 (s₁ := 5 / 8) (c₀ := 0)
    (fun s hs => psitP0_of_ge hs.le)
  obtain ⟨A, hA, HA⟩ := WJ_cut0 (V := Flat18)
  obtain ⟨Kc, hKc, HKc⟩ := coef_bounds hP α hα.le hα1.le
  obtain ⟨Mb, hMb, HMb⟩ := bdP_chart hP
  obtain ⟨Ks, hKs, HKs⟩ := sth_of_sigma_ex α (w - 4) hα.le
  obtain ⟨K4, hK4, HK4⟩ := sigma_of_sth_ex α (w - 4) hα.le
  obtain ⟨KJ, hKJ, HKJ⟩ := WJ_sigma_of_sth_ex α w 4 hα.le
  obtain ⟨KJ₀, hKJ₀, HKJ₀⟩ := WJ_sigma_of_sth_ex α₀ w 4 hα₀.le
  obtain ⟨K3, hK3, HK3⟩ := WJ_sigma_of_sth_ex α w 3 hα.le
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : ℝ, A₁ = 2 * (Bt * 2 ^ (0 + 1)) := ⟨_, rfl⟩
  have hA₁ : 0 ≤ A₁ := by rw [hA₁def]; positivity
  obtain ⟨Ksrc, hKsrcdef⟩ : ∃ Ksrc : ℝ, Ksrc = Ks * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * A₁) + 1 :=
    ⟨_, rfl⟩
  have hKsrc : 1 ≤ Ksrc := by
    rw [hKsrcdef]
    have : 0 ≤ Ks * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * A₁) := by positivity
    linarith
  obtain ⟨C₀, hC₀, H⟩ := exists_localized (V := Flat18) α (c ^ 2 / 256) 1
    (2 * (Ba * 2 ^ (0 + 1))) w 6 hα hα1 (by positivity) le_rfl (by positivity)
  have hC₀0 : 0 < C₀ := by linarith
  obtain ⟨Kσ, hKσdef⟩ : ∃ Kσ : ℝ, Kσ = K4 + K3 := ⟨_, rfl⟩
  have hKσ : 0 ≤ Kσ := by rw [hKσdef]; positivity
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q₀ : ℝ, Q₀ = Kσ * (C₀ * (A * Ksrc)) := ⟨_, rfl⟩
  have hQ₀ : 0 ≤ Q₀ := by rw [hQ₀def]; positivity
  obtain ⟨Kb, hKbdef⟩ : ∃ Kb : ℝ,
      Kb = |(1 / 16 : ℝ)| * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kc * Kc) := ⟨_, rfl⟩
  have hKb : 0 ≤ Kb := by rw [hKbdef]; positivity
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (1 + (2 : ℝ) ^ |(0 : ℝ)|) * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Mb)
      + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb + (1 + (2 : ℝ) ^ |(-4 : ℝ)|) * Kc
      + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Kb := ⟨_, rfl⟩
  have hN : 0 ≤ N := by rw [hNdef]; positivity
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = 1 + (2 : ℝ) ^ (|w| + ((4 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hCg : 0 ≤ Cg := by rw [hCgdef]; positivity
  have hCAK : 0 ≤ C₀ * (A * Ksrc) := by positivity
  refine ⟨(KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) + 1, by
    have : 0 ≤ (KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) := by positivity
    linarith, fun ε hε => ?_⟩
  -- the small parameters
  obtain ⟨ε₂, hε₂def⟩ : ∃ ε₂ : ℝ, ε₂ = ε / (N * Q₀ + 1) := ⟨_, rfl⟩
  have hNQ : 0 < N * Q₀ + 1 := by positivity
  have hε₂ : 0 < ε₂ := by rw [hε₂def]; positivity
  have hε₂N : ε₂ * (N * Q₀ + 1) = ε := by
    rw [hε₂def]
    field_simp
  obtain ⟨Cε, hCε, H⟩ := H (ε₂ / 2) (by positivity)
  have h1α : 0 < 1 - α := by linarith
  refine ⟨min (min (min (1 / 16) (1 / (16 ^ 4 * C₀))) (1 / 64 ^ 4))
    (min (ε₂ / 2 / (Cε * 16 ^ 4)) (ε₂ ^ (1 / (1 - α)))),
    lt_min (lt_min (lt_min (by norm_num) (by positivity)) (by norm_num))
      (lt_min (by positivity) (Real.rpow_pos_of_pos hε₂ _)),
    ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _), ?_⟩
  intro θ T F g hθ hθlam hT hTη hF hg hg0
  -- the consequences of the choice of the parameters
  have hθ4 : θ ≤ 1 / 4 := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hsq4 : (Real.sqrt θ / 16) ^ 4 = θ ^ 2 / 16 ^ 4 := by
    have e : Real.sqrt θ ^ 4 = θ ^ 2 := by
      calc Real.sqrt θ ^ 4 = (Real.sqrt θ ^ 2) ^ 2 := by ring
        _ = θ ^ 2 := by rw [hsq]
    rw [div_pow, e]
  have hη16 : T ≤ 1 / 16 * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)) hθ2.le)
  have hηC : T ≤ 1 / (16 ^ 4 * C₀) * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)) hθ2.le)
  have hη64 : T ≤ 1 / 64 ^ 4 * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) hθ2.le)
  have hηε : T ≤ ε₂ / 2 / (Cε * 16 ^ 4) * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) hθ2.le)
  have hηα : T ≤ ε₂ ^ (1 / (1 - α)) * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) hθ2.le)
  have hTθ : T ≤ (θ / 4) ^ 2 := by
    have e : (θ / 4) ^ 2 = 1 / 16 * θ ^ 2 := by ring
    rw [e]
    exact hη16
  have hθsq : θ ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hθ.le hθ4 2
    norm_num at this
    linarith
  have hθlamsq : θ ^ 2 ≤ (lam / 8) ^ 2 := pow_le_pow_left₀ hθ.le hθlam 2
  have hT1 : T ≤ 1 := by linarith
  have hT4 : T ≤ 1 / 4 := by linarith
  have hTlam : T ≤ lam ^ 2 := by nlinarith [sq_nonneg lam]
  have hTC : T ≤ (Real.sqrt θ / 16) ^ 4 / C₀ := by
    rw [hsq4]
    have e : θ ^ 2 / 16 ^ 4 / C₀ = 1 / (16 ^ 4 * C₀) * θ ^ 2 := by
      field_simp
    rw [e]
    exact hηC
  have hTa : T ≤ (1 / 64 * Real.sqrt θ) ^ 4 := by
    have e : (1 / 64 * Real.sqrt θ) ^ 4 = 1 / 64 ^ 4 * θ ^ 2 := by
      have e' : Real.sqrt θ ^ 4 = θ ^ 2 := by
        calc Real.sqrt θ ^ 4 = (Real.sqrt θ ^ 2) ^ 2 := by ring
          _ = θ ^ 2 := by rw [hsq]
      rw [mul_pow, e']
      ring
    rw [e]
    exact hη64
  -- `δ ≤ ε₂`
  have hδ : ε₂ / 2 + Cε * (T / (Real.sqrt θ / 16) ^ 4) ≤ ε₂ := by
    rw [hsq4]
    have h1 : T / (θ ^ 2 / 16 ^ 4) = T / θ ^ 2 * 16 ^ 4 := by
      field_simp
    rw [h1]
    have h2 : T / θ ^ 2 ≤ ε₂ / 2 / (Cε * 16 ^ 4) := by
      rw [div_le_iff₀ hθ2]
      exact hηε
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cε * 16 ^ 4)
    rw [mul_div_cancel₀ _ (by positivity : Cε * 16 ^ 4 ≠ 0)] at h3
    nlinarith
  have hδ0 : 0 ≤ ε₂ / 2 + Cε * (T / (Real.sqrt θ / 16) ^ 4) := by positivity
  -- `(T/θ²)^{1-α} ≤ ε₂`
  have hTθ0 : 0 ≤ T / θ ^ 2 := by positivity
  have hTθ1 : T / θ ^ 2 ≤ 1 := by
    rw [div_le_one hθ2]
    linarith
  have hpow : (T / θ ^ 2) ^ (1 - α / 1) ≤ ε₂ := by
    rw [div_one]
    have h2 : T / θ ^ 2 ≤ ε₂ ^ (1 / (1 - α)) := by
      rw [div_le_iff₀ hθ2]
      exact hηα
    have h3 := Real.rpow_le_rpow hTθ0 h2 h1α.le
    rw [← Real.rpow_mul hε₂.le, one_div_mul_cancel h1α.ne', Real.rpow_one] at h3
    exact h3
  -- the source in the scale `s_θ`
  have hsubI : {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} :=
    fun _ hp => hp
  have hψt : WJ α (1 / 64) (sigma (V := Flat18)) (dom0 T) 0 A₁ 0 (fun _ => psit0) := by
    rw [hA₁def]
    exact WJ_of_global (S := 2) (n := 0) (isScale0 T).pos (sigma_le_two0 hT1) (by norm_num) hBt
      (by norm_num) (by norm_num) hα.le hα1.le
      (contDiff_infty.1 (contDiff_radFn contDiff_psitP0) _) (fun j hj z => hBtj j (by omega) z)
  have hprod := WH.mul (isScale0 T) hA₁ hF.le hψt.value hg
  rw [zero_add] at hprod
  have hext := hprod.extend_zero0 (by positivity) (by norm_num) le_rfl hT1
    (fun p hp => by
      show psit0 p.1 * g p.2 (‖p.1‖ ^ 2) = 0
      have e : psit0 p.1 = 0 := psitP0_of_ge hp.le
      rw [e, zero_mul])
  have hsrc := HKs θ T _ _ _ hsubI hθ hθ4 hTθ (by positivity) hext
    (fun p hp hne => by
      constructor
      · by_contra hcon
        apply hne
        show psit0 p.1 * g p.2 (‖p.1‖ ^ 2) = 0
        rw [hg0 p.2 hp _ (by linarith [not_le.1 hcon]), mul_zero]
      · by_contra hcon
        apply hne
        show psit0 p.1 * g p.2 (‖p.1‖ ^ 2) = 0
        have e : psit0 p.1 = 0 := psitP0_of_ge (by linarith [not_le.1 hcon])
        rw [e, zero_mul])
  have hfW : WH α (1 / 4) (fun p : Flat18 × ℝ => sth θ p.1) {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0}
      (w - 4) (Ksrc * F) (fun p => psit0 p.1 * g p.2 (‖p.1‖ ^ 2)) := by
    refine hsrc.mono (fun p _ => sth_pos hθ p.1) ?_
    rw [hKsrcdef]
    linarith
  -- the coefficient
  have ha₀ : ∀ x : Flat18, acoef0 c lam x ∈ Icc (c ^ 2 / 256) 1 :=
    fun x => phi0_mem hc0 hc1 (sq_nonneg _)
  have ha₀1 : ∀ x : Flat18, 1 ≤ ‖x‖ → acoef0 c lam x = 1 := fun x hx =>
    phi0_of_gt (by nlinarith)
  have hsm : ContDiff ℝ ∞ (acoef0 c lam) := contDiff_radFn (contDiff_phi0 c lam)
  have ha₀W : ∀ Ω : Set (Flat18 × ℝ), WH α (1 / 4) (fun p : Flat18 × ℝ => sth θ p.1) Ω 0
      (2 * (Ba * 2 ^ (0 + 1))) (fun p => acoef0 c lam p.1) := fun Ω =>
    (WJ_of_global (s := fun p : Flat18 × ℝ => sth θ p.1) (Ω := Ω) (S := 2) (n := 0)
      (fun p _ => sth_pos hθ p.1) (fun p _ => (sth_le_one θ p.1).trans (by norm_num))
      (by norm_num) hBa (by norm_num) (by norm_num) hα.le hα1.le (contDiff_infty.1 hsm _)
      (fun j hj z => hBaj j (by omega) z)).value
  -- the cut-off
  have hχ4 : ContDiff ℝ 4 (cut0 (V := Flat18) θ) := contDiff_infty.1 (contDiff_cut0 θ) 4
  have hχW := HA α θ {p : Flat18 × ℝ | p.2 ∈ Icc (-T) 0} hθ hθ4 hα.le hα1.le
  -- the solution
  obtain ⟨Z, hZ0, hZ4, hZd, hUJ, hUt, hQ1, hQ2, hQ3, hQ4, hZrad⟩ := H (sth θ) (Real.sqrt θ) 1
    Ba Ba T (Ksrc * F) A (acoef0 c lam) (cut0 θ) (fun t z => psit0 z * g t (‖z‖ ^ 2)) hsθ
    (sqrt_le_sth hθ.le hθ1) (fun x => (sth_le_one θ x).trans (by norm_num)) (sth_lipschitz hθ)
    ha₀ ha₀1 hBa hBaL hsm hBa (fun n hn x => hBaj n (by omega) x) ha₀W hT hTC hT4
    (fun t _ x hx => by
      have e : psit0 x = 0 := psitP0_of_ge (by nlinarith)
      show psit0 x * g t (‖x‖ ^ 2) = 0
      rw [e, zero_mul])
    (by positivity) hfW hχ4 hA hχW
  -- supports
  have hcutL : ∀ z : Flat18, ‖z‖ ^ 2 < θ / 2 ∨ 1 / 2 < ‖z‖ ^ 2 → cut0 θ z = 0 := by
    intro z hz
    rcases hz with h | h
    · exact cut0_of_le hθ hθ4 h.le
    · exact cut0_of_ge hθ hθ4 h.le
  have hreg : ∀ z : Flat18, cut0 θ z ≠ 0 → θ / 4 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 3 / 4 := by
    intro z hne
    constructor
    · by_contra hcon
      exact hne (hcutL z (Or.inl (by linarith [not_le.1 hcon])))
    · by_contra hcon
      exact hne (hcutL z (Or.inr (by linarith [not_le.1 hcon])))
  have hsuppU : ∀ (t : ℝ) (z : Flat18), ‖z‖ ^ 2 < θ / 2 ∨ 1 / 2 < ‖z‖ ^ 2 →
      cut0 θ z • Z t z = 0 := fun t z hz => by rw [hcutL z hz, zero_smul]
  have hcontN : Continuous fun y : Flat18 => ‖y‖ ^ 2 := continuous_norm.pow 2
  have hcomm0 : ∀ p : Flat18 × ℝ, ‖p.1‖ ^ 2 < θ / 2 ∨ 1 / 2 < ‖p.1‖ ^ 2 →
      chartOp 6 (fun z => cut0 θ z • Z p.2 z) p.1 - cut0 θ p.1 • chartOp 6 (Z p.2) p.1 = 0 := by
    intro p hp
    have hev : (fun z => cut0 θ z • Z p.2 z) =ᶠ[𝓝 p.1] fun _ => 0 := by
      rcases hp with h | h
      · filter_upwards [(isOpen_lt hcontN continuous_const).mem_nhds h] with z hz
        exact hsuppU p.2 z (Or.inl hz)
      · filter_upwards [(isOpen_lt continuous_const hcontN).mem_nhds h] with z hz
        exact hsuppU p.2 z (Or.inr hz)
    rw [chartOp_eq_zero_of_eventually 6 hev, hcutL p.1 hp, zero_smul, sub_zero]
  -- subsets
  have hsub : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} := fun p hp => hp.1
  have hIcc : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Icc (-T) 0} := fun p hp => ⟨hp.1.1, hp.1.2.le⟩
  have hball : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} := fun p hp =>
    ⟨hp.1, by
      have := norm_nonneg p.1
      nlinarith [hp.2]⟩
  have hσpos := (isScale0 T).pos
  have hX0 : 0 ≤ C₀ * (A * (Ksrc * F)) := by positivity
  have hXδ : 0 ≤ C₀ * (A * ((ε₂ / 2 + Cε * (T / (Real.sqrt θ / 16) ^ 4)) * (Ksrc * F))) := by
    positivity
  -- the bounds in the scale `σ`
  have hUJσ := HKJ θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hX0 (hUJ.restrict hIcc) hsuppU
  have hUtσ := HK4 θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hX0 (hUt.restrict hsub)
    (fun p _ hne => hreg p.1 fun h0 => hne (by
      show cut0 θ p.1 • _ = 0
      rw [h0, zero_smul]))
  have hQ1σ := HK4 θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hX0 (hQ1.restrict hsub)
    (fun p _ hne => hreg p.1 fun h0 => hne (by
      show cut0 θ p.1 • _ = 0
      rw [h0, zero_smul]))
  have hQ2σ := HK4 θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hXδ (hQ2.restrict hball)
    (fun p _ hne => hreg p.1 fun h0 => hne (by
      show cut0 θ p.1 • _ = 0
      rw [h0, zero_smul]))
  have hQ3σ := (HK3 θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hXδ (hQ3.restrict hIcc) hsuppU).value
  have hQ4σ := HK4 θ T _ _ (dom0 T) hsub hθ hθ4 hTθ hXδ (hQ4.restrict hball)
    (fun p _ hne => by
      constructor
      · by_contra hcon
        exact hne (hcomm0 p (Or.inl (by linarith [not_le.1 hcon])))
      · by_contra hcon
        exact hne (hcomm0 p (Or.inr (by linarith [not_le.1 hcon]))))
  -- the common sizes
  have hK4σ : K4 ≤ Kσ := by rw [hKσdef]; linarith
  have hK3σ : K3 ≤ Kσ := by rw [hKσdef]; linarith
  have hQF : 0 ≤ Q₀ * F := by positivity
  have hmono : ∀ K δ : ℝ, 0 ≤ K → K ≤ Kσ → 0 ≤ δ → δ ≤ ε₂ →
      K * (C₀ * (A * (δ * (Ksrc * F)))) ≤ ε₂ * (Q₀ * F) := by
    intro K δ hK hKle hδ0' hδle
    rw [hQ₀def]
    have h1 : K * δ ≤ Kσ * ε₂ := mul_le_mul hKle hδle hδ0' hKσ
    have h2 : 0 ≤ C₀ * (A * (Ksrc * F)) := hX0
    calc K * (C₀ * (A * (δ * (Ksrc * F)))) = K * δ * (C₀ * (A * (Ksrc * F))) := by ring
      _ ≤ Kσ * ε₂ * (C₀ * (A * (Ksrc * F))) := mul_le_mul_of_nonneg_right h1 h2
      _ = ε₂ * (Kσ * (C₀ * (A * Ksrc)) * F) := by ring
  have hq1 : WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (w - 4) (Q₀ * F)
      (fun p => cut0 θ p.1 • Δ (Δ (Z p.2)) p.1) := by
    refine hQ1σ.mono hσpos ?_
    rw [hQ₀def]
    have h1 := mul_le_mul_of_nonneg_right hK4σ hX0
    calc K4 * (C₀ * (A * (Ksrc * F))) ≤ Kσ * (C₀ * (A * (Ksrc * F))) := h1
      _ = Kσ * (C₀ * (A * Ksrc)) * F := by ring
  have hq2 := hQ2σ.mono hσpos (hmono K4 _ hK4 hK4σ hδ0 hδ)
  have hq3 := hQ3σ.mono hσpos (hmono K3 _ hK3 hK3σ hδ0 hδ)
  have hq4 := hQ4σ.mono hσpos (hmono K4 _ hK4 hK4σ hδ0 hδ)
  -- the coefficients
  obtain ⟨hbl, hcl, -, -⟩ := HKc lam T hlam hTlam hT1
  have hbl2 := (WH.mul (isScale0 T) hKc hKc hbl.1 hbl.1).const_smul (1 / 16)
  rw [zero_add, ← hKbdef] at hbl2
  obtain ⟨hbdW, hbdS⟩ := HMb lam θ T hlam hθ hTlam hTθ hT1
  have hbdI := hbdW.interp (isScale0 T) hMb hα hα1.le hTθ0 hTθ1
    (fun p hp => by
      rw [Real.rpow_zero, mul_one, Real.norm_eq_abs]
      exact hbdS p hp)
  have hbd : WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) 0
      (ε₂ * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Mb))
      (fun p => bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)) := by
    refine hbdI.mono hσpos ?_
    have h1 : 0 ≤ (1 + (2 : ℝ) ^ |(0 : ℝ)|) := by positivity
    calc (1 + (2 : ℝ) ^ |(0 : ℝ)|) * (T / θ ^ 2) ^ (1 - α / 1) * Mb
        ≤ (1 + (2 : ℝ) ^ |(0 : ℝ)|) * ε₂ * Mb :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h1) hMb
      _ = ε₂ * ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Mb) := by ring
  have herr := WH.err4 (isScale0 T) hε₂.le hQF (by positivity) hKb hKc hbd hq1 hbl2 hq2 hcl.1 hq3
    hq4
  rw [← hNdef] at herr
  -- the gap
  have hgap := hUJ.gap (isScale_sth hθ (by norm_num) _)
    (fun x => by
      show cut0 θ x • Z (-T) x = 0
      rw [hZ0 x, smul_zero])
    hX0 hα₀ hα₀α hT hsθ (sqrt_le_sth hθ.le hθ1) (by norm_num) (by norm_num) hTa
  rw [← hCgdef] at hgap
  have hρ0 : 0 ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) :=
    Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hT.le _) hsθ.le) _
  have hgapσ := HKJ₀ θ T _ _ (dom0 T) hsub hθ hθ4 hTθ (by positivity) (hgap.restrict hIcc)
    hsuppU
  have hKC : 0 ≤ (KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) := by positivity
  refine ⟨fun t z => cut0 θ z • Z t z,
    fun t z => cut0 θ z • (psit0 z * g t (‖z‖ ^ 2) - acoef0 c lam z * Δ (Δ (Z t)) z),
    fun p => bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)
        * (cut0 θ p.1 • Δ (Δ (Z p.2)) p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (cut0 θ p.1 • lowOp 6 (Z p.2) p.1)
      + clam G lam p.2 (‖p.1‖ ^ 2) * (cut0 θ p.1 • Z p.2 p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (chartOp 6 (fun z => cut0 θ z • Z p.2 z) p.1 - cut0 θ p.1 • chartOp 6 (Z p.2) p.1),
    fun t => hχ4.smul (hZ4 t), fun t z hz => hsuppU t z (Or.inr hz), fun t z hz => ?_,
    fun z => ?_, fun t ht z => (hZd t ht z).const_smul (cut0 θ z), fun t Q z => ?_, ?_, ?_, ?_,
    ?_, fun p hp => ?_, fun t ht z => ?_⟩
  · show cut0 θ z • (psit0 z * g t (‖z‖ ^ 2) - acoef0 c lam z * Δ (Δ (Z t)) z) = 0
    rw [hcutL z (Or.inr hz), zero_smul]
  · show cut0 θ z • Z (-T) z = 0
    rw [hZ0 z, smul_zero]
  · show cut0 θ (Q z) • Z t (Q z) = cut0 θ z • Z t z
    have e2 := hZrad (fun Q x => radFn_rotate (phi0 c lam) Q x)
      (fun t _ Q x => by
        show psit0 (Q x) * g t (‖Q x‖ ^ 2) = psit0 x * g t (‖x‖ ^ 2)
        have e3 : psit0 (Q x) = psit0 x := radFn_rotate psitP0 Q x
        rw [e3, Q.norm_map]) t Q z
    rw [cut0_rotate, e2]
  · refine hUJσ.mono hσpos ?_
    have h1 : KJ * (C₀ * (A * (Ksrc * F))) = KJ * (C₀ * (A * Ksrc)) * F := by ring
    rw [h1]
    have h2 : KJ * (C₀ * (A * Ksrc)) ≤ (KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hKJ₀ hCg]) hCAK
    have h3 := mul_le_mul_of_nonneg_right h2 hF.le
    linarith [hF.le]
  · refine hUtσ.mono hσpos ?_
    have h1 : K4 * (C₀ * (A * (Ksrc * F))) = K4 * (C₀ * (A * Ksrc)) * F := by ring
    rw [h1]
    have h2 : K4 * (C₀ * (A * Ksrc)) ≤ (KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) :=
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hKJ₀ hCg]) hCAK
    have h3 := mul_le_mul_of_nonneg_right h2 hF.le
    linarith [hF.le]
  · refine hgapσ.mono hσpos ?_
    have h1 : KJ₀ * (Cg * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * (C₀ * (A * (Ksrc * F))))
        = KJ₀ * Cg * (C₀ * (A * Ksrc)) * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) := by
      ring
    rw [h1]
    have h2 : KJ₀ * Cg * (C₀ * (A * Ksrc)) ≤ (KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) + 1 := by
      have := mul_le_mul_of_nonneg_right (by linarith : KJ₀ * Cg ≤ KJ + K4 + KJ₀ * Cg) hCAK
      linarith
    have h3 : 0 ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := mul_nonneg hρ0 hF.le
    calc KJ₀ * Cg * (C₀ * (A * Ksrc)) * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F)
        ≤ ((KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) + 1)
          * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = ((KJ + K4 + KJ₀ * Cg) * (C₀ * (A * Ksrc)) + 1)
          * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := by ring
  · refine herr.mono hσpos ?_
    have h1 : N * (ε₂ * (Q₀ * F)) = ε₂ * (N * Q₀) * F := by ring
    rw [h1]
    have h2 : ε₂ * (N * Q₀) ≤ ε := by
      rw [← hε₂N]
      nlinarith [hε₂.le]
    exact mul_le_mul_of_nonneg_right h2 hF.le
  · show bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)
        * (cut0 θ p.1 • Δ (Δ (Z p.2)) p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (cut0 θ p.1 • lowOp 6 (Z p.2) p.1)
      + clam G lam p.2 (‖p.1‖ ^ 2) * (cut0 θ p.1 • Z p.2 p.1)
      + (1 / 16 : ℝ) • (blam G lam p.2 (‖p.1‖ ^ 2) * blam G lam p.2 (‖p.1‖ ^ 2))
        * (chartOp 6 (fun z => cut0 θ z • Z p.2 z) p.1 - cut0 θ p.1 • chartOp 6 (Z p.2) p.1) = 0
    rw [hcomm0 p (Or.inr hp), hcutL p.1 (Or.inr hp)]
    simp
  · have hid := localized_identity (V := Flat18) 6 (blam G lam t (‖z‖ ^ 2) ^ 2)
      (clam G lam t (‖z‖ ^ 2)) (acoef0 c lam z) (psit0 z * g t (‖z‖ ^ 2)) (cut0 θ z)
      (fun y => cut0 θ y • Z t y) (Z t) z
    have h1 := cut0_source (θ := θ) hθ (z := z) (gz := g t (‖z‖ ^ 2)) (fun hz => hg0 t ht _ hz)
    have h2 := coef_diff (c := c) (G := G) (lam := lam) (t := t) hθ hθ4 z
    show cut0 θ z • (psit0 z * g t (‖z‖ ^ 2) - acoef0 c lam z * Δ (Δ (Z t)) z)
        + blam G lam t (‖z‖ ^ 2) ^ 2 * (chartOp 6 (fun y => cut0 θ y • Z t y) z / 16)
        + clam G lam t (‖z‖ ^ 2) * (cut0 θ z • Z t z)
      = chi (4 * ‖z‖ ^ 2) * g t (‖z‖ ^ 2)
        + (bdiff G c lam θ t (‖z‖ ^ 2) * ((1 - ‖z‖ ^ 2) ^ 2 / 16) * (cut0 θ z • Δ (Δ (Z t)) z)
          + (1 / 16 : ℝ) • (blam G lam t (‖z‖ ^ 2) * blam G lam t (‖z‖ ^ 2))
            * (cut0 θ z • lowOp 6 (Z t) z)
          + clam G lam t (‖z‖ ^ 2) * (cut0 θ z • Z t z)
          + (1 / 16 : ℝ) • (blam G lam t (‖z‖ ^ 2) * blam G lam t (‖z‖ ^ 2))
            * (chartOp 6 (fun y => cut0 θ y • Z t y) z - cut0 θ z • chartOp 6 (Z t) z))
    simp only [smul_eq_mul] at hid h1 h2 ⊢
    linear_combination hid + h1 + Δ (Δ (Z t)) z * h2

end Calabi.Weighted
