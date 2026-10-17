import Calabi.Correction.RealSolvers

/-!
# A localized zero-data solution in a flat chart

The outer part of the approximate inverse of Section 6.2 of the manuscript is,
in each flat chart, a cut-off `χ` times the zero-data solution `Z` of the
forward problem `∂ₜ Z + a₀ Δ² Z = f` with a time-independent coefficient.
`exists_localized` collects what the construction needs from it, for the
time-independent scale of the forward block:

* the weighted jets of `χ Z` of order at most four and its time derivative
  `χ (f - a₀ Δ² Z)` are bounded by the source;
* `χ Δ² Z` is bounded by the source;
* the three quantities that enter the error of the approximate inverse are
  small on a short time interval: `χ` times the terms of order at most three
  of the chart operator, the jets of order at most three of `χ Z`, and the
  commutator of the chart operator with `χ`. The factor is
  `ε + C_ε T / (inf s / 16)⁴`.

`localized_identity` is the algebraic identity that expresses the chart form of
the operator `∂ₜ + q A + c₀` on `χ Z` through these quantities.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The chart operator on a localized solution.** With `Uₜ = χ (f - a₀ Δ² Z)`,

  `Uₜ + q chartOp(χ Z)/16 + c₀ χ Z = χ f + (q (1 - |z|²)²/16 - a₀) χ Δ² Z
      + q χ lowOp(Z)/16 + c₀ χ Z + q [chartOp, χ] Z/16`. -/
theorem localized_identity (m q c₀ a₀ fx χx : ℝ) (χZ Z : V → ℝ) (x : V) :
    χx * (fx - a₀ * Δ (Δ Z) x) + q * chartOp m χZ x / 16 + c₀ * (χx * Z x)
      = χx * fx + (q * (1 - ‖x‖ ^ 2) ^ 2 / 16 - a₀) * (χx * Δ (Δ Z) x)
        + q / 16 * (χx * lowOp m Z x) + c₀ * (χx * Z x)
        + q / 16 * (chartOp m χZ x - χx * chartOp m Z x) := by
  rw [chartOp_eq_lowOp m Z x]
  ring

variable [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1600000 in
/-- **A cut-off times the zero-data solution of the forward problem.** -/
theorem exists_localized (α κ Λ K w m : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ)
    (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (s : V → ℝ) (smin ρ₀ L J T F A : ℝ) (a₀ χ : V → ℝ) (f : ℝ → V → ℝ),
        0 < smin → (∀ x, smin ≤ s x) → (∀ x, s x ≤ 2) →
        (∀ x y, |s x - s y| ≤ ‖x - y‖) →
        (∀ x, a₀ x ∈ Icc κ Λ) → (∀ x, ρ₀ ≤ ‖x‖ → a₀ x = 1) → 0 ≤ L →
        (∀ x z, |a₀ x - a₀ z| ≤ L * ‖x - z‖) → ContDiff ℝ ∞ a₀ → 0 ≤ J →
        (∀ n : ℕ, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n a₀ x‖ ≤ J) →
        (∀ Ω : Set (V × ℝ), WH α (1 / 4) (fun p : V × ℝ => s p.1) Ω 0 K (fun p => a₀ p.1)) →
        0 < T → T ≤ (smin / 16) ^ 4 / C → T ≤ 1 / 4 →
        (∀ t ∈ Ico (-T) 0, ∀ x, ρ₀ ≤ ‖x‖ → f t x = 0) → 0 < F →
        WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico (-T) 0} (w - 4) F
          (fun p => f p.2 p.1) →
        ContDiff ℝ 4 χ → 0 ≤ A →
        WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} 0 A 4
          (fun _ => χ) →
        ∃ Z : ℝ → V → ℝ, (∀ x, Z (-T) x = 0) ∧ (∀ t, ContDiff ℝ 4 (Z t)) ∧
          (∀ t ∈ Ioo (-T) 0, ∀ x, HasDerivAt (fun r => Z r x)
            (f t x - a₀ x * Δ (Δ (Z t)) x) t) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w
            (C * (A * F)) 4 (fun t x => χ x • Z t x) ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico (-T) 0} (w - 4)
            (C * (A * F)) (fun p => χ p.1 • (f p.2 p.1 - a₀ p.1 * Δ (Δ (Z p.2)) p.1)) ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico (-T) 0} (w - 4)
            (C * (A * F)) (fun p => χ p.1 • Δ (Δ (Z p.2)) p.1) ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1)
            {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} (w - 4)
            (C * (A * ((ε + Cε * (T / (smin / 16) ^ 4)) * F)))
            (fun p => χ p.1 • lowOp m (Z p.2) p.1) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w
            (C * (A * ((ε + Cε * (T / (smin / 16) ^ 4)) * F))) 3 (fun t x => χ x • Z t x) ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1)
            {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} (w - 4)
            (C * (A * ((ε + Cε * (T / (smin / 16) ^ 4)) * F)))
            (fun p => chartOp m (fun z => χ z • Z p.2 z) p.1 - χ p.1 • chartOp m (Z p.2) p.1) ∧
          ((∀ (Q : V ≃ₗᵢ[ℝ] V) x, a₀ (Q x) = a₀ x) →
            (∀ t ∈ Ico (-T) 0, ∀ (Q : V ≃ₗᵢ[ℝ] V) x, f t (Q x) = f t x) →
            ∀ t (Q : V ≃ₗᵢ[ℝ] V) x, Z t (Q x) = Z t x) := by
  obtain ⟨C₀, hC₀, H⟩ := exists_forward_real (V := V) α κ Λ K w hα hα1 hκ hΛ hK
  obtain ⟨C₁, hC₁, H₁⟩ := lowBound_lowOp (V := V) 2 w 2 m (by norm_num)
  obtain ⟨C₂, hC₂, H₂⟩ := chartOp_comm_WH (V := V) 2 w 2 m (by norm_num) (by norm_num)
  have hC₀0 : 0 < C₀ := by linarith
  -- the numerical constants
  obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : ℝ, N₀ = 1 + (2 : ℝ) ^ |(0 : ℝ)| := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁def⟩ : ∃ N₁ : ℝ, N₁ = 2 ^ 4 * (1 + (2 : ℝ) ^ ((4 : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨N₃, hN₃def⟩ : ∃ N₃ : ℝ, N₃ = 2 ^ 3 * (1 + (2 : ℝ) ^ ((3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hN₀ : 0 ≤ N₀ := by rw [hN₀def]; positivity
  have hN₁ : 0 ≤ N₁ := by rw [hN₁def]; positivity
  have hN₃ : 0 ≤ N₃ := by rw [hN₃def]; positivity
  obtain ⟨Bl, hBldef⟩ : ∃ Bl : ℝ, Bl = ‖(bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hBl : 0 ≤ Bl := by
    rw [hBldef]
    exact norm_nonneg (bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 1 + N₁ + N₀ + N₀ * Bl + N₀ * C₁ * 2 + N₃ + C₂ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  have hleN : ∀ n : ℝ, n ≤ N → ∀ X : ℝ, 0 ≤ X → n * (C₀ * X) ≤ C₀ * N * X := by
    intro n hn X hX
    have h1 : 0 ≤ C₀ * X := mul_nonneg hC₀0.le hX
    have h2 := mul_le_mul_of_nonneg_right hn h1
    linarith
  have hn₁ : N₁ ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  have hn₀ : N₀ ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  have hnb : N₀ * Bl ≤ N := by
    rw [hNdef]
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  have hnl : N₀ * C₁ * 2 ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    linarith
  have hn₃ : N₃ ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  have hnc : C₂ ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ N₀ * Bl := mul_nonneg hN₀ hBl
    have h2 : 0 ≤ N₀ * C₁ * 2 := by positivity
    linarith
  refine ⟨C₀ * N, one_le_mul_of_one_le_of_one_le hC₀ hN1, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε, H⟩ := H ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro s smin ρ₀ L J T F A a₀ χ f hsmin hsm hsM hsl ha₀ ha₀1 hL ha₀L ha₀s hJ ha₀J ha₀W hT hTC
    hT4 hf0 hF hfW hχ4 hA hχW
  have hspos : ∀ x, 0 < s x := fun x => hsmin.trans_le (hsm x)
  have hTC₀ : T ≤ (smin / 16) ^ 4 / C₀ := by
    refine hTC.trans ?_
    have h1 : C₀ ≤ C₀ * N := le_mul_of_one_le_right hC₀0.le hN1
    exact div_le_div_of_nonneg_left (by positivity) hC₀0 h1
  obtain ⟨Z, hZ0, hZ4, hZd, hZJ, hZt, hZS, hZrad⟩ := H s smin 2 ρ₀ L J T F a₀ f hsmin hsm hsM
    (by norm_num) hsl ha₀ ha₀1 hL ha₀L ha₀s hJ ha₀J ha₀W hT hTC₀ hT4 hf0 hF hfW
  -- the scale
  have hsc : ∀ Ω : Set (V × ℝ), IsScale (1 / 64) 2 (fun p : V × ℝ => s p.1) Ω :=
    fun Ω => isScale_of_space hspos hsl (by norm_num)
  have hCF : 0 ≤ C₀ * F := mul_nonneg hC₀0.le hF.le
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε + Cε * (T / (smin / 16) ^ 4) := ⟨_, rfl⟩
  have hδ : 0 ≤ δ := by
    rw [hδdef]
    have : 0 ≤ T / (smin / 16) ^ 4 := by positivity
    exact add_nonneg hε.le (mul_nonneg hCε.le this)
  rw [← hδdef] at hZS
  have hδCF : 0 ≤ δ * (C₀ * F) := mul_nonneg hδ hCF
  have hAF : 0 ≤ A * F := mul_nonneg hA hF.le
  have hAδF : 0 ≤ A * (δ * F) := mul_nonneg hA (mul_nonneg hδ hF.le)
  have hχs : ∀ _ : ℝ, ContDiff ℝ 4 χ := fun _ => hχ4
  have hχ3 : ∀ _ : ℝ, ContDiff ℝ 3 χ := fun _ => hχ4.of_le (by norm_num)
  have hZ3 : ∀ t, ContDiff ℝ 3 (Z t) := fun t => (hZ4 t).of_le (by norm_num)
  have hIco : {p : V × ℝ | p.2 ∈ Ico (-T) 0} ⊆ {p : V × ℝ | p.2 ∈ Icc (-T) 0} :=
    fun p hp => ⟨hp.1, hp.2.le⟩
  have hball : {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} ⊆ {p : V × ℝ | p.2 ∈ Icc (-T) 0} :=
    fun p hp => ⟨hp.1.1, hp.1.2.le⟩
  have hχv := (hχW.value).restrict hIco
  have hχvb := (hχW.value).restrict hball
  rw [← hδdef]
  refine ⟨Z, hZ0, hZ4, hZd, ?_, ?_, ?_, ?_, ?_, ?_, hZrad⟩
  · -- the jets of `χ Z`
    have h := WJ.smul (hsc _) hA hCF hχs hZ4 hχW hZJ
    rw [← hN₁def] at h
    refine h.mono (hsc _).pos ?_
    calc N₁ * A * (C₀ * F) = N₁ * (C₀ * (A * F)) := by ring
      _ ≤ C₀ * N * (A * F) := hleN N₁ hn₁ _ hAF
  · -- the time derivative
    have h := WH.smul (hsc _) hA hCF hχv hZt
    rw [zero_add, ← hN₀def] at h
    refine h.mono (hsc _).pos ?_
    calc N₀ * A * (C₀ * F) = N₀ * (C₀ * (A * F)) := by ring
      _ ≤ C₀ * N * (A * F) := hleN N₀ hn₀ _ hAF
  · -- `χ Δ² Z`
    have e4 : w - ((4 : ℕ) : ℝ) = w - 4 := by norm_num
    have h4 := ((hZJ 4 le_rfl).clm bilapL).restrict hIco
    rw [e4, ← hBldef] at h4
    have h := WH.smul (hsc _) hA (mul_nonneg hBl hCF) hχv h4
    rw [zero_add, ← hN₀def] at h
    refine (h.congr fun p _ => ?_).mono (hsc _).pos ?_
    · show χ p.1 • Δ (Δ (Z p.2)) p.1 = χ p.1 • bilapL (iteratedFDeriv ℝ 4 (Z p.2) p.1)
      rw [bilaplacian_eq_bilapL (hZ4 p.2)]
    · calc N₀ * A * (Bl * (C₀ * F)) = N₀ * Bl * (C₀ * (A * F)) := by ring
        _ ≤ C₀ * N * (A * F) := hleN _ hnb _ hAF
  · -- `χ` times the terms of order at most three
    have hlow := (H₁ α (1 / 64) (δ * (C₀ * F)) (fun p : V × ℝ => s p.1)
      {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} Z (hsc _) hδCF (by norm_num) hα.le hα1.le
      (fun p _ => hsM p.1) (fun p hp => hp.2) hZ3 (hZS.restrict hball)).weight (w' := w - 4)
      (mul_nonneg hC₁ hδCF) (hsc _).pos (fun p _ => hsM p.1) (by linarith)
    have e1 : w - 3 - (w - 4) = 1 := by ring
    rw [e1, Real.rpow_one] at hlow
    have h := WH.smul (hsc _) hA (by positivity) hχvb hlow
    rw [zero_add, ← hN₀def] at h
    refine h.mono (hsc _).pos ?_
    calc N₀ * A * (C₁ * (δ * (C₀ * F)) * 2) = N₀ * C₁ * 2 * (C₀ * (A * (δ * F))) := by ring
      _ ≤ C₀ * N * (A * (δ * F)) := hleN _ hnl _ hAδF
  · -- the jets of order at most three of `χ Z`
    have h := WJ.smul (hsc _) hA hδCF hχ3 hZ3 (hχW.of_le (by norm_num)) hZS
    rw [← hN₃def] at h
    refine h.mono (hsc _).pos ?_
    calc N₃ * A * (δ * (C₀ * F)) = N₃ * (C₀ * (A * (δ * F))) := by ring
      _ ≤ C₀ * N * (A * (δ * F)) := hleN N₃ hn₃ _ hAδF
  · -- the commutator
    have h := H₂ α (1 / 64) A (δ * (C₀ * F)) (fun p : V × ℝ => s p.1)
      {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ≤ 1} (fun _ => χ) Z (hsc _) hA hδCF (by norm_num)
      hα.le hα1.le (fun p _ => hsM p.1) (fun p hp => hp.2) hχs hZ4 (hχW.restrict hball)
      (hZS.restrict hball)
    refine h.mono (hsc _).pos ?_
    calc C₂ * (A * (δ * (C₀ * F))) = C₂ * (C₀ * (A * (δ * F))) := by ring
      _ ≤ C₀ * N * (A * (δ * F)) := hleN C₂ hnc _ hAδF

end Calabi.Weighted
