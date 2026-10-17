import Calabi.Correction.LocalSolve
import Calabi.Correction.SigmaTheta
import Calabi.Correction.Coefficients

/-!
# The outer block in the chart at the point orbit

Away from the point orbit, on `x ≥ θ/2` in the chart `x = |z|²` on `ℝ¹⁸`, the
linearized operator `∂ₜ + b_λ² A + c_λ` is solved approximately for a source
`g` that vanishes for `x ≤ θ`:

  `U = χ⁰ Z`,   `∂ₜ Z + a⁰ Δ² Z = ψ̃⁰ g`,   `Z(-T) = 0`,

with the cut-off `χ⁰ = χ(4x) - χ(2x/θ)` and the time-independent coefficient
`a⁰ = (b⁰_λ)² (1 - x)²/16`, where `b⁰_λ` is the limit of the multiplier `b_λ` at
the singular time (`OuterOsc.lean`). The differences with the true operator are
error terms:

* the difference `b_λ² - (b⁰_λ)²` of the principal coefficients, which is
  `O(T/θ²)` (`bdiff_small`) and is made small in the Hölder norm by
  interpolation (`WH.interp`);
* the terms of order at most three of the chart operator, the zeroth-order
  term `c_λ` and the commutator with `χ⁰`, which involve only the jets of order
  at most three of `Z` and are small on a short time interval (Lemma 4.5).

`outer_chart0`: `U` is bounded by the source, uniformly in `θ` and
`T ≤ η θ²`; `∂ₜ U + b_λ² A U + c_λ U = χ(4x) g + err` with a small error; and
the jets of `U` are small in a smaller Hölder exponent (Lemma 4.5, (4.17)).
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Four error terms: a small coefficient times a bounded quantity, and
bounded coefficients times small quantities. -/
theorem WH.err4 {α a w ε Q Mb Kb Kc : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}
    {bd q1 bl2 q2 cl q3 q4 : V × ℝ → ℝ} (hsc : IsScale a 2 s Ω) (hε : 0 ≤ ε) (hQ : 0 ≤ Q)
    (hMb : 0 ≤ Mb) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc) (hbd : WH α a s Ω 0 (ε * Mb) bd)
    (hq1 : WH α a s Ω (w - 4) Q q1) (hbl : WH α a s Ω 0 Kb bl2)
    (hq2 : WH α a s Ω (w - 4) (ε * Q) q2) (hcl : WH α a s Ω (-4) Kc cl)
    (hq3 : WH α a s Ω w (ε * Q) q3) (hq4 : WH α a s Ω (w - 4) (ε * Q) q4) :
    WH α a s Ω (w - 4)
      (((1 + 2 ^ |(0 : ℝ)|) * Mb + (1 + 2 ^ |(0 : ℝ)|) * Kb + (1 + 2 ^ |(-4 : ℝ)|) * Kc
        + (1 + 2 ^ |(0 : ℝ)|) * Kb) * (ε * Q))
      (fun p => bd p * q1 p + bl2 p * q2 p + cl p * q3 p + bl2 p * q4 p) := by
  have h1 := WH.mul hsc (mul_nonneg hε hMb) hQ hbd hq1
  have h2 := WH.mul hsc hKb (mul_nonneg hε hQ) hbl hq2
  have h3 := WH.mul hsc hKc (mul_nonneg hε hQ) hcl hq3
  have h4 := WH.mul hsc hKb (mul_nonneg hε hQ) hbl hq4
  rw [zero_add] at h1 h2 h4
  have e : (-4 : ℝ) + w = w - 4 := by ring
  rw [e] at h3
  refine (((h1.add h2).add h3).add h4).mono hsc.pos (le_of_eq ?_)
  ring

/-! ### The coefficient and the cut-off of the source -/

/-- The profile of the coefficient of the forward problem in the chart at the
point orbit: `(b⁰_λ)² (1 - s)²/16` for `s ≤ 1/2`, and `1` for `s ≥ 3/4`. -/
noncomputable def phi0 (c lam s : ℝ) : ℝ :=
  chi (4 * s - 1) * (bzero c lam s ^ 2 * (1 - s) ^ 2 / 16) + (1 - chi (4 * s - 1))

theorem contDiff_bzero (c lam : ℝ) : ContDiff ℝ ∞ (bzero c lam) := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => chi (s / lam)) :=
    contDiff_chi.comp (contDiff_id.div_const lam)
  exact contDiff_const.add (((contDiff_const.sub contDiff_id).mul h1).mul contDiff_const)

theorem contDiff_phi0 (c lam : ℝ) : ContDiff ℝ ∞ (phi0 c lam) := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => chi (4 * s - 1)) :=
    contDiff_chi.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (h1.mul ((((contDiff_bzero c lam).pow 2).mul
    ((contDiff_const.sub contDiff_id).pow 2)).div_const 16)).add (contDiff_const.sub h1)

theorem phi0_of_gt {c lam s : ℝ} (hs : 3 / 4 < s) : phi0 c lam s = 1 := by
  unfold phi0
  rw [chi_of_ge (by linarith)]
  ring

theorem phi0_of_le {c lam s : ℝ} (hs : s ≤ 1 / 2) :
    phi0 c lam s = bzero c lam s ^ 2 * (1 - s) ^ 2 / 16 := by
  unfold phi0
  rw [chi_of_le (by linarith)]
  ring

theorem phi0_mem {c lam s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 ≤ s) :
    phi0 c lam s ∈ Icc (c ^ 2 / 256) 1 := by
  have hc2 : c ^ 2 / 256 ≤ 1 := by nlinarith
  rcases le_or_gt s (3 / 4) with h | h
  · obtain ⟨hb1, hb2⟩ := bzero_mem (lam := lam) hc0 hc1 ⟨hs, by linarith⟩
    have h1 := chi_nonneg (4 * s - 1)
    have h2 := chi_le_one (4 * s - 1)
    have hbb : c ^ 2 ≤ bzero c lam s ^ 2 := pow_le_pow_left₀ hc0.le hb1 2
    have hbb1 : bzero c lam s ^ 2 ≤ 1 := pow_le_one₀ (hc0.le.trans hb1) hb2
    have hss : (1 : ℝ) / 16 ≤ (1 - s) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s - 1 / 4)
        (by linarith : (0 : ℝ) ≤ 1 - s + 1 / 4)]
    have hss1 : (1 - s) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 2 - s)]
    have hq1 : c ^ 2 / 256 ≤ bzero c lam s ^ 2 * (1 - s) ^ 2 / 16 := by
      have := mul_le_mul hbb hss (by norm_num) (sq_nonneg _)
      linarith
    have hq2 : bzero c lam s ^ 2 * (1 - s) ^ 2 / 16 ≤ 1 := by
      have := mul_le_mul hbb1 hss1 (sq_nonneg _) zero_le_one
      linarith
    have h3 := mul_nonneg h1 (sub_nonneg.2 hq1)
    have h4 := mul_nonneg h1 (sub_nonneg.2 hq2)
    have h5 := mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hc2)
    unfold phi0
    constructor <;> nlinarith
  · rw [phi0_of_gt h]
    exact ⟨hc2, le_rfl⟩

/-- The coefficient of the forward problem in the chart at the point orbit. -/
noncomputable def acoef0 (c lam : ℝ) : Flat18 → ℝ := radFn (phi0 c lam)

/-- The profile of the cut-off of the source: one for `s ≤ 1/2`, zero for
`s ≥ 5/8`. -/
noncomputable def psitP0 (s : ℝ) : ℝ := chi (8 * s - 3)

theorem contDiff_psitP0 : ContDiff ℝ ∞ psitP0 :=
  contDiff_chi.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem psitP0_of_ge {s : ℝ} (hs : 5 / 8 ≤ s) : psitP0 s = 0 := by
  unfold psitP0
  exact chi_of_ge (by linarith)

/-- The cut-off of the source on the chart at the point orbit. -/
noncomputable def psit0 : Flat18 → ℝ := radFn psitP0

theorem chiV_quarter (z : Flat18) : chiV (1 / 4) z = chi (4 * ‖z‖ ^ 2) := by
  unfold chiV
  congr 1
  ring

/-- The cut-off of the outer problem times the cut-off source is `χ(4x)` times
the source, for a source that vanishes for `x ≤ θ`. -/
theorem cut0_source {θ : ℝ} (hθ : 0 < θ) {z : Flat18} {gz : ℝ} (hg : ‖z‖ ^ 2 ≤ θ → gz = 0) :
    cut0 θ z * (psit0 z * gz) = chi (4 * ‖z‖ ^ 2) * gz := by
  have h1 : chiV (θ / 2) z * gz = 0 := by
    rcases le_or_gt (‖z‖ ^ 2) θ with h | h
    · rw [hg h, mul_zero]
    · rw [chiV_of_ge (by positivity) (by linarith), zero_mul]
  have h2 : chiV (1 / 4) z * psit0 z = chiV (1 / 4) z := by
    rcases le_or_gt (‖z‖ ^ 2) (1 / 2) with h | h
    · have e : psit0 z = 1 := by
        show chi (8 * ‖z‖ ^ 2 - 3) = 1
        exact chi_of_le (by linarith)
      rw [e, mul_one]
    · rw [chiV_of_ge (by norm_num) (by linarith), zero_mul]
  rw [← chiV_quarter]
  unfold cut0
  linear_combination gz * h2 - psit0 z * h1

/-- On the support of the cut-off of the outer problem the difference of the
principal coefficients is the function `bdiff`. -/
theorem coef_diff {c : ℝ} {G : ℝ → ℝ} {lam θ t : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (z : Flat18) :
    (blam G lam t (‖z‖ ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 16 - acoef0 c lam z) * cut0 θ z
      = bdiff G c lam θ t (‖z‖ ^ 2) * ((1 - ‖z‖ ^ 2) ^ 2 / 16) * cut0 θ z := by
  rcases le_or_gt (‖z‖ ^ 2) (θ / 2) with h | h
  · rw [cut0_of_le hθ hθ4 h, mul_zero, mul_zero]
  · rcases le_or_gt (1 / 2) (‖z‖ ^ 2) with h' | h'
    · rw [cut0_of_ge hθ hθ4 h', mul_zero, mul_zero]
    · have e1 : acoef0 c lam z = bzero c lam (‖z‖ ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 16 :=
        phi0_of_le h'.le
      have e2 := bdiff_of_ge (G := G) (c := c) (lam := lam) (t := t) hθ h.le
      rw [e1, e2]
      unfold blam
      ring

/-! ### Constants of the changes of scale -/

theorem sigma_of_sth_ex (α v : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (θ T M : ℝ) (f : Flat18 × ℝ → ℝ) (Ω : Set (Flat18 × ℝ)),
      Ω ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} → 0 < θ → θ ≤ 1 / 4 → T ≤ (θ / 4) ^ 2 → 0 ≤ M →
      WH α (1 / 64) (fun p : Flat18 × ℝ => sth θ p.1) Ω v M f →
      (∀ p ∈ Ω, f p ≠ 0 → θ / 4 ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4) →
      WH α (1 / 64) (sigma (V := Flat18)) Ω v (K * M) f := by
  have h1 : 0 ≤ ((3 : ℝ) * 2) ^ (|v| + |v - α|) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ 1 + (1 + (2 : ℝ) ^ |v|) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) := by
    have h3 : 0 ≤ (2 : ℝ) ^ |v| := Real.rpow_nonneg (by norm_num) _
    have h4 : 0 ≤ (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) :=
      Real.rpow_nonneg (le_min (by norm_num) (by norm_num)) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ |v|) h4
    linarith
  refine ⟨((3 : ℝ) * 2) ^ (|v| + |v - α|)
    * (1 + (1 + (2 : ℝ) ^ |v|) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α)),
    mul_nonneg h1 h2, ?_⟩
  intro θ T M f Ω hΩ hθ hθ4 hT hM hf hsupp
  refine (hf.sigma_of_sth hΩ hθ hθ4 hT hM hα hsupp).mono
    (fun p hp => sigma_pos p (hΩ hp).2) (le_of_eq ?_)
  ring

theorem sth_of_sigma_ex (α v : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (θ T M : ℝ) (f : Flat18 × ℝ → ℝ) (Ω : Set (Flat18 × ℝ)),
      Ω ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} → 0 < θ → θ ≤ 1 / 4 → T ≤ (θ / 4) ^ 2 → 0 ≤ M →
      WH α (1 / 64) (sigma (V := Flat18)) Ω v M f →
      (∀ p ∈ Ω, f p ≠ 0 → θ / 4 ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4) →
      WH α (1 / 4) (fun p : Flat18 × ℝ => sth θ p.1) Ω v (K * M) f := by
  have h1 : 0 ≤ ((3 : ℝ) * 2) ^ (|v| + |v - α|) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ 1 + (1 + (2 : ℝ) ^ |v|) * (min (1 / 4) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) := by
    have h3 : 0 ≤ (2 : ℝ) ^ |v| := Real.rpow_nonneg (by norm_num) _
    have h4 : 0 ≤ (min (1 / 4) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) :=
      Real.rpow_nonneg (le_min (by norm_num) (by norm_num)) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ |v|) h4
    linarith
  refine ⟨((3 : ℝ) * 2) ^ (|v| + |v - α|)
    * (1 + (1 + (2 : ℝ) ^ |v|) * (min (1 / 4) (1 / 64 / (3 * 2)) : ℝ) ^ (-α)),
    mul_nonneg h1 h2, ?_⟩
  intro θ T M f Ω hΩ hθ hθ4 hT hM hf hsupp
  refine (hf.sth_of_sigma hΩ hθ hθ4 hT hM hα hsupp).mono (fun p _ => sth_pos hθ p.1)
    (le_of_eq ?_)
  ring

theorem WJ_sigma_of_sth_ex (α w : ℝ) (n : ℕ) (hα : 0 ≤ α) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (θ T M : ℝ) (u : ℝ → Flat18 → ℝ) (Ω : Set (Flat18 × ℝ)),
      Ω ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} → 0 < θ → θ ≤ 1 / 4 → T ≤ (θ / 4) ^ 2 → 0 ≤ M →
      WJ α (1 / 64) (fun p : Flat18 × ℝ => sth θ p.1) Ω w M n u →
      (∀ t z, ‖z‖ ^ 2 < θ / 2 ∨ 1 / 2 < ‖z‖ ^ 2 → u t z = 0) →
      WJ α (1 / 64) (sigma (V := Flat18)) Ω w (K * M) n u := by
  have h1 : 0 ≤ ((3 : ℝ) * 2) ^ (|w| + n + (|w - α| + n)) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ 1 + (1 + (2 : ℝ) ^ (|w| + n))
      * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) := by
    have h3 : 0 ≤ (2 : ℝ) ^ (|w| + n) := Real.rpow_nonneg (by norm_num) _
    have h4 : 0 ≤ (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) :=
      Real.rpow_nonneg (le_min (by norm_num) (by norm_num)) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ (|w| + n)) h4
    linarith
  refine ⟨((3 : ℝ) * 2) ^ (|w| + n + (|w - α| + n))
    * (1 + (1 + (2 : ℝ) ^ (|w| + n)) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α)),
    mul_nonneg h1 h2, ?_⟩
  intro θ T M u Ω hΩ hθ hθ4 hT hM hu hsupp
  refine (hu.sigma_of_sth hΩ hθ hθ4 hT hM hα hsupp).mono
    (fun p hp => sigma_pos p (hΩ hp).2) (le_of_eq ?_)
  ring

/-- **The difference of the principal coefficients in the chart**: bounded in
the Lipschitz two-point norm uniformly, and of size `T/θ²`. -/
theorem bdP_chart {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (lam θ T : ℝ), 0 < lam → 0 < θ → T ≤ lam ^ 2 → T ≤ (θ / 4) ^ 2 → T ≤ 1 →
      WH 1 (1 / 64) (sigma (V := Flat18)) (dom0 T) 0 M
        (fun p => bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)) ∧
      ∀ p ∈ dom0 T, |bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)|
        ≤ T / θ ^ 2 * M := by
  obtain ⟨Cb, hCb, Hb⟩ := bdiff_osc hP
  obtain ⟨Cs, hCs, Hs⟩ := bdiff_small hP
  obtain ⟨K, hK, HK⟩ := B0.of_oscE 1 0 zero_le_one le_rfl
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ, Cp = 4 * (|(1 / 16 : ℝ)| + |(-1 / 8 : ℝ)| + |(1 / 16 : ℝ)|
      + |(0 : ℝ)| + |(0 : ℝ)|) * 2 := ⟨_, rfl⟩
  have hCp : 0 ≤ Cp := by rw [hCpdef]; positivity
  refine ⟨K * (2 * Cb * Cp) + Cs, by positivity, ?_⟩
  intro lam θ T hlam hθ hTlam hTθ hT1
  have hosc := Hb lam θ T hlam hθ hTlam hTθ hT1
  have hpol := oscE_pol hT1 (1 / 16) (-1 / 8) (1 / 16) 0 0
  rw [← hCpdef] at hpol
  have hprod := (hosc.mul hpol hCb hCp).cast (by norm_num : (0 : ℤ) + 0 = 0)
  have hB := (HK T _ _ hprod (by positivity) hT1).1
  have e : ((2 * 0 : ℤ) : ℝ) = 0 := by norm_num
  rw [e] at hB
  constructor
  · refine (hB.congr fun p _ => ?_).mono (isScale0 T).pos (by linarith)
    show bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * ((1 - ‖p.1‖ ^ 2) ^ 2 / 16)
      = bdiff G c lam θ p.2 (‖p.1‖ ^ 2) * pol (1 / 16) (-1 / 8) (1 / 16) 0 0 (‖p.1‖ ^ 2)
    unfold pol
    ring
  · intro p hp
    have hx : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by linarith [hp.2]⟩
    have h1 := Hs lam θ T hθ hTθ p.2 hp.1 _ hx
    have h2 : |(1 - ‖p.1‖ ^ 2) ^ 2 / 16| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hx.1, hx.2]
    have hT0 : 0 ≤ T / θ ^ 2 := by
      have : 0 ≤ T := by linarith [hp.1.1, hp.1.2]
      positivity
    rw [abs_mul]
    calc |bdiff G c lam θ p.2 (‖p.1‖ ^ 2)| * |(1 - ‖p.1‖ ^ 2) ^ 2 / 16|
        ≤ Cs * (T / θ ^ 2) * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ T / θ ^ 2 * (K * (2 * Cb * Cp) + Cs) := by
        have := mul_nonneg hT0 (by positivity : 0 ≤ K * (2 * Cb * Cp))
        linarith

end Calabi.Weighted
