import Calabi.Correction.ForwardBlock
import Calabi.Correction.ChartJets
import Calabi.Correction.TwoPointMore
import OAI.Analysis.AncientFlat.Weighted.ExactWeightedInverse

/-!
# The two linear solvers for real functions on `[-T, 0)`

The construction of Section 6 of the manuscript works with real functions on
the time interval `[-T, 0)` that ends at the singular time. This file states
the two linear solvers in this form.

* `exists_forward_real`: the forward block (`ForwardBlock.lean`) for a real
  source on `[-T, 0)`: the solution of `∂ₜ Z + a₀ Δ² Z = f` with `Z(-T) = 0`,
  with its weighted bounds (the source is extended to the final time and the
  real part of the complex solution is taken);
* `WJ.gap`: the jets of order at most four of a function that vanishes at the
  initial time are small in a smaller Hölder exponent (Lemma 4.5, (4.17));
* `exists_ancient_real`: the reused ancient inverse for a real radial source
  on `[-T, 0)` with a weighted two-point bound for the scale `σ`: the source
  is extended to all negative times (`ancExt`), and the exact norm of the
  solution is converted into weighted two-point bounds for its jets.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted OAI.FlatSimilarity OAI.ParabolicAnnular

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Translation of the time -/

/-- A translation of the time, for a time-independent scale. -/
theorem WH.time_shift {E : Type*} [NormedAddCommGroup E] {s : V → ℝ} {α a v M : ℝ}
    {Ω : Set (V × ℝ)} {g : V × ℝ → E} (τ₀ : ℝ)
    (hg : WH α a (fun p : V × ℝ => s p.1) Ω v M g) :
    WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | ((p.1, p.2 + τ₀) : V × ℝ) ∈ Ω} v M
      (fun p => g (p.1, p.2 + τ₀)) := by
  refine ⟨fun p hp => hg.1 _ hp, fun p hp q hq hd => ?_⟩
  have e : pdist ((p.1, p.2 + τ₀) : V × ℝ) (q.1, q.2 + τ₀) = pdist p q := by
    unfold pdist
    simp
  have h := hg.2 _ hp _ hq (by rw [e]; exact hd)
  rwa [e] at h

/-! ### Real parts -/

theorem norm_reJet_le (j : ℕ) :
    ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
      Complex.reCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
  rw [one_mul, ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  have h := Complex.reCLM.norm_compContinuousMultilinearMap_le φ
  rwa [Complex.reCLM_norm, one_mul] at h

theorem iteratedFDeriv_re {u : V → ℂ} {j : ℕ} (hu : ContDiff ℝ 4 u) (hj : j ≤ 4) (x : V) :
    iteratedFDeriv ℝ j (fun y => (u y).re) x
      = ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => V) ℂ ℝ
        Complex.reCLM (iteratedFDeriv ℝ j u x) := by
  rw [ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  exact Complex.reCLM.iteratedFDeriv_comp_left hu.contDiffAt (by exact_mod_cast hj)

/-- The bilaplacian of the real part. -/
theorem bilaplacian_re {u : V → ℂ} (hu : ContDiff ℝ 4 u) (x : V) :
    Δ (Δ (fun y => (u y).re)) x = (Δ (Δ u) x).re := by
  have e1 := (hu.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)).contDiffAt.laplacian_CLM_comp_left_nhds
    (l := Complex.reCLM) (x := x)
  have h2 := (contDiff_two_laplacian hu).contDiffAt.laplacian_CLM_comp_left
    (l := Complex.reCLM) (x := x)
  show Δ (Δ (Complex.reCLM ∘ u)) x = _
  rw [(InnerProductSpace.laplacian_congr_nhds e1).eq_of_nhds, h2]
  rfl

/-- The real part of a function with weighted jets. -/
theorem WJ.re {α a w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} {n : ℕ} {u : ℝ → V → ℂ}
    (hn : n ≤ 4) (hus : ∀ t, ContDiff ℝ 4 (u t)) (hu : WJ α a s Ω w M n u) (hM : 0 ≤ M)
    (hs : ∀ p ∈ Ω, 0 < s p) : WJ α a s Ω w M n (fun t x => (u t x).re) := by
  intro j hj
  have h := (hu j hj).clm_le _ (norm_reJet_le (V := V) j) hM hs
  refine h.congr fun p _ => ?_
  exact iteratedFDeriv_re (hus p.2) (hj.trans hn) p.1

/-! ### Small jets from an exponent gap -/

set_option maxHeartbeats 1600000 in
/-- **Lemma 4.5, (4.17)**: the jets of a function that vanishes at the initial
time are small in a smaller Hölder exponent when the elapsed time is short in
the units of the scale. -/
theorem WJ.gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α α' a c w M T smin : ℝ}
    {s : V → ℝ} {n : ℕ} {Z : ℝ → V → E}
    (hZ : WJ α' a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w M n Z)
    (hsc : IsScale a c (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0})
    (hZ0 : ∀ x, Z (-T) x = 0) (hM : 0 ≤ M) (hα : 0 < α) (hαα : α ≤ α') (hT : 0 < T)
    (hsmin : 0 < smin) (hsm : ∀ x, smin ≤ s x) (ha : 0 < a) (ha1 : a ≤ 1)
    (hTa : T ≤ (a * smin) ^ 4) :
    WJ α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w
      ((1 + c ^ (|w| + n)) * (T ^ ((1 : ℝ) / 4) / smin) ^ (α' - α) * M) n Z := by
  intro j hj
  have hα' : 0 < α' := hα.trans_le hαα
  have hc1 := hsc.one_le
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hWH := hZ j hj
  have hTq : 0 ≤ T ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hT.le _
  have hη0 : 0 ≤ T ^ ((1 : ℝ) / 4) / smin := div_nonneg hTq hsmin.le
  have hT4 : T ^ ((1 : ℝ) / 4) ≤ a * smin := by
    have h5 := Real.rpow_le_rpow hT.le hTa (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [ParabolicLocalization.pow_four_quarter (mul_pos ha hsmin).le] at h5
  have hη1 : T ^ ((1 : ℝ) / 4) / smin ≤ 1 := by
    rw [div_le_one hsmin]
    exact hT4.trans (mul_le_of_le_one_left hsmin.le ha1)
  have hθ0 : 0 ≤ (T ^ ((1 : ℝ) / 4) / smin) ^ α' := Real.rpow_nonneg hη0 _
  have hθ1 : (T ^ ((1 : ℝ) / 4) / smin) ^ α' ≤ 1 := Real.rpow_le_one hη0 hη1 hα'.le
  -- the values are small
  have hsup : ∀ p ∈ {p : V × ℝ | p.2 ∈ Icc (-T) 0},
      ‖iteratedFDeriv ℝ j (Z p.2) p.1‖
        ≤ (T ^ ((1 : ℝ) / 4) / smin) ^ α' * (M * s p.1 ^ (w - j)) := by
    intro p hp
    have hsp : 0 < s p.1 := hsmin.trans_le (hsm p.1)
    have hq : ((p.1, -T) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Icc (-T) 0} := ⟨le_rfl, by linarith⟩
    have hz : iteratedFDeriv ℝ j (Z (-T)) p.1 = 0 := by
      have e : Z (-T) = fun _ => (0 : E) := funext hZ0
      rw [e]
      simp
    have hpd : pdist p ((p.1, -T) : V × ℝ) = |p.2 + T| ^ ((1 : ℝ) / 4) := by
      unfold pdist
      simp
    have hpT : |p.2 + T| ≤ T := by
      rw [abs_le]
      constructor <;> linarith [hp.1, hp.2]
    have hd1 : pdist p ((p.1, -T) : V × ℝ) ≤ T ^ ((1 : ℝ) / 4) := by
      rw [hpd]
      exact Real.rpow_le_rpow (abs_nonneg _) hpT (by norm_num)
    have hd2 : pdist p ((p.1, -T) : V × ℝ) ≤ a * s p.1 :=
      hd1.trans (hT4.trans (mul_le_mul_of_nonneg_left (hsm p.1) ha.le))
    have h1 : ‖iteratedFDeriv ℝ j (Z p.2) p.1 - iteratedFDeriv ℝ j (Z (-T)) p.1‖
        ≤ M * s p.1 ^ (w - j - α') * pdist p ((p.1, -T) : V × ℝ) ^ α' :=
      hWH.2 p hp ((p.1, -T) : V × ℝ) hq hd2
    rw [hz, sub_zero] at h1
    have h2 : pdist p ((p.1, -T) : V × ℝ) ^ α' ≤ (T ^ ((1 : ℝ) / 4)) ^ α' :=
      Real.rpow_le_rpow (pdist_nonneg _ _) hd1 hα'.le
    have h3 : s p.1 ^ (w - j - α') = s p.1 ^ (w - j) * s p.1 ^ (-α') := by
      rw [← Real.rpow_add hsp, sub_eq_add_neg (w - j)]
    have h4 : s p.1 ^ (-α') ≤ smin ^ (-α') :=
      Real.rpow_le_rpow_of_nonpos hsmin (hsm p.1) (by linarith)
    have h5 : (T ^ ((1 : ℝ) / 4) / smin) ^ α' = (T ^ ((1 : ℝ) / 4)) ^ α' * smin ^ (-α') := by
      rw [Real.div_rpow hTq hsmin.le, Real.rpow_neg hsmin.le, div_eq_mul_inv]
    have hX : 0 ≤ M * s p.1 ^ (w - j) := mul_nonneg hM (Real.rpow_nonneg hsp.le _)
    have hY : 0 ≤ (T ^ ((1 : ℝ) / 4)) ^ α' := Real.rpow_nonneg hTq _
    calc ‖iteratedFDeriv ℝ j (Z p.2) p.1‖
        ≤ M * s p.1 ^ (w - j - α') * pdist p ((p.1, -T) : V × ℝ) ^ α' := h1
      _ ≤ M * s p.1 ^ (w - j - α') * (T ^ ((1 : ℝ) / 4)) ^ α' :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hM (Real.rpow_nonneg hsp.le _))
      _ = M * s p.1 ^ (w - j) * (s p.1 ^ (-α') * (T ^ ((1 : ℝ) / 4)) ^ α') := by
        rw [h3]
        ring
      _ ≤ M * s p.1 ^ (w - j) * (smin ^ (-α') * (T ^ ((1 : ℝ) / 4)) ^ α') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hY) hX
      _ = (T ^ ((1 : ℝ) / 4) / smin) ^ α' * (M * s p.1 ^ (w - j)) := by
        rw [h5]
        ring
  have h := hWH.interp hsc hM hα hαα hθ0 hθ1 hsup
  refine h.mono hsc.pos ?_
  -- the constant
  have e1 : ((T ^ ((1 : ℝ) / 4) / smin) ^ α') ^ (1 - α / α')
      = (T ^ ((1 : ℝ) / 4) / smin) ^ (α' - α) := by
    rw [← Real.rpow_mul hη0]
    congr 1
    rw [mul_sub, mul_one, mul_div_cancel₀ α hα'.ne']
  rw [e1]
  have h6 : |w - (j : ℝ)| ≤ |w| + n := by
    have := abs_sub w (j : ℝ)
    rw [abs_of_nonneg hj0] at this
    linarith
  have h7 : c ^ |w - (j : ℝ)| ≤ c ^ (|w| + n) := Real.rpow_le_rpow_of_exponent_le hc1 h6
  have h8 : 0 ≤ (T ^ ((1 : ℝ) / 4) / smin) ^ (α' - α) := Real.rpow_nonneg hη0 _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h8) hM

/-! ### The forward problem -/

section Forward

variable [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1600000 in
/-- **The forward block for real sources on `[-T, 0)`.** -/
theorem exists_forward_real (α κ Λ K w : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ)
    (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (s : V → ℝ) (smin smax ρ₀ L J T F : ℝ) (a₀ : V → ℝ) (f : ℝ → V → ℝ),
        0 < smin → (∀ x, smin ≤ s x) → (∀ x, s x ≤ smax) → smax ≤ 16 →
        (∀ x y, |s x - s y| ≤ ‖x - y‖) →
        (∀ x, a₀ x ∈ Icc κ Λ) → (∀ x, ρ₀ ≤ ‖x‖ → a₀ x = 1) → 0 ≤ L →
        (∀ x z, |a₀ x - a₀ z| ≤ L * ‖x - z‖) → ContDiff ℝ ∞ a₀ → 0 ≤ J →
        (∀ n : ℕ, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n a₀ x‖ ≤ J) →
        (∀ Ω : Set (V × ℝ), WH α (1 / 4) (fun p : V × ℝ => s p.1) Ω 0 K (fun p => a₀ p.1)) →
        0 < T → T ≤ (smin / 16) ^ 4 / C → T ≤ 1 / 4 →
        (∀ t ∈ Ico (-T) 0, ∀ x, ρ₀ ≤ ‖x‖ → f t x = 0) → 0 < F →
        WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico (-T) 0} (w - 4) F
          (fun p => f p.2 p.1) →
        ∃ Z : ℝ → V → ℝ, (∀ x, Z (-T) x = 0) ∧ (∀ t, ContDiff ℝ 4 (Z t)) ∧
          (∀ t ∈ Ioo (-T) 0, ∀ x, HasDerivAt (fun r => Z r x)
            (f t x - a₀ x * Δ (Δ (Z t)) x) t) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w (C * F) 4 Z ∧
          WH α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico (-T) 0} (w - 4) (C * F)
            (fun p => f p.2 p.1 - a₀ p.1 * Δ (Δ (Z p.2)) p.1) ∧
          WJ α (1 / 64) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc (-T) 0} w
            ((ε + Cε * (T / (smin / 16) ^ 4)) * (C * F)) 3 Z ∧
          ((∀ (Q : V ≃ₗᵢ[ℝ] V) x, a₀ (Q x) = a₀ x) →
            (∀ t ∈ Ico (-T) 0, ∀ (Q : V ≃ₗᵢ[ℝ] V) x, f t (Q x) = f t x) →
            ∀ t (Q : V ≃ₗᵢ[ℝ] V) x, Z t (Q x) = Z t x) := by
  obtain ⟨C, hC, H⟩ := exists_forward_solution (V := V) α κ Λ K w hα hα1 hκ hΛ hK
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε, H⟩ := H ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro s smin smax ρ₀ L J T F a₀ f hsmin hsm hsM hsM16 hsl ha₀ ha₀1 hL ha₀L ha₀s hJ ha₀J ha₀W
    hT hTC hT4 hf0 hF hfW
  have hspos : ∀ x, 0 < s x := fun x => hsmin.trans_le (hsm x)
  have hsΩ : ∀ (Ω : Set (V × ℝ)), ∀ p ∈ Ω, 0 < (fun p : V × ℝ => s p.1) p :=
    fun _ p _ => hspos p.1
  have hCF : 0 ≤ C * F := mul_nonneg (by linarith) hF.le
  -- the source in the forward time, extended to the final time
  have hsh : WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico 0 T} (w - 4) F
      (fun p => f (p.2 + -T) p.1) :=
    (hfW.time_shift (-T)).restrict (Ω' := {p : V × ℝ | p.2 ∈ Ico 0 T})
      (fun p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩)
  obtain ⟨g, hg1, hg2, hg3⟩ := WH.exists_endpoint_extension hsh hspos (by norm_num) hα hT hF.le
  have hgin : ∀ τ ∈ Ico (0 : ℝ) T, ∀ x, g (x, τ) = f (τ + -T) x := fun τ hτ x => hg1 (x, τ) hτ
  have hmem : ∀ τ ∈ Ico (0 : ℝ) T, τ + -T ∈ Ico (-T) 0 :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hgT0 : ∀ x, ρ₀ ≤ ‖x‖ → g (x, T) = 0 := by
    intro x hx
    refine tendsto_nhds_unique (hg2 x) (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (hf0 (t + -T) (hmem t ⟨ht.1.le, ht.2⟩) x hx).symm
  -- the complex source
  classical
  obtain ⟨fc, hfcdef⟩ : ∃ fc : ℝ → V → ℂ,
      fc = fun τ x => if τ ∈ Icc (0 : ℝ) T then ((g (x, τ) : ℝ) : ℂ) else 0 := ⟨_, rfl⟩
  have hfc : ∀ τ x, fc τ x = if τ ∈ Icc (0 : ℝ) T then ((g (x, τ) : ℝ) : ℂ) else 0 :=
    fun τ x => by rw [hfcdef]
  have hfc_in : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, fc τ x = ((g (x, τ) : ℝ) : ℂ) := by
    intro τ hτ x
    rw [hfc, if_pos hτ]
  have hfc0 : ∀ τ x, ρ₀ ≤ ‖x‖ → fc τ x = 0 := by
    intro τ x hx
    rw [hfc]
    by_cases hτ : τ ∈ Icc (0 : ℝ) T
    · rw [if_pos hτ]
      rcases hτ.2.eq_or_lt with h | h
      · rw [h, hgT0 x hx, Complex.ofReal_zero]
      · rw [hgin τ ⟨hτ.1, h⟩ x, hf0 (τ + -T) (hmem τ ⟨hτ.1, h⟩) x hx, Complex.ofReal_zero]
    · rw [if_neg hτ]
  have hfcW : WH α (1 / 4) (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 T} (w - 4) F
      (fun p => fc p.2 p.1) := by
    refine (hg3.clm_le Complex.ofRealCLM (le_of_eq Complex.ofRealCLM_norm) hF.le
      (hsΩ _)).congr fun p hp => ?_
    exact hfc_in p.2 hp p.1
  obtain ⟨u, hu0, hu4, hud, huJ, hut, huS, hurad, -⟩ := H s smin smax ρ₀ L J T F a₀ fc hsmin
    hsm hsM hsM16 hsl ha₀ ha₀1 hL ha₀L ha₀s hJ ha₀J (ha₀W _) hT hTC hT4 hfc0 hF hfcW
  -- the real part of the equation
  have key : ∀ t ∈ Ico (-T) 0, ∀ x,
      Complex.reCLM (fc (t + T) x - (a₀ x : ℂ) * Δ (Δ (u (t + T))) x)
        = f t x - a₀ x * Δ (Δ (fun y => (u (t + T) y).re)) x := by
    intro t ht x
    have hτ : t + T ∈ Ico (0 : ℝ) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e1 : t + T + -T = t := by ring
    rw [bilaplacian_re (hu4 (t + T)), hfc_in (t + T) ⟨hτ.1, hτ.2.le⟩ x, hgin (t + T) hτ x, e1]
    show (((f t x : ℝ) : ℂ) - (a₀ x : ℂ) * Δ (Δ (u (t + T))) x).re = _
    rw [Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have hsub : ∀ {A B : Set ℝ}, (∀ t ∈ A, t + T ∈ B) →
      {p : V × ℝ | p.2 ∈ A} ⊆ {p : V × ℝ | ((p.1, p.2 + T) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ B}} :=
    fun h p hp => h p.2 hp
  have hIcc : ∀ t ∈ Icc (-T) 0, t + T ∈ Icc (0 : ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco : ∀ t ∈ Ico (-T) 0, t + T ∈ Icc (0 : ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t x => (u (t + T) x).re, fun x => ?_,
    fun t => Complex.reCLM.contDiff.comp (hu4 (t + T)), ?_, ?_, ?_, ?_, ?_⟩
  · show (u (-T + T) x).re = 0
    rw [neg_add_cancel, hu0 x, Complex.zero_re]
  · intro t ht x
    have hτ : t + T ∈ Ioo (0 : ℝ) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 := (hud (t + T) ⟨hτ.1.le, hτ.2.le⟩ x).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (t + T) h1).comp_add_const t T
    rw [key t ⟨ht.1.le, ht.2⟩ x] at h2
    exact h2
  · intro j hj
    have h := huJ.re le_rfl hu4 hCF (hsΩ _)
    exact ((h j hj).time_shift T).restrict (hsub hIcc)
  · have h := ((hut.clm_le Complex.reCLM (le_of_eq Complex.reCLM_norm) hCF
      (hsΩ _)).time_shift T).restrict (hsub hIco)
    refine h.congr fun p hp => ?_
    exact (key p.2 hp p.1).symm
  · intro j hj
    have hS0 : 0 ≤ (ε + Cε * (T / (smin / 16) ^ 4)) * (C * F) := by
      have : 0 ≤ T / (smin / 16) ^ 4 := by positivity
      exact mul_nonneg (add_nonneg hε.le (mul_nonneg hCε.le this)) hCF
    have h := huS.re (by norm_num) hu4 hS0 (hsΩ _)
    exact ((h j hj).time_shift T).restrict (hsub hIcc)
  · intro hrad hfrad t Q x
    have hfcrad : ∀ (Q : V ≃ₗᵢ[ℝ] V) (τ : ℝ) (x : V), fc τ (Q x) = fc τ x := by
      intro Q τ x
      rw [hfc, hfc]
      by_cases hτ : τ ∈ Icc (0 : ℝ) T
      · rw [if_pos hτ, if_pos hτ]
        congr 1
        rcases hτ.2.eq_or_lt with h | h
        · rw [h]
          refine tendsto_nhds_unique (hg2 (Q x)) ((hg2 x).congr' ?_)
          filter_upwards [Ioo_mem_nhdsLT hT] with t ht
          exact (hfrad (t + -T) (hmem t ⟨ht.1.le, ht.2⟩) Q x).symm
        · rw [hgin τ ⟨hτ.1, h⟩ (Q x), hgin τ ⟨hτ.1, h⟩ x]
          exact hfrad (τ + -T) (hmem τ ⟨hτ.1, h⟩) Q x
      · rw [if_neg hτ, if_neg hτ]
    show (u (t + T) (Q x)).re = (u (t + T) x).re
    rw [hurad hrad hfcrad (t + T) Q x]

end Forward

/-! ### The ancient inverse -/

/-- The extension of a radial source is radial. -/
theorem ancExt_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T)
    {f : V × ℝ → E}
    (hf : ∀ (Q : V ≃ₗᵢ[ℝ] V) (p : V × ℝ), p.2 ∈ Ico (-T) 0 → f (Q p.1, p.2) = f p)
    (Q : V ≃ₗᵢ[ℝ] V) (x : V) {t : ℝ} (ht : t < 0) :
    ancExt T f (Q x, t) = ancExt T f (x, t) := by
  have hσ : ∀ r : ℝ, sigma ((Q x, r) : V × ℝ) = sigma (x, r) := by
    intro r
    unfold sigma
    simp
  have hm : max t (-T) ∈ Ico (-T) 0 := ⟨le_max_right _ _, max_lt ht (by linarith)⟩
  unfold ancExt
  show clampT 1 (2 - sigma ((Q x, t) : V × ℝ) / sigma ((Q x, -T) : V × ℝ)) • f (Q x, max t (-T))
    = clampT 1 (2 - sigma ((x, t) : V × ℝ) / sigma ((x, -T) : V × ℝ)) • f (x, max t (-T))
  have e : f (Q x, max t (-T)) = f (x, max t (-T)) := hf Q (x, max t (-T)) hm
  rw [hσ t, hσ (-T), e]

/-- The space of the chart at the point orbit. -/
abbrev Flat18 := EuclideanSpace ℝ (Fin 18)

set_option maxHeartbeats 1600000 in
/-- **The ancient inverse for real radial sources on `[-T, 0)`.** -/
theorem exists_ancient_real {c κ : ℝ} {G H : ℝ → ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0)) (hH0 : H 0 = c)
    (hmatch : ∀ u : ℝ, 0 < u → H u = G (u ^ (-(1 : ℝ) / 2)))
    (hpos : ∀ y : ℝ, 0 ≤ y → κ ≤ G y) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∀ α a : ℝ, 0 < α → α < 1 → 0 < a → a ≤ 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (T M : ℝ) (f : Flat18 × ℝ → ℝ), 0 < T → 0 ≤ M →
        WH α a (sigma (V := Flat18)) {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} (-2 + 4 * γ - 4) M f →
        (∀ (Q : Flat18 ≃ₗᵢ[ℝ] Flat18) (p : Flat18 × ℝ), p.2 ∈ Ico (-T) 0 → f (Q p.1, p.2) = f p) →
        ∃ W Wt : ℝ → Flat18 → ℝ, (∀ t, ContDiff ℝ 4 (W t)) ∧
          (∀ t : ℝ, t < 0 → ∀ x, HasDerivAt (fun r => W r x) (Wt t x) t) ∧
          (∀ t ∈ Ico (-T) 0, ∀ x, Wt t x = f (x, t)
            - profilePrincipal G (x, t) * Δ (Δ (W t)) x - profilePotential G (x, t) * W t x) ∧
          WJ α (1 / 32) (sigma (V := Flat18)) {p : Flat18 × ℝ | p.2 < 0} (-2 + 4 * γ) (C * M) 4 W ∧
          WH α (1 / 32) (sigma (V := Flat18)) {p : Flat18 × ℝ | p.2 < 0} (-2 + 4 * γ - 4) (C * M)
            (fun p => Wt p.2 p.1) ∧
          (∀ t (Q : Flat18 ≃ₗᵢ[ℝ] Flat18) x, W t (Q x) = W t x) := by
  obtain ⟨γ, hγ, hγ1, hinv⟩ := exact_weighted_inverse
    (EuclideanSpace.basisFun (Fin 18) ℝ) G H c κ hc hκ hG hH hH0 hmatch hpos
  refine ⟨γ, hγ, hγ1, fun α a hα hα1 ha ha1 => ?_⟩
  obtain ⟨C, hC, D, hD⟩ := hinv α (1 / 16) hα hα1 (by norm_num) le_rfl
  -- the constants
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = (1 + 2 ^ |(0 : ℝ)|) * 72
      * (8 ^ (|(-2 + 4 * γ - 4 : ℝ)| + |(-2 + 4 * γ - 4 : ℝ) - α|) * 1 ^ α) := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by
    rw [hK₁def]
    positivity
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = 2 ^ |(-2 + 4 * γ - 4 : ℝ)|
      + 2 ^ |(-2 + 4 * γ - 4 : ℝ) - α| * 1 ^ α
      + 2 * 2 ^ |(-2 + 4 * γ - 4 : ℝ)| * (2 * 1 / (a / 8)) ^ α := ⟨_, rfl⟩
  have hK₂ : 0 ≤ K₂ := by
    rw [hK₂def]
    positivity
  refine ⟨(18 : ℝ) ^ 4 * (C * (2 * (K₂ * K₁))) + 1, by positivity, ?_⟩
  intro T M f hT hM hfW hfrad
  -- the extension of the source
  have hext := ancExt_WH hT hfW hM ha ha1 hα.le hα1.le
  have hextM : (1 + 2 ^ |(0 : ℝ)|) * 72
      * (M * 8 ^ (|(-2 + 4 * γ - 4 : ℝ)| + |(-2 + 4 * γ - 4 : ℝ) - α|) * 1 ^ α) = K₁ * M := by
    rw [hK₁def]
    ring
  rw [hextM] at hext
  classical
  obtain ⟨fc, hfcdef⟩ : ∃ fc : Flat18 × ℝ → ℂ,
      fc = fun p => if p.2 < 0 then ((ancExt T f p : ℝ) : ℂ) else 0 := ⟨_, rfl⟩
  have hfc : ∀ p, fc p = if p.2 < 0 then ((ancExt T f p : ℝ) : ℂ) else 0 :=
    fun p => by rw [hfcdef]
  have hfc_neg : ∀ p : Flat18 × ℝ, p.2 < 0 → fc p = ((ancExt T f p : ℝ) : ℂ) := by
    intro p hp
    rw [hfc, if_pos hp]
  have hσpos : ∀ p ∈ {p : Flat18 × ℝ | p.2 < 0}, 0 < sigma p := fun p hp => sigma_pos p hp
  have hK₁M : 0 ≤ K₁ * M := mul_nonneg hK₁ hM
  have hfcW : WH α (a / 8) (sigma (V := Flat18)) {p : Flat18 × ℝ | p.2 < 0} (-2 + 4 * γ - 4)
      (K₁ * M) fc := by
    refine (hext.clm_le Complex.ofRealCLM (le_of_eq Complex.ofRealCLM_norm) hK₁M
      hσpos).congr fun p hp => ?_
    exact hfc_neg p hp
  have hY := yBound_of_WH (a := 1 / 16) hfcW hK₁M (by positivity) hα.le (by norm_num)
    (by norm_num)
  rw [← hK₂def] at hY
  have hYM : 0 ≤ K₂ * (K₁ * M) := mul_nonneg hK₂ hK₁M
  -- the source as an element of the source space
  have hmemS : fc ∈ sourceSpace (V := Flat18) α (-2 + 4 * γ) (1 / 16) := by
    show yNorm α (-2 + 4 * γ) (1 / 16) fc ≠ ⊤ ∧ (∀ p : Flat18 × ℝ, 0 ≤ p.2 → fc p = 0) ∧
      (∀ t : ℝ, t < 0 → Radial (fun x => fc (x, t))) ∧
      (∀ t : ℝ, t < 0 → RealValued (fun x => fc (x, t)))
    refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hY.yNorm hYM), fun p hp => ?_,
      fun t ht Q x => ?_, fun t ht x => ?_⟩
    · rw [hfc, if_neg (not_lt.2 hp)]
    · show fc (Q x, t) = fc (x, t)
      rw [hfc_neg (Q x, t) ht, hfc_neg (x, t) ht, ancExt_rotate hT hfrad Q x ht]
    · show star (fc (x, t)) = fc (x, t)
      rw [hfc_neg (x, t) ht]
      exact Complex.conj_ofReal _
  obtain ⟨hD4, hDd, hDn, hDrad, -⟩ := hD ⟨fc, hmemS⟩
  have hsn : sourceNorm α (-2 + 4 * γ) (1 / 16) (⟨fc, hmemS⟩ : sourceSpace (V := Flat18) α
      (-2 + 4 * γ) (1 / 16)) ≤ 2 * (K₂ * (K₁ * M)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hY.yNorm hYM)
  have hCn : 0 ≤ C * (2 * (K₂ * (K₁ * M))) := by positivity
  have hxn := hDn.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsn hC.le))
  have hX := xBound_of_xNorm_le (EuclideanSpace.basisFun (Fin 18) ℝ) hCn (by norm_num) hxn
  obtain ⟨hWJ, hWt⟩ := WJ_of_xBound (a' := 1 / 32) hX (by norm_num) (by norm_num) hD4
  -- the constant
  have hconst : ((18 : ℕ) : ℝ) ^ 4 * (C * (2 * (K₂ * (K₁ * M))))
      ≤ ((18 : ℝ) ^ 4 * (C * (2 * (K₂ * K₁))) + 1) * M := by
    have e : ((18 : ℕ) : ℝ) ^ 4 * (C * (2 * (K₂ * (K₁ * M))))
        = (18 : ℝ) ^ 4 * (C * (2 * (K₂ * K₁))) * M := by
      push_cast
      ring
    rw [e]
    nlinarith
  have hXM : 0 ≤ ((18 : ℕ) : ℝ) ^ 4 * (C * (2 * (K₂ * (K₁ * M)))) := by positivity
  -- the real part of the equation
  have key : ∀ t ∈ Ico (-T) 0, ∀ x : Flat18,
      Complex.reCLM (profileTime G fc (D ⟨fc, hmemS⟩) t x)
        = f (x, t) - profilePrincipal G (x, t) * Δ (Δ (fun y => (D ⟨fc, hmemS⟩ (y, t)).re)) x
          - profilePotential G (x, t) * (D ⟨fc, hmemS⟩ (x, t)).re := by
    intro t ht x
    rw [bilaplacian_re (hD4 t)]
    unfold profileTime
    rw [hfc_neg (x, t) ht.2, ancExt_of_mem hT f (p := (x, t)) ht]
    show (((f (x, t) : ℝ) : ℂ)
      - (profilePrincipal G (x, t) : ℂ) * Δ (Δ (fun z => D ⟨fc, hmemS⟩ (z, t))) x
      - (profilePotential G (x, t) : ℂ) * D ⟨fc, hmemS⟩ (x, t)).re = _
    rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  refine ⟨fun t x => (D ⟨fc, hmemS⟩ (x, t)).re,
    fun t x => (profileTime G fc (D ⟨fc, hmemS⟩) t x).re,
    fun t => Complex.reCLM.contDiff.comp (hD4 t), fun t ht x => ?_, fun t ht x => ?_, ?_, ?_,
    fun t Q x => ?_⟩
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hDd t ht x)
  · exact key t ht x
  · exact ((hWJ.re le_rfl hD4 hXM hσpos).mono hσpos hconst)
  · exact ((hWt.clm_le Complex.reCLM (le_of_eq Complex.reCLM_norm) hXM hσpos).mono hσpos hconst)
  · show (D ⟨fc, hmemS⟩ (Q x, t)).re = (D ⟨fc, hmemS⟩ (x, t)).re
    exact congrArg Complex.re (hDrad t Q x)

end Calabi.Weighted
