import Calabi.Correction.TwoPointJets
import Calabi.Radial.Cutoff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial cut-offs and coefficients on a flat chart

The cut-offs and the time-independent coefficients of the construction are
functions `z ↦ φ(|z|²)` on the flat chart, with a smooth profile `φ` that is
eventually constant.

* `radFn φ`, `contDiff_radFn`, `radFn_bounded`: such a function is smooth and
  all its derivatives are bounded;
* `iteratedFDeriv_radFn_eq_zero`: its derivatives vanish where the profile is
  locally constant;
* `chiV μ z = χ(|z|²/μ)`, `norm_iteratedFDeriv_chiV_le`: the cut-off at the
  scale `μ` in the momentum coordinate has derivatives of order `j` bounded by
  `B μ^{-j/2}`, uniformly in `μ`;
* `WJ_of_global`, `WJ_chiV`: weighted jets of weight zero for a function with
  bounded derivatives on a bounded scale, and for `chiV μ` on a scale that is
  at most `K √μ` on the transition region.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Radial functions with a smooth profile -/

/-- The radial function `z ↦ φ(|z|²)`. -/
def radFn (φ : ℝ → ℝ) (z : V) : ℝ := φ (‖z‖ ^ 2)

theorem contDiff_radFn {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (radFn (V := V) φ) :=
  hφ.comp (contDiff_norm_sq ℝ)

theorem radFn_rotate (φ : ℝ → ℝ) (Q : V ≃ₗᵢ[ℝ] V) (z : V) : radFn φ (Q z) = radFn φ z := by
  unfold radFn
  rw [Q.norm_map]

/-- The derivatives of positive order vanish where the profile is locally
constant. -/
theorem iteratedFDeriv_radFn_eq_zero {φ : ℝ → ℝ} {c₀ : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hc : ∀ s ∈ U, φ s = c₀) {z : V} (hz : ‖z‖ ^ 2 ∈ U) {j : ℕ} (hj : j ≠ 0) :
    iteratedFDeriv ℝ j (radFn (V := V) φ) z = 0 := by
  have hcont : Continuous fun y : V => ‖y‖ ^ 2 := continuous_norm.pow 2
  have hev : radFn (V := V) φ =ᶠ[𝓝 z] fun _ => c₀ := by
    filter_upwards [(hU.preimage hcont).mem_nhds hz] with y hy
    exact hc _ hy
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_const_of_ne hj]
  rfl

/-- All the derivatives of a radial function with a smooth, eventually constant
profile are bounded. -/
theorem radFn_bounded {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {s₁ c₀ : ℝ}
    (hc : ∀ s : ℝ, s₁ < s → φ s = c₀) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : V, ‖iteratedFDeriv ℝ j (radFn (V := V) φ) z‖ ≤ B := by
  have hsm := contDiff_radFn (V := V) hφ
  have hcont : Continuous fun z : V => iteratedFDeriv ℝ j (radFn (V := V) φ) z :=
    (contDiff_infty.1 hsm j).continuous_iteratedFDeriv'
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) (|s₁| + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B |c₀|, le_max_of_le_right (abs_nonneg _), fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ |s₁| + 1
  · exact (hB z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · have hz1 : |s₁| + 1 < ‖z‖ := not_le.1 hz
    have hz2 : s₁ < ‖z‖ ^ 2 := by
      have h1 := abs_nonneg s₁
      have h2 := le_abs_self s₁
      nlinarith
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [norm_iteratedFDeriv_zero]
      unfold radFn
      rw [hc _ hz2, Real.norm_eq_abs]
      exact le_max_right _ _
    · rw [iteratedFDeriv_radFn_eq_zero isOpen_Ioi (fun s hs => hc s hs) hz2 h0.ne', norm_zero]
      exact le_max_of_le_right (abs_nonneg _)

/-- A uniform bound for the derivatives of order at most five and a Lipschitz
constant of a radial function with a smooth, eventually constant profile. -/
theorem radFn_data {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {s₁ c₀ : ℝ}
    (hc : ∀ s : ℝ, s₁ < s → φ s = c₀) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j : ℕ, j ≤ 5 → ∀ z : V, ‖iteratedFDeriv ℝ j (radFn (V := V) φ) z‖ ≤ B) ∧
      ∀ x z : V, |radFn φ x - radFn φ z| ≤ B * ‖x - z‖ := by
  choose B hB hb using radFn_bounded (V := V) hφ hc
  have hBtot : 0 ≤ ∑ j ∈ Finset.range 6, B j := Finset.sum_nonneg fun j _ => hB j
  have hle : ∀ j : ℕ, j ≤ 5 → B j ≤ ∑ i ∈ Finset.range 6, B i := fun j hj =>
    Finset.single_le_sum (f := B) (fun i _ => hB i) (Finset.mem_range.2 (by omega))
  refine ⟨∑ j ∈ Finset.range 6, B j, hBtot, fun j hj z => (hb j z).trans (hle j hj),
    fun x z => ?_⟩
  have hsm := contDiff_radFn (V := V) hφ
  have hdiff : Differentiable ℝ (radFn (V := V) φ) :=
    (contDiff_infty.1 hsm 1).differentiable one_ne_zero
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := radFn (V := V) φ)
    (s := Set.univ) (C := ∑ j ∈ Finset.range 6, B j) (fun y _ => hdiff y)
    (fun y _ => by
      rw [← norm_iteratedFDeriv_one]
      exact (hb 1 y).trans (hle 1 (by norm_num)))
    convex_univ (Set.mem_univ z) (Set.mem_univ x)
  rwa [Real.norm_eq_abs] at h

/-! ### The cut-off at a scale in the momentum coordinate -/

/-- The cut-off `χ(|z|²/μ)`: one for `|z|² ≤ μ`, zero for `|z|² ≥ 2μ`. -/
noncomputable def chiV (μ : ℝ) (z : V) : ℝ := chi (‖z‖ ^ 2 / μ)

theorem chiV_of_le {μ : ℝ} (hμ : 0 < μ) {z : V} (hz : ‖z‖ ^ 2 ≤ μ) : chiV μ z = 1 :=
  chi_of_le ((div_le_one hμ).2 hz)

theorem chiV_of_ge {μ : ℝ} (hμ : 0 < μ) {z : V} (hz : 2 * μ ≤ ‖z‖ ^ 2) : chiV μ z = 0 :=
  chi_of_ge ((le_div_iff₀ hμ).2 hz)

theorem chiV_nonneg (μ : ℝ) (z : V) : 0 ≤ chiV μ z := chi_nonneg _

theorem chiV_le_one (μ : ℝ) (z : V) : chiV μ z ≤ 1 := chi_le_one _

theorem contDiff_chiV (μ : ℝ) : ContDiff ℝ ∞ (chiV (V := V) μ) :=
  contDiff_chi.comp ((contDiff_norm_sq ℝ).div_const μ)

theorem chiV_rotate (μ : ℝ) (Q : V ≃ₗᵢ[ℝ] V) (z : V) : chiV μ (Q z) = chiV μ z := by
  unfold chiV
  rw [Q.norm_map]

theorem chiV_eq_smul {μ : ℝ} (hμ : 0 < μ) (z : V) :
    chiV μ z = radFn chi ((Real.sqrt μ)⁻¹ • z) := by
  unfold chiV radFn
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hμ.le, div_eq_inv_mul]

/-- The derivatives of positive order of the cut-off vanish off the transition
region `μ ≤ |z|² ≤ 2μ`. -/
theorem iteratedFDeriv_chiV_eq_zero {μ : ℝ} (hμ : 0 < μ) {z : V}
    (hz : ‖z‖ ^ 2 < μ ∨ 2 * μ < ‖z‖ ^ 2) {j : ℕ} (hj : j ≠ 0) :
    iteratedFDeriv ℝ j (chiV (V := V) μ) z = 0 := by
  have e : chiV (V := V) μ = radFn (fun s => chi (s / μ)) := rfl
  rw [e]
  rcases hz with h | h
  · exact iteratedFDeriv_radFn_eq_zero (c₀ := 1) isOpen_Iio
      (fun s hs => chi_of_le ((div_le_one hμ).2 (le_of_lt hs))) h hj
  · exact iteratedFDeriv_radFn_eq_zero (c₀ := 0) isOpen_Ioi
      (fun s hs => chi_of_ge ((le_div_iff₀ hμ).2 (le_of_lt hs))) h hj

/-- **The derivatives of the cut-off at the scale `μ`** are bounded by
`B μ^{-j/2}`, uniformly in `μ`. -/
theorem norm_iteratedFDeriv_chiV_le (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (μ : ℝ), 0 < μ → ∀ z : V,
    ‖iteratedFDeriv ℝ j (chiV (V := V) μ) z‖ ≤ B * (Real.sqrt μ)⁻¹ ^ j := by
  obtain ⟨B, hB, hb⟩ := radFn_bounded (V := V) contDiff_chi (s₁ := 2) (c₀ := 0)
    (fun s hs => chi_of_ge hs.le) j
  refine ⟨B, hB, fun μ hμ z => ?_⟩
  have hρ : 0 ≤ (Real.sqrt μ)⁻¹ ^ j := pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg μ)) j
  have e : chiV (V := V) μ = fun z => radFn chi ((Real.sqrt μ)⁻¹ • z) :=
    funext (chiV_eq_smul hμ)
  rw [e, iteratedFDeriv_comp_const_smul _ (contDiff_infty.1 (contDiff_radFn contDiff_chi) j)]
  show ‖(Real.sqrt μ)⁻¹ ^ j • iteratedFDeriv ℝ j (radFn chi) ((Real.sqrt μ)⁻¹ • z)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb _) hρ

/-! ### Weighted jets of cut-offs -/

variable {α a : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}

/-- A function with bounded derivatives has weighted jets of weight zero on a
bounded scale. -/
theorem WJ_of_global {S B : ℝ} {n : ℕ} {χ : V → ℝ} (hs : ∀ p ∈ Ω, 0 < s p)
    (hS : ∀ p ∈ Ω, s p ≤ S) (hS1 : 1 ≤ S) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hχ : ContDiff ℝ (n + 1 : ℕ) χ)
    (hb : ∀ j : ℕ, j ≤ n + 1 → ∀ z : V, ‖iteratedFDeriv ℝ j χ z‖ ≤ B) :
    WJ α a s Ω 0 (2 * (B * S ^ (n + 1))) n (fun _ => χ) := by
  have hS0 : 0 < S := by linarith
  refine WJ.of_bounds hs (by positivity) ha0 ha1 hα hα1 hχ fun p hp z _ j hj => ?_
  have hsp := hs p hp
  have h1 : S ^ (-(j : ℝ)) ≤ s p ^ (-(j : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hsp (hS p hp) (by simp)
  have h2 : (1 : ℝ) ≤ S ^ (n + 1) * S ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hS0.le, Real.rpow_natCast, le_mul_inv_iff₀ (pow_pos hS0 j), one_mul]
    exact pow_le_pow_right₀ hS1 hj
  calc ‖iteratedFDeriv ℝ j χ z‖ ≤ B := hb j hj z
    _ = B * 1 := (mul_one B).symm
    _ ≤ B * (S ^ (n + 1) * S ^ (-(j : ℝ))) := mul_le_mul_of_nonneg_left h2 hB
    _ ≤ B * (S ^ (n + 1) * s p ^ (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hB
    _ = B * S ^ (n + 1) * s p ^ (-(j : ℝ)) := by ring

/-- **The cut-off at the scale `μ` has weighted jets of weight zero** on a
scale that is at most `K √μ` near the transition region. The constant does not
depend on `μ`. -/
theorem WJ_chiV (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (α a K μ : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)),
    0 < μ → 1 ≤ K → (∀ p ∈ Ω, 0 < s p) → 0 ≤ a → a ≤ 1 → 0 ≤ α → α ≤ 1 →
    (∀ p ∈ Ω, ∀ z : V, ‖z - p.1‖ ≤ a * s p → μ ≤ ‖z‖ ^ 2 → ‖z‖ ^ 2 ≤ 2 * μ →
      s p ≤ K * Real.sqrt μ) →
    WJ α a s Ω 0 (2 * (B * K ^ (n + 1))) n (fun _ => chiV (V := V) μ) := by
  choose B hB hb using norm_iteratedFDeriv_chiV_le (V := V)
  refine ⟨∑ j ∈ Finset.range (n + 2), B j, Finset.sum_nonneg fun j _ => hB j, ?_⟩
  intro α a K μ s Ω hμ hK hs ha0 ha1 hα hα1 hcomp
  have hBtot : 0 ≤ ∑ j ∈ Finset.range (n + 2), B j := Finset.sum_nonneg fun j _ => hB j
  have hK0 : 0 < K := by linarith
  have hsq : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  refine WJ.of_bounds hs (by positivity) ha0 ha1 hα hα1
    ((contDiff_infty.1 (contDiff_chiV μ)) (n + 1)) fun p hp z hz j hj => ?_
  have hsp := hs p hp
  have hBj : B j ≤ ∑ i ∈ Finset.range (n + 2), B i :=
    Finset.single_le_sum (f := B) (fun i _ => hB i) (Finset.mem_range.2 (by omega))
  have hKj : K ^ j ≤ K ^ (n + 1) := pow_le_pow_right₀ hK hj
  have hpow : s p ^ (-(j : ℝ)) = (s p)⁻¹ ^ j := by
    rw [Real.rpow_neg hsp.le, Real.rpow_natCast, inv_pow]
  have hRHS : 0 ≤ (∑ i ∈ Finset.range (n + 2), B i) * K ^ (n + 1) * s p ^ (-(j : ℝ)) :=
    mul_nonneg (mul_nonneg hBtot (by positivity)) (Real.rpow_nonneg hsp.le _)
  by_cases hreg : μ ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 2 * μ
  · have hle := hcomp p hp z hz hreg.1 hreg.2
    -- `(√μ)⁻¹ ≤ K (s p)⁻¹`
    have h1 : (Real.sqrt μ)⁻¹ ≤ K * (s p)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hsq]
      have h2 : s p * (s p)⁻¹ = 1 := mul_inv_cancel₀ hsp.ne'
      have h3 : 0 ≤ (s p)⁻¹ := inv_nonneg.2 hsp.le
      calc (1 : ℝ) = s p * (s p)⁻¹ := h2.symm
        _ ≤ K * Real.sqrt μ * (s p)⁻¹ := mul_le_mul_of_nonneg_right hle h3
        _ = K * (s p)⁻¹ * Real.sqrt μ := by ring
    have h4 : (Real.sqrt μ)⁻¹ ^ j ≤ K ^ j * (s p)⁻¹ ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (inv_nonneg.2 hsq.le) h1 j
    have h5 : 0 ≤ (s p)⁻¹ ^ j := pow_nonneg (inv_nonneg.2 hsp.le) j
    calc ‖iteratedFDeriv ℝ j (chiV (V := V) μ) z‖ ≤ B j * (Real.sqrt μ)⁻¹ ^ j := hb j μ hμ z
      _ ≤ B j * (K ^ j * (s p)⁻¹ ^ j) := mul_le_mul_of_nonneg_left h4 (hB j)
      _ ≤ (∑ i ∈ Finset.range (n + 2), B i) * (K ^ (n + 1) * (s p)⁻¹ ^ j) :=
        mul_le_mul hBj (mul_le_mul_of_nonneg_right hKj h5) (by positivity) hBtot
      _ = (∑ i ∈ Finset.range (n + 2), B i) * K ^ (n + 1) * s p ^ (-(j : ℝ)) := by
        rw [hpow]
        ring
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have h1 := hb 0 μ hμ z
      rw [pow_zero, mul_one] at h1
      have h2 : (1 : ℝ) ≤ K ^ (n + 1) := one_le_pow₀ hK
      calc ‖iteratedFDeriv ℝ 0 (chiV (V := V) μ) z‖ ≤ B 0 := h1
        _ ≤ ∑ i ∈ Finset.range (n + 2), B i := hBj
        _ = (∑ i ∈ Finset.range (n + 2), B i) * 1 * 1 := by ring
        _ ≤ (∑ i ∈ Finset.range (n + 2), B i) * K ^ (n + 1) * s p ^ (-((0 : ℕ) : ℝ)) := by
          rw [Nat.cast_zero, neg_zero, Real.rpow_zero]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hBtot) zero_le_one
    · have hz' : ‖z‖ ^ 2 < μ ∨ 2 * μ < ‖z‖ ^ 2 := by
        by_contra hcon
        rw [not_or, not_lt, not_lt] at hcon
        exact hreg hcon
      rw [iteratedFDeriv_chiV_eq_zero hμ hz' h0.ne', norm_zero]
      exact hRHS

end Calabi.Weighted
