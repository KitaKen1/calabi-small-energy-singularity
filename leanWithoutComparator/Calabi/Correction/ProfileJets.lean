import Calabi.Flat.ProfileDecay
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Decay of all derivatives of the profile

For a profile `G` as in Theorem 3.1, `H(u) = G(u^{-1/2})` is smooth up to
`u = 0`. This file derives from it the decay of all derivatives of `G` and of
`h(y) = (G(y) - 1)/y` at infinity:

* `hfun_jet_decay`: `|h^{(k)}(y)| ≤ C / (1 + y)^{k + 1}` for `y ≥ 0`;
* `profile_jet_decay`: `|G^{(k + 1)}(y)| ≤ C / (1 + y)^{k + 3}` for `y ≥ 0`.

These are the bounds behind the scaled estimates of Lemma 6.2 of the
manuscript for the self-similar solution `F = ρ⁻¹ h(x/ρ)`: its `x`-derivative
of order `k` is `O((x + ρ)^{-1-k})`, and the time derivative of that is
`ρ^{-3-k} G^{(k+1)}(x/ρ) / 2 = O((x + ρ)^{-3-k})`.

The proof uses the class `InvClass H I M` of finite combinations of the
functions `y ↦ y^{-m} H^{(i)}(y^{-2})` with `m ≥ M` and `i ≥ I`, which is
stable under differentiation with `M` raised by one (`InvClass.deriv`) and
whose members are `O(y^{-M})` at infinity (`InvClass.bound`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Flat

variable {c : ℝ} {G : ℝ → ℝ}

/-! ### Derivatives within the half-line -/

/-- The iterated derivatives of a function within `[0, ∞)`. -/
noncomputable def halfDeriv (H : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => H
  | i + 1 => derivWithin (halfDeriv H i) (Ici 0)

theorem contDiffOn_halfDeriv {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) :
    ∀ i : ℕ, ContDiffOn ℝ ∞ (halfDeriv H i) (Ici 0)
  | 0 => hH
  | i + 1 => (contDiffOn_halfDeriv hH i).derivWithin (uniqueDiffOn_Ici 0) (by simp)

theorem hasDerivAt_halfDeriv {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) (i : ℕ) {u : ℝ}
    (hu : 0 < u) : HasDerivAt (halfDeriv H i) (halfDeriv H (i + 1) u) u := by
  have hd : DifferentiableWithinAt ℝ (halfDeriv H i) (Ici 0) u :=
    (contDiffOn_halfDeriv hH i).differentiableOn (by simp) u (le_of_lt hu)
  have h1 := (hd.differentiableAt (Ici_mem_nhds hu)).hasDerivAt
  have e : halfDeriv H (i + 1) u = deriv (halfDeriv H i) u :=
    derivWithin_of_mem_nhds (Ici_mem_nhds hu)
  rw [e]
  exact h1

/-! ### Inverse powers -/

theorem zpow_neg_two (y : ℝ) : y ^ (-2 : ℤ) = (y ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_ofNat]

theorem hasDerivAt_zpow_neg (m : ℕ) {y : ℝ} (hy0 : y ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ (-(m : ℤ))) (-(m : ℝ) * y ^ (-((m + 1 : ℕ) : ℤ))) y := by
  have h := hasDerivAt_zpow (-(m : ℤ)) y (Or.inl hy0)
  have e1 : (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have e0 : ((-(m : ℤ) : ℤ) : ℝ) = -(m : ℝ) := by
    push_cast
    rfl
  rw [e1, e0] at h
  exact h

theorem hasDerivAt_zpow_neg_two {y : ℝ} (hy0 : y ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ (-2 : ℤ)) (-2 * y ^ (-3 : ℤ)) y := by
  have h := hasDerivAt_zpow (-2 : ℤ) y (Or.inl hy0)
  have e1 : ((-2 : ℤ) - 1) = (-3 : ℤ) := by norm_num
  have e0 : (((-2 : ℤ) : ℤ) : ℝ) = (-2 : ℝ) := by norm_num
  rw [e1, e0] at h
  exact h

/-- The derivative of a generator `y ↦ y^{-m} H^{(i)}(y^{-2})`. -/
theorem hasDerivAt_gen {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) (m i : ℕ) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => y ^ (-(m : ℤ)) * halfDeriv H i (y ^ (-2 : ℤ)))
      (-(m : ℝ) * (y ^ (-((m + 1 : ℕ) : ℤ)) * halfDeriv H i (y ^ (-2 : ℤ)))
        + (-2) * (y ^ (-((m + 3 : ℕ) : ℤ)) * halfDeriv H (i + 1) (y ^ (-2 : ℤ)))) y := by
  have hy0 : y ≠ 0 := hy.ne'
  have hu : 0 < y ^ (-2 : ℤ) := zpow_pos hy _
  have hB := hasDerivAt_zpow_neg_two hy0
  have hKB : HasDerivAt (fun y : ℝ => halfDeriv H i (y ^ (-2 : ℤ)))
      (halfDeriv H (i + 1) (y ^ (-2 : ℤ)) * (-2 * y ^ (-3 : ℤ))) y :=
    (hasDerivAt_halfDeriv hH i hu).comp y hB
  have h := (hasDerivAt_zpow_neg m hy0).fun_mul hKB
  have e2 : y ^ (-(m : ℤ)) * y ^ (-3 : ℤ) = y ^ (-((m + 3 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hy0]
    congr 1
    push_cast
    ring
  refine h.congr_deriv ?_
  rw [← e2]
  ring

/-! ### The class of inverse-power combinations -/

/-- Finite combinations of the functions `y ↦ y^{-m} H^{(i)}(y^{-2})` with
`m ≥ M` and `i ≥ I`. -/
inductive InvClass (H : ℝ → ℝ) (I M : ℕ) : (ℝ → ℝ) → Prop
  | gen (m i : ℕ) (hm : M ≤ m) (hi : I ≤ i) :
      InvClass H I M (fun y => y ^ (-(m : ℤ)) * halfDeriv H i (y ^ (-2 : ℤ)))
  | zero : InvClass H I M (fun _ => 0)
  | add {φ ψ : ℝ → ℝ} : InvClass H I M φ → InvClass H I M ψ →
      InvClass H I M (fun y => φ y + ψ y)
  | smul (a : ℝ) {φ : ℝ → ℝ} : InvClass H I M φ → InvClass H I M (fun y => a * φ y)

/-- The class is stable under differentiation, with the order of decay raised
by one. -/
theorem InvClass.deriv {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) {I M : ℕ} {φ : ℝ → ℝ}
    (h : InvClass H I M φ) :
    ∃ ψ : ℝ → ℝ, InvClass H I (M + 1) ψ ∧ ∀ y : ℝ, 0 < y → HasDerivAt φ (ψ y) y := by
  induction h with
  | gen m i hm hi =>
    refine ⟨fun y => -(m : ℝ) * (y ^ (-((m + 1 : ℕ) : ℤ)) * halfDeriv H i (y ^ (-2 : ℤ)))
      + (-2) * (y ^ (-((m + 3 : ℕ) : ℤ)) * halfDeriv H (i + 1) (y ^ (-2 : ℤ))), ?_, ?_⟩
    · exact InvClass.add (InvClass.smul _ (InvClass.gen (m + 1) i (by omega) hi))
        (InvClass.smul _ (InvClass.gen (m + 3) (i + 1) (by omega) (by omega)))
    · intro y hy
      exact hasDerivAt_gen hH m i hy
  | zero => exact ⟨fun _ => 0, InvClass.zero, fun y _ => hasDerivAt_const y 0⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨ψ1, c1, d1⟩ := ih1
    obtain ⟨ψ2, c2, d2⟩ := ih2
    exact ⟨fun y => ψ1 y + ψ2 y, c1.add c2, fun y hy => (d1 y hy).fun_add (d2 y hy)⟩
  | smul a _ ih =>
    obtain ⟨ψ, c1, d1⟩ := ih
    exact ⟨fun y => a * ψ y, c1.smul a, fun y hy => (d1 y hy).const_mul a⟩

/-- The members of the class are `O(y^{-M})` at infinity. -/
theorem InvClass.bound {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) {I M : ℕ} {φ : ℝ → ℝ}
    (h : InvClass H I M φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |φ y| ≤ C * y ^ (-(M : ℤ)) := by
  induction h with
  | gen m i hm hi =>
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      ((contDiffOn_halfDeriv hH i).continuousOn.mono Icc_subset_Ici_self)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
    refine ⟨B, hB0, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have hu0 : 0 < y ^ (-2 : ℤ) := zpow_pos hy0 _
    have hu1 : y ^ (-2 : ℤ) ≤ 1 := by
      have h := zpow_le_zpow_right₀ hy (by norm_num : (-2 : ℤ) ≤ 0)
      rwa [zpow_zero] at h
    have hK : |halfDeriv H i (y ^ (-2 : ℤ))| ≤ B := by
      have h := hB _ ⟨hu0.le, hu1⟩
      rwa [Real.norm_eq_abs] at h
    have hm0 : 0 < y ^ (-(m : ℤ)) := zpow_pos hy0 _
    have hmM : y ^ (-(m : ℤ)) ≤ y ^ (-(M : ℤ)) :=
      zpow_le_zpow_right₀ hy (neg_le_neg (by exact_mod_cast hm))
    rw [abs_mul, abs_of_pos hm0]
    calc y ^ (-(m : ℤ)) * |halfDeriv H i (y ^ (-2 : ℤ))|
        ≤ y ^ (-(M : ℤ)) * B := mul_le_mul hmM hK (abs_nonneg _) (hm0.le.trans hmM)
      _ = B * y ^ (-(M : ℤ)) := mul_comm _ _
  | zero => exact ⟨0, le_rfl, fun y _ => by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨C1, hC1, b1⟩ := ih1
    obtain ⟨C2, hC2, b2⟩ := ih2
    refine ⟨C1 + C2, add_nonneg hC1 hC2, fun y hy => ?_⟩
    calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ C1 * y ^ (-(M : ℤ)) + C2 * y ^ (-(M : ℤ)) := add_le_add (b1 y hy) (b2 y hy)
      _ = (C1 + C2) * y ^ (-(M : ℤ)) := by ring
  | smul a _ ih =>
    obtain ⟨C, hC, b⟩ := ih
    refine ⟨|a| * C, mul_nonneg (abs_nonneg _) hC, fun y hy => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b y hy) (abs_nonneg _)

/-- All derivatives of a function that agrees with a member of the class on
`(0, ∞)`. -/
theorem iteratedDeriv_invClass {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) {I M : ℕ}
    {f φ : ℝ → ℝ} (hφ : InvClass H I M φ) (hf : ∀ y : ℝ, 0 < y → f y = φ y) :
    ∀ k : ℕ, ∃ ψ : ℝ → ℝ, InvClass H I (M + k) ψ ∧ ∀ y : ℝ, 0 < y → iteratedDeriv k f y = ψ y
  | 0 => ⟨φ, hφ, fun y hy => by
      rw [iteratedDeriv_zero]
      exact hf y hy⟩
  | k + 1 => by
    obtain ⟨ψ, hψ, he⟩ := iteratedDeriv_invClass hH hφ hf k
    obtain ⟨χ, hχ, hd⟩ := hψ.deriv hH
    refine ⟨χ, hχ, fun y hy => ?_⟩
    have hev : iteratedDeriv k f =ᶠ[𝓝 y] ψ := by
      filter_upwards [Ioi_mem_nhds hy] with z hz using he z hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hd y hy).deriv

/-- Decay at infinity and continuity on `[0, 1]` give a bound on `[0, ∞)`. -/
theorem decay_of_invClass {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Ici 0)) {I M : ℕ}
    {f φ : ℝ → ℝ} (hφ : InvClass H I M φ) (hf : ∀ y : ℝ, 0 < y → f y = φ y) (k : ℕ)
    (hc : ContinuousOn (iteratedDeriv k f) (Icc 0 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y → |iteratedDeriv k f y| ≤ C / (1 + y) ^ (M + k) := by
  obtain ⟨ψ, hψ, he⟩ := iteratedDeriv_invClass hH hφ hf k
  obtain ⟨C, hC, hb⟩ := hψ.bound hH
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨(C + B) * 2 ^ (M + k), mul_nonneg (add_nonneg hC hB0) (by positivity), fun y hy => ?_⟩
  have h1y : 0 < 1 + y := by linarith
  have hpow : 0 < (1 + y) ^ (M + k) := pow_pos h1y _
  rw [le_div_iff₀ hpow]
  rcases le_total y 1 with h | h
  · have h1 : |iteratedDeriv k f y| ≤ B := by
      have := hB y ⟨hy, h⟩
      rwa [Real.norm_eq_abs] at this
    have h2 : (1 + y) ^ (M + k) ≤ 2 ^ (M + k) := pow_le_pow_left₀ h1y.le (by linarith) _
    calc |iteratedDeriv k f y| * (1 + y) ^ (M + k) ≤ B * 2 ^ (M + k) :=
          mul_le_mul h1 h2 hpow.le hB0
      _ ≤ (C + B) * 2 ^ (M + k) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hy0 : 0 < y := by linarith
    have h1 : |iteratedDeriv k f y| ≤ C * y ^ (-((M + k : ℕ) : ℤ)) := by
      rw [he y hy0]
      exact hb y h
    have e : y ^ (-((M + k : ℕ) : ℤ)) = (y ^ (M + k))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [e] at h1
    have hyk : 0 < y ^ (M + k) := pow_pos hy0 _
    have h2 : (1 + y) ^ (M + k) ≤ 2 ^ (M + k) * y ^ (M + k) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h1y.le (by linarith) _
    calc |iteratedDeriv k f y| * (1 + y) ^ (M + k)
        ≤ C * (y ^ (M + k))⁻¹ * (2 ^ (M + k) * y ^ (M + k)) :=
          mul_le_mul h1 h2 hpow.le (mul_nonneg hC (inv_nonneg.2 hyk.le))
      _ = C * 2 ^ (M + k) * ((y ^ (M + k))⁻¹ * y ^ (M + k)) := by ring
      _ = C * 2 ^ (M + k) := by rw [inv_mul_cancel₀ hyk.ne', mul_one]
      _ ≤ (C + B) * 2 ^ (M + k) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-! ### The profile -/

/-- **Decay of all derivatives of `h`**: `|h^{(k)}(y)| ≤ C / (1 + y)^{k + 1}`. -/
theorem hfun_jet_decay (hP : IsProfile c G) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      |iteratedDeriv k (hfun G) y| ≤ C / (1 + y) ^ (1 + k) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  obtain ⟨H, hH, hGH⟩ := profile_eq_compact hP
  have hH1 : ContDiffOn ℝ ∞ (fun u => H u - 1) (Ici 0) := hH.sub contDiffOn_const
  have hh := contDiffOn_hfun hδ hsm
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioi (-δ) := fun y hy => mem_Ioi.2 (by linarith [hy.1])
  refine decay_of_invClass hH1 (InvClass.gen (I := 0) (M := 1) 1 0 le_rfl le_rfl)
    (fun y hy => ?_) k ((contDiffOn_iteratedDeriv isOpen_Ioi hh k).continuousOn.mono hsub)
  have h1 := mul_hfun hP y
  rw [hGH y hy] at h1
  have hy0 : y ≠ 0 := hy.ne'
  show hfun G y = y ^ (-((1 : ℕ) : ℤ)) * (H (y ^ (-2 : ℤ)) - 1)
  rw [zpow_neg_two, zpow_neg, zpow_natCast, pow_one, ← h1]
  field_simp

/-- **Decay of all derivatives of `G`**:
`|G^{(k + 1)}(y)| ≤ C / (1 + y)^{k + 3}`. -/
theorem profile_jet_decay (hP : IsProfile c G) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      |iteratedDeriv (k + 1) G y| ≤ C / (1 + y) ^ (3 + k) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  obtain ⟨H, hH, hGH⟩ := profile_eq_compact hP
  have hH1 : ContDiffOn ℝ ∞ (fun u => H u - 1) (Ici 0) := hH.sub contDiffOn_const
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioi (-δ) := fun y hy => mem_Ioi.2 (by linarith [hy.1])
  have hd1 : ContDiffOn ℝ ∞ (deriv G) (Ioi (-δ)) := by
    have h := contDiffOn_iteratedDeriv isOpen_Ioi hsm 1
    rwa [iteratedDeriv_one] at h
  have hgen : InvClass (fun u => H u - 1) 1 3
      (fun y => (-2 : ℝ) * (y ^ (-((3 : ℕ) : ℤ)) * halfDeriv (fun u => H u - 1) 1 (y ^ (-2 : ℤ)))) :=
    InvClass.smul _ (InvClass.gen 3 1 le_rfl le_rfl)
  have hfe : ∀ y : ℝ, 0 < y → deriv G y
      = (-2 : ℝ) * (y ^ (-((3 : ℕ) : ℤ)) * halfDeriv (fun u => H u - 1) 1 (y ^ (-2 : ℤ))) := by
    intro y hy
    have hy0 : y ≠ 0 := hy.ne'
    have hu : 0 < y ^ (-2 : ℤ) := zpow_pos hy _
    have hK : HasDerivAt (fun u => H u - 1)
        (halfDeriv (fun u => H u - 1) 1 (y ^ (-2 : ℤ))) (y ^ (-2 : ℤ)) :=
      hasDerivAt_halfDeriv hH1 0 hu
    have hcomp := hK.comp y (hasDerivAt_zpow_neg_two hy0)
    have hG : HasDerivAt (fun y : ℝ => G y - 1)
        (halfDeriv (fun u => H u - 1) 1 (y ^ (-2 : ℤ)) * (-2 * y ^ (-3 : ℤ))) y := by
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hy] with z hz
      show G z - 1 = H (z ^ (-2 : ℤ)) - 1
      rw [hGH z hz, zpow_neg_two]
    have hG' : HasDerivAt G
        (halfDeriv (fun u => H u - 1) 1 (y ^ (-2 : ℤ)) * (-2 * y ^ (-3 : ℤ))) y := by
      have h := hG.add_const 1
      simpa using h
    rw [hG'.deriv]
    have e3 : (-3 : ℤ) = -((3 : ℕ) : ℤ) := by norm_num
    rw [e3]
    ring
  have h := decay_of_invClass hH1 hgen hfe k
    (by
      have hc := (contDiffOn_iteratedDeriv isOpen_Ioi hd1 k).continuousOn.mono hsub
      exact hc)
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun y hy => ?_⟩
  have := hb y hy
  rwa [← iteratedDeriv_succ'] at this

end Calabi.Flat
