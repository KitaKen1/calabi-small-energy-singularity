import Calabi.Correction.WindowConvert
import Calabi.Correction.Extension
import OAI.Analysis.AncientFlat.Weighted.ExactXNorm

/-!
# Further operations on weighted two-point bounds

* `WH.comp_map`: composition with a map that is Lipschitz for the parabolic
  distance and compares the scales (evaluation along a ray, change of chart,
  translation or clamping of the time);
* `WH.interp`: a function with a two-point bound of exponent `α′` and small
  values has a small two-point bound of every exponent `α < α′`. This gives
  the smallness of the fourth derivatives in Lemma 4.5 of the manuscript and
  the smallness of the difference between the coefficients and their values
  at the singular time;
* `WH.weight_supp`, `WH.scale_supp`: lowering the weight and changing the
  scale for a function that vanishes where the scale is large, respectively
  where the two scales are not comparable;
* `xBound_of_xNorm_le`: the jets are bounded by their components in an
  orthonormal basis, so that the exact norm of the reused inverse gives the
  bound `XBound`;
* `ancExt`, `ancExt_WH`: the extension (6.8) of a source on `[-T, 0)` to all
  negative times. It is the value at the time clamped to `[-T, 0)` times a
  ramp in `σ(z, t) / σ(z, -T)`.
-/

open Set
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
variable {E : Type*} [NormedAddCommGroup E]
variable {α a c w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}

theorem pdist_comm (p q : V × ℝ) : pdist p q = pdist q p := by
  unfold pdist
  rw [norm_sub_rev, abs_sub_comm]

/-! ### Composition with a map -/

/-- **Composition with a map** that is Lipschitz for the parabolic distance and
compares the scales. -/
theorem WH.comp_map {k L : ℝ} {s' : V' × ℝ → ℝ} {Ω' : Set (V' × ℝ)} {Φ : V' × ℝ → V × ℝ}
    {f : V × ℝ → E} (hf : WH α a s Ω w M f) (hM : 0 ≤ M) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hΦ : ∀ p ∈ Ω', Φ p ∈ Ω) (hs : ∀ p ∈ Ω, 0 < s p)
    (hs' : ∀ p ∈ Ω', 0 < s' p) (h1 : ∀ p ∈ Ω', s (Φ p) ≤ k * s' p)
    (h2 : ∀ p ∈ Ω', s' p ≤ k * s (Φ p))
    (hd : ∀ p ∈ Ω', ∀ q ∈ Ω', pdist (Φ p) (Φ q) ≤ L * pdist p q) :
    WH α (a / (k * L)) s' Ω' w (M * k ^ (|w| + |w - α|) * L ^ α) (fun p => f (Φ p)) := by
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < L := by linarith
  have hkne : k ≠ 0 := hk0.ne'
  have hLne : L ≠ 0 := hL0.ne'
  have hkw : k ^ |w| ≤ k ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hk (le_add_of_nonneg_right (abs_nonneg _))
  have hkα : k ^ |w - α| ≤ k ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hk (le_add_of_nonneg_left (abs_nonneg _))
  have hLα : 1 ≤ L ^ α := Real.one_le_rpow hL hα
  have hK0 : 0 ≤ k ^ (|w| + |w - α|) := Real.rpow_nonneg hk0.le _
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
  · have h3 := rpow_le_of_comparable (hs _ (hΦ p hp)) (hs' p hp) hk (h1 p hp) (h2 p hp) w
    have h4 : 0 ≤ s' p ^ w := Real.rpow_nonneg (hs' p hp).le _
    calc ‖f (Φ p)‖ ≤ M * s (Φ p) ^ w := hf.1 _ (hΦ p hp)
      _ ≤ M * (k ^ |w| * s' p ^ w) := mul_le_mul_of_nonneg_left h3 hM
      _ ≤ M * (k ^ (|w| + |w - α|) * s' p ^ w) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkw h4) hM
      _ = M * k ^ (|w| + |w - α|) * 1 * s' p ^ w := by ring
      _ ≤ M * k ^ (|w| + |w - α|) * L ^ α * s' p ^ w :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLα (mul_nonneg hM hK0)) h4
  · have hd0 := pdist_nonneg p q
    have e : L * (a / (k * L) * s' p) = a / k * s' p := by
      field_simp
    have hd' : pdist (Φ p) (Φ q) ≤ a * s (Φ p) := by
      calc pdist (Φ p) (Φ q) ≤ L * pdist p q := hd p hp q hq
        _ ≤ L * (a / (k * L) * s' p) := mul_le_mul_of_nonneg_left hpq hL0.le
        _ = a / k * s' p := e
        _ ≤ a / k * (k * s (Φ p)) :=
          mul_le_mul_of_nonneg_left (h2 p hp) (div_nonneg ha hk0.le)
        _ = a * s (Φ p) := by rw [← mul_assoc, div_mul_cancel₀ a hkne]
    have h3 := rpow_le_of_comparable (hs _ (hΦ p hp)) (hs' p hp) hk (h1 p hp) (h2 p hp) (w - α)
    have h4 : 0 ≤ s' p ^ (w - α) := Real.rpow_nonneg (hs' p hp).le _
    have h6 : pdist (Φ p) (Φ q) ^ α ≤ L ^ α * pdist p q ^ α := by
      rw [← Real.mul_rpow hL0.le hd0]
      exact Real.rpow_le_rpow (pdist_nonneg _ _) (hd p hp q hq) hα
    calc ‖f (Φ p) - f (Φ q)‖ ≤ M * s (Φ p) ^ (w - α) * pdist (Φ p) (Φ q) ^ α :=
          hf.2 _ (hΦ p hp) _ (hΦ q hq) hd'
      _ ≤ M * (k ^ (|w| + |w - α|) * s' p ^ (w - α)) * (L ^ α * pdist p q ^ α) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right hkα h4)) hM)
          h6 (Real.rpow_nonneg (pdist_nonneg _ _) _) (mul_nonneg hM (mul_nonneg hK0 h4))
      _ = M * k ^ (|w| + |w - α|) * L ^ α * s' p ^ (w - α) * pdist p q ^ α := by ring

/-- A continuous linear map of norm at most one. -/
theorem WH.clm_le [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : V × ℝ → E} (hf : WH α a s Ω w M f) (hM : 0 ≤ M)
    (hs : ∀ p ∈ Ω, 0 < s p) : WH α a s Ω w M (fun p => L (f p)) :=
  (hf.clm L).mono hs (mul_le_of_le_one_left hM hL)

/-! ### Interpolation -/

theorem interp_aux {x A B lam : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) (hB : x ≤ B) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) : x ≤ A ^ lam * B ^ (1 - lam) := by
  have e1 : lam + (1 - lam) = 1 := by ring
  have e2 : lam + (1 - lam) ≠ 0 := by rw [e1]; exact one_ne_zero
  have e : x ^ lam * x ^ (1 - lam) = x := by
    rw [← Real.rpow_add' hx e2, e1, Real.rpow_one]
  calc x = x ^ lam * x ^ (1 - lam) := e.symm
    _ ≤ A ^ lam * B ^ (1 - lam) :=
      mul_le_mul (Real.rpow_le_rpow hx hA h0) (Real.rpow_le_rpow hx hB (by linarith))
        (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hA) _)

/-- **Interpolation**: a function with a two-point bound of exponent `α'` whose
values are small has a small two-point bound of every smaller exponent. -/
theorem WH.interp {α' θ : ℝ} {f : V × ℝ → E} (hf : WH α' a s Ω w M f) (hsc : IsScale a c s Ω)
    (hM : 0 ≤ M) (hα : 0 < α) (hαα : α ≤ α') (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsup : ∀ p ∈ Ω, ‖f p‖ ≤ θ * (M * s p ^ w)) :
    WH α a s Ω w ((1 + c ^ |w|) * θ ^ (1 - α / α') * M) f := by
  have hα' : 0 < α' := hα.trans_le hαα
  have hlam0 : 0 ≤ α / α' := (div_pos hα hα').le
  have hlam1 : α / α' ≤ 1 := (div_le_one hα').2 hαα
  have hc1 := hsc.one_le
  have hcw : 0 ≤ c ^ |w| := Real.rpow_nonneg (by linarith) _
  have hK1 : 1 ≤ 1 + c ^ |w| := by linarith
  have hθμ : 0 ≤ θ ^ (1 - α / α') := Real.rpow_nonneg hθ _
  have hθle : θ ≤ θ ^ (1 - α / α') := by
    rcases hθ.eq_or_lt with h | h
    · rw [← h]
      exact Real.rpow_nonneg le_rfl _
    · calc θ = θ ^ (1 : ℝ) := (Real.rpow_one θ).symm
        _ ≤ θ ^ (1 - α / α') := Real.rpow_le_rpow_of_exponent_ge h hθ1 (by linarith)
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hsc.pos p hp
    have hX : 0 ≤ M * s p ^ w := mul_nonneg hM (Real.rpow_nonneg hsp.le _)
    calc ‖f p‖ ≤ θ * (M * s p ^ w) := hsup p hp
      _ ≤ θ ^ (1 - α / α') * (M * s p ^ w) := mul_le_mul_of_nonneg_right hθle hX
      _ = 1 * θ ^ (1 - α / α') * (M * s p ^ w) := by ring
      _ ≤ (1 + c ^ |w|) * θ ^ (1 - α / α') * (M * s p ^ w) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hθμ) hX
      _ = (1 + c ^ |w|) * θ ^ (1 - α / α') * M * s p ^ w := by ring
  · have hsp := hsc.pos p hp
    have hd0 := pdist_nonneg p q
    have hX : 0 ≤ M * s p ^ w := mul_nonneg hM (Real.rpow_nonneg hsp.le _)
    have hA : ‖f p - f q‖ ≤ M * s p ^ w * (s p ^ (-α') * pdist p q ^ α') := by
      have h := hf.2 p hp q hq hd
      have e : s p ^ (w - α') = s p ^ w * s p ^ (-α') := by
        rw [← Real.rpow_add hsp, sub_eq_add_neg]
      rw [e] at h
      calc ‖f p - f q‖ ≤ M * (s p ^ w * s p ^ (-α')) * pdist p q ^ α' := h
        _ = M * s p ^ w * (s p ^ (-α') * pdist p q ^ α') := by ring
    have hB : ‖f p - f q‖ ≤ (1 + c ^ |w|) * θ * (M * s p ^ w) := by
      have hq' : ‖f q‖ ≤ θ * (M * (c ^ |w| * s p ^ w)) :=
        (hsup q hq).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hsc.rpow_le hp hq hd w) hM) hθ)
      calc ‖f p - f q‖ ≤ ‖f p‖ + ‖f q‖ := norm_sub_le _ _
        _ ≤ θ * (M * s p ^ w) + θ * (M * (c ^ |w| * s p ^ w)) := add_le_add (hsup p hp) hq'
        _ = (1 + c ^ |w|) * θ * (M * s p ^ w) := by ring
    have hY : 0 ≤ s p ^ (-α') * pdist p q ^ α' :=
      mul_nonneg (Real.rpow_nonneg hsp.le _) (Real.rpow_nonneg hd0 _)
    have h := interp_aux (norm_nonneg _) hA hB hlam0 hlam1
    have e4 : α' * (α / α') = α := mul_div_cancel₀ α hα'.ne'
    have e3 : -α' * (α / α') = -α := by rw [neg_mul, e4]
    have e1 : (M * s p ^ w * (s p ^ (-α') * pdist p q ^ α')) ^ (α / α')
        = (M * s p ^ w) ^ (α / α') * (s p ^ (-α) * pdist p q ^ α) := by
      rw [Real.mul_rpow hX hY,
        Real.mul_rpow (Real.rpow_nonneg hsp.le _) (Real.rpow_nonneg hd0 _),
        ← Real.rpow_mul hsp.le, ← Real.rpow_mul hd0, e3, e4]
    have e2 : ((1 + c ^ |w|) * θ * (M * s p ^ w)) ^ (1 - α / α')
        = ((1 + c ^ |w|) * θ) ^ (1 - α / α') * (M * s p ^ w) ^ (1 - α / α') :=
      Real.mul_rpow (mul_nonneg (by linarith) hθ) hX
    have e5 : (M * s p ^ w) ^ (α / α') * (M * s p ^ w) ^ (1 - α / α') = M * s p ^ w := by
      have e6 : α / α' + (1 - α / α') = 1 := by ring
      have e7 : α / α' + (1 - α / α') ≠ 0 := by rw [e6]; exact one_ne_zero
      rw [← Real.rpow_add' hX e7, e6, Real.rpow_one]
    have e7 : ((1 + c ^ |w|) * θ) ^ (1 - α / α') ≤ (1 + c ^ |w|) * θ ^ (1 - α / α') := by
      rw [Real.mul_rpow (by linarith) hθ]
      refine mul_le_mul_of_nonneg_right ?_ hθμ
      calc (1 + c ^ |w|) ^ (1 - α / α') ≤ (1 + c ^ |w|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
        _ = 1 + c ^ |w| := Real.rpow_one _
    have e8 : s p ^ (w - α) = s p ^ w * s p ^ (-α) := by
      rw [← Real.rpow_add hsp, sub_eq_add_neg]
    have hZ : 0 ≤ s p ^ (-α) * pdist p q ^ α :=
      mul_nonneg (Real.rpow_nonneg hsp.le _) (Real.rpow_nonneg hd0 _)
    calc ‖f p - f q‖ ≤ (M * s p ^ w * (s p ^ (-α') * pdist p q ^ α')) ^ (α / α')
          * ((1 + c ^ |w|) * θ * (M * s p ^ w)) ^ (1 - α / α') := h
      _ = ((1 + c ^ |w|) * θ) ^ (1 - α / α')
          * ((M * s p ^ w) ^ (α / α') * (M * s p ^ w) ^ (1 - α / α'))
          * (s p ^ (-α) * pdist p q ^ α) := by
        rw [e1, e2]
        ring
      _ = ((1 + c ^ |w|) * θ) ^ (1 - α / α') * (M * s p ^ w)
          * (s p ^ (-α) * pdist p q ^ α) := by rw [e5]
      _ ≤ (1 + c ^ |w|) * θ ^ (1 - α / α') * (M * s p ^ w) * (s p ^ (-α) * pdist p q ^ α) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e7 hX) hZ
      _ = (1 + c ^ |w|) * θ ^ (1 - α / α') * M * s p ^ (w - α) * pdist p q ^ α := by
        rw [e8]
        ring

/-! ### Functions supported where the scale is small or comparable -/

/-- Lowering the weight of a function that vanishes where the scale is larger
than `S₁`. -/
theorem WH.weight_supp {w' S₁ : ℝ} {f : V × ℝ → E} (hf : WH α a s Ω w M f)
    (hsc : IsScale a c s Ω) (hM : 0 ≤ M) (hS₁ : 0 ≤ S₁)
    (hS : ∀ p ∈ Ω, f p ≠ 0 → s p ≤ S₁) (hw : w' ≤ w) :
    WH α a s Ω w' (M * (c * S₁) ^ (w - w')) f := by
  have hc1 := hsc.one_le
  have hcS : 0 ≤ c * S₁ := mul_nonneg (by linarith) hS₁
  have hP : 0 ≤ (c * S₁) ^ (w - w') := Real.rpow_nonneg hcS _
  have key : ∀ p ∈ Ω, s p ≤ c * S₁ → ∀ v : ℝ,
      s p ^ v ≤ (c * S₁) ^ (w - w') * s p ^ (v - (w - w')) := by
    intro p hp hle v
    have hsp := hsc.pos p hp
    have e : s p ^ v = s p ^ (w - w') * s p ^ (v - (w - w')) := by
      rw [← Real.rpow_add hsp]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hsp.le hle (by linarith))
      (Real.rpow_nonneg hsp.le _)
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hsc.pos p hp
    by_cases h0 : f p = 0
    · rw [h0, norm_zero]
      exact mul_nonneg (mul_nonneg hM hP) (Real.rpow_nonneg hsp.le _)
    · have hle : s p ≤ c * S₁ := (hS p hp h0).trans (le_mul_of_one_le_left hS₁ hc1)
      have h1 := key p hp hle w
      have e : w - (w - w') = w' := by ring
      rw [e] at h1
      calc ‖f p‖ ≤ M * s p ^ w := hf.1 p hp
        _ ≤ M * ((c * S₁) ^ (w - w') * s p ^ w') := mul_le_mul_of_nonneg_left h1 hM
        _ = M * (c * S₁) ^ (w - w') * s p ^ w' := by ring
  · have hsp := hsc.pos p hp
    have h5 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
    by_cases h0 : f p = 0 ∧ f q = 0
    · rw [h0.1, h0.2, sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hM hP) (Real.rpow_nonneg hsp.le _)) h5
    · have hle : s p ≤ c * S₁ := by
        by_cases hp0 : f p = 0
        · have hq0 : f q ≠ 0 := fun h => h0 ⟨hp0, h⟩
          exact (hsc.ge p hp q hq hd).trans
            (mul_le_mul_of_nonneg_left (hS q hq hq0) (by linarith))
        · exact (hS p hp hp0).trans (le_mul_of_one_le_left hS₁ hc1)
      have h1 := key p hp hle (w - α)
      have e : w - α - (w - w') = w' - α := by ring
      rw [e] at h1
      calc ‖f p - f q‖ ≤ M * s p ^ (w - α) * pdist p q ^ α := hf.2 p hp q hq hd
        _ ≤ M * ((c * S₁) ^ (w - w') * s p ^ (w' - α)) * pdist p q ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hM) h5
        _ = M * (c * S₁) ^ (w - w') * s p ^ (w' - α) * pdist p q ^ α := by ring

/-- Changing the scale of a function that vanishes where the two scales are
not comparable. -/
theorem WH.scale_supp {s' : V × ℝ → ℝ} {k c' a' : ℝ} {f : V × ℝ → E} (hf : WH α a s Ω w M f)
    (hsc' : IsScale a' c' s' Ω) (hM : 0 ≤ M) (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hs : ∀ p ∈ Ω, 0 < s p)
    (hcomp : ∀ p ∈ Ω, f p ≠ 0 → s p ≤ k * s' p ∧ s' p ≤ k * s p) :
    WH α (min a' (a / (k * c'))) s' Ω w (M * (k * c') ^ (|w| + |w - α|)) f := by
  have hc1 := hsc'.one_le
  have hk0 : 0 < k := by linarith
  have hc0 : 0 < c' := by linarith
  have hK1 : 1 ≤ k * c' := one_le_mul_of_one_le_of_one_le hk hc1
  have hK0 : 0 < k * c' := by linarith
  have hKw : (k * c') ^ |w| ≤ (k * c') ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (le_add_of_nonneg_right (abs_nonneg _))
  have hKα : (k * c') ^ |w - α| ≤ (k * c') ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (le_add_of_nonneg_left (abs_nonneg _))
  have hP : 0 ≤ (k * c') ^ (|w| + |w - α|) := Real.rpow_nonneg hK0.le _
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp' := hsc'.pos p hp
    by_cases h0 : f p = 0
    · rw [h0, norm_zero]
      exact mul_nonneg (mul_nonneg hM hP) (Real.rpow_nonneg hsp'.le _)
    · obtain ⟨c1, c2⟩ := hcomp p hp h0
      have d1 : s p ≤ k * c' * s' p := by
        calc s p ≤ k * s' p := c1
          _ ≤ k * s' p * c' := le_mul_of_one_le_right (mul_nonneg hk0.le hsp'.le) hc1
          _ = k * c' * s' p := by ring
      have d2 : s' p ≤ k * c' * s p := by
        calc s' p ≤ k * s p := c2
          _ ≤ k * s p * c' := le_mul_of_one_le_right (mul_nonneg hk0.le (hs p hp).le) hc1
          _ = k * c' * s p := by ring
      have h3 := rpow_le_of_comparable (hs p hp) hsp' hK1 d1 d2 w
      have h4 : 0 ≤ s' p ^ w := Real.rpow_nonneg hsp'.le _
      calc ‖f p‖ ≤ M * s p ^ w := hf.1 p hp
        _ ≤ M * ((k * c') ^ |w| * s' p ^ w) := mul_le_mul_of_nonneg_left h3 hM
        _ ≤ M * ((k * c') ^ (|w| + |w - α|) * s' p ^ w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKw h4) hM
        _ = M * (k * c') ^ (|w| + |w - α|) * s' p ^ w := by ring
  · have hsp' := hsc'.pos p hp
    have hsq' := hsc'.pos q hq
    have hd0 := pdist_nonneg p q
    have h4 : 0 ≤ s' p ^ (w - α) := Real.rpow_nonneg hsp'.le _
    have h5 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg hd0 _
    have hda : pdist p q ≤ a' * s' p := hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsp'.le)
    have hdb : pdist p q ≤ a / (k * c') * s' p :=
      hd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsp'.le)
    have haK : 0 ≤ a / (k * c') := div_nonneg ha hK0.le
    -- the conclusion from a comparison of `s` at a point with `s'` at `p`
    have fin : ∀ r ∈ Ω, s r ≤ k * c' * s' p → s' p ≤ k * c' * s r →
        ‖f p - f q‖ ≤ M * s r ^ (w - α) * pdist p q ^ α →
        ‖f p - f q‖ ≤ M * (k * c') ^ (|w| + |w - α|) * s' p ^ (w - α) * pdist p q ^ α := by
      intro r hr d1 d2 hb
      have h3 := rpow_le_of_comparable (hs r hr) hsp' hK1 d1 d2 (w - α)
      calc ‖f p - f q‖ ≤ M * s r ^ (w - α) * pdist p q ^ α := hb
        _ ≤ M * ((k * c') ^ (|w| + |w - α|) * s' p ^ (w - α)) * pdist p q ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (h3.trans (mul_le_mul_of_nonneg_right hKα h4)) hM) h5
        _ = M * (k * c') ^ (|w| + |w - α|) * s' p ^ (w - α) * pdist p q ^ α := by ring
    by_cases hp0 : f p = 0
    · by_cases hq0 : f q = 0
      · rw [hp0, hq0, sub_zero, norm_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg hM hP) h4) h5
      · obtain ⟨c1, c2⟩ := hcomp q hq hq0
        have g1 := hsc'.le p hp q hq hda
        have g2 := hsc'.ge p hp q hq hda
        have hsq := hs q hq
        have d1 : s q ≤ k * c' * s' p := by
          calc s q ≤ k * s' q := c1
            _ ≤ k * (c' * s' p) := mul_le_mul_of_nonneg_left g1 hk0.le
            _ = k * c' * s' p := by ring
        have d2 : s' p ≤ k * c' * s q := by
          calc s' p ≤ c' * s' q := g2
            _ ≤ c' * (k * s q) := mul_le_mul_of_nonneg_left c2 hc0.le
            _ = k * c' * s q := by ring
        have hdq : pdist q p ≤ a * s q := by
          rw [pdist_comm]
          calc pdist p q ≤ a / (k * c') * s' p := hdb
            _ ≤ a / (k * c') * (k * c' * s q) := mul_le_mul_of_nonneg_left d2 haK
            _ = a * s q := by rw [← mul_assoc, div_mul_cancel₀ a hK0.ne']
        refine fin q hq d1 d2 ?_
        have hb := hf.2 q hq p hp hdq
        rwa [pdist_comm q p, ← norm_sub_rev] at hb
    · obtain ⟨c1, c2⟩ := hcomp p hp hp0
      have hsp := hs p hp
      have d1 : s p ≤ k * c' * s' p := by
        calc s p ≤ k * s' p := c1
          _ ≤ k * s' p * c' := le_mul_of_one_le_right (mul_nonneg hk0.le hsp'.le) hc1
          _ = k * c' * s' p := by ring
      have d2 : s' p ≤ k * c' * s p := by
        calc s' p ≤ k * s p := c2
          _ ≤ k * s p * c' := le_mul_of_one_le_right (mul_nonneg hk0.le hsp.le) hc1
          _ = k * c' * s p := by ring
      have hdp : pdist p q ≤ a * s p := by
        calc pdist p q ≤ a / (k * c') * s' p := hdb
          _ ≤ a / (k * c') * (k * c' * s p) := mul_le_mul_of_nonneg_left d2 haK
          _ = a * s p := by rw [← mul_assoc, div_mul_cancel₀ a hK0.ne']
      exact fin p hp d1 d2 (hf.2 p hp q hq hdp)

/-! ### Jets and their components -/

section Components

variable [NormedSpace ℝ E]

/-- The norm of a multilinear map is at most the sum of the norms of its values
on the tuples of vectors of an orthonormal basis. -/
theorem norm_le_sum_basis {m j : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (φ : V [×j]→L[ℝ] E) :
    ‖φ‖ ≤ ∑ i : Fin j → Fin m, ‖φ (fun k => e (i k))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : (fun k => ∑ i : Fin m, e.repr (v k) i • e i) = v := by
    funext k
    exact e.sum_repr (v k)
  have hsum := φ.map_sum (fun (k : Fin j) (i : Fin m) => e.repr (v k) i • e i)
  rw [hv] at hsum
  have hcoef : ∀ (k : Fin j) (i : Fin m), |e.repr (v k) i| ≤ ‖v k‖ := by
    intro k i
    rw [e.repr_apply_apply]
    have h := abs_real_inner_le_norm (e i) (v k)
    rwa [e.norm_eq_one, one_mul] at h
  calc ‖φ v‖ = ‖∑ r : Fin j → Fin m, φ (fun k => e.repr (v k) (r k) • e (r k))‖ := by rw [hsum]
    _ ≤ ∑ r : Fin j → Fin m, ‖φ (fun k => e.repr (v k) (r k) • e (r k))‖ := norm_sum_le _ _
    _ = ∑ r : Fin j → Fin m, (∏ k, |e.repr (v k) (r k)|) * ‖φ (fun k => e (r k))‖ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [φ.map_smul_univ, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ ∑ r : Fin j → Fin m, (∏ k, ‖v k‖) * ‖φ (fun k => e (r k))‖ := by
      refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => hcoef k (r k)
    _ = (∑ i : Fin j → Fin m, ‖φ (fun k => e (i k))‖) * ∏ k, ‖v k‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _

end Components

/-- **The exact norm of the reused inverse bounds the jets**: the bound
`XBound` with the constant `m⁴ K`. -/
theorem xBound_of_xNorm_le {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) {α w a K : ℝ}
    {u ut : ℝ → V → ℂ} (hK : 0 ≤ K) (hm : 1 ≤ m)
    (h : xNorm e α w a u ut ≤ ENNReal.ofReal K) : XBound α w a ((m : ℝ) ^ 4 * K) u ut := by
  intro p hp
  have hloc : localXNorm e α (localDomain a p) (weightedValue w p u) (weightedTime w p ut)
      ≤ ENNReal.ofReal K :=
    (le_iSup (fun P : {P : V × ℝ // P.2 < 0} => localXNorm e α (localDomain a P.val)
      (weightedValue w P.val u) (weightedTime w P.val ut)) ⟨p, hp⟩).trans h
  unfold localXNorm at hloc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm4 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hm1
  have hKle : K ≤ (m : ℝ) ^ 4 * K := le_mul_of_one_le_left hK hm4
  refine ⟨fun j hj => ?_, ?_⟩
  · -- the components
    have hcomp : ∀ i : Fin j → Fin m, HolderBound α (localDomain a p)
        (jetComponent e j i (weightedValue w p u)) K := by
      intro i
      apply holderNorm_holderBound hK
      refine le_trans ?_ hloc
      refine le_trans ?_ le_self_add
      have h1 : holderNorm α (localDomain a p) (jetComponent e j i (weightedValue w p u))
          ≤ ∑ i' : Fin j → Fin m,
            holderNorm α (localDomain a p) (jetComponent e j i' (weightedValue w p u)) :=
        Finset.single_le_sum (f := fun i' : Fin j → Fin m =>
          holderNorm α (localDomain a p) (jetComponent e j i' (weightedValue w p u)))
          (fun _ _ => zero_le) (Finset.mem_univ i)
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun j' : Fin 5 => ∑ i' : Fin j'.val → Fin m,
          holderNorm α (localDomain a p) (jetComponent e j'.val i' (weightedValue w p u)))
        (fun _ _ => zero_le) (Finset.mem_univ (⟨j, by omega⟩ : Fin 5))
    have hcard : (∑ _i : Fin j → Fin m, K) = (m : ℝ) ^ j * K := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
    have hmj : (m : ℝ) ^ j * K ≤ (m : ℝ) ^ 4 * K :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm1 hj) hK
    refine ⟨fun q hq => ?_, fun q hq r hr => ?_⟩
    · calc ‖iteratedFDeriv ℝ j (weightedValue w p u q.2) q.1‖
          ≤ ∑ i : Fin j → Fin m,
              ‖iteratedFDeriv ℝ j (weightedValue w p u q.2) q.1 (fun k => e (i k))‖ :=
            norm_le_sum_basis e _
        _ ≤ ∑ _i : Fin j → Fin m, K := Finset.sum_le_sum fun i _ => (hcomp i).1 q hq
        _ = (m : ℝ) ^ j * K := hcard
        _ ≤ (m : ℝ) ^ 4 * K := hmj
    · have hd : 0 ≤ pdist q r ^ α := Real.rpow_nonneg (pdist_nonneg q r) _
      calc ‖iteratedFDeriv ℝ j (weightedValue w p u q.2) q.1
            - iteratedFDeriv ℝ j (weightedValue w p u r.2) r.1‖
          ≤ ∑ i : Fin j → Fin m,
              ‖(iteratedFDeriv ℝ j (weightedValue w p u q.2) q.1
                - iteratedFDeriv ℝ j (weightedValue w p u r.2) r.1) (fun k => e (i k))‖ :=
            norm_le_sum_basis e _
        _ ≤ ∑ _i : Fin j → Fin m, K * pdist q r ^ α := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [ContinuousMultilinearMap.sub_apply]
            exact (hcomp i).2 q hq r hr
        _ = (m : ℝ) ^ j * K * pdist q r ^ α := by
            rw [← Finset.sum_mul, hcard]
        _ ≤ (m : ℝ) ^ 4 * K * pdist q r ^ α := mul_le_mul_of_nonneg_right hmj hd
  · have ht : HolderBound α (localDomain a p)
        (fun q => weightedTime w p ut q.2 q.1) K := by
      apply holderNorm_holderBound hK
      exact le_trans le_add_self hloc
    exact ht.mono hKle

/-! ### The extension of a source to all negative times -/

section Extension

variable [NormedSpace ℝ E]

/-- The extension (6.8) of a source on `[-T, 0)` to all negative times: the
value at the clamped time times a ramp in `σ(z, t) / σ(z, -T)`, which is one
for `t ≥ -T` and vanishes where `σ(z, t) ≥ 2 σ(z, -T)`. -/
noncomputable def ancExt (T : ℝ) (f : V × ℝ → E) (p : V × ℝ) : E :=
  clampT 1 (2 - sigma p / sigma (p.1, -T)) • f (p.1, max p.2 (-T))

theorem sigma_le_of_le {z : V} {t r : ℝ} (h : r ≤ t) (ht : t ≤ 0) :
    sigma (z, t) ≤ sigma (z, r) := by
  unfold sigma
  refine Real.sqrt_le_sqrt ?_
  have : Real.sqrt (-t) ≤ Real.sqrt (-r) := Real.sqrt_le_sqrt (by linarith)
  simpa using this

/-- On `[-T, 0)` the extension is the function itself. -/
theorem ancExt_of_mem {T : ℝ} (hT : 0 < T) (f : V × ℝ → E) {p : V × ℝ}
    (hp : p.2 ∈ Ico (-T) 0) : ancExt T f p = f p := by
  have hsT : 0 < sigma (p.1, -T) := sigma_pos _ (by simpa using hT)
  have h1 : sigma p ≤ sigma (p.1, -T) := sigma_le_of_le (z := p.1) hp.1 hp.2.le
  have h2 : sigma p / sigma (p.1, -T) ≤ 1 := (div_le_one hsT).2 h1
  have h3 : clampT 1 (2 - sigma p / sigma (p.1, -T)) = 1 := by
    unfold clampT
    rw [min_eq_right (by linarith), max_eq_left zero_le_one]
  have h4 : ((p.1, max p.2 (-T)) : V × ℝ) = p := by
    rw [max_eq_left hp.1]
  unfold ancExt
  rw [h3, one_smul, h4]

/-- **The extension has a weighted two-point bound on all negative times.** -/
theorem ancExt_WH {T v : ℝ} {f : V × ℝ → E} (hT : 0 < T)
    (hf : WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0} v M f) (hM : 0 ≤ M)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    WH α (a / 8) (sigma (V := V)) {p : V × ℝ | p.2 < 0} v
      ((1 + 2 ^ |(0 : ℝ)|) * 72 * (M * 8 ^ (|v| + |v - α|) * 1 ^ α)) (ancExt T f) := by
  have hnT : (-T : ℝ) < 0 := by linarith
  -- the scale at the time `-T`
  have hsT : ∀ z : V, 0 < sigma (z, -T) := fun z => sigma_pos _ hnT
  have hsTl : ∀ z z' : V, |sigma (z, -T) - sigma (z', -T)| ≤ ‖z - z'‖ := by
    intro z z'
    have h := abs_sigma_sub_le (p := (z, -T)) (q := (z', -T)) hnT.le hnT.le
    unfold pdist at h
    simpa using h
  have hxd : ∀ p q : V × ℝ, ‖p.1 - q.1‖ ≤ pdist p q := by
    intro p q
    unfold pdist
    linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
  -- the region where the extension does not vanish
  obtain ⟨Ω', hΩ'⟩ : ∃ Ω' : Set (V × ℝ),
      Ω' = {p : V × ℝ | p.2 < 0 ∧ sigma p ≤ 8 * sigma (p.1, -T)} := ⟨_, rfl⟩
  have hsub : Ω' ⊆ {p : V × ℝ | p.2 < 0} := by
    rw [hΩ']
    exact fun p hp => hp.1
  have hsc : IsScale (a / 8) 2 (sigma (V := V)) Ω' :=
    (isScale_sigma (V := V) (by linarith : a / 8 ≤ 1 / 2)).mono le_rfl hsub
  -- the clamped function
  have hΦ : ∀ p ∈ Ω', ((p.1, max p.2 (-T)) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Ico (-T) 0} :=
    fun p hp => ⟨le_max_right _ _, max_lt (hsub hp) hnT⟩
  have hc1 : ∀ p ∈ Ω', sigma ((p.1, max p.2 (-T)) : V × ℝ) ≤ 8 * sigma p := by
    intro p hp
    have hp0 : p.2 < 0 := hsub hp
    have h1 : sigma ((p.1, max p.2 (-T)) : V × ℝ) ≤ sigma p :=
      sigma_le_of_le (z := p.1) (le_max_left _ _) (max_lt hp0 hnT).le
    have := sigma_pos p hp0
    linarith
  have hc2 : ∀ p ∈ Ω', sigma p ≤ 8 * sigma ((p.1, max p.2 (-T)) : V × ℝ) := by
    intro p hp
    rw [hΩ'] at hp
    rcases le_total (-T) p.2 with h | h
    · rw [max_eq_left h]
      have := sigma_pos p hp.1
      linarith
    · rw [max_eq_right h]
      exact hp.2
  have hc3 : ∀ p ∈ Ω', ∀ q ∈ Ω', pdist ((p.1, max p.2 (-T)) : V × ℝ) (q.1, max q.2 (-T))
      ≤ 1 * pdist p q := by
    intro p _ q _
    show ‖p.1 - q.1‖ + |max p.2 (-T) - max q.2 (-T)| ^ ((1 : ℝ) / 4)
      ≤ 1 * (‖p.1 - q.1‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4))
    have h1 := abs_max_sub_max_le_abs p.2 q.2 (-T)
    have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith
  have hclamp : WH α (a / 8) (sigma (V := V)) Ω' v (M * 8 ^ (|v| + |v - α|) * 1 ^ α)
      (fun p => f (p.1, max p.2 (-T))) := by
    have h := hf.comp_map (k := 8) (L := 1) (s' := sigma (V := V)) (Ω' := Ω')
      (Φ := fun p => (p.1, max p.2 (-T))) hM (by norm_num) le_rfl ha.le hα hΦ
      (fun p hp => sigma_pos p hp.2) (fun p hp => sigma_pos p (hsub hp)) hc1 hc2 hc3
    rwa [mul_one] at h
  -- the ramp
  have hramp : WH α (a / 8) (sigma (V := V)) Ω' 0 72
      (fun p => clampT 1 (2 - sigma p / sigma (p.1, -T))) := by
    refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
    · have h1 := clampT_mem (R := 1) zero_le_one (2 - sigma p / sigma (p.1, -T))
      rw [Real.rpow_zero, Real.norm_eq_abs, abs_of_nonneg h1.1]
      linarith [h1.2]
    · have hp0 : p.2 < 0 := hsub hp
      have hq0 : q.2 < 0 := hsub hq
      have hσp := sigma_pos p hp0
      have hd0 := pdist_nonneg p q
      have hsp := hsT p.1
      have hsq := hsT q.1
      rw [hΩ'] at hp hq
      have hds : pdist p q ≤ sigma p := by
        have := mul_le_mul_of_nonneg_right (by linarith : a / 8 ≤ 1) hσp.le
        linarith
      have g1 := abs_sigma_sub_le hp0.le hq0.le
      have g2 := (hsTl p.1 q.1).trans (hxd p q)
      -- the difference of the ratios
      have hspne : sigma (p.1, -T) ≠ 0 := hsp.ne'
      have hsqne : sigma (q.1, -T) ≠ 0 := hsq.ne'
      have e : sigma p / sigma (p.1, -T) - sigma q / sigma (q.1, -T)
          = ((sigma p - sigma q) + sigma q / sigma (q.1, -T)
              * (sigma (q.1, -T) - sigma (p.1, -T))) / sigma (p.1, -T) := by
        field_simp
        ring
      have hu : sigma q / sigma (q.1, -T) ≤ 8 := (div_le_iff₀ hsq).2 hq.2
      have hu0 : 0 ≤ sigma q / sigma (q.1, -T) := div_nonneg (sigma_pos q hq0).le hsq.le
      have h3 : |sigma p / sigma (p.1, -T) - sigma q / sigma (q.1, -T)|
          ≤ 9 * pdist p q / sigma (p.1, -T) := by
        rw [e, abs_div, abs_of_pos hsp]
        refine div_le_div_of_nonneg_right ?_ hsp.le
        calc |(sigma p - sigma q) + sigma q / sigma (q.1, -T)
              * (sigma (q.1, -T) - sigma (p.1, -T))|
            ≤ |sigma p - sigma q| + |sigma q / sigma (q.1, -T)
              * (sigma (q.1, -T) - sigma (p.1, -T))| := abs_add_le _ _
          _ = |sigma p - sigma q| + sigma q / sigma (q.1, -T)
              * |sigma (p.1, -T) - sigma (q.1, -T)| := by
            rw [abs_mul, abs_of_nonneg hu0, abs_sub_comm (sigma (q.1, -T))]
          _ ≤ pdist p q + 8 * pdist p q :=
            add_le_add g1 (mul_le_mul hu g2 (abs_nonneg _) (by norm_num))
          _ = 9 * pdist p q := by ring
      have h4 : 9 * pdist p q / sigma (p.1, -T) ≤ 72 * (sigma p ^ (-1 : ℝ) * pdist p q) := by
        rw [Real.rpow_neg_one, div_le_iff₀ hsp]
        have h5 : sigma p * (sigma p)⁻¹ = 1 := mul_inv_cancel₀ hσp.ne'
        have h6 : 0 ≤ (sigma p)⁻¹ * pdist p q := mul_nonneg (inv_nonneg.2 hσp.le) hd0
        have h7 : 72 * ((sigma p)⁻¹ * pdist p q) * sigma p = 72 * pdist p q * (sigma p * (sigma p)⁻¹) := by
          ring
        calc 9 * pdist p q = 72 * pdist p q * 1 / 8 := by ring
          _ = 72 * ((sigma p)⁻¹ * pdist p q) * sigma p / 8 := by rw [h7, h5]
          _ ≤ 72 * ((sigma p)⁻¹ * pdist p q) * sigma (p.1, -T) := by
            have h8 : sigma p / 8 ≤ sigma (p.1, -T) := by linarith [hp.2]
            have h9 : 0 ≤ 72 * ((sigma p)⁻¹ * pdist p q) := by positivity
            calc 72 * ((sigma p)⁻¹ * pdist p q) * sigma p / 8
                = 72 * ((sigma p)⁻¹ * pdist p q) * (sigma p / 8) := by ring
              _ ≤ 72 * ((sigma p)⁻¹ * pdist p q) * sigma (p.1, -T) :=
                mul_le_mul_of_nonneg_left h8 h9
      have h10 := scale_interp (w := 0) hσp hd0 hds hα hα1
      rw [Real.rpow_one] at h10
      have e0 : (0 : ℝ) - 1 = -1 := by norm_num
      rw [e0] at h10
      have h11 := abs_clampT_sub_le 1 (2 - sigma p / sigma (p.1, -T))
        (2 - sigma q / sigma (q.1, -T))
      have e1 : 2 - sigma p / sigma (p.1, -T) - (2 - sigma q / sigma (q.1, -T))
          = -(sigma p / sigma (p.1, -T) - sigma q / sigma (q.1, -T)) := by ring
      rw [e1, abs_neg] at h11
      rw [Real.norm_eq_abs]
      calc |clampT 1 (2 - sigma p / sigma (p.1, -T)) - clampT 1 (2 - sigma q / sigma (q.1, -T))|
          ≤ |sigma p / sigma (p.1, -T) - sigma q / sigma (q.1, -T)| := h11
        _ ≤ 9 * pdist p q / sigma (p.1, -T) := h3
        _ ≤ 72 * (sigma p ^ (-1 : ℝ) * pdist p q) := h4
        _ ≤ 72 * (sigma p ^ ((0 : ℝ) - α) * pdist p q ^ α) :=
          mul_le_mul_of_nonneg_left h10 (by norm_num)
        _ = 72 * sigma p ^ ((0 : ℝ) - α) * pdist p q ^ α := by ring
  -- the product on the region
  have hprod := WH.smul hsc (by norm_num : (0 : ℝ) ≤ 72)
    (by positivity : 0 ≤ M * 8 ^ (|v| + |v - α|) * 1 ^ α) hramp hclamp
  rw [zero_add] at hprod
  -- the extension vanishes off the region
  have hzero : ∀ p : V × ℝ, p.2 < 0 → 2 * sigma (p.1, -T) ≤ sigma p → ancExt T f p = 0 := by
    intro p _ h
    have h1 : 2 ≤ sigma p / sigma (p.1, -T) := (le_div_iff₀ (hsT p.1)).2 h
    have h2 : clampT 1 (2 - sigma p / sigma (p.1, -T)) = 0 := by
      unfold clampT
      exact max_eq_right ((min_le_left _ _).trans (by linarith))
    unfold ancExt
    rw [h2, zero_smul]
  refine WH.of_local (Ω' := Ω') hprod (by positivity) (fun p hp => sigma_pos p hp)
    (fun p hp => ?_) (fun p hp q hq hd => ?_)
  · by_cases h : sigma p ≤ 8 * sigma (p.1, -T)
    · left
      rw [hΩ']
      exact ⟨hp, h⟩
    · right
      refine hzero p hp ?_
      have := hsT p.1
      linarith
  · have hσp := sigma_pos p hp
    have hds : pdist p q ≤ sigma p / 16 := by
      have := mul_le_mul_of_nonneg_right (by linarith : a / 8 ≤ 1 / 16) hσp.le
      linarith
    have g1 := abs_le.1 (abs_sigma_sub_le (le_of_lt hp) (le_of_lt hq))
    have g2 := abs_le.1 ((hsTl p.1 q.1).trans (hxd p q))
    have hsp := hsT p.1
    have hsq := hsT q.1
    by_cases h1 : sigma p ≤ 8 * sigma (p.1, -T)
    · by_cases h2 : sigma q ≤ 8 * sigma (q.1, -T)
      · left
        rw [hΩ']
        exact ⟨⟨hp, h1⟩, ⟨hq, h2⟩⟩
      · right
        exact ⟨hzero p hp (by linarith [g1.1, g1.2, g2.1, g2.2]),
          hzero q hq (by linarith)⟩
    · right
      exact ⟨hzero p hp (by linarith),
        hzero q hq (by linarith [g1.1, g1.2, g2.1, g2.2])⟩

end Extension

end Calabi.Weighted
