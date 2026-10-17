import Calabi.Correction.TwoPoint
import OAI.Analysis.AncientFlat.Regularity.CommutatorHolder
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Weighted bounds for jets: cut-offs and commutators

`WJ α a s Ω w M n u` is the weighted two-point bound of `TwoPoint.lean` for
the spatial jets `Dʲu`, `j ≤ n`, with the weights `w - j`. With `n = 4` and a
bound of weight `w - 4` for the time derivative this is the norm `X` of
Definition 4.1 of the manuscript; without the time derivative it is `X′`.

* `WJ.smul`: multiplication by a function whose jets have the weights `-j`
  (a cut-off at the local scale) preserves the bounds.
* `commutator_WH`: the commutator `D⁴(χ u) - χ D⁴u` is bounded by the jets of
  `u` of order at most three; this is the form in which the smallness of the
  lower jets of a zero-data solution (Lemma 4.5) enters the cut-off errors.
* `WJ.of_bounds`: scaled derivative bounds of a time-independent function give
  its weighted jets.
-/

open Set Finset
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicCommutator

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The Leibniz sum with scaled bounds -/

/-- The Leibniz sum, when the `i`-th and `(j - i)`-th factors have the scaled
sizes `σ^{u - i}` and `σ^{v - (j - i)}`. -/
theorem leibniz_sum_le {j : ℕ} {x y : ℕ → ℝ} {A B σ u v : ℝ} (hσ : 0 < σ)
    (h : ∀ i ≤ j, x i * y (j - i) ≤ A * σ ^ (u - i) * (B * σ ^ (v - ((j - i : ℕ) : ℝ)))) :
    ∑ i ∈ range (j + 1), (j.choose i : ℝ) * x i * y (j - i)
      ≤ 2 ^ j * (A * B) * σ ^ (u + v - j) := by
  have hterm : ∀ i ∈ range (j + 1), (j.choose i : ℝ) * x i * y (j - i)
      ≤ (j.choose i : ℝ) * ((A * B) * σ ^ (u + v - j)) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have e : σ ^ (u - i) * σ ^ (v - ((j - i : ℕ) : ℝ)) = σ ^ (u + v - j) := by
      rw [← Real.rpow_add hσ, Nat.cast_sub hij]
      congr 1
      ring
    calc (j.choose i : ℝ) * x i * y (j - i) = (j.choose i : ℝ) * (x i * y (j - i)) := by ring
      _ ≤ (j.choose i : ℝ) * (A * σ ^ (u - i) * (B * σ ^ (v - ((j - i : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left (h i hij) (Nat.cast_nonneg _)
      _ = (j.choose i : ℝ) * ((A * B) * (σ ^ (u - i) * σ ^ (v - ((j - i : ℕ) : ℝ)))) := by
        ring
      _ = (j.choose i : ℝ) * ((A * B) * σ ^ (u + v - j)) := by rw [e]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- The Leibniz bound for a product with scaled bounds at one point. -/
theorem norm_iteratedFDeriv_smul_scaled {j : ℕ} {f : V → ℝ} {g : V → E}
    (hf : ContDiff ℝ j f) (hg : ContDiff ℝ j g) (x : V) {A B σ u v : ℝ} (hσ : 0 < σ)
    (hA : 0 ≤ A) (hfb : ∀ i : ℕ, i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ A * σ ^ (u - i))
    (hgb : ∀ i : ℕ, i ≤ j → ‖iteratedFDeriv ℝ i g x‖ ≤ B * σ ^ (v - i)) :
    ‖iteratedFDeriv ℝ j (fun y => f y • g y) x‖ ≤ 2 ^ j * (A * B) * σ ^ (u + v - j) := by
  refine (norm_iteratedFDeriv_smul_le hf hg x le_rfl).trans ?_
  exact leibniz_sum_le (x := fun i => ‖iteratedFDeriv ℝ i f x‖)
    (y := fun i => ‖iteratedFDeriv ℝ i g x‖) hσ fun i hi =>
    mul_le_mul (hfb i hi) (hgb (j - i) (Nat.sub_le _ _)) (norm_nonneg _)
      (mul_nonneg hA (Real.rpow_nonneg hσ.le _))

/-- The commutator `D⁴(f g) - f D⁴g` with scaled bounds at one point: only the
derivatives of `g` of order at most three enter. -/
theorem norm_commutator_scaled {f : V → ℝ} {g : V → E} (hf : ContDiff ℝ 4 f)
    (hg : ContDiff ℝ 4 g) (x : V) {A B σ u v : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ‖iteratedFDeriv ℝ i f x‖ ≤ A * σ ^ (u - i))
    (hgb : ∀ i : ℕ, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ B * σ ^ (v - i)) :
    ‖commutator f g x‖ ≤ 2 ^ 4 * (A * B) * σ ^ (u + v - (4 : ℕ)) := by
  rw [commutator_eq f g x hf hg]
  refine (norm_iteratedFDeriv_smul_le (f := fun y => f y - f x) (hf.sub contDiff_const) hg x
    (by norm_num : ((4 : ℕ) : WithTop ℕ∞) ≤ 4)).trans ?_
  refine leibniz_sum_le (x := fun i => ‖iteratedFDeriv ℝ i (fun y => f y - f x) x‖)
    (y := fun i => ‖iteratedFDeriv ℝ i g x‖) hσ fun i hi => ?_
  show ‖iteratedFDeriv ℝ i (fun y => f y - f x) x‖ * ‖iteratedFDeriv ℝ (4 - i) g x‖
    ≤ A * σ ^ (u - (i : ℝ)) * (B * σ ^ (v - ((4 - i : ℕ) : ℝ)))
  by_cases hz : i = 0
  · subst hz
    rw [norm_iteratedFDeriv_zero, sub_self, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hσ.le _))
      (mul_nonneg hB (Real.rpow_nonneg hσ.le _))
  · have h1 : 1 ≤ i := Nat.pos_of_ne_zero hz
    rw [jet_sub_value hz f x (hf.of_le (by exact_mod_cast hi))]
    exact mul_le_mul (hfb i h1 hi) (hgb (4 - i) (by omega)) (norm_nonneg _)
      (mul_nonneg hA (Real.rpow_nonneg hσ.le _))

/-! ### Weighted jets -/

variable {α a c w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}

/-- Weighted two-point bounds for the spatial jets of order at most `n`: the
jet of order `j` has the weight `w - j`. -/
def WJ (α a : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) (w M : ℝ) (n : ℕ) (u : ℝ → V → E) : Prop :=
  ∀ j : ℕ, j ≤ n → WH α a s Ω (w - j) M (fun p => iteratedFDeriv ℝ j (u p.2) p.1)

theorem WJ.of_le {n m : ℕ} {u : ℝ → V → E} (h : WJ α a s Ω w M n u) (hm : m ≤ n) :
    WJ α a s Ω w M m u := fun j hj => h j (hj.trans hm)

theorem WJ.mono {n : ℕ} {u : ℝ → V → E} (h : WJ α a s Ω w M n u) (hs : ∀ p ∈ Ω, 0 < s p)
    {M' : ℝ} (hM : M ≤ M') : WJ α a s Ω w M' n u := fun j hj => (h j hj).mono hs hM

theorem WJ.restrict {n : ℕ} {u : ℝ → V → E} (h : WJ α a s Ω w M n u) {Ω' : Set (V × ℝ)}
    (hΩ : Ω' ⊆ Ω) : WJ α a s Ω' w M n u := fun j hj => (h j hj).restrict hΩ

/-- The values of a function with weighted jets. -/
theorem WJ.value {n : ℕ} {u : ℝ → V → E} (h : WJ α a s Ω w M n u) :
    WH α a s Ω w M (fun p => u p.2 p.1) := by
  have h0 := h 0 (Nat.zero_le n)
  rw [Nat.cast_zero, sub_zero] at h0
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have h1 : ‖iteratedFDeriv ℝ 0 (u p.2) p.1‖ ≤ M * s p ^ w := h0.1 p hp
    rwa [norm_iteratedFDeriv_zero] at h1
  · have h1 : ‖iteratedFDeriv ℝ 0 (u p.2) p.1 - iteratedFDeriv ℝ 0 (u q.2) q.1‖
        ≤ M * s p ^ (w - α) * pdist p q ^ α := h0.2 p hp q hq hd
    have e : iteratedFDeriv ℝ 0 (u p.2) p.1 - iteratedFDeriv ℝ 0 (u q.2) q.1
        = (continuousMultilinearCurryFin0 ℝ V E).symm (u p.2 p.1 - u q.2 q.1) := by
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        Function.comp_apply, map_sub]
    rwa [e, LinearIsometryEquiv.norm_map] at h1

theorem WJ.add {n : ℕ} {N : ℝ} {u v : ℝ → V → E} (hus : ∀ t, ContDiff ℝ n (u t))
    (hvs : ∀ t, ContDiff ℝ n (v t)) (hu : WJ α a s Ω w M n u) (hv : WJ α a s Ω w N n v) :
    WJ α a s Ω w (M + N) n (fun t x => u t x + v t x) := by
  intro j hj
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have e : (fun p : V × ℝ => iteratedFDeriv ℝ j (fun x => u p.2 x + v p.2 x) p.1)
      = fun p => iteratedFDeriv ℝ j (u p.2) p.1 + iteratedFDeriv ℝ j (v p.2) p.1 := by
    funext p
    exact iteratedFDeriv_add_apply (f := u p.2) (g := v p.2)
      ((hus p.2).of_le hjn).contDiffAt ((hvs p.2).of_le hjn).contDiffAt
  show WH α a s Ω (w - j) (M + N)
    (fun p => iteratedFDeriv ℝ j (fun x => u p.2 x + v p.2 x) p.1)
  rw [e]
  exact (hu j hj).add (hv j hj)

/-! ### Multiplication by a cut-off -/

/-- **Cut-offs**: multiplication by a function whose jets have the weights
`-j` preserves weighted jets. -/
theorem WJ.smul {n : ℕ} {A B : ℝ} {χ : ℝ → V → ℝ} {u : ℝ → V → E} (hsc : IsScale a c s Ω)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hχs : ∀ t, ContDiff ℝ n (χ t)) (hus : ∀ t, ContDiff ℝ n (u t))
    (hχ : WJ α a s Ω 0 A n χ) (hu : WJ α a s Ω w B n u) :
    WJ α a s Ω w (2 ^ n * (1 + c ^ (n : ℝ)) * A * B) n (fun t x => χ t x • u t x) := by
  intro j hj
  have hc1 := hsc.one_le
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcn : 0 ≤ c ^ (n : ℝ) := Real.rpow_nonneg hc0 _
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h2j : (0 : ℝ) ≤ 2 ^ j := by positivity
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hconst : (2 : ℝ) ^ j * (1 + c ^ (n : ℝ)) ≤ 2 ^ n * (1 + c ^ (n : ℝ)) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · -- the size of the jet
    have hsp := hsc.pos p hp
    have hT : 0 ≤ s p ^ (w - j) := Real.rpow_nonneg hsp.le _
    have h1 := norm_iteratedFDeriv_smul_scaled (j := j) ((hχs p.2).of_le hjn)
      ((hus p.2).of_le hjn) p.1 (A := A) (B := B) (u := 0) (v := w) hsp hA
      (fun i hi => (hχ i (hi.trans hj)).1 p hp) (fun i hi => (hu i (hi.trans hj)).1 p hp)
    rw [zero_add] at h1
    show ‖iteratedFDeriv ℝ j (fun y => χ p.2 y • u p.2 y) p.1‖
      ≤ 2 ^ n * (1 + c ^ (n : ℝ)) * A * B * s p ^ (w - j)
    refine h1.trans ?_
    have h3 : (2 : ℝ) ^ j * (A * B) * s p ^ (w - j)
        ≤ 2 ^ j * (1 + c ^ (n : ℝ)) * (A * B) * s p ^ (w - j) := by
      have h4 : 0 ≤ (2 : ℝ) ^ j * (A * B) * s p ^ (w - j) := mul_nonneg (mul_nonneg h2j hAB) hT
      nlinarith [mul_nonneg hcn h4]
    have h5 : (2 : ℝ) ^ j * (1 + c ^ (n : ℝ)) * (A * B) * s p ^ (w - j)
        ≤ 2 ^ n * (1 + c ^ (n : ℝ)) * (A * B) * s p ^ (w - j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hAB) hT
    calc (2 : ℝ) ^ j * (A * B) * s p ^ (w - j)
        ≤ 2 ^ n * (1 + c ^ (n : ℝ)) * (A * B) * s p ^ (w - j) := h3.trans h5
      _ = 2 ^ n * (1 + c ^ (n : ℝ)) * A * B * s p ^ (w - j) := by ring
  · -- two points: translate both to the origin
    have hsp := hsc.pos p hp
    have hd0 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
    have hT : 0 ≤ s p ^ (w - j - α) := Real.rpow_nonneg hsp.le _
    let f₁ : V → ℝ := fun z => χ p.2 (z + p.1)
    let f₂ : V → ℝ := fun z => χ q.2 (z + q.1)
    let g₁ : V → E := fun z => u p.2 (z + p.1)
    let g₂ : V → E := fun z => u q.2 (z + q.1)
    have hf₁ : ContDiff ℝ j f₁ := ((hχs p.2).of_le hjn).comp (contDiff_id.add contDiff_const)
    have hf₂ : ContDiff ℝ j f₂ := ((hχs q.2).of_le hjn).comp (contDiff_id.add contDiff_const)
    have hg₁ : ContDiff ℝ j g₁ := ((hus p.2).of_le hjn).comp (contDiff_id.add contDiff_const)
    have hg₂ : ContDiff ℝ j g₂ := ((hus q.2).of_le hjn).comp (contDiff_id.add contDiff_const)
    have ep : iteratedFDeriv ℝ j (fun y => χ p.2 y • u p.2 y) p.1
        = iteratedFDeriv ℝ j (fun z => f₁ z • g₁ z) 0 := by
      have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => χ p.2 y • u p.2 y)
        j p.1 (0 : V)
      rw [zero_add] at h
      exact h.symm
    have eq : iteratedFDeriv ℝ j (fun y => χ q.2 y • u q.2 y) q.1
        = iteratedFDeriv ℝ j (fun z => f₂ z • g₂ z) 0 := by
      have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => χ q.2 y • u q.2 y)
        j q.1 (0 : V)
      rw [zero_add] at h
      exact h.symm
    have e1 : (fun z => (f₁ - f₂) z • g₁ z)
        = (fun z => f₁ z • g₁ z) - fun z => f₂ z • g₁ z := by
      funext z
      simp only [Pi.sub_apply, sub_smul]
    have e2 : (fun z => f₂ z • (g₁ - g₂) z)
        = (fun z => f₂ z • g₁ z) - fun z => f₂ z • g₂ z := by
      funext z
      simp only [Pi.sub_apply, smul_sub]
    have hF₁ : ContDiff ℝ j (fun z => f₁ z • g₁ z) := hf₁.smul hg₁
    have hF₂ : ContDiff ℝ j (fun z => f₂ z • g₂ z) := hf₂.smul hg₂
    have hF₃ : ContDiff ℝ j (fun z => f₂ z • g₁ z) := hf₂.smul hg₁
    have esum : iteratedFDeriv ℝ j (fun z => f₁ z • g₁ z) 0
          - iteratedFDeriv ℝ j (fun z => f₂ z • g₂ z) 0
        = iteratedFDeriv ℝ j (fun z => (f₁ - f₂) z • g₁ z) 0
          + iteratedFDeriv ℝ j (fun z => f₂ z • (g₁ - g₂) z) 0 := by
      rw [e1, e2, iteratedFDeriv_sub hF₁ hF₃, iteratedFDeriv_sub hF₃ hF₂]
      simp only [Pi.sub_apply]
      abel
    -- the two Leibniz sums
    have b1 : ‖iteratedFDeriv ℝ j (fun z => (f₁ - f₂) z • g₁ z) 0‖
        ≤ 2 ^ j * (A * pdist p q ^ α * B) * s p ^ (-α + w - j) := by
      refine norm_iteratedFDeriv_smul_scaled (hf₁.sub hf₂) hg₁ 0 hsp (mul_nonneg hA hd0)
        (fun i hi => ?_) (fun i hi => ?_)
      · have hi' : (i : WithTop ℕ∞) ≤ j := by exact_mod_cast hi
        show ‖iteratedFDeriv ℝ i (f₁ - f₂) 0‖ ≤ A * pdist p q ^ α * s p ^ (-α - (i : ℝ))
        rw [iteratedFDeriv_sub_apply (hf₁.of_le hi').contDiffAt (hf₂.of_le hi').contDiffAt]
        have h1 : ‖iteratedFDeriv ℝ i (χ p.2) p.1 - iteratedFDeriv ℝ i (χ q.2) q.1‖
            ≤ A * s p ^ (0 - (i : ℝ) - α) * pdist p q ^ α :=
          (hχ i (hi.trans hj)).2 p hp q hq hd
        have e : s p ^ (0 - (i : ℝ) - α) = s p ^ (-α - (i : ℝ)) := by
          congr 1
          ring
        rw [e] at h1
        simp only [f₁, f₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (χ p.2) p.1 - iteratedFDeriv ℝ i (χ q.2) q.1‖
            ≤ A * s p ^ (-α - (i : ℝ)) * pdist p q ^ α := h1
          _ = A * pdist p q ^ α * s p ^ (-α - (i : ℝ)) := by ring
      · have h1 : ‖iteratedFDeriv ℝ i (u p.2) p.1‖ ≤ B * s p ^ (w - i) :=
          (hu i (hi.trans hj)).1 p hp
        simpa only [g₁, iteratedFDeriv_comp_add_right, zero_add] using h1
    have b2 : ‖iteratedFDeriv ℝ j (fun z => f₂ z • (g₁ - g₂) z) 0‖
        ≤ 2 ^ j * (A * c ^ (n : ℝ) * (B * pdist p q ^ α)) * s p ^ (0 + (w - α) - j) := by
      refine norm_iteratedFDeriv_smul_scaled hf₂ (hg₁.sub hg₂) 0 hsp (mul_nonneg hA hcn)
        (fun i hi => ?_) (fun i hi => ?_)
      · have h1 : ‖iteratedFDeriv ℝ i (χ q.2) q.1‖ ≤ A * s q ^ (0 - (i : ℝ)) :=
          (hχ i (hi.trans hj)).1 q hq
        have h2 := hsc.rpow_le hp hq hd (0 - (i : ℝ))
        have e : |0 - (i : ℝ)| = (i : ℝ) := by
          rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg i)]
        rw [e] at h2
        have h3 : c ^ (i : ℝ) ≤ c ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (Nat.cast_le.2 (hi.trans hj))
        have h4 : 0 ≤ s p ^ (0 - (i : ℝ)) := Real.rpow_nonneg hsp.le _
        simp only [f₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (χ q.2) q.1‖ ≤ A * s q ^ (0 - (i : ℝ)) := h1
          _ ≤ A * (c ^ (i : ℝ) * s p ^ (0 - (i : ℝ))) := mul_le_mul_of_nonneg_left h2 hA
          _ ≤ A * (c ^ (n : ℝ) * s p ^ (0 - (i : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) hA
          _ = A * c ^ (n : ℝ) * s p ^ (0 - (i : ℝ)) := by ring
      · have hi' : (i : WithTop ℕ∞) ≤ j := by exact_mod_cast hi
        show ‖iteratedFDeriv ℝ i (g₁ - g₂) 0‖ ≤ B * pdist p q ^ α * s p ^ (w - α - (i : ℝ))
        rw [iteratedFDeriv_sub_apply (hg₁.of_le hi').contDiffAt (hg₂.of_le hi').contDiffAt]
        have h1 : ‖iteratedFDeriv ℝ i (u p.2) p.1 - iteratedFDeriv ℝ i (u q.2) q.1‖
            ≤ B * s p ^ (w - (i : ℝ) - α) * pdist p q ^ α :=
          (hu i (hi.trans hj)).2 p hp q hq hd
        have e : s p ^ (w - (i : ℝ) - α) = s p ^ (w - α - (i : ℝ)) := by
          congr 1
          ring
        rw [e] at h1
        simp only [g₁, g₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (u p.2) p.1 - iteratedFDeriv ℝ i (u q.2) q.1‖
            ≤ B * s p ^ (w - α - (i : ℝ)) * pdist p q ^ α := h1
          _ = B * pdist p q ^ α * s p ^ (w - α - (i : ℝ)) := by ring
    have ex1 : s p ^ (-α + w - (j : ℝ)) = s p ^ (w - j - α) := by
      congr 1
      ring
    have ex2 : s p ^ (0 + (w - α) - (j : ℝ)) = s p ^ (w - j - α) := by
      congr 1
      ring
    rw [ex1] at b1
    rw [ex2] at b2
    show ‖iteratedFDeriv ℝ j (fun y => χ p.2 y • u p.2 y) p.1
        - iteratedFDeriv ℝ j (fun y => χ q.2 y • u q.2 y) q.1‖
      ≤ 2 ^ n * (1 + c ^ (n : ℝ)) * A * B * s p ^ (w - j - α) * pdist p q ^ α
    rw [ep, eq, esum]
    have hX : 0 ≤ A * B * s p ^ (w - j - α) * pdist p q ^ α :=
      mul_nonneg (mul_nonneg hAB hT) hd0
    calc ‖iteratedFDeriv ℝ j (fun z => (f₁ - f₂) z • g₁ z) 0
          + iteratedFDeriv ℝ j (fun z => f₂ z • (g₁ - g₂) z) 0‖
        ≤ ‖iteratedFDeriv ℝ j (fun z => (f₁ - f₂) z • g₁ z) 0‖
          + ‖iteratedFDeriv ℝ j (fun z => f₂ z • (g₁ - g₂) z) 0‖ := norm_add_le _ _
      _ ≤ 2 ^ j * (A * pdist p q ^ α * B) * s p ^ (w - j - α)
          + 2 ^ j * (A * c ^ (n : ℝ) * (B * pdist p q ^ α)) * s p ^ (w - j - α) :=
        add_le_add b1 b2
      _ = 2 ^ j * (1 + c ^ (n : ℝ)) * (A * B * s p ^ (w - j - α) * pdist p q ^ α) := by ring
      _ ≤ 2 ^ n * (1 + c ^ (n : ℝ)) * (A * B * s p ^ (w - j - α) * pdist p q ^ α) :=
        mul_le_mul_of_nonneg_right hconst hX
      _ = 2 ^ n * (1 + c ^ (n : ℝ)) * A * B * s p ^ (w - j - α) * pdist p q ^ α := by ring

/-! ### The commutator with a cut-off -/

/-- **The commutator of the fourth derivative with a cut-off** is bounded by
the jets of order at most three. -/
theorem commutator_WH {A B : ℝ} {χ : ℝ → V → ℝ} {u : ℝ → V → E} (hsc : IsScale a c s Ω)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hχs : ∀ t, ContDiff ℝ 4 (χ t)) (hus : ∀ t, ContDiff ℝ 4 (u t))
    (hχ : WJ α a s Ω 0 A 4 χ) (hu : WJ α a s Ω w B 3 u) :
    WH α a s Ω (w - 4) (2 ^ 4 * (1 + c ^ (4 : ℝ)) * A * B)
      (fun p => commutator (χ p.2) (u p.2) p.1) := by
  have hc1 := hsc.one_le
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hc4 : 0 ≤ c ^ (4 : ℝ) := Real.rpow_nonneg hc0 _
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hsc.pos p hp
    have hT : 0 ≤ s p ^ (w - 4) := Real.rpow_nonneg hsp.le _
    have h1 := norm_commutator_scaled (hχs p.2) (hus p.2) p.1 (A := A) (B := B) (u := 0)
      (v := w) hsp hA hB (fun i _ hi => (hχ i hi).1 p hp) (fun i hi => (hu i hi).1 p hp)
    rw [zero_add, e4] at h1
    refine h1.trans ?_
    have h4 : 0 ≤ (2 : ℝ) ^ 4 * (A * B) * s p ^ (w - 4) :=
      mul_nonneg (mul_nonneg (by norm_num) hAB) hT
    nlinarith [mul_nonneg hc4 h4]
  · have hsp := hsc.pos p hp
    have hd0 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
    have hT : 0 ≤ s p ^ (w - 4 - α) := Real.rpow_nonneg hsp.le _
    let f₁ : V → ℝ := fun z => χ p.2 (z + p.1)
    let f₂ : V → ℝ := fun z => χ q.2 (z + q.1)
    let g₁ : V → E := fun z => u p.2 (z + p.1)
    let g₂ : V → E := fun z => u q.2 (z + q.1)
    have hf₁ : ContDiff ℝ 4 f₁ := (hχs p.2).comp (contDiff_id.add contDiff_const)
    have hf₂ : ContDiff ℝ 4 f₂ := (hχs q.2).comp (contDiff_id.add contDiff_const)
    have hg₁ : ContDiff ℝ 4 g₁ := (hus p.2).comp (contDiff_id.add contDiff_const)
    have hg₂ : ContDiff ℝ 4 g₂ := (hus q.2).comp (contDiff_id.add contDiff_const)
    have hs : commutator (χ p.2) (u p.2) p.1 - commutator (χ q.2) (u q.2) q.1
        = commutator (f₁ - f₂) g₁ 0 + commutator f₂ (g₁ - g₂) 0 := by
      rw [commutator_sub_left _ _ _ _ hf₁ hf₂ hg₁, commutator_sub_right _ _ _ _ hf₂ hg₁ hg₂]
      simp only [f₁, f₂, g₁, g₂, commutator_translate, zero_add]
      abel
    have b1 : ‖commutator (f₁ - f₂) g₁ 0‖
        ≤ 2 ^ 4 * (A * pdist p q ^ α * B) * s p ^ (-α + w - (4 : ℕ)) := by
      refine norm_commutator_scaled (hf₁.sub hf₂) hg₁ 0 hsp (mul_nonneg hA hd0) hB
        (fun i _ hi => ?_) (fun i hi => ?_)
      · have hi' : (i : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hi
        show ‖iteratedFDeriv ℝ i (f₁ - f₂) 0‖ ≤ A * pdist p q ^ α * s p ^ (-α - (i : ℝ))
        rw [iteratedFDeriv_sub_apply (hf₁.of_le hi').contDiffAt (hf₂.of_le hi').contDiffAt]
        have h1 : ‖iteratedFDeriv ℝ i (χ p.2) p.1 - iteratedFDeriv ℝ i (χ q.2) q.1‖
            ≤ A * s p ^ (0 - (i : ℝ) - α) * pdist p q ^ α := (hχ i hi).2 p hp q hq hd
        have e : s p ^ (0 - (i : ℝ) - α) = s p ^ (-α - (i : ℝ)) := by
          congr 1
          ring
        rw [e] at h1
        simp only [f₁, f₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (χ p.2) p.1 - iteratedFDeriv ℝ i (χ q.2) q.1‖
            ≤ A * s p ^ (-α - (i : ℝ)) * pdist p q ^ α := h1
          _ = A * pdist p q ^ α * s p ^ (-α - (i : ℝ)) := by ring
      · have h1 : ‖iteratedFDeriv ℝ i (u p.2) p.1‖ ≤ B * s p ^ (w - i) := (hu i hi).1 p hp
        simpa only [g₁, iteratedFDeriv_comp_add_right, zero_add] using h1
    have b2 : ‖commutator f₂ (g₁ - g₂) 0‖
        ≤ 2 ^ 4 * (A * c ^ (4 : ℝ) * (B * pdist p q ^ α)) * s p ^ (0 + (w - α) - (4 : ℕ)) := by
      refine norm_commutator_scaled hf₂ (hg₁.sub hg₂) 0 hsp (mul_nonneg hA hc4)
        (mul_nonneg hB hd0) (fun i _ hi => ?_) (fun i hi => ?_)
      · have h1 : ‖iteratedFDeriv ℝ i (χ q.2) q.1‖ ≤ A * s q ^ (0 - (i : ℝ)) :=
          (hχ i hi).1 q hq
        have h2 := hsc.rpow_le hp hq hd (0 - (i : ℝ))
        have e : |0 - (i : ℝ)| = (i : ℝ) := by
          rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg i)]
        rw [e] at h2
        have h3 : c ^ (i : ℝ) ≤ c ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by exact_mod_cast hi)
        have h4 : 0 ≤ s p ^ (0 - (i : ℝ)) := Real.rpow_nonneg hsp.le _
        simp only [f₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (χ q.2) q.1‖ ≤ A * s q ^ (0 - (i : ℝ)) := h1
          _ ≤ A * (c ^ (i : ℝ) * s p ^ (0 - (i : ℝ))) := mul_le_mul_of_nonneg_left h2 hA
          _ ≤ A * (c ^ (4 : ℝ) * s p ^ (0 - (i : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) hA
          _ = A * c ^ (4 : ℝ) * s p ^ (0 - (i : ℝ)) := by ring
      · have hi' : (i : WithTop ℕ∞) ≤ 4 := by
          have : i ≤ 4 := by omega
          exact_mod_cast this
        show ‖iteratedFDeriv ℝ i (g₁ - g₂) 0‖ ≤ B * pdist p q ^ α * s p ^ (w - α - (i : ℝ))
        rw [iteratedFDeriv_sub_apply (hg₁.of_le hi').contDiffAt (hg₂.of_le hi').contDiffAt]
        have h1 : ‖iteratedFDeriv ℝ i (u p.2) p.1 - iteratedFDeriv ℝ i (u q.2) q.1‖
            ≤ B * s p ^ (w - (i : ℝ) - α) * pdist p q ^ α := (hu i hi).2 p hp q hq hd
        have e : s p ^ (w - (i : ℝ) - α) = s p ^ (w - α - (i : ℝ)) := by
          congr 1
          ring
        rw [e] at h1
        simp only [g₁, g₂, iteratedFDeriv_comp_add_right, zero_add]
        calc ‖iteratedFDeriv ℝ i (u p.2) p.1 - iteratedFDeriv ℝ i (u q.2) q.1‖
            ≤ B * s p ^ (w - α - (i : ℝ)) * pdist p q ^ α := h1
          _ = B * pdist p q ^ α * s p ^ (w - α - (i : ℝ)) := by ring
    have ex1 : s p ^ (-α + w - ((4 : ℕ) : ℝ)) = s p ^ (w - 4 - α) := by
      rw [e4]
      congr 1
      ring
    have ex2 : s p ^ (0 + (w - α) - ((4 : ℕ) : ℝ)) = s p ^ (w - 4 - α) := by
      rw [e4]
      congr 1
      ring
    rw [ex1] at b1
    rw [ex2] at b2
    show ‖commutator (χ p.2) (u p.2) p.1 - commutator (χ q.2) (u q.2) q.1‖
      ≤ 2 ^ 4 * (1 + c ^ (4 : ℝ)) * A * B * s p ^ (w - 4 - α) * pdist p q ^ α
    rw [hs]
    calc ‖commutator (f₁ - f₂) g₁ 0 + commutator f₂ (g₁ - g₂) 0‖
        ≤ ‖commutator (f₁ - f₂) g₁ 0‖ + ‖commutator f₂ (g₁ - g₂) 0‖ := norm_add_le _ _
      _ ≤ 2 ^ 4 * (A * pdist p q ^ α * B) * s p ^ (w - 4 - α)
          + 2 ^ 4 * (A * c ^ (4 : ℝ) * (B * pdist p q ^ α)) * s p ^ (w - 4 - α) :=
        add_le_add b1 b2
      _ = 2 ^ 4 * (1 + c ^ (4 : ℝ)) * A * B * s p ^ (w - 4 - α) * pdist p q ^ α := by ring

/-! ### Time-independent functions -/

/-- **Scaled derivative bounds give weighted jets**, for a function that does
not depend on the time. The bounds are assumed on the ball of radius `a s(p)`
around every point, in terms of the scale at its centre. -/
theorem WJ.of_bounds {n : ℕ} {A : ℝ} {χ : V → ℝ} (hs : ∀ p ∈ Ω, 0 < s p) (hA : 0 ≤ A)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hχ : ContDiff ℝ (n + 1 : ℕ) χ)
    (hb : ∀ p ∈ Ω, ∀ z : V, ‖z - p.1‖ ≤ a * s p → ∀ j : ℕ, j ≤ n + 1 →
      ‖iteratedFDeriv ℝ j χ z‖ ≤ A * s p ^ (-(j : ℝ))) :
    WJ α a s Ω 0 (2 * A) n (fun _ => χ) := by
  intro j hj
  refine WH.of_lipschitz hs hA ha1 hα hα1 (fun p hp => ?_) (fun p hp q hq hd => ?_)
  · have hsp := hs p hp
    have h0 : (0 : ℝ) ≤ a * s p := mul_nonneg ha0 hsp.le
    have h1 := hb p hp p.1 (by rw [sub_self, norm_zero]; exact h0) j (by omega)
    have e : s p ^ (-(j : ℝ)) = s p ^ (0 - (j : ℝ)) := by
      congr 1
      ring
    rw [e] at h1
    exact h1
  · have hsp := hs p hp
    have hx : ‖p.1 - q.1‖ ≤ pdist p q := by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
    have hball : ∀ z ∈ Metric.closedBall p.1 (a * s p),
        ‖fderiv ℝ (iteratedFDeriv ℝ j χ) z‖ ≤ A * s p ^ (0 - (j : ℝ) - 1) := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      have h1 := hb p hp z (by rw [← dist_eq_norm]; exact hz) (j + 1) (by omega)
      have e : s p ^ (-((j + 1 : ℕ) : ℝ)) = s p ^ (0 - (j : ℝ) - 1) := by
        congr 1
        push_cast
        ring
      rw [e] at h1
      exact h1
    have hdiff : ∀ z ∈ Metric.closedBall p.1 (a * s p),
        DifferentiableAt ℝ (iteratedFDeriv ℝ j χ) z := fun z _ =>
      (hχ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_le hj)) z
    have hp' : p.1 ∈ Metric.closedBall p.1 (a * s p) := by
      rw [Metric.mem_closedBall, dist_self]
      exact (norm_nonneg _).trans (hx.trans hd)
    have hq' : q.1 ∈ Metric.closedBall p.1 (a * s p) := by
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact hx.trans hd
    have hmv := (convex_closedBall p.1 (a * s p)).norm_image_sub_le_of_norm_fderiv_le hdiff hball
      hq' hp'
    have h4 : 0 ≤ A * s p ^ (0 - (j : ℝ) - 4) * |p.2 - q.2| :=
      mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hsp.le _)) (abs_nonneg _)
    show ‖iteratedFDeriv ℝ j χ p.1 - iteratedFDeriv ℝ j χ q.1‖
      ≤ A * s p ^ (0 - (j : ℝ) - 1) * ‖p.1 - q.1‖ + A * s p ^ (0 - (j : ℝ) - 4) * |p.2 - q.2|
    linarith

end Calabi.Weighted
