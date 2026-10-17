import Calabi.Correction.OuterEstimate
import OAI.Analysis.AncientFlat.Regularity.ShortHolder

/-!
# Small spatial jets from an exponent gap (Lemma 4.5 of the manuscript, (4.17))

If the jets `Dʲu`, `j ≤ 4`, of a function with zero initial data are bounded
in the parabolic Hölder norm of exponent `α′` on the windows of scale `a₁ s`
(`SJet` at `α′`), then on the windows of half the scale their Hölder norms of
exponent `α < α′` are small when the elapsed time is short:
the factor is `(R / (a₁ s(x₀) / 2)⁴)^{(α′ - α)/4}`.

No statement is made for the time derivative, which is not small (Remark 4.6
of the manuscript).
-/

open Set Filter
open scoped Topology ContDiff Laplacian

namespace Calabi.FlatZero

open OAI OAI.ParabolicInterior OAI.ParabolicInitial OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A window of half the scale is a window of a window. -/
theorem windowValue_half (x₀ : V) (q : ℝ) (u : ℝ → V → ℂ) :
    windowValue (x₀, 0) (q / 2) u
      = windowValue ((0 : V), 0) (1 / 2) (windowValue (x₀, 0) q u) := by
  funext t x
  show u (0 + (q / 2) ^ 4 * t) (x₀ + (q / 2) • x)
    = u (0 + q ^ 4 * (0 + (1 / 2) ^ 4 * t)) (x₀ + q • ((0 : V) + (1 / 2 : ℝ) • x))
  have e1 : (0 : ℝ) + (q / 2) ^ 4 * t = 0 + q ^ 4 * (0 + (1 / 2) ^ 4 * t) := by ring
  have e2 : x₀ + (q / 2) • x = x₀ + q • ((0 : V) + (1 / 2 : ℝ) • x) := by
    rw [zero_add, smul_smul]
    congr 2
    ring
  rw [e1, e2]

/-- **Lemma 4.5, (4.17)**: small spatial jets from an exponent gap. -/
theorem outer_gap_small (α α' : ℝ) (hα : 0 < α) (haa : α < α') (hα1 : α' < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : V → ℝ) (a₁ R w N : ℝ) (u ut : ℝ → V → ℂ),
      0 < a₁ → (∀ x, 0 < s x) → 0 < R → (∀ x, 0 ≤ N * s x ^ w) →
      (∀ t, ContDiff ℝ 4 (u t)) → (∀ x, u 0 x = 0) → SJet s a₁ R α' w N u ut →
      ∀ x₀ : V, R ≤ (a₁ * s x₀ / 2) ^ 4 → ∀ j : ℕ, j ≤ 4 →
        HolderBound α (slab 1 (R / (a₁ * s x₀ / 2) ^ 4))
          (fun p => iteratedFDeriv ℝ j (windowValue (x₀, 0) (a₁ * s x₀ / 2) u p.2) p.1)
          (C * (R / (a₁ * s x₀ / 2) ^ 4) ^ ((α' - α) / 4) * (N * s x₀ ^ w)) := by
  obtain ⟨C, hC, HS⟩ := OAI.ParabolicShort.spatial_small (V := V) (E := ℂ) α α' hα haa hα1
  refine ⟨C, hC, ?_⟩
  intro s a₁ R w N u ut ha₁ hs hR hN hu hu0 hJ x₀ hRq j hj
  have hq : 0 < a₁ * s x₀ := mul_pos ha₁ (hs x₀)
  have hq2 : 0 < a₁ * s x₀ / 2 := by positivity
  have hq24 : 0 < (a₁ * s x₀ / 2) ^ 4 := pow_pos hq2 4
  have hh : 0 < R / (a₁ * s x₀ / 2) ^ 4 := div_pos hR hq24
  have hh1 : R / (a₁ * s x₀ / 2) ^ 4 ≤ 1 := (div_le_one hq24).2 hRq
  have hα'0 : 0 ≤ α' := (hα.trans haa).le
  -- the half window as a window of the window
  have hmaps : MapsTo (window ((0 : V), 0) (1 / 2)) (slab 2 (R / (a₁ * s x₀ / 2) ^ 4))
      (slab 1 (R / (a₁ * s x₀) ^ 4)) := by
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · show ‖(0 : V) + (1 / 2 : ℝ) • p.1‖ < 1
      rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := hp.1
      linarith
    · show (0 : ℝ) ≤ 0 + (1 / 2) ^ 4 * p.2
      have := hp.2.1
      positivity
    · show (0 : ℝ) + (1 / 2) ^ 4 * p.2 ≤ R / (a₁ * s x₀) ^ 4
      have h2 := hp.2.2
      have e : R / (a₁ * s x₀ / 2) ^ 4 = 16 * (R / (a₁ * s x₀) ^ 4) := by
        field_simp
        ring
      rw [e] at h2
      linarith
  have hwc : ∀ t, ContDiff ℝ 4 (windowValue (x₀, 0) (a₁ * s x₀) u t) :=
    windowValue_contDiff (x₀, 0) (a₁ * s x₀) u hu
  have hjets : ∀ n : ℕ, n ≤ 4 → HolderBound α' (slab 2 (R / (a₁ * s x₀ / 2) ^ 4))
      (fun p => iteratedFDeriv ℝ n (windowValue (x₀, 0) (a₁ * s x₀ / 2) u p.2) p.1)
      (N * s x₀ ^ w) := by
    intro n hn
    have h := holder_window_smul hα'0 (hN x₀) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 ≤ 1) ((0 : V), 0) n ((hJ x₀).1 n hn) hmaps
    have heq : (fun p : V × ℝ =>
        iteratedFDeriv ℝ n (windowValue (x₀, 0) (a₁ * s x₀ / 2) u p.2) p.1)
        = fun p => ((1 : ℝ) / 2) ^ n • iteratedFDeriv ℝ n
          (windowValue (x₀, 0) (a₁ * s x₀) u (window ((0 : V), 0) (1 / 2) p).2)
          (window ((0 : V), 0) (1 / 2) p).1 := by
      funext p
      rw [windowValue_half]
      exact window_jet ((0 : V), 0) (1 / 2) (windowValue (x₀, 0) (a₁ * s x₀) u) hwc n hn p
    rw [heq]
    exact h
  have hzero : ∀ x : V, ‖x‖ < 2 → windowValue (x₀, 0) (a₁ * s x₀ / 2) u 0 x = 0 := by
    intro x _
    show u (0 + (a₁ * s x₀ / 2) ^ 4 * 0) (x₀ + (a₁ * s x₀ / 2) • x) = 0
    rw [mul_zero, add_zero]
    exact hu0 _
  exact HS (R / (a₁ * s x₀ / 2) ^ 4) (N * s x₀ ^ w) hh hh1 (hN x₀)
    (windowValue (x₀, 0) (a₁ * s x₀ / 2) u) hzero hjets j hj

end Calabi.FlatZero
