import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global existence for a Lipschitz field on a compact interval

Mathlib's Picard–Lindelöf theorem is local: the length of the interval is
limited by the size of the field on a ball. For a field that is Lipschitz on
the whole space, uniformly in time, short steps of a fixed length can be glued,
which gives a trajectory on any compact interval.
-/

open Set Metric
open scoped NNReal Topology

namespace Calabi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two trajectories that agree at the common endpoint glue to one. -/
theorem hasDerivWithinAt_glue {f : ℝ → E → E} {a c e : ℝ} {α β γ : ℝ → E}
    (hα : ∀ t ∈ Icc a c, HasDerivWithinAt α (f t (α t)) (Icc a c) t)
    (hβ : ∀ t ∈ Icc c e, HasDerivWithinAt β (f t (β t)) (Icc c e) t)
    (hγα : ∀ u ∈ Icc a c, γ u = α u) (hγβ : ∀ u ∈ Icc c e, γ u = β u) :
    ∀ t ∈ Icc a e, HasDerivWithinAt γ (f t (γ t)) (Icc a e) t := by
  intro t ht
  rcases lt_trichotomy t c with h | h | h
  · have h1 : HasDerivWithinAt γ (f t (γ t)) (Icc a c) t := by
      rw [hγα t ⟨ht.1, h.le⟩]
      exact (hα t ⟨ht.1, h.le⟩).congr hγα (hγα t ⟨ht.1, h.le⟩)
    refine h1.mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, h, fun u hu => ⟨hu.2.1, hu.1.le⟩⟩
  · subst h
    have h1 : HasDerivWithinAt γ (f t (γ t)) (Icc a t) t := by
      rw [hγα t ⟨ht.1, le_rfl⟩]
      exact (hα t ⟨ht.1, le_rfl⟩).congr hγα (hγα t ⟨ht.1, le_rfl⟩)
    have h2 : HasDerivWithinAt γ (f t (γ t)) (Icc t e) t := by
      rw [hγβ t ⟨le_rfl, ht.2⟩]
      exact (hβ t ⟨le_rfl, ht.2⟩).congr hγβ (hγβ t ⟨le_rfl, ht.2⟩)
    have h3 := h1.union h2
    rwa [Icc_union_Icc_eq_Icc ht.1 ht.2] at h3
  · have h2 : HasDerivWithinAt γ (f t (γ t)) (Icc c e) t := by
      rw [hγβ t ⟨h.le, ht.2⟩]
      exact (hβ t ⟨h.le, ht.2⟩).congr hγβ (hγβ t ⟨h.le, ht.2⟩)
    refine h2.mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, h, fun u hu => ⟨hu.1.le, hu.2.2⟩⟩

variable [CompleteSpace E]

/-- One step: a trajectory on an interval of length at most `1 / (2 K)`. -/
theorem exists_local_solution {f : ℝ → E → E} {K : ℝ≥0} {a b : ℝ}
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (fun t => f t x) (Icc a b))
    {c e : ℝ} (hac : a ≤ c) (hce : c ≤ e) (heb : e ≤ b) (hstep : (K : ℝ) * (e - c) ≤ 1 / 2)
    (x : E) :
    ∃ α : ℝ → E, α c = x ∧ ∀ t ∈ Icc c e, HasDerivWithinAt α (f t (α t)) (Icc c e) t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC c ⟨hac, hce.trans heb⟩)
  lift C to ℝ≥0 using hC0
  obtain ⟨h, hh⟩ : ∃ h : ℝ≥0, (h : ℝ) = e - c := ⟨⟨e - c, sub_nonneg.2 hce⟩, rfl⟩
  rw [← hh] at hstep
  have hPL : IsPicardLindelof f (⟨c, left_mem_Icc.2 hce⟩ : Icc c e) x (2 * C * h) 0
      (C + K * (2 * C * h)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun t ht => (hlip t ⟨hac.trans ht.1, ht.2.trans heb⟩).lipschitzOnWith
    · exact fun y _ => (hcont y).mono (Icc_subset_Icc hac heb)
    · intro t ht y hy
      have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.trans heb⟩
      have hy' : dist y x ≤ 2 * (C : ℝ) * (h : ℝ) := by
        have := mem_closedBall.1 hy
        push_cast at this
        exact this
      have h1 : ‖f t y - f t x‖ ≤ (K : ℝ) * (2 * (C : ℝ) * (h : ℝ)) := by
        have := (hlip t ht').dist_le_mul y x
        rw [dist_eq_norm] at this
        exact this.trans (mul_le_mul_of_nonneg_left hy' K.coe_nonneg)
      have h2 := norm_le_norm_add_norm_sub' (f t y) (f t x)
      have h3 := hC t ht'
      push_cast
      linarith
    · show ((C + K * (2 * C * h) : ℝ≥0) : ℝ) * max (e - c) (c - c) ≤
        ((2 * C * h : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [sub_self, max_eq_left (sub_nonneg.2 hce), ← hh]
      push_cast
      have hCh : 0 ≤ (C : ℝ) * (h : ℝ) := mul_nonneg C.coe_nonneg h.coe_nonneg
      nlinarith [mul_le_mul_of_nonneg_left hstep hCh]
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

theorem min_add_sub_min_le {x δ b : ℝ} (hδ : 0 ≤ δ) : min (x + δ) b - min x b ≤ δ := by
  rcases le_total x b with h | h
  · rw [min_eq_left h]
    linarith [min_le_left (x + δ) b]
  · rw [min_eq_right h]
    linarith [min_le_right (x + δ) b]

/-- **Global existence.** A field that is Lipschitz in the state, uniformly on
`[a, b]`, and continuous in time has a trajectory on `[a, b]` through every
initial value. -/
theorem exists_solution_Icc {f : ℝ → E → E} {K : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (hcont : ∀ x, ContinuousOn (fun t => f t x) (Icc a b)) (x₀ : E) :
    ∃ α : ℝ → E, α a = x₀ ∧ ∀ t ∈ Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hden : (0 : ℝ) < 2 * (K : ℝ) + 1 := by linarith
  have hδ0 : (0 : ℝ) < 1 / (2 * (K : ℝ) + 1) := by positivity
  have hKδ : (K : ℝ) * (1 / (2 * (K : ℝ) + 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ hden (by norm_num)]
    linarith
  have key : ∀ n : ℕ, ∃ α : ℝ → E, α a = x₀ ∧
      ∀ t ∈ Icc a (min (a + n * (1 / (2 * (K : ℝ) + 1))) b),
        HasDerivWithinAt α (f t (α t)) (Icc a (min (a + n * (1 / (2 * (K : ℝ) + 1))) b)) t := by
    intro n
    induction n with
    | zero =>
      have h0 : min (a + ((0 : ℕ) : ℝ) * (1 / (2 * (K : ℝ) + 1))) b = a := by
        rw [Nat.cast_zero, zero_mul, add_zero, min_eq_left hab]
      rw [h0]
      exact exists_local_solution hlip hcont le_rfl le_rfl hab
        (by rw [sub_self, mul_zero]; norm_num) x₀
    | succ n ih =>
      obtain ⟨α, hα0, hα⟩ := ih
      have hcast : a + ((n + 1 : ℕ) : ℝ) * (1 / (2 * (K : ℝ) + 1)) =
          a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1)) + 1 / (2 * (K : ℝ) + 1) := by
        push_cast
        ring
      rw [hcast]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) * (1 / (2 * (K : ℝ) + 1)) :=
        mul_nonneg (Nat.cast_nonneg n) hδ0.le
      have hac : a ≤ min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b :=
        le_min (by linarith) hab
      have hce : min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b ≤
          min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1)) + 1 / (2 * (K : ℝ) + 1)) b :=
        min_le_min (by linarith) le_rfl
      have hstep : (K : ℝ) *
          (min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1)) + 1 / (2 * (K : ℝ) + 1)) b
            - min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b) ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left (min_add_sub_min_le hδ0.le) hK0).trans hKδ
      obtain ⟨β, hβ0, hβ⟩ := exists_local_solution hlip hcont hac hce (min_le_right _ _) hstep
        (α (min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b))
      refine ⟨fun u => if u ≤ min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b then α u else β u,
        ?_, ?_⟩
      · show (if a ≤ min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b then α a else β a) = x₀
        rw [ite_eq_left hac]
        exact hα0
      · refine hasDerivWithinAt_glue hα hβ (fun u hu => ite_eq_left hu.2) fun u hu => ?_
        rcases eq_or_lt_of_le hu.1 with h | h
        · rw [← h]
          show (if min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b ≤
              min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b then
            α (min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b)
            else β (min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b)) =
            β (min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b)
          rw [ite_eq_left le_rfl, hβ0]
        · exact ite_eq_right (not_le.2 h)
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / (1 / (2 * (K : ℝ) + 1)))
  obtain ⟨α, hα0, hα⟩ := key n
  have hb : min (a + (n : ℝ) * (1 / (2 * (K : ℝ) + 1))) b = b := by
    have := (div_le_iff₀ hδ0).1 hn
    exact min_eq_right (by linarith)
  rw [hb] at hα
  exact ⟨α, hα0, hα⟩

end Calabi
