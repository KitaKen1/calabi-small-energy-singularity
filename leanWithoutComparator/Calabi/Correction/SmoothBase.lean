import Calabi.Correction.SmoothOps

/-!
# Membership in the local classes from weighted bounds

The solution of Section 6 is constructed with weighted two-point bounds for a
scale `s` (the parabolic scale `σ` near the point orbit, the constant scale
near the other end). Away from the final time the scale is bounded above and
below, so that the weighted bounds are uniform bounds near every point:

* `WH.to_uniform`: a weighted two-point bound on a set where the scale is
  comparable to one is a uniform two-point bound;
* `Sm.of_WJ`, `Sm.of_WH`: a function with weighted jets is in the local class;
* `Sm.of_vanish`: a function that vanishes on an open set is in the local
  class there;
* `Sm.union`: the local class on a union.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A weighted two-point bound on a set where the scale is comparable to one is
a uniform two-point bound. -/
theorem WH.to_uniform {E : Type*} [NormedAddCommGroup E] {α a w w' M k : ℝ} {s : V × ℝ → ℝ}
    {N : Set (V × ℝ)} {f : V × ℝ → E} (h : WH α a s N w M f) (hM : 0 ≤ M) (ha : 0 < a)
    (hα : 0 ≤ α) (hk : 1 ≤ k) (hs : ∀ p ∈ N, 0 < s p) (h1 : ∀ p ∈ N, s p ≤ k)
    (h2 : ∀ p ∈ N, 1 ≤ k * s p) :
    WH α 1 (fun _ : V × ℝ => (1 : ℝ)) N w'
      (M * k ^ (|w| + |w - α|) * (1 + (1 + (1 : ℝ) ^ |w|) * (a / k) ^ (-α))) f := by
  have hk0 : 0 < k := by linarith
  have h3 := h.scale (s' := fun _ => (1 : ℝ)) hM hk ha.le hs (fun _ _ => one_pos)
    (fun p hp => by rw [mul_one]; exact h1 p hp) h2
  have hM' : 0 ≤ M * k ^ (|w| + |w - α|) := mul_nonneg hM (Real.rpow_nonneg hk0.le _)
  have h4 := h3.radius_ge (a' := 1) (IsScale.const one_pos) hM' (div_pos ha hk0) hα
  exact h4.one_weight

/-- A two-point bound of the values is a bound of the jets of order zero. -/
theorem WJ.zero_of_WH {α a w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} {u : ℝ → V → ℝ}
    (h : WH α a s Ω w M (fun p => u p.2 p.1)) : WJ α a s Ω w M 0 u := by
  intro j hj
  have hj0 : j = 0 := Nat.le_zero.1 hj
  subst hj0
  rw [Nat.cast_zero, sub_zero]
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · show ‖iteratedFDeriv ℝ 0 (u p.2) p.1‖ ≤ M * s p ^ w
    rw [norm_iteratedFDeriv_zero]
    exact h.1 p hp
  · have e : iteratedFDeriv ℝ 0 (u p.2) p.1 - iteratedFDeriv ℝ 0 (u q.2) q.1
        = (continuousMultilinearCurryFin0 ℝ V ℝ).symm (u p.2 p.1 - u q.2 q.1) := by
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        Function.comp_apply, map_sub]
    show ‖iteratedFDeriv ℝ 0 (u p.2) p.1 - iteratedFDeriv ℝ 0 (u q.2) q.1‖
      ≤ M * s p ^ (w - α) * pdist p q ^ α
    rw [e, LinearIsometryEquiv.norm_map]
    exact h.2 p hp q hq hd

/-- **A function with weighted jets is in the local class**, on an open set
where the scale is locally comparable to one. -/
theorem Sm.of_WJ {α a w M : ℝ} {s : V × ℝ → ℝ} {D Ω : Set (V × ℝ)} {k : ℕ} {u : ℝ → V → ℝ}
    (hα : 0 ≤ α) (ha : 0 < a) (hM : 0 ≤ M) (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D)
    (hsD : ∀ p ∈ D, 0 < s p)
    (hloc : ∀ p₀ ∈ Ω, ∃ (K : ℝ) (N₀ : Set (V × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
      ∀ p ∈ N₀ ∩ Ω, s p ≤ K ∧ 1 ≤ K * s p)
    (hsu : ∀ t, ContDiff ℝ k (u t)) (hW : WJ α a s D w M k u) : Sm α Ω k u := by
  intro p₀ hp₀
  obtain ⟨K, N₀, hK, hN₀, hp₀N, hsb⟩ := hloc p₀ hp₀
  have hK0 : 0 < K := by linarith
  have hterm : ∀ j : ℕ, 0 ≤ M * K ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|)
      * (1 + (1 + (1 : ℝ) ^ |w - (j : ℝ)|) * (a / K) ^ (-α)) := fun j => by
    have h1 : 0 ≤ K ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|) := Real.rpow_nonneg hK0.le _
    have h2 : 0 ≤ (a / K) ^ (-α) := Real.rpow_nonneg (div_pos ha hK0).le _
    have h3 : 0 ≤ (1 : ℝ) ^ |w - (j : ℝ)| := Real.rpow_nonneg zero_le_one _
    positivity
  refine ⟨N₀ ∩ Ω, u, ∑ j ∈ Finset.range (k + 1), M * K ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|)
      * (1 + (1 + (1 : ℝ) ^ |w - (j : ℝ)|) * (a / K) ^ (-α)), hN₀.inter hΩ, ⟨hp₀N, hp₀⟩,
    Finset.sum_nonneg fun j _ => hterm j, fun _ _ => rfl, hsu, ?_⟩
  intro j hj
  have h1 := ((hW j hj).restrict (inter_subset_right.trans hΩD)).to_uniform
    (w' := (0 : ℝ) - (j : ℝ)) hM ha hα hK (fun p hp => hsD p (hΩD hp.2))
    (fun p hp => (hsb p hp).1) (fun p hp => (hsb p hp).2)
  exact h1.mono (fun _ _ => one_pos) (Finset.single_le_sum
    (f := fun j : ℕ => M * K ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|)
      * (1 + (1 + (1 : ℝ) ^ |w - (j : ℝ)|) * (a / K) ^ (-α)))
    (fun i _ => hterm i) (Finset.mem_range.2 (by omega)))

/-- A function with a weighted two-point bound is in the local class of order
zero. -/
theorem Sm.of_WH {α a w M : ℝ} {s : V × ℝ → ℝ} {D Ω : Set (V × ℝ)} {u : ℝ → V → ℝ}
    (hα : 0 ≤ α) (ha : 0 < a) (hM : 0 ≤ M) (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D)
    (hsD : ∀ p ∈ D, 0 < s p)
    (hloc : ∀ p₀ ∈ Ω, ∃ (K : ℝ) (N₀ : Set (V × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
      ∀ p ∈ N₀ ∩ Ω, s p ≤ K ∧ 1 ≤ K * s p)
    (hsu : ∀ t, Continuous (u t)) (hW : WH α a s D w M (fun p => u p.2 p.1)) : Sm α Ω 0 u :=
  Sm.of_WJ hα ha hM hΩ hΩD hsD hloc (fun t => by exact_mod_cast contDiff_zero.2 (hsu t))
    (WJ.zero_of_WH hW)

/-- A function that vanishes on an open set is in the local classes there. -/
theorem Sm.of_vanish {α : ℝ} {W : Set V} (hW : IsOpen W) {k : ℕ} {u : ℝ → V → ℝ}
    (hsu : ∀ t, ContDiff ℝ k (u t)) (h0 : ∀ t, ∀ z ∈ W, u t z = 0) :
    Sm α {p : V × ℝ | p.1 ∈ W} k u := by
  intro p₀ hp₀
  refine ⟨{p : V × ℝ | p.1 ∈ W}, u, 0, hW.preimage continuous_fst, hp₀, le_rfl,
    fun _ _ => rfl, hsu, fun j _ => ?_⟩
  refine (WH.zero le_rfl fun _ _ => one_pos).congr fun p hp => ?_
  have hev : u p.2 =ᶠ[𝓝 p.1] fun _ => (0 : ℝ) := by
    filter_upwards [hW.mem_nhds hp] with z hz
    exact h0 p.2 z hz
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
  simp

theorem Sm.union {α : ℝ} {Ω₁ Ω₂ : Set (V × ℝ)} {k : ℕ} {g : ℝ → V → ℝ} (h₁ : Sm α Ω₁ k g)
    (h₂ : Sm α Ω₂ k g) : Sm α (Ω₁ ∪ Ω₂) k g := by
  intro p₀ hp₀
  rcases hp₀ with h | h
  · exact h₁ p₀ h
  · exact h₂ p₀ h

end Calabi.Weighted
