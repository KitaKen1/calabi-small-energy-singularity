import OAI.Analysis.AncientFlat.Regularity.InitialSchauder
import OAI.Analysis.AncientFlat.Regularity.InitialJetModel
import OAI.Analysis.AncientFlat.Regularity.SourceHolderEvolution

/-!
# Bundled coefficients and sources for the reused parabolic library

The existence theorems of the reused library take the coefficient of
`u_t + a Δ² u = f` as a continuous map `ℝ → (V →ᵇ [κ, Λ])` and the source as a
bounded continuous map `ℝ → C₀(V, ℂ)`. This file builds these objects from
ordinary functions:

* `c0OfSupport`: a continuous function vanishing outside a ball, in `C₀(V, ℂ)`;
* `sourceMap`: a family `f t` of such functions, bounded and continuous in `t`
  uniformly in `x`;
* `coeffMap`: a family `a t` of continuous functions with values in `[κ, Λ]`,
  Lipschitz in `t` uniformly in `x`.
-/

open Set Filter
open scoped Topology ZeroAtInfty BoundedContinuousFunction

namespace Calabi.FlatZero

/-- Continuity from a modulus of continuity. -/
theorem continuous_of_modulus {X : Type*} [PseudoMetricSpace X] {g : ℝ → X} {ω : ℝ → ℝ}
    (hω : Tendsto ω (𝓝 0) (𝓝 0)) (h : ∀ t s, dist (g t) (g s) ≤ ω |t - s|) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
    have h2 : Continuous fun s : ℝ => |s - t| := continuous_abs.comp (continuous_id.sub continuous_const)
    have h3 := h2.tendsto t
    simpa using h3
  exact squeeze_zero (fun s => dist_nonneg) (fun s => h s t) (hω.comp h1)

/-- A bounded Lipschitz quantity is Hölder. -/
theorem lip_bdd_holder {L B γ d y : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (h1 : y ≤ L * d) (h2 : y ≤ B) : y ≤ max L B * d ^ γ := by
  rcases le_or_gt d 1 with h | h
  · have hd1 : d ≤ d ^ γ := by
      have h3 := Real.rpow_le_rpow_of_exponent_ge' hd h hγ.le hγ1
      rwa [Real.rpow_one] at h3
    calc y ≤ L * d := h1
      _ ≤ L * d ^ γ := mul_le_mul_of_nonneg_left hd1 hL
      _ ≤ max L B * d ^ γ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd γ)
  · have hd1 : 1 ≤ d ^ γ := Real.one_le_rpow h.le hγ.le
    calc y ≤ B := h2
      _ ≤ B * d ^ γ := le_mul_of_one_le_right hB hd1
      _ ≤ max L B * d ^ γ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd γ)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A continuous function vanishing outside a ball, as an element of `C₀(V, ℂ)`. -/
noncomputable def c0OfSupport (g : V → ℂ) (hc : Continuous g) (ρ : ℝ)
    (h0 : ∀ x, ρ ≤ ‖x‖ → g x = 0) : C₀(V, ℂ) :=
  ⟨⟨g, hc⟩, (HasCompactSupport.intro (isCompact_closedBall (0 : V) ρ) (fun x hx => h0 x (by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le))).is_zero_at_infty⟩

@[simp] theorem c0OfSupport_apply (g : V → ℂ) (hc : Continuous g) (ρ : ℝ)
    (h0 : ∀ x, ρ ≤ ‖x‖ → g x = 0) (x : V) : c0OfSupport g hc ρ h0 x = g x := rfl

/-- A family of continuous functions vanishing outside a ball, bounded and
continuous in time uniformly in space, as a bounded continuous map into
`C₀(V, ℂ)`. -/
noncomputable def sourceMap (f : ℝ → V → ℂ) (hc : ∀ t, Continuous (f t)) (ρ : ℝ)
    (h0 : ∀ t x, ρ ≤ ‖x‖ → f t x = 0) (B : ℝ) (hB : ∀ t x, ‖f t x‖ ≤ B) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝 0) (𝓝 0)) (ht : ∀ t s x, ‖f t x - f s x‖ ≤ ω |t - s|) :
    ℝ →ᵇ C₀(V, ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => c0OfSupport (f t) (hc t) ρ (h0 t))
    (continuous_of_modulus hω fun t s => by
      rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
      refine (BoundedContinuousFunction.dist_le ((norm_nonneg _).trans (ht t s 0))).mpr
        fun x => ?_
      rw [dist_eq_norm]
      exact ht t s x)
    B (fun t => by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (hB t 0))).mpr
        fun x => hB t x)

@[simp] theorem sourceMap_apply (f : ℝ → V → ℂ) (hc : ∀ t, Continuous (f t)) (ρ : ℝ)
    (h0 : ∀ t x, ρ ≤ ‖x‖ → f t x = 0) (B : ℝ) (hB : ∀ t x, ‖f t x‖ ≤ B) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝 0) (𝓝 0)) (ht : ∀ t s x, ‖f t x - f s x‖ ≤ ω |t - s|) (t : ℝ) (x : V) :
    sourceMap f hc ρ h0 B hB ω hω ht t x = f t x := rfl

/-- A family of continuous functions with values in `[κ, Λ]`, Lipschitz in time
uniformly in space, as a continuous map into the bounded continuous
functions. -/
noncomputable def coeffMap (a : ℝ → V → ℝ) (κ Λ : ℝ) (ha : ∀ t x, a t x ∈ Icc κ Λ)
    (hc : ∀ t, Continuous (a t)) (L : ℝ) (hL : ∀ t s x, |a t x - a s x| ≤ L * |t - s|) :
    C(ℝ, V →ᵇ Icc κ Λ) :=
  ⟨fun t => (BoundedContinuousFunction.ofNormedAddCommGroup (a t) (hc t) (max |κ| |Λ|)
      (fun x => abs_le_max_abs_abs (ha t x).1 (ha t x).2)).codRestrict (Icc κ Λ) (ha t),
    continuous_of_modulus (ω := fun r => L * r)
      (by
        have h : Continuous fun r : ℝ => L * r := continuous_const.mul continuous_id
        have h' := h.tendsto 0
        simpa using h')
      fun t s => by
        refine (BoundedContinuousFunction.dist_le ((abs_nonneg _).trans (hL t s 0))).mpr
          fun x => ?_
        change dist (a t x) (a s x) ≤ L * |t - s|
        rw [Real.dist_eq]
        exact hL t s x⟩

@[simp] theorem coeffMap_apply (a : ℝ → V → ℝ) (κ Λ : ℝ) (ha : ∀ t x, a t x ∈ Icc κ Λ)
    (hc : ∀ t, Continuous (a t)) (L : ℝ) (hL : ∀ t s x, |a t x - a s x| ≤ L * |t - s|)
    (t : ℝ) (x : V) : ((coeffMap a κ Λ ha hc L hL) t x).val = a t x := rfl

end Calabi.FlatZero
