import Calabi.Correction.Bundle
import OAI.Analysis.AncientFlat.Evolution.OrthogonalCalculus
import OAI.Analysis.AncientFlat.Profile.RotationCore
import OAI.Analysis.AncientFlat.Profile.RadialRealCore

/-!
# Rotations and conjugation of solutions of the flat problem

A solution of `u_t + a Δ² u = f` in the sense of the reused library
(`SourceEvolves`, with no zeroth-order term) is carried to a solution by a
linear isometry `R` of the space when `a` and `f` are invariant under `R`, and
by complex conjugation when `f` is real. With the uniqueness theorem of the
library this shows that the solution with zero initial data is radial when
the data are radial (`zero_data_radial`) and real when the source is real
(`zero_data_realValued`).
-/

open Set Filter
open scoped Topology ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian

namespace Calabi.FlatZero

open OAI OAI.ParametrixEvolution OAI.FlatSymmetry OAI.FlatSimilarity

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable {κ Λ : ℝ} {A : C(ℝ, V →ᵇ Icc κ Λ)} {f : ℝ → C₀(V, ℂ)} {s T : ℝ} {d : C₀(V, ℂ)}
  {u : ℝ → C₀(V, ℂ)}

/-- A rotated solution is a solution of the rotated problem. -/
theorem sourceEvolves_rotated (hu : SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T d u)
    (R : V ≃ₗᵢ[ℝ] V) (hA : ∀ t x, (A t (R x)).val = (A t x).val)
    (hf : ∀ t x, f t (R x) = f t x) :
    SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T (rotate R d) (fun t => rotate R (u t)) := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  refine ⟨congrArg (rotate R) hu.1, ?_, ?_, ?_, ?_⟩
  · exact (rotate R).continuous.comp_continuousOn hu.2.1
  · intro t ht
    exact (hu.2.2.1 t ht).comp R.toContinuousLinearEquiv.contDiff
  · intro t ht
    exact bounded_jets_rotate R _ (hu.2.2.1 t ht) (hu.2.2.2.1 t ht)
  · intro t ht
    obtain ⟨p, hp, hpe⟩ := hu.2.2.2.2 t ht
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) :=
      BoundedContinuousFunction.compContinuousCLM ℂ ℝ (rotMap R)
    refine ⟨Q p, ?_, fun x => ?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t hp using 1
      rfl
    · change p (R x) = f t x - ((A t x).val : ℂ) * Δ (Δ (fun y => u t (R y))) x
        - (0 : C(ℝ, V →ᵇ ℂ)) t x * u t (R x)
      rw [hpe, bilaplacian_rotate R _ (hu.2.2.1 t ht), hf, hA]
      simp

/-- The conjugate of a solution is a solution of the conjugate problem. -/
theorem sourceEvolves_conjugate (hu : SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T d u)
    (hf : ∀ t x, star (f t x) = f t x) :
    SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T (star d) (fun t => star (u t)) := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  refine ⟨congrArg Star.star hu.1, ?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp_continuousOn hu.2.1
  · intro t ht
    exact Complex.conjCLE.contDiff.comp (hu.2.2.1 t ht)
  · intro t ht
    exact bounded_jets_star _ (hu.2.2.2.1 t ht)
  · intro t ht
    obtain ⟨p, hp, hpe⟩ := hu.2.2.2.2 t ht
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) :=
      Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded V
    refine ⟨Q p, ?_, fun x => ?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t hp using 1
      rfl
    · change star (p x) = f t x - ((A t x).val : ℂ) * Δ (Δ (fun y => star (u t y))) x
        - (0 : C(ℝ, V →ᵇ ℂ)) t x * star (u t x)
      rw [hpe, bilaplacian_star]
      have hf' := hf t x
      simp only [Complex.star_def] at hf' ⊢
      simp only [map_sub, map_mul, Complex.conj_ofReal, hf']
      simp

variable [MeasurableSpace V] [BorelSpace V]

/-- **The zero-data solution is radial when the data are radial.** -/
theorem zero_data_radial {C : ℝ} (hu : SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T 0 u)
    (hsT : s ≤ T) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hA2 : ∀ t ∈ Icc s T, ContDiff ℝ 2 (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc s T, ∀ n : ℕ, n ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖ ≤ C)
    (hA : ∀ (R : V ≃ₗᵢ[ℝ] V) t x, (A t (R x)).val = (A t x).val)
    (hf : ∀ (R : V ≃ₗᵢ[ℝ] V) t x, f t (R x) = f t x) :
    ∀ t ∈ Icc s T, Radial (u t : V → ℂ) := by
  intro t ht R x
  have hrot := sourceEvolves_rotated hu R (hA R) (hf R)
  have h0 : rotate R (0 : C₀(V, ℂ)) = 0 := map_zero _
  rw [h0] at hrot
  have h := hrot.unique hu hsT hκ hC (le_refl (0 : ℝ)) (fun t _ => by simp) hA2 hAj t ht
  exact congrArg (fun g : C₀(V, ℂ) => g x) h

/-- **The zero-data solution is real when the source is real.** -/
theorem zero_data_realValued {C : ℝ} (hu : SourceEvolves A (0 : C(ℝ, V →ᵇ ℂ)) f s T 0 u)
    (hsT : s ≤ T) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hA2 : ∀ t ∈ Icc s T, ContDiff ℝ 2 (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc s T, ∀ n : ℕ, n ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖ ≤ C)
    (hf : ∀ t x, star (f t x) = f t x) :
    ∀ t ∈ Icc s T, RealValued (u t : V → ℂ) := by
  intro t ht x
  have hconj := sourceEvolves_conjugate hu hf
  have h0 : star (0 : C₀(V, ℂ)) = 0 := star_zero _
  rw [h0] at hconj
  have h := hconj.unique hu hsT hκ hC (le_refl (0 : ℝ)) (fun t _ => by simp) hA2 hAj t ht
  exact congrArg (fun g : C₀(V, ℂ) => g x) h

end Calabi.FlatZero
