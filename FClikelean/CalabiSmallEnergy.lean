/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/

module

public import FormalConjecturesUtil

/-!
# Finite-time singularities of Calabi flow

[OAI26] resolves the following question negatively: does Calabi flow from every
smooth Kähler metric on a compact Kähler manifold exist smoothly for all
positive time? The counterexample lies in the Fubini–Study class of `CP¹⁰`.

References:
- [OAI26] OpenAI, *A finite-time singularity of Calabi flow on projective space* (2026).
  https://github.com/openai/math/tree/main/preprints/A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026
-/

@[expose] public section

open Set
open scoped ContDiff

namespace CalabiFC
noncomputable section

abbrev Aff (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Hom (n : ℕ) := Fin (n + 1) → ℂ

/-- The affine chart with homogeneous coordinate `j` equal to one. -/
def chart {n : ℕ} (j : Fin (n + 1)) (Z : Aff n) : Hom n :=
  Fin.insertNth (α := fun _ => ℂ) j 1 (Z : Fin n → ℂ)

/-- The complex Hessian of a real potential. -/
def levi {n : ℕ} (u : Aff n → ℝ) (Z a b : Aff n) : ℂ :=
  let H (a b : Aff n) := iteratedFDeriv ℝ 2 u Z ![a, b]
  (((H a b + H (Complex.I • a) (Complex.I • b) : ℝ) : ℂ)
    + Complex.I * ((H a (Complex.I • b) - H (Complex.I • a) b : ℝ) : ℂ)) / 4

/-- Local coefficient data for a real `(1,1)`-form; `IsKahlerForm` enforces compatibility. -/
abbrev Form (n : ℕ) := Fin (n + 1) → Aff n → Aff n → Aff n → ℂ

/-- The form `i∂∂̄f`, written in the projective charts. -/
def ddbar {n : ℕ} (f : Hom n → ℝ) : Form n :=
  fun j Z a b => levi (fun W => f (chart j W)) Z a b

/-- The Fubini–Study form with local potential `log(1 + |Z|²)`. -/
def fubiniStudy (n : ℕ) : Form n :=
  fun _ Z a b => levi (fun W : Aff n => Real.log (1 + ‖W‖ ^ 2)) Z a b

/-- A smooth real function on complex projective space. -/
def IsSmoothCP {n : ℕ} (f : Hom n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f {v | v ≠ 0} ∧
    ∀ (c : ℂ) (v : Hom n), c ≠ 0 → f (c • v) = f v

/-- A smooth time-dependent real function on complex projective space. -/
def IsSmoothCPOn {n : ℕ} (T : ℝ) (φ : ℝ → Hom n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun p : ℝ × Hom n => φ p.1 p.2) (Ico 0 T ×ˢ {v | v ≠ 0}) ∧
    ∀ t ∈ Ico 0 T, ∀ (c : ℂ) (v : Hom n), c ≠ 0 → φ t (c • v) = φ t v

/-- Positivity of a real `(1,1)`-form. -/
def Positive {n : ℕ} (η : Form n) : Prop :=
  ∀ (j : Fin (n + 1)) (Z a : Aff n), a ≠ 0 → 0 < (η j Z a a).re

/-- A smooth Kähler form in the Fubini–Study class. -/
def IsKahlerForm {n : ℕ} (ω₀ : Form n) : Prop :=
  (∃ f : Hom n → ℝ, IsSmoothCP f ∧ ω₀ = fubiniStudy n + ddbar f) ∧ Positive ω₀

/-- Scalar curvature `S(η) = tr_η Ric(η)` on the first affine chart. -/
def scal {n : ℕ} (η : Form n) (Z : Aff n) : ℝ :=
  let g (W : Aff n) : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun j k => η 0 W (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
  let H : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun j k => levi (fun W => Real.log ((g W).det.re)) Z
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1);
  -((g Z)⁻¹ * H).trace.re

/-- Equation (1.1) of [OAI26] on `[0,T)`, specialized to the Fubini–Study class. -/
def IsCalabiFlow (n : ℕ) (T : ℝ) (ω₀ : Form n) (φ : ℝ → Hom n → ℝ) : Prop :=
  let ωₜ (t : ℝ) := ω₀ + ddbar (φ t)
  let S_avg : ℝ := n * (n + 1)
  IsKahlerForm ω₀ ∧
    φ 0 = 0 ∧
    IsSmoothCPOn T φ ∧
    (∀ t ∈ Ico 0 T, Positive (ωₜ t)) ∧
    ∀ t ∈ Ico 0 T, ∀ Z : Aff n,
      HasDerivWithinAt (fun s => φ s (chart 0 Z))
        (scal (ωₜ t) Z - S_avg) (Ico 0 T) t

/-- Every smooth Calabi flow extends past each finite endpoint, with the same initial form. -/
def CalabiFlowConjecture (n : ℕ) : Prop :=
  ∀ (T : ℝ) (ω₀ : Form n) (φ : ℝ → Hom n → ℝ), 0 < T → IsCalabiFlow n T ω₀ φ →
    ∃ (T' : ℝ) (ψ : ℝ → Hom n → ℝ), T < T' ∧ IsCalabiFlow n T' ω₀ ψ ∧
      ∀ t ∈ Ico 0 T, ∀ v : Hom n, v ≠ 0 → ψ t v = φ t v

/-- Does every smooth Calabi flow in the Fubini–Study class of `CP¹⁰` extend past each finite time?
The answer is negative [OAI26]. -/
@[category research solved, AMS 53 58]
theorem calabi_flow : answer(False) ↔ CalabiFlowConjecture 10 := by
  sorry

/-- Does every smooth Calabi flow in the Fubini–Study class of `CP⁷` extend past each finite time?
The answer is negative: Kitamura, *Small-energy finite-time singularities of Calabi flow*
(2026), Theorem 1.1 (`PDF/calabi-small-energy.pdf`). -/
@[category research solved, AMS 53 58]
theorem calabi_flow.variants.dimension_seven : answer(False) ↔ CalabiFlowConjecture 7 := by
  sorry

end
end CalabiFC
