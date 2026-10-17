import Calabi.Correction.TwoPointJets
import Calabi.Correction.EulerJets
import Calabi.Correction.RadialChart
import OAI.Analysis.AncientFlat.Evolution.TraceFour

/-!
# The terms of order at most three of the chart operator

`lowerOp m u` collects the terms of the chart operator `chartOp m`
(`RadialChart.lean`) other than `(1 - |z|²)² Δ²`:

  `-(4 + 2m)(1 - |z|²) E Δ u + ((160 + 2m)|z|² - 160) Δ u + m² E² u + 112 m E u + 2880 u`.

On a bounded part of the chart (`|z| ≤ 1`, scale at most `S`) it is bounded, in
the weighted two-point sense with the weight `w - 3`, by the jets of `u` of
order at most three (`lowerOp_bound`). In the approximate inverse these terms
are errors: the jets of order at most three of a zero-data solution are small
(Lemma 4.5 of the manuscript).

* `WH.apply_tuple`: a weighted jet evaluated at a tuple of vectors of norm at
  most one that depends on the point in a `1`-Lipschitz way;
* `WH.smul_lip`: multiplication by a bounded Lipschitz function of the point;
* `LowBound`: the class of operators bounded in this way, with its closure
  properties.
-/

open Set
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicCommutator Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A distance below the scale costs at most the bound of the scale. -/
theorem scale_dist_le {s d α w S : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hds : d ≤ s) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hS : s ≤ S) : s ^ w * d ≤ S * (s ^ (w - α) * d ^ α) := by
  have h1 := scale_interp (w := w + 1) hs hd hds hα hα1
  rw [Real.rpow_one] at h1
  have e1 : s ^ (w + 1 - 1) = s ^ w := by
    congr 1
    ring
  have e2 : s ^ (w + 1 - α) = s * s ^ (w - α) := by
    have e : w + 1 - α = 1 + (w - α) := by ring
    rw [e, Real.rpow_add hs, Real.rpow_one]
  rw [e1, e2] at h1
  have h2 : 0 ≤ s ^ (w - α) * d ^ α :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hd _)
  calc s ^ w * d ≤ s * s ^ (w - α) * d ^ α := h1
    _ = s * (s ^ (w - α) * d ^ α) := by ring
    _ ≤ S * (s ^ (w - α) * d ^ α) := mul_le_mul_of_nonneg_right hS h2

section Basic

variable {α a c w M S : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}

/-- **A weighted jet evaluated at a tuple of small vectors that depends on the
point.** -/
theorem WH.apply_tuple {k : ℕ} {φ : V × ℝ → V [×k]→L[ℝ] E} {m : V × ℝ → Fin k → V}
    (hφ : WH α a s Ω w M φ) (hsc : IsScale a c s Ω) (hM : 0 ≤ M) (ha1 : a ≤ 1) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hS : ∀ p ∈ Ω, s p ≤ S) (hm1 : ∀ p ∈ Ω, ∀ i, ‖m p i‖ ≤ 1)
    (hmd : ∀ p ∈ Ω, ∀ q ∈ Ω, ‖m p - m q‖ ≤ ‖p.1 - q.1‖) :
    WH α a s Ω w ((1 + c ^ |w| * k * S) * M) (fun p => φ p (m p)) := by
  have hc0 : 0 ≤ c ^ |w| := Real.rpow_nonneg (by linarith [hsc.one_le]) _
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hsc.pos p hp
    have hS0 : 0 ≤ S := hsp.le.trans (hS p hp)
    have h1 := (norm_apply_le_of_le_one (φ p) (hm1 p hp)).trans (hφ.1 p hp)
    have h0 : 0 ≤ M * s p ^ w := mul_nonneg hM (Real.rpow_nonneg hsp.le _)
    have hK : 0 ≤ c ^ |w| * k * S := mul_nonneg (mul_nonneg hc0 (Nat.cast_nonneg _)) hS0
    calc ‖φ p (m p)‖ ≤ M * s p ^ w := h1
      _ = 1 * (M * s p ^ w) := (one_mul _).symm
      _ ≤ (1 + c ^ |w| * k * S) * (M * s p ^ w) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (1 + c ^ |w| * k * S) * M * s p ^ w := by ring
  · have hsp := hsc.pos p hp
    have hd0 := pdist_nonneg p q
    have hxd : ‖p.1 - q.1‖ ≤ pdist p q := by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
    have hds : pdist p q ≤ s p := by
      have := mul_le_mul_of_nonneg_right ha1 hsp.le
      linarith
    have e : φ p (m p) - φ q (m q) = (φ p - φ q) (m p) + (φ q (m p) - φ q (m q)) := by
      rw [ContinuousMultilinearMap.sub_apply]
      abel
    have b1 : ‖(φ p - φ q) (m p)‖ ≤ M * s p ^ (w - α) * pdist p q ^ α :=
      (norm_apply_le_of_le_one _ (hm1 p hp)).trans (hφ.2 p hp q hq hd)
    have h0 : 0 ≤ M * (c ^ |w| * s p ^ w) :=
      mul_nonneg hM (mul_nonneg hc0 (Real.rpow_nonneg hsp.le _))
    have hφq : ‖φ q‖ ≤ M * (c ^ |w| * s p ^ w) :=
      (hφ.1 q hq).trans (mul_le_mul_of_nonneg_left (hsc.rpow_le hp hq hd w) hM)
    have b2 : ‖φ q (m p) - φ q (m q)‖ ≤ M * (c ^ |w| * s p ^ w) * k * pdist p q :=
      (norm_apply_sub_le_of_le_one (φ q) (hm1 p hp) (hm1 q hq)).trans
        (mul_le_mul (mul_le_mul_of_nonneg_right hφq (Nat.cast_nonneg _))
          ((hmd p hp q hq).trans hxd) (norm_nonneg _) (mul_nonneg h0 (Nat.cast_nonneg _)))
    have hint := scale_dist_le (w := w) hsp hd0 hds hα hα1 (hS p hp)
    have hMck : 0 ≤ M * c ^ |w| * k := mul_nonneg (mul_nonneg hM hc0) (Nat.cast_nonneg _)
    rw [e]
    calc ‖(φ p - φ q) (m p) + (φ q (m p) - φ q (m q))‖
        ≤ ‖(φ p - φ q) (m p)‖ + ‖φ q (m p) - φ q (m q)‖ := norm_add_le _ _
      _ ≤ M * s p ^ (w - α) * pdist p q ^ α + M * (c ^ |w| * s p ^ w) * k * pdist p q :=
        add_le_add b1 b2
      _ = M * s p ^ (w - α) * pdist p q ^ α + M * c ^ |w| * k * (s p ^ w * pdist p q) := by ring
      _ ≤ M * s p ^ (w - α) * pdist p q ^ α
          + M * c ^ |w| * k * (S * (s p ^ (w - α) * pdist p q ^ α)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hint hMck)
      _ = (1 + c ^ |w| * k * S) * M * s p ^ (w - α) * pdist p q ^ α := by ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Multiplication by a bounded Lipschitz function of the point.** -/
theorem WH.smul_lip {A : ℝ} {κ : V × ℝ → ℝ} {f : V × ℝ → E} (hf : WH α a s Ω w M f)
    (hpos : ∀ p ∈ Ω, 0 < s p) (hM : 0 ≤ M) (hA : 0 ≤ A) (ha1 : a ≤ 1) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hS : ∀ p ∈ Ω, s p ≤ S) (hκ0 : ∀ p ∈ Ω, |κ p| ≤ A)
    (hκ1 : ∀ p ∈ Ω, ∀ q ∈ Ω, |κ p - κ q| ≤ A * ‖p.1 - q.1‖) :
    WH α a s Ω w (A * (1 + S) * M) (fun p => κ p • f p) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hpos p hp
    have hS0 : 0 ≤ S := hsp.le.trans (hS p hp)
    have h0 : 0 ≤ M * s p ^ w := mul_nonneg hM (Real.rpow_nonneg hsp.le _)
    rw [norm_smul, Real.norm_eq_abs]
    calc |κ p| * ‖f p‖ ≤ A * (M * s p ^ w) :=
          mul_le_mul (hκ0 p hp) (hf.1 p hp) (norm_nonneg _) hA
      _ ≤ A * (1 + S) * (M * s p ^ w) := by
        have : 0 ≤ A * S * (M * s p ^ w) := mul_nonneg (mul_nonneg hA hS0) h0
        nlinarith
      _ = A * (1 + S) * M * s p ^ w := by ring
  · have hsp := hpos p hp
    have hd0 := pdist_nonneg p q
    have hxd : ‖p.1 - q.1‖ ≤ pdist p q := by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
    have hds : pdist p q ≤ s p := by
      have := mul_le_mul_of_nonneg_right ha1 hsp.le
      linarith
    have e : κ p • f p - κ q • f q = (κ p - κ q) • f p + κ q • (f p - f q) := by
      rw [sub_smul, smul_sub]
      abel
    have b1 : ‖(κ p - κ q) • f p‖ ≤ A * pdist p q * (M * s p ^ w) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ((hκ1 p hp q hq).trans (mul_le_mul_of_nonneg_left hxd hA)) (hf.1 p hp)
        (norm_nonneg _) (mul_nonneg hA hd0)
    have b2 : ‖κ q • (f p - f q)‖ ≤ A * (M * s p ^ (w - α) * pdist p q ^ α) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hκ0 q hq) (hf.2 p hp q hq hd) (norm_nonneg _) hA
    have hint := scale_dist_le (w := w) hsp hd0 hds hα hα1 (hS p hp)
    rw [e]
    calc ‖(κ p - κ q) • f p + κ q • (f p - f q)‖
        ≤ ‖(κ p - κ q) • f p‖ + ‖κ q • (f p - f q)‖ := norm_add_le _ _
      _ ≤ A * pdist p q * (M * s p ^ w) + A * (M * s p ^ (w - α) * pdist p q ^ α) :=
        add_le_add b1 b2
      _ = A * M * (s p ^ w * pdist p q) + A * (M * s p ^ (w - α) * pdist p q ^ α) := by ring
      _ ≤ A * M * (S * (s p ^ (w - α) * pdist p q ^ α))
          + A * (M * s p ^ (w - α) * pdist p q ^ α) :=
        add_le_add (mul_le_mul_of_nonneg_left hint (mul_nonneg hA hM)) le_rfl
      _ = A * (1 + S) * M * s p ^ (w - α) * pdist p q ^ α := by ring

end Basic

/-! ### Operators bounded by the jets of order at most three -/

/-- `T` is bounded, with the weight `w - 3`, by the jets of order at most
three, on every bounded part of the chart where the scale is at most `S` and
changes at most by the factor `c`. The constant depends only on `c`, `w`, `S`
(and on `T`). -/
def LowBound (c w S : ℝ) (T : (V → E) → V → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (α a B : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) (u : ℝ → V → E),
    IsScale a c s Ω → 0 ≤ B → a ≤ 1 → 0 ≤ α → α ≤ 1 → (∀ p ∈ Ω, s p ≤ S) →
    (∀ p ∈ Ω, ‖p.1‖ ≤ 1) → (∀ t, ContDiff ℝ 3 (u t)) → WJ α a s Ω w B 3 u →
    WH α a s Ω (w - 3) (C * B) (fun p => T (u p.2) p.1)

section Low

variable {c w S : ℝ} {T T' : (V → E) → V → E}

theorem LowBound.add (h : LowBound c w S T) (h' : LowBound c w S T') :
    LowBound c w S (fun u z => T u z + T' u z) := by
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨C', hC', h'⟩ := h'
  refine ⟨C + C', add_nonneg hC hC', fun α a B s Ω u hsc hB ha hα hα1 hS hz hus hu => ?_⟩
  have h1 := (h α a B s Ω u hsc hB ha hα hα1 hS hz hus hu).add
    (h' α a B s Ω u hsc hB ha hα hα1 hS hz hus hu)
  have e : (C + C') * B = C * B + C' * B := by ring
  rw [e]
  exact h1

/-- Multiplication by a function of the point that is bounded by `A` and
`A`-Lipschitz on the unit ball. -/
theorem LowBound.smul_coef (h : LowBound c w S T) (hS : 0 ≤ S) {A : ℝ} (hA : 0 ≤ A)
    {κ : V → ℝ} (hκ0 : ∀ z : V, ‖z‖ ≤ 1 → |κ z| ≤ A)
    (hκ1 : ∀ z z' : V, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → |κ z - κ z'| ≤ A * ‖z - z'‖) :
    LowBound c w S (fun u z => κ z • T u z) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨A * (1 + S) * C, by positivity, fun α a B s Ω u hsc hB ha hα hα1 hS' hz hus hu => ?_⟩
  have h1 := (h α a B s Ω u hsc hB ha hα hα1 hS' hz hus hu).smul_lip (κ := fun p => κ p.1)
    hsc.pos (mul_nonneg hC hB) hA ha hα hα1 hS' (fun p hp => hκ0 p.1 (hz p hp))
    (fun p hp q hq => hκ1 p.1 q.1 (hz p hp) (hz q hq))
  have e : A * (1 + S) * C * B = A * (1 + S) * (C * B) := by ring
  rw [e]
  exact h1

theorem LowBound.congr (h : LowBound c w S T) (hT : ∀ (u : V → E), ContDiff ℝ 3 u → ∀ z,
    T' u z = T u z) : LowBound c w S T' := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun α a B s Ω u hsc hB ha hα hα1 hS hz hus hu => ?_⟩
  exact (h α a B s Ω u hsc hB ha hα hα1 hS hz hus hu).congr fun p _ => hT (u p.2) (hus p.2) p.1

theorem LowBound.zero : LowBound c w S (fun (_ : V → E) (_ : V) => (0 : E)) := by
  refine ⟨0, le_rfl, fun α a B s Ω u hsc hB ha hα hα1 hS hz hus hu => ?_⟩
  exact WH.zero (le_of_eq (zero_mul B).symm) hsc.pos

theorem LowBound.sum {ι : Type*} (t : Finset ι) {T : ι → (V → E) → V → E}
    (h : ∀ i ∈ t, LowBound c w S (T i)) : LowBound c w S (fun u z => ∑ i ∈ t, T i u z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact LowBound.zero
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LowBound.const_smul (h : LowBound c w S T) (k : ℝ) :
    LowBound c w S (fun u z => k • T u z) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨|k| * C, mul_nonneg (abs_nonneg k) hC,
    fun α a B s Ω u hsc hB ha hα hα1 hS hz hus hu => ?_⟩
  have h1 := (h α a B s Ω u hsc hB ha hα hα1 hS hz hus hu).const_smul k
  rw [mul_assoc]
  exact h1

/-- A jet of order `j ≤ 3` evaluated at a tuple of small vectors. -/
theorem lowBound_tuple (c w S : ℝ) (hS : 0 ≤ S) {j : ℕ} (hj : j ≤ 3) (m : V → Fin j → V)
    (hm1 : ∀ z : V, ‖z‖ ≤ 1 → ∀ i, ‖m z i‖ ≤ 1) (hmd : ∀ z z' : V, ‖m z - m z'‖ ≤ ‖z - z'‖) :
    LowBound c w S (fun (u : V → E) z => iteratedFDeriv ℝ j u z (m z)) := by
  have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have hc0 : 0 ≤ max c 1 ^ |w - j| := Real.rpow_nonneg (le_max_of_le_right zero_le_one) _
  refine ⟨(1 + max c 1 ^ |w - j| * j * S) * S ^ ((3 : ℝ) - j),
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hc0 (Nat.cast_nonneg _)) hS))
      (Real.rpow_nonneg hS _), fun α a B s Ω u hsc hB ha hα hα1 hS' hz hus hu => ?_⟩
  have hc : max c 1 = c := max_eq_left hsc.one_le
  rw [hc]
  have h1 := (hu j hj).apply_tuple (m := fun p => m p.1) hsc hB ha hα hα1 hS'
    (fun p hp i => hm1 p.1 (hz p hp) i) (fun p _ q _ => hmd p.1 q.1)
  have hc0' : 0 ≤ c ^ |w - (j : ℝ)| := Real.rpow_nonneg (by linarith [hsc.one_le]) _
  have hK : 0 ≤ (1 + c ^ |w - (j : ℝ)| * j * S) * B :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hc0' (Nat.cast_nonneg _)) hS)) hB
  have h2 := h1.weight (w' := w - 3) hK hsc.pos hS' (by linarith)
  have e : w - (j : ℝ) - (w - 3) = 3 - j := by ring
  rw [e] at h2
  refine h2.mono hsc.pos (le_of_eq ?_)
  ring

end Low

/-! ### The chart operator -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A polynomial of degree one in `|z|²` is bounded and Lipschitz on the unit
ball. -/
theorem coef_bound (p q : ℝ) :
    (∀ z : V, ‖z‖ ≤ 1 → |p + q * ‖z‖ ^ 2| ≤ |p| + 2 * |q|) ∧
      ∀ z z' : V, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
        |(p + q * ‖z‖ ^ 2) - (p + q * ‖z'‖ ^ 2)| ≤ (|p| + 2 * |q|) * ‖z - z'‖ := by
  constructor
  · intro z hz
    have h1 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    have h2 : |q * ‖z‖ ^ 2| ≤ |q| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
      exact mul_le_of_le_one_right (abs_nonneg q) h1
    have h3 := abs_add_le p (q * ‖z‖ ^ 2)
    linarith [abs_nonneg q]
  · intro z z' hz hz'
    have h1 : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have e : (p + q * ‖z‖ ^ 2) - (p + q * ‖z'‖ ^ 2)
        = q * ((‖z‖ - ‖z'‖) * (‖z‖ + ‖z'‖)) := by ring
    rw [e, abs_mul, abs_mul]
    have h2 : |‖z‖ + ‖z'‖| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      linarith
    have h3 : |‖z‖ - ‖z'‖| * |‖z‖ + ‖z'‖| ≤ ‖z - z'‖ * 2 :=
      mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg q)
    have h5 := mul_nonneg (abs_nonneg p) (norm_nonneg (z - z'))
    nlinarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The principal coefficient `(1 - |z|²)²` is bounded and Lipschitz on the
unit ball. -/
theorem coef0_bound :
    (∀ z : V, ‖z‖ ≤ 1 → |(1 - ‖z‖ ^ 2) ^ 2| ≤ 4) ∧
      ∀ z z' : V, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
        |(1 - ‖z‖ ^ 2) ^ 2 - (1 - ‖z'‖ ^ 2) ^ 2| ≤ 4 * ‖z - z'‖ := by
  constructor
  · intro z hz
    have h1 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.2 h1), sq_nonneg ‖z‖]
  · intro z z' hz hz'
    have h0 := norm_nonneg z
    have h0' := norm_nonneg z'
    have h1 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ h0 hz
    have h1' : ‖z'‖ ^ 2 ≤ 1 := pow_le_one₀ h0' hz'
    have hd : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have e : (1 - ‖z‖ ^ 2) ^ 2 - (1 - ‖z'‖ ^ 2) ^ 2
        = (‖z'‖ - ‖z‖) * ((‖z‖ + ‖z'‖) * (2 - ‖z‖ ^ 2 - ‖z'‖ ^ 2)) := by ring
    rw [e, abs_mul, abs_sub_comm]
    have h2 : |(‖z‖ + ‖z'‖) * (2 - ‖z‖ ^ 2 - ‖z'‖ ^ 2)| ≤ 4 := by
      rw [abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
      calc (‖z‖ + ‖z'‖) * (2 - ‖z‖ ^ 2 - ‖z'‖ ^ 2) ≤ 2 * 2 :=
            mul_le_mul (by linarith) (by linarith [sq_nonneg ‖z‖, sq_nonneg ‖z'‖])
              (by linarith) (by norm_num)
        _ = 4 := by norm_num
    calc |‖z‖ - ‖z'‖| * |(‖z‖ + ‖z'‖) * (2 - ‖z‖ ^ 2 - ‖z'‖ ^ 2)|
        ≤ ‖z - z'‖ * 4 := mul_le_mul hd h2 (abs_nonneg _) (norm_nonneg _)
      _ = 4 * ‖z - z'‖ := by ring

/-- The terms of order at most three of the chart operator `chartOp m`. -/
noncomputable def lowOp (m : ℝ) (u : V → ℝ) (z : V) : ℝ :=
  -((4 + 2 * m) * (1 - ‖z‖ ^ 2)) * eulerE (Δ u) z + ((160 + 2 * m) * ‖z‖ ^ 2 - 160) * Δ u z
    + m ^ 2 * eulerE (eulerE u) z + 112 * m * eulerE u z + 2880 * u z

theorem chartOp_eq_lowOp (m : ℝ) (u : V → ℝ) (z : V) :
    chartOp m u z = (1 - ‖z‖ ^ 2) ^ 2 * Δ (Δ u) z + lowOp m u z := by
  have e1 : euler (Δ u) z = eulerE (Δ u) z := rfl
  have e2 : euler (euler u) z = eulerE (eulerE u) z := rfl
  have e3 : euler u z = eulerE u z := rfl
  unfold chartOp lowOp
  rw [e2, e1, e3]
  ring

/-- **The terms of order at most three of the chart operator are bounded by
the jets of order at most three.** -/
theorem lowBound_lowOp (c w S m : ℝ) (hS : 0 ≤ S) : LowBound c w S (lowOp (V := V) m) := by
  have hT3 : LowBound c w S (fun (u : V → ℝ) z =>
      ∑ i, iteratedFDeriv ℝ 3 u z
        ![z, stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i]) :=
    LowBound.sum Finset.univ fun i _ => lowBound_tuple c w S hS (j := 3) le_rfl
      (fun z => ![z, stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i])
      (fun z hz i' => by
        fin_cases i' <;> simp [hz, OrthonormalBasis.norm_eq_one])
      (fun z z' => by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i' => ?_
        fin_cases i' <;> simp)
  have hT2 : LowBound c w S (fun (u : V → ℝ) z =>
      ∑ i, iteratedFDeriv ℝ 2 u z
        ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i]) :=
    LowBound.sum Finset.univ fun i _ => lowBound_tuple c w S hS (j := 2) (by norm_num)
      (fun _ => ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i])
      (fun z hz i' => by
        fin_cases i' <;> simp [OrthonormalBasis.norm_eq_one])
      (fun z z' => by simp)
  have hT2z : LowBound c w S (fun (u : V → ℝ) z => iteratedFDeriv ℝ 2 u z ![z, z]) :=
    lowBound_tuple c w S hS (j := 2) (by norm_num) (fun z => ![z, z])
      (fun z hz i' => by fin_cases i' <;> simp [hz])
      (fun z z' => by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i' => ?_
        fin_cases i' <;> simp)
  have hT1 : LowBound c w S (fun (u : V → ℝ) z => iteratedFDeriv ℝ 1 u z (fun _ => z)) :=
    lowBound_tuple c w S hS (j := 1) (by norm_num) (fun z _ => z) (fun z hz _ => hz)
      (fun z z' => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => le_rfl)
  have hT0 : LowBound c w S (fun (u : V → ℝ) z => iteratedFDeriv ℝ 0 u z (fun _ => z)) :=
    lowBound_tuple c w S hS (j := 0) (by norm_num) (fun z _ => z) (fun z hz _ => hz)
      (fun z z' => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => le_rfl)
  obtain ⟨hk1a, hk1b⟩ := coef_bound (V := V) (-(4 + 2 * m)) (4 + 2 * m)
  obtain ⟨hk2a, hk2b⟩ := coef_bound (V := V) (-160) (160 + 2 * m)
  have hA1 : (0 : ℝ) ≤ |(-(4 + 2 * m))| + 2 * |4 + 2 * m| := by positivity
  have hA2 : (0 : ℝ) ≤ |(-160 : ℝ)| + 2 * |160 + 2 * m| := by positivity
  have h := ((((hT3.smul_coef hS hA1
      (κ := fun z => -(4 + 2 * m) + (4 + 2 * m) * ‖z‖ ^ 2) hk1a hk1b).add
    (hT2.smul_coef hS hA2 (κ := fun z => -160 + (160 + 2 * m) * ‖z‖ ^ 2) hk2a hk2b)).add
    ((hT2z.add hT1).const_smul (m ^ 2))).add (hT1.const_smul (112 * m))).add
    (hT0.const_smul 2880)
  refine h.congr fun u hu z => ?_
  rw [← eulerE_laplacian hu z, ← laplacian_eq_sum u z, ← eulerE_eq u z,
    ← eulerE_eulerE (hu.of_le (by norm_num)) z, iteratedFDeriv_zero_apply]
  unfold lowOp
  simp only [smul_eq_mul]
  ring

/-- The Laplacian of a function of class `C⁴` is of class `C²`. -/
theorem contDiff_two_laplacian {u : V → E} (hu : ContDiff ℝ 4 u) : ContDiff ℝ 2 (Δ u) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine ContDiff.sum fun i _ => ?_
  have h2 : ContDiff ℝ 2 (iteratedFDeriv ℝ 2 u) := hu.iteratedFDeriv_right (by norm_num)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) E
    ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i]).contDiff.comp h2

/-- The trace of a four-jet that gives the bilaplacian of a real function. -/
noncomputable def bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ V), ∑ j : Fin (Module.finrank ℝ V),
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => V) ℝ
      ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i,
        stdOrthonormalBasis ℝ V j, stdOrthonormalBasis ℝ V j]

theorem bilaplacian_eq_bilapL {u : V → ℝ} (hu : ContDiff ℝ 4 u) (z : V) :
    Δ (Δ u) z = bilapL (iteratedFDeriv ℝ 4 u z) := by
  have hc : ContDiff ℝ 4 (Complex.ofRealCLM ∘ u) := Complex.ofRealCLM.contDiff.comp hu
  have h1 := OAI.ClassicalIBP.bilaplacian_eq_traceFour (Complex.ofRealCLM ∘ u) hc z
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hu.contDiffAt (i := 4) (by norm_num)] at h1
  have e1 := (hu.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)).contDiffAt.laplacian_CLM_comp_left_nhds
    (l := Complex.ofRealCLM) (x := z)
  rw [(InnerProductSpace.laplacian_congr_nhds e1).eq_of_nhds,
    (contDiff_two_laplacian hu).contDiffAt.laplacian_CLM_comp_left] at h1
  have h2 : OAI.ClassicalIBP.traceFour
      (Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ 4 u z))
      = ((bilapL (iteratedFDeriv ℝ 4 u z) : ℝ) : ℂ) := by
    simp [OAI.ClassicalIBP.traceFour, bilapL]
  rw [h2] at h1
  exact Complex.ofReal_injective h1

section Operator

variable {c w S : ℝ}

/-- **The chart operator on functions with weighted jets of order four** has
the weight `w - 4`. -/
theorem chartOp_WH (c w S m : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α a B : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) (u : ℝ → V → ℝ),
      IsScale a c s Ω → 0 ≤ B → a ≤ 1 → 0 ≤ α → α ≤ 1 → (∀ p ∈ Ω, s p ≤ S) →
      (∀ p ∈ Ω, ‖p.1‖ ≤ 1) → (∀ t, ContDiff ℝ 4 (u t)) → WJ α a s Ω w B 4 u →
      WH α a s Ω (w - 4) (C * B) (fun p => chartOp m (u p.2) p.1) := by
  obtain ⟨C₁, hC₁, H₁⟩ := lowBound_lowOp (V := V) c w S m hS
  refine ⟨4 * (1 + S) * ‖(bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)‖ + C₁ * S, by positivity,
    fun α a B s Ω u hsc hB ha hα hα1 hS' hz hus hu => ?_⟩
  have e4 : w - ((4 : ℕ) : ℝ) = w - 4 := by norm_num
  have h4 := (hu 4 le_rfl).clm bilapL
  rw [e4] at h4
  have hp := h4.smul_lip (κ := fun p => (1 - ‖p.1‖ ^ 2) ^ 2) hsc.pos
    (mul_nonneg (norm_nonneg _) hB) (by norm_num : (0 : ℝ) ≤ 4) ha hα hα1 hS'
    (fun p hp => coef0_bound.1 p.1 (hz p hp))
    (fun p hp q hq => coef0_bound.2 p.1 q.1 (hz p hp) (hz q hq))
  have hl := (H₁ α a B s Ω u hsc hB ha hα hα1 hS' hz (fun t => (hus t).of_le (by norm_num))
    (hu.of_le (by norm_num))).weight (w' := w - 4) (mul_nonneg hC₁ hB) hsc.pos hS'
    (by linarith)
  have e1 : w - 3 - (w - 4) = 1 := by ring
  rw [e1, Real.rpow_one] at hl
  have h := hp.add hl
  refine (h.congr fun p _ => ?_).mono hsc.pos (le_of_eq ?_)
  · show chartOp m (u p.2) p.1
        = (1 - ‖p.1‖ ^ 2) ^ 2 • bilapL (iteratedFDeriv ℝ 4 (u p.2) p.1) + lowOp m (u p.2) p.1
    rw [chartOp_eq_lowOp, bilaplacian_eq_bilapL (hus p.2), smul_eq_mul]
  · ring

/-- **The commutator of the chart operator with a cut-off** is bounded by the
jets of order at most three. -/
theorem chartOp_comm_WH (c w S m : ℝ) (hc : 1 ≤ c) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α a A B : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) (χ u : ℝ → V → ℝ),
      IsScale a c s Ω → 0 ≤ A → 0 ≤ B → a ≤ 1 → 0 ≤ α → α ≤ 1 → (∀ p ∈ Ω, s p ≤ S) →
      (∀ p ∈ Ω, ‖p.1‖ ≤ 1) → (∀ t, ContDiff ℝ 4 (χ t)) → (∀ t, ContDiff ℝ 4 (u t)) →
      WJ α a s Ω 0 A 4 χ → WJ α a s Ω w B 3 u →
      WH α a s Ω (w - 4) (C * (A * B))
        (fun p => chartOp m (fun z => χ p.2 z • u p.2 z) p.1
          - χ p.2 p.1 • chartOp m (u p.2) p.1) := by
  obtain ⟨C₁, hC₁, H₁⟩ := lowBound_lowOp (V := V) c w S m hS
  have hc0 : (0 : ℝ) ≤ c := by linarith
  refine ⟨4 * (1 + S) * ‖(bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)‖ * (2 ^ 4 * (1 + c ^ (4 : ℝ)))
      + C₁ * (2 ^ 3 * (1 + c ^ ((3 : ℕ) : ℝ))) * S + (1 + c ^ |(0 : ℝ)|) * C₁ * S,
    by positivity, ?_⟩
  intro α a A B s Ω χ u hsc hA hB ha hα hα1 hS' hz hχs hus hχ hu
  have hχ3 : ∀ t, ContDiff ℝ 3 (χ t) := fun t => (hχs t).of_le (by norm_num)
  have hu3 : ∀ t, ContDiff ℝ 3 (u t) := fun t => (hus t).of_le (by norm_num)
  -- the principal part
  have hcomm := commutator_WH hsc hA hB hχs hus hχ hu
  have h1 := (hcomm.clm bilapL).smul_lip (κ := fun p => (1 - ‖p.1‖ ^ 2) ^ 2) hsc.pos
    (by positivity) (by norm_num : (0 : ℝ) ≤ 4) ha hα hα1 hS'
    (fun p hp => coef0_bound.1 p.1 (hz p hp))
    (fun p hp q hq => coef0_bound.2 p.1 q.1 (hz p hp) (hz q hq))
  -- the lower part of the product
  have hχu := WJ.smul hsc hA hB hχ3 hu3 (hχ.of_le (by norm_num)) hu
  have hK3 : 0 ≤ 2 ^ 3 * (1 + c ^ ((3 : ℕ) : ℝ)) * A * B := by positivity
  have h2 := (H₁ α a _ s Ω (fun t x => χ t x • u t x) hsc hK3 ha hα hα1 hS' hz
    (fun t => (hχ3 t).smul (hu3 t)) hχu).weight (w' := w - 4) (mul_nonneg hC₁ hK3) hsc.pos
    hS' (by linarith)
  -- the product with the lower part
  have hlow := H₁ α a B s Ω u hsc hB ha hα hα1 hS' hz hu3 hu
  have h3 := (WH.smul hsc hA (mul_nonneg hC₁ hB) hχ.value hlow).weight (w' := w - 4)
    (by positivity) hsc.pos hS' (by linarith)
  have e1 : w - 3 - (w - 4) = 1 := by ring
  have e2 : (0 : ℝ) + (w - 3) - (w - 4) = 1 := by ring
  rw [e1, Real.rpow_one] at h2
  rw [e2, Real.rpow_one] at h3
  have h := h1.add (h2.sub h3)
  refine (h.congr fun p _ => ?_).mono hsc.pos (le_of_eq ?_)
  · show chartOp m (fun z => χ p.2 z • u p.2 z) p.1 - χ p.2 p.1 • chartOp m (u p.2) p.1
        = (1 - ‖p.1‖ ^ 2) ^ 2 • bilapL (commutator (χ p.2) (u p.2) p.1)
          + (lowOp m (fun z => χ p.2 z • u p.2 z) p.1 - χ p.2 p.1 • lowOp m (u p.2) p.1)
    have hχu4 : ContDiff ℝ 4 (fun z => χ p.2 z • u p.2 z) := (hχs p.2).smul (hus p.2)
    rw [chartOp_eq_lowOp, chartOp_eq_lowOp, bilaplacian_eq_bilapL hχu4,
      bilaplacian_eq_bilapL (hus p.2)]
    unfold OAI.ParabolicCommutator.commutator
    rw [map_sub, map_smul]
    simp only [smul_eq_mul]
    ring
  · ring

end Operator

/-! ### The chart operator is local and additive -/

open Filter Topology in
/-- The chart operator at a point depends on the germ of the function. -/
theorem chartOp_congr (m : ℝ) {u v : V → ℝ} {z : V} (h : u =ᶠ[𝓝 z] v) :
    chartOp m u z = chartOp m v z := by
  have hL : Δ u =ᶠ[𝓝 z] Δ v := InnerProductSpace.laplacian_congr_nhds h
  have hE : euler u =ᶠ[𝓝 z] euler v := h.fderiv.mono fun y hy => by
    show fderiv ℝ u y y = fderiv ℝ v y y
    rw [hy]
  have e0 : Δ (Δ u) z = Δ (Δ v) z := (InnerProductSpace.laplacian_congr_nhds hL).eq_of_nhds
  have e1 : euler (Δ u) z = euler (Δ v) z := by
    unfold euler
    rw [hL.fderiv_eq]
  have e2 : euler (euler u) z = euler (euler v) z := by
    show fderiv ℝ (euler u) z z = fderiv ℝ (euler v) z z
    rw [hE.fderiv_eq]
  have e3 : euler u z = euler v z := by
    unfold euler
    rw [h.fderiv_eq]
  unfold chartOp
  rw [e0, e1, hL.eq_of_nhds, e2, e3, h.eq_of_nhds]

theorem chartOp_zero_fun (m : ℝ) (z : V) : chartOp m (fun _ : V => (0 : ℝ)) z = 0 := by
  have e : euler (fun _ : V => (0 : ℝ)) = fun _ => 0 := by
    funext y
    simp [euler]
  unfold chartOp
  rw [InnerProductSpace.laplacian_const]
  have e' : (0 : V → ℝ) = fun _ => 0 := rfl
  rw [e', InnerProductSpace.laplacian_const, e', e, e]
  simp

open Filter Topology in
/-- The chart operator of a function that vanishes near the point. -/
theorem chartOp_eq_zero_of_eventually (m : ℝ) {u : V → ℝ} {z : V}
    (h : u =ᶠ[𝓝 z] fun _ => 0) : chartOp m u z = 0 := by
  rw [chartOp_congr m h, chartOp_zero_fun]

theorem laplacian_add_fun {u v : V → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    Δ (fun y => u y + v y) = fun y => Δ u y + Δ v y := by
  funext y
  exact hu.contDiffAt.laplacian_add hv.contDiffAt

omit [FiniteDimensional ℝ V] in
theorem euler_add_fun {u v : V → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    euler (fun y => u y + v y) = fun y => euler u y + euler v y := by
  funext y
  unfold euler
  rw [fderiv_fun_add (hu y) (hv y)]
  rfl

omit [FiniteDimensional ℝ V] in
theorem differentiable_euler {u : V → ℝ} (hu : ContDiff ℝ 2 u) : Differentiable ℝ (euler u) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  exact (h1.differentiable one_ne_zero).clm_apply differentiable_id

/-- **The chart operator is additive** on functions of class `C⁴`. -/
theorem chartOp_add (m : ℝ) {u v : V → ℝ} (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v) (z : V) :
    chartOp m (fun y => u y + v y) z = chartOp m u z + chartOp m v z := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hLu : ContDiff ℝ 2 (Δ u) := contDiff_two_laplacian hu
  have hLv : ContDiff ℝ 2 (Δ v) := contDiff_two_laplacian hv
  have hLu1 : ContDiff ℝ 1 (Δ u) := hLu.of_le (by norm_num)
  have hLv1 : ContDiff ℝ 1 (Δ v) := hLv.of_le (by norm_num)
  have eL := laplacian_add_fun hu2 hv2
  have eLL : Δ (Δ fun y => u y + v y) = fun y => Δ (Δ u) y + Δ (Δ v) y := by
    rw [eL]
    exact laplacian_add_fun hLu hLv
  have eE := euler_add_fun (hu1.differentiable one_ne_zero) (hv1.differentiable one_ne_zero)
  have eEL : euler (Δ fun y => u y + v y) = fun y => euler (Δ u) y + euler (Δ v) y := by
    rw [eL]
    exact euler_add_fun (hLu1.differentiable one_ne_zero) (hLv1.differentiable one_ne_zero)
  have eEE : euler (euler fun y => u y + v y)
      = fun y => euler (euler u) y + euler (euler v) y := by
    rw [eE]
    exact euler_add_fun (differentiable_euler hu2) (differentiable_euler hv2)
  unfold chartOp
  rw [eLL, eEL, eL, eEE, eE]
  ring

end Calabi.Weighted
