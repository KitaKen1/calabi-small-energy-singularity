import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The linear problem at the origin

In the variable `r = s^{3/2}` and with `D = r d/dr` the profile equation reads

  `(27/8) (D - 1)(D + 6)(D + 7)(p - d) + r² p / (1 + p) = 0`.

The solution of `(D - 1)(D + 6)(D + 7) w = r² f` that is `O(r²)` at the origin
is `w = r² K0 f`, where `K0 f` is a combination of the averages
`T e f r = ∫₀¹ tᵉ f(t r) dt`, `e = 0, 7, 8`: on monomials,
`K0 (x ↦ xʲ) r = rʲ / ((j+1)(j+8)(j+9))`. The combinations `K1`, `K2` give
`D w` and `D² w` in the same way. No derivative of `f` is involved, and nothing
is singular at `r = 0`.
-/

open Set

namespace Calabi.Origin

/-- `T e f r = ∫₀¹ tᵉ f(t r) dt`. -/
noncomputable def T (e : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ e * f (t * r)

theorem continuous_integrand {f : ℝ → ℝ} (hf : Continuous f) (e : ℕ) (r : ℝ) :
    Continuous fun t : ℝ => t ^ e * f (t * r) :=
  (continuous_id.pow e).mul (hf.comp (continuous_id.mul continuous_const))

theorem abs_T_le {f : ℝ → ℝ} (hf : Continuous f) {M r : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |f (t * r)| ≤ M) (e : ℕ) : |T e f r| ≤ M / ((e : ℝ) + 1) := by
  have hc := continuous_integrand hf e r
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have h1 : |∫ t in (0 : ℝ)..1, t ^ e * f (t * r)| ≤ ∫ t in (0 : ℝ)..1, |t ^ e * f (t * r)| :=
    intervalIntegral.abs_integral_le_integral_abs h01
  have h2 : ∫ t in (0 : ℝ)..1, |t ^ e * f (t * r)| ≤ ∫ t in (0 : ℝ)..1, M * t ^ e := by
    refine intervalIntegral.integral_mono_on h01 (hc.abs.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow e)).intervalIntegrable _ _) fun t ht => ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 e), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (pow_nonneg ht.1 e)
  have h3 : ∫ t in (0 : ℝ)..1, M * t ^ e = M / ((e : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow, one_pow,
      zero_pow (Nat.succ_ne_zero e), sub_zero, mul_one_div]
  unfold T
  linarith

theorem T_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (e : ℕ) (r : ℝ) :
    T e f r - T e g r = T e (fun x => f x - g x) r := by
  unfold T
  rw [← intervalIntegral.integral_sub ((continuous_integrand hf e r).intervalIntegrable _ _)
    ((continuous_integrand hg e r).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

theorem continuous_T {f : ℝ → ℝ} (hf : Continuous f) (e : ℕ) : Continuous (T e f) := by
  unfold T
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r t => t ^ e * f (t * r)) (by fun_prop) 0 1

/-- Only the values of `f` between `0` and `r` matter. -/
theorem T_congr {f g : ℝ → ℝ} {r : ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, f (t * r) = g (t * r)) (e : ℕ) :
    T e f r = T e g r := by
  unfold T
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  show t ^ e * f (t * r) = t ^ e * g (t * r)
  rw [h t ht]

theorem T_pow (e j : ℕ) (r : ℝ) : T e (fun x => x ^ j) r = r ^ j / ((j + e + 1 : ℕ) : ℝ) := by
  unfold T
  have h : ∀ t : ℝ, t ^ e * (t * r) ^ j = r ^ j * t ^ (j + e) := fun t => by
    rw [mul_pow, pow_add]
    ring
  simp only [h]
  rw [intervalIntegral.integral_const_mul, integral_pow, one_pow,
    zero_pow (Nat.succ_ne_zero (j + e)), sub_zero, mul_one_div]
  push_cast
  rfl

theorem T_sum (e : ℕ) (c : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    T e (fun x => ∑ j ∈ Finset.range n, c j * x ^ j) r =
      ∑ j ∈ Finset.range n, c j * (r ^ j / ((j + e + 1 : ℕ) : ℝ)) := by
  have h : ∀ t : ℝ, t ^ e * ∑ j ∈ Finset.range n, c j * (t * r) ^ j =
      ∑ j ∈ Finset.range n, c j * (t ^ e * (t * r) ^ j) := fun t => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold T
  simp only [h]
  have hint : ∀ j ∈ Finset.range n, IntervalIntegrable
      (fun t : ℝ => c j * (t ^ e * (t * r) ^ j)) MeasureTheory.volume 0 1 := fun j _ =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact T_pow e j r

/-- `r² K0 f` is the solution of `(D - 1)(D + 6)(D + 7) w = r² f`. -/
noncomputable def K0 (f : ℝ → ℝ) (r : ℝ) : ℝ := T 0 f r / 56 - T 7 f r / 7 + T 8 f r / 8

/-- `r² K1 f = D (r² K0 f)`. -/
noncomputable def K1 (f : ℝ → ℝ) (r : ℝ) : ℝ := T 0 f r / 56 + 6 / 7 * T 7 f r - 7 / 8 * T 8 f r

/-- `r² K2 f = D² (r² K0 f)`. -/
noncomputable def K2 (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  T 0 f r / 56 - 36 / 7 * T 7 f r + 49 / 8 * T 8 f r

theorem abs_K_le {f : ℝ → ℝ} (hf : Continuous f) {M r : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |f (t * r)| ≤ M) :
    |K0 f r| ≤ 25 / 504 * M ∧ |K1 f r| ≤ 2 / 9 * M ∧ |K2 f r| ≤ 169 / 126 * M := by
  have h0 := abs_le.1 (abs_T_le hf hM 0)
  have h7 := abs_le.1 (abs_T_le hf hM 7)
  have h8 := abs_le.1 (abs_T_le hf hM 8)
  norm_num at h0 h7 h8
  unfold K0 K1 K2
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> linarith [h0.1, h0.2, h7.1,
    h7.2, h8.1, h8.2]

theorem K_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    K0 f r - K0 g r = K0 (fun x => f x - g x) r ∧ K1 f r - K1 g r = K1 (fun x => f x - g x) r ∧
      K2 f r - K2 g r = K2 (fun x => f x - g x) r := by
  have h0 := T_sub hf hg 0 r
  have h7 := T_sub hf hg 7 r
  have h8 := T_sub hf hg 8 r
  unfold K0 K1 K2
  rw [← h0, ← h7, ← h8]
  refine ⟨by ring, by ring, by ring⟩

theorem K_congr {f g : ℝ → ℝ} {r : ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, f (t * r) = g (t * r)) :
    K0 f r = K0 g r ∧ K1 f r = K1 g r ∧ K2 f r = K2 g r := by
  unfold K0 K1 K2
  rw [T_congr h 0, T_congr h 7, T_congr h 8]
  exact ⟨rfl, rfl, rfl⟩

theorem continuous_K {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (K0 f) ∧ Continuous (K1 f) ∧ Continuous (K2 f) := by
  have h0 := continuous_T hf 0
  have h7 := continuous_T hf 7
  have h8 := continuous_T hf 8
  unfold K0 K1 K2
  exact ⟨((h0.div_const 56).sub (h7.div_const 7)).add (h8.div_const 8),
    ((h0.div_const 56).add (continuous_const.mul h7)).sub (continuous_const.mul h8),
    ((h0.div_const 56).sub (continuous_const.mul h7)).add (continuous_const.mul h8)⟩

theorem K_sum (c : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    K0 (fun x => ∑ j ∈ Finset.range n, c j * x ^ j) r =
        ∑ j ∈ Finset.range n, c j * r ^ j / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) ∧
      K1 (fun x => ∑ j ∈ Finset.range n, c j * x ^ j) r =
        ∑ j ∈ Finset.range n,
          c j * r ^ j * ((j : ℝ) + 2) / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) ∧
      K2 (fun x => ∑ j ∈ Finset.range n, c j * x ^ j) r =
        ∑ j ∈ Finset.range n,
          c j * r ^ j * ((j : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) := by
  have term : ∀ j : ℕ, ((j + 0 + 1 : ℕ) : ℝ) = (j : ℝ) + 1 ∧ ((j + 7 + 1 : ℕ) : ℝ) = (j : ℝ) + 8 ∧
      ((j + 8 + 1 : ℕ) : ℝ) = (j : ℝ) + 9 := fun j => by
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring
  unfold K0 K1 K2
  rw [T_sum, T_sum, T_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨e0, e7, e8⟩ := term j
    rw [e0, e7, e8]
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
    have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
    field_simp
    ring
  · rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨e0, e7, e8⟩ := term j
    rw [e0, e7, e8]
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
    have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
    field_simp
    ring
  · rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨e0, e7, e8⟩ := term j
    rw [e0, e7, e8]
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
    have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
    field_simp
    ring

/-- The source of a polynomial: `-(27/8) (D - 1)(D + 6)(D + 7) q / r²` for
`q = ∑ aᵢ rⁱ`. -/
noncomputable def polySource (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    -(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) * a (j + 2)) * x ^ j

/-- **A polynomial solves its own equation.** With the source `polySource`, a
polynomial is recovered from its first two coefficients by `K0`, and its
`D`-derivatives by `K1`, `K2`. -/
theorem poly_solution (a : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ∑ i ∈ Finset.range (n + 2), a i * r ^ i =
        a 0 + a 1 * r - 8 / 27 * r ^ 2 * K0 (polySource a n) r ∧
      ∑ i ∈ Finset.range (n + 2), (i : ℝ) * a i * r ^ i =
        a 1 * r - 8 / 27 * r ^ 2 * K1 (polySource a n) r ∧
      ∑ i ∈ Finset.range (n + 2), (i : ℝ) ^ 2 * a i * r ^ i =
        a 1 * r - 8 / 27 * r ^ 2 * K2 (polySource a n) r := by
  obtain ⟨k0, k1, k2⟩ := K_sum
    (fun j => -(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) * a (j + 2))) n r
  have hsrc : polySource a n = fun x => ∑ j ∈ Finset.range n,
      -(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) * a (j + 2)) * x ^ j := rfl
  rw [hsrc, k0, k1, k2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
    have : ∀ j ∈ Finset.range n, a (j + 1 + 1) * r ^ (j + 1 + 1) =
        -(8 / 27 * r ^ 2 * (-(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9))
          * a (j + 2)) * r ^ j / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)))) := by
      intro j _
      have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
      have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    ring
  · rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
    have : ∀ j ∈ Finset.range n, ((j + 1 + 1 : ℕ) : ℝ) * a (j + 1 + 1) * r ^ (j + 1 + 1) =
        -(8 / 27 * r ^ 2 * (-(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9))
          * a (j + 2)) * r ^ j * ((j : ℝ) + 2)
            / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)))) := by
      intro j _
      have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
      have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    push_cast
    ring
  · rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
    have : ∀ j ∈ Finset.range n,
        ((j + 1 + 1 : ℕ) : ℝ) ^ 2 * a (j + 1 + 1) * r ^ (j + 1 + 1) =
        -(8 / 27 * r ^ 2 * (-(27 / 8 * (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9))
          * a (j + 2)) * r ^ j * ((j : ℝ) + 2) ^ 2
            / (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)))) := by
      intro j _
      have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have h8 : (j : ℝ) + 8 ≠ 0 := by positivity
      have h9 : (j : ℝ) + 9 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    push_cast
    ring

end Calabi.Origin
