import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Calabi.Certificate

/-- A quantitative binomial bound avoiding expansion of enormous rational powers. -/
theorem pow_mul_one_sub_le_one (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ n * (1 - n * x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
    have hstep : (1 + x) * (1 - ((n : ℝ) + 1) * x) ≤ 1 - n * x := by
      nlinarith [sq_nonneg x, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]
    have hm := mul_le_mul_of_nonneg_left hstep hp
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_two_mul (n : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hnx : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n - 1 ≤ 2 * n * x := by
  have h := pow_mul_one_sub_le_one n hx
  have hp : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
  have hnx0 : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx
  have hp2 : (1 + x) ^ n ≤ 2 := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hnx)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp2) hnx0]

noncomputable def transferError : ℝ :=
  260000 * ((1 + 4 * (1 / 10 ^ 24) * 260000) ^ (576 : ℕ) - 1)

theorem transferError_nonneg : 0 ≤ transferError := by
  unfold transferError
  have h : (1 : ℝ) ≤ (1 + 4 * (1 / 10 ^ 24) * 260000) ^ (576 : ℕ) := by
    exact one_le_pow₀ (by norm_num)
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr h)

theorem scaled_power_bound (n : ℕ) (M x ε : ℝ) (hx : 0 ≤ x)
    (hnx : (n : ℝ) * x ≤ 1 / 2) (hM : 0 ≤ M)
    (hsmall : M * (2 * n * x) < ε) :
    M * ((1 + x) ^ n - 1) < ε := by
  calc
    _ ≤ M * (2 * n * x) :=
      mul_le_mul_of_nonneg_left (pow_sub_one_le_two_mul n hx hnx) hM
    _ < ε := hsmall

theorem transferError_lt : transferError < 1 / 10 ^ 8 :=
  scaled_power_bound 576 260000 (4 * (1 / 10 ^ 24) * 260000) (1 / 10 ^ 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Calabi.Certificate
