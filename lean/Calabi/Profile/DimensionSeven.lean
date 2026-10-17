import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calabi.ProfileSeven

def complexDimension : ℕ := 7
def realDimension : ℕ := 2 * complexDimension
def flatDimension : ℕ := 2 * complexDimension + 4
def sphereDimension : ℕ := flatDimension + 5

theorem dimensions : realDimension = 14 ∧ flatDimension = 18 ∧ sphereDimension = 23 := by
  norm_num [realDimension, flatDimension, sphereDimension, complexDimension]

noncomputable def profilePolynomial (z : ℝ) : ℝ := (z - 1) * (z + 6) * (z + 7)

theorem profilePolynomial_expand (z : ℝ) :
    profilePolynomial z = z ^ 3 + 12 * z ^ 2 + 29 * z - 42 := by
  unfold profilePolynomial
  ring

noncomputable def compactPolynomial (z : ℝ) : ℝ := (-z / 4 + 10) * (-z / 4 + 18)

theorem compactPolynomial_expand (z : ℝ) :
    compactPolynomial z = z ^ 2 / 16 - 7 * z + 180 := by
  unfold compactPolynomial
  ring

/-- The cubic used for the constant-coefficient tail at s = 56. -/
noncomputable def tailPolynomial (z : ℝ) : ℝ :=
  z ^ 3 + (21 / 112) * z ^ 2 + (337 / 25088) * z + (1 - 567 / 1404928)

theorem tail_discriminant_negative :
    (21 / 112 : ℝ) ^ 2 - 3 * (337 / 25088) < 0 := by norm_num

theorem tail_root_bracket :
    tailPolynomial (-(1061676856305 / 10 ^ 12)) < 0 ∧
    0 < tailPolynomial (-(1061676856304 / 10 ^ 12)) := by
  norm_num [tailPolynomial]

end Calabi.ProfileSeven
