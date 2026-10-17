import Calabi.Shot.Core
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Algebra behind the residual polynomials

The residual polynomials of `Calabi.Shot.Core` are the defects of the profile
equation and of its linearisation, multiplied by positive factors. These are
the identities, stated for real numbers.
-/

namespace Calabi.Shot

theorem le_ceilDiv_mul (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have h1 := Nat.div_add_mod (a + (c + 1 - 1)) (c + 1)
  have h2 := Nat.mod_lt (a + (c + 1 - 1)) (Nat.succ_pos c)
  have h3 : c + 1 - 1 = c := by omega
  rw [h3] at h1 h2 ⊢
  nlinarith

/-- The residual of the profile polynomial is its defect times
`S² · 4 σ³ H³ (1 + P)`, with `P = e0 / S` and `d / S` the parameter. -/
theorem resP_identity {S σ H d e0 e1 e2 e3 : ℝ} (hS : S ≠ 0) (hσ : σ ≠ 0) (hH : H ≠ 0)
    (hu : S + e0 ≠ 0) :
    H ^ 3 * ((S + e0) * (567 * d + (4 * σ ^ 3 * e3 + 84 * σ ^ 2 * e2 + 337 * σ * e1
        - 567 * e0))) + 4 * S * (σ ^ 3 * e0) =
      S ^ 2 * (4 * σ ^ 3 * H ^ 3 * (1 + e0 / S)) *
        (e3 / S + 21 / σ * (e2 / S) + 337 / (4 * σ ^ 2) * (e1 / S)
          - 567 / (4 * σ ^ 3) * (e0 / S - d / S) + e0 / S / (1 + e0 / S) / H ^ 3) := by
  have h1 : 1 + e0 / S = (S + e0) / S := by
    field_simp
  rw [h1]
  field_simp
  ring1

/-- The residual of a tangent polynomial is its linearised defect times
`S² Su · 4 σ³ H³ (1 + P)²`. -/
theorem resU_identity {S Su σ H φ e0 u0 u1 u2 u3 : ℝ} (hS : S ≠ 0) (hSu : Su ≠ 0)
    (hσ : σ ≠ 0) (hH : H ≠ 0) (hu : S + e0 ≠ 0) :
    H ^ 3 * ((S + e0) * (S + e0) * (567 * Su * φ + (4 * σ ^ 3 * u3 + 84 * σ ^ 2 * u2
        + 337 * σ * u1 - 567 * u0))) + 4 * S * S * (σ ^ 3 * u0) =
      S ^ 2 * Su * (4 * σ ^ 3 * H ^ 3 * (1 + e0 / S) ^ 2) *
        (u3 / Su + 21 / σ * (u2 / Su) + 337 / (4 * σ ^ 2) * (u1 / Su)
          - 567 / (4 * σ ^ 3) * (u0 / Su - φ) + u0 / Su / (1 + e0 / S) ^ 2 / H ^ 3) := by
  have h1 : 1 + e0 / S = (S + e0) / S := by
    field_simp
  rw [h1]
  field_simp
  ring1

/-- If `x = c y` with `0 < c₀ ≤ c` and `|x| ≤ n`, then `|y| ≤ n / c₀`. -/
theorem abs_le_div_of_eq_mul {x y c c₀ n : ℝ} (h : x = c * y) (hc₀ : 0 < c₀) (hc : c₀ ≤ c)
    (hx : |x| ≤ n) : |y| ≤ n / c₀ := by
  have hcpos : 0 < c := hc₀.trans_le hc
  have hxy : |x| = c * |y| := by rw [h, abs_mul, abs_of_pos hcpos]
  rw [le_div_iff₀ hc₀]
  have h0 : 0 ≤ |y| := abs_nonneg y
  nlinarith [mul_le_mul_of_nonneg_right hc h0]

end Calabi.Shot
