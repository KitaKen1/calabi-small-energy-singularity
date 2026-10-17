import Calabi.Certificate.PowerBound
import Mathlib.Tactic.Ring

namespace Calabi.Certificate

noncomputable def shootingRadius : ℝ := 1 / 10 ^ 12

noncomputable def endpointError : ℝ :=
  40000000 * (1 / 10 ^ 24) +
  260001 * (1 / 10 ^ 38 + (1 / 1000) * shootingRadius ^ 2) +
  3 * 130000000 * (1001 / 1000) * (10 * shootingRadius) ^ 2

theorem endpointError_nonneg : 0 ≤ endpointError := by
  norm_num [endpointError, shootingRadius]

theorem endpointError_lt : endpointError < (4 / 100) * shootingRadius := by
  norm_num [endpointError, shootingRadius]

theorem tube_bootstrap :
    3 * ((269 / 100) * shootingRadius + endpointError) +
      3 * (1001 / 1000) * (10 * shootingRadius) ^ 2 / (7 / 100) ^ 3 <
      10 * shootingRadius := by
  norm_num [endpointError, shootingRadius]

theorem tail_self_map :
    (4 / 10 ^ 22 : ℝ) + (23 / 100) * (16 / 100) * shootingRadius +
      (39 / 100) * (1 / 10) * shootingRadius < (1 / 10) * shootingRadius := by
  norm_num [shootingRadius]

theorem shooting_self_map : (4 / 100 : ℝ) + (8 / 100) < 1 := by norm_num

theorem perturbed_product_sums_bound {δ : ℝ} (h : δ < 1 / 10 ^ 8) :
    39000000 + 576 * δ < 40000000 ∧
    127000000 + 55 * δ / (7 / 100) ^ 3 < 130000000 := by
  have e : 55 * δ / (7 / 100 : ℝ) ^ 3 = (55000000 / 343) * δ := by ring
  have h' : δ < 1 / 100000000 := by
    have e8 : (1 : ℝ) / 10 ^ 8 = 1 / 100000000 := by norm_num
    rwa [e8] at h
  rw [e]
  constructor <;> linarith

theorem perturbed_product_sums :
    39000000 + 576 * transferError < 40000000 ∧
    127000000 + 55 * transferError / (7 / 100) ^ 3 < 130000000 :=
  perturbed_product_sums_bound transferError_lt

end Calabi.Certificate
