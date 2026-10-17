import Calabi.Certificate.Dyadic
import Mathlib.Tactic.LinearCombination

namespace Calabi.Certificate.Dyadic

def inv (scale : ℤ) (a : Interval) : Interval :=
  ⟨scale ^ 2 / a.hi, -((-scale ^ 2) / a.lo)⟩

/-- The profile recurrence only takes reciprocals of strictly positive intervals. -/
theorem inv_positive_sound {scale : ℤ} (hs : 0 < scale) {a : Interval}
    (ha : 0 < a.lo) {x : ℝ} (hx : Contains scale a x) :
    Contains scale (inv scale a) x⁻¹ := by
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hlo : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hxpos : 0 < x := by
    have hprod : 0 < (scale : ℝ) * x := hlo.trans_le hx.1
    exact (mul_pos_iff_of_pos_left hsR).mp hprod
  have hhiR : (0 : ℝ) < a.hi := (mul_pos hsR hxpos).trans_le hx.2
  have hhi : 0 < a.hi := by exact_mod_cast hhiR
  have hrd := round_down (scale ^ 2) a.hi hhi
  have hru := round_up (scale ^ 2) a.lo ha
  have hlow : ((scale ^ 2 / a.hi : ℤ) : ℝ) ≤ (scale : ℝ) ^ 2 / (a.hi : ℝ) := by
    apply (le_div_iff₀ hhiR).mpr
    simpa only [Int.cast_pow] using hrd
  have hupp : (scale : ℝ) ^ 2 / (a.lo : ℝ) ≤
      (-((-scale ^ 2) / a.lo : ℤ) : ℝ) := by
    apply (div_le_iff₀ hlo).mpr
    simpa only [Int.cast_pow] using hru
  have hid : (scale : ℝ) ^ 2 / ((scale : ℝ) * x) = (scale : ℝ) * x⁻¹ := by
    rw [div_eq_iff (ne_of_gt (mul_pos hsR hxpos))]
    have h1 : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hxpos)
    linear_combination (-(scale : ℝ) ^ 2) * h1
  unfold Contains inv
  simp only [Int.cast_neg]
  constructor
  · change ((scale ^ 2 / a.hi : ℤ) : ℝ) ≤ _
    calc
      _ ≤ (scale : ℝ) ^ 2 / (a.hi : ℝ) := hlow
      _ ≤ (scale : ℝ) ^ 2 / ((scale : ℝ) * x) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hsR hxpos) hx.2
      _ = _ := hid
  · change _ ≤ (-((-scale ^ 2) / a.lo : ℤ) : ℝ)
    calc
      _ = (scale : ℝ) ^ 2 / ((scale : ℝ) * x) := hid.symm
      _ ≤ (scale : ℝ) ^ 2 / (a.lo : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hlo hx.1
      _ ≤ _ := hupp

end Calabi.Certificate.Dyadic
