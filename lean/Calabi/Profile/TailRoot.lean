import Calabi.Profile.DimensionSeven
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

namespace Calabi.ProfileSeven

theorem tailPolynomial_strictMono : StrictMono tailPolynomial := by
  intro x y hxy
  have hq : 0 < x ^ 2 + x * y + y ^ 2 + (21 / 112) * (x + y) + 337 / 25088 := by
    have hdisc := tail_discriminant_negative
    nlinarith [sq_nonneg (x + y + (2 / 3) * (21 / 112 : ℝ)), sq_nonneg (x - y)]
  have hp := mul_pos (sub_pos.mpr hxy) hq
  have heq : tailPolynomial y - tailPolynomial x =
      (y - x) * (x ^ 2 + x * y + y ^ 2 + (21 / 112) * (x + y) + 337 / 25088) := by
    unfold tailPolynomial
    ring
  linarith

/-- The tail cubic has a unique real root, certified in the rational bracket. -/
theorem tail_root_exists_unique :
    ∃! r : ℝ, tailPolynomial r = 0 := by
  have hc : Continuous tailPolynomial := by unfold tailPolynomial; fun_prop
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc
    (show -(1061676856305 / 10 ^ 12 : ℝ) ≤ -(1061676856304 / 10 ^ 12) by norm_num)
    hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc
      (tailPolynomial (-(1061676856305 / 10 ^ 12)))
      (tailPolynomial (-(1061676856304 / 10 ^ 12))) from
      ⟨tail_root_bracket.1.le, tail_root_bracket.2.le⟩)
  refine ⟨r, hz, ?_⟩
  intro y hy
  exact tailPolynomial_strictMono.injective (hy.trans hz.symm)

theorem tail_root_in_bracket {r : ℝ} (hr : tailPolynomial r = 0) :
    -(1061676856305 / 10 ^ 12 : ℝ) < r ∧ r < -(1061676856304 / 10 ^ 12) := by
  constructor
  · apply tailPolynomial_strictMono.lt_iff_lt.mp
    simpa [hr] using tail_root_bracket.1
  · apply tailPolynomial_strictMono.lt_iff_lt.mp
    simpa [hr] using tail_root_bracket.2

end Calabi.ProfileSeven
