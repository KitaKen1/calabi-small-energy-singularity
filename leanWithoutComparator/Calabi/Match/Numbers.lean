import Calabi.Shot.Data.ChainData
import Calabi.Tail.Data
import Calabi.Match.Bounds
import Calabi.Shot.FrameAlgebra

/-!
# The numbers of the matching at `s = 56`

Closed inequalities between the certified data: the end jet and response of
the finite shot, the jet of the approximate tail, and the preconditioner

  `C = [[-11685, 31935], [-19332, -22620]] / 2^16`.

All bounds are coarse powers of two; `R = 2^-56` is the radius of the box.
-/

namespace Calabi.Match

open Calabi.Shot Calabi.Shot.Data Calabi.Tail Calabi.Tail.Data

/-- The end jet of the finite shot at the centre minus the jet of the
approximate tail, in the variable `s`. -/
noncomputable def Δ₀ : State :=
  ((sum575.stop.v : ℝ) / (scaleP : ℝ) - (tailSum.v : ℝ) / (scaleP : ℝ),
    16 * ((sum575.stop.d1 : ℝ) / (scaleP : ℝ)) - (tailSum.d1 : ℝ) / ((scaleP : ℝ) * 56),
    256 * ((sum575.stop.d2 : ℝ) / (scaleP : ℝ)) - (tailSum.d2 : ℝ) / ((scaleP : ℝ) * 56 ^ 2))

/-- The response of the end jet to `z₁`, in the variable `s`. -/
noncomputable def g₁ : State :=
  ((respEnd.a11 : ℝ) / (scaleU : ℝ), 16 * ((respEnd.a21 : ℝ) / (scaleU : ℝ)),
    256 * ((respEnd.a31 : ℝ) / (scaleU : ℝ)))

/-- The response of the end jet to `z₂`, in the variable `s`. -/
noncomputable def g₂ : State :=
  ((respEnd.a12 : ℝ) / (scaleU : ℝ), 16 * ((respEnd.a22 : ℝ) / (scaleU : ℝ)),
    256 * ((respEnd.a32 : ℝ) / (scaleU : ℝ)))

theorem stab_Δ₀ : |stab Δ₀| ≤ 1 / 2 ^ 77 := by
  rw [abs_le]
  constructor <;> norm_num [stab, Δ₀, sum575, tailSum, scaleP]

theorem stab_g₁ : |stab g₁| ≤ 7 / 1000 := by
  rw [abs_le]
  constructor <;> norm_num [stab, g₁, respEnd, scaleU]

theorem stab_g₂ : |stab g₂| ≤ 19 / 125 := by
  rw [abs_le]
  constructor <;> norm_num [stab, g₂, respEnd, scaleU]

theorem row1_m1 : |1 - -11685 / 65536 * ux g₁ - 31935 / 65536 * uw g₁| ≤ 1 / 2 ^ 22 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, g₁, respEnd, scaleU]

theorem row1_m2 : |0 - -11685 / 65536 * ux g₂ - 31935 / 65536 * uw g₂| ≤ 1 / 2 ^ 17 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, g₂, respEnd, scaleU]

theorem row1_v : |-11685 / 65536 * ux Δ₀ + 31935 / 65536 * uw Δ₀| ≤ 1 / 2 ^ 73 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, Δ₀, sum575, tailSum, scaleP]

theorem row2_m1 : |0 - -19332 / 65536 * ux g₁ - -22620 / 65536 * uw g₁| ≤ 1 / 2 ^ 18 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, g₁, respEnd, scaleU]

theorem row2_m2 : |1 - -19332 / 65536 * ux g₂ - -22620 / 65536 * uw g₂| ≤ 1 / 2 ^ 15 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, g₂, respEnd, scaleU]

theorem row2_v : |-19332 / 65536 * ux Δ₀ + -22620 / 65536 * uw Δ₀| ≤ 1 / 2 ^ 75 := by
  rw [abs_le]
  constructor <;> norm_num [ux, uw, Δ₀, sum575, tailSum, scaleP]

/-- The remainder at `s = 56`, in the variable `s`. -/
theorem rad_bounds : (radEnd.a : ℝ) / (scaleE : ℝ) ≤ 1 / 2 ^ 70 ∧
    16 * ((radEnd.b : ℝ) / (scaleE : ℝ)) ≤ 1 / 2 ^ 67 ∧
    256 * ((radEnd.c : ℝ) / (scaleE : ℝ)) ≤ 1 / 2 ^ 68 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [radEnd, scaleE]

/-- The residual of the approximate tail at the centre parameter. -/
theorem eps_bound : (tailSum.eps : ℝ) / (scaleE : ℝ) ≤ 1 / 2 ^ 90 := by
  norm_num [tailSum, scaleE]

/-- The displacement of `d` on the box. -/
theorem dz_bound : ((dz1.natAbs + dz2.natAbs : ℕ) : ℝ) / (scaleU : ℝ) ≤ 1 / 2 ^ 13 := by
  norm_num [dz1, dz2, scaleU]

end Calabi.Match
