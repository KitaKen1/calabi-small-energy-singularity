import Calabi.Origin.Nonlinear
import Calabi.Shot.Physical
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The regular solution solves the profile system on `0 < s ≤ 1`

For `r ≠ 0` the averages `T e f` are differentiable, with
`r (T e f)′ = f - (e + 1) T e f`. Hence `D (r² K0 f) = r² K1 f`,
`D (r² K1 f) = r² K2 f`, and `D (r² K2 f)` closes the third-order equation.
With `r = s^{3/2}` the jet of the regular solution in the variable `s`,

  `(P, (3/2) D P / s, ((9/4) D² P - (3/2) D P) / s²)`,

is a trajectory of `Calabi.Shot.pfield` on `0 < s ≤ 1`.
-/

open Set Filter
open scoped Topology

namespace Calabi.Origin

open Calabi.Shot (State pfield Ntr Ntr_of_ge)

theorem T_eq_div {f : ℝ → ℝ} (e : ℕ) {r : ℝ} (hr : r ≠ 0) :
    T e f r = (∫ u in (0 : ℝ)..r, u ^ e * f u) / r ^ (e + 1) := by
  unfold T
  have h := intervalIntegral.integral_comp_mul_right (f := fun u : ℝ => u ^ e * f u) (a := 0)
    (b := 1) hr
  have e1 : ∀ t : ℝ, t ^ e * f (t * r) = (t * r) ^ e * f (t * r) / r ^ e := fun t => by
    rw [mul_pow]
    field_simp
  simp only [e1]
  rw [intervalIntegral.integral_div, h, zero_mul, one_mul, smul_eq_mul, pow_succ]
  field_simp

theorem hasDerivAt_T {f : ℝ → ℝ} (hf : Continuous f) (e : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (T e f) ((f r - ((e : ℝ) + 1) * T e f r) / r) r := by
  have hI : HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, u ^ e * f u) (r ^ e * f r) r :=
    (((continuous_id.pow e).mul hf).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hq := hI.fun_div (hasDerivAt_pow (e + 1) r) (pow_ne_zero (e + 1) hr)
  have heq : T e f =ᶠ[𝓝 r] fun x => (∫ u in (0 : ℝ)..x, u ^ e * f u) / x ^ (e + 1) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using T_eq_div e hx
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [T_eq_div e hr]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- `D` of `r²` times a combination of the three averages. -/
theorem hasDerivAt_sq_comb {f : ℝ → ℝ} (hf : Continuous f) {r : ℝ} (hr : r ≠ 0) (a b c : ℝ) :
    HasDerivAt (fun x => x ^ 2 * (a * T 0 f x + b * T 7 f x + c * T 8 f x))
      (r * ((a + b + c) * f r + (a * T 0 f r - 6 * b * T 7 f r - 7 * c * T 8 f r))) r := by
  have h0 := hasDerivAt_T hf 0 hr
  have h7 := hasDerivAt_T hf 7 hr
  have h8 := hasDerivAt_T hf 8 hr
  have h := (hasDerivAt_pow 2 r).fun_mul
    (((h0.const_mul a).fun_add (h7.const_mul b)).fun_add (h8.const_mul c))
  refine h.congr_deriv ?_
  push_cast
  field_simp
  ring

theorem hasDerivAt_sq_K {f : ℝ → ℝ} (hf : Continuous f) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x => x ^ 2 * K0 f x) (r * K1 f r) r ∧
      HasDerivAt (fun x => x ^ 2 * K1 f x) (r * K2 f r) r ∧
      HasDerivAt (fun x => x ^ 2 * K2 f x)
        (r * (f r + (T 0 f r / 56 + 216 / 7 * T 7 f r - 343 / 8 * T 8 f r))) r := by
  have e0 : (fun x => x ^ 2 * K0 f x) =
      fun x => x ^ 2 * (1 / 56 * T 0 f x + -(1 / 7) * T 7 f x + 1 / 8 * T 8 f x) := by
    funext x
    unfold K0
    ring
  have e1 : (fun x => x ^ 2 * K1 f x) =
      fun x => x ^ 2 * (1 / 56 * T 0 f x + 6 / 7 * T 7 f x + -(7 / 8) * T 8 f x) := by
    funext x
    unfold K1
    ring
  have e2 : (fun x => x ^ 2 * K2 f x) =
      fun x => x ^ 2 * (1 / 56 * T 0 f x + -(36 / 7) * T 7 f x + 49 / 8 * T 8 f x) := by
    funext x
    unfold K2
    ring
  rw [e0, e1, e2]
  refine ⟨(hasDerivAt_sq_comb hf hr _ _ _).congr_deriv ?_,
    (hasDerivAt_sq_comb hf hr _ _ _).congr_deriv ?_,
    (hasDerivAt_sq_comb hf hr _ _ _).congr_deriv ?_⟩
  · unfold K1
    ring
  · unfold K2
    ring
  · ring

/-- The regular solution continued by its integral formula: it equals `osol`
on `|r| ≤ 1` and is differentiable for all `r ≠ 0`. -/
noncomputable def oP (k d r : ℝ) : ℝ :=
  d + k * r - 8 / 27 * r ^ 2 * K0 (fun x => Nor (osol k d x)) r

theorem oP_eq_osol (k d : ℝ) {r : ℝ} (hr : |r| ≤ 1) : oP k d r = osol k d r :=
  (osol_eq k d hr).symm

theorem hasDerivAt_oP (k d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (oP k d) (osol1 k d r / r) r := by
  have hK := (hasDerivAt_sq_K (continuous_Nor_osol k d) hr).1
  have h := ((hasDerivAt_const r d).fun_add ((hasDerivAt_id' r).const_mul k)).fun_sub
    (hK.const_mul (8 / 27))
  have e : oP k d = fun x => d + k * x - 8 / 27 * (x ^ 2 * K0 (fun y => Nor (osol k d y)) x) := by
    funext x
    unfold oP
    ring
  rw [e]
  refine h.congr_deriv ?_
  unfold osol1
  field_simp
  ring

theorem hasDerivAt_osol1 (k d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (osol1 k d) (osol2 k d r / r) r := by
  have hK := (hasDerivAt_sq_K (continuous_Nor_osol k d) hr).2.1
  have h := ((hasDerivAt_id' r).const_mul k).fun_sub (hK.const_mul (8 / 27))
  have e : osol1 k d = fun x => k * x - 8 / 27 * (x ^ 2 * K1 (fun y => Nor (osol k d y)) x) := by
    funext x
    unfold osol1
    ring
  rw [e]
  refine h.congr_deriv ?_
  unfold osol2
  field_simp

theorem hasDerivAt_osol2 (k d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (osol2 k d)
      ((-12 * osol2 k d r - 29 * osol1 k d r + 42 * (oP k d r - d)
        - 8 / 27 * r ^ 2 * Nor (osol k d r)) / r) r := by
  have hK := (hasDerivAt_sq_K (continuous_Nor_osol k d) hr).2.2
  have h := ((hasDerivAt_id' r).const_mul k).fun_sub (hK.const_mul (8 / 27))
  have e : osol2 k d = fun x => k * x - 8 / 27 * (x ^ 2 * K2 (fun y => Nor (osol k d y)) x) := by
    funext x
    unfold osol2
    ring
  have h' : HasDerivAt (osol2 k d) (k * 1 - 8 / 27 * (r * (Nor (osol k d r)
      + (T 0 (fun y => Nor (osol k d y)) r / 56 + 216 / 7 * T 7 (fun y => Nor (osol k d y)) r
        - 343 / 8 * T 8 (fun y => Nor (osol k d y)) r)))) r := by
    rw [e]
    exact h
  refine h'.congr_deriv ?_
  unfold osol2 osol1 oP K0 K1 K2
  field_simp
  ring

/-- The jet of the regular solution in the variable `s`, with `r = s √s`. -/
noncomputable def originJet (k d s : ℝ) : State :=
  (oP k d (s * Real.sqrt s), 3 / 2 * osol1 k d (s * Real.sqrt s) / s,
    (9 / 4 * osol2 k d (s * Real.sqrt s) - 3 / 2 * osol1 k d (s * Real.sqrt s)) / s ^ 2)

theorem originJet_one (k d : ℝ) :
    originJet k d 1 = (osol k d 1, 3 / 2 * osol1 k d 1,
      9 / 4 * osol2 k d 1 - 3 / 2 * osol1 k d 1) := by
  unfold originJet
  rw [Real.sqrt_one, mul_one, oP_eq_osol k d (by norm_num)]
  norm_num

theorem originJet_sq (k d : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    originJet k d (w ^ 2) = (oP k d (w ^ 3), 3 / 2 * osol1 k d (w ^ 3) / w ^ 2,
      (9 / 4 * osol2 k d (w ^ 3) - 3 / 2 * osol1 k d (w ^ 3)) / (w ^ 2) ^ 2) := by
  have e : w ^ 2 * Real.sqrt (w ^ 2) = w ^ 3 := by
    rw [Real.sqrt_sq hw]
    ring
  unfold originJet
  rw [e]

/-- **The regular solution is a trajectory of the profile system** at
`s = w²`, `0 < w ≤ 1`, as long as it stays above `-1/2`. -/
theorem hasDerivAt_originJet (k d : ℝ) {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hlow : -(1 / 2) ≤ osol k d (w ^ 3)) :
    HasDerivAt (originJet k d) (pfield d (w ^ 2) (originJet k d (w ^ 2))) (w ^ 2) := by
  have hw0 : w ≠ 0 := hw.ne'
  have hs : (0 : ℝ) < w ^ 2 := by positivity
  have hr : w ^ 3 ≠ 0 := by positivity
  have hr1 : |w ^ 3| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    exact pow_le_one₀ hw.le hw1
  have e : w ^ 2 * Real.sqrt (w ^ 2) = w ^ 3 := by
    rw [Real.sqrt_sq hw.le]
    ring
  have hρ : HasDerivAt (fun s : ℝ => s * Real.sqrt s) (3 / 2 * w) (w ^ 2) := by
    have h := (hasDerivAt_id' (w ^ 2)).fun_mul (Real.hasDerivAt_sqrt hs.ne')
    refine h.congr_deriv ?_
    rw [Real.sqrt_sq hw.le]
    field_simp
    ring
  have hP : HasDerivAt (oP k d) (osol1 k d (w ^ 3) / w ^ 3) (w ^ 2 * Real.sqrt (w ^ 2)) := by
    rw [e]
    exact hasDerivAt_oP k d hr
  have h1 : HasDerivAt (osol1 k d) (osol2 k d (w ^ 3) / w ^ 3) (w ^ 2 * Real.sqrt (w ^ 2)) := by
    rw [e]
    exact hasDerivAt_osol1 k d hr
  have h2 : HasDerivAt (osol2 k d)
      ((-12 * osol2 k d (w ^ 3) - 29 * osol1 k d (w ^ 3) + 42 * (oP k d (w ^ 3) - d)
        - 8 / 27 * (w ^ 3) ^ 2 * Nor (osol k d (w ^ 3))) / w ^ 3)
      (w ^ 2 * Real.sqrt (w ^ 2)) := by
    rw [e]
    exact hasDerivAt_osol2 k d hr
  have c1 := hP.comp (w ^ 2) hρ
  have c2 := h1.comp (w ^ 2) hρ
  have c3 := h2.comp (w ^ 2) hρ
  have f2 := (c2.const_mul (3 / 2)).fun_div (hasDerivAt_id' (w ^ 2)) hs.ne'
  have f3 := ((c3.const_mul (9 / 4)).fun_sub (c2.const_mul (3 / 2))).fun_div
    (hasDerivAt_pow 2 (w ^ 2)) (pow_ne_zero 2 hs.ne')
  have hall := c1.prodMk (f2.prodMk f3)
  refine HasDerivAt.congr_deriv (f := originJet k d) hall ?_
  rw [originJet_sq k d hw.le]
  have hposeq : oP k d (w ^ 3) = osol k d (w ^ 3) := oP_eq_osol k d hr1
  have hNor : Nor (osol k d (w ^ 3)) = oP k d (w ^ 3) / (1 + oP k d (w ^ 3)) := by
    rw [hposeq]
    exact Nor_of_ge hlow
  have hNtr : Ntr (oP k d (w ^ 3)) = oP k d (w ^ 3) / (1 + oP k d (w ^ 3)) := by
    rw [hposeq]
    exact Ntr_of_ge (by linarith)
  have h1p : (1 : ℝ) + oP k d (w ^ 3) ≠ 0 := by
    rw [hposeq]
    have : (0 : ℝ) < 1 + osol k d (w ^ 3) := by linarith
    exact this.ne'
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [pfield]
    field_simp
  · simp only [Function.comp_apply, pfield, e]
    field_simp
    ring
  · simp only [Function.comp_apply, pfield, e, hNor, hNtr, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring

end Calabi.Origin
