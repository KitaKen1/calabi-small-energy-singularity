import Calabi.Correction.Factor
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The compact operator in the two flat charts

For a function `f` of the momentum coordinate, `u(z) = f(|z|²)` is a radial
function on the unit ball of a Euclidean space `V` of dimension `d`:

* `laplacian_radial`: `Δ u = 4 |z|² f″ + 2 d f′`;
* `euler_radial`: `z · ∇u = 2 |z|² f′`.

`chartOp m` is the fourth-order operator

  `(1 - |z|²)² Δ² - (4 + 2 m) (1 - |z|²) E Δ + ((160 + 2 m) |z|² - 160) Δ
    + m² E² + 112 m E + 2880`,   `E = z · ∇`,

defined on all functions on `V`. Its principal part is `(1 - |z|²)²` times the
flat bilaplacian. On radial functions it is the operator `16 A` of the Calabi
flow:

* `sixteen_Aop_chart0`: `16 (A f)(|z|²) = chartOp 6 (f(|·|²))(z)` on `ℝ¹⁸`;
* `sixteen_Aop_chart1`: `16 (A f)(1 - |w|²) = chartOp 18 (f(1 - |·|²))(w)` on `ℝ⁶`.

This is Lemma 2.2 of the manuscript in the form used for the linear theory:
near `x = 0` and near `x = 1` the Calabi flow in the momentum coordinate is a
fourth-order equation on a flat space, of the type treated by the reused
parabolic library, plus terms of order at most three.
-/

open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian

namespace Calabi.Chart

open Calabi.Radial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Radial functions -/

theorem hasFDerivAt_norm_sq (z : V) :
    HasFDerivAt (fun w : V => ‖w‖ ^ 2) ((2 : ℝ) • innerSL ℝ z) z := by
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  convert h using 1
  ext y
  simp [two_smul]

omit [InnerProductSpace ℝ V] in
theorem isOpen_ball_sq : IsOpen {w : V | ‖w‖ ^ 2 < 1} :=
  isOpen_lt (continuous_norm.pow 2) continuous_const

/-- The derivative of a radial function on the unit ball. The derivative of the
profile is taken within `[0, 1]`, so that the centre is included. -/
theorem hasFDerivAt_radial {f : ℝ → ℝ} {f' : ℝ} {z : V} (hz : ‖z‖ ^ 2 < 1)
    (h : HasDerivWithinAt f f' (Icc 0 1) (‖z‖ ^ 2)) :
    HasFDerivAt (fun w : V => f (‖w‖ ^ 2)) (f' • ((2 : ℝ) • innerSL ℝ z)) z := by
  have hmaps : MapsTo (fun w : V => ‖w‖ ^ 2) {w : V | ‖w‖ ^ 2 < 1} (Icc (0 : ℝ) 1) :=
    fun w hw => ⟨sq_nonneg _, le_of_lt hw⟩
  exact (h.comp_hasFDerivWithinAt z (hasFDerivAt_norm_sq z).hasFDerivWithinAt
    hmaps).hasFDerivAt (isOpen_ball_sq.mem_nhds hz)

/-- `z · ∇u`. -/
noncomputable def euler (u : V → ℝ) (z : V) : ℝ := fderiv ℝ u z z

theorem euler_radial {f : ℝ → ℝ} {f' : ℝ} {z : V} (hz : ‖z‖ ^ 2 < 1)
    (h : HasDerivWithinAt f f' (Icc 0 1) (‖z‖ ^ 2)) :
    euler (fun w : V => f (‖w‖ ^ 2)) z = 2 * ‖z‖ ^ 2 * f' := by
  unfold euler
  rw [(hasFDerivAt_radial hz h).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  ring

variable {f f1 : ℝ → ℝ} {f2 : ℝ} {z : V}

/-- The second derivative of a radial function. -/
theorem fderiv_fderiv_radial (hz : ‖z‖ ^ 2 < 1)
    (h1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f1 x) (Icc 0 1) x)
    (h2 : HasDerivWithinAt f1 f2 (Icc 0 1) (‖z‖ ^ 2)) (a b : V) :
    fderiv ℝ (fderiv ℝ fun w : V => f (‖w‖ ^ 2)) z a b
      = 2 * f1 (‖z‖ ^ 2) * inner ℝ a b + 4 * f2 * inner ℝ z a * inner ℝ z b := by
  have hfd : fderiv ℝ (fun w : V => f (‖w‖ ^ 2))
      =ᶠ[𝓝 z] fun w => f1 (‖w‖ ^ 2) • ((2 : ℝ) • innerSL ℝ w) := by
    filter_upwards [isOpen_ball_sq.mem_nhds hz] with w hw
    exact (hasFDerivAt_radial hw (h1 _ ⟨sq_nonneg _, le_of_lt hw⟩)).fderiv
  have hc : HasFDerivAt (fun w : V => f1 (‖w‖ ^ 2)) (f2 • ((2 : ℝ) • innerSL ℝ z)) z :=
    hasFDerivAt_radial hz h2
  have hl : HasFDerivAt (fun w : V => ((2 : ℝ) • innerSL ℝ w : V →L[ℝ] ℝ))
      ((2 : ℝ) • (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)) z :=
    ((2 : ℝ) • (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)).hasFDerivAt
  have hprod := hc.smul hl
  have hfd2 : fderiv ℝ (fun w : V => f1 (‖w‖ ^ 2) • ((2 : ℝ) • innerSL ℝ w)) z = _ :=
    hprod.fderiv
  rw [hfd.fderiv_eq, hfd2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  erw [innerSL_apply_apply]
  ring

variable [FiniteDimensional ℝ V]

/-- **The Laplacian of a radial function**: `Δ u = 4 |z|² f″ + 2 d f′`. -/
theorem laplacian_radial (hz : ‖z‖ ^ 2 < 1)
    (h1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f1 x) (Icc 0 1) x)
    (h2 : HasDerivWithinAt f1 f2 (Icc 0 1) (‖z‖ ^ 2)) :
    Δ (fun w : V => f (‖w‖ ^ 2)) z
      = 4 * ‖z‖ ^ 2 * f2 + 2 * (Module.finrank ℝ V : ℝ) * f1 (‖z‖ ^ 2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hterm : ∀ i, fderiv ℝ (fderiv ℝ fun w : V => f (‖w‖ ^ 2)) z
      (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i)
      = 2 * f1 (‖z‖ ^ 2) + 4 * f2 * inner ℝ (stdOrthonormalBasis ℝ V i) z ^ 2 := by
    intro i
    rw [fderiv_fderiv_radial hz h1 h2, real_inner_self_eq_norm_sq,
      (stdOrthonormalBasis ℝ V).norm_eq_one i, real_inner_comm z]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, (stdOrthonormalBasis ℝ V).sum_sq_inner_right, Finset.card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  ring

/-! ### Smooth profiles -/

section Smooth

variable {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Icc 0 1))

include hg

theorem laplacian_comp {z : V} (hz : ‖z‖ ^ 2 < 1) :
    Δ (fun w : V => g (‖w‖ ^ 2)) z = lapR (Module.finrank ℝ V : ℝ) g (‖z‖ ^ 2) := by
  have hI : ‖z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, le_of_lt hz⟩
  rw [laplacian_radial hz (fun x hx => hasDerivWithinAt_D hg hx)
    (hasDerivWithinAt_D (contDiffOn_D hg) hI)]
  unfold lapR
  ring

omit [FiniteDimensional ℝ V] in
theorem euler_comp {z : V} (hz : ‖z‖ ^ 2 < 1) :
    euler (fun w : V => g (‖w‖ ^ 2)) z = eulR g (‖z‖ ^ 2) := by
  have hI : ‖z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, le_of_lt hz⟩
  rw [euler_radial hz (hasDerivWithinAt_D hg hI)]
  rfl

theorem laplacian_comp_eventually {z : V} (hz : ‖z‖ ^ 2 < 1) :
    Δ (fun w : V => g (‖w‖ ^ 2))
      =ᶠ[𝓝 z] fun w => lapR (Module.finrank ℝ V : ℝ) g (‖w‖ ^ 2) := by
  filter_upwards [isOpen_ball_sq.mem_nhds hz] with w hw
  exact laplacian_comp hg hw

omit [FiniteDimensional ℝ V] in
theorem euler_comp_eventually {z : V} (hz : ‖z‖ ^ 2 < 1) :
    euler (fun w : V => g (‖w‖ ^ 2)) =ᶠ[𝓝 z] fun w => eulR g (‖w‖ ^ 2) := by
  filter_upwards [isOpen_ball_sq.mem_nhds hz] with w hw
  exact euler_comp hg hw

end Smooth

/-! ### The chart operator -/

/-- The operator `16 A` in a flat chart of dimension `24 - m`, on arbitrary
functions:
`(1 - |z|²)² Δ² - (4 + 2 m) (1 - |z|²) E Δ + ((160 + 2 m) |z|² - 160) Δ + m² E²
+ 112 m E + 2880`. -/
noncomputable def chartOp (m : ℝ) (u : V → ℝ) (z : V) : ℝ :=
  (1 - ‖z‖ ^ 2) ^ 2 * Δ (Δ u) z - (4 + 2 * m) * (1 - ‖z‖ ^ 2) * euler (Δ u) z
    + ((160 + 2 * m) * ‖z‖ ^ 2 - 160) * Δ u z + m ^ 2 * euler (euler u) z
    + 112 * m * euler u z + 2880 * u z

/-- On radial functions the chart operator is the one-dimensional operator
`chart1D`. -/
theorem chartOp_radial {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Icc 0 1)) {z : V}
    (hz : ‖z‖ ^ 2 < 1) :
    chartOp (24 - (Module.finrank ℝ V : ℝ)) (fun w : V => g (‖w‖ ^ 2)) z
      = chart1D (Module.finrank ℝ V : ℝ) g (‖z‖ ^ 2) := by
  have hL := contDiffOn_lapR hg (Module.finrank ℝ V : ℝ)
  have hE := contDiffOn_eulR hg
  have e1 := laplacian_comp hg hz
  have e2 : Δ (Δ fun w : V => g (‖w‖ ^ 2)) z
      = lapR (Module.finrank ℝ V : ℝ) (lapR (Module.finrank ℝ V : ℝ) g) (‖z‖ ^ 2) := by
    rw [(laplacian_congr_nhds (laplacian_comp_eventually hg hz)).eq_of_nhds]
    exact laplacian_comp hL hz
  have e3 : euler (Δ fun w : V => g (‖w‖ ^ 2)) z
      = eulR (lapR (Module.finrank ℝ V : ℝ) g) (‖z‖ ^ 2) := by
    unfold euler
    rw [(laplacian_comp_eventually hg hz).fderiv_eq]
    exact euler_comp hL hz
  have e4 := euler_comp hg hz
  have e5 : euler (euler fun w : V => g (‖w‖ ^ 2)) z = eulR (eulR g) (‖z‖ ^ 2) := by
    have h : euler (euler fun w : V => g (‖w‖ ^ 2)) z
        = fderiv ℝ (euler fun w : V => g (‖w‖ ^ 2)) z z := rfl
    rw [h, (euler_comp_eventually hg hz).fderiv_eq]
    exact euler_comp hE hz
  unfold chartOp chart1D
  rw [e1, e2, e3, e4, e5]

/-- **The compact operator in the chart `ℝ¹⁸` at the end `x = 0`.** -/
theorem sixteen_Aop_chart0 (hV : Module.finrank ℝ V = 18) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {z : V} (hz : ‖z‖ ^ 2 < 1) :
    16 * Aop f (‖z‖ ^ 2) = chartOp 6 (fun w : V => f (‖w‖ ^ 2)) z := by
  have hI : ‖z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, le_of_lt hz⟩
  have hd : (Module.finrank ℝ V : ℝ) = 18 := by
    rw [hV]
    norm_num
  have h := chartOp_radial hf hz
  rw [hd] at h
  rw [sixteen_Aop_chart hf hI, ← h]
  norm_num

/-- **The compact operator in the chart `ℝ⁶` at the end `x = 1`.** -/
theorem sixteen_Aop_chart1 (hV : Module.finrank ℝ V = 6) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {w : V} (hw : ‖w‖ ^ 2 < 1) :
    16 * Aop f (1 - ‖w‖ ^ 2) = chartOp 18 (fun v : V => f (1 - ‖v‖ ^ 2)) w := by
  have hI : ‖w‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, le_of_lt hw⟩
  have hd : (Module.finrank ℝ V : ℝ) = 6 := by
    rw [hV]
    norm_num
  have h := chartOp_radial (contDiffOn_refl hf) hw
  rw [hd] at h
  rw [sixteen_Aop_chart_refl hf hI, ← h]
  norm_num

end Calabi.Chart
