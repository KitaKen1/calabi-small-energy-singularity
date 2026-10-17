import Calabi.Correction.Solution
import Calabi.Correction.KopBound
import Calabi.Radial.Estimates

/-!
# Proposition 6.1: the localized correction

`localizedCorrection` is Proposition 6.1 of the manuscript in the pointwise
form `Calabi.Radial.LocalizedCorrection` used in Section 7: for a profile `G`
and a localization `λ` there is, for every small `e > 0` and arbitrarily short
time `T`, a smooth solution `H = F_λ + V` on `(-T, 0) × [0, 1]` of the Calabi
flow in the momentum coordinate with

* `κ₁ ≤ 1 + v∗ H ≤ κ₂`,
* `|V| ≤ C e (x + √(-t))^(-1 + δ)`,
* `|K(H) - K(F_λ)| ≤ C e (x + √(-t))^(-1 + δ)`.

The solution is `Hsol` of `Solution.lean`, with the correction of
`exists_correction`. The bounds are the pointwise part of the weighted norm of
the correction in the two charts:

* `chart0_point`, `chart1_point`: the values and the Euler derivatives `E u`,
  `E² u` of the chart functions along the rays;
* `valOf_point`: the bound of `V` and of `v∗ V`;
* `kop_point`: the bound of `K(H) - K(F_λ)`, by `kop_diff_formula` in the
  interior and by the values of `K` at the two ends.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

variable {c : ℝ} {G : ℝ → ℝ} {lam α T w e M γ : ℝ} {U : Pair}

/-! ### Elementary facts -/

/-- The Euler operator of a function that vanishes near a point vanishes near
the point. -/
theorem eulerE_eventuallyEq_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {u : V → ℝ} {z : V} (h : u =ᶠ[𝓝 z] fun _ => 0) :
    eulerE u =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  show fderiv ℝ u y y = 0
  rw [hy.fderiv_eq (𝕜 := ℝ)]
  simp

/-- A jet of order `j` with the weight `w - j`, on vectors of length at most
the scale. -/
theorem jet_mul_le (j : ℕ) {N r s w e : ℝ} (hs : 0 < s) (he : 0 ≤ e)
    (hN : N ≤ e * s ^ (w - j)) (hr0 : 0 ≤ r) (hr : r ≤ s) : N * r ^ j ≤ e * s ^ w := by
  have h1 : r ^ j ≤ s ^ j := pow_le_pow_left₀ hr0 hr j
  have h2 : s ^ (w - j) * s ^ j = s ^ w := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    ring
  calc N * r ^ j ≤ e * s ^ (w - j) * s ^ j :=
        mul_le_mul hN h1 (pow_nonneg hr0 j) (mul_nonneg he (Real.rpow_nonneg hs.le _))
    _ = e * s ^ w := by rw [mul_assoc, h2]

/-- The weight `(x + √(-t))^(-1 + 2γ)` is bounded below, and its product with
`x` is bounded. -/
theorem weight_facts (hγ : 0 < γ) (hγ1 : γ < 1 / 2) {S x : ℝ} (hxS : x ≤ S) (hS : 0 < S)
    (hS2 : S ≤ 2) : 1 / 2 ≤ S ^ (-1 + 2 * γ) ∧ x * S ^ (-1 + 2 * γ) ≤ 2 := by
  constructor
  · have h1 : (2 : ℝ) ^ (-1 + 2 * γ) ≤ S ^ (-1 + 2 * γ) :=
      Real.rpow_le_rpow_of_nonpos hS hS2 (by linarith)
    have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (-1 + 2 * γ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at h2
    have h3 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  · have h1 : S * S ^ (-1 + 2 * γ) = S ^ (2 * γ) := by
      have h := Real.rpow_add hS 1 (-1 + 2 * γ)
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have h2 : S ^ (2 * γ) ≤ (2 : ℝ) ^ (2 * γ) := Real.rpow_le_rpow hS.le hS2 (by linarith)
    have h3 : (2 : ℝ) ^ (2 * γ) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h3
    have h4 : x * S ^ (-1 + 2 * γ) ≤ S * S ^ (-1 + 2 * γ) :=
      mul_le_mul_of_nonneg_right hxS (Real.rpow_nonneg hS.le _)
    linarith

/-- The algebra of the bound of `K` on a function given in the two charts. -/
theorem kop_alg {x A B p0 p1 p2 q0 q1 q2 : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hp0 : |p0| ≤ A)
    (hp1 : |p1| ≤ A) (hp2 : |p2| ≤ 2 * A) (hq0 : |q0| ≤ B) (hq1 : |q1| ≤ B)
    (hq2 : |q2| ≤ 2 * B) :
    |(1 - x) ^ 2 * (p2 / 4 - p1 / 2) + 2 * (1 - x) * (4 - 5 * x) * p1
        + x ^ 2 * (q2 / 4 - q1 / 2) - 2 * x * (4 - 5 * x) * q1
        + (56 - 144 * x + 90 * x ^ 2) * (p0 + q0)| ≤ 65 * A + 65 * B := by
  have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.2 hx1)
  have key : ∀ {k a D l : ℝ}, |l| ≤ k → |a| ≤ D → |l * a| ≤ k * D := by
    intro k a D l hl ha
    rw [abs_mul]
    exact mul_le_mul hl ha (abs_nonneg _) ((abs_nonneg _).trans hl)
  have c1 : |(1 - x) ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (1 - x)]
  have c2 : |2 * (1 - x) * (4 - 5 * x)| ≤ 8 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 9 / 10)]
  have c3 : |x ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  have c4 : |2 * x * (4 - 5 * x)| ≤ 8 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 2 / 5)]
  have c5 : |56 - 144 * x + 90 * x ^ 2| ≤ 56 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 4 / 5)]
  obtain ⟨p0l, p0u⟩ := abs_le.1 hp0
  obtain ⟨p1l, p1u⟩ := abs_le.1 hp1
  obtain ⟨p2l, p2u⟩ := abs_le.1 hp2
  obtain ⟨q0l, q0u⟩ := abs_le.1 hq0
  obtain ⟨q1l, q1u⟩ := abs_le.1 hq1
  obtain ⟨q2l, q2u⟩ := abs_le.1 hq2
  have d1 : |p2 / 4 - p1 / 2| ≤ A := by
    rw [abs_le]
    constructor <;> linarith
  have d3 : |q2 / 4 - q1 / 2| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  have d5 : |p0 + q0| ≤ A + B := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨t1l, t1u⟩ := abs_le.1 (key c1 d1)
  obtain ⟨t2l, t2u⟩ := abs_le.1 (key c2 hp1)
  obtain ⟨t3l, t3u⟩ := abs_le.1 (key c3 d3)
  obtain ⟨t4l, t4u⟩ := abs_le.1 (key c4 hq1)
  obtain ⟨t5l, t5u⟩ := abs_le.1 (key c5 d5)
  rw [abs_le]
  constructor <;> linarith

/-! ### The chart functions along the rays -/

/-- **The chart function at `x = 0` along a ray**: the value and the Euler
derivatives have the weight `(x + √(-t))^(w/2)`. -/
theorem chart0_point (hR : Reg U) (he : 0 ≤ e) (hX : XJ α T w e U) {t x : ℝ}
    (ht : t ∈ Ioo (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |U.1 t (Real.sqrt x • e18)| ≤ e * (x + Real.sqrt (-t)) ^ (w / 2) ∧
      |eulerE (U.1 t) (Real.sqrt x • e18)| ≤ e * (x + Real.sqrt (-t)) ^ (w / 2) ∧
      |eulerE (eulerE (U.1 t)) (Real.sqrt x • e18)|
        ≤ 2 * (e * (x + Real.sqrt (-t)) ^ (w / 2)) := by
  have hS : 0 < x + Real.sqrt (-t) :=
    add_pos_of_nonneg_of_pos hx.1 (Real.sqrt_pos.2 (by linarith [ht.2]))
  have hA : 0 ≤ e * (x + Real.sqrt (-t)) ^ (w / 2) := mul_nonneg he (Real.rpow_nonneg hS.le _)
  rcases le_or_gt x (3 / 4) with hx34 | hx34
  · -- in the domain of the chart
    obtain ⟨z, hz⟩ : ∃ z : Flat18, z = Real.sqrt x • e18 := ⟨_, rfl⟩
    rw [← hz]
    have hzn : ‖z‖ ^ 2 = x := by
      rw [hz]
      exact norm_sq_ray18 hx.1
    have hp : ((z, t) : Flat18 × ℝ) ∈ dom0 T := ⟨⟨ht.1.le, ht.2⟩, by
      show ‖z‖ ^ 2 ≤ 3 / 4
      rw [hzn]
      exact hx34⟩
    have hs : 0 < sigma ((z, t) : Flat18 × ℝ) := sigma_pos _ ht.2
    have hsw : sigma ((z, t) : Flat18 × ℝ) ^ w = (x + Real.sqrt (-t)) ^ (w / 2) := by
      have h2 : sigma ((z, t) : Flat18 × ℝ) ^ 2 = x + Real.sqrt (-t) := by
        rw [sigma_sq_eq]
        show ‖z‖ ^ 2 + Real.sqrt (-t) = _
        rw [hzn]
      rw [← h2, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      push_cast
      ring
    have hzs : ‖z‖ ≤ sigma ((z, t) : Flat18 × ℝ) := norm_le_sigma ((z, t) : Flat18 × ℝ)
    have hj : ∀ j : ℕ, j ≤ 4 →
        ‖iteratedFDeriv ℝ j (U.1 t) z‖ * ‖z‖ ^ j ≤ e * (x + Real.sqrt (-t)) ^ (w / 2) := by
      intro j hj
      rw [← hsw]
      exact jet_mul_le j hs he ((hX.1 j hj).1 (z, t) hp) (norm_nonneg z) hzs
    have h0 := hj 0 (by norm_num)
    have h1 := hj 1 (by norm_num)
    have h2 := hj 2 (by norm_num)
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs] at h0
    rw [norm_iteratedFDeriv_one, pow_one] at h1
    have hE1 := abs_eulerE_le (U.1 t) z
    have hE2 := abs_eulerE_eulerE_le ((hR.smooth0 t).of_le (by norm_num)) z
    exact ⟨h0, hE1.trans h1, by linarith⟩
  · -- outside the support
    have hopen : IsOpen {y : Flat18 | 1 / 2 < ‖y‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    have hmem : Real.sqrt x • e18 ∈ {y : Flat18 | 1 / 2 < ‖y‖ ^ 2} := by
      show 1 / 2 < ‖Real.sqrt x • e18‖ ^ 2
      rw [norm_sq_ray18 hx.1]
      linarith
    have hev : U.1 t =ᶠ[𝓝 (Real.sqrt x • e18)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hmem] with y hy
      exact hR.supp0 t y hy
    have h1 := eulerE_eventuallyEq_zero hev
    have h2 := eulerE_eventuallyEq_zero h1
    have e0 : U.1 t (Real.sqrt x • e18) = 0 := hev.eq_of_nhds
    have e1 : eulerE (U.1 t) (Real.sqrt x • e18) = 0 := h1.eq_of_nhds
    have e2 : eulerE (eulerE (U.1 t)) (Real.sqrt x • e18) = 0 := h2.eq_of_nhds
    rw [e0, e1, e2, abs_zero]
    exact ⟨hA, hA, by linarith⟩

/-- **The chart function at `x = 1` along a ray**: the value and the Euler
derivatives are bounded. -/
theorem chart1_point (hR : Reg U) (he : 0 ≤ e) (hX : XJ α T w e U) {t x : ℝ}
    (ht : t ∈ Ioo (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |U.2.2.1 t (Real.sqrt (1 - x) • e6)| ≤ e ∧
      |eulerE (U.2.2.1 t) (Real.sqrt (1 - x) • e6)| ≤ e ∧
      |eulerE (eulerE (U.2.2.1 t)) (Real.sqrt (1 - x) • e6)| ≤ 2 * e := by
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  rcases le_or_gt (1 - x) (7 / 8) with hx78 | hx78
  · -- in the domain of the chart
    obtain ⟨v, hv⟩ : ∃ v : Flat6, v = Real.sqrt (1 - x) • e6 := ⟨_, rfl⟩
    rw [← hv]
    have hvn : ‖v‖ ^ 2 = 1 - x := by
      rw [hv]
      exact norm_sq_ray6 h1x
    have hp : ((v, t) : Flat6 × ℝ) ∈ dom1 T := ⟨⟨ht.1.le, ht.2⟩, by
      show ‖v‖ ^ 2 ≤ 7 / 8
      rw [hvn]
      exact hx78⟩
    have hv1 : ‖v‖ ≤ 1 := by
      have h0 := norm_nonneg v
      have := hx.1
      nlinarith
    have hj : ∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j (U.2.2.1 t) v‖ * ‖v‖ ^ j ≤ e := by
      intro j hj
      have h := jet_mul_le (s := 1) (w := w) j one_pos he ((hX.2 j hj).1 (v, t) hp)
        (norm_nonneg v) hv1
      rwa [Real.one_rpow, mul_one] at h
    have h0 := hj 0 (by norm_num)
    have h1 := hj 1 (by norm_num)
    have h2 := hj 2 (by norm_num)
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs] at h0
    rw [norm_iteratedFDeriv_one, pow_one] at h1
    have hE1 := abs_eulerE_le (U.2.2.1 t) v
    have hE2 := abs_eulerE_eulerE_le ((hR.smooth1 t).of_le (by norm_num)) v
    exact ⟨h0, hE1.trans h1, by linarith⟩
  · -- outside the support
    have hopen : IsOpen {y : Flat6 | 3 / 4 < ‖y‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    have hmem : Real.sqrt (1 - x) • e6 ∈ {y : Flat6 | 3 / 4 < ‖y‖ ^ 2} := by
      show 3 / 4 < ‖Real.sqrt (1 - x) • e6‖ ^ 2
      rw [norm_sq_ray6 h1x]
      linarith
    have hev : U.2.2.1 t =ᶠ[𝓝 (Real.sqrt (1 - x) • e6)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hmem] with y hy
      exact hR.supp1 t y hy
    have h1 := eulerE_eventuallyEq_zero hev
    have h2 := eulerE_eventuallyEq_zero h1
    have e0 : U.2.2.1 t (Real.sqrt (1 - x) • e6) = 0 := hev.eq_of_nhds
    have e1 : eulerE (U.2.2.1 t) (Real.sqrt (1 - x) • e6) = 0 := h1.eq_of_nhds
    have e2 : eulerE (eulerE (U.2.2.1 t)) (Real.sqrt (1 - x) • e6) = 0 := h2.eq_of_nhds
    rw [e0, e1, e2, abs_zero]
    exact ⟨he, he, by linarith⟩

/-! ### The bounds of Proposition 6.1 -/

/-- **The correction** is bounded by the weight, and its product with `v∗` is
small. -/
theorem valOf_point (hR : Reg U) (he : 0 ≤ e) (hγ : 0 < γ) (hγ1 : γ < 1 / 2) (hT1 : T ≤ 1)
    (hX : XJ α T (-2 + 4 * γ) e U) {t x : ℝ} (ht : t ∈ Ioo (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |valOf U t x| ≤ 3 * e * (x + Real.sqrt (-t)) ^ (-1 + 2 * γ)
      ∧ |vstar x * valOf U t x| ≤ 3 * e := by
  have hw : (-2 + 4 * γ) / 2 = -1 + 2 * γ := by ring
  obtain ⟨a0, -, -⟩ := chart0_point hR he hX ht hx
  obtain ⟨b0, -, -⟩ := chart1_point hR he hX ht hx
  rw [hw] at a0
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith [ht.2])
  have hρ1 : Real.sqrt (-t) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (by linarith [ht.1] : -t ≤ (1 : ℝ))
    rwa [Real.sqrt_one] at h
  obtain ⟨hW1, hW2⟩ := weight_facts hγ hγ1 (by linarith : x ≤ x + Real.sqrt (-t))
    (by linarith [hx.1]) (by linarith [hx.2])
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (x + Real.sqrt (-t)) ^ (-1 + 2 * γ) := ⟨_, rfl⟩
  rw [← hW] at a0 hW1 hW2 ⊢
  have heW : e ≤ 2 * (e * W) := by nlinarith [mul_nonneg he (sub_nonneg.2 hW1)]
  have hv0 : 0 ≤ vstar x := by
    unfold vstar
    exact mul_nonneg hx.1 (by linarith [hx.2])
  have hvx : vstar x ≤ x := by
    unfold vstar
    nlinarith [hx.1, hx.2]
  have hv1 : vstar x ≤ 1 := by linarith [hx.2]
  have hsum : |valOf U t x|
      ≤ |U.1 t (Real.sqrt x • e18)| + |U.2.2.1 t (Real.sqrt (1 - x) • e6)| := abs_add_le _ _
  constructor
  · linarith
  · rw [abs_mul, abs_of_nonneg hv0]
    have h2 : vstar x * |U.1 t (Real.sqrt x • e18)| ≤ x * (e * W) :=
      mul_le_mul hvx a0 (abs_nonneg _) hx.1
    have h3 : x * (e * W) ≤ 2 * e := by nlinarith [mul_le_mul_of_nonneg_left hW2 he]
    have h4 : vstar x * |U.2.2.1 t (Real.sqrt (1 - x) • e6)| ≤ 1 * e :=
      mul_le_mul hv1 b0 (abs_nonneg _) zero_le_one
    calc vstar x * |valOf U t x|
        ≤ vstar x * (|U.1 t (Real.sqrt x • e18)| + |U.2.2.1 t (Real.sqrt (1 - x) • e6)|) :=
          mul_le_mul_of_nonneg_left hsum hv0
      _ = vstar x * |U.1 t (Real.sqrt x • e18)|
          + vstar x * |U.2.2.1 t (Real.sqrt (1 - x) • e6)| := mul_add _ _ _
      _ ≤ 3 * e := by linarith

set_option maxHeartbeats 800000 in
/-- **The operator `K` on the solution** differs from `K(F_λ)` by the weight. -/
theorem kop_point (hP : IsProfile c G) (hR : Reg U) (he : 0 ≤ e) (hγ : 0 < γ)
    (hγ1 : γ < 1 / 2) (hT1 : T ≤ 1) (hX : XJ α T (-2 + 4 * γ) e U) {t x : ℝ}
    (ht : t ∈ Ioo (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |Kop (Hsol G lam U t) x - Kop (Flam G lam t) x|
      ≤ 195 * e * (x + Real.sqrt (-t)) ^ (-1 + 2 * γ) := by
  have hw : (-2 + 4 * γ) / 2 = -1 + 2 * γ := by ring
  obtain ⟨a0, a1, a2⟩ := chart0_point hR he hX ht hx
  obtain ⟨b0, b1, b2⟩ := chart1_point hR he hX ht hx
  rw [hw] at a0 a1 a2
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith [ht.2])
  have hρ1 : Real.sqrt (-t) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (by linarith [ht.1] : -t ≤ (1 : ℝ))
    rwa [Real.sqrt_one] at h
  obtain ⟨hW1, -⟩ := weight_facts hγ hγ1 (by linarith : x ≤ x + Real.sqrt (-t))
    (by linarith [hx.1]) (by linarith [hx.2])
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (x + Real.sqrt (-t)) ^ (-1 + 2 * γ) := ⟨_, rfl⟩
  rw [← hW] at a0 a1 a2 hW1 ⊢
  have heW : e ≤ 2 * (e * W) := by nlinarith [mul_nonneg he (sub_nonneg.2 hW1)]
  have heW0 : 0 ≤ e * W := mul_nonneg he (by linarith)
  have hval : ∀ y : ℝ, Hsol G lam U t y - Flam G lam t y
      = U.1 t (Real.sqrt y • e18) + U.2.2.1 t (Real.sqrt (1 - y) • e6) := by
    intro y
    unfold Hsol valOf
    ring
  have hsum := abs_add_le (U.1 t (Real.sqrt x • e18)) (U.2.2.1 t (Real.sqrt (1 - x) • e6))
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · -- the end `x = 0`
    have e1 : Kop (Hsol G lam U t) x - Kop (Flam G lam t) x
        = 56 * (U.1 t (Real.sqrt x • e18) + U.2.2.1 t (Real.sqrt (1 - x) • e6)) := by
      rw [← hval x, ← hx0, Kop_zero, Kop_zero]
      ring
    rw [e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 56)]
    linarith
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · -- the end `x = 1`
    have e1 : Kop (Hsol G lam U t) x - Kop (Flam G lam t) x
        = 2 * (U.1 t (Real.sqrt x • e18) + U.2.2.1 t (Real.sqrt (1 - x) • e6)) := by
      rw [← hval x, hx1, Kop_one, Kop_one]
      ring
    rw [e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · -- the interior
    have hfun : Hsol G lam U t = fun y => Flam G lam t y
        + (U.1 t (Real.sqrt y • e18) + U.2.2.1 t (Real.sqrt (1 - y) • e6)) := rfl
    rw [hfun, kop_diff_formula ((hR.smooth0 t).of_le (by norm_num))
      ((hR.smooth1 t).of_le (by norm_num)) e18 e6 (contDiffOn_Flam_Icc hP lam ht.2) ⟨hx0, hx1⟩]
    have h := kop_alg hx.1 hx.2 a0 a1 a2 b0 b1 b2
    linarith

set_option maxHeartbeats 1600000 in
/-- **Proposition 6.1 of the manuscript**: the localized correction of the
self-similar profile, in the pointwise form used in Section 7. -/
theorem localizedCorrection (hP : IsProfile c G) : LocalizedCorrection G := by
  obtain ⟨κ, hκ, hκG⟩ := hP.lower
  obtain ⟨Mu, hMuG⟩ := hP.upper
  obtain ⟨γ, hγ, hγ1, H⟩ := exists_correction hP
  have hm : 0 < min 1 κ := lt_min one_pos hκ
  have hm1 : min 1 κ ≤ 1 := min_le_left _ _
  refine ⟨2 * γ, min 1 κ / 2, max 1 Mu + 1, 195, by linarith, by linarith, by linarith,
    by norm_num, ?_⟩
  intro lam hlam hlam8
  obtain ⟨e₀, he₀, -, H1⟩ := H lam hlam hlam8 (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨min e₀ (min 1 κ / 6), lt_min he₀ (by linarith), ?_⟩
  intro e he hee T₀ hT₀
  have hee0 : e ≤ e₀ := hee.trans (min_le_left _ _)
  have hee1 : e ≤ min 1 κ / 6 := hee.trans (min_le_right _ _)
  obtain ⟨T₁, hT₁, -, hT₁1, H2⟩ := H1 e he hee0
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = min T₁ (T₀ / 2) := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hTdef]
    exact lt_min hT₁ (by linarith)
  have hTT₁ : T ≤ T₁ := by
    rw [hTdef]
    exact min_le_left _ _
  have hTT₀ : T < T₀ := by
    rw [hTdef]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hT1 : T ≤ 1 := hTT₁.trans hT₁1
  obtain ⟨U, M, hR, hS, hX, hXT, hEq⟩ := H2 T hT hTT₁
  -- the bounds of the multiplier
  have hB : ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      min 1 κ / 2 ≤ 1 + vstar x * Hsol G lam U t x
        ∧ 1 + vstar x * Hsol G lam U t x ≤ max 1 Mu + 1 := by
    intro t ht x hx
    obtain ⟨-, hv⟩ := valOf_point hR he.le hγ hγ1 hT1 hX ht hx
    obtain ⟨h1, h2⟩ := blam_mem hP (lam := lam) hκG hMuG ht.2 hx
    obtain ⟨hvl, hvu⟩ := abs_le.1 hv
    have e1 : 1 + vstar x * Hsol G lam U t x
        = (1 + vstar x * Flam G lam t x) + vstar x * valOf U t x := by
      unfold Hsol
      ring
    rw [e1]
    constructor <;> linarith
  have hU : IsCorrection G lam (1 / 4) T (-2 + 4 * γ) e (max M 0) U :=
    { reg := hR
      sol := hS
      xj := hX
      xt := hXT.mono (le_max_left _ _)
      eqn := hEq
      pos := fun t ht x hx => by
        have h := (hB t ht x hx).1
        have e1 : Hsol G lam U t x = Flam G lam t x + valOf U t x := rfl
        rw [e1] at h
        linarith }
  refine ⟨T, Hsol G lam U, hT, hTT₀,
    ⟨Hsol_smooth hP (by norm_num) (by norm_num) hlam hlam8 he.le (le_max_right _ _) hT1 hU,
      Hsol_eqn hP (by norm_num) (by norm_num) hlam hlam8 he.le (le_max_right _ _) hT1 hU⟩, ?_⟩
  intro t ht x hx
  obtain ⟨h1, h2⟩ := hB t ht x hx
  refine ⟨h1, h2, ?_, kop_point hP hR he.le hγ hγ1 hT1 hX ht hx⟩
  have e1 : Hsol G lam U t x - Flam G lam t x = valOf U t x := by
    unfold Hsol
    ring
  rw [e1]
  refine (valOf_point hR he.le hγ hγ1 hT1 hX ht hx).1.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith)
    (Real.rpow_nonneg (add_nonneg hx.1 (Real.sqrt_nonneg _)) _)

end Calabi.Weighted
