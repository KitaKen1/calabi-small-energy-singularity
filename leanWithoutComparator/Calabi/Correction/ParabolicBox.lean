import Calabi.Correction.InteriorReal

/-!
# Parabolic boxes

`pbox p₀ r` is the two-sided parabolic box `{|x - x₀| < r, |t - t₀| < r⁴}`. It
is an open neighbourhood of `p₀`; its diameter for the parabolic distance is
at most `4 r`. The window of scale `q` centred at the later point
`(x₀, t₀ + q⁴/2)` maps the cylinder of radius two into `pbox p₀ (2 q)`, and
the image of the cylinder of radius one contains `pbox p₀ (q/2)`: this is how
the one-sided interior estimate `interior_real` is used at an arbitrary
interior point.
-/

open Set Filter Topology

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The two-sided parabolic box of radius `r` around `p₀`. -/
def pbox (p₀ : V × ℝ) (r : ℝ) : Set (V × ℝ) :=
  {p | ‖p.1 - p₀.1‖ < r ∧ |p.2 - p₀.2| < r ^ 4}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem isOpen_pbox (p₀ : V × ℝ) (r : ℝ) : IsOpen (pbox p₀ r) := by
  have h1 : IsOpen {p : V × ℝ | ‖p.1 - p₀.1‖ < r} :=
    isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const
  have h2 : IsOpen {p : V × ℝ | |p.2 - p₀.2| < r ^ 4} :=
    isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
  exact h1.inter h2

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem mem_pbox_self (p₀ : V × ℝ) {r : ℝ} (hr : 0 < r) : p₀ ∈ pbox p₀ r := by
  refine ⟨?_, ?_⟩
  · rw [sub_self, norm_zero]
    exact hr
  · rw [sub_self, abs_zero]
    positivity

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem pbox_mono (p₀ : V × ℝ) {r r' : ℝ} (hr : 0 ≤ r) (h : r ≤ r') : pbox p₀ r ⊆ pbox p₀ r' :=
  fun _ hp => ⟨hp.1.trans_le h, hp.2.trans_le (pow_le_pow_left₀ hr h 4)⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A small box is contained in a ball of the product metric. -/
theorem pbox_subset_ball (p₀ : V × ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    pbox p₀ r ⊆ Metric.ball p₀ r := by
  intro p hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq]
  refine ⟨hp.1, hp.2.trans_le ?_⟩
  calc r ^ 4 = r * r ^ 3 := by ring
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) hr
    _ = r := mul_one r

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem pbox_shift {p₀ p : V × ℝ} {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hp : p ∈ pbox p₀ r)
    {v : V} (hv : ‖v‖ ≤ r') : ((p.1 + v, p.2) : V × ℝ) ∈ pbox p₀ (r + r') := by
  refine ⟨?_, hp.2.trans_le (pow_le_pow_left₀ hr (by linarith) 4)⟩
  show ‖p.1 + v - p₀.1‖ < r + r'
  calc ‖p.1 + v - p₀.1‖ = ‖(p.1 - p₀.1) + v‖ := by
        congr 1
        abel
    _ ≤ ‖p.1 - p₀.1‖ + ‖v‖ := norm_add_le _ _
    _ < r + r' := add_lt_add_of_lt_of_le hp.1 hv

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem quarter_le_of_le_pow {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (h : x ≤ r ^ 4) :
    x ^ ((1 : ℝ) / 4) ≤ r := by
  have h1 := Real.rpow_le_rpow hx h (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rwa [pow_four_quarter hr] at h1

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The diameter of a box for the parabolic distance. -/
theorem pdist_le_of_pbox {p₀ p q : V × ℝ} {r : ℝ} (hr : 0 ≤ r) (hp : p ∈ pbox p₀ r)
    (hq : q ∈ pbox p₀ r) : pdist p q ≤ 4 * r := by
  have h1 : ‖p.1 - q.1‖ ≤ 2 * r := by
    calc ‖p.1 - q.1‖ = ‖(p.1 - p₀.1) - (q.1 - p₀.1)‖ := by
          congr 1
          abel
      _ ≤ ‖p.1 - p₀.1‖ + ‖q.1 - p₀.1‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith [hp.1, hq.1]
  have h2 : |p.2 - q.2| ≤ (2 * r) ^ 4 := by
    have h3 : |p.2 - q.2| ≤ |p.2 - p₀.2| + |q.2 - p₀.2| := by
      have e : p.2 - q.2 = (p.2 - p₀.2) - (q.2 - p₀.2) := by ring
      rw [e]
      exact abs_sub _ _
    have h4 : (0 : ℝ) ≤ r ^ 4 := by positivity
    nlinarith [hp.2, hq.2]
  have h3 := quarter_le_of_le_pow (abs_nonneg (p.2 - q.2)) (by linarith : (0 : ℝ) ≤ 2 * r) h2
  unfold pdist
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem pdist_center_le {p₀ p : V × ℝ} {r : ℝ} (hr : 0 ≤ r) (hp : p ∈ pbox p₀ r) :
    pdist p p₀ ≤ 2 * r := by
  have h3 := quarter_le_of_le_pow (abs_nonneg (p.2 - p₀.2)) hr hp.2.le
  unfold pdist
  linarith [hp.1]

omit [FiniteDimensional ℝ V] in
/-- The window centred at a later time maps the large cylinder into a box. -/
theorem window_mapsTo_pbox (p₀ : V × ℝ) {q : ℝ} (hq : 0 < q) :
    MapsTo (window ((p₀.1, p₀.2 + q ^ 4 / 2) : V × ℝ) q) (cylinder 2) (pbox p₀ (2 * q)) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hq4 : 0 < q ^ 4 := by positivity
  refine ⟨?_, ?_⟩
  · show ‖p₀.1 + q • p.1 - p₀.1‖ < 2 * q
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    nlinarith
  · show |p₀.2 + q ^ 4 / 2 + q ^ 4 * p.2 - p₀.2| < (2 * q) ^ 4
    rw [abs_lt]
    constructor <;> nlinarith

omit [FiniteDimensional ℝ V] in
/-- The image of the small cylinder contains a box around `p₀`. -/
theorem pbox_subset_window_image (p₀ : V × ℝ) {q : ℝ} (hq : 0 < q) :
    pbox p₀ (q / 2) ⊆ window ((p₀.1, p₀.2 + q ^ 4 / 2) : V × ℝ) q '' cylinder 1 := by
  intro P hP
  have hq4 : 0 < q ^ 4 := by positivity
  have h2 := abs_lt.1 hP.2
  have e16 : (q / 2) ^ 4 = q ^ 4 / 16 := by ring
  rw [e16] at h2
  refine ⟨(q⁻¹ • (P.1 - p₀.1), (P.2 - (p₀.2 + q ^ 4 / 2)) / q ^ 4), ⟨?_, ?_, ?_⟩, ?_⟩
  · show ‖q⁻¹ • (P.1 - p₀.1)‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq), inv_mul_lt_iff₀ hq]
    linarith [hP.1]
  · show -(1 : ℝ) ^ 4 < (P.2 - (p₀.2 + q ^ 4 / 2)) / q ^ 4
    rw [lt_div_iff₀ hq4]
    nlinarith [h2.1]
  · show (P.2 - (p₀.2 + q ^ 4 / 2)) / q ^ 4 ≤ 0
    apply div_nonpos_of_nonpos_of_nonneg _ hq4.le
    linarith [h2.2]
  · show ((p₀.1 + q • q⁻¹ • (P.1 - p₀.1),
      p₀.2 + q ^ 4 / 2 + q ^ 4 * ((P.2 - (p₀.2 + q ^ 4 / 2)) / q ^ 4)) : V × ℝ) = P
    rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul, mul_div_cancel₀ _ hq4.ne']
    ext
    · simp
    · simp

end Calabi.Weighted
