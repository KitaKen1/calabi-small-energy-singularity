import Calabi.Correction.TwoCharts
import Calabi.Correction.ChartCutoff

/-!
# The two scales of the chart at the point orbit

In the chart `x = |z|²` the weighted norms of Section 6 of the manuscript use
the scale `σ = (|z|² + √(-t))^{1/2}`. The outer problem is solved in the
time-independent scale `s_θ = min((|z|² + θ)^{1/2}, 1)`, where `θ = β²` is the
inner radius in the momentum coordinate (the scale `s_β` of the manuscript,
cut at one because the forward block needs a bounded scale). On
`θ/4 ≤ |z|² ≤ 3/4`, for `T ≤ (θ/4)²`, the two scales are comparable
(`sigma_sth_comparable`).

* `WH.sigma_of_sth`, `WH.sth_of_sigma`, `WJ.sigma_of_sth`: change of scale for
  functions that vanish off this region, with constants that do not depend on
  `θ` and `T`;
* `WJ_cut0`: the cut-off `χ(4|z|²) - χ(2|z|²/θ)` of the outer problem has
  weighted jets of weight zero for `s_θ`, uniformly in `θ`;
* `WJ_chiV_sigma`: the cut-offs `χ(|z|²/μ)`, `μ ≥ θ`, of the inner problem have
  weighted jets of weight zero for `σ`, uniformly.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The time-independent scale -/

/-- The scale of the outer problem: `min((|z|² + θ)^{1/2}, 1)`. -/
noncomputable def sth (θ : ℝ) (z : V) : ℝ := min (Real.sqrt (‖z‖ ^ 2 + θ)) 1

theorem sth_le_one (θ : ℝ) (z : V) : sth θ z ≤ 1 := min_le_right _ _

theorem sqrt_le_sth {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (z : V) : Real.sqrt θ ≤ sth θ z := by
  refine le_min (Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖z‖])) ?_
  have h := Real.sqrt_le_sqrt hθ1
  rwa [Real.sqrt_one] at h

theorem sth_pos {θ : ℝ} (hθ : 0 < θ) (z : V) : 0 < sth θ z :=
  lt_min (Real.sqrt_pos.2 (by linarith [sq_nonneg ‖z‖])) one_pos

theorem sth_eq {θ : ℝ} {z : V} (h : ‖z‖ ^ 2 + θ ≤ 1) : sth θ z = Real.sqrt (‖z‖ ^ 2 + θ) := by
  refine min_eq_left ?_
  have h1 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_one] at h1

theorem abs_sqrt_sq_add_sub_le {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ : 0 < θ) :
    |Real.sqrt (x ^ 2 + θ) - Real.sqrt (y ^ 2 + θ)| ≤ |x - y| := by
  have hX : 0 < Real.sqrt (x ^ 2 + θ) := Real.sqrt_pos.2 (by positivity)
  have hY : 0 < Real.sqrt (y ^ 2 + θ) := Real.sqrt_pos.2 (by positivity)
  have hXx : x ≤ Real.sqrt (x ^ 2 + θ) := by
    have h := Real.sqrt_le_sqrt (by linarith : x ^ 2 ≤ x ^ 2 + θ)
    rwa [Real.sqrt_sq hx] at h
  have hYy : y ≤ Real.sqrt (y ^ 2 + θ) := by
    have h := Real.sqrt_le_sqrt (by linarith : y ^ 2 ≤ y ^ 2 + θ)
    rwa [Real.sqrt_sq hy] at h
  have e1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ x ^ 2 + θ)
  have e2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y ^ 2 + θ)
  have e : (Real.sqrt (x ^ 2 + θ) - Real.sqrt (y ^ 2 + θ))
      * (Real.sqrt (x ^ 2 + θ) + Real.sqrt (y ^ 2 + θ)) = (x - y) * (x + y) := by
    linear_combination e1 - e2
  have hsum : 0 < Real.sqrt (x ^ 2 + θ) + Real.sqrt (y ^ 2 + θ) := by linarith
  have h1 : |Real.sqrt (x ^ 2 + θ) - Real.sqrt (y ^ 2 + θ)|
      * (Real.sqrt (x ^ 2 + θ) + Real.sqrt (y ^ 2 + θ)) = |x - y| * (x + y) := by
    have h0 := congrArg abs e
    rwa [abs_mul, abs_mul, abs_of_pos hsum, abs_of_nonneg (by linarith : 0 ≤ x + y)] at h0
  have h2 : |x - y| * (x + y)
      ≤ |x - y| * (Real.sqrt (x ^ 2 + θ) + Real.sqrt (y ^ 2 + θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  rw [← h1] at h2
  exact le_of_mul_le_mul_right h2 hsum

theorem sth_lipschitz {θ : ℝ} (hθ : 0 < θ) (x y : V) : |sth θ x - sth θ y| ≤ ‖x - y‖ := by
  unfold sth
  have h1 := abs_min_sub_min_le (Real.sqrt (‖x‖ ^ 2 + θ)) (Real.sqrt (‖y‖ ^ 2 + θ)) 1
  have h2 := abs_sqrt_sq_add_sub_le (norm_nonneg x) (norm_nonneg y) hθ
  exact h1.trans (h2.trans (abs_norm_sub_norm_le x y))

theorem isScale_sth {θ a : ℝ} (hθ : 0 < θ) (ha : a ≤ 1 / 2) (Ω : Set (V × ℝ)) :
    IsScale a 2 (fun p : V × ℝ => sth θ p.1) Ω :=
  isScale_of_space (sth_pos hθ) (sth_lipschitz hθ) ha

/-! ### Comparison with `σ` -/

theorem sqrt_neg_le {θ T : ℝ} {t : ℝ} (hθ : 0 ≤ θ) (hT : T ≤ (θ / 4) ^ 2) (ht : t ∈ Ico (-T) 0) :
    Real.sqrt (-t) ≤ θ / 4 := by
  have h := Real.sqrt_le_sqrt (by linarith [ht.1] : -t ≤ (θ / 4) ^ 2)
  rwa [Real.sqrt_sq (by positivity)] at h

theorem sigma_sq_eq (p : V × ℝ) : sigma p ^ 2 = ‖p.1‖ ^ 2 + Real.sqrt (-p.2) := by
  unfold sigma
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))

/-- `σ ≤ |z| + √θ/2` for `T ≤ (θ/4)²`. -/
theorem sigma_le_norm_add {θ T : ℝ} {p : V × ℝ} (hθ : 0 < θ) (hT : T ≤ (θ / 4) ^ 2)
    (hp : p.2 ∈ Ico (-T) 0) : sigma p ≤ ‖p.1‖ + Real.sqrt θ / 2 := by
  have hρ := sqrt_neg_le hθ.le hT hp
  have hsq := Real.sq_sqrt hθ.le
  have h1 : ‖p.1‖ ^ 2 + Real.sqrt (-p.2) ≤ (‖p.1‖ + Real.sqrt θ / 2) ^ 2 := by
    nlinarith [norm_nonneg p.1, Real.sqrt_nonneg θ,
      mul_nonneg (norm_nonneg p.1) (Real.sqrt_nonneg θ)]
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at h2
  exact h2

/-- **The two scales are comparable on `θ/4 ≤ |z|² ≤ 3/4`.** -/
theorem sigma_sth_comparable {θ T : ℝ} {p : V × ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hT : T ≤ (θ / 4) ^ 2) (hp : p.2 ∈ Ico (-T) 0) (h1 : θ / 4 ≤ ‖p.1‖ ^ 2)
    (h2 : ‖p.1‖ ^ 2 ≤ 3 / 4) : sigma p ≤ 3 * sth θ p.1 ∧ sth θ p.1 ≤ 3 * sigma p := by
  have hρ := sqrt_neg_le hθ.le hT hp
  have hρ0 := Real.sqrt_nonneg (-p.2)
  have hσ := sigma_pos p hp.2
  have hσ2 := sigma_sq_eq p
  have hs : sth θ p.1 = Real.sqrt (‖p.1‖ ^ 2 + θ) := sth_eq (by linarith)
  have hs0 : 0 < sth θ p.1 := sth_pos hθ p.1
  have hs2 : sth θ p.1 ^ 2 = ‖p.1‖ ^ 2 + θ := by
    rw [hs]
    exact Real.sq_sqrt (by positivity)
  constructor
  · have h3 : sigma p ^ 2 ≤ sth θ p.1 ^ 2 := by
      rw [hσ2, hs2]
      linarith
    have h4 : sigma p ≤ sth θ p.1 := (pow_le_pow_iff_left₀ hσ.le hs0.le two_ne_zero).1 h3
    linarith
  · have h3 : sth θ p.1 ^ 2 ≤ (3 * sigma p) ^ 2 := by
      rw [hs2, mul_pow, hσ2]
      nlinarith
    exact (pow_le_pow_iff_left₀ hs0.le (by positivity) two_ne_zero).1 h3

/-! ### Change of scale -/

/-- From the scale `s_θ` to the scale `σ`, for a function that vanishes off
`θ/4 ≤ |z|² ≤ 3/4`. -/
theorem WH.sigma_of_sth {α v M θ T : ℝ} {f : V × ℝ → E} {Ω : Set (V × ℝ)}
    (hf : WH α (1 / 64) (fun p : V × ℝ => sth θ p.1) Ω v M f)
    (hΩ : Ω ⊆ {p : V × ℝ | p.2 ∈ Ico (-T) 0}) (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hT : T ≤ (θ / 4) ^ 2) (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hsupp : ∀ p ∈ Ω, f p ≠ 0 → θ / 4 ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4) :
    WH α (1 / 64) (sigma (V := V)) Ω v
      (M * ((3 : ℝ) * 2) ^ (|v| + |v - α|)
        * (1 + (1 + 2 ^ |v|) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α))) f := by
  have hsc : IsScale (1 / 64) 2 (sigma (V := V)) Ω :=
    (isScale_sigma (V := V) (by norm_num : (1 : ℝ) / 64 ≤ 1 / 2)).mono le_rfl
      fun p hp => (hΩ hp).2
  have h1 := hf.scale_supp (s' := sigma (V := V)) (k := 3) hsc hM (by norm_num) (by norm_num)
    (fun p _ => sth_pos hθ p.1)
    (fun p hp hne => by
      obtain ⟨c1, c2⟩ := sigma_sth_comparable hθ hθ4 hT (hΩ hp) (hsupp p hp hne).1
        (hsupp p hp hne).2
      exact ⟨c2, c1⟩)
  exact h1.radius_ge hsc (mul_nonneg hM (Real.rpow_nonneg (by norm_num) _))
    (lt_min (by norm_num) (by norm_num)) hα

/-- From the scale `σ` to the scale `s_θ`, with the radius `1/4` of the
forward block, for a function that vanishes off `θ/4 ≤ |z|² ≤ 3/4`. -/
theorem WH.sth_of_sigma {α v M θ T : ℝ} {f : V × ℝ → E} {Ω : Set (V × ℝ)}
    (hf : WH α (1 / 64) (sigma (V := V)) Ω v M f)
    (hΩ : Ω ⊆ {p : V × ℝ | p.2 ∈ Ico (-T) 0}) (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hT : T ≤ (θ / 4) ^ 2) (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hsupp : ∀ p ∈ Ω, f p ≠ 0 → θ / 4 ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4) :
    WH α (1 / 4) (fun p : V × ℝ => sth θ p.1) Ω v
      (M * ((3 : ℝ) * 2) ^ (|v| + |v - α|)
        * (1 + (1 + 2 ^ |v|) * (min (1 / 4) (1 / 64 / (3 * 2)) : ℝ) ^ (-α))) f := by
  have hsc : IsScale (1 / 4) 2 (fun p : V × ℝ => sth θ p.1) Ω :=
    isScale_sth hθ (by norm_num) Ω
  have h1 := hf.scale_supp (s' := fun p : V × ℝ => sth θ p.1) (k := 3) hsc hM (by norm_num)
    (by norm_num) (fun p hp => sigma_pos p (hΩ hp).2)
    (fun p hp hne => sigma_sth_comparable hθ hθ4 hT (hΩ hp) (hsupp p hp hne).1
      (hsupp p hp hne).2)
  exact h1.radius_ge hsc (mul_nonneg hM (Real.rpow_nonneg (by norm_num) _))
    (lt_min (by norm_num) (by norm_num)) hα

/-- The jets of a function that vanishes near the points off
`θ/2 ≤ |z|² ≤ 1/2`, from the scale `s_θ` to the scale `σ`. -/
theorem WJ.sigma_of_sth {α w M θ T : ℝ} {n : ℕ} {u : ℝ → V → E} {Ω : Set (V × ℝ)}
    (hu : WJ α (1 / 64) (fun p : V × ℝ => sth θ p.1) Ω w M n u)
    (hΩ : Ω ⊆ {p : V × ℝ | p.2 ∈ Ico (-T) 0}) (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hT : T ≤ (θ / 4) ^ 2) (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hsupp : ∀ t z, ‖z‖ ^ 2 < θ / 2 ∨ 1 / 2 < ‖z‖ ^ 2 → u t z = 0) :
    WJ α (1 / 64) (sigma (V := V)) Ω w
      (M * ((3 : ℝ) * 2) ^ (|w| + n + (|w - α| + n))
        * (1 + (1 + 2 ^ (|w| + n)) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α))) n u := by
  intro j hj
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsc : IsScale (1 / 64) 2 (sigma (V := V)) Ω :=
    (isScale_sigma (V := V) (by norm_num : (1 : ℝ) / 64 ≤ 1 / 2)).mono le_rfl
      fun p hp => (hΩ hp).2
  -- the jets vanish off the region
  have hjet : ∀ p ∈ Ω, iteratedFDeriv ℝ j (u p.2) p.1 ≠ 0 →
      θ / 4 ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4 := by
    intro p _ hne
    have hcont : Continuous fun y : V => ‖y‖ ^ 2 := continuous_norm.pow 2
    constructor
    · by_contra hcon
      have hlt : ‖p.1‖ ^ 2 < θ / 2 := by linarith [not_le.1 hcon]
      have hev : u p.2 =ᶠ[𝓝 p.1] fun _ => 0 := by
        filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hlt] with y hy
        exact hsupp p.2 y (Or.inl hy)
      apply hne
      rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
      simp
    · by_contra hcon
      have hlt : 1 / 2 < ‖p.1‖ ^ 2 := by linarith [not_le.1 hcon]
      have hev : u p.2 =ᶠ[𝓝 p.1] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hlt] with y hy
        exact hsupp p.2 y (Or.inr hy)
      apply hne
      rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
      simp
  have h1 := (hu j hj).sigma_of_sth hΩ hθ hθ4 hT hM hα hjet
  refine h1.mono hsc.pos ?_
  -- the constants
  have e1 : |w - (j : ℝ)| ≤ |w| + n := by
    have := abs_sub w (j : ℝ)
    rw [abs_of_nonneg hj0] at this
    linarith
  have e2 : |w - (j : ℝ) - α| ≤ |w - α| + n := by
    have e3 : w - (j : ℝ) - α = w - α - j := by ring
    rw [e3]
    have := abs_sub (w - α) (j : ℝ)
    rw [abs_of_nonneg hj0] at this
    linarith
  have h6 : ((3 : ℝ) * 2) ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|)
      ≤ ((3 : ℝ) * 2) ^ (|w| + n + (|w - α| + n)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h7 : (2 : ℝ) ^ |w - (j : ℝ)| ≤ 2 ^ (|w| + n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) e1
  have hr : 0 ≤ (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) :=
    Real.rpow_nonneg (le_min (by norm_num) (by norm_num)) _
  have h8 : 1 + (1 + (2 : ℝ) ^ |w - (j : ℝ)|) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α)
      ≤ 1 + (1 + (2 : ℝ) ^ (|w| + n)) * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) := by
    have := mul_le_mul_of_nonneg_right h7 hr
    nlinarith
  have h9 : 0 ≤ ((3 : ℝ) * 2) ^ (|w - (j : ℝ)| + |w - (j : ℝ) - α|) :=
    Real.rpow_nonneg (by norm_num) _
  have h10 : 0 ≤ 1 + (1 + (2 : ℝ) ^ (|w| + n))
      * (min (1 / 64) (1 / 64 / (3 * 2)) : ℝ) ^ (-α) := by
    have h11 : 0 ≤ (2 : ℝ) ^ (|w| + n) := Real.rpow_nonneg (by norm_num) _
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ (|w| + n)) hr
    linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left h6 hM) h8
    (by
      have h11 : 0 ≤ (2 : ℝ) ^ |w - (j : ℝ)| := Real.rpow_nonneg (by norm_num) _
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + (2 : ℝ) ^ |w - (j : ℝ)|) hr
      linarith)
    (mul_nonneg hM (Real.rpow_nonneg (by norm_num) _))

/-! ### The cut-offs -/

/-- The difference of two functions with weighted jets. -/
theorem WJ.sub' {α a w M N : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} {n : ℕ} {u v : ℝ → V → E}
    (hus : ∀ t, ContDiff ℝ n (u t)) (hvs : ∀ t, ContDiff ℝ n (v t))
    (hu : WJ α a s Ω w M n u) (hv : WJ α a s Ω w N n v) :
    WJ α a s Ω w (M + N) n (fun t x => u t x - v t x) := by
  intro j hj
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have e : (fun p : V × ℝ => iteratedFDeriv ℝ j (fun x => u p.2 x - v p.2 x) p.1)
      = fun p => iteratedFDeriv ℝ j (u p.2) p.1 - iteratedFDeriv ℝ j (v p.2) p.1 := by
    funext p
    exact iteratedFDeriv_sub_apply (f := u p.2) (g := v p.2)
      ((hus p.2).of_le hjn).contDiffAt ((hvs p.2).of_le hjn).contDiffAt
  show WH α a s Ω (w - j) (M + N)
    (fun p => iteratedFDeriv ℝ j (fun x => u p.2 x - v p.2 x) p.1)
  rw [e]
  exact (hu j hj).sub (hv j hj)

/-- The cut-off of the outer problem: `χ(4|z|²) - χ(2|z|²/θ)`. It is one for
`θ ≤ |z|² ≤ 1/4` and vanishes for `|z|² ≤ θ/2` and for `|z|² ≥ 1/2`. -/
noncomputable def cut0 (θ : ℝ) (z : V) : ℝ := chiV (1 / 4) z - chiV (θ / 2) z

theorem contDiff_cut0 (θ : ℝ) : ContDiff ℝ ∞ (cut0 (V := V) θ) :=
  (contDiff_chiV _).sub (contDiff_chiV _)

theorem cut0_of_le {θ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) {z : V} (hz : ‖z‖ ^ 2 ≤ θ / 2) :
    cut0 θ z = 0 := by
  unfold cut0
  rw [chiV_of_le (by norm_num) (by linarith), chiV_of_le (by positivity) hz, sub_self]

theorem cut0_of_ge {θ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) {z : V} (hz : 1 / 2 ≤ ‖z‖ ^ 2) :
    cut0 θ z = 0 := by
  unfold cut0
  rw [chiV_of_ge (by norm_num) (by linarith), chiV_of_ge (by positivity) (by linarith), sub_self]

theorem cut0_rotate (θ : ℝ) (Q : V ≃ₗᵢ[ℝ] V) (z : V) : cut0 θ (Q z) = cut0 θ z := by
  unfold cut0
  rw [chiV_rotate, chiV_rotate]

/-- **The cut-off of the outer problem has weighted jets of weight zero** for
the scale `s_θ`, uniformly in `θ`. -/
theorem WJ_cut0 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (α θ : ℝ) (Ω : Set (V × ℝ)), 0 < θ → θ ≤ 1 / 4 →
    0 ≤ α → α ≤ 1 →
    WJ α (1 / 64) (fun p : V × ℝ => sth θ p.1) Ω 0 A 4 (fun _ => cut0 (V := V) θ) := by
  obtain ⟨B₁, hB₁, hb₁, -⟩ := radFn_data (V := V) (φ := fun s => chi (s / (1 / 4)))
    (contDiff_chi.comp (contDiff_id.div_const _)) (s₁ := 1 / 2) (c₀ := 0)
    (fun s hs => chi_of_ge (by
      rw [le_div_iff₀ (by norm_num)]
      linarith))
  obtain ⟨B₂, hB₂, H₂⟩ := WJ_chiV (V := V) 4
  refine ⟨2 * (B₁ * 1 ^ (4 + 1)) + 2 * (B₂ * 4 ^ (4 + 1)), by positivity, ?_⟩
  intro α θ Ω hθ hθ4 hα hα1
  have hpos : ∀ p ∈ Ω, 0 < (fun p : V × ℝ => sth θ p.1) p := fun p _ => sth_pos hθ p.1
  have h1 : WJ α (1 / 64) (fun p : V × ℝ => sth θ p.1) Ω 0 (2 * (B₁ * 1 ^ (4 + 1))) 4
      (fun _ => chiV (V := V) (1 / 4)) :=
    WJ_of_global (S := 1) (n := 4) hpos (fun p _ => sth_le_one θ p.1) le_rfl hB₁ (by norm_num)
      (by norm_num) hα hα1 (contDiff_infty.1 (contDiff_chiV _) _) (fun j hj z => hb₁ j hj z)
  have h2 := H₂ α (1 / 64) 4 (θ / 2) (fun p : V × ℝ => sth θ p.1) Ω (by positivity)
    (by norm_num) hpos (by norm_num) (by norm_num) hα hα1
    (fun p _ z hz hz1 hz2 => by
      -- `s_θ(p) ≤ |p| + √θ ≤ |z| + s_θ(p)/64 + √θ ≤ 2 √θ + s_θ(p)/64`
      have hsq := Real.sq_sqrt hθ.le
      have hsq2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ θ / 2)
      have hs0 := sth_pos hθ p.1
      have hzn := norm_nonneg z
      have hpn := norm_nonneg p.1
      have hr0 := Real.sqrt_nonneg θ
      have hr2 := Real.sqrt_nonneg (θ / 2)
      have h3 : sth θ p.1 ≤ ‖p.1‖ + Real.sqrt θ := by
        refine (min_le_left _ _).trans ?_
        have h4 := Real.sqrt_le_sqrt
          (by nlinarith : ‖p.1‖ ^ 2 + θ ≤ (‖p.1‖ + Real.sqrt θ) ^ 2)
        rwa [Real.sqrt_sq (by positivity)] at h4
      have h5 : ‖p.1‖ ≤ ‖z‖ + 1 / 64 * sth θ p.1 := by
        have h6 := norm_sub_norm_le p.1 z
        have h7 : ‖p.1 - z‖ = ‖z - p.1‖ := norm_sub_rev _ _
        linarith
      have h8 : ‖z‖ ≤ Real.sqrt θ := by
        have h9 := Real.sqrt_le_sqrt (by linarith : ‖z‖ ^ 2 ≤ θ)
        rwa [Real.sqrt_sq hzn] at h9
      have h10 : Real.sqrt θ ≤ 3 / 2 * Real.sqrt (θ / 2) := by
        have h11 : Real.sqrt θ ^ 2 ≤ (3 / 2 * Real.sqrt (θ / 2)) ^ 2 := by
          rw [mul_pow, hsq, hsq2]
          nlinarith
        exact (pow_le_pow_iff_left₀ hr0 (by positivity) two_ne_zero).1 h11
      linarith)
  have h3 := WJ.sub' (fun _ => contDiff_infty.1 (contDiff_chiV (V := V) (1 / 4)) 4)
    (fun _ => contDiff_infty.1 (contDiff_chiV (V := V) (θ / 2)) 4) h1 h2
  exact h3

/-- **The cut-offs of the inner problem have weighted jets of weight zero** for
the scale `σ`, uniformly in the inner radius. -/
theorem WJ_chiV_sigma : ∃ A : ℝ, 0 ≤ A ∧ ∀ (α θ μ T : ℝ) (Ω : Set (V × ℝ)), 0 < θ → θ ≤ μ →
    T ≤ (θ / 4) ^ 2 → Ω ⊆ {p : V × ℝ | p.2 ∈ Ico (-T) 0} → 0 ≤ α → α ≤ 1 →
    WJ α (1 / 64) (sigma (V := V)) Ω 0 A 4 (fun _ => chiV (V := V) μ) := by
  obtain ⟨B₂, hB₂, H₂⟩ := WJ_chiV (V := V) 4
  refine ⟨2 * (B₂ * 3 ^ (4 + 1)), by positivity, ?_⟩
  intro α θ μ T Ω hθ hθμ hT hΩ hα hα1
  have hμ : 0 < μ := hθ.trans_le hθμ
  refine H₂ α (1 / 64) 3 μ (sigma (V := V)) Ω hμ (by norm_num)
    (fun p hp => sigma_pos p (hΩ hp).2) (by norm_num) (by norm_num) hα hα1
    (fun p hp z hz hz1 hz2 => ?_)
  -- `σ(p) ≤ |p| + √θ/2 ≤ |z| + σ(p)/64 + √μ/2 ≤ (√2 + 1/2) √μ + σ(p)/64`
  have hσ0 := sigma_pos p (hΩ hp).2
  have h3 := sigma_le_norm_add hθ hT (hΩ hp)
  have hzn := norm_nonneg z
  have hr0 := Real.sqrt_nonneg μ
  have hsqμ := Real.sq_sqrt hμ.le
  have h4 : Real.sqrt θ ≤ Real.sqrt μ := Real.sqrt_le_sqrt hθμ
  have h5 : ‖p.1‖ ≤ ‖z‖ + 1 / 64 * sigma p := by
    have h6 := norm_sub_norm_le p.1 z
    have h7 : ‖p.1 - z‖ = ‖z - p.1‖ := norm_sub_rev _ _
    linarith
  have h8 : ‖z‖ ≤ 3 / 2 * Real.sqrt μ := by
    have h9 : ‖z‖ ^ 2 ≤ (3 / 2 * Real.sqrt μ) ^ 2 := by
      rw [mul_pow, hsqμ]
      nlinarith
    exact (pow_le_pow_iff_left₀ hzn (by positivity) two_ne_zero).1 h9
  linarith

end Calabi.Weighted
