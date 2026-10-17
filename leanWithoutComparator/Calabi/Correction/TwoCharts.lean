import Calabi.Correction.ChartMaps
import Calabi.Correction.ProfileChart
import Calabi.Correction.RealSolvers

/-!
# Quantities of order zero in the two charts

The construction of Section 6 of the manuscript is carried out in two flat
charts of the momentum interval: `ℝ¹⁸` with `x = |z|²` and `ℝ⁶` with
`x = 1 - |w|²`. A quantity of order zero (a source, a coefficient, the value of
an operator on a solution) is a function `g(t, x)`. Its size is measured by the
pair of weighted two-point bounds `B0`:

* for the scale `σ` on `dom0 T = {(z, t) : -T ≤ t < 0, |z|² ≤ 3/4}`, of
  `g(t, |z|²)`;
* for the constant scale `1` on `dom1 T = {(w, t) : -T ≤ t < 0, |w|² ≤ 7/8}`,
  of `g(t, 1 - |w|²)`.

This file contains the algebra of `B0` (sums, products, lowering of the
weight), the passage from the scaled bounds of `Osc.lean` (`B0.of_oscE`), and
the extension by zero of a two-point bound on a chart domain to the whole
space (`WH.extend_zero0`, `WH.extend_zero1`).
-/

open Set
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Osc

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E]

/-! ### Elementary bounds -/

theorem norm_fst_sub_le_pdist (p q : V × ℝ) : ‖p.1 - q.1‖ ≤ pdist p q := by
  unfold pdist
  linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]

theorem norm_le_sigma (p : V × ℝ) : ‖p.1‖ ≤ sigma p := by
  unfold sigma
  have h : ‖p.1‖ ^ 2 ≤ ‖p.1‖ ^ 2 + Real.sqrt (-p.2) := by linarith [Real.sqrt_nonneg (-p.2)]
  have h1 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _)] at h1

theorem sigma_le_norm_add_one {T : ℝ} {p : V × ℝ} (hT : T ≤ 1) (hp : p.2 ∈ Ico (-T) 0) :
    sigma p ≤ ‖p.1‖ + 1 := by
  unfold sigma
  have h1 : Real.sqrt (-p.2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (by linarith [hp.1] : -p.2 ≤ (1 : ℝ))
    rwa [Real.sqrt_one] at h
  have h2 : ‖p.1‖ ^ 2 + Real.sqrt (-p.2) ≤ (‖p.1‖ + 1) ^ 2 := by
    nlinarith [norm_nonneg p.1]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (by positivity)] at h3

theorem sigma_le_two {T : ℝ} {p : V × ℝ} (hT : T ≤ 1) (hp : p.2 ∈ Ico (-T) 0)
    (hz : ‖p.1‖ ^ 2 ≤ 1) : sigma p ≤ 2 := by
  have h1 := sigma_le_norm_add_one hT hp
  have h2 : ‖p.1‖ ≤ 1 := by
    have := norm_nonneg p.1
    nlinarith
  linarith

/-- If `u² > A` and `v ≥ (1 - r) u - r`, then `v² > (1 - r)(1 - 2r) A - r`. -/
theorem sq_gt_of_near {u v r A B : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r) (hr4 : r ≤ 1 / 4)
    (h : (1 - r) * u - r ≤ v) (hA1 : 1 / 4 ≤ A) (hA : A < u ^ 2)
    (hB : B < (1 - r) * (1 - 2 * r) * A - r) : B < v ^ 2 := by
  have hu2 : 1 / 2 < u := by nlinarith
  have hpos : 0 ≤ (1 - r) * u - r := by nlinarith
  have h3 : ((1 - r) * u - r) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hpos h 2
  have h1 : 0 ≤ (1 - r) * (1 - 2 * r) := mul_nonneg (by linarith) (by linarith)
  have h2 : (1 - r) * (1 - 2 * r) * A ≤ (1 - r) * (1 - 2 * r) * u ^ 2 :=
    mul_le_mul_of_nonneg_left hA.le h1
  have h4 : (1 - r) * (1 - 2 * r) * u ^ 2 - r ≤ ((1 - r) * u - r) ^ 2 := by
    have h5 : 0 ≤ r * (1 - r) * (u - 1) ^ 2 :=
      mul_nonneg (mul_nonneg hr (by linarith)) (sq_nonneg _)
    nlinarith [sq_nonneg r]
  linarith

/-! ### Extension by zero -/

/-- A function on the chart at `x = 0` that vanishes for `|z|² > 5/8` and has
a two-point bound on `|z|² ≤ 3/4` has the same bound on the whole space. -/
theorem WH.extend_zero0 {α a v M T : ℝ} {f : V × ℝ → E}
    (hf : WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4} v M f)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (ha64 : a ≤ 1 / 64) (hT : T ≤ 1)
    (hsupp : ∀ p : V × ℝ, 5 / 8 < ‖p.1‖ ^ 2 → f p = 0) :
    WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0} v M f := by
  refine WH.of_local hf hM (fun p hp => sigma_pos p hp.2) (fun p hp => ?_)
    (fun p hp q hq hd => ?_)
  · by_cases h : ‖p.1‖ ^ 2 ≤ 3 / 4
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr (hsupp p (by linarith [not_le.1 h]))
  · have hxd : |‖p.1‖ - ‖q.1‖| ≤ pdist p q :=
      (abs_norm_sub_norm_le _ _).trans (norm_fst_sub_le_pdist p q)
    have h1 := abs_le.1 (hxd.trans hd)
    have hpn := norm_nonneg p.1
    have hqn := norm_nonneg q.1
    by_cases hp' : ‖p.1‖ ^ 2 ≤ 3 / 4
    · by_cases hq' : ‖q.1‖ ^ 2 ≤ 3 / 4
      · exact Or.inl ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
      · right
        have hσ : sigma p ≤ 2 := sigma_le_two hT hp (by linarith)
        have hq2 : 3 / 4 < ‖q.1‖ ^ 2 := not_le.1 hq'
        have h2 := mul_le_mul_of_nonneg_left hσ ha
        have h3 := mul_nonneg ha hqn
        have hpg : 5 / 8 < ‖p.1‖ ^ 2 :=
          sq_gt_of_near (u := ‖q.1‖) (v := ‖p.1‖) (r := 2 * a) hqn (by linarith) (by linarith)
            (by nlinarith [h1.1]) (by norm_num) hq2 (by nlinarith [sq_nonneg a])
        exact ⟨hsupp p hpg, hsupp q (by linarith)⟩
    · right
      have hp2 : 3 / 4 < ‖p.1‖ ^ 2 := not_le.1 hp'
      have hσ := sigma_le_norm_add_one hT hp
      have h2 := mul_le_mul_of_nonneg_left hσ ha
      have hqg : 5 / 8 < ‖q.1‖ ^ 2 :=
        sq_gt_of_near (u := ‖p.1‖) (v := ‖q.1‖) (r := a) hpn ha (by linarith)
          (by nlinarith [h1.2]) (by norm_num) hp2 (by nlinarith [sq_nonneg a])
      exact ⟨hsupp p (by linarith), hsupp q hqg⟩

/-- A function on the chart at `x = 1` that vanishes for `|w|² > 13/16` and has
a two-point bound, for the constant scale, on `|w|² ≤ 7/8` has the same bound
on the whole space. -/
theorem WH.extend_zero1 {α a v M T : ℝ} {f : V × ℝ → E}
    (hf : WH α a (fun _ : V × ℝ => (1 : ℝ))
      {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 7 / 8} v M f)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (ha64 : a ≤ 1 / 64)
    (hsupp : ∀ p : V × ℝ, 13 / 16 < ‖p.1‖ ^ 2 → f p = 0) :
    WH α a (fun _ : V × ℝ => (1 : ℝ)) {p : V × ℝ | p.2 ∈ Ico (-T) 0} v M f := by
  refine WH.of_local hf hM (fun p _ => zero_lt_one) (fun p hp => ?_)
    (fun p hp q hq hd => ?_)
  · by_cases h : ‖p.1‖ ^ 2 ≤ 7 / 8
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr (hsupp p (by linarith [not_le.1 h]))
  · have hxd : |‖p.1‖ - ‖q.1‖| ≤ pdist p q :=
      (abs_norm_sub_norm_le _ _).trans (norm_fst_sub_le_pdist p q)
    have hd' : pdist p q ≤ a := by
      have h := hd
      rwa [mul_one] at h
    have h1 := abs_le.1 (hxd.trans hd')
    have hpn := norm_nonneg p.1
    have hqn := norm_nonneg q.1
    have h3 := mul_nonneg ha hqn
    have h4 := mul_nonneg ha hpn
    by_cases hp' : ‖p.1‖ ^ 2 ≤ 7 / 8
    · by_cases hq' : ‖q.1‖ ^ 2 ≤ 7 / 8
      · exact Or.inl ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
      · right
        have hq2 : 7 / 8 < ‖q.1‖ ^ 2 := not_le.1 hq'
        have hpg : 13 / 16 < ‖p.1‖ ^ 2 :=
          sq_gt_of_near (u := ‖q.1‖) (v := ‖p.1‖) (r := a) hqn ha (by linarith)
            (by nlinarith [h1.1]) (by norm_num) hq2 (by nlinarith [sq_nonneg a])
        exact ⟨hsupp p hpg, hsupp q (by linarith)⟩
    · right
      have hp2 : 7 / 8 < ‖p.1‖ ^ 2 := not_le.1 hp'
      have hqg : 13 / 16 < ‖q.1‖ ^ 2 :=
        sq_gt_of_near (u := ‖p.1‖) (v := ‖q.1‖) (r := a) hpn ha (by linarith)
          (by nlinarith [h1.2]) (by norm_num) hp2 (by nlinarith [sq_nonneg a])
      exact ⟨hsupp p (by linarith), hsupp q hqg⟩

/-! ### The two charts -/

/-- The space of the chart at `x = 1`. -/
abbrev Flat6 := EuclideanSpace ℝ (Fin 6)

/-- A unit vector of the chart at `x = 0`. -/
noncomputable def e18 : Flat18 := EuclideanSpace.single 0 1

/-- A unit vector of the chart at `x = 1`. -/
noncomputable def e6 : Flat6 := EuclideanSpace.single 0 1

theorem norm_e18 : ‖e18‖ = 1 := by simp [e18]

theorem norm_e6 : ‖e6‖ = 1 := by simp [e6]

/-- The domain of the chart at `x = 0`. -/
def dom0 (T : ℝ) : Set (Flat18 × ℝ) := {p | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 3 / 4}

/-- The domain of the chart at `x = 1`. -/
def dom1 (T : ℝ) : Set (Flat6 × ℝ) := {p | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 7 / 8}

theorem isScale0 (T : ℝ) : IsScale (1 / 64) 2 (sigma (V := Flat18)) (dom0 T) :=
  (isScale_sigma (V := Flat18) (by norm_num : (1 : ℝ) / 64 ≤ 1 / 2)).mono le_rfl
    fun p hp => hp.1.2

theorem isScale1 (T : ℝ) : IsScale (1 / 64) 1 (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) :=
  IsScale.const one_pos

theorem sigma_le_two0 {T : ℝ} (hT : T ≤ 1) : ∀ p ∈ dom0 T, sigma p ≤ 2 :=
  fun p hp => sigma_le_two hT hp.1 (by linarith [hp.2])

/-- **The two-chart bound of a quantity of order zero.** -/
def B0 (α T v M : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) v M (fun p => g p.2 (‖p.1‖ ^ 2)) ∧
    WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) v M (fun p => g p.2 (1 - ‖p.1‖ ^ 2))

section Algebra

variable {α T v M N : ℝ} {g g' : ℝ → ℝ → ℝ}

theorem B0.mono (h : B0 α T v M g) (hMN : M ≤ N) : B0 α T v N g :=
  ⟨h.1.mono (isScale0 T).pos hMN, h.2.mono (isScale1 T).pos hMN⟩

theorem B0.congr (h : B0 α T v M g)
    (hg : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, g' t x = g t x) : B0 α T v M g' := by
  refine ⟨h.1.congr fun p hp => hg p.2 hp.1 _ ⟨sq_nonneg _, by linarith [hp.2]⟩,
    h.2.congr fun p hp => hg p.2 hp.1 _ ⟨by linarith [hp.2], by linarith [sq_nonneg ‖p.1‖]⟩⟩

theorem B0.add (h : B0 α T v M g) (h' : B0 α T v N g') :
    B0 α T v (M + N) (fun t x => g t x + g' t x) :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

theorem B0.sub (h : B0 α T v M g) (h' : B0 α T v N g') :
    B0 α T v (M + N) (fun t x => g t x - g' t x) :=
  ⟨h.1.sub h'.1, h.2.sub h'.2⟩

theorem B0.neg (h : B0 α T v M g) : B0 α T v M (fun t x => -g t x) :=
  ⟨h.1.neg, h.2.neg⟩

theorem B0.const_mul (k : ℝ) (h : B0 α T v M g) : B0 α T v (|k| * M) (fun t x => k * g t x) :=
  ⟨h.1.const_smul k, h.2.const_smul k⟩

/-- Products: the weights add. -/
theorem B0.mul {v' : ℝ} (h : B0 α T v M g) (h' : B0 α T v' N g') (hM : 0 ≤ M) (hN : 0 ≤ N) :
    B0 α T (v + v') ((1 + 2 ^ |v|) * M * N) (fun t x => g t x * g' t x) := by
  refine ⟨WH.mul (isScale0 T) hM hN h.1 h'.1, ?_⟩
  refine (WH.mul (isScale1 T) hM hN h.2 h'.2).mono (isScale1 T).pos ?_
  have h1 : (1 : ℝ) ^ |v| ≤ 2 ^ |v| := by
    rw [Real.one_rpow]
    exact Real.one_le_rpow (by norm_num) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hM) hN

/-- Lowering the weight. -/
theorem B0.weight {v' : ℝ} (h : B0 α T v M g) (hM : 0 ≤ M) (hT : T ≤ 1) (hv : v' ≤ v) :
    B0 α T v' (M * 2 ^ (v - v')) g :=
  ⟨h.1.weight hM (isScale0 T).pos (sigma_le_two0 hT) hv,
    h.2.weight hM (isScale1 T).pos (fun _ _ => by norm_num) hv⟩

end Algebra

/-! ### From the momentum coordinate to the two charts -/

/-- **Scaled bounds in the momentum coordinate give two-chart bounds**: the
order `n` becomes the weight `2n`. -/
theorem B0.of_oscE (α : ℝ) (n : ℤ) (hα : 0 ≤ α) (hα1 : α ≤ 1) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (T M : ℝ) (c : ℝ → ℝ → ℝ), OscE T n M c → 0 ≤ M → T ≤ 1 →
      B0 α T ((2 * n : ℤ) : ℝ) (K * M) c := by
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : ℝ,
      K₀ = 2 * (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) := ⟨_, rfl⟩
  have hK₀ : 0 ≤ K₀ := by
    rw [hK₀def]
    positivity
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = (3 : ℝ) ^ (|((2 * n : ℤ) : ℝ)| + |((2 * n : ℤ) : ℝ) - α|)
      * (1 / (1 / 3)) ^ α := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by
    rw [hK₁def]
    positivity
  refine ⟨K₀ + K₀ * K₁, by positivity, ?_⟩
  intro T M c h hM hT
  have hM₀ : 0 ≤ K₀ * M := mul_nonneg hK₀ hM
  have hfull := OscE.toWH (V := Flat18) (a := 1 / 2) h hM hα hα1 le_rfl
  have e0 : 2 * ((1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M) = K₀ * M := by
    rw [hK₀def]
    ring
  rw [e0] at hfull
  have hposD : ∀ p ∈ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1}, 0 < sigma p :=
    fun p hp => sigma_pos p hp.1.2
  constructor
  · refine ((hfull.radius_le hposD (by norm_num : (1 : ℝ) / 64 ≤ 1 / 2)).restrict
      (fun p hp => ⟨hp.1, by linarith [hp.2]⟩)).mono (isScale0 T).pos ?_
    linarith [mul_nonneg (mul_nonneg hK₀ hK₁) hM]
  · have hsw := hfull.swap (e := e18) (s' := fun _ : Flat6 × ℝ => (1 : ℝ)) (Ω' := dom1 T)
      (k := 3) (δ := 1 / 3) norm_e18 hM₀ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hα
      (fun p hp => ⟨hp.1, by
        rw [norm_sq_swapPt norm_e18 (by linarith [hp.2])]
        linarith [sq_nonneg ‖p.1‖]⟩)
      (fun p hp => by
        have := hp.2
        norm_num
        linarith)
      hposD (fun _ _ => zero_lt_one)
      (fun p hp => by
        have h1 : sigma (swapPt e18 p) ≤ 2 := sigma_le_two hT hp.1 (by
          rw [norm_sq_swapPt norm_e18 (by linarith [hp.2])]
          linarith [sq_nonneg ‖p.1‖])
        linarith)
      (fun p hp => by
        have h1 := norm_le_sigma (swapPt e18 p)
        rw [norm_swapPt norm_e18] at h1
        have h2 := Real.sqrt_le_sqrt (by linarith [hp.2] : ((1 : ℝ) / 3) ^ 2 ≤ 1 - ‖p.1‖ ^ 2)
        rw [Real.sqrt_sq (by norm_num)] at h2
        linarith)
    refine ((hsw.radius_le (fun _ _ => zero_lt_one) (by norm_num)).congr
      (fun p hp => ?_)).mono (isScale1 T).pos ?_
    · show c p.2 (1 - ‖p.1‖ ^ 2) = c (swapPt e18 p).2 (‖(swapPt e18 p).1‖ ^ 2)
      rw [norm_sq_swapPt norm_e18 (by linarith [hp.2])]
      rfl
    · rw [hK₁def]
      linarith [mul_nonneg hK₀ hM]

end Calabi.Weighted
