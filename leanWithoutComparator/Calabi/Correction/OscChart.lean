import Calabi.Correction.WindowConvert
import Calabi.Correction.Osc

/-!
# From the momentum coordinate to the flat chart

A function `c(t, x)` with scaled bounds of order `n` in the momentum
coordinate (`Osc.lean`) gives, in a flat chart `x = |z|²`, a function with a
weighted two-point bound of weight `2n` for the scale
`σ = (|z|² + √(-t))^{1/2}` (`OscE.toWH`): the square of `σ` is
`ς = x + √(-t)`, one `x`-derivative costs `ς⁻¹ = σ⁻²` and `|x - x′| ≤ 3σ |z - z′|`.
This turns the one-dimensional estimates of Lemma 6.2 into the hypotheses of
the weighted theory.
-/

open Set

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Osc

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `σ² = ς`. -/
theorem sigma_sq (p : V × ℝ) : sigma p ^ 2 = vs p.2 (‖p.1‖ ^ 2) := by
  unfold sigma vs
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))]

theorem zpow_le_of_comparable {u v k : ℝ} (hu : 0 < u) (hv : 0 < v) (hk : 1 ≤ k)
    (h1 : u ≤ k * v) (h2 : v ≤ k * u) (m : ℤ) : u ^ m ≤ k ^ |(m : ℝ)| * v ^ m := by
  have h := rpow_le_of_comparable hu hv hk h1 h2 (m : ℝ)
  rwa [Real.rpow_intCast, Real.rpow_intCast] at h

theorem sq_zpow (σ : ℝ) (m : ℤ) : (σ ^ 2) ^ m = σ ^ (2 * m) := by
  rw [zpow_mul, zpow_ofNat]

/-- The powers of `ς` at a nearby point, in terms of `σ` at the centre. -/
theorem vs_zpow_le {σ u : ℝ} (hσ : 0 < σ) (h1 : σ ^ 2 / 4 ≤ u) (h2 : u ≤ 4 * σ ^ 2) (m : ℤ) :
    u ^ m ≤ 4 ^ |(m : ℝ)| * σ ^ ((2 * m : ℤ) : ℝ) := by
  have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
  have hu : 0 < u := by linarith
  have h := zpow_le_of_comparable hu hσ2 (by norm_num : (1 : ℝ) ≤ 4) h2 (by linarith) m
  rw [sq_zpow, ← Real.rpow_intCast σ (2 * m)] at h
  exact h

/-- **A function with scaled bounds in the momentum coordinate has a weighted
two-point bound in the flat chart `x = |z|²`.** -/
theorem OscE.toWH {T : ℝ} {n : ℤ} {M α a : ℝ} {c : ℝ → ℝ → ℝ} (h : OscE T n M c) (hM : 0 ≤ M)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ha2 : a ≤ 1 / 2) :
    WH α a (sigma (V := V)) {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1} ((2 * n : ℤ) : ℝ)
      (2 * ((1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M))
      (fun p => c p.2 (‖p.1‖ ^ 2)) := by
  obtain ⟨cx, ct, h⟩ := h
  have h41 : (0 : ℝ) ≤ 4 ^ |((n - 1 : ℤ) : ℝ)| := Real.rpow_nonneg (by norm_num) _
  have h42 : (0 : ℝ) ≤ 4 ^ |((n - 2 : ℤ) : ℝ)| := Real.rpow_nonneg (by norm_num) _
  have hpos : ∀ p ∈ {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ 1}, 0 < sigma p :=
    fun p hp => sigma_pos p hp.1.2
  have hKM : 0 ≤ (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M :=
    mul_nonneg (by linarith) hM
  refine WH.of_lipschitz hpos hKM (by linarith) hα hα1 (fun p hp => ?_) (fun p hp q hq hd => ?_)
  · -- the size
    have hσ := hpos p hp
    have hx : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, hp.2⟩
    have h1 := h.bound p.2 hp.1 _ hx
    rw [← sigma_sq p, sq_zpow, ← Real.rpow_intCast] at h1
    have h0 : 0 ≤ M * sigma p ^ ((2 * n : ℤ) : ℝ) :=
      mul_nonneg hM (Real.rpow_nonneg hσ.le _)
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    have hK0 : (1 : ℝ)
        ≤ 1 + 3 * (4 : ℝ) ^ |((n - 1 : ℤ) : ℝ)| + (4 : ℝ) ^ |((n - 2 : ℤ) : ℝ)| := by linarith
    calc M * sigma p ^ ((2 * n : ℤ) : ℝ) = 1 * (M * sigma p ^ ((2 * n : ℤ) : ℝ)) := by ring
      _ ≤ (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|)
          * (M * sigma p ^ ((2 * n : ℤ) : ℝ)) := mul_le_mul_of_nonneg_right hK0 h0
      _ = (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M
          * sigma p ^ ((2 * n : ℤ) : ℝ) := by ring
  · -- two points: first move in space, then in time
    have hσ := hpos p hp
    have hd0 := pdist_nonneg p q
    have hx : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, hp.2⟩
    have hx' : ‖q.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, hq.2⟩
    have hsp : pdist p q ≤ sigma p / 2 := by
      have := mul_le_mul_of_nonneg_right ha2 hσ.le
      linarith
    have hxd : ‖p.1 - q.1‖ ≤ pdist p q := by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
    -- the scale at the intermediate point and at the second point
    have hσ1 : |sigma ((q.1, p.2) : V × ℝ) - sigma p| ≤ sigma p / 2 := by
      have h1 := abs_sigma_sub_le (p := ((q.1, p.2) : V × ℝ)) (q := p) hp.1.2.le hp.1.2.le
      have e : pdist ((q.1, p.2) : V × ℝ) p = ‖q.1 - p.1‖ := by
        unfold pdist
        simp
      rw [e, norm_sub_rev] at h1
      linarith
    have hσ2 : |sigma q - sigma p| ≤ sigma p / 2 := by
      have h1 := abs_sigma_sub_le (p := q) (q := p) hq.1.2.le hp.1.2.le
      have e : pdist q p = pdist p q := by
        unfold pdist
        rw [norm_sub_rev, abs_sub_comm]
      rw [e] at h1
      linarith
    obtain ⟨hσ1a, hσ1b⟩ := abs_le.1 hσ1
    obtain ⟨hσ2a, hσ2b⟩ := abs_le.1 hσ2
    have es : sigma p ^ 2 = vs p.2 (‖p.1‖ ^ 2) := sigma_sq p
    have es1 : sigma ((q.1, p.2) : V × ℝ) ^ 2 = vs p.2 (‖q.1‖ ^ 2) := sigma_sq _
    have es2 : sigma q ^ 2 = vs q.2 (‖q.1‖ ^ 2) := sigma_sq q
    have hlo1 : sigma p ^ 2 / 4 ≤ sigma ((q.1, p.2) : V × ℝ) ^ 2 := by nlinarith
    have hhi1 : sigma ((q.1, p.2) : V × ℝ) ^ 2 ≤ 4 * sigma p ^ 2 := by nlinarith
    have hlo2 : sigma p ^ 2 / 4 ≤ sigma q ^ 2 := by nlinarith
    have hhi2 : sigma q ^ 2 ≤ 4 * sigma p ^ 2 := by nlinarith
    have hσsq : 0 < sigma p ^ 2 := pow_pos hσ 2
    -- the step in space
    have hsubx : uIcc (‖p.1‖ ^ 2) (‖q.1‖ ^ 2) ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc hx hx'
    have hbx : ∀ ξ ∈ uIcc (‖p.1‖ ^ 2) (‖q.1‖ ^ 2),
        ‖cx p.2 ξ‖ ≤ M * (4 ^ |((n - 1 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 1) : ℤ) : ℝ)) := by
      intro ξ hξ
      have h1 := h.dx_bound p.2 hp.1 ξ (hsubx hξ)
      have hlo : sigma p ^ 2 / 4 ≤ vs p.2 ξ := by
        have h2 : min (‖p.1‖ ^ 2) (‖q.1‖ ^ 2) ≤ ξ := hξ.1
        unfold vs at es es1 ⊢
        rcases le_total (‖p.1‖ ^ 2) (‖q.1‖ ^ 2) with h3 | h3
        · rw [min_eq_left h3] at h2
          linarith
        · rw [min_eq_right h3] at h2
          linarith
      have hhi : vs p.2 ξ ≤ 4 * sigma p ^ 2 := by
        have h2 : ξ ≤ max (‖p.1‖ ^ 2) (‖q.1‖ ^ 2) := hξ.2
        unfold vs at es es1 ⊢
        rcases le_total (‖p.1‖ ^ 2) (‖q.1‖ ^ 2) with h3 | h3
        · rw [max_eq_right h3] at h2
          linarith
        · rw [max_eq_left h3] at h2
          linarith
      rw [Real.norm_eq_abs]
      exact h1.trans (mul_le_mul_of_nonneg_left (vs_zpow_le hσ hlo hhi (n - 1)) hM)
    have hmvx := (convex_uIcc (‖p.1‖ ^ 2) (‖q.1‖ ^ 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := c p.2) (f' := cx p.2)
      (fun ξ hξ => (h.dx p.2 hp.1.2 ξ (hsubx hξ)).mono hsubx) hbx right_mem_uIcc left_mem_uIcc
    have hnp : ‖p.1‖ ≤ sigma p := by
      have h1 : ‖p.1‖ ^ 2 ≤ sigma p ^ 2 := by
        rw [es]
        unfold vs
        linarith [Real.sqrt_nonneg (-p.2)]
      exact (abs_le_of_sq_le_sq' h1 hσ.le).2
    have hnq : ‖q.1‖ ≤ 2 * sigma p := by
      have h1 : ‖q.1‖ ^ 2 ≤ sigma ((q.1, p.2) : V × ℝ) ^ 2 := by
        rw [es1]
        unfold vs
        linarith [Real.sqrt_nonneg (-p.2)]
      have hσ1pos : 0 ≤ sigma ((q.1, p.2) : V × ℝ) := by linarith
      have := (abs_le_of_sq_le_sq' h1 hσ1pos).2
      linarith
    have hxx : ‖‖p.1‖ ^ 2 - ‖q.1‖ ^ 2‖ ≤ 3 * sigma p * ‖p.1 - q.1‖ := by
      have e : ‖p.1‖ ^ 2 - ‖q.1‖ ^ 2 = (‖p.1‖ - ‖q.1‖) * (‖p.1‖ + ‖q.1‖) := by ring
      rw [e, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (add_nonneg (norm_nonneg p.1) (norm_nonneg q.1))]
      have h1 : |‖p.1‖ - ‖q.1‖| ≤ ‖p.1 - q.1‖ := abs_norm_sub_norm_le _ _
      have h2 : ‖p.1‖ + ‖q.1‖ ≤ 3 * sigma p := by linarith
      calc |‖p.1‖ - ‖q.1‖| * (‖p.1‖ + ‖q.1‖) ≤ ‖p.1 - q.1‖ * (3 * sigma p) :=
            mul_le_mul h1 h2 (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
        _ = 3 * sigma p * ‖p.1 - q.1‖ := by ring
    -- the step in time
    have hsubt : ∀ τ ∈ uIcc p.2 q.2, τ ∈ Ico (-T) 0 := by
      intro τ hτ
      have h1 : min p.2 q.2 ≤ τ := hτ.1
      have h2 : τ ≤ max p.2 q.2 := hτ.2
      exact ⟨(le_min hp.1.1 hq.1.1).trans h1, h2.trans_lt (max_lt hp.1.2 hq.1.2)⟩
    have hbt : ∀ τ ∈ uIcc p.2 q.2,
        ‖ct τ (‖q.1‖ ^ 2)‖ ≤ M * (4 ^ |((n - 2 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 2) : ℤ) : ℝ)) := by
      intro τ hτ
      have hτm := hsubt τ hτ
      have h1 := h.dt_bound τ hτm _ hx'
      have hmono : ∀ {s r : ℝ}, s ≤ r → r ≤ 0 → Real.sqrt (-r) ≤ Real.sqrt (-s) :=
        fun hsr _ => Real.sqrt_le_sqrt (by linarith)
      have hlo : sigma p ^ 2 / 4 ≤ vs τ (‖q.1‖ ^ 2) := by
        have h2 : τ ≤ max p.2 q.2 := hτ.2
        unfold vs at es1 es2 ⊢
        rcases le_total p.2 q.2 with h3 | h3
        · rw [max_eq_right h3] at h2
          have := hmono h2 hq.1.2.le
          linarith
        · rw [max_eq_left h3] at h2
          have := hmono h2 hp.1.2.le
          linarith
      have hhi : vs τ (‖q.1‖ ^ 2) ≤ 4 * sigma p ^ 2 := by
        have h2 : min p.2 q.2 ≤ τ := hτ.1
        unfold vs at es1 es2 ⊢
        rcases le_total p.2 q.2 with h3 | h3
        · rw [min_eq_left h3] at h2
          have := hmono h2 hτm.2.le
          linarith
        · rw [min_eq_right h3] at h2
          have := hmono h2 hτm.2.le
          linarith
      rw [Real.norm_eq_abs]
      exact h1.trans (mul_le_mul_of_nonneg_left (vs_zpow_le hσ hlo hhi (n - 2)) hM)
    have hmvt := (convex_uIcc p.2 q.2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => c τ (‖q.1‖ ^ 2)) (f' := fun τ => ct τ (‖q.1‖ ^ 2))
      (fun τ hτ => (h.dt τ (hsubt τ hτ).2 _ hx').hasDerivWithinAt) hbt right_mem_uIcc
      left_mem_uIcc
    -- the weights
    have ew1 : sigma p ^ ((2 * (n - 1) : ℤ) : ℝ) * sigma p = sigma p ^ (((2 * n : ℤ) : ℝ) - 1) := by
      have e : (((2 * n : ℤ) : ℝ) - 1) = ((2 * (n - 1) : ℤ) : ℝ) + 1 := by
        push_cast
        ring
      rw [e, Real.rpow_add hσ, Real.rpow_one]
    have ew4 : sigma p ^ ((2 * (n - 2) : ℤ) : ℝ) = sigma p ^ (((2 * n : ℤ) : ℝ) - 4) := by
      congr 1
      push_cast
      ring
    have hw1 : 0 ≤ sigma p ^ (((2 * n : ℤ) : ℝ) - 1) := Real.rpow_nonneg hσ.le _
    have hw4 : 0 ≤ sigma p ^ (((2 * n : ℤ) : ℝ) - 4) := Real.rpow_nonneg hσ.le _
    have hA : ‖c p.2 (‖p.1‖ ^ 2) - c p.2 (‖q.1‖ ^ 2)‖
        ≤ 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖ := by
      have h0 : 0 ≤ M * (4 ^ |((n - 1 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 1) : ℤ) : ℝ)) :=
        mul_nonneg hM (mul_nonneg h41 (Real.rpow_nonneg hσ.le _))
      calc ‖c p.2 (‖p.1‖ ^ 2) - c p.2 (‖q.1‖ ^ 2)‖
          ≤ M * (4 ^ |((n - 1 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 1) : ℤ) : ℝ))
            * ‖‖p.1‖ ^ 2 - ‖q.1‖ ^ 2‖ := hmvx
        _ ≤ M * (4 ^ |((n - 1 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 1) : ℤ) : ℝ))
            * (3 * sigma p * ‖p.1 - q.1‖) := mul_le_mul_of_nonneg_left hxx h0
        _ = 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| * M
            * (sigma p ^ ((2 * (n - 1) : ℤ) : ℝ) * sigma p) * ‖p.1 - q.1‖ := by ring
        _ = 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1)
            * ‖p.1 - q.1‖ := by rw [ew1]
    have hB : ‖c p.2 (‖q.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)‖
        ≤ 4 ^ |((n - 2 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2| := by
      calc ‖c p.2 (‖q.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)‖
          ≤ M * (4 ^ |((n - 2 : ℤ) : ℝ)| * sigma p ^ ((2 * (n - 2) : ℤ) : ℝ)) * ‖p.2 - q.2‖ :=
            hmvt
        _ = 4 ^ |((n - 2 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2| := by
            rw [ew4, Real.norm_eq_abs]
            ring
    have hsplit : c p.2 (‖p.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)
        = (c p.2 (‖p.1‖ ^ 2) - c p.2 (‖q.1‖ ^ 2))
          + (c p.2 (‖q.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)) := by ring
    have hX : 0 ≤ M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖ :=
      mul_nonneg (mul_nonneg hM hw1) (norm_nonneg _)
    have hY : 0 ≤ M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2| :=
      mul_nonneg (mul_nonneg hM hw4) (abs_nonneg _)
    show ‖c p.2 (‖p.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)‖
      ≤ (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M
          * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖
        + (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M
          * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2|
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hK1 : 3 * (4 : ℝ) ^ |((n - 1 : ℤ) : ℝ)|
        ≤ 1 + 3 * (4 : ℝ) ^ |((n - 1 : ℤ) : ℝ)| + (4 : ℝ) ^ |((n - 2 : ℤ) : ℝ)| := by linarith
    have hK2 : (4 : ℝ) ^ |((n - 2 : ℤ) : ℝ)|
        ≤ 1 + 3 * (4 : ℝ) ^ |((n - 1 : ℤ) : ℝ)| + (4 : ℝ) ^ |((n - 2 : ℤ) : ℝ)| := by linarith
    calc ‖c p.2 (‖p.1‖ ^ 2) - c p.2 (‖q.1‖ ^ 2)‖ + ‖c p.2 (‖q.1‖ ^ 2) - c q.2 (‖q.1‖ ^ 2)‖
        ≤ 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖
          + 4 ^ |((n - 2 : ℤ) : ℝ)| * M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2| :=
          add_le_add hA hB
      _ = 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| * (M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖)
          + 4 ^ |((n - 2 : ℤ) : ℝ)| * (M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2|) := by
          ring
      _ ≤ (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|)
            * (M * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖)
          + (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|)
            * (M * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2|) :=
          add_le_add (mul_le_mul_of_nonneg_right hK1 hX) (mul_le_mul_of_nonneg_right hK2 hY)
      _ = (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M
            * sigma p ^ (((2 * n : ℤ) : ℝ) - 1) * ‖p.1 - q.1‖
          + (1 + 3 * 4 ^ |((n - 1 : ℤ) : ℝ)| + 4 ^ |((n - 2 : ℤ) : ℝ)|) * M
            * sigma p ^ (((2 * n : ℤ) : ℝ) - 4) * |p.2 - q.2| := by ring

end Calabi.Weighted
