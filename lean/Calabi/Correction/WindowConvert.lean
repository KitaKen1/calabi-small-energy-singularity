import Calabi.Correction.OuterEstimate
import Calabi.Correction.TwoPointJets
import OAI.Analysis.AncientFlat.Weighted.WeightedScaling
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Boxes and two-point bounds

The estimates of the reused library and of `OuterEstimate.lean` are stated on
parabolic boxes: the boxes `localDomain` of the scale
`σ = (|z|² + √(-t))^{1/2}` for the ancient problem (`YBound`, `XBound`), and the
boxes of a time-independent scale `s`, centred at the initial time, for the
forward problem (`SSource`, `SCoeff`, `SJet`). This file translates between
these and the two-point bounds of `TwoPoint.lean`.

* `abs_sigma_sub_le`, `isScale_sigma`: `σ` is `1`-Lipschitz for the parabolic
  distance, hence a scale.
* `sSource_of_WH`, `sCoeff_of_WH`: two-point bounds give the hypotheses of the
  forward estimates.
* `WH_of_window`, `WH_of_window_jets`, `WH_of_window_time`, `WJ_of_sJet`: the
  conclusions of the forward estimates give two-point bounds.
* `yBound_of_WH`: a two-point bound for `σ` gives the source bound of the
  ancient inverse; `WJ_of_xBound`: its solution bound gives two-point bounds.
-/

open Set

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicInitial OAI.ParabolicLocalization
  OAI.FlatWeighted Calabi.FlatZero

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The scale `σ` -/

/-- The fourth root is `1/4`-Hölder with constant one. -/
theorem quarter_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x ^ ((1 : ℝ) / 4) - y ^ ((1 : ℝ) / 4)| ≤ |x - y| ^ ((1 : ℝ) / 4) := by
  have key : ∀ u v : ℝ, 0 ≤ v → v ≤ u →
      u ^ ((1 : ℝ) / 4) - v ^ ((1 : ℝ) / 4) ≤ (u - v) ^ ((1 : ℝ) / 4) := by
    intro u v hv hvu
    have h := Real.rpow_add_le_add_rpow hv (sub_nonneg.2 hvu) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 : ℝ) / 4 ≤ 1)
    have e : v + (u - v) = u := by ring
    rw [e] at h
    linarith
  rcases le_total y x with h | h
  · have h2 : y ^ ((1 : ℝ) / 4) ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hy h (by norm_num)
    rw [abs_of_nonneg (sub_nonneg.2 h2), abs_of_nonneg (sub_nonneg.2 h)]
    exact key x y hy h
  · have h2 : x ^ ((1 : ℝ) / 4) ≤ y ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hx h (by norm_num)
    rw [abs_sub_comm (x ^ ((1 : ℝ) / 4)) (y ^ ((1 : ℝ) / 4)), abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.2 h2), abs_of_nonneg (sub_nonneg.2 h)]
    exact key y x hx h

/-- The triangle inequality for the Euclidean norm of the plane, in coordinates. -/
theorem sqrt_sq_add_le {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (a' ^ 2 + b' ^ 2) + (|a - a'| + |b - b'|) := by
  have hN : 0 ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := Real.sqrt_nonneg _
  have hNsq : Real.sqrt (a' ^ 2 + b' ^ 2) ^ 2 = a' ^ 2 + b' ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have h1 : a' ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := by
    calc a' = Real.sqrt (a' ^ 2) := (Real.sqrt_sq ha').symm
      _ ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b'])
  have h2 : b' ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := by
    calc b' = Real.sqrt (b' ^ 2) := (Real.sqrt_sq hb').symm
      _ ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a'])
  have hda := abs_nonneg (a - a')
  have hdb := abs_nonneg (b - b')
  have h3 : a ≤ a' + |a - a'| := by linarith [le_abs_self (a - a')]
  have h4 : b ≤ b' + |b - b'| := by linarith [le_abs_self (b - b')]
  have e1 : a ^ 2 ≤ (a' + |a - a'|) ^ 2 := pow_le_pow_left₀ ha h3 2
  have e2 : b ^ 2 ≤ (b' + |b - b'|) ^ 2 := pow_le_pow_left₀ hb h4 2
  have key : a ^ 2 + b ^ 2 ≤ (Real.sqrt (a' ^ 2 + b' ^ 2) + (|a - a'| + |b - b'|)) ^ 2 := by
    nlinarith [mul_nonneg hda (sub_nonneg.2 h1), mul_nonneg hdb (sub_nonneg.2 h2),
      mul_nonneg hda hdb]
  calc Real.sqrt (a ^ 2 + b ^ 2)
      ≤ Real.sqrt ((Real.sqrt (a' ^ 2 + b' ^ 2) + (|a - a'| + |b - b'|)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = Real.sqrt (a' ^ 2 + b' ^ 2) + (|a - a'| + |b - b'|) :=
        Real.sqrt_sq (add_nonneg hN (add_nonneg hda hdb))

theorem sqrt_eq_quarter_sq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = (x ^ ((1 : ℝ) / 4)) ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

/-- **The scale `σ` is `1`-Lipschitz for the parabolic distance.** -/
theorem abs_sigma_sub_le {p q : V × ℝ} (hp : p.2 ≤ 0) (hq : q.2 ≤ 0) :
    |sigma p - sigma q| ≤ pdist p q := by
  have hp' : (0 : ℝ) ≤ -p.2 := by linarith
  have hq' : (0 : ℝ) ≤ -q.2 := by linarith
  have hbp : 0 ≤ (-p.2) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hp' _
  have hbq : 0 ≤ (-q.2) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hq' _
  have ep : sigma p = Real.sqrt (‖p.1‖ ^ 2 + ((-p.2) ^ ((1 : ℝ) / 4)) ^ 2) := by
    unfold sigma
    rw [sqrt_eq_quarter_sq hp']
  have eq : sigma q = Real.sqrt (‖q.1‖ ^ 2 + ((-q.2) ^ ((1 : ℝ) / 4)) ^ 2) := by
    unfold sigma
    rw [sqrt_eq_quarter_sq hq']
  have h1 := sqrt_sq_add_le (norm_nonneg p.1) hbp (norm_nonneg q.1) hbq
  have h2 := sqrt_sq_add_le (norm_nonneg q.1) hbq (norm_nonneg p.1) hbp
  rw [← ep, ← eq] at h1
  rw [← ep, ← eq, abs_sub_comm ‖q.1‖ ‖p.1‖,
    abs_sub_comm ((-q.2) ^ ((1 : ℝ) / 4)) ((-p.2) ^ ((1 : ℝ) / 4))] at h2
  have h3 : |‖p.1‖ - ‖q.1‖| ≤ ‖p.1 - q.1‖ := abs_norm_sub_norm_le _ _
  have h4 : |(-p.2) ^ ((1 : ℝ) / 4) - (-q.2) ^ ((1 : ℝ) / 4)|
      ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) := by
    have h := quarter_sub_le hp' hq'
    have e : -p.2 - -q.2 = -(p.2 - q.2) := by ring
    rwa [e, abs_neg] at h
  unfold pdist
  rw [abs_le]
  constructor <;> linarith

/-- `σ` is a scale on `{t < 0}` with constant `2`, for every radius `a ≤ 1/2`. -/
theorem isScale_sigma {a : ℝ} (ha : a ≤ 1 / 2) :
    IsScale a 2 (sigma (V := V)) {p : V × ℝ | p.2 < 0} :=
  IsScale.of_lipschitz (fun p hp => sigma_pos p hp)
    (fun p hp q hq => abs_sigma_sub_le (le_of_lt hp) (le_of_lt hq)) ha

/-- A positive time-independent function that is `1`-Lipschitz is a scale. -/
theorem isScale_of_space {s : V → ℝ} {a : ℝ} {Ω : Set (V × ℝ)} (hs : ∀ x, 0 < s x)
    (hl : ∀ x y, |s x - s y| ≤ ‖x - y‖) (ha : a ≤ 1 / 2) :
    IsScale a 2 (fun p : V × ℝ => s p.1) Ω :=
  IsScale.of_lipschitz (fun p _ => hs p.1)
    (fun p _ q _ => (hl p.1 q.1).trans (by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)])) ha

/-! ### The boxes of the forward problem -/

section Forward

variable {s : V → ℝ} {a a₁ c R α : ℝ}

/-- From the two-point bound to the boxes of the forward problem. -/
theorem holderBound_slab_of_WH {E : Type*} [NormedAddCommGroup E] {v M : ℝ} {g : V × ℝ → E}
    (hg : WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} v M g)
    (hM : 0 ≤ M) (ha : 0 < a) (hα : 0 ≤ α) (hc : 1 ≤ c) (ha₁ : 0 < a₁) (hs : ∀ x, 0 < s x)
    (hcomp : ∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ≤ c * s x₀ ∧ s x₀ ≤ c * s x) (x₀ : V) :
    HolderBound α (slab 2 (R / (a₁ * s x₀) ^ 4))
      (fun p => g (window (x₀, 0) (a₁ * s x₀) p))
      ((c ^ |v| + c ^ |v - α| * a₁ ^ α + 2 * c ^ |v| * (c * a₁ / a) ^ α) * M * s x₀ ^ v) := by
  have hq : 0 < a₁ * s x₀ := mul_pos ha₁ (hs x₀)
  have hmem : ∀ p ∈ slab (V := V) 2 (R / (a₁ * s x₀) ^ 4),
      ‖(window (x₀, (0 : ℝ)) (a₁ * s x₀) p).1 - x₀‖ < 2 * (a₁ * s x₀) := by
    intro p hp
    show ‖x₀ + (a₁ * s x₀) • p.1 - x₀‖ < 2 * (a₁ * s x₀)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    have := hp.1
    nlinarith
  exact hg.holderBound_window (k := a₁) (s₀ := s x₀) (q := a₁ * s x₀) hM ha hα hc hq (hs x₀)
    le_rfl (x₀, 0) (D := slab 2 (R / (a₁ * s x₀) ^ 4)) (fun p hp => window_mem_slab hq hp)
    (fun p _ => hs _) (fun p hp => (hcomp x₀ _ (hmem p hp)).1)
    (fun p hp => (hcomp x₀ _ (hmem p hp)).2)

/-- **A two-point bound gives the source bound of the forward estimates.** -/
theorem sSource_of_WH {w M : ℝ} {f : ℝ → V → ℂ}
    (hf : WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4) M
      (fun p => f p.2 p.1))
    (hM : 0 ≤ M) (ha : 0 < a) (hα : 0 ≤ α) (hc : 1 ≤ c) (ha₁ : 0 < a₁) (hs : ∀ x, 0 < s x)
    (hcomp : ∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ≤ c * s x₀ ∧ s x₀ ≤ c * s x) :
    SSource s a₁ R α w
      (a₁ ^ 4 * (c ^ |w - 4| + c ^ |w - 4 - α| * a₁ ^ α + 2 * c ^ |w - 4| * (c * a₁ / a) ^ α)
        * M) f := by
  intro x₀
  have hq : 0 < a₁ * s x₀ := mul_pos ha₁ (hs x₀)
  have hsx := hs x₀
  have h := (holderBound_slab_of_WH hf hM ha hα hc ha₁ hs hcomp x₀).const_smul
    ((a₁ * s x₀) ^ 4)
  have e : s x₀ ^ 4 * s x₀ ^ (w - 4) = s x₀ ^ w := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hsx]
    congr 1
    push_cast
    ring
  refine h.mono (le_of_eq ?_)
  rw [abs_of_pos (pow_pos hq 4), mul_pow]
  calc a₁ ^ 4 * s x₀ ^ 4 * ((c ^ |w - 4| + c ^ |w - 4 - α| * a₁ ^ α
        + 2 * c ^ |w - 4| * (c * a₁ / a) ^ α) * M * s x₀ ^ (w - 4))
      = a₁ ^ 4 * (c ^ |w - 4| + c ^ |w - 4 - α| * a₁ ^ α
        + 2 * c ^ |w - 4| * (c * a₁ / a) ^ α) * M * (s x₀ ^ 4 * s x₀ ^ (w - 4)) := by ring
    _ = a₁ ^ 4 * (c ^ |w - 4| + c ^ |w - 4 - α| * a₁ ^ α
        + 2 * c ^ |w - 4| * (c * a₁ / a) ^ α) * M * s x₀ ^ w := by rw [e]

/-- **A two-point bound gives the coefficient bound of the forward estimates.** -/
theorem sCoeff_of_WH {M : ℝ} {coef : ℝ → V → ℝ}
    (hf : WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} 0 M
      (fun p => coef p.2 p.1))
    (hM : 0 ≤ M) (ha : 0 < a) (hα : 0 ≤ α) (hc : 1 ≤ c) (ha₁ : 0 < a₁) (hs : ∀ x, 0 < s x)
    (hcomp : ∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ≤ c * s x₀ ∧ s x₀ ≤ c * s x) :
    SCoeff s a₁ R α
      ((c ^ |(0 : ℝ)| + c ^ |0 - α| * a₁ ^ α + 2 * c ^ |(0 : ℝ)| * (c * a₁ / a) ^ α) * M)
      coef := by
  intro x₀
  have h := holderBound_slab_of_WH hf hM ha hα hc ha₁ hs hcomp x₀
  rw [Real.rpow_zero, mul_one] at h
  exact h

/-- **Boxes centred at the initial time give a two-point bound.** -/
theorem WH_of_window {E : Type*} [NormedAddCommGroup E] {b ρ v N : ℝ} {g : V × ℝ → E}
    (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ) (hs : ∀ x, 0 < s x) (hα : 0 ≤ α) (hN : 0 ≤ N)
    (ha : a < ρ * b)
    (h : ∀ x₀ : V, HolderBound α
      {p : V × ℝ | ‖p.1‖ < ρ ∧ p.2 ∈ Icc 0 (R / (b * s x₀) ^ 4)}
      (fun p => g (window (x₀, 0) (b * s x₀) p)) (N * s x₀ ^ v)) :
    WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} v (N * b ^ (-α)) g := by
  have hbα : 1 ≤ b ^ (-α) := by
    rw [Real.rpow_neg hb.le]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hb _)).2 (Real.rpow_le_one hb.le hb1 hα)
  have hcentre : ∀ p : V × ℝ, p.2 ∈ Icc (0 : ℝ) R →
      ((0 : V), p.2 / (b * s p.1) ^ 4) ∈
          {p' : V × ℝ | ‖p'.1‖ < ρ ∧ p'.2 ∈ Icc 0 (R / (b * s p.1) ^ 4)} ∧
        window (p.1, (0 : ℝ)) (b * s p.1) ((0 : V), p.2 / (b * s p.1) ^ 4) = p := by
    intro p hp
    have hq4 : 0 < (b * s p.1) ^ 4 := pow_pos (mul_pos hb (hs p.1)) 4
    refine ⟨⟨by simpa using hρ, div_nonneg hp.1 hq4.le,
      div_le_div_of_nonneg_right hp.2 hq4.le⟩, Prod.ext ?_ ?_⟩
    · show p.1 + (b * s p.1) • (0 : V) = p.1
      rw [smul_zero, add_zero]
    · show 0 + (b * s p.1) ^ 4 * (p.2 / (b * s p.1) ^ 4) = p.2
      rw [mul_div_cancel₀ _ hq4.ne', zero_add]
  refine ⟨fun p hp => ?_, fun p hp z hz hd => ?_⟩
  · obtain ⟨hmem, e⟩ := hcentre p hp
    have h1 : ‖g (window (p.1, (0 : ℝ)) (b * s p.1) ((0 : V), p.2 / (b * s p.1) ^ 4))‖
        ≤ N * s p.1 ^ v := (h p.1).1 ((0 : V), p.2 / (b * s p.1) ^ 4) hmem
    rw [e] at h1
    have h2 : 0 ≤ N * s p.1 ^ v := mul_nonneg hN (Real.rpow_nonneg (hs p.1).le _)
    calc ‖g p‖ ≤ N * s p.1 ^ v := h1
      _ ≤ N * s p.1 ^ v * b ^ (-α) := le_mul_of_one_le_right h2 hbα
      _ = N * b ^ (-α) * s p.1 ^ v := by ring
  · obtain ⟨hmem, e⟩ := hcentre p hp
    have hsp := hs p.1
    have hq : 0 < b * s p.1 := mul_pos hb hsp
    have hq4 : 0 < (b * s p.1) ^ 4 := pow_pos hq 4
    have hd0 := pdist_nonneg p z
    have hd' : pdist p z ≤ a * s p.1 := hd
    have hx : ‖p.1 - z.1‖ ≤ pdist p z := by
      unfold pdist
      linarith [Real.rpow_nonneg (abs_nonneg (p.2 - z.2)) ((1 : ℝ) / 4)]
    -- the second point in the box of the first
    have hmemz : ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4) ∈
        {p' : V × ℝ | ‖p'.1‖ < ρ ∧ p'.2 ∈ Icc 0 (R / (b * s p.1) ^ 4)} := by
      refine ⟨?_, div_nonneg hz.1 hq4.le, div_le_div_of_nonneg_right hz.2 hq4.le⟩
      show ‖(b * s p.1)⁻¹ • (z.1 - p.1)‖ < ρ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq), norm_sub_rev,
        inv_mul_lt_iff₀ hq]
      have h3 : a * s p.1 < b * s p.1 * ρ := by nlinarith
      linarith
    have ez : window (p.1, (0 : ℝ)) (b * s p.1)
        ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4) = z := by
      refine Prod.ext ?_ ?_
      · show p.1 + (b * s p.1) • ((b * s p.1)⁻¹ • (z.1 - p.1)) = z.1
        rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
        abel
      · show 0 + (b * s p.1) ^ 4 * (z.2 / (b * s p.1) ^ 4) = z.2
        rw [mul_div_cancel₀ _ hq4.ne', zero_add]
    have h1 : ‖g (window (p.1, (0 : ℝ)) (b * s p.1) ((0 : V), p.2 / (b * s p.1) ^ 4))
          - g (window (p.1, (0 : ℝ)) (b * s p.1)
            ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4))‖
        ≤ N * s p.1 ^ v * pdist ((0 : V), p.2 / (b * s p.1) ^ 4)
          ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4) ^ α :=
      (h p.1).2 ((0 : V), p.2 / (b * s p.1) ^ 4) hmem
        ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4) hmemz
    have hpd : pdist ((0 : V), p.2 / (b * s p.1) ^ 4)
        ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4) = pdist p z / (b * s p.1) := by
      have h3 := pdist_window (p.1, (0 : ℝ)) hq.le ((0 : V), p.2 / (b * s p.1) ^ 4)
        ((b * s p.1)⁻¹ • (z.1 - p.1), z.2 / (b * s p.1) ^ 4)
      rw [e, ez] at h3
      rw [h3, mul_div_cancel_left₀ _ hq.ne']
    rw [e, ez, hpd, Real.div_rpow hd0 hq.le, Real.mul_rpow hb.le hsp.le] at h1
    have e3 : s p.1 ^ v / s p.1 ^ α = s p.1 ^ (v - α) := (Real.rpow_sub hsp v α).symm
    have e4 : (b ^ α)⁻¹ = b ^ (-α) := (Real.rpow_neg hb.le α).symm
    calc ‖g p - g z‖ ≤ N * s p.1 ^ v * (pdist p z ^ α / (b ^ α * s p.1 ^ α)) := h1
      _ = N * (b ^ α)⁻¹ * (s p.1 ^ v / s p.1 ^ α) * pdist p z ^ α := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      _ = N * b ^ (-α) * s p.1 ^ (v - α) * pdist p z ^ α := by rw [e3, e4]

/-- Boxes for the jets of the rescaled function give a two-point bound for
the jets. -/
theorem WH_of_window_jets {b ρ w N : ℝ} {j : ℕ} {u : ℝ → V → ℂ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ) (hs : ∀ x, 0 < s x) (hα : 0 ≤ α) (hN : 0 ≤ N)
    (ha : a < ρ * b) (hu : ∀ t, ContDiff ℝ 4 (u t)) (hj : j ≤ 4)
    (h : ∀ x₀ : V, HolderBound α
      {p : V × ℝ | ‖p.1‖ < ρ ∧ p.2 ∈ Icc 0 (R / (b * s x₀) ^ 4)}
      (fun p => iteratedFDeriv ℝ j (windowValue (x₀, 0) (b * s x₀) u p.2) p.1)
      (N * s x₀ ^ w)) :
    WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - j)
      (N * b ^ (-(j : ℝ)) * b ^ (-α)) (fun p => iteratedFDeriv ℝ j (u p.2) p.1) := by
  have hbj : 0 ≤ b ^ (-(j : ℝ)) := Real.rpow_nonneg hb.le _
  refine WH_of_window hb hb1 hρ hs hα (mul_nonneg hN hbj) ha fun x₀ => ?_
  have hsx := hs x₀
  have hq : 0 < b * s x₀ := mul_pos hb hsx
  have hqj : 0 < (b * s x₀) ^ j := pow_pos hq j
  have efun : (fun p : V × ℝ => ((b * s x₀) ^ j)⁻¹ •
        iteratedFDeriv ℝ j (windowValue (x₀, 0) (b * s x₀) u p.2) p.1)
      = fun p => iteratedFDeriv ℝ j (u (window (x₀, (0 : ℝ)) (b * s x₀) p).2)
        (window (x₀, (0 : ℝ)) (b * s x₀) p).1 := by
    funext p
    rw [window_jet (x₀, 0) (b * s x₀) u hu j hj p, smul_smul, inv_mul_cancel₀ hqj.ne', one_smul]
  have h1 : HolderBound α {p : V × ℝ | ‖p.1‖ < ρ ∧ p.2 ∈ Icc 0 (R / (b * s x₀) ^ 4)}
      (fun p => iteratedFDeriv ℝ j (u (window (x₀, (0 : ℝ)) (b * s x₀) p).2)
        (window (x₀, (0 : ℝ)) (b * s x₀) p).1)
      (|((b * s x₀) ^ j)⁻¹| * (N * s x₀ ^ w)) := by
    rw [← efun]
    exact (h x₀).const_smul (((b * s x₀) ^ j)⁻¹)
  refine h1.mono (le_of_eq ?_)
  rw [abs_of_pos (inv_pos.2 hqj), mul_pow, ← Real.rpow_natCast b j, ← Real.rpow_natCast (s x₀) j,
    mul_inv, ← Real.rpow_neg hb.le, ← Real.rpow_neg hsx.le]
  have e : s x₀ ^ (-(j : ℝ)) * s x₀ ^ w = s x₀ ^ (w - j) := by
    rw [← Real.rpow_add hsx]
    congr 1
    ring
  calc b ^ (-(j : ℝ)) * s x₀ ^ (-(j : ℝ)) * (N * s x₀ ^ w)
      = N * b ^ (-(j : ℝ)) * (s x₀ ^ (-(j : ℝ)) * s x₀ ^ w) := by ring
    _ = N * b ^ (-(j : ℝ)) * s x₀ ^ (w - j) := by rw [e]

/-- Boxes for the rescaled time derivative give a two-point bound. -/
theorem WH_of_window_time {b ρ w N : ℝ} {ut : ℝ → V → ℂ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ) (hs : ∀ x, 0 < s x) (hα : 0 ≤ α) (hN : 0 ≤ N)
    (ha : a < ρ * b)
    (h : ∀ x₀ : V, HolderBound α
      {p : V × ℝ | ‖p.1‖ < ρ ∧ p.2 ∈ Icc 0 (R / (b * s x₀) ^ 4)}
      (fun p => windowTime (x₀, 0) (b * s x₀) ut p.2 p.1) (N * s x₀ ^ w)) :
    WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4)
      (N * b ^ (-(4 : ℝ)) * b ^ (-α)) (fun p => ut p.2 p.1) := by
  have hb4 : 0 ≤ b ^ (-(4 : ℝ)) := Real.rpow_nonneg hb.le _
  refine WH_of_window hb hb1 hρ hs hα (mul_nonneg hN hb4) ha fun x₀ => ?_
  have hsx := hs x₀
  have hq : 0 < b * s x₀ := mul_pos hb hsx
  have hq4 : 0 < (b * s x₀) ^ 4 := pow_pos hq 4
  have efun : (fun p : V × ℝ => ((b * s x₀) ^ 4)⁻¹ • windowTime (x₀, 0) (b * s x₀) ut p.2 p.1)
      = fun p => ut (window (x₀, (0 : ℝ)) (b * s x₀) p).2
        (window (x₀, (0 : ℝ)) (b * s x₀) p).1 := by
    funext p
    show ((b * s x₀) ^ 4)⁻¹ • ((b * s x₀) ^ 4 •
        ut (0 + (b * s x₀) ^ 4 * p.2) (x₀ + (b * s x₀) • p.1))
      = ut (0 + (b * s x₀) ^ 4 * p.2) (x₀ + (b * s x₀) • p.1)
    rw [smul_smul, inv_mul_cancel₀ hq4.ne', one_smul]
  have h1 : HolderBound α {p : V × ℝ | ‖p.1‖ < ρ ∧ p.2 ∈ Icc 0 (R / (b * s x₀) ^ 4)}
      (fun p => ut (window (x₀, (0 : ℝ)) (b * s x₀) p).2 (window (x₀, (0 : ℝ)) (b * s x₀) p).1)
      (|((b * s x₀) ^ 4)⁻¹| * (N * s x₀ ^ w)) := by
    rw [← efun]
    exact (h x₀).const_smul (((b * s x₀) ^ 4)⁻¹)
  refine h1.mono (le_of_eq ?_)
  have e4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [abs_of_pos (inv_pos.2 hq4), mul_pow, ← Real.rpow_natCast b 4, ← Real.rpow_natCast (s x₀) 4,
    mul_inv, ← Real.rpow_neg hb.le, ← Real.rpow_neg hsx.le, e4]
  have e : s x₀ ^ (-((4 : ℕ) : ℝ)) * s x₀ ^ w = s x₀ ^ (w - ((4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hsx]
    congr 1
    ring
  calc b ^ (-((4 : ℕ) : ℝ)) * s x₀ ^ (-((4 : ℕ) : ℝ)) * (N * s x₀ ^ w)
      = N * b ^ (-((4 : ℕ) : ℝ)) * (s x₀ ^ (-((4 : ℕ) : ℝ)) * s x₀ ^ w) := by ring
    _ = N * b ^ (-((4 : ℕ) : ℝ)) * s x₀ ^ (w - ((4 : ℕ) : ℝ)) := by rw [e]

/-- **The conclusion of the forward estimates in two-point form**: jets with
the weights `w - j` and a time derivative with the weight `w - 4`. -/
theorem WJ_of_sJet {w N : ℝ} {u ut : ℝ → V → ℂ} (ha₁ : 0 < a₁) (ha₁1 : a₁ ≤ 1)
    (hs : ∀ x, 0 < s x) (hα : 0 ≤ α) (hN : 0 ≤ N) (ha : a < a₁) (hu : ∀ t, ContDiff ℝ 4 (u t))
    (h : SJet s a₁ R α w N u ut) :
    WJ α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} w
        (N * a₁ ^ (-(4 : ℝ)) * a₁ ^ (-α)) 4 u ∧
      WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} (w - 4)
        (N * a₁ ^ (-(4 : ℝ)) * a₁ ^ (-α)) (fun p => ut p.2 p.1) := by
  have ha' : a < 1 * a₁ := by rwa [one_mul]
  have hpos : ∀ p ∈ {p : V × ℝ | p.2 ∈ Icc (0 : ℝ) R}, 0 < (fun p : V × ℝ => s p.1) p :=
    fun p _ => hs p.1
  have hα0 : 0 ≤ a₁ ^ (-α) := Real.rpow_nonneg ha₁.le _
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := WH_of_window_jets ha₁ ha₁1 zero_lt_one hs hα hN ha' hu hj
      (fun x₀ => (h x₀).1 j hj)
    refine h1.mono hpos ?_
    have h2 : a₁ ^ (-(j : ℝ)) ≤ a₁ ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ha₁ ha₁1 (by
        have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
        linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hN) hα0
  · exact WH_of_window_time ha₁ ha₁1 zero_lt_one hs hα hN ha' (fun x₀ => (h x₀).2)

end Forward

/-! ### The boxes of the scale `σ` -/

section Ancient

variable {α a w M : ℝ}

theorem inv_mul_mul_self {x y : ℝ} (hx : x ≠ 0) : x⁻¹ * (y * x) = y := by
  rw [mul_comm y x, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem weight_factor {σ : ℝ} (hσ : 0 < σ) (w : ℝ) (j : ℕ) :
    σ ^ (-w) * σ ^ j = (σ ^ (w - j))⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hσ, ← Real.rpow_neg hσ.le]
  congr 1
  ring

/-- From a bound for a positive multiple to a bound for the vector. -/
theorem norm_le_of_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {k B : ℝ} (hk : 0 < k) (h : ‖k⁻¹ • x‖ ≤ B) : ‖x‖ ≤ B * k := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk), inv_mul_le_iff₀ hk] at h
  linarith

/-- **A two-point bound for the scale `σ` gives the source bound of the
ancient inverse.** -/
theorem yBound_of_WH {a₂ : ℝ} {f : V × ℝ → ℂ}
    (hf : WH α a₂ (sigma (V := V)) {p : V × ℝ | p.2 < 0} (w - 4) M f) (hM : 0 ≤ M)
    (ha₂ : 0 < a₂) (hα : 0 ≤ α) (ha : 0 < a) (ha4 : a ≤ 1 / 4) :
    YBound α w a
      ((2 ^ |w - 4| + 2 ^ |w - 4 - α| * 1 ^ α + 2 * 2 ^ |w - 4| * (2 * 1 / a₂) ^ α) * M) f := by
  intro p hp
  have hσ := sigma_pos p hp
  have e0 : window p (sigma p) (0 : V × ℝ) = p := chart_zero p
  have hcomp : ∀ q ∈ localDomain a p,
      |sigma (window p (sigma p) q) - sigma p| ≤ sigma p / 2 := by
    intro q hq
    have hq2 : (window p (sigma p) q).2 ≤ 0 := le_of_lt hq.2.2.2
    have h1 := abs_sigma_sub_le hq2 (le_of_lt hp)
    have e : pdist (window p (sigma p) q) p = sigma p * pdist q 0 := by
      have h := pdist_window p hσ.le q (0 : V × ℝ)
      rwa [e0] at h
    have ht : |q.2| ^ ((1 : ℝ) / 4) ≤ a := by
      have h3 : |q.2| ≤ a ^ 4 := le_of_lt (abs_lt.2 ⟨hq.2.1, hq.2.2.1⟩)
      have h4 := Real.rpow_le_rpow (abs_nonneg q.2) h3 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [pow_four_quarter ha.le] at h4
    have h2 : pdist q (0 : V × ℝ) ≤ 1 / 2 := by
      have hx := hq.1
      unfold pdist
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
      linarith
    rw [e] at h1
    nlinarith
  have h := hf.holderBound_window (k := 1) (s₀ := sigma p) (q := sigma p) hM ha₂ hα
    (by norm_num : (1 : ℝ) ≤ 2) hσ hσ (by rw [one_mul]) p (D := localDomain a p)
    (fun q hq => hq.2.2.2) (fun q hq => sigma_pos _ hq.2.2.2)
    (fun q hq => by
      have := (abs_le.1 (hcomp q hq)).2
      linarith)
    (fun q hq => by
      have := (abs_le.1 (hcomp q hq)).1
      linarith)
  have h2 := h.const_smul (sigma p ^ (-(w - 4)))
  refine h2.mono (le_of_eq ?_)
  have hne : sigma p ^ (w - 4) ≠ 0 := (Real.rpow_pos_of_pos hσ _).ne'
  rw [abs_of_pos (Real.rpow_pos_of_pos hσ _), Real.rpow_neg hσ.le, inv_mul_mul_self hne]

/-- **The solution bound of the ancient inverse in two-point form.** -/
theorem WJ_of_xBound {a' : ℝ} {u ut : ℝ → V → ℂ} (h : XBound α w a M u ut) (ha : 0 < a)
    (ha' : a' < a) (hu : ∀ t, ContDiff ℝ 4 (u t)) :
    WJ α a' (sigma (V := V)) {p : V × ℝ | p.2 < 0} w M 4 u ∧
      WH α a' (sigma (V := V)) {p : V × ℝ | p.2 < 0} (w - 4) M (fun p => ut p.2 p.1) := by
  -- the general step: from the box of `p` to the two-point bound at `p`
  have step : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) (g : V × ℝ → E)
      (G : V × ℝ → V × ℝ → E),
      (∀ p : V × ℝ, p.2 < 0 → HolderBound α (localDomain a p) (G p) M) →
      (∀ p : V × ℝ, p.2 < 0 → ∀ q : V × ℝ, G p q = (sigma p ^ (-w) * sigma p ^ j) • g (chart p q)) →
      WH α a' (sigma (V := V)) {p : V × ℝ | p.2 < 0} (w - j) M g := by
    intro E _ _ j g G hG hGe
    refine ⟨fun p hp => ?_, fun p hp z hz hd => ?_⟩
    · have hσ := sigma_pos p hp
      have hk : 0 < sigma p ^ (w - j) := Real.rpow_pos_of_pos hσ _
      have h1 := (hG p hp).1 0 (zero_localDomain a ha p hp)
      rw [hGe p hp, chart_zero, weight_factor hσ] at h1
      exact norm_le_of_inv_smul hk h1
    · have hσ := sigma_pos p hp
      have hk : 0 < sigma p ^ (w - j) := Real.rpow_pos_of_pos hσ _
      have hd' : pdist p z < a * sigma p :=
        hd.trans_lt (mul_lt_mul_of_pos_right ha' hσ)
      have hmem := unchart_mem_of_near ha p z hp hz hd'
      have h1 := (hG p hp).2 0 (zero_localDomain a ha p hp) (unchart p z) hmem
      rw [hGe p hp, hGe p hp, chart_zero, chart_unchart p z hp, pdist_unchart p z hp,
        ← smul_sub, weight_factor hσ, Real.div_rpow (pdist_nonneg p z) hσ.le] at h1
      have h2 := norm_le_of_inv_smul hk h1
      have e : sigma p ^ (w - j) / sigma p ^ α = sigma p ^ (w - j - α) :=
        (Real.rpow_sub hσ _ α).symm
      calc ‖g p - g z‖ ≤ M * (pdist p z ^ α / sigma p ^ α) * sigma p ^ (w - j) := h2
        _ = M * (sigma p ^ (w - j) / sigma p ^ α) * pdist p z ^ α := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        _ = M * sigma p ^ (w - j - α) * pdist p z ^ α := by rw [e]
  refine ⟨fun j hj => ?_, ?_⟩
  · have hj' : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
    refine step (V [×j]→L[ℝ] ℂ) j (fun p => iteratedFDeriv ℝ j (u p.2) p.1)
      (fun p q => iteratedFDeriv ℝ j (weightedValue w p u q.2) q.1)
      (fun p hp => (h p hp).1 j hj) (fun p _ q => ?_)
    show iteratedFDeriv ℝ j (fun x => sigma p ^ (-w) • windowValue p (sigma p) u q.2 x) q.1 = _
    rw [iteratedFDeriv_const_smul_apply'
      ((windowValue_contDiff p (sigma p) u hu q.2).of_le hj').contDiffAt,
      window_jet p (sigma p) u hu j hj q, smul_smul]
    rfl
  · have h4 := step ℂ 4 (fun p => ut p.2 p.1)
      (fun p q => weightedTime w p ut q.2 q.1) (fun p hp => (h p hp).2) (fun p _ q => rfl)
    have e : w - ((4 : ℕ) : ℝ) = w - 4 := by norm_num
    rw [e] at h4
    exact h4

end Ancient

end Calabi.Weighted
