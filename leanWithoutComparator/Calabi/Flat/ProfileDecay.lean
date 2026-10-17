import Calabi.Flat.SelfSimilar

/-!
# Decay of the profile at infinity

From the smoothness of `H(u) = G(u^{-1/2})` at `u = 0`:

* `profile_deriv_decay`: `G′ = O(y⁻³)` and `G″ = O(y⁻⁴)` for `y ≥ 1`;
* `hfun_decay`: for `h(y) = (G(y) - 1)/y` and all `y ≥ 0`,
  `|h|`, `|y h′|` and `|y² h″|` are at most `C / (1 + y)`.

The second statement is what bounds the self-similar solution
`F = ρ⁻¹ h(x/ρ)` and its first two `x`-derivatives by `C / (x + ρ)`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Flat

variable {c : ℝ} {G : ℝ → ℝ}

theorem inv_sq_rpow {y : ℝ} (hy : 0 < y) : ((y ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) = y := by
  have h2 : (0 : ℝ) ≤ y ^ 2 := by positivity
  have e : ((2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -1 := by norm_num
  rw [Real.inv_rpow h2, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le, e, Real.rpow_neg_one,
    inv_inv]

/-- The profile in the variable `u = y⁻²`. -/
theorem profile_eq_compact (hP : IsProfile c G) :
    ∃ H : ℝ → ℝ, ContDiffOn ℝ ∞ H (Ici 0) ∧ ∀ y : ℝ, 0 < y → G y = H ((y ^ 2)⁻¹) := by
  obtain ⟨H, hH, -, hm⟩ := hP.compact
  refine ⟨H, hH, fun y hy => ?_⟩
  have h := hm ((y ^ 2)⁻¹) (inv_pos.2 (pow_pos hy 2))
  rw [inv_sq_rpow hy] at h
  exact h.symm

/-- `G′ = O(y⁻³)` and `G″ = O(y⁻⁴)` at infinity. -/
theorem profile_deriv_decay (hP : IsProfile c G) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 1 ≤ y →
    |deriv G y| ≤ B / y ^ 3 ∧ |iteratedDeriv 2 G y| ≤ B / y ^ 4 := by
  obtain ⟨H, hH, hGH⟩ := profile_eq_compact hP
  have hud : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have h1c : ContinuousOn (derivWithin H (Ici 0)) (Ici 0) :=
    hH.continuousOn_derivWithin hud (by simp)
  have h1s : ContDiffOn ℝ ∞ (derivWithin H (Ici 0)) (Ici 0) := hH.derivWithin hud (by simp)
  have h2c : ContinuousOn (derivWithin (derivWithin H (Ici 0)) (Ici 0)) (Ici 0) :=
    h1s.continuousOn_derivWithin hud (by simp)
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (h1c.mono Icc_subset_Ici_self)
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (h2c.mono Icc_subset_Ici_self)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0 ⟨le_rfl, zero_le_one⟩)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0 ⟨le_rfl, zero_le_one⟩)
  have hHo : ContDiffOn ℝ ∞ H (Ioi 0) := hH.mono Ioi_subset_Ici_self
  have e1 : ∀ u : ℝ, 0 < u → derivWithin H (Ici 0) u = deriv H u := fun u hu =>
    derivWithin_of_mem_nhds (Ici_mem_nhds hu)
  have e2 : ∀ u : ℝ, 0 < u →
      derivWithin (derivWithin H (Ici 0)) (Ici 0) u = iteratedDeriv 2 H u := by
    intro u hu
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hu), iteratedDeriv_succ, iteratedDeriv_one]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioi_mem_nhds hu] with v hv using e1 v hv
  have dH0 : ∀ u : ℝ, 0 < u → HasDerivAt H (deriv H u) u := fun u hu => by
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hHo 0 (mem_Ioi.2 hu)
    rwa [iteratedDeriv_zero, iteratedDeriv_one] at h
  have dH1 : ∀ u : ℝ, 0 < u → HasDerivAt (deriv H) (iteratedDeriv 2 H u) u := fun u hu => by
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hHo 1 (mem_Ioi.2 hu)
    rwa [iteratedDeriv_one] at h
  have du : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-2 * (x ^ 3)⁻¹) x := by
    intro x hx
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x :=
      (hasDerivAt_pow 2 x).congr_deriv (by norm_num)
    have hx0 := hx.ne'
    refine (hp.fun_inv (pow_ne_zero 2 hx0)).congr_deriv ?_
    field_simp
  have dG : ∀ x : ℝ, 0 < x →
      HasDerivAt G (deriv H ((x ^ 2)⁻¹) * (-2 * (x ^ 3)⁻¹)) x := by
    intro x hx
    have hpos : 0 < (x ^ 2)⁻¹ := inv_pos.2 (pow_pos hx 2)
    have hc : HasDerivAt (fun x : ℝ => H ((x ^ 2)⁻¹))
        (deriv H ((x ^ 2)⁻¹) * (-2 * (x ^ 3)⁻¹)) x := (dH0 _ hpos).comp x (du x hx)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with v hv using hGH v hv
  have dG2 : ∀ x : ℝ, 0 < x → HasDerivAt (deriv G)
      (iteratedDeriv 2 H ((x ^ 2)⁻¹) * (-2 * (x ^ 3)⁻¹) * (-2 * (x ^ 3)⁻¹)
        + deriv H ((x ^ 2)⁻¹) * (-2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2))) x := by
    intro x hx
    have hpos : 0 < (x ^ 2)⁻¹ := inv_pos.2 (pow_pos hx 2)
    have hx0 := hx.ne'
    have hp3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x :=
      (hasDerivAt_pow 3 x).congr_deriv (by norm_num)
    have hk : HasDerivAt (fun x : ℝ => -2 * (x ^ 3)⁻¹) (-2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2)) x :=
      (hp3.fun_inv (pow_ne_zero 3 hx0)).const_mul (-2)
    have hc0 := (dH1 ((x ^ 2)⁻¹) hpos).comp x (du x hx)
    have hc1 : HasDerivAt (fun x : ℝ => deriv H ((x ^ 2)⁻¹))
        (iteratedDeriv 2 H ((x ^ 2)⁻¹) * (-2 * (x ^ 3)⁻¹)) x := hc0
    refine (hc1.fun_mul hk).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with v hv using (dG v hv).deriv
  refine ⟨2 * B1 + (4 * B2 + 6 * B1), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hy0' := hy0.ne'
  have hu0 : 0 < (y ^ 2)⁻¹ := inv_pos.2 (pow_pos hy0 2)
  have hu1 : (y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hy)
  have b1 : |deriv H ((y ^ 2)⁻¹)| ≤ B1 := by
    have h := hB1 _ ⟨hu0.le, hu1⟩
    rwa [Real.norm_eq_abs, e1 _ hu0] at h
  have b2 : |iteratedDeriv 2 H ((y ^ 2)⁻¹)| ≤ B2 := by
    have h := hB2 _ ⟨hu0.le, hu1⟩
    rwa [Real.norm_eq_abs, e2 _ hu0] at h
  have hy3 : 0 < y ^ 3 := pow_pos hy0 3
  have hy4 : 0 < y ^ 4 := pow_pos hy0 4
  have hy6 : 0 < y ^ 6 := pow_pos hy0 6
  constructor
  · have hk : |(-2 : ℝ) * (y ^ 3)⁻¹| = 2 / y ^ 3 := by
      rw [abs_mul, abs_inv, abs_of_pos hy3, div_eq_mul_inv]
      norm_num
    rw [(dG y hy0).deriv]
    calc |deriv H ((y ^ 2)⁻¹) * (-2 * (y ^ 3)⁻¹)|
        = |deriv H ((y ^ 2)⁻¹)| * (2 / y ^ 3) := by rw [abs_mul, hk]
      _ ≤ B1 * (2 / y ^ 3) := mul_le_mul_of_nonneg_right b1 (by positivity)
      _ = 2 * B1 / y ^ 3 := by ring
      _ ≤ (2 * B1 + (4 * B2 + 6 * B1)) / y ^ 3 :=
        div_le_div_of_nonneg_right (by linarith) hy3.le
  · have hval : iteratedDeriv 2 H ((y ^ 2)⁻¹) * (-2 * (y ^ 3)⁻¹) * (-2 * (y ^ 3)⁻¹)
        + deriv H ((y ^ 2)⁻¹) * (-2 * (-(3 * y ^ 2) / (y ^ 3) ^ 2))
        = iteratedDeriv 2 H ((y ^ 2)⁻¹) * (4 / y ^ 6) + deriv H ((y ^ 2)⁻¹) * (6 / y ^ 4) := by
      field_simp
      ring
    have h6 : (4 : ℝ) / y ^ 6 ≤ 4 / y ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) hy4 (pow_le_pow_right₀ hy (by norm_num))
    rw [iteratedDeriv_succ, iteratedDeriv_one, (dG2 y hy0).deriv, hval]
    calc |iteratedDeriv 2 H ((y ^ 2)⁻¹) * (4 / y ^ 6) + deriv H ((y ^ 2)⁻¹) * (6 / y ^ 4)|
        ≤ |iteratedDeriv 2 H ((y ^ 2)⁻¹) * (4 / y ^ 6)|
          + |deriv H ((y ^ 2)⁻¹) * (6 / y ^ 4)| := abs_add_le _ _
      _ ≤ B2 * (4 / y ^ 4) + B1 * (6 / y ^ 4) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / y ^ 6),
          abs_of_pos (by positivity : (0 : ℝ) < 6 / y ^ 4)]
        exact add_le_add (mul_le_mul b2 h6 (by positivity) hB20)
          (mul_le_mul_of_nonneg_right b1 (by positivity))
      _ = (4 * B2 + 6 * B1) / y ^ 4 := by ring
      _ ≤ (2 * B1 + (4 * B2 + 6 * B1)) / y ^ 4 :=
        div_le_div_of_nonneg_right (by linarith) hy4.le

/-- **Decay of `h`.** For `y ≥ 0`, `|h|`, `|y h′|` and `|y² h″|` are at most
`C / (1 + y)`. -/
theorem hfun_decay (hP : IsProfile c G) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 ≤ y →
    |hfun G y| ≤ C / (1 + y) ∧ |y * deriv (hfun G) y| ≤ C / (1 + y) ∧
      |y ^ 2 * iteratedDeriv 2 (hfun G) y| ≤ C / (1 + y) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  obtain ⟨M, hM⟩ := hP.upper
  obtain ⟨B, hB0, hB⟩ := profile_deriv_decay hP
  have hh := contDiffOn_hfun hδ hsm
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioi (-δ) := fun y hy => mem_Ioi.2 (by linarith [hy.1])
  have c0 : ContinuousOn (hfun G) (Icc 0 1) := hh.continuousOn.mono hsub
  have c1 : ContinuousOn (deriv (hfun G)) (Icc 0 1) := by
    have h := (contDiffOn_iteratedDeriv isOpen_Ioi hh 1).continuousOn.mono hsub
    rwa [iteratedDeriv_one] at h
  have c2 : ContinuousOn (iteratedDeriv 2 (hfun G)) (Icc 0 1) :=
    (contDiffOn_iteratedDeriv isOpen_Ioi hh 2).continuousOn.mono hsub
  obtain ⟨A0, hA0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn c0
  obtain ⟨A1, hA1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn c1
  obtain ⟨A2, hA2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn c2
  have hA00 : 0 ≤ A0 := (norm_nonneg _).trans (hA0 0 ⟨le_rfl, zero_le_one⟩)
  have hA10 : 0 ≤ A1 := (norm_nonneg _).trans (hA1 0 ⟨le_rfl, zero_le_one⟩)
  have hA20 : 0 ≤ A2 := (norm_nonneg _).trans (hA2 0 ⟨le_rfl, zero_le_one⟩)
  have hM1 : 1 ≤ M := by
    have h := hM 0 le_rfl
    rwa [hP.zero] at h
  have hX : 0 ≤ A0 + A1 + A2 + 3 * B + 2 * M + 2 := by positivity
  refine ⟨2 * (A0 + A1 + A2 + 3 * B + 2 * M + 2) + 1, by positivity, fun y hy => ?_⟩
  have hden : (0 : ℝ) < 1 + y := by linarith
  rcases le_total y 1 with h1 | h1
  · have hmem : y ∈ Icc (0 : ℝ) 1 := ⟨hy, h1⟩
    have a0 := hA0 y hmem
    have a1 := hA1 y hmem
    have a2 := hA2 y hmem
    rw [Real.norm_eq_abs] at a0 a1 a2
    have hC : A0 + A1 + A2 + 3 * B + 2 * M + 2
        ≤ (2 * (A0 + A1 + A2 + 3 * B + 2 * M + 2) + 1) / (1 + y) := by
      rw [le_div_iff₀ hden]
      nlinarith [mul_nonneg hX (by linarith : (0 : ℝ) ≤ 1 - y)]
    refine ⟨?_, ?_, ?_⟩
    · exact (a0.trans (by linarith)).trans hC
    · rw [abs_mul, abs_of_nonneg hy]
      have h := (mul_le_of_le_one_left (abs_nonneg (deriv (hfun G) y)) h1).trans a1
      exact (h.trans (by linarith)).trans hC
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2)]
      have h := (mul_le_of_le_one_left (abs_nonneg (iteratedDeriv 2 (hfun G) y))
        (pow_le_one₀ (n := 2) hy h1)).trans a2
      exact (h.trans (by linarith)).trans hC
  · have hy0 : 0 < y := by linarith
    have hy0' := hy0.ne'
    have hy' : y ∈ Ioi (-δ) := mem_Ioi.2 (by linarith)
    obtain ⟨g1, g2⟩ := hB y h1
    have s0 := mul_hfun hP y
    have s1 := hrel hP hδ hsm 0 y hy'
    have s2 := hrel hP hδ hsm 1 y hy'
    simp only [iteratedDeriv_one, iteratedDeriv_zero, zero_add] at s1 s2
    norm_num at s1 s2
    have hGpos := profile_pos hP hy
    have hGle := hM y hy
    have hG1 : |G y - 1| ≤ M + 1 := by
      rw [abs_le]
      constructor <;> linarith
    have b0 : |hfun G y| ≤ (M + 1) / y := by
      have e : hfun G y = (G y - 1) / y := by
        rw [← s0]
        field_simp
      rw [e, abs_div, abs_of_pos hy0]
      exact div_le_div_of_nonneg_right hG1 hy0.le
    have g1' : |deriv G y| ≤ B / y :=
      g1.trans (div_le_div_of_nonneg_left hB0 hy0 (le_self_pow₀ h1 (by norm_num)))
    have b1 : |y * deriv (hfun G) y| ≤ (B + M + 1) / y := by
      have e : y * deriv (hfun G) y = deriv G y - hfun G y := by linarith
      rw [e]
      calc |deriv G y - hfun G y| ≤ |deriv G y| + |hfun G y| := abs_sub _ _
        _ ≤ B / y + (M + 1) / y := add_le_add g1' b0
        _ = (B + M + 1) / y := by ring
    have b2 : |y ^ 2 * iteratedDeriv 2 (hfun G) y| ≤ (3 * B + 2 * M + 2) / y := by
      have e : y ^ 2 * iteratedDeriv 2 (hfun G) y
          = y * iteratedDeriv 2 G y - 2 * (y * deriv (hfun G) y) := by
        rw [← s2]
        ring
      have g2' : |y * iteratedDeriv 2 G y| ≤ B / y := by
        rw [abs_mul, abs_of_pos hy0]
        calc y * |iteratedDeriv 2 G y| ≤ y * (B / y ^ 4) := mul_le_mul_of_nonneg_left g2 hy0.le
          _ = B / y ^ 3 := by field_simp
          _ ≤ B / y := div_le_div_of_nonneg_left hB0 hy0 (le_self_pow₀ h1 (by norm_num))
      rw [e]
      calc |y * iteratedDeriv 2 G y - 2 * (y * deriv (hfun G) y)|
          ≤ |y * iteratedDeriv 2 G y| + |2 * (y * deriv (hfun G) y)| := abs_sub _ _
        _ ≤ B / y + 2 * ((B + M + 1) / y) := by
          rw [abs_mul 2, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact add_le_add g2' (mul_le_mul_of_nonneg_left b1 (by norm_num))
        _ = (3 * B + 2 * M + 2) / y := by ring
    have key : ∀ K : ℝ, 0 ≤ K → K ≤ A0 + A1 + A2 + 3 * B + 2 * M + 2 →
        K / y ≤ (2 * (A0 + A1 + A2 + 3 * B + 2 * M + 2) + 1) / (1 + y) := by
      intro K hK hKle
      rw [div_le_div_iff₀ hy0 hden]
      nlinarith [mul_nonneg hK (by linarith : (0 : ℝ) ≤ y - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ A0 + A1 + A2 + 3 * B + 2 * M + 2 - K) hy0.le]
    exact ⟨b0.trans (key _ (by linarith) (by linarith)),
      b1.trans (key _ (by positivity) (by linarith)),
      b2.trans (key _ (by positivity) (by linarith))⟩

end Calabi.Flat
