import Calabi.Infinity.Compact
import Calabi.Origin.Global
import Calabi.Origin.Smooth
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# A positive seven-dimensional shrinking profile

This file proves Theorem 3.1 of the manuscript: there are `0 < c < 1` and
`G ∈ C^∞[0, ∞)` with

  `(D - 1)(D + 6)(D + 7)(G - 1) = (y² / 2)(1/G - 1/c)`,   `D = y d/dy`,

`G(0) = 1`, `G′(0) < 0`, `0 < inf G ≤ sup G < ∞`, and an expansion of `G` at
infinity in powers of `y⁻²` with the leading term `c`.

* The equation is stated with the operator expanded,
  `(D - 1)(D + 6)(D + 7)(G - 1) = y³ G‴ + 15 y² G″ + 42 y G′ - 42 (G - 1)`.
* The expansion at infinity is stated in the form in which it is used:
  `H(u) = G(u^{-1/2})` extends to a smooth function on `[0, ∞)` with `H(0) = c`.

With `c = 1 / (1 + d)` and `λ = √27 / (4c)`, the profile is `G(y) = c (1 + P(λ y))`
where `P(r) = p(s)`, `s³ = r²`, and `(p, p′, p″)` is the trajectory of the
profile system of `Calabi.Origin.exists_profile_jet`: the regular solution at
the origin, the certified finite shot, and the bounded tail, matched by
Brouwer's theorem.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.ShrinkingProfile

open Calabi.Shot (State pfield Ntr Ntr_of_ge scaleP scaleU scaleP_pos param Poly)
open Calabi.Shot.Data (dnum)
open Calabi.Match (box mem_box dOf abs_dOf_sub_le)
open Calabi.Origin (kOf oP osol originJet oP_eq_osol abs_osol_le exists_profile_jet
  contDiffOn_oP_infty hasDerivAt_oP_all)
open Calabi.Tail (apx apx1 apx2 tau tau_mem continuous_eval tailP1 tailP2
  hasDerivAt_components)
open Calabi.Infinity (iota iota_pos iota_pow_three contDiffAt_iota hasDerivAt_iota ext
  ext_of_pos ext_profile_zero norm_le_iff contDiffOn_ext_profile contDiffOn_fst)

/-! ### The parameters -/

theorem dOf_mem {z : ℝ × ℝ} (hz : z ∈ box) : 13 / 100 ≤ dOf z ∧ dOf z ≤ 14 / 100 := by
  obtain ⟨h1, h2⟩ := abs_le.1 (abs_dOf_sub_le hz)
  have e1 : (13 : ℝ) / 100 + 1 / 2 ^ 69 ≤ (dnum : ℝ) / (scaleP : ℝ) := by
    norm_num [dnum, scaleP]
  have e2 : (dnum : ℝ) / (scaleP : ℝ) + 1 / 2 ^ 69 ≤ 14 / 100 := by
    norm_num [dnum, scaleP]
  constructor <;> linarith

theorem kOf_le {z : ℝ × ℝ} (hz : z ∈ box) : kOf z ≤ -(1 / 10) := by
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  obtain ⟨a1, a2⟩ := abs_le.1 hz1
  obtain ⟨b1, b2⟩ := abs_le.1 hz2
  have h3 : (Calabi.Origin.Data.knum : ℝ) / (scaleP : ℝ) ≤ -(18 / 100) := by
    norm_num [Calabi.Origin.Data.knum, scaleP]
  have hU : (scaleU : ℝ) = 2 ^ 64 := by norm_num [scaleU]
  have h5 : ((Calabi.Origin.Data.kz1 : ℝ) * z.1 + (Calabi.Origin.Data.kz2 : ℝ) * z.2)
      / (scaleU : ℝ) ≤ 8 / 100 := by
    rw [hU, div_le_iff₀ (by positivity)]
    norm_num [Calabi.Origin.Data.kz1, Calabi.Origin.Data.kz2]
    linarith
  unfold kOf param
  linarith

/-! ### The trajectory -/

theorem apx_bounded (P : Poly) :
    ∃ B, ∀ s, (56 : ℝ) ≤ s → |apx P s| ≤ B ∧ |apx1 P s| ≤ B ∧ |apx2 P s| ≤ B := by
  obtain ⟨C0, h0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_eval P).continuousOn
  obtain ⟨C1, h1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_eval (tailP1 P)).continuousOn
  obtain ⟨C2, h2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_eval (tailP2 P)).continuousOn
  refine ⟨max C0 (max C1 C2), fun s hs => ?_⟩
  obtain ⟨ht0, ht1⟩ := tau_mem hs
  have hτ : tau s ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hP : (1 : ℝ) ≤ (scaleP : ℝ) := by norm_num [scaleP]
  have b0 := h0 _ hτ
  have b1 := h1 _ hτ
  have b2 := h2 _ hτ
  rw [Real.norm_eq_abs] at b0 b1 b2
  refine ⟨?_, ?_, ?_⟩
  · unfold apx
    rw [abs_div, abs_of_pos scaleP_pos]
    exact ((div_le_self (abs_nonneg _) hP).trans b0).trans (le_max_left _ _)
  · unfold apx1
    have hden : (1 : ℝ) ≤ (scaleP : ℝ) * s := one_le_mul_of_one_le_of_one_le hP hs1
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (scaleP : ℝ) * s)]
    exact ((div_le_self (abs_nonneg _) hden).trans b1).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · unfold apx2
    have hden : (1 : ℝ) ≤ (scaleP : ℝ) * s ^ 2 :=
      one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hs1)
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (scaleP : ℝ) * s ^ 2)]
    exact ((div_le_self (abs_nonneg _) hden).trans b2).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-- The trajectory of the profile system on `(0, ∞)`: regular at the origin,
bounded at infinity. -/
theorem exists_trajectory :
    ∃ z ∈ box, ∃ Z : ℝ → State,
      (∀ s, 0 < s → HasDerivAt Z (pfield (dOf z) s (Z s)) s) ∧
      (∀ s, 0 < s → -19 / 20 ≤ (Z s).1) ∧
      (∀ s, 0 < s → s ≤ 1 → Z s = originJet (kOf z) (dOf z) s) ∧
      (∃ B, ∀ s, (56 : ℝ) ≤ s → ‖Z s‖ ≤ B) ∧
      ∀ s, (56 : ℝ) ≤ s → |(Z s).1| ≤ 1 / 100 := by
  obtain ⟨z, hz, Z, hZ, hlow, hor, X, -, ⟨BX, hBX⟩, hXZ⟩ := exists_profile_jet
  obtain ⟨BA, hBA⟩ := apx_bounded Calabi.Tail.Data.tailP
  refine ⟨z, hz, Z, hZ, hlow, hor, ⟨BA + BX, fun s hs => ?_⟩, fun s hs => (hXZ s hs).2⟩
  obtain ⟨a0, a1, a2⟩ := hBA s hs
  obtain ⟨x0, x1, x2⟩ := hBX s hs
  rw [(hXZ s hs).1, norm_le_iff]
  exact ⟨(abs_add_le _ _).trans (add_le_add a0 x0), (abs_add_le _ _).trans (add_le_add a1 x1),
    (abs_add_le _ _).trans (add_le_add a2 x2)⟩

variable {k d c lam : ℝ} {Z : ℝ → State}

theorem exists_upper (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hsmall : ∀ s, (56 : ℝ) ≤ s → |(Z s).1| ≤ 1 / 100) :
    ∃ M, ∀ s, (1 : ℝ) ≤ s → (Z s).1 ≤ M := by
  have hc : ContinuousOn (fun s => (Z s).1) (Icc (1 : ℝ) 56) := fun s hs =>
    (hasDerivAt_components (hZ s (by linarith [hs.1]))).1.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 56)).exists_bound_of_continuousOn hc
  refine ⟨max C (1 / 100), fun s hs => ?_⟩
  rcases le_total s 56 with h | h
  · have hb := hC s ⟨hs, h⟩
    rw [Real.norm_eq_abs] at hb
    exact ((le_abs_self _).trans hb).trans (le_max_left _ _)
  · exact ((le_abs_self _).trans (hsmall s h)).trans (le_max_right _ _)

/-! ### The variable `y` -/

/-- The variable `s` of the profile system as a function of `y`: `s³ = (λ y)²`. -/
noncomputable def sOf (lam y : ℝ) : ℝ := iota (((lam * y) ^ 2)⁻¹)

theorem sOf_pos {y : ℝ} (hlam : 0 < lam) (hy : 0 < y) : 0 < sOf lam y :=
  iota_pos (inv_pos.2 (pow_pos (mul_pos hlam hy) 2))

theorem sOf_pow_three {y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    sOf lam y ^ 3 = (lam * y) ^ 2 := by
  unfold sOf
  rw [iota_pow_three (inv_pos.2 (pow_pos (mul_pos hlam hy) 2)), inv_inv]

theorem hasDerivAt_sOf {y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    HasDerivAt (sOf lam) (2 / 3 * sOf lam y / y) y := by
  have hly : 0 < lam * y := mul_pos hlam hy
  have hσ : 0 < ((lam * y) ^ 2)⁻¹ := inv_pos.2 (pow_pos hly 2)
  have ha : HasDerivAt (fun y : ℝ => lam * y) lam y :=
    ((hasDerivAt_id' y).const_mul lam).congr_deriv (mul_one lam)
  have hb : HasDerivAt (fun y : ℝ => (lam * y) ^ 2) (2 * (lam * y) * lam) y :=
    (ha.fun_pow 2).congr_deriv (by norm_num)
  have h1 := hb.fun_inv (pow_pos hly 2).ne'
  have h2 := (hasDerivAt_iota hσ).comp y h1
  have h3 : iota (((lam * y) ^ 2)⁻¹) ^ 3 = (lam * y) ^ 2 := by
    rw [iota_pow_three hσ, inv_inv]
  have h4 : iota (((lam * y) ^ 2)⁻¹) ^ 4 = iota (((lam * y) ^ 2)⁻¹) * (lam * y) ^ 2 := by
    linear_combination iota (((lam * y) ^ 2)⁻¹) * h3
  refine h2.congr_deriv ?_
  rw [h4]
  unfold sOf
  have hy0 := hy.ne'
  have hl0 := hlam.ne'
  field_simp

theorem hasDerivAt_comp_sOf {y : ℝ} (hlam : 0 < lam) (hy : 0 < y) {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' (sOf lam y)) :
    HasDerivAt (fun y => f (sOf lam y)) (2 / 3 * sOf lam y * f' / y) y := by
  refine (hf.comp y (hasDerivAt_sOf hlam hy)).congr_deriv ?_
  ring

/-! ### The profile -/

/-- The profile in the variable `r = λ y`: the regular solution for `r < 1`,
and the trajectory in the variable `s = r^{2/3}` beyond. -/
noncomputable def Pf (k d : ℝ) (Z : ℝ → State) (r : ℝ) : ℝ :=
  if r < 1 then oP k d r else (Z (iota ((r ^ 2)⁻¹))).1

theorem Pf_of_pos (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s) {r : ℝ} (hr : 0 < r) :
    Pf k d Z r = (Z (iota ((r ^ 2)⁻¹))).1 := by
  unfold Pf
  split_ifs with h
  · have hσ : 0 < (r ^ 2)⁻¹ := inv_pos.2 (pow_pos hr 2)
    have hs0 : 0 < iota ((r ^ 2)⁻¹) := iota_pos hσ
    have hs3 : iota ((r ^ 2)⁻¹) ^ 3 = r ^ 2 := by rw [iota_pow_three hσ, inv_inv]
    have hs1 : iota ((r ^ 2)⁻¹) ≤ 1 := by
      by_contra hcon
      have h1 : 1 < iota ((r ^ 2)⁻¹) := not_le.1 hcon
      have h2 : (1 : ℝ) < iota ((r ^ 2)⁻¹) ^ 3 := one_lt_pow₀ h1 (by norm_num)
      have h3 : r ^ 2 < 1 := pow_lt_one₀ hr.le h (by norm_num)
      linarith
    have hsq : iota ((r ^ 2)⁻¹) * Real.sqrt (iota ((r ^ 2)⁻¹)) = r := by
      have h4 : (iota ((r ^ 2)⁻¹) * Real.sqrt (iota ((r ^ 2)⁻¹))) ^ 2 = r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs0.le]
        linear_combination hs3
      exact (pow_left_inj₀ (mul_nonneg hs0.le (Real.sqrt_nonneg _)) hr.le two_ne_zero).1 h4
    rw [hor _ hs0 hs1]
    show oP k d r = oP k d (iota ((r ^ 2)⁻¹) * Real.sqrt (iota ((r ^ 2)⁻¹)))
    rw [hsq]
  · rfl

theorem Pf_mem {z : ℝ × ℝ} (hz : z ∈ box) (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1) {M : ℝ}
    (hM : ∀ s, (1 : ℝ) ≤ s → (Z s).1 ≤ M) {r : ℝ} (hr : 0 ≤ r) :
    -19 / 20 ≤ Pf (kOf z) (dOf z) Z r ∧ Pf (kOf z) (dOf z) Z r ≤ max (2 / 5) M := by
  unfold Pf
  split_ifs with h
  · have hr1 : |r| ≤ 1 := abs_le.2 ⟨by linarith, h.le⟩
    rw [oP_eq_osol _ _ hr1]
    obtain ⟨b1, b2⟩ := abs_le.1 (abs_osol_le hz hr1)
    exact ⟨by linarith, b2.trans (le_max_left _ _)⟩
  · have hr1 : 1 ≤ r := not_lt.1 h
    have hσ : 0 < (r ^ 2)⁻¹ := inv_pos.2 (pow_pos (by linarith) 2)
    have hs0 := iota_pos hσ
    have hs3 : iota ((r ^ 2)⁻¹) ^ 3 = r ^ 2 := by rw [iota_pow_three hσ, inv_inv]
    have hs1 : 1 ≤ iota ((r ^ 2)⁻¹) := by
      by_contra hcon
      have h1 : iota ((r ^ 2)⁻¹) < 1 := not_le.1 hcon
      have h2 : iota ((r ^ 2)⁻¹) ^ 3 < 1 := pow_lt_one₀ hs0.le h1 (by norm_num)
      have h3 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr1
      linarith
    exact ⟨hlow _ hs0, (hM _ hs1).trans (le_max_right _ _)⟩

/-- The profile `G`. -/
noncomputable def Gf (k d : ℝ) (Z : ℝ → State) (c lam y : ℝ) : ℝ :=
  c * (1 + Pf k d Z (lam * y))

theorem Gf_of_pos (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s) (hlam : 0 < lam) {y : ℝ}
    (hy : 0 < y) : Gf k d Z c lam y = c * (1 + (Z (sOf lam y)).1) := by
  unfold Gf sOf
  rw [Pf_of_pos hor (mul_pos hlam hy)]

theorem Gf_near_zero {y : ℝ} (hy : lam * y < 1) :
    Gf k d Z c lam y = c * (1 + oP k d (lam * y)) := by
  unfold Gf Pf
  rw [ite_eq_left hy]

theorem Gf_zero (hc : c * (1 + d) = 1) : Gf k d Z c lam 0 = 1 := by
  have h0 : lam * 0 < 1 := by
    rw [mul_zero]
    exact one_pos
  have e : oP k d 0 = d := by simp [oP]
  rw [Gf_near_zero h0, mul_zero, e, hc]

theorem eventually_near_zero (hlam : 0 < lam) :
    ∀ᶠ y in 𝓝 (0 : ℝ), Gf k d Z c lam y = c * (1 + oP k d (lam * y)) := by
  have hnhd : Iio (1 / lam) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (one_div_pos.2 hlam)
  filter_upwards [hnhd] with x hx
  refine Gf_near_zero ?_
  have := (lt_div_iff₀ hlam).1 hx
  linarith

theorem hasDerivAt_Gf_zero (hlam : 0 < lam) :
    HasDerivAt (Gf k d Z c lam) (c * (k * lam)) 0 := by
  have e : lam * (0 : ℝ) = 0 := mul_zero lam
  have h0 : HasDerivAt (oP k d) k (lam * 0) := by
    rw [e]
    exact (hasDerivAt_oP_all k d 0).congr_deriv (by simp)
  have h1 : HasDerivAt (fun y : ℝ => lam * y) lam 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul lam).congr_deriv (mul_one lam)
  have h2 : HasDerivAt (fun y : ℝ => c * (1 + oP k d (lam * y))) (c * (k * lam)) 0 :=
    ((h0.comp 0 h1).const_add 1).const_mul c
  exact h2.congr_of_eventuallyEq (eventually_near_zero hlam)

theorem contDiffOn_Gf (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s)
    (hoP : ContDiffOn ℝ ∞ (oP k d) (Ioo (-1 : ℝ) 1)) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (Gf k d Z c lam) (Ici 0) := by
  intro y hy
  rcases eq_or_lt_of_le (mem_Ici.1 hy) with h | h
  · subst h
    have e : lam * (0 : ℝ) = 0 := mul_zero lam
    have h0 : ContDiffAt ℝ ∞ (oP k d) (lam * 0) := by
      rw [e]
      exact hoP.contDiffAt (Ioo_mem_nhds (by norm_num) (by norm_num))
    have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => lam * y) 0 := contDiffAt_const.mul contDiffAt_id
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => c * (1 + oP k d (lam * y))) 0 :=
      contDiffAt_const.mul (contDiffAt_const.add (h0.comp 0 h1))
    exact (h2.congr_of_eventuallyEq (eventually_near_zero hlam)).contDiffWithinAt
  · have hs := sOf_pos hlam h
    have hly : 0 < lam * y := mul_pos hlam h
    have h0 : ContDiffAt ℝ ∞ (fun s => (Z s).1) (sOf lam y) :=
      (contDiffOn_fst hZ hlow).contDiffAt (Ioi_mem_nhds hs)
    have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => ((lam * y) ^ 2)⁻¹) y :=
      ((contDiffAt_const.mul contDiffAt_id).pow 2).inv (pow_pos hly 2).ne'
    have h2 : ContDiffAt ℝ ∞ (sOf lam) y :=
      (contDiffAt_iota (inv_pos.2 (pow_pos hly 2)) ∞).comp y h1
    have h3 : ContDiffAt ℝ ∞ (fun y : ℝ => c * (1 + (Z (sOf lam y)).1)) y :=
      contDiffAt_const.mul (contDiffAt_const.add (h0.comp y h2))
    refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact Gf_of_pos hor hlam hx

theorem eventually_near {y₀ : ℝ} (hlam : 0 < lam) (hy : lam * y₀ < 1) :
    ∀ᶠ y in 𝓝 y₀, Gf k d Z c lam y = c * (1 + oP k d (lam * y)) := by
  have hy' : y₀ < 1 / lam := by
    rw [lt_div_iff₀ hlam]
    linarith
  filter_upwards [Iio_mem_nhds hy'] with x hx
  refine Gf_near_zero ?_
  have := (lt_div_iff₀ hlam).1 hx
  linarith

/-- The profile is smooth on a neighbourhood of `[0, ∞)`. -/
theorem contDiffOn_Gf_open (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s)
    (hoP : ContDiffOn ℝ ∞ (oP k d) (Ioo (-1 : ℝ) 1)) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (Gf k d Z c lam) (Ioi (-(1 / lam))) := by
  intro y hy
  rcases lt_or_ge (lam * y) 1 with h | h
  · have hl0 := hlam.ne'
    have hlow' : -1 < lam * y := by
      have h1 := mul_lt_mul_of_pos_left (mem_Ioi.1 hy) hlam
      have h2 : lam * -(1 / lam) = -1 := by field_simp
      linarith
    have h0 : ContDiffAt ℝ ∞ (oP k d) (lam * y) := hoP.contDiffAt (Ioo_mem_nhds hlow' h)
    have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => lam * y) y := contDiffAt_const.mul contDiffAt_id
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => c * (1 + oP k d (lam * y))) y :=
      contDiffAt_const.mul (contDiffAt_const.add (h0.comp y h1))
    exact (h2.congr_of_eventuallyEq (eventually_near hlam h)).contDiffWithinAt
  · have hy0 : 0 < y := by
      by_contra hcon
      have := mul_nonpos_of_nonneg_of_nonpos hlam.le (not_lt.1 hcon)
      linarith
    exact ((contDiffOn_Gf hZ hlow hor hoP hlam).contDiffAt (Ici_mem_nhds hy0)).contDiffWithinAt

/-- The profile in the variable `u = y⁻²`. -/
noncomputable def Hf (Z : ℝ → State) (c lam u : ℝ) : ℝ :=
  c * (1 + ext (fun s => (Z s).1) (u / lam ^ 2))

theorem contDiffOn_Hf (hext : ContDiffOn ℝ ∞ (ext fun s => (Z s).1) (Ici 0)) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (Hf Z c lam) (Ici 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun u : ℝ => u / lam ^ 2) (Ici 0) := contDiffOn_id.div_const _
  have h2 : MapsTo (fun u : ℝ => u / lam ^ 2) (Ici 0) (Ici 0) := fun u hu =>
    div_nonneg (mem_Ici.1 hu) (pow_pos hlam 2).le
  exact contDiffOn_const.mul (contDiffOn_const.add (hext.comp h1 h2))

theorem Hf_zero : Hf Z c lam 0 = c := by
  unfold Hf
  rw [zero_div, ext_profile_zero, add_zero, mul_one]

theorem rpow_neg_half_sq {u : ℝ} (hu : 0 < u) : (u ^ (-(1 : ℝ) / 2)) ^ 2 = u⁻¹ := by
  have e : (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le, e, Real.rpow_neg_one]

theorem Hf_match (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s) (hlam : 0 < lam) {u : ℝ}
    (hu : 0 < u) : Hf Z c lam u = Gf k d Z c lam (u ^ (-(1 : ℝ) / 2)) := by
  have hr : 0 < u ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  have e : ((lam * u ^ (-(1 : ℝ) / 2)) ^ 2)⁻¹ = u / lam ^ 2 := by
    rw [mul_pow, rpow_neg_half_sq hu, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  rw [Gf_of_pos hor hlam hr]
  unfold Hf sOf
  rw [e, ext_of_pos _ (div_pos hu (pow_pos hlam 2))]

/-! ### The equation -/

/-- `D p`, `D = y d/dy = (2/3) s d/ds`, along the trajectory. -/
noncomputable def D1 (Z : ℝ → State) (s : ℝ) : ℝ := 2 / 3 * s * (Z s).2.1

/-- `D² p` along the trajectory. -/
noncomputable def D2 (Z : ℝ → State) (s : ℝ) : ℝ :=
  4 / 9 * (s ^ 2 * (Z s).2.2 + s * (Z s).2.1)

/-- `D³ p` along the trajectory. -/
noncomputable def D3 (d : ℝ) (Z : ℝ → State) (s : ℝ) : ℝ :=
  8 / 27 * (s ^ 3 * (pfield d s (Z s)).2.2 + 3 * s ^ 2 * (Z s).2.2 + s * (Z s).2.1)

theorem hasDerivAt_D1 (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s) {s : ℝ}
    (hs : 0 < s) : HasDerivAt (D1 Z) (2 / 3 * ((Z s).2.1 + s * (Z s).2.2)) s := by
  obtain ⟨-, h2, -⟩ := hasDerivAt_components (hZ s hs)
  have h := ((hasDerivAt_id' s).const_mul (2 / 3 : ℝ)).fun_mul h2
  refine h.congr_deriv ?_
  have e : (pfield d s (Z s)).2.1 = (Z s).2.2 := rfl
  rw [e]
  ring

theorem hasDerivAt_D2 (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (D2 Z) (4 / 9 * (2 * s * (Z s).2.2 + s ^ 2 * (pfield d s (Z s)).2.2
      + ((Z s).2.1 + s * (Z s).2.2))) s := by
  obtain ⟨-, h2, h3⟩ := hasDerivAt_components (hZ s hs)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s :=
    (hasDerivAt_pow 2 s).congr_deriv (by norm_num)
  have h := ((hsq.fun_mul h3).fun_add ((hasDerivAt_id' s).fun_mul h2)).const_mul (4 / 9 : ℝ)
  refine h.congr_deriv ?_
  have e : (pfield d s (Z s)).2.1 = (Z s).2.2 := rfl
  rw [e]
  ring

section Chain

variable (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s) (hlam : 0 < lam) {y : ℝ}
  (hy : 0 < y)

include hZ hlam hy

theorem hasDerivAt_b0 : HasDerivAt (fun y => (Z (sOf lam y)).1) (D1 Z (sOf lam y) / y) y :=
  (hasDerivAt_comp_sOf hlam hy (hasDerivAt_components (hZ _ (sOf_pos hlam hy))).1).congr_deriv
    (by simp only [D1, pfield])

theorem hasDerivAt_b1 : HasDerivAt (fun y => D1 Z (sOf lam y)) (D2 Z (sOf lam y) / y) y :=
  (hasDerivAt_comp_sOf hlam hy (hasDerivAt_D1 hZ (sOf_pos hlam hy))).congr_deriv
    (by simp only [D2]; ring)

theorem hasDerivAt_b2 : HasDerivAt (fun y => D2 Z (sOf lam y)) (D3 d Z (sOf lam y) / y) y :=
  (hasDerivAt_comp_sOf hlam hy (hasDerivAt_D2 hZ (sOf_pos hlam hy))).congr_deriv
    (by simp only [D3]; ring)

theorem hasDerivAt_g0 (c : ℝ) :
    HasDerivAt (fun y => c * (1 + (Z (sOf lam y)).1)) (c * D1 Z (sOf lam y) / y) y :=
  (((hasDerivAt_b0 hZ hlam hy).const_add 1).const_mul c).congr_deriv (by ring)

theorem hasDerivAt_g1 (c : ℝ) :
    HasDerivAt (fun y => c * D1 Z (sOf lam y) / y)
      (c * (D2 Z (sOf lam y) - D1 Z (sOf lam y)) / y ^ 2) y := by
  have hy0 := hy.ne'
  have h := ((hasDerivAt_b1 hZ hlam hy).const_mul c).fun_div (hasDerivAt_id' y) hy0
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_g2 (c : ℝ) :
    HasDerivAt (fun y => c * (D2 Z (sOf lam y) - D1 Z (sOf lam y)) / y ^ 2)
      (c * (D3 d Z (sOf lam y) - 3 * D2 Z (sOf lam y) + 2 * D1 Z (sOf lam y)) / y ^ 3) y := by
  have hy0 := hy.ne'
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y :=
    (hasDerivAt_pow 2 y).congr_deriv (by norm_num)
  have h := (((hasDerivAt_b2 hZ hlam hy).fun_sub (hasDerivAt_b1 hZ hlam hy)).const_mul c).fun_div
    hp (pow_ne_zero 2 hy0)
  refine h.congr_deriv ?_
  field_simp
  ring

end Chain

/-- The profile equation in the variable `y`, as an identity between real
numbers. -/
theorem ode_algebra {c d s y p0 p1 p2 lam : ℝ} (hc : c * (1 + d) = 1) (hc0 : 0 < c) (hs : 0 < s)
    (hy : 0 < y) (hp : 0 < 1 + p0) (hlam : lam ^ 2 = 27 / (16 * c ^ 2))
    (hsy : s ^ 3 = (lam * y) ^ 2) :
    y ^ 3 * (c * (8 / 27 * (s ^ 3 * (-(21 / s) * p2 - 337 / (4 * s ^ 2) * p1
        + 567 / (4 * s ^ 3) * (p0 - d) - p0 / (1 + p0)) + 3 * s ^ 2 * p2 + s * p1)
        - 3 * (4 / 9 * (s ^ 2 * p2 + s * p1)) + 2 * (2 / 3 * s * p1)) / y ^ 3)
      + 15 * y ^ 2 * (c * (4 / 9 * (s ^ 2 * p2 + s * p1) - 2 / 3 * s * p1) / y ^ 2)
      + 42 * y * (c * (2 / 3 * s * p1) / y) - 42 * (c * (1 + p0) - 1)
      = y ^ 2 / 2 * ((c * (1 + p0))⁻¹ - c⁻¹) := by
  have hy0 := hy.ne'
  have hs0 := hs.ne'
  have hc0' := hc0.ne'
  have hp0 := hp.ne'
  have hd : d = 1 / c - 1 := by
    rw [eq_sub_iff_add_eq, eq_div_iff hc0']
    linarith
  have hy2 : y ^ 2 = 16 * c ^ 2 * s ^ 3 / 27 := by
    rw [hsy, mul_pow, hlam]
    field_simp
  have e1 : ∀ X : ℝ, y ^ 3 * (X / y ^ 3) = X := fun X => by field_simp
  have e2 : ∀ X : ℝ, 15 * y ^ 2 * (X / y ^ 2) = 15 * X := fun X => by field_simp
  have e3 : ∀ X : ℝ, 42 * y * (X / y) = 42 * X := fun X => by field_simp
  rw [e1, e2, e3, hy2, hd]
  field_simp
  ring

theorem ode_Gf (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hor : ∀ s, 0 < s → s ≤ 1 → Z s = originJet k d s) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 = 27 / (16 * c ^ 2)) (hc : c * (1 + d) = 1) (hc0 : 0 < c) {y : ℝ}
    (hy : 0 < y) :
    y ^ 3 * iteratedDeriv 3 (Gf k d Z c lam) y + 15 * y ^ 2 * iteratedDeriv 2 (Gf k d Z c lam) y
      + 42 * y * deriv (Gf k d Z c lam) y - 42 * (Gf k d Z c lam y - 1)
      = y ^ 2 / 2 * ((Gf k d Z c lam y)⁻¹ - c⁻¹) := by
  have hG : ∀ x, 0 < x → Gf k d Z c lam x = c * (1 + (Z (sOf lam x)).1) := fun x hx =>
    Gf_of_pos hor hlam hx
  have hd1 : ∀ x, 0 < x → HasDerivAt (Gf k d Z c lam) (c * D1 Z (sOf lam x) / x) x := by
    intro x hx
    refine (hasDerivAt_g0 hZ hlam hx c).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with u hu using hG u hu
  have e1 : ∀ x, 0 < x → deriv (Gf k d Z c lam) x = c * D1 Z (sOf lam x) / x := fun x hx =>
    (hd1 x hx).deriv
  have hd2 : ∀ x, 0 < x → HasDerivAt (deriv (Gf k d Z c lam))
      (c * (D2 Z (sOf lam x) - D1 Z (sOf lam x)) / x ^ 2) x := by
    intro x hx
    refine (hasDerivAt_g1 hZ hlam hx c).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with u hu using e1 u hu
  have e2 : ∀ x, 0 < x → deriv (deriv (Gf k d Z c lam)) x =
      c * (D2 Z (sOf lam x) - D1 Z (sOf lam x)) / x ^ 2 := fun x hx => (hd2 x hx).deriv
  have hd3 : HasDerivAt (deriv (deriv (Gf k d Z c lam)))
      (c * (D3 d Z (sOf lam y) - 3 * D2 Z (sOf lam y) + 2 * D1 Z (sOf lam y)) / y ^ 3) y := by
    refine (hasDerivAt_g2 hZ hlam hy c).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with u hu using e2 u hu
  have i2 : iteratedDeriv 2 (Gf k d Z c lam) = deriv (deriv (Gf k d Z c lam)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have i3 : iteratedDeriv 3 (Gf k d Z c lam) = deriv (deriv (deriv (Gf k d Z c lam))) := by
    rw [iteratedDeriv_succ, i2]
  have hs := sOf_pos hlam hy
  have hp : 0 < 1 + (Z (sOf lam y)).1 := by linarith [hlow _ hs]
  have key := ode_algebra (p0 := (Z (sOf lam y)).1) (p1 := (Z (sOf lam y)).2.1)
    (p2 := (Z (sOf lam y)).2.2) hc hc0 hs hy hp hlam2 (sOf_pow_three hlam hy)
  rw [i3, i2, hd3.deriv, e2 y hy, e1 y hy, hG y hy]
  simp only [D1, D2, D3, pfield, Ntr_of_ge (hlow _ hs)]
  exact key

end Calabi.ShrinkingProfile

namespace Calabi

open Calabi.ShrinkingProfile Calabi.Match Calabi.Origin Calabi.Infinity

/-- A profile as in Theorem 3.1 of the manuscript, smooth on a neighbourhood of
`[0, ∞)`:

* `(D - 1)(D + 6)(D + 7)(G - 1) = (y² / 2)(1/G - 1/c)` for `D = y d/dy`, written
  with the operator expanded;
* `G(0) = 1` and `G′(0) < 0`;
* `G` is bounded above and below by positive constants on `[0, ∞)`;
* `H(u) = G(u^{-1/2})` extends smoothly to `u = 0` with `H(0) = c`: this is the
  expansion of `G` at infinity in powers of `y⁻²`, with all its derivatives. -/
structure IsProfile (c : ℝ) (G : ℝ → ℝ) : Prop where
  c_pos : 0 < c
  c_lt_one : c < 1
  smooth : ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ ∞ G (Ioi (-δ))
  ode : ∀ y, 0 < y → y ^ 3 * iteratedDeriv 3 G y + 15 * y ^ 2 * iteratedDeriv 2 G y
    + 42 * y * deriv G y - 42 * (G y - 1) = y ^ 2 / 2 * ((G y)⁻¹ - c⁻¹)
  zero : G 0 = 1
  deriv_neg : deriv G 0 < 0
  lower : ∃ κ, 0 < κ ∧ ∀ y, 0 ≤ y → κ ≤ G y
  upper : ∃ M, ∀ y, 0 ≤ y → G y ≤ M
  compact : ∃ H : ℝ → ℝ, ContDiffOn ℝ ∞ H (Ici 0) ∧ H 0 = c ∧
    ∀ u, 0 < u → H u = G (u ^ (-(1 : ℝ) / 2))

/-- **Theorem 3.1: a positive seven-dimensional shrinking profile.** -/
theorem exists_profile : ∃ (c : ℝ) (G : ℝ → ℝ), IsProfile c G := by
  obtain ⟨z, hz, Z, hZ, hlow, hor, hbdd, hsmall⟩ := exists_trajectory
  obtain ⟨hd1, hd2⟩ := dOf_mem hz
  have hk := kOf_le hz
  have hd0 : 0 < 1 + dOf z := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 + dOf z) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    exact one_div_pos.2 hd0
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hd0]
    linarith
  have hcd : c * (1 + dOf z) = 1 := by
    rw [hc]
    exact one_div_mul_cancel hd0.ne'
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.sqrt 27 / (4 * c) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact div_pos (Real.sqrt_pos.2 (by norm_num)) (by positivity)
  have hlam2 : lam ^ 2 = 27 / (16 * c ^ 2) := by
    rw [hlam, div_pow, Real.sq_sqrt (by norm_num), mul_pow]
    norm_num
  have hoP : ContDiffOn ℝ ∞ (oP (kOf z) (dOf z)) (Ioo (-1 : ℝ) 1) :=
    contDiffOn_oP_infty fun r hr => by
      have := (abs_le.1 (abs_osol_le hz (abs_le.2 ⟨hr.1.le, hr.2.le⟩))).1
      linarith
  obtain ⟨M₁, hM₁⟩ := exists_upper hZ hsmall
  have hder := hasDerivAt_Gf_zero (k := kOf z) (d := dOf z) (Z := Z) (c := c) hlam0
  refine ⟨c, Gf (kOf z) (dOf z) Z c lam, ?_⟩
  exact
    { c_pos := hc0
      c_lt_one := hc1
      smooth := ⟨1 / lam, one_div_pos.2 hlam0, contDiffOn_Gf_open hZ hlow hor hoP hlam0⟩
      ode := fun y hy => ode_Gf hZ hlow hor hlam0 hlam2 hcd hc0 hy
      zero := Gf_zero hcd
      deriv_neg := by
        rw [hder.deriv]
        exact mul_neg_of_pos_of_neg hc0 (mul_neg_of_neg_of_pos (by linarith) hlam0)
      lower := ⟨c / 20, by positivity, fun y hy => by
        obtain ⟨b1, -⟩ := Pf_mem hz hlow hM₁ (mul_nonneg hlam0.le hy)
        unfold Gf
        have hm := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) / 20 ≤ 1 + Pf (kOf z) (dOf z) Z (lam * y) by linarith) hc0.le
        linarith⟩
      upper := ⟨c * (1 + max (2 / 5) M₁), fun y hy => by
        obtain ⟨-, b2⟩ := Pf_mem hz hlow hM₁ (mul_nonneg hlam0.le hy)
        unfold Gf
        exact mul_le_mul_of_nonneg_left (by linarith) hc0.le⟩
      compact := ⟨Hf Z c lam, contDiffOn_Hf (contDiffOn_ext_profile hZ hlow hbdd hsmall) hlam0,
        Hf_zero, fun u hu => Hf_match hor hlam0 hu⟩ }

/-- Theorem 3.1 with the profile on the closed half-line `[0, ∞)`, as in the
manuscript. -/
theorem shrinking_profile :
    ∃ (c : ℝ) (G H : ℝ → ℝ), 0 < c ∧ c < 1 ∧
      ContDiffOn ℝ ∞ G (Ici 0) ∧
      (∀ y, 0 < y → y ^ 3 * iteratedDeriv 3 G y + 15 * y ^ 2 * iteratedDeriv 2 G y
        + 42 * y * deriv G y - 42 * (G y - 1) = y ^ 2 / 2 * ((G y)⁻¹ - c⁻¹)) ∧
      G 0 = 1 ∧ (∃ g, g < 0 ∧ HasDerivWithinAt G g (Ici 0) 0) ∧
      (∃ κ, 0 < κ ∧ ∀ y, 0 ≤ y → κ ≤ G y) ∧ (∃ M, ∀ y, 0 ≤ y → G y ≤ M) ∧
      ContDiffOn ℝ ∞ H (Ici 0) ∧ H 0 = c ∧ ∀ u, 0 < u → H u = G (u ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨c, G, hP⟩ := exists_profile
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  obtain ⟨H, hH, hH0, hm⟩ := hP.compact
  have hd : HasDerivAt G (deriv G 0) 0 :=
    ((hsm.contDiffAt (Ioi_mem_nhds (by linarith))).differentiableAt (by simp)).hasDerivAt
  exact ⟨c, G, H, hP.c_pos, hP.c_lt_one,
    hsm.mono fun y hy => mem_Ioi.2 (by linarith [mem_Ici.1 hy]), hP.ode, hP.zero,
    ⟨deriv G 0, hP.deriv_neg, hd.hasDerivWithinAt⟩, hP.lower, hP.upper, hH, hH0, hm⟩

end Calabi
