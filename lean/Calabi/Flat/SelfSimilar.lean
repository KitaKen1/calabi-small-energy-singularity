import Calabi.ShrinkingProfile
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The flat self-similar solution

For a profile `G` as in Theorem 3.1, put `h(y) = (G(y) - 1)/y`, `h(0) = G′(0)`,
and `F(t, x) = ρ⁻¹ h(x/ρ)` with `ρ = √(-t)`. This file proves the last
assertion of Theorem 3.1: `F` solves the flat equation

  `F_t + (1 + x F)² (x² F_xxxx + 20 x F_xxx + 90 F_xx) = 0`

for `t < 0` and `x ≥ 0`, including `x = 0`. The operator in brackets is
`(x ∂ₓ² + 9 ∂ₓ)² = Δ² / 16` on radial functions of `x = |z|²`, `z ∈ ℝ¹⁸`.

* `ode4`: applying `D - 2` to the profile equation gives the equation of order
  four `(D - 2)(D - 1)(D + 6)(D + 7)(G - 1) = -y³ G′ / (2 G²)`.
* `contDiffOn_hfun`: `h` is smooth on a neighbourhood of `[0, ∞)` (Hadamard's
  lemma).
* `hfun_ode`: `y² h⁗ + 20 y h‴ + 90 h″ = -(h + y h′) / (2 (1 + y h)²)` on
  `[0, ∞)`; the value at `y = 0` follows by continuity.
* `flat_equation`: the equation for `F`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Flat

open Calabi.Origin (T contDiffOn_T T_eq_div)

/-! ### Derivatives of smooth functions on open sets -/

theorem contDiffOn_iteratedDeriv {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) : ∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv k f) s
  | 0 => by
    rw [iteratedDeriv_zero]
    exact hf
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact ((contDiffOn_infty_iff_deriv_of_isOpen hs).1 (contDiffOn_iteratedDeriv hs hf k)).2

theorem hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (k : ℕ) {y : ℝ} (hy : y ∈ s) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f y) y := by
  have hd := ((contDiffOn_infty_iff_deriv_of_isOpen hs).1 (contDiffOn_iteratedDeriv hs hf k)).1
  rw [iteratedDeriv_succ]
  exact ((hd y hy).differentiableAt (hs.mem_nhds hy)).hasDerivAt

/-- If `y a + n b = g` on an open set, `b′ = a`, then `y a′ + (n + 1) a = g′`. -/
theorem leibniz_step {U : Set ℝ} (hU : IsOpen U) {a a' b g g' : ℝ → ℝ} {n : ℝ}
    (h : ∀ y ∈ U, y * a y + n * b y = g y) (ha : ∀ y ∈ U, HasDerivAt a (a' y) y)
    (hb : ∀ y ∈ U, HasDerivAt b (a y) y) (hg : ∀ y ∈ U, HasDerivAt g (g' y) y) {y : ℝ}
    (hy : y ∈ U) : y * a' y + (n + 1) * a y = g' y := by
  have h1 : HasDerivAt (fun y => y * a y + n * b y) (1 * a y + y * a' y + n * a y) y :=
    ((hasDerivAt_id' y).fun_mul (ha y hy)).fun_add ((hb y hy).const_mul n)
  have h2 : HasDerivAt (fun y => y * a y + n * b y) (g' y) y :=
    (hg y hy).congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hy] with x hx using h x hx)
  have h3 := h1.unique h2
  linarith

/-! ### Division by `y` -/

/-- Hadamard's lemma: the difference quotient at `0` is an average of the
derivative. -/
theorem dslope_eq_T {f : ℝ → ℝ} {δ : ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo (-δ) δ)) {y : ℝ}
    (hy : y ∈ Ioo (-δ) δ) (h0 : (0 : ℝ) ∈ Ioo (-δ) δ) : dslope f 0 y = T 0 (deriv f) y := by
  have hopen : IsOpen (Ioo (-δ) δ) := isOpen_Ioo
  obtain ⟨hdiff, hder⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hopen).1 hf
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [dslope_same]
    unfold T
    simp
  · rw [dslope_of_ne f hy0, slope_def_field, T_eq_div 0 hy0]
    have hsub : uIcc 0 y ⊆ Ioo (-δ) δ := ordConnected_Ioo.uIcc_subset h0 hy
    have hint : IntervalIntegrable (deriv f) MeasureTheory.volume 0 y :=
      (hder.continuousOn.mono hsub).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => ((hdiff x (hsub hx)).differentiableAt (hopen.mem_nhds (hsub hx))).hasDerivAt)
      hint
    simp only [pow_zero, one_mul, zero_add, pow_one, sub_zero]
    rw [hftc]

theorem contDiffOn_dslope {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ∞ f (Ioo (-δ) δ)) : ContDiffOn ℝ ∞ (dslope f 0) (Ioo (-δ) δ) := by
  have hopen : IsOpen (Ioo (-δ) δ) := isOpen_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hder := ((contDiffOn_infty_iff_deriv_of_isOpen hopen).1 hf).2
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => deriv f (δ * x)) (Ioo (-1 : ℝ) 1) :=
    hder.comp (contDiffOn_const.mul contDiffOn_id) fun x hx =>
      ⟨by
        have := mul_pos hδ (show (0 : ℝ) < x + 1 by linarith [hx.1])
        linarith, by
        have := mul_pos hδ (show (0 : ℝ) < 1 - x by linarith [hx.2])
        linarith⟩
  have hT : ContDiffOn ℝ ∞ (T 0 fun x : ℝ => deriv f (δ * x)) (Ioo (-1 : ℝ) 1) :=
    contDiffOn_infty.2 fun m => contDiffOn_T m 0 _ (contDiffOn_infty.1 hg m)
  have hcomp : ContDiffOn ℝ ∞ (fun y : ℝ => T 0 (fun x : ℝ => deriv f (δ * x)) (y / δ))
      (Ioo (-δ) δ) :=
    hT.comp (contDiffOn_id.div_const δ) fun y hy =>
      ⟨by
        rw [lt_div_iff₀ hδ]
        linarith [hy.1], by
        rw [div_lt_one hδ]
        exact hy.2⟩
  refine hcomp.congr fun y hy => ?_
  rw [dslope_eq_T hf hy h0]
  unfold T
  have hδ0 := hδ.ne'
  have e : ∀ t : ℝ, δ * (t * (y / δ)) = t * y := fun t => by field_simp
  simp only [e]

theorem contDiffOn_dslope_Ioi {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ∞ f (Ioi (-δ))) : ContDiffOn ℝ ∞ (dslope f 0) (Ioi (-δ)) := by
  intro y hy
  rcases lt_or_ge y δ with h | h
  · exact ((contDiffOn_dslope hδ (hf.mono Ioo_subset_Ioi_self)).contDiffAt
      (Ioo_mem_nhds hy h)).contDiffWithinAt
  · have hy0 : y ≠ 0 := by linarith
    have h1 : ContDiffAt ℝ ∞ f y := hf.contDiffAt (Ioi_mem_nhds hy)
    have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => (f x - f 0) / x) y :=
      (h1.sub contDiffAt_const).div contDiffAt_id hy0
    refine (h2.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [isOpen_ne.mem_nhds hy0] with x hx
    rw [dslope_of_ne f hx, slope_def_field, sub_zero]

/-! ### The equation of order four -/

variable {c : ℝ} {G : ℝ → ℝ}

theorem profile_pos (hP : IsProfile c G) {y : ℝ} (hy : 0 ≤ y) : 0 < G y := by
  obtain ⟨κ, hκ, hl⟩ := hP.lower
  exact hκ.trans_le (hl y hy)

/-- Applying `D - 2` to the profile equation:
`(D - 2)(D - 1)(D + 6)(D + 7)(G - 1) = -y³ G′ / (2 G²)`. -/
theorem ode4 (hP : IsProfile c G) {y : ℝ} (hy : 0 < y) :
    y ^ 4 * iteratedDeriv 4 G y + 16 * y ^ 3 * iteratedDeriv 3 G y
      + 42 * y ^ 2 * iteratedDeriv 2 G y - 84 * y * deriv G y + 84 * (G y - 1)
      = -(y ^ 3 * deriv G y / (2 * G y ^ 2)) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have mem : ∀ x : ℝ, 0 < x → x ∈ Ioi (-δ) := fun x hx => mem_Ioi.2 (by linarith)
  have d0 : ∀ x, 0 < x → HasDerivAt G (deriv G x) x := fun x hx => by
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hsm 0 (mem x hx)
    rwa [iteratedDeriv_zero, iteratedDeriv_one] at h
  have d1 : ∀ x, 0 < x → HasDerivAt (deriv G) (iteratedDeriv 2 G x) x := fun x hx => by
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hsm 1 (mem x hx)
    rwa [iteratedDeriv_one] at h
  have d2 : ∀ x, 0 < x → HasDerivAt (iteratedDeriv 2 G) (iteratedDeriv 3 G x) x := fun x hx =>
    hasDerivAt_iteratedDeriv isOpen_Ioi hsm 2 (mem x hx)
  have d3 : ∀ x, 0 < x → HasDerivAt (iteratedDeriv 3 G) (iteratedDeriv 4 G x) x := fun x hx =>
    hasDerivAt_iteratedDeriv isOpen_Ioi hsm 3 (mem x hx)
  have hGy : G y ≠ 0 := (profile_pos hP hy.le).ne'
  have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y :=
    (hasDerivAt_pow 2 y).congr_deriv (by norm_num)
  have p3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * y ^ 2) y :=
    (hasDerivAt_pow 3 y).congr_deriv (by norm_num)
  have p2 : HasDerivAt (fun x : ℝ => 15 * x ^ 2) (30 * y) y :=
    (hp2.const_mul 15).congr_deriv (by ring)
  have p1 : HasDerivAt (fun x : ℝ => 42 * x) 42 y :=
    ((hasDerivAt_id' y).const_mul 42).congr_deriv (by ring)
  have q2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) y y := (hp2.div_const 2).congr_deriv (by ring)
  have t1 := p3.fun_mul (d3 y hy)
  have t2 := p2.fun_mul (d2 y hy)
  have t3 := p1.fun_mul (d1 y hy)
  have t4 := ((d0 y hy).sub_const 1).const_mul 42
  have t5 := q2.fun_mul (((d0 y hy).fun_inv hGy).sub_const c⁻¹)
  have hEd := (((t1.fun_add t2).fun_add t3).fun_sub t4).fun_sub t5
  have hEz : HasDerivAt (fun x : ℝ => x ^ 3 * iteratedDeriv 3 G x
      + 15 * x ^ 2 * iteratedDeriv 2 G x + 42 * x * deriv G x - 42 * (G x - 1)
      - x ^ 2 / 2 * ((G x)⁻¹ - c⁻¹)) 0 y := by
    refine (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with x hx
    have := hP.ode x hx
    linarith
  have h1 := hEd.unique hEz
  have h2 := hP.ode y hy
  linear_combination y * h1 - 2 * h2

/-! ### The function `h` -/

/-- `h(y) = (G(y) - 1) / y`, with the value `G′(0)` at `y = 0`. -/
noncomputable def hfun (G : ℝ → ℝ) : ℝ → ℝ := dslope G 0

theorem hfun_zero (G : ℝ → ℝ) : hfun G 0 = deriv G 0 := dslope_same G 0

theorem mul_hfun (hP : IsProfile c G) (y : ℝ) : y * hfun G y = G y - 1 := by
  have h := sub_smul_dslope G 0 y
  rw [sub_zero, smul_eq_mul, hP.zero] at h
  exact h

theorem one_add_mul_hfun (hP : IsProfile c G) (y : ℝ) : 1 + y * hfun G y = G y := by
  rw [mul_hfun hP y]
  ring

theorem contDiffOn_hfun {δ : ℝ} (hδ : 0 < δ) (hsm : ContDiffOn ℝ ∞ G (Ioi (-δ))) :
    ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ)) :=
  contDiffOn_dslope_Ioi hδ hsm

/-- `y h^{(k+1)} + (k + 1) h^{(k)} = G^{(k+1)}` on the neighbourhood of `[0, ∞)`. -/
theorem hrel (hP : IsProfile c G) {δ : ℝ} (hδ : 0 < δ) (hsm : ContDiffOn ℝ ∞ G (Ioi (-δ))) :
    ∀ k : ℕ, ∀ y ∈ Ioi (-δ), y * iteratedDeriv (k + 1) (hfun G) y
      + ((k : ℝ) + 1) * iteratedDeriv k (hfun G) y = iteratedDeriv (k + 1) G y := by
  have hh := contDiffOn_hfun hδ hsm
  intro k
  induction k with
  | zero =>
    intro y hy
    have h1 : HasDerivAt (fun y => y * iteratedDeriv 0 (hfun G) y)
        (1 * iteratedDeriv 0 (hfun G) y + y * iteratedDeriv (0 + 1) (hfun G) y) y :=
      (hasDerivAt_id' y).fun_mul (hasDerivAt_iteratedDeriv isOpen_Ioi hh 0 hy)
    have h2 : HasDerivAt (fun y => y * iteratedDeriv 0 (hfun G) y)
        (iteratedDeriv (0 + 1) G y) y := by
      have hg := (hasDerivAt_iteratedDeriv isOpen_Ioi hsm 0 hy).sub_const 1
      refine hg.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      simp only [iteratedDeriv_zero]
      exact mul_hfun hP x
    have h3 := h1.unique h2
    rw [Nat.cast_zero]
    linarith
  | succ k ih =>
    intro y hy
    have h := leibniz_step isOpen_Ioi (n := (k : ℝ) + 1) ih
      (fun y hy => hasDerivAt_iteratedDeriv isOpen_Ioi hh (k + 1) hy)
      (fun y hy => hasDerivAt_iteratedDeriv isOpen_Ioi hh k hy)
      (fun y hy => hasDerivAt_iteratedDeriv isOpen_Ioi hsm (k + 1) hy) hy
    rw [Nat.cast_succ]
    exact h

/-- The equation of `h` for `y > 0`. -/
theorem hfun_ode_pos (hP : IsProfile c G) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * iteratedDeriv 4 (hfun G) y + 20 * y * iteratedDeriv 3 (hfun G) y
      + 90 * iteratedDeriv 2 (hfun G) y
      = -((hfun G y + y * deriv (hfun G) y) / (2 * (1 + y * hfun G y) ^ 2)) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hy' : y ∈ Ioi (-δ) := mem_Ioi.2 (by linarith)
  have s4 := hrel hP hδ hsm 3 y hy'
  have s3 := hrel hP hδ hsm 2 y hy'
  have s2 := hrel hP hδ hsm 1 y hy'
  have s1 := hrel hP hδ hsm 0 y hy'
  have s0 := mul_hfun hP y
  have hG := one_add_mul_hfun hP y
  have hode := ode4 hP hy
  simp only [iteratedDeriv_one, iteratedDeriv_zero, zero_add] at s1 s2
  norm_num at s1 s2 s3 s4
  rw [← s4, ← s3, ← s2, ← s1, ← hG] at hode
  have hy3 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy.ne'
  refine mul_left_cancel₀ hy3 ?_
  linear_combination hode

/-- **The equation of `h`** on `[0, ∞)`:
`y² h⁗ + 20 y h‴ + 90 h″ = -(h + y h′) / (2 (1 + y h)²)`. -/
theorem hfun_ode (hP : IsProfile c G) {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 * iteratedDeriv 4 (hfun G) y + 20 * y * iteratedDeriv 3 (hfun G) y
      + 90 * iteratedDeriv 2 (hfun G) y
      = -((hfun G y + y * deriv (hfun G) y) / (2 * (1 + y * hfun G y) ^ 2)) := by
  rcases eq_or_lt_of_le hy with h | h
  · subst h
    obtain ⟨δ, hδ, hsm⟩ := hP.smooth
    have hh := contDiffOn_hfun hδ hsm
    have h0 : (0 : ℝ) ∈ Ioi (-δ) := mem_Ioi.2 (by linarith)
    have c0 : ContinuousAt (hfun G) 0 := by
      have h := (hasDerivAt_iteratedDeriv isOpen_Ioi hh 0 h0).continuousAt
      rwa [iteratedDeriv_zero] at h
    have c1 : ContinuousAt (deriv (hfun G)) 0 := by
      have h := (hasDerivAt_iteratedDeriv isOpen_Ioi hh 1 h0).continuousAt
      rwa [iteratedDeriv_one] at h
    have c2 := (hasDerivAt_iteratedDeriv isOpen_Ioi hh 2 h0).continuousAt
    have c3 := (hasDerivAt_iteratedDeriv isOpen_Ioi hh 3 h0).continuousAt
    have c4 := (hasDerivAt_iteratedDeriv isOpen_Ioi hh 4 h0).continuousAt
    have cid : ContinuousAt (fun y : ℝ => y) 0 := continuousAt_id
    have hcL : ContinuousAt (fun y : ℝ => y ^ 2 * iteratedDeriv 4 (hfun G) y
        + 20 * y * iteratedDeriv 3 (hfun G) y + 90 * iteratedDeriv 2 (hfun G) y) 0 :=
      (((cid.pow 2).mul c4).add ((continuousAt_const.mul cid).mul c3)).add
        (continuousAt_const.mul c2)
    have hden : (2 : ℝ) * (1 + 0 * hfun G 0) ^ 2 ≠ 0 := by norm_num
    have hcR : ContinuousAt (fun y : ℝ => -((hfun G y + y * deriv (hfun G) y)
        / (2 * (1 + y * hfun G y) ^ 2))) 0 :=
      ((c0.add (cid.mul c1)).div
        (continuousAt_const.mul ((continuousAt_const.add (cid.mul c0)).pow 2)) hden).neg
    have t1 := hcL.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have t2 := (hcR.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (hfun_ode_pos hP hy).symm)
    exact tendsto_nhds_unique t1 t2
  · exact hfun_ode_pos hP h

/-! ### The self-similar solution -/

/-- The flat self-similar solution `F(t, x) = ρ⁻¹ h(x/ρ)`, `ρ = √(-t)`. -/
noncomputable def Fss (G : ℝ → ℝ) (t x : ℝ) : ℝ :=
  hfun G (x / Real.sqrt (-t)) / Real.sqrt (-t)

/-- At the concentrating point, `F(t, 0) = G′(0) (-t)^{-1/2}`. -/
theorem Fss_zero (G : ℝ → ℝ) (t : ℝ) : Fss G t 0 = deriv G 0 / Real.sqrt (-t) := by
  unfold Fss
  rw [zero_div, hfun_zero]

theorem one_add_mul_Fss (hP : IsProfile c G) {t : ℝ} (ht : t < 0) (x : ℝ) :
    1 + x * Fss G t x = G (x / Real.sqrt (-t)) := by
  have hρ : Real.sqrt (-t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [← one_add_mul_hfun hP (x / Real.sqrt (-t))]
  unfold Fss
  field_simp

/-- The derivatives in `x`: `∂ₓᵏ F = ρ^{-(k+1)} h^{(k)}(x/ρ)`. -/
theorem iteratedDeriv_Fss {δ : ℝ} (hh : ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ))) {t : ℝ}
    (ht : t < 0) : ∀ (k : ℕ) {x : ℝ}, -δ * Real.sqrt (-t) < x →
      iteratedDeriv k (Fss G t) x
        = iteratedDeriv k (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ (k + 1) := by
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  intro k
  induction k with
  | zero =>
    intro x _
    rw [iteratedDeriv_zero, iteratedDeriv_zero, zero_add, pow_one]
    rfl
  | succ k ih =>
    intro x hx
    have hy : x / Real.sqrt (-t) ∈ Ioi (-δ) := by
      rw [mem_Ioi, lt_div_iff₀ hρ]
      exact hx
    have he : iteratedDeriv k (Fss G t) =ᶠ[𝓝 x] fun x =>
        iteratedDeriv k (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ (k + 1) := by
      filter_upwards [Ioi_mem_nhds hx] with u hu using ih hu
    have hdiv : HasDerivAt (fun x : ℝ => x / Real.sqrt (-t)) (1 / Real.sqrt (-t)) x :=
      (hasDerivAt_id' x).div_const _
    have hd : HasDerivAt (fun x : ℝ =>
        iteratedDeriv k (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ (k + 1))
        (iteratedDeriv (k + 1) (hfun G) (x / Real.sqrt (-t)) * (1 / Real.sqrt (-t))
          / Real.sqrt (-t) ^ (k + 1)) x :=
      ((hasDerivAt_iteratedDeriv isOpen_Ioi hh k hy).comp x hdiv).div_const
        (Real.sqrt (-t) ^ (k + 1))
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv]
    ring

/-- The derivative in `t`. -/
theorem hasDerivAt_Fss_time {δ : ℝ} (hh : ContDiffOn ℝ ∞ (hfun G) (Ioi (-δ))) {t x : ℝ}
    (ht : t < 0) (hx : -δ * Real.sqrt (-t) < x) :
    HasDerivAt (fun τ => Fss G τ x)
      ((hfun G (x / Real.sqrt (-t)) + x / Real.sqrt (-t) * deriv (hfun G) (x / Real.sqrt (-t)))
        / (2 * Real.sqrt (-t) ^ 3)) t := by
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hρ0 := hρ.ne'
  have hy : x / Real.sqrt (-t) ∈ Ioi (-δ) := by
    rw [mem_Ioi, lt_div_iff₀ hρ]
    exact hx
  have hr : HasDerivAt (fun τ : ℝ => Real.sqrt (-τ)) (1 / (2 * Real.sqrt (-t)) * -1) t :=
    (Real.hasDerivAt_sqrt (by linarith : -t ≠ 0)).comp t (hasDerivAt_id' t).neg
  have hq : HasDerivAt (fun τ : ℝ => x / Real.sqrt (-τ))
      ((0 * Real.sqrt (-t) - x * (1 / (2 * Real.sqrt (-t)) * -1)) / Real.sqrt (-t) ^ 2) t :=
    (hasDerivAt_const t x).fun_div hr hρ0
  have h0 : HasDerivAt (hfun G) (deriv (hfun G) (x / Real.sqrt (-t))) (x / Real.sqrt (-t)) := by
    have h := hasDerivAt_iteratedDeriv isOpen_Ioi hh 0 hy
    rwa [iteratedDeriv_zero, iteratedDeriv_one] at h
  have hc : HasDerivAt (fun τ : ℝ => hfun G (x / Real.sqrt (-τ)))
      (deriv (hfun G) (x / Real.sqrt (-t))
        * ((0 * Real.sqrt (-t) - x * (1 / (2 * Real.sqrt (-t)) * -1)) / Real.sqrt (-t) ^ 2)) t :=
    h0.comp t hq
  have hF := hc.fun_div hr hρ0
  refine hF.congr_deriv ?_
  field_simp
  ring

/-- **The flat equation** for the self-similar solution, for `t < 0` and
`x ≥ 0`, including `x = 0`. -/
theorem flat_equation (hP : IsProfile c G) {t x : ℝ} (ht : t < 0) (hx : 0 ≤ x) :
    deriv (fun τ => Fss G τ x) t + (1 + x * Fss G t x) ^ 2
      * (x ^ 2 * iteratedDeriv 4 (Fss G t) x + 20 * x * iteratedDeriv 3 (Fss G t) x
        + 90 * iteratedDeriv 2 (Fss G t) x) = 0 := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hρ0 := hρ.ne'
  have hx' : -δ * Real.sqrt (-t) < x := by
    have := mul_pos hδ hρ
    linarith
  have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx hρ.le
  have hstar := hfun_ode hP hy
  have hGpos : 0 < 1 + x / Real.sqrt (-t) * hfun G (x / Real.sqrt (-t)) := by
    rw [one_add_mul_hfun hP]
    exact profile_pos hP hy
  have i4 : iteratedDeriv 4 (Fss G t) x
      = iteratedDeriv 4 (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 5 :=
    iteratedDeriv_Fss hh ht 4 hx'
  have i3 : iteratedDeriv 3 (Fss G t) x
      = iteratedDeriv 3 (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 4 :=
    iteratedDeriv_Fss hh ht 3 hx'
  have i2 : iteratedDeriv 2 (Fss G t) x
      = iteratedDeriv 2 (hfun G) (x / Real.sqrt (-t)) / Real.sqrt (-t) ^ 3 :=
    iteratedDeriv_Fss hh ht 2 hx'
  have e0 : Fss G t x = hfun G (x / Real.sqrt (-t)) / Real.sqrt (-t) := rfl
  rw [(hasDerivAt_Fss_time hh ht hx').deriv, i4, i3, i2, e0]
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = x / Real.sqrt (-t) := ⟨_, rfl⟩
  have hxy : x = Real.sqrt (-t) * y := by
    rw [hy_def]
    field_simp
  rw [← hy_def] at hstar hGpos ⊢
  rw [hxy]
  generalize iteratedDeriv 4 (hfun G) y = h4 at hstar ⊢
  generalize iteratedDeriv 3 (hfun G) y = h3 at hstar ⊢
  generalize iteratedDeriv 2 (hfun G) y = h2 at hstar ⊢
  generalize deriv (hfun G) y = h1 at hstar ⊢
  generalize hfun G y = h0 at hstar hGpos ⊢
  generalize Real.sqrt (-t) = ρ at hρ hρ0 ⊢
  have hne := hGpos.ne'
  have e : 1 + ρ * y * (h0 / ρ) = 1 + y * h0 := by field_simp
  have e1 : (ρ * y) ^ 2 * (h4 / ρ ^ 5) + 20 * (ρ * y) * (h3 / ρ ^ 4) + 90 * (h2 / ρ ^ 3)
      = (y ^ 2 * h4 + 20 * y * h3 + 90 * h2) / ρ ^ 3 := by
    field_simp
  rw [e, e1, hstar]
  generalize 1 + y * h0 = C at hne
  generalize h0 + y * h1 = B
  field_simp
  ring

end Calabi.Flat
