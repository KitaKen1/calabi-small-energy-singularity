import Calabi.Correction.CutoffOsc

/-!
# The residual and the inner mismatch in the momentum coordinate

The remaining assertions of Lemma 6.2 of the manuscript, in the calculus of
`Osc.lean` and uniformly in the cut-off radius `λ` and the time
`T ≤ min(λ², 1)`. Write `Â f = x² f⁗ + 20 x f‴ + 90 f″` for the flat operator
(`Δ²/16` on radial functions of `x = |z|²`, `z ∈ ℝ¹⁸`), `G_ρ = G(x/ρ)`,
`b̂ = 1 + v∗ F` and `b_λ = 1 + v∗ F_λ`.

* `uosc_AhatF`, `uosc_AdiffF`: `Â F` has order `-3` and `(A - Â) F` order `-2`;
* `deriv_Fss_time`: the flat equation `F_t = -G_ρ² Â F`;
* `uosc_blam`, `uosc_bhat`, `uosc_bhat_sub`: `b_λ`, `b̂` have order `0`, and
  `b̂ - G_ρ = -x² F` order `1`;
* `uosc_Elam`: the residual `E_λ = (F_λ)_t + b_λ² A F_λ` has order `-3`;
  `uosc_Ein`, `Elam_eq_Ein`: for `x < λ` it equals a function of order `-2`
  (the first line of (6.6), from the cancellation in the flat equation);
  `Elam_eq_zero`: it vanishes for `x > 2λ`;
* `uosc_Pmis`, `uosc_cmis`: the mismatch of the principal coefficient
  `b̂² (1 - x)² - G_ρ²` has order `1`, and that of the zeroth-order coefficient
  `2 v∗ b̂ A F - 2 x G_ρ Â F` order `-1`;
* `two_x_G_AhatF`: `2 x G_ρ Â F = -(−t)⁻¹ y G′(y)/G(y)`, the potential of the
  flat linearized operator.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Osc

open Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-! ### The flat operator on the self-similar solution -/

/-- `Â F = x² F⁗ + 20 x F‴ + 90 F″`. -/
noncomputable def AhatF (G : ℝ → ℝ) (t x : ℝ) : ℝ :=
  x ^ 2 * iteratedDeriv 4 (Fss G t) x + 20 * x * iteratedDeriv 3 (Fss G t) x
    + 90 * iteratedDeriv 2 (Fss G t) x

/-- `(A - Â) F`. -/
noncomputable def AdiffF (G : ℝ → ℝ) (t x : ℝ) : ℝ :=
  x ^ 3 * (x - 2) * iteratedDeriv 4 (Fss G t) x
    + x ^ 2 * (-48 + 28 * x) * iteratedDeriv 3 (Fss G t) x
    + x * (-300 + 222 * x) * iteratedDeriv 2 (Fss G t) x
    + (-360 + 480 * x) * iteratedDeriv 1 (Fss G t) x + 180 * Fss G t x

theorem uosc_AhatF (hP : IsProfile c G) : UOsc (-3) (fun _ t x => AhatF G t x) := by
  have t4 : UOsc (-3) _ := ((uosc_Fss hP 4).term 2 1 0 0 0 0).cast (by norm_num)
  have t3 : UOsc (-3) _ := ((uosc_Fss hP 3).term 1 20 0 0 0 0).cast (by norm_num)
  have t2 : UOsc (-3) _ := ((uosc_Fss hP 2).term 0 90 0 0 0 0).cast (by norm_num)
  refine ((t4.add t3).add t2).congr fun lam _ t _ x _ => ?_
  unfold AhatF pol
  ring

theorem uosc_AdiffF (hP : IsProfile c G) : UOsc (-2) (fun _ t x => AdiffF G t x) := by
  have t4 : UOsc (-2) _ := ((uosc_Fss hP 4).term 3 (-2) 1 0 0 0).cast (by norm_num)
  have t3 : UOsc (-2) _ := ((uosc_Fss hP 3).term 2 (-48) 28 0 0 0).cast (by norm_num)
  have t2 : UOsc (-2) _ := ((uosc_Fss hP 2).term 1 (-300) 222 0 0 0).cast (by norm_num)
  have t1 : UOsc (-2) _ := ((uosc_Fss hP 1).term 0 (-360) 480 0 0 0).cast (by norm_num)
  have t0 : UOsc (-2) _ := (((uosc_Fss hP 0).term 0 180 0 0 0 0).lower 1).cast (by norm_num)
  refine ((((t4.add t3).add t2).add t1).add t0).congr fun lam _ t _ x _ => ?_
  unfold AdiffF pol
  rw [iteratedDeriv_zero]
  ring

/-- The derivatives of the self-similar solution on `[0, 1]`. -/
theorem D_Fss (hP : IsProfile c G) {t : ℝ} (ht : t < 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, D (Fss G t) x = iteratedDeriv 1 (Fss G t) x ∧
      D (D (Fss G t)) x = iteratedDeriv 2 (Fss G t) x ∧
      D (D (D (Fss G t))) x = iteratedDeriv 3 (Fss G t) x ∧
      D (D (D (D (Fss G t)))) x = iteratedDeriv 4 (Fss G t) x := by
  obtain ⟨C0, hC0, htow⟩ := tower_Fss hP 5
  have h : ∀ x ∈ Icc (0 : ℝ) 1,
      D (fun x => iteratedDeriv 0 (Fss G t) x) x = iteratedDeriv 1 (Fss G t) x ∧
      D (D (fun x => iteratedDeriv 0 (Fss G t) x)) x = iteratedDeriv 2 (Fss G t) x ∧
      D (D (D (fun x => iteratedDeriv 0 (Fss G t) x))) x = iteratedDeriv 3 (Fss G t) x ∧
      D (D (D (D (fun x => iteratedDeriv 0 (Fss G t) x)))) x = iteratedDeriv 4 (Fss G t) x :=
    (htow 1).D_eq (by norm_num) ht
  have e0 : (fun x => iteratedDeriv 0 (Fss G t) x) = Fss G t := by
    funext x
    rw [iteratedDeriv_zero]
  rw [e0] at h
  exact h

theorem contDiffOn_Fss_Icc (hP : IsProfile c G) {t : ℝ} (ht : t < 0) :
    ContDiffOn ℝ ∞ (Fss G t) (Icc 0 1) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  exact (contDiffOn_Fss hh ht).mono fun y hy => by
    rw [mem_Ioi]
    nlinarith [hy.1]

/-- `A F = Â F + (A - Â) F` on `[0, 1]`. -/
theorem Aop_Fss_eq (hP : IsProfile c G) {t : ℝ} (ht : t < 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Aop (Fss G t) x = AhatF G t x + AdiffF G t x := by
  obtain ⟨d1, d2, d3, d4⟩ := D_Fss hP ht x hx
  rw [Aop_eq (contDiffOn_Fss_Icc hP ht) hx, d1, d2, d3, d4]
  unfold AhatF AdiffF
  ring

/-- **The flat equation**: `F_t = -G(x/ρ)² Â F`. -/
theorem deriv_Fss_time (hP : IsProfile c G) {t x : ℝ} (ht : t < 0) (hx : 0 ≤ x) :
    deriv (fun τ => Fss G τ x) t = -(G (x / Real.sqrt (-t)) ^ 2 * AhatF G t x) := by
  have h := flat_equation hP ht hx
  rw [one_add_mul_Fss hP ht x] at h
  unfold AhatF
  linarith

/-! ### The multipliers -/

theorem uosc_Flam (hP : IsProfile c G) : UOsc (-1) (fun lam t x => Flam G lam t x) :=
  ((uosc_flamJet hP 0).cast (by norm_num)).congr fun lam _ t _ x _ =>
    (flamJet_zero G lam t x).symm

theorem uosc_Fss0 (hP : IsProfile c G) : UOsc (-1) (fun _ t x => Fss G t x) :=
  ((uosc_Fss hP 0).cast (by norm_num)).congr fun lam _ t _ x _ => by
    rw [iteratedDeriv_zero]

/-- `b_λ = 1 + v∗ F_λ` has order zero. -/
theorem uosc_blam (hP : IsProfile c G) :
    UOsc 0 (fun lam t x => 1 + vstar x * Flam G lam t x) := by
  have h1 : UOsc 0 _ := ((uosc_Flam hP).term 1 1 (-1) 0 0 0).cast (by norm_num)
  refine (uosc_one.add h1).congr fun lam _ t _ x _ => ?_
  unfold vstar pol
  ring

/-- `b̂ = 1 + v∗ F` has order zero. -/
theorem uosc_bhat (hP : IsProfile c G) : UOsc 0 (fun _ t x => 1 + vstar x * Fss G t x) := by
  have h1 : UOsc 0 _ := ((uosc_Fss0 hP).term 1 1 (-1) 0 0 0).cast (by norm_num)
  refine (uosc_one.add h1).congr fun lam _ t _ x _ => ?_
  unfold vstar pol
  ring

/-- `b̂ - G(x/ρ) = -x² F` has order one. -/
theorem uosc_bhat_sub (hP : IsProfile c G) :
    UOsc 1 (fun _ t x => 1 + vstar x * Fss G t x - G (x / Real.sqrt (-t))) := by
  have h1 : UOsc 1 _ := ((uosc_Fss0 hP).term 2 (-1) 0 0 0 0).cast (by norm_num)
  refine h1.congr fun lam _ t ht x _ => ?_
  rw [← one_add_mul_Fss hP ht x]
  unfold vstar pol
  ring

/-- The cut-off itself. -/
theorem uosc_chi : UOsc 0 (fun lam _ x => chi (x / lam)) := by
  have h : UOsc ((0 : ℤ) - ((0 : ℕ) : ℤ))
      (fun lam => (fun j (_ : ℝ) x => iteratedDeriv j chi (x / lam) / lam ^ j) 0) :=
    UOsc.of_tower (c := fun lam j _ x => iteratedDeriv j chi (x / lam) / lam ^ j)
      (d := fun _ _ _ _ => 0) (tower_chi 1) zero_lt_one
  refine (h.cast (by norm_num)).congr fun lam _ t _ x _ => ?_
  show chi (x / lam) = iteratedDeriv 0 chi (x / lam) / lam ^ 0
  rw [iteratedDeriv_zero, pow_zero, div_one]

/-! ### The residual -/

/-- The residual `E_λ = (F_λ)_t + b_λ² A F_λ` of the localized profile. -/
noncomputable def Elam (G : ℝ → ℝ) (lam t x : ℝ) : ℝ :=
  deriv (fun τ => Flam G lam τ x) t + (1 + vstar x * Flam G lam t x) ^ 2 * Aop (Flam G lam t) x

/-- The inner form of the residual: `(b̂² - G_ρ²) Â F + b̂² (A - Â) F`. -/
noncomputable def Ein (G : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ((1 + vstar x * Fss G t x) ^ 2 - G (x / Real.sqrt (-t)) ^ 2) * AhatF G t x
    + (1 + vstar x * Fss G t x) ^ 2 * AdiffF G t x

theorem Elam_eq (hP : IsProfile c G) (lam : ℝ) {t x : ℝ} (ht : t < 0) (hx : 0 ≤ x) :
    Elam G lam t x = -(chi (x / lam) * (G (x / Real.sqrt (-t)) ^ 2 * AhatF G t x))
      + (1 + vstar x * Flam G lam t x) ^ 2 * Aop (Flam G lam t) x := by
  unfold Elam
  congr 1
  have e : (fun τ => Flam G lam τ x) = fun τ => chi (x / lam) * Fss G τ x := rfl
  rw [e, deriv_const_mul_field, deriv_Fss_time hP ht hx]
  ring

/-- **The residual has order `-3`** (the second line of (6.6)). -/
theorem uosc_Elam (hP : IsProfile c G) : UOsc (-3) (fun lam t x => Elam G lam t x) := by
  have hG2 : UOsc 0 _ := ((uosc_G hP).mul (uosc_G hP)).cast (by norm_num)
  have h1 : UOsc (-3) _ := ((uosc_chi.mul (hG2.mul (uosc_AhatF hP))).neg).cast (by norm_num)
  have hb2 : UOsc 0 _ := ((uosc_blam hP).mul (uosc_blam hP)).cast (by norm_num)
  have h2 : UOsc (-3) _ := (hb2.mul (uosc_AFlam hP)).cast (by norm_num)
  refine (h1.add h2).congr fun lam _ t ht x hx => ?_
  rw [Elam_eq hP lam ht hx.1]
  ring

/-- **The inner form of the residual has order `-2`** (the first line of
(6.6)). -/
theorem uosc_Ein (hP : IsProfile c G) : UOsc (-2) (fun _ t x => Ein G t x) := by
  have hsum : UOsc 0 (fun (_ : ℝ) t x => 1 + vstar x * Fss G t x + G (x / Real.sqrt (-t))) :=
    (uosc_bhat hP).add (uosc_G hP)
  have h1 : UOsc (-2) _ :=
    (((uosc_bhat_sub hP).mul hsum).mul (uosc_AhatF hP)).cast (by norm_num)
  have hb2 : UOsc 0 _ := ((uosc_bhat hP).mul (uosc_bhat hP)).cast (by norm_num)
  have h2 : UOsc (-2) _ := (hb2.mul (uosc_AdiffF hP)).cast (by norm_num)
  refine (h1.add h2).congr fun lam _ t _ x _ => ?_
  unfold Ein
  ring

/-- For `x < λ` the Leibniz sums are the derivatives of `F`. -/
theorem flamJet_of_lt {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (t : ℝ) {x : ℝ} (hx : x < lam) :
    flamJet G lam k t x = iteratedDeriv k (Fss G t) x := by
  have hx1 : x / lam < 1 := (div_lt_one hlam).2 hx
  show ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
    * (iteratedDeriv i chi (x / lam) / lam ^ i * iteratedDeriv (k - i) (Fss G t) x) = _
  rw [Finset.sum_eq_single 0]
  · rw [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, pow_zero, div_one,
      chi_of_le hx1.le, one_mul, Nat.sub_zero]
  · intro i _ hi
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [iteratedDeriv_succ_chi_eq_zero i' (Or.inl hx1)]
    ring
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h

/-- For `x > 2λ` the Leibniz sums vanish. -/
theorem flamJet_of_gt {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (t : ℝ) {x : ℝ} (hx : 2 * lam < x) :
    flamJet G lam k t x = 0 := by
  have hx2 : 2 < x / lam := (lt_div_iff₀ hlam).2 hx
  show ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
    * (iteratedDeriv i chi (x / lam) / lam ^ i * iteratedDeriv (k - i) (Fss G t) x) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, chi_of_ge hx2.le]
    ring
  | succ i =>
    rw [iteratedDeriv_succ_chi_eq_zero i (Or.inr hx2)]
    ring

/-- **For `x < λ` the residual is its inner form.** -/
theorem Elam_eq_Ein (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : x < lam) : Elam G lam t x = Ein G t x := by
  obtain ⟨d1, d2, d3, d4⟩ := D_Flam hP hlam ht x hx
  have hF : Flam G lam t x = Fss G t x := by
    rw [← flamJet_zero, flamJet_of_lt hlam 0 t hxl, iteratedDeriv_zero]
  have hA : Aop (Flam G lam t) x = AhatF G t x + AdiffF G t x := by
    rw [Aop_eq (contDiffOn_Flam_Icc hP lam ht) hx, d1, d2, d3, d4, flamJet_of_lt hlam 1 t hxl,
      flamJet_of_lt hlam 2 t hxl, flamJet_of_lt hlam 3 t hxl, flamJet_of_lt hlam 4 t hxl, hF]
    unfold AhatF AdiffF
    ring
  rw [Elam_eq hP lam ht hx.1, hA, hF, chi_of_le ((div_lt_one hlam).2 hxl).le]
  unfold Ein
  ring

/-- **For `x > 2λ` the residual vanishes.** -/
theorem Elam_eq_zero (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : 2 * lam < x) : Elam G lam t x = 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := D_Flam hP hlam ht x hx
  have hF : Flam G lam t x = 0 := by
    rw [← flamJet_zero, flamJet_of_gt hlam 0 t hxl]
  have hA : Aop (Flam G lam t) x = 0 := by
    rw [Aop_eq (contDiffOn_Flam_Icc hP lam ht) hx, d1, d2, d3, d4, flamJet_of_gt hlam 1 t hxl,
      flamJet_of_gt hlam 2 t hxl, flamJet_of_gt hlam 3 t hxl, flamJet_of_gt hlam 4 t hxl, hF]
    ring
  rw [Elam_eq hP lam ht hx.1, hA, chi_of_ge ((le_div_iff₀ hlam).2 hxl.le)]
  ring

/-! ### The mismatch with the flat operator -/

/-- **The mismatch of the principal coefficient** `b̂² (1 - x)² - G_ρ²` has
order one. -/
theorem uosc_Pmis (hP : IsProfile c G) :
    UOsc 1 (fun _ t x => (1 + vstar x * Fss G t x) ^ 2 * (1 - x) ^ 2
      - G (x / Real.sqrt (-t)) ^ 2) := by
  -- `(1 - x) b̂ - G = (b̂ - G) - x b̂` and `(1 - x) b̂ + G`
  have hxb : UOsc 1 (fun (_ : ℝ) t x => x ^ 1 * pol 1 0 0 0 0 x * (1 + vstar x * Fss G t x)) :=
    ((uosc_bhat hP).term 1 1 0 0 0 0).cast (by norm_num)
  have hd : UOsc 1 _ := (uosc_bhat_sub hP).sub hxb
  have hb1 : UOsc 0 (fun (_ : ℝ) t x => x ^ 0 * pol 1 (-1) 0 0 0 x * (1 + vstar x * Fss G t x)) :=
    ((uosc_bhat hP).term 0 1 (-1) 0 0 0).cast (by norm_num)
  have hs : UOsc 0 _ := hb1.add (uosc_G hP)
  refine ((hd.mul hs).cast (by norm_num)).congr fun lam _ t _ x _ => ?_
  unfold pol
  ring

/-- **The mismatch of the zeroth-order coefficient**
`2 v∗ b̂ A F - 2 x G_ρ Â F` has order `-1`. -/
theorem uosc_cmis (hP : IsProfile c G) :
    UOsc (-1) (fun _ t x => 2 * vstar x * (1 + vstar x * Fss G t x) * Aop (Fss G t) x
      - 2 * x * G (x / Real.sqrt (-t)) * AhatF G t x) := by
  have hxb : UOsc 1 (fun (_ : ℝ) t x => x ^ 1 * pol 1 0 0 0 0 x * (1 + vstar x * Fss G t x)) :=
    ((uosc_bhat hP).term 1 1 0 0 0 0).cast (by norm_num)
  have hd : UOsc 1 _ := (uosc_bhat_sub hP).sub hxb
  -- `A F` has order `-3`
  have hAF : UOsc (-3) (fun (_ : ℝ) t x => AhatF G t x + AdiffF G t x) :=
    (uosc_AhatF hP).add (((uosc_AdiffF hP).lower 1).cast (by norm_num))
  have h1 : UOsc (-1) _ := (((hd.mul hAF).term 1 2 0 0 0 0)).cast (by norm_num)
  have h2 : UOsc (-1) _ :=
    ((((uosc_G hP).mul (uosc_AdiffF hP)).term 1 2 0 0 0 0)).cast (by norm_num)
  refine (h1.add h2).congr fun lam _ t ht x hx => ?_
  rw [Aop_Fss_eq hP ht hx]
  unfold vstar pol
  ring

/-- **The potential of the flat linearized operator**:
`2 x G_ρ Â F = -(−t)⁻¹ y G′(y)/G(y)` with `y = x/ρ`. -/
theorem two_x_G_AhatF (hP : IsProfile c G) {t x : ℝ} (ht : t < 0) (hx : 0 ≤ x) :
    2 * x * G (x / Real.sqrt (-t)) * AhatF G t x
      = -(-t)⁻¹ * (x / Real.sqrt (-t) * deriv G (x / Real.sqrt (-t))
        / G (x / Real.sqrt (-t))) := by
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx hρ.le
  have hGpos : 0 < G (x / Real.sqrt (-t)) := profile_pos hP hy
  have hsq : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt (by linarith)
  -- the time derivative in two ways
  have h1 := deriv_Fss_time hP ht hx
  have h2 : HasDerivAt (fun τ => Fss G τ x)
      (deriv G (x / Real.sqrt (-t)) / (2 * Real.sqrt (-t) ^ 3)) t := by
    obtain ⟨δ, hδ, hsm⟩ := hP.smooth
    have hh := contDiffOn_hfun hδ hsm
    have hxδ : -δ * Real.sqrt (-t) < x := by nlinarith
    have hymem : x / Real.sqrt (-t) ∈ Ioi (-δ) := by
      rw [mem_Ioi]
      linarith
    have h3 := hasDerivAt_Fss_time hh ht hxδ
    have h4 := hrel hP hδ hsm 0 _ hymem
    rw [iteratedDeriv_zero, zero_add, iteratedDeriv_one, iteratedDeriv_one, Nat.cast_zero,
      zero_add, one_mul] at h4
    refine h3.congr_deriv ?_
    rw [← h4]
    ring
  rw [h2.deriv] at h1
  have hne : G (x / Real.sqrt (-t)) ≠ 0 := hGpos.ne'
  have hρ0 := hρ.ne'
  have e3 : Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * (-t) := by
    calc Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * Real.sqrt (-t) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) := by rw [hsq]
  have ht0 : (-t) ≠ 0 := by linarith
  -- solve for `Â F`
  have h5 : AhatF G t x = -(deriv G (x / Real.sqrt (-t)) / (2 * Real.sqrt (-t) ^ 3))
      / G (x / Real.sqrt (-t)) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hne)]
    linarith
  rw [h5, e3]
  field_simp

/-! ### The multiplier -/

/-- **The multiplier `b_λ = 1 + v∗ F_λ` lies between the bounds of the
profile**, (6.1) of the manuscript: it is a convex combination of `1` and
`G(x/ρ)`. -/
theorem blam_mem (hP : IsProfile c G) {κ Mu lam t x : ℝ} (hκ : ∀ y : ℝ, 0 ≤ y → κ ≤ G y)
    (hMu : ∀ y : ℝ, 0 ≤ y → G y ≤ Mu) (ht : t < 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    min 1 κ ≤ 1 + vstar x * Flam G lam t x ∧ 1 + vstar x * Flam G lam t x ≤ max 1 Mu := by
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  have hy : 0 ≤ x / Real.sqrt (-t) := div_nonneg hx.1 hρ.le
  have hG := one_add_mul_Fss hP ht x
  have hθ0 : 0 ≤ (1 - x) * chi (x / lam) := mul_nonneg (by linarith [hx.2]) (chi_nonneg _)
  have hθ1 : (1 - x) * chi (x / lam) ≤ 1 := by
    calc (1 - x) * chi (x / lam) ≤ 1 * 1 :=
          mul_le_mul (by linarith [hx.1]) (chi_le_one _) (chi_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have e : 1 + vstar x * Flam G lam t x
      = (1 - (1 - x) * chi (x / lam)) * 1
        + (1 - x) * chi (x / lam) * G (x / Real.sqrt (-t)) := by
    rw [← hG]
    unfold vstar Flam
    ring
  rw [e]
  have h1 := hκ _ hy
  have h2 := hMu _ hy
  constructor
  · have hm1 : min 1 κ ≤ 1 := min_le_left _ _
    have hm2 : min 1 κ ≤ G (x / Real.sqrt (-t)) := (min_le_right _ _).trans h1
    nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hm2),
      mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hm1)]
  · have hm1 : (1 : ℝ) ≤ max 1 Mu := le_max_left _ _
    have hm2 : G (x / Real.sqrt (-t)) ≤ max 1 Mu := h2.trans (le_max_right _ _)
    nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hm2),
      mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hm1)]

end Calabi.Osc
