import Calabi.Infinity.Decay
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Smoothness at infinity in the variable `σ = s⁻³`

`iota σ = σ^{-1/3}` inverts `s ↦ s⁻³` on the positive half-line and
`d/dσ U(iota σ) = -(1/3) (s⁴ U′)(iota σ)`. If `U` and its first `m + 1`
derivatives are `O(s^a)` with `a + 4m + 6 ≤ 0`, then every function of the
chain `U, s⁴ U′, s⁴ (s⁴ U′)′, …` up to the order `m` is `O(σ²)` in the variable
`σ`, so `σ ↦ U(iota σ)` extended by zero to `σ ≤ 0` is `C^m` (`contDiffOn_ext`).

Applied to the remainder of high order of the expansion at infinity this gives
the smoothness of `σ ↦ p(σ^{-1/3})` on `[0, ∞)` (`contDiffOn_ext_profile`).
-/

open Polynomial Set Filter
open scoped Topology ContDiff

namespace Calabi.Infinity

open Calabi.Shot (State pfield Ntr Ntr_of_ge)

/-! ### The inverse of `s ↦ s⁻³` -/

/-- `σ ↦ σ^{-1/3}`. -/
noncomputable def iota (σ : ℝ) : ℝ := σ ^ (-(1 / 3) : ℝ)

theorem iota_pos {σ : ℝ} (hσ : 0 < σ) : 0 < iota σ := Real.rpow_pos_of_pos hσ _

theorem iota_pow_three {σ : ℝ} (hσ : 0 < σ) : iota σ ^ 3 = σ⁻¹ := by
  have e : (-(1 / 3) : ℝ) * ((3 : ℕ) : ℝ) = -1 := by norm_num
  unfold iota
  rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le, e, Real.rpow_neg_one]

theorem iota_zpow {σ : ℝ} (hσ : 0 < σ) : iota σ ^ (-3 : ℤ) = σ := by
  rw [sigma_eq, iota_pow_three hσ, inv_inv]

theorem hasDerivAt_iota {σ : ℝ} (hσ : 0 < σ) : HasDerivAt iota (-(1 / 3) * iota σ ^ 4) σ := by
  have h := Real.hasDerivAt_rpow_const (x := σ) (p := -(1 / 3)) (Or.inl hσ.ne')
  refine h.congr_deriv ?_
  have e : (-(1 / 3) : ℝ) * ((4 : ℕ) : ℝ) = -(1 / 3) - 1 := by norm_num
  unfold iota
  rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le, e]

theorem contDiffAt_iota {σ : ℝ} (hσ : 0 < σ) (n : WithTop ℕ∞) : ContDiffAt ℝ n iota σ :=
  Real.contDiffAt_rpow_const_of_ne hσ.ne'

theorem lt_iota {S σ : ℝ} (hσ : 0 < σ) (h : σ < (S ^ 3)⁻¹) : S < iota σ := by
  by_contra hcon
  have h1 : iota σ ≤ S := not_lt.1 hcon
  have h2 : iota σ ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (iota_pos hσ).le h1 3
  rw [iota_pow_three hσ] at h2
  have h3 := inv_anti₀ (inv_pos.2 hσ) h2
  rw [inv_inv] at h3
  linarith

/-! ### Extension by zero -/

/-- A function of `s` as a function of `σ = s⁻³`, extended by zero to `σ ≤ 0`. -/
noncomputable def ext (U : ℝ → ℝ) (σ : ℝ) : ℝ := if 0 < σ then U (iota σ) else 0

theorem ext_of_pos (U : ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) : ext U σ = U (iota σ) := ite_eq_left hσ

theorem ext_of_nonpos (U : ℝ → ℝ) {σ : ℝ} (hσ : σ ≤ 0) : ext U σ = 0 := ite_eq_right (not_lt.2 hσ)

theorem abs_ext_le {S : ℝ} (hS : 0 < S) {a : ℤ} (ha : a ≤ -6) {U : ℝ → ℝ} (hU : Bd0 S a U) :
    ∃ C, 0 ≤ C ∧ ∀ σ, σ < (S ^ 3)⁻¹ → |ext U σ| ≤ C * σ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hU
  refine ⟨C * S ^ (a - (-6)), mul_nonneg hC (zpow_pos hS _).le, fun σ hσ => ?_⟩
  rcases lt_or_ge 0 σ with h0 | h0
  · have hs := lt_iota h0 hσ
    have h1 := hb _ hs
    have h2 := zpow_le_of_le hS ha hs
    have h3 : iota σ ^ (-6 : ℤ) = σ ^ 2 := by
      have e : (-6 : ℤ) = (-3) * 2 := by norm_num
      rw [e, zpow_mul, iota_zpow h0]
      exact zpow_ofNat σ 2
    rw [h3] at h2
    rw [ext_of_pos U h0]
    calc |U (iota σ)| ≤ C * iota σ ^ a := h1
      _ ≤ C * (S ^ (a - (-6)) * σ ^ 2) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * S ^ (a - (-6)) * σ ^ 2 := by ring
  · rw [ext_of_nonpos U h0, abs_zero]
    exact mul_nonneg (mul_nonneg hC (zpow_pos hS _).le) (sq_nonneg σ)

/-- A function that is `O(x²)` at the origin has derivative zero there. -/
theorem hasDerivAt_zero_of_sq_le {f : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ) (h0 : f 0 = 0)
    (h : ∀ x, |x| < δ → |f x| ≤ C * x ^ 2) : HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  have hg : Tendsto (fun x : ℝ => |C| * |x|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => |C| * |x| := by fun_prop
    have ht := hc.tendsto 0
    rwa [abs_zero, mul_zero] at ht
  refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hg
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with x hx
  rw [mem_ball_zero_iff, Real.norm_eq_abs] at hx
  have hx' := h x hx
  simp only [sub_zero, h0, smul_zero, Real.norm_eq_abs]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [h0]
  · rw [inv_mul_le_iff₀ (abs_pos.2 hx0)]
    calc |f x| ≤ C * x ^ 2 := hx'
      _ ≤ |C| * x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg x)
      _ = |x| * (|C| * |x|) := by
        rw [← sq_abs]
        ring

/-- The derivative of the extension, at every point of `(-∞, S⁻³)`. -/
theorem hasDerivAt_ext {S : ℝ} (hS : 0 < S) {a : ℤ} (ha : a ≤ -6) {U U' : ℝ → ℝ}
    (hU : Bd0 S a U) (hd : ∀ s, S < s → HasDerivAt U (U' s) s) {σ : ℝ} (hσ : σ < (S ^ 3)⁻¹) :
    HasDerivAt (ext U) (ext (fun s => -(1 / 3) * s ^ 4 * U' s) σ) σ := by
  rcases lt_trichotomy σ 0 with h | h | h
  · rw [ext_of_nonpos _ h.le]
    refine (hasDerivAt_const σ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with x hx
    exact ext_of_nonpos U (le_of_lt hx)
  · subst h
    rw [ext_of_nonpos _ le_rfl]
    obtain ⟨C, -, hC⟩ := abs_ext_le hS ha hU
    have hpos : (0 : ℝ) < (S ^ 3)⁻¹ := inv_pos.2 (pow_pos hS 3)
    exact hasDerivAt_zero_of_sq_le hpos (ext_of_nonpos U le_rfl) fun x hx =>
      hC x (lt_of_abs_lt hx)
  · have hs := lt_iota h hσ
    have e : ext (fun s => -(1 / 3) * s ^ 4 * U' s) σ =
        U' (iota σ) * (-(1 / 3) * iota σ ^ 4) := by
      rw [ext_of_pos _ h]
      ring
    rw [e]
    have hc := (hd _ hs).comp σ (hasDerivAt_iota h)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact ext_of_pos U hx

/-- **Smoothness of the extension.** -/
theorem contDiffOn_ext {S : ℝ} (hS : 0 < S) : ∀ (m : ℕ) {a : ℤ} {U : ℝ → ℝ},
    a + 4 * (m : ℤ) + 6 ≤ 0 → Bd S a (m + 1) U → ContDiffOn ℝ m (ext U) (Iio (S ^ 3)⁻¹)
  | 0, a, U, ha, hU => by
    obtain ⟨h0, U', hd, -⟩ := hU
    have ha6 : a ≤ -6 := by omega
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun σ hσ => (hasDerivAt_ext hS ha6 h0 hd hσ).continuousAt.continuousWithinAt
  | m + 1, a, U, ha, hU => by
    obtain ⟨h0, U', hd, hU'⟩ := hU
    have ha6 : a ≤ -6 := by omega
    have hV : Bd S (a + 4) (m + 1) (fun s => -(1 / 3) * s ^ 4 * U' s) := by
      have h := Bd.const_mul (-(1 / 3)) (Bd.mul hS (Bd.zpow hS (m + 1) 4) hU')
      refine Bd.congr (fun s _ => ?_) (Bd.mono_a hS (by omega : (4 : ℤ) + a ≤ a + 4) h)
      rw [zpow_ofNat]
      ring
    have hih := contDiffOn_ext hS m (a := a + 4) (by omega) hV
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio).2
      ⟨fun σ hσ => (hasDerivAt_ext hS ha6 h0 hd hσ).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
    exact hih.congr fun σ hσ => (hasDerivAt_ext hS ha6 h0 hd hσ).deriv

/-! ### Smoothness of a trajectory on `(0, ∞)` -/

variable {d : ℝ} {Z : ℝ → State}

theorem contDiffOn_trajectory (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1) (n : ℕ) :
    ContDiffOn ℝ n (fun s => (Z s).1) (Ioi 0) ∧ ContDiffOn ℝ n (fun s => (Z s).2.1) (Ioi 0) ∧
      ContDiffOn ℝ n (fun s => (Z s).2.2) (Ioi 0) := by
  have hd := fun s (hs : (0 : ℝ) < s) => Calabi.Tail.hasDerivAt_components (hZ s hs)
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero, contDiffOn_zero, contDiffOn_zero]
    exact ⟨fun s hs => (hd s hs).1.continuousAt.continuousWithinAt,
      fun s hs => (hd s hs).2.1.continuousAt.continuousWithinAt,
      fun s hs => (hd s hs).2.2.continuousAt.continuousWithinAt⟩
  | succ n ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have hne : ∀ s ∈ Ioi (0 : ℝ), s ≠ 0 := fun s hs => ne_of_gt hs
    have c1 : ContDiffOn ℝ n (fun s : ℝ => 21 / s) (Ioi 0) :=
      contDiffOn_const.div contDiffOn_id hne
    have c2 : ContDiffOn ℝ n (fun s : ℝ => 337 / (4 * s ^ 2)) (Ioi 0) :=
      contDiffOn_const.div (contDiffOn_const.mul (contDiffOn_id.pow 2))
        fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hne s hs))
    have c3 : ContDiffOn ℝ n (fun s : ℝ => 567 / (4 * s ^ 3)) (Ioi 0) :=
      contDiffOn_const.div (contDiffOn_const.mul (contDiffOn_id.pow 3))
        fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 3 (hne s hs))
    have hN : ContDiffOn ℝ n (fun s => (Z s).1 / (1 + (Z s).1)) (Ioi 0) :=
      ih0.div (contDiffOn_const.add ih0) fun s hs => by
        have := hlow s hs
        intro h
        linarith
    have hF : ContDiffOn ℝ n (fun s => -(21 / s) * (Z s).2.2 - 337 / (4 * s ^ 2) * (Z s).2.1
        + 567 / (4 * s ^ 3) * ((Z s).1 - d) - (Z s).1 / (1 + (Z s).1)) (Ioi 0) :=
      (((c1.neg.mul ih2).sub (c2.mul ih1)).add (c3.mul (ih0.sub contDiffOn_const))).sub hN
    rw [Nat.cast_succ]
    refine ⟨?_, ?_, ?_⟩
    · refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
        ⟨fun s hs => (hd s hs).1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact ih1.congr fun s hs => (hd s hs).1.deriv
    · refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
        ⟨fun s hs => (hd s hs).2.1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact ih2.congr fun s hs => (hd s hs).2.1.deriv
    · refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
        ⟨fun s hs => (hd s hs).2.2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
      refine hF.congr fun s hs => ?_
      rw [(hd s hs).2.2.deriv]
      simp only [pfield, Ntr_of_ge (hlow s hs)]

theorem contDiffOn_fst (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1) :
    ContDiffOn ℝ ∞ (fun s => (Z s).1) (Ioi 0) :=
  contDiffOn_infty.2 fun n => (contDiffOn_trajectory hZ hlow n).1

/-! ### The profile in the variable `σ` -/

theorem contDiff_eval (P : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (fun x : ℝ => P.eval x) := by
  simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) P n

/-- **Smoothness at infinity.** In the variable `σ = s⁻³` the first component
of a trajectory of the profile system that is bounded at infinity is smooth on
`[0, ∞)`, with the value zero at `σ = 0`. -/
theorem contDiffOn_ext_profile (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hbdd : ∃ B, ∀ s, (56 : ℝ) ≤ s → ‖Z s‖ ≤ B)
    (hsmall : ∀ s, (56 : ℝ) ≤ s → |(Z s).1| ≤ 1 / 100) :
    ContDiffOn ℝ ∞ (ext fun s => (Z s).1) (Ici 0) := by
  refine contDiffOn_infty.2 fun m => ?_
  intro σ hσ
  rcases eq_or_lt_of_le (mem_Ici.1 hσ) with h | h
  · subst h
    -- the remainder of order `2m + 1`
    obtain ⟨S₀, C, hS, hC, hq, hdec⟩ := exists_decay hZ hlow hbdd hsmall (2 * m + 1)
    have hS0 : 0 < S₀ := by linarith
    have hW := (wjet_bd hZ hlow hS hC hq hdec (m + 1)).1
    have hext := contDiffOn_ext hS0 m (by push_cast; omega) hW
    have hsum : ContDiffOn ℝ m
        (fun σ => ext (fun s => (Wjet (tailPoly d (2 * m + 1)) Z s).1) σ
          + (tailPoly d (2 * m + 1)).eval σ) (Iio (S₀ ^ 3)⁻¹) :=
      hext.add (contDiff_eval _ _).contDiffOn
    have hat := (hsum.contDiffAt (Iio_mem_nhds (inv_pos.2 (pow_pos hS0 3)))).contDiffWithinAt
      (s := Ici (0 : ℝ))
    have hEq : ∀ x, 0 ≤ x → ext (fun s => (Z s).1) x =
        ext (fun s => (Wjet (tailPoly d (2 * m + 1)) Z s).1) x
          + (tailPoly d (2 * m + 1)).eval x := by
      intro x hx
      rcases eq_or_lt_of_le hx with h0 | h0
      · subst h0
        rw [ext_of_nonpos _ le_rfl, ext_of_nonpos _ le_rfl, ← coeff_zero_eq_eval_zero,
          tailPoly_coeff_zero, add_zero]
      · rw [ext_of_pos _ h0, ext_of_pos _ h0]
        simp only [Wjet, Prod.fst_sub, q0, iota_zpow h0]
        ring
    exact hat.congr_of_eventuallyEq (eventually_nhdsWithin_of_forall fun x hx => hEq x hx)
      (hEq 0 le_rfl)
  · have h1 : ContDiffAt ℝ m (fun s => (Z s).1) (iota σ) :=
      ((contDiffOn_trajectory hZ hlow m).1).contDiffAt (Ioi_mem_nhds (iota_pos h))
    have h2 := h1.comp σ (contDiffAt_iota h m)
    refine (h2.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact ext_of_pos _ hx

theorem ext_profile_zero (Z : ℝ → State) : ext (fun s => (Z s).1) 0 = 0 :=
  ext_of_nonpos _ le_rfl

end Calabi.Infinity
