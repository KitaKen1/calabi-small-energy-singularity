import Calabi.Origin.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The regular solution is smooth at the origin

The averages `T e g r = ∫₀¹ tᵉ g(t r) dt` preserve `C^m` on `(-1, 1)`: their
derivative is `T (e + 1) g′`. For the regular solution `P`,

  `P′(r) = k - (8/27) r K1 (N ∘ P) r`   for all `|r| < 1`, including `r = 0`,

so `P ∈ C^m` implies `P′ ∈ C^m`, and `P` is smooth on `(-1, 1)`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Origin

/-- The clamp to `[-ρ, ρ]`. -/
noncomputable def clampTo (ρ x : ℝ) : ℝ := max (-ρ) (min x ρ)

theorem abs_clampTo_le {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) : |clampTo ρ x| ≤ ρ :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampTo_of_abs_le {ρ x : ℝ} (h : |x| ≤ ρ) : clampTo ρ x = x := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold clampTo
  rw [min_eq_left h2, max_eq_right h1]

theorem continuous_clampTo (ρ : ℝ) : Continuous (clampTo ρ) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- A function continuous on `(-1, 1)`, cut off at `ρ < 1`, is continuous. -/
theorem continuous_localize {g : ℝ → ℝ} (hg : ContinuousOn g (Ioo (-1) 1)) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) : Continuous fun x => g (clampTo ρ x) :=
  hg.comp_continuous (continuous_clampTo ρ) fun x => by
    have := abs_le.1 (abs_clampTo_le hρ0 x)
    exact ⟨by linarith, by linarith⟩

theorem abs_mul_le_of_mem {t r ρ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hr : |r| ≤ ρ) : |t * r| ≤ ρ := by
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hr

theorem T_localize {g : ℝ → ℝ} {ρ r : ℝ} (hr : |r| ≤ ρ) (e : ℕ) :
    T e g r = T e (fun x => g (clampTo ρ x)) r :=
  T_congr (fun t ht => by rw [clampTo_of_abs_le (abs_mul_le_of_mem ht hr)]) e

/-- The midpoint between `|r₀|` and `1`. -/
theorem exists_radius {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo (-1 : ℝ) 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ |r₀| < ρ ∧ {x : ℝ | |x| < ρ} ∈ 𝓝 r₀ := by
  have habs : |r₀| < 1 := abs_lt.2 hr₀
  have h0 := abs_nonneg r₀
  refine ⟨(|r₀| + 1) / 2, by linarith, by linarith, by linarith, ?_⟩
  exact (isOpen_lt continuous_abs continuous_const).mem_nhds (by show |r₀| < (|r₀| + 1) / 2; linarith)

theorem continuousOn_T {g : ℝ → ℝ} (hg : ContinuousOn g (Ioo (-1) 1)) (e : ℕ) :
    ContinuousOn (T e g) (Ioo (-1) 1) := by
  intro r₀ hr₀
  obtain ⟨ρ, hρ0, hρ1, -, hs⟩ := exists_radius hr₀
  have hc := continuous_T (continuous_localize hg hρ0 hρ1) e
  have heq : T e (fun x => g (clampTo ρ x)) =ᶠ[𝓝 r₀] T e g := by
    filter_upwards [hs] with x hx using (T_localize (le_of_lt hx) e).symm
  exact (hc.continuousAt.congr heq).continuousWithinAt

/-- Differentiation under the integral sign: `(T e g)′ = T (e + 1) g′`. -/
theorem hasDerivAt_T_param {g g' : ℝ → ℝ} (hg : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Ioo (-1) 1)) (e : ℕ) {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (T e g) (T (e + 1) g' r₀) r₀ := by
  obtain ⟨ρ, hρ0, hρ1, hρr, hs⟩ := exists_radius hr₀
  have hgc : ContinuousOn g (Ioo (-1) 1) := fun x hx =>
    (hg x hx).continuousAt.continuousWithinAt
  have hcG := continuous_localize hgc hρ0 hρ1
  have hcG' := continuous_localize hg' hρ0 hρ1
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |g' (clampTo ρ x)| ≤ C := by
    have hsub : Icc (-ρ) ρ ⊆ Ioo (-1 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg'.mono hsub)
    exact ⟨C, fun x => by
      rw [← Real.norm_eq_abs]
      exact hC _ (abs_le.1 (abs_clampTo_le hρ0 x))⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r t => t ^ e * g (clampTo ρ (t * r)))
    (F' := fun r t => t ^ (e + 1) * g' (clampTo ρ (t * r)))
    (x₀ := r₀) (a := 0) (b := 1) (bound := fun _ => C) (μ := MeasureTheory.volume) hs
    (Eventually.of_forall fun r => (continuous_integrand hcG e r).aestronglyMeasurable)
    ((continuous_integrand hcG e r₀).intervalIntegrable _ _)
    ((continuous_integrand hcG' (e + 1) r₀).aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun t ht r _ => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht.1.le _)]
      have h1 : t ^ (e + 1) ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have h2 := hC (t * r)
      have h3 := abs_nonneg (g' (clampTo ρ (t * r)))
      nlinarith [pow_nonneg ht.1.le (e + 1)])
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t ht r hr => by
      rw [uIoc_of_le zero_le_one] at ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hr' : |r| < ρ := hr
      have htr : |t * r| < ρ := by
        rw [abs_mul, abs_of_pos ht.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hr'
      have hmem : t * r ∈ Ioo (-1 : ℝ) 1 := by
        obtain ⟨a1, a2⟩ := abs_lt.1 htr
        exact ⟨by linarith, by linarith⟩
      have hchain : HasDerivAt (fun x : ℝ => g (t * x)) (g' (t * r) * (t * 1)) r :=
        (hg (t * r) hmem).comp r ((hasDerivAt_id' r).const_mul t)
      have hopen : {x : ℝ | |t * x| < ρ} ∈ 𝓝 r :=
        (isOpen_lt (continuous_abs.comp (continuous_const.mul continuous_id))
          continuous_const).mem_nhds htr
      have heq : (fun x : ℝ => g (clampTo ρ (t * x))) =ᶠ[𝓝 r] fun x => g (t * x) := by
        filter_upwards [hopen] with x hx
        rw [clampTo_of_abs_le (le_of_lt hx)]
      have h := (hchain.congr_of_eventuallyEq heq).const_mul (t ^ e)
      refine h.congr_deriv ?_
      rw [clampTo_of_abs_le htr.le]
      ring)
  have heq : T e g =ᶠ[𝓝 r₀] fun r => ∫ t in (0 : ℝ)..1, t ^ e * g (clampTo ρ (t * r)) := by
    filter_upwards [hs] with x hx using T_localize (le_of_lt hx) e
  have hval : T (e + 1) g' r₀ = ∫ t in (0 : ℝ)..1, t ^ (e + 1) * g' (clampTo ρ (t * r₀)) :=
    T_localize hρr.le (e + 1)
  rw [hval]
  exact key.2.congr_of_eventuallyEq heq

/-- The averages preserve `C^m` on `(-1, 1)`. -/
theorem contDiffOn_T : ∀ (m e : ℕ) (g : ℝ → ℝ), ContDiffOn ℝ m g (Ioo (-1 : ℝ) 1) →
    ContDiffOn ℝ m (T e g) (Ioo (-1 : ℝ) 1) := by
  intro m
  induction m with
  | zero =>
    intro e g hg
    rw [Nat.cast_zero, contDiffOn_zero] at hg ⊢
    exact continuousOn_T hg e
  | succ m ih =>
    intro e g hg
    rw [Nat.cast_succ] at hg ⊢
    obtain ⟨hd, -, hg'⟩ := (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 hg
    have hder : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt (T e g) (T (e + 1) (deriv g) r) r := fun r hr =>
      hasDerivAt_T_param
        (fun x hx => ((hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
        hg'.continuousOn e hr
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
      ⟨fun r hr => (hder r hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (e + 1) (deriv g) hg').congr fun r hr => (hder r hr).deriv

theorem continuous_oP (k d : ℝ) : Continuous (oP k d) := by
  unfold oP
  exact (continuous_const.add (continuous_const.mul continuous_id)).sub
    ((continuous_const.mul (continuous_id.pow 2)).mul (continuous_K (continuous_Nor_osol k d)).1)

/-- The derivative of the regular solution at every `r`, including `r = 0`. -/
theorem hasDerivAt_oP_all (k d r : ℝ) :
    HasDerivAt (oP k d) (k - 8 / 27 * r * K1 (fun x => Nor (osol k d x)) r) r := by
  by_cases hr : r = 0
  · subst hr
    have hK : ContinuousAt (fun x : ℝ => x * K0 (fun y => Nor (osol k d y)) x) 0 :=
      (continuous_id.mul (continuous_K (continuous_Nor_osol k d)).1).continuousAt
    have hsl : HasDerivAt (fun x : ℝ => x * (x * K0 (fun y => Nor (osol k d y)) x)) 0 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      have ht : Tendsto (fun x : ℝ => x * K0 (fun y => Nor (osol k d y)) x) (𝓝[≠] 0) (𝓝 0) := by
        have := hK.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
        simpa using this
      refine ht.congr' ?_
      refine eventually_nhdsWithin_of_forall fun x hx => ?_
      have hx0 : x ≠ 0 := hx
      simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul, zero_mul]
      field_simp
    have e : oP k d = fun x => d + k * x
        - 8 / 27 * (x * (x * K0 (fun y => Nor (osol k d y)) x)) := by
      funext x
      unfold oP
      ring
    rw [e]
    have h := ((hasDerivAt_const (0 : ℝ) d).fun_add ((hasDerivAt_id' (0 : ℝ)).const_mul k)).fun_sub
      (hsl.const_mul (8 / 27))
    refine h.congr_deriv ?_
    ring
  · refine (hasDerivAt_oP k d hr).congr_deriv ?_
    unfold osol1
    field_simp

theorem contDiffOn_Nor (m : ℕ) : ContDiffOn ℝ m Nor (Ioi (-(1 / 2))) := by
  have h : ContDiffOn ℝ m (fun p : ℝ => p / (1 + p)) (Ioi (-(1 / 2))) :=
    contDiffOn_id.div (contDiffOn_const.add contDiffOn_id) fun p hp => by
      have hp' : -(1 / 2 : ℝ) < p := hp
      have : (0 : ℝ) < 1 + p := by linarith
      exact this.ne'
  exact h.congr fun p hp => Nor_of_ge (le_of_lt hp)

/-- **Smoothness at the origin.** As long as it stays above `-1/2`, the regular
solution is `C^m` on `(-1, 1)` for every `m`. -/
theorem contDiffOn_oP {k d : ℝ} (hlow : ∀ r ∈ Ioo (-1 : ℝ) 1, -(1 / 2) < osol k d r) :
    ∀ m : ℕ, ContDiffOn ℝ m (oP k d) (Ioo (-1 : ℝ) 1) := by
  have heq : ∀ r ∈ Ioo (-1 : ℝ) 1, osol k d r = oP k d r := fun r hr =>
    (oP_eq_osol k d (abs_le.2 ⟨hr.1.le, hr.2.le⟩)).symm
  intro m
  induction m with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (continuous_oP k d).continuousOn
  | succ m ih =>
    rw [Nat.cast_succ]
    have hos : ContDiffOn ℝ m (fun x => osol k d x) (Ioo (-1) 1) := ih.congr heq
    have hg : ContDiffOn ℝ m (fun x => Nor (osol k d x)) (Ioo (-1) 1) :=
      (contDiffOn_Nor m).comp hos fun r hr => hlow r hr
    have hK1 : ContDiffOn ℝ m (K1 fun x => Nor (osol k d x)) (Ioo (-1) 1) := by
      have h0 := contDiffOn_T m 0 _ hg
      have h7 := contDiffOn_T m 7 _ hg
      have h8 := contDiffOn_T m 8 _ hg
      show ContDiffOn ℝ m (fun r => T 0 (fun x => Nor (osol k d x)) r / 56
        + 6 / 7 * T 7 (fun x => Nor (osol k d x)) r
        - 7 / 8 * T 8 (fun x => Nor (osol k d x)) r) (Ioo (-1) 1)
      exact ((h0.div_const 56).add (contDiffOn_const.mul h7)).sub (contDiffOn_const.mul h8)
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
      ⟨fun r _ => (hasDerivAt_oP_all k d r).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hder : ContDiffOn ℝ m
        (fun r => k - 8 / 27 * r * K1 (fun x => Nor (osol k d x)) r) (Ioo (-1) 1) :=
      contDiffOn_const.sub ((contDiffOn_const.mul contDiffOn_id).mul hK1)
    exact hder.congr fun r _ => (hasDerivAt_oP_all k d r).deriv

theorem contDiffOn_oP_infty {k d : ℝ} (hlow : ∀ r ∈ Ioo (-1 : ℝ) 1, -(1 / 2) < osol k d r) :
    ContDiffOn ℝ ∞ (oP k d) (Ioo (-1 : ℝ) 1) :=
  contDiffOn_infty.2 (contDiffOn_oP hlow)

end Calabi.Origin
