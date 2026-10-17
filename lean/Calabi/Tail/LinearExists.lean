import Calabi.Tail.Linear
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.LinearCombination

/-!
# The bounded solution of `V‴ + V = j` with a prescribed stable coordinate

For a bounded continuous source `j` on the line, `linSol S q₀ j` is the jet of
a solution of `V‴ + V = j` whose stable coordinate at `S` is `q₀` and whose
unstable part is bounded: the stable part is integrated forwards from `S`, the
unstable part backwards from infinity with the complex root `e^{iπ/3}`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Calabi.Tail

open Calabi.Shot (State)

/-- The root `e^{iπ/3}` of `λ² - λ + 1`. -/
noncomputable def lam : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem lam_mul_re (t : ℝ) : (lam * (t : ℂ)).re = t / 2 := by
  simp only [lam, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The integrand of the unstable part. -/
noncomputable def kern (j : ℝ → ℝ) (u : ℝ) : ℂ := Complex.exp (-(lam * (u : ℂ))) * (j u : ℂ)

theorem norm_kern (j : ℝ → ℝ) (u : ℝ) : ‖kern j u‖ = Real.exp (-(1 / 2) * u) * |j u| := by
  unfold kern
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, Complex.neg_re,
    lam_mul_re]
  congr 2
  ring

theorem continuous_kern {j : ℝ → ℝ} (hj : Continuous j) : Continuous (kern j) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
    (Complex.continuous_ofReal.comp hj)

theorem norm_kern_le {j : ℝ → ℝ} {M : ℝ} (hM : ∀ u, |j u| ≤ M) (u : ℝ) :
    ‖kern j u‖ ≤ M * Real.exp (-(1 / 2) * u) := by
  rw [norm_kern, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM u) (Real.exp_pos _).le

theorem integrableOn_kern {j : ℝ → ℝ} (hj : Continuous j) {M : ℝ} (hM : ∀ u, |j u| ≤ M)
    (a : ℝ) : IntegrableOn (kern j) (Ioi a) :=
  Integrable.mono' (Integrable.const_mul (exp_neg_integrableOn_Ioi a (by norm_num)) M)
    (continuous_kern hj).aestronglyMeasurable (ae_of_all _ (norm_kern_le hM))

theorem norm_integral_kern_le {j : ℝ → ℝ} {M : ℝ} (hM : ∀ u, |j u| ≤ M) (s : ℝ) :
    ‖∫ u in Ioi s, kern j u‖ ≤ 2 * M * Real.exp (-(s / 2)) := by
  have h : Integrable (fun u : ℝ => M * Real.exp (-(1 / 2) * u)) (volume.restrict (Ioi s)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi s (by norm_num)) M
  refine (norm_integral_le_of_norm_le h (ae_of_all _ (norm_kern_le hM))).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) s,
    show (-(1 / 2) : ℝ) * s = -(s / 2) by ring]
  ring

theorem hasDerivAt_integral_kern {j : ℝ → ℝ} (hj : Continuous j) {M : ℝ}
    (hM : ∀ u, |j u| ≤ M) (s : ℝ) :
    HasDerivAt (fun t => ∫ u in Ioi t, kern j u) (-kern j s) s := by
  have hid : (fun t => ∫ u in Ioi t, kern j u) =
      fun t => (∫ u in Ioi (0 : ℝ), kern j u) - ∫ u in (0 : ℝ)..t, kern j u := by
    funext t
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_kern hj hM 0)
      (integrableOn_kern hj hM t), sub_sub_cancel]
  rw [hid]
  have h := (hasDerivAt_const s (∫ u in Ioi (0 : ℝ), kern j u)).sub
    ((continuous_kern hj).integral_hasStrictDerivAt 0 s).hasDerivAt
  rwa [zero_sub] at h

/-- The unstable part: the bounded solution of `ζ′ = λ ζ + j`. -/
noncomputable def zeta (j : ℝ → ℝ) (s : ℝ) : ℂ :=
  -(Complex.exp (lam * (s : ℂ)) * ∫ u in Ioi s, kern j u)

theorem hasDerivAt_zeta {j : ℝ → ℝ} (hj : Continuous j) {M : ℝ} (hM : ∀ u, |j u| ≤ M)
    (s : ℝ) : HasDerivAt (zeta j) (lam * zeta j s + (j s : ℂ)) s := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (lam * (t : ℂ)))
      (Complex.exp (lam * (s : ℂ)) * (lam * ((1 : ℝ) : ℂ))) s :=
    (((hasDerivAt_id s).ofReal_comp).const_mul lam).cexp
  have h := (h1.mul (hasDerivAt_integral_kern hj hM s)).neg
  refine h.congr_deriv ?_
  have hE : Complex.exp (lam * (s : ℂ)) * Complex.exp (-(lam * (s : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  unfold zeta kern
  push_cast
  linear_combination (j s : ℂ) * hE

theorem norm_zeta_le {j : ℝ → ℝ} {M : ℝ} (hM : ∀ u, |j u| ≤ M) (s : ℝ) :
    ‖zeta j s‖ ≤ 2 * M := by
  unfold zeta
  rw [norm_neg, norm_mul, Complex.norm_exp, lam_mul_re]
  have h := mul_le_mul_of_nonneg_left (norm_integral_kern_le hM s) (Real.exp_pos (s / 2)).le
  have e : Real.exp (s / 2) * (2 * M * Real.exp (-(s / 2))) = 2 * M := by
    rw [show Real.exp (s / 2) * (2 * M * Real.exp (-(s / 2))) =
      2 * M * (Real.exp (s / 2) * Real.exp (-(s / 2))) by ring, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  rwa [e] at h

/-- The stable part: the solution of `q′ = -q + j / 3` with `q(S) = q₀`. -/
noncomputable def stabSol (S q₀ : ℝ) (j : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(s - S)) * q₀ + Real.exp (-s) * (∫ u in S..s, Real.exp u * j u) / 3

theorem stabSol_self (S q₀ : ℝ) (j : ℝ → ℝ) : stabSol S q₀ j S = q₀ := by
  simp [stabSol]

theorem hasDerivAt_stabSol {j : ℝ → ℝ} (hj : Continuous j) (S q₀ s : ℝ) :
    HasDerivAt (stabSol S q₀ j) (-stabSol S q₀ j s + j s / 3) s := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(t - S))) (Real.exp (-(s - S)) * -1) s :=
    (((hasDerivAt_id s).sub_const S).neg).exp
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-s) * -1) s :=
    (hasDerivAt_id s).neg.exp
  have h3 : HasDerivAt (fun t : ℝ => ∫ u in S..t, Real.exp u * j u) (Real.exp s * j s) s :=
    ((Real.continuous_exp.mul hj).integral_hasStrictDerivAt S s).hasDerivAt
  have h := (h1.mul_const q₀).add ((h2.mul h3).div_const 3)
  refine h.congr_deriv ?_
  have hE : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold stabSol
  linear_combination (j s / 3) * hE

/-- The jet of the bounded solution with stable coordinate `q₀` at `S`. -/
noncomputable def linSol (S q₀ : ℝ) (j : ℝ → ℝ) (s : ℝ) : State :=
  (stabSol S q₀ j s + (zeta j s).im * (Real.sqrt 3 / 3) - (zeta j s).re / 3,
    -stabSol S q₀ j s + (zeta j s).re / 3 + (zeta j s).im * (Real.sqrt 3 / 3),
    stabSol S q₀ j s + 2 * (zeta j s).re / 3)

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem hasDerivAt_linSol {j : ℝ → ℝ} (hj : Continuous j) {M : ℝ} (hM : ∀ u, |j u| ≤ M)
    (S q₀ s : ℝ) :
    HasDerivAt (linSol S q₀ j)
      ((linSol S q₀ j s).2.1, (linSol S q₀ j s).2.2, -(linSol S q₀ j s).1 + j s) s := by
  have hq := hasDerivAt_stabSol hj S q₀ s
  have hz := hasDerivAt_zeta hj hM s
  have hre : HasDerivAt (fun t => (zeta j t).re) ((lam * zeta j s + (j s : ℂ)).re) s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hz
  have him : HasDerivAt (fun t => (zeta j t).im) ((lam * zeta j s + (j s : ℂ)).im) s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hz
  have h1 := (hq.add (him.mul_const (Real.sqrt 3 / 3))).sub (hre.div_const 3)
  have h2 := ((hq.neg).add (hre.div_const 3)).add (him.mul_const (Real.sqrt 3 / 3))
  have h3 := hq.add ((hre.const_mul 2).div_const 3)
  have h := h1.prodMk (h2.prodMk h3)
  refine h.congr_deriv ?_
  have h3sq := sqrt_three_sq
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [linSol, lam, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_im, add_zero]
    linear_combination ((zeta j s).re / 6) * h3sq
  · simp only [linSol, lam, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_im, add_zero]
    linear_combination ((zeta j s).re / 6) * h3sq
  · simp only [linSol, lam, Complex.add_re, Complex.mul_re, Complex.ofReal_re]
    ring

theorem linSol_solves {j : ℝ → ℝ} (hj : Continuous j) {M : ℝ} (hM : ∀ u, |j u| ≤ M)
    (S q₀ S' : ℝ) : Solves S' (linSol S q₀ j) j :=
  fun s _ => hasDerivAt_linSol hj hM S q₀ s

theorem stab_linSol (S q₀ : ℝ) (j : ℝ → ℝ) (s : ℝ) :
    stab (linSol S q₀ j s) = stabSol S q₀ j s := by
  simp only [stab, linSol]
  ring

theorem stab_linSol_self (S q₀ : ℝ) (j : ℝ → ℝ) : stab (linSol S q₀ j S) = q₀ := by
  rw [stab_linSol, stabSol_self]

theorem energy_linSol {j : ℝ → ℝ} (S q₀ : ℝ) (s : ℝ) :
    energy (linSol S q₀ j s) = ‖zeta j s‖ ^ 2 := by
  have h3sq := sqrt_three_sq
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [energy, ux, uw, linSol]
  linear_combination ((zeta j s).im ^ 2 / 3) * h3sq

theorem energy_linSol_le {j : ℝ → ℝ} {M : ℝ} (hM : ∀ u, |j u| ≤ M) (S q₀ s : ℝ) :
    energy (linSol S q₀ j s) ≤ 4 * M ^ 2 := by
  rw [energy_linSol]
  have h := norm_zeta_le hM s
  have h0 := norm_nonneg (zeta j s)
  nlinarith

end Calabi.Tail
