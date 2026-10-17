import Calabi.Correction.ResidualOsc
import Calabi.Correction.FrozenOsc

/-!
# The coefficients of the outer problem in the momentum coordinate

Scaled bounds, in the sense of `Osc.lean`, for the quantities that enter the
outer part of the approximate inverse of Section 6.2 of the manuscript.

* `uosc_clam`: the zeroth-order coefficient `2 v∗ b_λ A F_λ` has order `-2`
  (`Osc(σ⁻⁴)` in the notation of the manuscript);
* `bzero`, `bdiff`: away from the point orbit the multiplier `b_λ` has the
  limit `b⁰_λ = 1 + (1 - x) χ_λ (c - 1)` at the singular time. The outer
  problems are solved with this time-independent multiplier, and the
  difference `b_λ² - (b⁰_λ)²`, cut off inside `x ≤ θ/4`, is an error term: it
  has order zero with a uniform constant (`bdiff_osc`) and it is small,
  `O(T/θ²)` (`bdiff_small`);
* `elam_osc`: for a fixed cut-off radius `λ` the residual `E_λ` has order `-2`
  with the constant `C/λ` (its annular part is not small, cf. the remark after
  Lemma 6.2).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Osc

open Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-! ### The zeroth-order coefficient -/

/-- `2 v∗ b_λ A F_λ` has order `-2`. -/
theorem uosc_clam (hP : IsProfile c G) :
    UOsc (-2) (fun lam t x =>
      2 * vstar x * (1 + vstar x * Flam G lam t x) * Aop (Flam G lam t) x) := by
  have h1 : UOsc (-2) _ := ((uosc_AFlam hP).term 1 1 (-1) 0 0 0).cast (by norm_num)
  have h2 : UOsc (-2) _ := (h1.mul (uosc_blam hP)).cast (by norm_num)
  refine (h2.const_mul 2).congr fun lam _ t _ x _ => ?_
  unfold vstar pol
  ring

/-- `v∗ = x (1 - x)` has order one. -/
theorem uosc_vstar : UOsc 1 (fun _ _ x => vstar x) := by
  have h : UOsc 1 _ := ((uosc_xpow 1).mul (uosc_pol 1 (-1) 0 0 0)).cast (by norm_num)
  refine h.congr fun lam _ t _ x _ => ?_
  unfold vstar pol
  ring

/-! ### The localized profile near and away from the point orbit -/

theorem Flam_of_lt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) {x : ℝ} (hxl : x < lam) :
    Flam G lam t x = Fss G t x := by
  rw [← flamJet_zero, flamJet_of_lt hlam 0 t hxl, iteratedDeriv_zero]

/-- For `x < λ` the operator `A` on the localized profile is the operator on
the self-similar profile. -/
theorem Aop_Flam_of_lt (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : x < lam) :
    Aop (Flam G lam t) x = Aop (Fss G t) x := by
  obtain ⟨d1, d2, d3, d4⟩ := D_Flam hP hlam ht x hx
  have hF := Flam_of_lt (G := G) hlam t hxl
  rw [Aop_Fss_eq hP ht hx, Aop_eq (contDiffOn_Flam_Icc hP lam ht) hx, d1, d2, d3, d4,
    flamJet_of_lt hlam 1 t hxl, flamJet_of_lt hlam 2 t hxl, flamJet_of_lt hlam 3 t hxl,
    flamJet_of_lt hlam 4 t hxl, hF]
  unfold AhatF AdiffF
  ring

/-- For `x > 2λ` the operator `A` on the localized profile vanishes. -/
theorem Aop_Flam_of_gt (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : t < 0)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxl : 2 * lam < x) : Aop (Flam G lam t) x = 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := D_Flam hP hlam ht x hx
  have hF : Flam G lam t x = 0 := by
    rw [← flamJet_zero, flamJet_of_gt hlam 0 t hxl]
  rw [Aop_eq (contDiffOn_Flam_Icc hP lam ht) hx, d1, d2, d3, d4, flamJet_of_gt hlam 1 t hxl,
    flamJet_of_gt hlam 2 t hxl, flamJet_of_gt hlam 3 t hxl, flamJet_of_gt hlam 4 t hxl, hF]
  ring

/-! ### The multiplier at the singular time -/

/-- The limit of the multiplier `b_λ` at the singular time, away from the point
orbit. -/
noncomputable def bzero (c lam x : ℝ) : ℝ := 1 + (1 - x) * chi (x / lam) * (c - 1)

theorem blam_eq (hP : IsProfile c G) (lam : ℝ) {t : ℝ} (ht : t < 0) (x : ℝ) :
    1 + vstar x * Flam G lam t x
      = 1 + (1 - x) * chi (x / lam) * (G (x / Real.sqrt (-t)) - 1) := by
  have h := one_add_mul_Fss hP ht x
  unfold vstar Flam
  linear_combination ((1 - x) * chi (x / lam)) * h

theorem blam_sub_bzero (hP : IsProfile c G) (lam : ℝ) {t : ℝ} (ht : t < 0) (x : ℝ) :
    1 + vstar x * Flam G lam t x - bzero c lam x
      = (1 - x) * chi (x / lam) * (G (x / Real.sqrt (-t)) - c) := by
  rw [blam_eq hP lam ht x]
  unfold bzero
  ring

theorem bzero_mem {lam x : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    c ≤ bzero c lam x ∧ bzero c lam x ≤ 1 := by
  have h1 := chi_nonneg (x / lam)
  have h2 := chi_le_one (x / lam)
  have h3 : 0 ≤ (1 - x) * chi (x / lam) := mul_nonneg (by linarith [hx.2]) h1
  have h4 : (1 - x) * chi (x / lam) ≤ 1 := by
    calc (1 - x) * chi (x / lam) ≤ 1 * 1 := mul_le_mul (by linarith [hx.1]) h2 h1 zero_le_one
      _ = 1 := one_mul 1
  have h5 := mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hc1.le)
  have h6 := mul_nonneg h3 (sub_nonneg.2 hc1.le)
  unfold bzero
  constructor <;> nlinarith

theorem uosc_bzero (c : ℝ) : UOsc 0 (fun lam _ x => bzero c lam x) := by
  have h1 : UOsc 0 _ := (((uosc_pol 1 (-1) 0 0 0).mul uosc_chi).const_mul (c - 1)).cast
    (by norm_num)
  refine (uosc_one.add h1).congr fun lam _ t _ x _ => ?_
  unfold bzero pol
  ring

/-! ### The difference between the multiplier and its limit -/

/-- `b_λ² - (b⁰_λ)²`, cut off inside `x ≤ θ/4`. -/
noncomputable def bdiff (G : ℝ → ℝ) (c lam θ t x : ℝ) : ℝ :=
  (1 - chi (x / (θ / 4))) * ((1 + vstar x * Flam G lam t x) ^ 2 - bzero c lam x ^ 2)

theorem bdiff_of_ge {lam θ t x : ℝ} (hθ : 0 < θ) (hx : θ / 2 ≤ x) :
    bdiff G c lam θ t x = (1 + vstar x * Flam G lam t x) ^ 2 - bzero c lam x ^ 2 := by
  have h : 2 ≤ x / (θ / 4) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  unfold bdiff
  rw [chi_of_ge h, sub_zero, one_mul]

theorem bdiff_of_le {lam θ t x : ℝ} (hθ : 0 < θ) (hx : x ≤ θ / 4) :
    bdiff G c lam θ t x = 0 := by
  have h : x / (θ / 4) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hx
  unfold bdiff
  rw [chi_of_le h, sub_self, zero_mul]

/-- The difference has order zero, uniformly. -/
theorem bdiff_osc (hP : IsProfile c G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam θ T : ℝ), 0 < lam → 0 < θ →
    T ≤ lam ^ 2 → T ≤ (θ / 4) ^ 2 → T ≤ 1 → OscE T 0 C (bdiff G c lam θ) := by
  obtain ⟨M₁, hM₁, h₁⟩ := uosc_chi
  obtain ⟨M₂, hM₂, h₂⟩ := uosc_blam hP
  obtain ⟨M₃, hM₃, h₃⟩ := uosc_bzero c
  refine ⟨2 * (1 + M₁) * (2 * M₂ * M₂ + 2 * M₃ * M₃), by positivity, ?_⟩
  intro lam θ T hlam hθ hT hTθ hT1
  have hcut : OscE T 0 (1 + M₁) (fun (_ : ℝ) x => 1 - chi (x / (θ / 4))) :=
    oscE_one.sub (h₁ (θ / 4) T (by positivity) hTθ hT1)
  have hb := h₂ lam T hlam hT hT1
  have hz := h₃ lam T hlam hT hT1
  have hsq : OscE T 0 (2 * M₂ * M₂ + 2 * M₃ * M₃)
      (fun t x => (1 + vstar x * Flam G lam t x) * (1 + vstar x * Flam G lam t x)
        - bzero c lam x * bzero c lam x) :=
    ((hb.mul hb hM₂ hM₂).cast (by norm_num)).sub ((hz.mul hz hM₃ hM₃).cast (by norm_num))
  have h := (hcut.mul hsq (by positivity) (by positivity)).cast (by norm_num : (0 : ℤ) + 0 = 0)
  refine h.congr_fun fun t _ x _ => ?_
  unfold bdiff
  ring

/-- The difference is small: `O(T / θ²)`. -/
theorem bdiff_small (hP : IsProfile c G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam θ T : ℝ), 0 < θ →
    T ≤ (θ / 4) ^ 2 → ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      |bdiff G c lam θ t x| ≤ C * (T / θ ^ 2) := by
  obtain ⟨C₀, hC₀, hfr⟩ := frozen_bounds hP
  obtain ⟨Mu, hMu⟩ := hP.upper
  obtain ⟨κ, hκ, hlow⟩ := hP.lower
  have hmax : 0 ≤ max 1 Mu + 1 := by
    have := le_max_left (1 : ℝ) Mu
    linarith
  refine ⟨16 * C₀ * (max 1 Mu + 1), mul_nonneg (mul_nonneg (by norm_num) hC₀) hmax, ?_⟩
  intro lam θ T hθ hTθ t ht x hx
  have ht0 : t < 0 := ht.2
  have hT0 : 0 ≤ T := by linarith [ht.1]
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hθne : θ ≠ 0 := hθ.ne'
  have hRHS : 0 ≤ 16 * C₀ * (max 1 Mu + 1) * (T / θ ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) hmax) (div_nonneg hT0 hθ2.le)
  rcases le_or_gt x (θ / 4) with hxs | hxl
  · rw [bdiff_of_le hθ hxs, abs_zero]
    exact hRHS
  · -- `√(-t) ≤ θ/4 < x`
    have hρ : Real.sqrt (-t) ≤ θ / 4 := by
      have h1 : Real.sqrt (-t) ≤ Real.sqrt ((θ / 4) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [ht.1])
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hx0 : 0 < x := lt_trans (by positivity) hxl
    obtain ⟨hG, -, -⟩ := hfr t x ht0 (hρ.trans hxl.le)
    -- `|G - c| ≤ 16 C₀ T / θ²`
    have hGc : |G (x / Real.sqrt (-t)) - c| ≤ 16 * C₀ * (T / θ ^ 2) := by
      have hx2 : (θ / 4) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxl.le 2
      have h1 : C₀ * (-t) / x ^ 2 ≤ C₀ * T / (θ / 4) ^ 2 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith [ht.1]) hC₀)
          (by positivity) hx2
      have e : C₀ * T / (θ / 4) ^ 2 = 16 * C₀ * (T / θ ^ 2) := by
        field_simp
        ring
      rw [e] at h1
      exact hG.trans h1
    obtain ⟨hb1, hb2⟩ := blam_mem (lam := lam) hP hlow hMu ht0 hx
    obtain ⟨hz1, hz2⟩ := bzero_mem (lam := lam) hP.c_pos hP.c_lt_one hx
    have hκ1 : 0 ≤ min 1 κ := le_min zero_le_one hκ.le
    have hsum : |1 + vstar x * Flam G lam t x + bzero c lam x| ≤ max 1 Mu + 1 := by
      rw [abs_of_nonneg (by linarith [hP.c_pos])]
      linarith
    have hdiff : |1 + vstar x * Flam G lam t x - bzero c lam x| ≤ 16 * C₀ * (T / θ ^ 2) := by
      rw [blam_sub_bzero hP lam ht0 x, abs_mul, abs_mul, abs_of_nonneg (chi_nonneg _),
        abs_of_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)]
      have h1 : (1 - x) * chi (x / lam) ≤ 1 := by
        calc (1 - x) * chi (x / lam) ≤ 1 * 1 :=
              mul_le_mul (by linarith [hx.1]) (chi_le_one _) (chi_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc (1 - x) * chi (x / lam) * |G (x / Real.sqrt (-t)) - c|
          ≤ 1 * |G (x / Real.sqrt (-t)) - c| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |G (x / Real.sqrt (-t)) - c| := one_mul _
        _ ≤ 16 * C₀ * (T / θ ^ 2) := hGc
    have hcut : |1 - chi (x / (θ / 4))| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [chi_le_one (x / (θ / 4))])]
      linarith [chi_nonneg (x / (θ / 4))]
    have e : bdiff G c lam θ t x = (1 - chi (x / (θ / 4)))
        * ((1 + vstar x * Flam G lam t x - bzero c lam x)
          * (1 + vstar x * Flam G lam t x + bzero c lam x)) := by
      unfold bdiff
      ring
    rw [e, abs_mul, abs_mul]
    have h0 : 0 ≤ 16 * C₀ * (T / θ ^ 2) := by positivity
    calc |1 - chi (x / (θ / 4))| * (|1 + vstar x * Flam G lam t x - bzero c lam x|
          * |1 + vstar x * Flam G lam t x + bzero c lam x|)
        ≤ 1 * (16 * C₀ * (T / θ ^ 2) * (max 1 Mu + 1)) :=
          mul_le_mul hcut (mul_le_mul hdiff hsum (abs_nonneg _) h0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      _ = 16 * C₀ * (max 1 Mu + 1) * (T / θ ^ 2) := by ring

/-! ### The residual for a fixed cut-off radius -/

theorem zpow_raise {ς x₀ : ℝ} (hx₀ : 0 < x₀) (h : x₀ ≤ ς) (m : ℤ) :
    ς ^ m ≤ x₀⁻¹ * ς ^ (m + 1) := by
  have hς : 0 < ς := hx₀.trans_le h
  have e : ς ^ m = ς⁻¹ * ς ^ (m + 1) := by
    rw [zpow_add₀ hς.ne', zpow_one, mul_comm (ς ^ m), ← mul_assoc, inv_mul_cancel₀ hς.ne',
      one_mul]
  rw [e]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hx₀ h) (zpow_nonneg hς.le _)

variable {T : ℝ} {n : ℤ} {M : ℝ} {a ax at' : ℝ → ℝ → ℝ}

/-- A function that vanishes, with its derivatives, for `x < x₀` gains one
order at the cost of the factor `1/x₀`. -/
theorem Osc.raise {x₀ : ℝ} (h : Osc T n M a ax at') (hM : 0 ≤ M) (hx₀ : 0 < x₀)
    (hsupp : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, x < x₀ →
      a t x = 0 ∧ ax t x = 0 ∧ at' t x = 0) :
    Osc T (n + 1) (M / x₀) a ax at' := by
  have key : ∀ (f : ℝ → ℝ → ℝ) (m : ℤ),
      (∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, |f t x| ≤ M * vs t x ^ m) →
      (∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, x < x₀ → f t x = 0) →
      ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, |f t x| ≤ M / x₀ * vs t x ^ (m + 1) := by
    intro f m hb hz t ht x hx
    have hς := vs_pos ht hx
    rcases lt_or_ge x x₀ with hlt | hge
    · rw [hz t ht.2 x hx hlt, abs_zero]
      exact mul_nonneg (div_nonneg hM hx₀.le) (zpow_nonneg hς.le _)
    · have hle : x₀ ≤ vs t x := by
        unfold vs
        linarith [Real.sqrt_nonneg (-t)]
      calc |f t x| ≤ M * vs t x ^ m := hb t ht x hx
        _ ≤ M * (x₀⁻¹ * vs t x ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (zpow_raise hx₀ hle m) hM
        _ = M / x₀ * vs t x ^ (m + 1) := by
          rw [div_eq_mul_inv]
          ring
  refine ⟨key a n h.bound fun t ht x hx hlt => (hsupp t ht x hx hlt).1, h.dx, ?_, h.dt, ?_⟩
  · have h1 := key ax (n - 1) h.dx_bound fun t ht x hx hlt => (hsupp t ht x hx hlt).2.1
    have e : n - 1 + 1 = n + 1 - 1 := by ring
    rwa [e] at h1
  · have h1 := key at' (n - 2) h.dt_bound fun t ht x hx hlt => (hsupp t ht x hx hlt).2.2
    have e : n - 2 + 1 = n + 1 - 2 := by ring
    rwa [e] at h1

/-- **The residual has order `-2` for a fixed cut-off radius**, with the
constant `C/λ`. -/
theorem elam_osc (hP : IsProfile c G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam T : ℝ), 0 < lam → lam ≤ 1 →
    T ≤ (lam / 2) ^ 2 → T ≤ 1 → OscE T (-2) (C / lam) (Elam G lam) := by
  obtain ⟨M₁, hM₁, h₁⟩ := tower_chi 1
  obtain ⟨M₂, hM₂, h₂⟩ := uosc_Ein hP
  obtain ⟨M₃, hM₃, h₃⟩ := uosc_Elam hP
  refine ⟨2 * M₁ * M₂ + 4 * (1 + M₁) * M₃, by positivity, ?_⟩
  intro lam T hlam hlam1 hT hT1
  have hμ : 0 < lam / 2 := by positivity
  have hTl : T ≤ lam ^ 2 := hT.trans (by nlinarith)
  -- the cut-off at the scale `λ/2`
  have hχ := h₁ (lam / 2) T hμ hT 0 zero_lt_one
  have e0 : (0 : ℤ) - ((0 : ℕ) : ℤ) = 0 := by norm_num
  rw [e0] at hχ
  -- the inner part
  obtain ⟨ix, it, hI⟩ := h₂ lam T hlam hTl hT1
  have hin := (hχ.mul hI hM₁ hM₂).oscE
  -- the outer part
  obtain ⟨ex, et, hE⟩ := h₃ lam T hlam hTl hT1
  have hone : Osc T 0 1 (fun _ _ => (1 : ℝ)) (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ht x hx
      rw [zpow_zero, abs_one, mul_one]
    · intro t _ x _
      exact hasDerivWithinAt_const x _ _
    · intro t ht x hx
      rw [abs_zero, one_mul]
      exact zpow_nonneg (vs_pos ht hx).le _
    · intro t _ x _
      exact hasDerivAt_const t _
    · intro t ht x hx
      rw [abs_zero, one_mul]
      exact zpow_nonneg (vs_pos ht hx).le _
  have hq := hone.sub hχ
  have hout := ((hq.mul hE (by positivity) hM₃).cast (by norm_num : (0 : ℤ) + -3 = -3)).raise
    (x₀ := lam / 2) (by positivity) hμ (by
      intro t _ x _ hlt
      have hx1 : x / (lam / 2) < 1 := (div_lt_one hμ).2 hlt
      have c0 : (1 : ℝ) - iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0 = 0 := by
        rw [iteratedDeriv_zero, pow_zero, div_one, chi_of_le hx1.le, sub_self]
      have c1 : (0 : ℝ) - iteratedDeriv (0 + 1) chi (x / (lam / 2)) / (lam / 2) ^ (0 + 1) = 0 := by
        rw [iteratedDeriv_succ_chi_eq_zero 0 (Or.inl hx1), zero_div, sub_zero]
      refine ⟨?_, ?_, ?_⟩
      · show (1 - iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0) * Elam G lam t x = 0
        rw [c0, zero_mul]
      · show (0 - iteratedDeriv (0 + 1) chi (x / (lam / 2)) / (lam / 2) ^ (0 + 1)) * Elam G lam t x
          + (1 - iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0) * ex t x = 0
        rw [c0, c1, zero_mul, zero_mul, add_zero]
      · show ((0 : ℝ) - 0) * Elam G lam t x
          + (1 - iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0) * et t x = 0
        rw [c0, sub_zero, zero_mul, zero_mul, add_zero])
  have e1 : (-3 : ℤ) + 1 = -2 := by norm_num
  rw [e1] at hout
  have e2 : (0 : ℤ) + -2 = -2 := by norm_num
  rw [e2] at hin
  have hsum := hin.add hout.oscE
  refine (hsum.mono ?_).congr_fun fun t ht x hx => ?_
  · -- the constant
    have hlamne : lam ≠ 0 := hlam.ne'
    have h1 : 2 * M₁ * M₂ ≤ 2 * M₁ * M₂ / lam := by
      rw [le_div_iff₀ hlam]
      exact mul_le_of_le_one_right (by positivity) hlam1
    have h2 : 2 * (1 + M₁) * M₃ / (lam / 2) = 4 * (1 + M₁) * M₃ / lam := by
      field_simp
      ring
    rw [h2]
    have h3 : (2 * M₁ * M₂ + 4 * (1 + M₁) * M₃) / lam
        = 2 * M₁ * M₂ / lam + 4 * (1 + M₁) * M₃ / lam := by ring
    rw [h3]
    linarith
  · -- the identity
    show Elam G lam t x
      = iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0 * Ein G t x
        + (1 - iteratedDeriv 0 chi (x / (lam / 2)) / (lam / 2) ^ 0) * Elam G lam t x
    rw [iteratedDeriv_zero, pow_zero, div_one]
    rcases lt_or_ge x lam with hlt | hge
    · rw [Elam_eq_Ein hP hlam ht hx hlt]
      ring
    · have h2 : 2 ≤ x / (lam / 2) := by
        rw [le_div_iff₀ hμ]
        linarith
      rw [chi_of_ge h2]
      ring

end Calabi.Osc
