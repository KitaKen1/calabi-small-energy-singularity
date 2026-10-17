import Calabi.Correction.WindowEstimate
import OAI.Analysis.AncientFlat.Regularity.WithinInterpolation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The uniform zero-data forward estimate (Lemma 4.4 of the manuscript)

For `u_t + a Δ² u = f`, `u(0) = 0`, on a Euclidean space with a positive scale
function `s`, the weighted norms are taken on the windows with centre `x₀`,
scale `q = a₁ s(x₀)` and the whole time interval `[0, R]`:

* `SSource … F f`: the source in the units of the window is bounded by
  `F s(x₀)^w` in the parabolic Hölder norm;
* `SJet … N u u_t`: the jets `Dʲu`, `j ≤ 4`, and `u_t` in the units of the
  window are bounded by `N s(x₀)^w` in the parabolic Hölder norm;
* `SCoeff … K a`: the coefficient in the units of the window.

`outer_estimate`: if the elapsed time `R` is at most a fixed multiple of
`(inf s)⁴`, then `SJet` holds with `N = C F`, and
`|u(t, x)| ≤ C (R / (a₁ s(x))⁴) F s(x)^w`: the solution is small compared with
its size at the scale of the window when the time is short. The constant does
not depend on the scale function, on `inf s` or on `R`.

The proof is the absorption argument of the manuscript: the local initial
Schauder estimate bounds the jets by the source and the supremum of `u`; the
supremum is bounded by the elapsed time times the supremum of `u_t`, which is a
small multiple of the jets.
-/

open Set Filter
open scoped Topology ContDiff Laplacian

namespace Calabi.FlatZero

open OAI OAI.ParabolicInterior OAI.ParabolicInitial OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The weighted bound of the jets on the windows of scale `a₁ s`. -/
def SJet (s : V → ℝ) (a₁ R α w N : ℝ) (u ut : ℝ → V → ℂ) : Prop :=
  ∀ x₀ : V, JetBound α (slab 1 (R / (a₁ * s x₀) ^ 4))
    (windowValue (x₀, 0) (a₁ * s x₀) u) (windowTime (x₀, 0) (a₁ * s x₀) ut) (N * s x₀ ^ w)

/-- The weighted bound of a source on the windows of scale `a₁ s`. -/
def SSource (s : V → ℝ) (a₁ R α w F : ℝ) (f : ℝ → V → ℂ) : Prop :=
  ∀ x₀ : V, HolderBound α (slab 2 (R / (a₁ * s x₀) ^ 4))
    (fun p => windowTime (x₀, 0) (a₁ * s x₀) f p.2 p.1) (F * s x₀ ^ w)

/-- The bound of the coefficient on the windows of scale `a₁ s`. -/
def SCoeff (s : V → ℝ) (a₁ R α K : ℝ) (a : ℝ → V → ℝ) : Prop :=
  ∀ x₀ : V, HolderBound α (slab 2 (R / (a₁ * s x₀) ^ 4))
    (fun p => a (window (x₀, 0) (a₁ * s x₀) p).2 (window (x₀, 0) (a₁ * s x₀) p).1) K

theorem SJet.mono {s : V → ℝ} {a₁ R α w N N' : ℝ} {u ut : ℝ → V → ℂ}
    (h : SJet s a₁ R α w N u ut) (hs : ∀ x, 0 ≤ s x ^ w) (hN : N ≤ N') :
    SJet s a₁ R α w N' u ut := fun x₀ =>
  ⟨fun j hj => ((h x₀).1 j hj).mono (mul_le_mul_of_nonneg_right hN (hs x₀)),
    (h x₀).2.mono (mul_le_mul_of_nonneg_right hN (hs x₀))⟩

/-- The supremum of the solution in terms of the jets and the elapsed time. -/
theorem sup_le_of_sJet {s : V → ℝ} {a₁ R α w N : ℝ} {a : ℝ → V → ℝ} {f u : ℝ → V → ℂ}
    (ha₁ : 0 < a₁) (hs : ∀ x, 0 < s x) (hR : 0 < R) (hu0 : ∀ x, u 0 x = 0)
    (hd : ∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun r => u r x) (utOf a f u t x) (Icc 0 R) t)
    (h : SJet s a₁ R α w N u (utOf a f u)) {t : ℝ} (ht : t ∈ Icc 0 R) (x : V) :
    ‖u t x‖ ≤ R / (a₁ * s x) ^ 4 * (N * s x ^ w) := by
  have hq : 0 < a₁ * s x := mul_pos ha₁ (hs x)
  have hq4 : 0 < (a₁ * s x) ^ 4 := pow_pos hq 4
  have hbound : ∀ τ ∈ Icc (0 : ℝ) R, ‖utOf a f u τ x‖ ≤ N * s x ^ w / (a₁ * s x) ^ 4 := by
    intro τ hτ
    have hmem : ((0 : V), τ / (a₁ * s x) ^ 4) ∈ slab (V := V) 1 (R / (a₁ * s x) ^ 4) :=
      ⟨by simp, div_nonneg hτ.1 hq4.le, div_le_div_of_nonneg_right hτ.2 hq4.le⟩
    have h1 : ‖windowTime (x, 0) (a₁ * s x) (utOf a f u) (τ / (a₁ * s x) ^ 4) 0‖
        ≤ N * s x ^ w := (h x).2.1 ((0 : V), τ / (a₁ * s x) ^ 4) hmem
    have e : windowTime (x, 0) (a₁ * s x) (utOf a f u) (τ / (a₁ * s x) ^ 4) 0
        = (a₁ * s x) ^ 4 • utOf a f u τ x := by
      show (a₁ * s x) ^ 4 • utOf a f u (0 + (a₁ * s x) ^ 4 * (τ / (a₁ * s x) ^ 4))
        (x + (a₁ * s x) • (0 : V)) = _
      rw [mul_div_cancel₀ τ hq4.ne', zero_add, smul_zero, add_zero]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hq4] at h1
    rw [le_div_iff₀ hq4]
    linarith
  have hmv := (convex_Icc (0 : ℝ) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r => u r x) (fun τ hτ => hd τ hτ x) hbound ⟨le_rfl, hR.le⟩ ht
  simp only [hu0, sub_zero, Real.norm_eq_abs] at hmv
  have hN0 : 0 ≤ N * s x ^ w / (a₁ * s x) ^ 4 :=
    (norm_nonneg _).trans (hbound 0 ⟨le_rfl, hR.le⟩)
  calc ‖u t x‖ ≤ N * s x ^ w / (a₁ * s x) ^ 4 * |t| := hmv
    _ ≤ N * s x ^ w / (a₁ * s x) ^ 4 * R := by
        refine mul_le_mul_of_nonneg_left ?_ hN0
        rw [abs_of_nonneg ht.1]
        exact ht.2
    _ = R / (a₁ * s x) ^ 4 * (N * s x ^ w) := by ring

/-- The supremum of the solution on a window, in terms of the jets and the
elapsed time. -/
theorem window_sup_le {s : V → ℝ} {a₁ R α w N cw smin : ℝ} {a : ℝ → V → ℝ} {f u : ℝ → V → ℂ}
    (ha₁ : 0 < a₁) (hsmin : 0 < smin) (hsm : ∀ x, smin ≤ s x) (hsw : ∀ x, 0 ≤ s x ^ w)
    (hcomp : ∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ^ w ≤ cw * s x₀ ^ w)
    (hR : 0 < R) (hN : 0 ≤ N) (hu0 : ∀ x, u 0 x = 0)
    (hd : ∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun r => u r x) (utOf a f u t x) (Icc 0 R) t)
    (hNj : SJet s a₁ R α w N u (utOf a f u)) (x₀ : V) {p : V × ℝ}
    (hp : p ∈ slab 2 (R / (a₁ * s x₀) ^ 4)) :
    ‖windowValue (x₀, 0) (a₁ * s x₀) u p.2 p.1‖
      ≤ R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)) := by
  have hspos : ∀ x, 0 < s x := fun x => hsmin.trans_le (hsm x)
  have hqpos : 0 < a₁ * s x₀ := mul_pos ha₁ (hspos x₀)
  have hm4 : 0 < (a₁ * smin) ^ 4 := pow_pos (mul_pos ha₁ hsmin) 4
  have hmem := window_mem_slab (x₀ := x₀) hqpos hp
  have h1 := sup_le_of_sJet ha₁ hspos hR hu0 hd hNj hmem (window (x₀, 0) (a₁ * s x₀) p).1
  have hx : ‖(window (x₀, 0) (a₁ * s x₀) p).1 - x₀‖ < 2 * (a₁ * s x₀) := by
    show ‖x₀ + (a₁ * s x₀) • p.1 - x₀‖ < 2 * (a₁ * s x₀)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
    have := hp.1
    nlinarith [hqpos]
  have h2 := hcomp x₀ _ hx
  have h3 : R / (a₁ * s (window (x₀, 0) (a₁ * s x₀) p).1) ^ 4 ≤ R / (a₁ * smin) ^ 4 :=
    div_le_div_of_nonneg_left hR.le hm4 (pow_le_pow_left₀ (mul_pos ha₁ hsmin).le
      (mul_le_mul_of_nonneg_left (hsm _) ha₁.le) 4)
  calc ‖windowValue (x₀, 0) (a₁ * s x₀) u p.2 p.1‖
      ≤ R / (a₁ * s (window (x₀, 0) (a₁ * s x₀) p).1) ^ 4
        * (N * s (window (x₀, 0) (a₁ * s x₀) p).1 ^ w) := h1
    _ ≤ R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)) :=
        mul_le_mul h3 (mul_le_mul_of_nonneg_left h2 hN)
          (mul_nonneg hN (hsw _)) (div_nonneg hR.le hm4.le)

/-- **Lemma 4.4 on a flat space**: the uniform zero-data forward estimate. -/
theorem outer_estimate (α κ K : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ) (hK : 0 ≤ K) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (s : V → ℝ) (a₁ w cw mw smin R : ℝ), 0 < a₁ → 0 < smin →
      0 < mw → 1 ≤ cw → (∀ x, smin ≤ s x) → (∀ x, a₁ * s x ≤ 1) → (∀ x, mw ≤ s x ^ w) →
      (∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ^ w ≤ cw * s x₀ ^ w) →
      0 < R → R ≤ (a₁ * smin) ^ 4 / (2 * C₀ * cw) →
      ∀ (a : ℝ → V → ℝ) (f u : ℝ → V → ℂ),
      (∀ t, ContDiff ℝ 4 (u t)) → (∀ x, u 0 x = 0) →
      (∀ t ∈ Icc 0 R, ∀ x,
        HasDerivWithinAt (fun r => u r x) (utOf a f u t x) (Icc 0 R) t) →
      (∃ M : ℝ, 0 ≤ M ∧ JetBound α {p : V × ℝ | p.2 ∈ Icc 0 R} u (utOf a f u) M) →
      SCoeff s a₁ R α K a → (∀ t x, κ ≤ a t x) →
      ∀ F : ℝ, 0 < F → SSource s a₁ R α w F f →
      SJet s a₁ R α w ((2 * C₀ + 1) * F) u (utOf a f u) ∧
        ∀ t ∈ Icc 0 R, ∀ x, ‖u t x‖ ≤ R / (a₁ * s x) ^ 4 * ((2 * C₀ + 1) * F * s x ^ w) := by
  obtain ⟨C, hC, HW⟩ := window_initial_estimate (V := V) α κ K hα hα1 hκ hK
  refine ⟨C + 1, by linarith, ?_⟩
  intro s a₁ w cw mw smin R ha₁ hsmin hmw hcw hsm hq1 hmws hcomp hR hRη a f u hs hu0 hd hj
    hcoef hκa F hF hsrc
  have hC₀ : (0 : ℝ) < C + 1 := by linarith
  have hspos : ∀ x, 0 < s x := fun x => hsmin.trans_le (hsm x)
  have hswpos : ∀ x, 0 < s x ^ w := fun x => hmw.trans_le (hmws x)
  have hqpos : ∀ x, 0 < a₁ * s x := fun x => mul_pos ha₁ (hspos x)
  have hm4 : 0 < (a₁ * smin) ^ 4 := pow_pos (mul_pos ha₁ hsmin) 4
  have hcwpos : 0 < cw := by linarith
  have hmw0 : mw ≠ 0 := hmw.ne'
  have hden : 0 < 2 * (C + 1) * cw := by positivity
  -- `R ≤ q⁴` on every window
  have hRm : R ≤ (a₁ * smin) ^ 4 := by
    refine hRη.trans (div_le_self hm4.le ?_)
    nlinarith [mul_nonneg hC.le hcwpos.le]
  have hRq : ∀ x, R ≤ (a₁ * s x) ^ 4 := fun x =>
    hRm.trans (pow_le_pow_left₀ (mul_pos ha₁ hsmin).le
      (mul_le_mul_of_nonneg_left (hsm x) ha₁.le) 4)
  -- the smallness `(C + 1) cw R / (a₁ smin)⁴ ≤ 1/2`
  have hsmall : (C + 1) * cw * (R / (a₁ * smin) ^ 4) ≤ 1 / 2 := by
    have h1 : R / (a₁ * smin) ^ 4 ≤ 1 / (2 * (C + 1) * cw) := by
      rw [div_le_div_iff₀ hm4 hden]
      have h2 := (le_div_iff₀ hden).1 hRη
      linarith
    calc (C + 1) * cw * (R / (a₁ * smin) ^ 4)
        ≤ (C + 1) * cw * (1 / (2 * (C + 1) * cw)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 2 := by
          rw [mul_one_div, div_eq_div_iff hden.ne' (by norm_num)]
          ring
  -- one step of the absorption
  have step : ∀ N : ℝ, 0 ≤ N → SJet s a₁ R α w N u (utOf a f u) →
      SJet s a₁ R α w ((C + 1) * F + N / 2) u (utOf a f u) := by
    intro N hN hNj x₀
    have hsx : 0 < s x₀ ^ w := hswpos x₀
    have hsup : ∀ p ∈ slab (V := V) 2 (R / (a₁ * s x₀) ^ 4),
        ‖windowValue (x₀, 0) (a₁ * s x₀) u p.2 p.1‖
          ≤ R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)) := fun p hp =>
      window_sup_le ha₁ hsmin hsm (fun x => (hswpos x).le) hcomp hR hN hu0 hd hNj x₀ hp
    have hU0 : 0 ≤ R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)) :=
      mul_nonneg (div_nonneg hR.le hm4.le) (mul_nonneg hN (mul_nonneg hcwpos.le hsx.le))
    have hF0 : 0 ≤ F * s x₀ ^ w := mul_nonneg hF.le (hswpos x₀).le
    have h := HW R hR a f u hs hu0 hd hj x₀ (a₁ * s x₀) (hqpos x₀) (hq1 x₀) (hRq x₀)
      (hcoef x₀) (fun p _ => hκa _ _) (F * s x₀ ^ w)
      (R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w))) hF0 hU0 (hsrc x₀) hsup
    have hle : C * (F * s x₀ ^ w + R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)))
        ≤ ((C + 1) * F + N / 2) * s x₀ ^ w := by
      have hw0 := (hswpos x₀).le
      have h1 : C * (R / (a₁ * smin) ^ 4 * (N * (cw * s x₀ ^ w)))
          ≤ (C + 1) * cw * (R / (a₁ * smin) ^ 4) * (N * s x₀ ^ w) := by
        have h2 : 0 ≤ cw * (R / (a₁ * smin) ^ 4) * (N * s x₀ ^ w) :=
          mul_nonneg (mul_nonneg hcwpos.le (div_nonneg hR.le hm4.le)) (mul_nonneg hN hsx.le)
        nlinarith
      have h3 : (C + 1) * cw * (R / (a₁ * smin) ^ 4) * (N * s x₀ ^ w)
          ≤ 1 / 2 * (N * s x₀ ^ w) :=
        mul_le_mul_of_nonneg_right hsmall (mul_nonneg hN hsx.le)
      have h4 : 0 ≤ F * s x₀ ^ w := hF0
      nlinarith
    exact ⟨fun j hj => (h.1 j hj).mono hle, h.2.mono hle⟩
  -- a first finite bound
  obtain ⟨M, hM, hJ⟩ := hj
  have hN₀ : SJet s a₁ R α w (M / mw) u (utOf a f u) := by
    intro x₀
    have hmaps : MapsTo (window (x₀, 0) (a₁ * s x₀)) (slab 1 (R / (a₁ * s x₀) ^ 4))
        {p : V × ℝ | p.2 ∈ Icc 0 R} := fun p hp => window_mem_slab (hqpos x₀) hp
    have h := window_jet_bound hα.le hM (hqpos x₀) (hq1 x₀) (x₀, 0) u (utOf a f u) hs hJ hmaps
    have hle : M ≤ M / mw * s x₀ ^ w := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hmw]
      exact mul_le_mul_of_nonneg_left (hmws x₀) hM
    exact ⟨fun j hj => (h.1 j hj).mono hle, h.2.mono hle⟩
  have hN₀0 : 0 ≤ M / mw := div_nonneg hM hmw.le
  have iter : ∀ k : ℕ, SJet s a₁ R α w (2 * (C + 1) * F + M / mw / 2 ^ k) u (utOf a f u) := by
    intro k
    induction k with
    | zero =>
      refine hN₀.mono (fun x => (hswpos x).le) ?_
      have : 0 ≤ 2 * (C + 1) * F := by positivity
      simp only [pow_zero, div_one]
      linarith
    | succ k ih =>
      have h0 : 0 ≤ 2 * (C + 1) * F + M / mw / 2 ^ k := by positivity
      have h := step _ h0 ih
      refine h.mono (fun x => (hswpos x).le) (le_of_eq ?_)
      rw [pow_succ]
      field_simp
      ring
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / mw / F) (one_lt_two)
  have hkF : M / mw / 2 ^ k ≤ F := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_le_iff₀ h2k]
    have := (div_lt_iff₀ hF).1 hk
    linarith
  have hfin : SJet s a₁ R α w ((2 * (C + 1) + 1) * F) u (utOf a f u) :=
    (iter k).mono (fun x => (hswpos x).le) (by linarith)
  refine ⟨hfin, fun t ht x => ?_⟩
  have h := sup_le_of_sJet ha₁ hspos hR hu0 hd hfin ht x
  exact h

/-- **Lemma 4.5 of the manuscript, (4.16), on a flat space**: on a short time
interval the jets of order at most three of the zero-data solution are small.
The bound is `(ε + C_ε c_w η) (2 C₀ + 1) F s(x₀)^w` with `η = R / (a₁ inf s)⁴`. -/
theorem outer_lower_small (α κ K : ℝ) (hα : 0 < α) (hα1 : α < 1) (hκ : 0 < κ) (hK : 0 ≤ K) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (s : V → ℝ) (a₁ w cw mw smin R : ℝ), 0 < a₁ → 0 < smin →
      0 < mw → 1 ≤ cw → (∀ x, smin ≤ s x) → (∀ x, a₁ * s x ≤ 1) → (∀ x, mw ≤ s x ^ w) →
      (∀ x₀ x, ‖x - x₀‖ < 2 * (a₁ * s x₀) → s x ^ w ≤ cw * s x₀ ^ w) →
      0 < R → R ≤ (a₁ * smin) ^ 4 / (2 * C₀ * cw) →
      ∀ (a : ℝ → V → ℝ) (f u : ℝ → V → ℂ),
      (∀ t, ContDiff ℝ 4 (u t)) → (∀ x, u 0 x = 0) →
      (∀ t ∈ Icc 0 R, ∀ x,
        HasDerivWithinAt (fun r => u r x) (utOf a f u t x) (Icc 0 R) t) →
      (∃ M : ℝ, 0 ≤ M ∧ JetBound α {p : V × ℝ | p.2 ∈ Icc 0 R} u (utOf a f u) M) →
      SCoeff s a₁ R α K a → (∀ t x, κ ≤ a t x) →
      ∀ F : ℝ, 0 < F → SSource s a₁ R α w F f →
      ∀ (x₀ : V) (j : ℕ), j ≤ 3 →
        HolderBound α {p : V × ℝ | ‖p.1‖ < 1 / 2 ∧ p.2 ∈ Icc 0 (R / (a₁ * s x₀) ^ 4)}
          (fun p => iteratedFDeriv ℝ j (windowValue (x₀, 0) (a₁ * s x₀) u p.2) p.1)
          ((ε + Cε * cw * (R / (a₁ * smin) ^ 4)) * ((2 * C₀ + 1) * F) * s x₀ ^ w) := by
  obtain ⟨C₀, hC₀, HE⟩ := outer_estimate (V := V) α κ K hα hα1 hκ hK
  refine ⟨C₀, hC₀, fun ε hε => ?_⟩
  obtain ⟨CI, hCI, HI⟩ := within_lower_jet_interpolation (V := V) (E := ℂ) α ε (1 / 2) 1 hα hα1
    hε (by norm_num)
  refine ⟨CI, hCI, ?_⟩
  intro s a₁ w cw mw smin R ha₁ hsmin hmw hcw hsm hq1 hmws hcomp hR hRη a f u hs hu0 hd hj
    hcoef hκa F hF hsrc x₀ j hj3
  obtain ⟨hJ, -⟩ := HE s a₁ w cw mw smin R ha₁ hsmin hmw hcw hsm hq1 hmws hcomp hR hRη a f u
    hs hu0 hd hj hcoef hκa F hF hsrc
  have hspos : ∀ x, 0 < s x := fun x => hsmin.trans_le (hsm x)
  have hswpos : ∀ x, 0 < s x ^ w := fun x => hmw.trans_le (hmws x)
  have hqpos : 0 < a₁ * s x₀ := mul_pos ha₁ (hspos x₀)
  have hq4 : 0 < (a₁ * s x₀) ^ 4 := pow_pos hqpos 4
  have hm4 : 0 < (a₁ * smin) ^ 4 := pow_pos (mul_pos ha₁ hsmin) 4
  have hh : 0 < R / (a₁ * s x₀) ^ 4 := div_pos hR hq4
  have hN : 0 ≤ (2 * C₀ + 1) * F := by positivity
  have hM0 : 0 ≤ (2 * C₀ + 1) * F * s x₀ ^ w := mul_nonneg hN (hswpos x₀).le
  have hcwpos : 0 < cw := by linarith
  have hU0 : 0 ≤ R / (a₁ * smin) ^ 4 * ((2 * C₀ + 1) * F * (cw * s x₀ ^ w)) :=
    mul_nonneg (div_nonneg hR.le hm4.le)
      (mul_nonneg hN (mul_nonneg hcwpos.le (hswpos x₀).le))
  have hslab1 : ∀ (t : ℝ), t ∈ Icc 0 (R / (a₁ * s x₀) ^ 4) → ∀ y : V, ‖y‖ < 1 →
      ((y, t) : V × ℝ) ∈ slab (V := V) 1 (R / (a₁ * s x₀) ^ 4) := fun t ht y hy => ⟨hy, ht⟩
  have h := HI (windowValue (x₀, 0) (a₁ * s x₀) u)
    (windowTime (x₀, 0) (a₁ * s x₀) (utOf a f u)) 0 (R / (a₁ * s x₀) ^ 4) hh
    (R / (a₁ * smin) ^ 4 * ((2 * C₀ + 1) * F * (cw * s x₀ ^ w)))
    ((2 * C₀ + 1) * F * s x₀ ^ w) hU0 hM0
    (fun t _ => windowValue_contDiff (x₀, 0) (a₁ * s x₀) u hs t)
    (fun t ht y hy => window_hasDerivWithinAt (x₀ := x₀) hqpos hd (hslab1 t ht y hy))
    (fun t ht y hy => (hJ x₀).2.1 (y, t) (hslab1 t ht y hy))
    (fun t ht y hy => window_sup_le ha₁ hsmin hsm (fun x => (hswpos x).le) hcomp hR hN hu0 hd
      hJ x₀ (p := (y, t)) ⟨hy.trans (by norm_num), ht⟩)
    (fun t ht y hy => ((hJ x₀).1 4 le_rfl).1 (y, t) (hslab1 t ht y hy)) j hj3
  refine h.mono (le_of_eq ?_)
  ring

end Calabi.FlatZero
