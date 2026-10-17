import Calabi.Correction.ProfileOsc
import Calabi.Correction.Factor

/-!
# Scaled bounds for the localized profile

The localized profile `F_λ = χ(x/λ) F` of Section 6 of the manuscript in the
calculus of `Osc.lean`, for `T ≤ λ²` (so that `ρ ≤ λ` and the cut-off varies
at the local scale):

* `tower_chi`: the derivatives `λ⁻ʲ χ^{(j)}(x/λ)` have the orders `-j`;
* `tower_Flam`: the tower of `F_λ` (the Leibniz sums `flamJet`), of order `-1`;
* `Tower.D_eq`: the entries of a tower are the derivatives on `[0, 1]`;
* `oscE_AFlam`: `A F_λ` has order `-3`, uniformly in `λ` and `T`
  (Lemma 6.2: `A F_λ = Osc(σ⁻⁶)`).
-/

open Set Filter
open scoped Topology ContDiff

namespace Calabi.Osc

open Calabi.Flat Calabi.Radial

variable {c : ℝ} {G : ℝ → ℝ}

/-! ### Derivatives of the cut-off -/

theorem contDiff_iteratedDeriv_chi : ∀ j : ℕ, ContDiff ℝ ∞ (iteratedDeriv j chi)
  | 0 => by
    rw [iteratedDeriv_zero]
    exact contDiff_chi
  | j + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.1 (contDiff_iteratedDeriv_chi j)).2

theorem hasDerivAt_iteratedDeriv_chi (j : ℕ) (u : ℝ) :
    HasDerivAt (iteratedDeriv j chi) (iteratedDeriv (j + 1) chi u) u := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_iteratedDeriv_chi j).differentiable (by simp)).differentiableAt.hasDerivAt

theorem iteratedDeriv_succ_chi_eq_zero (j : ℕ) :
    ∀ {x : ℝ}, x < 1 ∨ 2 < x → iteratedDeriv (j + 1) chi x = 0 := by
  induction j with
  | zero =>
    intro x hx
    rw [zero_add, iteratedDeriv_one]
    exact deriv_chi_eq_zero hx
  | succ j ih =>
    intro x hx
    have he : iteratedDeriv (j + 1) chi =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      rcases hx with h | h
      · filter_upwards [Iio_mem_nhds h] with y hy using ih (Or.inl hy)
      · filter_upwards [Ioi_mem_nhds h] with y hy using ih (Or.inr hy)
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasDerivAt_const x (0 : ℝ)).deriv

theorem iteratedDeriv_chi_bound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |iteratedDeriv j chi x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_iteratedDeriv_chi j).continuous.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 ⟨le_rfl, by norm_num⟩)
  refine ⟨B + 1, by linarith, fun x => ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · have h := hB x hx
    rw [Real.norm_eq_abs] at h
    linarith
  · have hx' : x < 1 ∨ 2 < x := by
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      exact hx ⟨hcon.1, hcon.2⟩
    cases j with
    | zero =>
      rw [iteratedDeriv_zero]
      exact (abs_chi_le x).trans (by linarith)
    | succ j =>
      rw [iteratedDeriv_succ_chi_eq_zero j hx', abs_zero]
      linarith

/-- The derivatives of the scaled cut-off in the scale `ς`, when `ρ ≤ λ`. -/
theorem chi_scaled_bound (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 →
    ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      |iteratedDeriv i chi (x / lam) / lam ^ i| ≤ B * vs t x ^ (-(i : ℤ)) := by
  obtain ⟨B, hB, hb⟩ := iteratedDeriv_chi_bound i
  refine ⟨B * 3 ^ i, by positivity, fun lam T hlam hT t ht x hx => ?_⟩
  have hς := vs_pos ht hx
  have hli : 0 < lam ^ i := pow_pos hlam i
  have hςi : 0 < vs t x ^ i := pow_pos hς i
  rw [abs_div, abs_of_pos hli, zpow_neg, zpow_natCast]
  by_cases hz : iteratedDeriv i chi (x / lam) = 0
  · rw [hz, abs_zero, zero_div]
    exact mul_nonneg (by positivity) (inv_nonneg.2 hςi.le)
  · -- either `i = 0`, or `x ≤ 2λ` and then `ς ≤ 3λ`
    have hςle : vs t x ^ i ≤ 3 ^ i * lam ^ i := by
      cases i with
      | zero => simp
      | succ i =>
        have hx2 : x / lam ≤ 2 := by
          by_contra hcon
          exact hz (iteratedDeriv_succ_chi_eq_zero i (Or.inr (not_le.1 hcon)))
        have hxl : x ≤ 2 * lam := by rwa [div_le_iff₀ hlam] at hx2
        have hρ : Real.sqrt (-t) ≤ lam := by
          have h1 : Real.sqrt (-t) ≤ Real.sqrt (lam ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [ht.1])
          rwa [Real.sqrt_sq hlam.le] at h1
        have hv : vs t x ≤ 3 * lam := by
          unfold vs
          linarith
        rw [← mul_pow]
        exact pow_le_pow_left₀ hς.le hv _
    have h1 : B * vs t x ^ i ≤ B * (3 ^ i * lam ^ i) := mul_le_mul_of_nonneg_left hςle hB
    calc |iteratedDeriv i chi (x / lam)| / lam ^ i ≤ B / lam ^ i :=
          div_le_div_of_nonneg_right (hb _) hli.le
      _ ≤ B * 3 ^ i * (vs t x ^ i)⁻¹ := by
        rw [div_le_iff₀ hli]
        calc B = B * vs t x ^ i * (vs t x ^ i)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hςi.ne', mul_one]
          _ ≤ B * (3 ^ i * lam ^ i) * (vs t x ^ i)⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hςi.le)
          _ = B * 3 ^ i * (vs t x ^ i)⁻¹ * lam ^ i := by ring

/-- **The tower of the scaled cut-off** `χ(x/λ)`, of order zero, for `T ≤ λ²`. -/
theorem tower_chi (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 →
    Tower T 0 C K (fun j _ x => iteratedDeriv j chi (x / lam) / lam ^ j) (fun _ _ _ => 0) := by
  choose B hB hb using chi_scaled_bound
  refine ⟨∑ i ∈ Finset.range (K + 1), B i, Finset.sum_nonneg fun i _ => hB i,
    fun lam T hlam hT j hj => ?_⟩
  have hBj : B j ≤ ∑ i ∈ Finset.range (K + 1), B i :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_range.2 (by omega))
  have hBj1 : B (j + 1) ≤ ∑ i ∈ Finset.range (K + 1), B i :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_range.2 (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    have e : (0 : ℤ) - j = -(j : ℤ) := by ring
    rw [e]
    exact (hb j lam T hlam hT t ht x hx).trans
      (mul_le_mul_of_nonneg_right hBj (zpow_nonneg (vs_pos ht hx).le _))
  · intro t _ x _
    have h1 := (hasDerivAt_iteratedDeriv_chi j (x / lam)).comp x
      ((hasDerivAt_id' x).div_const lam)
    have h2 := h1.div_const (lam ^ j)
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    show iteratedDeriv (j + 1) chi (x / lam) * (1 / lam) / lam ^ j
      = iteratedDeriv (j + 1) chi (x / lam) / lam ^ (j + 1)
    rw [pow_succ, mul_one_div, div_div, mul_comm lam (lam ^ j)]
  · intro t ht x hx
    have e : (0 : ℤ) - j - 1 = -((j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e]
    exact (hb (j + 1) lam T hlam hT t ht x hx).trans
      (mul_le_mul_of_nonneg_right hBj1 (zpow_nonneg (vs_pos ht hx).le _))
  · intro t _ x _
    exact hasDerivAt_const t _
  · intro t ht x hx
    rw [abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => hB i) (zpow_nonneg (vs_pos ht hx).le _)

/-! ### The tower of the localized profile -/

/-- The Leibniz sums for the `x`-derivatives of `F_λ = χ(x/λ) F`. -/
noncomputable def flamJet (G : ℝ → ℝ) (lam : ℝ) : ℕ → ℝ → ℝ → ℝ :=
  tprod (fun j _ x => iteratedDeriv j chi (x / lam) / lam ^ j)
    (fun j t x => iteratedDeriv j (Fss G t) x)

/-- The time derivatives of the Leibniz sums. -/
noncomputable def flamJetT (G : ℝ → ℝ) (lam : ℝ) : ℕ → ℝ → ℝ → ℝ :=
  tprodT (fun j _ x => iteratedDeriv j chi (x / lam) / lam ^ j) (fun _ _ _ => 0)
    (fun j t x => iteratedDeriv j (Fss G t) x)
    (fun j t x => iteratedDeriv (j + 1) G (x / Real.sqrt (-t)) / (2 * Real.sqrt (-t) ^ (j + 3)))

theorem flamJet_zero (G : ℝ → ℝ) (lam t x : ℝ) : flamJet G lam 0 t x = Flam G lam t x := by
  unfold flamJet Flam
  rw [tprod_zero, iteratedDeriv_zero, iteratedDeriv_zero, pow_zero, div_one]

/-- **The tower of the localized profile**, of order `-1`, uniformly in `λ`
and `T ≤ λ²`. -/
theorem tower_Flam (hP : IsProfile c G) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 →
      Tower T (-1) C K (flamJet G lam) (flamJetT G lam) := by
  obtain ⟨C1, hC1, h1⟩ := tower_chi K
  obtain ⟨C2, hC2, h2⟩ := tower_Fss hP K
  refine ⟨2 ^ (K + 1) * C1 * C2, by positivity, fun lam T hlam hT => ?_⟩
  exact ((h1 lam T hlam hT).mul (h2 T) hC1 hC2).cast (by norm_num)

/-- The entries of a tower are the derivatives on `[0, 1]`. -/
theorem Tower.D_eq {T : ℝ} {n : ℤ} {M : ℝ} {K : ℕ} {a da : ℕ → ℝ → ℝ → ℝ}
    (h : Tower T n M K a da) (hK : 4 ≤ K) {t : ℝ} (ht : t < 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, D (a 0 t) x = a 1 t x ∧ D (D (a 0 t)) x = a 2 t x ∧
      D (D (D (a 0 t))) x = a 3 t x ∧ D (D (D (D (a 0 t)))) x = a 4 t x := by
  have ud := uniqueDiffOn_Icc_zero_one
  have e1 : ∀ x ∈ Icc (0 : ℝ) 1, D (a 0 t) x = a 1 t x := fun x hx =>
    ((h 0 (by omega)).dx t ht x hx).derivWithin (ud x hx)
  have e2 : ∀ x ∈ Icc (0 : ℝ) 1, D (D (a 0 t)) x = a 2 t x := fun x hx =>
    (derivWithin_congr e1 (e1 x hx)).trans
      (((h 1 (by omega)).dx t ht x hx).derivWithin (ud x hx))
  have e3 : ∀ x ∈ Icc (0 : ℝ) 1, D (D (D (a 0 t))) x = a 3 t x := fun x hx =>
    (derivWithin_congr e2 (e2 x hx)).trans
      (((h 2 (by omega)).dx t ht x hx).derivWithin (ud x hx))
  have e4 : ∀ x ∈ Icc (0 : ℝ) 1, D (D (D (D (a 0 t)))) x = a 4 t x := fun x hx =>
    (derivWithin_congr e3 (e3 x hx)).trans
      (((h 3 (by omega)).dx t ht x hx).derivWithin (ud x hx))
  exact fun x hx => ⟨e1 x hx, e2 x hx, e3 x hx, e4 x hx⟩

/-! ### Polynomial coefficients -/

theorem oscE_one {T : ℝ} : OscE T 0 1 (fun _ _ => (1 : ℝ)) := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    rw [zpow_zero, abs_one, mul_one]
  · intro t _ x _
    exact hasDerivWithinAt_const x _ 1
  · intro t ht x hx
    rw [abs_zero, one_mul]
    exact zpow_nonneg (vs_pos ht hx).le _
  · intro t _ x _
    exact hasDerivAt_const t 1
  · intro t ht x hx
    rw [abs_zero, one_mul]
    exact zpow_nonneg (vs_pos ht hx).le _

theorem abs_pol_le (a0 a1 a2 a3 a4 : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |pol a0 a1 a2 a3 a4 x| ≤ |a0| + |a1| + |a2| + |a3| + |a4| := by
  have h1 : |a1 * x| ≤ |a1| := by
    rw [abs_mul, abs_of_nonneg hx.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hx.2
  have hp : ∀ k : ℕ, ∀ a : ℝ, |a * x ^ k| ≤ |a| := by
    intro k a
    rw [abs_mul, abs_of_nonneg (pow_nonneg hx.1 k)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx.1 hx.2)
  unfold pol
  calc |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4|
      ≤ |a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3| + |a4 * x ^ 4| := abs_add_le _ _
    _ ≤ |a0 + a1 * x + a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ |a0 + a1 * x| + |a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ |a0| + |a1 * x| + |a2 * x ^ 2| + |a3 * x ^ 3| + |a4 * x ^ 4| :=
      add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ |a0| + |a1| + |a2| + |a3| + |a4| := by
      have := hp 2 a2
      have := hp 3 a3
      have := hp 4 a4
      linarith

/-- A polynomial of degree at most four has order zero. -/
theorem oscE_pol {T : ℝ} (hT : T ≤ 1) (a0 a1 a2 a3 a4 : ℝ) :
    OscE T 0 (4 * (|a0| + |a1| + |a2| + |a3| + |a4|) * 2)
      (fun _ x => pol a0 a1 a2 a3 a4 x) := by
  have hS : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, vs t x ≤ 2 := fun t ht x hx =>
    vs_le hT ht hx
  have hsum : 0 ≤ |a0| + |a1| + |a2| + |a3| + |a4| := by positivity
  refine OscE.of_x (p' := fun x => pol a1 (2 * a2) (3 * a3) (4 * a4) 0 x) (by positivity)
    (by norm_num) hS (fun x _ => (hasDerivAt_pol a0 a1 a2 a3 a4 x).hasDerivWithinAt)
    (fun x hx => (abs_pol_le a0 a1 a2 a3 a4 hx).trans (by linarith)) (fun x hx => ?_)
  refine (abs_pol_le a1 (2 * a2) (3 * a3) (4 * a4) 0 hx).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_zero]
  norm_num
  nlinarith [abs_nonneg a0, abs_nonneg a1, abs_nonneg a2, abs_nonneg a3, abs_nonneg a4]

/-- A power of the coordinate. -/
theorem oscE_xpow {T : ℝ} : ∀ k : ℕ, OscE T k (2 ^ k) (fun _ x => x ^ k)
  | 0 => by
    have h := oscE_one (T := T)
    have e : (fun (_ : ℝ) (x : ℝ) => x ^ 0) = fun _ _ => (1 : ℝ) := by
      funext t x
      rw [pow_zero]
    rw [e, pow_zero]
    exact h
  | k + 1 => by
    have h := ((oscE_xpow (T := T) k).mul OscE.coord (by positivity) zero_le_one).cast
      (show ((k : ℕ) : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring)
    have e : (fun (_ : ℝ) (x : ℝ) => x ^ (k + 1)) = fun _ x => x ^ k * x := by
      funext t x
      rw [pow_succ]
    rw [e]
    refine h.mono (le_of_eq ?_)
    rw [pow_succ]
    ring

/-- A monomial times a polynomial times a function of order `n`. -/
theorem OscE.term {T : ℝ} {n : ℤ} {M : ℝ} {J : ℝ → ℝ → ℝ} (hJ : OscE T n M J) (hT : T ≤ 1)
    (hM : 0 ≤ M) (k : ℕ) (a0 a1 a2 a3 a4 : ℝ) :
    OscE T (n + k) (2 * (2 * 2 ^ k * (4 * (|a0| + |a1| + |a2| + |a3| + |a4|) * 2)) * M)
      (fun t x => x ^ k * pol a0 a1 a2 a3 a4 x * J t x) := by
  have hsum : 0 ≤ |a0| + |a1| + |a2| + |a3| + |a4| := by positivity
  have h1 := ((oscE_xpow (T := T) k).mul (oscE_pol hT a0 a1 a2 a3 a4) (by positivity)
    (by positivity)).mul hJ (by positivity) hM
  exact h1.cast (by ring)

/-! ### Bounds that are uniform in the cut-off radius and the time -/

/-- `c lam` has order `n` with a constant that does not depend on the cut-off
radius `λ` or on the time `T ≤ min(λ², 1)`. -/
def UOsc (n : ℤ) (c : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → T ≤ 1 → OscE T n M (c lam)

section Uniform

variable {n n' : ℤ} {a b : ℝ → ℝ → ℝ → ℝ}

theorem UOsc.cast (h : UOsc n a) (e : n = n') : UOsc n' a := e ▸ h

theorem UOsc.congr (h : UOsc n a)
    (hc : ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, b lam t x = a lam t x) :
    UOsc n b := by
  obtain ⟨M, hM, h⟩ := h
  exact ⟨M, hM, fun lam T hlam hT hT1 => (h lam T hlam hT hT1).congr_fun (hc lam hlam)⟩

theorem UOsc.add (h : UOsc n a) (h' : UOsc n b) :
    UOsc n (fun lam t x => a lam t x + b lam t x) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨M', hM', h'⟩ := h'
  exact ⟨M + M', add_nonneg hM hM', fun lam T hlam hT hT1 =>
    (h lam T hlam hT hT1).add (h' lam T hlam hT hT1)⟩

theorem UOsc.sub (h : UOsc n a) (h' : UOsc n b) :
    UOsc n (fun lam t x => a lam t x - b lam t x) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨M', hM', h'⟩ := h'
  exact ⟨M + M', add_nonneg hM hM', fun lam T hlam hT hT1 =>
    (h lam T hlam hT hT1).sub (h' lam T hlam hT hT1)⟩

theorem UOsc.neg (h : UOsc n a) : UOsc n (fun lam t x => -a lam t x) := by
  obtain ⟨M, hM, h⟩ := h
  exact ⟨M, hM, fun lam T hlam hT hT1 => (h lam T hlam hT hT1).neg⟩

theorem UOsc.const_mul (k : ℝ) (h : UOsc n a) : UOsc n (fun lam t x => k * a lam t x) := by
  obtain ⟨M, hM, h⟩ := h
  exact ⟨|k| * M, mul_nonneg (abs_nonneg _) hM, fun lam T hlam hT hT1 =>
    (h lam T hlam hT hT1).const_mul k⟩

theorem UOsc.mul (h : UOsc n a) (h' : UOsc n' b) :
    UOsc (n + n') (fun lam t x => a lam t x * b lam t x) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨M', hM', h'⟩ := h'
  exact ⟨2 * M * M', by positivity, fun lam T hlam hT hT1 =>
    (h lam T hlam hT hT1).mul (h' lam T hlam hT hT1) hM hM'⟩

theorem UOsc.lower (h : UOsc n a) (k : ℕ) : UOsc (n - k) a := by
  obtain ⟨M, hM, h⟩ := h
  exact ⟨M * 2 ^ k, by positivity, fun lam T hlam hT hT1 =>
    (h lam T hlam hT hT1).lower hM k fun t ht x hx => vs_le hT1 ht hx⟩

theorem uosc_one : UOsc 0 (fun _ _ _ => (1 : ℝ)) :=
  ⟨1, zero_le_one, fun _ _ _ _ _ => oscE_one⟩

theorem uosc_pol (a0 a1 a2 a3 a4 : ℝ) : UOsc 0 (fun _ _ x => pol a0 a1 a2 a3 a4 x) :=
  ⟨_, by positivity, fun _ _ _ _ hT1 => oscE_pol hT1 a0 a1 a2 a3 a4⟩

theorem uosc_xpow (k : ℕ) : UOsc k (fun _ _ x => x ^ k) :=
  ⟨2 ^ k, by positivity, fun _ _ _ _ _ => oscE_xpow k⟩

/-- A monomial times a polynomial times a function of order `n`. -/
theorem UOsc.term (h : UOsc n a) (k : ℕ) (a0 a1 a2 a3 a4 : ℝ) :
    UOsc (n + k) (fun lam t x => x ^ k * pol a0 a1 a2 a3 a4 x * a lam t x) :=
  (((uosc_xpow k).mul (uosc_pol a0 a1 a2 a3 a4)).mul h).cast (by ring)

/-- The entries of a uniform tower. -/
theorem UOsc.of_tower {K : ℕ} {c d : ℝ → ℕ → ℝ → ℝ → ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam T : ℝ), 0 < lam → T ≤ lam ^ 2 → Tower T n C K (c lam) (d lam))
    {j : ℕ} (hj : j < K) : UOsc (n - j) (fun lam => c lam j) := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun lam T hlam hT _ => (h lam T hlam hT).oscE hj⟩

end Uniform

/-! ### The profile and the localized profile -/

theorem uosc_G (hP : IsProfile c G) : UOsc 0 (fun _ t x => G (x / Real.sqrt (-t))) := by
  obtain ⟨C, hC, h⟩ := osc_G hP
  exact ⟨C, hC, fun _ T _ _ _ => (h T).oscE⟩

theorem uosc_Fss (hP : IsProfile c G) (j : ℕ) :
    UOsc (-1 - j) (fun _ t x => iteratedDeriv j (Fss G t) x) := by
  obtain ⟨C, hC, h⟩ := osc_Fss hP j
  exact ⟨C, hC, fun _ T _ _ _ => (h T).oscE⟩

theorem uosc_flamJet (hP : IsProfile c G) (j : ℕ) :
    UOsc (-1 - j) (fun lam => flamJet G lam j) :=
  UOsc.of_tower (tower_Flam hP (j + 1)) (Nat.lt_succ_self j)

/-- The derivatives of the localized profile on `[0, 1]` are the Leibniz sums. -/
theorem D_Flam (hP : IsProfile c G) {lam t : ℝ} (hlam : 0 < lam) (ht : t < 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, D (Flam G lam t) x = flamJet G lam 1 t x ∧
      D (D (Flam G lam t)) x = flamJet G lam 2 t x ∧
      D (D (D (Flam G lam t))) x = flamJet G lam 3 t x ∧
      D (D (D (D (Flam G lam t)))) x = flamJet G lam 4 t x := by
  obtain ⟨C0, hC0, htow⟩ := tower_Flam hP 5
  have e0 : flamJet G lam 0 t = Flam G lam t := funext fun y => flamJet_zero G lam t y
  have h := (htow lam (lam ^ 2) hlam le_rfl).D_eq (by norm_num) ht
  rw [e0] at h
  exact h

theorem contDiffOn_Flam_Icc (hP : IsProfile c G) (lam : ℝ) {t : ℝ} (ht : t < 0) :
    ContDiffOn ℝ ∞ (Flam G lam t) (Icc 0 1) := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  have hρ : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
  exact (contDiffOn_Flam hh ht).mono fun y hy => by
    rw [mem_Ioi]
    nlinarith [hy.1]

/-! ### The operator `A` applied to the localized profile -/

/-- **`A F_λ` has order `-3`**, uniformly in `λ` and `T ≤ min(λ², 1)`
(Lemma 6.2 of the manuscript: `A F_λ = Osc(σ⁻⁶)`). -/
theorem uosc_AFlam (hP : IsProfile c G) : UOsc (-3) (fun lam t x => Aop (Flam G lam t) x) := by
  have t4 : UOsc (-3) _ := ((uosc_flamJet hP 4).term 2 1 (-2) 1 0 0).cast (by norm_num)
  have t3 : UOsc (-3) _ := ((uosc_flamJet hP 3).term 1 20 (-48) 28 0 0).cast (by norm_num)
  have t2 : UOsc (-3) _ := ((uosc_flamJet hP 2).term 0 90 (-300) 222 0 0).cast (by norm_num)
  have t1 : UOsc (-3) _ :=
    (((uosc_flamJet hP 1).term 0 (-360) 480 0 0 0).lower 1).cast (by norm_num)
  have t0 : UOsc (-3) _ :=
    (((uosc_flamJet hP 0).term 0 180 0 0 0 0).lower 2).cast (by norm_num)
  refine ((((t4.add t3).add t2).add t1).add t0).congr fun lam hlam t ht x hx => ?_
  obtain ⟨d1, d2, d3, d4⟩ := D_Flam hP hlam ht x hx
  rw [Aop_eq (contDiffOn_Flam_Icc hP lam ht) hx, d1, d2, d3, d4, flamJet_zero]
  unfold pol
  ring

end Calabi.Osc
