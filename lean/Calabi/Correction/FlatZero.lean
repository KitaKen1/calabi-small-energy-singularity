import Calabi.Correction.FlatSymmetry

/-!
# The flat zero-data problem: regularity up to the initial time

For `u_t + a(x, t) Δ² u = f`, `u(0) = 0`, on a Euclidean space, with a smooth
coefficient `a` (equal to one outside a ball) and a source `f` that is Hölder
continuous in the parabolic distance, there is a classical solution whose
fourth derivatives are bounded and Hölder continuous on the closed time slab
`[0, R]`, **including the initial time** (`exists_zero_data_solution`).

The reused library has the existence theorem
(`exists_holder_source_evolves`), but its bounds for the fourth derivatives are
on `[a, R]` with `a > 0`, and its initial Schauder estimate `initial_schauder`
is an a priori estimate which assumes that the Hölder norms are finite down to
`t = 0`. The gap is closed as follows. Let `ψ` be the solution of the
constant-coefficient problem `ψ_t + Δ² ψ = f`, `ψ(0) = 0`; the library bounds
`D⁴ψ` up to the initial time (`constant_fourth_estimate`). The difference
`w = u - ψ` solves `w_t + a Δ² w = (1 - a) Δ² ψ` with zero data, and this
source vanishes at `t = 0`. Extended by zero to the times `[-1/2, 0]` it is
still an admissible source, the solution vanishes there by uniqueness, and
the interior bounds of the library, started at the time `-1/2`, reach `t = 0`.
-/

open Set Filter
open scoped Topology ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian

namespace Calabi.FlatZero

open OAI OAI.ParametrixEvolution OAI.ParabolicInterior OAI.ParabolicSchauder OAI.ClassicalIBP
  OAI.FlatSymmetry OAI.FlatSimilarity

/-- The time parameter of the corrector: `s - 1/2` clamped to `[0, 1/2]`. -/
noncomputable def tau (s : ℝ) : ℝ := max (min (s - 1 / 2) (1 / 2)) 0

theorem tau_mem (s : ℝ) : tau s ∈ Icc (0 : ℝ) (1 / 2) :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩

theorem tau_of_le {s : ℝ} (hs : s ≤ 1 / 2) : tau s = 0 := by
  unfold tau
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

theorem tau_add {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) : tau (t + 1 / 2) = t := by
  unfold tau
  rw [add_sub_cancel_right, min_eq_left ht.2, max_eq_left ht.1]

theorem abs_tau_sub_le (s r : ℝ) : |tau s - tau r| ≤ |s - r| := by
  unfold tau
  have h1 := abs_max_sub_max_le_abs (min (s - 1 / 2) (1 / 2)) (min (r - 1 / 2) (1 / 2)) 0
  have h2 := abs_min_sub_min_le_max (s - 1 / 2) (1 / 2) (r - 1 / 2) (1 / 2)
  have h3 : max |s - 1 / 2 - (r - 1 / 2)| |(1 / 2 : ℝ) - 1 / 2| = |s - r| := by
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    congr 1
    ring
  rw [h3] at h2
  exact h1.trans h2

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Continuity of a Hölder function. -/
theorem continuous_of_holder {g : V → ℂ} {H γ : ℝ} (hγ : 0 < γ)
    (h : ∀ x y, ‖g x - g y‖ ≤ H * ‖x - y‖ ^ γ) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun y : V => H * ‖y - x‖ ^ γ) (𝓝 x) (𝓝 0) := by
    have h2 : Continuous fun y : V => ‖y - x‖ := continuous_norm.comp (continuous_id.sub continuous_const)
    have h3 : Tendsto (fun y : V => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have h4 := h2.tendsto x
      simpa using h4
    have h5 := (h3.rpow_const (Or.inr hγ.le)).const_mul H
    simpa [Real.zero_rpow hγ.ne'] using h5
  exact squeeze_zero (fun y => dist_nonneg) (fun y => by rw [dist_eq_norm]; exact h y x) h1

variable [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1600000 in
/-- **The flat zero-data problem.** A classical solution of
`u_t + a Δ² u = f`, `u(0) = 0`, on `[0, R]`, whose fourth derivatives are
bounded and Hölder continuous up to the initial time. -/
theorem exists_zero_data_solution {κ Λ L C ρ₀ R γ H Bf : ℝ} (hκ : 0 < κ)
    (hΛ : 1 ≤ Λ) (hL : 0 ≤ L) (hC : 0 ≤ C) (hR : 0 < R) (hR4 : R ≤ 1 / 4) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hH : 0 ≤ H) (a : ℝ → V → ℝ) (ha : ∀ t x, a t x ∈ Icc κ Λ)
    (ha1 : ∀ t x, ρ₀ ≤ ‖x‖ → a t x = 1)
    (haL : ∀ t r x z, |a t x - a r z| ≤ L * (‖x - z‖ + |t - r|))
    (haS : ∀ t, ContDiff ℝ ∞ (a t))
    (haJ : ∀ t, ∀ n : ℕ, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n (a t) x‖ ≤ C)
    (f : ℝ → V → ℂ) (hf0 : ∀ t x, ρ₀ ≤ ‖x‖ → f t x = 0) (hfB : ∀ t x, ‖f t x‖ ≤ Bf)
    (hfH : ∀ t s x y, ‖f t x - f s y‖ ≤ H * (‖x - y‖ ^ γ + |t - s| ^ (γ / 4))) :
    ∃ u : ℝ → V → ℂ, (∀ x, u 0 x = 0) ∧
      (∀ t ∈ Icc 0 R, ContDiff ℝ 4 (u t)) ∧
      (∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun s => u s x)
        (f t x - (a t x : ℂ) * Δ (Δ (u t)) x) (Icc 0 R) t) ∧
      (∃ U : ℝ, ∀ t ∈ Icc 0 R, ∀ x, ‖u t x‖ ≤ U) ∧
      (∃ M : ℝ, 0 ≤ M ∧ HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R}
        (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) M) ∧
      ((∀ (Q : V ≃ₗᵢ[ℝ] V) t x, a t (Q x) = a t x) →
        (∀ (Q : V ≃ₗᵢ[ℝ] V) t x, f t (Q x) = f t x) →
        ∀ t ∈ Icc 0 R, ∀ (Q : V ≃ₗᵢ[ℝ] V) x, u t (Q x) = u t x) ∧
      ((∀ t x, star (f t x) = f t x) → ∀ t ∈ Icc 0 R, ∀ x, star (u t x) = u t x) := by
  classical
  have hγ4 : (0 : ℝ) < γ / 4 := by positivity
  have h14 : ((1 : ℝ) / 4) ≠ 0 := by norm_num
  -- the source as a map into `C₀`
  have hfx : ∀ t x y, ‖f t x - f t y‖ ≤ H * ‖x - y‖ ^ γ := by
    intro t x y
    have h := hfH t t x y
    rwa [sub_self, abs_zero, Real.zero_rpow hγ4.ne', add_zero] at h
  have hfc : ∀ t, Continuous (f t) := fun t => continuous_of_holder hγ (hfx t)
  have hft : ∀ t s x, ‖f t x - f s x‖ ≤ H * |t - s| ^ (γ / 4) := by
    intro t s x
    have h := hfH t s x x
    rwa [sub_self, norm_zero, Real.zero_rpow hγ.ne', zero_add] at h
  have hωf : Tendsto (fun r : ℝ => H * r ^ (γ / 4)) (𝓝 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hγ4.le).tendsto 0).const_mul H
    simpa [Real.zero_rpow hγ4.ne'] using h
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ →ᵇ C₀(V, ℂ), F = sourceMap f hfc ρ₀ hf0 Bf hfB _ hωf hft :=
    ⟨_, rfl⟩
  have hFa : ∀ t x, F t x = f t x := fun t x => by rw [hFdef]; rfl
  have hFH : ∀ t x y, ‖F t x - F t y‖ ≤ H * ‖x - y‖ ^ γ := by
    intro t x y
    rw [hFa, hFa]
    exact hfx t x y
  -- the constant-coefficient corrector
  obtain ⟨Cc, hCc, Hc⟩ := constant_fourth_estimate (V := V) γ hγ hγ1
  have hb0 : ∀ s ∈ Icc (0 : ℝ) 1, ‖(0 : C(ℝ, V →ᵇ ℂ)) s‖ ≤ 0 := by simp
  have hLip1 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, ∀ x z : V,
      |((unitLine (V := V)) s x).val - (unitLine r z).val| ≤ 0 * (‖x - z‖ + |s - r|) := by
    intros
    simp [unitLine, unitCoefficient]
  have hLipb0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x z : V,
      ‖(0 : C(ℝ, V →ᵇ ℂ)) s x - (0 : C(ℝ, V →ᵇ ℂ)) s z‖ ≤ 0 * ‖x - z‖ := by simp
  have hA1 : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ ∞ (fun x : V => ((unitLine (V := V)) s x).val) :=
    fun _ _ => contDiff_const
  have hFex : ∃ H' : ℝ, 0 ≤ H' ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, ‖F t x - F t y‖ ≤ H' * ‖x - y‖ ^ γ :=
    ⟨H, hH, fun t _ => hFH t⟩
  obtain ⟨ψ, hψ⟩ := exists_source_evolves zero_lt_one 0 0 le_rfl le_rfl unitLine 0
    1 zero_le_one le_rfl hb0 hLip1 hLipb0 hA1 γ hγ hγ1.le F hFex 0
  have Hψ := Hc 1 zero_lt_one le_rfl F H hH (fun t _ => hFH t) ψ hψ
  have hψ0 : ψ 0 = 0 := hψ.1
  have hψC4 : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ContDiff ℝ 4 (fun x => ψ t x) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      simp only [hψ0, ZeroAtInftyContinuousMap.zero_apply]
      exact contDiff_const
    · exact hψ.2.2.1 t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), by linarith [ht.2]⟩
  obtain ⟨T4, hT4⟩ : ∃ T4 : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ, T4 = traceFour := ⟨_, rfl⟩
  obtain ⟨B4, hB4def⟩ : ∃ B4 : ℝ, B4 = ‖T4‖ * (Cc * H) := ⟨_, rfl⟩
  have hB4 : 0 ≤ B4 := by
    rw [hB4def]
    positivity
  have hbil : ∀ (h : V → ℂ), ContDiff ℝ 4 h → ∀ x, Δ (Δ h) x = T4 (iteratedFDeriv ℝ 4 h x) := by
    intro h hh x
    rw [hT4]
    exact bilaplacian_eq_traceFour h hh x
  -- bounds for `P s x = T4 (D⁴ ψ(s))(x)`
  have hPB : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∀ x,
      ‖T4 (iteratedFDeriv ℝ 4 (fun y => ψ t y) x)‖ ≤ B4 := by
    intro t ht x
    rw [hB4def]
    exact (T4.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Hψ.1 (x, t) ⟨ht.1, by linarith [ht.2]⟩) (norm_nonneg _))
  have hPH : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∀ s ∈ Icc (0 : ℝ) (1 / 2), ∀ x y,
      ‖T4 (iteratedFDeriv ℝ 4 (fun z => ψ t z) x) - T4 (iteratedFDeriv ℝ 4 (fun z => ψ s z) y)‖
        ≤ B4 * pdist (x, t) (y, s) ^ γ := by
    intro t ht s hs x y
    rw [← map_sub, hB4def, mul_assoc]
    exact (T4.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Hψ.2 (x, t) ⟨ht.1, by linarith [ht.2]⟩ (y, s) ⟨hs.1, by linarith [hs.2]⟩) (norm_nonneg _))
  -- the corrected source `g s x = (1 - a(s - 1/2, x)) P(τ s, x)`
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → V → ℂ, g = fun s x =>
      ((1 - a (s - 1 / 2) x : ℝ) : ℂ) * T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau s) y) x) :=
    ⟨_, rfl⟩
  have hga : ∀ s x, g s x
      = ((1 - a (s - 1 / 2) x : ℝ) : ℂ) * T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau s) y) x) :=
    fun s x => by rw [hgdef]
  have hac : ∀ t, Continuous (a t) := fun t => (haS t).continuous
  have habs : ∀ t x, |1 - a t x| ≤ Λ := by
    intro t x
    have h := ha t x
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hgc : ∀ s, Continuous (g s) := by
    intro s
    have h1 : Continuous fun x : V => ((1 - a (s - 1 / 2) x : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.sub (hac _))
    have h2 : Continuous fun x : V => T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau s) y) x) :=
      T4.continuous.comp ((hψC4 (tau s) (tau_mem s)).continuous_iteratedFDeriv le_rfl)
    have h3 := h1.mul h2
    rw [hgdef]
    exact h3
  have hg0 : ∀ s x, ρ₀ ≤ ‖x‖ → g s x = 0 := by
    intro s x hx
    rw [hga, ha1 _ x hx]
    simp
  have hgB : ∀ s x, ‖g s x‖ ≤ Λ * B4 := by
    intro s x
    rw [hga, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (habs _ x) (hPB (tau s) (tau_mem s) x) (norm_nonneg _) (by linarith)
  have hgt : ∀ t s x, ‖g t x - g s x‖
      ≤ L * B4 * |t - s| + Λ * B4 * (|t - s| ^ ((1 : ℝ) / 4)) ^ γ := by
    intro t s x
    have e : g t x - g s x
        = ((a (s - 1 / 2) x - a (t - 1 / 2) x : ℝ) : ℂ)
            * T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau t) y) x)
          + ((1 - a (s - 1 / 2) x : ℝ) : ℂ)
            * (T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau t) y) x)
              - T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau s) y) x)) := by
      rw [hga, hga]
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |a (s - 1 / 2) x - a (t - 1 / 2) x| ≤ L * |t - s| := by
        have h := haL (s - 1 / 2) (t - 1 / 2) x x
        rw [sub_self, norm_zero, zero_add] at h
        have e2 : |s - 1 / 2 - (t - 1 / 2)| = |t - s| := by
          rw [← abs_neg]
          congr 1
          ring
        rwa [e2] at h
      calc |a (s - 1 / 2) x - a (t - 1 / 2) x| * ‖T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau t) y) x)‖
          ≤ L * |t - s| * B4 :=
            mul_le_mul h1 (hPB (tau t) (tau_mem t) x) (norm_nonneg _)
              (mul_nonneg hL (abs_nonneg _))
        _ = L * B4 * |t - s| := by ring
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hPH (tau t) (tau_mem t) (tau s) (tau_mem s) x x
      have h2 : pdist (x, tau t) (x, tau s) ^ γ ≤ (|t - s| ^ ((1 : ℝ) / 4)) ^ γ := by
        have e3 : pdist (x, tau t) (x, tau s) = |tau t - tau s| ^ ((1 : ℝ) / 4) := by
          simp [pdist]
        rw [e3]
        exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _)
          (Real.rpow_le_rpow (abs_nonneg _) (abs_tau_sub_le t s) (by norm_num)) hγ.le
      calc |1 - a (s - 1 / 2) x| * ‖T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau t) y) x)
            - T4 (iteratedFDeriv ℝ 4 (fun y => ψ (tau s) y) x)‖
          ≤ Λ * (B4 * (|t - s| ^ ((1 : ℝ) / 4)) ^ γ) :=
            mul_le_mul (habs _ x) (h1.trans (mul_le_mul_of_nonneg_left h2 hB4)) (norm_nonneg _)
              (by linarith)
        _ = Λ * B4 * (|t - s| ^ ((1 : ℝ) / 4)) ^ γ := by ring
  have hωg : Tendsto (fun r : ℝ => L * B4 * r + Λ * B4 * (r ^ ((1 : ℝ) / 4)) ^ γ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => L * B4 * r + Λ * B4 * (r ^ ((1 : ℝ) / 4)) ^ γ :=
      (continuous_const.mul continuous_id).add (continuous_const.mul
        ((Real.continuous_rpow_const hγ.le).comp
          (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4))))
    have h := hc.tendsto 0
    simpa [Real.zero_rpow h14, Real.zero_rpow hγ.ne'] using h
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ →ᵇ C₀(V, ℂ), G = sourceMap g hgc ρ₀ hg0 (Λ * B4) hgB _ hωg hgt :=
    ⟨_, rfl⟩
  have hGa : ∀ s x, G s x = g s x := fun s x => by rw [hGdef]; rfl
  have hΛ0 : 0 ≤ Λ := by linarith
  have hGH : ∀ s x y, ‖G s x - G s y‖ ≤ (max L Λ * B4 + Λ * B4) * ‖x - y‖ ^ γ := by
    intro s x y
    rw [hGa, hGa]
    have e : g s x - g s y
        = ((a (s - 1 / 2) y - a (s - 1 / 2) x : ℝ) : ℂ)
            * T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) x)
          + ((1 - a (s - 1 / 2) y : ℝ) : ℂ)
            * (T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) x)
              - T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) y)) := by
      rw [hga, hga]
      push_cast
      ring
    rw [e, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |a (s - 1 / 2) y - a (s - 1 / 2) x| ≤ max L Λ * ‖x - y‖ ^ γ := by
        refine lip_bdd_holder hγ hγ1.le (norm_nonneg _) hL hΛ0 ?_ ?_
        · have h := haL (s - 1 / 2) (s - 1 / 2) y x
          rw [sub_self, abs_zero, add_zero, norm_sub_rev] at h
          exact h
        · have hy := ha (s - 1 / 2) y
          have hx := ha (s - 1 / 2) x
          rw [abs_le]
          constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
      calc |a (s - 1 / 2) y - a (s - 1 / 2) x| * ‖T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) x)‖
          ≤ max L Λ * ‖x - y‖ ^ γ * B4 :=
            mul_le_mul h1 (hPB (tau s) (tau_mem s) x) (norm_nonneg _)
              (mul_nonneg (le_max_of_le_left hL) (Real.rpow_nonneg (norm_nonneg _) _))
        _ = max L Λ * B4 * ‖x - y‖ ^ γ := by ring
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hPH (tau s) (tau_mem s) (tau s) (tau_mem s) x y
      have e3 : pdist (x, tau s) (y, tau s) = ‖x - y‖ := by
        simp [pdist, Real.zero_rpow h14]
      rw [e3] at h1
      calc |1 - a (s - 1 / 2) y| * ‖T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) x)
            - T4 (iteratedFDeriv ℝ 4 (fun z => ψ (tau s) z) y)‖
          ≤ Λ * (B4 * ‖x - y‖ ^ γ) := mul_le_mul (habs _ y) h1 (norm_nonneg _) hΛ0
        _ = Λ * B4 * ‖x - y‖ ^ γ := by ring
  -- the shifted coefficient
  have haδ : ∀ t x, a (t - 1 / 2) x ∈ Icc κ Λ := fun t x => ha _ x
  have hLδ : ∀ t s x, |a (t - 1 / 2) x - a (s - 1 / 2) x| ≤ L * |t - s| := by
    intro t s x
    have h := haL (t - 1 / 2) (s - 1 / 2) x x
    rw [sub_self, norm_zero, zero_add] at h
    have e2 : |t - 1 / 2 - (s - 1 / 2)| = |t - s| := by
      congr 1
      ring
    rwa [e2] at h
  obtain ⟨Aδ, hAδdef⟩ : ∃ Aδ : C(ℝ, V →ᵇ Icc κ Λ),
      Aδ = coeffMap (fun t => a (t - 1 / 2)) κ Λ haδ (fun t => hac _) L hLδ := ⟨_, rfl⟩
  have hAδa : ∀ t x, (Aδ t x).val = a (t - 1 / 2) x := fun t x => by rw [hAδdef]; rfl
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = 2 * R := ⟨_, rfl⟩
  have hRR' : R < R' := by linarith
  have hR'2 : R' ≤ 1 / 2 := by linarith
  have hbδ : ∀ s ∈ Icc (0 : ℝ) (R' + 1 / 2), ‖(0 : C(ℝ, V →ᵇ ℂ)) s‖ ≤ 0 := by simp
  have hLipδ : ∀ s ∈ Icc (0 : ℝ) (R' + 1 / 2), ∀ r ∈ Icc (0 : ℝ) (R' + 1 / 2), ∀ x z : V,
      |(Aδ s x).val - (Aδ r z).val| ≤ L * (‖x - z‖ + |s - r|) := by
    intro s _ r _ x z
    rw [hAδa, hAδa]
    have h := haL (s - 1 / 2) (r - 1 / 2) x z
    have e2 : |s - 1 / 2 - (r - 1 / 2)| = |s - r| := by
      congr 1
      ring
    rwa [e2] at h
  have hLipbδ : ∀ s ∈ Icc (0 : ℝ) (R' + 1 / 2), ∀ x z : V,
      ‖(0 : C(ℝ, V →ᵇ ℂ)) s x - (0 : C(ℝ, V →ᵇ ℂ)) s z‖ ≤ L * ‖x - z‖ := by
    intro s _ x z
    simp only [ContinuousMap.zero_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      sub_self, norm_zero]
    positivity
  have hAδS : ∀ s, ContDiff ℝ ∞ (fun x => (Aδ s x).val) := by
    intro s
    have h : (fun x => (Aδ s x).val) = a (s - 1 / 2) := funext fun x => hAδa s x
    rw [h]
    exact haS _
  have hGex : ∃ H' : ℝ, 0 ≤ H' ∧ ∀ t ∈ Icc (0 : ℝ) (R' + 1 / 2), ∀ x y,
      ‖G t x - G t y‖ ≤ H' * ‖x - y‖ ^ γ :=
    ⟨max L Λ * B4 + Λ * B4, by positivity, fun t _ => hGH t⟩
  obtain ⟨û, hû, hûB⟩ := exists_holder_source_evolves hκ L 0 hL le_rfl Aδ 0 (R' + 1 / 2)
    (by linarith) (by linarith) hbδ hLipδ hLipbδ (fun s _ => hAδS s) γ hγ hγ1 G hGex 0
  -- the solution vanishes on `[0, 1/2]`
  have hzfun : (fun y : V => (0 : C₀(V, ℂ)) y) = fun _ => (0 : ℂ) := rfl
  have hzC4 : ContDiff ℝ 4 (fun y : V => (0 : C₀(V, ℂ)) y) := by
    rw [hzfun]
    exact contDiff_const
  have hzeron : ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n (fun y => (0 : C₀(V, ℂ)) y) x = 0 := by
    intro n x
    rw [hzfun, iteratedFDeriv_zero_fun]
    rfl
  have hzero4 : ∀ x : V, iteratedFDeriv ℝ 4 (fun y => (0 : C₀(V, ℂ)) y) x = 0 := hzeron 4
  have hGzero : ∀ s ≤ (1 : ℝ) / 2, ∀ x, G s x = 0 := by
    intro s hs x
    rw [hGa, hga, tau_of_le hs, hψ0, hzero4]
    simp
  have hz : SourceEvolves Aδ (0 : C(ℝ, V →ᵇ ℂ)) G 0 (1 / 2) 0 (fun _ => (0 : C₀(V, ℂ))) := by
    refine ⟨rfl, continuousOn_const, fun t _ => hzC4, fun t _ n _ => ⟨0, fun x => ?_⟩,
      fun t ht => ⟨0, hasDerivAt_const t _, fun x => ?_⟩⟩
    · show ‖iteratedFDeriv ℝ n (fun y : V => (0 : C₀(V, ℂ)) y) x‖ ≤ 0
      rw [hzeron n x, norm_zero]
    · have h1 : Δ (Δ fun y : V => (0 : C₀(V, ℂ)) y) x = 0 := by
        rw [hbil _ hzC4, hzero4]
        simp
      show (0 : V →ᵇ ℂ) x = G t x - ((Aδ t x).val : ℂ) * Δ (Δ fun y : V => (0 : C₀(V, ℂ)) y) x
        - (0 : C(ℝ, V →ᵇ ℂ)) t x * (0 : C₀(V, ℂ)) x
      rw [h1, hGzero t ht.2.le x]
      simp
  have hû0 : ∀ t ∈ Icc (0 : ℝ) (1 / 2), û t = 0 := by
    intro t ht
    have h := (hû.end_mono (by linarith : (1 : ℝ) / 2 ≤ R' + 1 / 2)).unique hz
      (by norm_num) hκ hC (le_refl (0 : ℝ)) (fun t _ => by simp)
      (fun t _ => (hAδS t).of_le (by simp))
      (fun t _ n hn x => by
        have h : (fun y => (Aδ t y).val) = a (t - 1 / 2) := funext fun y => hAδa t y
        rw [h]
        exact haJ _ n hn x) t ht
    exact h
  have hûC4 : ∀ t ∈ Icc (0 : ℝ) R, ContDiff ℝ 4 (fun x => û (t + 1 / 2) x) := fun t ht =>
    hû.2.2.1 (t + 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hRhalf : ∀ t ∈ Icc (0 : ℝ) R, t ∈ Icc (0 : ℝ) (1 / 2) := fun t ht =>
    ⟨ht.1, by linarith [ht.2]⟩
  -- pointwise time derivatives
  have hψd : ∀ t ∈ Icc (0 : ℝ) R, ∀ x, HasDerivWithinAt (fun r => ψ r x)
      (f t x - T4 (iteratedFDeriv ℝ 4 (fun y => ψ t y) x)) (Icc 0 R) t := by
    intro t ht x
    by_cases ht0 : t = 0
    · subst ht0
      have hi := hψ.initial_derivative zero_lt_one 1 0 0 zero_le_one le_rfl le_rfl
        unitLine 0 1 zero_lt_one le_rfl hb0 hLip1 hLipb0 hA1
        (fun _ _ n _ x => unitLine_jets n x) γ hγ hγ1.le F hFex
      have hval : T4 (iteratedFDeriv ℝ 4 (fun y => ψ 0 y) x) = 0 := by
        rw [hψ0, hzero4]
        simp
      rw [hval, sub_zero, hasDerivWithinAt_iff_tendsto_slope]
      have hx := ((C0Convolution.eval x).continuous.tendsto (F 0)).comp hi
      have hm : Icc (0 : ℝ) R \ {0} ⊆ Ioi 0 := by
        intro s hs
        exact lt_of_le_of_ne hs.1.1 (Ne.symm (by simpa using hs.2))
      have hx' := hx.mono_left (nhdsWithin_mono 0 hm)
      have hF0 : (C0Convolution.eval x) (F 0) = f 0 x := by
        rw [C0Convolution.eval_apply, hFa]
      rw [hF0] at hx'
      refine hx'.congr fun s => ?_
      simp [slope, hψ0, C0Convolution.eval_apply]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      obtain ⟨p, hp, hpe⟩ := hψ.2.2.2.2 t ⟨htpos, by linarith [ht.2]⟩
      have hh := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t hp
      have he : p x = f t x - T4 (iteratedFDeriv ℝ 4 (fun y => ψ t y) x) := by
        rw [hpe x, hbil _ (hψC4 t (hRhalf t ht)), hFa]
        simp [unitLine, unitCoefficient]
      have hh' : HasDerivAt (fun r => ψ r x) (p x) t := by
        simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
          ZeroAtInftyContinuousMap.toBCF_apply] using hh
      rw [← he]
      exact hh'.hasDerivWithinAt
  have hûd : ∀ t ∈ Icc (0 : ℝ) R, ∀ x, HasDerivAt (fun r => û (r + 1 / 2) x)
      (g (t + 1 / 2) x - (a t x : ℂ) * T4 (iteratedFDeriv ℝ 4 (fun y => û (t + 1 / 2) y) x)) t := by
    intro t ht x
    obtain ⟨p, hp, hpe⟩ := hû.2.2.2.2 (t + 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hh := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt (t + 1 / 2) hp
    have he : p x = g (t + 1 / 2) x
        - (a t x : ℂ) * T4 (iteratedFDeriv ℝ 4 (fun y => û (t + 1 / 2) y) x) := by
      rw [hpe x, hbil _ (hûC4 t ht), hGa, hAδa, add_sub_cancel_right]
      simp
    have hh' : HasDerivAt (fun r => û r x) (p x) (t + 1 / 2) := by
      simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
        ZeroAtInftyContinuousMap.toBCF_apply] using hh
    rw [← he]
    exact hh'.comp_add_const t (1 / 2)
  have hsum4 : ∀ t ∈ Icc (0 : ℝ) R, ∀ x,
      iteratedFDeriv ℝ 4 (fun y => ψ t y + û (t + 1 / 2) y) x
        = iteratedFDeriv ℝ 4 (fun y => ψ t y) x
          + iteratedFDeriv ℝ 4 (fun y => û (t + 1 / 2) y) x := fun t ht x =>
    fun_iteratedFDeriv_add_apply (hψC4 t (hRhalf t ht)).contDiffAt (hûC4 t ht).contDiffAt
  refine ⟨fun t x => ψ t x + û (t + 1 / 2) x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := hû0 (1 / 2) ⟨by norm_num, le_rfl⟩
    show ψ 0 x + û (0 + 1 / 2) x = 0
    rw [zero_add, hψ0, h]
    simp
  · intro t ht
    exact (hψC4 t (hRhalf t ht)).add (hûC4 t ht)
  · intro t ht x
    have h := (hψd t ht x).fun_add (hûd t ht x).hasDerivWithinAt
    refine h.congr_deriv ?_
    have hC4 : ContDiff ℝ 4 (fun y => ψ t y + û (t + 1 / 2) y) :=
      (hψC4 t (hRhalf t ht)).add (hûC4 t ht)
    show f t x - T4 (iteratedFDeriv ℝ 4 (fun y => ψ t y) x)
        + (g (t + 1 / 2) x
          - (a t x : ℂ) * T4 (iteratedFDeriv ℝ 4 (fun y => û (t + 1 / 2) y) x))
      = f t x - (a t x : ℂ) * Δ (Δ fun y => ψ t y + û (t + 1 / 2) y) x
    rw [hbil _ hC4, hsum4 t ht, map_add, hga, tau_add (hRhalf t ht), add_sub_cancel_right]
    push_cast
    ring
  · obtain ⟨U1, hU1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
      (hψ.2.1.mono fun t ht => ⟨ht.1, by linarith [ht.2]⟩)
    have hshift : ContinuousOn (fun t : ℝ => û (t + 1 / 2)) (Icc 0 R) :=
      hû.2.1.comp (continuous_id.add continuous_const).continuousOn fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨U2, hU2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn hshift
    refine ⟨U1 + U2, fun t ht x => ?_⟩
    have h1 : ‖ψ t x‖ ≤ U1 := by
      have h := (ψ t).toBCF.norm_coe_le_norm x
      rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h
      exact h.trans (hU1 t ht)
    have h2 : ‖û (t + 1 / 2) x‖ ≤ U2 := by
      have h := (û (t + 1 / 2)).toBCF.norm_coe_le_norm x
      rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h
      exact h.trans (hU2 t ht)
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  · obtain ⟨Cδ, hCδ, hB1, hB2⟩ := hûB (1 / 2) (by norm_num)
    have hmem : ∀ t ∈ Icc (0 : ℝ) R, t + 1 / 2 ∈ Icc ((1 : ℝ) / 2) (R' + 1 / 2) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨Cc * H + 2 * Cδ, by positivity, fun p hp => ?_, fun p hp q hq => ?_⟩
    · change ‖iteratedFDeriv ℝ 4 (fun y => ψ p.2 y + û (p.2 + 1 / 2) y) p.1‖ ≤ _
      rw [hsum4 p.2 hp]
      refine (norm_add_le _ _).trans ?_
      have h1 := Hψ.1 (p.1, p.2) ⟨hp.1, by linarith [hp.2]⟩
      have h2 := hB1 (p.2 + 1 / 2) (hmem p.2 hp) p.1
      have h1' : ‖iteratedFDeriv ℝ 4 (fun y => ψ p.2 y) p.1‖ ≤ Cc * H := h1
      linarith
    · change ‖iteratedFDeriv ℝ 4 (fun y => ψ p.2 y + û (p.2 + 1 / 2) y) p.1
        - iteratedFDeriv ℝ 4 (fun y => ψ q.2 y + û (q.2 + 1 / 2) y) q.1‖ ≤ _
      rw [hsum4 p.2 hp, hsum4 q.2 hq]
      have h1 : ‖iteratedFDeriv ℝ 4 (fun y => ψ p.2 y) p.1
          - iteratedFDeriv ℝ 4 (fun y => ψ q.2 y) q.1‖ ≤ Cc * H * pdist p q ^ γ :=
        Hψ.2 (p.1, p.2) ⟨hp.1, by linarith [hp.2]⟩ (q.1, q.2) ⟨hq.1, by linarith [hq.2]⟩
      have h2 := hB2 (p.2 + 1 / 2) (hmem p.2 hp) (q.2 + 1 / 2) (hmem q.2 hq) p.1 q.1
      have e2 : |p.2 + 1 / 2 - (q.2 + 1 / 2)| = |p.2 - q.2| := by
        congr 1
        ring
      rw [e2] at h2
      have hd : 0 ≤ pdist p q := pdist_nonneg p q
      have hx : ‖p.1 - q.1‖ ^ γ ≤ pdist p q ^ γ :=
        Real.rpow_le_rpow (norm_nonneg _) (by
          unfold pdist
          exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hγ.le
      have ht : |p.2 - q.2| ^ (γ / 4) ≤ pdist p q ^ γ := by
        have e3 : |p.2 - q.2| ^ (γ / 4) = (|p.2 - q.2| ^ ((1 : ℝ) / 4)) ^ γ := by
          rw [← Real.rpow_mul (abs_nonneg _)]
          congr 1
          ring
        rw [e3]
        exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) (by
          unfold pdist
          exact le_add_of_nonneg_left (norm_nonneg _)) hγ.le
      have e4 : iteratedFDeriv ℝ 4 (fun y => ψ p.2 y) p.1
            + iteratedFDeriv ℝ 4 (fun y => û (p.2 + 1 / 2) y) p.1
          - (iteratedFDeriv ℝ 4 (fun y => ψ q.2 y) q.1
            + iteratedFDeriv ℝ 4 (fun y => û (q.2 + 1 / 2) y) q.1)
          = (iteratedFDeriv ℝ 4 (fun y => ψ p.2 y) p.1
              - iteratedFDeriv ℝ 4 (fun y => ψ q.2 y) q.1)
            + (iteratedFDeriv ℝ 4 (fun y => û (p.2 + 1 / 2) y) p.1
              - iteratedFDeriv ℝ 4 (fun y => û (q.2 + 1 / 2) y) q.1) := by
        abel
      rw [e4]
      refine (norm_add_le _ _).trans ?_
      have h3 : Cδ * (‖p.1 - q.1‖ ^ γ + |p.2 - q.2| ^ (γ / 4)) ≤ 2 * Cδ * pdist p q ^ γ := by
        nlinarith [mul_le_mul_of_nonneg_left hx hCδ, mul_le_mul_of_nonneg_left ht hCδ]
      calc _ ≤ Cc * H * pdist p q ^ γ + Cδ * (‖p.1 - q.1‖ ^ γ + |p.2 - q.2| ^ (γ / 4)) :=
            add_le_add h1 h2
        _ ≤ Cc * H * pdist p q ^ γ + 2 * Cδ * pdist p q ^ γ := add_le_add le_rfl h3
        _ = (Cc * H + 2 * Cδ) * pdist p q ^ γ := by ring
  · -- radial data give a radial solution
    intro hra hrf t ht Q x
    have hψrad := zero_data_radial (C := 1) hψ zero_le_one zero_lt_one zero_le_one
      (fun _ _ => contDiff_const) (fun _ _ n _ x => unitLine_jets n x)
      (fun _ _ _ => rfl) (fun Q t x => by rw [hFa, hFa]; exact hrf Q t x)
    have hGrad : ∀ (Q : V ≃ₗᵢ[ℝ] V) s x, G s (Q x) = G s x := by
      intro Q s x
      have hC4 := hψC4 (tau s) (tau_mem s)
      have hrot : (fun y => ψ (tau s) (Q y)) = fun y => ψ (tau s) y :=
        funext fun y => hψrad (tau s) ⟨(tau_mem s).1, by linarith [(tau_mem s).2]⟩ Q y
      have h1 : Δ (Δ (fun y => ψ (tau s) (Q y))) x = Δ (Δ (fun y => ψ (tau s) y)) (Q x) :=
        congrFun (bilaplacian_rotate Q (fun y => ψ (tau s) y) hC4) x
      rw [hrot] at h1
      rw [hGa, hGa, hga, hga, hra Q (s - 1 / 2) x, ← hbil _ hC4, ← hbil _ hC4, h1]
    have hûrad := zero_data_radial (C := C) hû (by linarith) hκ hC
      (fun t _ => (hAδS t).of_le (by simp))
      (fun t _ n hn x => by
        have h : (fun y => (Aδ t y).val) = a (t - 1 / 2) := funext fun y => hAδa t y
        rw [h]
        exact haJ _ n hn x)
      (fun Q t x => by rw [hAδa, hAδa]; exact hra Q _ x) hGrad
    show ψ t (Q x) + û (t + 1 / 2) (Q x) = ψ t x + û (t + 1 / 2) x
    rw [hψrad t ⟨ht.1, by linarith [ht.2]⟩ Q x,
      hûrad (t + 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩ Q x]
  · -- a real source gives a real solution
    intro hfr t ht x
    have hψre := zero_data_realValued (C := 1) hψ zero_le_one zero_lt_one zero_le_one
      (fun _ _ => contDiff_const) (fun _ _ n _ x => unitLine_jets n x)
      (fun t x => by rw [hFa]; exact hfr t x)
    have hGre : ∀ s x, star (G s x) = G s x := by
      intro s x
      have hC4 := hψC4 (tau s) (tau_mem s)
      have hst : (fun y => star (ψ (tau s) y)) = fun y => ψ (tau s) y :=
        funext fun y => hψre (tau s) ⟨(tau_mem s).1, by linarith [(tau_mem s).2]⟩ y
      have h1 : Δ (Δ (fun y => star (ψ (tau s) y))) x
          = star (Δ (Δ (fun y => ψ (tau s) y)) x) :=
        congrFun (bilaplacian_star (fun y => ψ (tau s) y)) x
      rw [hst] at h1
      rw [hGa, hga, star_mul', ← hbil _ hC4, ← h1, Complex.star_def, Complex.conj_ofReal]
    have hûre := zero_data_realValued (C := C) hû (by linarith) hκ hC
      (fun t _ => (hAδS t).of_le (by simp))
      (fun t _ n hn x => by
        have h : (fun y => (Aδ t y).val) = a (t - 1 / 2) := funext fun y => hAδa t y
        rw [h]
        exact haJ _ n hn x) hGre
    show star (ψ t x + û (t + 1 / 2) x) = ψ t x + û (t + 1 / 2) x
    rw [star_add, hψre t ⟨ht.1, by linarith [ht.2]⟩ x,
      hûre (t + 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x]

set_option maxHeartbeats 1600000 in
open OAI.ParabolicInitial in
/-- **The flat zero-data problem, with finite parabolic Hölder norms.** The
solution of `exists_zero_data_solution`, extended by zero outside `[0, R]`:
all the jets `Dʲu`, `j ≤ 4`, and `u_t` are bounded and Hölder continuous on
`V × [0, R]`. This is the qualitative hypothesis of the a priori estimate
`OAI.ParabolicInitial.initial_schauder`. -/
theorem exists_zero_data_jets {κ Λ L C ρ₀ R γ H Bf : ℝ} (hκ : 0 < κ)
    (hΛ : 1 ≤ Λ) (hL : 0 ≤ L) (hC : 0 ≤ C) (hR : 0 < R) (hR4 : R ≤ 1 / 4) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hH : 0 ≤ H) (a : ℝ → V → ℝ) (ha : ∀ t x, a t x ∈ Icc κ Λ)
    (ha1 : ∀ t x, ρ₀ ≤ ‖x‖ → a t x = 1)
    (haL : ∀ t r x z, |a t x - a r z| ≤ L * (‖x - z‖ + |t - r|))
    (haS : ∀ t, ContDiff ℝ ∞ (a t))
    (haJ : ∀ t, ∀ n : ℕ, n ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ n (a t) x‖ ≤ C)
    (f : ℝ → V → ℂ) (hf0 : ∀ t x, ρ₀ ≤ ‖x‖ → f t x = 0) (hfB : ∀ t x, ‖f t x‖ ≤ Bf)
    (hfH : ∀ t s x y, ‖f t x - f s y‖ ≤ H * (‖x - y‖ ^ γ + |t - s| ^ (γ / 4))) :
    ∃ u : ℝ → V → ℂ, (∀ x, u 0 x = 0) ∧ (∀ t, ContDiff ℝ 4 (u t)) ∧
      (∀ t ∈ Icc 0 R, ∀ x, HasDerivWithinAt (fun s => u s x)
        (f t x - (a t x : ℂ) * Δ (Δ (u t)) x) (Icc 0 R) t) ∧
      (∃ U : ℝ, ∀ t x, ‖u t x‖ ≤ U) ∧
      (∃ M : ℝ, 0 ≤ M ∧ JetBound γ {p : V × ℝ | p.2 ∈ Icc 0 R} u
        (fun t x => f t x - (a t x : ℂ) * Δ (Δ (u t)) x) M) ∧
      ((∀ (Q : V ≃ₗᵢ[ℝ] V) t x, a t (Q x) = a t x) →
        (∀ (Q : V ≃ₗᵢ[ℝ] V) t x, f t (Q x) = f t x) →
        ∀ t (Q : V ≃ₗᵢ[ℝ] V) x, u t (Q x) = u t x) ∧
      ((∀ t x, star (f t x) = f t x) → ∀ t x, star (u t x) = u t x) := by
  obtain ⟨u₀, hu0, hC4, hd, ⟨U, hU⟩, ⟨M, hM, hD4⟩, hrad₀, hreal₀⟩ :=
    exists_zero_data_solution hκ hΛ hL hC
      hR hR4 hγ hγ1 hH a ha ha1 haL haS haJ f hf0 hfB hfH
  have h0R : (0 : ℝ) ∈ Icc (0 : ℝ) R := ⟨le_rfl, hR.le⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℝ → V → ℂ, u = fun t => if t ∈ Icc (0 : ℝ) R then u₀ t else 0 :=
    ⟨_, rfl⟩
  have hue : ∀ t ∈ Icc (0 : ℝ) R, u t = u₀ t := fun t ht => by
    rw [hudef]
    simp only [if_pos ht]
  have hun : ∀ t, t ∉ Icc (0 : ℝ) R → u t = 0 := fun t ht => by
    rw [hudef]
    simp only [if_neg ht]
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0 h0R 0)
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hfB 0 0)
  have hΛ0 : 0 ≤ Λ := by linarith
  have huC4 : ∀ t, ContDiff ℝ 4 (u t) := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) R
    · rw [hue t ht]
      exact hC4 t ht
    · rw [hun t ht]
      exact contDiff_const
  have hud : ∀ t ∈ Icc (0 : ℝ) R, ∀ x, HasDerivWithinAt (fun s => u s x)
      (f t x - (a t x : ℂ) * Δ (Δ (u t)) x) (Icc 0 R) t := by
    intro t ht x
    rw [hue t ht]
    exact (hd t ht x).congr (fun s hs => by rw [hue s hs]) (by rw [hue t ht])
  have huU : ∀ t x, ‖u t x‖ ≤ U := by
    intro t x
    by_cases ht : t ∈ Icc (0 : ℝ) R
    · rw [hue t ht]
      exact hU t ht x
    · rw [hun t ht]
      simpa using hU0
  refine ⟨u, fun x => by rw [hue 0 h0R]; exact hu0 x, huC4, hud, ⟨U, huU⟩, ?_, ?_, ?_⟩
  rotate_left
  · intro hra hrf t Q x
    by_cases ht : t ∈ Icc (0 : ℝ) R
    · rw [hue t ht]
      exact hrad₀ hra hrf t ht Q x
    · rw [hun t ht]
      rfl
  · intro hfr t x
    by_cases ht : t ∈ Icc (0 : ℝ) R
    · rw [hue t ht]
      exact hreal₀ hfr t ht x
    · rw [hun t ht]
      simp
  -- the fourth derivatives
  obtain ⟨T4, hT4⟩ : ∃ T4 : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ, T4 = traceFour := ⟨_, rfl⟩
  have hbil : ∀ t x, Δ (Δ (u t)) x = T4 (iteratedFDeriv ℝ 4 (u t) x) := by
    intro t x
    rw [hT4]
    exact bilaplacian_eq_traceFour (u t) (huC4 t) x
  have hD4u : HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R}
      (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) M := by
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · have h := hD4.1 p hp
      simp only [hue p.2 hp]
      exact h
    · have h := hD4.2 p hp q hq
      simp only [hue p.2 hp, hue q.2 hq]
      exact h
  -- the time derivative
  have hfh : HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R} (fun p => f p.2 p.1) (Bf + 2 * H) := by
    refine ⟨fun p _ => (hfB p.2 p.1).trans (by linarith), fun p _ q _ => ?_⟩
    have h := hfH p.2 q.2 p.1 q.1
    have hx : ‖p.1 - q.1‖ ^ γ ≤ pdist p q ^ γ :=
      Real.rpow_le_rpow (norm_nonneg _) (by
        unfold pdist
        exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hγ.le
    have ht : |p.2 - q.2| ^ (γ / 4) ≤ pdist p q ^ γ := by
      have e3 : |p.2 - q.2| ^ (γ / 4) = (|p.2 - q.2| ^ ((1 : ℝ) / 4)) ^ γ := by
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      rw [e3]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) (by
        unfold pdist
        exact le_add_of_nonneg_left (norm_nonneg _)) hγ.le
    have hd0 : 0 ≤ pdist p q ^ γ := Real.rpow_nonneg (pdist_nonneg p q) _
    calc ‖f p.2 p.1 - f q.2 q.1‖ ≤ H * (‖p.1 - q.1‖ ^ γ + |p.2 - q.2| ^ (γ / 4)) := h
      _ ≤ (Bf + 2 * H) * pdist p q ^ γ := by
          nlinarith [mul_le_mul_of_nonneg_left hx hH, mul_le_mul_of_nonneg_left ht hH,
            mul_nonneg hBf0 hd0]
  have hah : HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R} (fun p => a p.2 p.1) (Λ + max L Λ) := by
    refine ⟨fun p _ => ?_, fun p hp q hq => ?_⟩
    · have h := ha p.2 p.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
      exact h.2.trans (le_add_of_nonneg_right (le_max_of_le_right hΛ0))
    · have hd0 : 0 ≤ pdist p q := pdist_nonneg p q
      have h1 : ‖a p.2 p.1 - a q.2 q.1‖ ≤ L * pdist p q := by
        have h := haL p.2 q.2 p.1 q.1
        have hts : |p.2 - q.2| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
        have hq4 : |p.2 - q.2| ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) := by
          have h3 := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (p.2 - q.2)) hts
            (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 ≤ 1)
          rwa [Real.rpow_one] at h3
        rw [Real.norm_eq_abs]
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hL)
        unfold pdist
        linarith
      have h2 : ‖a p.2 p.1 - a q.2 q.1‖ ≤ Λ := by
        have hp' := ha p.2 p.1
        have hq' := ha q.2 q.1
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hp'.1, hp'.2, hq'.1, hq'.2]
      have h3 := lip_bdd_holder hγ hγ1.le hd0 hL hΛ0 h1 h2
      exact h3.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hΛ0)
        (Real.rpow_nonneg hd0 _))
  have hTh := hD4u.clm T4
  have hprod := hah.smul hTh (by positivity) (by positivity)
  have hut0 := hfh.add hprod.neg
  obtain ⟨Mt, hMtdef⟩ : ∃ Mt : ℝ, Mt = Bf + 2 * H + 2 * (Λ + max L Λ) * (‖T4‖ * M) := ⟨_, rfl⟩
  have hMt0 : 0 ≤ Mt := by
    rw [hMtdef]
    positivity
  have hut : HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R}
      (fun p => f p.2 p.1 - (a p.2 p.1 : ℂ) * Δ (Δ (u p.2)) p.1) Mt := by
    have e : ∀ p : V × ℝ, f p.2 p.1 - (a p.2 p.1 : ℂ) * Δ (Δ (u p.2)) p.1
        = f p.2 p.1 + -(a p.2 p.1 • T4 (iteratedFDeriv ℝ 4 (u p.2) p.1)) := by
      intro p
      rw [hbil, Complex.real_smul]
      ring
    rw [hMtdef]
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · beta_reduce
      rw [e p]
      exact hut0.1 p hp
    · beta_reduce
      rw [e p, e q]
      exact hut0.2 p hp q hq
  -- the lower jets, uniformly in the centre
  obtain ⟨M₂, hM₂def⟩ : ∃ M₂ : ℝ, M₂ = M + Mt := ⟨_, rfl⟩
  have hM₂0 : 0 ≤ M₂ := by
    rw [hM₂def]
    positivity
  obtain ⟨CI, hCI, HI⟩ := within_lower_jet_interpolation (V := V) (E := ℂ) γ 1 1 2 hγ hγ1
    one_pos (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 * M₂ + CI * U := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    positivity
  have hloc : ∀ (x₀ : V) (j : ℕ), j ≤ 3 → HolderBound γ {p : V × ℝ | ‖p.1‖ < 1 ∧ p.2 ∈ Icc 0 R}
      (fun p => iteratedFDeriv ℝ j (u p.2) (x₀ + p.1)) K := by
    intro x₀ j hj
    have h := HI (fun t y => u t (x₀ + y))
      (fun t y => f t (x₀ + y) - (a t (x₀ + y) : ℂ) * Δ (Δ (u t)) (x₀ + y)) 0 R hR U M₂ hU0 hM₂0
      (fun t _ => (huC4 t).comp (contDiff_const.add contDiff_id))
      (fun t ht y _ => hud t ht (x₀ + y))
      (fun t ht y _ => by
        have h1 : ‖f t (x₀ + y) - (a t (x₀ + y) : ℂ) * Δ (Δ (u t)) (x₀ + y)‖ ≤ Mt :=
          hut.1 (x₀ + y, t) ht
        exact h1.trans (by rw [hM₂def]; linarith))
      (fun t _ y _ => huU t (x₀ + y))
      (fun t ht y _ => by
        have e : iteratedFDeriv ℝ 4 (fun y => u t (x₀ + y)) y
            = iteratedFDeriv ℝ 4 (u t) (x₀ + y) := by
          rw [iteratedFDeriv_comp_add_left]
        show ‖iteratedFDeriv ℝ 4 (fun y => u t (x₀ + y)) y‖ ≤ M₂
        rw [e]
        have h1 : ‖iteratedFDeriv ℝ 4 (u t) (x₀ + y)‖ ≤ M := hD4u.1 (x₀ + y, t) ht
        exact h1.trans (by rw [hM₂def]; linarith)) j hj
    rw [hKdef]
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · have h1 : ‖iteratedFDeriv ℝ j (fun y => u p.2 (x₀ + y)) p.1‖ ≤ 1 * M₂ + CI * U :=
        h.1 p hp
      rw [iteratedFDeriv_comp_add_left] at h1
      exact h1
    · have h1 : ‖iteratedFDeriv ℝ j (fun y => u p.2 (x₀ + y)) p.1
          - iteratedFDeriv ℝ j (fun y => u q.2 (x₀ + y)) q.1‖
          ≤ (1 * M₂ + CI * U) * pdist p q ^ γ := h.2 p hp q hq
      rw [iteratedFDeriv_comp_add_left, iteratedFDeriv_comp_add_left] at h1
      exact h1
  have hlow : ∀ j : ℕ, j ≤ 3 → HolderBound γ {p : V × ℝ | p.2 ∈ Icc 0 R}
      (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (2 * K) := by
    intro j hj
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · have h : ‖iteratedFDeriv ℝ j (u p.2) (p.1 + 0)‖ ≤ K :=
        (hloc p.1 j hj).1 (0, p.2) ⟨by simp, hp⟩
      rw [add_zero] at h
      exact h.trans (by linarith)
    · have hd0 : 0 ≤ pdist p q := pdist_nonneg p q
      by_cases hpq : ‖q.1 - p.1‖ < 1
      · have h : ‖iteratedFDeriv ℝ j (u p.2) (p.1 + 0)
            - iteratedFDeriv ℝ j (u q.2) (p.1 + (q.1 - p.1))‖
            ≤ K * pdist ((0 : V), p.2) (q.1 - p.1, q.2) ^ γ :=
          (hloc p.1 j hj).2 (0, p.2) ⟨by simp, hp⟩ (q.1 - p.1, q.2) ⟨hpq, hq⟩
        rw [add_zero, add_sub_cancel] at h
        have e : pdist ((0 : V), p.2) (q.1 - p.1, q.2) = pdist p q := by
          unfold pdist
          simp only [zero_sub, norm_neg]
          rw [norm_sub_rev]
        rw [e] at h
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd0 _))
      · have h1 : ‖iteratedFDeriv ℝ j (u p.2) (p.1 + 0)‖ ≤ K :=
          (hloc p.1 j hj).1 (0, p.2) ⟨by simp, hp⟩
        have h2 : ‖iteratedFDeriv ℝ j (u q.2) (q.1 + 0)‖ ≤ K :=
          (hloc q.1 j hj).1 (0, q.2) ⟨by simp, hq⟩
        rw [add_zero] at h1 h2
        have h3 : (1 : ℝ) ≤ pdist p q ^ γ := by
          refine Real.one_le_rpow ?_ hγ.le
          unfold pdist
          have h4 : 1 ≤ ‖p.1 - q.1‖ := by
            rw [norm_sub_rev]
            exact not_lt.1 hpq
          linarith [Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)]
        calc ‖iteratedFDeriv ℝ j (u p.2) p.1 - iteratedFDeriv ℝ j (u q.2) q.1‖
            ≤ ‖iteratedFDeriv ℝ j (u p.2) p.1‖ + ‖iteratedFDeriv ℝ j (u q.2) q.1‖ :=
              norm_sub_le _ _
          _ ≤ 2 * K := by linarith
          _ ≤ 2 * K * pdist p q ^ γ := le_mul_of_one_le_right (by positivity) h3
  refine ⟨2 * K + M + Mt, by positivity, fun j hj => ?_, hut.mono (by linarith)⟩
  by_cases hj3 : j ≤ 3
  · exact (hlow j hj3).mono (by linarith)
  · have hj4 : j = 4 := by omega
    subst hj4
    exact hD4u.mono (by linarith)

end Calabi.FlatZero
