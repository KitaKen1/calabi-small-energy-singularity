import Calabi.Correction.Commute

/-!
# Spatial smoothness of the solution in a chart

* `timeDeriv_fderiv_apply`: the time derivative commutes with a derivative in
  a direction, for functions of the local class of order one;
* `fderiv_equation`: the derivative in a direction of the equation
  `u_t + a Δ² u = f`;
* `linear_ladder`: if the coefficient and the source are of the class of order
  `k`, a solution of the class of order four is of the class of order `k + 4`,
  and its time derivative of the class of order `k`. The proof is by induction
  on `k`, with `Sm.diffquot` for one derivative and the differentiated equation
  for the next ones, so that no Leibniz formula of higher order is needed;
* `chart_space_smooth`: the chart form of the Calabi flow
  `h_t + (1 + v h)² (chartOp m h) / 16 = 0` is of this type with coefficient
  and source built from `h`; hence `h` is in the local classes of all orders.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The mean value form of a difference quotient. -/
theorem dq_eq_fderiv {u : V → ℝ} (hu : ContDiff ℝ 1 u) {h : ℝ} (hh : h ≠ 0) (e : V) (z : V) :
    ∃ ξ ∈ Ioo (0 : ℝ) 1, dq h e u z = fderiv ℝ u (z + (ξ * h) • e) e := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => u (z + (r * h) • e))
      (h * fderiv ℝ u (z + (s * h) • e) e) s := by
    intro s
    have hline : HasDerivAt (fun r : ℝ => z + (r * h) • e) (h • e) s := by
      have h1 := (((hasDerivAt_id s).mul_const h).smul_const e).const_add z
      simpa using h1
    have h1 : HasFDerivAt u (fderiv ℝ u (z + (s * h) • e)) (z + (s * h) • e) :=
      (hu.differentiable one_ne_zero _).hasFDerivAt
    have h2 := h1.comp_hasDerivAt s hline
    rw [map_smul, smul_eq_mul] at h2
    exact h2
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun r : ℝ => u (z + (r * h) • e))
    (fun s => h * fderiv ℝ u (z + (s * h) • e) e) zero_lt_one
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt) (fun s _ => hderiv s)
  refine ⟨ξ, hξ, ?_⟩
  have h1 : h * fderiv ℝ u (z + (ξ * h) • e) e = u (z + h • e) - u z := by
    rw [hξe]
    simp
  unfold dq
  rw [← h1]
  field_simp

set_option maxHeartbeats 1600000 in
/-- **The time derivative commutes with a derivative in a direction.** -/
theorem timeDeriv_fderiv_apply {α : ℝ} (hα : 0 < α) {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω)
    {g g' : ℝ → V → ℝ} (hg : Sm α Ω 1 g) (hg' : Sm α Ω 1 g')
    (hd : ∀ p ∈ Ω, HasDerivAt (fun t => g t p.1) (g' p.2 p.1) p.2) (e : V) :
    ∀ p ∈ Ω, HasDerivAt (fun t => fderiv ℝ (g t) p.1 e) (fderiv ℝ (g' p.2) p.1 e) p.2 := by
  intro p₀ hp₀
  obtain ⟨Ng, G, Mg, hNg, hpg, hMg, hgG, hsG0, hWG⟩ := hg p₀ hp₀
  obtain ⟨Ng', G', M', hNg', hpg', hM', hgG', hsG'0, hWG'⟩ := hg' p₀ hp₀
  have hsG : ∀ t, ContDiff ℝ 1 (G t) := fun t => by exact_mod_cast hsG0 t
  have hsG' : ∀ t, ContDiff ℝ 1 (G' t) := fun t => by exact_mod_cast hsG'0 t
  have hopen : IsOpen (Ng ∩ Ng' ∩ Ω) := (hNg.inter hNg').inter hΩ
  have hmem : p₀ ∈ Ng ∩ Ng' ∩ Ω := ⟨⟨hpg, hpg'⟩, hp₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen p₀ hmem
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min ε (1 / 4) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min hε (by norm_num)
  have hρε : ρ ≤ ε := by
    rw [hρdef]
    exact min_le_left _ _
  have hρ4 : ρ ≤ 1 / 4 := by
    rw [hρdef]
    exact min_le_right _ _
  have hρ1 : ρ ≤ 1 := by linarith
  have hbox : pbox p₀ ρ ⊆ Ng ∩ Ng' ∩ Ω := fun p hp =>
    hball (Metric.ball_subset_ball hρε (pbox_subset_ball p₀ hρ.le hρ1 hp))
  have hdiam : ∀ p ∈ pbox p₀ ρ, ∀ q ∈ pbox p₀ ρ, pdist p q ≤ 1 := fun p hp q hq =>
    (pdist_le_of_pbox hρ.le hp hq).trans (by linarith)
  have hJ' := holderBound_fderiv (k := 1) le_rfl hM' hWG' (fun p hp => (hbox hp).1.2) hdiam
  -- the time derivative of the representative
  have hD : ∀ p ∈ pbox p₀ ρ, HasDerivAt (fun t => G t p.1) (G' p.2 p.1) p.2 := by
    intro p hp
    have h1 := hd p (hbox hp).2
    rw [← hgG' p (hbox hp).1.2] at h1
    exact h1.congr_of_eventuallyEq (time_eventuallyEq hNg hgG (hbox hp).1.1)
  -- the steps
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  obtain ⟨hn, hhndef⟩ : ∃ hn : ℕ → ℝ,
      hn = fun n : ℕ => ρ / 2 / ((‖e‖ + 1) * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hhn_pos : ∀ n, 0 < hn n := fun n => by
    rw [hhndef]
    positivity
  have hhn_e : ∀ n, hn n * ‖e‖ ≤ ρ / 2 := fun n => by
    have h1 : hn n * ((‖e‖ + 1) * (n + 1)) = ρ / 2 := by
      rw [hhndef]
      field_simp
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h3 : hn n * ‖e‖ ≤ hn n * ((‖e‖ + 1) * (n + 1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (hhn_pos n).le
    linarith
  have hhn_tend : Tendsto hn atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ρ / 2 / (‖e‖ + 1) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (ρ / 2 / (‖e‖ + 1) * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    rw [hhndef]
    field_simp
  -- the points of the segments
  have hmemT : ∀ t : ℝ, |t - p₀.2| < (ρ / 2) ^ 4 → ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ n,
      ((p₀.1 + (s * hn n) • e, t) : V × ℝ) ∈ pbox p₀ ρ := by
    intro t ht s hs n
    refine ⟨?_, ht.trans_le (pow_le_pow_left₀ (by positivity) (by linarith) 4)⟩
    show ‖p₀.1 + (s * hn n) • e - p₀.1‖ < ρ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1,
      abs_of_pos (hhn_pos n)]
    have h1 : s * hn n * ‖e‖ ≤ 1 * (hn n * ‖e‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hs.2 (mul_nonneg (hhn_pos n).le he0)
    linarith [hhn_e n]
  have hmem0 : ∀ t : ℝ, |t - p₀.2| < (ρ / 2) ^ 4 → ((p₀.1, t) : V × ℝ) ∈ pbox p₀ ρ := by
    intro t ht
    have h1 := hmemT t ht 0 ⟨le_rfl, zero_le_one⟩ 0
    simpa using h1
  have hsopen : IsOpen (Metric.ball p₀.2 ((ρ / 2) ^ 4)) := Metric.isOpen_ball
  have hsmem : ∀ t ∈ Metric.ball p₀.2 ((ρ / 2) ^ 4), |t - p₀.2| < (ρ / 2) ^ 4 := fun t ht => by
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  -- the derivative of the limit
  have hmain : HasDerivAt (fun t => fderiv ℝ (G t) p₀.1 e) (fderiv ℝ (G' p₀.2) p₀.1 e) p₀.2 := by
    refine hasDerivAt_of_tendstoUniformlyOn (l := atTop)
      (f := fun n t => dq (hn n) e (G t) p₀.1) (f' := fun n t => dq (hn n) e (G' t) p₀.1)
      (g' := fun t => fderiv ℝ (G' t) p₀.1 e) hsopen ?_ ?_ ?_
      (Metric.mem_ball_self (by positivity))
    · -- uniform convergence of the derivatives
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      have hpow : Tendsto (fun n => M' * ‖e‖ * (hn n * ‖e‖) ^ α) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => hn n * ‖e‖) atTop (𝓝 0) := by
          have := hhn_tend.mul_const ‖e‖
          rwa [zero_mul] at this
        have h2 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h1
        rw [Real.zero_rpow hα.ne'] at h2
        have h3 := h2.const_mul (M' * ‖e‖)
        rwa [mul_zero] at h3
      filter_upwards [hpow.eventually (gt_mem_nhds hδ)] with n hnδ t ht
      have ht' := hsmem t ht
      obtain ⟨ξ, hξ, hξe⟩ := dq_eq_fderiv (hsG' t) (hhn_pos n).ne' e p₀.1
      rw [Real.dist_eq, hξe, ← ContinuousLinearMap.sub_apply]
      have hP := hmemT t ht' ξ ⟨hξ.1.le, hξ.2.le⟩ n
      have hQ := hmem0 t ht'
      have h1 := hJ'.2 _ hP _ hQ
      have hpd : pdist ((p₀.1 + (ξ * hn n) • e, t) : V × ℝ) (p₀.1, t) ≤ hn n * ‖e‖ := by
        unfold pdist
        simp only [add_sub_cancel_left, sub_self, abs_zero]
        rw [Real.zero_rpow (by norm_num), add_zero, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_pos hξ.1, abs_of_pos (hhn_pos n)]
        have h2 : ξ * hn n * ‖e‖ ≤ 1 * (hn n * ‖e‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hξ.2.le (mul_nonneg (hhn_pos n).le he0)
        linarith
      have h2 : pdist ((p₀.1 + (ξ * hn n) • e, t) : V × ℝ) (p₀.1, t) ^ α
          ≤ (hn n * ‖e‖) ^ α := Real.rpow_le_rpow (pdist_nonneg _ _) hpd hα.le
      calc |(fderiv ℝ (G' t) p₀.1 - fderiv ℝ (G' t) (p₀.1 + (ξ * hn n) • e)) e|
          ≤ ‖fderiv ℝ (G' t) p₀.1 - fderiv ℝ (G' t) (p₀.1 + (ξ * hn n) • e)‖ * ‖e‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (G' t) (p₀.1 + (ξ * hn n) • e) - fderiv ℝ (G' t) p₀.1‖ * ‖e‖ := by
            rw [norm_sub_rev]
        _ ≤ M' * (hn n * ‖e‖) ^ α * ‖e‖ :=
            mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hM')) he0
        _ = M' * ‖e‖ * (hn n * ‖e‖) ^ α := by ring
        _ < δ := hnδ
    · -- the derivatives of the difference quotients
      refine Eventually.of_forall fun n t ht => ?_
      have ht' := hsmem t ht
      have h1 := hD _ (hmemT t ht' 1 ⟨zero_le_one, le_rfl⟩ n)
      have h0 := hD _ (hmem0 t ht')
      rw [one_mul] at h1
      exact (h1.sub h0).const_mul (hn n)⁻¹
    · -- the pointwise limit
      intro t _
      exact tendsto_dq ((hsG t).differentiable one_ne_zero _) e hhn_tend
        (fun n => (hhn_pos n).ne')
  -- back to the original functions
  have hval : fderiv ℝ (g' p₀.2) p₀.1 e = fderiv ℝ (G' p₀.2) p₀.1 e := by
    rw [(slice_eventuallyEq hNg' hgG' hpg').fderiv_eq]
  rw [hval]
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hsopen.mem_nhds (Metric.mem_ball_self (by positivity))] with t ht
  have hmemt := (hbox (hmem0 t (hsmem t ht))).1.1
  show fderiv ℝ (g t) p₀.1 e = fderiv ℝ (G t) p₀.1 e
  rw [(slice_eventuallyEq hNg hgG (p := (p₀.1, t)) hmemt).fderiv_eq]

/-- A slice of a function of the local class of order `k` is `C^k` near the
point. -/
theorem Sm.contDiffAt {α : ℝ} {Ω : Set (V × ℝ)} {k : ℕ} {g : ℝ → V → ℝ} (h : Sm α Ω k g)
    {p : V × ℝ} (hp : p ∈ Ω) : ContDiffAt ℝ k (g p.2) p.1 := by
  obtain ⟨N, g', M, hN, hpN, hM, hgg, hs, hW⟩ := h p hp
  exact (hs p.2).contDiffAt.congr_of_eventuallyEq (slice_eventuallyEq hN hgg hpN).symm

/-- **The derivative of the equation in a direction.** -/
theorem fderiv_equation {α : ℝ} {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω) {u ut a f : ℝ → V → ℝ}
    (hu : Sm α Ω 5 u) (hut : Sm α Ω 1 ut) (ha : Sm α Ω 1 a) (hf : Sm α Ω 1 f)
    (heq : ∀ p ∈ Ω, ut p.2 p.1 + a p.2 p.1 * Δ (Δ (u p.2)) p.1 = f p.2 p.1) (e : V) :
    ∀ p ∈ Ω, fderiv ℝ (ut p.2) p.1 e + a p.2 p.1 * Δ (Δ (fun y => fderiv ℝ (u p.2) y e)) p.1
      = fderiv ℝ (f p.2) p.1 e - fderiv ℝ (a p.2) p.1 e * Δ (Δ (u p.2)) p.1 := by
  intro p hp
  have hu5 : ContDiffAt ℝ 5 (u p.2) p.1 := by exact_mod_cast hu.contDiffAt hp
  have hutd : DifferentiableAt ℝ (ut p.2) p.1 :=
    (hut.contDiffAt hp).differentiableAt (by norm_num)
  have had : DifferentiableAt ℝ (a p.2) p.1 := (ha.contDiffAt hp).differentiableAt (by norm_num)
  have hB1 : ContDiffAt ℝ 1 (Δ (Δ (u p.2))) p.1 := by
    have h5 : ContDiffAt ℝ ((3 + 2 : ℕ) : WithTop ℕ∞) (u p.2) p.1 := by exact_mod_cast hu5
    have h3 : ContDiffAt ℝ ((1 + 2 : ℕ) : WithTop ℕ∞) (Δ (u p.2)) p.1 := by
      exact_mod_cast contDiffAt_laplacian (n := 3) h5
    exact_mod_cast contDiffAt_laplacian (n := 1) h3
  have hBd : DifferentiableAt ℝ (Δ (Δ (u p.2))) p.1 := hB1.differentiableAt one_ne_zero
  -- the equation near the point
  have hc : Continuous fun z : V => ((z, p.2) : V × ℝ) := continuous_id.prodMk continuous_const
  have hev : (fun y => ut p.2 y + a p.2 y * Δ (Δ (u p.2)) y) =ᶠ[𝓝 p.1] f p.2 := by
    filter_upwards [(hΩ.preimage hc).mem_nhds hp] with y hy
    exact heq (y, p.2) hy
  have hmul : HasFDerivAt (fun y => a p.2 y * Δ (Δ (u p.2)) y)
      (a p.2 p.1 • fderiv ℝ (Δ (Δ (u p.2))) p.1 + Δ (Δ (u p.2)) p.1 • fderiv ℝ (a p.2) p.1)
      p.1 := had.hasFDerivAt.mul hBd.hasFDerivAt
  have hsum : HasFDerivAt (fun y => ut p.2 y + a p.2 y * Δ (Δ (u p.2)) y)
      (fderiv ℝ (ut p.2) p.1 + (a p.2 p.1 • fderiv ℝ (Δ (Δ (u p.2))) p.1
        + Δ (Δ (u p.2)) p.1 • fderiv ℝ (a p.2) p.1)) p.1 := hutd.hasFDerivAt.add hmul
  have h2 := hev.fderiv_eq (𝕜 := ℝ)
  rw [hsum.fderiv] at h2
  have h3 := congrArg (fun L : V →L[ℝ] ℝ => L e) h2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h3
  rw [bilaplacian_fderiv_apply hu5 e]
  linarith

set_option maxHeartbeats 1600000 in
/-- **The linear ladder.** -/
theorem linear_ladder {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω)
    (k : ℕ) : ∀ a u ut f : ℝ → V → ℝ, Sm α Ω k a → (∀ p ∈ Ω, 0 < a p.2 p.1) → Sm α Ω 4 u →
      Sm α Ω 0 ut → (∀ p ∈ Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) → Sm α Ω k f →
      (∀ p ∈ Ω, ut p.2 p.1 + a p.2 p.1 * Δ (Δ (u p.2)) p.1 = f p.2 p.1) →
      Sm α Ω (k + 4) u ∧ Sm α Ω k ut := by
  induction k with
  | zero =>
    intro a u ut f _ _ hu hut _ _ _
    exact ⟨hu, hut⟩
  | succ k ih =>
    intro a u ut f ha hpos hu hut hd hf heq
    have ha1 : Sm α Ω 1 a := ha.of_le (by omega)
    have hf1 : Sm α Ω 1 f := hf.of_le (by omega)
    have hu1 : Sm α Ω 1 u := hu.of_le (by norm_num)
    -- one derivative
    have hpart : ∀ e : V, Sm α Ω 4 (fun t z => fderiv ℝ (u t) z e) := fun e =>
      Sm.diffquot hα hα1 hΩ hu hut hd ha1 hf1 hpos heq e
    have hu5 : Sm α Ω 5 u := Sm.of_partials hu1 fun i => hpart _
    have hB1 : Sm α Ω 1 (fun t => Δ (Δ (u t))) :=
      Sm.bilaplacian hα.le hα1.le hΩ (show Sm α Ω (1 + 4) u from hu5)
    have hut1 : Sm α Ω 1 ut :=
      (hf1.sub hα.le hα1.le (ha1.mul hB1)).congr hΩ fun p hp => by
        have := heq p hp
        show ut p.2 p.1 = f p.2 p.1 - a p.2 p.1 * Δ (Δ (u p.2)) p.1
        linarith
    -- the regularity of the previous order
    obtain ⟨huk, -⟩ := ih a u ut f (ha.of_le (by omega)) hpos hu hut hd (hf.of_le (by omega)) heq
    have hBk : Sm α Ω k (fun t => Δ (Δ (u t))) := Sm.bilaplacian hα.le hα1.le hΩ huk
    -- the derivatives satisfy an equation of the same type
    have hder : ∀ e : V, Sm α Ω (k + 4) (fun t z => fderiv ℝ (u t) z e)
        ∧ Sm α Ω k (fun t z => fderiv ℝ (ut t) z e) := by
      intro e
      refine ih a (fun t z => fderiv ℝ (u t) z e) (fun t z => fderiv ℝ (ut t) z e)
        (fun t z => fderiv ℝ (f t) z e - fderiv ℝ (a t) z e * Δ (Δ (u t)) z)
        (ha.of_le (by omega)) hpos (hpart e) (hut1.fderiv_apply e)
        (timeDeriv_fderiv_apply hα hΩ hu1 hut1 hd e)
        ((hf.fderiv_apply e).sub hα.le hα1.le ((ha.fderiv_apply e).mul hBk))
        (fderiv_equation hΩ hu5 hut1 ha1 hf1 heq e)
    have e5 : k + 1 + 4 = k + 4 + 1 := by omega
    rw [e5]
    exact ⟨Sm.of_partials hu1 fun i => (hder _).1, Sm.of_partials hut1 fun i => (hder _).2⟩

set_option maxHeartbeats 1600000 in
/-- **Spatial smoothness of a solution of the chart equation.** -/
theorem chart_space_smooth {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Ω : Set (V × ℝ)}
    (hΩ : IsOpen Ω) (hball : ∀ p ∈ Ω, ‖p.1‖ < 1) (m : ℝ) {v : V → ℝ} (hv : ContDiff ℝ ∞ v)
    {h ht : ℝ → V → ℝ} (hh : Sm α Ω 4 h) (hht : Sm α Ω 0 ht)
    (hd : ∀ p ∈ Ω, HasDerivAt (fun t => h t p.1) (ht p.2 p.1) p.2)
    (hpos : ∀ p ∈ Ω, 0 < 1 + v p.1 * h p.2 p.1)
    (heq : ∀ p ∈ Ω, ht p.2 p.1 + (1 + v p.1 * h p.2 p.1) ^ 2 * (chartOp m (h p.2) p.1 / 16) = 0) :
    ∀ k : ℕ, Sm α Ω (k + 4) h ∧ Sm α Ω k ht := by
  intro k
  induction k with
  | zero => exact ⟨hh, hht⟩
  | succ k ih =>
    have hn : ContDiff ℝ ∞ fun z : V => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
    have hhk : Sm α Ω (k + 1) h := ih.1.of_le (by omega)
    have hb : Sm α Ω (k + 1) (fun t z => 1 + v z * h t z) :=
      (Sm.of_contDiff hα.le hα1.le (contDiff_const (c := (1 : ℝ))) Ω (k + 1)).add
        ((Sm.of_contDiff hα.le hα1.le hv Ω (k + 1)).mul hhk)
    have hc : Sm α Ω (k + 1) (fun (_ : ℝ) (z : V) => (1 - ‖z‖ ^ 2) ^ 2 / 16) :=
      Sm.of_contDiff hα.le hα1.le (((contDiff_const.sub hn).pow 2).div_const 16) Ω (k + 1)
    have ha : Sm α Ω (k + 1) (fun t z => (1 + v z * h t z) * (1 + v z * h t z)
        * ((1 - ‖z‖ ^ 2) ^ 2 / 16)) := (hb.mul hb).mul hc
    have hlow : Sm α Ω (k + 1) (fun t => lowOp m (h t)) :=
      Sm.lowOp hα.le hα1.le hΩ m (show Sm α Ω (k + 1 + 3) h from ih.1)
    have hf : Sm α Ω (k + 1) (fun t z => -1 / 16 * ((1 + v z * h t z) * (1 + v z * h t z)
        * lowOp m (h t) z)) := ((hb.mul hb).mul hlow).const_mul hα.le hα1.le (-1 / 16)
    refine linear_ladder hα hα1 hΩ (k + 1) _ h ht _ ha (fun p hp => ?_) hh hht hd hf
      (fun p hp => ?_)
    · have h1 := hpos p hp
      have h2 : 0 < 1 - ‖p.1‖ ^ 2 := by
        have := hball p hp
        nlinarith [norm_nonneg p.1]
      positivity
    · have h1 := heq p hp
      rw [chartOp_eq_lowOp] at h1
      linear_combination h1

end Calabi.Weighted
