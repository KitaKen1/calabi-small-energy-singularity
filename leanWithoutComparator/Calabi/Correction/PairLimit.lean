import Calabi.Correction.OuterPair
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The limit of a sequence of pairs with geometrically decaying increments

The iteration of `Newton.lean` produces pairs `u n` whose increments
`u (n + 1) - u n` are bounded by `A (3/4)ⁿ` in the norms of the jets and of the
time derivatives. This file constructs the limit pair:

* `limFn`: the limit of a sequence of chart functions, as a series (it is set
  to zero outside the time interval `[-T, 0)`, where no bound is available);
* `chart_limit`: in one chart, the limit is `C⁴` in space, has a time
  derivative on `(-T, 0)`, and the jets and the time derivatives converge
  pointwise;
* `pairLim`, `pairLim_spec`: the limit pair is regular, has the time
  derivatives and the radial symmetry of the iterates, inherits their bounds,
  and the quantities of order zero `V`, `∂ₜ V`, `A V` converge pointwise.

The spatial regularity is `contDiff_tsum` for each fixed time: on a compact
subinterval of `[-T, 0)` the scale is bounded above and below, so the weighted
bounds are uniform bounds.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

section Series

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A series of `C⁴` functions with summable uniform bounds of the jets. -/
theorem tsum_jets {g : ℕ → V → ℝ} {b : ℕ → ℝ} (hg : ∀ n, ContDiff ℝ 4 (g n)) (hb : Summable b)
    (hbd : ∀ n z, ∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j (g n) z‖ ≤ b n) :
    ContDiff ℝ 4 (fun z => ∑' n, g n z) ∧
      ∀ j : ℕ, j ≤ 4 → ∀ z, HasSum (fun n => iteratedFDeriv ℝ j (g n) z)
        (iteratedFDeriv ℝ j (fun z => ∑' n, g n z) z) := by
  have h4 : ((4 : ℕ∞) : WithTop ℕ∞) = 4 := rfl
  have hg' : ∀ n, ContDiff ℝ ((4 : ℕ∞) : WithTop ℕ∞) (g n) := fun n => by
    rw [h4]
    exact hg n
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ 4 → Summable ((fun _ n => b n : ℕ → ℕ → ℝ) k) := fun _ _ => hb
  have h'f : ∀ (k : ℕ) (i : ℕ) (x : V), (k : ℕ∞) ≤ 4 →
      ‖iteratedFDeriv ℝ k (g i) x‖ ≤ (fun _ n => b n : ℕ → ℕ → ℝ) k i :=
    fun k i x hk => hbd i x k (by exact_mod_cast hk)
  constructor
  · have h := contDiff_tsum hg' hv h'f
    rwa [h4] at h
  · intro j hj z
    have hk : ((j : ℕ) : ℕ∞) ≤ 4 := by exact_mod_cast hj
    have e := congrFun (iteratedFDeriv_tsum hg' hv h'f hk) z
    rw [e]
    exact (Summable.of_norm_bounded hb (fun n => hbd n z j hj)).hasSum

/-- Two-point bounds pass to pointwise limits. -/
theorem WH.of_tendsto {E : Type*} [NormedAddCommGroup E] {α a w M : ℝ} {s : V × ℝ → ℝ}
    {Ω : Set (V × ℝ)} {f : ℕ → V × ℝ → E} {g : V × ℝ → E} (h : ∀ n, WH α a s Ω w M (f n))
    (hlim : ∀ p ∈ Ω, Tendsto (fun n => f n p) atTop (𝓝 (g p))) : WH α a s Ω w M g :=
  ⟨fun p hp => le_of_tendsto' (hlim p hp).norm fun n => (h n).1 p hp,
    fun p hp q hq hd => le_of_tendsto' ((hlim p hp).sub (hlim q hq)).norm
      fun n => (h n).2 p hp q hq hd⟩

/-- The limit of a sequence of chart functions with summable increments. It is
set to zero outside the time interval `[-T, 0)`. -/
noncomputable def limFn (T : ℝ) (v : ℕ → ℝ → V → ℝ) (t : ℝ) (z : V) : ℝ :=
  if t ∈ Ico (-T) 0 then v 0 t z + ∑' n, (v (n + 1) t z - v n t z) else 0

theorem limFn_of_mem {T : ℝ} (v : ℕ → ℝ → V → ℝ) {t : ℝ} (ht : t ∈ Ico (-T) 0) (z : V) :
    limFn T v t z = v 0 t z + ∑' n, (v (n + 1) t z - v n t z) := by
  unfold limFn
  rw [if_pos ht]

set_option maxHeartbeats 1600000 in
/-- **The limit in one chart.** -/
theorem chart_limit {T R R' α a w A hi : ℝ} {s : V × ℝ → ℝ} (hRR : R' ≤ R) (hA : 0 ≤ A)
    (v vt : ℕ → ℝ → V → ℝ) (hC4 : ∀ n t, ContDiff ℝ 4 (v n t))
    (hsupp : ∀ n t z, R' < ‖z‖ ^ 2 → v n t z = 0)
    (hsuppt : ∀ n t z, R' < ‖z‖ ^ 2 → vt n t z = 0)
    (hder : ∀ n, ∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => v n r z) (vt n t z) t)
    (hdJ : ∀ n, WJ α a s {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ R} w (A * (3 / 4) ^ n) 4
      (fun t z => v (n + 1) t z - v n t z))
    (hdT : ∀ n, WH α a s {p : V × ℝ | p.2 ∈ Ico (-T) 0 ∧ ‖p.1‖ ^ 2 ≤ R} (w - 4)
      (A * (3 / 4) ^ n) (fun p => vt (n + 1) p.2 p.1 - vt n p.2 p.1))
    (hs : ∀ t₂ : ℝ, t₂ < 0 → ∃ lo : ℝ, 0 < lo ∧ ∀ p : V × ℝ, p.2 ∈ Ico (-T) 0 →
      ‖p.1‖ ^ 2 ≤ R → p.2 ≤ t₂ → lo ≤ s p ∧ s p ≤ hi) :
    (∀ t, ContDiff ℝ 4 (limFn T v t)) ∧ (∀ t z, R' < ‖z‖ ^ 2 → limFn T v t z = 0) ∧
    (∀ t z, R' < ‖z‖ ^ 2 → limFn T vt t z = 0) ∧
    (∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => limFn T v r z) (limFn T vt t z) t) ∧
    (∀ t ∈ Ico (-T) 0, ∀ z, ∀ j : ℕ, j ≤ 4 →
      Tendsto (fun n => iteratedFDeriv ℝ j (v n t) z) atTop
        (𝓝 (iteratedFDeriv ℝ j (limFn T v t) z))) ∧
    (∀ t ∈ Ico (-T) 0, ∀ z, Tendsto (fun n => vt n t z) atTop (𝓝 (limFn T vt t z))) := by
  have hsumq : Summable (fun n : ℕ => A * (3 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
  have hAq : ∀ n : ℕ, 0 ≤ A * (3 / 4 : ℝ) ^ n := fun n => by positivity
  -- uniform bounds up to a time before the final one
  have key : ∀ t₂ : ℝ, t₂ < 0 → ∃ K : ℝ, 0 ≤ K ∧
      (∀ n, ∀ t ∈ Ico (-T) 0, t ≤ t₂ → ∀ z, ∀ j : ℕ, j ≤ 4 →
        ‖iteratedFDeriv ℝ j (fun z => v (n + 1) t z - v n t z) z‖ ≤ K * (A * (3 / 4) ^ n)) ∧
      (∀ n, ∀ t ∈ Ico (-T) 0, t ≤ t₂ → ∀ z,
        ‖vt (n + 1) t z - vt n t z‖ ≤ K * (A * (3 / 4) ^ n)) := by
    intro t₂ ht₂
    obtain ⟨lo, hlo, hlohi⟩ := hs t₂ ht₂
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
        K = ∑ j ∈ Finset.range 5, max (lo ^ (w - (j : ℝ))) (hi ^ (w - (j : ℝ))) := ⟨_, rfl⟩
    have hterm : ∀ j : ℕ, 0 ≤ max (lo ^ (w - (j : ℝ))) (hi ^ (w - (j : ℝ))) := fun j =>
      le_max_of_le_left (Real.rpow_nonneg hlo.le _)
    have hK : 0 ≤ K := by
      rw [hKdef]
      exact Finset.sum_nonneg fun j _ => hterm j
    have hle : ∀ j : ℕ, j ≤ 4 → max (lo ^ (w - (j : ℝ))) (hi ^ (w - (j : ℝ))) ≤ K := by
      intro j hj
      rw [hKdef]
      exact Finset.single_le_sum
        (f := fun j : ℕ => max (lo ^ (w - (j : ℝ))) (hi ^ (w - (j : ℝ))))
        (fun i _ => hterm i) (Finset.mem_range.2 (by omega))
    refine ⟨K, hK, ?_, ?_⟩
    · intro n t ht htt z j hj
      rcases le_or_gt (‖z‖ ^ 2) R with hz | hz
      · have h1 : ‖iteratedFDeriv ℝ j (fun z => v (n + 1) t z - v n t z) z‖
            ≤ A * (3 / 4) ^ n * s (z, t) ^ (w - (j : ℝ)) := (hdJ n j hj).1 (z, t) ⟨ht, hz⟩
        have hsb := hlohi (z, t) ht hz htt
        have h2 : s (z, t) ^ (w - (j : ℝ)) ≤ K :=
          (rpow_le_max hlo hsb.1 hsb.2 _).trans (hle j hj)
        calc ‖iteratedFDeriv ℝ j (fun z => v (n + 1) t z - v n t z) z‖
            ≤ A * (3 / 4) ^ n * s (z, t) ^ (w - (j : ℝ)) := h1
          _ ≤ A * (3 / 4) ^ n * K := mul_le_mul_of_nonneg_left h2 (hAq n)
          _ = K * (A * (3 / 4) ^ n) := by ring
      · have hopen : IsOpen {y : V | R' < ‖y‖ ^ 2} :=
          isOpen_lt continuous_const (continuous_norm.pow 2)
        have hev : (fun y => v (n + 1) t y - v n t y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hopen.mem_nhds (lt_of_le_of_lt hRR hz)] with y hy
          rw [hsupp (n + 1) t y hy, hsupp n t y hy, sub_zero]
        rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
        have e0 : iteratedFDeriv ℝ j (fun _ : V => (0 : ℝ)) z = 0 := by simp
        rw [e0, norm_zero]
        exact mul_nonneg hK (hAq n)
    · intro n t ht htt z
      rcases le_or_gt (‖z‖ ^ 2) R with hz | hz
      · have h1 : ‖vt (n + 1) t z - vt n t z‖ ≤ A * (3 / 4) ^ n * s (z, t) ^ (w - 4) :=
          (hdT n).1 (z, t) ⟨ht, hz⟩
        have hsb := hlohi (z, t) ht hz htt
        have h2 : s (z, t) ^ (w - 4) ≤ K := by
          have h3 := (rpow_le_max hlo hsb.1 hsb.2 (w - ((4 : ℕ) : ℝ))).trans (hle 4 le_rfl)
          have e4 : w - ((4 : ℕ) : ℝ) = w - 4 := by norm_num
          rwa [e4] at h3
        calc ‖vt (n + 1) t z - vt n t z‖ ≤ A * (3 / 4) ^ n * s (z, t) ^ (w - 4) := h1
          _ ≤ A * (3 / 4) ^ n * K := mul_le_mul_of_nonneg_left h2 (hAq n)
          _ = K * (A * (3 / 4) ^ n) := by ring
      · have hz' : R' < ‖z‖ ^ 2 := lt_of_le_of_lt hRR hz
        rw [hsuppt (n + 1) t z hz', hsuppt n t z hz', sub_zero, norm_zero]
        exact mul_nonneg hK (hAq n)
  -- the series of the increments at a fixed time
  have hser : ∀ t ∈ Ico (-T) 0,
      ContDiff ℝ 4 (fun z => ∑' n, (v (n + 1) t z - v n t z)) ∧
        ∀ j : ℕ, j ≤ 4 → ∀ z,
          HasSum (fun n => iteratedFDeriv ℝ j (fun z => v (n + 1) t z - v n t z) z)
            (iteratedFDeriv ℝ j (fun z => ∑' n, (v (n + 1) t z - v n t z)) z) := by
    intro t ht
    obtain ⟨K, hK, hK1, -⟩ := key t ht.2
    exact tsum_jets (g := fun n z => v (n + 1) t z - v n t z)
      (fun n => (hC4 (n + 1) t).sub (hC4 n t)) (hsumq.mul_left K)
      (fun n z j hj => hK1 n t ht le_rfl z j hj)
  have hfun : ∀ t ∈ Ico (-T) 0,
      limFn T v t = fun z => v 0 t z + ∑' n, (v (n + 1) t z - v n t z) := fun t ht => by
    funext z
    exact limFn_of_mem v ht z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Ico (-T) 0
    · rw [hfun t ht]
      exact (hC4 0 t).add (hser t ht).1
    · have e : limFn T v t = fun _ => 0 := by
        funext z
        unfold limFn
        rw [if_neg ht]
      rw [e]
      exact contDiff_const
  · intro t z hz
    have h0 : ∀ n, v n t z = 0 := fun n => hsupp n t z hz
    simp [limFn, h0]
  · intro t z hz
    have h0 : ∀ n, vt n t z = 0 := fun n => hsuppt n t z hz
    simp [limFn, h0]
  · intro t ht z
    have ht2 : t / 2 < 0 := by linarith [ht.2]
    obtain ⟨K, hK, hK1, hK2⟩ := key (t / 2) ht2
    have htJ : t ∈ Ioo (-T) (t / 2) := ⟨ht.1, by linarith [ht.2]⟩
    have hmem : ∀ r ∈ Ioo (-T) (t / 2), r ∈ Ioo (-T) 0 := fun r hr =>
      ⟨hr.1, by linarith [hr.2]⟩
    have hsum0 : Summable fun n => v (n + 1) t z - v n t z := by
      refine Summable.of_norm_bounded (hsumq.mul_left K) fun n => ?_
      have h := hK1 n t ⟨ht.1.le, ht.2⟩ (by linarith [ht.2]) z 0 (by norm_num)
      rwa [norm_iteratedFDeriv_zero] at h
    have hs1 : HasDerivAt (fun r => ∑' n, (v (n + 1) r z - v n r z))
        (∑' n, (vt (n + 1) t z - vt n t z)) t :=
      hasDerivAt_tsum_of_isPreconnected (u := fun n => K * (A * (3 / 4) ^ n))
        (g := fun n r => v (n + 1) r z - v n r z)
        (g' := fun n r => vt (n + 1) r z - vt n r z)
        (hsumq.mul_left K) isOpen_Ioo isPreconnected_Ioo
        (fun n r hr => (hder (n + 1) r (hmem r hr) z).sub (hder n r (hmem r hr) z))
        (fun n r hr => hK2 n r ⟨hr.1.le, (hmem r hr).2⟩ hr.2.le z) htJ hsum0 htJ
    have hs2 : HasDerivAt (fun r => v 0 r z + ∑' n, (v (n + 1) r z - v n r z))
        (vt 0 t z + ∑' n, (vt (n + 1) t z - vt n t z)) t := (hder 0 t ht z).add hs1
    rw [limFn_of_mem vt ⟨ht.1.le, ht.2⟩ z]
    refine hs2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact limFn_of_mem v ⟨hr.1.le, hr.2⟩ z
  · intro t ht z j hj
    obtain ⟨hcd, hhs⟩ := hser t ht
    have hj4 : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
    have hpart : ∀ n, iteratedFDeriv ℝ j (v n t) z = iteratedFDeriv ℝ j (v 0 t) z
        + ∑ m ∈ Finset.range n, iteratedFDeriv ℝ j (fun z => v (m + 1) t z - v m t z) z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : v (n + 1) t = fun y => v n t y + (v (n + 1) t y - v n t y) := by
          funext y
          ring
        have h1 : iteratedFDeriv ℝ j (fun y => v n t y + (v (n + 1) t y - v n t y)) z
            = iteratedFDeriv ℝ j (v n t) z
              + iteratedFDeriv ℝ j (fun y => v (n + 1) t y - v n t y) z :=
          iteratedFDeriv_add_apply (f := v n t) (g := fun y => v (n + 1) t y - v n t y)
            ((hC4 n t).of_le hj4).contDiffAt
            (((hC4 (n + 1) t).sub (hC4 n t)).of_le hj4).contDiffAt
        rw [e, h1, ih, Finset.sum_range_succ, add_assoc]
    have hlim : iteratedFDeriv ℝ j (limFn T v t) z = iteratedFDeriv ℝ j (v 0 t) z
        + iteratedFDeriv ℝ j (fun z => ∑' n, (v (n + 1) t z - v n t z)) z := by
      rw [hfun t ht]
      exact iteratedFDeriv_add_apply (f := v 0 t)
        (g := fun z => ∑' n, (v (n + 1) t z - v n t z))
        ((hC4 0 t).of_le hj4).contDiffAt (hcd.of_le hj4).contDiffAt
    rw [hlim]
    have h2 := ((hhs j hj z).tendsto_sum_nat).const_add (iteratedFDeriv ℝ j (v 0 t) z)
    refine h2.congr fun n => ?_
    rw [hpart n]
  · intro t ht z
    obtain ⟨K, hK, -, hK2⟩ := key t ht.2
    have hsum : Summable fun n => vt (n + 1) t z - vt n t z :=
      Summable.of_norm_bounded (hsumq.mul_left K) fun n => hK2 n t ht le_rfl z
    rw [limFn_of_mem vt ht z]
    have h2 := (hsum.hasSum.tendsto_sum_nat).const_add (vt 0 t z)
    refine h2.congr fun n => ?_
    rw [Finset.sum_range_sub (fun m => vt m t z) n]
    ring

/-- A pointwise bound of the chart operator by the jets of order at most
four. -/
theorem chartOp_point_bound (m : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V → ℝ) (z : V) (B : ℝ),
    ContDiff ℝ 4 v → ‖z‖ ≤ 1 → 0 ≤ B → (∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j v z‖ ≤ B) →
    |chartOp m v z| ≤ C * B := by
  obtain ⟨C, hC, H⟩ := chartOp_WH (V := V) 1 0 1 m zero_le_one
  refine ⟨C, hC, fun v z B hv hz hB hbd => ?_⟩
  have hsc : IsScale (1 : ℝ) 1 (fun _ : V × ℝ => (1 : ℝ)) ({(z, (0 : ℝ))} : Set (V × ℝ)) :=
    IsScale.const one_pos
  have hWJ : WJ 1 1 (fun _ : V × ℝ => (1 : ℝ)) ({(z, (0 : ℝ))} : Set (V × ℝ)) 0 B 4
      (fun _ => v) := by
    intro j hj
    refine ⟨fun p hp => ?_, fun p hp q hq _ => ?_⟩
    · rw [Set.mem_singleton_iff] at hp
      rw [hp, Real.one_rpow, mul_one]
      exact hbd j hj
    · rw [Set.mem_singleton_iff] at hp hq
      rw [hp, hq, sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg zero_le_one _))
        (Real.rpow_nonneg (pdist_nonneg _ _) _)
  have h := (H 1 1 B (fun _ => 1) {(z, (0 : ℝ))} (fun _ => v) hsc hB le_rfl zero_le_one le_rfl
    (fun _ _ => le_rfl) (fun p hp => by
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact hz) (fun _ => hv) hWJ).1 (z, 0) rfl
  rw [Real.one_rpow, mul_one, Real.norm_eq_abs] at h
  exact h

/-- The chart operator is continuous for the pointwise convergence of the jets
of order at most four. -/
theorem tendsto_chartOp (m : ℝ) {f : ℕ → V → ℝ} {g : V → ℝ} (hf : ∀ n, ContDiff ℝ 4 (f n))
    (hg : ContDiff ℝ 4 g) {z : V} (hz : ‖z‖ ≤ 1)
    (h : ∀ j : ℕ, j ≤ 4 → Tendsto (fun n => iteratedFDeriv ℝ j (f n) z) atTop
      (𝓝 (iteratedFDeriv ℝ j g z))) :
    Tendsto (fun n => chartOp m (f n) z) atTop (𝓝 (chartOp m g z)) := by
  obtain ⟨C, hC, H⟩ := chartOp_point_bound (V := V) m
  -- the sum of the distances of the jets
  have hB : Tendsto (fun n => ∑ j ∈ Finset.range 5,
      ‖iteratedFDeriv ℝ j (f n) z - iteratedFDeriv ℝ j g z‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑ j ∈ Finset.range 5,
        ‖iteratedFDeriv ℝ j (f n) z - iteratedFDeriv ℝ j g z‖) atTop
        (𝓝 (∑ j ∈ Finset.range 5, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hj4 : j ≤ 4 := by
        have := Finset.mem_range.1 hj
        omega
      have h2 := ((h j hj4).sub_const (iteratedFDeriv ℝ j g z)).norm
      rwa [sub_self, norm_zero] at h2
    simpa using h1
  have hdiff : ∀ n, |chartOp m (f n) z - chartOp m g z|
      ≤ C * ∑ j ∈ Finset.range 5, ‖iteratedFDeriv ℝ j (f n) z - iteratedFDeriv ℝ j g z‖ := by
    intro n
    have hd4 : ContDiff ℝ 4 (fun y => f n y - g y) := (hf n).sub hg
    have e : f n = fun y => (f n y - g y) + g y := by
      funext y
      ring
    have h1 : chartOp m (f n) z = chartOp m (fun y => f n y - g y) z + chartOp m g z := by
      conv_lhs => rw [e]
      exact chartOp_add m hd4 hg z
    have h2 : chartOp m (f n) z - chartOp m g z = chartOp m (fun y => f n y - g y) z := by
      linarith
    rw [h2]
    refine H _ z _ hd4 hz (Finset.sum_nonneg fun j _ => norm_nonneg _) fun j hj => ?_
    have hj4 : (j : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hj
    have h3 : iteratedFDeriv ℝ j (fun y => f n y - g y) z
        = iteratedFDeriv ℝ j (f n) z - iteratedFDeriv ℝ j g z :=
      iteratedFDeriv_sub_apply (f := f n) (g := g) ((hf n).of_le hj4).contDiffAt
        (hg.of_le hj4).contDiffAt
    rw [h3]
    exact Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedFDeriv ℝ j (f n) z - iteratedFDeriv ℝ j g z‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hCB := hB.const_mul C
  rw [mul_zero] at hCB
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hCB
  rw [Real.dist_eq]
  exact hdiff n

/-- The values converge when the jets of order zero converge. -/
theorem tendsto_value_of_jets {f : ℕ → V → ℝ} {g : V → ℝ} {z : V}
    (h : Tendsto (fun n => iteratedFDeriv ℝ 0 (f n) z) atTop (𝓝 (iteratedFDeriv ℝ 0 g z))) :
    Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
  have hc : Continuous fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => V) ℝ => L 0 :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => V) ℝ 0).continuous
  have h2 := (hc.tendsto _).comp h
  simpa [Function.comp_def, iteratedFDeriv_zero_apply] using h2

end Series

/-! ### The limit pair -/

/-- The limit of a sequence of pairs. -/
noncomputable def pairLim (T : ℝ) (u : ℕ → Pair) : Pair :=
  (limFn T (fun n => (u n).1), limFn T (fun n => (u n).2.1), limFn T (fun n => (u n).2.2.1),
    limFn T (fun n => (u n).2.2.2))

theorem norm_ray18_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖Real.sqrt x • e18‖ ≤ 1 := by
  rw [norm_smul, norm_e18, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  have h := Real.sqrt_le_sqrt hx.2
  rwa [Real.sqrt_one] at h

theorem norm_ray6_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖Real.sqrt (1 - x) • e6‖ ≤ 1 := by
  rw [norm_smul, norm_e6, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := Real.sqrt_le_sqrt (by linarith [hx.1] : 1 - x ≤ 1)
  rwa [Real.sqrt_one] at h

set_option maxHeartbeats 1600000 in
/-- **The limit pair** of a sequence with geometrically decaying increments. -/
theorem pairLim_spec {α T w A : ℝ} (hT1 : T ≤ 1) (hA : 0 ≤ A) (u : ℕ → Pair)
    (hReg : ∀ n, Reg (u n)) (hSol : ∀ n, Sol T (u n))
    (hdJ : ∀ n, XJ α T w (A * (3 / 4) ^ n) (u (n + 1) - u n))
    (hdT : ∀ n, XT α T w (A * (3 / 4) ^ n) (u (n + 1) - u n)) :
    Reg (pairLim T u) ∧ Sol T (pairLim T u) ∧
      (∀ e : ℝ, (∀ n, XJ α T w e (u n)) → XJ α T w e (pairLim T u)) ∧
      (∀ M₀ : ℝ, XT α T w M₀ (u 0) → XT α T w (M₀ + 4 * A) (pairLim T u)) ∧
      ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
        Tendsto (fun n => valOf (u n) t x) atTop (𝓝 (valOf (pairLim T u) t x)) ∧
        Tendsto (fun n => dtOf (u n) t x) atTop (𝓝 (dtOf (pairLim T u) t x)) ∧
        Tendsto (fun n => AOf (u n) t x) atTop (𝓝 (AOf (pairLim T u) t x)) := by
  have hs0 : ∀ t₂ : ℝ, t₂ < 0 → ∃ lo : ℝ, 0 < lo ∧ ∀ p : Flat18 × ℝ, p.2 ∈ Ico (-T) 0 →
      ‖p.1‖ ^ 2 ≤ 3 / 4 → p.2 ≤ t₂ → lo ≤ sigma p ∧ sigma p ≤ 2 := by
    intro t₂ ht₂
    refine ⟨Real.sqrt (Real.sqrt (-t₂)), Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith)),
      fun p hp hz hpt => ⟨?_, sigma_le_two0 hT1 p ⟨hp, hz⟩⟩⟩
    unfold sigma
    apply Real.sqrt_le_sqrt
    have h := Real.sqrt_le_sqrt (by linarith : -t₂ ≤ -p.2)
    nlinarith [sq_nonneg ‖p.1‖]
  have hs1 : ∀ t₂ : ℝ, t₂ < 0 → ∃ lo : ℝ, 0 < lo ∧ ∀ p : Flat6 × ℝ, p.2 ∈ Ico (-T) 0 →
      ‖p.1‖ ^ 2 ≤ 7 / 8 → p.2 ≤ t₂ →
      lo ≤ (fun _ : Flat6 × ℝ => (1 : ℝ)) p ∧ (fun _ : Flat6 × ℝ => (1 : ℝ)) p ≤ 1 :=
    fun _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := chart_limit (T := T) (R := 3 / 4) (R' := 1 / 2) (α := α)
    (a := 1 / 64) (w := w) (A := A) (hi := 2) (s := sigma (V := Flat18)) (by norm_num) hA
    (fun n => (u n).1) (fun n => (u n).2.1) (fun n => (hReg n).smooth0)
    (fun n => (hReg n).supp0) (fun n => (hReg n).supp0t) (fun n => (hSol n).deriv0)
    (fun n => (hdJ n).1) (fun n => (hdT n).1) hs0
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := chart_limit (T := T) (R := 7 / 8) (R' := 3 / 4) (α := α)
    (a := 1 / 64) (w := w) (A := A) (hi := 1) (s := fun _ : Flat6 × ℝ => (1 : ℝ)) (by norm_num)
    hA (fun n => (u n).2.2.1) (fun n => (u n).2.2.2) (fun n => (hReg n).smooth1)
    (fun n => (hReg n).supp1) (fun n => (hReg n).supp1t) (fun n => (hSol n).deriv1)
    (fun n => (hdJ n).2) (fun n => (hdT n).2) hs1
  have hR : Reg (pairLim T u) := ⟨a1, b1, a2, a3, b2, b3⟩
  refine ⟨hR, ⟨a4, b4, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t Q z
    show limFn T (fun n => (u n).1) t (Q z) = limFn T (fun n => (u n).1) t z
    have h0 : ∀ n, (u n).1 t (Q z) = (u n).1 t z := fun n => (hSol n).radial0 t Q z
    unfold limFn
    simp only [h0]
  · intro t Q z
    show limFn T (fun n => (u n).2.2.1) t (Q z) = limFn T (fun n => (u n).2.2.1) t z
    have h0 : ∀ n, (u n).2.2.1 t (Q z) = (u n).2.2.1 t z := fun n => (hSol n).radial1 t Q z
    unfold limFn
    simp only [h0]
  · intro e hall
    exact ⟨fun j hj => WH.of_tendsto (fun n => (hall n).1 j hj)
        (fun p hp => a5 p.2 hp.1 p.1 j hj),
      fun j hj => WH.of_tendsto (fun n => (hall n).2 j hj) (fun p hp => b5 p.2 hp.1 p.1 j hj)⟩
  · intro M₀ h0
    have hXTn : ∀ n, XT α T w (M₀ + 4 * A * (1 - (3 / 4) ^ n)) (u n) := by
      intro n
      induction n with
      | zero =>
        have e0 : M₀ + 4 * A * (1 - (3 / 4) ^ 0) = M₀ := by norm_num
        rw [e0]
        exact h0
      | succ n ih =>
        have h1 := ih.add (hdT n)
        have e : u n + (u (n + 1) - u n) = u (n + 1) := by abel
        rw [e] at h1
        refine h1.mono (le_of_eq ?_)
        ring
    have hXT' : ∀ n, XT α T w (M₀ + 4 * A) (u n) := fun n => (hXTn n).mono (by
      have h1 : (0 : ℝ) ≤ (3 / 4) ^ n := by positivity
      nlinarith)
    exact ⟨WH.of_tendsto (fun n => (hXT' n).1) (fun p hp => a6 p.2 hp.1 p.1),
      WH.of_tendsto (fun n => (hXT' n).2) (fun p hp => b6 p.2 hp.1 p.1)⟩
  · intro t ht x hx
    have hz0 := norm_ray18_le hx
    have hz1 := norm_ray6_le hx
    refine ⟨?_, ?_, ?_⟩
    · exact (tendsto_value_of_jets (a5 t ht _ 0 (by norm_num))).add
        (tendsto_value_of_jets (b5 t ht _ 0 (by norm_num)))
    · exact (a6 t ht _).add (b6 t ht _)
    · exact ((tendsto_chartOp 6 (fun n => (hReg n).smooth0 t) (a1 t) hz0
          (fun j hj => a5 t ht _ j hj)).div_const 16).add
        ((tendsto_chartOp 18 (fun n => (hReg n).smooth1 t) (b1 t) hz1
          (fun j hj => b5 t ht _ j hj)).div_const 16)

end Calabi.Weighted
