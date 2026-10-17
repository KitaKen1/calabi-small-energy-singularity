import Calabi.Correction.Ladder
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Smoothness in space and time of the solution in a chart

`chart_space_smooth` gives the spatial regularity of a solution `h` of the
chart equation `h_t + (1 + v h)² (chartOp m h) / 16 = 0`. The equation
expresses `h_t` through `h` and its spatial derivatives, so the time
derivatives of all orders exist:

* `JS α Ω n g`: `g` is in the local classes `Sm` of all orders, has a time
  derivative, which has the same property with `n - 1` in place of `n`;
* the classes `JS` are closed under sums, products, derivatives in a direction
  (`timeDeriv_fderiv_apply`), the Laplacian, the Euler operator and the chart
  operator;
* `chart_time_smooth`: a solution of the chart equation is in `JS n` for all
  `n`;
* `JS.contDiffOn`: a function of the class `JS n` is `C^n` in space and time
  (continuous partial derivatives give differentiability,
  `hasStrictFDerivAt_uncurry_coprod`);
* `chart_smooth`: the solution is smooth in space and time.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Smooth in space, with `n` time derivatives of the same kind. -/
def JS (α : ℝ) (Ω : Set (V × ℝ)) : ℕ → (ℝ → V → ℝ) → Prop
  | 0, g => ∀ k, Sm α Ω k g
  | n + 1, g => (∀ k, Sm α Ω k g) ∧ ∃ g' : ℝ → V → ℝ,
      (∀ p ∈ Ω, HasDerivAt (fun t => g t p.1) (g' p.2 p.1) p.2) ∧ JS α Ω n g'

section JSClosure

variable {α : ℝ} {Ω : Set (V × ℝ)}

theorem JS.sm {n : ℕ} {g : ℝ → V → ℝ} (h : JS α Ω n g) (k : ℕ) : Sm α Ω k g := by
  cases n with
  | zero => exact h k
  | succ n => exact h.1 k

theorem JS.mono {n : ℕ} {g : ℝ → V → ℝ} (h : JS α Ω (n + 1) g) : JS α Ω n g := by
  induction n generalizing g with
  | zero => exact h.1
  | succ n ih =>
    obtain ⟨hs, g', hd, hg'⟩ := h
    exact ⟨hs, g', hd, ih hg'⟩

theorem JS.congr {n : ℕ} {g g₂ : ℝ → V → ℝ} (hΩ : IsOpen Ω) (h : JS α Ω n g)
    (hgg : ∀ p ∈ Ω, g₂ p.2 p.1 = g p.2 p.1) : JS α Ω n g₂ := by
  cases n with
  | zero => exact fun k => (h k).congr hΩ hgg
  | succ n =>
    obtain ⟨hs, g', hd, hg'⟩ := h
    exact ⟨fun k => (hs k).congr hΩ hgg, g', fun p hp =>
      (hd p hp).congr_of_eventuallyEq (time_eventuallyEq hΩ hgg hp), hg'⟩

theorem JS.add {n : ℕ} {g₁ g₂ : ℝ → V → ℝ} (h₁ : JS α Ω n g₁) (h₂ : JS α Ω n g₂) :
    JS α Ω n (fun t x => g₁ t x + g₂ t x) := by
  induction n generalizing g₁ g₂ with
  | zero => exact fun k => (h₁ k).add (h₂ k)
  | succ n ih =>
    obtain ⟨hs₁, g₁', hd₁, hg₁'⟩ := h₁
    obtain ⟨hs₂, g₂', hd₂, hg₂'⟩ := h₂
    exact ⟨fun k => (hs₁ k).add (hs₂ k), fun t x => g₁' t x + g₂' t x,
      fun p hp => (hd₁ p hp).add (hd₂ p hp), ih hg₁' hg₂'⟩

theorem JS.mul {n : ℕ} {g₁ g₂ : ℝ → V → ℝ} (h₁ : JS α Ω n g₁) (h₂ : JS α Ω n g₂) :
    JS α Ω n (fun t x => g₁ t x * g₂ t x) := by
  induction n generalizing g₁ g₂ with
  | zero => exact fun k => (h₁ k).mul (h₂ k)
  | succ n ih =>
    have m₁ := h₁.mono
    have m₂ := h₂.mono
    obtain ⟨hs₁, g₁', hd₁, hg₁'⟩ := h₁
    obtain ⟨hs₂, g₂', hd₂, hg₂'⟩ := h₂
    exact ⟨fun k => (hs₁ k).mul (hs₂ k),
      fun t x => g₁' t x * g₂ t x + g₁ t x * g₂' t x,
      fun p hp => (hd₁ p hp).mul (hd₂ p hp), (ih hg₁' m₂).add (ih m₁ hg₂')⟩

theorem JS.of_contDiff (hα : 0 ≤ α) (hα1 : α ≤ 1) (Ω : Set (V × ℝ)) (n : ℕ) :
    ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → JS α Ω n (fun _ => φ) := by
  induction n with
  | zero => exact fun φ hφ k => Sm.of_contDiff hα hα1 hφ Ω k
  | succ n ih =>
    intro φ hφ
    exact ⟨fun k => Sm.of_contDiff hα hα1 hφ Ω k, fun _ _ => 0,
      fun p _ => hasDerivAt_const p.2 (φ p.1), ih (fun _ => 0) contDiff_const⟩

theorem JS.const_mul (hα : 0 ≤ α) (hα1 : α ≤ 1) {n : ℕ} {g : ℝ → V → ℝ} (c : ℝ)
    (h : JS α Ω n g) : JS α Ω n (fun t x => c * g t x) :=
  (JS.of_contDiff hα hα1 Ω n (fun _ => c) contDiff_const).mul h

theorem JS.sum (hα : 0 ≤ α) (hα1 : α ≤ 1) {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → V → ℝ} (h : ∀ i ∈ s, JS α Ω n (f i)) :
    JS α Ω n (fun t x => ∑ i ∈ s, f i t x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun (t : ℝ) (x : V) => ∑ i ∈ (∅ : Finset ι), f i t x) = fun _ _ => 0 := by
      funext t x
      simp
    rw [e]
    exact JS.of_contDiff hα hα1 Ω n (fun _ => 0) contDiff_const
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun (t : ℝ) (x : V) => ∑ i ∈ insert a s, f i t x)
        = fun t x => f a t x + ∑ i ∈ s, f i t x := by
      funext t x
      rw [Finset.sum_insert ha]
    rw [e]
    exact h1

theorem JS.fderiv_apply (hα : 0 < α) (hΩ : IsOpen Ω) {n : ℕ} {g : ℝ → V → ℝ}
    (h : JS α Ω n g) (e : V) : JS α Ω n (fun t z => fderiv ℝ (g t) z e) := by
  induction n generalizing g with
  | zero => exact fun k => (h (k + 1)).fderiv_apply e
  | succ n ih =>
    obtain ⟨hs, g', hd, hg'⟩ := h
    exact ⟨fun k => (hs (k + 1)).fderiv_apply e, fun t z => fderiv ℝ (g' t) z e,
      timeDeriv_fderiv_apply hα hΩ (hs 1) (hg'.sm 1) hd e, ih hg'⟩

theorem JS.euler (hα : 0 < α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) {n : ℕ} {g : ℝ → V → ℝ}
    (h : JS α Ω n g) : JS α Ω n (fun t => eulerE (g t)) := by
  have e : (fun t => eulerE (g t)) = fun t z => ∑ i, inner ℝ (stdOrthonormalBasis ℝ V i) z
      * fderiv ℝ (g t) z (stdOrthonormalBasis ℝ V i) := by
    funext t z
    exact eulerE_eq_sum (stdOrthonormalBasis ℝ V) (g t) z
  rw [e]
  exact JS.sum hα.le hα1 Finset.univ fun i _ =>
    (JS.of_contDiff hα.le hα1 Ω n _ (contDiff_const.inner ℝ contDiff_id)).mul
      (h.fderiv_apply hα hΩ _)

theorem JS.laplacian (hα : 0 < α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) {n : ℕ} {g : ℝ → V → ℝ}
    (h : JS α Ω n g) : JS α Ω n (fun t => Δ (g t)) := by
  have hsum : JS α Ω n (fun t z => ∑ i,
      fderiv ℝ (fun y => fderiv ℝ (g t) y (stdOrthonormalBasis ℝ V i)) z
        (stdOrthonormalBasis ℝ V i)) :=
    JS.sum hα.le hα1 Finset.univ fun i _ =>
      (h.fderiv_apply hα hΩ (stdOrthonormalBasis ℝ V i)).fderiv_apply hα hΩ
        (stdOrthonormalBasis ℝ V i)
  refine hsum.congr hΩ fun p hp => ?_
  have hc : ContDiffAt ℝ 2 (g p.2) p.1 := by exact_mod_cast (h.sm 2).contDiffAt hp
  exact laplacian_eq_sum_of_contDiffAt hc

theorem JS.lowOp (hα : 0 < α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) (m : ℝ) {n : ℕ} {g : ℝ → V → ℝ}
    (h : JS α Ω n g) : JS α Ω n (fun t => lowOp m (g t)) := by
  have hL := h.laplacian hα hα1 hΩ
  have hEL := hL.euler hα hα1 hΩ
  have hE := h.euler hα hα1 hΩ
  have hEE := hE.euler hα hα1 hΩ
  have hn : ContDiff ℝ ∞ fun z : V => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
  have c1 : JS α Ω n (fun (_ : ℝ) (z : V) => -((4 + 2 * m) * (1 - ‖z‖ ^ 2))) :=
    JS.of_contDiff hα.le hα1 Ω n _ ((contDiff_const.mul (contDiff_const.sub hn)).neg)
  have c2 : JS α Ω n (fun (_ : ℝ) (z : V) => (160 + 2 * m) * ‖z‖ ^ 2 - 160) :=
    JS.of_contDiff hα.le hα1 Ω n _ ((contDiff_const.mul hn).sub contDiff_const)
  have h5 := ((((c1.mul hEL).add (c2.mul hL)).add (hEE.const_mul hα.le hα1 (m ^ 2))).add
    (hE.const_mul hα.le hα1 (112 * m))).add (h.const_mul hα.le hα1 2880)
  exact h5

theorem JS.chartOp (hα : 0 < α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) (m : ℝ) {n : ℕ}
    {g : ℝ → V → ℝ} (h : JS α Ω n g) : JS α Ω n (fun t => chartOp m (g t)) := by
  have hn : ContDiff ℝ ∞ fun z : V => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
  have c : JS α Ω n (fun (_ : ℝ) (z : V) => (1 - ‖z‖ ^ 2) ^ 2) :=
    JS.of_contDiff hα.le hα1 Ω n _ ((contDiff_const.sub hn).pow 2)
  have h1 := (c.mul ((h.laplacian hα hα1 hΩ).laplacian hα hα1 hΩ)).add (h.lowOp hα hα1 hΩ m)
  have e : (fun t => Calabi.Chart.chartOp m (g t))
      = fun t z => (1 - ‖z‖ ^ 2) ^ 2 * Δ (Δ (g t)) z + Calabi.Weighted.lowOp m (g t) z := by
    funext t z
    exact chartOp_eq_lowOp m (g t) z
  rw [e]
  exact h1

end JSClosure

/-- **A solution of the chart equation has time derivatives of all orders.** -/
theorem chart_time_smooth {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Ω : Set (V × ℝ)}
    (hΩ : IsOpen Ω) (hball : ∀ p ∈ Ω, ‖p.1‖ < 1) (m : ℝ) {v : V → ℝ} (hv : ContDiff ℝ ∞ v)
    {h ht : ℝ → V → ℝ} (hh : Sm α Ω 4 h) (hht : Sm α Ω 0 ht)
    (hd : ∀ p ∈ Ω, HasDerivAt (fun t => h t p.1) (ht p.2 p.1) p.2)
    (hpos : ∀ p ∈ Ω, 0 < 1 + v p.1 * h p.2 p.1)
    (heq : ∀ p ∈ Ω, ht p.2 p.1 + (1 + v p.1 * h p.2 p.1) ^ 2 * (chartOp m (h p.2) p.1 / 16) = 0)
    (n : ℕ) : JS α Ω n h := by
  have hsp := chart_space_smooth hα hα1 hΩ hball m hv hh hht hd hpos heq
  have hsm : ∀ k, Sm α Ω k h := fun k => (hsp k).1.of_le (by omega)
  induction n with
  | zero => exact hsm
  | succ n ih =>
    refine ⟨hsm, ht, hd, ?_⟩
    have hb : JS α Ω n (fun t z => 1 + v z * h t z) :=
      (JS.of_contDiff hα.le hα1.le Ω n (fun _ => 1) contDiff_const).add
        ((JS.of_contDiff hα.le hα1.le Ω n v hv).mul ih)
    have hΦ : JS α Ω n (fun t z => -1 / 16 * ((1 + v z * h t z) * (1 + v z * h t z)
        * chartOp m (h t) z)) :=
      ((hb.mul hb).mul (ih.chartOp hα hα1.le hΩ m)).const_mul hα.le hα1.le (-1 / 16)
    refine hΦ.congr hΩ fun p hp => ?_
    have h1 := heq p hp
    show ht p.2 p.1 = -1 / 16 * ((1 + v p.1 * h p.2 p.1) * (1 + v p.1 * h p.2 p.1)
      * chartOp m (h p.2) p.1)
    linear_combination h1

/-! ### From the classes to smoothness in space and time -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem continuous_pdist_left (p₀ : V × ℝ) : Continuous fun p : V × ℝ => pdist p p₀ := by
  unfold pdist
  exact (continuous_fst.sub continuous_const).norm.add
    ((continuous_snd.sub continuous_const).abs.rpow_const fun _ => Or.inr (by norm_num))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A function with a two-point bound near a point is continuous there. -/
theorem continuousAt_of_WH {E : Type*} [NormedAddCommGroup E] {α M w : ℝ} (hα : 0 < α)
    {N : Set (V × ℝ)} {f : V × ℝ → E} (hN : IsOpen N) {p₀ : V × ℝ} (hp₀ : p₀ ∈ N)
    (h : WH α 1 (fun _ : V × ℝ => (1 : ℝ)) N w M f) : ContinuousAt f p₀ := by
  have hpd : Tendsto (fun p : V × ℝ => pdist p p₀) (𝓝 p₀) (𝓝 0) := by
    have h1 := (continuous_pdist_left p₀).tendsto p₀
    have e : pdist p₀ p₀ = 0 := by
      unfold pdist
      simp
    rwa [e] at h1
  have hpow : Tendsto (fun p : V × ℝ => M * (1 : ℝ) ^ (w - α) * pdist p p₀ ^ α) (𝓝 p₀)
      (𝓝 0) := by
    have h2 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hpd
    rw [Real.zero_rpow hα.ne'] at h2
    have h3 := h2.const_mul (M * (1 : ℝ) ^ (w - α))
    rwa [mul_zero] at h3
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hpow
  filter_upwards [hN.mem_nhds hp₀, hpd.eventually (ge_mem_nhds zero_lt_one)] with p hp hp1
  rw [dist_eq_norm]
  exact h.2 p hp p₀ hp₀ (by rw [one_mul]; exact hp1)

/-- A function of the class of order zero is continuous in space and time. -/
theorem Sm.continuousAt {α : ℝ} (hα : 0 < α) {Ω : Set (V × ℝ)} {g : ℝ → V → ℝ}
    (h : Sm α Ω 0 g) {p₀ : V × ℝ} (hp₀ : p₀ ∈ Ω) :
    ContinuousAt (fun p : V × ℝ => g p.2 p.1) p₀ := by
  obtain ⟨N, g', M, hN, hp, hM, hgg, hs, hW⟩ := h p₀ hp₀
  have h1 := continuousAt_of_WH hα hN hp hW.value
  refine h1.congr ?_
  filter_upwards [hN.mem_nhds hp] with p hp'
  exact hgg p hp'

/-- The first derivative of a function of the class of order one is continuous
in space and time. -/
theorem Sm.continuousAt_fderiv {α : ℝ} (hα : 0 < α) {Ω : Set (V × ℝ)} {g : ℝ → V → ℝ}
    (h : Sm α Ω 1 g) {p₀ : V × ℝ} (hp₀ : p₀ ∈ Ω) :
    ContinuousAt (fun p : V × ℝ => fderiv ℝ (g p.2) p.1) p₀ := by
  obtain ⟨N, g', M, hN, hp, hM, hgg, hs, hW⟩ := h p₀ hp₀
  have h1 := (hW 1 le_rfl).clm
    ((continuousMultilinearCurryFin1 ℝ V ℝ).toContinuousLinearEquiv.toContinuousLinearMap)
  have h2 := continuousAt_of_WH hα hN hp h1
  refine h2.congr ?_
  filter_upwards [hN.mem_nhds hp] with p hp'
  show ((continuousMultilinearCurryFin1 ℝ V ℝ).toContinuousLinearEquiv.toContinuousLinearMap)
    (iteratedFDeriv ℝ 1 (g' p.2) p.1) = fderiv ℝ (g p.2) p.1
  rw [← (slice_eventuallyEq hN hgg hp').fderiv_eq]
  exact (fderiv_eq_curryFin1 (g' p.2) p.1).symm

set_option maxHeartbeats 1600000 in
/-- **A function of the class `JS n` is `C^n` in space and time.** -/
theorem JS.contDiffOn {α : ℝ} (hα : 0 < α) {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω) (n : ℕ) :
    ∀ g : ℝ → V → ℝ, JS α Ω n g → ContDiffOn ℝ n (fun p : V × ℝ => g p.2 p.1) Ω := by
  induction n with
  | zero =>
    intro g h
    have hc : ContinuousOn (fun p : V × ℝ => g p.2 p.1) Ω := fun p hp =>
      ((h 0).continuousAt hα hp).continuousWithinAt
    exact_mod_cast contDiffOn_zero.2 hc
  | succ n ih =>
    intro g h
    have hmono := h.mono
    obtain ⟨hs, g', hd, hg'⟩ := h
    -- the derivative in space and time
    have hF : ∀ p ∈ Ω, HasFDerivAt (fun p : V × ℝ => g p.2 p.1)
        ((fderiv ℝ (g p.2) p.1).coprod
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g' p.2 p.1))) p := by
      intro p hp
      have h1 := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := fun z t => g t z)
        (f₁ := fun z t => fderiv ℝ (g t) z)
        (f₂ := fun z t => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g' t z))
        (by
          filter_upwards [hΩ.mem_nhds hp] with q hq
          exact (((hs 1).contDiffAt hq).differentiableAt (by norm_num)).hasFDerivAt)
        (by
          filter_upwards [hΩ.mem_nhds hp] with q hq
          exact (hd q hq).hasFDerivAt)
        ((hs 1).continuousAt_fderiv hα hp)
        (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt).comp
          ((hg'.sm 0).continuousAt hα hp))
      exact h1.hasFDerivAt
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun p hp => (hF p hp).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [contDiffOn_clm_apply]
      intro y
      have h1 : ContDiffOn ℝ n
          (fun p : V × ℝ => fderiv ℝ (g p.2) p.1 y.1 + y.2 * g' p.2 p.1) Ω :=
        (ih _ (hmono.fderiv_apply hα hΩ y.1)).add (contDiffOn_const.mul (ih _ hg'))
      refine h1.congr fun p hp => ?_
      rw [(hF p hp).fderiv]
      simp [ContinuousLinearMap.coprod_apply]

/-- **A solution of the chart equation is smooth in space and time.** -/
theorem chart_smooth {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω)
    (hball : ∀ p ∈ Ω, ‖p.1‖ < 1) (m : ℝ) {v : V → ℝ} (hv : ContDiff ℝ ∞ v)
    {h ht : ℝ → V → ℝ} (hh : Sm α Ω 4 h) (hht : Sm α Ω 0 ht)
    (hd : ∀ p ∈ Ω, HasDerivAt (fun t => h t p.1) (ht p.2 p.1) p.2)
    (hpos : ∀ p ∈ Ω, 0 < 1 + v p.1 * h p.2 p.1)
    (heq : ∀ p ∈ Ω, ht p.2 p.1 + (1 + v p.1 * h p.2 p.1) ^ 2 * (chartOp m (h p.2) p.1 / 16) = 0) :
    ContDiffOn ℝ ∞ (fun p : V × ℝ => h p.2 p.1) Ω :=
  contDiffOn_infty.2 fun n =>
    JS.contDiffOn hα hΩ n h (chart_time_smooth hα hα1 hΩ hball m hv hh hht hd hpos heq n)

end Calabi.Weighted
