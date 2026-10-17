import Calabi.Correction.SmoothClass
import Calabi.Correction.ChartCutoff

/-!
# Differential operators on the local classes

Closure of the classes `Sm` of `SmoothClass.lean` under the operators that
occur in the chart form of the Calabi flow:

* `Sm.sum`: finite sums;
* `Sm.euler`: the Euler operator `z · ∇`, one order;
* `Sm.laplacian`, `Sm.bilaplacian`: the Laplacian, two orders, and its square;
* `Sm.lowOp`: the terms of order at most three of the chart operator;
* `Sm.of_partials`: a function of the class of order one whose derivatives in
  the directions of a basis are in the class of order `k` is in the class of
  order `k + 1`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Ops

variable {α : ℝ} {Ω : Set (V × ℝ)} {k : ℕ} {g : ℝ → V → ℝ}

theorem Sm.sum (hα : 0 ≤ α) (hα1 : α ≤ 1) {ι : Type*} (s : Finset ι) {f : ι → ℝ → V → ℝ}
    (h : ∀ i ∈ s, Sm α Ω k (f i)) : Sm α Ω k (fun t x => ∑ i ∈ s, f i t x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun (t : ℝ) (x : V) => ∑ i ∈ (∅ : Finset ι), f i t x) = fun _ _ => 0 := by
      funext t x
      simp
    rw [e]
    exact Sm.of_contDiff hα hα1 (contDiff_const (c := (0 : ℝ))) Ω k
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun (t : ℝ) (x : V) => ∑ i ∈ insert a s, f i t x)
        = fun t x => f a t x + ∑ i ∈ s, f i t x := by
      funext t x
      rw [Finset.sum_insert ha]
    rw [e]
    exact h1

omit [FiniteDimensional ℝ V] in
/-- The Euler operator in an orthonormal basis. -/
theorem eulerE_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (u : V → ℝ) (z : V) :
    eulerE u z = ∑ i, inner ℝ (b i) z * fderiv ℝ u z (b i) := by
  have h := congrArg (fderiv ℝ u z) (b.sum_repr' z)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  exact h.symm

theorem Sm.euler (hα : 0 ≤ α) (hα1 : α ≤ 1) (h : Sm α Ω (k + 1) g) :
    Sm α Ω k (fun t => eulerE (g t)) := by
  have e : (fun t => eulerE (g t)) = fun t z => ∑ i, inner ℝ (stdOrthonormalBasis ℝ V i) z
      * fderiv ℝ (g t) z (stdOrthonormalBasis ℝ V i) := by
    funext t z
    exact eulerE_eq_sum (stdOrthonormalBasis ℝ V) (g t) z
  rw [e]
  exact Sm.sum hα hα1 Finset.univ fun i _ =>
    (Sm.of_contDiff hα hα1 (contDiff_const.inner ℝ contDiff_id) Ω k).mul (h.fderiv_apply _)

/-- The Laplacian as the sum of the second derivatives in the directions of
the standard orthonormal basis. -/
theorem laplacian_eq_sum_of_contDiffAt {f : V → ℝ} {z : V} (hf : ContDiffAt ℝ 2 f z) :
    Δ f z = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) z
      (stdOrthonormalBasis ℝ V i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i))
      ((ContinuousLinearMap.apply ℝ ℝ (stdOrthonormalBasis ℝ V i)).comp
        (fderiv ℝ (fderiv ℝ f) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ (stdOrthonormalBasis ℝ V i)).hasFDerivAt.comp z hd.hasFDerivAt
  rw [h1.fderiv]
  rfl

theorem Sm.laplacian (hα : 0 ≤ α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) (h : Sm α Ω (k + 2) g) :
    Sm α Ω k (fun t => Δ (g t)) := by
  have hsum : Sm α Ω k (fun t z => ∑ i,
      fderiv ℝ (fun y => fderiv ℝ (g t) y (stdOrthonormalBasis ℝ V i)) z
        (stdOrthonormalBasis ℝ V i)) :=
    Sm.sum hα hα1 Finset.univ fun i _ =>
      ((show Sm α Ω (k + 1 + 1) g from h).fderiv_apply (stdOrthonormalBasis ℝ V i)).fderiv_apply
        (stdOrthonormalBasis ℝ V i)
  refine hsum.congr hΩ fun p hp => ?_
  obtain ⟨N, g', M, hN, hpN, hM, hgg, hs, hW⟩ := h p hp
  have hev := slice_eventuallyEq hN hgg hpN
  have hc : ContDiffAt ℝ 2 (g p.2) p.1 :=
    ((hs p.2).of_le (by
      have : (2 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast this)).contDiffAt.congr_of_eventuallyEq hev.symm
  exact laplacian_eq_sum_of_contDiffAt hc

theorem Sm.bilaplacian (hα : 0 ≤ α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) (h : Sm α Ω (k + 4) g) :
    Sm α Ω k (fun t => Δ (Δ (g t))) :=
  Sm.laplacian hα hα1 hΩ (Sm.laplacian hα hα1 hΩ (show Sm α Ω (k + 2 + 2) g from h))

theorem Sm.lowOp (hα : 0 ≤ α) (hα1 : α ≤ 1) (hΩ : IsOpen Ω) (m : ℝ) (h : Sm α Ω (k + 3) g) :
    Sm α Ω k (fun t => lowOp m (g t)) := by
  have hL1 : Sm α Ω (k + 1) (fun t => Δ (g t)) :=
    Sm.laplacian hα hα1 hΩ (show Sm α Ω (k + 1 + 2) g from h)
  have hEL : Sm α Ω k (fun t => eulerE (Δ (g t))) := Sm.euler hα hα1 hL1
  have hL : Sm α Ω k (fun t => Δ (g t)) := hL1.of_le (by omega)
  have hE2 : Sm α Ω (k + 2) (fun t => eulerE (g t)) :=
    Sm.euler hα hα1 (show Sm α Ω (k + 2 + 1) g from h)
  have hEE : Sm α Ω k (fun t => eulerE (eulerE (g t))) :=
    Sm.euler hα hα1 (hE2.of_le (by omega))
  have hE : Sm α Ω k (fun t => eulerE (g t)) := hE2.of_le (by omega)
  have h0 : Sm α Ω k g := h.of_le (by omega)
  have hn : ContDiff ℝ ∞ fun z : V => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
  have c1 : Sm α Ω k (fun (_ : ℝ) (z : V) => -((4 + 2 * m) * (1 - ‖z‖ ^ 2))) :=
    Sm.of_contDiff hα hα1 ((contDiff_const.mul (contDiff_const.sub hn)).neg) Ω k
  have c2 : Sm α Ω k (fun (_ : ℝ) (z : V) => (160 + 2 * m) * ‖z‖ ^ 2 - 160) :=
    Sm.of_contDiff hα hα1 ((contDiff_const.mul hn).sub contDiff_const) Ω k
  have h5 := ((((c1.mul hEL).add (c2.mul hL)).add (hEE.const_mul hα hα1 (m ^ 2))).add
    (hE.const_mul hα hα1 (112 * m))).add (h0.const_mul hα hα1 2880)
  exact h5

end Ops

/-! ### From the first derivatives to the function -/

section Sum

variable {E : Type*} [NormedAddCommGroup E] {α a w : ℝ} {s : V × ℝ → ℝ} {N : Set (V × ℝ)}

theorem WH.sum' {ι : Type*} (S : Finset ι) {M : ι → ℝ} {f : ι → V × ℝ → E}
    (hs : ∀ p ∈ N, 0 < s p) (h : ∀ i ∈ S, WH α a s N w (M i) (f i)) :
    WH α a s N w (∑ i ∈ S, M i) (fun p => ∑ i ∈ S, f i p) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact WH.zero le_rfl hs
  | insert b S hb ih =>
    have h1 := (h b (Finset.mem_insert_self b S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert hb]
    exact h1

end Sum

/-- Appending a slot paired with a fixed vector. -/
noncomputable def appendSlot (m : ℕ) (e : V) : (V [×m]→L[ℝ] ℝ) →L[ℝ] (V [×(m + 1)]→L[ℝ] ℝ) :=
  ((continuousMultilinearCurryRightEquiv' ℝ m V ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => V) ℝ (V →L[ℝ] ℝ)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (innerSL ℝ e)))

omit [FiniteDimensional ℝ V] in
/-- The jet of order `m + 1` from the jets of order `m` of the first
derivatives. -/
theorem iteratedFDeriv_succ_of_partials {ι : Type*} [Fintype ι] (b : ι → V) {f : V → ℝ}
    {w : ι → V → ℝ} {x : V} {m : ℕ} (hw : ∀ i, ContDiffAt ℝ m (w i) x)
    (hev : fderiv ℝ f =ᶠ[𝓝 x] fun z => ∑ i, w i z • innerSL ℝ (b i)) :
    iteratedFDeriv ℝ (m + 1) f x = ∑ i, appendSlot m (b i) (iteratedFDeriv ℝ m (w i) x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  show ((continuousMultilinearCurryRightEquiv' ℝ m V
    ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    (iteratedFDeriv ℝ m (fun y => fderiv ℝ f y) x) = _
  have e1 : iteratedFDeriv ℝ m (fun y => fderiv ℝ f y) x
      = ∑ i, iteratedFDeriv ℝ m (fun z => w i z • innerSL ℝ (b i)) x := by
    rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
    exact iteratedFDeriv_fun_sum_apply fun i _ => (hw i).smul contDiffAt_const
  have e2 : ∀ i, iteratedFDeriv ℝ m (fun z => w i z • innerSL ℝ (b i)) x
      = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (innerSL ℝ (b i))).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (w i) x) := by
    intro i
    have h := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (innerSL ℝ (b i))).iteratedFDeriv_comp_left (hw i) (i := m) le_rfl
    have hfun : (fun z => w i z • innerSL ℝ (b i))
        = ⇑(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (innerSL ℝ (b i))) ∘ w i := by
      funext z
      simp
    rw [hfun]
    exact h
  rw [e1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e2 i]
  rfl

set_option maxHeartbeats 3200000 in
/-- **From the first derivatives to the function.** -/
theorem Sm.of_partials {α : ℝ} {Ω : Set (V × ℝ)} {k : ℕ} {g : ℝ → V → ℝ} (h1 : Sm α Ω 1 g)
    (hp : ∀ i, Sm α Ω k (fun t z => fderiv ℝ (g t) z (stdOrthonormalBasis ℝ V i))) :
    Sm α Ω (k + 1) g := by
  intro p₀ hp₀
  obtain ⟨N₀, g₀, M₀, hN₀, hp0, hM₀, hg₀, hs₀, hW₀⟩ := h1 p₀ hp₀
  choose N w M hN hpN hM hgw hsw hWw using fun i => hp i p₀ hp₀
  have hopen : IsOpen (N₀ ∩ ⋂ i, N i) := hN₀.inter (isOpen_iInter_of_finite hN)
  have hmem : p₀ ∈ N₀ ∩ ⋂ i, N i := ⟨hp0, mem_iInter.2 hpN⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen p₀ hmem
  have hbox : ∀ (z : V) (t : ℝ), ‖z - p₀.1‖ < ε → |t - p₀.2| < ε →
      ((z, t) : V × ℝ) ∈ N₀ ∩ ⋂ i, N i := by
    intro z t hz ht
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by rwa [dist_eq_norm], by rwa [Real.dist_eq]⟩
  have hbox0 : ∀ (z : V) (t : ℝ), ‖z - p₀.1‖ < ε → |t - p₀.2| < ε → ((z, t) : V × ℝ) ∈ N₀ :=
    fun z t hz ht => (hbox z t hz ht).1
  have hboxi : ∀ (z : V) (t : ℝ), ‖z - p₀.1‖ < ε → |t - p₀.2| < ε → ∀ i,
      ((z, t) : V × ℝ) ∈ N i := fun z t hz ht i => mem_iInter.1 (hbox z t hz ht).2 i
  -- the first derivatives of the representative
  have hfd : ∀ (z : V) (t : ℝ), ‖z - p₀.1‖ < ε → |t - p₀.2| < ε →
      fderiv ℝ (g₀ t) z = ∑ i, w i t z • innerSL ℝ (stdOrthonormalBasis ℝ V i) := by
    intro z t hz ht
    have hev := slice_eventuallyEq hN₀ hg₀ (p := (z, t)) (hbox0 z t hz ht)
    have hi : ∀ i, fderiv ℝ (g₀ t) z (stdOrthonormalBasis ℝ V i) = w i t z := by
      intro i
      have h2 : fderiv ℝ (g₀ t) z = fderiv ℝ (g t) z := hev.fderiv_eq
      rw [h2]
      exact (hgw i (z, t) (hboxi z t hz ht i)).symm
    ext v
    have h3 := congrArg (fderiv ℝ (g₀ t) z) ((stdOrthonormalBasis ℝ V).sum_repr' v)
    rw [map_sum] at h3
    simp only [map_smul, smul_eq_mul, hi] at h3
    rw [← h3]
    simp [mul_comm]
  have hBopen : IsOpen (Metric.ball p₀.1 ε) := Metric.isOpen_ball
  have hCD : ∀ t : ℝ, |t - p₀.2| < ε → ContDiffOn ℝ (k + 1 : ℕ) (g₀ t) (Metric.ball p₀.1 ε) := by
    intro t ht
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hBopen]
    refine ⟨((hs₀ t).differentiable (by norm_num)).differentiableOn, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · have hc : ContDiff ℝ k (fun z => ∑ i, w i t z • innerSL ℝ (stdOrthonormalBasis ℝ V i)) :=
        ContDiff.sum fun i _ => (hsw i t).smul contDiff_const
      refine hc.contDiffOn.congr fun z hz => ?_
      exact hfd z t (by rwa [Metric.mem_ball, dist_eq_norm] at hz) ht
  -- the cut-off
  have hμ : 0 < (ε / 2) ^ 2 := by positivity
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : V → ℝ, ζ = fun z => chiV ((ε / 2) ^ 2) (z - p₀.1) := ⟨_, rfl⟩
  have hζs : ContDiff ℝ ∞ ζ := by
    rw [hζdef]
    exact (contDiff_chiV _).comp (contDiff_id.sub contDiff_const)
  have hζ1 : ∀ z : V, ‖z - p₀.1‖ < ε / 2 → ζ z = 1 := by
    intro z hz
    rw [hζdef]
    exact chiV_of_le hμ (pow_le_pow_left₀ (norm_nonneg _) hz.le 2)
  have hζ0 : ∀ z : V, 2 * (ε / 2) ^ 2 < ‖z - p₀.1‖ ^ 2 → ζ z = 0 := by
    intro z hz
    rw [hζdef]
    exact chiV_of_ge hμ hz.le
  refine ⟨Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε,
    fun t z => if |t - p₀.2| < ε then ζ z * g₀ t z else 0,
    M₀ + ∑ m ∈ Finset.range (k + 1), ∑ i,
      ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i,
    Metric.isOpen_ball.prod Metric.isOpen_ball,
    ⟨Metric.mem_ball_self (by positivity), Metric.mem_ball_self hε⟩, ?_, ?_, ?_, ?_⟩
  · refine add_nonneg hM₀ (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)).opNorm_nonneg (hM i))
  · intro p hp
    have hz : ‖p.1 - p₀.1‖ < ε / 2 := by
      have := hp.1
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have ht : |p.2 - p₀.2| < ε := by
      have := hp.2
      rwa [Metric.mem_ball, Real.dist_eq] at this
    show (if |p.2 - p₀.2| < ε then ζ p.1 * g₀ p.2 p.1 else 0) = g p.2 p.1
    rw [if_pos ht, hζ1 p.1 hz, one_mul]
    exact hg₀ p (hbox0 p.1 p.2 (by linarith) ht)
  · intro t
    beta_reduce
    by_cases ht : |t - p₀.2| < ε
    · have e : (fun z => if |t - p₀.2| < ε then ζ z * g₀ t z else 0) = fun z => ζ z * g₀ t z := by
        funext z
        rw [if_pos ht]
      rw [e, contDiff_iff_contDiffAt]
      intro z
      by_cases hz : ‖z - p₀.1‖ < ε
      · exact (hζs.of_le (by exact_mod_cast le_top)).contDiffAt.mul
          ((hCD t ht).contDiffAt (hBopen.mem_nhds (by rwa [Metric.mem_ball, dist_eq_norm])))
      · have hopen2 : IsOpen {y : V | 2 * (ε / 2) ^ 2 < ‖y - p₀.1‖ ^ 2} :=
          isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm.pow 2)
        have hzmem : z ∈ {y : V | 2 * (ε / 2) ^ 2 < ‖y - p₀.1‖ ^ 2} := by
          have h2 : ε ≤ ‖z - p₀.1‖ := not_lt.1 hz
          have h3 := pow_le_pow_left₀ hε.le h2 2
          show 2 * (ε / 2) ^ 2 < ‖z - p₀.1‖ ^ 2
          nlinarith
        have hev : (fun y => ζ y * g₀ t y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hopen2.mem_nhds hzmem] with y hy
          rw [hζ0 y hy, zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq hev
    · have e : (fun z : V => if |t - p₀.2| < ε then ζ z * g₀ t z else 0) = fun _ => 0 := by
        funext z
        rw [if_neg ht]
      rw [e]
      exact contDiff_const
  · -- the jets of the representative on the small neighbourhood
    have hmemN : ∀ p ∈ Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε,
        ‖p.1 - p₀.1‖ < ε / 2 ∧ |p.2 - p₀.2| < ε := by
      intro p hp
      constructor
      · have := hp.1
        rwa [Metric.mem_ball, dist_eq_norm] at this
      · have := hp.2
        rwa [Metric.mem_ball, Real.dist_eq] at this
    have hevG : ∀ p ∈ Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε,
        (fun z => if |p.2 - p₀.2| < ε then ζ z * g₀ p.2 z else 0) =ᶠ[𝓝 p.1] g₀ p.2 := by
      intro p hp
      obtain ⟨hz, ht⟩ := hmemN p hp
      filter_upwards [Metric.isOpen_ball.mem_nhds hp.1] with y hy
      rw [if_pos ht, hζ1 y (by rwa [Metric.mem_ball, dist_eq_norm] at hy), one_mul]
    have hsub0 : Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε ⊆ N₀ := fun p hp => by
      obtain ⟨hz, ht⟩ := hmemN p hp
      exact hbox0 p.1 p.2 (by linarith) ht
    have hsubi : ∀ i, Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε ⊆ N i := fun i p hp => by
      obtain ⟨hz, ht⟩ := hmemN p hp
      exact hboxi p.1 p.2 (by linarith) ht i
    have hsumnn : 0 ≤ ∑ m ∈ Finset.range (k + 1), ∑ i,
        ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i :=
      Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)).opNorm_nonneg (hM i)
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have h0 := ((hW₀ 0 (by norm_num)).restrict hsub0).one_weight (w' := (0 : ℝ) - ((0 : ℕ) : ℝ))
      refine (h0.congr fun p hp => ?_).mono (fun _ _ => one_pos) (by linarith)
      exact ((hevG p hp).iteratedFDeriv ℝ 0).eq_of_nhds
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hm : m ≤ k := by omega
      have h1 := WH.sum' (α := α) (a := 1) (w := (0 : ℝ) - ((m + 1 : ℕ) : ℝ))
        (s := fun _ : V × ℝ => (1 : ℝ))
        (N := Metric.ball p₀.1 (ε / 2) ×ˢ Metric.ball p₀.2 ε) Finset.univ
        (M := fun i => ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i)
        (f := fun i p => appendSlot m (stdOrthonormalBasis ℝ V i)
          (iteratedFDeriv ℝ m (w i p.2) p.1))
        (fun _ _ => one_pos) (fun i _ =>
          ((((hWw i) m hm).restrict (hsubi i)).clm
            (appendSlot m (stdOrthonormalBasis ℝ V i))).one_weight)
      refine (h1.congr fun p hp => ?_).mono (fun _ _ => one_pos) ?_
      · obtain ⟨hz, ht⟩ := hmemN p hp
        rw [((hevG p hp).iteratedFDeriv ℝ (m + 1)).eq_of_nhds]
        refine iteratedFDeriv_succ_of_partials (fun i => stdOrthonormalBasis ℝ V i)
          (fun i => ((hsw i p.2).of_le (by exact_mod_cast hm)).contDiffAt) ?_
        filter_upwards [hBopen.mem_nhds (show p.1 ∈ Metric.ball p₀.1 ε by
          rw [Metric.mem_ball, dist_eq_norm]
          linarith)] with y hy
        exact hfd y p.2 (by rwa [Metric.mem_ball, dist_eq_norm] at hy) ht
      · have h2 : ∑ i, ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i
            ≤ ∑ m ∈ Finset.range (k + 1), ∑ i,
              ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i :=
          Finset.single_le_sum (f := fun m => ∑ i,
            ‖appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)‖ * M i)
            (fun m _ => Finset.sum_nonneg fun i _ =>
              mul_nonneg (appendSlot (V := V) m (stdOrthonormalBasis ℝ V i)).opNorm_nonneg
                (hM i)) (Finset.mem_range.2 (by omega))
        linarith

end Calabi.Weighted
