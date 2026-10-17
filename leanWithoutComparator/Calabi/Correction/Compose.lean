import Calabi.Correction.SmoothBase
import Calabi.Correction.TwoPointMore

/-!
# Composition with a smooth map in the local classes

The two pieces of the solution live in two different charts. On the overlap
of the charts the piece of the second chart is transferred to the first one by
composition with a smooth map `Ψ`. `Sm.comp_map` shows that this preserves the
local classes: if `u` is in the class of order `k`, so is `u(t, Ψ(z))`.

The proof is an induction on the order that uses only the chain rule of first
order: the derivative of `u ∘ Ψ` is `Σᵢ (∂ᵢu ∘ Ψ) • (ℓᵢ ∘ DΨ)`, the functions
`∂ᵢ u` are of the class of order `k - 1`, and the products are handled by
`WJ.smul`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Sums

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {α a w : ℝ} {s : V × ℝ → ℝ}
  {Ω : Set (V × ℝ)}

/-- Finite sums of functions with weighted jets. -/
theorem WJ.sum {ι : Type*} (S : Finset ι) {n : ℕ} {Mi : ι → ℝ} {f : ι → ℝ → V → E}
    (hs : ∀ p ∈ Ω, 0 < s p) (hf : ∀ i ∈ S, ∀ t, ContDiff ℝ n (f i t))
    (h : ∀ i ∈ S, WJ α a s Ω w (Mi i) n (f i)) :
    WJ α a s Ω w (∑ i ∈ S, Mi i) n (fun t x => ∑ i ∈ S, f i t x) := by
  intro j hj
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have h1 := WH.sum' (α := α) (a := a) (w := w - (j : ℝ)) (s := s) (N := Ω) S (M := Mi)
    (f := fun i p => iteratedFDeriv ℝ j (f i p.2) p.1) hs (fun i hi => h i hi j hj)
  refine h1.congr fun p _ => ?_
  exact iteratedFDeriv_fun_sum_apply fun i hi => ((hf i hi p.2).of_le hjn).contDiffAt

end Sums

/-- A smooth function that does not depend on the time has uniform jets on a
set with a bounded projection to the space. -/
theorem WJ_of_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ} (hα : 0 ≤ α)
    (hα1 : α ≤ 1) {B : V → E} (hB : ContDiff ℝ ∞ B) {N : Set (V × ℝ)} {z₀ : V} {R : ℝ}
    (hN : ∀ p ∈ N, ‖p.1 - z₀‖ ≤ R) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 A k (fun _ => B) := by
  have hbd : ∀ j : ℕ, ∃ A : ℝ, ∀ z ∈ Metric.closedBall z₀ R, ‖iteratedFDeriv ℝ j B z‖ ≤ A :=
    fun j => (isCompact_closedBall z₀ R).exists_bound_of_continuousOn
      ((hB.of_le (by exact_mod_cast le_top)).continuous_iteratedFDeriv' (m := j)).continuousOn
  choose A hA using hbd
  obtain ⟨At, hAtdef⟩ : ∃ At : ℝ, At = ∑ i ∈ Finset.range (k + 2), |A i| := ⟨_, rfl⟩
  have hAt0 : 0 ≤ At := by
    rw [hAtdef]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hAle : ∀ j : ℕ, j ≤ k + 1 → A j ≤ At := fun j hj => by
    rw [hAtdef]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |A i|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  have hmem : ∀ p ∈ N, p.1 ∈ Metric.closedBall z₀ R := fun p hp => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hN p hp
  refine ⟨2 * At, by positivity, fun j hj => ?_⟩
  refine WH.of_lipschitz (fun _ _ => one_pos) hAt0 le_rfl hα hα1 (fun p hp => ?_)
    (fun p hp q hq _ => ?_)
  · rw [Real.one_rpow, mul_one]
    exact (hA j p.1 (hmem p hp)).trans (hAle j (by omega))
  · have hdiff : ∀ z ∈ Metric.closedBall z₀ R, DifferentiableAt ℝ (iteratedFDeriv ℝ j B) z :=
      fun z _ => ((hB.of_le (by exact_mod_cast le_top) :
        ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) B).differentiable_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self j)) z
    have hbound : ∀ z ∈ Metric.closedBall z₀ R, ‖fderiv ℝ (iteratedFDeriv ℝ j B) z‖ ≤ At := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      exact (hA (j + 1) z hz).trans (hAle (j + 1) (by omega))
    have hmv := (convex_closedBall z₀ R).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (hmem q hq) (hmem p hp)
    have h4 : 0 ≤ At * (1 : ℝ) ^ ((0 : ℝ) - (j : ℝ) - 4) * |p.2 - q.2| :=
      mul_nonneg (mul_nonneg hAt0 (Real.rpow_nonneg zero_le_one _)) (abs_nonneg _)
    show ‖iteratedFDeriv ℝ j B p.1 - iteratedFDeriv ℝ j B q.1‖
      ≤ At * (1 : ℝ) ^ ((0 : ℝ) - (j : ℝ) - 1) * ‖p.1 - q.1‖
        + At * (1 : ℝ) ^ ((0 : ℝ) - (j : ℝ) - 4) * |p.2 - q.2|
    rw [Real.one_rpow, mul_one] at h4 ⊢
    rw [Real.one_rpow, mul_one]
    linarith

/-- A linear isometry preserves two-point bounds. -/
theorem WH.isometry {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] {α a w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}
    {f : V × ℝ → E} (e : E ≃ₗᵢ[ℝ] F) (hf : WH α a s Ω w M f) :
    WH α a s Ω w M (fun p => e (f p)) :=
  ⟨fun p hp => by
    rw [e.norm_map]
    exact hf.1 p hp, fun p hp q hq hd => by
    rw [← e.map_sub, e.norm_map]
    exact hf.2 p hp q hq hd⟩

/-- The derivative in a direction of a function with uniform jets. -/
theorem WJ.fderiv_apply {α M : ℝ} {N : Set (V × ℝ)} {k : ℕ} {u : ℝ → V → ℝ} (hM : 0 ≤ M)
    (hs : ∀ t, ContDiff ℝ (k + 1 : ℕ) (u t))
    (hW : WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M (k + 1) u) (e : V) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M₁ k
      (fun t z => fderiv ℝ (u t) z e) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ∑ j ∈ Finset.range (k + 1), ‖lastSlot (V := V) j e‖ :=
    ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact Finset.sum_nonneg fun j _ => (lastSlot (V := V) j e).opNorm_nonneg
  have hLj : ∀ j : ℕ, j ≤ k → ‖lastSlot (V := V) j e‖ ≤ L := fun j hj => by
    rw [hLdef]
    exact Finset.single_le_sum (f := fun j => ‖lastSlot (V := V) j e‖)
      (fun i _ => (lastSlot (V := V) i e).opNorm_nonneg) (Finset.mem_range.2 (by omega))
  refine ⟨L * M, mul_nonneg hL0 hM, fun j hj => ?_⟩
  have h1 := ((hW (j + 1) (by omega)).clm (lastSlot j e)).one_weight (w' := (0 : ℝ) - (j : ℝ))
  refine (h1.congr fun p _ => ?_).mono (fun _ _ => one_pos)
    (mul_le_mul_of_nonneg_right (hLj j hj) hM)
  exact iteratedFDeriv_fderiv_apply
    ((hs p.2).of_le (by exact_mod_cast Nat.succ_le_succ hj)).contDiffAt e

section Comp

variable {V' : Type} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']

/-- The values of a composition with a Lipschitz map. -/
theorem WH.comp_lipschitz {E : Type*} [NormedAddCommGroup E] {α M L w w' : ℝ} {Ψ : V → V'}
    {N : Set (V × ℝ)} {N' : Set (V' × ℝ)} {f : V' × ℝ → E} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hL : 1 ≤ L) (hmaps : ∀ p ∈ N, ((Ψ p.1, p.2) : V' × ℝ) ∈ N')
    (hLip : ∀ p ∈ N, ∀ q ∈ N, ‖Ψ p.1 - Ψ q.1‖ ≤ L * ‖p.1 - q.1‖)
    (hW : WH α 1 (fun _ : V' × ℝ => (1 : ℝ)) N' w M f) :
    WH α 1 (fun _ : V × ℝ => (1 : ℝ)) N w'
      (M * (1 : ℝ) ^ (|w| + |w - α|) * L ^ α
        * (1 + (1 + (1 : ℝ) ^ |w|) * (1 / (1 * L)) ^ (-α)))
      (fun p => f (Ψ p.1, p.2)) := by
  have hL0 : 0 < L := by linarith
  have h1 := WH.comp_map (Φ := fun p : V × ℝ => ((Ψ p.1, p.2) : V' × ℝ))
    (s' := fun _ : V × ℝ => (1 : ℝ)) (Ω' := N) (k := 1) (L := L) hW hM le_rfl hL zero_le_one hα
    hmaps (fun _ _ => one_pos) (fun _ _ => one_pos) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun p hp q hq => by
      have h2 := hLip p hp q hq
      have h3 : (0 : ℝ) ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
      unfold pdist
      show ‖Ψ p.1 - Ψ q.1‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4)
        ≤ L * (‖p.1 - q.1‖ + |p.2 - q.2| ^ ((1 : ℝ) / 4))
      nlinarith)
  have hM' : 0 ≤ M * (1 : ℝ) ^ (|w| + |w - α|) * L ^ α :=
    mul_nonneg (mul_nonneg hM (Real.rpow_nonneg zero_le_one _)) (Real.rpow_nonneg hL0.le _)
  have h4 := h1.radius_ge (a' := 1) (IsScale.const one_pos) hM' (by positivity) hα
  exact h4.one_weight

set_option maxHeartbeats 3200000 in
/-- **Composition with a smooth map preserves uniform jets.** -/
theorem WJ.comp_smooth {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ψ : V → V'} (hΨ : ContDiff ℝ ∞ Ψ)
    {N : Set (V × ℝ)} {N' : Set (V' × ℝ)} (hmaps : ∀ p ∈ N, ((Ψ p.1, p.2) : V' × ℝ) ∈ N')
    {z₀ : V} {R L : ℝ} (hN : ∀ p ∈ N, ‖p.1 - z₀‖ ≤ R) (hL : 1 ≤ L)
    (hLip : ∀ p ∈ N, ∀ q ∈ N, ‖Ψ p.1 - Ψ q.1‖ ≤ L * ‖p.1 - q.1‖) (k : ℕ) :
    ∀ (u : ℝ → V' → ℝ) (M : ℝ), 0 ≤ M → (∀ t, ContDiff ℝ k (u t)) →
      WJ α 1 (fun _ : V' × ℝ => (1 : ℝ)) N' 0 M k u →
      ∃ M' : ℝ, 0 ≤ M' ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M' k
        (fun t z => u t (Ψ z)) := by
  have hL0 : 0 < L := by linarith
  -- the jets of order zero
  have hzero : ∀ (u : ℝ → V' → ℝ) (M : ℝ), 0 ≤ M →
      WH α 1 (fun _ : V' × ℝ => (1 : ℝ)) N' 0 M (fun p => u p.2 p.1) →
      ∃ M₀ : ℝ, 0 ≤ M₀ ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M₀ 0 (fun t z => u t (Ψ z)) := by
    intro u M hM hW
    have h1 := WH.comp_lipschitz (w' := (0 : ℝ)) hα hM hL hmaps hLip hW
    refine ⟨_, ?_, WJ.zero_of_WH h1⟩
    have h2 : 0 ≤ (1 / (1 * L)) ^ (-α) := Real.rpow_nonneg (by positivity) _
    have h3 : 0 ≤ (1 : ℝ) ^ (|(0 : ℝ)| + |(0 : ℝ) - α|) := Real.rpow_nonneg zero_le_one _
    have h4 : 0 ≤ L ^ α := Real.rpow_nonneg hL0.le _
    have h5 : 0 ≤ (1 : ℝ) ^ |(0 : ℝ)| := Real.rpow_nonneg zero_le_one _
    positivity
  induction k with
  | zero =>
    intro u M hM _ hW
    exact hzero u M hM hW.value
  | succ k ih =>
    intro u M hM hs hW
    have hs1 : ∀ t, Differentiable ℝ (u t) := fun t => (hs t).differentiable (by simp)
    have hΨk : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast le_top)
    have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    -- the first derivatives of `u`, composed with `Ψ`
    have hpart : ∀ i, ∃ Mi : ℝ, 0 ≤ Mi ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 Mi k
        (fun t z => fderiv ℝ (u t) (Ψ z) (stdOrthonormalBasis ℝ V' i)) := by
      intro i
      obtain ⟨M₁, hM₁, hW₁⟩ := WJ.fderiv_apply hM hs hW (stdOrthonormalBasis ℝ V' i)
      exact ih (fun t y => fderiv ℝ (u t) y (stdOrthonormalBasis ℝ V' i)) M₁ hM₁
        (fun t => ((hs t).fderiv_right (m := k) (by exact_mod_cast le_rfl)).clm_apply
          contDiff_const) hW₁
    choose Mi hMi hWi using hpart
    -- the smooth factors
    have hBs : ∀ i, ContDiff ℝ ∞ (fun y : V =>
        (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ y)) := fun i =>
      contDiff_const.clm_comp (hΨ.fderiv_right (by simp))
    have hBW : ∀ i, ∃ A : ℝ, 0 ≤ A ∧ WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 A k
        (fun (_ : ℝ) (y : V) => (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ y)) :=
      fun i => WJ_of_smooth hα hα1 (hBs i) hN k
    choose Ai hAi hWA using hBW
    have hci : ∀ i t, ContDiff ℝ k
        (fun z => fderiv ℝ (u t) (Ψ z) (stdOrthonormalBasis ℝ V' i)) := fun i t =>
      (((hs t).fderiv_right (m := k) (by exact_mod_cast le_rfl)).clm_apply contDiff_const).comp
        (hΨ.of_le (by exact_mod_cast le_top))
    have hprod : ∀ i, WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0
        (2 ^ k * (1 + (1 : ℝ) ^ (k : ℝ)) * Mi i * Ai i) k
        (fun t z => fderiv ℝ (u t) (Ψ z) (stdOrthonormalBasis ℝ V' i)
          • (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ z)) := fun i =>
      WJ.smul (IsScale.const one_pos) (hMi i) (hAi i) (hci i)
        (fun _ => (hBs i).of_le (by exact_mod_cast le_top)) (hWi i) (hWA i)
    have hsum := WJ.sum (α := α) (a := 1) (w := 0) (s := fun _ : V × ℝ => (1 : ℝ)) (Ω := N)
      Finset.univ (n := k)
      (Mi := fun i => 2 ^ k * (1 + (1 : ℝ) ^ (k : ℝ)) * Mi i * Ai i)
      (f := fun i t z => fderiv ℝ (u t) (Ψ z) (stdOrthonormalBasis ℝ V' i)
        • (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ z))
      (fun _ _ => one_pos)
      (fun i _ t => (hci i t).smul ((hBs i).of_le (by exact_mod_cast le_top)))
      (fun i _ => hprod i)
    -- the derivative of the composition
    have hfd : ∀ t, fderiv ℝ (fun z => u t (Ψ z)) = fun z => ∑ i,
        fderiv ℝ (u t) (Ψ z) (stdOrthonormalBasis ℝ V' i)
          • (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ z) := by
      intro t
      funext z
      have h1 : HasFDerivAt (fun z => u t (Ψ z)) ((fderiv ℝ (u t) (Ψ z)).comp (fderiv ℝ Ψ z)) z :=
        (hs1 t (Ψ z)).hasFDerivAt.comp z (hΨd z).hasFDerivAt
      rw [h1.fderiv]
      ext v
      have h3 := congrArg (fderiv ℝ (u t) (Ψ z))
        ((stdOrthonormalBasis ℝ V').sum_repr' (fderiv ℝ Ψ z v))
      rw [map_sum] at h3
      simp only [map_smul, smul_eq_mul] at h3
      rw [ContinuousLinearMap.comp_apply, ← h3]
      simp [mul_comm]
    obtain ⟨M₀, hM₀, hW₀⟩ := hzero u M hM hW.value
    have hMs : 0 ≤ ∑ i, 2 ^ k * (1 + (1 : ℝ) ^ (k : ℝ)) * Mi i * Ai i :=
      Finset.sum_nonneg fun i _ => by
        have := hMi i
        have := hAi i
        positivity
    refine ⟨M₀ + ∑ i, 2 ^ k * (1 + (1 : ℝ) ^ (k : ℝ)) * Mi i * Ai i, add_nonneg hM₀ hMs,
      fun j hj => ?_⟩
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      exact (hW₀ 0 le_rfl).mono (fun _ _ => one_pos) (by linarith)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hm : m ≤ k := by omega
      have h1 := (((hsum m hm).isometry
        (continuousMultilinearCurryRightEquiv' ℝ m V ℝ).symm).one_weight
        (w' := (0 : ℝ) - ((m + 1 : ℕ) : ℝ)))
      refine (h1.congr fun p _ => ?_).mono (fun _ _ => one_pos) (by linarith)
      show iteratedFDeriv ℝ (m + 1) (fun z => u p.2 (Ψ z)) p.1
        = (continuousMultilinearCurryRightEquiv' ℝ m V ℝ).symm
          (iteratedFDeriv ℝ m (fun z => ∑ i,
            fderiv ℝ (u p.2) (Ψ z) (stdOrthonormalBasis ℝ V' i)
              • (innerSL ℝ (stdOrthonormalBasis ℝ V' i)).comp (fderiv ℝ Ψ z)) p.1)
      rw [iteratedFDeriv_succ_eq_comp_right, ← hfd p.2]
      rfl

set_option maxHeartbeats 1600000 in
/-- **Composition with a smooth map preserves the local classes.** -/
theorem Sm.comp_map {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ψ : V → V'} (hΨ : ContDiff ℝ ∞ Ψ)
    {Ω : Set (V × ℝ)} {Ω' : Set (V' × ℝ)} (hmaps : ∀ p ∈ Ω, ((Ψ p.1, p.2) : V' × ℝ) ∈ Ω')
    {k : ℕ} {u : ℝ → V' → ℝ} (h : Sm α Ω' k u) : Sm α Ω k (fun t z => u t (Ψ z)) := by
  intro p₀ hp₀
  obtain ⟨N', u', M, hN', hp', hM, hgg, hs, hW⟩ := h (Ψ p₀.1, p₀.2) (hmaps p₀ hp₀)
  have hΨc : Continuous fun p : V × ℝ => ((Ψ p.1, p.2) : V' × ℝ) :=
    (hΨ.continuous.comp continuous_fst).prodMk continuous_snd
  -- a Lipschitz constant of `Ψ` on the unit ball around the point
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall p₀.1 1).exists_bound_of_continuousOn
    ((hΨ.continuous_fderiv (by simp)).continuousOn)
  have hLip : ∀ z ∈ Metric.closedBall p₀.1 1, ∀ z' ∈ Metric.closedBall p₀.1 1,
      ‖Ψ z - Ψ z'‖ ≤ (|L₀| + 1) * ‖z - z'‖ := by
    intro z hz z' hz'
    exact (convex_closedBall p₀.1 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hΨ.differentiable (by simp)) y)
      (fun y hy => (hL₀ y hy).trans ((le_abs_self _).trans (by linarith))) hz' hz
  have hNmem : ∀ p ∈ (fun p : V × ℝ => ((Ψ p.1, p.2) : V' × ℝ)) ⁻¹' N'
      ∩ (Metric.ball p₀.1 1 ×ˢ univ), p.1 ∈ Metric.closedBall p₀.1 1 := fun p hp =>
    Metric.ball_subset_closedBall hp.2.1
  obtain ⟨M', hM', hW'⟩ := WJ.comp_smooth hα hα1 hΨ
    (N := (fun p : V × ℝ => ((Ψ p.1, p.2) : V' × ℝ)) ⁻¹' N' ∩ (Metric.ball p₀.1 1 ×ˢ univ))
    (N' := N') (fun p hp => hp.1) (z₀ := p₀.1) (R := 1) (L := |L₀| + 1)
    (fun p hp => by
      have := hNmem p hp
      rwa [Metric.mem_closedBall, dist_eq_norm] at this)
    (by linarith [abs_nonneg L₀])
    (fun p hp q hq => hLip p.1 (hNmem p hp) q.1 (hNmem q hq)) k u' M hM hs hW
  refine ⟨(fun p : V × ℝ => ((Ψ p.1, p.2) : V' × ℝ)) ⁻¹' N' ∩ (Metric.ball p₀.1 1 ×ˢ univ),
    fun t z => u' t (Ψ z), M', (hN'.preimage hΨc).inter (Metric.isOpen_ball.prod isOpen_univ),
    ⟨hp', Metric.mem_ball_self one_pos, mem_univ _⟩, hM', fun p hp => ?_, fun t => ?_, hW'⟩
  · exact hgg (Ψ p.1, p.2) hp.1
  · exact (hs t).comp (hΨ.of_le (by exact_mod_cast le_top))

end Comp

end Calabi.Weighted
