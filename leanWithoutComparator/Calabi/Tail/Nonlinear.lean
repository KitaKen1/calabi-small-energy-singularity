import Calabi.Tail.LinearExists
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Bounded solutions of `V‴ + V = F(s, V, V′, V″)` on a half-line

If `F` is Lipschitz in the jet with constant `κ < 3/5`, uniformly on `[S, ∞)`,
then every stable coordinate at `S` belongs to a bounded solution
(`exists_tail`), and bounded solutions depend Lipschitz-continuously on the
stable coordinate and on `F` (`tail_dist_le`). The constant `5/3` is the bound
of `Calabi.Tail.jet_bound`.
-/

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace Calabi.Tail

open Calabi.Shot (State)

theorem Solves.sub {S : ℝ} {X X' : ℝ → State} {j j' : ℝ → ℝ} (h : Solves S X j)
    (h' : Solves S X' j') : Solves S (fun s => X s - X' s) (fun s => j s - j' s) := by
  intro s hs
  refine ((h s hs).sub (h' s hs)).congr_deriv ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_sub, Prod.snd_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub]
    ring

theorem stab_sub (X Y : State) : stab (X - Y) = stab X - stab Y := by
  simp only [stab, Prod.fst_sub, Prod.snd_sub]
  ring

theorem energy_sub_le (X Y : State) : energy (X - Y) ≤ 2 * energy X + 2 * energy Y := by
  have hx : ux (X - Y) = ux X - ux Y := by
    simp only [ux, Prod.fst_sub, Prod.snd_sub]
    ring
  have hw : uw (X - Y) = uw X - uw Y := by
    simp only [uw, Prod.fst_sub, Prod.snd_sub]
    ring
  unfold energy
  rw [hx, hw]
  nlinarith [sq_nonneg (ux X + ux Y), sq_nonneg (uw X + uw Y)]

theorem energy_le_of_abs_le {X : State} {B : ℝ} (h1 : |X.1| ≤ B) (h2 : |X.2.1| ≤ B)
    (h3 : |X.2.2| ≤ B) : energy X ≤ 7 * B ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans h1
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 h3
  have hx : |ux X| ≤ 2 * B := by
    rw [abs_le]
    unfold ux
    constructor <;> linarith
  have hw : |uw X| ≤ B := by
    rw [abs_le]
    unfold uw
    constructor <;> linarith
  have hx2 : ux X ^ 2 ≤ (2 * B) ^ 2 := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
  have hw2 : uw X ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.1 hw).1 (abs_le.1 hw).2
  unfold energy
  nlinarith

/-- If every bound `B` of `f` improves to `c + θ B` with `θ < 1`, then
`c / (1 - θ)` is a bound. -/
theorem le_of_le_add_mul {ι : Type*} {p : ι → Prop} {f : ι → ℝ} {c θ B₀ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (h0 : ∀ i, p i → f i ≤ B₀)
    (hstep : ∀ B, (∀ i, p i → f i ≤ B) → ∀ i, p i → f i ≤ c + θ * B) :
    ∀ i, p i → f i ≤ c / (1 - θ) := by
  have h1θ : (1 - θ) ≠ 0 := by linarith
  have hall : ∀ n : ℕ, ∀ i, p i → f i ≤ c / (1 - θ) + θ ^ n * (B₀ - c / (1 - θ)) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have := h0 i hi
      simpa using this
    | succ n ih =>
      intro i hi
      have := hstep _ ih i hi
      have e : c + θ * (c / (1 - θ) + θ ^ n * (B₀ - c / (1 - θ))) =
          c / (1 - θ) + θ ^ (n + 1) * (B₀ - c / (1 - θ)) := by
        field_simp
        ring
      rwa [e] at this
  intro i hi
  have hlim : Tendsto (fun n : ℕ => c / (1 - θ) + θ ^ n * (B₀ - c / (1 - θ))) atTop
      (𝓝 (c / (1 - θ))) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).mul_const
      (B₀ - c / (1 - θ))).const_add (c / (1 - θ))
    simpa using h
  exact ge_of_tendsto' hlim fun n => hall n i hi

/-- **Lipschitz dependence.** Two bounded solutions, for nonlinearities that
differ by at most `δ`, differ by their stable coordinates at `S` and by `δ`. -/
theorem tail_dist_le {S κ δ : ℝ} {F F' : ℝ → State → ℝ} (hκ0 : 0 ≤ κ) (hκ : κ * (5 / 3) < 1)
    (hLip : ∀ s, S ≤ s → ∀ X Y, |F s X - F s Y| ≤ κ * dist X Y)
    (hFF' : ∀ s, S ≤ s → ∀ X, |F s X - F' s X| ≤ δ)
    {X X' : ℝ → State} (hX : Solves S X fun s => F s (X s))
    (hX' : Solves S X' fun s => F' s (X' s))
    (hb : ∃ B, ∀ s, S ≤ s → |(X s).1| ≤ B ∧ |(X s).2.1| ≤ B ∧ |(X s).2.2| ≤ B)
    (hb' : ∃ B, ∀ s, S ≤ s → |(X' s).1| ≤ B ∧ |(X' s).2.1| ≤ B ∧ |(X' s).2.2| ≤ B) :
    ∀ s, S ≤ s →
      dist (X s) (X' s) ≤ (|stab (X S) - stab (X' S)| + 5 / 3 * δ) / (1 - κ * (5 / 3)) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨B', hB'⟩ := hb'
  have hD := hX.sub hX'
  have hen : ∃ E, ∀ s, S ≤ s → energy (X s - X' s) ≤ E := by
    refine ⟨2 * (7 * B ^ 2) + 2 * (7 * B' ^ 2), fun s hs => ?_⟩
    obtain ⟨a1, a2, a3⟩ := hB s hs
    obtain ⟨b1, b2, b3⟩ := hB' s hs
    have := energy_sub_le (X s) (X' s)
    have e1 := energy_le_of_abs_le a1 a2 a3
    have e2 := energy_le_of_abs_le b1 b2 b3
    linarith
  have hθ0 : 0 ≤ κ * (5 / 3) := by positivity
  refine le_of_le_add_mul (p := fun s => S ≤ s) (f := fun s => dist (X s) (X' s))
    (B₀ := B + B') hθ0 hκ (fun s hs => ?_) fun C hC s hs => ?_
  · obtain ⟨a1, a2, a3⟩ := hB s hs
    obtain ⟨b1, b2, b3⟩ := hB' s hs
    rw [Calabi.Shot.State.dist_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · exact (abs_sub _ _).trans (add_le_add a1 b1)
    · exact (abs_sub _ _).trans (add_le_add a2 b2)
    · exact (abs_sub _ _).trans (add_le_add a3 b3)
  · have hj : ∀ u, S ≤ u → |F u (X u) - F' u (X' u)| ≤ κ * C + δ := by
      intro u hu
      have t1 := hLip u hu (X u) (X' u)
      have t2 := hFF' u hu (X' u)
      have t3 := abs_add_le (F u (X u) - F u (X' u)) (F u (X' u) - F' u (X' u))
      rw [sub_add_sub_cancel] at t3
      have t4 := mul_le_mul_of_nonneg_left (hC u hu) hκ0
      linarith
    obtain ⟨h1, h2, h3⟩ := jet_bound hD hj hen hs
    have hexp : Real.exp (-(s - S)) * |stab (X S - X' S)| ≤ |stab (X S - X' S)| :=
      mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
    rw [stab_sub] at hexp h1 h2 h3
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3
    rw [Calabi.Shot.State.dist_le_iff]
    have e : |stab (X S) - stab (X' S)| + 5 / 3 * δ + κ * (5 / 3) * C =
        |stab (X S) - stab (X' S)| + 5 / 3 * (κ * C + δ) := by ring
    rw [e]
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **Existence.** Every stable coordinate at `S` belongs to a bounded solution. -/
theorem exists_tail {S κ ε : ℝ} {F : ℝ → State → ℝ} (hκ0 : 0 ≤ κ) (hκ : κ * (5 / 3) < 1)
    (hFc : ContinuousOn (Function.uncurry F) (Ici S ×ˢ univ))
    (hLip : ∀ s, S ≤ s → ∀ X Y, |F s X - F s Y| ≤ κ * dist X Y)
    (hF0 : ∀ s, S ≤ s → |F s 0| ≤ ε) (q₀ : ℝ) :
    ∃ X : ℝ → State, Solves S X (fun s => F s (X s)) ∧ stab (X S) = q₀ ∧
      (∀ s, S ≤ s → energy (X s) ≤ 4 * ((ε + κ * |q₀|) / (1 - κ * (5 / 3))) ^ 2) ∧
      ∀ s, S ≤ s →
        |(X s).1| ≤ Real.exp (-(s - S)) * |q₀| + 5 / 3 * ((ε + κ * |q₀|) / (1 - κ * (5 / 3))) ∧
        |(X s).2.1| ≤
          Real.exp (-(s - S)) * |q₀| + 5 / 3 * ((ε + κ * |q₀|) / (1 - κ * (5 / 3))) ∧
        |(X s).2.2| ≤
          Real.exp (-(s - S)) * |q₀| + 5 / 3 * ((ε + κ * |q₀|) / (1 - κ * (5 / 3))) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hF0 S le_rfl)
  have hθ : 0 < 1 - κ * (5 / 3) := by linarith
  have hK : (0 : ℝ) ≤ κ * (5 / 3) := by positivity
  have habs : ∀ (j : ℝ →ᵇ ℝ) (u : ℝ), |j u| ≤ ‖j‖ := fun j u => by
    rw [← Real.norm_eq_abs]
    exact j.norm_coe_le_norm u
  have hsol : ∀ j : ℝ →ᵇ ℝ, Solves S (linSol S q₀ j) j := fun j =>
    linSol_solves j.continuous (habs j) S q₀ S
  have hen : ∀ j : ℝ →ᵇ ℝ, ∀ u, energy (linSol S q₀ j u) ≤ 4 * ‖j‖ ^ 2 := fun j u =>
    energy_linSol_le (habs j) S q₀ u
  have hjet : ∀ (j : ℝ →ᵇ ℝ) (s : ℝ), S ≤ s →
      |(linSol S q₀ j s).1| ≤ Real.exp (-(s - S)) * |q₀| + 5 / 3 * ‖j‖ ∧
      |(linSol S q₀ j s).2.1| ≤ Real.exp (-(s - S)) * |q₀| + 5 / 3 * ‖j‖ ∧
      |(linSol S q₀ j s).2.2| ≤ Real.exp (-(s - S)) * |q₀| + 5 / 3 * ‖j‖ := by
    intro j s hs
    have h := jet_bound (hsol j) (fun u _ => habs j u) ⟨4 * ‖j‖ ^ 2, fun u _ => hen j u⟩ hs
    rwa [stab_linSol_self] at h
  have hexp : ∀ s, S ≤ s → Real.exp (-(s - S)) * |q₀| ≤ |q₀| := fun s hs =>
    mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
  have hXc : ∀ j : ℝ →ᵇ ℝ, Continuous (linSol S q₀ j) := fun j =>
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_linSol j.continuous (habs j) S q₀ s).continuousAt
  have hTc : ∀ j : ℝ →ᵇ ℝ,
      Continuous fun s : ℝ => F (max s S) (linSol S q₀ j (max s S)) := by
    intro j
    have hm : Continuous fun s : ℝ => max s S := continuous_id.max continuous_const
    exact hFc.comp_continuous (hm.prodMk ((hXc j).comp hm))
      fun s => ⟨le_max_right s S, mem_univ _⟩
  have hTb : ∀ (j : ℝ →ᵇ ℝ) (s : ℝ),
      |F (max s S) (linSol S q₀ j (max s S))| ≤ ε + κ * (|q₀| + 5 / 3 * ‖j‖) := by
    intro j s
    have hs : S ≤ max s S := le_max_right s S
    obtain ⟨h1, h2, h3⟩ := hjet j (max s S) hs
    have he := hexp (max s S) hs
    have hd : dist (linSol S q₀ j (max s S)) 0 ≤ |q₀| + 5 / 3 * ‖j‖ := by
      rw [Calabi.Shot.State.dist_le_iff]
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
      exact ⟨by linarith, by linarith, by linarith⟩
    have t1 := hLip (max s S) hs (linSol S q₀ j (max s S)) 0
    have t2 := hF0 (max s S) hs
    have t3 := abs_add_le (F (max s S) (linSol S q₀ j (max s S)) - F (max s S) 0)
      (F (max s S) 0)
    rw [sub_add_cancel] at t3
    have t4 := mul_le_mul_of_nonneg_left hd hκ0
    linarith
  let T : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) := fun j =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun s : ℝ => F (max s S) (linSol S q₀ j (max s S))) (hTc j)
      (ε + κ * (|q₀| + 5 / 3 * ‖j‖)) fun s => by
        rw [Real.norm_eq_abs]
        exact hTb j s
  have hTapp : ∀ (j : ℝ →ᵇ ℝ) (s : ℝ), T j s = F (max s S) (linSol S q₀ j (max s S)) :=
    fun _ _ => rfl
  have hT : ContractingWith (κ * (5 / 3)).toNNReal T := by
    refine ⟨Real.toNNReal_lt_one.2 hκ, LipschitzWith.of_dist_le_mul fun j j' => ?_⟩
    · rw [Real.coe_toNNReal _ hK, BoundedContinuousFunction.dist_le (mul_nonneg hK dist_nonneg)]
      intro s
      rw [hTapp, hTapp, Real.dist_eq]
      have hs : S ≤ max s S := le_max_right s S
      have hD := (hsol j).sub (hsol j')
      have hjj : ∀ u, S ≤ u → |j u - j' u| ≤ dist j j' := fun u _ => by
        rw [← Real.dist_eq]
        exact BoundedContinuousFunction.dist_coe_le_dist u
      have henD : ∃ E, ∀ u, S ≤ u → energy (linSol S q₀ j u - linSol S q₀ j' u) ≤ E :=
        ⟨2 * (4 * ‖j‖ ^ 2) + 2 * (4 * ‖j'‖ ^ 2), fun u _ => by
          have := energy_sub_le (linSol S q₀ j u) (linSol S q₀ j' u)
          linarith [hen j u, hen j' u]⟩
      obtain ⟨h1, h2, h3⟩ := jet_bound hD hjj henD hs
      rw [stab_sub, stab_linSol_self, stab_linSol_self, sub_self, abs_zero, mul_zero,
        zero_add] at h1 h2 h3
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3
      have hd : dist (linSol S q₀ j (max s S)) (linSol S q₀ j' (max s S)) ≤
          5 / 3 * dist j j' := by
        rw [Calabi.Shot.State.dist_le_iff]
        exact ⟨h1, h2, h3⟩
      have t1 := hLip (max s S) hs (linSol S q₀ j (max s S)) (linSol S q₀ j' (max s S))
      have t2 := mul_le_mul_of_nonneg_left hd hκ0
      calc |F (max s S) (linSol S q₀ j (max s S)) - F (max s S) (linSol S q₀ j' (max s S))|
          ≤ κ * dist (linSol S q₀ j (max s S)) (linSol S q₀ j' (max s S)) := t1
        _ ≤ κ * (5 / 3 * dist j j') := t2
        _ = κ * (5 / 3) * dist j j' := by ring
  have hfix : T (ContractingWith.fixedPoint T hT) = ContractingWith.fixedPoint T hT :=
    hT.fixedPoint_isFixedPt
  generalize ContractingWith.fixedPoint T hT = jf at hfix
  have hJ : ‖jf‖ ≤ (ε + κ * |q₀|) / (1 - κ * (5 / 3)) := by
    have h1 : ‖T jf‖ ≤ ε + κ * (|q₀| + 5 / 3 * ‖jf‖) :=
      (BoundedContinuousFunction.norm_le (by positivity)).2 fun s => by
        rw [Real.norm_eq_abs]
        exact hTb jf s
    rw [hfix] at h1
    rw [le_div_iff₀ hθ]
    nlinarith
  have hJ0 : 0 ≤ ‖jf‖ := norm_nonneg jf
  refine ⟨linSol S q₀ jf, ?_, stab_linSol_self S q₀ jf, fun s _ => ?_, fun s hs => ?_⟩
  · intro s hs
    have h := hasDerivAt_linSol jf.continuous (habs jf) S q₀ s
    have e : jf s = F s (linSol S q₀ jf s) := by
      conv_lhs => rw [← hfix]
      rw [hTapp, max_eq_left hs]
    rwa [e] at h
  · refine (hen jf s).trans ?_
    have := mul_le_mul hJ hJ hJ0 (hJ0.trans hJ)
    nlinarith
  · obtain ⟨h1, h2, h3⟩ := hjet jf s hs
    exact ⟨by linarith, by linarith, by linarith⟩

end Calabi.Tail
