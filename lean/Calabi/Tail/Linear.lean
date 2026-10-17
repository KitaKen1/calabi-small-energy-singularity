import Calabi.Shot.BlockODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bounded solutions of `V‴ + V = j` on a half-line: a priori bounds

Jets `(V, V′, V″)` are split along the roots of `λ³ + 1`. The stable
coordinate `stab` belongs to `λ = -1`; the unstable coordinates `ux`, `uw`
belong to `λ² - λ + 1 = 0`. All coefficients are rational:

  `stab′ = -stab + j / 3`,   `ux′ = ux / 2 - 3 uw / 2 + j`,   `uw′ = ux / 2 + uw / 2`,

and `energy = ux² + 3 uw²` satisfies `energy′ = energy + 2 ux j`. A solution
that stays bounded on `[S, ∞)` therefore has `energy ≤ 4 sup |j|²`: otherwise
the energy would grow exponentially. No Green function is needed for this.
-/

open Set Filter
open scoped Topology

namespace Calabi.Tail

open Calabi.Shot (State)

/-- The stable coordinate of a jet. -/
noncomputable def stab (X : State) : ℝ := (X.1 - X.2.1 + X.2.2) / 3

/-- The first unstable coordinate of a jet. -/
noncomputable def ux (X : State) : ℝ := -X.1 / 2 + X.2.1 / 2 + X.2.2

/-- The second unstable coordinate of a jet. -/
noncomputable def uw (X : State) : ℝ := (X.1 + X.2.1) / 2

/-- The quadratic form on the unstable plane that the flow of `∂³ + 1` expands
at the exact rate `1`. -/
noncomputable def energy (X : State) : ℝ := ux X ^ 2 + 3 * uw X ^ 2

theorem energy_nonneg (X : State) : 0 ≤ energy X := by
  unfold energy
  positivity

theorem fst_eq (X : State) : X.1 = stab X + uw X - ux X / 3 := by
  simp only [stab, ux, uw]
  ring

theorem snd_eq (X : State) : X.2.1 = -stab X + ux X / 3 + uw X := by
  simp only [stab, ux, uw]
  ring

theorem thd_eq (X : State) : X.2.2 = stab X + 2 * ux X / 3 := by
  simp only [stab, ux]
  ring

/-- `X` is the jet of a solution of `V‴ + V = j` on `[S, ∞)`. -/
def Solves (S : ℝ) (X : ℝ → State) (j : ℝ → ℝ) : Prop :=
  ∀ s, S ≤ s → HasDerivAt X ((X s).2.1, (X s).2.2, -(X s).1 + j s) s

theorem Solves.mono {S S' : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (h : Solves S X j) (hS : S ≤ S') :
    Solves S' X j := fun s hs => h s (hS.trans hs)

theorem hasDerivAt_components {X : ℝ → State} {s : ℝ} {Y : State} (h : HasDerivAt X Y s) :
    HasDerivAt (fun t => (X t).1) Y.1 s ∧ HasDerivAt (fun t => (X t).2.1) Y.2.1 s ∧
      HasDerivAt (fun t => (X t).2.2) Y.2.2 s := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt s h
  have h23 := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt s h
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt s h23
  have h3 := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt s h23
  exact ⟨h1, h2, h3⟩

theorem hasDerivAt_stab {S : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (h : Solves S X j) {s : ℝ}
    (hs : S ≤ s) : HasDerivAt (fun t => stab (X t)) (-stab (X s) + j s / 3) s := by
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_components (h s hs)
  refine (((h1.sub h2).add h3).div_const 3).congr_deriv ?_
  simp only [Tail.stab]
  ring

theorem hasDerivAt_ux {S : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (h : Solves S X j) {s : ℝ}
    (hs : S ≤ s) :
    HasDerivAt (fun t => ux (X t)) (ux (X s) / 2 - 3 * uw (X s) / 2 + j s) s := by
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_components (h s hs)
  refine (((h1.neg.div_const 2).add (h2.div_const 2)).add h3).congr_deriv ?_
  simp only [Tail.ux, Tail.uw]
  ring

theorem hasDerivAt_uw {S : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (h : Solves S X j) {s : ℝ}
    (hs : S ≤ s) : HasDerivAt (fun t => uw (X t)) (ux (X s) / 2 + uw (X s) / 2) s := by
  obtain ⟨h1, h2, -⟩ := hasDerivAt_components (h s hs)
  refine ((h1.add h2).div_const 2).congr_deriv ?_
  simp only [Tail.ux, Tail.uw]
  ring

theorem hasDerivAt_energy {S : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (h : Solves S X j) {s : ℝ}
    (hs : S ≤ s) :
    HasDerivAt (fun t => energy (X t)) (energy (X s) + 2 * ux (X s) * j s) s := by
  have hx := hasDerivAt_ux h hs
  have hw := hasDerivAt_uw h hs
  refine ((hx.pow 2).add ((hw.pow 2).const_mul 3)).congr_deriv ?_
  simp only [Tail.energy]
  ring

theorem le_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (h' : ∀ t ∈ Icc a b, f' t ≤ 0) : f b ≤ f a := by
  have hmono : AntitoneOn f (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t ht => (h t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) fun t ht => ?_
    · rw [interior_Icc] at ht
      exact (h t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(h t (Ioo_subset_Icc_self ht)).deriv]
      exact h' t (Ioo_subset_Icc_self ht)
  exact hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (h' : ∀ t ∈ Icc a b, 0 ≤ f' t) : f a ≤ f b := by
  have := le_of_hasDerivAt_nonpos (f := fun t => -f t) (f' := fun t => -f' t) hab
    (fun t ht => (h t ht).neg) fun t ht => neg_nonpos.2 (h' t ht)
  linarith

/-- The stable coordinate forgets its initial value at the rate `e^{-(s - S)}`. -/
theorem stab_bound {S M : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (hX : Solves S X j)
    (hj : ∀ s, S ≤ s → |j s| ≤ M) {s : ℝ} (hs : S ≤ s) :
    |stab (X s)| ≤ Real.exp (-(s - S)) * |stab (X S)| + M / 3 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hj S le_rfl)
  have hE : 0 < Real.exp (-(s - S)) := Real.exp_pos _
  have hSs : Real.exp S = Real.exp s * Real.exp (-(s - S)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hes : 0 < Real.exp s := Real.exp_pos s
  have up : Real.exp s * (stab (X s) - M / 3) ≤ Real.exp S * (stab (X S) - M / 3) := by
    refine le_of_hasDerivAt_nonpos
      (f := fun t => Real.exp t * (stab (X t) - M / 3))
      (f' := fun t => Real.exp t * (stab (X t) - M / 3)
        + Real.exp t * (-stab (X t) + j t / 3)) hs
      (fun t ht => (Real.hasDerivAt_exp t).mul ((hasDerivAt_stab hX ht.1).sub_const (M / 3))) fun t ht => ?_
    have e : Real.exp t * (stab (X t) - M / 3) + Real.exp t * (-stab (X t) + j t / 3) =
        Real.exp t * ((j t - M) / 3) := by ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le
      (by linarith [(abs_le.1 (hj t ht.1)).2])
  have low : Real.exp S * (stab (X S) + M / 3) ≤ Real.exp s * (stab (X s) + M / 3) := by
    refine le_of_hasDerivAt_nonneg
      (f := fun t => Real.exp t * (stab (X t) + M / 3))
      (f' := fun t => Real.exp t * (stab (X t) + M / 3)
        + Real.exp t * (-stab (X t) + j t / 3)) hs
      (fun t ht => (Real.hasDerivAt_exp t).mul ((hasDerivAt_stab hX ht.1).add_const (M / 3))) fun t ht => ?_
    have e : Real.exp t * (stab (X t) + M / 3) + Real.exp t * (-stab (X t) + j t / 3) =
        Real.exp t * ((j t + M) / 3) := by ring
    rw [e]
    exact mul_nonneg (Real.exp_pos t).le (by linarith [(abs_le.1 (hj t ht.1)).1])
  rw [hSs, mul_assoc] at up low
  have up' : stab (X s) - M / 3 ≤ Real.exp (-(s - S)) * (stab (X S) - M / 3) :=
    le_of_mul_le_mul_left up hes
  have low' : Real.exp (-(s - S)) * (stab (X S) + M / 3) ≤ stab (X s) + M / 3 :=
    le_of_mul_le_mul_left low hes
  have a1 := mul_le_mul_of_nonneg_left (le_abs_self (stab (X S))) hE.le
  have a2 := mul_le_mul_of_nonneg_left (neg_abs_le (stab (X S))) hE.le
  have a3 := mul_nonneg hE.le hM
  rw [abs_le]
  constructor <;> nlinarith

/-- A bounded solution has unstable energy at most `4 sup |j|²`. -/
theorem energy_bound {S M : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (hX : Solves S X j)
    (hj : ∀ s, S ≤ s → |j s| ≤ M) (hbdd : ∃ B, ∀ s, S ≤ s → energy (X s) ≤ B) {s : ℝ}
    (hs : S ≤ s) : energy (X s) ≤ 4 * M ^ 2 := by
  obtain ⟨B, hB⟩ := hbdd
  have hmono : ∀ t, s ≤ t → Real.exp (-(s / 2)) * (energy (X s) - 4 * M ^ 2) ≤
      Real.exp (-(t / 2)) * (energy (X t) - 4 * M ^ 2) := by
    intro t ht
    refine le_of_hasDerivAt_nonneg
      (f := fun r => Real.exp (-(r / 2)) * (energy (X r) - 4 * M ^ 2))
      (f' := fun r => Real.exp (-(r / 2)) * (-(1 / 2)) * (energy (X r) - 4 * M ^ 2)
        + Real.exp (-(r / 2)) * (energy (X r) + 2 * ux (X r) * j r)) ht
      (fun r hr => ?_) fun r hr => ?_
    · have h1 : HasDerivAt (fun r : ℝ => Real.exp (-(r / 2)))
          (Real.exp (-(r / 2)) * (-(1 / 2))) r :=
        (((hasDerivAt_id r).div_const 2).neg).exp
      exact h1.mul ((hasDerivAt_energy hX (hs.trans hr.1)).sub_const (4 * M ^ 2))
    · have hjr := abs_le.1 (hj r (hs.trans hr.1))
      have hux : ux (X r) ^ 2 ≤ energy (X r) := by
        unfold energy
        nlinarith [sq_nonneg (uw (X r))]
      have key : 0 ≤ energy (X r) / 2 + 2 * M ^ 2 + 2 * ux (X r) * j r := by
        nlinarith [sq_nonneg (ux (X r) + 2 * j r), sq_nonneg (j r), sq_nonneg M,
          mul_nonneg (sub_nonneg.2 hjr.2) (sub_nonneg.2 (neg_le.1 hjr.1))]
      have e : Real.exp (-(r / 2)) * (-(1 / 2)) * (energy (X r) - 4 * M ^ 2)
          + Real.exp (-(r / 2)) * (energy (X r) + 2 * ux (X r) * j r) =
          Real.exp (-(r / 2)) * (energy (X r) / 2 + 2 * M ^ 2 + 2 * ux (X r) * j r) := by ring
      rw [e]
      exact mul_nonneg (Real.exp_pos _).le key
  have hlim : Tendsto (fun t : ℝ => Real.exp (-(t / 2)) * |B - 4 * M ^ 2|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(t / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num))
    simpa using h1.mul_const |B - 4 * M ^ 2|
  have hle : Real.exp (-(s / 2)) * (energy (X s) - 4 * M ^ 2) ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop s] with t ht
    refine (hmono t ht).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    exact (sub_le_sub_right (hB t (hs.trans ht)) _).trans (le_abs_self _)
  have hpos : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  nlinarith

/-- The unstable part of a jet, in terms of its energy. -/
theorem jet_sub_stab_le {X : State} {M : ℝ} (hM : 0 ≤ M) (h : energy X ≤ 4 * M ^ 2) :
    |X.1 - stab X| ≤ 4 / 3 * M ∧ |X.2.1 + stab X| ≤ 4 / 3 * M ∧
      |X.2.2 - stab X| ≤ 4 / 3 * M := by
  have hb : (0 : ℝ) ≤ 4 / 3 * M := by positivity
  unfold energy at h
  refine ⟨abs_le_of_sq_le_sq ?_ hb, abs_le_of_sq_le_sq ?_ hb, abs_le_of_sq_le_sq ?_ hb⟩
  · rw [show X.1 - stab X = uw X - ux X / 3 by rw [fst_eq X]; ring]
    nlinarith [sq_nonneg (ux X + uw X)]
  · rw [show X.2.1 + stab X = ux X / 3 + uw X by rw [snd_eq X]; ring]
    nlinarith [sq_nonneg (ux X - uw X)]
  · rw [show X.2.2 - stab X = 2 * ux X / 3 by rw [thd_eq X]; ring]
    nlinarith [sq_nonneg (uw X)]

/-- **A priori bound.** A bounded solution of `V‴ + V = j` on `[S, ∞)` is
controlled by its stable coordinate at `S` and by `sup |j|`. -/
theorem jet_bound {S M : ℝ} {X : ℝ → State} {j : ℝ → ℝ} (hX : Solves S X j)
    (hj : ∀ s, S ≤ s → |j s| ≤ M) (hbdd : ∃ B, ∀ s, S ≤ s → energy (X s) ≤ B) {s : ℝ}
    (hs : S ≤ s) :
    |(X s).1| ≤ Real.exp (-(s - S)) * |stab (X S)| + 5 / 3 * M ∧
      |(X s).2.1| ≤ Real.exp (-(s - S)) * |stab (X S)| + 5 / 3 * M ∧
      |(X s).2.2| ≤ Real.exp (-(s - S)) * |stab (X S)| + 5 / 3 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hj S le_rfl)
  have hq := stab_bound hX hj hs
  obtain ⟨h1, h2, h3⟩ := jet_sub_stab_le hM (energy_bound hX hj hbdd hs)
  refine ⟨?_, ?_, ?_⟩
  · have := abs_add_le ((X s).1 - stab (X s)) (stab (X s))
    rw [sub_add_cancel] at this
    linarith
  · have := abs_add_le ((X s).2.1 + stab (X s)) (-stab (X s))
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  · have := abs_add_le ((X s).2.2 - stab (X s)) (stab (X s))
    rw [sub_add_cancel] at this
    linarith

end Calabi.Tail
