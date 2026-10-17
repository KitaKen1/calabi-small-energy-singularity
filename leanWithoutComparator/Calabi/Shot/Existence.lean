import Calabi.Shot.Physical
import Calabi.Analysis.GlobalODE

/-!
# Trajectories of the clamped profile system on `[1, 56]`

The clamped field is Lipschitz in the jet, uniformly for `s ≥ 1`, so every
initial jet at `s = 1` and every parameter `d` has a trajectory on `[1, 56]`,
and the trajectory depends Lipschitz-continuously on both.
-/

open Set
open scoped NNReal

namespace Calabi.Shot

theorem pfield_lipschitz (d : ℝ) {s : ℝ} (hs : 1 ≤ s) : LipschitzWith 647 (pfield d s) := by
  refine LipschitzWith.of_dist_le_mul fun X Y => ?_
  obtain ⟨h1, h2, h3⟩ := State.dist_le_iff.1 (le_refl (dist X Y))
  have hr0 : 0 ≤ dist X Y := dist_nonneg
  have hs0 : (0 : ℝ) < s := by linarith
  have hs2 : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs
  have hs3 : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ hs
  have c2 : 21 / s ≤ 21 := by
    rw [div_le_iff₀ hs0]
    linarith
  have c2' : 0 ≤ 21 / s := div_nonneg (by norm_num) hs0.le
  have c1 : 337 / (4 * s ^ 2) ≤ 337 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c1' : 0 ≤ 337 / (4 * s ^ 2) := div_nonneg (by norm_num) (by positivity)
  have c0 : 567 / (4 * s ^ 3) ≤ 567 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c0' : 0 ≤ 567 / (4 * s ^ 3) := div_nonneg (by norm_num) (by positivity)
  have hN := Ntr_lipschitz X.1 Y.1
  have hK : ((647 : ℝ≥0) : ℝ) = 647 := by norm_num
  rw [hK, State.dist_le_iff]
  refine ⟨h2.trans (by linarith), h3.trans (by linarith), ?_⟩
  have e : (pfield d s X).2.2 - (pfield d s Y).2.2 =
      -(21 / s * (X.2.2 - Y.2.2)) - 337 / (4 * s ^ 2) * (X.2.1 - Y.2.1)
        + 567 / (4 * s ^ 3) * (X.1 - Y.1) - (Ntr X.1 - Ntr Y.1) := by
    simp only [pfield]
    ring
  rw [e]
  have b3 : |21 / s * (X.2.2 - Y.2.2)| ≤ 21 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c2']
    exact mul_le_mul c2 h3 (abs_nonneg _) (by norm_num)
  have b2 : |337 / (4 * s ^ 2) * (X.2.1 - Y.2.1)| ≤ 337 / 4 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c1']
    exact mul_le_mul c1 h2 (abs_nonneg _) (by norm_num)
  have b1 : |567 / (4 * s ^ 3) * (X.1 - Y.1)| ≤ 567 / 4 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c0']
    exact mul_le_mul c0 h1 (abs_nonneg _) (by norm_num)
  have bN : |Ntr X.1 - Ntr Y.1| ≤ 400 * dist X Y := hN.trans (by linarith)
  obtain ⟨b3l, b3u⟩ := abs_le.1 b3
  obtain ⟨b2l, b2u⟩ := abs_le.1 b2
  obtain ⟨b1l, b1u⟩ := abs_le.1 b1
  obtain ⟨bNl, bNu⟩ := abs_le.1 bN
  rw [abs_le]
  constructor <;> linarith

theorem pfield_continuousOn (d : ℝ) (X : State) :
    ContinuousOn (fun s => pfield d s X) (Icc 1 56) := by
  have hpos : ∀ s ∈ Icc (1 : ℝ) 56, (0 : ℝ) < s := fun s hs => by linarith [hs.1]
  have h1 : ContinuousOn (fun s : ℝ => 21 / s) (Icc 1 56) :=
    continuousOn_const.div continuousOn_id fun s hs => (hpos s hs).ne'
  have h2 : ContinuousOn (fun s : ℝ => 337 / (4 * s ^ 2)) (Icc 1 56) :=
    continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun s hs => by
      have := hpos s hs
      positivity
  have h3 : ContinuousOn (fun s : ℝ => 567 / (4 * s ^ 3)) (Icc 1 56) :=
    continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 3)) fun s hs => by
      have := hpos s hs
      positivity
  show ContinuousOn (fun s : ℝ => ((X.2.1, X.2.2,
    -(21 / s) * X.2.2 - 337 / (4 * s ^ 2) * X.2.1 + 567 / (4 * s ^ 3) * (X.1 - d) - Ntr X.1) :
      State)) (Icc 1 56)
  exact continuousOn_const.prodMk (continuousOn_const.prodMk
    ((((h1.neg.mul continuousOn_const).sub (h2.mul continuousOn_const)).add
      (h3.mul continuousOn_const)).sub continuousOn_const))

/-- Every initial jet has a trajectory on `[1, 56]`. -/
theorem exists_trajectory (d : ℝ) (J : State) :
    ∃ Y : ℝ → State, Y 1 = J ∧
      ∀ s ∈ Icc (1 : ℝ) 56, HasDerivWithinAt Y (pfield d s (Y s)) (Icc 1 56) s :=
  exists_solution_Icc (f := pfield d) (K := 647) (by norm_num)
    (fun _ hs => pfield_lipschitz d hs.1) (pfield_continuousOn d) J

theorem solvesOn_of_hasDerivWithinAt {d : ℝ} {Y : ℝ → State}
    (h : ∀ s ∈ Icc (1 : ℝ) 56, HasDerivWithinAt Y (pfield d s (Y s)) (Icc 1 56) s) :
    SolvesOn d 1 56 Y :=
  ⟨fun s hs => (h s hs).continuousWithinAt, fun s hs =>
    (h s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)⟩

/-- Lipschitz dependence of a trajectory on the initial jet and on `d`. -/
theorem trajectory_dist_le {d₁ d₂ : ℝ} {Y₁ Y₂ : ℝ → State} (h₁ : SolvesOn d₁ 1 56 Y₁)
    (h₂ : SolvesOn d₂ 1 56 Y₂) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 56) :
    dist (Y₁ s) (Y₂ s) ≤ (dist (Y₁ 1) (Y₂ 1) + |d₁ - d₂|) * Real.exp (647 * 55) := by
  have hbound : ∀ t ∈ Ico (1 : ℝ) 56,
      dist (pfield d₂ t (Y₂ t)) (pfield d₁ t (Y₂ t)) ≤ 567 / 4 * |d₁ - d₂| := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht.1
    have c0 : 567 / (4 * t ^ 3) ≤ 567 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have c0' : 0 ≤ 567 / (4 * t ^ 3) := div_nonneg (by norm_num) (by positivity)
    have hnn : 0 ≤ 567 / 4 * |d₁ - d₂| := by positivity
    rw [State.dist_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp only [pfield, sub_self, abs_zero]
      exact hnn
    · simp only [pfield, sub_self, abs_zero]
      exact hnn
    · have e : (pfield d₂ t (Y₂ t)).2.2 - (pfield d₁ t (Y₂ t)).2.2 =
          567 / (4 * t ^ 3) * (d₁ - d₂) := by
        simp only [pfield]
        ring
      rw [e, abs_mul, abs_of_nonneg c0']
      exact mul_le_mul_of_nonneg_right c0 (abs_nonneg _)
  have hexact : ∀ t ∈ Ico (1 : ℝ) 56,
      dist (pfield d₁ t (Y₁ t)) (pfield d₁ t (Y₁ t)) ≤ (0 : ℝ) := fun t _ => by
    rw [dist_self]
  have h := dist_le_of_approx_trajectories_ODE_of_mem (s := fun _ => Set.univ) (K := 647)
    (fun t ht => (pfield_lipschitz d₁ ht.1).lipschitzOnWith) h₁.1 h₁.2 hexact
    (fun _ _ => Set.mem_univ _) h₂.1 h₂.2 hbound (fun _ _ => Set.mem_univ _)
    (le_refl (dist (Y₁ 1) (Y₂ 1)))
  have hb := h s hs
  have hK : ((647 : ℝ≥0) : ℝ) = 647 := by norm_num
  rw [zero_add, hK, gronwallBound_of_K_ne_0 (by norm_num : (647 : ℝ) ≠ 0)] at hb
  have hx0 : 0 ≤ 647 * (s - 1) := mul_nonneg (by norm_num) (by linarith [hs.1])
  have h1e : 1 ≤ Real.exp (647 * (s - 1)) := Real.one_le_exp hx0
  have hexp : Real.exp (647 * (s - 1)) ≤ Real.exp (647 * 55) :=
    Real.exp_le_exp.2 (by linarith [hs.2])
  have hδ : 0 ≤ dist (Y₁ 1) (Y₂ 1) := dist_nonneg
  have hΔ : 0 ≤ |d₁ - d₂| := abs_nonneg _
  have p1 := mul_nonneg hδ (sub_nonneg.2 hexp)
  have p2 := mul_nonneg hΔ (sub_nonneg.2 hexp)
  have p3 := mul_nonneg hΔ (sub_nonneg.2 h1e)
  nlinarith

/-- A trajectory with the given initial jet, chosen once and for all. -/
noncomputable def traj (d : ℝ) (J : State) : ℝ → State :=
  Classical.choose (exists_trajectory d J)

theorem traj_one (d : ℝ) (J : State) : traj d J 1 = J :=
  (Classical.choose_spec (exists_trajectory d J)).1

theorem traj_hasDerivWithinAt (d : ℝ) (J : State) :
    ∀ s ∈ Icc (1 : ℝ) 56,
      HasDerivWithinAt (traj d J) (pfield d s (traj d J s)) (Icc 1 56) s :=
  (Classical.choose_spec (exists_trajectory d J)).2

theorem traj_solves (d : ℝ) (J : State) : SolvesOn d 1 56 (traj d J) :=
  solvesOn_of_hasDerivWithinAt (traj_hasDerivWithinAt d J)

theorem traj_dist_le (d₁ d₂ : ℝ) (J₁ J₂ : State) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 56) :
    dist (traj d₁ J₁ s) (traj d₂ J₂ s) ≤
      (dist J₁ J₂ + |d₁ - d₂|) * Real.exp (647 * 55) := by
  have h := trajectory_dist_le (traj_solves d₁ J₁) (traj_solves d₂ J₂) hs
  rwa [traj_one, traj_one] at h

end Calabi.Shot
