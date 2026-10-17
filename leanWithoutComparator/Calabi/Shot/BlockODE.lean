import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Comparison of a true trajectory with an approximate one on a block

On a block the profile equation is written for `X = (p, p', p'')` in the
block variable `t ∈ [-1, 1]`, with `σ = A + t ≥ 128`, `H ≥ 16` and a parameter `d`:

  `p‴ = -(21/σ) p″ - (337/(4σ²)) p′ + (567/(4σ³)) (p - d) - N(p) / H³`.

The nonlinearity `N(p) = p / (1 + p)` is replaced by `Ntr`, which clamps `p`
below at `-19/20`. The clamped field is Lipschitz with constant one on the
whole space, so Grönwall's inequality needs no tube. A function whose defect is
at most `ε` stays within `8 ε` of the true trajectory with the same data at
`t = -1`; when that function stays above `-19/20`, so does the trajectory, and
the clamp is inactive.
-/

open Set
open scoped NNReal

namespace Calabi.Shot

/-- `p / (1 + p)` with `p` clamped below at `-19/20`. -/
noncomputable def Ntr (p : ℝ) : ℝ := max p (-19 / 20) / (1 + max p (-19 / 20))

theorem Ntr_of_ge {p : ℝ} (h : -19 / 20 ≤ p) : Ntr p = p / (1 + p) := by
  unfold Ntr
  rw [max_eq_left h]

theorem Ntr_lipschitz (p q : ℝ) : |Ntr p - Ntr q| ≤ 400 * |p - q| := by
  have hu : (1 : ℝ) / 20 ≤ 1 + max p (-19 / 20) := by
    have := le_max_right p (-19 / 20 : ℝ)
    linarith
  have hv : (1 : ℝ) / 20 ≤ 1 + max q (-19 / 20) := by
    have := le_max_right q (-19 / 20 : ℝ)
    linarith
  have hu0 : 0 < 1 + max p (-19 / 20) := by linarith
  have hv0 : 0 < 1 + max q (-19 / 20) := by linarith
  have hm := abs_max_sub_max_le_abs p q (-19 / 20 : ℝ)
  have key : Ntr p - Ntr q =
      (max p (-19 / 20) - max q (-19 / 20)) /
        ((1 + max p (-19 / 20)) * (1 + max q (-19 / 20))) := by
    unfold Ntr
    rw [div_sub_div _ _ hu0.ne' hv0.ne']
    congr 1
    ring
  have hprod : (1 : ℝ) / 400 ≤ (1 + max p (-19 / 20)) * (1 + max q (-19 / 20)) := by
    calc (1 : ℝ) / 400 = 1 / 20 * (1 / 20) := by norm_num
      _ ≤ (1 + max p (-19 / 20)) * (1 + max q (-19 / 20)) :=
          mul_le_mul hu hv (by norm_num) hu0.le
  rw [key, abs_div, abs_of_pos (mul_pos hu0 hv0), div_le_iff₀ (mul_pos hu0 hv0)]
  calc |max p (-19 / 20) - max q (-19 / 20)| ≤ |p - q| := hm
    _ = 400 * |p - q| * (1 / 400) := by ring
    _ ≤ 400 * |p - q| * ((1 + max p (-19 / 20)) * (1 + max q (-19 / 20))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- `(p, p', p'')` in the block variable. -/
abbrev State := ℝ × ℝ × ℝ

theorem State.dist_le_iff {X Y : State} {r : ℝ} :
    dist X Y ≤ r ↔ |X.1 - Y.1| ≤ r ∧ |X.2.1 - Y.2.1| ≤ r ∧ |X.2.2 - Y.2.2| ≤ r := by
  simp only [Prod.dist_eq, Real.dist_eq, max_le_iff]

/-- The block system with the clamped nonlinearity and parameter `d`. -/
noncomputable def field (H A d : ℝ) (t : ℝ) (X : State) : State :=
  (X.2.1, X.2.2,
    -(21 / (A + t)) * X.2.2 - 337 / (4 * (A + t) ^ 2) * X.2.1
      + 567 / (4 * (A + t) ^ 3) * (X.1 - d) - Ntr X.1 / H ^ 3)

theorem field_lipschitz {H A t : ℝ} (d : ℝ) (hH : 16 ≤ H) (hA : 129 ≤ A) (ht : -1 ≤ t) :
    LipschitzWith 1 (field H A d t) := by
  apply LipschitzWith.mk_one
  intro X Y
  obtain ⟨h1, h2, h3⟩ := State.dist_le_iff.1 (le_refl (dist X Y))
  have hr0 : 0 ≤ dist X Y := dist_nonneg
  have hσ : (128 : ℝ) ≤ A + t := by linarith
  have hσ0 : (0 : ℝ) < A + t := by linarith
  have hσ2 : (16384 : ℝ) ≤ (A + t) ^ 2 := by
    have := mul_le_mul hσ hσ (by norm_num) hσ0.le
    nlinarith
  have hσ3 : (2097152 : ℝ) ≤ (A + t) ^ 3 := by
    calc (2097152 : ℝ) = 16384 * 128 := by norm_num
      _ ≤ (A + t) ^ 2 * (A + t) := mul_le_mul hσ2 hσ (by norm_num) (by positivity)
      _ = (A + t) ^ 3 := by ring
  have hH0 : (0 : ℝ) < H := by linarith
  have hH2 : (256 : ℝ) ≤ H ^ 2 := by
    have := mul_le_mul hH hH (by norm_num) hH0.le
    nlinarith
  have hH3 : (4096 : ℝ) ≤ H ^ 3 := by
    calc (4096 : ℝ) = 256 * 16 := by norm_num
      _ ≤ H ^ 2 * H := mul_le_mul hH2 hH (by norm_num) (by positivity)
      _ = H ^ 3 := by ring
  have hH3pos : (0 : ℝ) < H ^ 3 := pow_pos hH0 3
  have c2 : 21 / (A + t) ≤ 21 / 128 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hσ
  have c2' : 0 ≤ 21 / (A + t) := div_nonneg (by norm_num) hσ0.le
  have c1 : 337 / (4 * (A + t) ^ 2) ≤ 337 / 65536 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c1' : 0 ≤ 337 / (4 * (A + t) ^ 2) := div_nonneg (by norm_num) (by positivity)
  have c0 : 567 / (4 * (A + t) ^ 3) ≤ 567 / 8388608 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c0' : 0 ≤ 567 / (4 * (A + t) ^ 3) :=
    div_nonneg (by norm_num) (by have := pow_pos hσ0 3; linarith)
  have hN := Ntr_lipschitz X.1 Y.1
  rw [State.dist_le_iff]
  refine ⟨h2, h3, ?_⟩
  · have e : (field H A d t X).2.2 - (field H A d t Y).2.2 =
        -(21 / (A + t) * (X.2.2 - Y.2.2)) - 337 / (4 * (A + t) ^ 2) * (X.2.1 - Y.2.1)
          + 567 / (4 * (A + t) ^ 3) * (X.1 - Y.1)
          - (Ntr X.1 - Ntr Y.1) / H ^ 3 := by
      simp only [field]
      ring
    rw [e]
    have b3 : |21 / (A + t) * (X.2.2 - Y.2.2)| ≤ 21 / 128 * dist X Y := by
      rw [abs_mul, abs_of_nonneg c2']
      exact mul_le_mul c2 h3 (abs_nonneg _) (by norm_num)
    have b2 : |337 / (4 * (A + t) ^ 2) * (X.2.1 - Y.2.1)| ≤ 337 / 65536 * dist X Y := by
      rw [abs_mul, abs_of_nonneg c1']
      exact mul_le_mul c1 h2 (abs_nonneg _) (by norm_num)
    have b1 : |567 / (4 * (A + t) ^ 3) * (X.1 - Y.1)| ≤ 567 / 8388608 * dist X Y := by
      rw [abs_mul, abs_of_nonneg c0']
      exact mul_le_mul c0 h1 (abs_nonneg _) (by norm_num)
    have bN : |(Ntr X.1 - Ntr Y.1) / H ^ 3| ≤ 400 / 4096 * dist X Y := by
      rw [abs_div, abs_of_pos hH3pos, div_le_iff₀ hH3pos]
      calc |Ntr X.1 - Ntr Y.1| ≤ 400 * |X.1 - Y.1| := hN
        _ ≤ 400 * dist X Y := by linarith
        _ = 400 / 4096 * dist X Y * 4096 := by ring
        _ ≤ 400 / 4096 * dist X Y * H ^ 3 :=
            mul_le_mul_of_nonneg_left hH3 (by positivity)
    obtain ⟨b3l, b3u⟩ := abs_le.1 b3
    obtain ⟨b2l, b2u⟩ := abs_le.1 b2
    obtain ⟨b1l, b1u⟩ := abs_le.1 b1
    obtain ⟨bNl, bNu⟩ := abs_le.1 bN
    rw [abs_le]
    constructor <;> linarith

/-- Grönwall's bound with constant one over a time span of at most two. -/
theorem gronwallBound_one_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : x ≤ 2) :
    gronwallBound 0 ((1 : ℝ≥0) : ℝ) ε x ≤ 8 * ε := by
  have hK : (1 : ℝ) ≠ 0 := one_ne_zero
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp x ≤ Real.exp 2 := Real.exp_le_exp.2 hx
  have h4 : Real.exp x ≤ 9 := by
    have := mul_lt_mul'' h1 h1 hp.le hp.le
    linarith
  have h5 := mul_nonneg hε (sub_nonneg.2 h4)
  rw [NNReal.coe_one, gronwallBound_of_K_ne_0 hK]
  simp only [zero_mul, zero_add, one_mul, div_one]
  linarith

/-- The defect of a function in the block equation with the clamped
nonlinearity. -/
noncomputable def defectTr (H A d : ℝ) (q q1 q2 q3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  q3 t + 21 / (A + t) * q2 t + 337 / (4 * (A + t) ^ 2) * q1 t
    - 567 / (4 * (A + t) ^ 3) * (q t - d) + Ntr (q t) / H ^ 3

/-- **Block comparison.** A function with defect at most `ε` stays within
`8 ε` of the trajectory of the clamped system that has the same data at
`t = -1`. -/
theorem block_compare {H A d ε : ℝ} (hH : 16 ≤ H) (hA : 129 ≤ A)
    {q q1 q2 q3 : ℝ → ℝ}
    (hq : ∀ t, HasDerivAt q (q1 t) t) (hq1 : ∀ t, HasDerivAt q1 (q2 t) t)
    (hq2 : ∀ t, HasDerivAt q2 (q3 t) t)
    (hdef : ∀ t ∈ Ico (-1 : ℝ) 1, |defectTr H A d q q1 q2 q3 t| ≤ ε)
    {X : ℝ → State} (hX : ContinuousOn X (Icc (-1) 1))
    (hX' : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt X (field H A d t (X t)) (Ici t) t)
    (h0 : X (-1) = (q (-1), q1 (-1), q2 (-1))) :
    ∀ t ∈ Icc (-1 : ℝ) 1, dist ((q t, q1 t, q2 t) : State) (X t) ≤ 8 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hdef (-1) ⟨le_refl _, by norm_num⟩)
  have hY : ∀ t, HasDerivAt (fun t => ((q t, q1 t, q2 t) : State))
      ((q1 t, q2 t, q3 t) : State) t := fun t =>
    (hq t).prodMk ((hq1 t).prodMk (hq2 t))
  have hYc : ContinuousOn (fun t => ((q t, q1 t, q2 t) : State)) (Icc (-1) 1) :=
    fun t _ => (hY t).continuousAt.continuousWithinAt
  have hbound : ∀ t ∈ Ico (-1 : ℝ) 1,
      dist ((q1 t, q2 t, q3 t) : State) (field H A d t (q t, q1 t, q2 t)) ≤ ε := by
    intro t ht
    have hd := hdef t ht
    have key : ((q1 t, q2 t, q3 t) : State).2.2 - (field H A d t (q t, q1 t, q2 t)).2.2 =
        defectTr H A d q q1 q2 q3 t := by
      simp only [field, defectTr]
      ring
    rw [State.dist_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp only [field, sub_self, abs_zero]
      exact hε
    · simp only [field, sub_self, abs_zero]
      exact hε
    · rw [key]
      exact hd
  have hexact : ∀ t ∈ Ico (-1 : ℝ) 1,
      dist (field H A d t (X t)) (field H A d t (X t)) ≤ (0 : ℝ) := fun t _ => by
    rw [dist_self]
  have hinit : dist ((q (-1), q1 (-1), q2 (-1)) : State) (X (-1)) ≤ (0 : ℝ) := by
    rw [h0, dist_self]
  have h := dist_le_of_approx_trajectories_ODE_of_mem (s := fun _ => Set.univ) (K := 1)
    (fun t ht => (field_lipschitz d hH hA ht.1).lipschitzOnWith) hYc
    (fun t _ => (hY t).hasDerivWithinAt) hbound (fun _ _ => Set.mem_univ _) hX hX' hexact
    (fun _ _ => Set.mem_univ _) hinit
  intro t ht
  have hb := h t ht
  rw [add_zero] at hb
  exact hb.trans (gronwallBound_one_le hε (by linarith [ht.2]))

end Calabi.Shot
