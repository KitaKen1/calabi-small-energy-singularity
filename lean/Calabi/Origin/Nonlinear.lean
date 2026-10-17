import Calabi.Origin.Linear
import Calabi.Tail.Nonlinear

/-!
# The regular solution at the origin

For parameters `k`, `d` the regular solution of the profile equation in the
variable `r = s^{3/2}` is the fixed point of

  `P(r) = d + k r - (8/27) r² K0 (N ∘ P) r`,   `N(p) = p / (1 + p)`,

on `|r| ≤ 1`. With `N` clamped at `p ≥ -1/2` this is a contraction with
constant `100/1701` in the uniform norm (`osol`). `compare` bounds the distance
from `osol` to any function that satisfies the same equation up to a defect:
an approximate polynomial solution, or the solution for other parameters.
-/

open Set
open scoped BoundedContinuousFunction NNReal

namespace Calabi.Origin

/-- `p / (1 + p)` clamped at `p ≥ -1/2`. -/
noncomputable def Nor (p : ℝ) : ℝ := max p (-(1 / 2)) / (1 + max p (-(1 / 2)))

theorem Nor_of_ge {p : ℝ} (h : -(1 / 2) ≤ p) : Nor p = p / (1 + p) := by
  unfold Nor
  rw [max_eq_left h]

theorem Nor_lipschitz (p q : ℝ) : |Nor p - Nor q| ≤ 4 * |p - q| := by
  have hu : (1 : ℝ) / 2 ≤ 1 + max p (-(1 / 2)) := by
    have := le_max_right p (-(1 / 2) : ℝ)
    linarith
  have hv : (1 : ℝ) / 2 ≤ 1 + max q (-(1 / 2)) := by
    have := le_max_right q (-(1 / 2) : ℝ)
    linarith
  have hu0 : 0 < 1 + max p (-(1 / 2)) := by linarith
  have hv0 : 0 < 1 + max q (-(1 / 2)) := by linarith
  have hm := abs_max_sub_max_le_abs p q (-(1 / 2) : ℝ)
  have key : Nor p - Nor q = (max p (-(1 / 2)) - max q (-(1 / 2))) /
      ((1 + max p (-(1 / 2))) * (1 + max q (-(1 / 2)))) := by
    unfold Nor
    field_simp
    ring
  have hden : (1 : ℝ) / 4 ≤ (1 + max p (-(1 / 2))) * (1 + max q (-(1 / 2))) := by nlinarith
  rw [key, abs_div, abs_of_pos (mul_pos hu0 hv0), div_le_iff₀ (mul_pos hu0 hv0)]
  have h0 : 0 ≤ |p - q| := abs_nonneg _
  nlinarith

theorem abs_Nor_le (p : ℝ) : |Nor p| ≤ 1 := by
  have hu : -(1 / 2 : ℝ) ≤ max p (-(1 / 2)) := le_max_right _ _
  have hu0 : 0 < 1 + max p (-(1 / 2)) := by linarith
  unfold Nor
  rw [abs_div, abs_of_pos hu0, div_le_one hu0, abs_le]
  constructor <;> linarith

theorem continuous_Nor : Continuous Nor := by
  have hc : Continuous fun p : ℝ => max p (-(1 / 2)) := continuous_id.max continuous_const
  exact hc.div (continuous_const.add hc) fun p => by
    have := le_max_right p (-(1 / 2) : ℝ)
    linarith

/-- The clamp to `[-1, 1]`. -/
noncomputable def cl (r : ℝ) : ℝ := max (-1) (min r 1)

theorem abs_cl_le (r : ℝ) : |cl r| ≤ 1 :=
  abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem cl_of_abs_le {r : ℝ} (h : |r| ≤ 1) : cl r = r := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold cl
  rw [min_eq_left h2, max_eq_right h1]

theorem continuous_cl : Continuous cl := continuous_const.max (continuous_id.min continuous_const)

theorem abs_mul_le_one {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hr : |r| ≤ 1) : |t * r| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ht.1]
  exact mul_le_one₀ ht.2 (abs_nonneg _) hr

theorem sq_le_one_of_abs_le {r : ℝ} (hr : |r| ≤ 1) : r ^ 2 ≤ 1 := by
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) hr

/-- The right-hand side of the fixed-point equation, for a given `g = N ∘ P`. -/
noncomputable def psiFun (k d : ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  d + k * cl r - 8 / 27 * cl r ^ 2 * K0 g (cl r)

theorem continuous_psiFun (k d : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (psiFun k d g) :=
  (continuous_const.add (continuous_const.mul continuous_cl)).sub
    ((continuous_const.mul (continuous_cl.pow 2)).mul ((continuous_K hg).1.comp continuous_cl))

theorem abs_psiFun_le (k d : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) (r : ℝ) :
    |psiFun k d g r| ≤ |d| + |k| + 1 := by
  have hK := (abs_K_le hg (M := 1) (r := cl r) fun t _ => hb _).1
  have hc := abs_cl_le r
  have hc2 := sq_le_one_of_abs_le hc
  have h1 : |k * cl r| ≤ |k| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hc
  have h2 : |8 / 27 * cl r ^ 2 * K0 g (cl r)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 27),
      abs_of_nonneg (sq_nonneg _)]
    have := abs_nonneg (K0 g (cl r))
    nlinarith [sq_nonneg (cl r)]
  unfold psiFun
  have t1 := abs_sub (d + k * cl r) (8 / 27 * cl r ^ 2 * K0 g (cl r))
  have t2 := abs_add_le d (k * cl r)
  linarith

/-- The fixed-point map on bounded continuous functions. -/
noncomputable def Psi (k d : ℝ) (P : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (psiFun k d fun x => Nor (P x))
    (continuous_psiFun k d (continuous_Nor.comp P.continuous)) (|d| + |k| + 1) fun r => by
      rw [Real.norm_eq_abs]
      exact abs_psiFun_le k d (continuous_Nor.comp P.continuous) (fun x => abs_Nor_le _) r

theorem Psi_apply (k d : ℝ) (P : ℝ →ᵇ ℝ) (r : ℝ) :
    Psi k d P r = psiFun k d (fun x => Nor (P x)) r := rfl

theorem Psi_contracting (k d : ℝ) : ContractingWith (100 / 1701 : ℝ).toNNReal (Psi k d) := by
  refine ⟨Real.toNNReal_lt_one.2 (by norm_num), LipschitzWith.of_dist_le_mul fun P P' => ?_⟩
  rw [Real.coe_toNNReal _ (by norm_num),
    BoundedContinuousFunction.dist_le (mul_nonneg (by norm_num) dist_nonneg)]
  intro r
  have hg : Continuous fun x => Nor (P x) := continuous_Nor.comp P.continuous
  have hg' : Continuous fun x => Nor (P' x) := continuous_Nor.comp P'.continuous
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, |Nor (P (t * cl r)) - Nor (P' (t * cl r))| ≤ 4 * dist P P' := by
    intro t _
    refine (Nor_lipschitz _ _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist _
  have hsub : Continuous fun x => Nor (P x) - Nor (P' x) := hg.sub hg'
  have hK := (abs_K_le hsub hM).1
  rw [← (K_sub hg hg' (cl r)).1] at hK
  have hc2 := sq_le_one_of_abs_le (abs_cl_le r)
  have e : psiFun k d (fun x => Nor (P x)) r - psiFun k d (fun x => Nor (P' x)) r =
      -(8 / 27 * cl r ^ 2 * (K0 (fun x => Nor (P x)) (cl r) - K0 (fun x => Nor (P' x)) (cl r))) := by
    unfold psiFun
    ring
  rw [Psi_apply, Psi_apply, Real.dist_eq, e, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 27), abs_of_nonneg (sq_nonneg _)]
  have h0 := abs_nonneg (K0 (fun x => Nor (P x)) (cl r) - K0 (fun x => Nor (P' x)) (cl r))
  have hd : 0 ≤ dist P P' := dist_nonneg
  nlinarith [sq_nonneg (cl r)]

/-- **The regular solution** for the parameters `k`, `d`, on `|r| ≤ 1`. -/
noncomputable def osol (k d : ℝ) : ℝ →ᵇ ℝ :=
  ContractingWith.fixedPoint (Psi k d) (Psi_contracting k d)

theorem osol_fixed (k d : ℝ) : Psi k d (osol k d) = osol k d :=
  (Psi_contracting k d).fixedPoint_isFixedPt

theorem continuous_Nor_osol (k d : ℝ) : Continuous fun x => Nor (osol k d x) :=
  continuous_Nor.comp (osol k d).continuous

theorem osol_eq (k d : ℝ) {r : ℝ} (hr : |r| ≤ 1) :
    osol k d r = d + k * r - 8 / 27 * r ^ 2 * K0 (fun x => Nor (osol k d x)) r := by
  have h : osol k d r = Psi k d (osol k d) r := by rw [osol_fixed]
  rw [h, Psi_apply]
  unfold psiFun
  rw [cl_of_abs_le hr]

/-- `D P = r P′` of the regular solution, defined by the integral formula. -/
noncomputable def osol1 (k d r : ℝ) : ℝ :=
  k * r - 8 / 27 * r ^ 2 * K1 (fun x => Nor (osol k d x)) r

/-- `D² P` of the regular solution, defined by the integral formula. -/
noncomputable def osol2 (k d r : ℝ) : ℝ :=
  k * r - 8 / 27 * r ^ 2 * K2 (fun x => Nor (osol k d x)) r

/-- **Comparison.** If `Q` satisfies the fixed-point equation for the
parameters `k′`, `d′` with a source `h` that differs from `N ∘ Q` by at most
`δ`, then `Q` and its `D`-derivatives are close to the regular solution for
`k`, `d`. -/
theorem compare (k d : ℝ) {k' d' δ : ℝ} {Q h : ℝ → ℝ} (hQ : Continuous Q) (hh : Continuous h)
    (hQeq : ∀ r, |r| ≤ 1 → Q r = d' + k' * r - 8 / 27 * r ^ 2 * K0 h r)
    (hδ : ∀ x, |x| ≤ 1 → |Nor (Q x) - h x| ≤ δ) :
    (∀ r, |r| ≤ 1 →
        |osol k d r - Q r| ≤ (|d - d'| + |k - k'| + 25 / 1701 * δ) / (1601 / 1701)) ∧
      (∀ r, |r| ≤ 1 → |osol1 k d r - (k' * r - 8 / 27 * r ^ 2 * K1 h r)| ≤
        |k - k'| + 16 / 243 *
          (4 * ((|d - d'| + |k - k'| + 25 / 1701 * δ) / (1601 / 1701)) + δ)) ∧
      ∀ r, |r| ≤ 1 → |osol2 k d r - (k' * r - 8 / 27 * r ^ 2 * K2 h r)| ≤
        |k - k'| + 676 / 1701 *
          (4 * ((|d - d'| + |k - k'| + 25 / 1701 * δ) / (1601 / 1701)) + δ) := by
  have hg := continuous_Nor_osol k d
  -- the source difference on a segment, given a bound for the difference of the solutions
  have hsrc : ∀ B : ℝ, (∀ x, |x| ≤ 1 → |osol k d x - Q x| ≤ B) → ∀ r, |r| ≤ 1 →
      ∀ t ∈ Icc (0 : ℝ) 1, |Nor (osol k d (t * r)) - h (t * r)| ≤ 4 * B + δ := by
    intro B hB r hr t ht
    have hx := abs_mul_le_one ht hr
    have t1 := Nor_lipschitz (osol k d (t * r)) (Q (t * r))
    have t2 := hδ (t * r) hx
    have t3 := hB (t * r) hx
    have t4 := abs_add_le (Nor (osol k d (t * r)) - Nor (Q (t * r))) (Nor (Q (t * r)) - h (t * r))
    rw [sub_add_sub_cancel] at t4
    linarith
  have hKb : ∀ B : ℝ, (∀ x, |x| ≤ 1 → |osol k d x - Q x| ≤ B) → ∀ r, |r| ≤ 1 →
      |K0 (fun x => Nor (osol k d x)) r - K0 h r| ≤ 25 / 504 * (4 * B + δ) ∧
      |K1 (fun x => Nor (osol k d x)) r - K1 h r| ≤ 2 / 9 * (4 * B + δ) ∧
      |K2 (fun x => Nor (osol k d x)) r - K2 h r| ≤ 169 / 126 * (4 * B + δ) := by
    intro B hB r hr
    obtain ⟨s0, s1, s2⟩ := K_sub hg hh r
    rw [s0, s1, s2]
    exact abs_K_le (hg.sub hh) (hsrc B hB r hr)
  -- an initial bound
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hQ.continuousOn (s := Icc (-1) 1))
  have h0 : ∀ r, |r| ≤ 1 → |osol k d r - Q r| ≤ ‖osol k d‖ + C := by
    intro r hr
    have t1 := abs_sub (osol k d r) (Q r)
    have t2 : |osol k d r| ≤ ‖osol k d‖ := by
      rw [← Real.norm_eq_abs]
      exact (osol k d).norm_coe_le_norm r
    have t3 : |Q r| ≤ C := by
      rw [← Real.norm_eq_abs]
      exact hC r (abs_le.1 hr)
    linarith
  have hstep : ∀ B : ℝ, (∀ r, |r| ≤ 1 → |osol k d r - Q r| ≤ B) → ∀ r, |r| ≤ 1 →
      |osol k d r - Q r| ≤ |d - d'| + |k - k'| + 25 / 1701 * δ + 100 / 1701 * B := by
    intro B hB r hr
    have hK := (hKb B hB r hr).1
    have hr2 := sq_le_one_of_abs_le hr
    have e : osol k d r - Q r = (d - d') + (k - k') * r
        - 8 / 27 * r ^ 2 * (K0 (fun x => Nor (osol k d x)) r - K0 h r) := by
      rw [osol_eq k d hr, hQeq r hr]
      ring
    rw [e]
    have a1 : |(k - k') * r| ≤ |k - k'| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hr
    have a2 : |8 / 27 * r ^ 2 * (K0 (fun x => Nor (osol k d x)) r - K0 h r)| ≤
        8 / 27 * (25 / 504 * (4 * B + δ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 27),
        abs_of_nonneg (sq_nonneg _)]
      have := abs_nonneg (K0 (fun x => Nor (osol k d x)) r - K0 h r)
      nlinarith [sq_nonneg r]
    have t1 := abs_sub ((d - d') + (k - k') * r)
      (8 / 27 * r ^ 2 * (K0 (fun x => Nor (osol k d x)) r - K0 h r))
    have t2 := abs_add_le (d - d') ((k - k') * r)
    linarith
  have hfin := Calabi.Tail.le_of_le_add_mul (p := fun r : ℝ => |r| ≤ 1)
    (f := fun r => |osol k d r - Q r|) (c := |d - d'| + |k - k'| + 25 / 1701 * δ)
    (θ := 100 / 1701) (B₀ := ‖osol k d‖ + C) (by norm_num) (by norm_num) h0 hstep
  have hθ : (1 : ℝ) - 100 / 1701 = 1601 / 1701 := by norm_num
  rw [hθ] at hfin
  refine ⟨hfin, fun r hr => ?_, fun r hr => ?_⟩
  · have hK := (hKb _ hfin r hr).2.1
    have hr2 := sq_le_one_of_abs_le hr
    have e : osol1 k d r - (k' * r - 8 / 27 * r ^ 2 * K1 h r) = (k - k') * r
        - 8 / 27 * r ^ 2 * (K1 (fun x => Nor (osol k d x)) r - K1 h r) := by
      unfold osol1
      ring
    rw [e]
    have a1 : |(k - k') * r| ≤ |k - k'| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hr
    have a2 : |8 / 27 * r ^ 2 * (K1 (fun x => Nor (osol k d x)) r - K1 h r)| ≤ 8 / 27 *
        (2 / 9 * (4 * ((|d - d'| + |k - k'| + 25 / 1701 * δ) / (1601 / 1701)) + δ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 27),
        abs_of_nonneg (sq_nonneg _)]
      have := abs_nonneg (K1 (fun x => Nor (osol k d x)) r - K1 h r)
      nlinarith [sq_nonneg r]
    have t1 := abs_sub ((k - k') * r)
      (8 / 27 * r ^ 2 * (K1 (fun x => Nor (osol k d x)) r - K1 h r))
    linarith
  · have hK := (hKb _ hfin r hr).2.2
    have hr2 := sq_le_one_of_abs_le hr
    have e : osol2 k d r - (k' * r - 8 / 27 * r ^ 2 * K2 h r) = (k - k') * r
        - 8 / 27 * r ^ 2 * (K2 (fun x => Nor (osol k d x)) r - K2 h r) := by
      unfold osol2
      ring
    rw [e]
    have a1 : |(k - k') * r| ≤ |k - k'| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hr
    have a2 : |8 / 27 * r ^ 2 * (K2 (fun x => Nor (osol k d x)) r - K2 h r)| ≤ 8 / 27 *
        (169 / 126 * (4 * ((|d - d'| + |k - k'| + 25 / 1701 * δ) / (1601 / 1701)) + δ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 27),
        abs_of_nonneg (sq_nonneg _)]
      have := abs_nonneg (K2 (fun x => Nor (osol k d x)) r - K2 h r)
      nlinarith [sq_nonneg r]
    have t1 := abs_sub ((k - k') * r)
      (8 / 27 * r ^ 2 * (K2 (fun x => Nor (osol k d x)) r - K2 h r))
    linarith

/-- Lipschitz dependence of the regular solution and of its `D`-derivatives on
the two parameters. -/
theorem osol_dist_le (k d k' d' : ℝ) {r : ℝ} (hr : |r| ≤ 1) :
    |osol k d r - osol k' d' r| ≤ (|d - d'| + |k - k'|) / (1601 / 1701) ∧
      |osol1 k d r - osol1 k' d' r| ≤
        |k - k'| + 16 / 243 * (4 * ((|d - d'| + |k - k'|) / (1601 / 1701))) ∧
      |osol2 k d r - osol2 k' d' r| ≤
        |k - k'| + 676 / 1701 * (4 * ((|d - d'| + |k - k'|) / (1601 / 1701))) := by
  obtain ⟨h0, h1, h2⟩ := compare k d (k' := k') (d' := d') (δ := 0) (osol k' d').continuous
    (continuous_Nor_osol k' d') (fun r hr => osol_eq k' d' hr)
    (fun x _ => by rw [sub_self, abs_zero])
  simp only [mul_zero, add_zero] at h0 h1 h2
  exact ⟨h0 r hr, h1 r hr, h2 r hr⟩

end Calabi.Origin
