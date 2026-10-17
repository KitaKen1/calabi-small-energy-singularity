import Calabi.Correction.TwoPoint
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Extension of sources in time

The solver of `FlatZero.lean` takes a source that is bounded and Hölder
continuous on the whole space-time, while the sources of the construction are
given on a half-open time interval `[0, R)` with a weighted two-point bound.

* `WH.exists_endpoint_extension`: for a time-independent scale, a function with
  a two-point bound on `V × [0, R)` extends to `V × [0, R]` with the same
  bound (the limit at the final time exists by completeness, and it is the
  value of the extension there).
* `clampT`, `WH.global_holder`: on a scale bounded above and below, the
  function with the time clamped to `[0, R]` is bounded and globally Hölder.
-/

open Set Filter Topology

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Clamping the time -/

/-- The time clamped to `[0, R]`. -/
noncomputable def clampT (R t : ℝ) : ℝ := max (min t R) 0

theorem clampT_mem {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : clampT R t ∈ Icc (0 : ℝ) R :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hR⟩

theorem clampT_of_mem {R t : ℝ} (ht : t ∈ Icc (0 : ℝ) R) : clampT R t = t := by
  unfold clampT
  rw [min_eq_left ht.2, max_eq_left ht.1]

theorem abs_clampT_sub_le (R t r : ℝ) : |clampT R t - clampT R r| ≤ |t - r| := by
  unfold clampT
  have h1 := abs_max_sub_max_le_abs (min t R) (min r R) 0
  have h2 := abs_min_sub_min_le_max t R r R
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h2
  exact h1.trans h2

theorem abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h2 := abs_min_sub_min_le_max a c b c
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h2
  exact h2

/-! ### Elementary bounds -/

/-- A power of a number between two positive bounds. -/
theorem rpow_le_max {x lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ x) (h2 : x ≤ hi) (v : ℝ) :
    x ^ v ≤ max (lo ^ v) (hi ^ v) := by
  rcases le_or_gt 0 v with hv | hv
  · exact (Real.rpow_le_rpow (hlo.le.trans h1) h2 hv).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hlo h1 hv.le).trans (le_max_left _ _)

/-- A power of the parabolic distance is at most the sum of the powers of its
two parts. -/
theorem pdist_rpow_le (p q : V × ℝ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    pdist p q ^ α ≤ ‖p.1 - q.1‖ ^ α + |p.2 - q.2| ^ (α / 4) := by
  have h := Real.rpow_add_le_add_rpow (norm_nonneg (p.1 - q.1))
    (Real.rpow_nonneg (abs_nonneg (p.2 - q.2)) ((1 : ℝ) / 4)) hα hα1
  have e : (|p.2 - q.2| ^ ((1 : ℝ) / 4)) ^ α = |p.2 - q.2| ^ (α / 4) := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [e] at h
  exact h

/-! ### Global Hölder continuity on a bounded scale -/

/-- **A two-point bound on a scale bounded above and below gives a bounded and
globally Hölder continuous function**, after clamping the time. -/
theorem WH.global_holder {s : V → ℝ} {a α v F R smin smax : ℝ} {f : ℝ → V → ℂ}
    (hf : WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} v F
      (fun p => f p.2 p.1))
    (hF : 0 ≤ F) (ha : 0 < a) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R) (hsmin : 0 < smin)
    (hs1 : ∀ x, smin ≤ s x) (hs2 : ∀ x, s x ≤ smax) :
    (∀ t x, ‖f (clampT R t) x‖ ≤ F * max (smin ^ v) (smax ^ v)) ∧
      ∀ t r x y, ‖f (clampT R t) x - f (clampT R r) y‖
        ≤ (F * max (smin ^ (v - α)) (smax ^ (v - α))
            + 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α))
          * (‖x - y‖ ^ α + |t - r| ^ (α / 4)) := by
  have hsup : ∀ t x, ‖f (clampT R t) x‖ ≤ F * max (smin ^ v) (smax ^ v) := by
    intro t x
    have h1 : ‖f (clampT R t) x‖ ≤ F * s x ^ v := hf.1 (x, clampT R t) (clampT_mem hR t)
    exact h1.trans (mul_le_mul_of_nonneg_left (rpow_le_max hsmin (hs1 x) (hs2 x) v) hF)
  refine ⟨hsup, fun t r x y => ?_⟩
  have hB0 : 0 ≤ F * max (smin ^ v) (smax ^ v) := (norm_nonneg _).trans (hsup t x)
  have hH1 : 0 ≤ F * max (smin ^ (v - α)) (smax ^ (v - α)) :=
    mul_nonneg hF (le_max_of_le_left (Real.rpow_nonneg hsmin.le _))
  have has : 0 < a * smin := mul_pos ha hsmin
  have hH2 : 0 ≤ 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α) :=
    mul_nonneg (mul_nonneg (by norm_num) hB0) (Real.rpow_nonneg has.le _)
  have hd0 := pdist_nonneg (x, clampT R t) (y, clampT R r)
  have hdα : 0 ≤ pdist (x, clampT R t) (y, clampT R r) ^ α := Real.rpow_nonneg hd0 _
  have hdle : pdist (x, clampT R t) (y, clampT R r) ^ α
      ≤ ‖x - y‖ ^ α + |t - r| ^ (α / 4) := by
    refine (pdist_rpow_le (x, clampT R t) (y, clampT R r) hα hα1).trans ?_
    have h1 : |clampT R t - clampT R r| ^ (α / 4) ≤ |t - r| ^ (α / 4) :=
      Real.rpow_le_rpow (abs_nonneg _) (abs_clampT_sub_le R t r) (by linarith)
    exact add_le_add le_rfl h1
  have hmain : ‖f (clampT R t) x - f (clampT R r) y‖
      ≤ (F * max (smin ^ (v - α)) (smax ^ (v - α))
          + 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α))
        * pdist (x, clampT R t) (y, clampT R r) ^ α := by
    rcases le_or_gt (pdist (x, clampT R t) (y, clampT R r)) (a * s x) with h | h
    · have h1 : ‖f (clampT R t) x - f (clampT R r) y‖
          ≤ F * s x ^ (v - α) * pdist (x, clampT R t) (y, clampT R r) ^ α :=
        hf.2 (x, clampT R t) (clampT_mem hR t) (y, clampT R r) (clampT_mem hR r) h
      have h2 : F * s x ^ (v - α) ≤ F * max (smin ^ (v - α)) (smax ^ (v - α)) :=
        mul_le_mul_of_nonneg_left (rpow_le_max hsmin (hs1 x) (hs2 x) _) hF
      calc ‖f (clampT R t) x - f (clampT R r) y‖
          ≤ F * s x ^ (v - α) * pdist (x, clampT R t) (y, clampT R r) ^ α := h1
        _ ≤ F * max (smin ^ (v - α)) (smax ^ (v - α))
            * pdist (x, clampT R t) (y, clampT R r) ^ α := mul_le_mul_of_nonneg_right h2 hdα
        _ ≤ (F * max (smin ^ (v - α)) (smax ^ (v - α))
              + 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α))
            * pdist (x, clampT R t) (y, clampT R r) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) hdα
    · have h1 : ‖f (clampT R t) x - f (clampT R r) y‖
          ≤ 2 * (F * max (smin ^ v) (smax ^ v)) := by
        have := norm_sub_le (f (clampT R t) x) (f (clampT R r) y)
        have := hsup t x
        have := hsup r y
        linarith
      have h2 : a * smin ≤ pdist (x, clampT R t) (y, clampT R r) :=
        (mul_le_mul_of_nonneg_left (hs1 x) ha.le).trans h.le
      have h3 : 1 ≤ (a * smin) ^ (-α) * pdist (x, clampT R t) (y, clampT R r) ^ α := by
        rw [Real.rpow_neg has.le, ← div_eq_inv_mul, ← Real.div_rpow hd0 has.le]
        exact Real.one_le_rpow ((one_le_div has).2 h2) hα
      calc ‖f (clampT R t) x - f (clampT R r) y‖
          ≤ 2 * (F * max (smin ^ v) (smax ^ v)) * 1 := by
            rw [mul_one]
            exact h1
        _ ≤ 2 * (F * max (smin ^ v) (smax ^ v))
            * ((a * smin) ^ (-α) * pdist (x, clampT R t) (y, clampT R r) ^ α) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) hB0)
        _ = 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α)
            * pdist (x, clampT R t) (y, clampT R r) ^ α := by ring
        _ ≤ (F * max (smin ^ (v - α)) (smax ^ (v - α))
              + 2 * (F * max (smin ^ v) (smax ^ v)) * (a * smin) ^ (-α))
            * pdist (x, clampT R t) (y, clampT R r) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) hdα
  exact hmain.trans (mul_le_mul_of_nonneg_left hdle (add_nonneg hH1 hH2))

/-! ### Extension to the final time -/

/-- **Extension to the final time**: for a time-independent scale, a function
with a two-point bound on `V × [0, R)` has an extension to `V × [0, R]` with
the same bound. -/
theorem WH.exists_endpoint_extension {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {s : V → ℝ} {a α v M R : ℝ} {f : V × ℝ → E}
    (hf : WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Ico 0 R} v M f)
    (hs : ∀ x, 0 < s x) (ha : 0 < a) (hα : 0 < α) (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ g : V × ℝ → E, (∀ p : V × ℝ, p.2 ∈ Ico 0 R → g p = f p) ∧
      (∀ x : V, Tendsto (fun t : ℝ => f (x, t)) (𝓝[<] R) (𝓝 (g (x, R)))) ∧
      WH α a (fun p : V × ℝ => s p.1) {p : V × ℝ | p.2 ∈ Icc 0 R} v M g := by
  -- the limit at the final time
  have hlim : ∀ x : V, ∃ L : E, Tendsto (fun t : ℝ => f (x, t)) (𝓝[<] R) (𝓝 L) := by
    intro x
    have hsx := hs x
    have hK : 0 ≤ M * s x ^ (v - α) := mul_nonneg hM (Real.rpow_nonneg hsx.le _)
    have hc : Cauchy (map (fun t : ℝ => f (x, t)) (𝓝[<] R)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      have hK1 : 0 < M * s x ^ (v - α) + 1 := by linarith
      have hq : 0 < ε / (M * s x ^ (v - α) + 1) := div_pos hε hK1
      have hδ0 : 0 < min (min R ((a * s x) ^ 4)) ((ε / (M * s x ^ (v - α) + 1)) ^ (4 / α)) :=
        lt_min (lt_min hR (pow_pos (mul_pos ha hsx) 4)) (Real.rpow_pos_of_pos hq _)
      obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
          δ = min (min R ((a * s x) ^ 4)) ((ε / (M * s x ^ (v - α) + 1)) ^ (4 / α)) := ⟨_, rfl⟩
      have hδ : 0 < δ := by
        rw [hδdef]
        exact hδ0
      have hδR : δ ≤ R := by
        rw [hδdef]
        exact (min_le_left _ _).trans (min_le_left _ _)
      have hδa : δ ≤ (a * s x) ^ 4 := by
        rw [hδdef]
        exact (min_le_left _ _).trans (min_le_right _ _)
      have hδε : δ ≤ (ε / (M * s x ^ (v - α) + 1)) ^ (4 / α) := by
        rw [hδdef]
        exact min_le_right _ _
      refine ⟨(fun t : ℝ => f (x, t)) '' Ioo (R - δ) R,
        image_mem_map (Ioo_mem_nhdsLT (by linarith)), ?_⟩
      rintro _ ⟨t, ht, rfl⟩ _ ⟨r, hr, rfl⟩
      have htm : ((x, t) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Ico 0 R} := ⟨by linarith [ht.1], ht.2⟩
      have hrm : ((x, r) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Ico 0 R} := ⟨by linarith [hr.1], hr.2⟩
      have htr : |t - r| ≤ δ := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
      have hpd : pdist ((x, t) : V × ℝ) (x, r) = |t - r| ^ ((1 : ℝ) / 4) := by
        unfold pdist
        simp
      have h4 : |t - r| ^ ((1 : ℝ) / 4) ≤ a * s x := by
        have h5 := Real.rpow_le_rpow (abs_nonneg _) (htr.trans hδa)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [ParabolicLocalization.pow_four_quarter (mul_pos ha hsx).le] at h5
      have h1 : ‖f (x, t) - f (x, r)‖ ≤ M * s x ^ (v - α) * pdist ((x, t) : V × ℝ) (x, r) ^ α :=
        hf.2 (x, t) htm (x, r) hrm (by rw [hpd]; exact h4)
      have h6 : pdist ((x, t) : V × ℝ) (x, r) ^ α ≤ ε / (M * s x ^ (v - α) + 1) := by
        rw [hpd, ← Real.rpow_mul (abs_nonneg _)]
        have h7 := Real.rpow_le_rpow (abs_nonneg _) (htr.trans hδε)
          (mul_nonneg (by norm_num) hα.le : (0 : ℝ) ≤ 1 / 4 * α)
        have e : ((ε / (M * s x ^ (v - α) + 1)) ^ (4 / α)) ^ (1 / 4 * α)
            = ε / (M * s x ^ (v - α) + 1) := by
          rw [← Real.rpow_mul hq.le]
          have e1 : 4 / α * (1 / 4 * α) = 1 := by
            calc 4 / α * (1 / 4 * α) = 4 * (1 / 4) * (α / α) := by ring
              _ = 1 := by
                rw [div_self hα.ne']
                norm_num
          rw [e1, Real.rpow_one]
        rwa [e] at h7
      rw [dist_eq_norm]
      calc ‖f (x, t) - f (x, r)‖
          ≤ M * s x ^ (v - α) * pdist ((x, t) : V × ℝ) (x, r) ^ α := h1
        _ ≤ M * s x ^ (v - α) * (ε / (M * s x ^ (v - α) + 1)) :=
          mul_le_mul_of_nonneg_left h6 hK
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hK1]
          nlinarith
    exact CompleteSpace.complete hc
  choose L hL using hlim
  classical
  refine ⟨fun p => if p.2 < R then f p else L p.1, fun p hp => if_pos hp.2, fun x => ?_, ?_⟩
  · show Tendsto (fun t : ℝ => f (x, t)) (𝓝[<] R) (𝓝 (if R < R then f (x, R) else L x))
    rw [if_neg (lt_irrefl R)]
    exact hL x
  -- every value of the extension is a limit of values of `f` at earlier times
  have hpath : ∀ p : V × ℝ, p.2 ∈ Icc (0 : ℝ) R →
      Tendsto (fun t : ℝ => f (p.1, min p.2 t)) (𝓝[<] R)
        (𝓝 (if p.2 < R then f p else L p.1)) := by
    intro p hp
    by_cases h : p.2 < R
    · rw [if_pos h]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT h] with t ht
      rw [min_eq_left ht.1.le]
    · rw [if_neg h]
      have hpR : p.2 = R := le_antisymm hp.2 (not_lt.1 h)
      refine (hL p.1).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hpR, min_eq_right (le_of_lt ht)]
  have hmem : ∀ p : V × ℝ, p.2 ∈ Icc (0 : ℝ) R → ∀ t ∈ Ioo (0 : ℝ) R,
      ((p.1, min p.2 t) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Ico 0 R} := fun p hp t ht =>
    ⟨le_min hp.1 ht.1.le, (min_le_right _ _).trans_lt ht.2⟩
  have hev : Ioo (0 : ℝ) R ∈ 𝓝[<] R := Ioo_mem_nhdsLT hR
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · show ‖if p.2 < R then f p else L p.1‖ ≤ M * s p.1 ^ v
    refine le_of_tendsto (hpath p hp).norm ?_
    filter_upwards [hev] with t ht
    exact hf.1 _ (hmem p hp t ht)
  · have hd' : pdist p q ≤ a * s p.1 := hd
    show ‖(if p.2 < R then f p else L p.1) - (if q.2 < R then f q else L q.1)‖
      ≤ M * s p.1 ^ (v - α) * pdist p q ^ α
    refine le_of_tendsto ((hpath p hp).sub (hpath q hq)).norm ?_
    filter_upwards [hev] with t ht
    have h1 : pdist ((p.1, min p.2 t) : V × ℝ) (q.1, min q.2 t) ≤ pdist p q := by
      unfold pdist
      have h2 : |min p.2 t - min q.2 t| ^ ((1 : ℝ) / 4) ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (abs_nonneg _) (abs_min_sub_min_le p.2 q.2 t) (by norm_num)
      exact add_le_add le_rfl h2
    have h3 := hf.2 _ (hmem p hp t ht) _ (hmem q hq t ht) (h1.trans hd')
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (pdist_nonneg _ _) h1 hα.le)
      (mul_nonneg hM (Real.rpow_nonneg (hs p.1).le _))

end Calabi.Weighted
