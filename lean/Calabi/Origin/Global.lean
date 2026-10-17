import Calabi.Origin.Start
import Calabi.Origin.Deriv

/-!
# The profile system on `(0, ∞)`

The regular solution at the origin, on `0 < s ≤ 1`, and the solution of
`Calabi.Origin.exists_profile_tail_part`, on `s ≥ 1`, have the same jet at
`s = 1`. Glued there they are one trajectory of the profile system on the
whole half-line `s > 0`.
-/

open Set Filter
open scoped Topology

namespace Calabi.Origin

open Calabi.Shot Calabi.Shot.Data Calabi.Origin.Data Calabi.Match

theorem size_num : (originSum.n0 : ℝ) / (scaleO : ℝ)
    + 1 / 2 ^ 56 * ((originSum.nQ : ℝ) / (scaleP : ℝ)) ≤ 1 / 3 := by
  norm_num [originSum, scaleO, scaleP]

/-- On the box the regular solution stays within `2/5` on `|r| ≤ 1`. -/
theorem abs_osol_le {z : ℝ × ℝ} (hz : z ∈ box) {r : ℝ} (hr : |r| ≤ 1) :
    |osol (kOf z) (dOf z) r| ≤ 2 / 5 := by
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  obtain ⟨a0, a1⟩ := coef_zero_one origin_ok z.1 z.2
  have hdef : ∀ x : ℝ, |x| ≤ 1 →
      |Nor (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z.1 z.2 i * x ^ i)
        - polySource (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2) x| ≤ 1 / 2 ^ 137 :=
    fun x hx => (origin_defect origin_ok hz1 hz2 pos_num hx).trans delta_num
  obtain ⟨c0, -, -⟩ := compare (kOf z) (dOf z) (k' := coef q0 q1 q2 z.1 z.2 1)
    (d' := coef q0 q1 q2 z.1 z.2 0) (δ := 1 / 2 ^ 137)
    (continuous_polySum (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2 + 2))
    (continuous_polySource (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2))
    (fun r _ => (poly_solution (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2) r).1) hdef
  have hd0 : dOf z - coef q0 q1 q2 z.1 z.2 0 = 0 := by
    rw [a0]
    exact sub_self _
  have hk0 : kOf z - coef q0 q1 q2 z.1 z.2 1 = 0 := by
    rw [a1]
    exact sub_self _
  have b := c0 r hr
  rw [hd0, hk0, abs_zero] at b
  have hQ := (origin_Q_bound origin_ok hz1 hz2 hr).trans size_num
  have E0 : (0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701 : ℝ) ≤ 1 / 15 := by norm_num
  have t := abs_sub_abs_le_abs_sub (osol (kOf z) (dOf z) r)
    (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z.1 z.2 i * r ^ i)
  linarith

theorem abs_mul_sqrt_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : |s * Real.sqrt s| ≤ 1 := by
  have h1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1
  have h0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  rw [abs_of_nonneg (mul_nonneg hs0.le h0)]
  exact mul_le_one₀ hs1 h0 h1

/-- **The profile system on `(0, ∞)`.** There are a parameter `z` of the box
and a trajectory `Z` of the profile system on `s > 0` that stays above
`-19/20`, is the regular solution at the origin for `0 < s ≤ 1`, and from
`s = 56` on is the approximate tail plus a bounded solution of the tail
equation. -/
theorem exists_profile_jet :
    ∃ z ∈ box, ∃ Z : ℝ → State,
      (∀ s, 0 < s → HasDerivAt Z (pfield (dOf z) s (Z s)) s) ∧
      (∀ s, 0 < s → -19 / 20 ≤ (Z s).1) ∧
      (∀ s, 0 < s → s ≤ 1 → Z s = originJet (kOf z) (dOf z) s) ∧
      ∃ X : ℝ → State, Calabi.Tail.Solves 56 X (fun s => tailF (dOf z) s (X s)) ∧
        (∃ B, ∀ s, (56 : ℝ) ≤ s → |(X s).1| ≤ B ∧ |(X s).2.1| ≤ B ∧ |(X s).2.2| ≤ B) ∧
        ∀ s, 56 ≤ s →
          Z s = (Calabi.Tail.apx Calabi.Tail.Data.tailP s + (X s).1,
            Calabi.Tail.apx1 Calabi.Tail.Data.tailP s + (X s).2.1,
            Calabi.Tail.apx2 Calabi.Tail.Data.tailP s + (X s).2.2) ∧
          |(Z s).1| ≤ 1 / 100 := by
  obtain ⟨z, hz, Y, hY1, hYr, hYd, hYlow, X, hX, hXb, hXY⟩ := exists_profile_tail_part
  have hO1 : originJet (kOf z) (dOf z) 1 = Y 1 := by
    rw [originJet_one, hY1]
    rfl
  -- the regular solution is a trajectory on `0 < s ≤ 1`
  have hO : ∀ s, 0 < s → s ≤ 1 → HasDerivAt (originJet (kOf z) (dOf z))
      (pfield (dOf z) s (originJet (kOf z) (dOf z) s)) s := by
    intro s hs0 hs1
    have hw : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have hw1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1
    have hr : |Real.sqrt s ^ 3| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact pow_le_one₀ hw.le hw1
    have hlow : -(1 / 2) ≤ osol (kOf z) (dOf z) (Real.sqrt s ^ 3) := by
      have := (abs_le.1 (abs_osol_le hz hr)).1
      linarith
    have h := hasDerivAt_originJet (kOf z) (dOf z) hw hw1 hlow
    rwa [Real.sq_sqrt hs0.le] at h
  let Z : ℝ → State := fun s => if s ≤ 1 then originJet (kOf z) (dOf z) s else Y s
  have hZle : ∀ s, s ≤ 1 → Z s = originJet (kOf z) (dOf z) s := fun s hs => ite_eq_left hs
  have hZge : ∀ s, 1 ≤ s → Z s = Y s := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, hZle 1 le_rfl, hO1]
    · exact ite_eq_right (not_le.2 h)
  refine ⟨z, hz, Z, ?_, ?_, fun s _ hs1 => hZle s hs1, X, hX, hXb, ?_⟩
  · intro s hs
    rcases lt_trichotomy s 1 with h | h | h
    · rw [hZle s h.le]
      refine (hO s hs h.le).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with u hu using hZle u (le_of_lt hu)
    · subst h
      have hl : HasDerivWithinAt Z (pfield (dOf z) 1 (Z 1)) (Iic 1) 1 := by
        rw [hZle 1 le_rfl]
        exact (hO 1 one_pos le_rfl).hasDerivWithinAt.congr (fun u hu => hZle u hu)
          (hZle 1 le_rfl)
      have hr : HasDerivWithinAt Z (pfield (dOf z) 1 (Z 1)) (Ici 1) 1 := by
        rw [hZge 1 le_rfl]
        exact hYr.congr (fun u hu => hZge u hu) (hZge 1 le_rfl)
      have hu := hl.union hr
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
      exact hu
    · rw [hZge s h.le]
      refine (hYd s h).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with u hu using hZge u (le_of_lt hu)
  · intro s hs
    rcases le_total s 1 with h | h
    · rw [hZle s h]
      have hr := abs_mul_sqrt_le hs h
      have hb := (abs_le.1 (abs_osol_le hz hr)).1
      show -19 / 20 ≤ oP (kOf z) (dOf z) (s * Real.sqrt s)
      rw [oP_eq_osol _ _ hr]
      linarith
    · rw [hZge s h]
      exact hYlow s h
  · intro s hs
    have h1 : (1 : ℝ) ≤ s := by linarith
    rw [hZge s h1]
    exact hXY s hs

end Calabi.Origin
