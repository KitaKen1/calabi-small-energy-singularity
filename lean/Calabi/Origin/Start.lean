import Calabi.Origin.CertSound
import Calabi.Origin.Data
import Calabi.Match.Matching

/-!
# The jets at `s = 1`

For every parameter of the box the regular solution at the origin has, at
`r = 1`, a jet `(P, D P, D² P)`; in the variable `s = r^{2/3}` this is

  `p = P`,   `p′ = (3/2) D P`,   `p″ = (9/4) D² P - (3/2) D P`.

The certificate at the origin places this jet within `2^-112` of the jet with
which the finite shot starts, so that the hypotheses of
`Calabi.Match.exists_matched` hold: `exists_profile_tail_part` is a solution of
the profile system on `[1, ∞)` whose jet at `s = 1` is the jet of a regular
solution at the origin.
-/

open Set Filter
open scoped Topology

namespace Calabi.Origin

open Calabi.Shot Calabi.Shot.Data Calabi.Origin.Data Calabi.Match

/-- The parameter `k` at the point `z` of the box. -/
noncomputable def kOf (z : ℝ × ℝ) : ℝ := param knum kz1 kz2 z.1 z.2

theorem continuous_kOf : Continuous kOf := by
  unfold kOf param
  fun_prop

/-- The jet `(p, p′, p″)` at `s = 1` of the regular solution. -/
noncomputable def Jmap (z : ℝ × ℝ) : State :=
  (osol (kOf z) (dOf z) 1, 3 / 2 * osol1 (kOf z) (dOf z) 1,
    9 / 4 * osol2 (kOf z) (dOf z) 1 - 3 / 2 * osol1 (kOf z) (dOf z) 1)

/-! ### Numbers -/

theorem pos_num : (originSum.n0 : ℝ) / (scaleO : ℝ)
    + 1 / 2 ^ 56 * ((originSum.nQ : ℝ) / (scaleP : ℝ)) ≤ 1 / 2 := by
  norm_num [originSum, scaleO, scaleP]

theorem delta_num : ((originSum.e0 : ℝ) / ((scaleO : ℝ) * (scaleO : ℝ))
    + 1 / 2 ^ 56 * ((originSum.e1 : ℝ) / ((scaleO : ℝ) * (scaleP : ℝ)))
    + 27 * (1 / 2 ^ 56 * ((originSum.nQ : ℝ) / (scaleP : ℝ)))
      * (1 / 2 ^ 56 * ((originSum.nL : ℝ) / (scaleP : ℝ)))) / 4 ≤ 1 / 2 ^ 137 := by
  norm_num [originSum, scaleO, scaleP]

theorem sum0_H : (sum0.H : ℝ) = 128 := by
  norm_num [sum0]

theorem cen1 : |(originSum.j0.v : ℝ) / (scaleO : ℝ) - (sum0.start.v : ℝ) / (scaleP : ℝ)| ≤
    1 / 2 ^ 127 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, sum0, scaleO, scaleP]

theorem cen2 : |3 / 256 * ((originSum.j0.d1 : ℝ) / (scaleO : ℝ))
    - (sum0.start.d1 : ℝ) / (scaleP : ℝ)| ≤ 1 / 2 ^ 127 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, sum0, scaleO, scaleP]

theorem cen3 : |9 / 65536 * ((originSum.j0.d2 : ℝ) / (scaleO : ℝ))
    - 3 / 32768 * ((originSum.j0.d1 : ℝ) / (scaleO : ℝ))
    - (sum0.start.d2 : ℝ) / (scaleP : ℝ)| ≤ 1 / 2 ^ 127 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, sum0, scaleO, scaleP]

theorem tan11 : |(originSum.j1.v : ℝ) / (scaleP : ℝ) - (resp0.a11 : ℝ) / (scaleU : ℝ)| ≤
    1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

theorem tan12 : |(originSum.j2.v : ℝ) / (scaleP : ℝ) - (resp0.a12 : ℝ) / (scaleU : ℝ)| ≤
    1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

theorem tan21 : |3 / 256 * ((originSum.j1.d1 : ℝ) / (scaleP : ℝ))
    - (resp0.a21 : ℝ) / (scaleU : ℝ)| ≤ 1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

theorem tan22 : |3 / 256 * ((originSum.j2.d1 : ℝ) / (scaleP : ℝ))
    - (resp0.a22 : ℝ) / (scaleU : ℝ)| ≤ 1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

theorem tan31 : |9 / 65536 * ((originSum.j1.d2 : ℝ) / (scaleP : ℝ))
    - 3 / 32768 * ((originSum.j1.d1 : ℝ) / (scaleP : ℝ))
    - (resp0.a31 : ℝ) / (scaleU : ℝ)| ≤ 1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

theorem tan32 : |9 / 65536 * ((originSum.j2.d2 : ℝ) / (scaleP : ℝ))
    - 3 / 32768 * ((originSum.j2.d1 : ℝ) / (scaleP : ℝ))
    - (resp0.a32 : ℝ) / (scaleU : ℝ)| ≤ 1 / 2 ^ 64 := by
  rw [abs_le]
  constructor <;> norm_num [originSum, resp0, scaleP, scaleU]

/-- One component of the first remainder: the error of the certificate, the
mismatch at the centre, and the mismatch of the two responses. -/
theorem start_component {err c0 t1 t2 z1 z2 E : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56)
    (hz2 : |z2| ≤ 1 / 2 ^ 56) (he : |err| ≤ E) (hE : E ≤ 1 / 2 ^ 136)
    (hc : |c0| ≤ 1 / 2 ^ 127) (h1 : |t1| ≤ 1 / 2 ^ 64) (h2 : |t2| ≤ 1 / 2 ^ 64) :
    |err + c0 + z1 * t1 + z2 * t2| ≤ 1 / 2 ^ 112 := by
  have a1 := abs_mul_le_mul hz1 h1
  have a2 := abs_mul_le_mul hz2 h2
  have b1 := abs_add_le (err + c0 + z1 * t1) (z2 * t2)
  have b2 := abs_add_le (err + c0) (z1 * t1)
  have b3 := abs_add_le err c0
  have hn : (1 : ℝ) / 2 ^ 136 + 1 / 2 ^ 127 + 1 / 2 ^ 56 * (1 / 2 ^ 64)
      + 1 / 2 ^ 56 * (1 / 2 ^ 64) ≤ 1 / 2 ^ 112 := by norm_num
  linarith

/-! ### The first remainder bound -/

theorem startOk : StartOk Jmap := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  obtain ⟨a0, a1⟩ := coef_zero_one origin_ok z.1 z.2
  obtain ⟨jv, jd1, jd2⟩ := origin_jets origin_ok z.1 z.2
  have hsol := poly_solution (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2) 1
  have hdef : ∀ x : ℝ, |x| ≤ 1 →
      |Nor (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z.1 z.2 i * x ^ i)
        - polySource (coef q0 q1 q2 z.1 z.2) (clen q0 q1 q2) x| ≤ 1 / 2 ^ 137 :=
    fun x hx => (origin_defect origin_ok hz1 hz2 pos_num hx).trans delta_num
  obtain ⟨c0, c1, c2⟩ := compare (kOf z) (dOf z) (k' := coef q0 q1 q2 z.1 z.2 1)
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
  have h1 : |(1 : ℝ)| ≤ 1 := by norm_num
  have b0 := c0 1 h1
  have b1 := c1 1 h1
  have b2 := c2 1 h1
  rw [hd0, hk0, abs_zero] at b0 b1 b2
  rw [← hsol.2.1] at b1
  rw [← hsol.2.2] at b2
  rw [jv] at b0
  rw [jd1] at b1
  rw [jd2] at b2
  have hH := sum0_H
  -- the three errors of the certificate
  have E0 : (0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701 : ℝ) ≤ 1 / 2 ^ 136 := by norm_num
  have E1 : 3 / 256 * ((0 : ℝ) + 16 / 243 *
      (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137)) ≤
      1 / 2 ^ 136 := by norm_num
  have E2 : 9 / 65536 * ((0 : ℝ) + 676 / 1701 *
        (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137))
      + 3 / 32768 * ((0 : ℝ) + 16 / 243 *
        (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137)) ≤
      1 / 2 ^ 136 := by norm_num
  have e1 : |3 / 256 * (osol1 (kOf z) (dOf z) 1
      - ((originSum.j0.d1 : ℝ) / (scaleO : ℝ) + z.1 * ((originSum.j1.d1 : ℝ) / (scaleP : ℝ))
        + z.2 * ((originSum.j2.d1 : ℝ) / (scaleP : ℝ))))| ≤
      3 / 256 * ((0 : ℝ) + 16 / 243 *
        (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 256)]
    exact mul_le_mul_of_nonneg_left b1 (by norm_num)
  have e2 : |9 / 65536 * (osol2 (kOf z) (dOf z) 1
        - ((originSum.j0.d2 : ℝ) / (scaleO : ℝ) + z.1 * ((originSum.j1.d2 : ℝ) / (scaleP : ℝ))
          + z.2 * ((originSum.j2.d2 : ℝ) / (scaleP : ℝ))))
      - 3 / 32768 * (osol1 (kOf z) (dOf z) 1
        - ((originSum.j0.d1 : ℝ) / (scaleO : ℝ) + z.1 * ((originSum.j1.d1 : ℝ) / (scaleP : ℝ))
          + z.2 * ((originSum.j2.d1 : ℝ) / (scaleP : ℝ))))| ≤
      9 / 65536 * ((0 : ℝ) + 676 / 1701 *
        (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137))
      + 3 / 32768 * ((0 : ℝ) + 16 / 243 *
        (4 * ((0 + 0 + 25 / 1701 * (1 / 2 ^ 137)) / (1601 / 1701)) + 1 / 2 ^ 137)) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 65536)]
      exact mul_le_mul_of_nonneg_left b2 (by norm_num)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 32768)]
      exact mul_le_mul_of_nonneg_left b1 (by norm_num)
  refine inv_initial frame0 ?_ ?_ ?_
  · have key := start_component hz1 hz2 b0 E0 cen1 tan11 tan12
    convert key using 2
    simp only [startJet, Jmap, jetVec, Mat32.app, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    ring
  · have key := start_component hz1 hz2 e1 E1 cen2 tan21 tan22
    convert key using 2
    simp only [startJet, Jmap, jetVec, Mat32.app, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, hH]
    ring
  · have key := start_component hz1 hz2 e2 E2 cen3 tan31 tan32
    convert key using 2
    simp only [startJet, Jmap, jetVec, Mat32.app, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, hH]
    ring

/-! ### Continuity -/

theorem Jmap_dist_le (x y : ℝ × ℝ) :
    dist (Jmap y) (Jmap x) ≤ 10 * (|dOf y - dOf x| + |kOf y - kOf x|) := by
  obtain ⟨h0, h1, h2⟩ := osol_dist_le (kOf y) (dOf y) (kOf x) (dOf x)
    (by norm_num : |(1 : ℝ)| ≤ 1)
  have hd : 0 ≤ |dOf y - dOf x| := abs_nonneg _
  have hk : 0 ≤ |kOf y - kOf x| := abs_nonneg _
  have e : (|dOf y - dOf x| + |kOf y - kOf x|) / (1601 / 1701 : ℝ) =
      1701 / 1601 * (|dOf y - dOf x| + |kOf y - kOf x|) := by ring
  rw [e] at h0 h1 h2
  rw [State.dist_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · show |osol (kOf y) (dOf y) 1 - osol (kOf x) (dOf x) 1| ≤ _
    linarith
  · show |3 / 2 * osol1 (kOf y) (dOf y) 1 - 3 / 2 * osol1 (kOf x) (dOf x) 1| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  · show |9 / 4 * osol2 (kOf y) (dOf y) 1 - 3 / 2 * osol1 (kOf y) (dOf y) 1
        - (9 / 4 * osol2 (kOf x) (dOf x) 1 - 3 / 2 * osol1 (kOf x) (dOf x) 1)| ≤ _
    have t := abs_sub (9 / 4 * (osol2 (kOf y) (dOf y) 1 - osol2 (kOf x) (dOf x) 1))
      (3 / 2 * (osol1 (kOf y) (dOf y) 1 - osol1 (kOf x) (dOf x) 1))
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at t
    have e2 : 9 / 4 * osol2 (kOf y) (dOf y) 1 - 3 / 2 * osol1 (kOf y) (dOf y) 1
        - (9 / 4 * osol2 (kOf x) (dOf x) 1 - 3 / 2 * osol1 (kOf x) (dOf x) 1) =
        9 / 4 * (osol2 (kOf y) (dOf y) 1 - osol2 (kOf x) (dOf x) 1)
          - 3 / 2 * (osol1 (kOf y) (dOf y) 1 - osol1 (kOf x) (dOf x) 1) := by ring
    rw [e2]
    linarith

theorem continuous_Jmap : Continuous Jmap := by
  rw [← continuousOn_univ]
  refine continuousOn_of_dist_le
    (B := fun x y => 10 * (|dOf y - dOf x| + |kOf y - kOf x|)) (fun x _ y _ => Jmap_dist_le x y)
    fun x _ => ?_
  have h1 : Tendsto (fun y => |dOf y - dOf x|) (𝓝[univ] x) (𝓝 |dOf x - dOf x|) :=
    ((continuous_dOf.continuousWithinAt (s := univ) (x := x)).sub tendsto_const_nhds).abs
  have h2 : Tendsto (fun y => |kOf y - kOf x|) (𝓝[univ] x) (𝓝 |kOf x - kOf x|) :=
    ((continuous_kOf.continuousWithinAt (s := univ) (x := x)).sub tendsto_const_nhds).abs
  have h3 := (h1.add h2).const_mul 10
  simpa using h3

/-- **The profile on `[1, ∞)`.** There are a parameter `z` of the box and a
solution of the profile system on `[1, ∞)` that stays above `-19/20`, whose jet
at `s = 1` is the jet of the regular solution at the origin for the parameters
`k(z)`, `d(z)`, and which from `s = 56` on is the approximate tail plus a
bounded solution of the tail equation. -/
theorem exists_profile_tail_part :
    ∃ z ∈ box, ∃ Y : ℝ → State, Y 1 = Jmap z ∧
      HasDerivWithinAt Y (pfield (dOf z) 1 (Y 1)) (Ici 1) 1 ∧
      (∀ s, 1 < s → HasDerivAt Y (pfield (dOf z) s (Y s)) s) ∧
      (∀ s, 1 ≤ s → -19 / 20 ≤ (Y s).1) ∧
      ∃ X : ℝ → State, Calabi.Tail.Solves 56 X (fun s => tailF (dOf z) s (X s)) ∧
        (∃ B, ∀ s, (56 : ℝ) ≤ s → |(X s).1| ≤ B ∧ |(X s).2.1| ≤ B ∧ |(X s).2.2| ≤ B) ∧
        ∀ s, 56 ≤ s →
          Y s = (Calabi.Tail.apx Calabi.Tail.Data.tailP s + (X s).1,
            Calabi.Tail.apx1 Calabi.Tail.Data.tailP s + (X s).2.1,
            Calabi.Tail.apx2 Calabi.Tail.Data.tailP s + (X s).2.2) ∧
          |(Y s).1| ≤ 1 / 100 :=
  exists_matched continuous_Jmap.continuousOn startOk

end Calabi.Origin
