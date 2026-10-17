import Calabi.Shot
import Calabi.Tail.CertSound
import Calabi.Match.Numbers
import OAI.Analysis.SphereIsometry.CompactConvexFixedPoint

/-!
# Matching the finite shot with the tail at `s = 56`

For every parameter `z` of the box the finite shot ends in a jet at `s = 56`,
and the tail equation has a bounded solution with the same stable coordinate.
The preconditioned difference of the unstable coordinates is a continuous map
of the box into itself, so Brouwer's theorem gives a parameter at which the two
jets agree. Glued at `s = 56`, the finite shot and the tail are then one
solution of the profile system on `[1, ∞)`.

The jet at `s = 1` is an abstract continuous map `Jmap` of the box that
satisfies the first remainder bound; the analytic family at the origin will
provide it.
-/

open Set Filter
open scoped Topology

namespace Calabi.Match

open Calabi.Shot Calabi.Shot.Data Calabi.Tail Calabi.Tail.Data

/-- The box of preconditioned parameters, `|z₁|, |z₂| ≤ 2^-56`. -/
def box : Set (ℝ × ℝ) := Metric.closedBall 0 (1 / 2 ^ 56)

theorem mem_box {z : ℝ × ℝ} : z ∈ box ↔ |z.1| ≤ 1 / 2 ^ 56 ∧ |z.2| ≤ 1 / 2 ^ 56 := by
  rw [box, mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- The parameter `d` at the point `z` of the box. -/
noncomputable def dOf (z : ℝ × ℝ) : ℝ := param dnum dz1 dz2 z.1 z.2

theorem continuous_dOf : Continuous dOf := by
  unfold dOf param
  fun_prop

theorem abs_dOf_sub_le {z : ℝ × ℝ} (hz : z ∈ box) :
    |dOf z - (dnum : ℝ) / (scaleP : ℝ)| ≤ 1 / 2 ^ 69 := by
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  have hSu := scaleU_pos
  have e : dOf z - (dnum : ℝ) / (scaleP : ℝ) =
      ((dz1 : ℝ) * z.1 + (dz2 : ℝ) * z.2) / (scaleU : ℝ) := by
    unfold dOf param
    ring
  have h1 := lin2_abs_le (dz1 : ℝ) (dz2 : ℝ) hz1 hz2
  have hc : ((dz1.natAbs + dz2.natAbs : ℕ) : ℝ) = |(dz1 : ℝ)| + |(dz2 : ℝ)| := by
    simp only [Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
  have h2 := dz_bound
  rw [hc, div_le_iff₀ hSu] at h2
  rw [e, abs_div, abs_of_pos hSu, div_le_iff₀ hSu]
  have h3 : (|(dz1 : ℝ)| + |(dz2 : ℝ)|) * (1 / 2 ^ 56) ≤
      1 / 2 ^ 13 * (scaleU : ℝ) * (1 / 2 ^ 56) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  calc |(dz1 : ℝ) * z.1 + (dz2 : ℝ) * z.2| ≤ (|(dz1 : ℝ)| + |(dz2 : ℝ)|) * (1 / 2 ^ 56) := h1
    _ ≤ 1 / 2 ^ 13 * (scaleU : ℝ) * (1 / 2 ^ 56) := h3
    _ = 1 / 2 ^ 69 * (scaleU : ℝ) := by ring

/-- The jet at `s = 1` in the variable of the first block. -/
noncomputable def startJet (J : State) : State :=
  (J.1, J.2.1 / (sum0.H : ℝ), J.2.2 / (sum0.H : ℝ) ^ 2)

theorem blockJet_start (Y : ℝ → State) :
    blockJet (sum0.H : ℝ) (sum0.A : ℝ) Y (-1) = startJet (Y 1) := by
  have h : ((sum0.A : ℝ) + -1) / (sum0.H : ℝ) = 1 := by
    rw [← sub_eq_add_neg]
    exact start_eq_one
  unfold blockJet startJet
  rw [h]

theorem sum575_H : (sum575.H : ℝ) = 16 := by
  norm_num [sum575]

theorem blockJet_end (Y : ℝ → State) :
    blockJet (sum575.H : ℝ) (sum575.A : ℝ) Y 1 =
      ((Y 56).1, (Y 56).2.1 / 16, (Y 56).2.2 / 16 ^ 2) := by
  unfold blockJet
  rw [stop_eq_56, sum575_H]

/-! ### The tail -/

/-- Bound for the residual of the approximate tail at the parameter `d`. -/
noncomputable def tailEps (d : ℝ) : ℝ :=
  (tailSum.eps : ℝ) / (scaleE : ℝ) + |d - (dnum : ℝ) / (scaleP : ℝ)| / 1000

theorem tailEps_nonneg (d : ℝ) : 0 ≤ tailEps d := by
  unfold tailEps
  positivity

theorem tailEps_le {z : ℝ × ℝ} (hz : z ∈ box) : tailEps (dOf z) ≤ 1 / 2 ^ 78 := by
  unfold tailEps
  have h1 := eps_bound
  have h2 := abs_dOf_sub_le hz
  have h3 : (1 : ℝ) / 2 ^ 90 + 1 / 2 ^ 69 / 1000 ≤ 1 / 2 ^ 78 := by norm_num
  linarith

/-- The right-hand side of the tail equation at the parameter `d`. -/
noncomputable def tailF (d : ℝ) (s : ℝ) (X : State) : ℝ :=
  Ftail (apx tailP) (resid d (apx tailP) (apx1 tailP) (apx2 tailP) (apx3 tailP)) s X

theorem exists_tailSol (d q₀ : ℝ) :
    ∃ X : ℝ → State, Solves 56 X (fun s => tailF d s (X s)) ∧ stab (X 56) = q₀ ∧
      (∀ s, 56 ≤ s → energy (X s) ≤ 4 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ^ 2) ∧
      ∀ s, 56 ≤ s →
        |(X s).1| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ∧
        |(X s).2.1| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ∧
        |(X s).2.2| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := tail_cert_spec tail_ok d
  exact exists_profile_tail h1 h2 h3 h4 (fun s hs => (h5 s hs).trans (by norm_num)) h6 q₀

/-- A bounded tail with parameter `d` and stable coordinate `q₀` at `s = 56`. -/
noncomputable def tailSol (d q₀ : ℝ) : ℝ → State := Classical.choose (exists_tailSol d q₀)

theorem tailSol_solves (d q₀ : ℝ) : Solves 56 (tailSol d q₀) (fun s => tailF d s (tailSol d q₀ s)) :=
  (Classical.choose_spec (exists_tailSol d q₀)).1

theorem stab_tailSol (d q₀ : ℝ) : stab (tailSol d q₀ 56) = q₀ :=
  (Classical.choose_spec (exists_tailSol d q₀)).2.1

theorem energy_tailSol (d q₀ : ℝ) {s : ℝ} (hs : 56 ≤ s) :
    energy (tailSol d q₀ s) ≤ 4 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ^ 2 :=
  (Classical.choose_spec (exists_tailSol d q₀)).2.2.1 s hs

theorem abs_tailSol (d q₀ : ℝ) {s : ℝ} (hs : 56 ≤ s) :
    |(tailSol d q₀ s).1| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ∧
      |(tailSol d q₀ s).2.1| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) ∧
      |(tailSol d q₀ s).2.2| ≤ |q₀| + 5 / 3 * ((tailEps d + 17 / 40 * |q₀|) / (7 / 24)) :=
  (Classical.choose_spec (exists_tailSol d q₀)).2.2.2 s hs

theorem tailSol_bounded (d q₀ : ℝ) : ∃ B, ∀ s, (56 : ℝ) ≤ s →
    |(tailSol d q₀ s).1| ≤ B ∧ |(tailSol d q₀ s).2.1| ≤ B ∧ |(tailSol d q₀ s).2.2| ≤ B :=
  ⟨_, fun _ hs => abs_tailSol d q₀ hs⟩

theorem tailSol_dist_le (d d' q₀ q₀' : ℝ) :
    dist (tailSol d q₀ 56) (tailSol d' q₀' 56) ≤ (|q₀ - q₀'| + 5 / 3 * |d - d'|) / (7 / 24) := by
  have h := profile_tail_dist_le (tailSol_solves d q₀) (tailSol_solves d' q₀')
    (tailSol_bounded d q₀) (tailSol_bounded d' q₀') 56 le_rfl
  rwa [stab_tailSol, stab_tailSol] at h

/-! ### The end of the finite shot -/

/-- The jet of the finite shot at `s = 56`. -/
noncomputable def shotEnd (Jmap : ℝ × ℝ → State) (z : ℝ × ℝ) : State :=
  traj (dOf z) (Jmap z) 56

/-- The jet of the approximate tail at `s = 56`. -/
noncomputable def A56 : State := (apx tailP 56, apx1 tailP 56, apx2 tailP 56)

theorem A56_eq : A56 = ((tailSum.v : ℝ) / (scaleP : ℝ), (tailSum.d1 : ℝ) / ((scaleP : ℝ) * 56),
    (tailSum.d2 : ℝ) / ((scaleP : ℝ) * 56 ^ 2)) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9⟩ := tail_cert_spec tail_ok 0
  unfold A56
  rw [h7, h8, h9]

/-- The jet of the finite shot minus the jet of the approximate tail. -/
noncomputable def gap (Jmap : ℝ × ℝ → State) (z : ℝ × ℝ) : State := shotEnd Jmap z - A56

/-- The hypothesis on the jets at `s = 1`: the first remainder bound. -/
def StartOk (Jmap : ℝ × ℝ → State) : Prop :=
  ∀ z ∈ box, Inv frame0 (initial frame0)
    (startJet (Jmap z) - (scaleP : ℝ)⁻¹ • jetVec sum0.start - (scaleU : ℝ)⁻¹ • resp0.app z.1 z.2)

theorem gap_decomp {Jmap : ℝ × ℝ → State} (hJ : StartOk Jmap) {z : ℝ × ℝ} (hz : z ∈ box) :
    (∀ σ ∈ Icc (1 : ℝ) 56, -19 / 20 ≤ (traj (dOf z) (Jmap z) σ).1) ∧
      ∃ ρ : State, gap Jmap z = Δ₀ + z.1 • g₁ + z.2 • g₂ + ρ ∧
        |ρ.1| ≤ 1 / 2 ^ 70 ∧ |ρ.2.1| ≤ 1 / 2 ^ 67 ∧ |ρ.2.2| ≤ 1 / 2 ^ 68 := by
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  have hY : SolvesOn (param dnum dz1 dz2 z.1 z.2) 1 56 (traj (dOf z) (Jmap z)) :=
    traj_solves (dOf z) (Jmap z)
  have h0 : Inv frame0 (initial frame0)
      (blockJet (sum0.H : ℝ) (sum0.A : ℝ) (traj (dOf z) (Jmap z)) (-1)
        - (scaleP : ℝ)⁻¹ • jetVec sum0.start - (scaleU : ℝ)⁻¹ • resp0.app z.1 z.2) := by
    rw [blockJet_start, traj_one]
    exact hJ z hz
  obtain ⟨hcov, hend⟩ := finite_shot hz1 hz2 hY h0
  rw [blockJet_end] at hend
  obtain ⟨r1, r2, r3⟩ := hend.abs_le frameEnd_det_pos
  rw [radius_end] at r1 r2 r3
  obtain ⟨p1, p2, p3⟩ := rad_bounds
  refine ⟨hcov, ?_⟩
  generalize hr : (((traj (dOf z) (Jmap z) 56).1, (traj (dOf z) (Jmap z) 56).2.1 / 16,
      (traj (dOf z) (Jmap z) 56).2.2 / 16 ^ 2) : State)
    - (scaleP : ℝ)⁻¹ • jetVec sum575.stop - (scaleU : ℝ)⁻¹ • respEnd.app z.1 z.2 = r
    at r1 r2 r3
  have e1 : (traj (dOf z) (Jmap z) 56).1 = (sum575.stop.v : ℝ) / (scaleP : ℝ)
      + ((respEnd.a11 : ℝ) * z.1 + (respEnd.a12 : ℝ) * z.2) / (scaleU : ℝ) + r.1 := by
    rw [← hr]
    simp only [jetVec, Mat32.app, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    ring
  have e2 : (traj (dOf z) (Jmap z) 56).2.1 = 16 * ((sum575.stop.d1 : ℝ) / (scaleP : ℝ)
      + ((respEnd.a21 : ℝ) * z.1 + (respEnd.a22 : ℝ) * z.2) / (scaleU : ℝ) + r.2.1) := by
    rw [← hr]
    simp only [jetVec, Mat32.app, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have e3 : (traj (dOf z) (Jmap z) 56).2.2 = 256 * ((sum575.stop.d2 : ℝ) / (scaleP : ℝ)
      + ((respEnd.a31 : ℝ) * z.1 + (respEnd.a32 : ℝ) * z.2) / (scaleU : ℝ) + r.2.2) := by
    rw [← hr]
    simp only [jetVec, Mat32.app, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    ring
  refine ⟨(r.1, 16 * r.2.1, 256 * r.2.2), ?_, ?_, ?_, ?_⟩
  · unfold gap shotEnd
    rw [A56_eq]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Δ₀, g₁, g₂, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      rw [e1]
      ring
    · simp only [Δ₀, g₁, g₂, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [e2]
      ring
    · simp only [Δ₀, g₁, g₂, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      rw [e3]
      ring
  · exact r1.trans p1
  · show |16 * r.2.1| ≤ 1 / 2 ^ 67
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
    linarith
  · show |256 * r.2.2| ≤ 1 / 2 ^ 68
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 256)]
    linarith

theorem abs_stab_gap_le {Jmap : ℝ × ℝ → State} (hJ : StartOk Jmap) {z : ℝ × ℝ} (hz : z ∈ box) :
    |stab (gap Jmap z)| ≤ 4 / 25 * (1 / 2 ^ 56) := by
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  obtain ⟨-, ρ, hgap, hρ1, hρ2, hρ3⟩ := gap_decomp hJ hz
  rw [hgap]
  have h := match_stab hz1 hz2 stab_Δ₀ (add_le_add stab_g₁ stab_g₂) hρ1 hρ2 hρ3
  refine h.trans ?_
  norm_num

/-! ### The matching map -/

/-- The jet of the tail at `s = 56` that has the stable coordinate of the shot. -/
noncomputable def tailJet (Jmap : ℝ × ℝ → State) (z : ℝ × ℝ) : State :=
  tailSol (dOf z) (stab (gap Jmap z)) 56

/-- The preconditioned matching map: its fixed points are the parameters at
which the shot and the tail have the same jet at `s = 56`. -/
noncomputable def Φ (Jmap : ℝ × ℝ → State) (z : ℝ × ℝ) : ℝ × ℝ :=
  (1 * z.1 + 0 * z.2 - -11685 / 65536 * (ux (gap Jmap z) - ux (tailJet Jmap z))
      - 31935 / 65536 * (uw (gap Jmap z) - uw (tailJet Jmap z)),
    0 * z.1 + 1 * z.2 - -19332 / 65536 * (ux (gap Jmap z) - ux (tailJet Jmap z))
      - -22620 / 65536 * (uw (gap Jmap z) - uw (tailJet Jmap z)))

theorem tail_J_le {Jmap : ℝ × ℝ → State} (hJ : StartOk Jmap) {z : ℝ × ℝ} (hz : z ∈ box) :
    (tailEps (dOf z) + 17 / 40 * |stab (gap Jmap z)|) / (7 / 24) ≤ 47 / 200 * (1 / 2 ^ 56) := by
  have h1 := tailEps_le hz
  have h2 := abs_stab_gap_le hJ hz
  rw [div_le_iff₀ (by norm_num)]
  have h3 : (1 : ℝ) / 2 ^ 78 + 17 / 40 * (4 / 25 * (1 / 2 ^ 56)) ≤
      47 / 200 * (1 / 2 ^ 56) * (7 / 24) := by norm_num
  linarith

theorem tail_J_nonneg (Jmap : ℝ × ℝ → State) (z : ℝ × ℝ) :
    0 ≤ (tailEps (dOf z) + 17 / 40 * |stab (gap Jmap z)|) / (7 / 24) := by
  have := tailEps_nonneg (dOf z)
  positivity

theorem Φ_mapsTo {Jmap : ℝ × ℝ → State} (hJ : StartOk Jmap) : MapsTo (Φ Jmap) box box := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := mem_box.1 hz
  obtain ⟨-, ρ, hgap, hρ1, hρ2, hρ3⟩ := gap_decomp hJ hz
  have hJ0 : (0 : ℝ) ≤ 47 / 200 * (1 / 2 ^ 56) := by positivity
  have hT : energy (tailJet Jmap z) ≤ 4 * (47 / 200 * (1 / 2 ^ 56)) ^ 2 := by
    refine (energy_tailSol (dOf z) (stab (gap Jmap z)) le_rfl).trans ?_
    have := pow_le_pow_left₀ (tail_J_nonneg Jmap z) (tail_J_le hJ hz) 2
    linarith
  have a1 : |(-11685 / 65536 : ℝ)| = 11685 / 65536 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  have a2 : |(31935 / 65536 : ℝ)| = 31935 / 65536 := abs_of_pos (by norm_num)
  have a3 : |(-19332 / 65536 : ℝ)| = 19332 / 65536 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  have a4 : |(-22620 / 65536 : ℝ)| = 22620 / 65536 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  have row1 := match_row (e1 := 1) (e2 := 0) (c1 := -11685 / 65536) (c2 := 31935 / 65536)
    (T := tailJet Jmap z) hz1 hz2 (add_le_add row1_m1 row1_m2) row1_v hρ1 hρ2 hρ3 hJ0 hT
  have row2 := match_row (e1 := 0) (e2 := 1) (c1 := -19332 / 65536) (c2 := -22620 / 65536)
    (T := tailJet Jmap z) hz1 hz2 (add_le_add row2_m1 row2_m2) row2_v hρ1 hρ2 hρ3 hJ0 hT
  rw [← hgap, a1, a2] at row1
  rw [← hgap, a3, a4] at row2
  refine mem_box.2 ⟨row1.trans ?_, row2.trans ?_⟩
  · norm_num
  · norm_num

/-! ### Continuity -/

theorem continuousOn_of_dist_le {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β]
    {S : Set α} {f : α → β} {B : α → α → ℝ} (h : ∀ x ∈ S, ∀ y ∈ S, dist (f y) (f x) ≤ B x y)
    (hB : ∀ x ∈ S, Tendsto (B x) (𝓝[S] x) (𝓝 0)) : ContinuousOn f S := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun y => dist_nonneg) ?_ (hB x hx)
  exact eventually_nhdsWithin_of_forall fun y hy => h x hx y hy

theorem continuous_stab : Continuous stab := by
  unfold stab
  fun_prop

theorem continuous_ux : Continuous ux := by
  unfold ux
  fun_prop

theorem continuous_uw : Continuous uw := by
  unfold uw
  fun_prop

theorem gap_continuousOn {Jmap : ℝ × ℝ → State} (hJc : ContinuousOn Jmap box) :
    ContinuousOn (gap Jmap) box := by
  have hs : ContinuousOn (shotEnd Jmap) box := by
    refine continuousOn_of_dist_le
      (B := fun x y => (dist (Jmap y) (Jmap x) + |dOf y - dOf x|) * Real.exp (647 * 55))
      (fun x _ y _ => traj_dist_le (dOf y) (dOf x) (Jmap y) (Jmap x) ⟨by norm_num, le_rfl⟩)
      fun x hx => ?_
    have h1 : Tendsto (fun y => dist (Jmap y) (Jmap x)) (𝓝[box] x)
        (𝓝 (dist (Jmap x) (Jmap x))) := (hJc x hx).dist tendsto_const_nhds
    have h2 : Tendsto (fun y => |dOf y - dOf x|) (𝓝[box] x) (𝓝 |dOf x - dOf x|) :=
      ((continuous_dOf.continuousWithinAt (s := box) (x := x)).sub tendsto_const_nhds).abs
    have h3 := (h1.add h2).mul_const (Real.exp (647 * 55))
    simpa using h3
  exact hs.sub continuousOn_const

theorem tailJet_continuousOn {Jmap : ℝ × ℝ → State} (hJc : ContinuousOn Jmap box) :
    ContinuousOn (tailJet Jmap) box := by
  have hq : ContinuousOn (fun z => stab (gap Jmap z)) box :=
    continuous_stab.comp_continuousOn (gap_continuousOn hJc)
  refine continuousOn_of_dist_le
    (B := fun x y => (|stab (gap Jmap y) - stab (gap Jmap x)| + 5 / 3 * |dOf y - dOf x|)
      / (7 / 24))
    (fun x _ y _ => tailSol_dist_le (dOf y) (dOf x) (stab (gap Jmap y)) (stab (gap Jmap x)))
    fun x hx => ?_
  have h1 : Tendsto (fun y => |stab (gap Jmap y) - stab (gap Jmap x)|) (𝓝[box] x)
      (𝓝 |stab (gap Jmap x) - stab (gap Jmap x)|) :=
    (((hq x hx).tendsto).sub tendsto_const_nhds).abs
  have h2 : Tendsto (fun y => |dOf y - dOf x|) (𝓝[box] x) (𝓝 |dOf x - dOf x|) :=
    ((continuous_dOf.continuousWithinAt (s := box) (x := x)).sub tendsto_const_nhds).abs
  have h3 := (h1.add (h2.const_mul (5 / 3))).div_const (7 / 24)
  simpa using h3

theorem Φ_continuousOn {Jmap : ℝ × ℝ → State} (hJc : ContinuousOn Jmap box) :
    ContinuousOn (Φ Jmap) box := by
  have hg := gap_continuousOn hJc
  have ht := tailJet_continuousOn hJc
  have hux : ContinuousOn (fun z => ux (gap Jmap z) - ux (tailJet Jmap z)) box :=
    (continuous_ux.comp_continuousOn hg).sub (continuous_ux.comp_continuousOn ht)
  have huw : ContinuousOn (fun z => uw (gap Jmap z) - uw (tailJet Jmap z)) box :=
    (continuous_uw.comp_continuousOn hg).sub (continuous_uw.comp_continuousOn ht)
  have l1 : ContinuousOn (fun z : ℝ × ℝ => 1 * z.1 + 0 * z.2) box :=
    (by fun_prop : Continuous fun z : ℝ × ℝ => 1 * z.1 + 0 * z.2).continuousOn
  have l2 : ContinuousOn (fun z : ℝ × ℝ => 0 * z.1 + 1 * z.2) box :=
    (by fun_prop : Continuous fun z : ℝ × ℝ => 0 * z.1 + 1 * z.2).continuousOn
  exact ((l1.sub (continuousOn_const.mul hux)).sub (continuousOn_const.mul huw)).prodMk
    ((l2.sub (continuousOn_const.mul hux)).sub (continuousOn_const.mul huw))

/-! ### The matched solution -/

/-- **Matching.** There is a parameter of the box at which the finite shot and
the tail have the same jet at `s = 56`. -/
theorem exists_match {Jmap : ℝ × ℝ → State} (hJc : ContinuousOn Jmap box) (hJ : StartOk Jmap) :
    ∃ z ∈ box, shotEnd Jmap z = A56 + tailJet Jmap z := by
  obtain ⟨z, hz, hfix⟩ := OAI.Tingley.exists_fixedPoint_of_isCompact_convex
    (isCompact_closedBall (0 : ℝ × ℝ) (1 / 2 ^ 56))
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩ (convex_closedBall (0 : ℝ × ℝ) (1 / 2 ^ 56))
    (Φ_continuousOn hJc) (Φ_mapsTo hJ)
  refine ⟨z, hz, ?_⟩
  have h1 := congrArg Prod.fst hfix
  have h2 := congrArg Prod.snd hfix
  simp only [Φ] at h1 h2
  obtain ⟨hx, hw⟩ := eq_zero_of_det_ne_zero
    (c11 := -11685 / 65536) (c12 := 31935 / 65536) (c21 := -19332 / 65536) (c22 := -22620 / 65536)
    (a := ux (gap Jmap z) - ux (tailJet Jmap z)) (b := uw (gap Jmap z) - uw (tailJet Jmap z))
    (by norm_num) (by linarith) (by linarith)
  have hs : stab (gap Jmap z) = stab (tailJet Jmap z) := (stab_tailSol _ _).symm
  have hgt : gap Jmap z = tailJet Jmap z :=
    eq_of_coords hs (sub_eq_zero.1 hx) (sub_eq_zero.1 hw)
  unfold gap at hgt
  rw [← hgt]
  abel

/-- **The solution on `[1, ∞)`.** Given the jets at `s = 1`, there are a
parameter of the box and a solution of the profile system on `[1, ∞)` that
starts at the given jet, stays above `-19/20`, and from `s = 56` on is the
approximate tail plus a bounded solution of the tail equation. -/
theorem exists_matched {Jmap : ℝ × ℝ → State} (hJc : ContinuousOn Jmap box) (hJ : StartOk Jmap) :
    ∃ z ∈ box, ∃ Y : ℝ → State, Y 1 = Jmap z ∧
      HasDerivWithinAt Y (pfield (dOf z) 1 (Y 1)) (Ici 1) 1 ∧
      (∀ s, 1 < s → HasDerivAt Y (pfield (dOf z) s (Y s)) s) ∧
      (∀ s, 1 ≤ s → -19 / 20 ≤ (Y s).1) ∧
      ∃ X : ℝ → State, Solves 56 X (fun s => tailF (dOf z) s (X s)) ∧
        (∃ B, ∀ s, (56 : ℝ) ≤ s → |(X s).1| ≤ B ∧ |(X s).2.1| ≤ B ∧ |(X s).2.2| ≤ B) ∧
        ∀ s, 56 ≤ s →
          Y s = (apx tailP s + (X s).1, apx1 tailP s + (X s).2.1, apx2 tailP s + (X s).2.2) ∧
          |(Y s).1| ≤ 1 / 100 := by
  obtain ⟨z, hz, hmatch⟩ := exists_match hJc hJ
  obtain ⟨hcov, -⟩ := gap_decomp hJ hz
  refine ⟨z, hz, ?_⟩
  set q₀ := stab (gap Jmap z) with hq₀
  set X := tailSol (dOf z) q₀ with hXdef
  set Ysh := traj (dOf z) (Jmap z) with hYsh
  obtain ⟨ha, ha1, ha2, -, hα, -, -⟩ := tail_cert_spec tail_ok (dOf z)
  -- the tail as a jet
  let Yt : ℝ → State := fun s =>
    (apx tailP s + (X s).1, apx1 tailP s + (X s).2.1, apx2 tailP s + (X s).2.2)
  have hm : Ysh 56 = Yt 56 := by
    have h : Ysh 56 = A56 + X 56 := hmatch
    rw [h]
    exact Prod.ext rfl (Prod.ext rfl rfl)
  -- smallness on the tail
  have hsmall : ∀ s, 56 ≤ s → |apx tailP s + (X s).1| ≤ 1 / 100 := by
    intro s hs
    have h1 := hα s hs
    have h2 := (abs_tailSol (dOf z) q₀ hs).1
    have h3 := tail_J_le hJ hz
    have h4 := abs_stab_gap_le hJ hz
    have h5 := abs_add_le (apx tailP s) (X s).1
    have h6 : (4 : ℝ) / 25 * (1 / 2 ^ 56) + 5 / 3 * (47 / 200 * (1 / 2 ^ 56)) ≤ 1 / 200 := by
      norm_num
    linarith
  have hYt : ∀ s, 56 ≤ s → HasDerivAt Yt (pfield (dOf z) s (Yt s)) s := fun s hs =>
    profile_of_tail (tailSol_solves (dOf z) q₀) hs (ha s hs) (ha1 s hs) (ha2 s hs)
      ((hα s hs).trans (by norm_num)) (hsmall s hs)
  have hYsh := traj_hasDerivWithinAt (dOf z) (Jmap z)
  -- the glued function
  let Y : ℝ → State := fun s => if s ≤ 56 then Ysh s else Yt s
  have hYle : ∀ s, s ≤ 56 → Y s = Ysh s := fun s hs => ite_eq_left hs
  have hYge : ∀ s, 56 ≤ s → Y s = Yt s := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, hYle 56 le_rfl, hm]
    · exact ite_eq_right (not_le.2 h)
  refine ⟨Y, ?_, ?_, ?_, ?_, X, tailSol_solves (dOf z) q₀, tailSol_bounded (dOf z) q₀, ?_⟩
  · rw [hYle 1 (by norm_num)]
    exact traj_one (dOf z) (Jmap z)
  · rw [hYle 1 (by norm_num)]
    have h := (hYsh 1 ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (⟨le_rfl, by norm_num⟩ : (1 : ℝ) ∈ Ico 1 56))
    refine h.congr_of_eventuallyEq ?_ (hYle 1 (by norm_num))
    have hmem : Iio (56 : ℝ) ∈ 𝓝[Ici 1] (1 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [hmem] with u hu using hYle u (le_of_lt hu)
  · intro s hs
    rcases lt_trichotomy s 56 with h | h | h
    · rw [hYle s h.le]
      have hd : HasDerivAt Ysh (pfield (dOf z) s (Ysh s)) s :=
        (hYsh s ⟨hs.le, h.le⟩).hasDerivAt (Icc_mem_nhds hs h)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with u hu using hYle u (le_of_lt hu)
    · subst h
      have hl : HasDerivWithinAt Y (pfield (dOf z) 56 (Y 56)) (Iic 56) 56 := by
        rw [hYle 56 le_rfl]
        have h := (hYsh 56 ⟨by norm_num, le_rfl⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE (by norm_num : (1 : ℝ) < 56))
        exact h.congr (fun u hu => hYle u hu) (hYle 56 le_rfl)
      have hr : HasDerivWithinAt Y (pfield (dOf z) 56 (Y 56)) (Ici 56) 56 := by
        rw [hYge 56 le_rfl]
        exact (hYt 56 le_rfl).hasDerivWithinAt.congr (fun u hu => hYge u hu) (hYge 56 le_rfl)
      have hu := hl.union hr
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
      exact hu
    · rw [hYge s h.le]
      refine (hYt s h.le).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with u hu using hYge u (le_of_lt hu)
  · intro s hs
    rcases le_total s 56 with h | h
    · rw [hYle s h]
      exact hcov s ⟨hs, h⟩
    · rw [hYge s h]
      have := (abs_le.1 (hsmall s h)).1
      show -19 / 20 ≤ apx tailP s + (X s).1
      linarith
  · intro s hs
    refine ⟨hYge s hs, ?_⟩
    rw [hYge s hs]
    exact hsmall s hs

end Calabi.Match
