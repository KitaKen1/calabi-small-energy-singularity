import Calabi.Shot.StepSound

/-!
# The frame part of one step

`step_core` is the linear algebra of a step, with the block error `e` treated
as given: the new remainder

  `scaleU⁻¹ • (D T) r + scaleU⁻² • mismatch z - D e`

satisfies the invariant in the next frame with the bound that the kernel's
`step` computes.
-/

namespace Calabi.Shot

theorem div_le_of_le_div {a b : ℕ} (hb : 0 < b) (h : a ≤ b / 1024) :
    (a : ℝ) / (b : ℝ) ≤ 1 / 1024 := by
  have h1 : a * 1024 ≤ b := (Nat.le_div_iff_mul_le (by norm_num)).1 h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h2 : (a : ℝ) * 1024 ≤ (b : ℝ) := by exact_mod_cast h1
  rw [div_le_div_iff₀ hbR (by norm_num)]
  linarith

theorem step_core {dz1 dz2 : Int} {s : Summary} {g : ℕ} {B Bn : Mat3} {L Ln : Mat32} {ρ : Nat3}
    (hd : 0 < B.det) {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56)
    {r : State} (hr : Inv B ρ r) {e : State} {err : ℕ}
    (he1 : |e.1| ≤ (err : ℝ) / scaleE) (he2 : |e.2.1| ≤ (err : ℝ) / scaleE)
    (he3 : |e.2.2| ≤ (err : ℝ) / scaleE) :
    Inv Bn
      ⟨ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).a
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply (injected dz1 dz2 s g L Ln err)).a,
        ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).b
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply (injected dz1 dz2 s g L Ln err)).b,
        ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).c
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply (injected dz1 dz2 s g L Ln err)).c⟩
      ((scaleU : ℝ)⁻¹ • ((transfer s).rescale g).app r
        + ((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • (mismatch dz1 dz2 s g L Ln).app z1 z2
        - resc (g : ℝ) e) := by
  have hSu := scaleU_pos
  have hE := scaleE_pos
  have hdR : (0 : ℝ) < (B.det : ℝ) := by exact_mod_cast hd
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
  simp only [injected]
  generalize mismatch dz1 dz2 s (g : Int) L Ln = m
  generalize (transfer s).rescale (g : Int) = DT
  -- the propagated part, through the frame identity
  have hw : ((Bn.adj.mul DT).mul B).app (B.adj.app r) =
      (B.det : ℝ) • Bn.adj.app (DT.app r) := by
    rw [Mat3.app_mul, Mat3.app_mul, Mat3.app_adj, Mat3.app_smul, Mat3.app_smul]
  obtain ⟨w1, w2, w3⟩ := hr
  obtain ⟨m1, m2, m3⟩ := ((Bn.adj.mul DT).mul B).abs_app_le w1 w2 w3
  rw [hw] at m1 m2 m3
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos hdR] at m1 m2 m3
  -- the injected part
  have k1 := mis_bound m.a11 m.a12 hz1 hz2
  have k2 := mis_bound m.a21 m.a22 hz1 hz2
  have k3 := mis_bound m.a31 m.a32 hz1 hz2
  have v1 : |(((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).1| ≤
      ((ceilDiv (m.a11.natAbs + m.a12.natAbs) misShift + err : ℕ) : ℝ) / scaleE := by
    have e1 : (((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).1 =
        ((m.a11 : ℝ) * z1 + (m.a12 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ)) + -e.1 := by
      simp only [Mat32.app, resc, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      ring
    have t := abs_add_le
      (((m.a11 : ℝ) * z1 + (m.a12 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ))) (-e.1)
    rw [abs_neg] at t
    have hr : ((ceilDiv (m.a11.natAbs + m.a12.natAbs) misShift + err : ℕ) : ℝ) / (scaleE : ℝ) =
        (ceilDiv (m.a11.natAbs + m.a12.natAbs) misShift : ℝ) / (scaleE : ℝ)
          + (err : ℝ) / (scaleE : ℝ) := by
      push_cast
      ring
    rw [e1, hr]
    linarith
  have v2 : |(((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).2.1| ≤
      ((ceilDiv (m.a21.natAbs + m.a22.natAbs) misShift + g * err : ℕ) : ℝ) / scaleE := by
    have e1 : (((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).2.1 =
        ((m.a21 : ℝ) * z1 + (m.a22 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ))
          + -((g : ℝ) * e.2.1) := by
      simp only [Mat32.app, resc, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    have t := abs_add_le
      (((m.a21 : ℝ) * z1 + (m.a22 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ)))
      (-((g : ℝ) * e.2.1))
    rw [abs_neg, abs_mul, abs_of_nonneg hg0] at t
    have ge : (g : ℝ) * |e.2.1| ≤ (g : ℝ) * ((err : ℝ) / scaleE) :=
      mul_le_mul_of_nonneg_left he2 hg0
    have hr : ((ceilDiv (m.a21.natAbs + m.a22.natAbs) misShift + g * err : ℕ) : ℝ) /
        (scaleE : ℝ) =
        (ceilDiv (m.a21.natAbs + m.a22.natAbs) misShift : ℝ) / (scaleE : ℝ)
          + (g : ℝ) * ((err : ℝ) / (scaleE : ℝ)) := by
      push_cast
      ring
    rw [e1, hr]
    linarith
  have v3 : |(((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).2.2| ≤
      ((ceilDiv (m.a31.natAbs + m.a32.natAbs) misShift + g * g * err : ℕ) : ℝ) / scaleE := by
    have e1 : (((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e).2.2 =
        ((m.a31 : ℝ) * z1 + (m.a32 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ))
          + -((g : ℝ) * (g : ℝ) * e.2.2) := by
      simp only [Mat32.app, resc, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      ring
    have t := abs_add_le
      (((m.a31 : ℝ) * z1 + (m.a32 : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ)))
      (-((g : ℝ) * (g : ℝ) * e.2.2))
    rw [abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hg0 hg0)] at t
    have ge : (g : ℝ) * (g : ℝ) * |e.2.2| ≤ (g : ℝ) * (g : ℝ) * ((err : ℝ) / scaleE) :=
      mul_le_mul_of_nonneg_left he3 (mul_nonneg hg0 hg0)
    have hr : ((ceilDiv (m.a31.natAbs + m.a32.natAbs) misShift + g * g * err : ℕ) : ℝ) /
        (scaleE : ℝ) =
        (ceilDiv (m.a31.natAbs + m.a32.natAbs) misShift : ℝ) / (scaleE : ℝ)
          + (g : ℝ) * (g : ℝ) * ((err : ℝ) / (scaleE : ℝ)) := by
      push_cast
      ring
    rw [e1, hr]
    linarith
  obtain ⟨q1, q2, q3⟩ := Bn.adj.abs_app_le
    (ν := ⟨ceilDiv (m.a11.natAbs + m.a12.natAbs) misShift + err,
      ceilDiv (m.a21.natAbs + m.a22.natAbs) misShift + g * err,
      ceilDiv (m.a31.natAbs + m.a32.natAbs) misShift + g * g * err⟩) v1 v2 v3
  -- the two parts together
  have hnat : 0 < B.det.toNat * scaleU := Nat.mul_pos (by omega) scaleU_pos_nat
  have hcast : ((B.det.toNat * scaleU : ℕ) : ℝ) = (B.det : ℝ) * (scaleU : ℝ) := by
    have h1 : ((B.det.toNat : ℕ) : Int) = B.det := Int.toNat_of_nonneg hd.le
    have h2 : ((B.det.toNat : ℕ) : ℝ) = (B.det : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_mul, h2]
  have c1 := div_le_ceilDiv (((Bn.adj.mul DT).mul B).absApply ρ).a hnat
  have c2 := div_le_ceilDiv (((Bn.adj.mul DT).mul B).absApply ρ).b hnat
  have c3 := div_le_ceilDiv (((Bn.adj.mul DT).mul B).absApply ρ).c hnat
  rw [hcast] at c1 c2 c3
  have hvec : Bn.adj.app ((scaleU : ℝ)⁻¹ • DT.app r
        + ((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e) =
      (scaleU : ℝ)⁻¹ • Bn.adj.app (DT.app r)
        + Bn.adj.app (((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • m.app z1 z2 - resc (g : ℝ) e) := by
    rw [add_sub_assoc, Mat3.app_add, Mat3.app_smul]
  unfold Inv
  rw [hvec]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.cast_add]
    exact final_component hdR hSu hE m1 q1 c1
  · rw [Nat.cast_add]
    exact final_component hdR hSu hE m2 q2 c2
  · rw [Nat.cast_add]
    exact final_component hdR hSu hE m3 q3 c3

end Calabi.Shot
