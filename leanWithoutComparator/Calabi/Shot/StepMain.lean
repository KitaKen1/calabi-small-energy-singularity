import Calabi.Shot.StepCore

/-!
# One step of the chain is sound

`step_sound` joins the three ingredients: the kernel-checked block
(`block_spec`), the frame algebra (`step_core`) and the identity that
expresses the new remainder through the old one (`remainder_identity`).
-/

open Set

namespace Calabi.Shot

theorem step_sound {dnum dz1 dz2 : Int} {s : Summary} {g : ℕ} {B Bn : Mat3} {L Ln : Mat32}
    {ρ ρn : Nat3} (hs : ∃ b, summarize dnum b = some s)
    (hstep : step dz1 dz2 s g B Bn L Ln ρ = some ρn)
    {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56)
    {r : State} (hr : Inv B ρ r)
    {X : ℝ → State} (hX : ContinuousOn X (Icc (-1) 1))
    (hX' : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt X
      (field (s.H : ℝ) (s.A : ℝ) (param dnum dz1 dz2 z1 z2) t (X t)) (Ici t) t)
    (h0 : X (-1) = (scaleP : ℝ)⁻¹ • jetVec s.start + (scaleU : ℝ)⁻¹ • L.app z1 z2 + r) :
    (∀ t ∈ Icc (-1 : ℝ) 1, -19 / 20 ≤ (X t).1) ∧
      Inv Bn ρn (resc (g : ℝ) (X 1) - (scaleP : ℝ)⁻¹ • resc (g : ℝ) (jetVec s.stop)
        - (scaleU : ℝ)⁻¹ • Ln.app z1 z2) := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨hd, hdn, hy, heps, hρ⟩ := step_unpack hstep
  subst hρ
  have hS := scaleP_pos
  have hSu := scaleU_pos
  have hE := scaleE_pos
  -- the deviation on this block
  obtain ⟨r1, r2, r3⟩ := hr.abs_le hd
  have l1 := lin2_bound L.a11 L.a12 hz1 hz2
  have l2 := lin2_bound L.a21 L.a22 hz1 hz2
  have l3 := lin2_bound L.a31 L.a32 hz1 hz2
  have l4 := lin2_bound dz1 dz2 hz1 hz2
  have x1 : ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).1 =
      ((L.a11 : ℝ) * z1 + (L.a12 : ℝ) * z2) / (scaleU : ℝ) + r.1 := by
    simp only [Mat32.app, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    ring
  have x2 : ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.1 =
      ((L.a21 : ℝ) * z1 + (L.a22 : ℝ) * z2) / (scaleU : ℝ) + r.2.1 := by
    simp only [Mat32.app, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have x3 : ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.2 =
      ((L.a31 : ℝ) * z1 + (L.a32 : ℝ) * z2) / (scaleU : ℝ) + r.2.2 := by
    simp only [Mat32.app, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    ring
  have hdev : ((deviation dz1 dz2 B L ρ : ℕ) : ℝ) =
      (((L.a11.natAbs + L.a12.natAbs) * boxShift : ℕ) : ℝ)
        + (((L.a21.natAbs + L.a22.natAbs) * boxShift : ℕ) : ℝ)
        + (((L.a31.natAbs + L.a32.natAbs) * boxShift : ℕ) : ℝ)
        + (((radius B ρ).a : ℝ) + ((radius B ρ).b : ℝ) + ((radius B ρ).c : ℝ))
        + (((dz1.natAbs + dz2.natAbs) * boxShift : ℕ) : ℝ) := by
    simp only [deviation, radius]
    push_cast
    ring
  have b1 := (abs_add_le (((L.a11 : ℝ) * z1 + (L.a12 : ℝ) * z2) / (scaleU : ℝ)) r.1).trans
    (add_le_add l1 r1)
  have b2 := (abs_add_le (((L.a21 : ℝ) * z1 + (L.a22 : ℝ) * z2) / (scaleU : ℝ)) r.2.1).trans
    (add_le_add l2 r2)
  have b3 := (abs_add_le (((L.a31 : ℝ) * z1 + (L.a32 : ℝ) * z2) / (scaleU : ℝ)) r.2.2).trans
    (add_le_add l3 r3)
  have hyR : |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).1| + |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.1|
      + |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.2|
      + |((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)| ≤
      ((deviation dz1 dz2 B L ρ : ℕ) : ℝ) / (scaleE : ℝ) := by
    rw [x1, x2, x3]
    refine (add_le_add (add_le_add (add_le_add b1 b2) b3) l4).trans (le_of_eq ?_)
    rw [hdev]
    ring
  have hy0 : 0 ≤ |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).1|
      + |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.1| + |((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.2|
      + |((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)| := by positivity
  have hy1024 := div_le_of_le_div scaleE_pos_nat hy
  have heps1024 := div_le_of_le_div scaleE_pos_nat heps
  -- the block
  have hX'' : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt X
      (field (s.H : ℝ) (s.A : ℝ)
        ((dnum : ℝ) / scaleP + ((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / scaleU) t (X t)) (Ici t) t :=
    hX'
  have h0' : X (-1) =
      ((s.start.v : ℝ) / scaleP + ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).1,
        (s.start.d1 : ℝ) / scaleP + ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.1,
        (s.start.d2 : ℝ) / scaleP + ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r).2.2) := by
    rw [h0]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [jetVec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
  obtain ⟨hpos, hdist⟩ := block_spec hb heps1024 (hyR.trans hy1024) hX hX'' h0'
  refine ⟨hpos, ?_⟩
  -- the error of the block as a vector
  have hErr := blockErr_bound s (deviation dz1 dz2 B L ρ) hy0 hyR
  obtain ⟨d1, d2, d3⟩ := State.dist_le_iff.1 (hdist.trans hErr)
  have he1 : |((scaleP : ℝ)⁻¹ • jetVec s.stop
      + (scaleU : ℝ)⁻¹ • ((transfer s).app ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r)
        + (((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)) • jetVec s.td) - X 1).1| ≤
      (blockErr s (deviation dz1 dz2 B L ρ) : ℝ) / scaleE := by
    convert d1 using 2
    simp only [jetVec, transfer, Mat3.app, Prod.fst_sub, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul]
    ring
  have he2 : |((scaleP : ℝ)⁻¹ • jetVec s.stop
      + (scaleU : ℝ)⁻¹ • ((transfer s).app ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r)
        + (((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)) • jetVec s.td) - X 1).2.1| ≤
      (blockErr s (deviation dz1 dz2 B L ρ) : ℝ) / scaleE := by
    convert d2 using 2
    simp only [jetVec, transfer, Mat3.app, Prod.fst_sub, Prod.snd_sub, Prod.fst_add,
      Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have he3 : |((scaleP : ℝ)⁻¹ • jetVec s.stop
      + (scaleU : ℝ)⁻¹ • ((transfer s).app ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r)
        + (((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)) • jetVec s.td) - X 1).2.2| ≤
      (blockErr s (deviation dz1 dz2 B L ρ) : ℝ) / scaleE := by
    convert d3 using 2
    simp only [jetVec, transfer, Mat3.app, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- the frame algebra
  have hcore := step_core (dz1 := dz1) (dz2 := dz2) (s := s) (g := g) (Bn := Bn) (L := L)
    (Ln := Ln) hd hz1 hz2 hr he1 he2 he3
  have hid := remainder_identity dz1 dz2 s (g : Int) L Ln z1 z2 r
    ((scaleP : ℝ)⁻¹ • jetVec s.stop
      + (scaleU : ℝ)⁻¹ • ((transfer s).app ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r)
        + (((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)) • jetVec s.td) - X 1)
  rw [sub_sub_cancel] at hid
  simp only [Int.cast_natCast] at hid
  rw [hid]
  exact hcore

end Calabi.Shot
