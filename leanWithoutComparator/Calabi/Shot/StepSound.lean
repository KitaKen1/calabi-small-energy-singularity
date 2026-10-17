import Calabi.Shot.StepBounds
import Calabi.Shot.Certified

/-!
# Soundness of one step of the chain

If the kernel's `step` returns `ρ'`, then for every parameter in the box and
every trajectory of the clamped block system whose jet at `t = -1` is

  `start / scaleP + L z / scaleU + r`,   with `|adj(B) r| ≤ ρ / scaleE`,

the trajectory keeps the clamp inactive, and its jet at `t = 1`, expressed in
the next block's variable, is

  `stop' / scaleP + L' z / scaleU + r'`,   with `|adj(B') r'| ≤ ρ' / scaleE`.
-/

open Set

namespace Calabi.Shot

/-- The parameter `d` at the point `(z₁, z₂)` of the box. -/
noncomputable def param (dnum dz1 dz2 : Int) (z1 z2 : ℝ) : ℝ :=
  (dnum : ℝ) / scaleP + ((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / scaleU

theorem step_unpack {dz1 dz2 : Int} {s : Summary} {g : ℕ} {B Bn : Mat3} {L Ln : Mat32}
    {ρ ρn : Nat3} (h : step dz1 dz2 s g B Bn L Ln ρ = some ρn) :
    0 < B.det ∧ 0 < Bn.det ∧ deviation dz1 dz2 B L ρ ≤ scaleE / 1024 ∧
      s.eps ≤ scaleE / 1024 ∧
      ρn = ⟨ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).a
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply
              (injected dz1 dz2 s g L Ln (blockErr s (deviation dz1 dz2 B L ρ)))).a,
        ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).b
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply
              (injected dz1 dz2 s g L Ln (blockErr s (deviation dz1 dz2 B L ρ)))).b,
        ceilDiv (((Bn.adj.mul ((transfer s).rescale g)).mul B).absApply ρ).c
            (B.det.toNat * scaleU)
          + (Bn.adj.absApply
              (injected dz1 dz2 s g L Ln (blockErr s (deviation dz1 dz2 B L ρ)))).c⟩ := by
  simp only [step] at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨h1, h2, h3, h4, (Option.some.inj h).symm⟩
  · cases h

/-- The remainder after one block, in terms of the remainder before it. -/
theorem remainder_identity (dz1 dz2 : Int) (s : Summary) (g : Int) (L Ln : Mat32)
    (z1 z2 : ℝ) (r e : State) :
    resc (g : ℝ) ((scaleP : ℝ)⁻¹ • jetVec s.stop
          + (scaleU : ℝ)⁻¹ • ((transfer s).app ((scaleU : ℝ)⁻¹ • L.app z1 z2 + r)
            + (((dz1 : ℝ) * z1 + (dz2 : ℝ) * z2) / (scaleU : ℝ)) • jetVec s.td) - e)
        - (scaleP : ℝ)⁻¹ • resc (g : ℝ) (jetVec s.stop) - (scaleU : ℝ)⁻¹ • Ln.app z1 z2 =
      (scaleU : ℝ)⁻¹ • ((transfer s).rescale g).app r
        + ((scaleU : ℝ) * (scaleU : ℝ))⁻¹ • (mismatch dz1 dz2 s g L Ln).app z1 z2
        - resc (g : ℝ) e := by
  have hS : (scaleP : ℝ) ≠ 0 := scaleP_pos.ne'
  have hSu : (scaleU : ℝ) ≠ 0 := scaleU_pos.ne'
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [resc, jetVec, transfer, Mat3.app, Mat32.app, Mat3.rescale, mismatch,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast] <;>
    field_simp <;> ring

theorem final_component {δ Su E u bv p q c : ℝ} (hδ : 0 < δ) (hSu : 0 < Su) (hE : 0 < E)
    (hu : δ * |u| ≤ p / E) (hb : |bv| ≤ q / E) (hc : p / (δ * Su) ≤ c) :
    |Su⁻¹ * u + bv| ≤ (c + q) / E := by
  have h1 : |Su⁻¹ * u + bv| ≤ Su⁻¹ * |u| + |bv| := by
    have t := abs_add_le (Su⁻¹ * u) bv
    rw [abs_mul, abs_of_pos (inv_pos.2 hSu)] at t
    exact t
  have h2 : Su⁻¹ * |u| ≤ c / E := by
    rw [le_div_iff₀ hE]
    have a1 : δ * |u| * E ≤ p := by rwa [le_div_iff₀ hE] at hu
    have a2 : p ≤ c * (δ * Su) := by rwa [div_le_iff₀ (mul_pos hδ hSu)] at hc
    have a3 : (δ * Su) * (Su⁻¹ * |u| * E) ≤ (δ * Su) * c := by
      have e : (δ * Su) * (Su⁻¹ * |u| * E) = δ * |u| * E := by
        have hSu0 := hSu.ne'
        field_simp
      rw [e]
      linarith
    exact le_of_mul_le_mul_left a3 (mul_pos hδ hSu)
  rw [add_div]
  linarith

end Calabi.Shot
