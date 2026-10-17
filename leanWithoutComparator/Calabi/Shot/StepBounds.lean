import Calabi.Shot.FrameAlgebra

/-!
# Real bounds behind one step of the chain

Each lemma turns one natural-number expression of `Calabi.Shot.step` into the
real inequality it stands for. The parameter box is `|z₁|, |z₂| ≤ 2^-56`.
-/

namespace Calabi.Shot

theorem boxShift_pos_nat : 0 < boxShift := by
  unfold boxShift
  positivity

theorem misShift_pos_nat : 0 < misShift := by
  unfold misShift
  positivity

/-- `2^64 · 2^56 · 2^40 = 2^160`. -/
theorem scale_box : (scaleU : ℝ) * 2 ^ 56 * (boxShift : ℝ) = (scaleE : ℝ) := by
  unfold scaleU boxShift scaleE
  norm_num

/-- `2^64 · 2^64 · 2^56 = 2^24 · 2^160`. -/
theorem scale_mis : (scaleU : ℝ) * (scaleU : ℝ) * 2 ^ 56 = (misShift : ℝ) * (scaleE : ℝ) := by
  unfold scaleU misShift scaleE
  norm_num

/-- `|adj(B) r| ≤ ρ / scaleE` componentwise. -/
def Inv (B : Mat3) (ρ : Nat3) (r : State) : Prop :=
  |(B.adj.app r).1| ≤ (ρ.a : ℝ) / scaleE ∧ |(B.adj.app r).2.1| ≤ (ρ.b : ℝ) / scaleE ∧
    |(B.adj.app r).2.2| ≤ (ρ.c : ℝ) / scaleE

theorem abs_le_of_mul_le {δ x a E c : ℝ} (hδ : 0 < δ) (hE : 0 < E) (h : δ * |x| ≤ a / E)
    (hc : a / δ ≤ c) : |x| ≤ c / E := by
  rw [le_div_iff₀ hE]
  have h1 : δ * |x| * E ≤ a := by rwa [le_div_iff₀ hE] at h
  have h2 : a ≤ c * δ := by rwa [div_le_iff₀ hδ] at hc
  have h3 : δ * (|x| * E) ≤ δ * c := by linarith
  exact le_of_mul_le_mul_left h3 hδ

/-- The invariant bounds the remainder itself by `radius`. -/
theorem Inv.abs_le {B : Mat3} {ρ : Nat3} {r : State} (h : Inv B ρ r) (hd : 0 < B.det) :
    |r.1| ≤ ((radius B ρ).a : ℝ) / scaleE ∧ |r.2.1| ≤ ((radius B ρ).b : ℝ) / scaleE ∧
      |r.2.2| ≤ ((radius B ρ).c : ℝ) / scaleE := by
  have hE := scaleE_pos
  have hdR : (0 : ℝ) < (B.det : ℝ) := by exact_mod_cast hd
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hb1, hb2, hb3⟩ := B.abs_app_le h1 h2 h3
  rw [B.app_adj r] at hb1 hb2 hb3
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos hdR] at hb1 hb2 hb3
  have hnat : 0 < B.det.toNat := by omega
  have hcast : ((B.det.toNat : ℕ) : ℝ) = (B.det : ℝ) := by
    have h1 : ((B.det.toNat : ℕ) : Int) = B.det := Int.toNat_of_nonneg hd.le
    exact_mod_cast h1
  have c1 := div_le_ceilDiv (B.absApply ρ).a hnat
  have c2 := div_le_ceilDiv (B.absApply ρ).b hnat
  have c3 := div_le_ceilDiv (B.absApply ρ).c hnat
  rw [hcast] at c1 c2 c3
  exact ⟨abs_le_of_mul_le hdR hE hb1 c1, abs_le_of_mul_le hdR hE hb2 c2,
    abs_le_of_mul_le hdR hE hb3 c3⟩

theorem lin2_abs_le (a b : ℝ) {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56) :
    |a * z1 + b * z2| ≤ (|a| + |b|) * (1 / 2 ^ 56) := by
  have e1 : |a * z1| ≤ |a| * (1 / 2 ^ 56) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz1 (abs_nonneg _)
  have e2 : |b * z2| ≤ |b| * (1 / 2 ^ 56) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz2 (abs_nonneg _)
  have t := abs_add_le (a * z1) (b * z2)
  linarith

/-- A response entry times the box, over `scaleU`, in the scale of `ρ`. -/
theorem lin2_bound (a b : Int) {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56) :
    |((a : ℝ) * z1 + (b : ℝ) * z2) / (scaleU : ℝ)| ≤
      (((a.natAbs + b.natAbs) * boxShift : ℕ) : ℝ) / (scaleE : ℝ) := by
  have hSu := scaleU_pos
  have hE := scaleE_pos
  have h1 := lin2_abs_le (a : ℝ) (b : ℝ) hz1 hz2
  have hc : (((a.natAbs + b.natAbs) * boxShift : ℕ) : ℝ) =
      (|(a : ℝ)| + |(b : ℝ)|) * (boxShift : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
  rw [hc, abs_div, abs_of_pos hSu, div_le_div_iff₀ hSu hE]
  calc |(a : ℝ) * z1 + (b : ℝ) * z2| * (scaleE : ℝ)
      ≤ (|(a : ℝ)| + |(b : ℝ)|) * (1 / 2 ^ 56) * (scaleE : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ = (|(a : ℝ)| + |(b : ℝ)|) * (boxShift : ℝ) * (scaleU : ℝ) := by
        rw [← scale_box]
        ring

/-- A mismatch entry times the box, over `scaleU²`, in the scale of `ρ`. -/
theorem mis_bound (a b : Int) {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56) :
    |((a : ℝ) * z1 + (b : ℝ) * z2) / ((scaleU : ℝ) * (scaleU : ℝ))| ≤
      (ceilDiv (a.natAbs + b.natAbs) misShift : ℝ) / (scaleE : ℝ) := by
  have hSu := scaleU_pos
  have hE := scaleE_pos
  have hms : (0 : ℝ) < (misShift : ℝ) := by exact_mod_cast misShift_pos_nat
  have h1 := lin2_abs_le (a : ℝ) (b : ℝ) hz1 hz2
  have hc : ((a.natAbs + b.natAbs : ℕ) : ℝ) = |(a : ℝ)| + |(b : ℝ)| := by
    simp only [Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
  have c := div_le_ceilDiv (a.natAbs + b.natAbs) misShift_pos_nat
  rw [hc, div_le_iff₀ hms] at c
  rw [abs_div, abs_of_pos (mul_pos hSu hSu), div_le_div_iff₀ (mul_pos hSu hSu) hE]
  have h2 : |(a : ℝ) * z1 + (b : ℝ) * z2| * (scaleE : ℝ) * (misShift : ℝ) ≤
      (ceilDiv (a.natAbs + b.natAbs) misShift : ℝ) * ((scaleU : ℝ) * (scaleU : ℝ)) *
        (misShift : ℝ) := by
    calc |(a : ℝ) * z1 + (b : ℝ) * z2| * (scaleE : ℝ) * (misShift : ℝ)
        ≤ (|(a : ℝ)| + |(b : ℝ)|) * (1 / 2 ^ 56) * (scaleE : ℝ) * (misShift : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE.le) hms.le
      _ = (|(a : ℝ)| + |(b : ℝ)|) * ((scaleU : ℝ) * (scaleU : ℝ)) := by
          have e := scale_mis
          have e2 : (|(a : ℝ)| + |(b : ℝ)|) * (1 / 2 ^ 56) * (scaleE : ℝ) * (misShift : ℝ) =
              (|(a : ℝ)| + |(b : ℝ)|) * (1 / 2 ^ 56) * ((misShift : ℝ) * (scaleE : ℝ)) := by ring
          rw [e2, ← e]
          ring
      _ ≤ (ceilDiv (a.natAbs + b.natAbs) misShift : ℝ) * (misShift : ℝ) *
            ((scaleU : ℝ) * (scaleU : ℝ)) :=
          mul_le_mul_of_nonneg_right c (mul_pos hSu hSu).le
      _ = _ := by ring
  exact le_of_mul_le_mul_right h2 hms

/-- The real error of a block is at most the kernel's `blockErr`. -/
theorem blockErr_bound (s : Summary) (y : ℕ) {yR : ℝ} (hy0 : 0 ≤ yR)
    (hy : yR ≤ (y : ℝ) / (scaleE : ℝ)) :
    8 * ((s.eps : ℝ) / scaleE + 1 / 2 ^ 40 * yR + 14 * yR ^ 2) ≤
      (blockErr s y : ℝ) / (scaleE : ℝ) := by
  have hE := scaleE_pos
  have c1 : (y : ℝ) ≤ (ceilDiv y (2 ^ 40) : ℝ) * 2 ^ 40 := by
    have h := le_ceilDiv_mul y (show 0 < 2 ^ 40 by norm_num)
    exact_mod_cast h
  have c2 := div_le_ceilDiv (14 * y * y) scaleE_pos_nat
  push_cast at c2
  have hsq : yR ^ 2 ≤ ((y : ℝ) / (scaleE : ℝ)) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have e1 : 1 / 2 ^ 40 * yR ≤ (ceilDiv y (2 ^ 40) : ℝ) / (scaleE : ℝ) := by
    rw [le_div_iff₀ hE]
    have h1 : yR * (scaleE : ℝ) ≤ (y : ℝ) := by rwa [le_div_iff₀ hE] at hy
    have h3 : yR * (scaleE : ℝ) ≤ (ceilDiv y (2 ^ 40) : ℝ) * 2 ^ 40 := h1.trans c1
    calc 1 / 2 ^ 40 * yR * (scaleE : ℝ) = 1 / 2 ^ 40 * (yR * (scaleE : ℝ)) := by ring
      _ ≤ 1 / 2 ^ 40 * ((ceilDiv y (2 ^ 40) : ℝ) * 2 ^ 40) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (ceilDiv y (2 ^ 40) : ℝ) := by ring
  have e2 : 14 * yR ^ 2 ≤ (ceilDiv (14 * y * y) scaleE : ℝ) / (scaleE : ℝ) := by
    have h1 : 14 * ((y : ℝ) / (scaleE : ℝ)) ^ 2 = 14 * (y : ℝ) * (y : ℝ) / (scaleE : ℝ) /
        (scaleE : ℝ) := by
      field_simp
    have h2 : 14 * (y : ℝ) * (y : ℝ) / (scaleE : ℝ) / (scaleE : ℝ) ≤
        (ceilDiv (14 * y * y) scaleE : ℝ) / (scaleE : ℝ) :=
      div_le_div_of_nonneg_right c2 hE.le
    linarith
  have e3 : (blockErr s y : ℝ) / (scaleE : ℝ) =
      8 * ((s.eps : ℝ) / scaleE + (ceilDiv y (2 ^ 40) : ℝ) / scaleE
        + (ceilDiv (14 * y * y) scaleE : ℝ) / scaleE) := by
    unfold blockErr
    push_cast
    ring
  rw [e3]
  linarith

end Calabi.Shot
