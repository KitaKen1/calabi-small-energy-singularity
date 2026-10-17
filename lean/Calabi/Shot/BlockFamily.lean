import Calabi.Shot.BlockODE
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# A family of approximate solutions on one block

Given an approximate solution `P` of the profile equation and four approximate
solutions `U0, U1, U2, Ud` of the equation linearised along `P`, the function

  `P + ξ₀ U0 + ξ₁ U1 + ξ₂ U2 + η Ud`

is an approximate solution for the parameter `d + η`, with a defect that is
the sum of the individual defects and a quadratic term. The block comparison
lemma then encloses the true trajectory with the same data at `t = -1`.
-/

open Set

namespace Calabi.Shot

/-- A real function with three successive derivatives. -/
structure Jet3 where
  f : ℝ → ℝ
  f1 : ℝ → ℝ
  f2 : ℝ → ℝ
  f3 : ℝ → ℝ
  h0 : ∀ t, HasDerivAt f (f1 t) t
  h1 : ∀ t, HasDerivAt f1 (f2 t) t
  h2 : ∀ t, HasDerivAt f2 (f3 t) t

/-- Defect of `P` in the profile equation with parameter `d`. -/
noncomputable def Jet3.defect (P : Jet3) (H A d t : ℝ) : ℝ :=
  P.f3 t + 21 / (A + t) * P.f2 t + 337 / (4 * (A + t) ^ 2) * P.f1 t
    - 567 / (4 * (A + t) ^ 3) * (P.f t - d) + P.f t / (1 + P.f t) / H ^ 3

/-- Defect of `U` in the equation linearised along `P`; `φ` is the forcing
coming from the parameter (`1` for the parameter tangent, `0` otherwise). -/
noncomputable def Jet3.linDefect (U P : Jet3) (H A φ t : ℝ) : ℝ :=
  U.f3 t + 21 / (A + t) * U.f2 t + 337 / (4 * (A + t) ^ 2) * U.f1 t
    - 567 / (4 * (A + t) ^ 3) * (U.f t - φ) + U.f t / (1 + P.f t) ^ 2 / H ^ 3

theorem defect_identity {c2 c1 c0 H3 d η p p1 p2 p3 w w1 w2 w3 : ℝ}
    (hH : H3 ≠ 0) (hu : 1 + p ≠ 0) (huw : 1 + (p + w) ≠ 0) :
    (p3 + w3) + c2 * (p2 + w2) + c1 * (p1 + w1) - c0 * ((p + w) - (d + η))
        + (p + w) / (1 + (p + w)) / H3 =
      (p3 + c2 * p2 + c1 * p1 - c0 * (p - d) + p / (1 + p) / H3)
        + (w3 + c2 * w2 + c1 * w1 - c0 * (w - η) + w / (1 + p) ^ 2 / H3)
        - w ^ 2 / ((1 + p) ^ 2 * (1 + (p + w))) / H3 := by
  field_simp
  ring1

/-- **Family enclosure on a block.** -/
theorem block_family {H A d ξ₀ ξ₁ ξ₂ η εP εU : ℝ} (hH : 16 ≤ H) (hA : 129 ≤ A)
    (P U0 U1 U2 Ud : Jet3)
    (hP : ∀ t ∈ Icc (-1 : ℝ) 1, 7 / 100 ≤ 1 + P.f t)
    (hU0 : ∀ t ∈ Icc (-1 : ℝ) 1, |U0.f t| ≤ 4)
    (hU1 : ∀ t ∈ Icc (-1 : ℝ) 1, |U1.f t| ≤ 4)
    (hU2 : ∀ t ∈ Icc (-1 : ℝ) 1, |U2.f t| ≤ 4)
    (hUd : ∀ t ∈ Icc (-1 : ℝ) 1, |Ud.f t| ≤ 4)
    (hdP : ∀ t ∈ Icc (-1 : ℝ) 1, |P.defect H A d t| ≤ εP)
    (hd0 : ∀ t ∈ Icc (-1 : ℝ) 1, |U0.linDefect P H A 0 t| ≤ εU)
    (hd1 : ∀ t ∈ Icc (-1 : ℝ) 1, |U1.linDefect P H A 0 t| ≤ εU)
    (hd2 : ∀ t ∈ Icc (-1 : ℝ) 1, |U2.linDefect P H A 0 t| ≤ εU)
    (hdd : ∀ t ∈ Icc (-1 : ℝ) 1, |Ud.linDefect P H A 1 t| ≤ εU)
    (hy : |ξ₀| + |ξ₁| + |ξ₂| + |η| ≤ 1 / 1024)
    {X : ℝ → State} (hX : ContinuousOn X (Icc (-1) 1))
    (hX' : ∀ t ∈ Ico (-1 : ℝ) 1,
      HasDerivWithinAt X (field H A (d + η) t (X t)) (Ici t) t)
    (h0 : X (-1) =
      (P.f (-1) + (ξ₀ * U0.f (-1) + ξ₁ * U1.f (-1) + ξ₂ * U2.f (-1) + η * Ud.f (-1)),
        P.f1 (-1) + (ξ₀ * U0.f1 (-1) + ξ₁ * U1.f1 (-1) + ξ₂ * U2.f1 (-1) + η * Ud.f1 (-1)),
        P.f2 (-1) + (ξ₀ * U0.f2 (-1) + ξ₁ * U1.f2 (-1) + ξ₂ * U2.f2 (-1) + η * Ud.f2 (-1)))) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      dist ((P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t),
          P.f1 t + (ξ₀ * U0.f1 t + ξ₁ * U1.f1 t + ξ₂ * U2.f1 t + η * Ud.f1 t),
          P.f2 t + (ξ₀ * U0.f2 t + ξ₁ * U1.f2 t + ξ₂ * U2.f2 t + η * Ud.f2 t)) : State) (X t) ≤
        8 * (εP + εU * (|ξ₀| + |ξ₁| + |ξ₂| + |η|)
          + 14 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2) := by
  have hy0 : 0 ≤ |ξ₀| + |ξ₁| + |ξ₂| + |η| := by positivity
  have hmem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hεU : 0 ≤ εU := (abs_nonneg _).trans (hd0 (-1) hmem)
  have hH0 : (0 : ℝ) < H := by linarith
  have hH2 : (256 : ℝ) ≤ H ^ 2 := by
    have := mul_le_mul hH hH (by norm_num) hH0.le
    nlinarith
  have hH3 : (4096 : ℝ) ≤ H ^ 3 := by
    calc (4096 : ℝ) = 256 * 16 := by norm_num
      _ ≤ H ^ 2 * H := mul_le_mul hH2 hH (by norm_num) (by positivity)
      _ = H ^ 3 := by ring
  have hH3pos : (0 : ℝ) < H ^ 3 := pow_pos hH0 3
  refine block_compare (ε := εP + εU * (|ξ₀| + |ξ₁| + |ξ₂| + |η|)
      + 14 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2) hH hA
    (q := fun t => P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))
    (q1 := fun t => P.f1 t + (ξ₀ * U0.f1 t + ξ₁ * U1.f1 t + ξ₂ * U2.f1 t + η * Ud.f1 t))
    (q2 := fun t => P.f2 t + (ξ₀ * U0.f2 t + ξ₁ * U1.f2 t + ξ₂ * U2.f2 t + η * Ud.f2 t))
    (q3 := fun t => P.f3 t + (ξ₀ * U0.f3 t + ξ₁ * U1.f3 t + ξ₂ * U2.f3 t + η * Ud.f3 t))
    (fun t => (P.h0 t).fun_add
      (((((U0.h0 t).const_mul ξ₀).fun_add ((U1.h0 t).const_mul ξ₁)).fun_add
        ((U2.h0 t).const_mul ξ₂)).fun_add ((Ud.h0 t).const_mul η)))
    (fun t => (P.h1 t).fun_add
      (((((U0.h1 t).const_mul ξ₀).fun_add ((U1.h1 t).const_mul ξ₁)).fun_add
        ((U2.h1 t).const_mul ξ₂)).fun_add ((Ud.h1 t).const_mul η)))
    (fun t => (P.h2 t).fun_add
      (((((U0.h2 t).const_mul ξ₀).fun_add ((U1.h2 t).const_mul ξ₁)).fun_add
        ((U2.h2 t).const_mul ξ₂)).fun_add ((Ud.h2 t).const_mul η)))
    ?_ hX hX' h0
  intro t ht
  have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hu := hP t htI
  -- size of the tangent combination
  have hW : |ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t| ≤
      4 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) := by
    have a0 : |ξ₀ * U0.f t| ≤ |ξ₀| * 4 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hU0 t htI) (abs_nonneg _)
    have a1 : |ξ₁ * U1.f t| ≤ |ξ₁| * 4 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hU1 t htI) (abs_nonneg _)
    have a2 : |ξ₂ * U2.f t| ≤ |ξ₂| * 4 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hU2 t htI) (abs_nonneg _)
    have a3 : |η * Ud.f t| ≤ |η| * 4 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hUd t htI) (abs_nonneg _)
    obtain ⟨a0l, a0u⟩ := abs_le.1 a0
    obtain ⟨a1l, a1u⟩ := abs_le.1 a1
    obtain ⟨a2l, a2u⟩ := abs_le.1 a2
    obtain ⟨a3l, a3u⟩ := abs_le.1 a3
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hWl, hWu⟩ := abs_le.1 hW
  have huw : 6 / 100 ≤
      1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)) := by
    linarith
  have hN : Ntr (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)) =
      (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)) /
        (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))) :=
    Ntr_of_ge (by linarith)
  have hid := defect_identity (c2 := 21 / (A + t)) (c1 := 337 / (4 * (A + t) ^ 2))
    (c0 := 567 / (4 * (A + t) ^ 3)) (H3 := H ^ 3) (d := d) (η := η)
    (p := P.f t) (p1 := P.f1 t) (p2 := P.f2 t) (p3 := P.f3 t)
    (w := ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)
    (w1 := ξ₀ * U0.f1 t + ξ₁ * U1.f1 t + ξ₂ * U2.f1 t + η * Ud.f1 t)
    (w2 := ξ₀ * U0.f2 t + ξ₁ * U1.f2 t + ξ₂ * U2.f2 t + η * Ud.f2 t)
    (w3 := ξ₀ * U0.f3 t + ξ₁ * U1.f3 t + ξ₂ * U2.f3 t + η * Ud.f3 t)
    hH3pos.ne' (show (0 : ℝ) < 1 + P.f t by linarith).ne'
    (show (0 : ℝ) < 1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))
      by linarith).ne'
  have key : defectTr H A (d + η)
      (fun t => P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))
      (fun t => P.f1 t + (ξ₀ * U0.f1 t + ξ₁ * U1.f1 t + ξ₂ * U2.f1 t + η * Ud.f1 t))
      (fun t => P.f2 t + (ξ₀ * U0.f2 t + ξ₁ * U1.f2 t + ξ₂ * U2.f2 t + η * Ud.f2 t))
      (fun t => P.f3 t + (ξ₀ * U0.f3 t + ξ₁ * U1.f3 t + ξ₂ * U2.f3 t + η * Ud.f3 t)) t =
      P.defect H A d t + ξ₀ * U0.linDefect P H A 0 t + ξ₁ * U1.linDefect P H A 0 t
        + ξ₂ * U2.linDefect P H A 0 t + η * Ud.linDefect P H A 1 t
        - (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t) ^ 2 /
            ((1 + P.f t) ^ 2 *
              (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)))) /
            H ^ 3 := by
    simp only [defectTr, Jet3.defect, Jet3.linDefect]
    rw [hN]
    linear_combination hid
  -- the quadratic term
  have hsq : (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t) ^ 2 ≤
      16 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2 := by
    calc (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t) ^ 2
        ≤ (4 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|)) ^ 2 := sq_le_sq' hWl hWu
      _ = 16 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2 := by ring
  have hden : (8 : ℝ) / 7 ≤ (1 + P.f t) ^ 2 *
      (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))) * H ^ 3 := by
    have s1 : (49 : ℝ) / 10000 ≤ (1 + P.f t) ^ 2 := by
      have := mul_le_mul hu hu (by norm_num) (by linarith : (0 : ℝ) ≤ 1 + P.f t)
      nlinarith
    calc (8 : ℝ) / 7 ≤ 49 / 10000 * (6 / 100) * 4096 := by norm_num
      _ ≤ (1 + P.f t) ^ 2 *
          (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))) * H ^ 3 :=
        mul_le_mul (mul_le_mul s1 huw (by norm_num) (by positivity)) hH3 (by norm_num)
          (mul_nonneg (by positivity) (by linarith))
  have hdenpos : 0 < (1 + P.f t) ^ 2 *
      (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t))) := by
    have s1 : (0 : ℝ) < (1 + P.f t) ^ 2 := pow_pos (by linarith) 2
    exact mul_pos s1 (by linarith)
  have hQ0 : 0 ≤ (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t) ^ 2 /
      ((1 + P.f t) ^ 2 *
        (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)))) / H ^ 3 :=
    div_nonneg (div_nonneg (sq_nonneg _) hdenpos.le) hH3pos.le
  have hy2 : 0 ≤ 14 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2 := by positivity
  have hQ : (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t) ^ 2 /
      ((1 + P.f t) ^ 2 *
        (1 + (P.f t + (ξ₀ * U0.f t + ξ₁ * U1.f t + ξ₂ * U2.f t + η * Ud.f t)))) / H ^ 3 ≤
      14 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2 := by
    rw [div_div, div_le_iff₀ (mul_pos hdenpos hH3pos)]
    have := mul_le_mul_of_nonneg_left hden hy2
    linarith
  -- collect the pieces
  obtain ⟨p_l, p_u⟩ := abs_le.1 (hdP t htI)
  have b0 : |ξ₀ * U0.linDefect P H A 0 t| ≤ |ξ₀| * εU := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hd0 t htI) (abs_nonneg _)
  have b1 : |ξ₁ * U1.linDefect P H A 0 t| ≤ |ξ₁| * εU := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hd1 t htI) (abs_nonneg _)
  have b2 : |ξ₂ * U2.linDefect P H A 0 t| ≤ |ξ₂| * εU := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hd2 t htI) (abs_nonneg _)
  have b3 : |η * Ud.linDefect P H A 1 t| ≤ |η| * εU := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hdd t htI) (abs_nonneg _)
  obtain ⟨b0l, b0u⟩ := abs_le.1 b0
  obtain ⟨b1l, b1u⟩ := abs_le.1 b1
  obtain ⟨b2l, b2u⟩ := abs_le.1 b2
  obtain ⟨b3l, b3u⟩ := abs_le.1 b3
  rw [key, abs_le]
  constructor <;> linarith

end Calabi.Shot
