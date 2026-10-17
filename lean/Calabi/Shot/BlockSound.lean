import Calabi.Shot.PolyEval
import Calabi.Shot.BlockFamily
import Calabi.Shot.BlockAlgebra

/-!
# What a kernel-checked block summary means

`summarize dnum b = some sm` is a statement about integers, checked by the
kernel. This file turns it into the hypotheses of `block_family`: the profile
polynomial stays away from `-1`, the tangent polynomials are bounded, and all
five defects are small.
-/

open Set

namespace Calabi.Shot

theorem scaleP_pos_nat : 0 < scaleP := by
  unfold scaleP
  positivity

theorem scaleU_pos_nat : 0 < scaleU := by
  unfold scaleU
  positivity

theorem scaleE_pos_nat : 0 < scaleE := by
  unfold scaleE
  positivity

theorem scaleP_pos : (0 : ℝ) < (scaleP : ℝ) := by exact_mod_cast scaleP_pos_nat

theorem scaleU_pos : (0 : ℝ) < (scaleU : ℝ) := by exact_mod_cast scaleU_pos_nat

theorem scaleE_pos : (0 : ℝ) < (scaleE : ℝ) := by exact_mod_cast scaleE_pos_nat

/-- The polynomial `p / s` together with its derivatives. -/
noncomputable def Jet3.ofPoly (p : Poly) (s : ℝ) : Jet3 where
  f t := Poly.eval p t / s
  f1 t := Poly.eval (Poly.deriv p) t / s
  f2 t := Poly.eval (Poly.deriv (Poly.deriv p)) t / s
  f3 t := Poly.eval (Poly.deriv (Poly.deriv (Poly.deriv p))) t / s
  h0 t := (Poly.hasDerivAt_eval p t).div_const s
  h1 t := (Poly.hasDerivAt_eval (Poly.deriv p) t).div_const s
  h2 t := (Poly.hasDerivAt_eval (Poly.deriv (Poly.deriv p)) t).div_const s

theorem summarize_some {dnum : Int} {b : Block} {sm : Summary}
    (h : summarize dnum b = some sm) :
    b.ok = true ∧ sm.H = b.H ∧ sm.A = b.A ∧ sm.start = jetAt (-1) b.P ∧
      sm.stop = jetAt 1 b.P ∧ sm.t0 = jetAt 1 b.U0 ∧ sm.t1 = jetAt 1 b.U1 ∧
      sm.t2 = jetAt 1 b.U2 ∧ sm.td = jetAt 1 b.Ud ∧ sm.eps = epsP dnum b := by
  unfold summarize at h
  by_cases hok : b.ok = true
  · rw [if_pos hok] at h
    cases h
    exact ⟨hok, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg hok] at h
    cases h

theorem minP_le_eval (b : Block) {t : ℝ} (ht : |t| ≤ 1) :
    ((minP b : Int) : ℝ) ≤ (scaleP : ℝ) + Poly.eval b.P t := by
  unfold minP
  cases b.P with
  | nil => simp
  | cons a p =>
    have h := Poly.abs_eval_le p ht
    have h2 : |t * Poly.eval p t| ≤ (Poly.l1 p : ℝ) := by
      rw [abs_mul]
      calc |t| * |Poly.eval p t| ≤ 1 * (Poly.l1 p : ℝ) :=
            mul_le_mul ht h (abs_nonneg _) zero_le_one
        _ = (Poly.l1 p : ℝ) := one_mul _
    have h3 := (abs_le.1 h2).1
    simp only [Poly.eval_cons]
    push_cast
    linarith

theorem tangent_abs_le {u : Poly} (h : Poly.l1 u ≤ 4 * scaleU) {t : ℝ} (ht : |t| ≤ 1) :
    |Poly.eval u t / (scaleU : ℝ)| ≤ 4 := by
  have hSu := scaleU_pos
  rw [abs_div, abs_of_pos hSu, div_le_iff₀ hSu]
  have h1 := Poly.abs_eval_le u ht
  have h2 : (Poly.l1 u : ℝ) ≤ 4 * (scaleU : ℝ) := by exact_mod_cast h
  linarith

theorem eval_resP (dnum : Int) (b : Block) (t : ℝ) :
    Poly.eval (resP dnum b) t =
      (b.H : ℝ) ^ 3 * (((scaleP : ℝ) + Poly.eval b.P t) *
        (567 * (dnum : ℝ) +
          (4 * ((b.A : ℝ) + t) ^ 3 * Poly.eval (Poly.deriv (Poly.deriv (Poly.deriv b.P))) t
            + 84 * ((b.A : ℝ) + t) ^ 2 * Poly.eval (Poly.deriv (Poly.deriv b.P)) t
            + 337 * ((b.A : ℝ) + t) * Poly.eval (Poly.deriv b.P) t
            - 567 * Poly.eval b.P t)))
        + 4 * (scaleP : ℝ) * (((b.A : ℝ) + t) ^ 3 * Poly.eval b.P t) := by
  simp only [resP, Poly.eval_add, Poly.eval_smul, Poly.eval_mul, eval_onePlus, eval_opA,
    eval_sig3, Poly.eval_cons, Poly.eval_nil]
  push_cast
  ring

theorem eval_resU (b : Block) (u : Poly) (forcing : Int) (t : ℝ) :
    Poly.eval (resU b u forcing) t =
      (b.H : ℝ) ^ 3 * (((scaleP : ℝ) + Poly.eval b.P t) * ((scaleP : ℝ) + Poly.eval b.P t) *
        ((forcing : ℝ) +
          (4 * ((b.A : ℝ) + t) ^ 3 * Poly.eval (Poly.deriv (Poly.deriv (Poly.deriv u))) t
            + 84 * ((b.A : ℝ) + t) ^ 2 * Poly.eval (Poly.deriv (Poly.deriv u)) t
            + 337 * ((b.A : ℝ) + t) * Poly.eval (Poly.deriv u) t
            - 567 * Poly.eval u t)))
        + 4 * (scaleP : ℝ) * (scaleP : ℝ) * (((b.A : ℝ) + t) ^ 3 * Poly.eval u t) := by
  simp only [resU, Poly.eval_add, Poly.eval_smul, Poly.eval_mul, eval_onePlus, eval_opA,
    eval_sig3, Poly.eval_cons, Poly.eval_nil]
  push_cast
  ring

/-- Real value of the kernel's lower bound `4 (A - 1)³ H³`. -/
theorem sigBound_cast (b : Block) (hA : 129 ≤ b.A) :
    ((sigBound b : ℕ) : ℝ) = 4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3 := by
  unfold sigBound
  have h1 : ((b.A - 1 : ℕ) : ℝ) = (b.A : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  push_cast [h1]
  ring

/-- `4 (A - 1)³ H³ · m ≤ 4 σ³ H³ · u` when `A - 1 ≤ σ` and `m ≤ u`. -/
theorem sig_mul_le {A t H m u : ℝ} (hA : 129 ≤ A) (ht : -1 ≤ t) (hH : 0 < H) (hm : 0 ≤ m)
    (hmu : m ≤ u) : 4 * (A - 1) ^ 3 * H ^ 3 * m ≤ 4 * (A + t) ^ 3 * H ^ 3 * u := by
  have hA1 : (0 : ℝ) ≤ A - 1 := by linarith
  have hσ : (0 : ℝ) < A + t := by linarith
  have hcube : (A - 1) ^ 3 ≤ (A + t) ^ 3 := pow_le_pow_left₀ hA1 (by linarith) 3
  have hH3 : (0 : ℝ) ≤ H ^ 3 := (pow_pos hH 3).le
  have hσ3 : (0 : ℝ) ≤ (A + t) ^ 3 := (pow_pos hσ 3).le
  have h1 : 4 * (A - 1) ^ 3 * H ^ 3 ≤ 4 * (A + t) ^ 3 * H ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) hH3
  exact mul_le_mul h1 hmu hm (mul_nonneg (mul_nonneg (by norm_num) hσ3) hH3)

theorem eval_neg_one (p : Poly) : Poly.eval p (-1) = ((Poly.evalInt (-1) p : Int) : ℝ) := by
  have h := Poly.eval_intCast (-1) p
  simpa using h

theorem eval_one (p : Poly) : Poly.eval p 1 = ((Poly.evalInt 1 p : Int) : ℝ) := by
  have h := Poly.eval_intCast 1 p
  simpa using h

/-- The defect of the profile polynomial is at most the kernel's `epsP`. -/
theorem defectP_le (dnum : Int) (b : Block) (hH : 16 ≤ b.H) (hA : 129 ≤ b.A)
    (hm : 7 * (scaleP : Int) ≤ 100 * minP b) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |(Jet3.ofPoly b.P scaleP).defect b.H b.A ((dnum : ℝ) / scaleP) t| ≤
      (epsP dnum b : ℝ) / scaleE := by
  have hS := scaleP_pos
  have hE := scaleE_pos
  have habs : |t| ≤ 1 := abs_le.2 ht
  have hHR : (16 : ℝ) ≤ (b.H : ℝ) := by exact_mod_cast hH
  have hAR : (129 : ℝ) ≤ (b.A : ℝ) := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < (b.H : ℝ) := by linarith
  have hσ : (0 : ℝ) < (b.A : ℝ) + t := by linarith [ht.1]
  have hmin := minP_le_eval b habs
  have hmR : 7 * (scaleP : ℝ) ≤ 100 * ((minP b : Int) : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < ((minP b : Int) : ℝ) := by linarith
  have hu : (0 : ℝ) < (scaleP : ℝ) + Poly.eval b.P t := by linarith
  have hmZ : (0 : Int) < minP b := by exact_mod_cast hmpos
  have key : Poly.eval (resP dnum b) t =
      (scaleP : ℝ) ^ 2 * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ))) *
        (Jet3.ofPoly b.P scaleP).defect b.H b.A ((dnum : ℝ) / scaleP) t := by
    rw [eval_resP, resP_identity hS.ne' hσ.ne' hH0.ne' hu.ne']
    simp only [Jet3.defect, Jet3.ofPoly]
  have hl1 : |Poly.eval (resP dnum b) t| ≤ (Poly.l1 (resP dnum b) : ℝ) :=
    Poly.abs_eval_le _ habs
  have hsig : (0 : ℝ) < 4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3 :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 3)) (pow_pos hH0 3)
  have hc0 : (0 : ℝ) < (scaleP : ℝ) * ((sigBound b : ℕ) : ℝ) * ((minP b : Int) : ℝ) := by
    rw [sigBound_cast b hA]
    exact mul_pos (mul_pos hS hsig) hmpos
  have hSe : (scaleP : ℝ) * (1 + Poly.eval b.P t / (scaleP : ℝ)) =
      (scaleP : ℝ) + Poly.eval b.P t := by
    have hS0 := hS.ne'
    field_simp
  have hc : (scaleP : ℝ) * ((sigBound b : ℕ) : ℝ) * ((minP b : Int) : ℝ) ≤
      (scaleP : ℝ) ^ 2 * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ))) := by
    rw [sigBound_cast b hA]
    have h1 := sig_mul_le (A := (b.A : ℝ)) (t := t) (H := (b.H : ℝ))
      (m := ((minP b : Int) : ℝ)) (u := (scaleP : ℝ) + Poly.eval b.P t)
      hAR ht.1 hH0 hmpos.le hmin
    have h2 : (scaleP : ℝ) ^ 2 * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ))) =
        (scaleP : ℝ) * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
          ((scaleP : ℝ) * (1 + Poly.eval b.P t / (scaleP : ℝ)))) := by ring
    rw [h2, hSe]
    calc (scaleP : ℝ) * (4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3) * ((minP b : Int) : ℝ)
        = (scaleP : ℝ) * (4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3 *
            ((minP b : Int) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hS.le
  refine (abs_le_div_of_eq_mul key hc0 hc hl1).trans ?_
  rw [div_le_div_iff₀ hc0 hE]
  have hden : 0 < scaleP * sigBound b * (minP b).toNat := by
    have h1 : 0 < b.A - 1 := by omega
    have h2 : 0 < sigBound b := by
      unfold sigBound
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos h1 3)) (pow_pos (by omega) 3)
    have h3 : 0 < (minP b).toNat := by omega
    exact Nat.mul_pos (Nat.mul_pos scaleP_pos_nat h2) h3
  have hceil : Poly.l1 (resP dnum b) * scaleE ≤
      epsP dnum b * (scaleP * sigBound b * (minP b).toNat) :=
    le_ceilDiv_mul (Poly.l1 (resP dnum b) * scaleE) hden
  have hcast : (((minP b).toNat : ℕ) : ℝ) = ((minP b : Int) : ℝ) := by
    have h1 : (((minP b).toNat : ℕ) : Int) = minP b := Int.toNat_of_nonneg hmZ.le
    exact_mod_cast h1
  have hR : ((Poly.l1 (resP dnum b) * scaleE : ℕ) : ℝ) ≤
      ((epsP dnum b * (scaleP * sigBound b * (minP b).toNat) : ℕ) : ℝ) := by
    exact_mod_cast hceil
  push_cast at hR
  rw [hcast] at hR
  exact hR

/-- The linearised defect of a tangent polynomial is at most `2^-40`. -/
theorem defectU_le (b : Block) (u : Poly) (forcing : Int) (φ : ℝ)
    (hφ : (forcing : ℝ) = 567 * (scaleU : ℝ) * φ)
    (hH : 16 ≤ b.H) (hA : 129 ≤ b.A) (hm : 7 * (scaleP : Int) ≤ 100 * minP b)
    (hres : Poly.l1 (resU b u forcing) * 2 ^ 40 ≤
      scaleU * sigBound b * ((minP b).toNat * (minP b).toNat))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |(Jet3.ofPoly u scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A φ t| ≤ 1 / 2 ^ 40 := by
  have hS := scaleP_pos
  have hSu := scaleU_pos
  have habs : |t| ≤ 1 := abs_le.2 ht
  have hHR : (16 : ℝ) ≤ (b.H : ℝ) := by exact_mod_cast hH
  have hAR : (129 : ℝ) ≤ (b.A : ℝ) := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < (b.H : ℝ) := by linarith
  have hσ : (0 : ℝ) < (b.A : ℝ) + t := by linarith [ht.1]
  have hmin := minP_le_eval b habs
  have hmR : 7 * (scaleP : ℝ) ≤ 100 * ((minP b : Int) : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < ((minP b : Int) : ℝ) := by linarith
  have hu : (0 : ℝ) < (scaleP : ℝ) + Poly.eval b.P t := by linarith
  have hmZ : (0 : Int) < minP b := by exact_mod_cast hmpos
  have key : Poly.eval (resU b u forcing) t =
      (scaleP : ℝ) ^ 2 * (scaleU : ℝ) * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ)) ^ 2) *
        (Jet3.ofPoly u scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A φ t := by
    rw [eval_resU, hφ, resU_identity hS.ne' hSu.ne' hσ.ne' hH0.ne' hu.ne']
    simp only [Jet3.linDefect, Jet3.ofPoly]
  have hl1 : |Poly.eval (resU b u forcing) t| ≤ (Poly.l1 (resU b u forcing) : ℝ) :=
    Poly.abs_eval_le _ habs
  have hsig : (0 : ℝ) < 4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3 :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 3)) (pow_pos hH0 3)
  have hc0 : (0 : ℝ) < (scaleU : ℝ) * ((sigBound b : ℕ) : ℝ) *
      (((minP b : Int) : ℝ) * ((minP b : Int) : ℝ)) := by
    rw [sigBound_cast b hA]
    exact mul_pos (mul_pos hSu hsig) (mul_pos hmpos hmpos)
  have hSe : (scaleP : ℝ) * (1 + Poly.eval b.P t / (scaleP : ℝ)) =
      (scaleP : ℝ) + Poly.eval b.P t := by
    have hS0 := hS.ne'
    field_simp
  have hc : (scaleU : ℝ) * ((sigBound b : ℕ) : ℝ) *
      (((minP b : Int) : ℝ) * ((minP b : Int) : ℝ)) ≤
      (scaleP : ℝ) ^ 2 * (scaleU : ℝ) * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ)) ^ 2) := by
    rw [sigBound_cast b hA]
    have h1 := sig_mul_le (A := (b.A : ℝ)) (t := t) (H := (b.H : ℝ))
      (m := ((minP b : Int) : ℝ) * ((minP b : Int) : ℝ))
      (u := ((scaleP : ℝ) + Poly.eval b.P t) * ((scaleP : ℝ) + Poly.eval b.P t))
      hAR ht.1 hH0 (mul_nonneg hmpos.le hmpos.le) (mul_le_mul hmin hmin hmpos.le hu.le)
    have h2 : (scaleP : ℝ) ^ 2 * (scaleU : ℝ) * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
        (1 + Poly.eval b.P t / (scaleP : ℝ)) ^ 2) =
        (scaleU : ℝ) * (4 * ((b.A : ℝ) + t) ^ 3 * (b.H : ℝ) ^ 3 *
          (((scaleP : ℝ) * (1 + Poly.eval b.P t / (scaleP : ℝ))) *
            ((scaleP : ℝ) * (1 + Poly.eval b.P t / (scaleP : ℝ))))) := by ring
    rw [h2, hSe]
    calc (scaleU : ℝ) * (4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3) *
          (((minP b : Int) : ℝ) * ((minP b : Int) : ℝ))
        = (scaleU : ℝ) * (4 * ((b.A : ℝ) - 1) ^ 3 * (b.H : ℝ) ^ 3 *
            (((minP b : Int) : ℝ) * ((minP b : Int) : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hSu.le
  refine (abs_le_div_of_eq_mul key hc0 hc hl1).trans ?_
  rw [div_le_div_iff₀ hc0 (by positivity)]
  have hcast : (((minP b).toNat : ℕ) : ℝ) = ((minP b : Int) : ℝ) := by
    have h1 : (((minP b).toNat : ℕ) : Int) = minP b := Int.toNat_of_nonneg hmZ.le
    exact_mod_cast h1
  have hR : ((Poly.l1 (resU b u forcing) * 2 ^ 40 : ℕ) : ℝ) ≤
      ((scaleU * sigBound b * ((minP b).toNat * (minP b).toNat) : ℕ) : ℝ) := by
    exact_mod_cast hres
  push_cast at hR
  rw [hcast] at hR
  linarith

end Calabi.Shot
