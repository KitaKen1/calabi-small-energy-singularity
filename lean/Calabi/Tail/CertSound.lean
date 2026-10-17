import Calabi.Tail.Cert
import Calabi.Tail.Profile
import Calabi.Shot.FrameAlgebra

/-!
# Soundness of the approximate tail

If the kernel's `tailSummarize` accepts `P`, then `a(s) = P((56/s)³) / 2^128`
is an approximate solution of the profile equation on `[56, ∞)` in the sense of
`Calabi.Tail.profile_tail`, with the residual bound of the summary plus
`|d - dnum / 2^128| / 1000`.
-/

open Set

namespace Calabi.Tail

open Calabi.Shot

/-- `τ = (56 / s)³`. -/
noncomputable def tau (s : ℝ) : ℝ := (56 / s) ^ 3

theorem tau_mem {s : ℝ} (hs : 56 ≤ s) : 0 < tau s ∧ tau s ≤ 1 := by
  have hs0 : (0 : ℝ) < s := by linarith
  have h1 : (0 : ℝ) < 56 / s := by positivity
  have h2 : 56 / s ≤ 1 := (div_le_one hs0).2 hs
  exact ⟨pow_pos h1 3, pow_le_one₀ h1.le h2⟩

theorem tau_56 : tau 56 = 1 := by
  unfold tau
  norm_num

theorem hasDerivAt_tau {s : ℝ} (hs : s ≠ 0) : HasDerivAt tau (-3 * tau s / s) s := by
  have h1 : HasDerivAt (fun t : ℝ => 56 / t) ((0 * s - 56 * 1) / s ^ 2) s :=
    (hasDerivAt_const s (56 : ℝ)).fun_div (hasDerivAt_id' s) hs
  refine (h1.fun_pow 3).congr_deriv ?_
  unfold tau
  simp only [Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
  field_simp
  ring

theorem eval_theta (q : Poly) (x : ℝ) :
    Poly.eval (theta q) x = -3 * (x * Poly.eval (Poly.deriv q) x) := by
  simp only [theta, Poly.eval_smul, Poly.eval_cons]
  push_cast
  ring

theorem hasDerivAt_eval_tau (q : Poly) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t => Poly.eval q (tau t)) (Poly.eval (theta q) (tau s) / s) s := by
  have h := (Poly.hasDerivAt_eval q (tau s)).comp s (hasDerivAt_tau hs)
  refine h.congr_deriv ?_
  rw [eval_theta]
  field_simp

/-- The approximate tail and its first three derivatives. -/
noncomputable def apx (P : Poly) (s : ℝ) : ℝ := Poly.eval P (tau s) / (scaleP : ℝ)

noncomputable def apx1 (P : Poly) (s : ℝ) : ℝ :=
  Poly.eval (tailP1 P) (tau s) / ((scaleP : ℝ) * s)

noncomputable def apx2 (P : Poly) (s : ℝ) : ℝ :=
  Poly.eval (tailP2 P) (tau s) / ((scaleP : ℝ) * s ^ 2)

noncomputable def apx3 (P : Poly) (s : ℝ) : ℝ :=
  Poly.eval (tailP3 P) (tau s) / ((scaleP : ℝ) * s ^ 3)

theorem hasDerivAt_apx (P : Poly) {s : ℝ} (hs : s ≠ 0) : HasDerivAt (apx P) (apx1 P s) s := by
  have hS : (scaleP : ℝ) ≠ 0 := scaleP_pos.ne'
  refine ((hasDerivAt_eval_tau P hs).div_const (scaleP : ℝ)).congr_deriv ?_
  unfold apx1 tailP1
  field_simp

theorem hasDerivAt_apx1 (P : Poly) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (apx1 P) (apx2 P s) s := by
  have hS : (scaleP : ℝ) ≠ 0 := scaleP_pos.ne'
  have hd : HasDerivAt (fun t : ℝ => (scaleP : ℝ) * t) ((scaleP : ℝ) * 1) s :=
    (hasDerivAt_id s).const_mul (scaleP : ℝ)
  refine ((hasDerivAt_eval_tau (tailP1 P) hs).div hd (mul_ne_zero hS hs)).congr_deriv ?_
  unfold apx2 tailP2
  rw [Poly.eval_add, Poly.eval_smul]
  push_cast
  field_simp
  ring

theorem hasDerivAt_apx2 (P : Poly) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (apx2 P) (apx3 P s) s := by
  have hS : (scaleP : ℝ) ≠ 0 := scaleP_pos.ne'
  have hd : HasDerivAt (fun t : ℝ => (scaleP : ℝ) * t ^ 2)
      ((scaleP : ℝ) * ((2 : ℕ) * s ^ (2 - 1) * 1)) s :=
    ((hasDerivAt_id s).pow 2).const_mul (scaleP : ℝ)
  refine ((hasDerivAt_eval_tau (tailP2 P) hs).div hd
    (mul_ne_zero hS (pow_ne_zero 2 hs))).congr_deriv ?_
  unfold apx3 tailP3
  rw [Poly.eval_add, Poly.eval_smul]
  push_cast
  field_simp
  ring

theorem continuous_eval (q : Poly) : Continuous (Poly.eval q) :=
  continuous_iff_continuousAt.2 fun x => (Poly.hasDerivAt_eval q x).continuousAt

theorem continuousOn_apx3 (P : Poly) : ContinuousOn (apx3 P) (Ici 56) := by
  have hpos : ∀ s ∈ Ici (56 : ℝ), (0 : ℝ) < s := fun s hs => by
    have : (56 : ℝ) ≤ s := hs
    linarith
  have ht : ContinuousOn tau (Ici 56) := fun s hs =>
    (hasDerivAt_tau (hpos s hs).ne').continuousAt.continuousWithinAt
  refine ((continuous_eval (tailP3 P)).comp_continuousOn ht).div
    (continuousOn_const.mul (continuousOn_id.pow 3)) fun s hs => ?_
  have := hpos s hs
  have hS := scaleP_pos
  positivity

theorem eval_tailRes (dnum : Int) (P : Poly) (x : ℝ) :
    Poly.eval (tailRes dnum P) x =
      x * (((scaleP : ℝ) + Poly.eval P x) *
        (567 * (dnum : ℝ) + (4 * Poly.eval (tailP3 P) x + 84 * Poly.eval (tailP2 P) x
          + 337 * Poly.eval (tailP1 P) x - 567 * Poly.eval P x)))
        + 4 * 56 ^ 3 * (scaleP : ℝ) * Poly.eval P x := by
  simp only [tailRes, tailLin, Poly.eval_add, Poly.eval_smul, Poly.eval_mul, Poly.eval_cons,
    Poly.eval_nil, eval_onePlus]
  push_cast
  ring

theorem resid_identity {SP s τ e0 e1 e2 e3 d dn R : ℝ} (hSP : SP ≠ 0) (hs : s ≠ 0)
    (hτ : τ = (56 / s) ^ 3) (hden : SP + e0 ≠ 0)
    (hR : R = τ * ((SP + e0) * (567 * dn + (4 * e3 + 84 * e2 + 337 * e1 - 567 * e0)))
      + 4 * 56 ^ 3 * SP * e0) :
    e3 / (SP * s ^ 3) + 21 / s * (e2 / (SP * s ^ 2)) + 337 / (4 * s ^ 2) * (e1 / (SP * s))
        - 567 / (4 * s ^ 3) * (e0 / SP - d) + e0 / SP / (1 + e0 / SP) =
      (R + τ * (SP + e0) * 567 * SP * (d - dn / SP)) / (4 * 56 ^ 3 * SP * (SP + e0)) := by
  subst hτ hR
  have h1 : 1 + e0 / SP ≠ 0 := by
    rw [show 1 + e0 / SP = (SP + e0) / SP by field_simp]
    exact div_ne_zero hden hSP
  field_simp
  ring

theorem tailSummarize_some {dnum : Int} {P : Poly} {ts : TailSummary}
    (h : tailSummarize dnum P = some ts) :
    Poly.l1 P * 200 ≤ scaleP ∧
      567 * (scaleP + Poly.l1 P) * 1000 ≤ 4 * 56 ^ 3 * (scaleP - Poly.l1 P) ∧
      ts.v = Poly.evalInt 1 P ∧ ts.d1 = Poly.evalInt 1 (tailP1 P) ∧
      ts.d2 = Poly.evalInt 1 (tailP2 P) ∧ ts.l1 = Poly.l1 P ∧
      ts.eps = ceilDiv (Poly.l1 (tailRes dnum P) * scaleE)
        (4 * 56 ^ 3 * scaleP * (scaleP - Poly.l1 P)) := by
  unfold tailSummarize at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc.1, hc.2, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

/-- **Soundness of the tail certificate.** -/
theorem tail_cert_spec {dnum : Int} {P : Poly} {ts : TailSummary}
    (h : tailSummarize dnum P = some ts) (d : ℝ) :
    (∀ s, (56 : ℝ) ≤ s → HasDerivAt (apx P) (apx1 P s) s) ∧
      (∀ s, (56 : ℝ) ≤ s → HasDerivAt (apx1 P) (apx2 P s) s) ∧
      (∀ s, (56 : ℝ) ≤ s → HasDerivAt (apx2 P) (apx3 P s) s) ∧
      ContinuousOn (apx3 P) (Ici 56) ∧
      (∀ s, (56 : ℝ) ≤ s → |apx P s| ≤ 1 / 200) ∧
      (∀ s, (56 : ℝ) ≤ s → |resid d (apx P) (apx1 P) (apx2 P) (apx3 P) s| ≤
        (ts.eps : ℝ) / (scaleE : ℝ) + |d - (dnum : ℝ) / (scaleP : ℝ)| / 1000) ∧
      apx P 56 = (ts.v : ℝ) / (scaleP : ℝ) ∧
      apx1 P 56 = (ts.d1 : ℝ) / ((scaleP : ℝ) * 56) ∧
      apx2 P 56 = (ts.d2 : ℝ) / ((scaleP : ℝ) * 56 ^ 2) := by
  obtain ⟨hl, hside, hv, hd1, hd2, -, heps⟩ := tailSummarize_some h
  have hS := scaleP_pos
  have hE := scaleE_pos
  have hne : ∀ s : ℝ, 56 ≤ s → s ≠ 0 := fun s hs => by
    have : (0 : ℝ) < s := by linarith
    exact this.ne'
  have hlR : (Poly.l1 P : ℝ) * 200 ≤ (scaleP : ℝ) := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ (Poly.l1 P : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) < (scaleP : ℝ) - (Poly.l1 P : ℝ) := by linarith
  have hlle : Poly.l1 P ≤ scaleP := by omega
  have hmcast : ((scaleP - Poly.l1 P : ℕ) : ℝ) = (scaleP : ℝ) - (Poly.l1 P : ℝ) :=
    Nat.cast_sub hlle
  have hev : ∀ s : ℝ, 56 ≤ s → |Poly.eval P (tau s)| ≤ (Poly.l1 P : ℝ) := fun s hs => by
    obtain ⟨t0, t1⟩ := tau_mem hs
    exact Poly.abs_eval_le P (by rw [abs_of_pos t0]; exact t1)
  have h1one : ((1 : Int) : ℝ) = 1 := by norm_num
  refine ⟨fun s hs => hasDerivAt_apx P (hne s hs), fun s hs => hasDerivAt_apx1 P (hne s hs),
    fun s hs => hasDerivAt_apx2 P (hne s hs), continuousOn_apx3 P, fun s hs => ?_,
    fun s hs => ?_, ?_, ?_, ?_⟩
  · unfold apx
    rw [abs_div, abs_of_pos hS, div_le_iff₀ hS]
    linarith [hev s hs]
  · obtain ⟨t0, t1⟩ := tau_mem hs
    have hs0 := hne s hs
    have he0 := abs_le.1 (hev s hs)
    have hden : (0 : ℝ) < (scaleP : ℝ) + Poly.eval P (tau s) := by linarith [he0.1]
    have hid := resid_identity (d := d) (dn := (dnum : ℝ)) hS.ne' hs0 (rfl : tau s = (56 / s) ^ 3)
      hden.ne' (eval_tailRes dnum P (tau s))
    have hres : resid d (apx P) (apx1 P) (apx2 P) (apx3 P) s =
        (Poly.eval (tailRes dnum P) (tau s) + tau s * ((scaleP : ℝ) + Poly.eval P (tau s)) * 567
          * (scaleP : ℝ) * (d - (dnum : ℝ) / (scaleP : ℝ))) /
          (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) + Poly.eval P (tau s))) := by
      rw [← hid]
      rfl
    rw [hres]
    -- the two parts of the numerator
    have hR := Poly.abs_eval_le (tailRes dnum P) (x := tau s) (by rw [abs_of_pos t0]; exact t1)
    have hnat : 0 < 4 * 56 ^ 3 * scaleP * (scaleP - Poly.l1 P) := by
      have h200 : 0 < scaleP := scaleP_pos_nat
      have hm : 0 < scaleP - Poly.l1 P := by omega
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) h200) hm
    have h56 : (4 : ℝ) * 56 ^ 3 = 702464 := by norm_num
    have hceil := le_ceilDiv_mul (Poly.l1 (tailRes dnum P) * scaleE) hnat
    rw [← heps] at hceil
    have hceilR : (Poly.l1 (tailRes dnum P) : ℝ) * (scaleE : ℝ) ≤
        (ts.eps : ℝ) * (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) - (Poly.l1 P : ℝ))) := by
      have := (Nat.cast_le (α := ℝ)).2 hceil
      push_cast at this
      rw [hmcast] at this
      rw [h56]
      exact this
    have hsideR : 567 * ((scaleP : ℝ) + (Poly.l1 P : ℝ)) * 1000 ≤
        4 * 56 ^ 3 * ((scaleP : ℝ) - (Poly.l1 P : ℝ)) := by
      have := (Nat.cast_le (α := ℝ)).2 hside
      push_cast at this
      rw [hmcast] at this
      rw [h56]
      exact this
    set e0 := Poly.eval P (tau s) with he0def
    set δ := d - (dnum : ℝ) / (scaleP : ℝ) with hδ
    have hD : (0 : ℝ) < 4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) + e0) := by positivity
    have hnum : |Poly.eval (tailRes dnum P) (tau s) + tau s * ((scaleP : ℝ) + e0) * 567
        * (scaleP : ℝ) * δ| ≤ (Poly.l1 (tailRes dnum P) : ℝ)
          + ((scaleP : ℝ) + (Poly.l1 P : ℝ)) * 567 * (scaleP : ℝ) * |δ| := by
      refine (abs_add_le _ _).trans (add_le_add hR ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos t0, abs_of_pos hden,
        abs_of_pos hS, abs_of_pos (by norm_num : (0 : ℝ) < 567)]
      have k1 : tau s * ((scaleP : ℝ) + e0) ≤ 1 * ((scaleP : ℝ) + (Poly.l1 P : ℝ)) :=
        mul_le_mul t1 (by linarith [he0.2]) hden.le (by norm_num)
      have k2 : 0 ≤ 567 * (scaleP : ℝ) * |δ| := by positivity
      calc tau s * ((scaleP : ℝ) + e0) * 567 * (scaleP : ℝ) * |δ|
          = tau s * ((scaleP : ℝ) + e0) * (567 * (scaleP : ℝ) * |δ|) := by ring
        _ ≤ 1 * ((scaleP : ℝ) + (Poly.l1 P : ℝ)) * (567 * (scaleP : ℝ) * |δ|) :=
            mul_le_mul_of_nonneg_right k1 k2
        _ = ((scaleP : ℝ) + (Poly.l1 P : ℝ)) * 567 * (scaleP : ℝ) * |δ| := by ring
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    refine hnum.trans ?_
    -- compare with the denominator, using `scaleP + e0 ≥ scaleP - l1 P`
    have hlow : (scaleP : ℝ) - (Poly.l1 P : ℝ) ≤ (scaleP : ℝ) + e0 := by linarith [he0.1]
    have hδ0 : 0 ≤ |δ| := abs_nonneg δ
    have heps0 : (0 : ℝ) ≤ (ts.eps : ℝ) := Nat.cast_nonneg _
    have p1 : (Poly.l1 (tailRes dnum P) : ℝ) ≤
        (ts.eps : ℝ) / (scaleE : ℝ) *
          (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) - (Poly.l1 P : ℝ))) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hE]
      exact hceilR
    have p2 : ((scaleP : ℝ) + (Poly.l1 P : ℝ)) * 567 * (scaleP : ℝ) * |δ| ≤
        |δ| / 1000 * (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) - (Poly.l1 P : ℝ))) := by
      have := mul_le_mul_of_nonneg_left hsideR (mul_nonneg hS.le hδ0)
      nlinarith
    have p3 : ((ts.eps : ℝ) / (scaleE : ℝ) + |δ| / 1000) *
        (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) - (Poly.l1 P : ℝ))) ≤
        ((ts.eps : ℝ) / (scaleE : ℝ) + |δ| / 1000) *
          (4 * 56 ^ 3 * (scaleP : ℝ) * ((scaleP : ℝ) + e0)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hlow (by positivity)
    nlinarith
  · unfold apx
    rw [tau_56, hv, ← h1one, Poly.eval_intCast]
  · unfold apx1
    rw [tau_56, hd1, ← h1one, Poly.eval_intCast]
  · unfold apx2
    rw [tau_56, hd2, ← h1one, Poly.eval_intCast]

end Calabi.Tail
