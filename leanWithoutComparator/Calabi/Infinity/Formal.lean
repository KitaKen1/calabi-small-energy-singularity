import Calabi.Infinity.Bd
import Calabi.Tail.Profile
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The formal expansion at infinity

In the variable `σ = s⁻³` the profile equation has a unique formal solution
`∑ c_j σ^j` without constant term. `tailPoly d J` is its truncation at order
`J`, defined by cancelling one more power of `σ` in each step. For
`q(s) = P(s⁻³)` with a polynomial `P`,

  `q′ = (Θ P)(σ) / s`,   `q″ = ((Θ - 1) Θ P)(σ) / s²`,   `q‴ = ((Θ - 2)(Θ - 1) Θ P)(σ) / s³`,

`Θ = -3 X d/dX`, and `1 + q` times the residual of `q` is the polynomial
`E d P` in `σ`. `tailPoly_dvd` says that `σ^{J+1}` divides `E d (tailPoly d J)`.
-/

open Polynomial Set

namespace Calabi.Infinity

/-- `θ = s d/ds` on polynomials in `σ = s⁻³`: `σ^j ↦ -3 j σ^j`. -/
noncomputable def Θ (P : ℝ[X]) : ℝ[X] := C (-3) * (X * derivative P)

theorem Θ_add (P Q : ℝ[X]) : Θ (P + Q) = Θ P + Θ Q := by
  simp only [Θ, derivative_add]
  ring

theorem Θ_sub (P Q : ℝ[X]) : Θ (P - Q) = Θ P - Θ Q := by
  simp only [Θ, derivative_sub]
  ring

theorem Θ_C_mul (c : ℝ) (P : ℝ[X]) : Θ (C c * P) = C c * Θ P := by
  simp only [Θ, derivative_C_mul]
  ring

theorem X_pow_dvd_Θ {n : ℕ} {P : ℝ[X]} (h : X ^ n ∣ P) : X ^ n ∣ Θ P := by
  obtain ⟨Q, rfl⟩ := h
  cases n with
  | zero => simp
  | succ m =>
    refine ⟨C (-3) * (C ((m + 1 : ℕ) : ℝ) * Q + X * derivative Q), ?_⟩
    simp only [Θ, derivative_mul, derivative_X_pow, Nat.add_sub_cancel]
    ring

/-- The polynomials of the first three derivatives. -/
noncomputable def P1 (P : ℝ[X]) : ℝ[X] := Θ P

noncomputable def P2 (P : ℝ[X]) : ℝ[X] := Θ (P1 P) - P1 P

noncomputable def P3 (P : ℝ[X]) : ℝ[X] := Θ (P2 P) - C 2 * P2 P

/-- `s³ (q‴ + (21/s) q″ + (337/4s²) q′ - (567/4s³) q)` as a polynomial in `σ`. -/
noncomputable def Lop (P : ℝ[X]) : ℝ[X] :=
  P3 P + C 21 * P2 P + C (337 / 4) * P1 P - C (567 / 4) * P

theorem Lop_add (P Q : ℝ[X]) : Lop (P + Q) = Lop P + Lop Q := by
  simp only [Lop, P3, P2, P1, Θ_add, Θ_sub]
  ring

theorem X_pow_dvd_Lop {n : ℕ} {P : ℝ[X]} (h : X ^ n ∣ P) : X ^ n ∣ Lop P := by
  have h1 : X ^ n ∣ P1 P := X_pow_dvd_Θ h
  have h2 : X ^ n ∣ P2 P := dvd_sub (X_pow_dvd_Θ h1) h1
  have h3 : X ^ n ∣ P3 P := dvd_sub (X_pow_dvd_Θ h2) (h2.mul_left _)
  exact dvd_sub (dvd_add (dvd_add h3 (h2.mul_left _)) (h1.mul_left _)) (h.mul_left _)

/-- `1 + q` times the residual of `q = P(σ)`, as a polynomial in `σ`. -/
noncomputable def E (d : ℝ) (P : ℝ[X]) : ℝ[X] := (1 + P) * (X * (Lop P + C (567 / 4 * d))) + P

theorem E_add_dvd (d : ℝ) (P : ℝ[X]) (c : ℝ) (n : ℕ) :
    X ^ (n + 1) ∣ E d (P + C c * X ^ n) - (E d P + C c * X ^ n) := by
  obtain ⟨R, hR⟩ := X_pow_dvd_Lop (P := C c * X ^ n) (n := n) (Dvd.intro_left _ rfl)
  refine ⟨C c * (Lop P + C (567 / 4 * d)) + (1 + P + C c * X ^ n) * R, ?_⟩
  simp only [E, Lop_add, hR]
  ring

/-- The truncation at order `J` of the formal solution at infinity. -/
noncomputable def tailPoly (d : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | J + 1 => tailPoly d J + C (-(E d (tailPoly d J)).coeff (J + 1)) * X ^ (J + 1)

theorem tailPoly_dvd (d : ℝ) : ∀ J : ℕ, X ^ (J + 1) ∣ E d (tailPoly d J)
  | 0 => by
    refine ⟨Lop 0 + C (567 / 4 * d), ?_⟩
    simp only [tailPoly, E]
    ring
  | J + 1 => by
    obtain ⟨Q, hQ⟩ := tailPoly_dvd d J
    have he : (E d (tailPoly d J)).coeff (J + 1) = Q.coeff 0 := by
      have h := coeff_X_pow_mul Q (J + 1) 0
      rw [zero_add] at h
      rw [hQ]
      exact h
    obtain ⟨Q', hQ'⟩ : X ∣ Q - C (Q.coeff 0) := X_dvd_iff.2 (by simp)
    have h1 : X ^ (J + 1 + 1) ∣ E d (tailPoly d J)
        + C (-(E d (tailPoly d J)).coeff (J + 1)) * X ^ (J + 1) := by
      refine ⟨Q', ?_⟩
      rw [he]
      calc E d (tailPoly d J) + C (-Q.coeff 0) * X ^ (J + 1)
          = X ^ (J + 1) * (Q - C (Q.coeff 0)) := by
            rw [hQ, C_neg]
            ring
        _ = X ^ (J + 1 + 1) * Q' := by
            rw [hQ']
            ring
    have h2 := E_add_dvd d (tailPoly d J) (-(E d (tailPoly d J)).coeff (J + 1)) (J + 1)
    have h3 := dvd_add h2 h1
    rw [sub_add_cancel] at h3
    exact h3

theorem tailPoly_coeff_zero (d : ℝ) : ∀ J : ℕ, (tailPoly d J).coeff 0 = 0
  | 0 => by simp [tailPoly]
  | J + 1 => by
    rw [tailPoly, coeff_add, tailPoly_coeff_zero d J, coeff_C_mul, coeff_X_pow]
    simp

/-! ### Functions of `s` -/

theorem sigma_eq {s : ℝ} : s ^ (-3 : ℤ) = (s ^ 3)⁻¹ := by
  rw [zpow_neg]
  norm_cast

theorem hasDerivAt_sigma {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => s ^ (-3 : ℤ)) (-3 * s ^ (-3 : ℤ) / s) s := by
  have h := hasDerivAt_zpow (-3) s (Or.inl hs.ne')
  refine h.congr_deriv ?_
  rw [show (-3 : ℤ) - 1 = -3 + -1 by norm_num, zpow_add₀ hs.ne', zpow_neg_one]
  push_cast
  ring

theorem eval_Θ (P : ℝ[X]) (x : ℝ) : (Θ P).eval x = -3 * (x * (derivative P).eval x) := by
  simp [Θ]

theorem hasDerivAt_eval_sigma (P : ℝ[X]) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => P.eval (s ^ (-3 : ℤ))) ((Θ P).eval (s ^ (-3 : ℤ)) / s) s := by
  have h := (P.hasDerivAt (s ^ (-3 : ℤ))).comp s (hasDerivAt_sigma hs)
  refine h.congr_deriv ?_
  rw [eval_Θ]
  ring

/-- The derivative of `Q(σ) / s^k`. -/
theorem hasDerivAt_eval_sigma_div (Q : ℝ[X]) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => Q.eval (s ^ (-3 : ℤ)) / s ^ k)
      ((Θ Q - C (k : ℝ) * Q).eval (s ^ (-3 : ℤ)) / s ^ (k + 1)) s := by
  have hs0 := hs.ne'
  have h := (hasDerivAt_eval_sigma Q hs).fun_div (hasDerivAt_pow k s) (pow_ne_zero k hs0)
  refine h.congr_deriv ?_
  simp only [eval_sub, eval_mul, eval_C]
  cases k with
  | zero =>
    simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- The jet `(q, q′, q″)` of `q = P(σ)` and its third derivative. -/
noncomputable def q0 (P : ℝ[X]) (s : ℝ) : ℝ := P.eval (s ^ (-3 : ℤ))

noncomputable def q1 (P : ℝ[X]) (s : ℝ) : ℝ := (P1 P).eval (s ^ (-3 : ℤ)) / s

noncomputable def q2 (P : ℝ[X]) (s : ℝ) : ℝ := (P2 P).eval (s ^ (-3 : ℤ)) / s ^ 2

noncomputable def q3 (P : ℝ[X]) (s : ℝ) : ℝ := (P3 P).eval (s ^ (-3 : ℤ)) / s ^ 3

theorem hasDerivAt_q0 (P : ℝ[X]) {s : ℝ} (hs : 0 < s) : HasDerivAt (q0 P) (q1 P s) s :=
  hasDerivAt_eval_sigma P hs

theorem hasDerivAt_q1 (P : ℝ[X]) {s : ℝ} (hs : 0 < s) : HasDerivAt (q1 P) (q2 P s) s := by
  have h := hasDerivAt_eval_sigma_div (P1 P) 1 hs
  simp only [pow_one, Nat.cast_one, C_1, one_mul] at h
  exact h

theorem hasDerivAt_q2 (P : ℝ[X]) {s : ℝ} (hs : 0 < s) : HasDerivAt (q2 P) (q3 P s) s := by
  have h := hasDerivAt_eval_sigma_div (P2 P) 2 hs
  have e : Θ (P2 P) - C ((2 : ℕ) : ℝ) * P2 P = P3 P := by
    simp [P3]
  rw [e] at h
  exact h

/-- **The residual of `q = P(σ)`** in the profile equation. -/
theorem resid_eq (d : ℝ) (P : ℝ[X]) {s : ℝ} (hs : 0 < s) (hq : 1 + q0 P s ≠ 0) :
    Calabi.Tail.resid d (q0 P) (q1 P) (q2 P) (q3 P) s =
      (E d P).eval (s ^ (-3 : ℤ)) / (1 + q0 P s) := by
  have hs0 := hs.ne'
  have hσ : s ^ (-3 : ℤ) = 1 / s ^ 3 := by rw [sigma_eq, one_div]
  unfold Calabi.Tail.resid q0 q1 q2 q3
  unfold q0 at hq
  simp only [E, Lop, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one]
  generalize P.eval (s ^ (-3 : ℤ)) = a at hq ⊢
  generalize (P1 P).eval (s ^ (-3 : ℤ)) = a1
  generalize (P2 P).eval (s ^ (-3 : ℤ)) = a2
  generalize (P3 P).eval (s ^ (-3 : ℤ)) = a3
  rw [hσ]
  field_simp
  ring

/-! ### Bounds of all orders -/

variable {S : ℝ}

theorem bd_eval_div (hS : 0 < S) (Q : ℝ[X]) (k l : ℕ) :
    Bd S 0 l (fun s : ℝ => Q.eval (s ^ (-3 : ℤ)) / s ^ k) := by
  have h1 := Bd.poly hS Q l
  have h2 : Bd S 0 l (fun s : ℝ => s ^ (-(k : ℤ))) :=
    Bd.mono_a hS (by omega) (Bd.zpow hS l (-(k : ℤ)))
  have h3 := Bd.mul hS h1 h2
  rw [show (0 : ℤ) + 0 = 0 by norm_num] at h3
  refine Bd.congr (fun s _ => ?_) h3
  rw [zpow_neg s (k : ℤ), zpow_natCast, div_eq_mul_inv]

theorem bd_q (hS : 0 < S) (P : ℝ[X]) (l : ℕ) :
    Bd S 0 l (q0 P) ∧ Bd S 0 l (q1 P) ∧ Bd S 0 l (q2 P) ∧ Bd S 0 l (q3 P) := by
  refine ⟨Bd.poly hS P l, ?_, bd_eval_div hS (P2 P) 2 l, bd_eval_div hS (P3 P) 3 l⟩
  have h := bd_eval_div hS (P1 P) 1 l
  exact Bd.congr (fun s _ => by simp [q1]) h

/-- A polynomial without constant term is `O(s⁻³)` in the variable `s`. -/
theorem bd_q0_decay (hS : 0 < S) {P : ℝ[X]} (hP : P.coeff 0 = 0) (l : ℕ) :
    Bd S (-3) l (q0 P) := by
  obtain ⟨Q, rfl⟩ := X_dvd_iff.2 hP
  have h := Bd.mul hS (Bd.zpow hS l (-3)) (Bd.poly hS Q l)
  rw [show (-3 : ℤ) + 0 = -3 by norm_num] at h
  refine Bd.congr (fun s _ => ?_) h
  simp [q0]

/-- The numerator of the residual of the truncation of order `J` is
`O(s^{-3(J+1)})` with all its derivatives. -/
theorem bd_E_tailPoly (hS : 0 < S) (d : ℝ) (J l : ℕ) :
    Bd S (-(3 * (J + 1 : ℕ) : ℤ)) l (fun s : ℝ => (E d (tailPoly d J)).eval (s ^ (-3 : ℤ))) := by
  obtain ⟨Q, hQ⟩ := tailPoly_dvd d J
  have h := Bd.mul hS (Bd.zpow hS l (-(3 * (J + 1 : ℕ) : ℤ))) (Bd.poly hS Q l)
  rw [add_zero] at h
  refine Bd.congr (fun s _ => ?_) h
  rw [hQ, eval_mul, eval_pow, eval_X, ← zpow_natCast, ← zpow_mul]
  congr 2

end Calabi.Infinity
