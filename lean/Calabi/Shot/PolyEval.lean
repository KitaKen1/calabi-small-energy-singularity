import Calabi.Shot.Core
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Real meaning of the integer polynomial computations

`Poly.eval p x` is the real value at `x` of the coefficient list `p`. Every
operation of `Calabi.Shot.Core` is shown to compute what its name says.
-/

namespace Calabi.Shot

namespace Poly

/-- Real value of an integer coefficient list. -/
noncomputable def eval : Poly → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * eval p x

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := by rw [eval]

@[simp] theorem eval_cons (a : Int) (p : Poly) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := by rw [eval]

theorem eval_add (p q : Poly) (x : ℝ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      simp only [add, eval_cons, ih, Int.cast_add]
      ring

theorem eval_smul (c : Int) (p : Poly) (x : ℝ) :
    eval (smul c p) x = (c : ℝ) * eval p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, eval_cons, ih, Int.cast_mul]
    ring

theorem eval_mul (p q : Poly) (x : ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, eval_add, eval_smul, eval_cons, ih, Int.cast_zero]
    ring

theorem eval_derivFrom (k : ℕ) (p : Poly) (x : ℝ) :
    eval (derivFrom k p) x = (k : ℝ) * eval p x + x * eval (deriv p) x := by
  induction p generalizing k with
  | nil => simp [derivFrom, deriv]
  | cons a p ih =>
    have h1 := ih (k + 1)
    have h2 := ih 1
    have e : deriv (a :: p) = derivFrom 1 p := rfl
    simp only [derivFrom, e, eval_cons, Int.cast_mul, Int.cast_natCast]
    rw [h1, h2]
    push_cast
    ring

/-- The formal derivative is the derivative. -/
theorem hasDerivAt_eval (p : Poly) (x : ℝ) : HasDerivAt (eval p) (eval (deriv p) x) x := by
  induction p with
  | nil =>
    have h : eval ([] : Poly) = fun _ : ℝ => (0 : ℝ) := by
      funext y
      simp
    have e : eval (deriv ([] : Poly)) x = 0 := by simp [deriv]
    rw [h, e]
    exact hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    have h : eval (a :: p) = fun y : ℝ => (a : ℝ) + y * eval p y := by
      funext y
      simp
    have hd : eval (deriv (a :: p)) x = 1 * eval p x + x * eval (deriv p) x := by
      have e : deriv (a :: p) = derivFrom 1 p := rfl
      rw [e, eval_derivFrom, Nat.cast_one]
    rw [h, hd]
    exact ((hasDerivAt_id' x).fun_mul ih).const_add (a : ℝ)

theorem abs_eval_le (p : Poly) {x : ℝ} (hx : |x| ≤ 1) : |eval p x| ≤ (l1 p : ℝ) := by
  induction p with
  | nil => simp [l1]
  | cons a p ih =>
    have ha : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hmul : |x * eval p x| ≤ (l1 p : ℝ) := by
      rw [abs_mul]
      calc |x| * |eval p x| ≤ 1 * (l1 p : ℝ) :=
            mul_le_mul hx ih (abs_nonneg _) zero_le_one
        _ = (l1 p : ℝ) := one_mul _
    calc |eval (a :: p) x| = |(a : ℝ) + x * eval p x| := by rw [eval_cons]
      _ ≤ |(a : ℝ)| + |x * eval p x| := abs_add_le _ _
      _ ≤ |(a : ℝ)| + (l1 p : ℝ) := by linarith
      _ = (l1 (a :: p) : ℝ) := by
        rw [l1, Nat.cast_add, ha]

theorem eval_intCast (x : Int) (p : Poly) : eval p (x : ℝ) = ((evalInt x p : Int) : ℝ) := by
  induction p with
  | nil => simp [evalInt]
  | cons a p ih =>
    simp only [eval_cons, evalInt, ih, Int.cast_add, Int.cast_mul]

end Poly

/-! ### Block operators -/

theorem eval_sig (A : Int) (p : Poly) (x : ℝ) :
    Poly.eval (sig A p) x = ((A : ℝ) + x) * Poly.eval p x := by
  simp only [sig, Poly.eval_add, Poly.eval_smul, Poly.eval_cons, Int.cast_zero]
  ring

theorem eval_sig3 (A : Int) (p : Poly) (x : ℝ) :
    Poly.eval (sig3 A p) x = ((A : ℝ) + x) ^ 3 * Poly.eval p x := by
  simp only [sig3, eval_sig]
  ring

theorem eval_opA (A : Int) (q : Poly) (x : ℝ) :
    Poly.eval (opA A q) x =
      4 * ((A : ℝ) + x) ^ 3 * Poly.eval (Poly.deriv (Poly.deriv (Poly.deriv q))) x +
        84 * ((A : ℝ) + x) ^ 2 * Poly.eval (Poly.deriv (Poly.deriv q)) x +
        337 * ((A : ℝ) + x) * Poly.eval (Poly.deriv q) x - 567 * Poly.eval q x := by
  simp only [opA, Poly.eval_add, Poly.eval_smul, eval_sig3, eval_sig]
  push_cast
  ring

theorem eval_onePlus (P : Poly) (x : ℝ) :
    Poly.eval (onePlus P) x = (scaleP : ℝ) + Poly.eval P x := by
  simp only [onePlus, Poly.eval_add, Poly.eval_cons, Poly.eval_nil]
  push_cast
  ring

end Calabi.Shot
