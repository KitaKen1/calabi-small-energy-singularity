import Calabi.Shot.Core

/-!
# Integer certificate for the regular solution at the origin

No imports beyond the Lean core and `Calabi.Shot.Core`. In the variable
`r = s^{3/2}` the regular solution is approximated, for the parameters of the
box, by

  `Q₀(r) / 2^192 + z₁ Q₁(r) / 2^128 + z₂ Q₂(r) / 2^128`

with integer polynomials `Q₀, Q₁, Q₂`. With `D = r d/dr` and
`L = (D - 1)(D + 6)(D + 7) Q / r²` the equation is `8 Q + 27 (1 + Q) L = 0`;
`res0` and `resT` are its parts of order zero and one in `z`.
-/

namespace Calabi.Origin

open Calabi.Shot

/-- Coefficients of the polynomial at the centre are integers over `scaleO`. -/
def scaleO : Nat := 2 ^ 192

/-- `[(j+1)(j+8)(j+9) a_j, (j+2)(j+9)(j+10) a_{j+1}, …]`. -/
def opLFrom : Nat → Poly → Poly
  | _, [] => []
  | j, a :: p => (((j + 1) * (j + 8) * (j + 9) : Nat) : Int) * a :: opLFrom (j + 1) p

/-- Coefficients of `(D - 1)(D + 6)(D + 7) q / r²`. -/
def opL (q : Poly) : Poly := opLFrom 0 (q.drop 2)

/-- `scaleO * (1 + Q)`. -/
def onePlusO (q : Poly) : Poly := Poly.add [(scaleO : Int)] q

/-- `scaleO² (8 Q + 27 (1 + Q) L)` for `Q = q0 / scaleO`. -/
def res0 (q0 : Poly) : Poly :=
  Poly.add (Poly.smul (8 * (scaleO : Int)) q0) (Poly.smul 27 (Poly.mul (onePlusO q0) (opL q0)))

/-- The part of the same expression that is linear in a tangent polynomial. -/
def resT (q0 qm : Poly) : Poly :=
  Poly.add (Poly.smul (8 * (scaleO : Int)) qm)
    (Poly.smul 27 (Poly.add (Poly.mul qm (opL q0)) (Poly.mul (onePlusO q0) (opL qm))))

/-- `(Q, D Q, D² Q)` at `r = 1`. -/
def jetOne (q : Poly) : Jet :=
  ⟨Poly.evalInt 1 q, Poly.evalInt 1 (Poly.derivFrom 0 q),
    Poly.evalInt 1 (Poly.derivFrom 0 (Poly.derivFrom 0 q))⟩

structure OriginSummary where
  /-- `ℓ¹` norm of `res0`. -/
  e0 : Nat
  /-- Sum of the `ℓ¹` norms of the two `resT`. -/
  e1 : Nat
  /-- `ℓ¹` norm of `Q₀`. -/
  n0 : Nat
  /-- Sum of the `ℓ¹` norms of `Q₁`, `Q₂`. -/
  nQ : Nat
  /-- Sum of the `ℓ¹` norms of `opL Q₁`, `opL Q₂`. -/
  nL : Nat
  j0 : Jet
  j1 : Jet
  j2 : Jet
  deriving DecidableEq, Repr

/-- The verified digest, or `none` when the first two coefficients are not the
prescribed parameters `d` and `k` and their derivatives. -/
def originSummarize (dnum knum dz1 kz1 dz2 kz2 : Int) (q0 q1 q2 : Poly) :
    Option OriginSummary :=
  if q0.getD 0 0 = dnum * 2 ^ 64 ∧ q0.getD 1 0 = knum * 2 ^ 64 ∧
      q1.getD 0 0 = dz1 * 2 ^ 64 ∧ q1.getD 1 0 = kz1 * 2 ^ 64 ∧
      q2.getD 0 0 = dz2 * 2 ^ 64 ∧ q2.getD 1 0 = kz2 * 2 ^ 64 then
    some {
      e0 := Poly.l1 (res0 q0)
      e1 := Poly.l1 (resT q0 q1) + Poly.l1 (resT q0 q2)
      n0 := Poly.l1 q0
      nQ := Poly.l1 q1 + Poly.l1 q2
      nL := Poly.l1 (opL q1) + Poly.l1 (opL q2)
      j0 := jetOne q0
      j1 := jetOne q1
      j2 := jetOne q2 }
  else none

end Calabi.Origin
