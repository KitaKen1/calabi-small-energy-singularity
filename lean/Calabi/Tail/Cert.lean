import Calabi.Shot.Core

/-!
# Integer certificate for the approximate tail

No imports beyond the Lean core and `Calabi.Shot.Core`. The approximate
solution on `[56, ∞)` is `a(s) = P(τ) / 2^128` with `τ = (56 / s)³` and an
integer polynomial `P`. Since `s d/ds τ^j = -3 j τ^j`,

  `a′ = P₁(τ) / (2^128 s)`,  `a″ = P₂(τ) / (2^128 s²)`,  `a‴ = P₃(τ) / (2^128 s³)`

with integer polynomials `P₁, P₂, P₃`, and `4 · 56³ · 2^128 (2^128 + P)` times
the residual of `a` is the integer polynomial `tailRes` in `τ ∈ (0, 1]`.
-/

namespace Calabi.Tail

open Calabi.Shot

/-- `θ = s d/ds` on polynomials in `τ = (56 / s)³`. -/
def theta (q : Poly) : Poly := Poly.smul (-3) (0 :: Poly.deriv q)

def tailP1 (P : Poly) : Poly := theta P

/-- `(θ - 1) θ P`. -/
def tailP2 (P : Poly) : Poly := Poly.add (theta (tailP1 P)) (Poly.smul (-1) (tailP1 P))

/-- `(θ - 2) (θ - 1) θ P`. -/
def tailP3 (P : Poly) : Poly := Poly.add (theta (tailP2 P)) (Poly.smul (-2) (tailP2 P))

/-- `4 P₃ + 84 P₂ + 337 P₁ - 567 P + 567 dnum`. -/
def tailLin (dnum : Int) (P : Poly) : Poly :=
  Poly.add [567 * dnum]
    (Poly.add
      (Poly.add (Poly.add (Poly.smul 4 (tailP3 P)) (Poly.smul 84 (tailP2 P)))
        (Poly.smul 337 (tailP1 P)))
      (Poly.smul (-567) P))

/-- `τ (2^128 + P) (4 P₃ + 84 P₂ + 337 P₁ - 567 P + 567 dnum) + 4 · 56³ · 2^128 P`. -/
def tailRes (dnum : Int) (P : Poly) : Poly :=
  Poly.add (0 :: Poly.mul (onePlus P) (tailLin dnum P))
    (Poly.smul (4 * 56 ^ 3 * (scaleP : Int)) P)

structure TailSummary where
  /-- `P(1)`: the value at `s = 56` is `v / 2^128`. -/
  v : Int
  /-- `P₁(1)`: the first derivative at `s = 56` is `d1 / (56 · 2^128)`. -/
  d1 : Int
  /-- `P₂(1)`: the second derivative at `s = 56` is `d2 / (56² · 2^128)`. -/
  d2 : Int
  /-- The `ℓ¹` norm of `P`: `|a| ≤ l1 / 2^128` on `[56, ∞)`. -/
  l1 : Nat
  /-- Residual bound over `scaleE`, for the centre parameter `dnum / 2^128`. -/
  eps : Nat
  deriving DecidableEq, Repr

/-- The verified digest of the approximate tail, or `none` when a side
condition fails: `|a| ≤ 1/200`, and the factor that multiplies a displacement
of the parameter in the residual is at most `1/1000`. -/
def tailSummarize (dnum : Int) (P : Poly) : Option TailSummary :=
  if Poly.l1 P * 200 ≤ scaleP ∧
      567 * (scaleP + Poly.l1 P) * 1000 ≤ 4 * 56 ^ 3 * (scaleP - Poly.l1 P) then
    some {
      v := Poly.evalInt 1 P
      d1 := Poly.evalInt 1 (tailP1 P)
      d2 := Poly.evalInt 1 (tailP2 P)
      l1 := Poly.l1 P
      eps := ceilDiv (Poly.l1 (tailRes dnum P) * scaleE)
        (4 * 56 ^ 3 * scaleP * (scaleP - Poly.l1 P)) }
  else none

end Calabi.Tail
