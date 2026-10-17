/-!
# Integer computations for the finite shot

This file has no imports beyond the Lean core. It defines the exact integer
computations that the kernel evaluates on a polynomial certificate. Nothing
here asserts an analytic fact; the meaning of each quantity is proved in the
modules that import Mathlib.

A block has a power of two `H` and an integer `A`; its variable `t` runs over
`[-1, 1]`, with `s = (A + t) / H` and `σ = A + t`. In that variable the profile
equation, multiplied by `4 σ³`, reads

  `4 σ³ p‴ + 84 σ² p″ + 337 σ p′ - 567 (p - d) + (4 σ³ / H³) p / (1 + p) = 0`.
-/

namespace Calabi.Shot

/-- Coefficient lists, lowest degree first. -/
abbrev Poly := List Int

namespace Poly

def add : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : Int) : Poly → Poly
  | [] => []
  | a :: p => (c * a) :: smul c p

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- `derivFrom k [a_k, a_{k+1}, …] = [k a_k, (k+1) a_{k+1}, …]`. -/
def derivFrom : Nat → Poly → Poly
  | _, [] => []
  | k, a :: p => ((k : Int) * a) :: derivFrom (k + 1) p

def deriv : Poly → Poly
  | [] => []
  | _ :: p => derivFrom 1 p

/-- Sum of absolute values of the coefficients. -/
def l1 : Poly → Nat
  | [] => 0
  | a :: p => a.natAbs + l1 p

/-- Value at an integer point. -/
def evalInt (x : Int) : Poly → Int
  | [] => 0
  | a :: p => a + x * evalInt x p

end Poly

/-- Coefficients of the profile polynomial are integers over `scaleP`. -/
def scaleP : Nat := 2 ^ 128

/-- Coefficients of the tangent polynomials are integers over `scaleU`. -/
def scaleU : Nat := 2 ^ 64

/-- Error bounds are natural numbers over `scaleE`. -/
def scaleE : Nat := 2 ^ 160

/-- Polynomial certificate on one block: the profile and four tangents. -/
structure Block where
  H : Nat
  A : Nat
  P : Poly
  U0 : Poly
  U1 : Poly
  U2 : Poly
  Ud : Poly

/-- Value, first and second derivative, as integers over the relevant scale. -/
structure Jet where
  v : Int
  d1 : Int
  d2 : Int
  deriving DecidableEq, Repr

structure Summary where
  H : Nat
  A : Nat
  /-- Jet of the profile polynomial at `t = -1`. -/
  start : Jet
  /-- Jet of the profile polynomial at `t = 1`. -/
  stop : Jet
  /-- Jets at `t = 1` of the four tangent polynomials. -/
  t0 : Jet
  t1 : Jet
  t2 : Jet
  td : Jet
  /-- Bound for the defect of the profile polynomial, over `scaleE`. -/
  eps : Nat
  deriving DecidableEq, Repr

/-- Multiplication by `σ = A + t`. -/
def sig (A : Int) (p : Poly) : Poly := Poly.add (Poly.smul A p) (0 :: p)

def sig3 (A : Int) (p : Poly) : Poly := sig A (sig A (sig A p))

/-- `4 σ³ q‴ + 84 σ² q″ + 337 σ q′ - 567 q`. -/
def opA (A : Int) (q : Poly) : Poly :=
  Poly.add
    (Poly.add
      (Poly.add (Poly.smul 4 (sig3 A (Poly.deriv (Poly.deriv (Poly.deriv q)))))
        (Poly.smul 84 (sig A (sig A (Poly.deriv (Poly.deriv q))))))
      (Poly.smul 337 (sig A (Poly.deriv q))))
    (Poly.smul (-567) q)

/-- `scaleP * (1 + P)`. -/
def onePlus (P : Poly) : Poly := Poly.add [(scaleP : Int)] P

/-- `scaleP² · 4 σ³ H³ (1 + P) · (defect of P)` as an integer polynomial. -/
def resP (dnum : Int) (b : Block) : Poly :=
  Poly.add
    (Poly.smul ((b.H ^ 3 : Nat) : Int)
      (Poly.mul (onePlus b.P) (Poly.add [567 * dnum] (opA (b.A : Int) b.P))))
    (Poly.smul (4 * (scaleP : Int)) (sig3 (b.A : Int) b.P))

/-- `scaleP² scaleU · 4 σ³ H³ (1 + P)² · (defect of a tangent)`; `forcing` is
`567 * scaleU` for the parameter column and `0` otherwise. -/
def resU (b : Block) (u : Poly) (forcing : Int) : Poly :=
  Poly.add
    (Poly.smul ((b.H ^ 3 : Nat) : Int)
      (Poly.mul (Poly.mul (onePlus b.P) (onePlus b.P)) (Poly.add [forcing] (opA (b.A : Int) u))))
    (Poly.smul (4 * (scaleP : Int) * (scaleP : Int)) (sig3 (b.A : Int) u))

/-- `scaleP` times a lower bound for `1 + P` on `[-1, 1]`. -/
def minP (b : Block) : Int :=
  match b.P with
  | [] => (scaleP : Int)
  | a :: p => (scaleP : Int) + a - (Poly.l1 p : Int)

def jetAt (x : Int) (p : Poly) : Jet :=
  ⟨Poly.evalInt x p, Poly.evalInt x (Poly.deriv p), Poly.evalInt x (Poly.deriv (Poly.deriv p))⟩

/-- `4 (A - 1)³ H³`, a lower bound for `4 σ³ H³` on the block. -/
def sigBound (b : Block) : Nat := 4 * (b.A - 1) ^ 3 * b.H ^ 3

/-- Side condition for one tangent polynomial: size, unit data at `t = -1`,
and a defect below `2^-40`. -/
def tangentOk (b : Block) (u : Poly) (forcing : Int) (unit : Jet) : Bool :=
  decide (Poly.l1 u ≤ 4 * scaleU) && decide (jetAt (-1) u = unit) &&
    decide (Poly.l1 (resU b u forcing) * 2 ^ 40 ≤
      scaleU * sigBound b * ((minP b).toNat * (minP b).toNat))

def Block.ok (b : Block) : Bool :=
  decide (16 ≤ b.H) && decide (129 ≤ b.A) &&
    decide (7 * (scaleP : Int) ≤ 100 * minP b) &&
    tangentOk b b.U0 0 ⟨scaleU, 0, 0⟩ &&
    tangentOk b b.U1 0 ⟨0, scaleU, 0⟩ &&
    tangentOk b b.U2 0 ⟨0, 0, scaleU⟩ &&
    tangentOk b b.Ud (567 * (scaleU : Int)) ⟨0, 0, 0⟩

/-- Smallest natural number `q` with `a ≤ q * b`, for `b > 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + (b - 1)) / b

def epsP (dnum : Int) (b : Block) : Nat :=
  ceilDiv (Poly.l1 (resP dnum b) * scaleE) (scaleP * sigBound b * (minP b).toNat)

/-- The verified digest of a block, or `none` when a side condition fails. -/
def summarize (dnum : Int) (b : Block) : Option Summary :=
  if b.ok then
    some {
      H := b.H
      A := b.A
      start := jetAt (-1) b.P
      stop := jetAt 1 b.P
      t0 := jetAt 1 b.U0
      t1 := jetAt 1 b.U1
      t2 := jetAt 1 b.U2
      td := jetAt 1 b.Ud
      eps := epsP dnum b }
  else none

end Calabi.Shot
