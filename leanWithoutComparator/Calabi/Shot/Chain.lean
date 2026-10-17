import Calabi.Shot.Core

/-!
# Integer computations for the chain of blocks

No imports beyond the Lean core and `Calabi.Shot.Core`. A block summary
controls one block. This file defines the kernel computation that carries a
remainder bound across all blocks, in a moving integer frame.

At the start of block `j`, in the block's own jet `(p, p', p'')`, the true jet
for the parameter `z ∈ [-2^-56, 2^-56]²` is written

  `start_j / 2^128 + L_j z / 2^64 + r_j`,

and the invariant is `|adj(B_j) r_j| ≤ ρ_j / 2^160` componentwise, where `B_j`
is an integer frame with positive determinant.
-/

namespace Calabi.Shot

structure Mat3 where
  a11 : Int
  a12 : Int
  a13 : Int
  a21 : Int
  a22 : Int
  a23 : Int
  a31 : Int
  a32 : Int
  a33 : Int
  deriving DecidableEq, Repr

/-- A `3 × 2` integer matrix: the linear response to the two parameters. -/
structure Mat32 where
  a11 : Int
  a12 : Int
  a21 : Int
  a22 : Int
  a31 : Int
  a32 : Int
  deriving DecidableEq, Repr

structure Nat3 where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

namespace Mat3

def mul (X Y : Mat3) : Mat3 :=
  ⟨X.a11 * Y.a11 + X.a12 * Y.a21 + X.a13 * Y.a31,
    X.a11 * Y.a12 + X.a12 * Y.a22 + X.a13 * Y.a32,
    X.a11 * Y.a13 + X.a12 * Y.a23 + X.a13 * Y.a33,
    X.a21 * Y.a11 + X.a22 * Y.a21 + X.a23 * Y.a31,
    X.a21 * Y.a12 + X.a22 * Y.a22 + X.a23 * Y.a32,
    X.a21 * Y.a13 + X.a22 * Y.a23 + X.a23 * Y.a33,
    X.a31 * Y.a11 + X.a32 * Y.a21 + X.a33 * Y.a31,
    X.a31 * Y.a12 + X.a32 * Y.a22 + X.a33 * Y.a32,
    X.a31 * Y.a13 + X.a32 * Y.a23 + X.a33 * Y.a33⟩

/-- The adjugate: `X * adj X = det X • 1`. -/
def adj (X : Mat3) : Mat3 :=
  ⟨X.a22 * X.a33 - X.a23 * X.a32, X.a13 * X.a32 - X.a12 * X.a33, X.a12 * X.a23 - X.a13 * X.a22,
    X.a23 * X.a31 - X.a21 * X.a33, X.a11 * X.a33 - X.a13 * X.a31, X.a13 * X.a21 - X.a11 * X.a23,
    X.a21 * X.a32 - X.a22 * X.a31, X.a12 * X.a31 - X.a11 * X.a32, X.a11 * X.a22 - X.a12 * X.a21⟩

def det (X : Mat3) : Int :=
  X.a11 * (X.a22 * X.a33 - X.a23 * X.a32) - X.a12 * (X.a21 * X.a33 - X.a23 * X.a31)
    + X.a13 * (X.a21 * X.a32 - X.a22 * X.a31)

/-- Left multiplication by `diag(1, g, g²)`: the change of block variable. -/
def rescale (g : Int) (X : Mat3) : Mat3 :=
  ⟨X.a11, X.a12, X.a13, g * X.a21, g * X.a22, g * X.a23,
    g * g * X.a31, g * g * X.a32, g * g * X.a33⟩

/-- `(Σ_k |X_ik| ρ_k)_i`. -/
def absApply (X : Mat3) (ρ : Nat3) : Nat3 :=
  ⟨X.a11.natAbs * ρ.a + X.a12.natAbs * ρ.b + X.a13.natAbs * ρ.c,
    X.a21.natAbs * ρ.a + X.a22.natAbs * ρ.b + X.a23.natAbs * ρ.c,
    X.a31.natAbs * ρ.a + X.a32.natAbs * ρ.b + X.a33.natAbs * ρ.c⟩

end Mat3

/-- The tangent jets at `t = 1` as columns: the block transfer over `scaleU`. -/
def transfer (s : Summary) : Mat3 :=
  ⟨s.t0.v, s.t1.v, s.t2.v, s.t0.d1, s.t1.d1, s.t2.d1, s.t0.d2, s.t1.d2, s.t2.d2⟩

/-- `2^(160 - 64 - 56)`: converts `|L| · 2^-64 · 2^-56` to the scale of `ρ`. -/
def boxShift : Nat := 2 ^ 40

/-- `2^(128 + 56 - 160)`: converts a mismatch over `2^128` times the box radius. -/
def misShift : Nat := 2 ^ 24

/-- `2^(160 - 112)`: the tolerance `2^-112` for the jet handed over at `s = 1`. -/
def initTol : Nat := 2 ^ 48

/-- The size of the deviation `|ξ₀| + |ξ₁| + |ξ₂| + |η|` on a block, over `scaleE`. -/
def deviation (dz1 dz2 : Int) (B : Mat3) (L : Mat32) (ρ : Nat3) : Nat :=
  (L.a11.natAbs + L.a12.natAbs + (L.a21.natAbs + L.a22.natAbs) + (L.a31.natAbs + L.a32.natAbs))
      * boxShift
    + (ceilDiv (B.absApply ρ).a B.det.toNat + ceilDiv (B.absApply ρ).b B.det.toNat
        + ceilDiv (B.absApply ρ).c B.det.toNat)
    + (dz1.natAbs + dz2.natAbs) * boxShift

/-- The bound for the block error, over `scaleE`. -/
def blockErr (s : Summary) (y : Nat) : Nat :=
  8 * (s.eps + ceilDiv y (2 ^ 40) + ceilDiv (14 * y * y) scaleE)

/-- `D T L + (D t_d) dzᵀ - 2^64 L'`: what rounding the response leaves behind. -/
def mismatch (dz1 dz2 : Int) (s : Summary) (g : Int) (L Ln : Mat32) : Mat32 :=
  let T := (transfer s).rescale g
  ⟨T.a11 * L.a11 + T.a12 * L.a21 + T.a13 * L.a31 + s.td.v * dz1 - (scaleU : Int) * Ln.a11,
    T.a11 * L.a12 + T.a12 * L.a22 + T.a13 * L.a32 + s.td.v * dz2 - (scaleU : Int) * Ln.a12,
    T.a21 * L.a11 + T.a22 * L.a21 + T.a23 * L.a31 + g * s.td.d1 * dz1 - (scaleU : Int) * Ln.a21,
    T.a21 * L.a12 + T.a22 * L.a22 + T.a23 * L.a32 + g * s.td.d1 * dz2 - (scaleU : Int) * Ln.a22,
    T.a31 * L.a11 + T.a32 * L.a21 + T.a33 * L.a31 + g * g * s.td.d2 * dz1
      - (scaleU : Int) * Ln.a31,
    T.a31 * L.a12 + T.a32 * L.a22 + T.a33 * L.a32 + g * g * s.td.d2 * dz2
      - (scaleU : Int) * Ln.a32⟩

/-- What is injected into the remainder on one block, before the frame. -/
def injected (dz1 dz2 : Int) (s : Summary) (g : Nat) (L Ln : Mat32) (err : Nat) : Nat3 :=
  let m := mismatch dz1 dz2 s g L Ln
  ⟨ceilDiv (m.a11.natAbs + m.a12.natAbs) misShift + err,
    ceilDiv (m.a21.natAbs + m.a22.natAbs) misShift + g * err,
    ceilDiv (m.a31.natAbs + m.a32.natAbs) misShift + g * g * err⟩

/-- One block: the next remainder bound, or `none` when a side condition fails.
`g` is the ratio of the block scales `H` of this block and the next. -/
def step (dz1 dz2 : Int) (s : Summary) (g : Nat) (B Bn : Mat3) (L Ln : Mat32) (ρ : Nat3) :
    Option Nat3 :=
  let y := deviation dz1 dz2 B L ρ
  if 0 < B.det ∧ 0 < Bn.det ∧ y ≤ scaleE / 1024 ∧ s.eps ≤ scaleE / 1024 then
    let inj := injected dz1 dz2 s g L Ln (blockErr s y)
    let M := (Bn.adj.mul ((transfer s).rescale g)).mul B
    let p := M.absApply ρ
    let q := Bn.adj.absApply inj
    some ⟨ceilDiv p.a (B.det.toNat * scaleU) + q.a, ceilDiv p.b (B.det.toNat * scaleU) + q.b,
      ceilDiv p.c (B.det.toNat * scaleU) + q.c⟩
  else none

/-- The next block starts where this one ends, `(A + 1) / H = (A' - 1) / H'`,
and its certified jet at the start continues the jet of this block. -/
def continues (s sn : Summary) (g : Nat) : Bool :=
  decide (s.H = g * sn.H) && decide (s.A + 1 + g = g * sn.A) &&
    decide (sn.start.v = s.stop.v) &&
    decide (sn.start.d1 = (g : Int) * s.stop.d1) &&
    decide (sn.start.d2 = (g : Int) * (g : Int) * s.stop.d2)

/-- The remainder bound at the start: tolerance `2^-112` in each component. -/
def initial (B : Mat3) : Nat3 :=
  B.adj.absApply ⟨initTol, initTol, initTol⟩

/-- Runs all blocks. `frames` and `Ls` have one more entry than `sums`. -/
def chainRun (dz1 dz2 : Int) : List Summary → List Mat3 → List Mat32 → Nat3 → Option Nat3
  | [], _, _, ρ => some ρ
  | [s], B :: Bn :: _, L :: Ln :: _, ρ => step dz1 dz2 s 1 B Bn L Ln ρ
  | s :: sn :: rest, B :: Bn :: frames, L :: Ln :: Ls, ρ =>
    if continues s sn (s.H / sn.H) then
      match step dz1 dz2 s (s.H / sn.H) B Bn L Ln ρ with
      | some ρn => chainRun dz1 dz2 (sn :: rest) (Bn :: frames) (Ln :: Ls) ρn
      | none => none
    else none
  | _, _, _, _ => none

/-- Componentwise bound for the remainder itself, over `scaleE`. -/
def radius (B : Mat3) (ρ : Nat3) : Nat3 :=
  ⟨ceilDiv (B.absApply ρ).a B.det.toNat, ceilDiv (B.absApply ρ).b B.det.toNat,
    ceilDiv (B.absApply ρ).c B.det.toNat⟩

/-- The first summary with its frame and response. -/
def chainStart : List Summary → List Mat3 → List Mat32 → Option (Summary × Mat3 × Mat32)
  | s :: _, B :: _, L :: _ => some (s, B, L)
  | _, _, _ => none

/-- The last summary with the frame and the response that follow it. -/
def chainEnd : List Summary → List Mat3 → List Mat32 → Option (Summary × Mat3 × Mat32)
  | [s], _ :: Bn :: _, _ :: Ln :: _ => some (s, Bn, Ln)
  | _ :: sn :: rest, _ :: frames, _ :: Ls => chainEnd (sn :: rest) frames Ls
  | _, _, _ => none

/-- The block lies in `lo ≤ s ≤ hi`. -/
def inRange (lo hi : Nat) (s : Summary) : Bool :=
  decide (lo * s.H + 1 ≤ s.A) && decide (s.A + 1 ≤ hi * s.H)

end Calabi.Shot
