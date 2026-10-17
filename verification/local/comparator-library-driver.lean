import Comparator
import Export.Parse
open Lean

def main : IO Unit := do
  let root : System.FilePath := "/private/tmp/calabi-local-exports-20261017"
  let challenge ← Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk (root / "Challenge.ndjson") .read))
  let solution ← Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk (root / "FCSolution.ndjson") .read))
  let targets := #[`CalabiFC.small_energy_singularity, `CalabiFC.small_calabi_energy]
  let axioms := #[``propext, ``Classical.choice, ``Quot.sound]
  let primitives := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
    ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
    ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List,
    ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam,
    ``semiOutParam, ``outParam]
  IO.ofExcept <| Comparator.compareAt challenge solution (targets ++ axioms) #[] primitives
  IO.ofExcept <| Comparator.checkAxioms solution targets #[] axioms
  IO.println "PASS: both target types and dependent definitions match; permitted axioms only."
