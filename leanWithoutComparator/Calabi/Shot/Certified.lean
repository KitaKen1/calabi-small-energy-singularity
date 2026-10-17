import Calabi.Shot.Core

/-!
# Lists of kernel-checked blocks

No imports beyond the Lean core and `Calabi.Shot.Core`. The generated data
files prove one statement `summarize dnum blk = some sum` per block. These
lemmas assemble them into statements about lists without evaluating anything
again.
-/

namespace Calabi.Shot

/-- The kernel has recomputed the summary of the block. -/
def Certified (dnum : Int) (p : Block × Summary) : Prop :=
  summarize dnum p.1 = some p.2

theorem certified_nil (dnum : Int) :
    ∀ p ∈ ([] : List (Block × Summary)), Certified dnum p := by
  intro p hp
  cases hp

theorem certified_cons {dnum : Int} {b : Block} {s : Summary} {l : List (Block × Summary)}
    (h : summarize dnum b = some s) (hl : ∀ p ∈ l, Certified dnum p) :
    ∀ p ∈ (b, s) :: l, Certified dnum p := by
  intro p hp
  cases hp with
  | head => exact h
  | tail _ hp' => exact hl p hp'

theorem certified_append {dnum : Int} {l₁ l₂ : List (Block × Summary)}
    (h₁ : ∀ p ∈ l₁, Certified dnum p) (h₂ : ∀ p ∈ l₂, Certified dnum p) :
    ∀ p ∈ l₁ ++ l₂, Certified dnum p := by
  intro p hp
  cases List.mem_append.1 hp with
  | inl h => exact h₁ p h
  | inr h => exact h₂ p h

end Calabi.Shot
