import Lake
open Lake DSL

package calabi where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI where
  srcDir := "vendor"
  globs := #[`OAI.+]

lean_lib Calabi

lean_lib Integration

@[default_target] lean_lib FCSolution

