/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import FormalConjecturesUtil.Answer
public import FormalConjecturesUtil.Attributes.Basic

/-!
Local standalone entry point for the FC-style statement.
The official category/AMS and answer implementations are vendored unchanged; its source is
pinned in vendor-lock.json. In Formal Conjectures itself the statement uses the
upstream FormalConjecturesUtil entry point, including its additional imports and linters.
-/
