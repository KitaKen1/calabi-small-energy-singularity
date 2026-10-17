import Calabi.Shot.BlockSpec
import Calabi.Shot.Chain

/-!
# Real meaning of the integer frames

`Mat3.app X v` applies the integer matrix `X` to a real vector. The lemmas
here are the linear algebra used to carry the remainder bound from one block
to the next: `B (adj B) = det B`, composition, and absolute-value bounds that
match the kernel's `absApply`.
-/

namespace Calabi.Shot

/-- Real application of an integer `3 × 3` matrix. -/
noncomputable def Mat3.app (X : Mat3) (v : State) : State :=
  ((X.a11 : ℝ) * v.1 + (X.a12 : ℝ) * v.2.1 + (X.a13 : ℝ) * v.2.2,
    (X.a21 : ℝ) * v.1 + (X.a22 : ℝ) * v.2.1 + (X.a23 : ℝ) * v.2.2,
    (X.a31 : ℝ) * v.1 + (X.a32 : ℝ) * v.2.1 + (X.a33 : ℝ) * v.2.2)

/-- Real application of the `3 × 2` response to the two parameters. -/
noncomputable def Mat32.app (L : Mat32) (z1 z2 : ℝ) : State :=
  ((L.a11 : ℝ) * z1 + (L.a12 : ℝ) * z2, (L.a21 : ℝ) * z1 + (L.a22 : ℝ) * z2,
    (L.a31 : ℝ) * z1 + (L.a32 : ℝ) * z2)

/-- Change of block variable on a jet: `diag(1, g, g²)`. -/
noncomputable def resc (g : ℝ) (v : State) : State := (v.1, g * v.2.1, g * g * v.2.2)

/-- A jet of integers as a real vector. -/
noncomputable def jetVec (j : Jet) : State := ((j.v : ℝ), (j.d1 : ℝ), (j.d2 : ℝ))

theorem Mat3.app_add (X : Mat3) (u v : State) : X.app (u + v) = X.app u + X.app v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Prod.fst_add, Prod.snd_add] <;> ring

theorem Mat3.app_sub (X : Mat3) (u v : State) : X.app (u - v) = X.app u - X.app v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem Mat3.app_smul (X : Mat3) (c : ℝ) (v : State) : X.app (c • v) = c • X.app v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem Mat3.app_mul (X Y : Mat3) (v : State) : (X.mul Y).app v = X.app (Y.app v) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Mat3.mul, Int.cast_add, Int.cast_mul] <;> ring

/-- `B (adj B) = det B`. -/
theorem Mat3.app_adj (B : Mat3) (v : State) : B.app (B.adj.app v) = (B.det : ℝ) • v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Mat3.adj, Mat3.det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Int.cast_add, Int.cast_sub, Int.cast_mul] <;> ring

theorem Mat3.app_rescale (g : Int) (X : Mat3) (v : State) :
    (X.rescale g).app v = resc (g : ℝ) (X.app v) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Mat3.app, Mat3.rescale, resc, Int.cast_mul] <;> ring

theorem resc_add (g : ℝ) (u v : State) : resc g (u + v) = resc g u + resc g v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [resc, Prod.fst_add, Prod.snd_add] <;> ring

theorem resc_sub (g : ℝ) (u v : State) : resc g (u - v) = resc g u - resc g v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [resc, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem resc_smul (g c : ℝ) (v : State) : resc g (c • v) = c • resc g v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [resc, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem abs_lin3 {a b c x y z n1 n2 n3 : ℝ} (h1 : |x| ≤ n1) (h2 : |y| ≤ n2) (h3 : |z| ≤ n3) :
    |a * x + b * y + c * z| ≤ |a| * n1 + |b| * n2 + |c| * n3 := by
  have e1 : |a * x| ≤ |a| * n1 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have e2 : |b * y| ≤ |b| * n2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
  have e3 : |c * z| ≤ |c| * n3 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
  have t1 := abs_add_le (a * x + b * y) (c * z)
  have t2 := abs_add_le (a * x) (b * y)
  linarith

/-- Componentwise bound for `X v`, in the form computed by `absApply`. -/
theorem Mat3.abs_app_le (X : Mat3) {v : State} {ν : Nat3} {E : ℝ}
    (h1 : |v.1| ≤ (ν.a : ℝ) / E) (h2 : |v.2.1| ≤ (ν.b : ℝ) / E) (h3 : |v.2.2| ≤ (ν.c : ℝ) / E) :
    |(X.app v).1| ≤ ((X.absApply ν).a : ℝ) / E ∧ |(X.app v).2.1| ≤ ((X.absApply ν).b : ℝ) / E ∧
      |(X.app v).2.2| ≤ ((X.absApply ν).c : ℝ) / E := by
  have c1 : ((X.absApply ν).a : ℝ) / E =
      |(X.a11 : ℝ)| * ((ν.a : ℝ) / E) + |(X.a12 : ℝ)| * ((ν.b : ℝ) / E)
        + |(X.a13 : ℝ)| * ((ν.c : ℝ) / E) := by
    simp only [Mat3.absApply, Nat.cast_add, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    ring
  have c2 : ((X.absApply ν).b : ℝ) / E =
      |(X.a21 : ℝ)| * ((ν.a : ℝ) / E) + |(X.a22 : ℝ)| * ((ν.b : ℝ) / E)
        + |(X.a23 : ℝ)| * ((ν.c : ℝ) / E) := by
    simp only [Mat3.absApply, Nat.cast_add, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    ring
  have c3 : ((X.absApply ν).c : ℝ) / E =
      |(X.a31 : ℝ)| * ((ν.a : ℝ) / E) + |(X.a32 : ℝ)| * ((ν.b : ℝ) / E)
        + |(X.a33 : ℝ)| * ((ν.c : ℝ) / E) := by
    simp only [Mat3.absApply, Nat.cast_add, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    ring
  rw [c1, c2, c3]
  exact ⟨abs_lin3 h1 h2 h3, abs_lin3 h1 h2 h3, abs_lin3 h1 h2 h3⟩

/-- `a / b ≤ ceilDiv a b` for natural numbers, as reals. -/
theorem div_le_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (ceilDiv a b : ℝ) := by
  have h := le_ceilDiv_mul a hb
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  exact_mod_cast h

end Calabi.Shot
