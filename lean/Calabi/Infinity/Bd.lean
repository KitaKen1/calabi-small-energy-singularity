import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Functions with controlled derivatives on a half-line

`Bd S a l f` says that `f` has `l` derivatives on `(S, ∞)` and that `f` and
these derivatives are bounded by multiples of `s ^ a`, `a ∈ ℤ`. The class is
closed under sums, products (the exponents add) and inverses, so derivative
bounds of all orders follow from a differential equation by induction on `l`
without any explicit Leibniz formula.
-/

open Set Filter
open scoped Topology

namespace Calabi.Infinity

/-- `|f s| ≤ C s ^ a` on `(S, ∞)`. -/
def Bd0 (S : ℝ) (a : ℤ) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s, S < s → |f s| ≤ C * s ^ a

/-- `f` and its first `l` derivatives are `O(s ^ a)` on `(S, ∞)`. -/
def Bd (S : ℝ) (a : ℤ) : ℕ → (ℝ → ℝ) → Prop
  | 0, f => Bd0 S a f
  | l + 1, f => Bd0 S a f ∧ ∃ f' : ℝ → ℝ, (∀ s, S < s → HasDerivAt f (f' s) s) ∧ Bd S a l f'

variable {S : ℝ} {a b : ℤ} {l : ℕ} {f g : ℝ → ℝ}

theorem Bd.bd0 : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a l f → Bd0 S a f
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem Bd.mono_l : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a (l + 1) f → Bd S a l f
  | 0, _, h => h.1
  | _ + 1, _, ⟨h0, f', hd, h'⟩ => ⟨h0, f', hd, Bd.mono_l h'⟩

theorem Bd.succ_of (h0 : Bd0 S a f) (hd : ∀ s, S < s → HasDerivAt f (g s) s) (hg : Bd S a l g) :
    Bd S a (l + 1) f :=
  ⟨h0, g, hd, hg⟩

theorem Bd0.congr (h : ∀ s, S < s → f s = g s) : Bd0 S a f → Bd0 S a g := by
  rintro ⟨C, hC, hb⟩
  exact ⟨C, hC, fun s hs => by rw [← h s hs]; exact hb s hs⟩

theorem Bd.congr : ∀ {l : ℕ} {f g : ℝ → ℝ}, (∀ s, S < s → f s = g s) → Bd S a l f → Bd S a l g
  | 0, _, _, h, hf => Bd0.congr h hf
  | _ + 1, _, _, h, ⟨h0, f', hd, h'⟩ => by
    refine ⟨Bd0.congr h h0, f', fun s hs => ?_, h'⟩
    refine (hd s hs).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with u hu using (h u hu).symm

/-- The derivative of a function of the class is in the class. -/
theorem Bd.deriv_of (hd : ∀ s, S < s → HasDerivAt f (g s) s) (h : Bd S a (l + 1) f) :
    Bd S a l g := by
  obtain ⟨-, f', hd', h'⟩ := h
  exact Bd.congr (fun s hs => (hd' s hs).unique (hd s hs)) h'

theorem Bd0.mono_S {S' : ℝ} (hS : S ≤ S') : Bd0 S a f → Bd0 S' a f := by
  rintro ⟨C, hC, hb⟩
  exact ⟨C, hC, fun s hs => hb s (hS.trans_lt hs)⟩

theorem Bd.mono_S {S' : ℝ} (hS : S ≤ S') : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a l f → Bd S' a l f
  | 0, _, h => Bd0.mono_S hS h
  | _ + 1, _, ⟨h0, f', hd, h'⟩ =>
    ⟨Bd0.mono_S hS h0, f', fun s hs => hd s (hS.trans_lt hs), Bd.mono_S hS h'⟩

theorem zpow_le_of_le (hS : 0 < S) (hab : a ≤ b) {s : ℝ} (hs : S < s) :
    s ^ a ≤ S ^ (a - b) * s ^ b := by
  have hs0 : 0 < s := hS.trans hs
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hab)
  have e1 : a - b = -(n : ℤ) := by omega
  have e2 : s ^ a = s ^ (a - b) * s ^ b := by
    rw [← zpow_add₀ hs0.ne']
    congr 1
    ring
  rw [e2, e1, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (zpow_pos hs0 b).le
  exact inv_anti₀ (pow_pos hS n) (pow_le_pow_left₀ hS.le hs.le n)

theorem Bd0.mono_a (hS : 0 < S) (hab : a ≤ b) : Bd0 S a f → Bd0 S b f := by
  rintro ⟨C, hC, hb⟩
  refine ⟨C * S ^ (a - b), mul_nonneg hC (zpow_pos hS _).le, fun s hs => ?_⟩
  have h1 := hb s hs
  have h2 := mul_le_mul_of_nonneg_left (zpow_le_of_le hS hab hs) hC
  calc |f s| ≤ C * s ^ a := h1
    _ ≤ C * (S ^ (a - b) * s ^ b) := h2
    _ = C * S ^ (a - b) * s ^ b := by ring

theorem Bd.mono_a (hS : 0 < S) (hab : a ≤ b) : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a l f → Bd S b l f
  | 0, _, h => Bd0.mono_a hS hab h
  | _ + 1, _, ⟨h0, f', hd, h'⟩ => ⟨Bd0.mono_a hS hab h0, f', hd, Bd.mono_a hS hab h'⟩

theorem Bd0.add (hf : Bd0 S a f) (hg : Bd0 S a g) : Bd0 S a (fun s => f s + g s) := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun s hs => ?_⟩
  have := abs_add_le (f s) (g s)
  nlinarith [hb s hs, hd s hs]

theorem Bd.add : ∀ {l : ℕ} {f g : ℝ → ℝ}, Bd S a l f → Bd S a l g →
    Bd S a l (fun s => f s + g s)
  | 0, _, _, hf, hg => Bd0.add hf hg
  | _ + 1, _, _, ⟨f0, f', fd, hf'⟩, ⟨g0, g', gd, hg'⟩ =>
    ⟨Bd0.add f0 g0, fun s => f' s + g' s, fun s hs => (fd s hs).fun_add (gd s hs),
      Bd.add hf' hg'⟩

theorem Bd0.const_mul (c : ℝ) (hf : Bd0 S a f) : Bd0 S a (fun s => c * f s) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, fun s hs => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb s hs) (abs_nonneg c)

theorem Bd.const_mul (c : ℝ) : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a l f → Bd S a l (fun s => c * f s)
  | 0, _, hf => Bd0.const_mul c hf
  | _ + 1, _, ⟨f0, f', fd, hf'⟩ =>
    ⟨Bd0.const_mul c f0, fun s => c * f' s, fun s hs => (fd s hs).const_mul c,
      Bd.const_mul c hf'⟩

theorem Bd.neg (hf : Bd S a l f) : Bd S a l (fun s => -f s) :=
  Bd.congr (fun s _ => by ring) (Bd.const_mul (-1) hf)

theorem Bd.sub (hf : Bd S a l f) (hg : Bd S a l g) : Bd S a l (fun s => f s - g s) :=
  Bd.congr (fun s _ => by ring) (Bd.add hf (Bd.neg hg))

theorem Bd0.mul (hS : 0 < S) (hf : Bd0 S a f) (hg : Bd0 S b g) :
    Bd0 S (a + b) (fun s => f s * g s) := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun s hs => ?_⟩
  have hs0 : 0 < s := hS.trans hs
  rw [abs_mul, zpow_add₀ hs0.ne']
  calc |f s| * |g s| ≤ (C * s ^ a) * (D * s ^ b) :=
        mul_le_mul (hb s hs) (hd s hs) (abs_nonneg _) (mul_nonneg hC (zpow_pos hs0 a).le)
    _ = C * D * (s ^ a * s ^ b) := by ring

theorem Bd.mul (hS : 0 < S) : ∀ {l : ℕ} {f g : ℝ → ℝ}, Bd S a l f → Bd S b l g →
    Bd S (a + b) l (fun s => f s * g s)
  | 0, _, _, hf, hg => Bd0.mul hS hf hg
  | l + 1, f, g, hf, hg => by
    obtain ⟨f0, f', fd, hf'⟩ := hf
    obtain ⟨g0, g', gd, hg'⟩ := hg
    have hfl : Bd S a l f := Bd.mono_l ⟨f0, f', fd, hf'⟩
    have hgl : Bd S b l g := Bd.mono_l ⟨g0, g', gd, hg'⟩
    refine ⟨Bd0.mul hS f0 g0, fun s => f' s * g s + f s * g' s,
      fun s hs => (fd s hs).fun_mul (gd s hs), ?_⟩
    exact Bd.add (Bd.mul hS hf' hgl) (Bd.mul hS hfl hg')

theorem Bd.zero_fun : ∀ l : ℕ, Bd S a l (fun _ => (0 : ℝ))
  | 0 => ⟨0, le_rfl, fun s _ => by simp⟩
  | l + 1 => ⟨⟨0, le_rfl, fun s _ => by simp⟩, fun _ => 0, fun s _ => hasDerivAt_const s 0,
      Bd.zero_fun l⟩

theorem Bd.const (c : ℝ) : ∀ l : ℕ, Bd S 0 l (fun _ => c)
  | 0 => ⟨|c|, abs_nonneg c, fun s _ => by simp⟩
  | l + 1 => ⟨⟨|c|, abs_nonneg c, fun s _ => by simp⟩, fun _ => 0,
      fun s _ => hasDerivAt_const s c, Bd.zero_fun l⟩

theorem Bd.zpow (hS : 0 < S) : ∀ (l : ℕ) (b : ℤ), Bd S b l (fun s => s ^ b)
  | 0, b => ⟨1, zero_le_one, fun s hs => by
      rw [abs_of_pos (zpow_pos (hS.trans hs) b), one_mul]⟩
  | l + 1, b => by
    refine ⟨⟨1, zero_le_one, fun s hs => by
      rw [abs_of_pos (zpow_pos (hS.trans hs) b), one_mul]⟩, fun s => (b : ℝ) * s ^ (b - 1),
      fun s hs => hasDerivAt_zpow b s (Or.inl (hS.trans hs).ne'), ?_⟩
    exact Bd.mono_a hS (by omega) (Bd.const_mul (b : ℝ) (Bd.zpow hS l (b - 1)))

/-- The inverse of a function of the class that is bounded below. -/
theorem Bd.inv (hS : 0 < S) {c : ℝ} (hc : 0 < c) : ∀ {l : ℕ} {f : ℝ → ℝ},
    (∀ s, S < s → c ≤ f s) → Bd S 0 l f → Bd S 0 l (fun s => (f s)⁻¹)
  | 0, f, hlow, _ => ⟨c⁻¹, (inv_pos.2 hc).le, fun s hs => by
      have hf : 0 < f s := hc.trans_le (hlow s hs)
      rw [zpow_zero, mul_one, abs_of_pos (inv_pos.2 hf)]
      exact inv_anti₀ hc (hlow s hs)⟩
  | l + 1, f, hlow, hf => by
    obtain ⟨f0, f', fd, hf'⟩ := hf
    have hfl : Bd S 0 l f := Bd.mono_l ⟨f0, f', fd, hf'⟩
    have hinv : Bd S 0 l (fun s => (f s)⁻¹) := Bd.inv hS hc hlow hfl
    refine ⟨⟨c⁻¹, (inv_pos.2 hc).le, fun s hs => by
      have hfs : 0 < f s := hc.trans_le (hlow s hs)
      rw [zpow_zero, mul_one, abs_of_pos (inv_pos.2 hfs)]
      exact inv_anti₀ hc (hlow s hs)⟩, fun s => -f' s / f s ^ 2,
      fun s hs => (fd s hs).fun_inv (hc.trans_le (hlow s hs)).ne', ?_⟩
    have hprod := Bd.mul hS (Bd.neg hf') (Bd.mul hS hinv hinv)
    rw [show (0 : ℤ) + (0 + 0) = 0 by norm_num] at hprod
    refine Bd.congr (fun s hs => ?_) hprod
    have hfs : f s ≠ 0 := (hc.trans_le (hlow s hs)).ne'
    field_simp

/-- A polynomial in `σ = s⁻³`. -/
theorem Bd.poly (hS : 0 < S) (P : Polynomial ℝ) (l : ℕ) :
    Bd S 0 l (fun s => P.eval (s ^ (-3 : ℤ))) := by
  induction P using Polynomial.induction_on with
  | C c =>
    simp only [Polynomial.eval_C]
    exact Bd.const c l
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Bd.add hp hq
  | monomial n c h =>
    have hσ : Bd S 0 l (fun s : ℝ => s ^ (-3 : ℤ)) := Bd.mono_a hS (by norm_num) (Bd.zpow hS l (-3))
    have hprod := Bd.mul hS h hσ
    rw [show (0 : ℤ) + 0 = 0 by norm_num] at hprod
    refine Bd.congr (fun s _ => ?_) hprod
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

/-- A function with one more controlled derivative is `C^l`. -/
theorem Bd.contDiffOn : ∀ {l : ℕ} {f : ℝ → ℝ}, Bd S a (l + 1) f → ContDiffOn ℝ l f (Ioi S)
  | 0, f, ⟨_, f', fd, _⟩ => by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun s hs => (fd s hs).continuousAt.continuousWithinAt
  | l + 1, f, ⟨_, f', fd, hf'⟩ => by
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun s hs => (fd s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (Bd.contDiffOn hf').congr fun s hs => (fd s hs).deriv

end Calabi.Infinity
