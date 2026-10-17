import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# The iteration with an approximate right inverse

Section 6.4 of the manuscript solves `P V = -E - N(V)` by a contraction with an
exact right inverse of `P`, obtained from an approximate one by a Neumann
series. This file gives an equivalent scheme that uses the approximate right
inverse directly and does not need it to be linear, or even to be a function:

  `u_{n+1} = u_n + s_n`,   `s_n` an approximate solution of `P s = r_n`,
  `r_n = E₀ - N(u_n) - P u_n`.

The hypotheses are stated for abstract bound predicates (`BX u a` reads
`‖u‖_X ≤ a`, and similarly `BX'` for the weaker norm `X′` and `BY` for the
source norm):

* `P` is additive on functions with finite `X′` norm (the bound predicates may
  carry regularity conditions, so that `P` need not be additive on arbitrary
  functions);
* every `g` with `‖g‖_Y ≤ m` has an approximate solution `s` with
  `‖s‖_X ≤ C_S m` and `‖g - P s‖_Y ≤ m / 2`;
* `‖N(u) - N(v)‖_Y ≤ C_N e ‖u - v‖_{X′}` on the ball of radius `e` of `X′`;
* `4 C_N C_S e ≤ 1`, a starting point with `‖u₁‖_{X′} ≤ e/2` and a residual
  `‖r₁‖_Y ≤ ε₁` with `8 C_S ε₁ ≤ e`.

Then the residuals decay like `ε₁ (3/4)ⁿ`, the increments like
`C_S ε₁ (3/4)ⁿ` in `X`, and all iterates stay in the ball (`newton_iteration`).
-/

namespace Calabi.Newton

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- **The iteration with an approximate right inverse.** -/
theorem newton_iteration (BX BX' : X → ℝ → Prop) (BY : Y → ℝ → Prop) (P N : X → Y)
    (E₀ : Y) {CS CN e ε₁ : ℝ} (u₁ : X) (hCS : 0 ≤ CS) (he : 0 < e) (hε : 0 < ε₁)
    (hX'add : ∀ u v a b, BX' u a → BX' v b → BX' (u + v) (a + b))
    (hX'mono : ∀ u a b, BX' u a → a ≤ b → BX' u b)
    (hX'zero : BX' 0 0)
    (hXX' : ∀ u a, BX u a → BX' u a)
    (hYsub : ∀ g h a b, BY g a → BY h b → BY (g - h) (a + b))
    (hYmono : ∀ g a b, BY g a → a ≤ b → BY g b)
    (hP : ∀ u d a b, BX' u a → BX' d b → P (u + d) = P u + P d)
    (hS : ∀ g m, 0 < m → BY g m → ∃ s : X, BX s (CS * m) ∧ BY (g - P s) (m / 2))
    (hN : ∀ u v d, BX' u e → BX' v e → 0 ≤ d → BX' (u - v) d → BY (N u - N v) (CN * e * d))
    (hsmall : 4 * CN * CS * e ≤ 1) (hstart : BX' u₁ (e / 2))
    (hres : BY (E₀ - N u₁ - P u₁) ε₁) (hε₁ : 8 * CS * ε₁ ≤ e) :
    ∃ u : ℕ → X, u 0 = u₁ ∧
      (∀ n, BX (u (n + 1) - u n) (CS * (ε₁ * (3 / 4) ^ n))) ∧
      (∀ n, BY (E₀ - N (u n) - P (u n)) (ε₁ * (3 / 4) ^ n)) ∧ (∀ n, BX' (u n) e) := by
  have hq : ∀ n : ℕ, (0 : ℝ) < (3 / 4) ^ n := fun n => by positivity
  -- the iterates stay in the ball
  have hball : ∀ (n : ℕ) (u : X), BX' (u - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ n)) → BX' u e := by
    intro n u hu
    have h1 := hX'add _ _ _ _ hstart hu
    have e1 : u₁ + (u - u₁) = u := by abel
    rw [e1] at h1
    refine hX'mono _ _ _ h1 ?_
    have h2 : 4 * CS * ε₁ * (1 - (3 / 4) ^ n) ≤ 4 * CS * ε₁ := by
      have h3 : 0 ≤ 4 * CS * ε₁ := by positivity
      nlinarith [hq n]
    linarith
  -- one step
  have step : ∀ (n : ℕ) (u : X),
      BY (E₀ - N u - P u) (ε₁ * (3 / 4) ^ n) ∧ BX' (u - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ n)) →
      ∃ u' : X, (BY (E₀ - N u' - P u') (ε₁ * (3 / 4) ^ (n + 1)) ∧
        BX' (u' - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ (n + 1)))) ∧
        BX (u' - u) (CS * (ε₁ * (3 / 4) ^ n)) := by
    rintro n u ⟨ihr, ihu⟩
    have hm : 0 < ε₁ * (3 / 4) ^ n := mul_pos hε (hq n)
    obtain ⟨s, hd, hrem⟩ := hS _ _ hm ihr
    have hd' := hXX' _ _ hd
    have hunext : BX' (u + s - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ (n + 1))) := by
      have h1 := hX'add _ _ _ _ ihu hd'
      have e1 : u - u₁ + s = u + s - u₁ := by abel
      rw [e1] at h1
      refine hX'mono _ _ _ h1 (le_of_eq ?_)
      rw [pow_succ]
      ring
    have es : u + s - u = s := by abel
    refine ⟨u + s, ⟨?_, hunext⟩, by rw [es]; exact hd⟩
    have hdiff : BX' (u + s - u) (CS * (ε₁ * (3 / 4) ^ n)) := by
      rw [es]
      exact hd'
    have hNL := hN (u + s) u _ (hball (n + 1) _ hunext) (hball n _ ihu)
      (mul_nonneg hCS hm.le) hdiff
    have h1 := hYsub _ _ _ _ hrem hNL
    have e2 : E₀ - N u - P u - P s - (N (u + s) - N u) = E₀ - N (u + s) - P (u + s) := by
      rw [hP u s _ _ (hball n _ ihu) hd']
      abel
    rw [e2] at h1
    refine hYmono _ _ _ h1 ?_
    have h3 : CN * e * (CS * (ε₁ * (3 / 4) ^ n)) ≤ ε₁ * (3 / 4) ^ n / 4 := by
      have h4 : CN * e * (CS * (ε₁ * (3 / 4) ^ n))
          = 4 * CN * CS * e * (ε₁ * (3 / 4) ^ n) / 4 := by ring
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_right hsmall hm.le
      linarith
    rw [pow_succ]
    linarith
  -- the start
  have h0 : BY (E₀ - N u₁ - P u₁) (ε₁ * (3 / 4) ^ 0) ∧
      BX' (u₁ - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ 0)) := by
    constructor
    · simpa using hres
    · simpa using hX'zero
  -- the sequence
  let f : (n : ℕ) → {u : X // BY (E₀ - N u - P u) (ε₁ * (3 / 4) ^ n) ∧
      BX' (u - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ n))} := fun n =>
    Nat.rec (motive := fun n => {u : X // BY (E₀ - N u - P u) (ε₁ * (3 / 4) ^ n) ∧
      BX' (u - u₁) (4 * CS * ε₁ * (1 - (3 / 4) ^ n))}) ⟨u₁, h0⟩
      (fun n p => ⟨Classical.choose (step n p.1 p.2),
        (Classical.choose_spec (step n p.1 p.2)).1⟩) n
  refine ⟨fun n => (f n).1, rfl, fun n => ?_, fun n => (f n).2.1,
    fun n => hball n _ (f n).2.2⟩
  exact (Classical.choose_spec (step n (f n).1 (f n).2)).2

end Calabi.Newton
