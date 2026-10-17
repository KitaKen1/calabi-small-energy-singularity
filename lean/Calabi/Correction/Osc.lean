import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Sum

/-!
# Scaled bounds in the momentum coordinate

Lemma 6.2 of the manuscript writes `Osc(s^q)` for a quantity whose derivatives
of spatial order `j` and temporal order `k` are bounded by `C s^{q - j - 4k}`.
In the momentum coordinate `x = r²`, with `ς = x + √(-t) = σ²`, one
`x`-derivative costs `ς⁻¹` and one time derivative costs `ς⁻²`. This file sets
up the first-order version of this calculus for functions of `(t, x)` on
`[-T, 0) × [0, 1]`:

* `Osc T n M c cx ct`: `|c| ≤ M ς^n`, `c_x = cx` with `|cx| ≤ M ς^{n-1}`, and
  `c_t = ct` with `|ct| ≤ M ς^{n-2}`;
* sums, products (the orders add), lowering of the order;
* `Tower T n M K c d`: `c j` is the `j`-th `x`-derivative, of order `n - j`,
  with time derivative `d j`, for `j < K`;
* `Tower.mul`: the Leibniz rule for towers.
-/

open Set Finset

namespace Calabi.Osc

/-- `ς(t, x) = x + √(-t)`, the square of the scale `σ`. -/
noncomputable def vs (t x : ℝ) : ℝ := x + Real.sqrt (-t)

theorem vs_pos {T t x : ℝ} (ht : t ∈ Ico (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < vs t x := by
  have h := Real.sqrt_pos.2 (by linarith [ht.2] : (0 : ℝ) < -t)
  unfold vs
  linarith [hx.1]

theorem vs_le {T t x : ℝ} (hT : T ≤ 1) (ht : t ∈ Ico (-T) 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    vs t x ≤ 2 := by
  have h : Real.sqrt (-t) ≤ 1 := by
    have h1 := Real.sqrt_le_sqrt (by linarith [ht.1] : -t ≤ (1 : ℝ))
    rwa [Real.sqrt_one] at h1
  unfold vs
  linarith [hx.2]

theorem zpow_le_lower {ς S : ℝ} (hς : 0 < ς) (hS : ς ≤ S) (m : ℤ) (k : ℕ) :
    ς ^ m ≤ S ^ k * ς ^ (m - k) := by
  have e : ς ^ m = ς ^ k * ς ^ (m - k) := by
    rw [← zpow_natCast, ← zpow_add₀ hς.ne']
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hς.le hS k) (zpow_nonneg hς.le _)

/-- Scaled bounds of order `n` for a function of `(t, x)` on `[-T, 0) × [0, 1]`,
with its `x`-derivative `cx` and its time derivative `ct`. The derivative
relations are required for all `t < 0`, the bounds for `-T ≤ t < 0`. -/
structure Osc (T : ℝ) (n : ℤ) (M : ℝ) (c cx ct : ℝ → ℝ → ℝ) : Prop where
  bound : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, |c t x| ≤ M * vs t x ^ n
  dx : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (c t) (cx t x) (Icc 0 1) x
  dx_bound : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, |cx t x| ≤ M * vs t x ^ (n - 1)
  dt : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun τ => c τ x) (ct t x) t
  dt_bound : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, |ct t x| ≤ M * vs t x ^ (n - 2)

variable {T : ℝ} {n : ℤ} {M : ℝ} {c cx ct : ℝ → ℝ → ℝ}

theorem Osc.cast {n' : ℤ} (h : Osc T n M c cx ct) (e : n = n') : Osc T n' M c cx ct := e ▸ h

/-- The derivatives may be replaced by functions that agree with them on the
domain. -/
theorem Osc.congr_deriv {cx' ct' : ℝ → ℝ → ℝ} (h : Osc T n M c cx ct)
    (hx : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, cx' t x = cx t x)
    (ht : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, ct' t x = ct t x) : Osc T n M c cx' ct' where
  bound := h.bound
  dx t ht' x hx' := by
    rw [hx t ht' x hx']
    exact h.dx t ht' x hx'
  dx_bound t ht' x hx' := by
    rw [hx t ht'.2 x hx']
    exact h.dx_bound t ht' x hx'
  dt t ht' x hx' := by
    rw [ht t ht' x hx']
    exact h.dt t ht' x hx'
  dt_bound t ht' x hx' := by
    rw [ht t ht'.2 x hx']
    exact h.dt_bound t ht' x hx'

/-- The function may be replaced by one that agrees with it for `t < 0` and
`0 ≤ x ≤ 1`. -/
theorem Osc.congr_fun {c' : ℝ → ℝ → ℝ} (h : Osc T n M c cx ct)
    (hc : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, c' t x = c t x) : Osc T n M c' cx ct where
  bound t ht x hx := by
    rw [hc t ht.2 x hx]
    exact h.bound t ht x hx
  dx t ht x hx := (h.dx t ht x hx).congr (fun y hy => hc t ht y hy) (hc t ht x hx)
  dx_bound := h.dx_bound
  dt t ht x hx := by
    refine (h.dt t ht x hx).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with τ hτ using hc τ hτ x hx
  dt_bound := h.dt_bound

theorem Osc.mono {M' : ℝ} (h : Osc T n M c cx ct) (hM : M ≤ M') : Osc T n M' c cx ct where
  bound t ht x hx := (h.bound t ht x hx).trans
    (mul_le_mul_of_nonneg_right hM (zpow_nonneg (vs_pos ht hx).le _))
  dx := h.dx
  dx_bound t ht x hx := (h.dx_bound t ht x hx).trans
    (mul_le_mul_of_nonneg_right hM (zpow_nonneg (vs_pos ht hx).le _))
  dt := h.dt
  dt_bound t ht x hx := (h.dt_bound t ht x hx).trans
    (mul_le_mul_of_nonneg_right hM (zpow_nonneg (vs_pos ht hx).le _))

theorem Osc.zero (hM : 0 ≤ M) :
    Osc T n M (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  bound t ht x hx := by
    rw [abs_zero]
    exact mul_nonneg hM (zpow_nonneg (vs_pos ht hx).le _)
  dx t _ x _ := hasDerivWithinAt_const x _ 0
  dx_bound t ht x hx := by
    rw [abs_zero]
    exact mul_nonneg hM (zpow_nonneg (vs_pos ht hx).le _)
  dt t _ x _ := hasDerivAt_const t 0
  dt_bound t ht x hx := by
    rw [abs_zero]
    exact mul_nonneg hM (zpow_nonneg (vs_pos ht hx).le _)

theorem Osc.add {M' : ℝ} {c' cx' ct' : ℝ → ℝ → ℝ} (h : Osc T n M c cx ct)
    (h' : Osc T n M' c' cx' ct') :
    Osc T n (M + M') (fun t x => c t x + c' t x) (fun t x => cx t x + cx' t x)
      (fun t x => ct t x + ct' t x) where
  bound t ht x hx := by
    calc |c t x + c' t x| ≤ |c t x| + |c' t x| := abs_add_le _ _
      _ ≤ M * vs t x ^ n + M' * vs t x ^ n := add_le_add (h.bound t ht x hx) (h'.bound t ht x hx)
      _ = (M + M') * vs t x ^ n := by ring
  dx t ht x hx := (h.dx t ht x hx).fun_add (h'.dx t ht x hx)
  dx_bound t ht x hx := by
    calc |cx t x + cx' t x| ≤ |cx t x| + |cx' t x| := abs_add_le _ _
      _ ≤ M * vs t x ^ (n - 1) + M' * vs t x ^ (n - 1) :=
        add_le_add (h.dx_bound t ht x hx) (h'.dx_bound t ht x hx)
      _ = (M + M') * vs t x ^ (n - 1) := by ring
  dt t ht x hx := (h.dt t ht x hx).fun_add (h'.dt t ht x hx)
  dt_bound t ht x hx := by
    calc |ct t x + ct' t x| ≤ |ct t x| + |ct' t x| := abs_add_le _ _
      _ ≤ M * vs t x ^ (n - 2) + M' * vs t x ^ (n - 2) :=
        add_le_add (h.dt_bound t ht x hx) (h'.dt_bound t ht x hx)
      _ = (M + M') * vs t x ^ (n - 2) := by ring

theorem Osc.const_mul (k : ℝ) (h : Osc T n M c cx ct) :
    Osc T n (|k| * M) (fun t x => k * c t x) (fun t x => k * cx t x) (fun t x => k * ct t x) where
  bound t ht x hx := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.bound t ht x hx) (abs_nonneg _)
  dx t ht x hx := (h.dx t ht x hx).const_mul k
  dx_bound t ht x hx := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.dx_bound t ht x hx) (abs_nonneg _)
  dt t ht x hx := (h.dt t ht x hx).const_mul k
  dt_bound t ht x hx := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.dt_bound t ht x hx) (abs_nonneg _)

theorem Osc.neg (h : Osc T n M c cx ct) :
    Osc T n M (fun t x => -c t x) (fun t x => -cx t x) (fun t x => -ct t x) where
  bound t ht x hx := by
    rw [abs_neg]
    exact h.bound t ht x hx
  dx t ht x hx := (h.dx t ht x hx).fun_neg
  dx_bound t ht x hx := by
    rw [abs_neg]
    exact h.dx_bound t ht x hx
  dt t ht x hx := (h.dt t ht x hx).fun_neg
  dt_bound t ht x hx := by
    rw [abs_neg]
    exact h.dt_bound t ht x hx

theorem Osc.sub {M' : ℝ} {c' cx' ct' : ℝ → ℝ → ℝ} (h : Osc T n M c cx ct)
    (h' : Osc T n M' c' cx' ct') :
    Osc T n (M + M') (fun t x => c t x - c' t x) (fun t x => cx t x - cx' t x)
      (fun t x => ct t x - ct' t x) := by
  have h2 := h.add h'.neg
  have e1 : (fun t x => c t x - c' t x) = fun t x => c t x + -c' t x := by
    funext t x
    ring
  have e2 : (fun t x => cx t x - cx' t x) = fun t x => cx t x + -cx' t x := by
    funext t x
    ring
  have e3 : (fun t x => ct t x - ct' t x) = fun t x => ct t x + -ct' t x := by
    funext t x
    ring
  rw [e1, e2, e3]
  exact h2

/-- **Products**: the orders add. -/
theorem Osc.mul {n' : ℤ} {M' : ℝ} {c' cx' ct' : ℝ → ℝ → ℝ} (h : Osc T n M c cx ct)
    (h' : Osc T n' M' c' cx' ct') (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    Osc T (n + n') (2 * M * M') (fun t x => c t x * c' t x)
      (fun t x => cx t x * c' t x + c t x * cx' t x)
      (fun t x => ct t x * c' t x + c t x * ct' t x) where
  bound t ht x hx := by
    have hς := vs_pos ht hx
    have h0 : 0 ≤ M * M' * vs t x ^ (n + n') :=
      mul_nonneg (mul_nonneg hM hM') (zpow_nonneg hς.le _)
    calc |c t x * c' t x| = |c t x| * |c' t x| := abs_mul _ _
      _ ≤ M * vs t x ^ n * (M' * vs t x ^ n') :=
        mul_le_mul (h.bound t ht x hx) (h'.bound t ht x hx) (abs_nonneg _)
          (mul_nonneg hM (zpow_nonneg hς.le _))
      _ = M * M' * vs t x ^ (n + n') := by
        rw [zpow_add₀ hς.ne']
        ring
      _ ≤ 2 * M * M' * vs t x ^ (n + n') := by linarith
  dx t ht x hx := (h.dx t ht x hx).fun_mul (h'.dx t ht x hx)
  dx_bound t ht x hx := by
    have hς := vs_pos ht hx
    have e1 : vs t x ^ (n - 1) * vs t x ^ n' = vs t x ^ (n + n' - 1) := by
      rw [← zpow_add₀ hς.ne']
      congr 1
      ring
    have e2 : vs t x ^ n * vs t x ^ (n' - 1) = vs t x ^ (n + n' - 1) := by
      rw [← zpow_add₀ hς.ne']
      congr 1
      ring
    calc |cx t x * c' t x + c t x * cx' t x|
        ≤ |cx t x * c' t x| + |c t x * cx' t x| := abs_add_le _ _
      _ = |cx t x| * |c' t x| + |c t x| * |cx' t x| := by rw [abs_mul, abs_mul]
      _ ≤ M * vs t x ^ (n - 1) * (M' * vs t x ^ n') + M * vs t x ^ n * (M' * vs t x ^ (n' - 1)) :=
        add_le_add
          (mul_le_mul (h.dx_bound t ht x hx) (h'.bound t ht x hx) (abs_nonneg _)
            (mul_nonneg hM (zpow_nonneg hς.le _)))
          (mul_le_mul (h.bound t ht x hx) (h'.dx_bound t ht x hx) (abs_nonneg _)
            (mul_nonneg hM (zpow_nonneg hς.le _)))
      _ = M * M' * (vs t x ^ (n - 1) * vs t x ^ n') + M * M' * (vs t x ^ n * vs t x ^ (n' - 1)) := by
        ring
      _ = 2 * M * M' * vs t x ^ (n + n' - 1) := by
        rw [e1, e2]
        ring
  dt t ht x hx := (h.dt t ht x hx).fun_mul (h'.dt t ht x hx)
  dt_bound t ht x hx := by
    have hς := vs_pos ht hx
    have e1 : vs t x ^ (n - 2) * vs t x ^ n' = vs t x ^ (n + n' - 2) := by
      rw [← zpow_add₀ hς.ne']
      congr 1
      ring
    have e2 : vs t x ^ n * vs t x ^ (n' - 2) = vs t x ^ (n + n' - 2) := by
      rw [← zpow_add₀ hς.ne']
      congr 1
      ring
    calc |ct t x * c' t x + c t x * ct' t x|
        ≤ |ct t x * c' t x| + |c t x * ct' t x| := abs_add_le _ _
      _ = |ct t x| * |c' t x| + |c t x| * |ct' t x| := by rw [abs_mul, abs_mul]
      _ ≤ M * vs t x ^ (n - 2) * (M' * vs t x ^ n') + M * vs t x ^ n * (M' * vs t x ^ (n' - 2)) :=
        add_le_add
          (mul_le_mul (h.dt_bound t ht x hx) (h'.bound t ht x hx) (abs_nonneg _)
            (mul_nonneg hM (zpow_nonneg hς.le _)))
          (mul_le_mul (h.bound t ht x hx) (h'.dt_bound t ht x hx) (abs_nonneg _)
            (mul_nonneg hM (zpow_nonneg hς.le _)))
      _ = M * M' * (vs t x ^ (n - 2) * vs t x ^ n') + M * M' * (vs t x ^ n * vs t x ^ (n' - 2)) := by
        ring
      _ = 2 * M * M' * vs t x ^ (n + n' - 2) := by
        rw [e1, e2]
        ring

/-- **Lowering the order** on a bounded scale. -/
theorem Osc.lower {S : ℝ} (h : Osc T n M c cx ct) (hM : 0 ≤ M) (k : ℕ)
    (hS : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, vs t x ≤ S) :
    Osc T (n - k) (M * S ^ k) c cx ct where
  bound t ht x hx := by
    calc |c t x| ≤ M * vs t x ^ n := h.bound t ht x hx
      _ ≤ M * (S ^ k * vs t x ^ (n - k)) :=
        mul_le_mul_of_nonneg_left (zpow_le_lower (vs_pos ht hx) (hS t ht x hx) n k) hM
      _ = M * S ^ k * vs t x ^ (n - k) := by ring
  dx := h.dx
  dx_bound t ht x hx := by
    have e : n - (k : ℤ) - 1 = n - 1 - k := by ring
    rw [e]
    calc |cx t x| ≤ M * vs t x ^ (n - 1) := h.dx_bound t ht x hx
      _ ≤ M * (S ^ k * vs t x ^ (n - 1 - k)) :=
        mul_le_mul_of_nonneg_left (zpow_le_lower (vs_pos ht hx) (hS t ht x hx) (n - 1) k) hM
      _ = M * S ^ k * vs t x ^ (n - 1 - k) := by ring
  dt := h.dt
  dt_bound t ht x hx := by
    have e : n - (k : ℤ) - 2 = n - 2 - k := by ring
    rw [e]
    calc |ct t x| ≤ M * vs t x ^ (n - 2) := h.dt_bound t ht x hx
      _ ≤ M * (S ^ k * vs t x ^ (n - 2 - k)) :=
        mul_le_mul_of_nonneg_left (zpow_le_lower (vs_pos ht hx) (hS t ht x hx) (n - 2) k) hM
      _ = M * S ^ k * vs t x ^ (n - 2 - k) := by ring

/-- Finite sums. -/
theorem Osc.sum {ι : Type*} (s : Finset ι) {N : ι → ℝ} {a ax at' : ι → ℝ → ℝ → ℝ}
    (hN : ∀ i ∈ s, 0 ≤ N i) (h : ∀ i ∈ s, Osc T n (N i) (a i) (ax i) (at' i)) :
    Osc T n (∑ i ∈ s, N i) (fun t x => ∑ i ∈ s, a i t x) (fun t x => ∑ i ∈ s, ax i t x)
      (fun t x => ∑ i ∈ s, at' i t x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Osc.zero le_rfl
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hN j (Finset.mem_insert_of_mem hj))
      (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact h1.add h2

/-! ### Elementary examples -/

/-- The coordinate `x` has order one. -/
theorem Osc.coord : Osc T 1 1 (fun _ x => x) (fun _ _ => 1) (fun _ _ => 0) where
  bound t ht x hx := by
    rw [zpow_one, one_mul, abs_of_nonneg hx.1]
    unfold vs
    linarith [Real.sqrt_nonneg (-t)]
  dx t _ x _ := (hasDerivAt_id' x).hasDerivWithinAt
  dx_bound t ht x hx := by
    have e : (1 : ℤ) - 1 = 0 := by norm_num
    rw [e, zpow_zero, abs_one, mul_one]
  dt t _ x _ := hasDerivAt_const t x
  dt_bound t ht x hx := by
    rw [abs_zero, one_mul]
    exact zpow_nonneg (vs_pos ht hx).le _

/-- A function of `x` alone with bounded derivative has order zero. -/
theorem Osc.of_x {p p' : ℝ → ℝ} {B S : ℝ} (hB : 0 ≤ B) (hS1 : 1 ≤ S)
    (hS : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, vs t x ≤ S)
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt p (p' x) (Icc 0 1) x)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |p x| ≤ B) (hb' : ∀ x ∈ Icc (0 : ℝ) 1, |p' x| ≤ B) :
    Osc T 0 (B * S) (fun _ => p) (fun _ => p') (fun _ _ => 0) where
  bound t ht x hx := by
    rw [zpow_zero, mul_one]
    exact (hb x hx).trans (le_mul_of_one_le_right hB hS1)
  dx t _ x hx := hp x hx
  dx_bound t ht x hx := by
    have hς := vs_pos ht hx
    have h1 := zpow_le_lower hς (hS t ht x hx) 0 1
    rw [zpow_zero, pow_one] at h1
    have e : (0 : ℤ) - ((1 : ℕ) : ℤ) = 0 - 1 := by norm_num
    rw [e] at h1
    calc |p' x| ≤ B * 1 := by
          rw [mul_one]
          exact hb' x hx
      _ ≤ B * (S * vs t x ^ ((0 : ℤ) - 1)) := mul_le_mul_of_nonneg_left h1 hB
      _ = B * S * vs t x ^ ((0 : ℤ) - 1) := by ring
  dt t _ x _ := hasDerivAt_const t (p x)
  dt_bound t ht x hx := by
    rw [abs_zero]
    exact mul_nonneg (mul_nonneg hB (by linarith)) (zpow_nonneg (vs_pos ht hx).le _)

/-! ### Towers of derivatives -/

/-- `c j`, `j < K`, are the successive `x`-derivatives of `c 0`, of the orders
`n - j`, with the time derivatives `d j`. -/
def Tower (T : ℝ) (n : ℤ) (M : ℝ) (K : ℕ) (c d : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ j : ℕ, j < K → Osc T (n - j) M (c j) (c (j + 1)) (d j)

/-- The Leibniz sum for the `j`-th derivative of a product. -/
noncomputable def tprod (a b : ℕ → ℝ → ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (a i t x * b (j - i) t x)

/-- The time derivative of the Leibniz sum. -/
noncomputable def tprodT (a da b db : ℕ → ℝ → ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ i ∈ range (j + 1),
    (j.choose i : ℝ) * (da i t x * b (j - i) t x + a i t x * db (j - i) t x)

theorem tprod_zero (a b : ℕ → ℝ → ℝ → ℝ) (t x : ℝ) : tprod a b 0 t x = a 0 t x * b 0 t x := by
  simp [tprod]

/-- **The Leibniz rule for towers.** -/
theorem Tower.mul {n' : ℤ} {M' : ℝ} {K : ℕ} {a da b db : ℕ → ℝ → ℝ → ℝ}
    (ha : Tower T n M K a da) (hb : Tower T n' M' K b db) (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    Tower T (n + n') (2 ^ (K + 1) * M * M') K (tprod a b) (tprodT a da b db) := by
  intro j hj
  have hterm : ∀ i ∈ range (j + 1), Osc T (n + n' - j) ((j.choose i : ℝ) * (2 * M * M'))
      (fun t x => (j.choose i : ℝ) * (a i t x * b (j - i) t x))
      (fun t x => (j.choose i : ℝ) * (a (i + 1) t x * b (j - i) t x
        + a i t x * b (j - i + 1) t x))
      (fun t x => (j.choose i : ℝ) * (da i t x * b (j - i) t x + a i t x * db (j - i) t x)) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have h1 := ha i (lt_of_le_of_lt hij hj)
    have h2 := hb (j - i) (lt_of_le_of_lt (Nat.sub_le j i) hj)
    have e : n - (i : ℤ) + (n' - ((j - i : ℕ) : ℤ)) = n + n' - j := by
      rw [Nat.cast_sub hij]
      ring
    have h3 := ((h1.mul h2 hM hM').cast e).const_mul (j.choose i : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg _)] at h3
    exact h3
  have hsum := Osc.sum (range (j + 1))
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hM) hM'))
    hterm
  have hconst : ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (2 * M * M') ≤ 2 ^ (K + 1) * M * M' := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hj.le
    have h3 : 0 ≤ M * M' := mul_nonneg hM hM'
    calc (2 : ℝ) ^ j * (2 * M * M') = 2 ^ j * 2 * (M * M') := by ring
      _ ≤ 2 ^ K * 2 * (M * M') :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by norm_num)) h3
      _ = 2 ^ (K + 1) * M * M' := by
        rw [pow_succ]
        ring
  refine (hsum.mono hconst).congr_deriv (fun t _ x _ => ?_) (fun t _ x _ => rfl)
  -- the `x`-derivative of the Leibniz sum is the next Leibniz sum
  show tprod a b (j + 1) t x = ∑ i ∈ range (j + 1), (j.choose i : ℝ)
    * (a (i + 1) t x * b (j - i) t x + a i t x * b (j - i + 1) t x)
  have hP := Finset.sum_choose_succ_mul (R := ℝ) (fun i k => a i t x * b k t x) j
  have e1 : ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (a i t x * b (j + 1 - i) t x)
      = ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (a i t x * b (j - i + 1) t x) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.succ_sub (Nat.lt_succ_iff.1 (mem_range.1 hi))]
  unfold tprod
  rw [hP, e1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A tower with a different (equal) order. -/
theorem Tower.cast {n' : ℤ} {K : ℕ} {a da : ℕ → ℝ → ℝ → ℝ} (h : Tower T n M K a da)
    (e : n = n') : Tower T n' M K a da := e ▸ h

theorem Tower.mono {M' : ℝ} {K : ℕ} {a da : ℕ → ℝ → ℝ → ℝ} (h : Tower T n M K a da)
    (hM : M ≤ M') : Tower T n M' K a da := fun j hj => (h j hj).mono hM

theorem Tower.of_le {K K' : ℕ} {a da : ℕ → ℝ → ℝ → ℝ} (h : Tower T n M K a da)
    (hK : K' ≤ K) : Tower T n M K' a da := fun j hj => h j (lt_of_lt_of_le hj hK)

/-! ### Scaled bounds without the names of the derivatives -/

/-- `c` has order `n`: scaled bounds for `c` and for some `x`- and
`t`-derivatives of it. -/
def OscE (T : ℝ) (n : ℤ) (M : ℝ) (c : ℝ → ℝ → ℝ) : Prop :=
  ∃ cx ct : ℝ → ℝ → ℝ, Osc T n M c cx ct

theorem Osc.oscE (h : Osc T n M c cx ct) : OscE T n M c := ⟨cx, ct, h⟩

theorem Tower.oscE {K : ℕ} {a da : ℕ → ℝ → ℝ → ℝ} (h : Tower T n M K a da) {j : ℕ}
    (hj : j < K) : OscE T (n - j) M (a j) := (h j hj).oscE

theorem OscE.cast {n' : ℤ} (h : OscE T n M c) (e : n = n') : OscE T n' M c := e ▸ h

theorem OscE.mono {M' : ℝ} (h : OscE T n M c) (hM : M ≤ M') : OscE T n M' c := by
  obtain ⟨cx, ct, h⟩ := h
  exact (h.mono hM).oscE

theorem OscE.congr_fun {c' : ℝ → ℝ → ℝ} (h : OscE T n M c)
    (hc : ∀ t : ℝ, t < 0 → ∀ x ∈ Icc (0 : ℝ) 1, c' t x = c t x) : OscE T n M c' := by
  obtain ⟨cx, ct, h⟩ := h
  exact (h.congr_fun hc).oscE

theorem OscE.add {M' : ℝ} {c' : ℝ → ℝ → ℝ} (h : OscE T n M c) (h' : OscE T n M' c') :
    OscE T n (M + M') (fun t x => c t x + c' t x) := by
  obtain ⟨cx, ct, h⟩ := h
  obtain ⟨cx', ct', h'⟩ := h'
  exact (h.add h').oscE

theorem OscE.sub {M' : ℝ} {c' : ℝ → ℝ → ℝ} (h : OscE T n M c) (h' : OscE T n M' c') :
    OscE T n (M + M') (fun t x => c t x - c' t x) := by
  obtain ⟨cx, ct, h⟩ := h
  obtain ⟨cx', ct', h'⟩ := h'
  exact (h.sub h').oscE

theorem OscE.neg (h : OscE T n M c) : OscE T n M (fun t x => -c t x) := by
  obtain ⟨cx, ct, h⟩ := h
  exact h.neg.oscE

theorem OscE.const_mul (k : ℝ) (h : OscE T n M c) : OscE T n (|k| * M) (fun t x => k * c t x) := by
  obtain ⟨cx, ct, h⟩ := h
  exact (h.const_mul k).oscE

theorem OscE.mul {n' : ℤ} {M' : ℝ} {c' : ℝ → ℝ → ℝ} (h : OscE T n M c) (h' : OscE T n' M' c')
    (hM : 0 ≤ M) (hM' : 0 ≤ M') : OscE T (n + n') (2 * M * M') (fun t x => c t x * c' t x) := by
  obtain ⟨cx, ct, h⟩ := h
  obtain ⟨cx', ct', h'⟩ := h'
  exact (h.mul h' hM hM').oscE

theorem OscE.lower {S : ℝ} (h : OscE T n M c) (hM : 0 ≤ M) (k : ℕ)
    (hS : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, vs t x ≤ S) : OscE T (n - k) (M * S ^ k) c := by
  obtain ⟨cx, ct, h⟩ := h
  exact (h.lower hM k hS).oscE

theorem OscE.coord : OscE T 1 1 (fun _ x => x) := Osc.coord.oscE

theorem OscE.of_x {p p' : ℝ → ℝ} {B S : ℝ} (hB : 0 ≤ B) (hS1 : 1 ≤ S)
    (hS : ∀ t ∈ Ico (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1, vs t x ≤ S)
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt p (p' x) (Icc 0 1) x)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |p x| ≤ B) (hb' : ∀ x ∈ Icc (0 : ℝ) 1, |p' x| ≤ B) :
    OscE T 0 (B * S) (fun _ => p) := (Osc.of_x hB hS1 hS hp hb hb').oscE

end Calabi.Osc
