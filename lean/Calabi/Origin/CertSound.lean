import Calabi.Origin.Cert
import Calabi.Origin.Nonlinear
import Calabi.Shot.StepSound

/-!
# Soundness of the certificate at the origin

If the kernel's `originSummarize` accepts the polynomials, then for every
parameter of the box the polynomial

  `Q(r) = q0(r) / 2^192 + z₁ q1(r) / 2^128 + z₂ q2(r) / 2^128`

has the prescribed first two coefficients `d`, `k`, and it satisfies the
equation of `Calabi.Origin.compare` with the source `polySource` up to a defect
that the summary bounds. Its jet at `r = 1` is read off the summary.
-/

open Set

namespace Calabi.Origin

open Calabi.Shot

theorem scaleO_pos : (0 : ℝ) < (scaleO : ℝ) := by
  unfold scaleO
  positivity

theorem scaleO_eq : (scaleO : ℝ) = 2 ^ 64 * (scaleP : ℝ) := by
  unfold scaleO scaleP
  norm_num

theorem scaleP_eq : (scaleP : ℝ) = 2 ^ 64 * (scaleU : ℝ) := by
  unfold scaleP scaleU
  norm_num

theorem eval_eq_sum (q : Poly) : ∀ (m : ℕ), q.length ≤ m → ∀ x : ℝ,
    Poly.eval q x = ∑ i ∈ Finset.range m, ((q.getD i 0 : Int) : ℝ) * x ^ i := by
  induction q with
  | nil =>
    intro m _ x
    simp [Poly.eval]
  | cons a p ih =>
    intro m hm x
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
      have : 1 ≤ m := (Nat.succ_le_succ (Nat.zero_le _)).trans hm
      omega⟩
    have hm' : p.length ≤ m' := Nat.le_of_succ_le_succ hm
    rw [Poly.eval_cons, ih m' hm' x, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem getD_opLFrom (p : Poly) : ∀ (j i : ℕ), (opLFrom j p).getD i 0 =
    (((j + i + 1) * (j + i + 8) * (j + i + 9) : ℕ) : Int) * p.getD i 0 := by
  induction p with
  | nil =>
    intro j i
    simp [opLFrom]
  | cons a p ih =>
    intro j i
    cases i with
    | zero => simp [opLFrom]
    | succ i =>
      simp only [opLFrom, List.getD_cons_succ]
      rw [ih (j + 1) i]
      have : j + 1 + i = j + (i + 1) := by omega
      rw [this]

theorem length_opLFrom (p : Poly) : ∀ j : ℕ, (opLFrom j p).length = p.length := by
  induction p with
  | nil =>
    intro j
    rfl
  | cons a p ih =>
    intro j
    simp [opLFrom, ih]

theorem getD_drop_two (q : Poly) (i : ℕ) : (q.drop 2).getD i 0 = q.getD (i + 2) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem getD_derivFrom (p : Poly) : ∀ (k i : ℕ),
    (Poly.derivFrom k p).getD i 0 = ((k + i : ℕ) : Int) * p.getD i 0 := by
  induction p with
  | nil =>
    intro k i
    simp [Poly.derivFrom]
  | cons a p ih =>
    intro k i
    cases i with
    | zero => simp [Poly.derivFrom]
    | succ i =>
      simp only [Poly.derivFrom, List.getD_cons_succ]
      rw [ih (k + 1) i]
      have : k + 1 + i = k + (i + 1) := by omega
      rw [this]

theorem length_derivFrom (p : Poly) : ∀ k : ℕ, (Poly.derivFrom k p).length = p.length := by
  induction p with
  | nil =>
    intro k
    rfl
  | cons a p ih =>
    intro k
    simp [Poly.derivFrom, ih]

theorem eval_opL (q : Poly) (n : ℕ) (hn : q.length ≤ n + 2) (x : ℝ) :
    Poly.eval (opL q) x = ∑ j ∈ Finset.range n,
      (((j : ℝ) + 1) * ((j : ℝ) + 8) * ((j : ℝ) + 9)) * ((q.getD (j + 2) 0 : Int) : ℝ) * x ^ j := by
  have hlen : (opL q).length ≤ n := by
    unfold opL
    rw [length_opLFrom, List.length_drop]
    omega
  rw [eval_eq_sum (opL q) n hlen x]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold opL
  rw [getD_opLFrom, getD_drop_two]
  push_cast
  ring

theorem evalInt_one_eq (q : Poly) (m : ℕ) (hm : q.length ≤ m) :
    ((Poly.evalInt 1 q : Int) : ℝ) = ∑ i ∈ Finset.range m, ((q.getD i 0 : Int) : ℝ) := by
  have h := Poly.eval_intCast 1 q
  rw [← h, eval_eq_sum q m hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem jetOne_eq (q : Poly) (m : ℕ) (hm : q.length ≤ m) :
    ((jetOne q).v : ℝ) = ∑ i ∈ Finset.range m, ((q.getD i 0 : Int) : ℝ) ∧
      ((jetOne q).d1 : ℝ) = ∑ i ∈ Finset.range m, (i : ℝ) * ((q.getD i 0 : Int) : ℝ) ∧
      ((jetOne q).d2 : ℝ) = ∑ i ∈ Finset.range m, (i : ℝ) ^ 2 * ((q.getD i 0 : Int) : ℝ) := by
  have h1 : (Poly.derivFrom 0 q).length ≤ m := by rw [length_derivFrom]; exact hm
  have h2 : (Poly.derivFrom 0 (Poly.derivFrom 0 q)).length ≤ m := by
    rw [length_derivFrom]
    exact h1
  refine ⟨evalInt_one_eq q m hm, ?_, ?_⟩
  · show ((Poly.evalInt 1 (Poly.derivFrom 0 q) : Int) : ℝ) = _
    rw [evalInt_one_eq _ m h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [getD_derivFrom]
    push_cast
    ring
  · show ((Poly.evalInt 1 (Poly.derivFrom 0 (Poly.derivFrom 0 q)) : Int) : ℝ) = _
    rw [evalInt_one_eq _ m h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [getD_derivFrom, getD_derivFrom]
    push_cast
    ring

theorem eval_onePlusO (q : Poly) (x : ℝ) :
    Poly.eval (onePlusO q) x = (scaleO : ℝ) + Poly.eval q x := by
  simp only [onePlusO, Poly.eval_add, Poly.eval_cons, Poly.eval_nil]
  push_cast
  ring

theorem eval_res0 (q0 : Poly) (x : ℝ) : Poly.eval (res0 q0) x =
    8 * (scaleO : ℝ) * Poly.eval q0 x
      + 27 * (((scaleO : ℝ) + Poly.eval q0 x) * Poly.eval (opL q0) x) := by
  simp only [res0, Poly.eval_add, Poly.eval_smul, Poly.eval_mul, eval_onePlusO]
  push_cast
  ring

theorem eval_resT (q0 qm : Poly) (x : ℝ) : Poly.eval (resT q0 qm) x =
    8 * (scaleO : ℝ) * Poly.eval qm x
      + 27 * (Poly.eval qm x * Poly.eval (opL q0) x
        + ((scaleO : ℝ) + Poly.eval q0 x) * Poly.eval (opL qm) x) := by
  simp only [resT, Poly.eval_add, Poly.eval_smul, Poly.eval_mul, eval_onePlusO]
  push_cast
  ring

/-- The real coefficients of the approximate solution at `(z₁, z₂)`. -/
noncomputable def coef (q0 q1 q2 : Poly) (z1 z2 : ℝ) (i : ℕ) : ℝ :=
  ((q0.getD i 0 : Int) : ℝ) / (scaleO : ℝ) + z1 * (((q1.getD i 0 : Int) : ℝ) / (scaleP : ℝ))
    + z2 * (((q2.getD i 0 : Int) : ℝ) / (scaleP : ℝ))

/-- A common bound for the lengths. -/
def clen (q0 q1 q2 : Poly) : ℕ := max q0.length (max q1.length q2.length)

theorem clen_ge (q0 q1 q2 : Poly) :
    q0.length ≤ clen q0 q1 q2 ∧ q1.length ≤ clen q0 q1 q2 ∧ q2.length ≤ clen q0 q1 q2 :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem sum_coef (q0 q1 q2 : Poly) (z1 z2 x : ℝ) (m : ℕ) (h0 : q0.length ≤ m)
    (h1 : q1.length ≤ m) (h2 : q2.length ≤ m) :
    ∑ i ∈ Finset.range m, coef q0 q1 q2 z1 z2 i * x ^ i =
      Poly.eval q0 x / (scaleO : ℝ) + z1 * (Poly.eval q1 x / (scaleP : ℝ))
        + z2 * (Poly.eval q2 x / (scaleP : ℝ)) := by
  rw [eval_eq_sum q0 m h0, eval_eq_sum q1 m h1, eval_eq_sum q2 m h2, Finset.sum_div,
    Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold coef
  ring

theorem polySource_coef (q0 q1 q2 : Poly) (z1 z2 x : ℝ) (n : ℕ) (h0 : q0.length ≤ n + 2)
    (h1 : q1.length ≤ n + 2) (h2 : q2.length ≤ n + 2) :
    polySource (coef q0 q1 q2 z1 z2) n x =
      -(27 / 8) * (Poly.eval (opL q0) x / (scaleO : ℝ)
        + z1 * (Poly.eval (opL q1) x / (scaleP : ℝ))
        + z2 * (Poly.eval (opL q2) x / (scaleP : ℝ))) := by
  rw [eval_opL q0 n h0, eval_opL q1 n h1, eval_opL q2 n h2]
  unfold polySource
  rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold coef
  ring

theorem continuous_polySum (a : ℕ → ℝ) (m : ℕ) :
    Continuous fun x : ℝ => ∑ i ∈ Finset.range m, a i * x ^ i :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem continuous_polySource (a : ℕ → ℝ) (n : ℕ) : Continuous (polySource a n) := by
  unfold polySource
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem originSummarize_some {dnum knum dz1 kz1 dz2 kz2 : Int} {q0 q1 q2 : Poly}
    {os : OriginSummary} (h : originSummarize dnum knum dz1 kz1 dz2 kz2 q0 q1 q2 = some os) :
    (q0.getD 0 0 = dnum * 2 ^ 64 ∧ q0.getD 1 0 = knum * 2 ^ 64 ∧
      q1.getD 0 0 = dz1 * 2 ^ 64 ∧ q1.getD 1 0 = kz1 * 2 ^ 64 ∧
      q2.getD 0 0 = dz2 * 2 ^ 64 ∧ q2.getD 1 0 = kz2 * 2 ^ 64) ∧
      os.e0 = Poly.l1 (res0 q0) ∧ os.e1 = Poly.l1 (resT q0 q1) + Poly.l1 (resT q0 q2) ∧
      os.n0 = Poly.l1 q0 ∧ os.nQ = Poly.l1 q1 + Poly.l1 q2 ∧
      os.nL = Poly.l1 (opL q1) + Poly.l1 (opL q2) ∧
      os.j0 = jetOne q0 ∧ os.j1 = jetOne q1 ∧ os.j2 = jetOne q2 := by
  unfold originSummarize at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

theorem abs_mul_le_mul {a z b R : ℝ} (ha : |a| ≤ b) (hz : |z| ≤ R) : |a * z| ≤ b * R := by
  rw [abs_mul]
  exact mul_le_mul ha hz (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem abs_scaled_le {e : ℝ} {n : ℕ} {S : ℝ} (hS : 0 < S) (h : |e| ≤ (n : ℝ)) :
    |e / S| ≤ (n : ℝ) / S := by
  rw [abs_div, abs_of_pos hS]
  exact div_le_div_of_nonneg_right h hS.le

/-- The first two coefficients are the parameters `d` and `k`. -/
theorem coef_zero_one {dnum knum dz1 kz1 dz2 kz2 : Int} {q0 q1 q2 : Poly} {os : OriginSummary}
    (h : originSummarize dnum knum dz1 kz1 dz2 kz2 q0 q1 q2 = some os) (z1 z2 : ℝ) :
    coef q0 q1 q2 z1 z2 0 = param dnum dz1 dz2 z1 z2 ∧
      coef q0 q1 q2 z1 z2 1 = param knum kz1 kz2 z1 z2 := by
  obtain ⟨⟨a0, a1, b0, b1, c0, c1⟩, -⟩ := originSummarize_some h
  have hSP := scaleP_pos.ne'
  have hSU := scaleU_pos.ne'
  refine ⟨?_, ?_⟩
  · unfold coef param
    rw [a0, b0, c0, scaleO_eq, scaleP_eq]
    push_cast
    field_simp
    ring
  · unfold coef param
    rw [a1, b1, c1, scaleO_eq, scaleP_eq]
    push_cast
    field_simp
    ring

/-- The algebra behind the defect: the equation `8 Q + 27 (1 + Q) L = 0`
expanded to first order in the two parameters. -/
theorem defect_identity {SO SP z1 z2 eq0 eq1 eq2 eL0 eL1 eL2 : ℝ} (hSO : SO ≠ 0) (hSP : SP ≠ 0) :
    8 * (eq0 / SO + z1 * (eq1 / SP) + z2 * (eq2 / SP))
        + 27 * ((1 + (eq0 / SO + z1 * (eq1 / SP) + z2 * (eq2 / SP)))
          * (eL0 / SO + z1 * (eL1 / SP) + z2 * (eL2 / SP))) =
      (8 * SO * eq0 + 27 * ((SO + eq0) * eL0)) / (SO * SO)
        + (z1 * ((8 * SO * eq1 + 27 * (eq1 * eL0 + (SO + eq0) * eL1)) / (SO * SP))
          + z2 * ((8 * SO * eq2 + 27 * (eq2 * eL0 + (SO + eq0) * eL2)) / (SO * SP)))
        + 27 * (z1 * (eq1 / SP) + z2 * (eq2 / SP)) * (z1 * (eL1 / SP) + z2 * (eL2 / SP)) := by
  field_simp
  ring

theorem defect_quotient {Q Bs : ℝ} (hQ : 1 + Q ≠ 0) :
    Q / (1 + Q) - -(27 / 8) * Bs = (8 * Q + 27 * ((1 + Q) * Bs)) / (8 * (1 + Q)) := by
  field_simp
  ring

theorem abs_pair_le {z1 z2 u1 u2 R n1 n2 n S : ℝ} (hz1 : |z1| ≤ R) (hz2 : |z2| ≤ R)
    (h1 : |u1| ≤ n1 / S) (h2 : |u2| ≤ n2 / S) (hn : n = n1 + n2) :
    |z1 * u1 + z2 * u2| ≤ R * (n / S) := by
  have t1 := abs_mul_le_mul hz1 h1
  have t2 := abs_mul_le_mul hz2 h2
  have t3 := abs_add_le (z1 * u1) (z2 * u2)
  have e : R * (n / S) = R * (n1 / S) + R * (n2 / S) := by
    rw [hn]
    ring
  rw [e]
  linarith

/-- **The defect of the certificate.** For every parameter of a box of radius
`R` on which `1 + Q ≥ 1/2`, the polynomial satisfies the equation up to the
bound read off the summary. -/
theorem origin_defect {dnum knum dz1 kz1 dz2 kz2 : Int} {q0 q1 q2 : Poly} {os : OriginSummary}
    (h : originSummarize dnum knum dz1 kz1 dz2 kz2 q0 q1 q2 = some os) {R z1 z2 : ℝ}
    (hz1 : |z1| ≤ R) (hz2 : |z2| ≤ R)
    (hpos : (os.n0 : ℝ) / (scaleO : ℝ) + R * ((os.nQ : ℝ) / (scaleP : ℝ)) ≤ 1 / 2) {x : ℝ}
    (hx : |x| ≤ 1) :
    |Nor (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z1 z2 i * x ^ i)
        - polySource (coef q0 q1 q2 z1 z2) (clen q0 q1 q2) x| ≤
      ((os.e0 : ℝ) / ((scaleO : ℝ) * (scaleO : ℝ))
        + R * ((os.e1 : ℝ) / ((scaleO : ℝ) * (scaleP : ℝ)))
        + 27 * (R * ((os.nQ : ℝ) / (scaleP : ℝ))) * (R * ((os.nL : ℝ) / (scaleP : ℝ)))) / 4 := by
  obtain ⟨-, he0, he1, hn0, hnQ, hnL, -, -, -⟩ := originSummarize_some h
  have hSO := scaleO_pos
  have hSP := scaleP_pos
  have hR : 0 ≤ R := (abs_nonneg _).trans hz1
  obtain ⟨l0, l1, l2⟩ := clen_ge q0 q1 q2
  have l0' : q0.length ≤ clen q0 q1 q2 + 2 := l0.trans (Nat.le_add_right _ _)
  have l1' : q1.length ≤ clen q0 q1 q2 + 2 := l1.trans (Nat.le_add_right _ _)
  have l2' : q2.length ≤ clen q0 q1 q2 + 2 := l2.trans (Nat.le_add_right _ _)
  rw [sum_coef q0 q1 q2 z1 z2 x _ l0' l1' l2', polySource_coef q0 q1 q2 z1 z2 x _ l0' l1' l2']
  have hA0 := abs_scaled_le hSO (Poly.abs_eval_le q0 hx)
  have hA1 := abs_scaled_le hSP (Poly.abs_eval_le q1 hx)
  have hA2 := abs_scaled_le hSP (Poly.abs_eval_le q2 hx)
  have hB1 := abs_scaled_le hSP (Poly.abs_eval_le (opL q1) hx)
  have hB2 := abs_scaled_le hSP (Poly.abs_eval_le (opL q2) hx)
  have hR0 := abs_scaled_le (mul_pos hSO hSO) (Poly.abs_eval_le (res0 q0) hx)
  have hR1 := abs_scaled_le (mul_pos hSO hSP) (Poly.abs_eval_le (resT q0 q1) hx)
  have hR2 := abs_scaled_le (mul_pos hSO hSP) (Poly.abs_eval_le (resT q0 q2) hx)
  rw [eval_res0] at hR0
  rw [eval_resT] at hR1 hR2
  rw [← hn0] at hA0
  rw [← he0] at hR0
  have hnQR : (os.nQ : ℝ) = (Poly.l1 q1 : ℝ) + (Poly.l1 q2 : ℝ) := by
    rw [hnQ]
    exact Nat.cast_add _ _
  have hnLR : (os.nL : ℝ) = (Poly.l1 (opL q1) : ℝ) + (Poly.l1 (opL q2) : ℝ) := by
    rw [hnL]
    exact Nat.cast_add _ _
  have he1R : (os.e1 : ℝ) = (Poly.l1 (resT q0 q1) : ℝ) + (Poly.l1 (resT q0 q2) : ℝ) := by
    rw [he1]
    exact Nat.cast_add _ _
  have hzA := abs_pair_le hz1 hz2 hA1 hA2 hnQR
  have hzB := abs_pair_le hz1 hz2 hB1 hB2 hnLR
  have hzR := abs_pair_le hz1 hz2 hR1 hR2 he1R
  generalize Poly.eval q0 x = eq0 at *
  generalize Poly.eval q1 x = eq1 at *
  generalize Poly.eval q2 x = eq2 at *
  generalize Poly.eval (opL q0) x = eL0 at *
  generalize Poly.eval (opL q1) x = eL1 at *
  generalize Poly.eval (opL q2) x = eL2 at *
  have hQlow : -(1 / 2) ≤ eq0 / (scaleO : ℝ) + z1 * (eq1 / (scaleP : ℝ))
      + z2 * (eq2 / (scaleP : ℝ)) := by
    have t1 := (abs_le.1 hA0).1
    have t2 := (abs_le.1 hzA).1
    linarith
  have hQpos : (0 : ℝ) < 1 + (eq0 / (scaleO : ℝ) + z1 * (eq1 / (scaleP : ℝ))
      + z2 * (eq2 / (scaleP : ℝ))) := by linarith
  rw [Nor_of_ge hQlow, defect_quotient hQpos.ne', defect_identity hSO.ne' hSP.ne', abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 8 * (1 + (eq0 / (scaleO : ℝ)
      + z1 * (eq1 / (scaleP : ℝ)) + z2 * (eq2 / (scaleP : ℝ)))))]
  have hprod : |27 * (z1 * (eq1 / (scaleP : ℝ)) + z2 * (eq2 / (scaleP : ℝ)))
      * (z1 * (eL1 / (scaleP : ℝ)) + z2 * (eL2 / (scaleP : ℝ)))| ≤
      27 * (R * ((os.nQ : ℝ) / (scaleP : ℝ))) * (R * ((os.nL : ℝ) / (scaleP : ℝ))) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 27)]
    have := mul_le_mul hzA hzB (abs_nonneg _) ((abs_nonneg _).trans hzA)
    nlinarith
  have htot := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add hR0 hzR)) hprod)
  have hT0 : 0 ≤ (os.e0 : ℝ) / ((scaleO : ℝ) * (scaleO : ℝ))
      + R * ((os.e1 : ℝ) / ((scaleO : ℝ) * (scaleP : ℝ)))
      + 27 * (R * ((os.nQ : ℝ) / (scaleP : ℝ))) * (R * ((os.nL : ℝ) / (scaleP : ℝ))) := by
    positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The size of the certificate polynomial on `|x| ≤ 1`. -/
theorem origin_Q_bound {dnum knum dz1 kz1 dz2 kz2 : Int} {q0 q1 q2 : Poly} {os : OriginSummary}
    (h : originSummarize dnum knum dz1 kz1 dz2 kz2 q0 q1 q2 = some os) {R z1 z2 : ℝ}
    (hz1 : |z1| ≤ R) (hz2 : |z2| ≤ R) {x : ℝ} (hx : |x| ≤ 1) :
    |∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z1 z2 i * x ^ i| ≤
      (os.n0 : ℝ) / (scaleO : ℝ) + R * ((os.nQ : ℝ) / (scaleP : ℝ)) := by
  obtain ⟨-, -, -, hn0, hnQ, -, -, -, -⟩ := originSummarize_some h
  have hSO := scaleO_pos
  have hSP := scaleP_pos
  obtain ⟨l0, l1, l2⟩ := clen_ge q0 q1 q2
  rw [sum_coef q0 q1 q2 z1 z2 x _ (l0.trans (Nat.le_add_right _ 2))
    (l1.trans (Nat.le_add_right _ 2)) (l2.trans (Nat.le_add_right _ 2))]
  have hA0 := abs_scaled_le hSO (Poly.abs_eval_le q0 hx)
  have hA1 := abs_scaled_le hSP (Poly.abs_eval_le q1 hx)
  have hA2 := abs_scaled_le hSP (Poly.abs_eval_le q2 hx)
  rw [← hn0] at hA0
  have hnQR : (os.nQ : ℝ) = (Poly.l1 q1 : ℝ) + (Poly.l1 q2 : ℝ) := by
    rw [hnQ]
    exact Nat.cast_add _ _
  have hzA := abs_pair_le hz1 hz2 hA1 hA2 hnQR
  have t := abs_add_le (Poly.eval q0 x / (scaleO : ℝ))
    (z1 * (Poly.eval q1 x / (scaleP : ℝ)) + z2 * (Poly.eval q2 x / (scaleP : ℝ)))
  rw [← add_assoc] at t
  linarith

theorem sum_weighted (q0 q1 q2 : Poly) (z1 z2 : ℝ) (m : ℕ) (w : ℕ → ℝ) {s0 s1 s2 : ℝ}
    (h0 : s0 = ∑ i ∈ Finset.range m, w i * ((q0.getD i 0 : Int) : ℝ))
    (h1 : s1 = ∑ i ∈ Finset.range m, w i * ((q1.getD i 0 : Int) : ℝ))
    (h2 : s2 = ∑ i ∈ Finset.range m, w i * ((q2.getD i 0 : Int) : ℝ)) :
    ∑ i ∈ Finset.range m, w i * coef q0 q1 q2 z1 z2 i =
      s0 / (scaleO : ℝ) + z1 * (s1 / (scaleP : ℝ)) + z2 * (s2 / (scaleP : ℝ)) := by
  rw [h0, h1, h2, Finset.sum_div, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold coef
  ring

/-- **The jet of the certificate at `r = 1`.** -/
theorem origin_jets {dnum knum dz1 kz1 dz2 kz2 : Int} {q0 q1 q2 : Poly} {os : OriginSummary}
    (h : originSummarize dnum knum dz1 kz1 dz2 kz2 q0 q1 q2 = some os) (z1 z2 : ℝ) :
    (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), coef q0 q1 q2 z1 z2 i * (1 : ℝ) ^ i =
        (os.j0.v : ℝ) / (scaleO : ℝ) + z1 * ((os.j1.v : ℝ) / (scaleP : ℝ))
          + z2 * ((os.j2.v : ℝ) / (scaleP : ℝ))) ∧
      (∑ i ∈ Finset.range (clen q0 q1 q2 + 2), (i : ℝ) * coef q0 q1 q2 z1 z2 i * (1 : ℝ) ^ i =
        (os.j0.d1 : ℝ) / (scaleO : ℝ) + z1 * ((os.j1.d1 : ℝ) / (scaleP : ℝ))
          + z2 * ((os.j2.d1 : ℝ) / (scaleP : ℝ))) ∧
      ∑ i ∈ Finset.range (clen q0 q1 q2 + 2), (i : ℝ) ^ 2 * coef q0 q1 q2 z1 z2 i * (1 : ℝ) ^ i =
        (os.j0.d2 : ℝ) / (scaleO : ℝ) + z1 * ((os.j1.d2 : ℝ) / (scaleP : ℝ))
          + z2 * ((os.j2.d2 : ℝ) / (scaleP : ℝ)) := by
  obtain ⟨-, -, -, -, -, -, hj0, hj1, hj2⟩ := originSummarize_some h
  obtain ⟨l0, l1, l2⟩ := clen_ge q0 q1 q2
  obtain ⟨u0, v0, w0⟩ := jetOne_eq q0 _ (l0.trans (Nat.le_add_right _ 2))
  obtain ⟨u1, v1, w1⟩ := jetOne_eq q1 _ (l1.trans (Nat.le_add_right _ 2))
  obtain ⟨u2, v2, w2⟩ := jetOne_eq q2 _ (l2.trans (Nat.le_add_right _ 2))
  rw [hj0, hj1, hj2]
  refine ⟨?_, ?_, ?_⟩
  · have e := sum_weighted q0 q1 q2 z1 z2 (clen q0 q1 q2 + 2) (fun _ => 1)
      (s0 := ((jetOne q0).v : ℝ)) (s1 := ((jetOne q1).v : ℝ)) (s2 := ((jetOne q2).v : ℝ))
      (by rw [u0]; simp) (by rw [u1]; simp) (by rw [u2]; simp)
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one, one_mul]
  · have e := sum_weighted q0 q1 q2 z1 z2 (clen q0 q1 q2 + 2) (fun i => (i : ℝ))
      (s0 := ((jetOne q0).d1 : ℝ)) (s1 := ((jetOne q1).d1 : ℝ)) (s2 := ((jetOne q2).d1 : ℝ))
      v0 v1 v2
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
  · have e := sum_weighted q0 q1 q2 z1 z2 (clen q0 q1 q2 + 2) (fun i => (i : ℝ) ^ 2)
      (s0 := ((jetOne q0).d2 : ℝ)) (s1 := ((jetOne q1).d2 : ℝ)) (s2 := ((jetOne q2).d2 : ℝ))
      w0 w1 w2
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]

end Calabi.Origin
