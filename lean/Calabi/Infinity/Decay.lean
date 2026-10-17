import Calabi.Infinity.Formal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Decay of the remainders of the expansion at infinity

Let `Z = (p, p′, p″)` be a trajectory of the profile system that is bounded on
`[56, ∞)` and satisfies `|p| ≤ 1/100` there. For the truncation `P_J` of the
formal solution, the remainder jet `W = Z - (q, q′, q″)`, `q = P_J(s⁻³)`,
solves

  `W‴ + W = -(21/s) W″ - (B/s²) W′ - (C/s³) W + ψ W - res_J`,

where `ψ = 1 - 1/((1+p)(1+q))` and `res_J = O(s^{-3(J+1)})`. The a priori bound
`Calabi.Tail.jet_bound` on `[S, ∞)` and on `[2S, ∞)` gives

  `sup_{[2S, ∞)} ‖W‖ ≤ θ sup_{[S, ∞)} ‖W‖ + E / S^N`

with `θ` as small as we like for large `S`, hence `‖W‖ = O(s^{-N})`
(`dyadic_decay`). All derivatives of `W` then have the same decay by induction
on the order, the equation being linear in `W` with coefficients of the class
`Bd` (`wjet_bd`).
-/

open Polynomial Set Filter
open scoped Topology

namespace Calabi.Infinity

open Calabi.Shot (State pfield Ntr Ntr_of_ge)
open Calabi.Tail (Solves stab energy jet_bound energy_le_of_abs_le resid)

/-! ### A dyadic bootstrap -/

/-- If every bound `B` of `f` on `[S, ∞)` improves to `θ B + E / S^N` on
`[2S, ∞)` and `θ 2^N ≤ 1/2`, then `f = O(s^{-N})`. -/
theorem dyadic_decay {f : ℝ → ℝ} {S₀ B₀ θ E : ℝ} {N : ℕ} (hS : 0 < S₀) (hB0 : 0 ≤ B₀)
    (hB : ∀ u, S₀ ≤ u → f u ≤ B₀) (hθ : θ * 2 ^ N ≤ 1 / 2)
    (hstep : ∀ S B, S₀ ≤ S → 0 ≤ B → (∀ u, S ≤ u → f u ≤ B) →
      ∀ u, 2 * S ≤ u → f u ≤ θ * B + E / S ^ N) :
    ∃ C, 0 ≤ C ∧ ∀ s, S₀ ≤ s → f s ≤ C / s ^ N := by
  set C₁ := max (B₀ * S₀ ^ N) (2 ^ (N + 1) * E) with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_of_le_left (mul_nonneg hB0 (pow_pos hS N).le)
  have h2E : 2 ^ (N + 1) * E ≤ C₁ := le_max_right _ _
  have key : ∀ n : ℕ, ∀ u, 2 ^ n * S₀ ≤ u → f u ≤ C₁ / (2 ^ n * S₀) ^ N := by
    intro n
    induction n with
    | zero =>
      intro u hu
      rw [pow_zero, one_mul] at hu ⊢
      refine (hB u hu).trans ?_
      rw [le_div_iff₀ (pow_pos hS N)]
      exact le_max_left _ _
    | succ n ih =>
      intro u hu
      have hSn : 0 < 2 ^ n * S₀ := by positivity
      have hS0n : S₀ ≤ 2 ^ n * S₀ := le_mul_of_one_le_left hS.le (one_le_pow₀ (by norm_num))
      have hX : 0 < (2 ^ n * S₀) ^ N := pow_pos hSn N
      have hu' : 2 * (2 ^ n * S₀) ≤ u := by
        rw [pow_succ] at hu
        linarith
      have h := hstep (2 ^ n * S₀) (C₁ / (2 ^ n * S₀) ^ N) hS0n (div_nonneg hC₁0 hX.le) ih u hu'
      refine h.trans ?_
      have h3 : θ * C₁ * 2 ^ N + E * 2 ^ N ≤ C₁ := by
        have h4 : θ * 2 ^ N * C₁ ≤ 1 / 2 * C₁ := mul_le_mul_of_nonneg_right hθ hC₁0
        have h5 : (2 : ℝ) ^ (N + 1) * E = 2 * (E * 2 ^ N) := by ring
        nlinarith
      have h6 : (2 ^ (n + 1) * S₀) ^ N = (2 ^ n * S₀) ^ N * 2 ^ N := by ring
      rw [h6]
      calc θ * (C₁ / (2 ^ n * S₀) ^ N) + E / (2 ^ n * S₀) ^ N
          = (θ * C₁ * 2 ^ N + E * 2 ^ N) / ((2 ^ n * S₀) ^ N * 2 ^ N) := by
            rw [← add_mul, mul_div_mul_right _ _ (pow_pos two_pos N).ne']
            ring
        _ ≤ C₁ / ((2 ^ n * S₀) ^ N * 2 ^ N) :=
            div_le_div_of_nonneg_right h3 (by positivity)
  refine ⟨2 ^ N * C₁, by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := hS.trans_le hs
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := s / S₀) (y := 2) ((one_le_div hS).2 hs)
    (by norm_num)
  rw [le_div_iff₀ hS] at hn1
  rw [div_lt_iff₀ hS] at hn2
  refine (key n s hn1).trans ?_
  have hSn : 0 < 2 ^ n * S₀ := by positivity
  rw [div_le_div_iff₀ (pow_pos hSn N) (pow_pos hs0 N)]
  have h7 : s ^ N ≤ (2 * (2 ^ n * S₀)) ^ N :=
    pow_le_pow_left₀ hs0.le (by rw [pow_succ] at hn2; linarith) N
  rw [mul_pow] at h7
  calc C₁ * s ^ N ≤ C₁ * (2 ^ N * (2 ^ n * S₀) ^ N) := mul_le_mul_of_nonneg_left h7 hC₁0
    _ = 2 ^ N * C₁ * (2 ^ n * S₀) ^ N := by ring

/-! ### Decay for the reference operator -/

theorem norm_le_iff {X : State} {r : ℝ} :
    ‖X‖ ≤ r ↔ |X.1| ≤ r ∧ |X.2.1| ≤ r ∧ |X.2.2| ≤ r := by
  simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff]

/-- A bounded solution of `W‴ + W = j` whose right-hand side is a small
multiple of the jet plus `O(s^{-N})` is `O(s^{-N})`. -/
theorem solves_decay {W : ℝ → State} {j : ℝ → ℝ} {S₀ ε R : ℝ} {N : ℕ} (hS : 0 < S₀)
    (hW : Solves S₀ W j) (hbdd : ∃ B, ∀ s, S₀ ≤ s → ‖W s‖ ≤ B) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hj : ∀ s, S₀ ≤ s → |j s| ≤ ε * ‖W s‖ + R / s ^ N)
    (hθ : (Real.exp (-S₀) + 5 / 3 * ε) * 2 ^ N ≤ 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ s, S₀ ≤ s → ‖W s‖ ≤ C / s ^ N := by
  obtain ⟨B₀, hB₀⟩ := hbdd
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ S₀ le_rfl)
  refine dyadic_decay (θ := Real.exp (-S₀) + 5 / 3 * ε) (E := 5 / 3 * R) hS hB₀0 hB₀ hθ ?_
  intro S B hS' _ hWB u hu
  have hS0 : 0 < S := hS.trans_le hS'
  have hSu : S ≤ u := by linarith
  have hM : ∀ t, S ≤ t → |j t| ≤ ε * B + R / S ^ N := by
    intro t ht
    have h1 := hj t (hS'.trans ht)
    have h2 : ε * ‖W t‖ ≤ ε * B := mul_le_mul_of_nonneg_left (hWB t ht) hε
    have h3 : R / t ^ N ≤ R / S ^ N :=
      div_le_div_of_nonneg_left hR (pow_pos hS0 N) (pow_le_pow_left₀ hS0.le ht N)
    linarith
  have hen : ∃ B', ∀ t, S ≤ t → energy (W t) ≤ B' := by
    refine ⟨7 * B ^ 2, fun t ht => ?_⟩
    obtain ⟨h1, h2, h3⟩ := norm_le_iff.1 (hWB t ht)
    exact energy_le_of_abs_le h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := jet_bound (hW.mono hS') hM hen hSu
  have hstab : |stab (W S)| ≤ B := by
    obtain ⟨h1, h2, h3⟩ := norm_le_iff.1 (hWB S le_rfl)
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨c1, c2⟩ := abs_le.1 h2
    obtain ⟨e1, e2⟩ := abs_le.1 h3
    rw [abs_le]
    unfold stab
    constructor <;> linarith
  have hexp : Real.exp (-(u - S)) ≤ Real.exp (-S₀) := Real.exp_le_exp.2 (by linarith)
  have hmul : Real.exp (-(u - S)) * |stab (W S)| ≤ Real.exp (-S₀) * B :=
    mul_le_mul hexp hstab (abs_nonneg _) (Real.exp_pos _).le
  have hfin : Real.exp (-(u - S)) * |stab (W S)| + 5 / 3 * (ε * B + R / S ^ N) ≤
      (Real.exp (-S₀) + 5 / 3 * ε) * B + 5 / 3 * R / S ^ N := by
    have e : 5 / 3 * (ε * B + R / S ^ N) = 5 / 3 * ε * B + 5 / 3 * R / S ^ N := by ring
    rw [e, add_mul]
    linarith
  exact norm_le_iff.2 ⟨b1.trans hfin, b2.trans hfin, b3.trans hfin⟩

/-! ### The remainder of a trajectory -/

/-- The remainder jet of a trajectory against the polynomial `P` in `σ = s⁻³`. -/
noncomputable def Wjet (P : ℝ[X]) (Z : ℝ → State) (s : ℝ) : State :=
  Z s - (q0 P s, q1 P s, q2 P s)

/-- The coefficient of the nonlinearity in the equation of the remainder. -/
noncomputable def psi (P : ℝ[X]) (Z : ℝ → State) (s : ℝ) : ℝ :=
  1 - ((1 + (Z s).1) * (1 + q0 P s))⁻¹

/-- The right-hand side of the equation of the remainder. -/
noncomputable def jrem (d : ℝ) (P : ℝ[X]) (Z : ℝ → State) (s : ℝ) : ℝ :=
  -(21 / s) * (Wjet P Z s).2.2 - 337 / (4 * s ^ 2) * (Wjet P Z s).2.1
    + 567 / (4 * s ^ 3) * (Wjet P Z s).1 + psi P Z s * (Wjet P Z s).1
    - resid d (q0 P) (q1 P) (q2 P) (q3 P) s

theorem hasDerivAt_qjet (P : ℝ[X]) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => ((q0 P s, q1 P s, q2 P s) : State)) (q1 P s, q2 P s, q3 P s) s :=
  (hasDerivAt_q0 P hs).prodMk ((hasDerivAt_q1 P hs).prodMk (hasDerivAt_q2 P hs))

variable {d : ℝ} {Z : ℝ → State}

theorem wjet_solves (P : ℝ[X]) (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1) {S : ℝ} (hS : 0 < S)
    (hq : ∀ s, S ≤ s → 0 < 1 + q0 P s) : Solves S (Wjet P Z) (jrem d P Z) := by
  intro s hs
  have hs0 : 0 < s := hS.trans_le hs
  have hsne : s ≠ 0 := hs0.ne'
  have hp : (1 : ℝ) + (Z s).1 ≠ 0 := by
    have := hlow s hs0
    intro h
    linarith
  have hq' : (1 : ℝ) + q0 P s ≠ 0 := (hq s hs).ne'
  refine ((hZ s hs0).sub (hasDerivAt_qjet P hs0)).congr_deriv ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [pfield, Wjet, Prod.fst_sub, Prod.snd_sub]
  · simp only [pfield, Wjet, Prod.fst_sub, Prod.snd_sub]
  · simp only [pfield, Wjet, jrem, psi, resid, Prod.fst_sub, Prod.snd_sub,
      Ntr_of_ge (hlow s hs0)]
    field_simp
    ring

theorem abs_jrem_le (d : ℝ) (P : ℝ[X]) (Z : ℝ → State) {s : ℝ} (hs : 0 < s) :
    |jrem d P Z s| ≤
      (21 / s + 337 / (4 * s ^ 2) + 567 / (4 * s ^ 3) + |psi P Z s|) * ‖Wjet P Z s‖
        + |resid d (q0 P) (q1 P) (q2 P) (q3 P) s| := by
  obtain ⟨h1, h2, h3⟩ := norm_le_iff.1 (le_refl ‖Wjet P Z s‖)
  have e1 : |(-(21 / s)) * (Wjet P Z s).2.2| ≤ 21 / s * ‖Wjet P Z s‖ := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have e2 : |337 / (4 * s ^ 2) * (Wjet P Z s).2.1| ≤ 337 / (4 * s ^ 2) * ‖Wjet P Z s‖ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : |567 / (4 * s ^ 3) * (Wjet P Z s).1| ≤ 567 / (4 * s ^ 3) * ‖Wjet P Z s‖ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have e4 : |psi P Z s * (Wjet P Z s).1| ≤ |psi P Z s| * ‖Wjet P Z s‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  obtain ⟨a1, a2⟩ := abs_le.1 e1
  obtain ⟨b1, b2⟩ := abs_le.1 e2
  obtain ⟨c1, c2⟩ := abs_le.1 e3
  obtain ⟨f1, f2⟩ := abs_le.1 e4
  have r1 := neg_abs_le (resid d (q0 P) (q1 P) (q2 P) (q3 P) s)
  have r2 := le_abs_self (resid d (q0 P) (q1 P) (q2 P) (q3 P) s)
  unfold jrem
  rw [abs_le, add_mul, add_mul, add_mul]
  constructor <;> linarith

theorem zpow_neg_three_mul (s : ℝ) (n : ℕ) : s ^ (-(3 * (n : ℤ))) = (s ^ (3 * n))⁻¹ := by
  have e : (3 * (n : ℤ)) = ((3 * n : ℕ) : ℤ) := by push_cast; ring
  rw [zpow_neg, e, zpow_natCast]

/-- **Decay of the remainder**, given that the coefficients of the equation are
small beyond `S₀`. -/
theorem wjet_decay (J : ℕ) (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hbdd : ∃ B, ∀ s, (56 : ℝ) ≤ s → ‖Z s‖ ≤ B) {S₀ ε : ℝ} (hS : 56 ≤ S₀) (hε : 0 ≤ ε)
    (hq : ∀ s, S₀ ≤ s → 1 / 2 ≤ 1 + q0 (tailPoly d J) s)
    (hκ : ∀ s, S₀ ≤ s → 21 / s + 337 / (4 * s ^ 2) + 567 / (4 * s ^ 3)
      + |psi (tailPoly d J) Z s| ≤ ε)
    (hθ : (Real.exp (-S₀) + 5 / 3 * ε) * 2 ^ (3 * (J + 1)) ≤ 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ s, S₀ ≤ s → ‖Wjet (tailPoly d J) Z s‖ ≤ C / s ^ (3 * (J + 1)) := by
  have hS0 : 0 < S₀ := by linarith
  have hsol : Solves S₀ (Wjet (tailPoly d J) Z) (jrem d (tailPoly d J) Z) :=
    wjet_solves (tailPoly d J) hZ hlow hS0 fun s hs => by linarith [hq s hs]
  -- the residual
  obtain ⟨CE, hCE, hE⟩ := (bd_E_tailPoly (S := 1) one_pos d J 0).bd0
  have hres : ∀ s, S₀ ≤ s →
      |resid d (q0 (tailPoly d J)) (q1 (tailPoly d J)) (q2 (tailPoly d J))
        (q3 (tailPoly d J)) s| ≤ 2 * CE / s ^ (3 * (J + 1)) := by
    intro s hs
    have hs0 : 0 < s := hS0.trans_le hs
    have hq1 := hq s hs
    have hpos : (0 : ℝ) < 1 + q0 (tailPoly d J) s := by linarith
    rw [resid_eq d (tailPoly d J) hs0 hpos.ne', abs_div, abs_of_pos hpos]
    have h1 := hE s (by linarith)
    rw [zpow_neg_three_mul] at h1
    calc |(E d (tailPoly d J)).eval (s ^ (-3 : ℤ))| / (1 + q0 (tailPoly d J) s)
        ≤ (CE * (s ^ (3 * (J + 1)))⁻¹) / (1 / 2) :=
          div_le_div₀ (by positivity) h1 (by norm_num) hq1
      _ = 2 * CE / s ^ (3 * (J + 1)) := by ring
  -- boundedness
  obtain ⟨BZ, hBZ⟩ := hbdd
  obtain ⟨C0, hC0, h0⟩ := (bd_q (S := 1) one_pos (tailPoly d J) 0).1.bd0
  obtain ⟨C1, hC1, h1⟩ := (bd_q (S := 1) one_pos (tailPoly d J) 0).2.1.bd0
  obtain ⟨C2, hC2, h2⟩ := (bd_q (S := 1) one_pos (tailPoly d J) 0).2.2.1.bd0
  have hWb : ∃ B, ∀ s, S₀ ≤ s → ‖Wjet (tailPoly d J) Z s‖ ≤ B := by
    refine ⟨BZ + (C0 + C1 + C2), fun s hs => ?_⟩
    have hz := hBZ s (hS.trans hs)
    have hs1 : (1 : ℝ) < s := by linarith
    have hqn : ‖((q0 (tailPoly d J) s, q1 (tailPoly d J) s, q2 (tailPoly d J) s) : State)‖ ≤
        C0 + C1 + C2 := by
      rw [norm_le_iff]
      have a0 := h0 s hs1
      have a1 := h1 s hs1
      have a2 := h2 s hs1
      rw [zpow_zero, mul_one] at a0 a1 a2
      exact ⟨by linarith, by linarith, by linarith⟩
    calc ‖Wjet (tailPoly d J) Z s‖
        ≤ ‖Z s‖ + ‖((q0 (tailPoly d J) s, q1 (tailPoly d J) s, q2 (tailPoly d J) s) : State)‖ :=
          norm_sub_le _ _
      _ ≤ BZ + (C0 + C1 + C2) := add_le_add hz hqn
  refine solves_decay (ε := ε) (R := 2 * CE) hS0 hsol hWb hε (by positivity) ?_ hθ
  intro s hs
  have hs0 : 0 < s := hS0.trans_le hs
  have h1 := abs_jrem_le d (tailPoly d J) Z hs0
  have h2 := hκ s hs
  have h3 := hres s hs
  have h4 : (21 / s + 337 / (4 * s ^ 2) + 567 / (4 * s ^ 3) + |psi (tailPoly d J) Z s|)
      * ‖Wjet (tailPoly d J) Z s‖ ≤ ε * ‖Wjet (tailPoly d J) Z s‖ :=
    mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  linarith

/-! ### The first step: `p = O(s⁻³)` -/

theorem exp_neg_le_inv {S : ℝ} (hS : 0 < S) : Real.exp (-S) ≤ 1 / S := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hS (by linarith [Real.add_one_le_exp S])

theorem decay_zero (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hbdd : ∃ B, ∀ s, (56 : ℝ) ≤ s → ‖Z s‖ ≤ B)
    (hsmall : ∀ s, (56 : ℝ) ≤ s → |(Z s).1| ≤ 1 / 100) :
    ∃ C, 0 ≤ C ∧ ∀ s, (1024 : ℝ) ≤ s → ‖Z s‖ ≤ C / s ^ 3 := by
  have hq0 : ∀ s, q0 (tailPoly d 0) s = 0 := fun s => by simp [q0, tailPoly]
  have hq1 : ∀ s, q1 (tailPoly d 0) s = 0 := fun s => by simp [q1, P1, Θ, tailPoly]
  have hq2 : ∀ s, q2 (tailPoly d 0) s = 0 := fun s => by simp [q2, P2, P1, Θ, tailPoly]
  have hW : ∀ s, Wjet (tailPoly d 0) Z s = Z s := fun s => by
    simp only [Wjet, hq0, hq1, hq2]
    exact sub_zero (Z s)
  have hκ : ∀ s, (1024 : ℝ) ≤ s → 21 / s + 337 / (4 * s ^ 2) + 567 / (4 * s ^ 3)
      + |psi (tailPoly d 0) Z s| ≤
        21 / 1024 + 337 / (4 * 1024 ^ 2) + 567 / (4 * 1024 ^ 3) + 1 / 99 := by
    intro s hs
    have p2 : (1024 : ℝ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
    have p3 : (1024 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
    have h1 : 21 / s ≤ 21 / 1024 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have h2 : 337 / (4 * s ^ 2) ≤ 337 / (4 * 1024 ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h3 : 567 / (4 * s ^ 3) ≤ 567 / (4 * 1024 ^ 3) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h4 : |psi (tailPoly d 0) Z s| ≤ 1 / 99 := by
      have hp := abs_le.1 (hsmall s (by linarith))
      have hpos : (0 : ℝ) < 1 + (Z s).1 := by linarith [hp.1]
      have e : psi (tailPoly d 0) Z s = (Z s).1 / (1 + (Z s).1) := by
        unfold psi
        rw [hq0, add_zero, mul_one, eq_div_iff hpos.ne', sub_mul, inv_mul_cancel₀ hpos.ne']
        ring
      rw [e, abs_le]
      constructor
      · rw [le_div_iff₀ hpos]
        linarith [hp.1]
      · rw [div_le_iff₀ hpos]
        linarith [hp.2]
    linarith
  have hθ : (Real.exp (-1024) + 5 / 3 * (21 / 1024 + 337 / (4 * 1024 ^ 2)
      + 567 / (4 * 1024 ^ 3) + 1 / 99)) * 2 ^ (3 * (0 + 1)) ≤ 1 / 2 := by
    have he : Real.exp (-1024) ≤ 1 / 1024 := exp_neg_le_inv (by norm_num)
    have h8 : (2 : ℝ) ^ (3 * (0 + 1)) = 8 := by norm_num
    have hc : (5 : ℝ) / 3 * (21 / 1024 + 337 / (4 * 1024 ^ 2) + 567 / (4 * 1024 ^ 3) + 1 / 99)
        ≤ 52 / 1000 := by norm_num
    rw [h8]
    linarith
  obtain ⟨C, hC, h⟩ := wjet_decay (d := d) (Z := Z) 0 hZ hlow hbdd (S₀ := 1024) (by norm_num)
    (by norm_num) (fun s _ => by rw [hq0]; norm_num) hκ hθ
  refine ⟨C, hC, fun s hs => ?_⟩
  have := h s hs
  rw [hW] at this
  simpa using this

/-! ### Limits at infinity -/

theorem Bd0.tendsto_zero {S : ℝ} {a : ℤ} {f : ℝ → ℝ} (ha : a < 0) (h : Bd0 S a f) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := h
  refine squeeze_zero_norm' (a := fun s : ℝ => C * s ^ a) ?_ ?_
  · filter_upwards [eventually_gt_atTop S] with s hs
    rw [Real.norm_eq_abs]
    exact hb s hs
  · have h := (tendsto_zpow_atTop_zero (𝕜 := ℝ) ha).const_mul C
    rwa [mul_zero] at h

theorem tendsto_fst_zero {C : ℝ} (h : ∀ s, (1024 : ℝ) ≤ s → ‖Z s‖ ≤ C / s ^ 3) :
    Tendsto (fun s => (Z s).1) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun s : ℝ => C / s ^ 3) ?_
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num)))
  filter_upwards [eventually_ge_atTop (1024 : ℝ)] with s hs
  rw [Real.norm_eq_abs]
  exact (norm_le_iff.1 (h s hs)).1

/-- **Decay of every remainder.** Beyond some `S₀` the remainder of order `J`
is `O(s^{-3(J+1)})`. -/
theorem exists_decay (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1)
    (hbdd : ∃ B, ∀ s, (56 : ℝ) ≤ s → ‖Z s‖ ≤ B)
    (hsmall : ∀ s, (56 : ℝ) ≤ s → |(Z s).1| ≤ 1 / 100) (J : ℕ) :
    ∃ S₀ C, 56 ≤ S₀ ∧ 0 ≤ C ∧ (∀ s, S₀ ≤ s → 1 / 2 ≤ 1 + q0 (tailPoly d J) s) ∧
      ∀ s, S₀ ≤ s → ‖Wjet (tailPoly d J) Z s‖ ≤ C / s ^ (3 * (J + 1)) := by
  obtain ⟨C₀, -, h₀⟩ := decay_zero hZ hlow hbdd hsmall
  have hp : Tendsto (fun s => (Z s).1) atTop (𝓝 0) := tendsto_fst_zero h₀
  have hq : Tendsto (q0 (tailPoly d J)) atTop (𝓝 0) :=
    Bd0.tendsto_zero (by norm_num)
      (bd_q0_decay (S := 1) one_pos (tailPoly_coeff_zero d J) 0).bd0
  have hψ : Tendsto (psi (tailPoly d J) Z) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hp).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add hq)
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub (h.inv₀ (by norm_num))
    have e : (1 : ℝ) - ((1 + 0) * (1 + 0))⁻¹ = 0 := by norm_num
    rw [e] at h'
    exact h'
  have hκ : Tendsto (fun s : ℝ => 21 / s + 337 / (4 * s ^ 2) + 567 / (4 * s ^ 3)
      + |psi (tailPoly d J) Z s|) atTop (𝓝 0) := by
    have t1 : Tendsto (fun s : ℝ => (21 : ℝ) / s) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have t2 : Tendsto (fun s : ℝ => (337 : ℝ) / (4 * s ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by norm_num)).const_mul_atTop (by norm_num))
    have t3 : Tendsto (fun s : ℝ => (567 : ℝ) / (4 * s ^ 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by norm_num)).const_mul_atTop (by norm_num))
    have h := ((t1.add t2).add t3).add hψ.abs
    have e : (0 : ℝ) + 0 + 0 + |0| = 0 := by simp
    rw [e] at h
    exact h
  have hT : (0 : ℝ) < 2 ^ (3 * (J + 1)) := by positivity
  have hη0 : (0 : ℝ) < 1 / (8 * 2 ^ (3 * (J + 1))) := by positivity
  have hηT : 1 / (8 * (2 : ℝ) ^ (3 * (J + 1))) * 2 ^ (3 * (J + 1)) = 1 / 8 := by
    rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hT.ne', mul_one, one_div]
  obtain ⟨a1, ha1⟩ := eventually_atTop.1 (hκ.eventually_le_const hη0)
  obtain ⟨a2, ha2⟩ := eventually_atTop.1
    (hq.eventually_const_le (show (-(1 / 2) : ℝ) < 0 by norm_num))
  obtain ⟨a3, ha3⟩ := eventually_atTop.1
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually_le_const hη0)
  have h56 : (56 : ℝ) ≤ max 56 (max a1 (max a2 a3)) := le_max_left _ _
  have h1 : a1 ≤ max 56 (max a1 (max a2 a3)) := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : a2 ≤ max 56 (max a1 (max a2 a3)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h3 : a3 ≤ max 56 (max a1 (max a2 a3)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hq' : ∀ s, max 56 (max a1 (max a2 a3)) ≤ s → 1 / 2 ≤ 1 + q0 (tailPoly d J) s := by
    intro s hs
    have := ha2 s (h2.trans hs)
    linarith
  have hθ : (Real.exp (-(max 56 (max a1 (max a2 a3)))) + 5 / 3 * (1 / (8 * 2 ^ (3 * (J + 1)))))
      * 2 ^ (3 * (J + 1)) ≤ 1 / 2 := by
    have he := ha3 _ h3
    have hm := mul_le_mul_of_nonneg_right he hT.le
    rw [add_mul, mul_assoc, hηT]
    linarith
  obtain ⟨C, hC, hdec⟩ := wjet_decay J hZ hlow hbdd h56 hη0.le hq'
    (fun s hs => ha1 s (h1.trans hs)) hθ
  exact ⟨_, C, h56, hC, hq', hdec⟩

/-! ### Derivatives of all orders -/

section Derivs

variable {S : ℝ} {a : ℤ} {l : ℕ} {f g : ℝ → ℝ}

theorem Bd.mul_left0 (hS : 0 < S) (hf : Bd S 0 l f) (hg : Bd S a l g) :
    Bd S a l (fun s => f s * g s) := by
  have h := Bd.mul hS hf hg
  rwa [zero_add] at h

theorem bd_const_div (hS : 0 < S) (c : ℝ) (k l : ℕ) : Bd S 0 l (fun s : ℝ => c / s ^ k) :=
  Bd.congr (fun s _ => by rw [eval_C]) (bd_eval_div hS (C c) k l)

end Derivs

/-- **The remainder of order `J` and all its derivatives are `O(s^{-3(J+1)})`.** -/
theorem wjet_bd (hZ : ∀ s, 0 < s → HasDerivAt Z (pfield d s (Z s)) s)
    (hlow : ∀ s, 0 < s → -19 / 20 ≤ (Z s).1) {J : ℕ} {S₀ C : ℝ} (hS : 56 ≤ S₀) (hC : 0 ≤ C)
    (hq : ∀ s, S₀ ≤ s → 1 / 2 ≤ 1 + q0 (tailPoly d J) s)
    (hdec : ∀ s, S₀ ≤ s → ‖Wjet (tailPoly d J) Z s‖ ≤ C / s ^ (3 * (J + 1))) (l : ℕ) :
    Bd S₀ (-(3 * (J + 1 : ℕ) : ℤ)) l (fun s => (Wjet (tailPoly d J) Z s).1) ∧
      Bd S₀ (-(3 * (J + 1 : ℕ) : ℤ)) l (fun s => (Wjet (tailPoly d J) Z s).2.1) ∧
      Bd S₀ (-(3 * (J + 1 : ℕ) : ℤ)) l (fun s => (Wjet (tailPoly d J) Z s).2.2) := by
  have hS0 : 0 < S₀ := by linarith
  have hsol : Solves S₀ (Wjet (tailPoly d J) Z) (jrem d (tailPoly d J) Z) :=
    wjet_solves (tailPoly d J) hZ hlow hS0 fun s hs => by linarith [hq s hs]
  have hd := fun s (hs : S₀ < s) => Calabi.Tail.hasDerivAt_components (hsol s hs.le)
  have hbase : ∀ s, S₀ < s →
      C / s ^ (3 * (J + 1)) = C * s ^ (-(3 * (J + 1 : ℕ) : ℤ)) := by
    intro s _
    rw [zpow_neg_three_mul, div_eq_mul_inv]
  induction l with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨C, hC, fun s hs => (hbase s hs) ▸ (norm_le_iff.1 (hdec s hs.le)).1⟩
    · exact ⟨C, hC, fun s hs => (hbase s hs) ▸ (norm_le_iff.1 (hdec s hs.le)).2.1⟩
    · exact ⟨C, hC, fun s hs => (hbase s hs) ▸ (norm_le_iff.1 (hdec s hs.le)).2.2⟩
  | succ l ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have hq0 := (bd_q hS0 (tailPoly d J) l).1
    -- the coefficient of the nonlinearity
    have hp0 : Bd S₀ 0 l (fun s => (Z s).1) := by
      refine Bd.congr (fun s _ => ?_) (Bd.add (Bd.mono_a hS0 (by omega) ih0) hq0)
      simp only [Wjet, Prod.fst_sub]
      ring
    have h1p : Bd S₀ 0 l (fun s => 1 + (Z s).1) := Bd.add (Bd.const 1 l) hp0
    have h1q : Bd S₀ 0 l (fun s => 1 + q0 (tailPoly d J) s) := Bd.add (Bd.const 1 l) hq0
    have hprod := Bd.mul_left0 hS0 h1p h1q
    have hinv : Bd S₀ 0 l (fun s => ((1 + (Z s).1) * (1 + q0 (tailPoly d J) s))⁻¹) := by
      refine Bd.inv hS0 (c := 1 / 40) (by norm_num) (fun s hs => ?_) hprod
      have h1 : (1 : ℝ) / 20 ≤ 1 + (Z s).1 := by linarith [hlow s (hS0.trans hs)]
      have h2 := hq s hs.le
      calc (1 : ℝ) / 40 = 1 / 20 * (1 / 2) := by norm_num
        _ ≤ (1 + (Z s).1) * (1 + q0 (tailPoly d J) s) :=
          mul_le_mul h1 h2 (by norm_num) (by linarith)
    have hψ : Bd S₀ 0 l (psi (tailPoly d J) Z) := Bd.sub (Bd.const 1 l) hinv
    -- the residual
    have hres : Bd S₀ (-(3 * (J + 1 : ℕ) : ℤ)) l
        (resid d (q0 (tailPoly d J)) (q1 (tailPoly d J)) (q2 (tailPoly d J))
          (q3 (tailPoly d J))) := by
      have h := Bd.mul hS0 (bd_E_tailPoly hS0 d J l)
        (Bd.inv hS0 (c := 1 / 2) (by norm_num) (fun s hs => hq s hs.le) h1q)
      rw [add_zero] at h
      refine Bd.congr (fun s hs => ?_) h
      have hpos : (0 : ℝ) < 1 + q0 (tailPoly d J) s := by linarith [hq s hs.le]
      rw [resid_eq d (tailPoly d J) (hS0.trans hs) hpos.ne', div_eq_mul_inv]
    -- the right-hand side
    have c1 : Bd S₀ 0 l (fun s : ℝ => -(21 / s)) :=
      Bd.congr (fun s _ => by rw [pow_one]; ring) (bd_const_div hS0 (-21) 1 l)
    have c2 : Bd S₀ 0 l (fun s : ℝ => 337 / (4 * s ^ 2)) :=
      Bd.congr (fun s _ => by ring) (bd_const_div hS0 (337 / 4) 2 l)
    have c3 : Bd S₀ 0 l (fun s : ℝ => 567 / (4 * s ^ 3)) :=
      Bd.congr (fun s _ => by ring) (bd_const_div hS0 (567 / 4) 3 l)
    have hF : Bd S₀ (-(3 * (J + 1 : ℕ) : ℤ)) l
        (fun s => -(Wjet (tailPoly d J) Z s).1 + jrem d (tailPoly d J) Z s) :=
      Bd.add (Bd.neg ih0)
        (Bd.sub (Bd.add (Bd.add (Bd.sub (Bd.mul_left0 hS0 c1 ih2) (Bd.mul_left0 hS0 c2 ih1))
          (Bd.mul_left0 hS0 c3 ih0)) (Bd.mul_left0 hS0 hψ ih0)) hres)
    exact ⟨Bd.succ_of ih0.bd0 (fun s hs => (hd s hs).1) ih1,
      Bd.succ_of ih1.bd0 (fun s hs => (hd s hs).2.1) ih2,
      Bd.succ_of ih2.bd0 (fun s hs => (hd s hs).2.2) hF⟩

end Calabi.Infinity
