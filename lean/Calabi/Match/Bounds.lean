import Calabi.Tail.Linear

/-!
# Bounds for the matching map at `s = 56`

The difference between the jet of the finite shot and the jet of the
approximate tail is `Δ₀ + z₁ g₁ + z₂ g₂ + ρ`, with a small remainder `ρ`. The
tail has the same stable coordinate and a small unstable energy. `match_row`
bounds one coordinate of the preconditioned matching map
`z ↦ z - C (unstable(Δ) - unstable(tail))`.
-/

namespace Calabi.Match

open Calabi.Shot (State)
open Calabi.Tail

theorem stab_comb (Δ₀ g₁ g₂ ρ : State) (z1 z2 : ℝ) :
    stab (Δ₀ + z1 • g₁ + z2 • g₂ + ρ) = stab Δ₀ + z1 * stab g₁ + z2 * stab g₂ + stab ρ := by
  simp only [stab, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem ux_comb (Δ₀ g₁ g₂ ρ : State) (z1 z2 : ℝ) :
    ux (Δ₀ + z1 • g₁ + z2 • g₂ + ρ) = ux Δ₀ + z1 * ux g₁ + z2 * ux g₂ + ux ρ := by
  simp only [ux, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem uw_comb (Δ₀ g₁ g₂ ρ : State) (z1 z2 : ℝ) :
    uw (Δ₀ + z1 • g₁ + z2 • g₂ + ρ) = uw Δ₀ + z1 * uw g₁ + z2 * uw g₂ + uw ρ := by
  simp only [uw, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem abs_stab_le {X : State} {p1 p2 p3 : ℝ} (h1 : |X.1| ≤ p1) (h2 : |X.2.1| ≤ p2)
    (h3 : |X.2.2| ≤ p3) : |stab X| ≤ (p1 + p2 + p3) / 3 := by
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 h3
  rw [abs_le]
  unfold stab
  constructor <;> linarith

theorem abs_ux_le {X : State} {p1 p2 p3 : ℝ} (h1 : |X.1| ≤ p1) (h2 : |X.2.1| ≤ p2)
    (h3 : |X.2.2| ≤ p3) : |ux X| ≤ p1 / 2 + p2 / 2 + p3 := by
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 h3
  rw [abs_le]
  unfold ux
  constructor <;> linarith

theorem abs_uw_le {X : State} {p1 p2 : ℝ} (h1 : |X.1| ≤ p1) (h2 : |X.2.1| ≤ p2) :
    |uw X| ≤ (p1 + p2) / 2 := by
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  unfold uw
  constructor <;> linarith

/-- The unstable coordinates in terms of the energy. -/
theorem abs_unstable_le {T : State} {J : ℝ} (hJ : 0 ≤ J) (h : energy T ≤ 4 * J ^ 2) :
    |ux T| ≤ 2 * J ∧ |uw T| ≤ 6 / 5 * J := by
  unfold energy at h
  refine ⟨abs_le_of_sq_le_sq ?_ (by positivity), abs_le_of_sq_le_sq ?_ (by positivity)⟩
  · nlinarith [sq_nonneg (uw T)]
  · nlinarith [sq_nonneg (ux T), sq_nonneg J]

theorem abs_mul_le_mul {a z b R : ℝ} (ha : |a| ≤ b) (hz : |z| ≤ R) : |a * z| ≤ b * R := by
  rw [abs_mul]
  exact mul_le_mul ha hz (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The stable coordinate of the difference. -/
theorem match_stab {R z1 z2 q0b qgb p1 p2 p3 : ℝ} {Δ₀ g₁ g₂ ρ : State} (hz1 : |z1| ≤ R)
    (hz2 : |z2| ≤ R) (h0 : |stab Δ₀| ≤ q0b) (hg : |stab g₁| + |stab g₂| ≤ qgb)
    (hρ1 : |ρ.1| ≤ p1) (hρ2 : |ρ.2.1| ≤ p2) (hρ3 : |ρ.2.2| ≤ p3) :
    |stab (Δ₀ + z1 • g₁ + z2 • g₂ + ρ)| ≤ q0b + qgb * R + (p1 + p2 + p3) / 3 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hz1
  rw [stab_comb]
  have t1 := abs_mul_le_mul (le_refl |stab g₁|) hz1
  have t2 := abs_mul_le_mul (le_refl |stab g₂|) hz2
  rw [mul_comm] at t1 t2
  have t3 := abs_stab_le hρ1 hρ2 hρ3
  have t4 := mul_le_mul_of_nonneg_right hg hR
  obtain ⟨a1, a2⟩ := abs_le.1 h0
  obtain ⟨b1, b2⟩ := abs_le.1 t1
  obtain ⟨c1, c2⟩ := abs_le.1 t2
  obtain ⟨d1, d2⟩ := abs_le.1 t3
  rw [abs_le]
  constructor <;> nlinarith

/-- One coordinate of the preconditioned matching map; `(e1, e2)` is `(1, 0)`
or `(0, 1)` and `(c1, c2)` the corresponding row of the preconditioner. -/
theorem match_row {R z1 z2 c1 c2 e1 e2 mb vb J p1 p2 p3 : ℝ} {Δ₀ g₁ g₂ ρ T : State}
    (hz1 : |z1| ≤ R) (hz2 : |z2| ≤ R)
    (hm : |e1 - c1 * ux g₁ - c2 * uw g₁| + |e2 - c1 * ux g₂ - c2 * uw g₂| ≤ mb)
    (hv : |c1 * ux Δ₀ + c2 * uw Δ₀| ≤ vb)
    (hρ1 : |ρ.1| ≤ p1) (hρ2 : |ρ.2.1| ≤ p2) (hρ3 : |ρ.2.2| ≤ p3)
    (hJ : 0 ≤ J) (hT : energy T ≤ 4 * J ^ 2) :
    |e1 * z1 + e2 * z2 - c1 * (ux (Δ₀ + z1 • g₁ + z2 • g₂ + ρ) - ux T)
        - c2 * (uw (Δ₀ + z1 • g₁ + z2 • g₂ + ρ) - uw T)| ≤
      mb * R + vb + (|c1| * (p1 / 2 + p2 / 2 + p3) + |c2| * ((p1 + p2) / 2))
        + (2 * |c1| + 6 / 5 * |c2|) * J := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hz1
  obtain ⟨hTx, hTw⟩ := abs_unstable_le hJ hT
  rw [ux_comb, uw_comb]
  have e : e1 * z1 + e2 * z2 - c1 * (ux Δ₀ + z1 * ux g₁ + z2 * ux g₂ + ux ρ - ux T)
      - c2 * (uw Δ₀ + z1 * uw g₁ + z2 * uw g₂ + uw ρ - uw T) =
      (e1 - c1 * ux g₁ - c2 * uw g₁) * z1 + (e2 - c1 * ux g₂ - c2 * uw g₂) * z2
        - (c1 * ux Δ₀ + c2 * uw Δ₀) - (c1 * ux ρ + c2 * uw ρ) + (c1 * ux T + c2 * uw T) := by
    ring
  rw [e]
  have t1 := abs_mul_le_mul (le_refl |e1 - c1 * ux g₁ - c2 * uw g₁|) hz1
  have t2 := abs_mul_le_mul (le_refl |e2 - c1 * ux g₂ - c2 * uw g₂|) hz2
  have t12 := mul_le_mul_of_nonneg_right hm hR
  have r1 := abs_mul_le_mul (le_refl |c1|) (abs_ux_le hρ1 hρ2 hρ3)
  have r2 := abs_mul_le_mul (le_refl |c2|) (abs_uw_le hρ1 hρ2)
  have s1 := abs_mul_le_mul (le_refl |c1|) hTx
  have s2 := abs_mul_le_mul (le_refl |c2|) hTw
  obtain ⟨a1, a2⟩ := abs_le.1 t1
  obtain ⟨b1, b2⟩ := abs_le.1 t2
  obtain ⟨v1, v2⟩ := abs_le.1 hv
  obtain ⟨k1, k2⟩ := abs_le.1 r1
  obtain ⟨l1, l2⟩ := abs_le.1 r2
  obtain ⟨m1, m2⟩ := abs_le.1 s1
  obtain ⟨n1, n2⟩ := abs_le.1 s2
  rw [abs_le]
  constructor <;> nlinarith

/-- A jet is determined by its three coordinates. -/
theorem eq_of_coords {X Y : State} (hs : stab X = stab Y) (hx : ux X = ux Y)
    (hw : uw X = uw Y) : X = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [fst_eq X, fst_eq Y, hs, hx, hw]
  · rw [snd_eq X, snd_eq Y, hs, hx, hw]
  · rw [thd_eq X, thd_eq Y, hs, hx]

/-- A matrix with nonzero determinant has trivial kernel. -/
theorem eq_zero_of_det_ne_zero {c11 c12 c21 c22 a b : ℝ} (hdet : c11 * c22 - c12 * c21 ≠ 0)
    (h1 : c11 * a + c12 * b = 0) (h2 : c21 * a + c22 * b = 0) : a = 0 ∧ b = 0 := by
  have ha : (c11 * c22 - c12 * c21) * a = 0 := by linear_combination c22 * h1 - c12 * h2
  have hb : (c11 * c22 - c12 * c21) * b = 0 := by linear_combination c11 * h2 - c21 * h1
  exact ⟨(mul_eq_zero.1 ha).resolve_left hdet, (mul_eq_zero.1 hb).resolve_left hdet⟩

end Calabi.Match
