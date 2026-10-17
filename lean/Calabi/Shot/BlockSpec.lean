import Calabi.Shot.BlockSound

/-!
# The analytic statement carried by a block summary

`block_spec` is the only fact about polynomial certificates that later
modules use. It speaks about an arbitrary trajectory `X` of the clamped block
system whose data at `t = -1` differ from the certified ones by `(ξ₀, ξ₁, ξ₂)`
and whose parameter differs by `η`: the trajectory stays in the region where
the clamp is inactive, and its value at `t = 1` is the certified one plus the
certified linear response, up to an explicit error.
-/

open Set

namespace Calabi.Shot

theorem comb_abs_le {ξ₀ ξ₁ ξ₂ η a b c e : ℝ} (ha : |a| ≤ 4) (hb : |b| ≤ 4) (hc : |c| ≤ 4)
    (he : |e| ≤ 4) :
    |ξ₀ * a + ξ₁ * b + ξ₂ * c + η * e| ≤ 4 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) := by
  have a0 : |ξ₀ * a| ≤ |ξ₀| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have a1 : |ξ₁ * b| ≤ |ξ₁| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have a2 : |ξ₂ * c| ≤ |ξ₂| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have a3 : |η * e| ≤ |η| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  obtain ⟨a0l, a0u⟩ := abs_le.1 a0
  obtain ⟨a1l, a1u⟩ := abs_le.1 a1
  obtain ⟨a2l, a2u⟩ := abs_le.1 a2
  obtain ⟨a3l, a3u⟩ := abs_le.1 a3
  rw [abs_le]
  constructor <;> linarith

theorem Block.ok_spec {b : Block} (h : b.ok = true) :
    16 ≤ b.H ∧ 129 ≤ b.A ∧ 7 * (scaleP : Int) ≤ 100 * minP b ∧
      tangentOk b b.U0 0 ⟨scaleU, 0, 0⟩ = true ∧ tangentOk b b.U1 0 ⟨0, scaleU, 0⟩ = true ∧
      tangentOk b b.U2 0 ⟨0, 0, scaleU⟩ = true ∧
      tangentOk b b.Ud (567 * (scaleU : Int)) ⟨0, 0, 0⟩ = true := by
  simp only [Block.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem tangentOk_spec {b : Block} {u : Poly} {forcing : Int} {unit : Jet}
    (h : tangentOk b u forcing unit = true) :
    Poly.l1 u ≤ 4 * scaleU ∧ jetAt (-1) u = unit ∧
      Poly.l1 (resU b u forcing) * 2 ^ 40 ≤
        scaleU * sigBound b * ((minP b).toNat * (minP b).toNat) := by
  simp only [tangentOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem ofPoly_neg_one (u : Poly) (s : ℝ) :
    (Jet3.ofPoly u s).f (-1) = ((jetAt (-1) u).v : ℝ) / s ∧
      (Jet3.ofPoly u s).f1 (-1) = ((jetAt (-1) u).d1 : ℝ) / s ∧
      (Jet3.ofPoly u s).f2 (-1) = ((jetAt (-1) u).d2 : ℝ) / s := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Jet3.ofPoly, jetAt, eval_neg_one]

theorem ofPoly_one (u : Poly) (s : ℝ) :
    (Jet3.ofPoly u s).f 1 = ((jetAt 1 u).v : ℝ) / s ∧
      (Jet3.ofPoly u s).f1 1 = ((jetAt 1 u).d1 : ℝ) / s ∧
      (Jet3.ofPoly u s).f2 1 = ((jetAt 1 u).d2 : ℝ) / s := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Jet3.ofPoly, jetAt, eval_one]

/-- **Meaning of a block summary.** -/
theorem block_spec {dnum : Int} {b : Block} {sm : Summary} (h : summarize dnum b = some sm)
    (heps : (sm.eps : ℝ) / (scaleE : ℝ) ≤ 1 / 1024)
    {ξ₀ ξ₁ ξ₂ η : ℝ} (hy : |ξ₀| + |ξ₁| + |ξ₂| + |η| ≤ 1 / 1024)
    {X : ℝ → State} (hX : ContinuousOn X (Icc (-1) 1))
    (hX' : ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt X
      (field (sm.H : ℝ) (sm.A : ℝ) ((dnum : ℝ) / scaleP + η) t (X t)) (Ici t) t)
    (h0 : X (-1) = ((sm.start.v : ℝ) / scaleP + ξ₀, (sm.start.d1 : ℝ) / scaleP + ξ₁,
      (sm.start.d2 : ℝ) / scaleP + ξ₂)) :
    (∀ t ∈ Icc (-1 : ℝ) 1, -19 / 20 ≤ (X t).1) ∧
      dist (((sm.stop.v : ℝ) / scaleP
            + (ξ₀ * ((sm.t0.v : ℝ) / scaleU) + ξ₁ * ((sm.t1.v : ℝ) / scaleU)
              + ξ₂ * ((sm.t2.v : ℝ) / scaleU) + η * ((sm.td.v : ℝ) / scaleU)),
          (sm.stop.d1 : ℝ) / scaleP
            + (ξ₀ * ((sm.t0.d1 : ℝ) / scaleU) + ξ₁ * ((sm.t1.d1 : ℝ) / scaleU)
              + ξ₂ * ((sm.t2.d1 : ℝ) / scaleU) + η * ((sm.td.d1 : ℝ) / scaleU)),
          (sm.stop.d2 : ℝ) / scaleP
            + (ξ₀ * ((sm.t0.d2 : ℝ) / scaleU) + ξ₁ * ((sm.t1.d2 : ℝ) / scaleU)
              + ξ₂ * ((sm.t2.d2 : ℝ) / scaleU) + η * ((sm.td.d2 : ℝ) / scaleU))) : State)
          (X 1) ≤
        8 * ((sm.eps : ℝ) / scaleE + 1 / 2 ^ 40 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|)
          + 14 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2) := by
  obtain ⟨hok, hH, hA, hstart, hstop, ht0, ht1, ht2, htd, hepsEq⟩ := summarize_some h
  obtain ⟨hHn, hAn, hm, hk0, hk1, hk2, hkd⟩ := Block.ok_spec hok
  obtain ⟨hl0, hj0, hr0⟩ := tangentOk_spec hk0
  obtain ⟨hl1, hj1, hr1⟩ := tangentOk_spec hk1
  obtain ⟨hl2, hj2, hr2⟩ := tangentOk_spec hk2
  obtain ⟨hld, hjd, hrd⟩ := tangentOk_spec hkd
  rw [hH, hA] at hX'
  rw [hstart] at h0
  rw [hepsEq] at heps
  rw [hstop, ht0, ht1, ht2, htd, hepsEq]
  have hSu := scaleU_pos
  have hHR : (16 : ℝ) ≤ (b.H : ℝ) := by exact_mod_cast hHn
  have hAR : (129 : ℝ) ≤ (b.A : ℝ) := by exact_mod_cast hAn
  have habs : ∀ t ∈ Icc (-1 : ℝ) 1, |t| ≤ 1 := fun t ht => abs_le.2 ht
  have hP : ∀ t ∈ Icc (-1 : ℝ) 1, 7 / 100 ≤ 1 + (Jet3.ofPoly b.P scaleP).f t := by
    intro t ht
    have hS := scaleP_pos
    have h1 := minP_le_eval b (habs t ht)
    have h2 : 7 * (scaleP : ℝ) ≤ 100 * ((minP b : Int) : ℝ) := by exact_mod_cast hm
    show 7 / 100 ≤ 1 + Poly.eval b.P t / (scaleP : ℝ)
    rw [one_add_div hS.ne', le_div_iff₀ hS]
    linarith
  have hU0 : ∀ t ∈ Icc (-1 : ℝ) 1, |(Jet3.ofPoly b.U0 scaleU).f t| ≤ 4 :=
    fun t ht => tangent_abs_le hl0 (habs t ht)
  have hU1 : ∀ t ∈ Icc (-1 : ℝ) 1, |(Jet3.ofPoly b.U1 scaleU).f t| ≤ 4 :=
    fun t ht => tangent_abs_le hl1 (habs t ht)
  have hU2 : ∀ t ∈ Icc (-1 : ℝ) 1, |(Jet3.ofPoly b.U2 scaleU).f t| ≤ 4 :=
    fun t ht => tangent_abs_le hl2 (habs t ht)
  have hUd : ∀ t ∈ Icc (-1 : ℝ) 1, |(Jet3.ofPoly b.Ud scaleU).f t| ≤ 4 :=
    fun t ht => tangent_abs_le hld (habs t ht)
  have hφ0 : ((0 : Int) : ℝ) = 567 * (scaleU : ℝ) * 0 := by simp
  have hφ1 : ((567 * (scaleU : Int) : Int) : ℝ) = 567 * (scaleU : ℝ) * 1 := by
    push_cast
    ring
  have hdP : ∀ t ∈ Icc (-1 : ℝ) 1,
      |(Jet3.ofPoly b.P scaleP).defect b.H b.A ((dnum : ℝ) / scaleP) t| ≤
        (epsP dnum b : ℝ) / scaleE :=
    fun t ht => defectP_le dnum b hHn hAn hm ht
  have hd0 : ∀ t ∈ Icc (-1 : ℝ) 1,
      |(Jet3.ofPoly b.U0 scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A 0 t| ≤ 1 / 2 ^ 40 :=
    fun t ht => defectU_le b b.U0 0 0 hφ0 hHn hAn hm hr0 ht
  have hd1 : ∀ t ∈ Icc (-1 : ℝ) 1,
      |(Jet3.ofPoly b.U1 scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A 0 t| ≤ 1 / 2 ^ 40 :=
    fun t ht => defectU_le b b.U1 0 0 hφ0 hHn hAn hm hr1 ht
  have hd2 : ∀ t ∈ Icc (-1 : ℝ) 1,
      |(Jet3.ofPoly b.U2 scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A 0 t| ≤ 1 / 2 ^ 40 :=
    fun t ht => defectU_le b b.U2 0 0 hφ0 hHn hAn hm hr2 ht
  have hdd : ∀ t ∈ Icc (-1 : ℝ) 1,
      |(Jet3.ofPoly b.Ud scaleU).linDefect (Jet3.ofPoly b.P scaleP) b.H b.A 1 t| ≤ 1 / 2 ^ 40 :=
    fun t ht => defectU_le b b.Ud (567 * (scaleU : Int)) 1 hφ1 hHn hAn hm hrd ht
  -- data at `t = -1`
  obtain ⟨p0, p1, p2⟩ := ofPoly_neg_one b.P scaleP
  obtain ⟨a0, a1, a2⟩ := ofPoly_neg_one b.U0 scaleU
  obtain ⟨b0, b1, b2⟩ := ofPoly_neg_one b.U1 scaleU
  obtain ⟨c0, c1, c2⟩ := ofPoly_neg_one b.U2 scaleU
  obtain ⟨e0, e1, e2⟩ := ofPoly_neg_one b.Ud scaleU
  rw [hj0] at a0 a1 a2
  rw [hj1] at b0 b1 b2
  rw [hj2] at c0 c1 c2
  rw [hjd] at e0 e1 e2
  simp only [Int.cast_natCast, Int.cast_zero, zero_div, div_self hSu.ne'] at a0 a1 a2 b0 b1 b2
  simp only [Int.cast_natCast, Int.cast_zero, zero_div, div_self hSu.ne'] at c0 c1 c2 e0 e1 e2
  have h0' : X (-1) =
      ((Jet3.ofPoly b.P scaleP).f (-1) + (ξ₀ * (Jet3.ofPoly b.U0 scaleU).f (-1)
          + ξ₁ * (Jet3.ofPoly b.U1 scaleU).f (-1) + ξ₂ * (Jet3.ofPoly b.U2 scaleU).f (-1)
          + η * (Jet3.ofPoly b.Ud scaleU).f (-1)),
        (Jet3.ofPoly b.P scaleP).f1 (-1) + (ξ₀ * (Jet3.ofPoly b.U0 scaleU).f1 (-1)
          + ξ₁ * (Jet3.ofPoly b.U1 scaleU).f1 (-1) + ξ₂ * (Jet3.ofPoly b.U2 scaleU).f1 (-1)
          + η * (Jet3.ofPoly b.Ud scaleU).f1 (-1)),
        (Jet3.ofPoly b.P scaleP).f2 (-1) + (ξ₀ * (Jet3.ofPoly b.U0 scaleU).f2 (-1)
          + ξ₁ * (Jet3.ofPoly b.U1 scaleU).f2 (-1) + ξ₂ * (Jet3.ofPoly b.U2 scaleU).f2 (-1)
          + η * (Jet3.ofPoly b.Ud scaleU).f2 (-1))) := by
    simp only [h0, p0, p1, p2, a0, a1, a2, b0, b1, b2, c0, c1, c2, e0, e1, e2, mul_one,
      mul_zero, add_zero, zero_add]
  have hfam := block_family (εP := (epsP dnum b : ℝ) / scaleE) (εU := 1 / 2 ^ 40) hHR hAR
    (Jet3.ofPoly b.P scaleP) (Jet3.ofPoly b.U0 scaleU) (Jet3.ofPoly b.U1 scaleU)
    (Jet3.ofPoly b.U2 scaleU) (Jet3.ofPoly b.Ud scaleU) hP hU0 hU1 hU2 hUd hdP hd0 hd1 hd2 hdd
    hy hX hX' h0'
  refine ⟨fun t ht => ?_, ?_⟩
  · have hd := hfam t ht
    obtain ⟨hx1, -, -⟩ := State.dist_le_iff.1 hd
    simp only at hx1
    obtain ⟨-, hxu⟩ := abs_le.1 hx1
    have hPt := hP t ht
    have hW := comb_abs_le (ξ₀ := ξ₀) (ξ₁ := ξ₁) (ξ₂ := ξ₂) (η := η)
      (hU0 t ht) (hU1 t ht) (hU2 t ht) (hUd t ht)
    obtain ⟨hWl, -⟩ := abs_le.1 hW
    have hy0 : 0 ≤ |ξ₀| + |ξ₁| + |ξ₂| + |η| := by positivity
    have hsq : (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ^ 2 ≤ (1 / 1024 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hy0 hy 2
    have hE1 : (1 : ℝ) / 2 ^ 40 * (|ξ₀| + |ξ₁| + |ξ₂| + |η|) ≤ 1 / 2 ^ 40 * (1 / 1024) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    norm_num at hsq hE1
    linarith
  · have h1mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
    have hend := hfam 1 h1mem
    obtain ⟨q0, q1, q2⟩ := ofPoly_one b.P scaleP
    obtain ⟨u00, u01, u02⟩ := ofPoly_one b.U0 scaleU
    obtain ⟨u10, u11, u12⟩ := ofPoly_one b.U1 scaleU
    obtain ⟨u20, u21, u22⟩ := ofPoly_one b.U2 scaleU
    obtain ⟨ud0, ud1, ud2⟩ := ofPoly_one b.Ud scaleU
    simp only [q0, q1, q2, u00, u01, u02, u10, u11, u12, u20, u21, u22, ud0, ud1, ud2] at hend
    exact hend

end Calabi.Shot
