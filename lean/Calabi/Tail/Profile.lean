import Calabi.Tail.Nonlinear
import Calabi.Shot.Physical

/-!
# The profile equation on `[56, ∞)`

Let `a` be an approximate solution of the profile equation on `[56, ∞)` with
residual at most `ε`. Writing `p = a + V`, the equation becomes

  `V‴ + V = -res - (21/s) V″ - (B/s²) V′ - (C/s³) V + N(a + V) - N(a)`,

`N(p) = p² / (1 + p)`. With `N` clamped to `|p| ≤ 1/100` the right-hand side
is Lipschitz in the jet with constant `17/40 < 3/5`, so
`Calabi.Tail.exists_tail` applies; the solution is small, hence the clamp is
inactive and `a + V` solves the profile system.
-/

open Set Filter
open scoped Topology

namespace Calabi.Tail

open Calabi.Shot (State pfield Ntr Ntr_of_ge)

/-- The clamp to `[-1/100, 1/100]`. -/
noncomputable def clamp (p : ℝ) : ℝ := max (-(1 / 100)) (min p (1 / 100))

theorem clamp_mem (p : ℝ) : -(1 / 100) ≤ clamp p ∧ clamp p ≤ 1 / 100 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem clamp_of_abs_le {p : ℝ} (h : |p| ≤ 1 / 100) : clamp p = p := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold clamp
  rw [min_eq_left h2, max_eq_right h1]

theorem abs_clamp_sub_le (p q : ℝ) : |clamp p - clamp q| ≤ |p - q| := by
  unfold clamp
  have h1 := abs_max_sub_max_le_max (-(1 / 100) : ℝ) (min p (1 / 100)) (-(1 / 100))
    (min q (1 / 100))
  have h2 := abs_min_sub_min_le_max p (1 / 100 : ℝ) q (1 / 100)
  rw [sub_self, abs_zero] at h1 h2
  exact h1.trans (max_le (abs_nonneg _) (h2.trans (max_le le_rfl (abs_nonneg _))))

/-- `p² / (1 + p)` with the argument clamped. -/
noncomputable def Ncl (p : ℝ) : ℝ := clamp p ^ 2 / (1 + clamp p)

theorem Ncl_of_abs_le {p : ℝ} (h : |p| ≤ 1 / 100) : Ncl p = p ^ 2 / (1 + p) := by
  unfold Ncl
  rw [clamp_of_abs_le h]

theorem Ncl_lipschitz (p q : ℝ) : |Ncl p - Ncl q| ≤ 21 / 1000 * |p - q| := by
  obtain ⟨u1, u2⟩ := clamp_mem p
  obtain ⟨v1, v2⟩ := clamp_mem q
  have hu : 0 < 1 + clamp p := by linarith
  have hv : 0 < 1 + clamp q := by linarith
  have key : Ncl p - Ncl q = (clamp p - clamp q) * (clamp p + clamp q + clamp p * clamp q) /
      ((1 + clamp p) * (1 + clamp q)) := by
    unfold Ncl
    field_simp
    ring
  have hnum : |clamp p + clamp q + clamp p * clamp q| ≤ 201 / 10000 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hden : (9801 : ℝ) / 10000 ≤ (1 + clamp p) * (1 + clamp q) := by nlinarith
  have hc := abs_clamp_sub_le p q
  rw [key, abs_div, abs_mul, abs_of_pos (mul_pos hu hv), div_le_iff₀ (mul_pos hu hv)]
  calc |clamp p - clamp q| * |clamp p + clamp q + clamp p * clamp q|
      ≤ |p - q| * (201 / 10000) := mul_le_mul hc hnum (abs_nonneg _) (abs_nonneg _)
    _ ≤ 21 / 1000 * |p - q| * (9801 / 10000) := by
        nlinarith [abs_nonneg (p - q)]
    _ ≤ 21 / 1000 * |p - q| * ((1 + clamp p) * (1 + clamp q)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

theorem continuous_Ncl : Continuous Ncl := by
  have hc : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  exact (hc.pow 2).div (continuous_const.add hc) fun p => by
    have := (clamp_mem p).1
    linarith

/-- The residual of an approximate solution `a`, with derivatives `a1, a2, a3`. -/
noncomputable def resid (d : ℝ) (a a1 a2 a3 : ℝ → ℝ) (s : ℝ) : ℝ :=
  a3 s + 21 / s * a2 s + 337 / (4 * s ^ 2) * a1 s - 567 / (4 * s ^ 3) * (a s - d)
    + a s / (1 + a s)

/-- The right-hand side of the equation for `V = p - a`. -/
noncomputable def Ftail (a res : ℝ → ℝ) (s : ℝ) (X : State) : ℝ :=
  -res s - 21 / s * X.2.2 - 337 / (4 * s ^ 2) * X.2.1 + 567 / (4 * s ^ 3) * X.1
    + Ncl (a s + X.1) - Ncl (a s)

theorem Ftail_zero (a res : ℝ → ℝ) (s : ℝ) : Ftail a res s 0 = -res s := by
  simp [Ftail]

theorem Ftail_lipschitz (a res : ℝ → ℝ) {s : ℝ} (hs : 56 ≤ s) (X Y : State) :
    |Ftail a res s X - Ftail a res s Y| ≤ 17 / 40 * dist X Y := by
  obtain ⟨h1, h2, h3⟩ := Calabi.Shot.State.dist_le_iff.1 (le_refl (dist X Y))
  have hr0 : 0 ≤ dist X Y := dist_nonneg
  have hs0 : (0 : ℝ) < s := by linarith
  have hs2 : (3136 : ℝ) ≤ s ^ 2 := by nlinarith
  have hs3 : (175616 : ℝ) ≤ s ^ 3 := by nlinarith
  have c2 : 21 / s ≤ 21 / 56 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have c2' : 0 ≤ 21 / s := div_nonneg (by norm_num) hs0.le
  have c1 : 337 / (4 * s ^ 2) ≤ 337 / 12544 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c1' : 0 ≤ 337 / (4 * s ^ 2) := div_nonneg (by norm_num) (by positivity)
  have c0 : 567 / (4 * s ^ 3) ≤ 567 / 702464 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have c0' : 0 ≤ 567 / (4 * s ^ 3) := div_nonneg (by norm_num) (by positivity)
  have hN := Ncl_lipschitz (a s + X.1) (a s + Y.1)
  rw [add_sub_add_left_eq_sub] at hN
  have e : Ftail a res s X - Ftail a res s Y =
      -(21 / s * (X.2.2 - Y.2.2)) - 337 / (4 * s ^ 2) * (X.2.1 - Y.2.1)
        + 567 / (4 * s ^ 3) * (X.1 - Y.1) + (Ncl (a s + X.1) - Ncl (a s + Y.1)) := by
    simp only [Ftail]
    ring
  rw [e]
  have b3 : |21 / s * (X.2.2 - Y.2.2)| ≤ 21 / 56 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c2']
    exact mul_le_mul c2 h3 (abs_nonneg _) (by norm_num)
  have b2 : |337 / (4 * s ^ 2) * (X.2.1 - Y.2.1)| ≤ 337 / 12544 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c1']
    exact mul_le_mul c1 h2 (abs_nonneg _) (by norm_num)
  have b1 : |567 / (4 * s ^ 3) * (X.1 - Y.1)| ≤ 567 / 702464 * dist X Y := by
    rw [abs_mul, abs_of_nonneg c0']
    exact mul_le_mul c0 h1 (abs_nonneg _) (by norm_num)
  have bN : |Ncl (a s + X.1) - Ncl (a s + Y.1)| ≤ 21 / 1000 * dist X Y := hN.trans (by linarith)
  obtain ⟨b3l, b3u⟩ := abs_le.1 b3
  obtain ⟨b2l, b2u⟩ := abs_le.1 b2
  obtain ⟨b1l, b1u⟩ := abs_le.1 b1
  obtain ⟨bNl, bNu⟩ := abs_le.1 bN
  rw [abs_le]
  constructor <;> linarith

theorem Ftail_continuousOn {a res : ℝ → ℝ} (ha : ContinuousOn a (Ici 56))
    (hres : ContinuousOn res (Ici 56)) :
    ContinuousOn (Function.uncurry (Ftail a res)) (Ici (56 : ℝ) ×ˢ univ) := by
  have hmaps : MapsTo (fun p : ℝ × State => p.1) (Ici (56 : ℝ) ×ˢ univ) (Ici 56) :=
    fun p hp => hp.1
  have hpos : ∀ p ∈ Ici (56 : ℝ) ×ˢ (univ : Set State), (0 : ℝ) < p.1 := fun p hp => by
    have : (56 : ℝ) ≤ p.1 := hp.1
    linarith
  have hs : ContinuousOn (fun p : ℝ × State => p.1) (Ici (56 : ℝ) ×ˢ univ) := continuousOn_fst
  have hx1 : ContinuousOn (fun p : ℝ × State => p.2.1) (Ici (56 : ℝ) ×ˢ univ) :=
    continuous_snd.fst.continuousOn
  have hx2 : ContinuousOn (fun p : ℝ × State => p.2.2.1) (Ici (56 : ℝ) ×ˢ univ) :=
    continuous_snd.snd.fst.continuousOn
  have hx3 : ContinuousOn (fun p : ℝ × State => p.2.2.2) (Ici (56 : ℝ) ×ˢ univ) :=
    continuous_snd.snd.snd.continuousOn
  have ha' : ContinuousOn (fun p : ℝ × State => a p.1) (Ici (56 : ℝ) ×ˢ univ) :=
    ha.comp hs hmaps
  have hres' : ContinuousOn (fun p : ℝ × State => res p.1) (Ici (56 : ℝ) ×ˢ univ) :=
    hres.comp hs hmaps
  have g2 : ContinuousOn (fun p : ℝ × State => 21 / p.1) (Ici (56 : ℝ) ×ˢ univ) :=
    continuousOn_const.div hs fun p hp => (hpos p hp).ne'
  have g1 : ContinuousOn (fun p : ℝ × State => 337 / (4 * p.1 ^ 2)) (Ici (56 : ℝ) ×ˢ univ) :=
    continuousOn_const.div (continuousOn_const.mul (hs.pow 2)) fun p hp => by
      have := hpos p hp
      positivity
  have g0 : ContinuousOn (fun p : ℝ × State => 567 / (4 * p.1 ^ 3)) (Ici (56 : ℝ) ×ˢ univ) :=
    continuousOn_const.div (continuousOn_const.mul (hs.pow 3)) fun p hp => by
      have := hpos p hp
      positivity
  have hN1 : ContinuousOn (fun p : ℝ × State => Ncl (a p.1 + p.2.1)) (Ici (56 : ℝ) ×ˢ univ) :=
    continuous_Ncl.comp_continuousOn (ha'.add hx1)
  have hN2 : ContinuousOn (fun p : ℝ × State => Ncl (a p.1)) (Ici (56 : ℝ) ×ˢ univ) :=
    continuous_Ncl.comp_continuousOn ha'
  exact (((((hres'.neg.sub (g2.mul hx3)).sub (g1.mul hx2)).add (g0.mul hx1)).add hN1).sub hN2)

/-- The contraction constant of the profile tail: `1 - (17/40)(5/3) = 7/24`. -/
theorem tail_gap : (1 : ℝ) - 17 / 40 * (5 / 3) = 7 / 24 := by norm_num

theorem resid_continuousOn (d : ℝ) {a a1 a2 a3 : ℝ → ℝ}
    (ha : ∀ s, 56 ≤ s → HasDerivAt a (a1 s) s) (ha1 : ∀ s, 56 ≤ s → HasDerivAt a1 (a2 s) s)
    (ha2 : ∀ s, 56 ≤ s → HasDerivAt a2 (a3 s) s) (ha3 : ContinuousOn a3 (Ici 56))
    (hα : ∀ s, 56 ≤ s → |a s| ≤ 1 / 100) : ContinuousOn (resid d a a1 a2 a3) (Ici 56) := by
  have hac : ContinuousOn a (Ici 56) := fun s hs => (ha s hs).continuousAt.continuousWithinAt
  have ha1c : ContinuousOn a1 (Ici 56) := fun s hs => (ha1 s hs).continuousAt.continuousWithinAt
  have ha2c : ContinuousOn a2 (Ici 56) := fun s hs => (ha2 s hs).continuousAt.continuousWithinAt
  have hpos : ∀ s ∈ Ici (56 : ℝ), (0 : ℝ) < s := fun s hs => by
    have : (56 : ℝ) ≤ s := hs
    linarith
  have g2 : ContinuousOn (fun s : ℝ => 21 / s) (Ici 56) :=
    continuousOn_const.div continuousOn_id fun s hs => (hpos s hs).ne'
  have g1 : ContinuousOn (fun s : ℝ => 337 / (4 * s ^ 2)) (Ici 56) :=
    continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun s hs => by
      have := hpos s hs
      positivity
  have g0 : ContinuousOn (fun s : ℝ => 567 / (4 * s ^ 3)) (Ici 56) :=
    continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 3)) fun s hs => by
      have := hpos s hs
      positivity
  have gq : ContinuousOn (fun s : ℝ => a s / (1 + a s)) (Ici 56) :=
    hac.div (continuousOn_const.add hac) fun s hs => by
      have h1 := abs_le.1 (hα s hs)
      linarith
  exact (((ha3.add (g2.mul ha2c)).add (g1.mul ha1c)).sub (g0.mul (hac.sub continuousOn_const))).add
    gq

/-- **Existence of the tail.** For an approximate solution `a` with residual at
most `ε` on `[56, ∞)`, every stable coordinate `q₀` at `s = 56` belongs to a
bounded solution of the clamped equation for `V = p - a`. -/
theorem exists_profile_tail {d ε : ℝ} {a a1 a2 a3 : ℝ → ℝ}
    (ha : ∀ s, 56 ≤ s → HasDerivAt a (a1 s) s) (ha1 : ∀ s, 56 ≤ s → HasDerivAt a1 (a2 s) s)
    (ha2 : ∀ s, 56 ≤ s → HasDerivAt a2 (a3 s) s) (ha3 : ContinuousOn a3 (Ici 56))
    (hα : ∀ s, 56 ≤ s → |a s| ≤ 1 / 100) (hres : ∀ s, 56 ≤ s → |resid d a a1 a2 a3 s| ≤ ε)
    (q₀ : ℝ) :
    ∃ X : ℝ → State, Solves 56 X (fun s => Ftail a (resid d a a1 a2 a3) s (X s)) ∧
      stab (X 56) = q₀ ∧
      (∀ s, 56 ≤ s → energy (X s) ≤ 4 * ((ε + 17 / 40 * |q₀|) / (7 / 24)) ^ 2) ∧
      ∀ s, 56 ≤ s →
        |(X s).1| ≤ |q₀| + 5 / 3 * ((ε + 17 / 40 * |q₀|) / (7 / 24)) ∧
        |(X s).2.1| ≤ |q₀| + 5 / 3 * ((ε + 17 / 40 * |q₀|) / (7 / 24)) ∧
        |(X s).2.2| ≤ |q₀| + 5 / 3 * ((ε + 17 / 40 * |q₀|) / (7 / 24)) := by
  have hac : ContinuousOn a (Ici 56) := fun s hs => (ha s hs).continuousAt.continuousWithinAt
  obtain ⟨X, hX, hq, hen, hb⟩ := exists_tail (F := Ftail a (resid d a a1 a2 a3))
    (by norm_num : (0 : ℝ) ≤ 17 / 40) (by norm_num)
    (Ftail_continuousOn hac (resid_continuousOn d ha ha1 ha2 ha3 hα))
    (fun s hs X Y => Ftail_lipschitz a _ hs X Y)
    (fun s hs => by rw [Ftail_zero, abs_neg]; exact hres s hs) q₀
  rw [tail_gap] at hen hb
  refine ⟨X, hX, hq, hen, fun s hs => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hb s hs
  have he : Real.exp (-(s - 56)) * |q₀| ≤ |q₀| :=
    mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The tail solves the profile system** wherever the clamp is inactive. -/
theorem profile_of_tail {d : ℝ} {a a1 a2 a3 : ℝ → ℝ} {X : ℝ → State}
    (hX : Solves 56 X (fun s => Ftail a (resid d a a1 a2 a3) s (X s))) {s : ℝ} (hs : 56 ≤ s)
    (ha : HasDerivAt a (a1 s) s) (ha1 : HasDerivAt a1 (a2 s) s) (ha2 : HasDerivAt a2 (a3 s) s)
    (hsa : |a s| ≤ 1 / 100) (hp : |a s + (X s).1| ≤ 1 / 100) :
    HasDerivAt (fun t => ((a t + (X t).1, a1 t + (X t).2.1, a2 t + (X t).2.2) : State))
      (pfield d s (a s + (X s).1, a1 s + (X s).2.1, a2 s + (X s).2.2)) s := by
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_components (hX s hs)
  have hs0 : (0 : ℝ) < s := by linarith
  have hall := (ha.add h1).prodMk ((ha1.add h2).prodMk (ha2.add h3))
  refine hall.congr_deriv ?_
  have hp1 : (0 : ℝ) < 1 + (a s + (X s).1) := by linarith [(abs_le.1 hp).1]
  have ha1' : (0 : ℝ) < 1 + a s := by linarith [(abs_le.1 hsa).1]
  have hNtr : Ntr (a s + (X s).1) = (a s + (X s).1) / (1 + (a s + (X s).1)) :=
    Ntr_of_ge (by linarith [(abs_le.1 hp).1])
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only [pfield, Ftail, resid, hNtr, Ncl_of_abs_le hp, Ncl_of_abs_le hsa]
  field_simp
  ring

/-- Two tails, for parameters `d` and `d′`, differ by their stable coordinates
at `s = 56` and by `|d - d′|`. -/
theorem profile_tail_dist_le {d d' : ℝ} {a a1 a2 a3 : ℝ → ℝ} {X X' : ℝ → State}
    (hX : Solves 56 X fun s => Ftail a (resid d a a1 a2 a3) s (X s))
    (hX' : Solves 56 X' fun s => Ftail a (resid d' a a1 a2 a3) s (X' s))
    (hb : ∃ B, ∀ s, (56 : ℝ) ≤ s → |(X s).1| ≤ B ∧ |(X s).2.1| ≤ B ∧ |(X s).2.2| ≤ B)
    (hb' : ∃ B, ∀ s, (56 : ℝ) ≤ s → |(X' s).1| ≤ B ∧ |(X' s).2.1| ≤ B ∧ |(X' s).2.2| ≤ B) :
    ∀ s, 56 ≤ s →
      dist (X s) (X' s) ≤ (|stab (X 56) - stab (X' 56)| + 5 / 3 * |d - d'|) / (7 / 24) := by
  have h := tail_dist_le (F := Ftail a (resid d a a1 a2 a3)) (F' := Ftail a (resid d' a a1 a2 a3))
    (δ := |d - d'|) (by norm_num : (0 : ℝ) ≤ 17 / 40) (by norm_num)
    (fun s hs X Y => Ftail_lipschitz a _ hs X Y) (fun s hs Y => ?_) hX hX' hb hb'
  · rw [tail_gap] at h
    exact h
  · have hs0 : (0 : ℝ) < s := by linarith
    have hs2 : (3136 : ℝ) ≤ s ^ 2 := by nlinarith
    have hs3 : (175616 : ℝ) ≤ s ^ 3 := by nlinarith
    have c0 : 567 / (4 * s ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have c0' : 0 ≤ 567 / (4 * s ^ 3) := div_nonneg (by norm_num) (by positivity)
    have e : Ftail a (resid d a a1 a2 a3) s Y - Ftail a (resid d' a a1 a2 a3) s Y =
        -(567 / (4 * s ^ 3) * (d - d')) := by
      simp only [Ftail, resid]
      ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg c0']
    exact mul_le_of_le_one_left (abs_nonneg _) c0

end Calabi.Tail
