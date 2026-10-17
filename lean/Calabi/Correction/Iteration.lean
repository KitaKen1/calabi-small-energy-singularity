import Calabi.Correction.FirstStep
import Calabi.Correction.PairLimit
import Calabi.Correction.Newton

/-!
# The correction as a pair of chart functions

Section 6.4 of the manuscript: with `H = F_λ + V`, the Calabi flow in the
momentum coordinate is

  `P_λ V + N_λ(V) = -E_λ`.

`exists_correction` solves this equation by the iteration of `Newton.lean`,
with the approximate right inverse of Lemma 6.3 (`approx_inverse`), the
Lipschitz estimate (6.15) of the nonlinearity (`NOf_diff_bound`) and the first
step `first_step`. The solution is a pair of chart functions (`PairSpace.lean`)
that is `C⁴` in space, has time derivatives on `(-T, 0)`, and is bounded by the
prescribed `e` in the weighted norm of the jets; the equation holds pointwise
on `(-T, 0) × [0, 1]`.

The exponent `γ` of the weight `w = -2 + 4γ` depends on the profile only; the
bound `e₀` on the size and the bound `T₁` on the time depend on the cut-off
radius `λ`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

theorem valOf_zero (t x : ℝ) : valOf (0 : Pair) t x = 0 := by
  show (0 : ℝ) + 0 = 0
  norm_num

theorem NOf_zero (vs : ℝ → ℝ) (bl af : ℝ → ℝ → ℝ) (t x : ℝ) : NOf vs bl af (0 : Pair) t x = 0 := by
  unfold NOf
  rw [valOf_zero]
  ring

variable {c : ℝ} {G : ℝ → ℝ}

set_option maxHeartbeats 3200000 in
/-- **The correction** (Proposition 6.1 of the manuscript, as a pair of chart
functions). -/
theorem exists_correction (hP : IsProfile c G) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∀ lam : ℝ, 0 < lam → lam < 1 / 8 → ∀ α α' : ℝ, 0 < α →
      α < α' → α' < 1 → ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 ∧ ∀ e : ℝ, 0 < e → e ≤ e₀ →
        ∃ T₁ : ℝ, 0 < T₁ ∧ T₁ ≤ lam ^ 2 ∧ T₁ ≤ 1 ∧ ∀ T : ℝ, 0 < T → T ≤ T₁ →
          ∃ (U : Pair) (M : ℝ), Reg U ∧ Sol T U ∧ XJ α T (-2 + 4 * γ) e U ∧
            XT α T (-2 + 4 * γ) M U ∧
            ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
              POf (blam G lam) (clam G lam) U t x
                + NOf vstar (blam G lam) (aflam G lam) U t x = -Elam G lam t x := by
  obtain ⟨γ, hγ, hγ1, Hinv⟩ := approx_inverse hP
  refine ⟨γ, hγ, hγ1, fun lam hlam hlam8 α α' hα hαα hα1 => ?_⟩
  have hα1' : α < 1 := hαα.trans hα1
  obtain ⟨CS, hCS, θ₀, hθ₀, hθ₀lam, η₀, hη₀, hη₀16, HS⟩ := Hinv lam hlam hlam8 α hα hα1'
  obtain ⟨K, hK, HK⟩ := coef_bounds hP α hα.le hα1'.le
  obtain ⟨CN, hCN, HN⟩ := NOf_diff_bound α (-2 + 4 * γ) K hα.le hα1'.le (by linarith) hK
  obtain ⟨M₁, hM₁, H1⟩ := first_step hP γ lam α α' hγ hγ1 hlam hlam8 hα hαα hα1
  have hCS0 : 0 < CS := by linarith
  refine ⟨min 1 (1 / (4 * (CN + 1) * CS)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro e he hee₀
  have he1 : e ≤ 1 := hee₀.trans (min_le_left _ _)
  have hsmall : 4 * CN * CS * e ≤ 1 := by
    have h1 : e ≤ 1 / (4 * (CN + 1) * CS) := hee₀.trans (min_le_right _ _)
    have h2 : 4 * CN * CS * e ≤ 4 * CN * CS * (1 / (4 * (CN + 1) * CS)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * CN * CS * (1 / (4 * (CN + 1) * CS)) = CN / (CN + 1) := by
      field_simp
    have h4 : CN / (CN + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  -- the size of the first residual
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = e / (8 * CS) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by
    rw [hε₁def]
    positivity
  have h8 : 8 * CS * ε₁ = e := by
    rw [hε₁def]
    field_simp
  -- the size of the first step
  obtain ⟨εf, hεfdef⟩ : ∃ εf : ℝ,
      εf = min (min (e / 2) (ε₁ / 2)) (min 1 (ε₁ / (2 * (CN + 1)))) := ⟨_, rfl⟩
  have hεf : 0 < εf := by
    rw [hεfdef]
    exact lt_min (lt_min (by positivity) (by positivity)) (lt_min one_pos (by positivity))
  have hεf_e : εf ≤ e / 2 := by
    rw [hεfdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hεf_ε : εf ≤ ε₁ / 2 := by
    rw [hεfdef]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεf_1 : εf ≤ 1 := by
    rw [hεfdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεf_N : εf ≤ ε₁ / (2 * (CN + 1)) := by
    rw [hεfdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨θ₁, hθ₁, hθ₁lam, η₁, hη₁, hη₁16, H1⟩ := H1 εf hεf
  -- the parameters
  obtain ⟨θs, hθsdef⟩ : ∃ θs : ℝ, θs = min θ₀ θ₁ := ⟨_, rfl⟩
  obtain ⟨ηs, hηsdef⟩ : ∃ ηs : ℝ, ηs = min η₀ η₁ := ⟨_, rfl⟩
  have hθs : 0 < θs := by
    rw [hθsdef]
    exact lt_min hθ₀ hθ₁
  have hηs : 0 < ηs := by
    rw [hηsdef]
    exact lt_min hη₀ hη₁
  have hθs0 : θs ≤ θ₀ := by
    rw [hθsdef]
    exact min_le_left _ _
  have hθs1 : θs ≤ θ₁ := by
    rw [hθsdef]
    exact min_le_right _ _
  have hηs0 : ηs ≤ η₀ := by
    rw [hηsdef]
    exact min_le_left _ _
  have hηs1 : ηs ≤ η₁ := by
    rw [hηsdef]
    exact min_le_right _ _
  have hθs2 : 0 < θs ^ 2 := by positivity
  have hθslam : θs ≤ lam / 8 := hθs0.trans hθ₀lam
  have hθs64 : θs ≤ 1 / 64 := by linarith
  have hθssq : θs ^ 2 ≤ lam ^ 2 := by
    have h1 : θs ≤ lam := by linarith
    exact pow_le_pow_left₀ hθs.le h1 2
  have hlamsq : lam ^ 2 ≤ 1 := pow_le_one₀ hlam.le (by linarith)
  have hηs16 : ηs ≤ 1 / 16 := hηs0.trans hη₀16
  have hT₁lam : ηs * θs ^ 2 ≤ lam ^ 2 := by
    have h1 : ηs * θs ^ 2 ≤ 1 / 16 * θs ^ 2 := mul_le_mul_of_nonneg_right hηs16 hθs2.le
    linarith
  refine ⟨ηs * θs ^ 2, by positivity, hT₁lam, hT₁lam.trans hlamsq, ?_⟩
  intro T hT hTT₁
  have hTlam : T ≤ lam ^ 2 := hTT₁.trans hT₁lam
  have hT1 : T ≤ 1 := hTlam.trans hlamsq
  have hTη₀ : T ≤ η₀ * θs ^ 2 := hTT₁.trans (mul_le_mul_of_nonneg_right hηs0 hθs2.le)
  have hTη₁ : T ≤ η₁ * θs ^ 2 := hTT₁.trans (mul_le_mul_of_nonneg_right hηs1 hθs2.le)
  obtain ⟨hbl, hcl, haf, hvs⟩ := HK lam T hlam hTlam hT1
  -- the first step
  obtain ⟨u₁, hu₁R, hu₁S, hu₁J, hu₁T, hu₁res⟩ := H1 θs T hθs hθs1 hT hTη₁
  have hNu₁ := HN T εf εf vstar (blam G lam) (aflam G lam) u₁ 0 hT1 hεf.le hεf_1 hεf.le hvs hbl
    haf hu₁R Reg.zero hu₁J ((XJ.zero α T (-2 + 4 * γ)).mono hεf.le) (by
      rw [sub_zero]
      exact hu₁J)
  have hres₁ : B0 α T (-2 + 4 * γ - 4) ε₁
      ((fun t x => -Elam G lam t x) - NOf vstar (blam G lam) (aflam G lam) u₁
        - POf (blam G lam) (clam G lam) u₁) := by
    refine ((hu₁res.sub hNu₁).congr fun t _ x _ => ?_).mono ?_
    · show -Elam G lam t x - NOf vstar (blam G lam) (aflam G lam) u₁ t x
          - POf (blam G lam) (clam G lam) u₁ t x
        = -Elam G lam t x - POf (blam G lam) (clam G lam) u₁ t x
          - (NOf vstar (blam G lam) (aflam G lam) u₁ t x
            - NOf vstar (blam G lam) (aflam G lam) 0 t x)
      rw [NOf_zero]
      ring
    · have h1 : εf * εf ≤ εf := by nlinarith
      have h2 : CN * (εf * εf) ≤ (CN + 1) * (ε₁ / (2 * (CN + 1))) := by
        calc CN * (εf * εf) ≤ CN * εf := mul_le_mul_of_nonneg_left h1 hCN
          _ ≤ (CN + 1) * εf := mul_le_mul_of_nonneg_right (by linarith) hεf.le
          _ ≤ (CN + 1) * (ε₁ / (2 * (CN + 1))) :=
              mul_le_mul_of_nonneg_left hεf_N (by linarith)
      have h3 : (CN + 1) * (ε₁ / (2 * (CN + 1))) = ε₁ / 2 := by
        field_simp
      linarith
  -- the iteration
  obtain ⟨u, hu0, hinc, hres, hball⟩ := Calabi.Newton.newton_iteration
    (BX := fun U a => Reg U ∧ Sol T U ∧ XJ α T (-2 + 4 * γ) a U ∧ XT α T (-2 + 4 * γ) a U)
    (BX' := fun U a => Reg U ∧ XJ α T (-2 + 4 * γ) a U)
    (BY := fun g a => B0 α T (-2 + 4 * γ - 4) a g)
    (P := POf (blam G lam) (clam G lam)) (N := NOf vstar (blam G lam) (aflam G lam))
    (E₀ := fun t x => -Elam G lam t x) (CS := CS) (CN := CN) (e := e) (ε₁ := ε₁) u₁ hCS0.le he
    hε₁
    (fun U U' a b h h' => ⟨h.1.add h'.1, XJ.add h.1 h'.1 h.2 h'.2⟩)
    (fun U a b h hab => ⟨h.1, h.2.mono hab⟩)
    ⟨Reg.zero, XJ.zero α T (-2 + 4 * γ)⟩
    (fun U a h => ⟨h.1, h.2.2.1⟩)
    (fun g h a b hg hh => hg.sub hh)
    (fun g a b hg hab => hg.mono hab)
    (fun U d a b h h' => POf_add _ _ h.1 h'.1)
    (fun g m hm hg => by
      obtain ⟨S, hSR, hSS, hSJ, hST, hSres⟩ := HS θs T m g hθs hθs0 hT hTη₀ hm hg
      exact ⟨S, ⟨hSR, hSS, hSJ, hST⟩, hSres⟩)
    (fun U U' d h h' hd hdd => by
      have h1 := HN T e d vstar (blam G lam) (aflam G lam) U U' hT1 he.le he1 hd hvs hbl haf
        h.1 h'.1 h.2 h'.2 hdd.2
      refine h1.mono (le_of_eq ?_)
      ring)
    hsmall ⟨hu₁R, hu₁J.mono hεf_e⟩ hres₁ (le_of_eq h8)
  -- the limit
  have hA : 0 ≤ CS * ε₁ := by positivity
  have hSol : ∀ n, Sol T (u n) := by
    intro n
    induction n with
    | zero =>
      rw [hu0]
      exact hu₁S
    | succ n ih =>
      have h1 := ih.add (hinc n).2.1
      have e1 : u n + (u (n + 1) - u n) = u (n + 1) := by abel
      rwa [e1] at h1
  have hdJ : ∀ n, XJ α T (-2 + 4 * γ) (CS * ε₁ * (3 / 4) ^ n) (u (n + 1) - u n) := fun n =>
    (hinc n).2.2.1.mono (le_of_eq (by ring))
  have hdT : ∀ n, XT α T (-2 + 4 * γ) (CS * ε₁ * (3 / 4) ^ n) (u (n + 1) - u n) := fun n =>
    (hinc n).2.2.2.mono (le_of_eq (by ring))
  obtain ⟨hR, hS, hXJ, hXT, hconv⟩ := pairLim_spec hT1 hA u (fun n => (hball n).1) hSol hdJ hdT
  refine ⟨pairLim T u, M₁ + 4 * (CS * ε₁), hR, hS, hXJ e (fun n => (hball n).2),
    hXT M₁ (by rw [hu0]; exact hu₁T), ?_⟩
  intro t ht x hx
  have ht' : t ∈ Ico (-T) 0 := ⟨ht.1.le, ht.2⟩
  obtain ⟨hv, hd, hAc⟩ := hconv t ht' x hx
  -- the residuals tend to zero
  have hzero : Tendsto (fun n => -Elam G lam t x
      - NOf vstar (blam G lam) (aflam G lam) (u n) t x
      - POf (blam G lam) (clam G lam) (u n) t x) atTop (𝓝 0) := by
    have hbound : ∃ W : ℝ, ∀ n, |(-Elam G lam t x
        - NOf vstar (blam G lam) (aflam G lam) (u n) t x
        - POf (blam G lam) (clam G lam) (u n) t x)| ≤ ε₁ * (3 / 4) ^ n * W := by
      rcases le_or_gt x (3 / 4) with hx34 | hx34
      · have hz : ‖Real.sqrt x • e18‖ ^ 2 = x := norm_sq_ray18 hx.1
        have hp : ((Real.sqrt x • e18, t) : Flat18 × ℝ) ∈ dom0 T := ⟨ht', by
          show ‖Real.sqrt x • e18‖ ^ 2 ≤ 3 / 4
          rw [hz]
          exact hx34⟩
        refine ⟨sigma ((Real.sqrt x • e18, t) : Flat18 × ℝ) ^ (-2 + 4 * γ - 4), fun n => ?_⟩
        have h1 := (hres n).1.1 _ hp
        rw [Real.norm_eq_abs] at h1
        simp only [hz] at h1
        exact h1
      · have hz : ‖Real.sqrt (1 - x) • e6‖ ^ 2 = 1 - x := norm_sq_ray6 (by linarith [hx.2])
        have hp : ((Real.sqrt (1 - x) • e6, t) : Flat6 × ℝ) ∈ dom1 T := ⟨ht', by
          show ‖Real.sqrt (1 - x) • e6‖ ^ 2 ≤ 7 / 8
          rw [hz]
          linarith⟩
        refine ⟨(1 : ℝ) ^ (-2 + 4 * γ - 4), fun n => ?_⟩
        have h1 := (hres n).2.1 _ hp
        rw [Real.norm_eq_abs] at h1
        simp only [hz, sub_sub_cancel] at h1
        exact h1
    obtain ⟨W, hW⟩ := hbound
    have hgeo : Tendsto (fun n : ℕ => ε₁ * (3 / 4 : ℝ) ^ n * W) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)).const_mul ε₁
      have h2 := h1.mul_const W
      simpa using h2
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hgeo
    rw [Real.dist_eq, sub_zero]
    exact hW n
  -- the limit of the residuals
  have hPc : Tendsto (fun n => POf (blam G lam) (clam G lam) (u n) t x) atTop
      (𝓝 (POf (blam G lam) (clam G lam) (pairLim T u) t x)) :=
    (hd.add (hAc.const_mul (blam G lam t x ^ 2))).add (hv.const_mul (clam G lam t x))
  have hNc : Tendsto (fun n => NOf vstar (blam G lam) (aflam G lam) (u n) t x) atTop
      (𝓝 (NOf vstar (blam G lam) (aflam G lam) (pairLim T u) t x)) :=
    (((hv.pow 2).const_mul (vstar x ^ 2)).mul_const (aflam G lam t x)).add
      (((hv.const_mul (2 * vstar x * blam G lam t x)).add
        ((hv.pow 2).const_mul (vstar x ^ 2))).mul hAc)
  have hlim := (tendsto_const_nhds (x := -Elam G lam t x)).sub hNc |>.sub hPc
  have huniq := tendsto_nhds_unique hlim hzero
  linarith

end Calabi.Weighted
