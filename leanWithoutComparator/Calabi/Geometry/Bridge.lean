import Calabi.Geometry.Kahler
import Calabi.Geometry.Volume
import Calabi.Geometry.PotentialBound
import Calabi.Geometry.SobolevTransfer
import Calabi.Radial.Estimates

/-!
# From the momentum coordinate to `CP⁷`

Proposition 2.1 and Lemma 2.3 of the manuscript, and the part of Section 7 that
does not concern the Sobolev constant: a family of solutions of the momentum
equation as in `Calabi.Radial.RadialMainP` gives Calabi flows on `CP⁷`.

For a positive solution `H` of the momentum equation on `(-T_r, 0)`,
`flowOf H T_r` is the potential of the metric of `H` at the time `s - T_r / 2`,
`0 ≤ s < T_r / 2`: the time `t₀ = -T_r / 2` is the initial time of the flow.

* `isCalabiFlow_flowOf`: it is a smooth Calabi flow in the Fubini–Study class;
* `abs_flowOf_zero_le`: the initial potential is bounded by the first moment
  of `H(t₀)`;
* `isProbabilityMeasure_flowOf`, `eLpNorm_flowOf`: the normalized volume is a
  probability measure and `∫ |S - 56|^p dν = ∫₀¹ |K(H)|^p 7x⁶ dx`;
* `tendsto_flowOf`: `S(o) = 56 (1 - H(t, 0))` and the blow-up of Lemma 2.3.

`mainTheoremCore_of_radialMainP` combines them: for every `2 ≤ p < 7` and
`ε, τ > 0` a smooth `U(7)`-invariant Calabi flow on `[0, T)`, `T < τ`, with
initial potential smaller than `ε` in the uniform norm, `‖S - 56‖_{L^p(ν)} < ε`
at every time, and `√(T - t) S(o) → -56 G′(0) > 0`. This is
`Calabi.Geometry.MainTheorem` without the uniform Sobolev bound
(`MainTheoremCore`).
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Calabi.Legendre.Flow

open Calabi.Geometry Calabi.Strip Calabi.Radial

variable {J : Set ℝ} {H : ℝ → ℝ → ℝ} {t₀ t : ℝ}

/-- Every momentum `x ∈ (0, 1)` is attained on the chart. -/
theorem xq_surj (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∃ q, 0 < q ∧ xq H t₀ t q = x := by
  intro x hx
  have hxI := Ioo_subset_Icc_self hx
  have hE := Real.exp_pos (afun H t₀ t x)
  have h1x : 0 < 1 - x := sub_pos.2 hx.2
  have hN : 0 < x * Real.exp (afun H t₀ t x) := mul_pos hx.1 hE
  refine ⟨x * Real.exp (afun H t₀ t x) / (1 - x), div_pos hN h1x, ?_⟩
  have e : x * Real.exp (afun H t₀ t x) / (1 - x)
      / (1 + x * Real.exp (afun H t₀ t x) / (1 - x)) = Xi H t₀ t x := by
    unfold Xi Dhat
    generalize x * Real.exp (afun H t₀ t x) = N at hN ⊢
    generalize 1 - x = w at h1x ⊢
    have h1 : (1 + N / w) ≠ 0 := by positivity
    have h2 : (w + N) ≠ 0 := by positivity
    rw [div_eq_div_iff h1 h2]
    field_simp
  show Xinv H t₀ t (x * Real.exp (afun H t₀ t x) / (1 - x)
    / (1 + x * Real.exp (afun H t₀ t x) / (1 - x))) = x
  rw [e, hF.Xinv_Xi ht₀ ht hxI]

/-- The momentum of the point `q = x e^{a(x)} / (1 - x)` is `x`. -/
theorem xq_Q (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    ∀ x ∈ Ico (0 : ℝ) 1, xq H t₀ t (x * Real.exp (afun H t₀ t x) / (1 - x)) = x := by
  intro x hx
  have hxI := Ico_subset_Icc_self hx
  have hE := Real.exp_pos (afun H t₀ t x)
  have h1x : 0 < 1 - x := sub_pos.2 hx.2
  have hN : 0 ≤ x * Real.exp (afun H t₀ t x) := mul_nonneg hx.1 hE.le
  have e : x * Real.exp (afun H t₀ t x) / (1 - x)
      / (1 + x * Real.exp (afun H t₀ t x) / (1 - x)) = Xi H t₀ t x := by
    unfold Xi Dhat
    generalize x * Real.exp (afun H t₀ t x) = N at hN ⊢
    generalize 1 - x = w at h1x ⊢
    have h1 : (1 + N / w) ≠ 0 := by positivity
    have h2 : (w + N) ≠ 0 := by positivity
    rw [div_eq_div_iff h1 h2]
    field_simp
  show Xinv H t₀ t (x * Real.exp (afun H t₀ t x) / (1 - x)
    / (1 + x * Real.exp (afun H t₀ t x) / (1 - x))) = x
  rw [e, hF.Xinv_Xi ht₀ ht hxI]

theorem contDiffOn_afun (hF : Flow J H) (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    ContDiffOn ℝ ∞ (afun H t₀ t) (Icc 0 1) := by
  have hpair : ContDiffOn ℝ ∞ (fun x : ℝ => ((t, x) : ℝ × ℝ)) (Icc 0 1) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := ContDiffOn.comp (hF.smooth_afun ht₀) hpair fun x hx => ⟨ht, hx⟩
  exact h

end Calabi.Legendre.Flow

namespace Calabi.Geometry

open Calabi.Legendre Calabi.Radial

/-- The Calabi flow on `[0, T_r / 2)` defined by a solution `H` of the momentum
equation on `(-T_r, 0)`. -/
noncomputable def flowOf (H : ℝ → ℝ → ℝ) (Tr s : ℝ) : Hom → ℝ :=
  Fhat H (-(Tr / 2)) (s + -(Tr / 2))

theorem isU7Invariant_flowOf (H : ℝ → ℝ → ℝ) (Tr s : ℝ) : IsU7Invariant (flowOf H Tr s) :=
  isU7Invariant_Fhat H _ _

section FlowOf

variable {H : ℝ → ℝ → ℝ} {Tr : ℝ}

theorem t0_mem (hTr : 0 < Tr) : -(Tr / 2) ∈ Ioo (-Tr) 0 := ⟨by linarith, by linarith⟩

theorem shift_mem {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (Tr / 2)) : s + -(Tr / 2) ∈ Ioo (-Tr) 0 :=
  ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩

variable (hF : Flow (Ioo (-Tr) 0) H) (hTr : 0 < Tr)

include hF hTr

/-- **Proposition 2.1**: the metrics of a solution of the momentum equation
form a smooth Calabi flow in the Fubini–Study class of `CP⁷`. -/
theorem isCalabiFlow_flowOf : IsCalabiFlow (Tr / 2) (flowOf H Tr) := by
  have ht₀ := t0_mem hTr
  refine ⟨?_, fun s hs => hF.isKahlerPotential_Fhat ht₀ (shift_mem hs), fun s hs Z => ?_⟩
  · have hshift : ContDiffOn ℝ ∞ (fun p : ℝ × Hom => ((p.1 + -(Tr / 2), p.2) : ℝ × Hom))
        (Ico 0 (Tr / 2) ×ˢ {v : Hom | v ≠ 0}) :=
      (contDiffOn_fst.add contDiffOn_const).prodMk contDiffOn_snd
    have h := ContDiffOn.comp (hF.contDiffOn_Fhat ht₀) hshift
      fun p hp => ⟨shift_mem hp.1, hp.2⟩
    exact h
  · have h := hF.hasDerivAt_Fhat_chart ht₀ (shift_mem hs) Z
    exact (HasDerivAt.comp_add_const s (-(Tr / 2)) h).hasDerivWithinAt

/-- **Section 7.2**: the initial potential is bounded by the first moment of
`H` at the initial time. -/
theorem abs_flowOf_zero_le {κ : ℝ} (hκ : 0 < κ)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ 1 + vstar x * H (-(Tr / 2)) x) (v : Hom) :
    |flowOf H Tr 0 v| ≤ 2 * (κ⁻¹ * ∫ s in (0 : ℝ)..1, s * |H (-(Tr / 2)) s|) := by
  have ht₀ := t0_mem hTr
  show |Fhat H (-(Tr / 2)) (0 + -(Tr / 2)) v| ≤ _
  rw [zero_add]
  have h1 := hF.abs_Fhat_le ht₀ v
  have h2 := hF.integral_hq_le ht₀ hκ hpos
  linarith

theorem isProbabilityMeasure_flowOf {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (Tr / 2)) :
    IsProbabilityMeasure (nu (pot (flowOf H Tr s) 0)) := by
  have ht₀ := t0_mem hTr
  have ht := shift_mem hs
  show IsProbabilityMeasure (nu (pot (Fhat H (-(Tr / 2)) (s + -(Tr / 2))) 0))
  rw [pot_Fhat_zero]
  exact (hF.momentumData ht₀ ht).isProbabilityMeasure_nu (hF.xq_surj ht₀ ht)

/-- **Section 7.1**: `∫ |S - 56|^p dν = ∫₀¹ |K(H)|^p 7x⁶ dx`. -/
theorem eLpNorm_flowOf {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (Tr / 2)) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun Z => scal (pot (flowOf H Tr s) 0) Z - 56) (ENNReal.ofReal p)
        (nu (pot (flowOf H Tr s) 0)) ^ p
      = ENNReal.ofReal (∫ x in (0 : ℝ)..1, |Kop (H (s + -(Tr / 2))) x| ^ p * (7 * x ^ 6)) := by
  have ht₀ := t0_mem hTr
  have ht := shift_mem hs
  show eLpNorm (fun Z => scal (pot (Fhat H (-(Tr / 2)) (s + -(Tr / 2))) 0) Z - 56)
      (ENNReal.ofReal p) (nu (pot (Fhat H (-(Tr / 2)) (s + -(Tr / 2))) 0)) ^ p = _
  rw [pot_Fhat_zero]
  exact (hF.momentumData ht₀ ht).eLpNorm_scal_rpow (hF.xq_surj ht₀ ht)
    (hF.smooth_KH.continuousOn_x ht) hp

/-- **Lemma 2.3**: the scalar curvature at the origin is `56 (1 - H(t, 0))`, and
blows up like `(T - s)^{-1/2}`. -/
theorem tendsto_flowOf {g : ℝ}
    (htend : Tendsto (fun t => Real.sqrt (-t) * H t 0) (𝓝[<] 0) (𝓝 g)) :
    Tendsto (fun s => Real.sqrt (Tr / 2 - s) * scal (pot (flowOf H Tr s) 0) 0)
      (𝓝[<] (Tr / 2)) (𝓝 (-56 * g)) := by
  have ht₀ := t0_mem hTr
  have hscal : ∀ s ∈ Ico (0 : ℝ) (Tr / 2),
      scal (pot (flowOf H Tr s) 0) 0 = 56 * (1 - H (s + -(Tr / 2)) 0) :=
    fun s hs => hF.scal_Fhat_origin ht₀ (shift_mem hs)
  have hshift : Tendsto (fun s : ℝ => s + -(Tr / 2)) (𝓝[<] (Tr / 2)) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun s : ℝ => s + -(Tr / 2)) (𝓝 (Tr / 2))
          (𝓝 (Tr / 2 + -(Tr / 2))) := (continuous_id.add continuous_const).tendsto _
      rw [add_neg_cancel] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s < Tr / 2 := hs
      show s + -(Tr / 2) < 0
      linarith
  have h1 : Tendsto (fun s : ℝ => Real.sqrt (-(s + -(Tr / 2))) * H (s + -(Tr / 2)) 0)
      (𝓝[<] (Tr / 2)) (𝓝 g) := htend.comp hshift
  have h2 : Tendsto (fun s : ℝ => Real.sqrt (Tr / 2 - s)) (𝓝[<] (Tr / 2)) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => Real.sqrt (Tr / 2 - s)) (𝓝 (Tr / 2))
        (𝓝 (Real.sqrt (Tr / 2 - Tr / 2))) :=
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).tendsto _
    rw [sub_self, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun s : ℝ => 56 * Real.sqrt (Tr / 2 - s)
      - 56 * (Real.sqrt (-(s + -(Tr / 2))) * H (s + -(Tr / 2)) 0))
      (𝓝[<] (Tr / 2)) (𝓝 (56 * 0 - 56 * g)) := (h2.const_mul 56).sub (h1.const_mul 56)
  have h4 : (56 * 0 - 56 * g : ℝ) = -56 * g := by ring
  rw [h4] at h3
  refine h3.congr' ?_
  have hev : ∀ᶠ s in 𝓝[<] (Tr / 2), s ∈ Ico (0 : ℝ) (Tr / 2) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Tr / 2 by positivity)] with s hs
      using ⟨hs.1.le, hs.2⟩
  filter_upwards [hev] with s hs
  show 56 * Real.sqrt (Tr / 2 - s)
      - 56 * (Real.sqrt (-(s + -(Tr / 2))) * H (s + -(Tr / 2)) 0)
    = Real.sqrt (Tr / 2 - s) * scal (pot (flowOf H Tr s) 0) 0
  rw [hscal s hs]
  have e : -(s + -(Tr / 2)) = Tr / 2 - s := by ring
  rw [e]
  ring

/-- **Section 7.3**: the Sobolev constant of the metrics of the flow is at most
`Λ` times the Sobolev constant of the Fubini–Study metric, where `Λ` bounds the
positivity multiplier `1 + v∗ H` and its inverse. -/
theorem hasSobolevBound_flowOf {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (Tr / 2)) {Λ C₀ : ℝ}
    (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ t ∈ Ioo (-Tr) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      1 + vstar x * H t x ≤ Λ ∧ (1 + vstar x * H t x)⁻¹ ≤ Λ)
    (hC₀ : 0 < C₀) (hFS : HasSobolevBound (pot (fun _ => 0) 0) C₀) :
    HasSobolevBound (pot (flowOf H Tr s) 0) (Λ * C₀) := by
  have ht₀ := t0_mem hTr
  have ht := shift_mem hs
  show HasSobolevBound (pot (Fhat H (-(Tr / 2)) (s + -(Tr / 2))) 0) (Λ * C₀)
  rw [pot_Fhat_zero]
  rw [pot_zero] at hFS
  exact (hF.momentumData ht₀ ht).hasSobolevBound (hF.xq_Q ht₀ ht) (hF.contDiffOn_afun ht₀ ht)
    hΛ1 (fun x hx => hΛ _ ht x hx) hC₀ hFS

end FlowOf

/-! ### The main theorem without the Sobolev bound -/

/-- **Theorem 1.1 of the manuscript without the Sobolev bound.** For every
`2 ≤ p < 7` and `ε, τ > 0` there is a smooth `U(7)`-invariant Calabi flow on
`[0, T)`, `T < τ`, in the Fubini–Study class of `CP⁷`, with initial potential
smaller than `ε` in the uniform norm, `‖S - 56‖_{L^p(ν)} < ε` at every time, and
`S(o) ∼ a (T - t)^{-1/2}` at the origin `o` of the first chart, `a > 0`. -/
def MainTheoremCore : Prop :=
  ∀ p : ℝ, 2 ≤ p → p < 7 → ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (F : ℝ → Hom → ℝ), 0 < T ∧ T < τ ∧ IsCalabiFlow T F ∧
      (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
      (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
      (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
        eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) (ENNReal.ofReal p) (nu (pot (F t) 0))
          < ENNReal.ofReal ε) ∧
      ∃ a : ℝ, 0 < a ∧
        Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

/-- The case `p = 2` of `MainTheoremCore`: arbitrarily small Calabi energy. -/
def MainTheoremEnergyCore : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, 0 < τ →
    ∃ (T : ℝ) (F : ℝ → Hom → ℝ), 0 < T ∧ T < τ ∧ IsCalabiFlow T F ∧
      (∀ t ∈ Ico 0 T, IsU7Invariant (F t)) ∧
      (∀ v : Hom, v ≠ 0 → |F 0 v| < ε) ∧
      (∀ t ∈ Ico 0 T, IsProbabilityMeasure (nu (pot (F t) 0)) ∧
        eLpNorm (fun Z => scal (pot (F t) 0) Z - 56) 2 (nu (pot (F t) 0)) < ENNReal.ofReal ε) ∧
      ∃ a : ℝ, 0 < a ∧
        Tendsto (fun t => Real.sqrt (T - t) * scal (pot (F t) 0) 0) (𝓝[<] T) (𝓝 a)

theorem MainTheorem.core (h : MainTheorem) : MainTheoremCore := by
  obtain ⟨CS, hCS⟩ := h
  intro p hp2 hp7 ε hε τ hτ
  obtain ⟨T, F, hT, hTτ, hflow, hU, h0, hmeas, hblow⟩ := hCS p hp2 hp7 ε hε τ hτ
  exact ⟨T, F, hT, hTτ, hflow, hU, h0, fun t ht => ⟨(hmeas t ht).1, (hmeas t ht).2.1⟩, hblow⟩

theorem MainTheoremCore.energy (h : MainTheoremCore) : MainTheoremEnergyCore := by
  intro ε hε τ hτ
  have h2 := h 2 le_rfl (by norm_num) ε hε τ hτ
  simpa using h2

/-- **The geometric reduction**: solutions of the momentum equation as in
`RadialMainP` give the Calabi flows of the main theorem (without the Sobolev
bound). -/
theorem mainTheoremCore_of_radialMainP {G : ℝ → ℝ} (hG : deriv G 0 < 0)
    (h : RadialMainP G) : MainTheoremCore := by
  obtain ⟨κ₁, κ₂, hκ₁, hmain⟩ := h
  intro p hp2 hp7 ε hε τ hτ
  have hp0 : 0 < p := by linarith
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hεr : 0 < min (ε ^ p) (κ₁ * ε / 2) := lt_min hεp (by positivity)
  obtain ⟨Tr, H, hTr, hTrτ, hflow, hpos, henergy, hmoment, htend⟩ :=
    hmain p hp2 hp7 _ hεr τ hτ
  have hF : Flow (Ioo (-Tr) 0) H :=
    ⟨isOpen_Ioo, ordConnected_Ioo, hflow.smooth,
      fun t ht x hx => lt_of_lt_of_le hκ₁ (hpos t ht x hx).1, hflow.eqn⟩
  refine ⟨Tr / 2, flowOf H Tr, by positivity, by linarith, isCalabiFlow_flowOf hF hTr,
    fun s _ => isU7Invariant_flowOf H Tr s, fun v _ => ?_, fun s hs => ?_,
    ⟨-56 * deriv G 0, by nlinarith, tendsto_flowOf hF hTr htend⟩⟩
  · have h1 := abs_flowOf_zero_le hF hTr hκ₁ (fun x hx => (hpos _ (t0_mem hTr) x hx).1) v
    have h3 := (hmoment _ (t0_mem hTr)).trans_le (min_le_right _ _)
    have h4 : κ₁⁻¹ * ∫ s in (0 : ℝ)..1, s * |H (-(Tr / 2)) s| < κ₁⁻¹ * (κ₁ * ε / 2) :=
      mul_lt_mul_of_pos_left h3 (inv_pos.2 hκ₁)
    have h5 : κ₁⁻¹ * (κ₁ * ε / 2) = ε / 2 := by
      field_simp
    linarith
  · refine ⟨isProbabilityMeasure_flowOf hF hTr hs, ?_⟩
    have hE := eLpNorm_flowOf hF hTr hs hp0
    have hlt : ∫ x in (0 : ℝ)..1, |Kop (H (s + -(Tr / 2))) x| ^ p * (7 * x ^ 6) < ε ^ p :=
      (henergy _ (shift_mem hs)).trans_le (min_le_left _ _)
    rw [← ENNReal.rpow_lt_rpow_iff (z := p) hp0, hE,
      ENNReal.ofReal_rpow_of_nonneg hε.le hp0.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hεp).2 hlt

/-- The Sobolev inequality (1.1) of the manuscript for the Fubini–Study metric
of `CP⁷`, with some constant. -/
def FubiniStudySobolev : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ HasSobolevBound (pot (fun _ => 0) 0) C₀

/-- **The geometric reduction with the Sobolev bound**: solutions of the
momentum equation as in `RadialMainP` give Theorem 1.1, the Sobolev constant
being `max (1, κ₂, 1 / κ₁)` times that of the Fubini–Study metric. -/
theorem mainTheorem_of_radialMainP {G : ℝ → ℝ} (hG : deriv G 0 < 0) (h : RadialMainP G)
    (hFS : FubiniStudySobolev) : MainTheorem := by
  obtain ⟨κ₁, κ₂, hκ₁, hmain⟩ := h
  obtain ⟨C₀, hC₀, hFS⟩ := hFS
  refine ⟨max 1 (max κ₂ κ₁⁻¹) * C₀, fun p hp2 hp7 ε hε τ hτ => ?_⟩
  have hp0 : 0 < p := by linarith
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hεr : 0 < min (ε ^ p) (κ₁ * ε / 2) := lt_min hεp (by positivity)
  obtain ⟨Tr, H, hTr, hTrτ, hflow, hpos, henergy, hmoment, htend⟩ :=
    hmain p hp2 hp7 _ hεr τ hτ
  have hF : Flow (Ioo (-Tr) 0) H :=
    ⟨isOpen_Ioo, ordConnected_Ioo, hflow.smooth,
      fun t ht x hx => lt_of_lt_of_le hκ₁ (hpos t ht x hx).1, hflow.eqn⟩
  have hΛ : ∀ t ∈ Ioo (-Tr) 0, ∀ x ∈ Icc (0 : ℝ) 1,
      1 + vstar x * H t x ≤ max 1 (max κ₂ κ₁⁻¹)
        ∧ (1 + vstar x * H t x)⁻¹ ≤ max 1 (max κ₂ κ₁⁻¹) := by
    intro t ht x hx
    obtain ⟨h1, h2⟩ := hpos t ht x hx
    refine ⟨h2.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
    exact (inv_anti₀ hκ₁ h1).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Tr / 2, flowOf H Tr, by positivity, by linarith, isCalabiFlow_flowOf hF hTr,
    fun s _ => isU7Invariant_flowOf H Tr s, fun v _ => ?_, fun s hs => ?_,
    ⟨-56 * deriv G 0, by nlinarith, tendsto_flowOf hF hTr htend⟩⟩
  · have h1 := abs_flowOf_zero_le hF hTr hκ₁ (fun x hx => (hpos _ (t0_mem hTr) x hx).1) v
    have h3 := (hmoment _ (t0_mem hTr)).trans_le (min_le_right _ _)
    have h4 : κ₁⁻¹ * ∫ s in (0 : ℝ)..1, s * |H (-(Tr / 2)) s| < κ₁⁻¹ * (κ₁ * ε / 2) :=
      mul_lt_mul_of_pos_left h3 (inv_pos.2 hκ₁)
    have h5 : κ₁⁻¹ * (κ₁ * ε / 2) = ε / 2 := by
      field_simp
    linarith
  · refine ⟨isProbabilityMeasure_flowOf hF hTr hs, ?_,
      hasSobolevBound_flowOf hF hTr hs (le_max_left _ _) hΛ hC₀ hFS⟩
    have hE := eLpNorm_flowOf hF hTr hs hp0
    have hlt : ∫ x in (0 : ℝ)..1, |Kop (H (s + -(Tr / 2))) x| ^ p * (7 * x ^ 6) < ε ^ p :=
      (henergy _ (shift_mem hs)).trans_le (min_le_left _ _)
    rw [← ENNReal.rpow_lt_rpow_iff (z := p) hp0, hE,
      ENNReal.ofReal_rpow_of_nonneg hε.le hp0.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hεp).2 hlt

/-- **Theorem 1.1 of the manuscript follows from the localized correction**
(Proposition 6.1) and the Sobolev inequality of the Fubini–Study metric. -/
theorem mainTheorem_of_correction {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G)
    (h : LocalizedCorrection G) (hFS : FubiniStudySobolev) : MainTheorem :=
  mainTheorem_of_radialMainP hP.deriv_neg (radialMainP_of_correction hP h) hFS

/-- **Theorem 1.1 without the Sobolev bound follows from the localized
correction**, Proposition 6.1 of the manuscript. -/
theorem mainTheoremCore_of_correction {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G)
    (h : LocalizedCorrection G) : MainTheoremCore :=
  mainTheoremCore_of_radialMainP hP.deriv_neg (radialMainP_of_correction hP h)

theorem mainTheoremEnergyCore_of_correction {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G)
    (h : LocalizedCorrection G) : MainTheoremEnergyCore :=
  (mainTheoremCore_of_correction hP h).energy

end Calabi.Geometry
