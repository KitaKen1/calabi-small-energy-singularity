import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered

open MeasureTheory Set Filter
open scoped Topology

namespace Calabi.Energy

theorem radial_volume_mass : (∫ x in (0 : ℝ)..1, 7 * x ^ 6) = 1 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem core_pointwise {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x) :
    x ^ 6 / (ρ + x) ^ 2 ≤ x ^ 4 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < ρ + x))).mpr
  have h : x ^ 2 ≤ (ρ + x) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg hx 4)
  nlinarith

/-- Uniform in the positive shrinking scale ρ. -/
theorem core_integral {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) :
    (∫ x in (0 : ℝ)..L, x ^ 6 / (ρ + x) ^ 2) ≤ L ^ 5 / 5 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 6 / (ρ + x) ^ 2) (Icc 0 L) := by
    apply (continuousOn_id.pow 6).div ((continuousOn_const.add continuousOn_id).pow 2)
    intro x hx
    change (ρ + x) ^ 2 ≠ 0
    exact ne_of_gt (sq_pos_of_pos (by linarith [hx.1]))
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hL
  have hm := intervalIntegral.integral_mono_on (μ := volume) hL hi
    ((continuous_pow 4).intervalIntegrable 0 L)
    (fun x hx => core_pointwise hρ hx.1)
  have h4 : (∫ x in (0 : ℝ)..L, x ^ 4) = L ^ 5 / 5 := by
    rw [integral_pow]
    norm_num
  exact hm.trans_eq h4

theorem weighted_pointwise {s A B e ρ x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hρ : 0 < ρ) (hx : 0 ≤ x)
    (hs : |s| ≤ A / (ρ + x) + B * e) :
    7 * x ^ 6 * s ^ 2 ≤ 14 * A ^ 2 * x ^ 4 + 14 * B ^ 2 * e ^ 2 * x ^ 6 := by
  have hd : 0 < ρ + x := by linarith
  have hab : 0 ≤ A / (ρ + x) + B * e := by positivity
  have hsq : |s| ^ 2 ≤ (A / (ρ + x) + B * e) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg s) hab).mpr hs
  have ht : s ^ 2 ≤ 2 * (A / (ρ + x)) ^ 2 + 2 * (B * e) ^ 2 := by
    nlinarith [sq_abs s, sq_nonneg (A / (ρ + x) - B * e)]
  calc
    _ ≤ 7 * x ^ 6 * (2 * (A / (ρ + x)) ^ 2 + 2 * (B * e) ^ 2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 14 * A ^ 2 * (x ^ 6 / (ρ + x) ^ 2) + 14 * B ^ 2 * e ^ 2 * x ^ 6 := by
      field_simp [ne_of_gt hd]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left (core_pointwise hρ hx)
        (show 0 ≤ 14 * A ^ 2 by positivity)
      linarith

/-- A scalar curvature deviation with a localized inverse-radius bound has
uniformly small energy. This lemma is independent of the geometric construction. -/
theorem radial_energy_bound {s : ℝ → ℝ} (hs : Continuous s)
    {A B e ρ L : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hL1 : L ≤ 1)
    (hinner : ∀ x ∈ Icc 0 L, |s x| ≤ A / (ρ + x) + B * e)
    (houter : ∀ x ∈ Icc L 1, |s x| ≤ B * e) :
    (∫ x in (0 : ℝ)..1, 7 * x ^ 6 * (s x) ^ 2) ≤
      (14 / 5) * A ^ 2 * L ^ 5 + 2 * B ^ 2 * e ^ 2 := by
  let f : ℝ → ℝ := fun x => 7 * x ^ 6 * (s x) ^ 2
  let base : ℝ → ℝ := fun x => 14 * B ^ 2 * e ^ 2 * x ^ 6
  let major : ℝ → ℝ := fun x => 14 * A ^ 2 * x ^ 4 + base x
  have hf : Continuous f := (continuous_const.mul (continuous_id.pow 6)).mul (hs.pow 2)
  have hb : Continuous base := continuous_const.mul (continuous_id.pow 6)
  have hm : Continuous major := (continuous_const.mul (continuous_id.pow 4)).add hb
  have hi := intervalIntegral.integral_mono_on (μ := volume) hL (hf.intervalIntegrable 0 L)
    (hm.intervalIntegrable 0 L) (fun x hx => weighted_pointwise hA hB he hρ hx.1 (hinner x hx))
  have ho := intervalIntegral.integral_mono_on (μ := volume) hL1 (hf.intervalIntegrable L 1)
    (hb.intervalIntegrable L 1) (fun x hx => by
      have h := weighted_pointwise (A := 0) (by norm_num) hB he hρ
        (hL.trans hx.1) (by simpa using houter x hx)
      simpa [f, base] using h)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 L) (hf.intervalIntegrable L 1)
  have heval : (∫ x in (0 : ℝ)..L, major x) + (∫ x in L..1, base x) =
      (14 / 5) * A ^ 2 * L ^ 5 + 2 * B ^ 2 * e ^ 2 := by
    have c4 : Continuous fun x : ℝ => 14 * A ^ 2 * x ^ 4 := by fun_prop
    have c6 : Continuous fun x : ℝ => 14 * B ^ 2 * e ^ 2 * x ^ 6 := by fun_prop
    have hadd : (∫ x in (0 : ℝ)..L, 14 * A ^ 2 * x ^ 4 + 14 * B ^ 2 * e ^ 2 * x ^ 6) =
        (∫ x in (0 : ℝ)..L, 14 * A ^ 2 * x ^ 4) +
          ∫ x in (0 : ℝ)..L, 14 * B ^ 2 * e ^ 2 * x ^ 6 :=
      intervalIntegral.integral_add (c4.intervalIntegrable 0 L) (c6.intervalIntegrable 0 L)
    have hadj : (∫ x in (0 : ℝ)..L, 14 * B ^ 2 * e ^ 2 * x ^ 6) +
        (∫ x in L..1, 14 * B ^ 2 * e ^ 2 * x ^ 6) =
        ∫ x in (0 : ℝ)..1, 14 * B ^ 2 * e ^ 2 * x ^ 6 :=
      intervalIntegral.integral_add_adjacent_intervals
        (c6.intervalIntegrable 0 L) (c6.intervalIntegrable L 1)
    have h4 : (∫ x in (0 : ℝ)..L, 14 * A ^ 2 * x ^ 4) = (14 / 5) * A ^ 2 * L ^ 5 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring1
    have h6 : (∫ x in (0 : ℝ)..1, 14 * B ^ 2 * e ^ 2 * x ^ 6) = 2 * B ^ 2 * e ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring1
    dsimp only [major, base]
    rw [hadd, add_assoc, hadj, h4, h6]
  change (∫ x in (0 : ℝ)..1, f x) ≤ _
  rw [← hsplit, ← heval]
  exact add_le_add hi ho

/-- A fixed rational relation e ≤ ℓ³ makes the energy majorant tend to zero. -/
theorem exists_small_scale (A B ε : ℝ) (hε : 0 < ε) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ 2 * ℓ ≤ 1 ∧
      (14 / 5) * A ^ 2 * (2 * ℓ) ^ 5 + 2 * B ^ 2 * (ℓ ^ 3) ^ 2 < ε := by
  let f : ℝ → ℝ := fun ℓ =>
    (14 / 5) * A ^ 2 * (2 * ℓ) ^ 5 + 2 * B ^ 2 * (ℓ ^ 3) ^ 2
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hc ε hε
  let ℓ := min (δ / 2) (1 / 4)
  have hℓ : 0 < ℓ := lt_min (by linarith) (by norm_num)
  have hℓδ : ℓ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hℓ1 : 2 * ℓ ≤ 1 := by have h := min_le_right (δ / 2) (1 / 4 : ℝ); linarith
  have hdist : dist ℓ 0 < δ := by simpa [Real.dist_eq, abs_of_pos hℓ] using hℓδ
  have hb := hsmall hdist
  have hf0 : f 0 = 0 := by dsimp [f]; ring
  rw [hf0, Real.dist_eq, sub_zero] at hb
  exact ⟨ℓ, hℓ, hℓ1, (le_abs_self _).trans_lt hb⟩

/-- Transfer of a Sobolev inequality once the unchanged mass term and the
Dirichlet-energy comparison have been established geometrically. -/
theorem sobolev_transfer {lhs mass dirichletRef dirichlet C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 1 ≤ Λ) (hmass : 0 ≤ mass)
    (hbase : lhs ≤ C * (dirichletRef + mass))
    (hdir : dirichletRef ≤ Λ * dirichlet) :
    lhs ≤ Λ * C * (dirichlet + mass) := by
  have hdir' := mul_le_mul_of_nonneg_left hdir hC
  have hmass' : mass ≤ Λ * mass := by nlinarith
  have hmassC := mul_le_mul_of_nonneg_left hmass' hC
  nlinarith

/-- Blow-up at a fixed point rules out a continuous extension of that scalar
curvature value; the geometric construction supplies the curvature identity. -/
theorem no_continuous_scalar_extension {T : ℝ} {curvature extension : ℝ → ℝ}
    (hT : 0 < T)
    (hblow : Tendsto curvature (𝓝[<] T) atTop)
    (hcont : ContinuousAt extension T)
    (hmatch : ∀ t ∈ Ico 0 T, extension t = curvature t) : False := by
  have hpos : ∀ᶠ t in 𝓝[<] T, 0 < t :=
    (eventually_gt_nhds hT).filter_mono inf_le_left
  have heq : extension =ᶠ[𝓝[<] T] curvature := by
    filter_upwards [self_mem_nhdsWithin, hpos] with t ht hp
    exact hmatch t ⟨hp.le, ht⟩
  have hc : Tendsto curvature (𝓝[<] T) (𝓝 (extension T)) :=
    (hcont.tendsto.mono_left inf_le_left).congr' heq
  exact not_tendsto_atTop_of_tendsto_nhds hc hblow

end Calabi.Energy
