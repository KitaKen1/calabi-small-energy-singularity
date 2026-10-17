import Calabi.Correction.OuterZeroBlock
import Calabi.Correction.OuterOne
import Calabi.Correction.PairSpace

/-!
# The outer part of the approximate inverse

The two outer blocks (`outer_chart0`, `outer_chart1`) are applied to the same
source `g`, which vanishes for `x ≤ θ`. Since their cut-offs `χ(4x)` and
`1 - χ(4x)` add up to one, the pair `U = (χ⁰ Z⁰, ψ¹ Z¹)` satisfies

  `P_λ U = g + err`,

with an error that is small in the two-chart norm when `T ≤ η θ²` and `η` is
small (`outer_pair`). The pair is bounded by the source, and its jets are small
in a smaller Hölder exponent (Lemma 4.5, (4.17)); this is used for the first
step of the iteration (Lemma 6.4).

`Sol T U` records the time derivatives and the radial symmetry of a pair.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

/-- The time derivatives and the radial symmetry of a pair. -/
structure Sol (T : ℝ) (U : Pair) : Prop where
  deriv0 : ∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => U.1 r z) (U.2.1 t z) t
  deriv1 : ∀ t ∈ Ioo (-T) 0, ∀ z, HasDerivAt (fun r => U.2.2.1 r z) (U.2.2.2 t z) t
  radial0 : ∀ t (Q : Flat18 ≃ₗᵢ[ℝ] Flat18) z, U.1 t (Q z) = U.1 t z
  radial1 : ∀ t (Q : Flat6 ≃ₗᵢ[ℝ] Flat6) z, U.2.2.1 t (Q z) = U.2.2.1 t z

theorem Sol.add {T : ℝ} {U U' : Pair} (h : Sol T U) (h' : Sol T U') : Sol T (U + U') where
  deriv0 t ht z := (h.deriv0 t ht z).add (h'.deriv0 t ht z)
  deriv1 t ht z := (h.deriv1 t ht z).add (h'.deriv1 t ht z)
  radial0 t Q z := by
    show U.1 t (Q z) + U'.1 t (Q z) = U.1 t z + U'.1 t z
    rw [h.radial0, h'.radial0]
  radial1 t Q z := by
    show U.2.2.1 t (Q z) + U'.2.2.1 t (Q z) = U.2.2.1 t z + U'.2.2.1 t z
    rw [h.radial1, h'.radial1]

theorem Sol.sub {T : ℝ} {U U' : Pair} (h : Sol T U) (h' : Sol T U') : Sol T (U - U') where
  deriv0 t ht z := (h.deriv0 t ht z).sub (h'.deriv0 t ht z)
  deriv1 t ht z := (h.deriv1 t ht z).sub (h'.deriv1 t ht z)
  radial0 t Q z := by
    show U.1 t (Q z) - U'.1 t (Q z) = U.1 t z - U'.1 t z
    rw [h.radial0, h'.radial0]
  radial1 t Q z := by
    show U.2.2.1 t (Q z) - U'.2.2.1 t (Q z) = U.2.2.1 t z - U'.2.2.1 t z
    rw [h.radial1, h'.radial1]

/-! ### Points of the two rays -/

theorem norm_sq_ray18 {x : ℝ} (hx : 0 ≤ x) : ‖Real.sqrt x • e18‖ ^ 2 = x := by
  rw [norm_smul, norm_e18, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    Real.sq_sqrt hx]

theorem norm_sq_ray6 {x : ℝ} (hx : 0 ≤ x) : ‖Real.sqrt x • e6‖ ^ 2 = x := by
  rw [norm_smul, norm_e6, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    Real.sq_sqrt hx]

/-- In the chart at `x = 1`, on a function that vanishes for `|w|² > 3/4`, the
coefficients of the linearized operator are trivial: `b_λ = 1` and `c_λ = 0`
for `x ≥ 1/4 > 2λ`. -/
theorem chart1_coef {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) {lam : ℝ} (hlam : 0 < lam)
    (hlam8 : lam < 1 / 8) {u : Flat6 → ℝ} (hu : ∀ z : Flat6, 3 / 4 < ‖z‖ ^ 2 → u z = 0) {t : ℝ}
    (ht : t < 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    blam G lam t x ^ 2 * (chartOp 18 u (Real.sqrt (1 - x) • e6) / 16)
        + clam G lam t x * u (Real.sqrt (1 - x) • e6)
      = chartOp 18 u (Real.sqrt (1 - x) • e6) / 16 := by
  rcases le_or_gt (1 / 4) x with h | h
  · rw [blam_of_ge hlam t (by linarith), clam_of_gt hP hlam ht hx (by linarith)]
    ring
  · have hw : (3 : ℝ) / 4 < ‖Real.sqrt (1 - x) • e6‖ ^ 2 := by
      rw [norm_sq_ray6 (by linarith [hx.2])]
      linarith
    have hopen : IsOpen {z : Flat6 | 3 / 4 < ‖z‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    have hev : u =ᶠ[𝓝 (Real.sqrt (1 - x) • e6)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hw] with z hz
      exact hu z hz
    rw [chartOp_eq_zero_of_eventually 18 hev, hu _ hw]
    ring

set_option maxHeartbeats 3200000 in
/-- **The outer part of the approximate inverse.** -/
theorem outer_pair {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) (α α₀ w lam : ℝ) (hα : 0 < α)
    (hα1 : α < 1) (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hlam : 0 < lam) (hlam8 : lam < 1 / 8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ 1 / 16 ∧
      ∀ (θ T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ lam / 8 → 0 < T → T ≤ η₁ * θ ^ 2 → 0 < F →
        B0 α T (w - 4) F g → (∀ t ∈ Ico (-T) 0, ∀ x, x ≤ θ → g t x = 0) →
        ∃ U : Pair, Reg U ∧ Sol T U ∧ XJ α T w (C * F) U ∧ XT α T w (C * F) U ∧
          XJ α₀ T w (C * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) U ∧
          B0 α T (w - 4) (ε * F)
            (fun t x => g t x - POf (blam G lam) (clam G lam) U t x) := by
  obtain ⟨Co, hCo, Ho⟩ := outer_chart0 hP α α₀ w lam hα hα1 hα₀ hα₀α hlam hlam8
  obtain ⟨C1, hC1, H1⟩ := outer_chart1 α w hα hα1
  obtain ⟨Kr0, hKr0, HR0⟩ := B0.ray0 α (w - 4) hα.le
  obtain ⟨Kr1, hKr1, HR1⟩ := B0.ray1 α (w - 4) hα.le
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = 1 + (1 : ℝ) ^ (|w| + ((4 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hCg : 0 ≤ Cg := by rw [hCgdef]; positivity
  have hCo0 : 0 ≤ Co := by linarith
  have hC10 : 0 ≤ C1 := by linarith
  refine ⟨Co + C1 * Cg + C1, by linarith [mul_nonneg hC10 hCg], fun ε hε => ?_⟩
  have hK01 : 0 < Kr0 + Kr1 := by linarith
  obtain ⟨η₁, hη₁, hη₁16, Ho⟩ := Ho (ε / (Kr0 + Kr1)) (div_pos hε hK01)
  obtain ⟨T₁, hT₁, H1⟩ := H1 (ε / (Kr0 + Kr1)) (div_pos hε hK01)
  refine ⟨min (min η₁ T₁) (1 / 64 ^ 4), lt_min (lt_min hη₁ hT₁) (by norm_num),
    ((min_le_left _ _).trans (min_le_left _ _)).trans hη₁16, ?_⟩
  intro θ T F g hθ hθlam hT hTη hF hg hg0
  -- the parameters
  have hθ1 : θ ≤ 1 := by linarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hθsq : θ ^ 2 ≤ 1 := pow_le_one₀ hθ.le hθ1
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hsθ1 : Real.sqrt θ ≤ 1 := by
    have h := Real.sqrt_le_sqrt hθ1
    rwa [Real.sqrt_one] at h
  have hTη₁ : T ≤ η₁ * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) hθ2.le)
  have hTT₁ : T ≤ T₁ := by
    have h1 := hTη.trans (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_right _ _)) hθ2.le)
    nlinarith
  have hT64 : T ≤ (1 / 64 * 1) ^ 4 := by
    have h1 := hTη.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hθ2.le)
    have e : ((1 : ℝ) / 64 * 1) ^ 4 = 1 / 64 ^ 4 := by norm_num
    rw [e]
    nlinarith
  have hT1 : T ≤ 1 := by
    have h1 : T ≤ 1 / 16 * θ ^ 2 := hTη₁.trans (mul_le_mul_of_nonneg_right hη₁16 hθ2.le)
    linarith
  -- the two blocks
  obtain ⟨uo, uot, erro, huo4, huo0, huot0, huoinit, huod, huorad, huoJ, huoT, huoG, herro,
    herro0, hido⟩ := Ho θ T F g hθ hθlam hT hTη₁ hF hg.1 hg0
  obtain ⟨u1, u1t, err1, hu14, hu10, hu1t0, hu1init, hu1d, hu1rad, hu1J, hu1T, herr1, herr10,
    hid1⟩ := H1 T F g hT hTT₁ hF hg.2
  have hρ0 : 0 ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) :=
    Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hT.le _) hsθ.le) _
  have hsub1 : dom1 T ⊆ {p : Flat6 × ℝ | p.2 ∈ Icc (-T) 0} := fun p hp => ⟨hp.1.1, hp.1.2.le⟩
  have hC1F : 0 ≤ C1 * F := by positivity
  have hCoF : 0 ≤ Co * F := by positivity
  have hCgC : 0 ≤ C1 * Cg := mul_nonneg hC10 hCg
  -- the gap in the chart at `x = 1`
  have hgap1 := hu1J.gap (s := fun _ : Flat6 => (1 : ℝ))
    (IsScale.const one_pos) hu1init hC1F hα₀ hα₀α hT one_pos (fun _ => le_rfl) (by norm_num)
    (by norm_num) hT64
  rw [← hCgdef] at hgap1
  have hbase : (T ^ ((1 : ℝ) / 4) / 1) ^ (α - α₀)
      ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hT.le _) hsθ hsθ1
  have hmonoC : ∀ k : ℝ, k ≤ Co + C1 * Cg + C1 → k * F ≤ (Co + C1 * Cg + C1) * F :=
    fun k hk => mul_le_mul_of_nonneg_right hk hF.le
  have hεK : 0 ≤ ε / (Kr0 + Kr1) * F := mul_nonneg (div_nonneg hε.le hK01.le) hF.le
  refine ⟨(uo, uot, u1, u1t), ⟨huo4, hu14, huo0, huot0, hu10, hu1t0⟩,
    ⟨huod, hu1d, huorad, hu1rad⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact huoJ.mono (isScale0 T).pos (hmonoC Co (by linarith))
  · exact (hu1J.restrict hsub1).mono (isScale1 T).pos (hmonoC C1 (by linarith))
  · exact huoT.mono (isScale0 T).pos (hmonoC Co (by linarith))
  · exact hu1T.mono (isScale1 T).pos (hmonoC C1 (by linarith))
  · refine huoG.mono (isScale0 T).pos ?_
    have h1 : Co ≤ Co + C1 * Cg + C1 := by linarith
    have h2 : 0 ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := mul_nonneg hρ0 hF.le
    calc Co * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F
        = Co * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) := by ring
      _ ≤ (Co + C1 * Cg + C1) * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) :=
        mul_le_mul_of_nonneg_right h1 h2
      _ = (Co + C1 * Cg + C1) * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := by ring
  · refine (hgap1.restrict hsub1).mono (isScale1 T).pos ?_
    have h1 : Cg * (T ^ ((1 : ℝ) / 4) / 1) ^ (α - α₀) * (C1 * F)
        ≤ Cg * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * (C1 * F) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hCg) hC1F
    have h2 : C1 * Cg ≤ Co + C1 * Cg + C1 := by linarith
    have h3 : 0 ≤ (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := mul_nonneg hρ0 hF.le
    calc Cg * (T ^ ((1 : ℝ) / 4) / 1) ^ (α - α₀) * (C1 * F)
        ≤ Cg * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * (C1 * F) := h1
      _ = C1 * Cg * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) := by ring
      _ ≤ (Co + C1 * Cg + C1) * ((T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F) :=
        mul_le_mul_of_nonneg_right h2 h3
      _ = (Co + C1 * Cg + C1) * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α - α₀) * F := by ring
  · -- the error
    have he0 := HR0 T _ erro hT1 hεK herro herro0
    have he1 := HR1 T _ err1 hT1 hεK herr1 herr10
    refine (((he0.add he1).neg).congr fun t ht x hx => ?_).mono (le_of_eq ?_)
    · have hz : ‖Real.sqrt x • e18‖ ^ 2 = x := norm_sq_ray18 hx.1
      have hw : ‖Real.sqrt (1 - x) • e6‖ ^ 2 = 1 - x := norm_sq_ray6 (by linarith [hx.2])
      have ho := hido t ht (Real.sqrt x • e18)
      rw [hz] at ho
      have h1 := hid1 t ht (Real.sqrt (1 - x) • e6)
      rw [hw, sub_sub_cancel] at h1
      have hc1 := chart1_coef hP hlam hlam8 (u := u1 t) (hu10 t) ht.2 hx
      show g t x - (uot t (Real.sqrt x • e18) + u1t t (Real.sqrt (1 - x) • e6)
          + blam G lam t x ^ 2 * (chartOp 6 (uo t) (Real.sqrt x • e18) / 16
            + chartOp 18 (u1 t) (Real.sqrt (1 - x) • e6) / 16)
          + clam G lam t x * (uo t (Real.sqrt x • e18) + u1 t (Real.sqrt (1 - x) • e6)))
        = -(erro (Real.sqrt x • e18, t) + err1 (Real.sqrt (1 - x) • e6, t))
      linear_combination (-1 : ℝ) * ho - h1 - hc1
    · rw [← add_mul, ← mul_assoc, mul_div_cancel₀ ε hK01.ne']

end Calabi.Weighted
