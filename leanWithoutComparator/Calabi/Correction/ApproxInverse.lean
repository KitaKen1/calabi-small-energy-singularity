import Calabi.Correction.InnerBlock
import Calabi.Correction.OuterPair

/-!
# The approximate right inverse of the linearized operator

Lemma 6.3 of the manuscript in the form used by the iteration of `Newton.lean`:
for a source `g` with the two-chart bound `F` of weight `w - 4`, there is a
pair `U` with

  `‖U‖_X ≤ C_S F`,   `‖g - P_λ U‖_Y ≤ F / 2`,

where `C_S` does not depend on the inner radius `θ ≤ θ₀` or on the time
`T ≤ η₀ θ²` (`approx_inverse`). The exponent `γ` of the weight `w = -2 + 4γ`
depends on the profile only.

The pair is the sum of the inner part `χ_b W` (`inner_pair`, from the inner
block) and of the outer part (`outer_pair`) applied to the source
`g_o = g - χ_i g - J`, where `J` is the commutator of the inner part. The
commutator cancels exactly, and the remaining errors are the mismatch of the
inner block, of size `√θ`, and the errors of the outer blocks, which are small
for small `η₀`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

set_option maxHeartbeats 3200000 in
/-- **The inner part of the approximate inverse** as a pair, with the source of
the outer part. -/
theorem inner_pair {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∀ lam : ℝ, 0 < lam → lam < 1 / 8 → ∀ α : ℝ, 0 < α → α < 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (θ T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ lam / 8 → 0 < T →
        T ≤ (θ / 4) ^ 2 → 0 ≤ F → B0 α T (-2 + 4 * γ - 4) F g →
        ∃ (U : Pair) (go : ℝ → ℝ → ℝ), Reg U ∧ Sol T U ∧ XJ α T (-2 + 4 * γ) (C * F) U ∧
          XT α T (-2 + 4 * γ) (C * F) U ∧ B0 α T (-2 + 4 * γ - 4) (C * F) go ∧
          (∀ t ∈ Ico (-T) 0, ∀ x, x ≤ θ → go t x = 0) ∧
          B0 α T (-2 + 4 * γ - 4) (C * Real.sqrt θ * F)
            (fun t x => g t x - POf (blam G lam) (clam G lam) U t x - go t x) := by
  obtain ⟨γ, hγ, hγ1, Hin⟩ := inner_block hP
  refine ⟨γ, hγ, hγ1, fun lam hlam hlam8 α hα hα1 => ?_⟩
  obtain ⟨Ci, hCi, Hi⟩ := Hin lam hlam hlam8 α hα hα1
  obtain ⟨Kr0, hKr0, HR0⟩ := B0.ray0 α (-2 + 4 * γ - 4) hα.le
  obtain ⟨Aχ, hAχ, HAχ⟩ := WJ_chiV_sigma (V := Flat18)
  have hCi0 : 0 ≤ Ci := by linarith
  have hKr00 : 0 ≤ Kr0 := by linarith
  obtain ⟨Cgo, hCgodef⟩ : ∃ Cgo : ℝ,
      Cgo = 1 + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Aχ + Kr0 * Ci := ⟨_, rfl⟩
  have hCgo : 0 ≤ Cgo := by rw [hCgodef]; positivity
  refine ⟨Ci + Cgo + Kr0 * Ci, by nlinarith [mul_nonneg hKr00 hCi0], ?_⟩
  intro θ T F g hθ hθlam hT hTθ hF hg
  have hθ4 : θ ≤ 1 / 4 := by linarith
  have hθsq : θ ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hθ.le hθ4 2
    norm_num at this
    linarith
  have hT1 : T ≤ 1 := by nlinarith
  have hsub : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} := fun p hp => hp.1
  have hCtot : ∀ k : ℝ, k ≤ Ci + Cgo + Kr0 * Ci → k * F ≤ (Ci + Cgo + Kr0 * Ci) * F :=
    fun k hk => mul_le_mul_of_nonneg_right hk hF
  have hKC : 0 ≤ Kr0 * Ci := mul_nonneg hKr00 hCi0
  obtain ⟨ui, uit, J, erri, hui4, hui0, huit0, huid, huirad, huiJ, huiT, hJ, hJ0, herri,
    herri0, hidi⟩ := Hi θ T F g hθ hθlam hT hTθ hF hg.1
  -- the source of the outer part
  have hχg : B0 α T (-2 + 4 * γ - 4) ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * Aχ * F)
      (fun t x => chi (x / θ) * g t x) := by
    constructor
    · have h := WH.mul (isScale0 T) hAχ hF
        (HAχ α θ θ T (dom0 T) hθ le_rfl hTθ hsub hα.le hα1.le).value hg.1
      rw [zero_add] at h
      exact h
    · refine (WH.zero (by positivity) (isScale1 T).pos).congr fun p hp => ?_
      have h2 : 2 ≤ (1 - ‖p.1‖ ^ 2) / θ := by
        rw [le_div_iff₀ hθ]
        linarith [hp.2]
      show chi ((1 - ‖p.1‖ ^ 2) / θ) * g p.2 (1 - ‖p.1‖ ^ 2) = 0
      rw [chi_of_ge h2, zero_mul]
  have hJr := HR0 T (Ci * F) J hT1 (by positivity) hJ
    (fun p hp => hJ0 p (Or.inr (by linarith)))
  have hgo := (hg.sub hχg).sub hJr
  have herr := HR0 T (Ci * Real.sqrt θ * F) erri hT1 (by positivity) herri
    (fun p hp => herri0 p (by linarith))
  refine ⟨(ui, uit, 0, 0), fun t x => g t x - chi (x / θ) * g t x - ray0 J t x,
    ⟨hui4, fun _ => contDiff_const, fun t z hz => hui0 t z (by linarith),
      fun t z hz => huit0 t z (by linarith), fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    ⟨fun t ht z => huid t ht.2 z, fun t _ z => hasDerivAt_const t _, huirad,
      fun _ _ _ => rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact huiJ.mono (isScale0 T).pos (hCtot Ci (by linarith))
  · exact ((XJ.zero α T (-2 + 4 * γ)).2).mono (isScale1 T).pos (by positivity)
  · exact huiT.mono (isScale0 T).pos (hCtot Ci (by linarith))
  · refine (WH.zero (by positivity) (isScale1 T).pos).congr fun p _ => rfl
  · refine hgo.mono ?_
    have e : F + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * Aχ * F + Kr0 * (Ci * F) = Cgo * F := by
      rw [hCgodef]
      ring
    rw [e]
    exact hCtot Cgo (by linarith)
  · intro t ht x hx
    have h1 : chi (x / θ) = 1 := chi_of_le ((div_le_one hθ).2 hx)
    have h2 : ray0 J t x = 0 := by
      show J (Real.sqrt x • e18, t) = 0
      refine hJ0 _ (Or.inl ?_)
      show ‖Real.sqrt x • e18‖ ^ 2 < 2 * θ
      rcases le_or_gt 0 x with h | h
      · rw [norm_sq_ray18 h]
        linarith
      · rw [Real.sqrt_eq_zero_of_nonpos h.le, zero_smul, norm_zero]
        nlinarith
    show g t x - chi (x / θ) * g t x - ray0 J t x = 0
    rw [h1, h2]
    ring
  · refine (herr.neg.congr fun t ht x hx => ?_).mono ?_
    · have hz : ‖Real.sqrt x • e18‖ ^ 2 = x := norm_sq_ray18 hx.1
      have hi := hidi t ht (Real.sqrt x • e18)
      rw [hz] at hi
      have hχ : chiV θ (Real.sqrt x • e18) = chi (x / θ) := by
        unfold chiV
        rw [hz]
      rw [hχ] at hi
      have h0 : chartOp 18 ((0 : ℝ → Flat6 → ℝ) t) (Real.sqrt (1 - x) • e6) = 0 :=
        chartOp_zero_fun 18 _
      show g t x - (uit t (Real.sqrt x • e18) + (0 : ℝ → Flat6 → ℝ) t (Real.sqrt (1 - x) • e6)
          + blam G lam t x ^ 2 * (chartOp 6 (ui t) (Real.sqrt x • e18) / 16
            + chartOp 18 ((0 : ℝ → Flat6 → ℝ) t) (Real.sqrt (1 - x) • e6) / 16)
          + clam G lam t x * (ui t (Real.sqrt x • e18)
            + (0 : ℝ → Flat6 → ℝ) t (Real.sqrt (1 - x) • e6)))
          - (g t x - chi (x / θ) * g t x - J (Real.sqrt x • e18, t))
        = -erri (Real.sqrt x • e18, t)
      rw [h0]
      have h00 : (0 : ℝ → Flat6 → ℝ) t (Real.sqrt (1 - x) • e6) = 0 := rfl
      rw [h00]
      linear_combination (-1 : ℝ) * hi
    · have h1 : Kr0 * (Ci * Real.sqrt θ * F) = Kr0 * Ci * (Real.sqrt θ * F) := by ring
      rw [h1]
      have h2 : Kr0 * Ci ≤ Ci + Cgo + Kr0 * Ci := by linarith
      have h3 : 0 ≤ Real.sqrt θ * F := mul_nonneg (Real.sqrt_nonneg θ) hF
      calc Kr0 * Ci * (Real.sqrt θ * F) ≤ (Ci + Cgo + Kr0 * Ci) * (Real.sqrt θ * F) :=
            mul_le_mul_of_nonneg_right h2 h3
        _ = (Ci + Cgo + Kr0 * Ci) * Real.sqrt θ * F := by ring

set_option maxHeartbeats 3200000 in
/-- **The approximate right inverse of the linearized operator**
(Lemma 6.3 of the manuscript). -/
theorem approx_inverse {c : ℝ} {G : ℝ → ℝ} (hP : IsProfile c G) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ ∀ lam : ℝ, 0 < lam → lam < 1 / 8 → ∀ α : ℝ, 0 < α → α < 1 →
      ∃ CS : ℝ, 1 ≤ CS ∧ ∃ θ₀ : ℝ, 0 < θ₀ ∧ θ₀ ≤ lam / 8 ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 16 ∧
        ∀ (θ T F : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ θ₀ → 0 < T → T ≤ η₀ * θ ^ 2 → 0 < F →
          B0 α T (-2 + 4 * γ - 4) F g →
          ∃ U : Pair, Reg U ∧ Sol T U ∧ XJ α T (-2 + 4 * γ) (CS * F) U ∧
            XT α T (-2 + 4 * γ) (CS * F) U ∧
            B0 α T (-2 + 4 * γ - 4) (F / 2)
              (fun t x => g t x - POf (blam G lam) (clam G lam) U t x) := by
  obtain ⟨γ, hγ, hγ1, Hin⟩ := inner_pair hP
  refine ⟨γ, hγ, hγ1, fun lam hlam hlam8 α hα hα1 => ?_⟩
  obtain ⟨Ci, hCi, Hi⟩ := Hin lam hlam hlam8 α hα hα1
  obtain ⟨Co, hCo, Ho⟩ := outer_pair hP α α (-2 + 4 * γ) lam hα hα1 hα le_rfl hlam hlam8
  have hCi0 : 0 < Ci := by linarith
  have hCine : Ci ≠ 0 := hCi0.ne'
  have hCo0 : 0 ≤ Co := by linarith
  obtain ⟨η₁, hη₁, hη₁16, Ho⟩ := Ho (1 / (4 * Ci)) (by positivity)
  have hθ₀ : 0 < min (lam / 8) ((1 / (4 * Ci)) ^ 2) := lt_min (by positivity) (by positivity)
  refine ⟨Ci + Co * Ci, by nlinarith [mul_nonneg hCo0 hCi0.le],
    min (lam / 8) ((1 / (4 * Ci)) ^ 2), hθ₀, min_le_left _ _, η₁, hη₁, hη₁16, ?_⟩
  intro θ T F g hθ hθ₀' hT hTη hF hg
  have hθlam : θ ≤ lam / 8 := hθ₀'.trans (min_le_left _ _)
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hTθ : T ≤ (θ / 4) ^ 2 := by
    have h1 : T ≤ 1 / 16 * θ ^ 2 := hTη.trans (mul_le_mul_of_nonneg_right hη₁16 hθ2.le)
    have e : (θ / 4) ^ 2 = 1 / 16 * θ ^ 2 := by ring
    rw [e]
    exact h1
  have hsθ : Real.sqrt θ ≤ 1 / (4 * Ci) := by
    have h1 := Real.sqrt_le_sqrt (hθ₀'.trans (min_le_right _ _))
    rwa [Real.sqrt_sq (by positivity)] at h1
  obtain ⟨Ui, go, hUiR, hUiS, hUiJ, hUiT, hgo, hgo0, herri⟩ := Hi θ T F g hθ hθlam hT hTθ hF.le
    hg
  obtain ⟨Uo, hUoR, hUoS, hUoJ, hUoT, -, herro⟩ := Ho θ T (Ci * F) go hθ hθlam hT hTη
    (by positivity) hgo hgo0
  refine ⟨Ui + Uo, hUiR.add hUoR, hUiS.add hUoS, ?_, ?_, ?_⟩
  · refine (XJ.add hUiR hUoR hUiJ hUoJ).mono (le_of_eq ?_)
    ring
  · refine (hUiT.add hUoT).mono (le_of_eq ?_)
    ring
  · refine ((herri.add herro).congr fun t ht x hx => ?_).mono ?_
    · show g t x - POf (blam G lam) (clam G lam) (Ui + Uo) t x
        = g t x - POf (blam G lam) (clam G lam) Ui t x - go t x
          + (go t x - POf (blam G lam) (clam G lam) Uo t x)
      rw [POf_add _ _ hUiR hUoR]
      show g t x - (POf (blam G lam) (clam G lam) Ui t x + POf (blam G lam) (clam G lam) Uo t x)
        = _
      ring
    · have h1 : Ci * Real.sqrt θ ≤ 1 / 4 := by
        have h2 := mul_le_mul_of_nonneg_left hsθ hCi0.le
        have e : Ci * (1 / (4 * Ci)) = 1 / 4 := by
          field_simp
        linarith
      have h3 : 1 / (4 * Ci) * (Ci * F) = F / 4 := by
        field_simp
      have h4 := mul_le_mul_of_nonneg_right h1 hF.le
      linarith

end Calabi.Weighted
