import Calabi.Correction.ApproxInverse

/-!
# The first step of the iteration (Lemma 6.4 of the manuscript)

The residual `E_λ` of the localized profile is not small in the source norm.
Lemma 6.4 produces an approximate solution `U₁` of `P_λ U₁ = -E_λ` that is
nevertheless small in the norm `X′` of the jets:

* near the point orbit, `f_c = χ(x/(2θ)) E_λ` is small in the source norm,
  because there the residual has the weight `-4` instead of `w - 4` and the
  scale is at most `3√θ` (`fc_bound`); the approximate inverse of Lemma 6.3 is
  applied to it;
* away from the point orbit, `f_e = (1 - χ(x/(2θ))) E_λ` is bounded in the
  source norm of a larger Hölder exponent `α′`, and the outer part of the
  approximate inverse applied to it is small in the jet norm of exponent `α`
  on a short time interval (Lemma 4.5, (4.17)).

`first_step` is the resulting statement: for every `e` and `ϵ` there is a pair
with `‖U₁‖_{X′} ≤ e` and `‖-E_λ - P_λ U₁‖_Y ≤ ϵ`, for all sufficiently small
`θ` and `T ≤ η θ²`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

/-! ### Lowering the Hölder exponent -/

section Exponent

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E]

/-- A two-point bound of exponent `α'` is a two-point bound of every smaller
exponent. -/
theorem WH.exp_le {α α' a w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : WH α' a s Ω w M f) (hs : ∀ p ∈ Ω, 0 < s p) (hM : 0 ≤ M) (ha : a ≤ 1) (hα : 0 ≤ α)
    (hαα : α ≤ α') : WH α a s Ω w M f := by
  refine ⟨hf.1, fun p hp q hq hd => (hf.2 p hp q hq hd).trans ?_⟩
  have hsp := hs p hp
  have hds : pdist p q ≤ s p := hd.trans (mul_le_of_le_one_left hsp.le ha)
  have h := scale_interp (w := w) hsp (pdist_nonneg p q) hds hα hαα
  calc M * s p ^ (w - α') * pdist p q ^ α' = M * (s p ^ (w - α') * pdist p q ^ α') := by ring
    _ ≤ M * (s p ^ (w - α) * pdist p q ^ α) := mul_le_mul_of_nonneg_left h hM
    _ = M * s p ^ (w - α) * pdist p q ^ α := by ring

/-- A constant function has a two-point bound of weight zero. -/
theorem WH.const_fun {α a : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)} (hs : ∀ p ∈ Ω, 0 < s p)
    (c₀ : ℝ) : WH α a s Ω 0 |c₀| (fun _ => c₀) := by
  refine ⟨fun p _ => ?_, fun p hp q _ _ => ?_⟩
  · rw [Real.rpow_zero, mul_one, Real.norm_eq_abs]
  · rw [sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hs p hp).le _))
      (Real.rpow_nonneg (pdist_nonneg p q) _)

end Exponent

theorem B0.exp_le {α α' T v M : ℝ} {g : ℝ → ℝ → ℝ} (h : B0 α' T v M g) (hM : 0 ≤ M)
    (hα : 0 ≤ α) (hαα : α ≤ α') : B0 α T v M g :=
  ⟨h.1.exp_le (isScale0 T).pos hM (by norm_num) hα hαα,
    h.2.exp_le (isScale1 T).pos hM (by norm_num) hα hαα⟩

theorem XJ.exp_le {α α' T w a : ℝ} {U : Pair} (h : XJ α' T w a U) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hαα : α ≤ α') : XJ α T w a U :=
  ⟨fun j hj => (h.1 j hj).exp_le (isScale0 T).pos ha (by norm_num) hα hαα,
    fun j hj => (h.2 j hj).exp_le (isScale1 T).pos ha (by norm_num) hα hαα⟩

theorem XT.exp_le {α α' T w a : ℝ} {U : Pair} (h : XT α' T w a U) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hαα : α ≤ α') : XT α T w a U :=
  ⟨h.1.exp_le (isScale0 T).pos ha (by norm_num) hα hαα,
    h.2.exp_le (isScale1 T).pos ha (by norm_num) hα hαα⟩

/-- On `|z|² ≤ 4θ` the scale `σ` is at most `3√θ`, for `T ≤ (θ/4)²`. -/
theorem sigma_le_three_sqrt {θ T : ℝ} {p : Flat18 × ℝ} (hθ : 0 < θ) (hT : T ≤ (θ / 4) ^ 2)
    (hp : p.2 ∈ Ico (-T) 0) (hz : ‖p.1‖ ^ 2 ≤ 4 * θ) : sigma p ≤ 3 * Real.sqrt θ := by
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have h1 := sigma_le_norm_add hθ hT hp
  have h2 : ‖p.1‖ ≤ 2 * Real.sqrt θ := by
    have h3 : ‖p.1‖ ^ 2 ≤ (2 * Real.sqrt θ) ^ 2 := by
      rw [mul_pow, hsq]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  linarith [Real.sqrt_nonneg θ]


/-- A positive power is small on a small interval. -/
theorem exists_rpow_small {p : ℝ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ x₀ → x ^ p ≤ ε := by
  refine ⟨ε ^ p⁻¹, Real.rpow_pos_of_pos hε _, fun x hx hxx => ?_⟩
  calc x ^ p ≤ (ε ^ p⁻¹) ^ p := Real.rpow_le_rpow hx hxx hp.le
    _ = ε := Real.rpow_inv_rpow hε.le hp.ne'

/-- `T^{1/4} / √θ ≤ η^{1/4}` for `T ≤ η θ²`. -/
theorem quarter_div_sqrt_le {T θ η : ℝ} (hT : 0 ≤ T) (hθ : 0 < θ) (hη : 0 ≤ η)
    (hTη : T ≤ η * θ ^ 2) : T ^ ((1 : ℝ) / 4) / Real.sqrt θ ≤ η ^ ((1 : ℝ) / 4) := by
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hq : 0 ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hη _
  rw [div_le_iff₀ hsθ]
  have h4 : (η ^ ((1 : ℝ) / 4) * Real.sqrt θ) ^ 4 = η * θ ^ 2 := by
    have e1 : (η ^ ((1 : ℝ) / 4)) ^ 4 = η := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
      norm_num
    have e2 : Real.sqrt θ ^ 4 = θ ^ 2 := by
      have := Real.sq_sqrt hθ.le
      calc Real.sqrt θ ^ 4 = (Real.sqrt θ ^ 2) ^ 2 := by ring
        _ = θ ^ 2 := by rw [this]
    rw [mul_pow, e1, e2]
  calc T ^ ((1 : ℝ) / 4) ≤ ((η ^ ((1 : ℝ) / 4) * Real.sqrt θ) ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hT (by rw [h4]; exact hTη) (by norm_num)
    _ = η ^ ((1 : ℝ) / 4) * Real.sqrt θ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg hq hsθ.le)]
        norm_num

/-! ### The inner cut-off in the two charts -/

/-- Multiplication by the inner cut-off `χ(x/μ)`, `θ ≤ μ ≤ 1/32`, of a quantity
of order zero. -/
theorem B0.chi_mul : ∃ A : ℝ, 0 ≤ A ∧ ∀ (α θ μ T v M : ℝ) (g : ℝ → ℝ → ℝ), 0 < θ → θ ≤ μ →
    μ ≤ 1 / 32 → T ≤ (θ / 4) ^ 2 → 0 ≤ α → α ≤ 1 → 0 ≤ M → B0 α T v M g →
    B0 α T v ((1 + (2 : ℝ) ^ |(0 : ℝ)|) * A * M) (fun t x => chi (x / μ) * g t x) := by
  obtain ⟨A, hA, HA⟩ := WJ_chiV_sigma (V := Flat18)
  refine ⟨A, hA, fun α θ μ T v M g hθ hθμ hμ hT hα hα1 hM hg => ⟨?_, ?_⟩⟩
  · have hsub : dom0 T ⊆ {p : Flat18 × ℝ | p.2 ∈ Ico (-T) 0} := fun p hp => hp.1
    have h := WH.mul (isScale0 T) hA hM (HA α θ μ T (dom0 T) hθ hθμ hT hsub hα hα1).value hg.1
    rw [zero_add] at h
    exact h
  · have hμ0 : 0 < μ := hθ.trans_le hθμ
    refine (WH.zero (by positivity) (isScale1 T).pos).congr fun p hp => ?_
    have h2 : 2 ≤ (1 - ‖p.1‖ ^ 2) / μ := by
      rw [le_div_iff₀ hμ0]
      linarith [hp.2]
    show chi ((1 - ‖p.1‖ ^ 2) / μ) * g p.2 (1 - ‖p.1‖ ^ 2) = 0
    rw [chi_of_ge h2, zero_mul]

variable {c : ℝ} {G : ℝ → ℝ}

/-- **The residual near the point orbit is small in the source norm**: there it
has the weight `-4` instead of `w - 4`, on a region where the scale is at most
`3√θ`. -/
theorem fc_bound (hP : IsProfile c G) (γ α : ℝ) (hγ : γ ≤ 1 / 2) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam θ T : ℝ), 0 < lam → lam < 1 / 8 → 0 < θ → θ ≤ lam / 8 →
      T ≤ (θ / 4) ^ 2 →
      B0 α T (-2 + 4 * γ - 4) (K * Real.sqrt θ ^ (2 - 4 * γ))
        (fun t x => chi (x / (2 * θ)) * Elam G lam t x) := by
  obtain ⟨Ke, hKe, HE⟩ := ein_bound hP α hα hα1
  obtain ⟨A, hA, HA⟩ := B0.chi_mul
  have h6 : 0 ≤ (6 : ℝ) ^ (2 - 4 * γ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(1 + (2 : ℝ) ^ |(0 : ℝ)|) * A * Ke * 6 ^ (2 - 4 * γ), by positivity, ?_⟩
  intro lam θ T hlam hlam8 hθ hθlam hT
  have hsθ : 0 ≤ Real.sqrt θ := Real.sqrt_nonneg θ
  have hθ64 : θ ≤ 1 / 64 := by linarith
  have hT1 : T ≤ 1 := by nlinarith
  have hM₁ : 0 ≤ (1 + (2 : ℝ) ^ |(0 : ℝ)|) * A * Ke := by positivity
  have h1 := HA α θ (2 * θ) T (-4) Ke (Ein G) hθ (by linarith) (by linarith) hT hα hα1 hKe
    (HE T hT1)
  have hrp : 0 ≤ Real.sqrt θ ^ (2 - 4 * γ) := Real.rpow_nonneg hsθ _
  constructor
  · have hS : ∀ p ∈ dom0 T, chi (‖p.1‖ ^ 2 / (2 * θ)) * Ein G p.2 (‖p.1‖ ^ 2) ≠ 0 →
        sigma p ≤ 3 * Real.sqrt θ := by
      intro p hp hne
      have hlt : ‖p.1‖ ^ 2 / (2 * θ) < 2 := by
        by_contra hcon
        exact hne (by rw [chi_of_ge (not_lt.1 hcon), zero_mul])
      have hz : ‖p.1‖ ^ 2 ≤ 4 * θ := by
        rw [div_lt_iff₀ (by positivity)] at hlt
        linarith
      exact sigma_le_three_sqrt hθ hT hp.1 hz
    have h2 := h1.1.weight_supp (isScale0 T) hM₁ (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt θ)
      hS (by linarith : (-2 + 4 * γ - 4 : ℝ) ≤ -4)
    have e : (-4 : ℝ) - (-2 + 4 * γ - 4) = 2 - 4 * γ := by ring
    have e6 : (2 * (3 * Real.sqrt θ)) ^ (2 - 4 * γ)
        = 6 ^ (2 - 4 * γ) * Real.sqrt θ ^ (2 - 4 * γ) := by
      rw [← Real.mul_rpow (by norm_num) hsθ]
      congr 1
      ring
    rw [e, e6] at h2
    refine (h2.congr fun p hp => ?_).mono (isScale0 T).pos (le_of_eq ?_)
    · show chi (‖p.1‖ ^ 2 / (2 * θ)) * Elam G lam p.2 (‖p.1‖ ^ 2)
        = chi (‖p.1‖ ^ 2 / (2 * θ)) * Ein G p.2 (‖p.1‖ ^ 2)
      rcases lt_or_ge (‖p.1‖ ^ 2) lam with h | h
      · rw [Elam_eq_Ein hP hlam hp.1.2 ⟨sq_nonneg _, by linarith [hp.2]⟩ h]
      · have h2 : 2 ≤ ‖p.1‖ ^ 2 / (2 * θ) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        rw [chi_of_ge h2, zero_mul, zero_mul]
    · ring
  · refine (WH.zero (by positivity) (isScale1 T).pos).congr fun p hp => ?_
    have h2 : 2 ≤ (1 - ‖p.1‖ ^ 2) / (2 * θ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hp.2]
    show chi ((1 - ‖p.1‖ ^ 2) / (2 * θ)) * Elam G lam p.2 (1 - ‖p.1‖ ^ 2) = 0
    rw [chi_of_ge h2, zero_mul]

set_option maxHeartbeats 1600000 in
/-- **The first step of the iteration** (in place of Lemma 6.4 of the
manuscript): a pair that is small in the jet norm and whose linear residual
`-E_λ - P_λ U` is small in the source norm. It is the outer part of the
approximate inverse applied to the residual away from the point orbit; the
residual near the point orbit is small by `fc_bound`. -/
theorem first_step (hP : IsProfile c G) (γ lam α α' : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1 / 2)
    (hlam : 0 < lam) (hlam8 : lam < 1 / 8) (hα : 0 < α) (hαα : α < α') (hα1 : α' < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∃ θ₁ : ℝ, 0 < θ₁ ∧ θ₁ ≤ lam / 8 ∧
      ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ 1 / 16 ∧ ∀ θ T : ℝ, 0 < θ → θ ≤ θ₁ → 0 < T → T ≤ η₁ * θ ^ 2 →
        ∃ U : Pair, Reg U ∧ Sol T U ∧ XJ α T (-2 + 4 * γ) ε U ∧ XT α T (-2 + 4 * γ) M U ∧
          B0 α T (-2 + 4 * γ - 4) ε
            (fun t x => -Elam G lam t x - POf (blam G lam) (clam G lam) U t x) := by
  have hα' : 0 < α' := hα.trans hαα
  obtain ⟨Ke, hKe, HE⟩ := elam_bound hP α' hα'.le hα1.le
  obtain ⟨A, hA, HA⟩ := B0.chi_mul
  obtain ⟨Co, hCo, Ho⟩ := outer_pair hP α' α (-2 + 4 * γ) lam hα' hα1 hα hαα.le hlam hlam8
  obtain ⟨Kc, hKc, HKc⟩ := fc_bound hP γ α hγ1.le hα.le (hαα.le.trans hα1.le)
  have hKl : 0 ≤ Ke / lam := div_nonneg hKe hlam.le
  have h2p : 0 ≤ (2 : ℝ) ^ (-4 - (-2 + 4 * γ - 4)) := Real.rpow_nonneg (by norm_num) _
  obtain ⟨Fe, hFedef⟩ : ∃ Fe : ℝ, Fe = (Ke / lam + (1 + (2 : ℝ) ^ |(0 : ℝ)|) * A * (Ke / lam))
      * 2 ^ (-4 - (-2 + 4 * γ - 4)) + 1 := ⟨_, rfl⟩
  have hFe : 0 < Fe := by
    rw [hFedef]
    positivity
  have hCo0 : 0 < Co := by linarith
  refine ⟨Co * Fe, by positivity, fun ε hε => ?_⟩
  have hp : 0 < 2 - 4 * γ := by linarith
  obtain ⟨x₀, hx₀, Hx₀⟩ := exists_rpow_small hp (show 0 < ε / (2 * (Kc + 1)) by positivity)
  obtain ⟨η₁, hη₁, hη₁16, Ho⟩ := Ho (ε / (2 * Fe)) (by positivity)
  have hd : 0 < α' - α := by linarith
  obtain ⟨y₀, hy₀, Hy₀⟩ := exists_rpow_small hd (show 0 < ε / (Co * Fe) by positivity)
  refine ⟨min (lam / 8) (x₀ ^ 2), lt_min (by positivity) (by positivity), min_le_left _ _,
    min η₁ (y₀ ^ 4), lt_min hη₁ (by positivity), (min_le_left _ _).trans hη₁16, ?_⟩
  intro θ T hθ hθ₁ hT hTη
  have hθlam : θ ≤ lam / 8 := hθ₁.trans (min_le_left _ _)
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hTη₁ : T ≤ η₁ * θ ^ 2 :=
    hTη.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hθ2.le)
  have hTy : T ≤ y₀ ^ 4 * θ ^ 2 :=
    hTη.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hθ2.le)
  have hTθ : T ≤ (θ / 4) ^ 2 := by
    have h1 : T ≤ 1 / 16 * θ ^ 2 := hTη₁.trans (mul_le_mul_of_nonneg_right hη₁16 hθ2.le)
    have e : (θ / 4) ^ 2 = 1 / 16 * θ ^ 2 := by ring
    rw [e]
    exact h1
  have hθ64 : θ ≤ 1 / 64 := by linarith
  have hT1 : T ≤ 1 := by nlinarith
  have hTlam : T ≤ (lam / 2) ^ 2 := by
    have h1 : θ / 4 ≤ lam / 2 := by linarith
    have h2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ θ / 4) h1 2
    linarith
  -- the source of the outer part
  have hE := HE lam T hlam (by linarith) hTlam hT1
  have hχE := HA α' θ (2 * θ) T (-4) (Ke / lam) (Elam G lam) hθ (by linarith) (by linarith) hTθ
    hα'.le hα1.le hKl hE
  have hg0 := ((hE.sub hχE).neg).weight (by positivity) hT1
    (by linarith : (-2 + 4 * γ - 4 : ℝ) ≤ -4)
  have hg : B0 α' T (-2 + 4 * γ - 4) Fe
      (fun t x => -(Elam G lam t x - chi (x / (2 * θ)) * Elam G lam t x)) :=
    hg0.mono (by rw [hFedef]; linarith)
  have hgz : ∀ t ∈ Ico (-T) 0, ∀ x, x ≤ θ →
      -(Elam G lam t x - chi (x / (2 * θ)) * Elam G lam t x) = 0 := by
    intro t _ x hx
    have h1 : chi (x / (2 * θ)) = 1 :=
      chi_of_le (by rw [div_le_one (by positivity)]; linarith)
    rw [h1]
    ring
  obtain ⟨U, hUR, hUS, -, hUT', hUJ, hUerr⟩ := Ho θ T Fe _ hθ hθlam hT hTη₁ hFe hg hgz
  refine ⟨U, hUR, hUS, ?_, hUT'.exp_le (by positivity) hα.le hαα.le, ?_⟩
  · refine hUJ.mono ?_
    have hq := quarter_div_sqrt_le hT.le hθ (by positivity : (0 : ℝ) ≤ y₀ ^ 4) hTy
    have hy4 : (y₀ ^ 4) ^ ((1 : ℝ) / 4) = y₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
      norm_num
    rw [hy4] at hq
    have hq0 : 0 ≤ T ^ ((1 : ℝ) / 4) / Real.sqrt θ :=
      div_nonneg (Real.rpow_nonneg hT.le _) (Real.sqrt_nonneg θ)
    have h1 := Hy₀ _ hq0 hq
    calc Co * (T ^ ((1 : ℝ) / 4) / Real.sqrt θ) ^ (α' - α) * Fe
        ≤ Co * (ε / (Co * Fe)) * Fe :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCo0.le) hFe.le
      _ = ε := by field_simp
  · have h1 := hUerr.exp_le (by positivity) hα.le hαα.le
    have h2 := HKc lam θ T hlam hlam8 hθ hθlam hTθ
    refine ((h1.sub h2).congr fun t _ x _ => ?_).mono ?_
    · show -Elam G lam t x - POf (blam G lam) (clam G lam) U t x
        = -(Elam G lam t x - chi (x / (2 * θ)) * Elam G lam t x)
          - POf (blam G lam) (clam G lam) U t x - chi (x / (2 * θ)) * Elam G lam t x
      ring
    · have hsθ : Real.sqrt θ ≤ x₀ := by
        have h3 := Real.sqrt_le_sqrt (hθ₁.trans (min_le_right _ _))
        rwa [Real.sqrt_sq hx₀.le] at h3
      have h4 := Hx₀ _ (Real.sqrt_nonneg θ) hsθ
      have h5 : Kc * Real.sqrt θ ^ (2 - 4 * γ) ≤ ε / 2 := by
        calc Kc * Real.sqrt θ ^ (2 - 4 * γ) ≤ Kc * (ε / (2 * (Kc + 1))) :=
              mul_le_mul_of_nonneg_left h4 hKc
          _ ≤ (Kc + 1) * (ε / (2 * (Kc + 1))) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = ε / 2 := by field_simp
      have h6 : ε / (2 * Fe) * Fe = ε / 2 := by field_simp
      linarith

end Calabi.Weighted
