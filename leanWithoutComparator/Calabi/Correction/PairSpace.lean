import Calabi.Correction.RayBounds

/-!
# The space of solutions: pairs of chart functions

The correction `V` of Section 6 of the manuscript is represented by a pair of
functions on the two flat charts, `U⁰` on `ℝ¹⁸` and `U¹` on `ℝ⁶`, together
with their time derivatives:

  `V(t, x) = U⁰(t, √x e) + U¹(t, √(1 - x) e')`.

`U⁰(t, ·)` vanishes for `|z|² > 1/2` and `U¹(t, ·)` for `|w|² > 3/4`, so that
the value of the chart operator on `V` is computed in each chart separately and
no derivative is ever transferred between the charts.

* `valOf`, `AOf`, `dtOf`: the quantities of order zero `V`, `A V`, `∂ₜ V`;
* `Reg`: regularity and support; `XJ`, `XT`: the weighted bounds of the jets
  and of the time derivatives in the two charts;
* `valOf_bound`, `AOf_bound`, `dtOf_bound`: the two-chart bounds of `V`, `A V`
  and `∂ₜ V` by the norm of the pair;
* `POf`, `NOf`: the linear operator `∂ₜ + b² A + c` and the nonlinearity
  `v∗² V² A F + (2 v∗ b V + v∗² V²) A V` for given coefficients;
* `NOf_diff_bound`: the Lipschitz estimate (6.15) of the nonlinearity.
-/

open Set Filter Topology
open scoped ContDiff

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart

/-- A pair of functions on the two charts with their time derivatives:
`(U⁰, U⁰ₜ, U¹, U¹ₜ)`. -/
abbrev Pair := (ℝ → Flat18 → ℝ) × (ℝ → Flat18 → ℝ) × (ℝ → Flat6 → ℝ) × (ℝ → Flat6 → ℝ)

/-- The function of the momentum coordinate represented by a pair. -/
noncomputable def valOf (U : Pair) (t x : ℝ) : ℝ :=
  U.1 t (Real.sqrt x • e18) + U.2.2.1 t (Real.sqrt (1 - x) • e6)

/-- The operator `A` on the function represented by a pair, computed in the
two charts. -/
noncomputable def AOf (U : Pair) (t x : ℝ) : ℝ :=
  chartOp 6 (U.1 t) (Real.sqrt x • e18) / 16
    + chartOp 18 (U.2.2.1 t) (Real.sqrt (1 - x) • e6) / 16

/-- The time derivative of the function represented by a pair. -/
noncomputable def dtOf (U : Pair) (t x : ℝ) : ℝ :=
  U.2.1 t (Real.sqrt x • e18) + U.2.2.2 t (Real.sqrt (1 - x) • e6)

/-- Regularity and support of a pair. -/
structure Reg (U : Pair) : Prop where
  smooth0 : ∀ t, ContDiff ℝ 4 (U.1 t)
  smooth1 : ∀ t, ContDiff ℝ 4 (U.2.2.1 t)
  supp0 : ∀ t z, 1 / 2 < ‖z‖ ^ 2 → U.1 t z = 0
  supp0t : ∀ t z, 1 / 2 < ‖z‖ ^ 2 → U.2.1 t z = 0
  supp1 : ∀ t w, 3 / 4 < ‖w‖ ^ 2 → U.2.2.1 t w = 0
  supp1t : ∀ t w, 3 / 4 < ‖w‖ ^ 2 → U.2.2.2 t w = 0

theorem Reg.zero : Reg (0 : Pair) where
  smooth0 _ := contDiff_const
  smooth1 _ := contDiff_const
  supp0 _ _ _ := rfl
  supp0t _ _ _ := rfl
  supp1 _ _ _ := rfl
  supp1t _ _ _ := rfl

theorem Reg.add {U U' : Pair} (h : Reg U) (h' : Reg U') : Reg (U + U') where
  smooth0 t := (h.smooth0 t).add (h'.smooth0 t)
  smooth1 t := (h.smooth1 t).add (h'.smooth1 t)
  supp0 t z hz := by
    show U.1 t z + U'.1 t z = 0
    rw [h.supp0 t z hz, h'.supp0 t z hz, add_zero]
  supp0t t z hz := by
    show U.2.1 t z + U'.2.1 t z = 0
    rw [h.supp0t t z hz, h'.supp0t t z hz, add_zero]
  supp1 t z hz := by
    show U.2.2.1 t z + U'.2.2.1 t z = 0
    rw [h.supp1 t z hz, h'.supp1 t z hz, add_zero]
  supp1t t z hz := by
    show U.2.2.2 t z + U'.2.2.2 t z = 0
    rw [h.supp1t t z hz, h'.supp1t t z hz, add_zero]

theorem Reg.sub {U U' : Pair} (h : Reg U) (h' : Reg U') : Reg (U - U') where
  smooth0 t := (h.smooth0 t).sub (h'.smooth0 t)
  smooth1 t := (h.smooth1 t).sub (h'.smooth1 t)
  supp0 t z hz := by
    show U.1 t z - U'.1 t z = 0
    rw [h.supp0 t z hz, h'.supp0 t z hz, sub_zero]
  supp0t t z hz := by
    show U.2.1 t z - U'.2.1 t z = 0
    rw [h.supp0t t z hz, h'.supp0t t z hz, sub_zero]
  supp1 t z hz := by
    show U.2.2.1 t z - U'.2.2.1 t z = 0
    rw [h.supp1 t z hz, h'.supp1 t z hz, sub_zero]
  supp1t t z hz := by
    show U.2.2.2 t z - U'.2.2.2 t z = 0
    rw [h.supp1t t z hz, h'.supp1t t z hz, sub_zero]

/-! ### Additivity -/

theorem valOf_add (U U' : Pair) (t x : ℝ) : valOf (U + U') t x = valOf U t x + valOf U' t x := by
  show U.1 t _ + U'.1 t _ + (U.2.2.1 t _ + U'.2.2.1 t _) = _
  unfold valOf
  ring

theorem valOf_sub (U U' : Pair) (t x : ℝ) : valOf (U - U') t x = valOf U t x - valOf U' t x := by
  show U.1 t _ - U'.1 t _ + (U.2.2.1 t _ - U'.2.2.1 t _) = _
  unfold valOf
  ring

theorem dtOf_add (U U' : Pair) (t x : ℝ) : dtOf (U + U') t x = dtOf U t x + dtOf U' t x := by
  show U.2.1 t _ + U'.2.1 t _ + (U.2.2.2 t _ + U'.2.2.2 t _) = _
  unfold dtOf
  ring

theorem AOf_add {U U' : Pair} (h : Reg U) (h' : Reg U') (t x : ℝ) :
    AOf (U + U') t x = AOf U t x + AOf U' t x := by
  show chartOp 6 (fun z => U.1 t z + U'.1 t z) _ / 16
    + chartOp 18 (fun w => U.2.2.1 t w + U'.2.2.1 t w) _ / 16 = _
  rw [chartOp_add 6 (h.smooth0 t) (h'.smooth0 t), chartOp_add 18 (h.smooth1 t) (h'.smooth1 t)]
  unfold AOf
  ring

theorem AOf_sub {U U' : Pair} (h : Reg U) (h' : Reg U') (t x : ℝ) :
    AOf (U - U') t x = AOf U t x - AOf U' t x := by
  have h1 := AOf_add (h.sub h') h' t x
  rw [sub_add_cancel] at h1
  linarith

/-! ### The norms -/

/-- The weighted bound of the jets of order at most four in the two charts. -/
def XJ (α T w a : ℝ) (U : Pair) : Prop :=
  WJ α (1 / 64) (sigma (V := Flat18)) (dom0 T) w a 4 U.1 ∧
    WJ α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) w a 4 U.2.2.1

/-- The weighted bound of the time derivatives in the two charts. -/
def XT (α T w a : ℝ) (U : Pair) : Prop :=
  WH α (1 / 64) (sigma (V := Flat18)) (dom0 T) (w - 4) a (fun p => U.2.1 p.2 p.1) ∧
    WH α (1 / 64) (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) (w - 4) a (fun p => U.2.2.2 p.2 p.1)

section Norms

variable {α T w a b : ℝ} {U U' : Pair}

theorem XJ.mono (h : XJ α T w a U) (hab : a ≤ b) : XJ α T w b U :=
  ⟨h.1.mono (isScale0 T).pos hab, h.2.mono (isScale1 T).pos hab⟩

theorem XJ.add (hU : Reg U) (hU' : Reg U') (h : XJ α T w a U) (h' : XJ α T w b U') :
    XJ α T w (a + b) (U + U') :=
  ⟨WJ.add hU.smooth0 hU'.smooth0 h.1 h'.1, WJ.add hU.smooth1 hU'.smooth1 h.2 h'.2⟩

theorem XJ.zero (α T w : ℝ) : XJ α T w 0 (0 : Pair) := by
  constructor
  · intro j _
    refine (WH.zero le_rfl (isScale0 T).pos).congr fun p _ => ?_
    show iteratedFDeriv ℝ j (fun _ : Flat18 => (0 : ℝ)) p.1 = 0
    simp
  · intro j _
    refine (WH.zero le_rfl (isScale1 T).pos).congr fun p _ => ?_
    show iteratedFDeriv ℝ j (fun _ : Flat6 => (0 : ℝ)) p.1 = 0
    simp

theorem XT.mono (h : XT α T w a U) (hab : a ≤ b) : XT α T w b U :=
  ⟨h.1.mono (isScale0 T).pos hab, h.2.mono (isScale1 T).pos hab⟩

theorem XT.add (h : XT α T w a U) (h' : XT α T w b U') : XT α T w (a + b) (U + U') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

end Norms

/-! ### The quantities of order zero of a pair -/

/-- **The function represented by a pair** has the two-chart bound of weight
`w`. -/
theorem valOf_bound (α w : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (T a : ℝ) (U : Pair),
    T ≤ 1 → 0 ≤ a → Reg U → XJ α T w a U → B0 α T w (K * a) (valOf U) := by
  obtain ⟨K₀, hK₀, H₀⟩ := B0.ray0 α w hα
  obtain ⟨K₁, hK₁, H₁⟩ := B0.ray1 α w hα
  refine ⟨K₀ + K₁, by linarith, fun T a U hT ha hU hX => ?_⟩
  have h0 := H₀ T a (fun p => U.1 p.2 p.1) hT ha hX.1.value (fun p hp => hU.supp0 p.2 p.1 hp)
  have h1 := H₁ T a (fun p => U.2.2.1 p.2 p.1) hT ha hX.2.value
    (fun p hp => hU.supp1 p.2 p.1 hp)
  refine ((h0.add h1).congr fun t _ x _ => rfl).mono (le_of_eq ?_)
  ring

/-- **The time derivative of a pair** has the two-chart bound of weight
`w - 4`. -/
theorem dtOf_bound (α w : ℝ) (hα : 0 ≤ α) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (T a : ℝ) (U : Pair),
    T ≤ 1 → 0 ≤ a → Reg U → XT α T w a U → B0 α T (w - 4) (K * a) (dtOf U) := by
  obtain ⟨K₀, hK₀, H₀⟩ := B0.ray0 α (w - 4) hα
  obtain ⟨K₁, hK₁, H₁⟩ := B0.ray1 α (w - 4) hα
  refine ⟨K₀ + K₁, by linarith, fun T a U hT ha hU hX => ?_⟩
  have h0 := H₀ T a (fun p => U.2.1 p.2 p.1) hT ha hX.1 (fun p hp => hU.supp0t p.2 p.1 hp)
  have h1 := H₁ T a (fun p => U.2.2.2 p.2 p.1) hT ha hX.2 (fun p hp => hU.supp1t p.2 p.1 hp)
  refine ((h0.add h1).congr fun t _ x _ => rfl).mono (le_of_eq ?_)
  ring

/-- **The operator `A` on a pair** has the two-chart bound of weight `w - 4`. -/
theorem AOf_bound (α w : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (T a : ℝ) (U : Pair), T ≤ 1 → 0 ≤ a → Reg U → XJ α T w a U →
      B0 α T (w - 4) (K * a) (AOf U) := by
  obtain ⟨C₀, hC₀, HC₀⟩ := chartOp_WH (V := Flat18) 2 w 2 6 (by norm_num)
  obtain ⟨C₁, hC₁, HC₁⟩ := chartOp_WH (V := Flat6) 1 w 2 18 (by norm_num)
  obtain ⟨K₀, hK₀, H₀⟩ := B0.ray0 α (w - 4) hα
  obtain ⟨K₁, hK₁, H₁⟩ := B0.ray1 α (w - 4) hα
  have hK₀0 : 0 ≤ K₀ := by linarith
  have hK₁0 : 0 ≤ K₁ := by linarith
  refine ⟨K₀ * (|(1 / 16 : ℝ)| * C₀) + K₁ * (|(1 / 16 : ℝ)| * C₁), by positivity, ?_⟩
  intro T a U hT ha hU hX
  -- the chart at `x = 0`
  have hc0 := (HC₀ α (1 / 64) a (sigma (V := Flat18)) (dom0 T) U.1 (isScale0 T) ha
    (by norm_num) hα hα1 (sigma_le_two0 hT)
    (fun p hp => by
      have := norm_nonneg p.1
      nlinarith [hp.2])
    hU.smooth0 hX.1).const_smul (1 / 16)
  have hz0 : ∀ p : Flat18 × ℝ, 1 / 2 < ‖p.1‖ ^ 2 →
      (1 / 16 : ℝ) • chartOp 6 (U.1 p.2) p.1 = 0 := by
    intro p hp
    have hopen : IsOpen {z : Flat18 | 1 / 2 < ‖z‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    have hev : U.1 p.2 =ᶠ[𝓝 p.1] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hp] with z hz
      exact hU.supp0 p.2 z hz
    rw [chartOp_eq_zero_of_eventually 6 hev, smul_zero]
  have h0 := H₀ T _ _ hT (by positivity) hc0 hz0
  -- the chart at `x = 1`
  have hc1 := (HC₁ α (1 / 64) a (fun _ : Flat6 × ℝ => (1 : ℝ)) (dom1 T) U.2.2.1 (isScale1 T) ha
    (by norm_num) hα hα1 (fun _ _ => by norm_num)
    (fun p hp => by
      have := norm_nonneg p.1
      nlinarith [hp.2])
    hU.smooth1 hX.2).const_smul (1 / 16)
  have hz1 : ∀ p : Flat6 × ℝ, 3 / 4 < ‖p.1‖ ^ 2 →
      (1 / 16 : ℝ) • chartOp 18 (U.2.2.1 p.2) p.1 = 0 := by
    intro p hp
    have hopen : IsOpen {z : Flat6 | 3 / 4 < ‖z‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_norm.pow 2)
    have hev : U.2.2.1 p.2 =ᶠ[𝓝 p.1] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hp] with z hz
      exact hU.supp1 p.2 z hz
    rw [chartOp_eq_zero_of_eventually 18 hev, smul_zero]
  have h1 := H₁ T _ _ hT (by positivity) hc1 hz1
  refine ((h0.add h1).congr fun t _ x _ => ?_).mono (le_of_eq ?_)
  · show AOf U t x = (1 / 16 : ℝ) • chartOp 6 (U.1 t) (Real.sqrt x • e18)
      + (1 / 16 : ℝ) • chartOp 18 (U.2.2.1 t) (Real.sqrt (1 - x) • e6)
    unfold AOf
    rw [smul_eq_mul, smul_eq_mul]
    ring
  · ring

/-! ### Products with a lowered weight -/

/-- The product of two quantities of order zero, with the weight lowered to a
prescribed one. -/
theorem B0.mul_lower (α v v' v'' : ℝ) (hv : v'' ≤ v + v') : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (T M N : ℝ) (g g' : ℝ → ℝ → ℝ), T ≤ 1 → 0 ≤ M → 0 ≤ N → B0 α T v M g → B0 α T v' N g' →
      B0 α T v'' (C * (M * N)) (fun t x => g t x * g' t x) := by
  have h2 : 0 ≤ (2 : ℝ) ^ |v| := Real.rpow_nonneg (by norm_num) _
  have h3 : 0 ≤ (2 : ℝ) ^ (v + v' - v'') := Real.rpow_nonneg (by norm_num) _
  refine ⟨(1 + (2 : ℝ) ^ |v|) * (2 : ℝ) ^ (v + v' - v''), mul_nonneg (by linarith) h3, ?_⟩
  intro T M N g g' hT hM hN hg hg'
  have h := (hg.mul hg' hM hN).weight (mul_nonneg (mul_nonneg (by linarith) hM) hN) hT hv
  refine h.mono (le_of_eq ?_)
  ring

/-! ### The linear operator and the nonlinearity -/

/-- The linear operator `∂ₜ + b² A + c` on a pair. -/
noncomputable def POf (bl cl : ℝ → ℝ → ℝ) (U : Pair) (t x : ℝ) : ℝ :=
  dtOf U t x + bl t x ^ 2 * AOf U t x + cl t x * valOf U t x

/-- The nonlinearity `v∗² V² A F + (2 v∗ b V + v∗² V²) A V` on a pair. -/
noncomputable def NOf (vs : ℝ → ℝ) (bl af : ℝ → ℝ → ℝ) (U : Pair) (t x : ℝ) : ℝ :=
  vs x ^ 2 * valOf U t x ^ 2 * af t x
    + (2 * vs x * bl t x * valOf U t x + vs x ^ 2 * valOf U t x ^ 2) * AOf U t x

theorem POf_add (bl cl : ℝ → ℝ → ℝ) {U U' : Pair} (h : Reg U) (h' : Reg U') :
    POf bl cl (U + U') = POf bl cl U + POf bl cl U' := by
  funext t x
  show POf bl cl (U + U') t x = POf bl cl U t x + POf bl cl U' t x
  unfold POf
  rw [dtOf_add, AOf_add h h', valOf_add]
  ring

set_option maxHeartbeats 1600000 in
/-- **The Lipschitz estimate of the nonlinearity**, (6.15) of the manuscript:
on the ball of radius `e ≤ 1` of the jet norm the difference of the values of
the nonlinearity is bounded by `C e` times the jet norm of the difference. -/
theorem NOf_diff_bound (α w K : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hw : -2 ≤ w) (hK : 0 ≤ K) :
    ∃ CN : ℝ, 0 ≤ CN ∧ ∀ (T e d : ℝ) (vs : ℝ → ℝ) (bl af : ℝ → ℝ → ℝ) (U U' : Pair),
      T ≤ 1 → 0 ≤ e → e ≤ 1 → 0 ≤ d →
      B0 α T 2 K (fun _ x => vs x) → B0 α T 0 K bl → B0 α T (-6) K af →
      Reg U → Reg U' → XJ α T w e U → XJ α T w e U' → XJ α T w d (U - U') →
      B0 α T (w - 4) (CN * (e * d))
        (fun t x => NOf vs bl af U t x - NOf vs bl af U' t x) := by
  obtain ⟨Kv, hKv, Hv⟩ := valOf_bound α w hα
  obtain ⟨KA, hKA, HA⟩ := AOf_bound α w hα hα1
  obtain ⟨Ca, hCa, Ha⟩ := B0.mul_lower α 2 2 4 (by norm_num)
  obtain ⟨Cb, hCb, Hb⟩ := B0.mul_lower α 4 (-6) (-2) (by norm_num)
  obtain ⟨Cc, hCc, Hc⟩ := B0.mul_lower α w w (2 * w) (by linarith)
  obtain ⟨Cd, hCd, Hd⟩ := B0.mul_lower α (-2) (2 * w) (w - 4) (by linarith)
  obtain ⟨Ce, hCe, He⟩ := B0.mul_lower α 2 0 2 (by norm_num)
  obtain ⟨Cf, hCf, Hf⟩ := B0.mul_lower α w (w - 4) (2 * w - 4) (by linarith)
  obtain ⟨Cg, hCg, Hg⟩ := B0.mul_lower α 2 (2 * w - 4) (w - 4) (by linarith)
  obtain ⟨Ch, hCh, Hh⟩ := B0.mul_lower α (2 * w) (w - 4) (3 * w - 4) (by linarith)
  obtain ⟨Ci, hCi, Hi⟩ := B0.mul_lower α 4 (3 * w - 4) (w - 4) (by linarith)
  have hKv0 : 0 ≤ Kv := by linarith
  refine ⟨Cd * (Cb * (Ca * (K * K) * K) * (Cc * (Kv * (Kv + Kv))))
      + 2 * (Cg * (Ce * (K * K) * (Cf * (Kv * KA) + Cf * (Kv * KA))))
      + Ci * (Ca * (K * K) * (Ch * (Cc * (Kv * (Kv + Kv)) * KA) + Ch * (Cc * (Kv * Kv) * KA))),
    by positivity, ?_⟩
  intro T e d vs bl af U U' hT he he1 hd hvs hbl haf hU hU' hXU hXU' hXd
  have hUd := hU.sub hU'
  -- the six quantities
  have ha := Hv T e U hT he hU hXU
  have ha' := Hv T e U' hT he hU' hXU'
  have hδa := Hv T d (U - U') hT hd hUd hXd
  have hA := HA T e U hT he hU hXU
  have hA1 := HA T 1 U hT zero_le_one hU (hXU.mono he1)
  have hδA := HA T d (U - U') hT hd hUd hXd
  have ha'1 := Hv T 1 U' hT zero_le_one hU' (hXU'.mono he1)
  have hsum := ha.add ha'
  have hKve : 0 ≤ Kv * e := mul_nonneg hKv0 he
  have hKvd : 0 ≤ Kv * d := mul_nonneg hKv0 hd
  have hKAe : 0 ≤ KA * e := mul_nonneg hKA he
  have hKAd : 0 ≤ KA * d := mul_nonneg hKA hd
  -- the coefficients
  have hvv := Ha T K K _ _ hT hK hK hvs hvs
  have hvvf := Hb T _ K _ _ hT (by positivity) hK hvv haf
  have hvb := He T K K _ _ hT hK hK hvs hbl
  -- the first term
  have hδs := Hc T _ _ _ _ hT hKvd (add_nonneg hKve hKve) hδa hsum
  have t1 := Hd T _ _ _ _ hT (by positivity) (by positivity) hvvf hδs
  -- the second term
  have hδaA := Hf T _ _ _ _ hT hKvd hKAe hδa hA
  have ha'δA := Hf T _ _ _ _ hT hKve hKAd ha' hδA
  have t2 := (Hg T _ _ _ _ hT (by positivity) (by positivity) hvb (hδaA.add ha'δA)).const_mul 2
  -- the third term
  have hδsA := Hh T _ _ _ _ hT (by positivity) (by positivity) hδs hA1
  have haa := Hc T _ _ _ _ hT hKve (by positivity : 0 ≤ Kv * 1) ha' ha'1
  have haaδA := Hh T _ _ _ _ hT (by positivity) hKAd haa hδA
  have t3 := Hi T _ _ _ _ hT (by positivity) (by positivity) hvv (hδsA.add haaδA)
  refine (((t1.add t2).add t3).congr fun t _ x _ => ?_).mono (le_of_eq ?_)
  · show NOf vs bl af U t x - NOf vs bl af U' t x
      = vs x * vs x * af t x * (valOf (U - U') t x * (valOf U t x + valOf U' t x))
        + 2 * (vs x * bl t x * (valOf (U - U') t x * AOf U t x
          + valOf U' t x * AOf (U - U') t x))
        + vs x * vs x * (valOf (U - U') t x * (valOf U t x + valOf U' t x) * AOf U t x
          + valOf U' t x * valOf U' t x * AOf (U - U') t x)
    rw [valOf_sub, AOf_sub hU hU']
    unfold NOf
    ring
  · rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring

end Calabi.Weighted
