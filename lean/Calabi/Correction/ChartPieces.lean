import Calabi.Correction.Iteration
import Calabi.Correction.JointSmooth
import Calabi.Correction.JointClass
import Calabi.Correction.Transfer

/-!
# The pieces of the solution in the local classes

The correction is a pair of chart functions with weighted bounds
(`exists_correction`). This file puts the pieces in the local classes of
`SmoothClass.lean`, on the whole space for the times in `(-T, 0)`:

* `sm_piece`, `sm_piece0`: a chart function with weighted jets on
  `{|z|² < R}` that vanishes for `|z|² > R′`, `R′ < R`, and its time
  derivative;
* `IsCorrection`: the properties of the correction pair that are used for the
  regularity and for the final statement;
* `IsCorrection.sm_U0`, `…sm_U1`, `…sm_U0t`, `…sm_U1t`: the four chart
  functions;
* `contDiffOn_Flam_chart`: the localized profile `F_λ(t, |z|²)` is smooth in
  space and time for `t < 0`.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.FlatWeighted Calabi.Chart Calabi.Radial Calabi.Osc
  Calabi.Flat

section Generic

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A function that vanishes on an open set is in the local classes there. -/
theorem Sm.of_vanish' {α : ℝ} {W : Set V} (hW : IsOpen W) {k : ℕ} {u : ℝ → V → ℝ}
    (h0 : ∀ t, ∀ z ∈ W, u t z = 0) : Sm α {p : V × ℝ | p.1 ∈ W} k u := by
  intro p₀ hp₀
  refine ⟨{p : V × ℝ | p.1 ∈ W}, fun _ _ => 0, 0, hW.preimage continuous_fst, hp₀, le_rfl,
    fun p hp => (h0 p.2 p.1 hp).symm, fun _ => contDiff_const, fun j _ => ?_⟩
  refine (WH.zero le_rfl fun _ _ => one_pos).congr fun p _ => ?_
  simp

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem isOpen_slab (T R : ℝ) :
    IsOpen {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} :=
  (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_lt (continuous_fst.norm.pow 2) continuous_const)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem isOpen_timeSlab (T : ℝ) : IsOpen {p : V × ℝ | p.2 ∈ Ioo (-T) 0} :=
  isOpen_Ioo.preimage continuous_snd

/-- **A chart function with weighted jets is in the local class**, on the whole
space for the times in `(-T, 0)`. -/
theorem sm_piece {α a w M R R' T : ℝ} {s : V × ℝ → ℝ} {k : ℕ} {u : ℝ → V → ℝ} (hα : 0 ≤ α)
    (ha : 0 < a) (hM : 0 ≤ M) (hRR : R' < R)
    (hs : ∀ p ∈ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}, 0 < s p)
    (hloc : ∀ p₀ ∈ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R},
      ∃ (K : ℝ) (N₀ : Set (V × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
        ∀ p ∈ N₀ ∩ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}, s p ≤ K ∧ 1 ≤ K * s p)
    (hsu : ∀ t, ContDiff ℝ k (u t)) (hsupp : ∀ t z, R' < ‖z‖ ^ 2 → u t z = 0)
    (hW : WJ α a s {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} w M k u) :
    Sm α {p : V × ℝ | p.2 ∈ Ioo (-T) 0} k u := by
  have hA : Sm α {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} k u :=
    Sm.of_WJ hα ha hM (isOpen_slab T R) (fun _ hp => hp) hs hloc hsu hW
  have hopen : IsOpen {z : V | R' < ‖z‖ ^ 2} := isOpen_lt continuous_const (continuous_norm.pow 2)
  have hB : Sm α {p : V × ℝ | p.1 ∈ {z : V | R' < ‖z‖ ^ 2}} k u :=
    Sm.of_vanish' hopen fun t z hz => hsupp t z hz
  refine (hA.union hB).mono_set fun p hp => ?_
  rcases lt_or_ge (‖p.1‖ ^ 2) R with h | h
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr (show R' < ‖p.1‖ ^ 2 by linarith)

set_option maxHeartbeats 1600000 in
/-- The same for a function with a weighted two-point bound, which is not
assumed to be continuous at the times outside `(-T, 0)`. -/
theorem sm_piece0 {α a w M R R' T : ℝ} {s : V × ℝ → ℝ} {u : ℝ → V → ℝ} (hα : 0 < α)
    (ha : 0 < a) (hM : 0 ≤ M) (hRR : R' < R)
    (hs : ∀ p ∈ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}, 0 < s p)
    (hloc : ∀ p₀ ∈ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R},
      ∃ (K : ℝ) (N₀ : Set (V × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
        ∀ p ∈ N₀ ∩ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}, s p ≤ K ∧ 1 ≤ K * s p)
    (hsupp : ∀ t z, R' < ‖z‖ ^ 2 → u t z = 0)
    (hW : WH α a s {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} w M (fun p => u p.2 p.1)) :
    Sm α {p : V × ℝ | p.2 ∈ Ioo (-T) 0} 0 u := by
  have hopenA := isOpen_slab (V := V) T R
  have hopen : IsOpen {z : V | R' < ‖z‖ ^ 2} := isOpen_lt continuous_const (continuous_norm.pow 2)
  -- the slices are continuous for the times in `(-T, 0)`
  have hcont : ∀ t ∈ Ioo (-T) 0, Continuous (u t) := by
    intro t ht
    rw [continuous_iff_continuousAt]
    intro z
    rcases lt_or_ge (‖z‖ ^ 2) R with hz | hz
    · have hp : ((z, t) : V × ℝ) ∈ {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} := ⟨ht, hz⟩
      obtain ⟨K, N₀, hK, hN₀, hpN, hsb⟩ := hloc _ hp
      have h1 := (hW.restrict (inter_subset_right
        (s := N₀) (t := {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R}))).to_uniform
        (w' := (0 : ℝ)) hM ha hα.le hK (fun p hp => hs p hp.2) (fun p hp => (hsb p hp).1)
        (fun p hp => (hsb p hp).2)
      have h2 := continuousAt_of_WH hα (hN₀.inter hopenA) ⟨hpN, hp⟩ h1
      have hc : Continuous fun y : V => ((y, t) : V × ℝ) :=
        continuous_id.prodMk continuous_const
      exact h2.comp (f := fun y : V => ((y, t) : V × ℝ)) hc.continuousAt
    · have hev : u t =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds (show R' < ‖z‖ ^ 2 by linarith)] with y hy
        exact hsupp t y hy
      exact continuousAt_const.congr hev.symm
  -- the modified function
  have hmod : ∀ t, Continuous (fun z => if t ∈ Ioo (-T) 0 then u t z else 0) := by
    intro t
    by_cases ht : t ∈ Ioo (-T) 0
    · simp only [ht, if_true]
      exact hcont t ht
    · simp only [ht, if_false]
      exact continuous_const
  have hA0 : Sm α {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} 0
      (fun t z => if t ∈ Ioo (-T) 0 then u t z else 0) := by
    refine Sm.of_WH hα.le ha hM hopenA (fun _ hp => hp) hs hloc hmod (hW.congr fun p hp => ?_)
    show (if p.2 ∈ Ioo (-T) 0 then u p.2 p.1 else 0) = u p.2 p.1
    rw [if_pos hp.1]
  have hA : Sm α {p : V × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < R} 0 u :=
    hA0.congr hopenA fun p hp => by
      show u p.2 p.1 = if p.2 ∈ Ioo (-T) 0 then u p.2 p.1 else 0
      rw [if_pos hp.1]
  have hB : Sm α {p : V × ℝ | p.1 ∈ {z : V | R' < ‖z‖ ^ 2}} 0 u :=
    Sm.of_vanish' hopen fun t z hz => hsupp t z hz
  refine (hA.union hB).mono_set fun p hp => ?_
  rcases lt_or_ge (‖p.1‖ ^ 2) R with h | h
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr (show R' < ‖p.1‖ ^ 2 by linarith)

end Generic

variable {c : ℝ} {G : ℝ → ℝ}

/-- **The correction pair of Proposition 6.1**: regularity, time derivatives,
weighted bounds, the equation in the momentum coordinate and the positivity of
the momentum profile. -/
structure IsCorrection (G : ℝ → ℝ) (lam α T w e M : ℝ) (U : Pair) : Prop where
  reg : Reg U
  sol : Sol T U
  xj : XJ α T w e U
  xt : XT α T w M U
  eqn : ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
    POf (blam G lam) (clam G lam) U t x + NOf vstar (blam G lam) (aflam G lam) U t x
      = -Elam G lam t x
  pos : ∀ t ∈ Ioo (-T) 0, ∀ x ∈ Icc (0 : ℝ) 1,
    0 < 1 + vstar x * (Flam G lam t x + valOf U t x)

section Pieces

variable {lam α T w e M : ℝ} {U : Pair}

/-- The scale `σ` is locally comparable to one before the final time. -/
theorem sigma_local (hT1 : T ≤ 1) :
    ∀ p₀ ∈ {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 3 / 4},
      ∃ (K : ℝ) (N₀ : Set (Flat18 × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
        ∀ p ∈ N₀ ∩ {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 3 / 4},
          sigma p ≤ K ∧ 1 ≤ K * sigma p := by
  intro p₀ hp₀
  have ht0 : p₀.2 < 0 := hp₀.1.2
  obtain ⟨lo, hlodef⟩ : ∃ lo : ℝ, lo = Real.sqrt (Real.sqrt (-(p₀.2 / 2))) := ⟨_, rfl⟩
  have hlo : 0 < lo := by
    rw [hlodef]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith))
  refine ⟨max 2 (1 / lo), {p : Flat18 × ℝ | p.2 < p₀.2 / 2}, (by norm_num : (1 : ℝ) ≤ 2).trans
    (le_max_left _ _), isOpen_lt continuous_snd continuous_const, by
      show p₀.2 < p₀.2 / 2
      linarith, fun p hp => ?_⟩
  have hpt : p.2 < p₀.2 / 2 := hp.1
  have hdom : p ∈ dom0 T := ⟨⟨hp.2.1.1.le, hp.2.1.2⟩, hp.2.2.le⟩
  have h2 : sigma p ≤ 2 := sigma_le_two0 hT1 p hdom
  have h3 : lo ≤ sigma p := by
    rw [hlodef]
    unfold sigma
    apply Real.sqrt_le_sqrt
    have h4 := Real.sqrt_le_sqrt (by linarith : -(p₀.2 / 2) ≤ -p.2)
    nlinarith [sq_nonneg ‖p.1‖]
  refine ⟨h2.trans (le_max_left _ _), ?_⟩
  have h5 : 1 / lo * lo = 1 := by field_simp
  calc (1 : ℝ) = 1 / lo * lo := h5.symm
    _ ≤ max 2 (1 / lo) * sigma p :=
        mul_le_mul (le_max_right _ _) h3 hlo.le ((by norm_num : (0 : ℝ) ≤ 2).trans
          (le_max_left _ _))

theorem one_local (T : ℝ) :
    ∀ p₀ ∈ {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 7 / 8},
      ∃ (K : ℝ) (N₀ : Set (Flat6 × ℝ)), 1 ≤ K ∧ IsOpen N₀ ∧ p₀ ∈ N₀ ∧
        ∀ p ∈ N₀ ∩ {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 7 / 8},
          (fun _ : Flat6 × ℝ => (1 : ℝ)) p ≤ K ∧ 1 ≤ K * (fun _ : Flat6 × ℝ => (1 : ℝ)) p :=
  fun _ _ => ⟨1, univ, le_rfl, isOpen_univ, mem_univ _, fun _ _ => ⟨le_rfl, by norm_num⟩⟩

theorem slab0_subset (T : ℝ) :
    {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 3 / 4} ⊆ dom0 T :=
  fun _ hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2.le⟩

theorem slab1_subset (T : ℝ) :
    {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0 ∧ ‖p.1‖ ^ 2 < 7 / 8} ⊆ dom1 T :=
  fun _ hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2.le⟩

theorem sm_U0 (hα : 0 ≤ α) (he : 0 ≤ e) (hT1 : T ≤ 1) (hR : Reg U) (hJ : XJ α T w e U) :
    Sm α {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0} 4 U.1 :=
  sm_piece (a := 1 / 64) (R := 3 / 4) (R' := 1 / 2) hα (by norm_num) he (by norm_num)
    (fun p hp => (isScale0 T).pos p (slab0_subset T hp)) (sigma_local hT1) hR.smooth0 hR.supp0
    (hJ.1.restrict (slab0_subset T))

theorem sm_U1 (hα : 0 ≤ α) (he : 0 ≤ e) (hR : Reg U) (hJ : XJ α T w e U) :
    Sm α {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0} 4 U.2.2.1 :=
  sm_piece (a := 1 / 64) (R := 7 / 8) (R' := 3 / 4) hα (by norm_num) he (by norm_num)
    (fun _ _ => one_pos) (one_local T) hR.smooth1 hR.supp1 (hJ.2.restrict (slab1_subset T))

theorem sm_U0t (hα : 0 < α) (hM : 0 ≤ M) (hT1 : T ≤ 1) (hR : Reg U) (hXT : XT α T w M U) :
    Sm α {p : Flat18 × ℝ | p.2 ∈ Ioo (-T) 0} 0 U.2.1 :=
  sm_piece0 (a := 1 / 64) (R := 3 / 4) (R' := 1 / 2) hα (by norm_num) hM (by norm_num)
    (fun p hp => (isScale0 T).pos p (slab0_subset T hp)) (sigma_local hT1) hR.supp0t
    (hXT.1.restrict (slab0_subset T))

theorem sm_U1t (hα : 0 < α) (hM : 0 ≤ M) (hR : Reg U) (hXT : XT α T w M U) :
    Sm α {p : Flat6 × ℝ | p.2 ∈ Ioo (-T) 0} 0 U.2.2.2 :=
  sm_piece0 (a := 1 / 64) (R := 7 / 8) (R' := 3 / 4) hα (by norm_num) hM (by norm_num)
    (fun _ _ => one_pos) (one_local T) hR.supp1t (hXT.2.restrict (slab1_subset T))

end Pieces

/-! ### Radial symmetry -/

theorem Sol.eval0 {T : ℝ} {U : Pair} (h : Sol T U) (t : ℝ) (z : Flat18) :
    U.1 t (‖z‖ • e18) = U.1 t z :=
  radial_eq_of_norm_eq (h.radial0 t) (by rw [norm_smul, norm_e18, mul_one, norm_norm])

theorem Sol.eval1 {T : ℝ} {U : Pair} (h : Sol T U) (t : ℝ) (w : Flat6) :
    U.2.2.1 t (‖w‖ • e6) = U.2.2.1 t w :=
  radial_eq_of_norm_eq (h.radial1 t) (by rw [norm_smul, norm_e6, mul_one, norm_norm])

theorem Sol.evalt0 {T : ℝ} {U : Pair} (h : Sol T U) {t : ℝ} (ht : t ∈ Ioo (-T) 0) (z : Flat18) :
    U.2.1 t (‖z‖ • e18) = U.2.1 t z :=
  radial_eq_of_norm_eq (u := U.2.1 t)
    (fun Q y => invariant_timeDeriv (u := U.1) (ut := U.2.1) (Q := Q)
      (fun r y => h.radial0 r Q y) (fun y => h.deriv0 t ht y) y)
    (by rw [norm_smul, norm_e18, mul_one, norm_norm])

theorem Sol.evalt1 {T : ℝ} {U : Pair} (h : Sol T U) {t : ℝ} (ht : t ∈ Ioo (-T) 0) (w : Flat6) :
    U.2.2.2 t (‖w‖ • e6) = U.2.2.2 t w :=
  radial_eq_of_norm_eq (u := U.2.2.2 t)
    (fun Q y => invariant_timeDeriv (u := U.2.2.1) (ut := U.2.2.2) (Q := Q)
      (fun r y => h.radial1 r Q y) (fun y => h.deriv1 t ht y) y)
    (by rw [norm_smul, norm_e6, mul_one, norm_norm])

/-! ### The localized profile in the chart -/

/-- **The localized profile is smooth in space and time** for `t < 0`. -/
theorem contDiffOn_Flam_chart {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (hP : IsProfile c G) (lam : ℝ) :
    ContDiffOn ℝ ∞ (fun q : V × ℝ => Flam G lam q.2 (‖q.1‖ ^ 2)) {q : V × ℝ | q.2 < 0} := by
  obtain ⟨δ, hδ, hsm⟩ := hP.smooth
  have hh := contDiffOn_hfun hδ hsm
  have hneg : ∀ q ∈ {q : V × ℝ | q.2 < 0}, 0 < Real.sqrt (-q.2) := fun q hq =>
    Real.sqrt_pos.2 (by
      have : q.2 < 0 := hq
      linarith)
  have hsq : ContDiffOn ℝ ∞ (fun q : V × ℝ => Real.sqrt (-q.2)) {q : V × ℝ | q.2 < 0} :=
    (contDiff_snd.neg).contDiffOn.sqrt fun q hq => by
      have : q.2 < 0 := hq
      linarith
  have hn : ContDiff ℝ ∞ (fun q : V × ℝ => ‖q.1‖ ^ 2) := (contDiff_norm_sq ℝ).comp contDiff_fst
  have harg : ContDiffOn ℝ ∞ (fun q : V × ℝ => ‖q.1‖ ^ 2 / Real.sqrt (-q.2))
      {q : V × ℝ | q.2 < 0} := hn.contDiffOn.div hsq fun q hq => (hneg q hq).ne'
  have hcomp : ContDiffOn ℝ ∞ (fun q : V × ℝ => hfun G (‖q.1‖ ^ 2 / Real.sqrt (-q.2)))
      {q : V × ℝ | q.2 < 0} := hh.comp harg fun q hq => by
    have h1 : 0 ≤ ‖q.1‖ ^ 2 / Real.sqrt (-q.2) := div_nonneg (sq_nonneg _) (hneg q hq).le
    show -δ < ‖q.1‖ ^ 2 / Real.sqrt (-q.2)
    linarith
  have hF : ContDiffOn ℝ ∞ (fun q : V × ℝ =>
      hfun G (‖q.1‖ ^ 2 / Real.sqrt (-q.2)) / Real.sqrt (-q.2)) {q : V × ℝ | q.2 < 0} :=
    hcomp.div hsq fun q hq => (hneg q hq).ne'
  have hchi : ContDiff ℝ ∞ (fun q : V × ℝ => chi (‖q.1‖ ^ 2 / lam)) :=
    contDiff_chi.comp (hn.div_const lam)
  exact hchi.contDiffOn.mul hF

end Calabi.Weighted
