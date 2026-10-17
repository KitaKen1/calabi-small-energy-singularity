import Calabi.Correction.DiffQuot
import Calabi.Correction.ParabolicBox

/-!
# One spatial derivative from the interior estimate

`Sm.diffquot` is the step of the regularity argument (Section 6.4 of the
manuscript, "classical interior parabolic regularity, applied successively
after taking spatial difference quotients"): for a solution of

  `u_t + a Δ² u = f`

with `u` in the local class of order four, `u_t` of order zero, and `a > 0`,
`f` of order one, every first derivative `∂_e u` is again in the class of
order four.

`dq_uniform` is the uniform estimate: on a small box the difference quotients
of `u` satisfy the equation with the coefficient `a` and a source whose
Hölder bound does not depend on the step, so that `interior_real` bounds
their jets of order at most four uniformly. The derivative is then obtained
as the limit along a dyadic sequence of steps: by the dyadic identity the
increments are summable, and `contDiff_of_seq` applies after multiplication
by a cut-off.
-/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicLocalization OAI.FlatWeighted Calabi.Chart

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A spatial translation of a function with a parabolic Hölder bound. -/
theorem _root_.OAI.ParabolicInterior.HolderBound.shift {E : Type*} [NormedAddCommGroup E] {α M : ℝ} {S S' : Set (V × ℝ)}
    {f : V × ℝ → E} (hf : HolderBound α S f M) (v : V)
    (hS : ∀ p ∈ S', ((p.1 + v, p.2) : V × ℝ) ∈ S) :
    HolderBound α S' (fun p => f (p.1 + v, p.2)) M :=
  ⟨fun p hp => hf.1 _ (hS p hp), fun p hp q hq => by
    have h := hf.2 _ (hS p hp) _ (hS q hq)
    rwa [pdist_shift] at h⟩

omit [FiniteDimensional ℝ V] in
/-- The first derivative is the jet of order one. -/
theorem fderiv_eq_curryFin1 (f : V → ℝ) (x : V) :
    fderiv ℝ f x = continuousMultilinearCurryFin1 ℝ V ℝ (iteratedFDeriv ℝ 1 f x) := by
  ext v
  simp [iteratedFDeriv_one_apply]

/-- The first derivative of a function with uniform jets of order one. -/
theorem holderBound_fderiv {α M : ℝ} {N S : Set (V × ℝ)} {g : ℝ → V → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hM : 0 ≤ M) (h : WJ α 1 (fun _ : V × ℝ => (1 : ℝ)) N 0 M k g) (hS : S ⊆ N)
    (hd : ∀ p ∈ S, ∀ q ∈ S, pdist p q ≤ 1) :
    HolderBound α S (fun p => fderiv ℝ (g p.2) p.1) M := by
  have h1 := holderBound_of_WH (h 1 hk) hS hd
  have hL : ‖((continuousMultilinearCurryFin1 ℝ V ℝ).toContinuousLinearEquiv.toContinuousLinearMap :
      (V [×1]→L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
    rw [one_mul]
    exact le_of_eq ((continuousMultilinearCurryFin1 ℝ V ℝ).norm_map φ)
  have h2 := (h1.clm ((continuousMultilinearCurryFin1 ℝ V
    ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).mono (mul_le_of_le_one_left hM hL)
  have e : (fun p : V × ℝ => fderiv ℝ (g p.2) p.1)
      = fun p => ((continuousMultilinearCurryFin1 ℝ V
        ℝ).toContinuousLinearEquiv.toContinuousLinearMap) (iteratedFDeriv ℝ 1 (g p.2) p.1) :=
    funext fun p => fderiv_eq_curryFin1 (g p.2) p.1
  rw [e]
  exact h2

set_option maxHeartbeats 3200000 in
/-- **The uniform estimate for the difference quotients.** -/
theorem dq_uniform {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {κ Mu Mt Ma Mf ρ : ℝ} (hκ : 0 < κ)
    (hMu : 0 ≤ Mu) (hMt : 0 ≤ Mt) (hMa : 0 ≤ Ma) (hMf : 0 ≤ Mf) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p₀ : V × ℝ) {U Ut A Fr : ℝ → V → ℝ} (hsU : ∀ t, ContDiff ℝ 4 (U t))
    (hsA : ∀ t, ContDiff ℝ 1 (A t)) (hsF : ∀ t, ContDiff ℝ 1 (Fr t))
    (hJU : ∀ j : ℕ, j ≤ 4 →
      HolderBound α (pbox p₀ ρ) (fun p => iteratedFDeriv ℝ j (U p.2) p.1) Mu)
    (hJU1 : HolderBound α (pbox p₀ ρ) (fun p => fderiv ℝ (U p.2) p.1) Mu)
    (hJt : HolderBound α (pbox p₀ ρ) (fun p => Ut p.2 p.1) Mt)
    (hJA : HolderBound α (pbox p₀ ρ) (fun p => A p.2 p.1) Ma)
    (hJA1 : HolderBound α (pbox p₀ ρ) (fun p => fderiv ℝ (A p.2) p.1) Ma)
    (hJF1 : HolderBound α (pbox p₀ ρ) (fun p => fderiv ℝ (Fr p.2) p.1) Mf)
    (hκA : ∀ p ∈ pbox p₀ ρ, κ ≤ A p.2 p.1)
    (hD : ∀ p ∈ pbox p₀ ρ, HasDerivAt (fun t => U t p.1) (Ut p.2 p.1) p.2)
    (hE : ∀ p ∈ pbox p₀ ρ, Ut p.2 p.1 + A p.2 p.1 * Δ (Δ (U p.2)) p.1 = Fr p.2 p.1) (e : V) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ h : ℝ, h ≠ 0 → |h| * ‖e‖ ≤ ρ / 3 → ∀ j : ℕ, j ≤ 4 →
      HolderBound α (pbox p₀ (ρ / 6))
        (fun p => iteratedFDeriv ℝ j (dq h e (U p.2)) p.1) M₁ := by
  obtain ⟨C, hC, HI⟩ := interior_real (V := V) α κ Ma hα hα1 hκ hMa
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = ρ / 3 := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by rw [hqdef]; linarith
  obtain ⟨Bl, hBldef⟩ : ∃ Bl : ℝ, Bl = ‖(bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hBl : 0 ≤ Bl := by
    rw [hBldef]
    exact (bilapL : (V [×4]→L[ℝ] ℝ) →L[ℝ] ℝ).opNorm_nonneg
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  have hFb : 0 ≤ Mf * ‖e‖ + 2 * (Ma * ‖e‖) * (Bl * Mu) := by positivity
  have hUb : 0 ≤ Mu * ‖e‖ := by positivity
  refine ⟨C / q ^ 5 * (Mf * ‖e‖ + 2 * (Ma * ‖e‖) * (Bl * Mu) + Mu * ‖e‖), by positivity,
    fun h hh hhe j hj => ?_⟩
  -- the geometry of the boxes
  have hsub2 : pbox p₀ (2 * q) ⊆ pbox p₀ ρ :=
    pbox_mono p₀ (by positivity) (by rw [hqdef]; linarith)
  have hshift : ∀ p ∈ pbox p₀ (2 * q), ∀ s ∈ Icc (0 : ℝ) 1,
      ((p.1 + (s * h) • e, p.2) : V × ℝ) ∈ pbox p₀ ρ := by
    intro p hp s hs
    have h1 : ‖(s * h) • e‖ ≤ q := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
      have h2 : s * |h| * ‖e‖ ≤ 1 * (|h| * ‖e‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hs.2 (mul_nonneg (abs_nonneg h) he0)
      rw [hqdef]
      linarith
    have h2 := pbox_shift (p₀ := p₀) (by positivity : (0 : ℝ) ≤ 2 * q) hq.le hp h1
    have e3 : 2 * q + q = ρ := by rw [hqdef]; ring
    rwa [e3] at h2
  have hshift1 : ∀ p ∈ pbox p₀ (2 * q), ((p.1 + h • e, p.2) : V × ℝ) ∈ pbox p₀ ρ := by
    intro p hp
    have h1 := hshift p hp 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_mul] at h1
  have hsU1 : ∀ t, ContDiff ℝ 1 (U t) := fun t => (hsU t).of_le (by norm_num)
  have hsUj : ∀ (t : ℝ) (j' : ℕ), j' ≤ 4 → ContDiff ℝ j' (U t) := fun t j' hj' =>
    (hsU t).of_le (by exact_mod_cast hj')
  have hsU4 : ∀ t, ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (U t) := fun t => hsUj t 4 le_rfl
  have key := HI q hq hq1 (p₀.1, p₀.2 + q ^ 4 / 2) (pbox p₀ (2 * q)) (window_mapsTo_pbox p₀ hq)
    (fun p => A p.2 p.1) (hJA.restrict hsub2) (fun p hp => hκA p (hsub2 hp))
    (fun t => dq h e (U t)) (fun t => dq h e (Ut t))
    (fun t z => dq h e (Fr t) z - dq h e (A t) z * Δ (Δ (U t)) (z + h • e))
    (Mf * ‖e‖ + 2 * (Ma * ‖e‖) * (Bl * Mu)) (Mu * ‖e‖) hFb hUb
    (fun t => contDiff_dq (hsU t) h e) ?_ ?_ ?_ ?_ ?_ j hj
  · refine (key.restrict ?_)
    have e6 : ρ / 6 = q / 2 := by rw [hqdef]; ring
    rw [e6]
    exact pbox_subset_window_image p₀ hq
  · -- the time derivative
    intro p hp
    have h1 := hD _ (hshift1 p hp)
    have h2 := hD p (hsub2 hp)
    exact (h1.sub h2).const_mul h⁻¹
  · -- the qualitative bound of the jets
    refine ⟨|h⁻¹| * (Mu + Mu) + |h⁻¹| * (Mt + Mt), by positivity, ?_, ?_⟩
    · intro j' hj'
      have h1 := ((((hJU j' hj').shift (h • e) hshift1).add
        ((hJU j' hj').restrict hsub2).neg).const_smul h⁻¹).mono
        (by nlinarith [abs_nonneg h⁻¹, hMt] :
          |h⁻¹| * (Mu + Mu) ≤ |h⁻¹| * (Mu + Mu) + |h⁻¹| * (Mt + Mt))
      have e1 : (fun p : V × ℝ => iteratedFDeriv ℝ j' (dq h e (U p.2)) p.1)
          = fun p => h⁻¹ • (iteratedFDeriv ℝ j' (U p.2) (p.1 + h • e)
            + -iteratedFDeriv ℝ j' (U p.2) p.1) := by
        funext p
        rw [iteratedFDeriv_dq (hsUj p.2 j' hj') h e, sub_eq_add_neg]
      rw [e1]
      exact h1
    · have h1 := (((hJt.shift (h • e) hshift1).add (hJt.restrict hsub2).neg).const_smul
        h⁻¹).mono (by nlinarith [abs_nonneg h⁻¹, hMu] :
          |h⁻¹| * (Mt + Mt) ≤ |h⁻¹| * (Mu + Mu) + |h⁻¹| * (Mt + Mt))
      have e1 : (fun p : V × ℝ => dq h e (Ut p.2) p.1)
          = fun p => h⁻¹ • (Ut p.2 (p.1 + h • e) + -Ut p.2 p.1) := by
        funext p
        unfold dq
        rw [smul_eq_mul, sub_eq_add_neg]
      rw [e1]
      exact h1
  · -- the source
    have t1 := holderBound_dq hsF hα.le hJF1 hh e hshift
    have t2 := holderBound_dq hsA hα.le hJA1 hh e hshift
    have t3 : HolderBound α (pbox p₀ (2 * q)) (fun p => Δ (Δ (U p.2)) (p.1 + h • e))
        (Bl * Mu) := by
      have h1 := (((hJU 4 le_rfl).shift (h • e) hshift1).clm bilapL)
      rw [← hBldef] at h1
      have e1 : (fun p : V × ℝ => Δ (Δ (U p.2)) (p.1 + h • e))
          = fun p => bilapL (iteratedFDeriv ℝ 4 (U p.2) (p.1 + h • e)) :=
        funext fun p => bilaplacian_eq_bilapL (hsU p.2) _
      rw [e1]
      exact h1
    have t23 := t2.smul t3 (by positivity) (by positivity)
    have t := t1.add t23.neg
    have e1 : (fun p : V × ℝ => dq h e (Fr p.2) p.1
        - dq h e (A p.2) p.1 * Δ (Δ (U p.2)) (p.1 + h • e))
        = fun p => dq h e (Fr p.2) p.1 + -(dq h e (A p.2) p.1 • Δ (Δ (U p.2)) (p.1 + h • e)) := by
      funext p
      rw [smul_eq_mul, sub_eq_add_neg]
    rw [e1]
    exact t
  · -- the supremum
    intro p hp
    have h1 := (holderBound_dq hsU1 hα.le hJU1 hh e hshift).1 p hp
    rwa [Real.norm_eq_abs] at h1
  · -- the equation
    intro p hp
    have hb : Δ (Δ (dq h e (U p.2))) p.1
        = h⁻¹ * (Δ (Δ (U p.2)) (p.1 + h • e) - Δ (Δ (U p.2)) p.1) := by
      rw [bilaplacian_eq_bilapL (contDiff_dq (hsU p.2) h e), iteratedFDeriv_dq (hsU4 p.2) h e,
        map_smul, map_sub, ← bilaplacian_eq_bilapL (hsU p.2), ← bilaplacian_eq_bilapL (hsU p.2),
        smul_eq_mul]
    have h1 := hE _ (hshift1 p hp)
    have h0 := hE p (hsub2 hp)
    dsimp only at h1
    show dq h e (Ut p.2) p.1 + A p.2 p.1 * Δ (Δ (dq h e (U p.2))) p.1
      = dq h e (Fr p.2) p.1 - dq h e (A p.2) p.1 * Δ (Δ (U p.2)) (p.1 + h • e)
    rw [hb]
    unfold dq
    linear_combination h⁻¹ * h1 - h⁻¹ * h0

/-- A positive power is small on a small interval. -/
theorem exists_rpow_small' {p : ℝ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ x₀ → x ^ p ≤ ε := by
  refine ⟨ε ^ p⁻¹, Real.rpow_pos_of_pos hε _, fun x hx hxx => ?_⟩
  calc x ^ p ≤ (ε ^ p⁻¹) ^ p := Real.rpow_le_rpow hx hxx hp.le
    _ = ε := Real.rpow_inv_rpow hε.le hp.ne'

set_option maxHeartbeats 6400000 in
/-- **One spatial derivative.** A solution of `u_t + a Δ² u = f` of the class
of order four, with coefficient and source of the class of order one, has its
first derivatives in the class of order four. -/
theorem Sm.diffquot {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Ω : Set (V × ℝ)} (hΩ : IsOpen Ω)
    {u ut a f : ℝ → V → ℝ} (hu : Sm α Ω 4 u) (hut : Sm α Ω 0 ut)
    (hd : ∀ p ∈ Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2)
    (ha : Sm α Ω 1 a) (hf : Sm α Ω 1 f) (hpos : ∀ p ∈ Ω, 0 < a p.2 p.1)
    (heq : ∀ p ∈ Ω, ut p.2 p.1 + a p.2 p.1 * Δ (Δ (u p.2)) p.1 = f p.2 p.1) (e : V) :
    Sm α Ω 4 (fun t z => fderiv ℝ (u t) z e) := by
  intro p₀ hp₀
  obtain ⟨Nu, U, Mu, hNu, hpu, hMu, hgu, hsu0, hWu⟩ := hu p₀ hp₀
  obtain ⟨Nt, Ut, Mt, hNt, hpt, hMt, hgt, hst, hWt⟩ := hut p₀ hp₀
  obtain ⟨Na, A, Ma, hNa, hpa, hMa, hga, hsa0, hWa⟩ := ha p₀ hp₀
  obtain ⟨Nf, Fr, Mf, hNf, hpf, hMf, hgf, hsf0, hWf⟩ := hf p₀ hp₀
  have hsu : ∀ t, ContDiff ℝ 4 (U t) := fun t => by exact_mod_cast hsu0 t
  have hsa : ∀ t, ContDiff ℝ 1 (A t) := fun t => by exact_mod_cast hsa0 t
  have hsf : ∀ t, ContDiff ℝ 1 (Fr t) := fun t => by exact_mod_cast hsf0 t
  have hsU1 : ∀ t, ContDiff ℝ 1 (U t) := fun t => (hsu t).of_le (by norm_num)
  have hsUj : ∀ (t : ℝ) (j' : ℕ), j' ≤ 4 → ContDiff ℝ j' (U t) := fun t j' hj' =>
    (hsu t).of_le (by exact_mod_cast hj')
  have hopen : IsOpen (Nu ∩ Nt ∩ Na ∩ Nf ∩ Ω) :=
    (((hNu.inter hNt).inter hNa).inter hNf).inter hΩ
  have hmem : p₀ ∈ Nu ∩ Nt ∩ Na ∩ Nf ∩ Ω := ⟨⟨⟨⟨hpu, hpt⟩, hpa⟩, hpf⟩, hp₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen p₀ hmem
  have hA0 : 0 < A p₀.2 p₀.1 := by
    rw [hga p₀ hpa]
    exact hpos p₀ hp₀
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = A p₀.2 p₀.1 / 2 := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    positivity
  obtain ⟨x₀, hx₀, Hx₀⟩ := exists_rpow_small' hα (show 0 < κ / (Ma + 1) by positivity)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (min ε (1 / 4)) (x₀ / 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min (lt_min hε (by norm_num)) (by positivity)
  have hρε : ρ ≤ ε := by
    rw [hρdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := by
    rw [hρdef]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hρx : ρ ≤ x₀ / 2 := by
    rw [hρdef]
    exact min_le_right _ _
  have hρ1 : ρ ≤ 1 := by linarith
  -- the box
  have hbox : pbox p₀ ρ ⊆ Nu ∩ Nt ∩ Na ∩ Nf ∩ Ω := fun p hp =>
    hball (Metric.ball_subset_ball hρε (pbox_subset_ball p₀ hρ.le hρ1 hp))
  have hbu : pbox p₀ ρ ⊆ Nu := fun p hp => (hbox hp).1.1.1.1
  have hbt : pbox p₀ ρ ⊆ Nt := fun p hp => (hbox hp).1.1.1.2
  have hba : pbox p₀ ρ ⊆ Na := fun p hp => (hbox hp).1.1.2
  have hbf : pbox p₀ ρ ⊆ Nf := fun p hp => (hbox hp).1.2
  have hbΩ : pbox p₀ ρ ⊆ Ω := fun p hp => (hbox hp).2
  have hdiam : ∀ p ∈ pbox p₀ ρ, ∀ q ∈ pbox p₀ ρ, pdist p q ≤ 1 := fun p hp q hq =>
    (pdist_le_of_pbox hρ.le hp hq).trans (by linarith)
  -- the Hölder bounds on the box
  have hJU : ∀ j : ℕ, j ≤ 4 →
      HolderBound α (pbox p₀ ρ) (fun p => iteratedFDeriv ℝ j (U p.2) p.1) Mu :=
    fun j hj => holderBound_of_WH (hWu j hj) hbu hdiam
  have hJU1 := holderBound_fderiv (k := 4) (by norm_num) hMu hWu hbu hdiam
  have hJt : HolderBound α (pbox p₀ ρ) (fun p => Ut p.2 p.1) Mt :=
    holderBound_of_WH hWt.value hbt hdiam
  have hJA : HolderBound α (pbox p₀ ρ) (fun p => A p.2 p.1) Ma :=
    holderBound_of_WH hWa.value hba hdiam
  have hJA1 := holderBound_fderiv (k := 1) le_rfl hMa hWa hba hdiam
  have hJF1 := holderBound_fderiv (k := 1) le_rfl hMf hWf hbf hdiam
  -- the lower bound of the coefficient
  have hκA : ∀ p ∈ pbox p₀ ρ, κ ≤ A p.2 p.1 := by
    intro p hp
    have h1 := hJA.2 p hp p₀ (mem_pbox_self p₀ hρ)
    have h2 : pdist p p₀ ≤ x₀ := (pdist_center_le hρ.le hp).trans (by linarith)
    have h3 := Hx₀ _ (pdist_nonneg p p₀) h2
    have h4 : Ma * pdist p p₀ ^ α ≤ κ := by
      calc Ma * pdist p p₀ ^ α ≤ Ma * (κ / (Ma + 1)) := mul_le_mul_of_nonneg_left h3 hMa
        _ ≤ (Ma + 1) * (κ / (Ma + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = κ := by field_simp
    have h5 : |A p.2 p.1 - A p₀.2 p₀.1| ≤ κ := by
      rw [← Real.norm_eq_abs]
      exact h1.trans h4
    have h6 := (abs_le.1 h5).1
    have h7 : A p₀.2 p₀.1 = 2 * κ := by
      rw [hκdef]
      ring
    linarith
  -- the time derivative and the equation of the representatives
  have hD : ∀ p ∈ pbox p₀ ρ, HasDerivAt (fun t => U t p.1) (Ut p.2 p.1) p.2 := by
    intro p hp
    have h1 := hd p (hbΩ hp)
    rw [← hgt p (hbt hp)] at h1
    exact h1.congr_of_eventuallyEq (time_eventuallyEq hNu hgu (hbu hp))
  have hE : ∀ p ∈ pbox p₀ ρ, Ut p.2 p.1 + A p.2 p.1 * Δ (Δ (U p.2)) p.1 = Fr p.2 p.1 := by
    intro p hp
    have hev := slice_eventuallyEq hNu hgu (hbu hp)
    have hb : Δ (Δ (U p.2)) p.1 = Δ (Δ (u p.2)) p.1 :=
      (InnerProductSpace.laplacian_congr_nhds
        (InnerProductSpace.laplacian_congr_nhds hev)).eq_of_nhds
    rw [hgt p (hbt hp), hga p (hba hp), hgf p (hbf hp), hb]
    exact heq p (hbΩ hp)
  obtain ⟨M₁, hM₁, key⟩ := dq_uniform hα hα1 hκ hMu hMt hMa hMf hρ hρ1 p₀ hsu hsa hsf hJU hJU1
    hJt hJA hJA1 hJF1 hκA hD hE e
  -- the dyadic sequence of steps
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  obtain ⟨h₀, hh₀def⟩ : ∃ h₀ : ℝ, h₀ = ρ / (12 * (‖e‖ + 1)) := ⟨_, rfl⟩
  have hh₀ : 0 < h₀ := by
    rw [hh₀def]
    positivity
  have hh₀e : h₀ * ‖e‖ ≤ ρ / 12 := by
    have h1 : h₀ * (12 * (‖e‖ + 1)) = ρ := by
      rw [hh₀def]
      field_simp
    nlinarith
  obtain ⟨hn, hhndef⟩ : ∃ hn : ℕ → ℝ, hn = fun n => h₀ / 2 ^ n := ⟨_, rfl⟩
  have hhn_pos : ∀ n, 0 < hn n := fun n => by
    rw [hhndef]
    positivity
  have hhn_succ : ∀ n, hn (n + 1) = hn n / 2 := fun n => by
    rw [hhndef]
    show h₀ / 2 ^ (n + 1) = h₀ / 2 ^ n / 2
    rw [pow_succ]
    field_simp
  have hhn_le : ∀ n, hn n ≤ h₀ := fun n => by
    rw [hhndef]
    exact div_le_self hh₀.le (one_le_pow₀ (by norm_num))
  have hhn_e : ∀ n, |hn n| * ‖e‖ ≤ ρ / 12 := fun n => by
    rw [abs_of_pos (hhn_pos n)]
    exact (mul_le_mul_of_nonneg_right (hhn_le n) he0).trans hh₀e
  have hhn_tend : Tendsto hn atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul h₀
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    rw [hhndef]
    show h₀ * (1 / 2) ^ n = h₀ / 2 ^ n
    rw [one_div, inv_pow, div_eq_mul_inv]
  have hkey : ∀ n, ∀ j : ℕ, j ≤ 4 → HolderBound α (pbox p₀ (ρ / 6))
      (fun p => iteratedFDeriv ℝ j (dq (hn n) e (U p.2)) p.1) M₁ :=
    fun n j hj => key (hn n) (hhn_pos n).ne' (by linarith [hhn_e n]) j hj
  -- the increments
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (1 / 2 : ℝ) ^ α := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    positivity
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hrn : ∀ n : ℕ, ((1 / 2 : ℝ) ^ n) ^ α = r ^ n := fun n => by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hinc : ∀ n, ∀ p ∈ pbox p₀ (ρ / 12), ∀ j : ℕ, j ≤ 4 →
      ‖iteratedFDeriv ℝ j (fun y => dq (hn (n + 1)) e (U p.2) y - dq (hn n) e (U p.2) y) p.1‖
        ≤ 1 / 2 * (M₁ * r ^ n) := by
    intro n p hp j hj
    have hw : ContDiff ℝ j (dq (hn (n + 1)) e (U p.2)) := contDiff_dq (hsUj p.2 j hj) _ e
    have efun : (fun y => dq (hn (n + 1)) e (U p.2) y - dq (hn n) e (U p.2) y)
        = fun y => (-(hn n / 4)) • dq (hn (n + 1)) e (dq (hn (n + 1)) e (U p.2)) y := by
      funext y
      have h1 := dq_sub_dq_half (U p.2) (hhn_pos n).ne' e y
      rw [← hhn_succ n] at h1
      rw [smul_eq_mul]
      linarith
    rw [efun, iteratedFDeriv_const_smul_apply' (contDiff_dq hw _ e).contDiffAt,
      iteratedFDeriv_dq hw, norm_smul, norm_smul]
    have hP : ((p.1 + hn (n + 1) • e, p.2) : V × ℝ) ∈ pbox p₀ (ρ / 6) := by
      have h1 := pbox_shift (p₀ := p₀) (by positivity : (0 : ℝ) ≤ ρ / 12)
        (by positivity : (0 : ℝ) ≤ ρ / 12) hp (v := hn (n + 1) • e) (by
          rw [norm_smul, Real.norm_eq_abs]
          exact hhn_e (n + 1))
      have e2 : ρ / 12 + ρ / 12 = ρ / 6 := by ring
      rwa [e2] at h1
    have hQ : p ∈ pbox p₀ (ρ / 6) := pbox_mono p₀ (by positivity) (by linarith) hp
    have h2 := (hkey (n + 1) j hj).2 _ hP p hQ
    have hpd : pdist ((p.1 + hn (n + 1) • e, p.2) : V × ℝ) p = hn (n + 1) * ‖e‖ := by
      unfold pdist
      simp [norm_smul, abs_of_pos (hhn_pos (n + 1))]
    rw [hpd] at h2
    have h3 : (hn (n + 1) * ‖e‖) ^ α ≤ r ^ n := by
      have h4 : hn (n + 1) * ‖e‖ ≤ (1 / 2 : ℝ) ^ n := by
        have h5 : hn (n + 1) * ‖e‖ = h₀ * ‖e‖ * ((1 / 2) ^ n * (1 / 2)) := by
          rw [hhndef]
          show h₀ / 2 ^ (n + 1) * ‖e‖ = h₀ * ‖e‖ * ((1 / 2) ^ n * (1 / 2))
          rw [pow_succ, one_div, inv_pow]
          field_simp
        have h6 : (0 : ℝ) < (1 / 2) ^ n := by positivity
        have h7 : 0 ≤ h₀ * ‖e‖ := mul_nonneg hh₀.le he0
        rw [h5]
        nlinarith
      rw [← hrn n]
      exact Real.rpow_le_rpow (mul_nonneg (hhn_pos _).le he0) h4 hα.le
    have hcoef : ‖-(hn n / 4)‖ * ‖(hn (n + 1))⁻¹‖ = 1 / 2 := by
      rw [norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by have := hhn_pos n; positivity),
        abs_of_pos (inv_pos.2 (hhn_pos (n + 1))), hhn_succ n]
      have := (hhn_pos n).ne'
      field_simp
      norm_num
    calc ‖-(hn n / 4)‖ * (‖(hn (n + 1))⁻¹‖ * ‖iteratedFDeriv ℝ j (dq (hn (n + 1)) e (U p.2))
          (p.1 + hn (n + 1) • e) - iteratedFDeriv ℝ j (dq (hn (n + 1)) e (U p.2)) p.1‖)
        = 1 / 2 * ‖iteratedFDeriv ℝ j (dq (hn (n + 1)) e (U p.2))
          (p.1 + hn (n + 1) • e) - iteratedFDeriv ℝ j (dq (hn (n + 1)) e (U p.2)) p.1‖ := by
          rw [← mul_assoc, hcoef]
      _ ≤ 1 / 2 * (M₁ * (hn (n + 1) * ‖e‖) ^ α) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 1 / 2 * (M₁ * r ^ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hM₁) (by norm_num)
  -- the cut-off
  have hμ : 0 < (ρ / 48) ^ 2 := by positivity
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : V → ℝ, ζ = fun z => chiV ((ρ / 48) ^ 2) (z - p₀.1) := ⟨_, rfl⟩
  have hζs : ContDiff ℝ ∞ ζ := by
    rw [hζdef]
    exact (contDiff_chiV _).comp (contDiff_id.sub contDiff_const)
  have hζ4 : ContDiff ℝ 4 ζ := by exact_mod_cast contDiff_infty.1 hζs 4
  have hζ1 : ∀ z : V, ‖z - p₀.1‖ < ρ / 48 → ζ z = 1 := by
    intro z hz
    rw [hζdef]
    exact chiV_of_le hμ (pow_le_pow_left₀ (norm_nonneg _) hz.le 2)
  have hζ0 : ∀ z : V, 2 * (ρ / 48) ^ 2 < ‖z - p₀.1‖ ^ 2 → ζ z = 0 := by
    intro z hz
    rw [hζdef]
    exact chiV_of_ge hμ hz.le
  have hζb : ∀ i : ℕ, ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ i ζ z‖ ≤ B := by
    intro i
    obtain ⟨B, hB, hb⟩ := norm_iteratedFDeriv_chiV_le (V := V) i
    refine ⟨B * (Real.sqrt ((ρ / 48) ^ 2))⁻¹ ^ i, fun z => ?_⟩
    rw [hζdef, iteratedFDeriv_comp_sub]
    exact hb _ hμ _
  choose Bz hBz using hζb
  obtain ⟨Bζ, hBζdef⟩ : ∃ Bζ : ℝ, Bζ = ∑ i ∈ Finset.range 5, |Bz i| := ⟨_, rfl⟩
  have hBζ0 : 0 ≤ Bζ := by
    rw [hBζdef]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBζ : ∀ i : ℕ, i ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ i ζ z‖ ≤ Bζ := by
    intro i hi z
    rw [hBζdef]
    exact (hBz i z).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Bz i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))))
  have hb0 : ∀ n : ℕ, 0 ≤ 1 / 2 * (M₁ * r ^ n) := fun n => by positivity
  -- the limit at a fixed time
  have hlimit : ∀ t : ℝ, |t - p₀.2| < (ρ / 12) ^ 4 →
      ContDiff ℝ 4 (fun z => ζ z * fderiv ℝ (U t) z e) ∧ ∀ j : ℕ, j ≤ 4 → ∀ z,
        Tendsto (fun n => iteratedFDeriv ℝ j (fun y => ζ y * dq (hn n) e (U t) y) z) atTop
          (𝓝 (iteratedFDeriv ℝ j (fun y => ζ y * fderiv ℝ (U t) y e) z)) := by
    intro t ht
    refine contDiff_of_seq (v := fun n y => ζ y * dq (hn n) e (U t) y)
      (b := fun n => 16 * Bζ * (1 / 2 * (M₁ * r ^ n)))
      (fun n => hζ4.mul (contDiff_dq (hsu t) _ e))
      ((((summable_geometric_of_lt_one hr0 hr1).mul_left M₁).mul_left (1 / 2)).mul_left _) ?_ ?_
    · intro n z j hj
      show ‖iteratedFDeriv ℝ j (fun y => ζ y * dq (hn (n + 1)) e (U t) y
        - ζ y * dq (hn n) e (U t) y) z‖ ≤ 16 * Bζ * (1 / 2 * (M₁ * r ^ n))
      have efun : (fun y => ζ y * dq (hn (n + 1)) e (U t) y - ζ y * dq (hn n) e (U t) y)
          = fun y => ζ y * (dq (hn (n + 1)) e (U t) y - dq (hn n) e (U t) y) := by
        funext y
        ring
      rw [efun]
      by_cases hz : ‖z - p₀.1‖ < ρ / 12
      · have hp : ((z, t) : V × ℝ) ∈ pbox p₀ (ρ / 12) := ⟨hz, ht⟩
        have hd4 : ContDiff ℝ 4 (fun y => dq (hn (n + 1)) e (U t) y - dq (hn n) e (U t) y) :=
          (contDiff_dq (hsu t) _ e).sub (contDiff_dq (hsu t) _ e)
        have hL := norm_iteratedFDeriv_mul_le hζ4 hd4 z (n := j) (by exact_mod_cast hj)
        refine hL.trans ?_
        calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ζ z‖
              * ‖iteratedFDeriv ℝ (j - i)
                (fun y => dq (hn (n + 1)) e (U t) y - dq (hn n) e (U t) y) z‖
            ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Bζ * (1 / 2 * (M₁ * r ^ n))) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi4 : i ≤ 4 := by
                have := Finset.mem_range.1 hi
                omega
              have h1 := hBζ i hi4 z
              have h2 := hinc n (z, t) hp (j - i) (by omega)
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hBζ0)
                (Nat.cast_nonneg _)
          _ = (2 : ℝ) ^ j * (Bζ * (1 / 2 * (M₁ * r ^ n))) := by
              rw [← Finset.sum_mul]
              congr 1
              exact_mod_cast Nat.sum_range_choose j
          _ ≤ 16 * Bζ * (1 / 2 * (M₁ * r ^ n)) := by
              have h16 : (2 : ℝ) ^ j ≤ 16 := by
                calc (2 : ℝ) ^ j ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hj
                  _ = 16 := by norm_num
              have h1 := mul_le_mul_of_nonneg_right h16
                (mul_nonneg hBζ0 (hb0 n))
              linarith
      · have hopen2 : IsOpen {y : V | 2 * (ρ / 48) ^ 2 < ‖y - p₀.1‖ ^ 2} :=
          isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm.pow 2)
        have hzmem : z ∈ {y : V | 2 * (ρ / 48) ^ 2 < ‖y - p₀.1‖ ^ 2} := by
          have h2 : ρ / 12 ≤ ‖z - p₀.1‖ := not_lt.1 hz
          have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ρ / 12) h2 2
          show 2 * (ρ / 48) ^ 2 < ‖z - p₀.1‖ ^ 2
          nlinarith
        have hev : (fun y => ζ y * (dq (hn (n + 1)) e (U t) y - dq (hn n) e (U t) y))
            =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hopen2.mem_nhds hzmem] with y hy
          rw [hζ0 y hy, zero_mul]
        rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
        have e0 : iteratedFDeriv ℝ j (fun _ : V => (0 : ℝ)) z = 0 := by simp
        rw [e0, norm_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hBζ0) (hb0 n)
    · intro z
      exact (tendsto_dq ((hsU1 t).differentiable one_ne_zero z) e hhn_tend
        (fun n => (hhn_pos n).ne')).const_mul (ζ z)
  -- the representative of the derivative
  refine ⟨pbox p₀ (ρ / 48),
    fun t z => if |t - p₀.2| < (ρ / 12) ^ 4 then ζ z * fderiv ℝ (U t) z e else 0, M₁,
    isOpen_pbox p₀ _, mem_pbox_self p₀ (by positivity), hM₁, ?_, ?_, ?_⟩
  · intro p hp
    have ht : |p.2 - p₀.2| < (ρ / 12) ^ 4 :=
      hp.2.trans_le (pow_le_pow_left₀ (by positivity) (by linarith) 4)
    have hpρ : p ∈ pbox p₀ ρ := pbox_mono p₀ (by positivity) (by linarith) hp
    show (if |p.2 - p₀.2| < (ρ / 12) ^ 4 then ζ p.1 * fderiv ℝ (U p.2) p.1 e else 0)
      = fderiv ℝ (u p.2) p.1 e
    rw [if_pos ht, hζ1 p.1 hp.1, one_mul, (slice_eventuallyEq hNu hgu (hbu hpρ)).fderiv_eq]
  · intro t
    beta_reduce
    by_cases ht : |t - p₀.2| < (ρ / 12) ^ 4
    · have e1 : (fun z => if |t - p₀.2| < (ρ / 12) ^ 4 then ζ z * fderiv ℝ (U t) z e else 0)
          = fun z => ζ z * fderiv ℝ (U t) z e := by
        funext z
        rw [if_pos ht]
      rw [e1]
      exact_mod_cast (hlimit t ht).1
    · have e1 : (fun z : V => if |t - p₀.2| < (ρ / 12) ^ 4 then ζ z * fderiv ℝ (U t) z e
          else 0) = fun _ => 0 := by
        funext z
        rw [if_neg ht]
      rw [e1]
      exact contDiff_const
  · intro j hj
    refine WH.of_tendsto (f := fun n p => iteratedFDeriv ℝ j (dq (hn n) e (U p.2)) p.1)
      (fun n => ?_) (fun p hp => ?_)
    · exact (WH_of_holderBound (hkey n j hj)).restrict
        (pbox_mono p₀ (by positivity) (by linarith))
    · have ht : |p.2 - p₀.2| < (ρ / 12) ^ 4 :=
        hp.2.trans_le (pow_le_pow_left₀ (by positivity) (by linarith) 4)
      have hevG : (fun z => if |p.2 - p₀.2| < (ρ / 12) ^ 4 then ζ z * fderiv ℝ (U p.2) z e
          else 0) = fun z => ζ z * fderiv ℝ (U p.2) z e := by
        funext z
        rw [if_pos ht]
      show Tendsto (fun n => iteratedFDeriv ℝ j (dq (hn n) e (U p.2)) p.1) atTop
        (𝓝 (iteratedFDeriv ℝ j (fun z => if |p.2 - p₀.2| < (ρ / 12) ^ 4
          then ζ z * fderiv ℝ (U p.2) z e else 0) p.1))
      rw [hevG]
      refine ((hlimit p.2 ht).2 j hj p.1).congr fun n => ?_
      have hev : (fun y => ζ y * dq (hn n) e (U p.2) y) =ᶠ[𝓝 p.1] dq (hn n) e (U p.2) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (show p.1 ∈ Metric.ball p₀.1 (ρ / 48) by
          rw [Metric.mem_ball, dist_eq_norm]
          exact hp.1)] with y hy
        rw [hζ1 y (by rwa [Metric.mem_ball, dist_eq_norm] at hy), one_mul]
      exact (hev.iteratedFDeriv ℝ j).eq_of_nhds

end Calabi.Weighted
