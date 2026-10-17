import Calabi.Shot.BlockODE
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp

/-!
# The profile system in the variable `s`

`pfield d` is the clamped profile equation as a first-order system for the jet
`(p, p', p'')` in the original variable `s`. A trajectory restricted to the
`s`-interval of a block and written in the block variable `t`, `s = (A + t) / H`,
is a trajectory of the block system `field H A d`.
-/

open Set

namespace Calabi.Shot

/-- The clamped profile system in the variable `s`, on jets `(p, p', p'')`. -/
noncomputable def pfield (d s : ℝ) (Y : State) : State :=
  (Y.2.1, Y.2.2,
    -(21 / s) * Y.2.2 - 337 / (4 * s ^ 2) * Y.2.1 + 567 / (4 * s ^ 3) * (Y.1 - d) - Ntr Y.1)

/-- `Y` is a trajectory of the clamped profile system on `[a, b]`. -/
def SolvesOn (d a b : ℝ) (Y : ℝ → State) : Prop :=
  ContinuousOn Y (Icc a b) ∧ ∀ s ∈ Ico a b, HasDerivWithinAt Y (pfield d s (Y s)) (Ici s) s

theorem SolvesOn.mono {d a b a' b' : ℝ} {Y : ℝ → State} (h : SolvesOn d a b Y) (ha : a ≤ a')
    (hb : b' ≤ b) : SolvesOn d a' b' Y :=
  ⟨h.1.mono (Icc_subset_Icc ha hb), fun s hs => h.2 s ⟨ha.trans hs.1, hs.2.trans_le hb⟩⟩

/-- The jet of the block `(H, A)` at `t`: the jet at `s = (A + t) / H`, in the
block variable. -/
noncomputable def blockJet (H A : ℝ) (Y : ℝ → State) (t : ℝ) : State :=
  ((Y ((A + t) / H)).1, (Y ((A + t) / H)).2.1 / H, (Y ((A + t) / H)).2.2 / H ^ 2)

theorem blockJet_continuousOn {H A : ℝ} (hH : 0 < H) {Y : ℝ → State}
    (h : ContinuousOn Y (Icc ((A - 1) / H) ((A + 1) / H))) :
    ContinuousOn (blockJet H A Y) (Icc (-1) 1) := by
  have hφ : ContinuousOn (fun u : ℝ => (A + u) / H) (Icc (-1 : ℝ) 1) :=
    ((continuous_const.add continuous_id).div_const H).continuousOn
  have hmaps : MapsTo (fun u : ℝ => (A + u) / H) (Icc (-1 : ℝ) 1)
      (Icc ((A - 1) / H) ((A + 1) / H)) := by
    intro u hu
    exact ⟨div_le_div_of_nonneg_right (by linarith [hu.1]) hH.le,
      div_le_div_of_nonneg_right (by linarith [hu.2]) hH.le⟩
  have hc : ContinuousOn (fun u : ℝ => Y ((A + u) / H)) (Icc (-1 : ℝ) 1) := h.comp hφ hmaps
  exact hc.fst.prodMk ((hc.snd.fst.div_const H).prodMk (hc.snd.snd.div_const (H ^ 2)))

theorem blockJet_hasDeriv {H A d t : ℝ} (hH : 0 < H) (hσ : 0 < A + t) {Y : ℝ → State}
    (h : HasDerivWithinAt Y (pfield d ((A + t) / H) (Y ((A + t) / H))) (Ici ((A + t) / H))
      ((A + t) / H)) :
    HasDerivWithinAt (blockJet H A Y) (field H A d t (blockJet H A Y t)) (Ici t) t := by
  have hH0 : H ≠ 0 := hH.ne'
  have hσ0 : A + t ≠ 0 := hσ.ne'
  have hφ : HasDerivWithinAt (fun u : ℝ => (A + u) / H) (1 / H) (Ici t) t :=
    (((hasDerivAt_id t).const_add A).div_const H).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => (A + u) / H) (Ici t) (Ici ((A + t) / H)) := by
    intro u hu
    exact div_le_div_of_nonneg_right (by linarith [mem_Ici.1 hu]) hH.le
  have hc : HasDerivWithinAt (Y ∘ fun u : ℝ => (A + u) / H)
      ((1 / H) • pfield d ((A + t) / H) (Y ((A + t) / H))) (Ici t) t := h.scomp t hφ hmaps
  have c1 := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivWithinAt t hc
  have c23 := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivWithinAt t hc
  have c2 := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivWithinAt t c23
  have c3 := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivWithinAt t c23
  have hall := c1.prodMk ((c2.div_const H).prodMk (c3.div_const (H ^ 2)))
  refine HasDerivWithinAt.congr_deriv (f := blockJet H A Y) hall ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [ContinuousLinearMap.coe_fst', Prod.smul_fst, smul_eq_mul, pfield, field, blockJet]
    field_simp
  · simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, pfield, field, blockJet]
    field_simp
  · simp only [ContinuousLinearMap.coe_snd', Prod.smul_snd, smul_eq_mul, pfield, field, blockJet]
    field_simp

/-- A trajectory in `s` gives a trajectory of the block system. -/
theorem blockJet_solves {H A d : ℝ} (hH : 0 < H) (hA : 1 < A) {Y : ℝ → State}
    (h : SolvesOn d ((A - 1) / H) ((A + 1) / H) Y) :
    ContinuousOn (blockJet H A Y) (Icc (-1) 1) ∧
      ∀ t ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt (blockJet H A Y)
        (field H A d t (blockJet H A Y t)) (Ici t) t := by
  refine ⟨blockJet_continuousOn hH h.1, fun t ht => ?_⟩
  refine blockJet_hasDeriv hH (by linarith [ht.1]) (h.2 _ ⟨?_, ?_⟩)
  · exact div_le_div_of_nonneg_right (by linarith [ht.1]) hH.le
  · exact div_lt_div_of_pos_right (by linarith [ht.2]) hH

/-- A bound on the block, read in the variable `s`. -/
theorem block_cover {H A : ℝ} (hH : 0 < H) {Y : ℝ → State}
    (h : ∀ t ∈ Icc (-1 : ℝ) 1, -19 / 20 ≤ (blockJet H A Y t).1) {σ : ℝ}
    (hσ : σ ∈ Icc ((A - 1) / H) ((A + 1) / H)) : -19 / 20 ≤ (Y σ).1 := by
  have h1 : A - 1 ≤ σ * H := (div_le_iff₀ hH).1 hσ.1
  have h2 : σ * H ≤ A + 1 := (le_div_iff₀ hH).1 hσ.2
  have e : (A + (σ * H - A)) / H = σ := by
    rw [add_sub_cancel, mul_div_cancel_right₀ _ hH.ne']
  have key := h (σ * H - A) ⟨by linarith, by linarith⟩
  rw [show (blockJet H A Y (σ * H - A)).1 = (Y ((A + (σ * H - A)) / H)).1 from rfl, e] at key
  exact key

/-- Consecutive blocks meet: `(A + 1) / H = (A' - 1) / H'`. -/
theorem layout_eq {H A Hn An g : ℕ} (hH : H = g * Hn) (hA : A + 1 + g = g * An) (hpos : 0 < H) :
    ((A : ℝ) + 1) / (H : ℝ) = ((An : ℝ) - 1) / (Hn : ℝ) := by
  have h2 : 0 < g * Hn := by omega
  have hg : 0 < g := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.zero_mul] at h2
    exact lt_irrefl _ h2
  have hHn : 0 < Hn := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at h2
    exact lt_irrefl _ h2
  have hHR : (H : ℝ) = (g : ℝ) * (Hn : ℝ) := by exact_mod_cast hH
  have hAR : (A : ℝ) + 1 + (g : ℝ) = (g : ℝ) * (An : ℝ) := by exact_mod_cast hA
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hHnR : (0 : ℝ) < (Hn : ℝ) := by exact_mod_cast hHn
  rw [hHR, div_eq_div_iff (mul_pos hgR hHnR).ne' hHnR.ne']
  linear_combination (Hn : ℝ) * hAR

end Calabi.Shot
