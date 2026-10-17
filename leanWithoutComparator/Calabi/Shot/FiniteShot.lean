import Calabi.Shot.ChainSound
import Calabi.Shot.Data.ChainData

/-!
# The finite shot

The kernel-checked data of `Calabi.Shot.Data` and the soundness of the chain
enclose every trajectory of the clamped profile system on `1 ≤ s ≤ 56`, for
every parameter of the box `|z₁|, |z₂| ≤ 2^-56`.
-/

open Set

namespace Calabi.Shot

open Data

theorem sums_certified : ∀ x ∈ sums, ∃ b, summarize dnum b = some x := by
  intro x hx
  have hx' : x ∈ pairs.map Prod.snd := hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx'
  exact ⟨p.1, pairs_ok p hp⟩

/-- A trajectory on `[1, 56]` is a trajectory on the interval of every block. -/
theorem sums_solves {d : ℝ} {Y : ℝ → State} (hY : SolvesOn d 1 56 Y) :
    ∀ x ∈ sums, SolvesOn d (((x.A : ℝ) - 1) / (x.H : ℝ)) (((x.A : ℝ) + 1) / (x.H : ℝ)) Y := by
  intro x hx
  have hr := List.all_eq_true.1 sums_range x hx
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨hH, -⟩ := summary_bounds (sums_certified x hx)
  have hHR : (0 : ℝ) < (x.H : ℝ) := by exact_mod_cast (show 0 < x.H by omega)
  have h1R : (x.H : ℝ) + 1 ≤ (x.A : ℝ) := by exact_mod_cast (show x.H + 1 ≤ x.A by omega)
  have h2R : (x.A : ℝ) + 1 ≤ 56 * (x.H : ℝ) := by exact_mod_cast h2
  refine hY.mono ?_ ?_
  · rw [le_div_iff₀ hHR]
    linarith
  · rw [div_le_iff₀ hHR]
    linarith

/-- The first block starts at `s = 1`. -/
theorem start_eq_one : ((sum0.A : ℝ) - 1) / (sum0.H : ℝ) = 1 := by
  have h : sum0.A = sum0.H + 1 := by decide
  have hH : 0 < sum0.H := by decide
  have hR : (sum0.A : ℝ) = (sum0.H : ℝ) + 1 := by exact_mod_cast h
  have hHR : (0 : ℝ) < (sum0.H : ℝ) := by exact_mod_cast hH
  rw [div_eq_iff hHR.ne']
  linarith

/-- The last block ends at `s = 56`. -/
theorem stop_eq_56 : ((sum575.A : ℝ) + 1) / (sum575.H : ℝ) = 56 := by
  have h : sum575.A + 1 = 56 * sum575.H := by decide
  have hH : 0 < sum575.H := by decide
  have hR : (sum575.A : ℝ) + 1 = 56 * (sum575.H : ℝ) := by exact_mod_cast h
  have hHR : (0 : ℝ) < (sum575.H : ℝ) := by exact_mod_cast hH
  rw [div_eq_iff hHR.ne']
  linarith

/-- **The finite shot.** For every parameter of the box, a trajectory of the
clamped profile system on `[1, 56]` whose jet at `s = 1` satisfies the first
remainder bound keeps `p ≥ -19/20`, so that the clamp is inactive, and its jet
at `s = 56` satisfies the last remainder bound. -/
theorem finite_shot {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56)
    {Y : ℝ → State} (hY : SolvesOn (param dnum dz1 dz2 z1 z2) 1 56 Y)
    (h0 : Inv frame0 (initial frame0) (blockJet (sum0.H : ℝ) (sum0.A : ℝ) Y (-1)
      - (scaleP : ℝ)⁻¹ • jetVec sum0.start - (scaleU : ℝ)⁻¹ • resp0.app z1 z2)) :
    (∀ σ ∈ Icc (1 : ℝ) 56, -19 / 20 ≤ (Y σ).1) ∧
      Inv frameEnd rhoEnd (blockJet (sum575.H : ℝ) (sum575.A : ℝ) Y 1
        - (scaleP : ℝ)⁻¹ • jetVec sum575.stop - (scaleU : ℝ)⁻¹ • respEnd.app z1 z2) := by
  obtain ⟨hcov, hend⟩ := chain_sound sums_certified chain_ok chain_start chain_end hz1 hz2
    (sums_solves hY) h0
  refine ⟨fun σ hσ => hcov σ ?_, hend⟩
  rw [start_eq_one, stop_eq_56]
  exact hσ

end Calabi.Shot
