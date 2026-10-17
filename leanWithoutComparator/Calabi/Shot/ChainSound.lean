import Calabi.Shot.StepMain
import Calabi.Shot.Physical

/-!
# Soundness of the chain

If the kernel's `chainRun` accepts a list of certified blocks, then every
trajectory of the clamped profile system that starts within the first
remainder bound keeps the clamp inactive on all blocks, and its jet at the
end of the last block lies in the last remainder bound.
-/

open Set

namespace Calabi.Shot

theorem summary_bounds {dnum : Int} {s : Summary} (h : ∃ b, summarize dnum b = some s) :
    16 ≤ s.H ∧ 129 ≤ s.A := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨hok, hH, hA, -⟩ := summarize_some hb
  obtain ⟨h1, h2, -⟩ := Block.ok_spec hok
  rw [hH, hA]
  exact ⟨h1, h2⟩

theorem continues_unpack {s sn : Summary} {g : ℕ} (h : continues s sn g = true) :
    s.H = g * sn.H ∧ s.A + 1 + g = g * sn.A ∧ sn.start.v = s.stop.v ∧
      sn.start.d1 = (g : Int) * s.stop.d1 ∧ sn.start.d2 = (g : Int) * (g : Int) * s.stop.d2 := by
  simp only [continues, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem resc_one (v : State) : resc 1 v = v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [resc, one_mul]

theorem resc_div {g Hn y : ℝ} (hg : g ≠ 0) (hHn : Hn ≠ 0) : g * (y / (g * Hn)) = y / Hn := by
  field_simp

theorem resc_div_sq {g Hn y : ℝ} (hg : g ≠ 0) (hHn : Hn ≠ 0) :
    g * g * (y / (g * Hn) ^ 2) = y / Hn ^ 2 := by
  field_simp

/-- The jet at the end of a block is the jet at the start of the next one. -/
theorem resc_blockJet {H A Hn An g : ℕ} (hH : H = g * Hn) (hA : A + 1 + g = g * An) (hpos : 0 < H)
    (Y : ℝ → State) :
    resc (g : ℝ) (blockJet (H : ℝ) (A : ℝ) Y 1) = blockJet (Hn : ℝ) (An : ℝ) Y (-1) := by
  have h2 : 0 < g * Hn := by omega
  have hg : (g : ℝ) ≠ 0 := by
    have : g ≠ 0 := fun h0 => by
      rw [h0, Nat.zero_mul] at h2
      exact lt_irrefl _ h2
    exact_mod_cast this
  have hHn : (Hn : ℝ) ≠ 0 := by
    have : Hn ≠ 0 := fun h0 => by
      rw [h0, Nat.mul_zero] at h2
      exact lt_irrefl _ h2
    exact_mod_cast this
  have hHR : (H : ℝ) = (g : ℝ) * (Hn : ℝ) := by exact_mod_cast hH
  have hs : ((An : ℝ) + -1) / (Hn : ℝ) = ((A : ℝ) + 1) / (H : ℝ) := by
    rw [layout_eq hH hA hpos]
    ring
  unfold blockJet
  rw [hs]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show (g : ℝ) * ((Y (((A : ℝ) + 1) / (H : ℝ))).2.1 / (H : ℝ)) =
      (Y (((A : ℝ) + 1) / (H : ℝ))).2.1 / (Hn : ℝ)
    generalize (Y (((A : ℝ) + 1) / (H : ℝ))).2.1 = y
    rw [hHR]
    exact resc_div hg hHn
  · show (g : ℝ) * (g : ℝ) * ((Y (((A : ℝ) + 1) / (H : ℝ))).2.2 / (H : ℝ) ^ 2) =
      (Y (((A : ℝ) + 1) / (H : ℝ))).2.2 / (Hn : ℝ) ^ 2
    generalize (Y (((A : ℝ) + 1) / (H : ℝ))).2.2 = y
    rw [hHR]
    exact resc_div_sq hg hHn

theorem resc_jetVec {s sn : Summary} {g : ℕ} (hv : sn.start.v = s.stop.v)
    (h1 : sn.start.d1 = (g : Int) * s.stop.d1)
    (h2 : sn.start.d2 = (g : Int) * (g : Int) * s.stop.d2) :
    resc (g : ℝ) (jetVec s.stop) = jetVec sn.start := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((s.stop.v : Int) : ℝ) = ((sn.start.v : Int) : ℝ)
    rw [hv]
  · show (g : ℝ) * ((s.stop.d1 : Int) : ℝ) = ((sn.start.d1 : Int) : ℝ)
    rw [h1]
    push_cast
    ring
  · show (g : ℝ) * (g : ℝ) * ((s.stop.d2 : Int) : ℝ) = ((sn.start.d2 : Int) : ℝ)
    rw [h2]
    push_cast
    ring

/-- One block of the chain, for a trajectory in the variable `s`. -/
theorem block_step {dnum dz1 dz2 : Int} {s : Summary} {g : ℕ} {B Bn : Mat3} {L Ln : Mat32}
    {ρ ρn : Nat3} (hs : ∃ b, summarize dnum b = some s)
    (hstep : step dz1 dz2 s g B Bn L Ln ρ = some ρn)
    {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56) {Y : ℝ → State}
    (hY : SolvesOn (param dnum dz1 dz2 z1 z2) (((s.A : ℝ) - 1) / (s.H : ℝ))
      (((s.A : ℝ) + 1) / (s.H : ℝ)) Y)
    (hinv : Inv B ρ (blockJet (s.H : ℝ) (s.A : ℝ) Y (-1) - (scaleP : ℝ)⁻¹ • jetVec s.start
      - (scaleU : ℝ)⁻¹ • L.app z1 z2)) :
    (∀ σ ∈ Icc (((s.A : ℝ) - 1) / (s.H : ℝ)) (((s.A : ℝ) + 1) / (s.H : ℝ)),
        -19 / 20 ≤ (Y σ).1) ∧
      Inv Bn ρn (resc (g : ℝ) (blockJet (s.H : ℝ) (s.A : ℝ) Y 1)
        - (scaleP : ℝ)⁻¹ • resc (g : ℝ) (jetVec s.stop) - (scaleU : ℝ)⁻¹ • Ln.app z1 z2) := by
  obtain ⟨hH, hA⟩ := summary_bounds hs
  have hHR : (0 : ℝ) < (s.H : ℝ) := by exact_mod_cast (show 0 < s.H by omega)
  have hAR : (1 : ℝ) < (s.A : ℝ) := by exact_mod_cast (show 1 < s.A by omega)
  obtain ⟨hXc, hXd⟩ := blockJet_solves hHR hAR hY
  have h0 : blockJet (s.H : ℝ) (s.A : ℝ) Y (-1) =
      (scaleP : ℝ)⁻¹ • jetVec s.start + (scaleU : ℝ)⁻¹ • L.app z1 z2
        + (blockJet (s.H : ℝ) (s.A : ℝ) Y (-1) - (scaleP : ℝ)⁻¹ • jetVec s.start
          - (scaleU : ℝ)⁻¹ • L.app z1 z2) := by
    abel
  obtain ⟨hpos, hinvN⟩ := step_sound hs hstep hz1 hz2 hinv hXc hXd h0
  exact ⟨fun σ hσ => block_cover hHR hpos hσ, hinvN⟩

theorem chain_sound_aux {dnum dz1 dz2 : Int} {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56)
    (hz2 : |z2| ≤ 1 / 2 ^ 56) {Y : ℝ → State} :
    ∀ (rest : List Summary) (s : Summary) (B : Mat3) (frames : List Mat3) (L : Mat32)
      (Ls : List Mat32) (ρ ρe : Nat3) (se : Summary) (Be : Mat3) (Le : Mat32),
      (∀ x ∈ s :: rest, ∃ b, summarize dnum b = some x) →
      chainRun dz1 dz2 (s :: rest) (B :: frames) (L :: Ls) ρ = some ρe →
      chainEnd (s :: rest) (B :: frames) (L :: Ls) = some (se, Be, Le) →
      (∀ x ∈ s :: rest, SolvesOn (param dnum dz1 dz2 z1 z2) (((x.A : ℝ) - 1) / (x.H : ℝ))
        (((x.A : ℝ) + 1) / (x.H : ℝ)) Y) →
      Inv B ρ (blockJet (s.H : ℝ) (s.A : ℝ) Y (-1) - (scaleP : ℝ)⁻¹ • jetVec s.start
        - (scaleU : ℝ)⁻¹ • L.app z1 z2) →
      (∀ σ ∈ Icc (((s.A : ℝ) - 1) / (s.H : ℝ)) (((se.A : ℝ) + 1) / (se.H : ℝ)),
          -19 / 20 ≤ (Y σ).1) ∧
        Inv Be ρe (blockJet (se.H : ℝ) (se.A : ℝ) Y 1 - (scaleP : ℝ)⁻¹ • jetVec se.stop
          - (scaleU : ℝ)⁻¹ • Le.app z1 z2) := by
  intro rest
  induction rest with
  | nil =>
    intro s B frames L Ls ρ ρe se Be Le hcert hrun hend hsol hinv
    cases frames with
    | nil => simp [chainRun] at hrun
    | cons Bn frames =>
      cases Ls with
      | nil => simp [chainRun] at hrun
      | cons Ln Ls =>
        simp only [chainRun] at hrun
        simp only [chainEnd, Option.some.injEq, Prod.mk.injEq] at hend
        obtain ⟨rfl, rfl, rfl⟩ := hend
        obtain ⟨hcov, hinvN⟩ := block_step (hcert _ (List.mem_cons_self ..)) hrun hz1 hz2
          (hsol _ (List.mem_cons_self ..)) hinv
        simp only [Nat.cast_one, resc_one] at hinvN
        exact ⟨hcov, hinvN⟩
  | cons sn rest ih =>
    intro s B frames L Ls ρ ρe se Be Le hcert hrun hend hsol hinv
    cases frames with
    | nil => simp [chainRun] at hrun
    | cons Bn frames =>
      cases Ls with
      | nil => simp [chainRun] at hrun
      | cons Ln Ls =>
        simp only [chainRun] at hrun
        split at hrun
        · rename_i hcont
          split at hrun
          · rename_i ρn hstep
            obtain ⟨hH, hA, hv, h1, h2⟩ := continues_unpack hcont
            obtain ⟨hH16, -⟩ := summary_bounds (hcert s (List.mem_cons_self ..))
            have hpos : 0 < s.H := by omega
            obtain ⟨hcov, hinvN⟩ := block_step (hcert s (List.mem_cons_self ..)) hstep hz1 hz2
              (hsol s (List.mem_cons_self ..)) hinv
            rw [resc_blockJet hH hA hpos Y, resc_jetVec hv h1 h2] at hinvN
            have hend' : chainEnd (sn :: rest) (Bn :: frames) (Ln :: Ls) = some (se, Be, Le) := by
              simpa only [chainEnd] using hend
            obtain ⟨hcov', hinvE⟩ := ih sn Bn frames Ln Ls ρn ρe se Be Le
              (fun x hx => hcert x (List.mem_cons_of_mem _ hx)) hrun hend'
              (fun x hx => hsol x (List.mem_cons_of_mem _ hx)) hinvN
            refine ⟨fun σ hσ => ?_, hinvE⟩
            rcases le_total σ (((s.A : ℝ) + 1) / (s.H : ℝ)) with hle | hge
            · exact hcov σ ⟨hσ.1, hle⟩
            · refine hcov' σ ⟨?_, hσ.2⟩
              rw [← layout_eq hH hA hpos]
              exact hge
          · cases hrun
        · cases hrun

/-- **Soundness of the chain.** `s0`, `B0`, `L0` are the first summary, frame
and response; `se`, `Be`, `Le` the last summary and the frame and response
that follow it. -/
theorem chain_sound {dnum dz1 dz2 : Int} {sums : List Summary} {frames : List Mat3}
    {Ls : List Mat32} {ρ ρe : Nat3} {s0 se : Summary} {B0 Be : Mat3} {L0 Le : Mat32}
    (hcert : ∀ x ∈ sums, ∃ b, summarize dnum b = some x)
    (hrun : chainRun dz1 dz2 sums frames Ls ρ = some ρe)
    (hstart : chainStart sums frames Ls = some (s0, B0, L0))
    (hend : chainEnd sums frames Ls = some (se, Be, Le))
    {z1 z2 : ℝ} (hz1 : |z1| ≤ 1 / 2 ^ 56) (hz2 : |z2| ≤ 1 / 2 ^ 56) {Y : ℝ → State}
    (hsol : ∀ x ∈ sums, SolvesOn (param dnum dz1 dz2 z1 z2) (((x.A : ℝ) - 1) / (x.H : ℝ))
      (((x.A : ℝ) + 1) / (x.H : ℝ)) Y)
    (hinv : Inv B0 ρ (blockJet (s0.H : ℝ) (s0.A : ℝ) Y (-1) - (scaleP : ℝ)⁻¹ • jetVec s0.start
      - (scaleU : ℝ)⁻¹ • L0.app z1 z2)) :
    (∀ σ ∈ Icc (((s0.A : ℝ) - 1) / (s0.H : ℝ)) (((se.A : ℝ) + 1) / (se.H : ℝ)),
        -19 / 20 ≤ (Y σ).1) ∧
      Inv Be ρe (blockJet (se.H : ℝ) (se.A : ℝ) Y 1 - (scaleP : ℝ)⁻¹ • jetVec se.stop
        - (scaleU : ℝ)⁻¹ • Le.app z1 z2) := by
  cases sums with
  | nil => simp [chainStart] at hstart
  | cons s rest =>
    cases frames with
    | nil => simp [chainStart] at hstart
    | cons B frames =>
      cases Ls with
      | nil => simp [chainStart] at hstart
      | cons L Ls =>
        simp only [chainStart, Option.some.injEq, Prod.mk.injEq] at hstart
        obtain ⟨rfl, rfl, rfl⟩ := hstart
        exact chain_sound_aux hz1 hz2 rest _ _ frames _ Ls ρ ρe se Be Le hcert hrun hend hsol
          hinv

/-- A jet within `2^-112` of the certified one satisfies the first remainder bound. -/
theorem inv_initial (B : Mat3) {r : State} (h1 : |r.1| ≤ 1 / 2 ^ 112)
    (h2 : |r.2.1| ≤ 1 / 2 ^ 112) (h3 : |r.2.2| ≤ 1 / 2 ^ 112) : Inv B (initial B) r := by
  have e : ((initTol : ℕ) : ℝ) / (scaleE : ℝ) = 1 / 2 ^ 112 := by
    unfold initTol scaleE
    norm_num
  have k1 : |r.1| ≤ ((initTol : ℕ) : ℝ) / (scaleE : ℝ) := by rw [e]; exact h1
  have k2 : |r.2.1| ≤ ((initTol : ℕ) : ℝ) / (scaleE : ℝ) := by rw [e]; exact h2
  have k3 : |r.2.2| ≤ ((initTol : ℕ) : ℝ) / (scaleE : ℝ) := by rw [e]; exact h3
  exact B.adj.abs_app_le (ν := ⟨initTol, initTol, initTol⟩) k1 k2 k3

end Calabi.Shot
