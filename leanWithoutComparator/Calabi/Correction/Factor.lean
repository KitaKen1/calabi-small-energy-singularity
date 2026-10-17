import Calabi.Radial.Basic

/-!
# The compact operator as a product of two shifted Laplacians

On functions of the momentum coordinate `x = |z|²`, the Laplacian of the round
sphere `S²³ ⊂ ℝ¹⁸ × ℝ⁶` is `Δ_S f = 4 x (1 - x) f″ + (36 - 48 x) f′`
(`LSd 18`), and the operator `A H = K(H)″` of the Calabi flow is

  `16 A = (Δ_S - 40) (Δ_S - 72)`   (`sixteen_Aop`).

With the flat radial Laplacian `Δ f = 4 x f″ + 2 d f′` of `ℝᵈ` (`lapR d`) and
the Euler operator `E f = 2 x f′` (`eulR`), `Δ_S = (1 - x) Δ - m E`,
`m = 24 - d`, and (`LSd_LSd`)

  `Δ_S² = (1 - x)² Δ² - (4 + 2 m) (1 - x) E Δ + ((48 + 2 m) x - 48) Δ + m² E²`.

So the principal part of `16 A` is `(1 - x)²` times the flat bilaplacian of
`ℝ¹⁸`, and the remainder has order three (`sixteen_Aop_flat`). At the other end
`x = 1` the same holds with `ℝ⁶` in place of `ℝ¹⁸` (`sixteen_Aop_refl`): the
reflection `x ↦ 1 - x` exchanges `LSd 18` and `LSd 6`.

This is the form of Lemma 2.2 of the manuscript used for the linear theory:
in the two flat charts the Calabi flow is a fourth-order parabolic equation
whose principal part is a positive multiple of the flat bilaplacian.
-/

open Set
open scoped ContDiff

namespace Calabi.Radial

/-! ### Polynomial coefficients -/

/-- A polynomial of degree at most four. -/
def pol (a0 a1 a2 a3 a4 y : ℝ) : ℝ := a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4

theorem hasDerivAt_pol (a0 a1 a2 a3 a4 x : ℝ) :
    HasDerivAt (pol a0 a1 a2 a3 a4) (pol a1 (2 * a2) (3 * a3) (4 * a4) 0 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => a1 * y) a1 x := by
    simpa using (hasDerivAt_id' x).const_mul a1
  have h2 : HasDerivAt (fun y : ℝ => a2 * y ^ 2) (a2 * (2 * x)) x := by
    have h := (hasDerivAt_pow 2 x).const_mul a2
    refine h.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun y : ℝ => a3 * y ^ 3) (a3 * (3 * x ^ 2)) x := by
    have h := (hasDerivAt_pow 3 x).const_mul a3
    refine h.congr_deriv ?_
    norm_num
  have h4 : HasDerivAt (fun y : ℝ => a4 * y ^ 4) (a4 * (4 * x ^ 3)) x := by
    have h := (hasDerivAt_pow 4 x).const_mul a4
    refine h.congr_deriv ?_
    norm_num
  have h := ((((hasDerivAt_const x a0).fun_add h1).fun_add h2).fun_add h3).fun_add h4
  show HasDerivAt (fun y : ℝ => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4) _ x
  refine h.congr_deriv ?_
  unfold pol
  ring

theorem contDiff_pol (a0 a1 a2 a3 a4 : ℝ) : ContDiff ℝ ∞ (pol a0 a1 a2 a3 a4) := by
  show ContDiff ℝ ∞ (fun y : ℝ => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4)
  fun_prop

/-! ### Derivatives on `[0, 1]` -/

theorem hasDerivWithinAt_D {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt f (D f x) (Icc 0 1) x :=
  (hf.differentiableOn (by simp) x hx).hasDerivWithinAt

/-- The derivative on `[0, 1]` of `p₀ f + p₁ Df + p₂ D²f + p₃ D³f`. -/
theorem hasDerivWithinAt_comb {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1))
    {p0 p1 p2 p3 : ℝ → ℝ} {q0 q1 q2 q3 x : ℝ}
    (h0 : HasDerivAt p0 q0 x) (h1 : HasDerivAt p1 q1 x) (h2 : HasDerivAt p2 q2 x)
    (h3 : HasDerivAt p3 q3 x) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun y => p0 y * f y + p1 y * D f y + p2 y * D (D f) y + p3 y * D (D (D f)) y)
      (q0 * f x + (p0 x + q1) * D f x + (p1 x + q2) * D (D f) x
        + (p2 x + q3) * D (D (D f)) x + p3 x * D (D (D (D f))) x) (Icc 0 1) x := by
  have hf1 := contDiffOn_D hf
  have hf2 := contDiffOn_D hf1
  have hf3 := contDiffOn_D hf2
  have h := (((h0.hasDerivWithinAt.fun_mul (hasDerivWithinAt_D hf hx)).fun_add
    (h1.hasDerivWithinAt.fun_mul (hasDerivWithinAt_D hf1 hx))).fun_add
    (h2.hasDerivWithinAt.fun_mul (hasDerivWithinAt_D hf2 hx))).fun_add
    (h3.hasDerivWithinAt.fun_mul (hasDerivWithinAt_D hf3 hx))
  refine h.congr_deriv ?_
  ring

/-- Smoothness of a combination with smooth coefficients. -/
theorem contDiffOn_comb {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {p0 p1 p2 : ℝ → ℝ}
    (h0 : ContDiff ℝ ∞ p0) (h1 : ContDiff ℝ ∞ p1) (h2 : ContDiff ℝ ∞ p2) :
    ContDiffOn ℝ ∞ (fun y => p0 y * f y + p1 y * D f y + p2 y * D (D f) y) (Icc 0 1) :=
  ((h0.contDiffOn.mul hf).add (h1.contDiffOn.mul (contDiffOn_D hf))).add
    (h2.contDiffOn.mul (contDiffOn_D (contDiffOn_D hf)))

/-! ### The operators -/

/-- The Laplacian of the sphere `S²³ ⊂ ℝᵈ × ℝ^{24 - d}` on functions of
`x = |z|²`, `z ∈ ℝᵈ`: `4 x (1 - x) f″ + (2 d - 48 x) f′`. -/
noncomputable def LSd (d : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  4 * x * (1 - x) * D (D f) x + (2 * d - 48 * x) * D f x

/-- The flat Laplacian of `ℝᵈ` on functions of `x = |z|²`: `4 x f″ + 2 d f′`. -/
noncomputable def lapR (d : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := 4 * x * D (D f) x + 2 * d * D f x

/-- The Euler operator `z · ∇` on functions of `x = |z|²`: `2 x f′`. -/
noncomputable def eulR (f : ℝ → ℝ) (x : ℝ) : ℝ := 2 * x * D f x

theorem LSd_eq (d : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    LSd d f x = (1 - x) * lapR d f x - (24 - d) * eulR f x := by
  unfold LSd lapR eulR
  ring

section Smooth

variable {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1))

include hf

theorem contDiffOn_LSd (d : ℝ) : ContDiffOn ℝ ∞ (LSd d f) (Icc 0 1) := by
  have h := contDiffOn_comb hf (contDiff_pol 0 0 0 0 0) (contDiff_pol (2 * d) (-48) 0 0 0)
    (contDiff_pol 0 4 (-4) 0 0)
  refine h.congr fun y _ => ?_
  unfold LSd pol
  ring

theorem contDiffOn_lapR (d : ℝ) : ContDiffOn ℝ ∞ (lapR d f) (Icc 0 1) := by
  have h := contDiffOn_comb hf (contDiff_pol 0 0 0 0 0) (contDiff_pol (2 * d) 0 0 0 0)
    (contDiff_pol 0 4 0 0 0)
  refine h.congr fun y _ => ?_
  unfold lapR pol
  ring

theorem contDiffOn_eulR : ContDiffOn ℝ ∞ (eulR f) (Icc 0 1) := by
  have h := contDiffOn_comb hf (contDiff_pol 0 0 0 0 0) (contDiff_pol 0 2 0 0 0)
    (contDiff_pol 0 0 0 0 0)
  refine h.congr fun y _ => ?_
  unfold eulR pol
  ring

theorem contDiffOn_Kop : ContDiffOn ℝ ∞ (Kop f) (Icc 0 1) := by
  have h := contDiffOn_comb hf (contDiff_pol 56 (-144) 90 0 0) (contDiff_pol 0 16 (-36) 20 0)
    (contDiff_pol 0 0 1 (-2) 1)
  refine h.congr fun y _ => ?_
  unfold Kop pol
  ring

/-- The first two derivatives of `LSd d f`. -/
theorem D_LSd (d : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    D (LSd d f) x = -48 * D f x + (2 * d + 4 - 56 * x) * D (D f) x
        + (4 * x - 4 * x ^ 2) * D (D (D f)) x ∧
      D (D (LSd d f)) x = -104 * D (D f) x + (2 * d + 8 - 64 * x) * D (D (D f)) x
        + (4 * x - 4 * x ^ 2) * D (D (D (D f))) x := by
  have e1 : ∀ y ∈ Icc (0 : ℝ) 1, D (LSd d f) y
      = pol 0 0 0 0 0 y * f y + pol (-48) 0 0 0 0 y * D f y
        + pol (2 * d + 4) (-56) 0 0 0 y * D (D f) y + pol 0 4 (-4) 0 0 y * D (D (D f)) y := by
    intro y hy
    have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 0 0 0 0 0 y)
      (hasDerivAt_pol (2 * d) (-48) 0 0 0 y) (hasDerivAt_pol 0 4 (-4) 0 0 y)
      (hasDerivAt_pol 0 0 0 0 0 y) hy
    have h' : HasDerivWithinAt (LSd d f) _ (Icc 0 1) y :=
      h.congr (fun w _ => by unfold LSd pol; ring) (by unfold LSd pol; ring)
    have e : D (LSd d f) y = _ := h'.derivWithin (uniqueDiffOn_Icc_zero_one y hy)
    rw [e]
    unfold pol
    ring
  refine ⟨?_, ?_⟩
  · rw [e1 x hx]
    unfold pol
    ring
  · have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 0 0 0 0 0 x)
      (hasDerivAt_pol (-48) 0 0 0 0 x) (hasDerivAt_pol (2 * d + 4) (-56) 0 0 0 x)
      (hasDerivAt_pol 0 4 (-4) 0 0 x) hx
    have e2 : D (D (LSd d f)) x = derivWithin (fun y => pol 0 0 0 0 0 y * f y
        + pol (-48) 0 0 0 0 y * D f y + pol (2 * d + 4) (-56) 0 0 0 y * D (D f) y
        + pol 0 4 (-4) 0 0 y * D (D (D f)) y) (Icc 0 1) x := derivWithin_congr e1 (e1 x hx)
    rw [e2, h.derivWithin (uniqueDiffOn_Icc_zero_one x hx)]
    unfold pol
    ring

/-- The first two derivatives of `lapR d f`. -/
theorem D_lapR (d : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    D (lapR d f) x = (2 * d + 4) * D (D f) x + 4 * x * D (D (D f)) x ∧
      D (D (lapR d f)) x = (2 * d + 8) * D (D (D f)) x + 4 * x * D (D (D (D f))) x := by
  have e1 : ∀ y ∈ Icc (0 : ℝ) 1, D (lapR d f) y
      = pol 0 0 0 0 0 y * f y + pol 0 0 0 0 0 y * D f y
        + pol (2 * d + 4) 0 0 0 0 y * D (D f) y + pol 0 4 0 0 0 y * D (D (D f)) y := by
    intro y hy
    have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 0 0 0 0 0 y)
      (hasDerivAt_pol (2 * d) 0 0 0 0 y) (hasDerivAt_pol 0 4 0 0 0 y)
      (hasDerivAt_pol 0 0 0 0 0 y) hy
    have h' : HasDerivWithinAt (lapR d f) _ (Icc 0 1) y :=
      h.congr (fun w _ => by unfold lapR pol; ring) (by unfold lapR pol; ring)
    have e : D (lapR d f) y = _ := h'.derivWithin (uniqueDiffOn_Icc_zero_one y hy)
    rw [e]
    unfold pol
    ring
  refine ⟨?_, ?_⟩
  · rw [e1 x hx]
    unfold pol
    ring
  · have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 0 0 0 0 0 x)
      (hasDerivAt_pol 0 0 0 0 0 x) (hasDerivAt_pol (2 * d + 4) 0 0 0 0 x)
      (hasDerivAt_pol 0 4 0 0 0 x) hx
    have e2 : D (D (lapR d f)) x = derivWithin (fun y => pol 0 0 0 0 0 y * f y
        + pol 0 0 0 0 0 y * D f y + pol (2 * d + 4) 0 0 0 0 y * D (D f) y
        + pol 0 4 0 0 0 y * D (D (D f)) y) (Icc 0 1) x := derivWithin_congr e1 (e1 x hx)
    rw [e2, h.derivWithin (uniqueDiffOn_Icc_zero_one x hx)]
    unfold pol
    ring

/-- The derivative of `eulR f`. -/
theorem D_eulR {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    D (eulR f) x = 2 * D f x + 2 * x * D (D f) x := by
  have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 0 0 0 0 0 x)
    (hasDerivAt_pol 0 2 0 0 0 x) (hasDerivAt_pol 0 0 0 0 0 x)
    (hasDerivAt_pol 0 0 0 0 0 x) hx
  have h' : HasDerivWithinAt (eulR f) _ (Icc 0 1) x :=
    h.congr (fun w _ => by unfold eulR pol; ring) (by unfold eulR pol; ring)
  have e : D (eulR f) x = _ := h'.derivWithin (uniqueDiffOn_Icc_zero_one x hx)
  rw [e]
  unfold pol
  ring

/-- `Δ_S² f` with the derivatives expanded. -/
theorem LSd_LSd_eq (d : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LSd d (LSd d f) x = 4 * x * (1 - x) * (-104 * D (D f) x
          + (2 * d + 8 - 64 * x) * D (D (D f)) x + (4 * x - 4 * x ^ 2) * D (D (D (D f))) x)
        + (2 * d - 48 * x) * (-48 * D f x + (2 * d + 4 - 56 * x) * D (D f) x
          + (4 * x - 4 * x ^ 2) * D (D (D f)) x) := by
  obtain ⟨e1, e2⟩ := D_LSd hf d hx
  show 4 * x * (1 - x) * D (D (LSd d f)) x + (2 * d - 48 * x) * D (LSd d f) x = _
  rw [e1, e2]

/-- **The square of the spherical Laplacian in the flat chart**:
`Δ_S² = (1 - x)² Δ² - (4 + 2 m) (1 - x) E Δ + ((48 + 2 m) x - 48) Δ + m² E²`,
`m = 24 - d`. -/
theorem LSd_LSd (d : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LSd d (LSd d f) x = (1 - x) ^ 2 * lapR d (lapR d f) x
      - (4 + 2 * (24 - d)) * (1 - x) * eulR (lapR d f) x
      + ((48 + 2 * (24 - d)) * x - 48) * lapR d f x + (24 - d) ^ 2 * eulR (eulR f) x := by
  obtain ⟨l1, l2⟩ := D_lapR hf d hx
  have he := D_eulR hf hx
  rw [LSd_LSd_eq hf d hx]
  show _ = (1 - x) ^ 2 * (4 * x * D (D (lapR d f)) x + 2 * d * D (lapR d f) x)
    - (4 + 2 * (24 - d)) * (1 - x) * (2 * x * D (lapR d f) x)
    + ((48 + 2 * (24 - d)) * x - 48) * (4 * x * D (D f) x + 2 * d * D f x)
    + (24 - d) ^ 2 * (2 * x * D (eulR f) x)
  rw [l1, l2, he]
  ring

/-- `A H = K(H)″` with the derivatives expanded. -/
theorem Aop_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Aop f x = x ^ 2 * (1 - x) ^ 2 * D (D (D (D f))) x
      + (20 * x - 48 * x ^ 2 + 28 * x ^ 3) * D (D (D f)) x
      + (90 - 300 * x + 222 * x ^ 2) * D (D f) x + (-360 + 480 * x) * D f x + 180 * f x := by
  have e1 : ∀ y ∈ Icc (0 : ℝ) 1, D (Kop f) y
      = pol (-144) 180 0 0 0 y * f y + pol 72 (-216) 150 0 0 y * D f y
        + pol 0 18 (-42) 24 0 y * D (D f) y + pol 0 0 1 (-2) 1 y * D (D (D f)) y := by
    intro y hy
    have h := hasDerivWithinAt_comb hf (hasDerivAt_pol 56 (-144) 90 0 0 y)
      (hasDerivAt_pol 0 16 (-36) 20 0 y) (hasDerivAt_pol 0 0 1 (-2) 1 y)
      (hasDerivAt_pol 0 0 0 0 0 y) hy
    have h' : HasDerivWithinAt (Kop f) _ (Icc 0 1) y :=
      h.congr (fun w _ => by unfold Kop pol; ring) (by unfold Kop pol; ring)
    have e : D (Kop f) y = _ := h'.derivWithin (uniqueDiffOn_Icc_zero_one y hy)
    rw [e]
    unfold pol
    ring
  have h := hasDerivWithinAt_comb hf (hasDerivAt_pol (-144) 180 0 0 0 x)
    (hasDerivAt_pol 72 (-216) 150 0 0 x) (hasDerivAt_pol 0 18 (-42) 24 0 x)
    (hasDerivAt_pol 0 0 1 (-2) 1 x) hx
  have e2 : Aop f x = derivWithin (fun y => pol (-144) 180 0 0 0 y * f y
      + pol 72 (-216) 150 0 0 y * D f y + pol 0 18 (-42) 24 0 y * D (D f) y
      + pol 0 0 1 (-2) 1 y * D (D (D f)) y) (Icc 0 1) x := derivWithin_congr e1 (e1 x hx)
  rw [e2, h.derivWithin (uniqueDiffOn_Icc_zero_one x hx)]
  unfold pol
  ring

/-- **The compact operator is a product of two shifted Laplacians of the
sphere**: `16 A = (Δ_S - 40) (Δ_S - 72)`. -/
theorem sixteen_Aop {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    16 * Aop f x = LSd 18 (LSd 18 f) x - 112 * LSd 18 f x + 2880 * f x := by
  rw [Aop_eq hf hx, LSd_LSd_eq hf 18 hx]
  unfold LSd
  ring

/-- **The compact operator in the flat chart `ℝ¹⁸`**: the principal part is
`(1 - x)²` times the flat bilaplacian, and the remainder has order three. -/
theorem sixteen_Aop_flat {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    16 * Aop f x = (1 - x) ^ 2 * lapR 18 (lapR 18 f) x - 16 * (1 - x) * eulR (lapR 18 f) x
      + (172 * x - 160) * lapR 18 f x + 36 * eulR (eulR f) x + 672 * eulR f x
      + 2880 * f x := by
  rw [sixteen_Aop hf hx, LSd_LSd hf 18 hx, LSd_eq]
  ring

end Smooth

/-! ### The other end -/

/-- The reflection `x ↦ 1 - x`. -/
theorem contDiffOn_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) :
    ContDiffOn ℝ ∞ (fun y => f (1 - y)) (Icc 0 1) :=
  hf.comp (contDiff_const.sub contDiff_id).contDiffOn fun y hy =>
    ⟨by linarith [hy.2], by linarith [hy.1]⟩

theorem D_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    D (fun y => f (1 - y)) y = -D f (1 - y) := by
  have hy' : 1 - y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h1 : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1) (Icc 0 1) y :=
    ((hasDerivAt_id' y).const_sub 1).hasDerivWithinAt
  have h := (hasDerivWithinAt_D hf hy').scomp y h1 fun w hw =>
    ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have e : D (fun y => f (1 - y)) y = _ := h.derivWithin (uniqueDiffOn_Icc_zero_one y hy)
  rw [e]
  simp

theorem D_D_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : D (D (fun y => f (1 - y))) y = D (D f) (1 - y) := by
  have e : D (D (fun y => f (1 - y))) y = D (fun y => -D f (1 - y)) y :=
    derivWithin_congr (fun w hw => D_refl hf hw) (D_refl hf hy)
  have hneg : D (fun y => -D f (1 - y)) y = -D (fun y => D f (1 - y)) y := by
    show derivWithin (fun y => -D f (1 - y)) (Icc 0 1) y = -derivWithin (fun y => D f (1 - y)) (Icc 0 1) y
    exact derivWithin.fun_neg
  rw [e, hneg, D_refl (contDiffOn_D hf) hy, neg_neg]

/-- The reflection exchanges the two forms of the spherical Laplacian. -/
theorem LSd_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : LSd 6 (fun y => f (1 - y)) y = LSd 18 f (1 - y) := by
  unfold LSd
  rw [D_D_refl hf hy, D_refl hf hy]
  ring

/-- **The compact operator at the other end**, in the coordinate `y = 1 - x`:
again `16 A = (Δ_S - 40) (Δ_S - 72)`, with `ℝ⁶` in place of `ℝ¹⁸`. -/
theorem sixteen_Aop_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    16 * Aop f (1 - y) = LSd 6 (LSd 6 fun y => f (1 - y)) y
      - 112 * LSd 6 (fun y => f (1 - y)) y + 2880 * f (1 - y) := by
  have hy' : 1 - y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hg := contDiffOn_refl hf
  have hL := contDiffOn_LSd hf 18
  -- `LSd 6 g = (LSd 18 f) ∘ refl` on `[0, 1]`
  have e1 : ∀ w ∈ Icc (0 : ℝ) 1, LSd 6 (fun y => f (1 - y)) w = LSd 18 f (1 - w) :=
    fun w hw => LSd_refl hf hw
  have e2 : LSd 6 (LSd 6 fun y => f (1 - y)) y = LSd 6 (fun y => LSd 18 f (1 - y)) y := by
    unfold LSd
    have d1 : D (fun x => 4 * x * (1 - x) * D (D fun y => f (1 - y)) x
        + (2 * 6 - 48 * x) * D (fun y => f (1 - y)) x) y
        = D (fun y => 4 * (1 - y) * (1 - (1 - y)) * D (D f) (1 - y)
          + (2 * 18 - 48 * (1 - y)) * D f (1 - y)) y :=
      derivWithin_congr (fun w hw => e1 w hw) (e1 y hy)
    have d2 : D (D fun x => 4 * x * (1 - x) * D (D fun y => f (1 - y)) x
        + (2 * 6 - 48 * x) * D (fun y => f (1 - y)) x) y
        = D (D fun y => 4 * (1 - y) * (1 - (1 - y)) * D (D f) (1 - y)
          + (2 * 18 - 48 * (1 - y)) * D f (1 - y)) y :=
      derivWithin_congr (fun w hw => derivWithin_congr (fun v hv => e1 v hv) (e1 w hw))
        (derivWithin_congr (fun v hv => e1 v hv) (e1 y hy))
    rw [d1, d2]
  rw [sixteen_Aop hf hy', e2, LSd_refl hL hy, LSd_refl hf hy]

/-! ### The chart form -/

/-- The operator `16 A` in the flat chart `ℝᵈ`, on functions of `x = |z|²`:
`(1 - x)² Δ² - (4 + 2 m) (1 - x) E Δ + ((160 + 2 m) x - 160) Δ + m² E² + 112 m E
+ 2880` with `m = 24 - d`. -/
noncomputable def chart1D (d : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - x) ^ 2 * lapR d (lapR d g) x - (4 + 2 * (24 - d)) * (1 - x) * eulR (lapR d g) x
    + ((160 + 2 * (24 - d)) * x - 160) * lapR d g x + (24 - d) ^ 2 * eulR (eulR g) x
    + 112 * (24 - d) * eulR g x + 2880 * g x

theorem chart1D_eq {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Icc 0 1)) (d : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    LSd d (LSd d g) x - 112 * LSd d g x + 2880 * g x = chart1D d g x := by
  rw [LSd_LSd hg d hx, LSd_eq]
  unfold chart1D
  ring

/-- `16 A` in the chart `ℝ¹⁸` at the end `x = 0`. -/
theorem sixteen_Aop_chart {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 16 * Aop f x = chart1D 18 f x := by
  rw [sixteen_Aop hf hx, chart1D_eq hf 18 hx]

/-- `16 A` in the chart `ℝ⁶` at the end `x = 1`, in the coordinate `y = 1 - x`. -/
theorem sixteen_Aop_chart_refl {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 1)) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : 16 * Aop f (1 - y) = chart1D 6 (fun y => f (1 - y)) y := by
  rw [sixteen_Aop_refl hf hy, chart1D_eq (contDiffOn_refl hf) 6 hy]

end Calabi.Radial
