import OAI.Analysis.AncientFlat.Regularity.HolderProducts
import OAI.Analysis.AncientFlat.Geometry.ParabolicWindows

/-!
# Weighted two-point Hölder bounds

The weighted local spaces of Definition 4.1 of the manuscript are defined
through parabolic boxes whose size is the local scale. For the algebra of
Section 6 (cut-offs, products, comparison of scales) this file introduces an
equivalent form of the bounds without boxes. For a positive scale `s`, a
weight `w` and a radius `a`,

  `WH α a s Ω w M f`

says that `|f(P)| ≤ M s(P)^w` on `Ω` and
`|f(P) - f(Q)| ≤ M s(P)^{w - α} d(P, Q)^α` for `P, Q ∈ Ω` with
`d(P, Q) ≤ a s(P)`, where `d` is the parabolic distance.

* `IsScale a c s Ω`: the scale is positive and changes at most by the factor
  `c` over the distance `a s`.
* The bounds are stable under sums, bounded bi-additive products (the weights
  add), continuous linear maps, lowering of the weight on a bounded scale,
  change to a comparable scale and change of the radius.
* `WH.of_lipschitz`: scaled bounds for the space and time increments give the
  two-point bound.
* `WH.holderBound_window`: on a box of comparable size the two-point bound is
  an ordinary Hölder bound for the rescaled function, which is the form used by
  the estimates of the reused library.
-/

open Set

namespace Calabi.Weighted

open OAI OAI.ParabolicInterior OAI.ParabolicLocalization

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Powers of comparable scales -/

/-- Powers of comparable positive numbers are comparable. -/
theorem rpow_le_of_comparable {x y k : ℝ} (hx : 0 < x) (hy : 0 < y) (hk : 1 ≤ k)
    (hxy : x ≤ k * y) (hyx : y ≤ k * x) (w : ℝ) : x ^ w ≤ k ^ |w| * y ^ w := by
  have hk0 : 0 < k := by linarith
  rcases le_or_gt 0 w with hw | hw
  · rw [abs_of_nonneg hw, ← Real.mul_rpow hk0.le hy.le]
    exact Real.rpow_le_rpow hx.le hxy hw
  · rw [abs_of_neg hw]
    have h1 : y / k ≤ x := by
      rw [div_le_iff₀ hk0]
      linarith
    have h2 : x ^ w ≤ (y / k) ^ w :=
      Real.rpow_le_rpow_of_nonpos (div_pos hy hk0) h1 hw.le
    rw [Real.div_rpow hy.le hk0.le, div_eq_mul_inv, ← Real.rpow_neg hk0.le, mul_comm] at h2
    exact h2

/-- A power of a distance below the scale is traded for a smaller power. -/
theorem scale_interp {s d α k w : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hds : d ≤ s) (hα : 0 ≤ α)
    (hαk : α ≤ k) : s ^ (w - k) * d ^ k ≤ s ^ (w - α) * d ^ α := by
  rcases hαk.eq_or_lt with h | h
  · subst h
    exact le_rfl
  · have hk : α + (k - α) ≠ 0 := by
      have e : α + (k - α) = k := by ring
      rw [e]
      exact (hα.trans_lt h).ne'
    have e1 : d ^ k = d ^ α * d ^ (k - α) := by
      rw [← Real.rpow_add' hd hk]
      congr 1
      ring
    have e2 : s ^ (w - α) = s ^ (w - k) * s ^ (k - α) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    have h1 : d ^ (k - α) ≤ s ^ (k - α) := Real.rpow_le_rpow hd hds (by linarith)
    rw [e1, e2]
    calc s ^ (w - k) * (d ^ α * d ^ (k - α))
        ≤ s ^ (w - k) * (d ^ α * s ^ (k - α)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hd _))
            (Real.rpow_nonneg hs.le _)
      _ = s ^ (w - k) * s ^ (k - α) * d ^ α := by ring

/-! ### Scales -/

/-- `s` is a scale on `Ω`: it is positive and changes at most by the factor `c`
over the parabolic distance `a s`. -/
structure IsScale (a c : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) : Prop where
  one_le : 1 ≤ c
  pos : ∀ p ∈ Ω, 0 < s p
  le : ∀ p ∈ Ω, ∀ q ∈ Ω, pdist p q ≤ a * s p → s q ≤ c * s p
  ge : ∀ p ∈ Ω, ∀ q ∈ Ω, pdist p q ≤ a * s p → s p ≤ c * s q

variable {α a c w M : ℝ} {s : V × ℝ → ℝ} {Ω : Set (V × ℝ)}

theorem IsScale.rpow_le (hs : IsScale a c s Ω) {p q : V × ℝ} (hp : p ∈ Ω) (hq : q ∈ Ω)
    (hd : pdist p q ≤ a * s p) (w : ℝ) : s q ^ w ≤ c ^ |w| * s p ^ w :=
  rpow_le_of_comparable (hs.pos q hq) (hs.pos p hp) hs.one_le (hs.le p hp q hq hd)
    (hs.ge p hp q hq hd) w

theorem IsScale.mono (hs : IsScale a c s Ω) {a' : ℝ} {Ω' : Set (V × ℝ)} (ha : a' ≤ a)
    (hΩ : Ω' ⊆ Ω) : IsScale a' c s Ω' where
  one_le := hs.one_le
  pos p hp := hs.pos p (hΩ hp)
  le p hp q hq hd := hs.le p (hΩ hp) q (hΩ hq)
    (hd.trans (mul_le_mul_of_nonneg_right ha (hs.pos p (hΩ hp)).le))
  ge p hp q hq hd := hs.ge p (hΩ hp) q (hΩ hq)
    (hd.trans (mul_le_mul_of_nonneg_right ha (hs.pos p (hΩ hp)).le))

/-- A positive function that is `1`-Lipschitz for the parabolic distance is a
scale with constant `2` for every radius `a ≤ 1/2`. -/
theorem IsScale.of_lipschitz (hpos : ∀ p ∈ Ω, 0 < s p)
    (hl : ∀ p ∈ Ω, ∀ q ∈ Ω, |s p - s q| ≤ pdist p q) (ha : a ≤ 1 / 2) : IsScale a 2 s Ω where
  one_le := by norm_num
  pos := hpos
  le p hp q hq hd := by
    have h1 := (abs_le.1 (hl p hp q hq)).1
    have h2 := mul_le_mul_of_nonneg_right ha (hpos p hp).le
    have h3 := hpos p hp
    linarith
  ge p hp q hq hd := by
    have h1 := (abs_le.1 (hl p hp q hq)).2
    have h2 := mul_le_mul_of_nonneg_right ha (hpos p hp).le
    have h3 := hpos p hp
    linarith

/-- A positive constant is a scale. -/
theorem IsScale.const {s₀ : ℝ} (hs₀ : 0 < s₀) : IsScale a 1 (fun _ : V × ℝ => s₀) Ω where
  one_le := le_rfl
  pos _ _ := hs₀
  le _ _ _ _ _ := by rw [one_mul]
  ge _ _ _ _ _ := by rw [one_mul]

/-! ### The weighted two-point bound -/

section Bound

variable {E : Type*} [NormedAddCommGroup E] {f g : V × ℝ → E}

/-- The weighted two-point Hölder bound with scale `s`, weight `w`, radius `a`
and constant `M`. -/
def WH (α a : ℝ) (s : V × ℝ → ℝ) (Ω : Set (V × ℝ)) (w M : ℝ) (f : V × ℝ → E) : Prop :=
  (∀ p ∈ Ω, ‖f p‖ ≤ M * s p ^ w) ∧
    ∀ p ∈ Ω, ∀ q ∈ Ω, pdist p q ≤ a * s p → ‖f p - f q‖ ≤ M * s p ^ (w - α) * pdist p q ^ α

theorem WH.mono (h : WH α a s Ω w M f) (hs : ∀ p ∈ Ω, 0 < s p) {M' : ℝ} (hM : M ≤ M') :
    WH α a s Ω w M' f := by
  refine ⟨fun p hp => (h.1 p hp).trans
    (mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg (hs p hp).le _)),
    fun p hp q hq hd => (h.2 p hp q hq hd).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg (hs p hp).le _))
    (Real.rpow_nonneg (pdist_nonneg p q) _)

theorem WH.restrict (h : WH α a s Ω w M f) {Ω' : Set (V × ℝ)} (hΩ : Ω' ⊆ Ω) :
    WH α a s Ω' w M f :=
  ⟨fun p hp => h.1 p (hΩ hp), fun p hp q hq hd => h.2 p (hΩ hp) q (hΩ hq) hd⟩

theorem WH.radius_le (h : WH α a s Ω w M f) (hs : ∀ p ∈ Ω, 0 < s p) {a' : ℝ} (ha : a' ≤ a) :
    WH α a' s Ω w M f :=
  ⟨h.1, fun p hp q hq hd =>
    h.2 p hp q hq (hd.trans (mul_le_mul_of_nonneg_right ha (hs p hp).le))⟩

theorem WH.congr (h : WH α a s Ω w M f) (hfg : ∀ p ∈ Ω, g p = f p) : WH α a s Ω w M g := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · rw [hfg p hp]
    exact h.1 p hp
  · rw [hfg p hp, hfg q hq]
    exact h.2 p hp q hq hd

theorem WH.zero (hM : 0 ≤ M) (hs : ∀ p ∈ Ω, 0 < s p) :
    WH α a s Ω w M (fun _ => (0 : E)) := by
  refine ⟨fun p hp => ?_, fun p hp q _ _ => ?_⟩
  · rw [norm_zero]
    exact mul_nonneg hM (Real.rpow_nonneg (hs p hp).le _)
  · rw [sub_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (hs p hp).le _))
      (Real.rpow_nonneg (pdist_nonneg p q) _)

theorem WH.add {N : ℝ} (hf : WH α a s Ω w M f) (hg : WH α a s Ω w N g) :
    WH α a s Ω w (M + N) (fun p => f p + g p) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · calc ‖f p + g p‖ ≤ ‖f p‖ + ‖g p‖ := norm_add_le _ _
      _ ≤ M * s p ^ w + N * s p ^ w := add_le_add (hf.1 p hp) (hg.1 p hp)
      _ = (M + N) * s p ^ w := by ring
  · have e : f p + g p - (f q + g q) = (f p - f q) + (g p - g q) := by abel
    rw [e]
    calc ‖(f p - f q) + (g p - g q)‖ ≤ ‖f p - f q‖ + ‖g p - g q‖ := norm_add_le _ _
      _ ≤ M * s p ^ (w - α) * pdist p q ^ α + N * s p ^ (w - α) * pdist p q ^ α :=
        add_le_add (hf.2 p hp q hq hd) (hg.2 p hp q hq hd)
      _ = (M + N) * s p ^ (w - α) * pdist p q ^ α := by ring

theorem WH.neg (hf : WH α a s Ω w M f) : WH α a s Ω w M (fun p => -f p) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · rw [norm_neg]
    exact hf.1 p hp
  · have e : -f p - -f q = -(f p - f q) := by abel
    rw [e, norm_neg]
    exact hf.2 p hp q hq hd

theorem WH.sub {N : ℝ} (hf : WH α a s Ω w M f) (hg : WH α a s Ω w N g) :
    WH α a s Ω w (M + N) (fun p => f p - g p) := by
  have h := hf.add hg.neg
  have e : (fun p => f p - g p) = fun p => f p + -g p := funext fun p => sub_eq_add_neg _ _
  rw [e]
  exact h

/-- A function that vanishes where the bound is not known. -/
theorem WH.of_local {Ω' : Set (V × ℝ)} (hf : WH α a s Ω' w M f) (hM : 0 ≤ M)
    (hs : ∀ p ∈ Ω, 0 < s p) (h0 : ∀ p ∈ Ω, p ∈ Ω' ∨ f p = 0)
    (h : ∀ p ∈ Ω, ∀ q ∈ Ω, pdist p q ≤ a * s p → (p ∈ Ω' ∧ q ∈ Ω') ∨ (f p = 0 ∧ f q = 0)) :
    WH α a s Ω w M f := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · rcases h0 p hp with h1 | h1
    · exact hf.1 p h1
    · rw [h1, norm_zero]
      exact mul_nonneg hM (Real.rpow_nonneg (hs p hp).le _)
  · rcases h p hp q hq hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hf.2 p h1 q h2 hd
    · rw [h1, h2, sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (hs p hp).le _))
        (Real.rpow_nonneg (pdist_nonneg p q) _)

/-- Lowering the weight on a bounded scale. -/
theorem WH.weight {w' S : ℝ} (hf : WH α a s Ω w M f) (hM : 0 ≤ M) (hs : ∀ p ∈ Ω, 0 < s p)
    (hS : ∀ p ∈ Ω, s p ≤ S) (hw : w' ≤ w) : WH α a s Ω w' (M * S ^ (w - w')) f := by
  have key : ∀ p ∈ Ω, ∀ v : ℝ, s p ^ v ≤ S ^ (w - w') * s p ^ (v - (w - w')) := by
    intro p hp v
    have hsp := hs p hp
    have e : s p ^ v = s p ^ (w - w') * s p ^ (v - (w - w')) := by
      rw [← Real.rpow_add hsp]
      congr 1
      ring
    calc s p ^ v = s p ^ (w - w') * s p ^ (v - (w - w')) := e
      _ ≤ S ^ (w - w') * s p ^ (v - (w - w')) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hsp.le (hS p hp) (by linarith))
          (Real.rpow_nonneg hsp.le _)
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have h1 := key p hp w
    have e : w - (w - w') = w' := by ring
    rw [e] at h1
    calc ‖f p‖ ≤ M * s p ^ w := hf.1 p hp
      _ ≤ M * (S ^ (w - w') * s p ^ w') := mul_le_mul_of_nonneg_left h1 hM
      _ = M * S ^ (w - w') * s p ^ w' := by ring
  · have h1 := key p hp (w - α)
    have e : w - α - (w - w') = w' - α := by ring
    rw [e] at h1
    calc ‖f p - f q‖ ≤ M * s p ^ (w - α) * pdist p q ^ α := hf.2 p hp q hq hd
      _ ≤ M * (S ^ (w - w') * s p ^ (w' - α)) * pdist p q ^ α :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hM)
          (Real.rpow_nonneg (pdist_nonneg p q) _)
      _ = M * S ^ (w - w') * s p ^ (w' - α) * pdist p q ^ α := by ring

/-- Change to a comparable scale. -/
theorem WH.scale {s' : V × ℝ → ℝ} {k : ℝ} (hf : WH α a s Ω w M f) (hM : 0 ≤ M) (hk : 1 ≤ k)
    (ha : 0 ≤ a) (hs : ∀ p ∈ Ω, 0 < s p) (hs' : ∀ p ∈ Ω, 0 < s' p)
    (h1 : ∀ p ∈ Ω, s p ≤ k * s' p) (h2 : ∀ p ∈ Ω, s' p ≤ k * s p) :
    WH α (a / k) s' Ω w (M * k ^ (|w| + |w - α|)) f := by
  have hk0 : 0 < k := by linarith
  have hkw : k ^ |w| ≤ k ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hk (le_add_of_nonneg_right (abs_nonneg _))
  have hkα : k ^ |w - α| ≤ k ^ (|w| + |w - α|) :=
    Real.rpow_le_rpow_of_exponent_le hk (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have h3 := rpow_le_of_comparable (hs p hp) (hs' p hp) hk (h1 p hp) (h2 p hp) w
    have h4 : 0 ≤ s' p ^ w := Real.rpow_nonneg (hs' p hp).le _
    calc ‖f p‖ ≤ M * s p ^ w := hf.1 p hp
      _ ≤ M * (k ^ |w| * s' p ^ w) := mul_le_mul_of_nonneg_left h3 hM
      _ ≤ M * (k ^ (|w| + |w - α|) * s' p ^ w) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkw h4) hM
      _ = M * k ^ (|w| + |w - α|) * s' p ^ w := by ring
  · have hd' : pdist p q ≤ a * s p := by
      refine hd.trans ?_
      calc a / k * s' p ≤ a / k * (k * s p) :=
            mul_le_mul_of_nonneg_left (h2 p hp) (div_nonneg ha hk0.le)
        _ = a * s p := by
            rw [← mul_assoc, div_mul_cancel₀ a hk0.ne']
    have h3 := rpow_le_of_comparable (hs p hp) (hs' p hp) hk (h1 p hp) (h2 p hp) (w - α)
    have h4 : 0 ≤ s' p ^ (w - α) := Real.rpow_nonneg (hs' p hp).le _
    have h5 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
    calc ‖f p - f q‖ ≤ M * s p ^ (w - α) * pdist p q ^ α := hf.2 p hp q hq hd'
      _ ≤ M * (k ^ |w - α| * s' p ^ (w - α)) * pdist p q ^ α :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hM) h5
      _ ≤ M * (k ^ (|w| + |w - α|) * s' p ^ (w - α)) * pdist p q ^ α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkα h4) hM) h5
      _ = M * k ^ (|w| + |w - α|) * s' p ^ (w - α) * pdist p q ^ α := by ring

/-- Increasing the radius. -/
theorem WH.radius_ge {a' : ℝ} (hf : WH α a s Ω w M f) (hsc : IsScale a' c s Ω) (hM : 0 ≤ M)
    (ha : 0 < a) (hα : 0 ≤ α) :
    WH α a' s Ω w (M * (1 + (1 + c ^ |w|) * a ^ (-α))) f := by
  have hc0 : 0 ≤ c ^ |w| := Real.rpow_nonneg (by linarith [hsc.one_le]) _
  have ha0 : 0 ≤ a ^ (-α) := Real.rpow_nonneg ha.le _
  have hK : 0 ≤ (1 + c ^ |w|) * a ^ (-α) := mul_nonneg (by linarith) ha0
  have hMK : M ≤ M * (1 + (1 + c ^ |w|) * a ^ (-α)) := by
    nlinarith [mul_nonneg hM hK]
  refine ⟨fun p hp => (hf.1 p hp).trans
    (mul_le_mul_of_nonneg_right hMK (Real.rpow_nonneg (hsc.pos p hp).le _)),
    fun p hp q hq hd => ?_⟩
  have hsp := hsc.pos p hp
  have hd0 := pdist_nonneg p q
  have h5 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg hd0 _
  have h6 : 0 ≤ s p ^ (w - α) := Real.rpow_nonneg hsp.le _
  rcases le_or_gt (pdist p q) (a * s p) with h | h
  · exact (hf.2 p hp q hq h).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMK h6) h5)
  · have h1 : ‖f p - f q‖ ≤ M * s p ^ w + M * (c ^ |w| * s p ^ w) := by
      calc ‖f p - f q‖ ≤ ‖f p‖ + ‖f q‖ := norm_sub_le _ _
        _ ≤ M * s p ^ w + M * s q ^ w := add_le_add (hf.1 p hp) (hf.1 q hq)
        _ ≤ M * s p ^ w + M * (c ^ |w| * s p ^ w) := by
          have := mul_le_mul_of_nonneg_left (hsc.rpow_le hp hq hd w) hM
          linarith
    have h2 : s p ≤ pdist p q / a := by
      rw [le_div_iff₀ ha]
      linarith
    have h3 : s p ^ α ≤ pdist p q ^ α * a ^ (-α) := by
      have h4 := Real.rpow_le_rpow hsp.le h2 hα
      rw [Real.div_rpow hd0 ha.le, div_eq_mul_inv, ← Real.rpow_neg ha.le] at h4
      exact h4
    have e : s p ^ w = s p ^ (w - α) * s p ^ α := by
      rw [← Real.rpow_add hsp]
      congr 1
      ring
    have h7 : s p ^ w ≤ s p ^ (w - α) * (pdist p q ^ α * a ^ (-α)) := by
      rw [e]
      exact mul_le_mul_of_nonneg_left h3 h6
    have h8 : 0 ≤ M * (1 + c ^ |w|) := mul_nonneg hM (by linarith)
    calc ‖f p - f q‖ ≤ M * (1 + c ^ |w|) * s p ^ w := by
          refine h1.trans (le_of_eq ?_)
          ring
      _ ≤ M * (1 + c ^ |w|) * (s p ^ (w - α) * (pdist p q ^ α * a ^ (-α))) :=
          mul_le_mul_of_nonneg_left h7 h8
      _ = M * ((1 + c ^ |w|) * a ^ (-α)) * s p ^ (w - α) * pdist p q ^ α := by ring
      _ ≤ M * (1 + (1 + c ^ |w|) * a ^ (-α)) * s p ^ (w - α) * pdist p q ^ α := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ h6) h5
          exact mul_le_mul_of_nonneg_left (by linarith) hM

/-- Scaled bounds for the space and time increments give the two-point bound. -/
theorem WH.of_lipschitz (hs : ∀ p ∈ Ω, 0 < s p) (hM : 0 ≤ M) (ha1 : a ≤ 1) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (h0 : ∀ p ∈ Ω, ‖f p‖ ≤ M * s p ^ w)
    (h1 : ∀ p ∈ Ω, ∀ q ∈ Ω, pdist p q ≤ a * s p →
      ‖f p - f q‖ ≤ M * s p ^ (w - 1) * ‖p.1 - q.1‖ + M * s p ^ (w - 4) * |p.2 - q.2|) :
    WH α a s Ω w (2 * M) f := by
  refine ⟨fun p hp => (h0 p hp).trans ?_, fun p hp q hq hd => ?_⟩
  · have := mul_nonneg hM (Real.rpow_nonneg (hs p hp).le w)
    linarith
  · have hsp := hs p hp
    have hd0 := pdist_nonneg p q
    have hds : pdist p q ≤ s p := by
      have := mul_le_mul_of_nonneg_right ha1 hsp.le
      linarith
    have hr0 : 0 ≤ |p.2 - q.2| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
    have hx : ‖p.1 - q.1‖ ≤ pdist p q := by
      unfold pdist
      linarith
    have hr : |p.2 - q.2| ^ ((1 : ℝ) / 4) ≤ pdist p q := by
      unfold pdist
      linarith [norm_nonneg (p.1 - q.1)]
    have ht : |p.2 - q.2| ≤ pdist p q ^ (4 : ℝ) := by
      have e : |p.2 - q.2| = (|p.2 - q.2| ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul (abs_nonneg _)]
        norm_num
      rw [e]
      exact Real.rpow_le_rpow hr0 hr (by norm_num)
    have i1 : s p ^ (w - 1) * pdist p q ^ (1 : ℝ) ≤ s p ^ (w - α) * pdist p q ^ α :=
      scale_interp hsp hd0 hds hα hα1
    have i4 : s p ^ (w - 4) * pdist p q ^ (4 : ℝ) ≤ s p ^ (w - α) * pdist p q ^ α :=
      scale_interp hsp hd0 hds hα (by linarith)
    rw [Real.rpow_one] at i1
    have b1 : M * s p ^ (w - 1) * ‖p.1 - q.1‖ ≤ M * (s p ^ (w - α) * pdist p q ^ α) := by
      calc M * s p ^ (w - 1) * ‖p.1 - q.1‖ ≤ M * s p ^ (w - 1) * pdist p q :=
            mul_le_mul_of_nonneg_left hx (mul_nonneg hM (Real.rpow_nonneg hsp.le _))
        _ = M * (s p ^ (w - 1) * pdist p q) := by ring
        _ ≤ M * (s p ^ (w - α) * pdist p q ^ α) := mul_le_mul_of_nonneg_left i1 hM
    have b4 : M * s p ^ (w - 4) * |p.2 - q.2| ≤ M * (s p ^ (w - α) * pdist p q ^ α) := by
      calc M * s p ^ (w - 4) * |p.2 - q.2| ≤ M * s p ^ (w - 4) * pdist p q ^ (4 : ℝ) :=
            mul_le_mul_of_nonneg_left ht (mul_nonneg hM (Real.rpow_nonneg hsp.le _))
        _ = M * (s p ^ (w - 4) * pdist p q ^ (4 : ℝ)) := by ring
        _ ≤ M * (s p ^ (w - α) * pdist p q ^ α) := mul_le_mul_of_nonneg_left i4 hM
    calc ‖f p - f q‖
        ≤ M * s p ^ (w - 1) * ‖p.1 - q.1‖ + M * s p ^ (w - 4) * |p.2 - q.2| := h1 p hp q hq hd
      _ ≤ M * (s p ^ (w - α) * pdist p q ^ α) + M * (s p ^ (w - α) * pdist p q ^ α) :=
        add_le_add b1 b4
      _ = 2 * M * s p ^ (w - α) * pdist p q ^ α := by ring

end Bound

/-! ### Products and linear maps -/

section Product

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- A bounded bi-additive product adds the weights. -/
theorem WH.bilin {B : E → F → G} {K N w₁ w₂ : ℝ} {f : V × ℝ → E} {g : V × ℝ → F}
    (hsc : IsScale a c s Ω) (hK : 0 ≤ K) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖) (hBl : ∀ x x' y, B x y - B x' y = B (x - x') y)
    (hBr : ∀ x y y', B x y - B x y' = B x (y - y'))
    (hf : WH α a s Ω w₁ M f) (hg : WH α a s Ω w₂ N g) :
    WH α a s Ω (w₁ + w₂) (K * (1 + c ^ |w₁|) * M * N) (fun p => B (f p) (g p)) := by
  have hcw : 0 ≤ c ^ |w₁| := Real.rpow_nonneg (by linarith [hsc.one_le]) _
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · have hsp := hsc.pos p hp
    have hA : 0 ≤ s p ^ w₁ := Real.rpow_nonneg hsp.le _
    have hT : 0 ≤ s p ^ (w₁ + w₂) := Real.rpow_nonneg hsp.le _
    have h0 : 0 ≤ K * M * N * s p ^ (w₁ + w₂) :=
      mul_nonneg (mul_nonneg (mul_nonneg hK hM) hN) hT
    calc ‖B (f p) (g p)‖ ≤ K * ‖f p‖ * ‖g p‖ := hB _ _
      _ ≤ K * (M * s p ^ w₁) * (N * s p ^ w₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf.1 p hp) hK) (hg.1 p hp) (norm_nonneg _)
          (mul_nonneg hK (mul_nonneg hM hA))
      _ = K * M * N * s p ^ (w₁ + w₂) := by
        rw [Real.rpow_add hsp]
        ring
      _ ≤ K * (1 + c ^ |w₁|) * M * N * s p ^ (w₁ + w₂) := by
        nlinarith [mul_nonneg hcw h0]
  · have hsp := hsc.pos p hp
    have hd0 : 0 ≤ pdist p q ^ α := Real.rpow_nonneg (pdist_nonneg p q) _
    have e : B (f p) (g p) - B (f q) (g q)
        = B (f p - f q) (g p) + B (f q) (g p - g q) := by
      rw [← hBl, ← hBr]
      abel
    have e1 : s p ^ (w₁ - α) * s p ^ w₂ = s p ^ (w₁ + w₂ - α) := by
      rw [← Real.rpow_add hsp]
      congr 1
      ring
    have e2 : s p ^ w₁ * s p ^ (w₂ - α) = s p ^ (w₁ + w₂ - α) := by
      rw [← Real.rpow_add hsp]
      congr 1
      ring
    have hS1 : 0 ≤ s p ^ (w₁ - α) := Real.rpow_nonneg hsp.le _
    have hS3 : 0 ≤ s p ^ w₁ := Real.rpow_nonneg hsp.le _
    have b1 : ‖B (f p - f q) (g p)‖
        ≤ K * (M * s p ^ (w₁ - α) * pdist p q ^ α) * (N * s p ^ w₂) :=
      (hB _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hf.2 p hp q hq hd) hK)
        (hg.1 p hp) (norm_nonneg _)
        (mul_nonneg hK (mul_nonneg (mul_nonneg hM hS1) hd0)))
    have hfq : ‖f q‖ ≤ M * (c ^ |w₁| * s p ^ w₁) :=
      (hf.1 q hq).trans (mul_le_mul_of_nonneg_left (hsc.rpow_le hp hq hd w₁) hM)
    have b2 : ‖B (f q) (g p - g q)‖
        ≤ K * (M * (c ^ |w₁| * s p ^ w₁)) * (N * s p ^ (w₂ - α) * pdist p q ^ α) :=
      (hB _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hfq hK)
        (hg.2 p hp q hq hd) (norm_nonneg _)
        (mul_nonneg hK (mul_nonneg hM (mul_nonneg hcw hS3))))
    rw [e]
    calc ‖B (f p - f q) (g p) + B (f q) (g p - g q)‖
        ≤ ‖B (f p - f q) (g p)‖ + ‖B (f q) (g p - g q)‖ := norm_add_le _ _
      _ ≤ K * (M * s p ^ (w₁ - α) * pdist p q ^ α) * (N * s p ^ w₂)
          + K * (M * (c ^ |w₁| * s p ^ w₁)) * (N * s p ^ (w₂ - α) * pdist p q ^ α) :=
        add_le_add b1 b2
      _ = K * M * N * (s p ^ (w₁ - α) * s p ^ w₂) * pdist p q ^ α
          + K * c ^ |w₁| * M * N * (s p ^ w₁ * s p ^ (w₂ - α)) * pdist p q ^ α := by ring
      _ = K * (1 + c ^ |w₁|) * M * N * s p ^ (w₁ + w₂ - α) * pdist p q ^ α := by
        rw [e1, e2]
        ring

/-- Product with a scalar function. -/
theorem WH.smul [NormedSpace ℝ E] {N w₁ w₂ : ℝ} {φ : V × ℝ → ℝ} {f : V × ℝ → E}
    (hsc : IsScale a c s Ω) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : WH α a s Ω w₁ M φ) (hf : WH α a s Ω w₂ N f) :
    WH α a s Ω (w₁ + w₂) ((1 + c ^ |w₁|) * M * N) (fun p => φ p • f p) := by
  have h := WH.bilin (B := fun (x : ℝ) (y : E) => x • y) hsc zero_le_one hM hN
    (fun x y => by
      show ‖x • y‖ ≤ 1 * ‖x‖ * ‖y‖
      rw [norm_smul, one_mul]) (fun x x' y => (sub_smul x x' y).symm)
    (fun x y y' => (smul_sub x y y').symm) hφ hf
  rw [one_mul] at h
  exact h

/-- Product of real functions. -/
theorem WH.mul {N w₁ w₂ : ℝ} {φ ψ : V × ℝ → ℝ} (hsc : IsScale a c s Ω) (hM : 0 ≤ M)
    (hN : 0 ≤ N) (hφ : WH α a s Ω w₁ M φ) (hψ : WH α a s Ω w₂ N ψ) :
    WH α a s Ω (w₁ + w₂) ((1 + c ^ |w₁|) * M * N) (fun p => φ p * ψ p) :=
  WH.smul hsc hM hN hφ hψ

/-- A continuous linear map. -/
theorem WH.clm [NormedSpace ℝ E] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : V × ℝ → E}
    (hf : WH α a s Ω w M f) : WH α a s Ω w (‖L‖ * M) (fun p => L (f p)) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · calc ‖L (f p)‖ ≤ ‖L‖ * ‖f p‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (M * s p ^ w) := mul_le_mul_of_nonneg_left (hf.1 p hp) (norm_nonneg _)
      _ = ‖L‖ * M * s p ^ w := by ring
  · rw [← map_sub]
    calc ‖L (f p - f q)‖ ≤ ‖L‖ * ‖f p - f q‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (M * s p ^ (w - α) * pdist p q ^ α) :=
        mul_le_mul_of_nonneg_left (hf.2 p hp q hq hd) (norm_nonneg _)
      _ = ‖L‖ * M * s p ^ (w - α) * pdist p q ^ α := by ring

/-- Multiplication by a constant. -/
theorem WH.const_smul [NormedSpace ℝ E] (k : ℝ) {f : V × ℝ → E} (hf : WH α a s Ω w M f) :
    WH α a s Ω w (|k| * M) (fun p => k • f p) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hd => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs]
    calc |k| * ‖f p‖ ≤ |k| * (M * s p ^ w) :=
          mul_le_mul_of_nonneg_left (hf.1 p hp) (abs_nonneg _)
      _ = |k| * M * s p ^ w := by ring
  · rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |k| * ‖f p - f q‖ ≤ |k| * (M * s p ^ (w - α) * pdist p q ^ α) :=
          mul_le_mul_of_nonneg_left (hf.2 p hp q hq hd) (abs_nonneg _)
      _ = |k| * M * s p ^ (w - α) * pdist p q ^ α := by ring

end Product

/-! ### Boxes -/

section Window

variable {E : Type*} [NormedAddCommGroup E] {f : V × ℝ → E}

/-- **From the two-point bound to a box**: for a box of size `q ≤ k s₀` on which
the scale is comparable with `s₀`, the rescaled function satisfies an ordinary
parabolic Hölder bound. -/
theorem WH.holderBound_window {k s₀ q : ℝ} (hf : WH α a s Ω w M f) (hM : 0 ≤ M) (ha : 0 < a)
    (hα : 0 ≤ α) (hc : 1 ≤ c) (hq : 0 < q) (hs₀ : 0 < s₀) (hqs : q ≤ k * s₀) (p₀ : V × ℝ)
    {D : Set (V × ℝ)} (hD : MapsTo (window p₀ q) D Ω)
    (hpos : ∀ p ∈ D, 0 < s (window p₀ q p))
    (hc1 : ∀ p ∈ D, s (window p₀ q p) ≤ c * s₀) (hc2 : ∀ p ∈ D, s₀ ≤ c * s (window p₀ q p)) :
    HolderBound α D (fun p => f (window p₀ q p))
      ((c ^ |w| + c ^ |w - α| * k ^ α + 2 * c ^ |w| * (c * k / a) ^ α) * M * s₀ ^ w) := by
  have hc0 : 0 < c := by linarith
  have hk : 0 < k := by
    by_contra h
    have : k * s₀ ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨not_lt.1 h, hs₀.le⟩)
    linarith
  have hA : 0 ≤ c ^ |w| := Real.rpow_nonneg hc0.le _
  have hB : 0 ≤ c ^ |w - α| * k ^ α :=
    mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg hk.le _)
  have hck : 0 ≤ c * k / a := div_nonneg (mul_nonneg hc0.le hk.le) ha.le
  have hC : 0 ≤ 2 * c ^ |w| * (c * k / a) ^ α :=
    mul_nonneg (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg hck _)
  have hs₀w : 0 ≤ s₀ ^ w := Real.rpow_nonneg hs₀.le _
  have hMs : 0 ≤ M * s₀ ^ w := mul_nonneg hM hs₀w
  have hsup : ∀ p ∈ D, ‖f (window p₀ q p)‖ ≤ c ^ |w| * (M * s₀ ^ w) := by
    intro p hp
    have h1 := rpow_le_of_comparable (hpos p hp) hs₀ hc (hc1 p hp) (hc2 p hp) w
    calc ‖f (window p₀ q p)‖ ≤ M * s (window p₀ q p) ^ w := hf.1 _ (hD hp)
      _ ≤ M * (c ^ |w| * s₀ ^ w) := mul_le_mul_of_nonneg_left h1 hM
      _ = c ^ |w| * (M * s₀ ^ w) := by ring
  refine ⟨fun p hp => (hsup p hp).trans ?_, fun p hp z hz => ?_⟩
  · nlinarith [mul_nonneg hB hMs, mul_nonneg hC hMs]
  · have hd0 := pdist_nonneg p z
    have hdα : 0 ≤ pdist p z ^ α := Real.rpow_nonneg hd0 _
    have hsP := hpos p hp
    have hpd : pdist (window p₀ q p) (window p₀ q z) = q * pdist p z :=
      pdist_window p₀ hq.le p z
    have hX : 0 ≤ M * s₀ ^ w * pdist p z ^ α := mul_nonneg hMs hdα
    rcases le_or_gt (q * pdist p z) (a * s (window p₀ q p)) with h | h
    · -- the two points are close
      have h1 := hf.2 _ (hD hp) _ (hD hz) (hpd.trans_le h)
      rw [hpd, Real.mul_rpow hq.le hd0] at h1
      have h2 := rpow_le_of_comparable hsP hs₀ hc (hc1 p hp) (hc2 p hp) (w - α)
      have h3 : q ^ α ≤ k ^ α * s₀ ^ α := by
        rw [← Real.mul_rpow hk.le hs₀.le]
        exact Real.rpow_le_rpow hq.le hqs hα
      have e : s₀ ^ (w - α) * s₀ ^ α = s₀ ^ w := by
        rw [← Real.rpow_add hs₀]
        congr 1
        ring
      have h4 : s (window p₀ q p) ^ (w - α) * q ^ α
          ≤ c ^ |w - α| * s₀ ^ (w - α) * (k ^ α * s₀ ^ α) :=
        mul_le_mul h2 h3 (Real.rpow_nonneg hq.le _)
          (mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg hs₀.le _))
      calc ‖f (window p₀ q p) - f (window p₀ q z)‖
          ≤ M * s (window p₀ q p) ^ (w - α) * (q ^ α * pdist p z ^ α) := h1
        _ = M * (s (window p₀ q p) ^ (w - α) * q ^ α) * pdist p z ^ α := by ring
        _ ≤ M * (c ^ |w - α| * s₀ ^ (w - α) * (k ^ α * s₀ ^ α)) * pdist p z ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hM) hdα
        _ = c ^ |w - α| * k ^ α * (M * (s₀ ^ (w - α) * s₀ ^ α) * pdist p z ^ α) := by ring
        _ = c ^ |w - α| * k ^ α * (M * s₀ ^ w * pdist p z ^ α) := by rw [e]
        _ ≤ (c ^ |w| + c ^ |w - α| * k ^ α + 2 * c ^ |w| * (c * k / a) ^ α) * M * s₀ ^ w
              * pdist p z ^ α := by
          nlinarith [mul_nonneg hA hX, mul_nonneg hC hX]
    · -- the two points are far apart in the box
      have h1 : ‖f (window p₀ q p) - f (window p₀ q z)‖ ≤ 2 * c ^ |w| * (M * s₀ ^ w) := by
        have := norm_sub_le (f (window p₀ q p)) (f (window p₀ q z))
        have := hsup p hp
        have := hsup z hz
        linarith
      have h2 : 1 ≤ c * k / a * pdist p z := by
        have h3 : a * s (window p₀ q p) < k * (c * s (window p₀ q p)) * pdist p z := by
          refine h.trans_le (mul_le_mul_of_nonneg_right ?_ hd0)
          exact hqs.trans (mul_le_mul_of_nonneg_left (hc2 p hp) hk.le)
        have h4 : a < k * c * pdist p z := by
          by_contra hcon
          have := mul_le_mul_of_nonneg_right (not_lt.1 hcon) hsP.le
          nlinarith
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]
        nlinarith
      have h5 : 1 ≤ (c * k / a) ^ α * pdist p z ^ α := by
        rw [← Real.mul_rpow hck hd0]
        exact Real.one_le_rpow h2 hα
      have h6 : 0 ≤ 2 * c ^ |w| * (M * s₀ ^ w) := mul_nonneg (mul_nonneg (by norm_num) hA) hMs
      calc ‖f (window p₀ q p) - f (window p₀ q z)‖ ≤ 2 * c ^ |w| * (M * s₀ ^ w) * 1 := by
            rw [mul_one]
            exact h1
        _ ≤ 2 * c ^ |w| * (M * s₀ ^ w) * ((c * k / a) ^ α * pdist p z ^ α) :=
          mul_le_mul_of_nonneg_left h5 h6
        _ = 2 * c ^ |w| * (c * k / a) ^ α * (M * s₀ ^ w * pdist p z ^ α) := by ring
        _ ≤ (c ^ |w| + c ^ |w - α| * k ^ α + 2 * c ^ |w| * (c * k / a) ^ α) * M * s₀ ^ w
              * pdist p z ^ α := by
          nlinarith [mul_nonneg hA hX, mul_nonneg hB hX]

end Window

end Calabi.Weighted
