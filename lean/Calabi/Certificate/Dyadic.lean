import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option exponentiation.threshold 1024

namespace Calabi.Certificate.Dyadic

/-- Integer endpoints; the interpretation uses a separately fixed positive scale. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Contains (scale : ℤ) (box : Interval) (x : ℝ) : Prop :=
  (box.lo : ℝ) ≤ (scale : ℝ) * x ∧ (scale : ℝ) * x ≤ (box.hi : ℝ)

def point (scale n : ℤ) : Interval := ⟨n * scale, n * scale⟩
def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩
def divNat (a : Interval) (n : ℕ) : Interval :=
  ⟨a.lo / (n : ℤ), -((-a.hi) / (n : ℤ))⟩

def lowerProduct (a b : Interval) : ℤ :=
  min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
def upperProduct (a b : Interval) : ℤ :=
  max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
def mul (scale : ℤ) (a b : Interval) : Interval :=
  ⟨lowerProduct a b / scale, -((-upperProduct a b) / scale)⟩

theorem point_sound (scale n : ℤ) : Contains scale (point scale n) (n : ℝ) := by
  simp [Contains, point, mul_comm]

theorem add_sound {scale : ℤ} {a b : Interval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) :
    Contains scale (add a b) (x + y) := by
  simp only [Contains, add, Int.cast_add] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem neg_sound {scale : ℤ} {a : Interval} {x : ℝ}
    (hx : Contains scale a x) : Contains scale (neg a) (-x) := by
  simp only [Contains, neg, Int.cast_neg] at *
  constructor <;> nlinarith [hx.1, hx.2]

theorem round_down (a scale : ℤ) (hs : 0 < scale) :
    ((a / scale : ℤ) : ℝ) * (scale : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hs)

theorem round_up (a scale : ℤ) (hs : 0 < scale) :
    (a : ℝ) ≤ (-((-a) / scale : ℤ) : ℝ) * (scale : ℝ) := by
  have h := round_down (-a) scale hs
  simp only [Int.cast_neg] at *
  linarith

theorem divNat_sound {scale : ℤ} {a : Interval} {x : ℝ} {n : ℕ}
    (hn : 0 < n) (hx : Contains scale a x) :
    Contains scale (divNat a n) (x / n) := by
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := round_down a.lo n hnZ
  have hu := round_up a.hi n hnZ
  simp only [Contains, divNat] at *
  constructor
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hnR).mpr
    simpa only [Int.cast_natCast] using hl.trans hx.1
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hnR).mpr
    simpa only [Int.cast_natCast, Int.cast_neg] using hx.2.trans hu

theorem mul_le_corners {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  by_cases h : 0 ≤ y
  · have hxy := mul_le_mul_of_nonneg_right hx.2 h
    by_cases hb : 0 ≤ b
    · have hbd := mul_le_mul_of_nonneg_left hy.2 hb
      exact (hxy.trans hbd).trans ((le_max_right _ _).trans (le_max_right _ _))
    · have hbc := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb)
      exact (hxy.trans hbc).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hxy := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge h)
    by_cases ha : 0 ≤ a
    · have had := mul_le_mul_of_nonneg_left hy.2 ha
      exact (hxy.trans had).trans ((le_max_right _ _).trans (le_max_left _ _))
    · have hac := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha)
      exact (hxy.trans hac).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem corners_le_mul {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h := mul_le_corners hx (show -d ≤ -y ∧ -y ≤ -c by constructor <;> linarith [hy.1, hy.2])
  simp only [mul_neg, max_neg_neg, min_comm] at h
  linarith

theorem mul_sound {scale : ℤ} (hs : 0 < scale) {a b : Interval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) :
    Contains scale (mul scale a b) (x * y) := by
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hl := corners_le_mul hx hy
  have hu := mul_le_corners hx hy
  have hrd := round_down (lowerProduct a b) scale hs
  have hru := round_up (upperProduct a b) scale hs
  simp only [Contains, mul] at *
  have hl' : (lowerProduct a b : ℝ) ≤ (scale : ℝ) * x * ((scale : ℝ) * y) := by
    simpa only [lowerProduct, Int.cast_min, Int.cast_mul] using hl
  have hu' : (scale : ℝ) * x * ((scale : ℝ) * y) ≤ (upperProduct a b : ℝ) := by
    simpa only [upperProduct, Int.cast_max, Int.cast_mul] using hu
  constructor
  · apply (mul_le_mul_iff_left₀ hsR).mp
    calc
      _ ≤ (lowerProduct a b : ℝ) := hrd
      _ ≤ (scale : ℝ) * x * ((scale : ℝ) * y) := hl'
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ hsR).mp
    calc
      _ = (scale : ℝ) * x * ((scale : ℝ) * y) := by ring
      _ ≤ (upperProduct a b : ℝ) := hu'
      _ ≤ _ := by simpa only [Int.cast_neg] using hru

def certificateScale : ℤ := 2 ^ 384

theorem certificateScale_positive : 0 < certificateScale := by
  unfold certificateScale
  positivity

end Calabi.Certificate.Dyadic
