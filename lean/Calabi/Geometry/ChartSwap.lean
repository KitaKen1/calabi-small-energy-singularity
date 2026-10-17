import Calabi.Geometry.Dilation
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The transition maps between the charts of `CP⁷`

In the coordinates of the chart `0`, the exchange of the homogeneous
coordinates `v₀` and `v_{m+1}` is the map

  `τ_m(Z) = Z_m⁻¹ (Z + (1 - Z_m) e_m)`,

an involution of `{Z_m ≠ 0}`. It is a holomorphic isometry of the Fubini–Study
metric:

* `lintegral_tau`: it preserves the Fubini–Study volume `(1 + ‖Z‖²)⁻⁸ dZ`; the
  complex Jacobian is `-Z_m⁻⁸` (`det_tauDeriv`) and
  `1 + ‖τ_m Z‖² = (1 + ‖Z‖²) / |Z_m|²`;
* `quad_tau`: it preserves the Fubini–Study quadratic form;
* `gradSq_tau_le`: `|∇(F ∘ τ_m)|² ≤ |∇F|² ∘ τ_m` for the Fubini–Study metric.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Calabi.Geometry

/-! ### A determinant over a field -/

theorem det_smul_one_add_vecMulVec' {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {c : K}
    (hc : c ≠ 0) (w v : ι → K) :
    (c • (1 : Matrix ι ι K) + Matrix.vecMulVec w v).det
      = c ^ Fintype.card ι * (1 + c⁻¹ * (v ⬝ᵥ w)) := by
  have e : c • (1 : Matrix ι ι K) + Matrix.vecMulVec w v
      = c • (1 + Matrix.replicateCol Unit (c⁻¹ • w) * Matrix.replicateRow Unit v) := by
    rw [← Matrix.vecMulVec_eq Unit]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Pi.smul_apply]
    field_simp
  rw [e, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul]

/-- The complex determinant of `c + w ⊗ φ` on `ℂ⁷`. -/
theorem det_complex_smul_id_add_smulRight {c : ℂ} (hc : c ≠ 0) (φ : Aff →L[ℂ] ℂ) (w : Aff) :
    LinearMap.det ((c • ContinuousLinearMap.id ℂ Aff + φ.smulRight w : Aff →L[ℂ] Aff)
      : Aff →ₗ[ℂ] Aff) = c ^ 7 * (1 + c⁻¹ * φ w) := by
  have hd := LinearMap.det_toMatrix (Module.finBasis ℂ Aff)
    ((c • ContinuousLinearMap.id ℂ Aff + φ.smulRight w : Aff →L[ℂ] Aff) : Aff →ₗ[ℂ] Aff)
  have hcard : Fintype.card (Fin (Module.finrank ℂ Aff)) = 7 := by
    rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin]
  have hmat : LinearMap.toMatrix (Module.finBasis ℂ Aff) (Module.finBasis ℂ Aff)
      ((c • ContinuousLinearMap.id ℂ Aff + φ.smulRight w : Aff →L[ℂ] Aff) : Aff →ₗ[ℂ] Aff)
      = c • (1 : Matrix _ _ ℂ) + Matrix.vecMulVec
        (fun i => (Module.finBasis ℂ Aff).repr w i) (fun j => φ (Module.finBasis ℂ Aff j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [Matrix.vecMulVec_apply, Matrix.one_apply, Finsupp.single_apply, mul_comm, eq_comm]
  have hdot : (fun j => φ ((Module.finBasis ℂ Aff) j))
      ⬝ᵥ (fun i => (Module.finBasis ℂ Aff).repr w i) = φ w := by
    have hw := (Module.finBasis ℂ Aff).sum_repr w
    calc (fun j => φ ((Module.finBasis ℂ Aff) j)) ⬝ᵥ (fun i => (Module.finBasis ℂ Aff).repr w i)
        = ∑ i, (Module.finBasis ℂ Aff).repr w i * φ ((Module.finBasis ℂ Aff) i) := by
          simp [dotProduct, mul_comm]
      _ = φ (∑ i, (Module.finBasis ℂ Aff).repr w i • (Module.finBasis ℂ Aff) i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = φ w := by rw [hw]
  rw [← hd, hmat, det_smul_one_add_vecMulVec' hc, hcard, hdot]

/-! ### The map -/

/-- The coordinate vector `e_m`. -/
noncomputable def evec (m : Fin 7) : Aff := EuclideanSpace.single m (1 : ℂ)

/-- The transition map between the chart `0` and the chart `m + 1`, in the
coordinates of the chart `0`. -/
noncomputable def tau (m : Fin 7) (Z : Aff) : Aff := (Z m)⁻¹ • (Z + (1 - Z m) • evec m)

theorem evec_apply_self (m : Fin 7) : evec m m = 1 := by
  simp [evec]

theorem evec_apply_ne {m k : Fin 7} (h : k ≠ m) : evec m k = 0 := by
  simp [evec, h]

theorem tau_apply_self (m : Fin 7) (Z : Aff) : tau m Z m = (Z m)⁻¹ := by
  show (Z m)⁻¹ * (Z m + (1 - Z m) * evec m m) = (Z m)⁻¹
  rw [evec_apply_self]
  ring

theorem tau_apply_ne {m k : Fin 7} (h : k ≠ m) (Z : Aff) : tau m Z k = (Z m)⁻¹ * Z k := by
  show (Z m)⁻¹ * (Z k + (1 - Z m) * evec m k) = (Z m)⁻¹ * Z k
  rw [evec_apply_ne h]
  ring

theorem tau_tau {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) : tau m (tau m Z) = Z := by
  ext k
  by_cases hk : k = m
  · subst hk
    rw [tau_apply_self, tau_apply_self, inv_inv]
  · rw [tau_apply_ne hk, tau_apply_self, tau_apply_ne hk, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ hZ, one_mul]

theorem tau_coord_ne_zero {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) : tau m Z m ≠ 0 := by
  rw [tau_apply_self]
  exact inv_ne_zero hZ

/-- `1 + ‖τ Z‖² = (1 + ‖Z‖²) / |Z_m|²`. -/
theorem one_add_norm_tau_sq {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) :
    1 + ‖tau m Z‖ ^ 2 = (1 + ‖Z‖ ^ 2) / ‖Z m‖ ^ 2 := by
  have hn : ‖Z m‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hZ)
  have h1 : ∑ k, ‖tau m Z k‖ ^ 2
      = (‖Z m‖ ^ 2)⁻¹ * (1 + ∑ k ∈ Finset.univ.erase m, ‖Z k‖ ^ 2) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m), tau_apply_self, mul_add,
      mul_one, Finset.mul_sum]
    congr 1
    · rw [norm_inv, inv_pow]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [tau_apply_ne (Finset.ne_of_mem_erase hk), norm_mul, norm_inv, mul_pow, inv_pow]
  have h2 : ∑ k, ‖Z k‖ ^ 2 = ‖Z m‖ ^ 2 + ∑ k ∈ Finset.univ.erase m, ‖Z k‖ ^ 2 :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m)).symm
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, h1, h2]
  field_simp
  ring

/-! ### The derivative -/

/-- The complex derivative of `tau m` at `Z`. -/
noncomputable def tauDeriv (m : Fin 7) (Z : Aff) : Aff →L[ℂ] Aff :=
  (Z m)⁻¹ • ContinuousLinearMap.id ℂ Aff
    + ((-((Z m)⁻¹) ^ 2) • (EuclideanSpace.proj m : Aff →L[ℂ] ℂ)).smulRight (Z + evec m)

theorem tauDeriv_apply (m : Fin 7) (Z a : Aff) :
    tauDeriv m Z a = (Z m)⁻¹ • a + (-((Z m)⁻¹) ^ 2 * a m) • (Z + evec m) := rfl

theorem hasFDerivAt_tau {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) :
    HasFDerivAt (tau m) ((tauDeriv m Z).restrictScalars ℝ) Z := by
  obtain ⟨P, hP⟩ : ∃ P : Aff →L[ℝ] ℂ,
      P = (EuclideanSpace.proj m : Aff →L[ℂ] ℂ).restrictScalars ℝ := ⟨_, rfl⟩
  have hPa : ∀ a : Aff, P a = a m := fun a => by rw [hP]; rfl
  have hc : HasFDerivAt (fun W : Aff => (P W)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(P Z ^ 2)⁻¹)).restrictScalars ℝ).comp
        P) Z := by
    have h1 : HasFDerivAt (fun y : ℂ => y⁻¹)
        (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(P Z ^ 2)⁻¹)) (P Z) :=
      (hasDerivAt_inv (by rw [hPa]; exact hZ)).hasFDerivAt
    exact (h1.restrictScalars ℝ).comp Z P.hasFDerivAt
  have hf : HasFDerivAt (fun W : Aff => W - (P W) • evec m + evec m)
      (ContinuousLinearMap.id ℝ Aff - P.smulRight (evec m)) Z :=
    ((hasFDerivAt_id Z).sub (P.smulRight (evec m)).hasFDerivAt).add_const (evec m)
  have h0 := hc.smul hf
  have h : HasFDerivAt (fun W : Aff => (P W)⁻¹ • (W - (P W) • evec m + evec m)) _ Z := h0
  have hfun : (fun W : Aff => (P W)⁻¹ • (W - (P W) • evec m + evec m)) = tau m := by
    funext W
    rw [hPa]
    show (W m)⁻¹ • (W - (W m) • evec m + evec m) = (W m)⁻¹ • (W + (1 - W m) • evec m)
    congr 1
    rw [sub_smul, one_smul]
    abel
  rw [hfun] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun a => ?_
  show (P Z)⁻¹ • (a - (P a) • evec m) + ((P a) * (-(P Z ^ 2)⁻¹)) • (Z - (P Z) • evec m + evec m)
    = (Z m)⁻¹ • a + (-((Z m)⁻¹) ^ 2 * a m) • (Z + evec m)
  rw [hPa, hPa]
  ext k
  by_cases hk : k = m
  · subst hk
    show (Z k)⁻¹ * (a k - a k * evec k k) + a k * (-(Z k ^ 2)⁻¹) * (Z k - Z k * evec k k + evec k k)
      = (Z k)⁻¹ * a k + -((Z k)⁻¹) ^ 2 * a k * (Z k + evec k k)
    rw [evec_apply_self]
    field_simp
    ring
  · show (Z m)⁻¹ * (a k - a m * evec m k) + a m * (-(Z m ^ 2)⁻¹) * (Z k - Z m * evec m k + evec m k)
      = (Z m)⁻¹ * a k + -((Z m)⁻¹) ^ 2 * a m * (Z k + evec m k)
    rw [evec_apply_ne hk]
    field_simp
    ring

/-- The real Jacobian determinant of `tau m`: `|Z_m|⁻¹⁶`. -/
theorem det_tauDeriv {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) :
    ((tauDeriv m Z).restrictScalars ℝ).det = (‖Z m‖ ^ 16)⁻¹ := by
  have h1 : ((tauDeriv m Z).restrictScalars ℝ).det
      = LinearMap.det (((tauDeriv m Z : Aff →L[ℂ] Aff) : Aff →ₗ[ℂ] Aff).restrictScalars ℝ) := rfl
  rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  unfold tauDeriv
  rw [det_complex_smul_id_add_smulRight (inv_ne_zero hZ)]
  have hφ : ((-((Z m)⁻¹) ^ 2) • (EuclideanSpace.proj m : Aff →L[ℂ] ℂ)) (Z + evec m)
      = -((Z m)⁻¹) ^ 2 * (Z m + 1) := by
    show -((Z m)⁻¹) ^ 2 * (Z m + evec m m) = _
    rw [evec_apply_self]
  rw [hφ]
  have e : (Z m)⁻¹ ^ 7 * (1 + ((Z m)⁻¹)⁻¹ * (-((Z m)⁻¹) ^ 2 * (Z m + 1))) = -((Z m)⁻¹) ^ 8 := by
    field_simp
    ring
  rw [e, Complex.normSq_neg, map_pow, map_inv₀, Complex.normSq_eq_norm_sq, inv_pow, ← pow_mul]

/-! ### The Fubini–Study volume -/

theorem measure_coord_zero (m : Fin 7) : (volume : Measure Aff) {Z : Aff | Z m = 0} = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Aff →ₗ[ℝ] ℂ, P = (((EuclideanSpace.proj m : Aff →L[ℂ] ℂ).restrictScalars
      ℝ : Aff →L[ℝ] ℂ) : Aff →ₗ[ℝ] ℂ) := ⟨_, rfl⟩
  have hPa : ∀ a : Aff, P a = a m := fun a => by rw [hP]; rfl
  have h : ({Z : Aff | Z m = 0} : Set Aff) = (LinearMap.ker P : Set Aff) := by
    ext Z
    simp [hPa]
  rw [h]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have hmem : evec m ∈ LinearMap.ker P := by
    rw [htop]
    trivial
  rw [LinearMap.mem_ker, hPa, evec_apply_self] at hmem
  exact one_ne_zero hmem

/-- **`τ_m` preserves the Fubini–Study volume.** -/
theorem lintegral_tau (m : Fin 7) (g : Aff → ℝ≥0∞) :
    ∫⁻ Z : Aff, ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z)
      = ∫⁻ W : Aff, ENNReal.ofReal (((1 + ‖W‖ ^ 2) ^ 8)⁻¹) * g W := by
  obtain ⟨U, hU⟩ : ∃ U : Set Aff, U = {Z : Aff | Z m ≠ 0} := ⟨_, rfl⟩
  have hmemU : ∀ Z : Aff, Z ∈ U ↔ Z m ≠ 0 := fun Z => by rw [hU]; rfl
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_ne_fun ((EuclideanSpace.proj m : Aff →L[ℂ] ℂ).continuous) continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hae : ∀ᵐ Z ∂(volume : Measure Aff), Z ∈ U := by
    rw [ae_iff]
    have e : {Z : Aff | ¬Z ∈ U} = {Z : Aff | Z m = 0} := by
      ext Z
      simp [hmemU]
    rw [e]
    exact measure_coord_zero m
  have hres : (volume : Measure Aff).restrict U = volume := Measure.restrict_eq_self_of_ae_mem hae
  have himg : tau m '' U = U := by
    ext W
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact (hmemU _).2 (tau_coord_ne_zero ((hmemU Z).1 hZ))
    · intro hW
      exact ⟨tau m W, (hmemU _).2 (tau_coord_ne_zero ((hmemU W).1 hW)), tau_tau ((hmemU W).1 hW)⟩
  have hinj : InjOn (tau m) U := by
    intro Z₁ h₁ Z₂ h₂ h
    rw [← tau_tau ((hmemU Z₁).1 h₁), ← tau_tau ((hmemU Z₂).1 h₂), h]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure Aff) hUmeas
    (fun Z hZ => (hasFDerivAt_tau ((hmemU Z).1 hZ)).hasFDerivWithinAt) hinj
    (fun W => ENNReal.ofReal (((1 + ‖W‖ ^ 2) ^ 8)⁻¹) * g W)
  rw [himg] at hcv
  have hpt : ∀ Z ∈ U, ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z)
      = ENNReal.ofReal |((tauDeriv m Z).restrictScalars ℝ).det|
        * (ENNReal.ofReal (((1 + ‖tau m Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z)) := by
    intro Z hZ
    have hZm := (hmemU Z).1 hZ
    have hn : 0 < ‖Z m‖ := norm_pos_iff.2 hZm
    rw [det_tauDeriv hZm, abs_of_pos (inv_pos.2 (pow_pos hn 16)), ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_pos.2 (pow_pos hn 16)).le, one_add_norm_tau_sq hZm]
    congr 2
    have hs : (1 + ‖Z‖ ^ 2) ≠ 0 := by positivity
    have hn' := hn.ne'
    generalize 1 + ‖Z‖ ^ 2 = s at hs ⊢
    generalize ‖Z m‖ = n at hn' ⊢
    field_simp
  calc ∫⁻ Z : Aff, ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z)
      = ∫⁻ Z in U, ENNReal.ofReal (((1 + ‖Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z) := by rw [hres]
    _ = ∫⁻ Z in U, ENNReal.ofReal |((tauDeriv m Z).restrictScalars ℝ).det|
          * (ENNReal.ofReal (((1 + ‖tau m Z‖ ^ 2) ^ 8)⁻¹) * g (tau m Z)) :=
        setLIntegral_congr_fun hUmeas hpt
    _ = ∫⁻ W in U, ENNReal.ofReal (((1 + ‖W‖ ^ 2) ^ 8)⁻¹) * g W := hcv.symm
    _ = ∫⁻ W : Aff, ENNReal.ofReal (((1 + ‖W‖ ^ 2) ^ 8)⁻¹) * g W := by rw [hres]

/-! ### The Fubini–Study metric -/

theorem inner_evec_left (m : Fin 7) (a : Aff) : (inner ℂ (evec m) a : ℂ) = a m := by
  unfold evec
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

theorem inner_evec_right (m : Fin 7) (a : Aff) :
    (inner ℂ a (evec m) : ℂ) = (starRingEnd ℂ) (a m) := by
  unfold evec
  rw [EuclideanSpace.inner_single_right, one_mul]

theorem inner_self_ofReal (v : Aff) : (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The algebraic identity behind `quad_tau`. -/
theorem quad_tau_aux {z zb am ab X Xb q A nb nM : ℂ} (hz : z ≠ 0) (hzb : zb ≠ 0)
    (hs : 1 + q ≠ 0)
    (hnb : nb = z⁻¹ * zb⁻¹ * (A - zb⁻¹ * ab * X - z⁻¹ * am * Xb
      + z⁻¹ * am * (zb⁻¹ * ab) * (1 + q)))
    (hnM : nM = z⁻¹ * zb⁻¹ * (X - (1 + q) * (z⁻¹ * am))
      * (zb⁻¹ * z⁻¹ * (Xb - (1 + q) * (zb⁻¹ * ab)))) :
    1 * ((1 + q) / (z * zb))⁻¹ * nb + 1 * (-1 / ((1 + q) / (z * zb)) ^ 2) * nM
      = 1 * (1 + q)⁻¹ * A + 1 * (-1 / (1 + q) ^ 2) * (X * Xb) := by
  subst hnb hnM
  generalize 1 + q = s at hs ⊢
  field_simp
  ring

/-- **`τ_m` is an isometry of the Fubini–Study metric.** -/
theorem quad_tau {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) (a : Aff) :
    quad (1 * (1 + ‖tau m Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖tau m Z‖ ^ 2) ^ 2)) (tau m Z)
        (tauDeriv m Z a)
      = quad (1 * (1 + ‖Z‖ ^ 2)⁻¹) (1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2)) Z a := by
  have hZb : (starRingEnd ℂ) (Z m) ≠ 0 := (map_ne_zero _).2 hZ
  have hZZ := inner_self_ofReal Z
  have haa := inner_self_ofReal a
  have hs : (1 : ℂ) + ((‖Z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < 1 + ‖Z‖ ^ 2 := by positivity
    exact_mod_cast h.ne'
  -- the two inner products
  have hM : (inner ℂ (tau m Z) (tauDeriv m Z a) : ℂ)
      = (Z m)⁻¹ * ((starRingEnd ℂ) (Z m))⁻¹
        * (inner ℂ Z a - (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ)) * ((Z m)⁻¹ * a m)) := by
    rw [tauDeriv_apply]
    unfold tau
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_evec_left, inner_evec_right, evec_apply_self, hZZ, map_inv₀, map_sub, map_one]
    generalize ((‖Z‖ ^ 2 : ℝ) : ℂ) = q
    field_simp
    ring
  have hN : (inner ℂ (tauDeriv m Z a) (tauDeriv m Z a) : ℂ)
      = (Z m)⁻¹ * ((starRingEnd ℂ) (Z m))⁻¹
        * (((‖a‖ ^ 2 : ℝ) : ℂ) - ((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m) * inner ℂ Z a
          - (Z m)⁻¹ * a m * inner ℂ a Z
          + (Z m)⁻¹ * a m * (((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m))
            * (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ))) := by
    rw [tauDeriv_apply]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_evec_left, inner_evec_right, evec_apply_self, hZZ, haa, map_inv₀, map_mul, map_neg,
      map_pow, map_one]
    generalize ((‖Z‖ ^ 2 : ℝ) : ℂ) = q
    generalize ((‖a‖ ^ 2 : ℝ) : ℂ) = A
    field_simp
    ring
  have hMc : (starRingEnd ℂ) (inner ℂ (tau m Z) (tauDeriv m Z a) : ℂ)
      = ((starRingEnd ℂ) (Z m))⁻¹ * (Z m)⁻¹
        * (inner ℂ a Z - (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ))
          * (((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m))) := by
    rw [hM]
    simp only [map_mul, map_sub, map_add, map_one, map_inv₀, Complex.conj_conj,
      Complex.conj_ofReal, inner_conj_symm]
  have hnb : ((‖tauDeriv m Z a‖ ^ 2 : ℝ) : ℂ)
      = (Z m)⁻¹ * ((starRingEnd ℂ) (Z m))⁻¹
        * (((‖a‖ ^ 2 : ℝ) : ℂ) - ((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m) * inner ℂ Z a
          - (Z m)⁻¹ * a m * inner ℂ a Z
          + (Z m)⁻¹ * a m * (((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m))
            * (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ))) := by
    rw [← inner_self_ofReal, hN]
  have hnM : ((‖(inner ℂ (tau m Z) (tauDeriv m Z a) : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = (Z m)⁻¹ * ((starRingEnd ℂ) (Z m))⁻¹
          * (inner ℂ Z a - (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ)) * ((Z m)⁻¹ * a m))
        * (((starRingEnd ℂ) (Z m))⁻¹ * (Z m)⁻¹
          * (inner ℂ a Z - (1 + ((‖Z‖ ^ 2 : ℝ) : ℂ))
            * (((starRingEnd ℂ) (Z m))⁻¹ * (starRingEnd ℂ) (a m)))) := by
    rw [← hM, ← hMc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hzz : Z m * (starRingEnd ℂ) (Z m) = ((‖Z m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hXX : (inner ℂ Z a : ℂ) * inner ℂ a Z = ((‖(inner ℂ Z a : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm a Z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key := quad_tau_aux (z := Z m) (zb := (starRingEnd ℂ) (Z m)) (am := a m)
    (ab := (starRingEnd ℂ) (a m)) (X := inner ℂ Z a) (Xb := inner ℂ a Z)
    (q := ((‖Z‖ ^ 2 : ℝ) : ℂ)) (A := ((‖a‖ ^ 2 : ℝ) : ℂ)) hZ hZb hs hnb hnM
  rw [hzz, hXX] at key
  unfold quad
  rw [one_add_norm_tau_sq hZ]
  exact_mod_cast key

/-! ### Gradient norms under a change of variables -/

/-- Comparison of gradient norms under a change of variables which does not
increase the metric by more than the factor `Λ`. -/
theorem gradSq_comp_le {u₀ u₁ F : Aff → ℝ} {θ : Aff → Aff} {θ' : Aff →L[ℝ] Aff} {Z : Aff}
    {α₀ β₀ α₁ β₁ Λ : ℝ}
    (hg0 : gmat u₀ Z = (α₀ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β₀ : ℂ) • Matrix.vecMulVec (fun j => star (Z j)) (fun k => Z k))
    (hα0 : 0 < α₀) (hαβ0 : 0 < α₀ + β₀ * ‖Z‖ ^ 2)
    (hg1 : gmat u₁ (θ Z) = (α₁ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      + (β₁ : ℂ) • Matrix.vecMulVec (fun j => star (θ Z j)) (fun k => θ Z k))
    (hα1 : 0 < α₁) (hαβ1 : 0 < α₁ + β₁ * ‖θ Z‖ ^ 2)
    (hθ : HasFDerivAt θ θ' Z) (hF : DifferentiableAt ℝ F (θ Z)) (hΛ : 0 ≤ Λ)
    (hq : ∀ c : Aff, quad α₁ β₁ (θ Z) (θ' c) ≤ Λ * quad α₀ β₀ Z c) :
    gradSq u₀ (fun W => F (θ W)) Z ≤ Λ * gradSq u₁ F (θ Z) := by
  have hchain : ∀ c : Aff, fderiv ℝ (fun W => F (θ W)) Z c = fderiv ℝ F (θ Z) (θ' c) := by
    intro c
    have h := (hF.hasFDerivAt.comp Z hθ).fderiv
    have h' : fderiv ℝ (fun W => F (θ W)) Z = _ := h
    rw [h']
    rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Aff, c₀ = gradVec α₀ β₀ Z (dz (fun W => F (θ W)) Z) := ⟨_, rfl⟩
  have e1 : fderiv ℝ (fun W => F (θ W)) Z c₀ = gradSq u₀ (fun W => F (θ W)) Z := by
    rw [hc₀]
    exact fderiv_gradVec hg0 hα0 hαβ0
  have e2 : 2 * quad α₀ β₀ Z c₀ = gradSq u₀ (fun W => F (θ W)) Z := by
    rw [hc₀, quad_gradVec hα0 hαβ0, gradSq_rank_one hg0 hα0 hαβ0]
  have hcs := sq_fderiv_le (F := F) hg1 hα1 hαβ1 (θ' c₀)
  rw [← hchain c₀, e1] at hcs
  have hcmp := hq c₀
  have hg0nn := gradSq_nonneg (F := fun W => F (θ W)) hg0 hα0 hαβ0
  have hg1nn := gradSq_nonneg (F := F) hg1 hα1 hαβ1
  have hfin : gradSq u₀ (fun W => F (θ W)) Z ^ 2
      ≤ Λ * gradSq u₁ F (θ Z) * gradSq u₀ (fun W => F (θ W)) Z := by
    have h3 : gradSq u₁ F (θ Z) * (2 * quad α₁ β₁ (θ Z) (θ' c₀))
        ≤ gradSq u₁ F (θ Z) * (2 * (Λ * quad α₀ β₀ Z c₀)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg1nn
    calc _ ≤ _ := hcs
      _ ≤ _ := h3
      _ = _ := by
        rw [← e2]
        ring
  rcases eq_or_lt_of_le hg0nn with h0 | h0
  · rw [← h0]
    exact mul_nonneg hΛ hg1nn
  · have h4 : gradSq u₀ (fun W => F (θ W)) Z * gradSq u₀ (fun W => F (θ W)) Z
        ≤ Λ * gradSq u₁ F (θ Z) * gradSq u₀ (fun W => F (θ W)) Z := by
      rw [← pow_two]
      exact hfin
    exact le_of_mul_le_mul_right h4 h0

/-- Positivity of the coefficients of the Fubini–Study metric. -/
theorem fubiniStudy_pos (Z : Aff) : (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ ∧
    (0 : ℝ) < 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2 := by
  refine ⟨by positivity, ?_⟩
  have e : 1 * (1 + ‖Z‖ ^ 2)⁻¹ + 1 * (-1 / (1 + ‖Z‖ ^ 2) ^ 2) * ‖Z‖ ^ 2
      = 1 / (1 + ‖Z‖ ^ 2) ^ 2 := by
    field_simp
    ring
  rw [e]
  positivity

/-- `|∇(F ∘ τ_m)|² ≤ |∇F|² ∘ τ_m` for the Fubini–Study metric. -/
theorem gradSq_tau_le {m : Fin 7} {Z : Aff} (hZ : Z m ≠ 0) {F : Aff → ℝ}
    (hF : DifferentiableAt ℝ F (tau m Z)) :
    gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) (fun W => F (tau m W)) Z
      ≤ gradSq (fun W : Aff => 1 * Real.log (1 + ‖W‖ ^ 2)) F (tau m Z) := by
  have h := gradSq_comp_le (F := F) (θ := tau m) (Λ := 1) (gmat_log 1 Z) (fubiniStudy_pos Z).1
    (fubiniStudy_pos Z).2 (gmat_log 1 (tau m Z)) (fubiniStudy_pos (tau m Z)).1
    (fubiniStudy_pos (tau m Z)).2 (hasFDerivAt_tau hZ) hF zero_le_one
    (fun c => (quad_tau hZ c).le.trans_eq (one_mul _).symm)
  rwa [one_mul] at h

end Calabi.Geometry
