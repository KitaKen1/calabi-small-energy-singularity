import Calabi.Geometry.FubiniStudySobolev
import Calabi.Correction.Assembly

/-!
# The main theorem

`Calabi.mainTheorem` is Theorem 1.1 of the manuscript *Small-energy
finite-time singularities of Calabi flow*, in the form
`Calabi.Geometry.MainTheorem` of `Geometry/Statement.lean`, with no
hypothesis: on `CP⁷` with the Fubini–Study class there is one Sobolev constant
such that for every `p ∈ [2, 7)`, every `ε > 0` and every `τ > 0` there is a
`U(7)`-invariant Calabi flow on `[0, T)`, `T < τ`, whose potential is
`ε`-small away from one point at the initial time, with
`‖S - 56‖_{L^p} < ε` and the Sobolev bound throughout the flow, and whose
scalar curvature at the point blows up like `a / √(T - t)`, `a > 0`.

The proof joins the three parts of the formalization:

* `Calabi.exists_profile` (Theorem 3.1): the seven-dimensional shrinking
  profile, by the finite-interval certificate and the two asymptotic regimes;
* `Calabi.Weighted.localizedCorrection` (Proposition 6.1): the correction of
  the localized profile to an exact solution of the flow in the momentum
  coordinate;
* `Calabi.Geometry.mainTheorem_of_forall_localizedCorrection` (Sections 2 and
  7): the passage from the momentum coordinate to `CP⁷`, the small energy and
  the Sobolev inequality.
-/

namespace Calabi

/-- **Theorem 1.1 of the manuscript: small-energy finite-time singularities
of the Calabi flow on `CP⁷`.** -/
theorem mainTheorem : Geometry.MainTheorem :=
  Geometry.mainTheorem_of_forall_localizedCorrection fun _ _ hP =>
    Weighted.localizedCorrection hP

/-- The case `p = 2`: arbitrarily small Calabi energy. -/
theorem mainTheoremEnergy : Geometry.MainTheoremEnergy :=
  mainTheorem.energy

end Calabi
