import Calabi.Shot.FiniteShot
import Calabi.Shot.Existence

/-!
# The finite shot `1 ≤ s ≤ 56`

Entry point for the finite-interval part of the profile theorem.

* `Calabi.Shot.exists_trajectory`, `Calabi.Shot.traj`: every initial jet at
  `s = 1` and every parameter `d` has a trajectory of the clamped profile
  system on `[1, 56]`, with Lipschitz dependence (`traj_dist_le`).
* `Calabi.Shot.finite_shot`: for every parameter of the box
  `|z₁|, |z₂| ≤ 2^-56`, a trajectory that starts within the first remainder
  bound keeps `p ≥ -19/20` on `[1, 56]`, so that the clamp is inactive, and its
  jet at `s = 56` lies in the last remainder bound.

The data in `Calabi.Shot.Data` are proposals of untrusted numerics. What is
used about them is what the kernel recomputes: `ok0`, …, `ok575` (one block
each), `chain_ok`, `chain_start`, `chain_end` and `sums_range`.
-/
