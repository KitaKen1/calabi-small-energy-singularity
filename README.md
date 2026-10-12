# Small-Energy Finite-Time Singularities of Calabi Flow

> [!NOTE]
> **Theorem.** There is a constant $`C_S`$ such that, for every $`2\le p<7`$ and $`\varepsilon,\tau>0`$, there is a smooth $`U(7)`$-invariant Kähler metric in the Fubini–Study class of $`\mathbb{CP}^7`$ whose maximal smooth Calabi flow satisfies
>
> ```math
> \|\phi_0\|_{C^0}<\varepsilon,\qquad
> 0<T_*<\tau,\qquad
> \sup_{0\le t<T_*}\|S(\omega(t))-56\|_{L^p(\nu_t)}<\varepsilon,
> ```
>
> has Sobolev constant at most $`C_S`$ throughout $`[0,T_*)`$, and has scalar curvature
>
> ```math
> S(\omega(t))(o)\sim a(T_*-t)^{-1/2},\qquad a>0,
> ```
>
> at one fixed point $`o`$.

Here $`\omega_*`$ has affine potential $`\log(1+|Z|^2)`$, $`\omega_0=\omega_*+i\partial\bar\partial\phi_0`$, and $`\nu_t`$ is the evolving volume measure normalized to total mass one. The Sobolev inequality is

```math
\|f\|_{L^{7/3}(\nu_t)}^2
\le C_S\bigl(\|\nabla f\|_{L^2(\nu_t)}^2+\|f\|_{L^2(\nu_t)}^2\bigr).
```

The same constant works for all the constructed examples. Taking $`p=2`$ gives arbitrarily small Calabi energy throughout the smooth existence interval. The Kähler class and total volume are fixed.

This repository presents a proposed proof. The [PDF manuscript](PDF/calabi-small-energy.pdf) contains the detailed argument.

## Proof sketch

### 1. Construct a positive shrinking profile

With $`D=y\partial_y`$, solve

```math
(D-1)(D+6)(D+7)(G-1)
=\frac{y^2}{2}\left(\frac1G-\frac1c\right),
\qquad G(0)=1,\quad G'(0)<0,\quad 0<c<1.
```

A rational interval computation encloses the finite shot. A contraction constructs the actual half-line solution, and a two-dimensional Brouwer argument matches their jets. This gives a smooth profile bounded above and away from zero, with a differentiated expansion at infinity.

### 2. Localize the model while preserving positivity

Use momentum coordinate $`x\in[0,1]`$ and write

```math
v=x(1-x)+x^2(1-x)^2H,\qquad
F_\lambda(t,x)=\chi(x/\lambda)\rho^{-1}h(x/\rho),
\quad \rho=\sqrt{-t},\quad h(y)=\frac{G(y)-1}{y}.
```

The multiplier $`1+x(1-x)F_\lambda`$ is a convex combination of positive bounded quantities. The model agrees with the shrinking core near the origin and with the stationary reference metric outside the cutoff region.

### 3. Correct the localized model to an exact flow

The cutoff residual can be large. Fix $`\lambda`$ first. Combine the ancient inner inverse with an outer inverse having zero initial data, and cancel the inner cutoff commutator in the outer forcing. The remaining operator error is small when the inner radius and the time interval are small.

The corrected residual is small in a weighted norm controlling four spatial derivatives and their temporal Hölder seminorms. The exponent gap $`0<\alpha<\alpha'<1`$ gives the required smallness of the fourth derivatives. A contraction then produces the exact solution $`H=F_\lambda+V`$.

### 4. Estimate the exact metric

The normalized radial volume density is $`7x^6\,dx`$. For any prescribed $`p<7`$,

```math
\sup_t\|S-56\|_{L^p(\nu_t)}
\le C_p\lambda^{7/p-1}+C_p\|V\|_{X'}.
```

The Legendre transform gives a small initial global potential. In momentum coordinates, the radial, Hopf and horizontal metric components have ratios $`b^{-1},b,1`$ to the reference metric, where $`b`$ has fixed positive lower and upper bounds. The corresponding volume forms agree, yielding one common Sobolev bound.

### 5. Identify the maximal time

The correction is lower order at the fixed origin, so the scalar curvature diverges with the stated rate. Smooth uniqueness identifies the constructed solution with the maximal smooth Calabi flow. Its divergence prevents continuation through the terminal time.

## Verification

From the repository root, with Python 3 and assertions enabled:

```sh
python3 -B verification/profile7/calabi7_verify.py
```

Do not use `-O` or `-OO`, and ensure `PYTHONOPTIMIZE` is unset. The checker recomputes 576 blocks using degree-58 Taylor enclosures and 384-bit integer interval arithmetic. It uses the Python standard library; `gmpy2` is an optional integer accelerator. Previously saved binary trajectories are not used by this command.

The finite arithmetic checks were rerun successfully on 12 October 2026. They verify the computational lemmas used in the profile construction; the analytic and geometric proof is in the manuscript. This repository does not contain a Lean formalization.

## Conclusion

The proposed construction shows that arbitrarily small Calabi energy and a common Sobolev bound can coexist with finite-time singularity formation in a fixed class on $`\mathbb{CP}^7`$. The strong $`L^7`$ curvature norm diverges logarithmically, so the critical strong-$`L^7`$ continuation question remains outside this result.

## Detailed manuscript

- [PDF manuscript](PDF/calabi-small-energy.pdf)

Draft 1, 12 October 2026.
