"""Untrusted high-precision numerics for the finite shot of the n = 7 profile.

Nothing in this file is part of a proof. It proposes polynomial certificates;
the exact integer checks in shot_checks.py (mirrored in Lean) decide whether a
proposal is accepted.

Block conventions. Block j has a power of two H and an odd integer A; the
block variable t runs over [-1, 1] and s = (A + t) / H. With sigma = A + t and
dots for d/dt, the profile equation is

    4 sigma^3 p''' + 84 sigma^2 p'' + 337 sigma p' - 567 (p - d)
        + (4 sigma^3 / H^3) p / (1 + p) = 0.
"""
import gmpy2
from gmpy2 import mpfr

PREC = 520
gmpy2.get_context().precision = PREC


def blocks():
    """(H, A) for the 576 blocks covering s in [1, 56]."""
    out = []
    for h, s0 in ((64, 1), (32, 2), (16, 4)):
        out += [(2 * h, 2 * (h * s0 + j) + 1) for j in range(64)]
    out += [(16, 2 * (64 + j) + 1) for j in range(8 * 48)]
    return out


def origin_jet(k, d, n=150):
    """Physical jet (p, p_s, p_ss) at s = 1 of the regular solution, and its
    derivatives with respect to k and d, from the series in r = s^(3/2)."""
    z = [[1 + d, mpfr(0), mpfr(1)], [k, mpfr(1), mpfr(0)]]
    b = []
    for i in range(n - 1):
        f = 1 / z[0][0]
        first = f if i == 0 else -f * sum(z[t][0] * b[i - t][0] for t in range(1, i + 1))
        q = [first]
        for j in (1, 2):
            acc = sum(z[t][j] * (first if t == 0 else b[i - t][0]) for t in range(i + 1))
            acc += sum(z[t][0] * b[i - t][j] for t in range(1, i + 1))
            q.append(-f * acc)
        b.append(q)
        den = mpfr(27 * (i + 1) * (i + 8) * (i + 9))
        z.append([8 * (q[j] - (1 if (i == 0 and j == 0) else 0)) / den for j in range(3)])
    cols = []
    for j in range(3):
        v = [mpfr(0)] * 3
        for i, c in enumerate(z):
            a = c[j] - (1 if (i == 0 and j == 0) else 0)
            e = mpfr(3 * i) / 2
            v[0] += a
            v[1] += a * e
            v[2] += a * e * (e - 1)
        cols.append(v)
    return cols[0], cols[1], cols[2]


def series(A, H, d, jets, dflags, n):
    """Taylor coefficients in t about a point with H s = A.

    jets[0] is the scaled jet (p, p', p'') of the solution; jets[c], c >= 1, are
    jets of solutions of the linearised equation, with unit forcing from the
    parameter d when dflags[c] is 1. Returns z[i][c] with column 0 holding the
    coefficients of 1 + p."""
    A = mpfr(A)
    A2, A3 = A * A, A * A * A
    H3 = mpfr(H) ** 3
    ncol = len(jets)
    z = [[None] * ncol for _ in range(3)]
    for c in range(ncol):
        z[0][c] = jets[c][0] + (1 if c == 0 else 0)
        z[1][c] = jets[c][1]
        z[2][c] = jets[c][2] / 2
    b, g = [], []
    zero = mpfr(0)
    for i in range(n - 2):
        f = 1 / z[0][0]
        b.append(f if i == 0 else -f * sum(z[t][0] * b[i - t] for t in range(1, i + 1)))
        if ncol > 1:
            g.append(sum(b[t] * b[i - t] for t in range(i + 1)))
        new = []
        for c in range(ncol):
            def Z(m):
                return z[m][c] if m >= 0 else zero

            def w3(m):
                return (m + 3) * (m + 2) * (m + 1) * z[m + 3][c] if m >= 0 else zero

            def w2(m):
                return (m + 2) * (m + 1) * z[m + 2][c] if m >= 0 else zero

            def w1(m):
                return (m + 1) * z[m + 1][c] if m >= 0 else zero

            if c == 0:
                def cc(m):
                    return ((1 if m == 0 else 0) - b[m]) if m >= 0 else zero
                const = (1 + d) if i == 0 else 0
            else:
                def cc(m, c=c):
                    return sum(g[t] * z[m - t][c] for t in range(m + 1)) if m >= 0 else zero
                const = dflags[c] if i == 0 else 0
            lhs = 4 * (3 * A2 * w3(i - 1) + 3 * A * w3(i - 2) + w3(i - 3))
            lhs += 84 * (A2 * w2(i) + 2 * A * w2(i - 1) + w2(i - 2))
            lhs += 337 * (A * w1(i) + w1(i - 1))
            lhs += -567 * (Z(i) - const)
            rhs = -(4 / H3) * (A3 * cc(i) + 3 * A2 * cc(i - 1) + 3 * A * cc(i - 2) + cc(i - 3))
            new.append((rhs - lhs) / (4 * A3 * (i + 3) * (i + 2) * (i + 1)))
        z.append(new)
    return z


def jet_at(z, c, x):
    """(value, first, second t-derivative) of column c at t = x."""
    n = len(z)
    v = d1 = d2 = mpfr(0)
    for i in reversed(range(n)):
        v = v * x + z[i][c]
    for i in reversed(range(1, n)):
        d1 = d1 * x + i * z[i][c]
    for i in reversed(range(2, n)):
        d2 = d2 * x + i * (i - 1) * z[i][c]
    return [v, d1, d2]


UNIT = [[mpfr(1), mpfr(0), mpfr(0)], [mpfr(0), mpfr(1), mpfr(0)],
        [mpfr(0), mpfr(0), mpfr(1)], [mpfr(0), mpfr(0), mpfr(0)]]


def block_series(H, A, d, start_jet, n_left, n_centre, tangents=True):
    """Centre expansion of the solution with scaled jet start_jet at t = -1, and
    of the four tangent solutions with unit data there."""
    jets = [start_jet] + (UNIT if tangents else [])
    flags = [0, 0, 0, 0, 1][:len(jets)]
    left = series(A - 1, H, d, jets, flags, n_left)
    centre = [jet_at(left, c, mpfr(1)) for c in range(len(jets))]
    centre[0][0] -= 1
    return series(A, H, d, centre, flags, n_centre)


def shoot(k, d, n_left=44, n_centre=34):
    """Float-style shot used for Newton: physical jet at s = 56 and its 3 x 2
    derivative with respect to (k, d)."""
    jet, dk, dd = origin_jet(k, d)
    # extended tangent: columns d/dk, d/dd of (jet, d)
    T = [[dk[a], dd[a]] for a in range(3)] + [[mpfr(0), mpfr(1)]]
    phys = jet
    for H, A in blocks():
        sj = [phys[0], phys[1] / H, phys[2] / H ** 2]
        zc = block_series(H, A, d, sj, n_left, n_centre)
        end = [jet_at(zc, c, mpfr(1)) for c in range(5)]
        end[0][0] -= 1
        # block transfer in physical coordinates, 3 x 4
        M = [[end[c + 1][a] * H ** a / (H ** c if c < 3 else 1) for c in range(4)] for a in range(3)]
        T = [[sum(M[a][c] * T[c][j] for c in range(4)) for j in range(2)] for a in range(3)] + [T[3]]
        phys = [end[0][0], end[0][1] * H, end[0][2] * H ** 2]
    return phys, T[:3]
