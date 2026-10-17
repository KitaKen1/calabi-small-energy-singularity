"""Untrusted numerics at s = 56: frozen cubic, jet projection, formal tail.

Used only to locate the shooting centre. The proof obligations at s = 56 are
stated and checked elsewhere.
"""
from fractions import Fraction as F
import gmpy2
from gmpy2 import mpfr, mpc

S0 = 56
ALPHA = F(21, 2 * S0)
BETA = F(337, 8 * S0 ** 2)
GAMMA = 1 - F(567, 8 * S0 ** 3)


def to_mpfr(x):
    return mpfr(x.numerator) / mpfr(x.denominator)


def cubic_roots():
    """(r0, u, v): the roots of the frozen cubic are -r0 and u +- i v."""
    a, b, c = to_mpfr(ALPHA), to_mpfr(BETA), to_mpfr(GAMMA)
    x = mpfr("-1.0616768563045")
    for _ in range(12):
        x = x - (x ** 3 + a * x * x + b * x + c) / (3 * x * x + 2 * a * x + b)
    r0 = -x
    u = (r0 - a) / 2
    v = gmpy2.sqrt(c / r0 - u * u)
    return r0, u, v


def projection():
    """Real 3 x 3 matrix sending a jet (V, V', V'') to (q, Re xi, Im xi)."""
    r0, u, v = cubic_roots()
    lam = [mpc(-r0, 0), mpc(u, v), mpc(u, -v)]
    rows = []
    for i in range(3):
        others = [lam[j] for j in range(3) if j != i]
        den = (lam[i] - others[0]) * (lam[i] - others[1])
        rows.append([others[0] * others[1] / den, -(others[0] + others[1]) / den, 1 / den])
    return [[x.real for x in rows[0]], [x.real for x in rows[1]], [x.imag for x in rows[1]]]


def formal_tail(order=6):
    """Coefficients a_j(d), as polynomials in d, of p_a = sum_j a_j s^(-3j)."""
    def add(a, b):
        return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b)))]

    def mul(a, b):
        c = [F(0)] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i + j] += x * y
        return c

    def smul(a, c):
        return [x * c for x in a]

    a = [[F(0)] for _ in range(order + 1)]
    b = [[F(0)] for _ in range(order + 1)]
    b[0] = [F(1)]
    a[1] = [F(0), -F(567, 4)]
    b[1] = smul(a[1], -1)
    for j in range(2, order + 1):
        v = -3 * (j - 1)
        L = F(v * (v - 1) * (v - 2) + 21 * v * (v - 1)) + F(337, 4) * v - F(567, 4)
        cross = [F(0)]
        for k in range(1, j):
            cross = add(cross, mul(a[k], b[j - k]))
        a[j] = add(smul(a[j - 1], -L), smul(cross, -1))
        b[j] = add(smul(a[j], -1), smul(cross, -1))
    return a


def tail_jet(d, order=6):
    """Jet (p_a, p_a', p_a'') at s = 56 and its d-derivative."""
    a = formal_tail(order)
    jet = [mpfr(0)] * 3
    djet = [mpfr(0)] * 3
    for j in range(1, order + 1):
        val = mpfr(0)
        dval = mpfr(0)
        for i in reversed(range(len(a[j]))):
            dval = dval * d + val
            val = val * d + to_mpfr(a[j][i])
        for i, factor in enumerate([1, -3 * j, 3 * j * (3 * j + 1)]):
            scale = mpfr(factor) / mpfr(S0) ** (3 * j + i)
            jet[i] += val * scale
            djet[i] += dval * scale
    return jet, djet
