"""Exact integer mirror of Calabi/Shot/Core.lean.

Every function here has the same definition as its Lean namesake, so a block
accepted here is accepted by the Lean kernel. Only Python integers are used.
"""

SCALE_P = 2 ** 128      # coefficients of P are integers / SCALE_P
SCALE_U = 2 ** 64       # coefficients of the tangent polynomials
SCALE_E = 2 ** 160      # error bounds are naturals / SCALE_E


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def psmul(c, p):
    return [c * a for a in p]


def pmul(p, q):
    # Lean: mul [] q = [] and mul (a :: p) q = add (smul a q) (0 :: mul p q).
    # With q = [] that is len(p) zeros; otherwise the length is len(p) + len(q) - 1.
    if not p:
        return []
    if not q:
        return [0] * len(p)
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def pderiv(p):
    return [i * p[i] for i in range(1, len(p))]


def l1(p):
    return sum(abs(a) for a in p)


def eval_int(x, p):
    v = 0
    for a in reversed(p):
        v = a + x * v
    return v


def sig(A, p):
    return padd(psmul(A, p), [0] + p)


def sig3(A, p):
    return sig(A, sig(A, sig(A, p)))


def op_a(A, q):
    q1 = pderiv(q)
    q2 = pderiv(q1)
    q3 = pderiv(q2)
    return padd(padd(padd(psmul(4, sig3(A, q3)), psmul(84, sig(A, sig(A, q2)))),
                     psmul(337, sig(A, q1))), psmul(-567, q))


def one(blk):
    return padd([SCALE_P], blk["P"])


def res_p(dnum, blk):
    A, H3 = blk["A"], blk["H"] ** 3
    return padd(psmul(H3, pmul(one(blk), padd([567 * dnum], op_a(A, blk["P"])))),
                psmul(4 * SCALE_P, sig3(A, blk["P"])))


def res_u(blk, u, forcing):
    A, H3 = blk["A"], blk["H"] ** 3
    o = one(blk)
    return padd(psmul(H3, pmul(pmul(o, o), padd([forcing], op_a(A, u)))),
                psmul(4 * SCALE_P * SCALE_P, sig3(A, u)))


def min_p(blk):
    p = blk["P"]
    return SCALE_P if not p else SCALE_P + p[0] - l1(p[1:])


def jet(x, p):
    d1 = pderiv(p)
    return [eval_int(x, p), eval_int(x, d1), eval_int(x, pderiv(d1))]


def ceil_div(a, b):
    return (a + b - 1) // b


def summarize(dnum, blk):
    """Returns the block summary, or None when a side condition fails."""
    A, H = blk["A"], blk["H"]
    m = min_p(blk)
    cols = [blk["U0"], blk["U1"], blk["U2"], blk["Ud"]]
    forcing = [0, 0, 0, 567 * SCALE_U]
    unit = [[SCALE_U, 0, 0], [0, SCALE_U, 0], [0, 0, SCALE_U], [0, 0, 0]]
    den = 4 * (A - 1) ** 3 * H ** 3
    ok = H >= 16 and A >= 129 and 7 * SCALE_P <= 100 * m
    ok = ok and all(l1(u) <= 4 * SCALE_U for u in cols)
    ok = ok and all(jet(-1, u) == unit[c] for c, u in enumerate(cols))
    ok = ok and all(l1(res_u(blk, u, forcing[c])) * 2 ** 40 <= SCALE_U * den * m * m
                    for c, u in enumerate(cols))
    if not ok:
        return None
    eps = ceil_div(l1(res_p(dnum, blk)) * SCALE_E, SCALE_P * den * m)
    return dict(H=H, A=A, start=jet(-1, blk["P"]), stop=jet(1, blk["P"]),
                T=[jet(1, u) for u in cols], epsP=eps)
