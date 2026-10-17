"""Exact integer mirror of Calabi/Tail/Cert.lean.

Every function here has the same definition as its Lean namesake, so a tail
polynomial accepted here is accepted by the Lean kernel.
"""
from shot_checks import SCALE_P, SCALE_E, padd, psmul, pmul, pderiv, l1, eval_int, ceil_div


def theta(q):
    return psmul(-3, [0] + pderiv(q))


def tail_p1(P):
    return theta(P)


def tail_p2(P):
    return padd(theta(tail_p1(P)), psmul(-1, tail_p1(P)))


def tail_p3(P):
    return padd(theta(tail_p2(P)), psmul(-2, tail_p2(P)))


def one_plus(P):
    return padd([SCALE_P], P)


def tail_lin(dnum, P):
    return padd([567 * dnum],
                padd(padd(padd(psmul(4, tail_p3(P)), psmul(84, tail_p2(P))),
                          psmul(337, tail_p1(P))),
                     psmul(-567, P)))


def tail_res(dnum, P):
    return padd([0] + pmul(one_plus(P), tail_lin(dnum, P)), psmul(4 * 56 ** 3 * SCALE_P, P))


def tail_summarize(dnum, P):
    n = l1(P)
    if not (n * 200 <= SCALE_P and 567 * (SCALE_P + n) * 1000 <= 4 * 56 ** 3 * (SCALE_P - n)):
        return None
    return dict(v=eval_int(1, P), d1=eval_int(1, tail_p1(P)), d2=eval_int(1, tail_p2(P)), l1=n,
                eps=ceil_div(l1(tail_res(dnum, P)) * SCALE_E, 4 * 56 ** 3 * SCALE_P * (SCALE_P - n)))
