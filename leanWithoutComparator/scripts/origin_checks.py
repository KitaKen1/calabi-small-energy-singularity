"""Exact integer mirror of Calabi/Origin/Cert.lean.

The regular solution at the origin is a power series in r = s^(3/2). The
certificate is a polynomial Q0 (integers / 2^192) with two tangent polynomials
Q1, Q2 (integers / 2^128) for the two parameters. With D = r d/dr the profile
equation is

    (27/8) (D - 1)(D + 6)(D + 7)(p - d) + r^2 p / (1 + p) = 0,

and `op_l` is (D - 1)(D + 6)(D + 7) q / r^2 on coefficient lists.
"""
from shot_checks import SCALE_P, padd, psmul, pmul, l1, eval_int

SCALE_O = 2 ** 192      # coefficients of Q0 are integers / SCALE_O
SCALE_T = SCALE_P       # coefficients of Q1, Q2 are integers / SCALE_T


def deriv_from(k, p):
    return [(k + i) * a for i, a in enumerate(p)]


def op_l_from(j, p):
    return [(j + i + 1) * (j + i + 8) * (j + i + 9) * a for i, a in enumerate(p)]


def op_l(q):
    return op_l_from(0, q[2:])


def one_plus_o(q):
    return padd([SCALE_O], q)


def res0(q0):
    return padd(psmul(8 * SCALE_O, q0), psmul(27, pmul(one_plus_o(q0), op_l(q0))))


def res_t(q0, qm):
    return padd(psmul(8 * SCALE_O, qm),
                psmul(27, padd(pmul(qm, op_l(q0)), pmul(one_plus_o(q0), op_l(qm)))))


def jet1(q):
    """(Q, DQ, D^2 Q) at r = 1."""
    dq = deriv_from(0, q)
    return [eval_int(1, q), eval_int(1, dq), eval_int(1, deriv_from(0, dq))]


def head2(q):
    return [q[0] if len(q) > 0 else 0, q[1] if len(q) > 1 else 0]


def origin_summarize(dnum, knum, dz, kz, q0, q1, q2):
    """Same computation as `Calabi.Origin.originSummarize`."""
    shift = SCALE_O // SCALE_P
    if head2(q0) != [dnum * shift, knum * shift]:
        return None
    lift = SCALE_T // 2 ** 64
    if head2(q1) != [dz[0] * lift, kz[0] * lift] or head2(q2) != [dz[1] * lift, kz[1] * lift]:
        return None
    return dict(e0=l1(res0(q0)), e1=l1(res_t(q0, q1)) + l1(res_t(q0, q2)), n0=l1(q0),
                nQ=l1(q1) + l1(q2), nL=l1(op_l(q1)) + l1(op_l(q2)),
                j0=jet1(q0), j1=jet1(q1), j2=jet1(q2))
