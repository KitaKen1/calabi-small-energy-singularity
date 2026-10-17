"""Propagation of the block enclosures along the 576 blocks (exact integers).

`run` mirrors the kernel computation of Calabi/Shot/Chain.lean: it carries a
bound `rho` for the remainder in a moving integer frame. Frames and the linear
response `L` are untrusted proposals produced by `propose`; the fold accepts or
rejects them. The tangent defects enter through the uniform bound 2^-40 that
every accepted block satisfies.

Scales: jets are integers / 2^128, tangent jets and `L` are integers / 2^64,
`rho` and all error bounds are naturals / 2^160, the box radius is 2^-R_EXP.
"""
from fractions import Fraction
import json
import numpy as np
from shot_checks import SCALE_P, SCALE_U, SCALE_E, ceil_div

R_EXP = 56          # the parameter box is [-2^-56, 2^-56]^2
MU_EXP = 112        # tolerance 2^-112 for the jet handed over by the origin


def adj(B):
    (a, b, c), (d, e, f), (g, h, i) = B
    return [[e * i - f * h, c * h - b * i, b * f - c * e],
            [f * g - d * i, a * i - c * g, c * d - a * f],
            [d * h - e * g, b * g - a * h, a * e - b * d]]


def det(B):
    (a, b, c), (d, e, f), (g, h, i) = B
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def mmul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))]
            for i in range(len(X))]


def transfer(summary):
    """Integer 3 x 3 matrix whose columns are the tangent jets at t = 1."""
    T = summary["T"]
    return [[T[c][a] for c in range(3)] for a in range(3)]


def step(summary, g, B, Bn, L, Ln, dz, rho):
    """One block. Returns the next rho, or None when a side condition fails.
    Same computation as `Calabi.Shot.step`."""
    d, dn = det(B), det(Bn)
    if d <= 0 or dn <= 0:
        return None
    absB = [[abs(x) for x in row] for row in B]
    shift = 2 ** (160 - 64 - R_EXP)
    y = sum(abs(L[i][0]) + abs(L[i][1]) for i in range(3)) * shift
    y += sum(ceil_div(sum(absB[i][k] * rho[k] for k in range(3)), d) for i in range(3))
    y += (abs(dz[0]) + abs(dz[1])) * shift
    if y > SCALE_E // 1024 or summary["epsP"] > SCALE_E // 1024:
        return None
    err = 8 * (summary["epsP"] + ceil_div(y, 2 ** 40) + ceil_div(14 * y * y, SCALE_E))
    D = [1, g, g * g]
    T = transfer(summary)
    DT = [[D[i] * T[i][j] for j in range(3)] for i in range(3)]
    Dtd = [D[i] * summary["T"][3][i] for i in range(3)]
    mis = [[sum(DT[i][k] * L[k][j] for k in range(3)) + Dtd[i] * dz[j] - SCALE_U * Ln[i][j]
            for j in range(2)] for i in range(3)]
    lin = [ceil_div(abs(mis[i][0]) + abs(mis[i][1]), 2 ** (128 + R_EXP - 160)) for i in range(3)]
    Wn = adj(Bn)
    M = mmul(mmul(Wn, DT), B)
    out = []
    for i in range(3):
        prop = ceil_div(sum(abs(M[i][k]) * rho[k] for k in range(3)), d * SCALE_U)
        inj = sum(abs(Wn[i][k]) * (lin[k] + D[k] * err) for k in range(3))
        out.append(prop + inj)
    return out


def initial_rho(B0):
    W = adj(B0)
    return [sum(abs(W[i][k]) for k in range(3)) * 2 ** (160 - MU_EXP) for i in range(3)]


def continues(s, sn, g):
    return (s["H"] == g * sn["H"] and s["A"] + 1 + g == g * sn["A"]
            and sn["start"][0] == s["stop"][0]
            and sn["start"][1] == g * s["stop"][1] and sn["start"][2] == g * g * s["stop"][2])


def in_range(lo, hi, s):
    """Same as `Calabi.Shot.inRange`: the block lies in lo <= s <= hi."""
    return lo * s["H"] + 1 <= s["A"] and s["A"] + 1 <= hi * s["H"]


def run(summaries, frames, Ls, dz):
    """Same computation as `Calabi.Shot.chainRun`, keeping the history."""
    rho = initial_rho(frames[0])
    history = [rho]
    for j, s in enumerate(summaries):
        if j + 1 < len(summaries):
            g = s["H"] // summaries[j + 1]["H"]
            if not continues(s, summaries[j + 1], g):
                return None, j
        else:
            g = 1
        rho = step(s, g, frames[j], frames[j + 1], Ls[j], Ls[j + 1], dz, rho)
        if rho is None:
            return None, j
        history.append(rho)
    return history, len(summaries)


def final_radius(B, rho):
    """Componentwise bound (naturals / 2^160) for the remainder itself."""
    d = det(B)
    return [ceil_div(sum(abs(B[i][k]) * rho[k] for k in range(3)), d) for i in range(3)]


def propose(summaries, L0, dz, frame_bits=10):
    """Float QR frames and exactly propagated, rounded linear responses.

    The frames are orthogonal in the physical jet (p, p_s, p_ss), where one block
    is close to the identity. In the block's own scaled jet (p, p_t, p_tt) they
    are diag(H^2, H, 1) times an integer approximation of the orthogonal matrix.
    """
    def frame(Q, H):
        scale = [H * H, H, 1]
        return [[scale[i] * int(round(Q[i][k] * 2 ** frame_bits)) for k in range(3)]
                for i in range(3)]

    Q = np.eye(3)
    frames = [frame(Q, summaries[0]["H"])]
    Ls = [L0]
    for j, s in enumerate(summaries):
        H = s["H"]
        g = H // summaries[j + 1]["H"] if j + 1 < len(summaries) else 1
        D = [1, g, g * g]
        T = transfer(s)
        DT = [[D[i] * T[i][k] for k in range(3)] for i in range(3)]
        # physical transfer of the block: diag(1, H, H^2) T diag(1, 1/H, 1/H^2)
        A = np.array([[float(Fraction(T[i][k] * H ** i, SCALE_U * H ** k)) for k in range(3)]
                      for i in range(3)])
        Q, Rm = np.linalg.qr(A @ Q)
        sign = np.sign(np.diag(Rm))
        sign[sign == 0] = 1
        Q = Q * sign
        if np.linalg.det(Q) < 0:
            Q[:, 2] = -Q[:, 2]
        frames.append(frame(Q, H // g))
        L = Ls[-1]
        Dtd = [D[i] * s["T"][3][i] for i in range(3)]
        exact = [[sum(DT[i][k] * L[k][c] for k in range(3)) + Dtd[i] * dz[c] for c in range(2)]
                 for i in range(3)]
        Ls.append([[(2 * x + SCALE_U) // (2 * SCALE_U) for x in row] for row in exact])
    return frames, Ls
