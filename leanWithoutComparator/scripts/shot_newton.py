"""Untrusted Newton refinement of the shooting centre (k, d).

Zeroes the two unstable coordinates of (shot jet - formal tail jet) at s = 56.
Writes certificate/shot_centre.json; the values are proposals, not proofs.
"""
from pathlib import Path
import json
import sys
import time
import gmpy2
from gmpy2 import mpfr
from shot_numerics import shoot, PREC
from shot_tail_numerics import projection, tail_jet

ROOT = Path(__file__).resolve().parents[1]
K_START = "-0.188363675849724267614910321375326069594922491027024409460911"
D_START = "0.134296165791329499759950221780910232699022752255858568352643"


def fmt(x, digits=130):
    mantissa, exponent, _ = gmpy2.mpfr(x).digits(10, digits)
    sign = "-" if mantissa.startswith("-") else ""
    return f"{sign}0.{mantissa.lstrip('-')}e{exponent}"


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    k, d = mpfr(K_START), mpfr(D_START)
    G = projection()
    history = []
    for it in range(steps + 1):
        start = time.time()
        jet, J = shoot(k, d)
        tj, dtj = tail_jet(d)
        diff = [jet[a] - tj[a] for a in range(3)]
        proj = [sum(G[r][a] * diff[a] for a in range(3)) for r in range(3)]
        # derivative of the two unstable coordinates with respect to (k, d)
        Jd = [[J[a][0], J[a][1] - dtj[a]] for a in range(3)]
        DF = [[sum(G[r][a] * Jd[a][c] for a in range(3)) for c in range(2)] for r in (1, 2)]
        det = DF[0][0] * DF[1][1] - DF[0][1] * DF[1][0]
        inv = [[DF[1][1] / det, -DF[0][1] / det], [-DF[1][0] / det, DF[0][0] / det]]
        history.append(dict(iteration=it, k=fmt(k), d=fmt(d),
                            q=fmt(proj[0], 12), re_xi=fmt(proj[1], 12), im_xi=fmt(proj[2], 12),
                            seconds=round(time.time() - start, 1)))
        print(json.dumps(history[-1]), flush=True)
        if it == steps:
            break
        k -= inv[0][0] * proj[1] + inv[0][1] * proj[2]
        d -= inv[1][0] * proj[1] + inv[1][1] * proj[2]
    out = dict(precision_bits=PREC, k=fmt(k), d=fmt(d),
               jacobian_unstable=[[fmt(x, 40) for x in row] for row in DF],
               inverse_jacobian=[[fmt(x, 40) for x in row] for row in inv],
               q_row=[fmt(sum(G[0][a] * Jd[a][c] for a in range(3)), 40) for c in range(2)],
               projection=[[fmt(x, 40) for x in row] for row in G],
               end_jet=[fmt(x, 60) for x in jet], history=history)
    dest = ROOT / "certificate"
    dest.mkdir(exist_ok=True)
    (dest / "shot_centre.json").write_text(json.dumps(out, indent=2) + "\n")
    print("written", dest / "shot_centre.json")


if __name__ == "__main__":
    main()
