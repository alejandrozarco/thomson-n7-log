"""Rigorous check of the 1-D minorants H <= phi for the non-cap cells, by ball arithmetic (python-flint arb,
256 bits).  phi(t) = -1/2 log(2-2t) (log) or (2-2t)^(-1/2) (Coulomb).

usage: python3 check_minorant_cell.py cert_*.json [...]

Ranges (PAPER.md 5.3, 7.1):  case1 (cut a): H on [a, 1);   slab [lo,hi]: H_A on [lo, hi], H_B, H_C on [lo, 1).
Method: f = phi - H.  On [lo, 1 - 2^-20] adaptive bisection with the mean-value form
f(m) - |f'(I)| rad(I) > 0 (all quantities arb balls with exact rational endpoints; the whole interval is
covered, no sampling).  On [1 - 2^-20, 1): phi is increasing, so f(t) >= phi(1 - 2^-20) - max_{ball} H > 0.
Certifies phi - H > NEED = 1e-7 on each whole range (the reported min is the smallest certified piece bound).
"""
import json, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq

flint.ctx.prec = 256
NEED = 1e-7          # certified: phi - H > NEED on every range


def A(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


def poly(coefs, t, der=0):
    cs = list(coefs)
    for _ in range(der):
        cs = [j * cs[j] for j in range(1, len(cs))]
    acc = arb(0)
    for cj in reversed(cs):
        acc = acc * t + cj
    return acc


def make_phi(kernel):
    if kernel == "log":
        return (lambda t: -(2 - 2 * t).log() / 2), (lambda t: 1 / (2 - 2 * t))
    return (lambda t: 1 / (2 - 2 * t).sqrt()), (lambda t: 1 / ((2 - 2 * t) * (2 - 2 * t).sqrt()))


def ball(a, b):
    a = A(a); b = A(b)
    m = (a + b) / 2
    return arb(m.mid(), ((b - a) / 2).upper() + m.rad())


def cover(H, ph, dph, a, b, n0=256, maxdepth=50, need=NEED):
    """certify phi - H > need on [a, b] (exact rationals a < b); returns the smallest certified piece bound."""
    stack = [(a + (b - a) * k / n0, a + (b - a) * (k + 1) / n0, 0) for k in range(n0)]
    worst = None; pieces = 0
    while stack:
        lo, hi, dep = stack.pop()
        m = A((lo + hi) / 2)
        I = ball(lo, hi)
        lb = (ph(m) - poly(H, m)) - abs(dph(I) - poly(H, I, 1)) * A((hi - lo) / 2)
        if lb > need:
            v = float(lb.lower())
            worst = v if worst is None else min(worst, v); pieces += 1
            continue
        if dep >= maxdepth:
            raise RuntimeError(f"cannot certify H < phi on [{float(lo)}, {float(hi)}] (lb {float(lb.lower())})")
        mid = (lo + hi) / 2
        stack += [(lo, mid, dep + 1), (mid, hi, dep + 1)]
    return worst, pieces


def check(path):
    t0 = time.time()
    J = json.load(open(path))
    ph, dph = make_phi(J["kernel"])
    if J["kind"] == "case1":
        a = Fr(J["cell"]["a"])
        items = [("H", J["H"], a, Fr(1))]
    else:
        lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
        items = [("H_A", J["H"]["A"], lo, hi), ("H_B", J["H"]["B"], lo, Fr(1)), ("H_C", J["H"]["C"], lo, Fr(1))]
    rep = {"cert": path.split("/")[-1], "kernel": J["kernel"], "certified_phi_minus_H_gt": NEED}
    ok = True
    for nm, Hs, a, b in items:
        H = [A(x) for x in Hs]
        if b == 1:
            top = 1 - Fr(1, 2 ** 20)
            lb, pcs = cover(H, ph, dph, a, top)
            near1 = ph(A(top)) - poly(H, ball(top, Fr(1))).upper()
            ok &= bool(near1 > NEED)
            rep[nm] = dict(range=[str(a), "1)"], min_phi_minus_H=lb, pieces=pcs, near1_lower=float(near1.lower()))
        else:
            lb, pcs = cover(H, ph, dph, a, b)
            rep[nm] = dict(range=[str(a), str(b)], min_phi_minus_H=lb, pieces=pcs)
        ok &= lb > NEED
    rep["MINORANT_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    allok = True
    for p in sys.argv[1:]:
        try:
            r = check(p)
        except RuntimeError as ex:
            r = {"cert": p, "MINORANT_OK": False, "error": str(ex)}
        print(json.dumps(r), flush=True)
        allok &= r["MINORANT_OK"]
    print("MINORANT", "ALL_OK" if allok else "FAILED")
    sys.exit(0 if allok else 1)
