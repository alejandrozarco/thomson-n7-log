"""Piece design for the 1-D minorant layer (MINORANT_PLAN.md).

For a minorant H (exact rational coefficients) and a range [lo, 1) or [lo, hi], find a partition
into pieces [a, b) with, for each piece, a node g (1-g = 2^i 3^j 5^k / 2, i.e. 2(1-g) 5-smooth) and an
odd truncation order n such that

    P(t) := L_g + 1/2 * T_n((t-g)/(1-g)) - H(t)  >= 0  on [a, b)

is certified by the *Moebius (Bernstein) coefficients*: all coefficients of
    S(x) = sum_j p_j (a + b x)^j (1 + x)^(N-j),   N = max(n, deg H)
are >= 0 (t = (a + b x)/(1 + x) maps x in [0, inf) onto [a, b)).  Here T_n(u) = sum_{k<=n} u^k/k and
L_g <= -1/2 log(2(1-g)) is a rational lower bound built from the log2/log3/log5 enclosures.
Since -log(1-u) >= T_n(u) for odd n and u < 1, P >= 0 gives H <= phi on the piece.

Tail [t0, 1): phi is increasing, so phi(t) >= L_{t0}; certified by Moebius coefficients of
L_{t0} - H(t) on [t0, 1).

All arithmetic exact (Fractions).  python3, single-threaded; run with nice -n 19.
"""
import json
import sys
from fractions import Fraction as Fr
from math import comb

import mpmath as mp

mp.mp.dps = 60
DEN = 10 ** 32


def _enc(x, pad):
    f = int(mp.floor(x * DEN))
    return f - pad, f + pad   # must match MinorCore.lean l2/h2, l3/h3, l5/h5


L2 = _enc(mp.log(2), 100); L3 = _enc(mp.log(3), 300); L5 = _enc(mp.log(5), 400)
LBITS = 64                     # node constants rounded down to 2^-LBITS


def node_list(maxpow2=14):
    """nodes g with 2(1-g) = 2^i 3^j 5^k, -1 <= g < 1; returns list of (g, (a2,a3,a5,b2,b3,b5))."""
    out = {}
    for i in range(-maxpow2, 3):
        for j in range(-2, 3):
            for k in range(-2, 3):
                v = Fr(2) ** i * Fr(3) ** j * Fr(5) ** k       # = 2(1-g)
                g = 1 - v / 2
                if -1 <= g < 1:
                    e = (max(i, 0), max(j, 0), max(k, 0), max(-i, 0), max(-j, 0), max(-k, 0))
                    if g not in out or sum(e) < sum(out[g]):
                        out[g] = e
    return sorted(out.items())


def Lnode(e):
    """rational L <= -1/2 log(2(1-g)); log(2(1-g)) = sum a_p log p - sum b_p log p <= sum a_p hi_p - sum b_p lo_p."""
    a2, a3, a5, b2, b3, b5 = e
    ub = a2 * L2[1] + a3 * L3[1] + a5 * L5[1] - b2 * L2[0] - b3 * L3[0] - b5 * L5[0]
    return Fr((-ub * 2 ** LBITS) // (2 * DEN), 2 ** LBITS)


def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def ppow(p, k):
    r = [Fr(1)]
    for _ in range(k):
        r = pmul(r, p)
    return r


def minor_poly(H, g, e, n):
    """P(t) = L_g + 1/2 T_n((t-g)/(1-g)) - H(t), coefficient list."""
    r = 1 - g
    N = max(n, len(H) - 1)
    P = [Fr(0)] * (N + 1)
    P[0] += Lnode(e)
    lin = [-g / r, 1 / r]
    pw = [Fr(1)]
    for k in range(1, n + 1):
        pw = pmul(pw, lin)
        for i, c in enumerate(pw):
            P[i] += c / (2 * k)
    for i, c in enumerate(H):
        P[i] -= c
    return P


def mobius(P, a, b, N=None):
    """coefficients of sum_j p_j (a + b x)^j (1+x)^(N-j)."""
    N = len(P) - 1 if N is None else N
    S = [Fr(0)] * (N + 1)
    T = [Fr(a), Fr(b)]
    for j, pj in enumerate(P):
        if pj:
            term = pmul(ppow(T, j), ppow([Fr(1), Fr(1)], N - j))
            for i, c in enumerate(term):
                S[i] += pj * c
    return S


def mob_ok(P, a, b, N=None):
    S = mobius(P, a, b, N)
    return min(S) >= 0, S


def fastval(P, t):
    return sum(float(c) * t ** i for i, c in enumerate(P))


class Designer:
    def __init__(self, H, grid_den, ns=(5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25), elev=0):
        self.H = [Fr(x) for x in H]
        self.D = grid_den
        self.nodes = node_list()
        self.ns = ns
        self.elev = elev

    def try_piece(self, a, b):
        """find (g, e, n) certifying [a, b); nodes near the middle first, smallest n first."""
        mid = (a + b) / 2
        cand = sorted(self.nodes, key=lambda ge: abs(float(ge[0] - mid)) / float(1 - ge[0]))[:4]
        for n in self.ns:
            for g, e in cand:
                if not (g < 1):
                    continue
                P = minor_poly(self.H, g, e, n)
                # quick float pre-screen at a few points
                if min(fastval(P, float(a + (b - a) * s / 8)) for s in range(9)) < 0:
                    continue
                N = len(P) - 1 + self.elev
                ok, S = mob_ok(P, a, b, N)
                if ok:
                    return dict(a=a, b=b, g=g, e=e, n=n, N=N, minS=min(S))
        return None

    def cover(self, lo, hi, maxw=Fr(1, 2)):
        """greedy widest pieces on [lo, hi); endpoints on the grid 1/D (except lo)."""
        pieces = []
        a = Fr(lo)
        w = maxw
        while a < hi:
            got = None
            ww = w * 2 if w < maxw else w
            while ww >= Fr(1, self.D):
                b = min(Fr(hi), Fr(int((a + ww) * self.D), self.D))
                if b <= a:
                    ww /= 2
                    continue
                got = self.try_piece(a, b)
                if got:
                    break
                ww /= 2
            if not got:
                raise RuntimeError(f"cannot certify a piece starting at {a} ({float(a)})")
            pieces.append(got)
            w = got["b"] - got["a"]
            a = got["b"]
        return pieces

    def tail(self, t0):
        """phi(t) >= L_{t0} on [t0, 1): need L_{t0} - H >= 0 on [t0, 1) (Moebius)."""
        e = dict(self.nodes)[Fr(t0)]
        P = [-c for c in self.H]
        P[0] += Lnode(e)
        ok, S = mob_ok(P, Fr(t0), Fr(1))
        return ok, dict(t0=Fr(t0), e=e, minS=min(S))


def tail_start(des):
    for m in range(1, 15):
        t0 = 1 - Fr(1, 2 ** m)
        ok, info = des.tail(t0)
        if ok:
            return t0, info
    raise RuntimeError("no tail")


def design_class(H, lo, hi, closed, D=100 * 2 ** 12, verbose=True, elev=0):
    des = Designer(H, D, elev=elev)
    if hi is None:                        # [lo, 1): cover [lo, t0) then the tail
        t0, tinfo = tail_start(des)
        pcs = des.cover(Fr(lo), t0)
    else:                                 # [lo, hi] closed: extend the last piece past hi
        t0, tinfo = None, None
        pcs = des.cover(Fr(lo), Fr(hi) + Fr(1, D))
    if verbose:
        for p in pcs:
            print(f"  [{float(p['a']):+.5f},{float(p['b']):+.5f}) w={float(p['b']-p['a']):.4f} "
                  f"g={float(p['g']):+.4f} n={p['n']} N={p['N']} minS={float(p['minS']):.2e}")
        if t0 is not None:
            print(f"  tail [{float(t0)}, 1) minS={float(tinfo['minS']):.2e}")
    return pcs, (t0, tinfo)


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "numerics/cells/certs/cert_slab_93_90_log_D12.json"
    J = json.load(open(path))
    lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
    tot = 0
    for cls in "ABC":
        print(cls)
        pcs, _ = design_class(J["H"][cls], lo, hi if cls == "A" else None, cls == "A")
        print(f"  -> {len(pcs)} pieces")
        tot += len(pcs)
    print("total", tot)
