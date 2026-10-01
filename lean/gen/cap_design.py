"""Cap (dipole cell) minorant design: plain pieces + contact windows + coercivity (MINORANT_PLAN.md §4).

For each class X and each sub-range, certify   H_X(t) + K(t) <= L_g + 1/2 T_n((t-g)/(1-g))   by Moebius
coefficients (route C), where the slack polynomial K is
    delta' = 2e-16             outside the contact windows          (=> f > delta there)
    sA (t+1)                    on the A window [-1, -1+1/500)      (linear contact at -1)
    kB t^4                      on the B windows [-1/20,0), [0,1/20) (quartic contact at 0, node g = 0)
    kC (t - c~)^2               on the C windows [c~ -+ 1/50]        (quadratic contact, node g = c~)
c~ = rational within 2^-90 of c_{1,2} = (-1 +- sqrt5)/4; every window is split AT the node, so the
tiny contact value eta ~ 3.5e-18 sits at a piece endpoint and the Bernstein coefficients see it exactly.
Node constants: 5-smooth nodes as in minor_design.py (LBITS = 96 here); for c~ the constant comes from
log(2-2c) = 1/2 log5 -+ log Phi (LogPhi.lean) plus |log(1+y)| <= |y|/(1-|y|), |y| ~ 1e-27.
"""
import json
import os
import sys
from fractions import Fraction as Fr

import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import minor_design as md  # noqa: E402

md.LBITS = 96
mp.mp.dps = 80
LPHI_LO = Fr(481211825059603447497758913404, 10 ** 30)     # LogPhi.lean
LPHI_HI = Fr(481211825059603447497758914942, 10 ** 30)
S5_LO = Fr(223606797749978969640917366873127, 10 ** 32)    # sqrt5 bracket (LogPhi.lean)
S5_HI = Fr(223606797749978969640917366873128, 10 ** 32)
DELTA = Fr(1, 10 ** 16)
DELTAP = Fr(2, 10 ** 16)
KB = Fr(1, 1000)
KC = Fr(1, 10000)
SA = Fr(1, 1000)
CBITS = 90


def ctilde(sign):
    c = (-1 + sign * mp.sqrt(5)) / 4
    k = int(mp.floor(c * 2 ** CBITS))
    return Fr(k, 2 ** CBITS)


def L_ctilde(ct, sign):
    """rational L <= phi(ct) provable from log5_enc, logPhi_bounds, sqrt5 bracket (see module doc)."""
    l5, h5 = md.L5
    # upper bound of log(2 - 2c): 1/2 log 5 - log Phi (c1)   or   1/2 log 5 + log Phi (c2)
    up = Fr(h5, 2 * md.DEN) + (-LPHI_LO if sign > 0 else LPHI_HI)
    # y = (2 - 2ct)/(2 - 2c) - 1 = 2 (c - ct)/(2 - 2c); bound |y| with the sqrt5 bracket
    c_lo = (-1 + sign * (S5_LO if sign > 0 else S5_HI)) / 4
    c_hi = (-1 + sign * (S5_HI if sign > 0 else S5_LO)) / 4
    dmax = max(abs(c_lo - ct), abs(c_hi - ct))
    den_min = 2 - 2 * c_hi
    ymax = 2 * dmax / den_min
    logy = ymax / (1 - ymax)                     # |log(1+y)| <= |y|/(1-|y|)
    val = -(up + logy) / 2
    Ld = 2 ** md.LBITS
    return Fr((val.numerator * Ld) // val.denominator, Ld)


def phi_mp(t):
    return -mp.log(2 - 2 * mp.mpf(t.numerator) / t.denominator) / 2


def cover_forced(H, a, b, g, Lg, ns=(5, 7, 9, 11, 13, 15, 17), D=None):
    """one or more pieces on [a,b) with a FORCED node g (constant Lg); widest-first greedy."""
    pcs = []
    x = a
    while x < b:
        w = b - x
        got = None
        while w > Fr(1, 10 ** 9):
            y = min(b, x + w)
            for n in ns:
                P = minor_poly_L(H, g, Lg, n)
                ok, S = md.mob_ok(P, x, y)
                if ok:
                    got = dict(a=x, b=y, g=g, n=n, N=len(P) - 1, Lg=Lg, minS=min(S))
                    break
            if got:
                break
            w /= 2
        if not got:
            raise RuntimeError(f"forced node {float(g)}: cannot certify from {float(x)}")
        pcs.append(got)
        x = got["b"]
    return pcs


def minor_poly_L(H, g, Lg, n):
    r = 1 - g
    N = max(n, len(H) - 1)
    P = [Fr(0)] * (N + 1)
    P[0] += Lg
    lin = [-g / r, 1 / r]
    pw = [Fr(1)]
    for k in range(1, n + 1):
        pw = md.pmul(pw, lin)
        for i, c in enumerate(pw):
            P[i] += c / (2 * k)
    for i, c in enumerate(H):
        P[i] -= c
    return P


def addK(H, K):
    out = list(H) + [Fr(0)] * max(0, len(K) - len(H))
    for i, c in enumerate(K):
        out[i] += c
    return out


def plain(H, a, b, D=100 * 2 ** 12):
    des = md.Designer(H, D, ns=(5, 7, 9, 11, 13))
    return des.cover(Fr(a), Fr(b))


def main(path="numerics/hp/cert_cap_log_D12.json"):
    J = json.load(open(path))
    HA = [Fr(x) for x in J["H"]["A"]]; HB = [Fr(x) for x in J["H"]["B"]]; HC = [Fr(x) for x in J["H"]["C"]]
    rep = {}
    # ---- A: window [-1, -1+1/500) with K = sA (t+1), rest [-1+1/500, -99/100] with K = delta'
    eA = dict(md.node_list())[Fr(-1)]
    LA = md.Lnode(eA)
    print("A: eta' at -1 =", float(LA - sum(c * (-1) ** i for i, c in enumerate(HA))))
    wA = cover_forced(addK(HA, [SA, SA]), Fr(-1), Fr(-1) + Fr(1, 500), Fr(-1), LA)
    rA = plain(addK(HA, [DELTAP]), Fr(-1) + Fr(1, 500), Fr(-99, 100) + Fr(1, 409600))
    rep["A"] = (wA, rA)
    # ---- B
    e0 = dict(md.node_list())[Fr(0)]
    L0 = md.Lnode(e0)
    print("B: eta' at 0 =", float(L0 - HB[0]))
    HBk = addK(HB, [0, 0, 0, 0, KB])
    wB = cover_forced(HBk, Fr(-1, 20), Fr(0), Fr(0), L0) + cover_forced(HBk, Fr(0), Fr(1, 20), Fr(0), L0)
    des = md.Designer(addK(HB, [DELTAP]), 100 * 2 ** 12, ns=(5, 7, 9, 11, 13))
    t0, tinfo = md.tail_start(des)
    rB = des.cover(Fr(-1), Fr(-1, 20)) + des.cover(Fr(1, 20), t0)
    rep["B"] = (wB, rB, t0)
    # ---- C
    out = []
    segs = []
    wins = []
    for sign in (-1, +1):
        ct = ctilde(sign)
        Lc = L_ctilde(ct, sign)
        HCv = sum(c * mp.mpf(ct.numerator) / ct.denominator ** 1 * 0 for c in HC)  # placeholder
        etap = Lc - sum(c * ct ** i for i, c in enumerate(HC))
        print(f"C: c~ = {float(ct):.12f}, L_c~ below phi(c~) by {float(phi_mp(ct) - mp.mpf(Lc.numerator) / Lc.denominator):.3e}, "
              f"eta' = {float(etap):.4e}")
        K = [KC * ct ** 2, -2 * KC * ct, KC]
        HCk = addK(HC, K)
        w = cover_forced(HCk, ct - Fr(1, 50), ct, ct, Lc) + cover_forced(HCk, ct, ct + Fr(1, 50), ct, Lc)
        wins.append(w)
    c2t, c1t = ctilde(-1), ctilde(+1)
    grid = lambda x: Fr(int(x * 409600), 409600)  # noqa: E731
    desC = md.Designer(addK(HC, [DELTAP]), 100 * 2 ** 12, ns=(5, 7, 9, 11, 13))
    t0C, _ = md.tail_start(desC)
    rC = (desC.cover(Fr(-1), c2t - Fr(1, 50)) + desC.cover(c2t + Fr(1, 50), c1t - Fr(1, 50)) +
          desC.cover(c1t + Fr(1, 50), t0C))
    rep["C"] = (wins, rC, t0C)
    nA = len(wA) + len(rA); nB = len(wB) + len(rB) + 1; nC = sum(len(w) for w in wins) + len(rC) + 1
    print(f"A: window {len(wA)} + rest {len(rA)};  B: windows {len(wB)} + rest {len(rB)} + tail;  "
          f"C: windows {sum(len(w) for w in wins)} + rest {len(rC)} + tail")
    for w in wB + [p for w in wins for p in w] + wA:
        print(f"   window piece [{float(w['a']):+.6f},{float(w['b']):+.6f}) n={w['n']} N={w['N']} minS={float(w['minS']):.2e}")
    print("cap total pieces:", nA + nB + nC)
    # coercivity arithmetic (exact)
    tau = Fr(1, 1650)
    print("coercivity: kB tau^4 >= delta:", KB * tau ** 4 >= DELTA, "; kC (tau - 2^-90)^2 >= delta:",
          KC * (tau - Fr(1, 2 ** CBITS)) ** 2 >= DELTA, "; sA tau >= delta:", SA * tau >= DELTA,
          "; delta' > delta:", DELTAP > DELTA)
    return rep


if __name__ == "__main__":
    main(*sys.argv[1:])
