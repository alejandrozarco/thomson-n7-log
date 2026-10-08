#!/usr/bin/env python3
"""Exact Möbius-chain generator for the Coulomb kernel (N = 7, s = 1) minorants.

Library used by gen_minor1.py.  Semantics mirror CoulN7/MinorCore.lean exactly:
  gapPoly Gn Gd = padd [Gd*Gd] (pneg (pmul [2,-2] (pmul Gn Gn)))
  nnChainOK q D ps l r : every piece (A,B) has homog [A,B] [D,D] q (len q - 1) all >= 0, A <= l, chained, last B >= r.
  shiftN Hn Hd k m = padd (pscale m Hn) [k*Hd],  denominator m*Hd.
"""
from fractions import Fraction as Fr
from math import lcm


# ---------------------------------------------------------------- Lean list semantics
def padd(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p[0] + q[0]] + padd(p[1:], q[1:])


def padd_it(p, q):  # iterative, same result as padd
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(c, p):
    return [c * x for x in p]


def pneg(p):
    return [-x for x in p]


def pmul(p, q):
    # Lean: pmul [] q = [];  pmul (a::as) q = padd (pscale a q) (0 :: pmul as q)
    if not p:
        return []
    out = []
    for a in reversed(p):
        out = padd_it(pscale(a, q), [0] + out)
    return out


def ppow(p, n):
    r = [1]
    for _ in range(n):
        r = pmul(p, r)
    return r


def homog(T, E, q, m):
    # Lean: homog T E [] _ = [];  homog T E (c::cs) m = padd (pscale c (ppow E m)) (pmul T (homog T E cs (m-1)))
    if not q:
        return []
    rest = homog(T, E, q[1:], m - 1 if m > 0 else 0)
    return padd_it(pscale(q[0], ppow(E, m)), pmul(T, rest))


def gapPoly(Gn, Gd):
    return padd_it([Gd * Gd], pneg(pmul([2, -2], pmul(Gn, Gn))))


def shiftN(Hn, Hd, k, m):
    return padd_it(pscale(m, Hn), [k * Hd])


def nnChainOK(q, D, ps, l, r):
    for (A, B) in ps:
        h = homog([A, B], [D, D], q, len(q) - 1)
        if not (all(c >= 0 for c in h) and A <= l):
            return False
        l = B
    return r <= l


# ---------------------------------------------------------------- fast piece test (same coefficients)
def mob_coeffs(q, A, B, D):
    """coefficients of sum_j q_j (A + B x)^j (D (1+x))^(m-j), m = len(q)-1 (= homog result up to trailing zeros).
    Horner in T = A + B x with E^k = D^k (1+x)^k."""
    from math import comb
    m = len(q) - 1
    r = [q[m]]
    for j in range(m - 1, -1, -1):
        # r <- r*T + q_j * E^(m-j)
        k = m - j
        nr = [0] * (len(r) + 1)
        for i, v in enumerate(r):
            nr[i] += A * v
            nr[i + 1] += B * v
        if q[j]:
            c = q[j] * D ** k
            for i in range(k + 1):
                nr[i] += c * comb(k, i)
        r = nr
    return r


def piece_ok(q, A, B, D):
    return all(c >= 0 for c in mob_coeffs(q, A, B, D))


def build_chain(q, D, lo, hi, w0=None, wmin=1):
    """greedy widest-first chain on the integer grid covering [lo, hi); returns list of (A,B) or None."""
    ps = []
    l = lo
    w = w0 or max(1, (hi - lo) // 4)
    while l < hi:
        w = min(w, hi - l)
        while not piece_ok(q, l, l + w, D):
            if w <= wmin:
                return None, l
            w = max(wmin, w // 2)
        ps.append((l, l + w))
        l += w
        w *= 2
    return ps, None


def int_poly(coeffs):
    """rational coefficient strings -> (integer list, denominator)."""
    fs = [Fr(c) for c in coeffs]
    d = 1
    for f in fs:
        d = lcm(d, f.denominator)
    return [int(f * d) for f in fs], d
