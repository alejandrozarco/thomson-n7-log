#!/usr/bin/env python3
"""JSON slab certificate (Coulomb kernel)  ->  upstream `TCert` Lean data module + kernel-check modules.

usage (from anywhere; run with `nice -n 19`, OMP_NUM_THREADS=1):
  python3 numerics/n7_interval/lean/gen/emit_tcert.py <cert_slab_*.json> <Name>            emit, then --check
  python3 numerics/n7_interval/lean/gen/emit_tcert.py <cert_slab_*.json> <Name> --check-only   re-parse + check the emitted files
  options: --no-check (emit only), --split (put SA/SB/SG in DataA/DataB/DataG modules; automatic when a
           single Data.lean would exceed --max-module bytes, default 1_000_000)

Writes lean/CoulN7/<Name>/Data.lean (+ DataA/DataB/DataG.lean when split), ChkMeta.lean, ChkA.lean, ChkB.lean,
ChkG.lean, mirroring ThomsonGen/S9998/* of the M0 split of upstream (huwngtran/thomson-n7-lean).

Semantics (ThomsonGen/CertT.lean, `TCert`):
  * real data = integer data / Lam:  H_X = polyR Lam HX,  psi = polyR Lam psi,  e = e/Lam, c_alpha = cal/Lam,
    c_beta = cbe/Lam, F-block k = (sum_q d_q l_q l_q^T + Delta)/Lam  (Blk, Blk.ok);
  * identities  mA * (5 Lam lamA) = sum_r gT(codes_r) * z_r^T M_r z_r   (resp. mB * 4 Lam lamB, mG * 30 Lam lamG),
    M_r = sum_q d_q l_q l_q^T + Delta (packed TBlk, okF);  hence  M_r = (5 Lam mA / scale_r) * B_r  where
    gT(codes_r) = scale_r * g_r  (g_r = our JSON multiplier, scale_r > 0 rational).
All integers are EXACT images of the JSON rationals (no rounding of any certificate datum): Lam and mA/mB/mG are
chosen as (lcm of denominators) * 2^k, k minimal such that every block has an integer LDL^T + diagonally dominant
remainder (the remainder Delta absorbs the rounding of the integer pivots/columns exactly).

--check re-implements, on the integers parsed back from the emitted .lean files, the Lean Bool functions
`TCert.checkMeta` (Blk.ok, okF: transposeSq/domAll/offAbs), `TCert.chkA/chkB/chkG` (hybChk with fqCur = fqFlat:
dotN/rowsN/comb1/comb2; Ex trees of lamAE/lamBE/lamGE built exactly as in CertT.lean/Cert3.lean/Cert1.lean,
kev/l1/degK by structural recursion; hybW = Nat.log2 idL + 1, hybD = max idDeg + 1), and in addition compares the
parsed data with the JSON certificate (exact rationals).
"""
import argparse
import hashlib
import itertools
import json
import os
import re
import sys
import time
from fractions import Fraction as Fr
from math import lcm

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
LEANROOT = os.environ.get("COULN7_LEAN", os.path.join(os.path.expanduser("~"), "claude_projects", "thomson-n7-log-macbuild", "lean"))   # Lake workspace that receives CoulN7/
T0 = time.time()


def log(*a):
    print(f"[{time.strftime('%H:%M:%S')} +{time.time() - T0:6.1f}s]", *a, flush=True)


# ====================================================================== Ex trees (Kron.lean, Cert1/3, CertT)
# ('c', n) | ('m', a, b, d) | ('+', p, q) | ('*', p, q)
def c(n):
    return ('c', int(n))


def mon(a, b, d):
    return ('m', a, b, d)


def add(p, q):
    return ('+', p, q)


def mul(p, q):
    return ('*', p, q)


U = mon(1, 0, 0)
V = mon(0, 1, 0)
T = mon(0, 0, 1)


def neg(e):
    return mul(c(-1), e)


def sub(e, f):
    return add(e, neg(f))


def smul(a, e):
    return mul(c(a), e)


def sq(e):
    return mul(e, e)


def sumE(lst):                     # l.foldr add (c 0)
    acc = c(0)
    for e in reversed(lst):
        acc = add(e, acc)
    return acc


def sumRange(r, f):
    return sumE([f(i) for i in range(r)])


def smulNZ(a, e):
    return c(0) if a == 0 else smul(a, e)


_q3 = {}


def q3E(k):
    if k in _q3:
        return _q3[k]
    if k == 0:
        e = c(1)
    elif k == 1:
        e = sub(T, mul(U, V))
    else:
        e = sub(mul(smul(2, sub(T, mul(U, V))), q3E(k - 1)),
                mul(mul(sub(c(1), sq(U)), sub(c(1), sq(V))), q3E(k - 2)))
    _q3[k] = e
    return e


_sb = {}


def sbst(i, j, k, e):
    key = (i, j, k, id(e))
    hit = _sb.get(key)
    if hit is not None and hit[0] is e:
        return hit[1]
    t = e[0]
    if t == 'c':
        r = e
    elif t == 'm':
        a, b, d = e[1], e[2], e[3]
        r = ('m', (a if i == 0 else 0) + (b if j == 0 else 0) + (d if k == 0 else 0),
             (a if i == 1 else 0) + (b if j == 1 else 0) + (d if k == 1 else 0),
             (a if i == 2 else 0) + (b if j == 2 else 0) + (d if k == 2 else 0))
    else:
        r = (t, sbst(i, j, k, e[1]), sbst(i, j, k, e[2]))
    _sb[key] = (e, r)
    return r


def getD(lst, i, dflt):
    return lst[i] if 0 <= i < len(lst) else dflt


class Blk:
    def __init__(self, d, l, D):
        self.d, self.l, self.D = d, l, D

    def dq(self, q):
        return getD(self.d, q, 0)

    def lq(self, q, a):
        return getD(getD(self.l, q, []), a, 0)

    def dl(self, a, cc):
        return getD(getD(self.D, a, []), cc, 0)


EMPTY = Blk([], [], [])


def fpE(r, b):
    return add(sumRange(r, lambda q: smulNZ(b.dq(q), mul(sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(a, 0, 0))),
                                                         sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(0, a, 0)))))),
               sumRange(r, lambda a: sumRange(r, lambda cc: smulNZ(b.dl(a, cc), mon(a, cc, 0)))))


def fkE(r, b, k):
    return mul(fpE(r, b), q3E(k))


def SE(K, m, bl):
    return sumRange(K, lambda k: fkE(m(k), bl(k), k))


def h1E(h):
    return sumRange(len(h), lambda j: smulNZ(getD(h, j, 0), mon(j, 0, 0)))


def hvE(h, i):
    return sbst(i, 3, 3, h1E(h))


def gmE(S, i):
    return add(add(sbst(3, i, i, S), sbst(i, 3, i, S)), sbst(i, i, 3, S))


def lamAE(HA, pBa, cal, SP, SR):
    return sub(add(add(sub(hvE(HA, 0), smul(2, gmE(SP, 0))), smul(5, hvE(pBa, 1))), smul(5, hvE(pBa, 2))),
               add(c(5 * cal), smul(10, add(add(sbst(0, 1, 2, SP), sbst(0, 2, 1, SP)), sbst(1, 2, 0, SR)))))


def lamBE(HB, pBa, pCb, cbe, SP, SR):
    return sub(add(add(sub(sub(sub(hvE(HB, 0), gmE(SP, 0)), gmE(SR, 0)), hvE(pBa, 0)),
                       sub(sub(sub(hvE(HB, 1), gmE(SP, 1)), gmE(SR, 1)), hvE(pBa, 1))),
                   smul(4, hvE(pCb, 2))),
               add(c(4 * cbe), smul(8, add(add(sbst(0, 1, 2, SP), sbst(0, 2, 1, SR)), sbst(1, 2, 0, SR)))))


def tgE(HC, pCb, SR, i):
    return sub(sub(hvE(HC, i), smul(2, gmE(SR, i))), smul(2, hvE(pCb, i)))


def lamGE(HC, pCb, e, cal, cbe, SP, SR):
    return sub(smul(10, add(add(tgE(HC, pCb, SR, 0), tgE(HC, pCb, SR, 1)), tgE(HC, pCb, SR, 2))),
               add(smul(3, add(add(add(c(e), smul(2, sbst(3, 3, 3, SP))), smul(5, sbst(3, 3, 3, SR))),
                               c(-5 * cal - 20 * cbe))),
                   smul(60, add(add(sbst(0, 1, 2, SR), sbst(0, 2, 1, SR)), sbst(1, 2, 0, SR)))))


def codeE(an, ad, j):
    if j == 0:
        return sub(c(1), sq(U))
    if j == 1:
        return sub(c(1), sq(V))
    if j == 2:
        return sub(c(1), sq(T))
    if j == 3:
        return sub(add(c(1), smul(2, mul(U, mul(V, T)))), add(sq(U), add(sq(V), sq(T))))
    if j == 4:
        return sub(c(1), U)
    if j == 5:
        return add(c(1), U)
    if j == 6:
        return sub(c(1), V)
    if j == 7:
        return add(c(1), V)
    if j == 8:
        return sub(c(1), T)
    if j == 9:
        return add(c(1), T)
    if j == 10:
        return sub(smul(ad, U), c(an))
    if j == 11:
        return sub(smul(ad, V), c(an))
    if j == 12:
        return sub(smul(ad, T), c(an))
    return c(1)


def codeT(an, ad, bn, bd, j):
    return sub(c(bn), smul(bd, U)) if j == 13 else codeE(an, ad, j)


def gT(an, ad, bn, bd, g):
    acc = c(1)
    for code in reversed(g):
        acc = mul(codeT(an, ad, bn, bd, code), acc)
    return acc


class Memo:
    """structural recursions of Kron.lean / CertT.lean, memoised on node identity (values are those of the tree)."""

    def __init__(self):
        self.m = {}

    def get(self, key, e):
        h = self.m.get((key, id(e)))
        return h[1] if h is not None and h[0] is e else None

    def put(self, key, e, v):
        self.m[(key, id(e))] = (e, v)
        return v


_MEMO = Memo()


def l1(e):
    v = _MEMO.get('l1', e)
    if v is not None:
        return v
    t = e[0]
    if t == 'c':
        v = abs(e[1])
    elif t == 'm':
        v = 1
    elif t == '+':
        v = l1(e[1]) + l1(e[2])
    else:
        v = l1(e[1]) * l1(e[2])
    return _MEMO.put('l1', e, v)


def degK(k, e):
    key = ('deg', k)
    v = _MEMO.get(key, e)
    if v is not None:
        return v
    t = e[0]
    if t == 'c':
        v = 0
    elif t == 'm':
        v = e[1 + k] if k in (0, 1) else e[3]      # proj: k = 0 -> a, 1 -> b, else d
    elif t == '+':
        v = max(degK(k, e[1]), degK(k, e[2]))
    else:
        v = degK(k, e[1]) + degK(k, e[2])
    return _MEMO.put(key, e, v)


def kev(w, D, e):
    """Ex.kev, plain structural recursion (no memo: values are up to w*D^3 bits, a memo would cost GBs)."""
    t = e[0]
    if t == 'c':
        return e[1]
    if t == 'm':
        return 1 << (w * (e[1] + D * e[2] + D * D * e[3]))
    if t == '+':
        v = kev(w, D, e[1]) + kev(w, D, e[2])
    else:
        v = kev(w, D, e[1]) * kev(w, D, e[2])
    b = v.bit_length() if v >= 0 else (-v).bit_length()
    if b > KEVSTAT[0]:
        KEVSTAT[0] = b
    return v


KEVSTAT = [0]


def expand(e):
    """collected polynomial {(a,b,d): int} of a tree (independent cross-check only)."""
    v = _MEMO.get('exp', e)
    if v is not None:
        return v
    t = e[0]
    if t == 'c':
        v = {(0, 0, 0): e[1]} if e[1] else {}
    elif t == 'm':
        v = {(e[1], e[2], e[3]): 1}
    elif t == '+':
        v = dict(expand(e[1]))
        for k2, x in expand(e[2]).items():
            y = v.get(k2, 0) + x
            if y:
                v[k2] = y
            else:
                v.pop(k2, None)
    else:
        v = {}
        for k1, x1 in expand(e[1]).items():
            for k2, x2 in expand(e[2]).items():
                k3 = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                v[k3] = v.get(k3, 0) + x1 * x2
        v = {k3: x for k3, x in v.items() if x}
    return _MEMO.put('exp', e, v)


# ====================================================================== packed blocks (CertF.lean, CertT.lean)
def unpackI(B, n, x):
    out = []
    for _ in range(n):
        out.append((x % (1 << B)) - (1 << (B - 1)))
        x >>= B
    return out


def unpackM(B, cols, rows, x):
    out = []
    for _ in range(rows):
        out.append(unpackI(B, cols, x % (1 << (B * cols))))
        x >>= B * cols
    return out


def mkBlk(r, Bd, Bl, BD, xd, xl, xD):
    return Blk(unpackI(Bd, r, xd), unpackM(Bl, r, r, xl), unpackM(BD, r, r, xD))


def packI(B, vals):
    x = 0
    off = 1 << (B - 1)
    for i, v in enumerate(vals):
        f = v + off
        assert 0 <= f < (1 << B), (B, v)
        x |= f << (B * i)
    return x


def packM(B, rows):
    x = 0
    for i, row in enumerate(rows):
        x |= packI(B, row) << (B * len(row) * i)
    return x


def width(vals):
    """least B >= 1 with -2^(B-1) <= v < 2^(B-1) for all v."""
    B = 1
    for v in vals:
        while not (-(1 << (B - 1)) <= v < (1 << (B - 1))):
            B += 1
    return B


class TBlk:
    def __init__(self, g, z, r, Bd, Bl, BD, xd, xl, xD):
        self.g, self.z, self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD = g, z, r, Bd, Bl, BD, xd, xl, xD

    def B(self):
        return mkBlk(self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD)

    def wf(self):
        return 0 < self.Bd and 0 < self.Bl and 0 < self.BD and len(self.z) == self.r

    def l1B(self):
        n = len(self.z)
        return n * ((1 << (self.Bd - 1)) * (n * (1 << (self.Bl - 1))) ** 2) + n * (n * (1 << (self.BD - 1)))


# ---- Blk.ok (Cert1.lean, random access) and okF (CertF.lean, list traversal)
def blk_ok(r, b):
    for i in range(r):
        if not (0 <= b.dq(i)):
            return False
        for j in range(r):
            if b.dl(i, j) != b.dl(j, i):
                return False
        if not (sum((0 if i == j else abs(b.dl(i, j))) for j in range(r)) <= b.dl(i, i)):
            return False
    return True


def transposeSq(n, M):
    out = []
    for _ in range(n):
        out.append([row[0] if row else 0 for row in M])
        M = [row[1:] for row in M]
    return out


def offAbs(i, k, row):
    s = 0
    for x in row:
        s += 0 if i == k else abs(x)
        k += 1
    return s


def domAll(k, rows):
    for row in rows:
        if not (offAbs(k, 0, row) <= getD(row, k, 0)):
            return False
        k += 1
    return True


def okF(r, b):
    return (all(0 <= x for x in b.d) and [row[:r] for row in b.D] == transposeSq(r, b.D) and domAll(0, b.D))


# ---- fqFlat (CertT.lean)
def offB(B):
    return 1 << (B - 1) if B >= 1 else 1


def dotN(B, ps, x):
    s = 0
    for p in ps:
        s += (x % (1 << B)) * p
        x >>= B
    return s


def rowsN(B, cols, ps, rows, x):
    out = []
    for _ in range(rows):
        out.append(dotN(B, ps, x % (1 << (B * cols))))
        x >>= B * cols
    return out


def comb1(Bd, Bl, Pt, Ls, xd):
    s = 0
    for L in Ls:
        f = (xd % (1 << Bd)) - offB(Bd)
        y = L - offB(Bl) * Pt
        s += f * (y * y)
        xd >>= Bd
    return s


def comb2(BD, Pt, ps, Ds):
    s = 0
    for p, Dv in zip(ps, Ds):
        s += p * (Dv - offB(BD) * Pt)
    return s


def weights(w, D, z):
    return [1 << (w * (t[0] + D * t[1] + D * D * t[2])) for t in z]


def fqFlat(w, D, s):
    ps = weights(w, D, s.z)
    Pt = sum(ps)
    v = (comb1(s.Bd, s.Bl, Pt, rowsN(s.Bl, s.r, ps, s.r, s.xl), s.xd)
         + comb2(s.BD, Pt, ps, rowsN(s.BD, s.r, ps, s.r, s.xD)))
    KEVSTAT[0] = max(KEVSTAT[0], abs(v).bit_length())
    return v


def mxs(k, z):
    m = 0
    for t in z:
        m = max(m, t[k])
    return m


def hybChk(Fx, an, ad, bn, bd, S, info):
    """CertT.hybChk fqCur Fx an ad bn bd S  (returns Bool, fills info)."""
    if not all(s.wf() for s in S):
        info["wf"] = False
        return False
    gs = [gT(an, ad, bn, bd, s.g) for s in S]
    idL = l1(Fx) + sum(l1(g) * s.l1B() for g, s in zip(gs, S))
    idDeg = [max(degK(k, Fx), max([degK(k, g) + 2 * mxs(k, s.z) for g, s in zip(gs, S)], default=0))
             for k in range(3)]
    w = (idL.bit_length() - 1 if idL > 0 else 0) + 1           # Nat.log2 idL + 1
    D = max(idDeg) + 1
    val = kev(w, D, Fx) - sum(kev(w, D, g) * fqFlat(w, D, s) for g, s in zip(gs, S))
    info.update(dict(wf=True, idL_bits=idL.bit_length(), l1_Fx_bits=l1(Fx).bit_length(), w=w, D=D,
                     idDeg=idDeg, kron_point_bits=w * D * D * D, hybVal_zero=(val == 0)))
    return val == 0


# ====================================================================== TCert (CertT.lean)
class TCert:
    fields = ["dd", "Lam", "an", "ad", "bn", "bd", "e", "cal", "cbe", "HA", "HB", "HC", "ψBa", "ψCb",
              "FP", "FR", "mA", "mB", "mG", "SA", "SB", "SG"]

    def __init__(self, **kw):
        self.__dict__.update(kw)

    def K(self):
        return self.dd + 1

    def m(self, k):
        return self.dd + 1 - k            # Nat subtraction; k <= dd in use

    def blkP(self, k):
        return getD(self.FP, k, EMPTY)

    def blkR(self, k):
        return getD(self.FR, k, EMPTY)

    def SPE(self):
        if not hasattr(self, "_SPE"):
            self._SPE = SE(self.K(), self.m, self.blkP)
        return self._SPE

    def SRE(self):
        if not hasattr(self, "_SRE"):
            self._SRE = SE(self.K(), self.m, self.blkR)
        return self._SRE

    def FA(self):
        return smul(self.mA, lamAE(self.HA, self.ψBa, self.cal, self.SPE(), self.SRE()))

    def FB(self):
        return smul(self.mB, lamBE(self.HB, self.ψBa, self.ψCb, self.cbe, self.SPE(), self.SRE()))

    def FG(self):
        return smul(self.mG, lamGE(self.HC, self.ψCb, self.e, self.cal, self.cbe, self.SPE(), self.SRE()))

    def checkMeta(self, info):
        parts = dict(Lam=0 < self.Lam, ad=0 < self.ad, bd=0 < self.bd, mA=0 < self.mA, mB=0 < self.mB,
                     mG=0 < self.mG,
                     FP=all(blk_ok(self.m(k), self.blkP(k)) for k in range(self.K())),
                     FR=all(blk_ok(self.m(k), self.blkR(k)) for k in range(self.K())),
                     SA=all(okF(len(s.z), s.B()) for s in self.SA),
                     SB=all(okF(len(s.z), s.B()) for s in self.SB),
                     SG=all(okF(len(s.z), s.B()) for s in self.SG))
        info.update(parts)
        return all(parts.values())

    def chkA(self, info):
        return hybChk(self.FA(), self.an, self.ad, self.bn, self.bd, self.SA, info)

    def chkB(self, info):
        return hybChk(self.FB(), self.an, self.ad, 1, 1, self.SB, info)

    def chkG(self, info):
        return hybChk(self.FG(), self.an, self.ad, 1, 1, self.SG, info)


# ====================================================================== exact integer LDL^T + DD remainder
def round_div(a, b):
    """nearest integer to a/b, b > 0."""
    return (2 * a + b) // (2 * b)


def decompose(M, order=None):
    """M: symmetric integer matrix (list of lists), PD.  Returns (order, d, l, Delta) with
         M[order][order] = sum_q d_q l_q l_q^T + Delta   EXACTLY,
       d_q >= 0, l_q[a] = 0 for a < q, l_q[q] = 2^{s_q}, Delta symmetric and diagonally dominant
       (Delta_qq >= sum_{c != q} |Delta_qc|), or None.
       Row q of Delta is final after step q; the pivot is reduced ("margin") so that the diagonal residual pays
       for the row's off-diagonal rounding residuals (left: earlier steps, right: this step)."""
    n = len(M)
    if order is None:
        order = list(range(n))
    A = [[M[order[i]][order[j]] for j in range(n)] for i in range(n)]
    d = [0] * n
    L = [[0] * n for _ in range(n)]
    for q in range(n):
        p = A[q][q]
        rowq = A[q]
        left = sum(abs(rowq[cc]) for cc in range(q))
        if p < left:
            return None
        rest = range(q + 1, n)
        best = None
        s0 = max(0, (max(1, n - q) * max(p, 1)).bit_length() // 3)
        for s in range(max(0, s0 - 4), s0 + 5):
            margin = left
            for _ in range(12):
                dq = (p - margin) >> (2 * s) if p > margin else 0
                if dq <= 0:
                    dq = 0
                    lv = [0] * n
                    right = sum(abs(rowq[cc]) for cc in rest)
                else:
                    sc = dq << s
                    lv = [0] * n
                    right = 0
                    for cc in rest:
                        x = round_div(rowq[cc], sc)
                        lv[cc] = x
                        right += abs(rowq[cc] - sc * x)
                diag = p - (dq << (2 * s))
                if diag >= left + right:
                    cand = (diag, s, dq, lv)
                    if best is None or cand[0] < best[0]:
                        best = cand
                    break
                if dq == 0:
                    break
                margin = left + right + (right >> 8) + 1
        if best is None:
            return None
        diag, s, dq, lv = best
        if dq > 0:
            lv[q] = 1 << s
        L[q] = lv
        d[q] = dq
        if dq:
            v = lv
            for a in range(q, n):
                if v[a] == 0:
                    continue
                da = dq * v[a]
                Aa = A[a]
                for cc in range(q, n):
                    if v[cc]:
                        Aa[cc] -= da * v[cc]
    Delta = A
    return order, d, L, Delta


def verify_decomp(M, order, d, L, Delta):
    n = len(M)
    for a in range(n):
        for cc in range(n):
            s = sum(d[q] * L[q][a] * L[q][cc] for q in range(n) if d[q] and L[q][a] and L[q][cc])
            if s + Delta[a][cc] != M[order[a]][order[cc]]:
                return False
    return True


def pivot_order(M):
    """greedy diagonal pivoting order (largest Schur-complement diagonal first), float64, used only to order z."""
    import numpy as np
    sh = max(0, max(abs(x) for row in M for x in row).bit_length() - 900)     # keep floats finite
    A = np.array([[float(x >> sh) for x in row] for row in M])
    A = A / max(1.0, float(np.max(np.abs(A))))
    n = len(A)
    idx = list(range(n))
    order = []
    for _ in range(n):
        j = max(idx, key=lambda i: A[i, i])
        order.append(j)
        idx.remove(j)
        pj = A[j, j]
        if pj <= 0:
            order.extend(idx)
            break
        col = A[:, j].copy()
        for i in idx:
            A[i, idx] -= col[i] * col[idx] / pj
    return order


def packed_bits(r, d, L, Delta):
    Bd, Bl, BD = width(d), width([x for row in L for x in row]), width([x for row in Delta for x in row])
    return Bd, Bl, BD, r * Bd + r * r * (Bl + BD)


# ====================================================================== exact polynomial helpers (JSON side)
def P_add(p, q, cf=1):
    r = dict(p)
    for k, v in q.items():
        w = r.get(k, 0) + cf * v
        if w == 0:
            r.pop(k, None)
        else:
            r[k] = w
    return r


def P_mul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
            r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}


def monos_upto(dg):                 # numerics/hp/check_cert.py order (the JSON B index order)
    return [e for e in itertools.product(range(dg + 1), repeat=3) if sum(e) <= dg]


def code_poly(an, ad, bn, bd, codes):
    return {k: Fr(v) for k, v in expand(gT(an, ad, bn, bd, codes)).items()}


def match_codes(g, an, ad, bn, bd):
    """smallest code list whose gT is a POSITIVE multiple of g; returns (codes, scale) with gT = scale * g."""
    cands = [[]] + [[j] for j in range(14)] + [[i, j] for i in range(14) for j in range(i, 14)]
    for codes in cands:
        P = code_poly(an, ad, bn, bd, codes)
        if set(P) != set(g):
            continue
        k0 = next(iter(g))
        scale = P[k0] / g[k0]
        if scale > 0 and all(P[k] == scale * g[k] for k in g):
            return codes, scale
    return None, None


# ====================================================================== build the TCert data from the JSON
def load_json(path):
    J = json.load(open(path))
    assert J["kind"] == "slab" and J["kernel"].startswith("coulomb"), "expects a Coulomb slab certificate"
    return J


def build(J, log_fn=log):
    D = J["D"]
    dd = D // 2
    lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
    an, ad, bn, bd = lo.numerator, lo.denominator, hi.numerator, hi.denominator
    H = {X: [Fr(x) for x in J["H"][X]] for X in "ABC"}
    psi = {k: [Fr(x) for x in J["psi"][k]] for k in ("Ba", "Cb")}
    ca, cb, e = Fr(J["ca"]), Fr(J["cb"]), Fr(J["e"])
    F = {X: [[[Fr(x) for x in row] for row in M] for M in J["F"][X]] for X in "PR"}
    assert [len(M) for M in F["P"]] == [dd + 1 - k for k in range(dd + 1)] == [len(M) for M in F["R"]]
    # ---- Lam
    L0 = 1
    for xs in list(H.values()) + list(psi.values()) + [[ca, cb, e]]:
        for x in xs:
            L0 = lcm(L0, x.denominator)
    for X in "PR":
        for M in F[X]:
            for row in M:
                for x in row:
                    L0 = lcm(L0, x.denominator)
    rep = {"Lam0": L0}
    for k in range(0, 200):
        Lam = L0 << k
        blocks = {}
        good = True
        for X in "PR":
            for kk, M in enumerate(F[X]):
                Mi = [[int(x * Lam) for x in row] for row in M]
                assert all(Fr(Mi[i][j]) == M[i][j] * Lam for i in range(len(M)) for j in range(len(M)))
                res = decompose(Mi)
                if res is None:
                    good = False
                    break
                blocks[(X, kk)] = (Mi, res)
            if not good:
                break
        if good:
            break
    rep["Lam_shift"] = k
    log_fn(f"Lam = Lam0 * 2^{k}  (Lam0 = 2^{L0.bit_length() - 1}{'' if L0 & (L0 - 1) == 0 else ' NOT a power of 2'})")
    FP, FR = [], []
    for X, out in (("P", FP), ("R", FR)):
        for kk in range(dd + 1):
            Mi, (order, d, Lc, Dl) = blocks[(X, kk)]
            assert order == list(range(len(Mi))) and verify_decomp(Mi, order, d, Lc, Dl)
            out.append((Mi, d, Lc, Dl))
    toI = lambda x: int(x * Lam) if (x * Lam).denominator == 1 else None
    data = dict(dd=dd, Lam=Lam, an=an, ad=ad, bn=bn, bd=bd, e=toI(e), cal=toI(ca), cbe=toI(cb),
                HA=[toI(x) for x in H["A"]], HB=[toI(x) for x in H["B"]], HC=[toI(x) for x in H["C"]],
                ψBa=[toI(x) for x in psi["Ba"]], ψCb=[toI(x) for x in psi["Cb"]], FP=FP, FR=FR)
    for k2, v in data.items():
        assert v is not None and (not isinstance(v, list) or all(x is not None for x in v if not isinstance(x, tuple))), k2
    # ---- SOS
    factor = {"A": 5, "B": 4, "G": 30}
    band = {"A": (bn, bd), "B": (1, 1), "G": (1, 1)}
    rep["codes"] = {}
    for tag, mname, sname in (("A", "mA", "SA"), ("B", "mB", "SB"), ("G", "mG", "SG")):
        bn_, bd_ = band[tag]
        blks = J["SOS"][tag]
        meta = []
        m0 = 1
        for r, blk in enumerate(blks):
            g = {tuple(int(x) for x in k2.split(",")): Fr(v) for k2, v in blk["g"].items()}
            codes, scale = match_codes(g, an, ad, bn_, bd_)
            if codes is None:
                raise SystemExit(f"multiplier {tag}{r} {blk['g']} not expressible by upstream codes")
            Z = monos_upto(blk["d"])
            Bq = [[Fr(x) for x in row] for row in blk["B"]]
            assert len(Bq) == len(Z)
            f = factor[tag] * Lam / scale
            for row in Bq:
                for x in row:
                    m0 = lcm(m0, (f * x).denominator)
            meta.append((codes, scale, Z, Bq, g))
            rep["codes"][f"{tag}{r}"] = (blk["g"], codes, str(scale))
        for j in range(0, 200):
            mm = m0 << j
            res = []
            for codes, scale, Z, Bq, g in meta:
                f = factor[tag] * Lam * mm / scale
                Mi = [[int(f * x) for x in row] for row in Bq]
                assert all(Fr(Mi[i][jj]) == f * Bq[i][jj] for i in range(len(Z)) for jj in range(len(Z)))
                best = None
                for order in (sorted(range(len(Z)), key=lambda i: (sum(Z[i]), Z[i])), pivot_order(Mi)):
                    out = decompose(Mi, order)
                    if out is None:
                        continue
                    bits = packed_bits(len(Z), out[1], out[2], out[3])[3]
                    if best is None or bits < best[0]:
                        best = (bits, out)
                if best is None:
                    res = None
                    break
                res.append((codes, Z, Mi, best[1]))
            if res is not None:
                break
        log_fn(f"{mname} = {m0} * 2^{j}")
        rep[f"{mname}_base"], rep[f"{mname}_shift"] = m0, j
        data[mname] = mm
        S = []
        for codes, Z, Mi, (order, d, Lc, Dl) in res:
            assert verify_decomp(Mi, order, d, Lc, Dl)
            S.append((codes, [Z[i] for i in order], d, Lc, Dl))
        data[sname] = S
    return data, rep


# ====================================================================== Lean emission
def hexs(x):
    return hex(x)


def emit_blk(name, blk):
    Mi, d, Lc, Dl = blk
    r = len(d)
    Bd, Bl, BD, _ = packed_bits(r, d, Lc, Dl)
    return (f"def {name} : Blk := mkBlk {r} {Bd} {Bl} {BD}\n  {hexs(packI(Bd, d))}\n  {hexs(packM(Bl, Lc))}\n"
            f"  {hexs(packM(BD, Dl))}\n")


def emit_tblk(name, s):
    codes, z, d, Lc, Dl = s
    r = len(d)
    Bd, Bl, BD, _ = packed_bits(r, d, Lc, Dl)
    zs = ", ".join(f"({a}, {b}, {dd})" for a, b, dd in z)
    return (f"def {name} : TBlk :=\n  ⟨[{', '.join(map(str, codes))}], [{zs}], {r}, {Bd}, {Bl}, {BD},\n"
            f"  {hexs(packI(Bd, d))},\n  {hexs(packM(Bl, Lc))},\n  {hexs(packM(BD, Dl))}⟩\n")


def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def header(imports, src, sha, what):
    return ("".join(f"import {i}\n" for i in imports)
            + f"/-! {what}\n    Generated by `numerics/n7_interval/lean/gen/emit_tcert.py` from `{src}` (sha256 {sha[:16]}…).\n"
            + "    Coulomb kernel `phi t = (2-2t)^(-1/2)`; format = upstream `TCert` (ThomsonGen/CertT.lean).\n"
            + "    Regenerate; do not edit. -/\n\n")


OPENS = "namespace CoulN7\nopen ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.ThreePoint\n\n-- large literal lists: elaboration budget only (no effect on what is checked)\nset_option maxHeartbeats 0\n\n"


def emit(data, name, jpath, outdir, split_mode, max_module):
    nm = "tc_" + name.lower()
    sec = f"CoulN7_{name}_tc"
    src = os.path.basename(jpath)
    sha = hashlib.sha256(open(jpath, "rb").read()).hexdigest()
    os.makedirs(outdir, exist_ok=True)
    fdefs = "".join(emit_blk(f"{nm}_F{X}{k}", b) for X, key in (("P", "FP"), ("R", "FR"))
                    for k, b in enumerate(data[key]))
    sdefs = {sn: "".join(emit_tblk(f"{nm}_{sn}{r}", s) for r, s in enumerate(data[sn])) for sn in ("SA", "SB", "SG")}
    tc = (f"def {nm} : TCert where\n  dd := {data['dd']}\n  Lam := {data['Lam']}\n  an := {data['an']}\n"
          f"  ad := {data['ad']}\n  bn := {data['bn']}\n  bd := {data['bd']}\n  e := {data['e']}\n"
          f"  cal := {data['cal']}\n  cbe := {data['cbe']}\n  HA := {lst(data['HA'])}\n  HB := {lst(data['HB'])}\n"
          f"  HC := {lst(data['HC'])}\n  ψBa := {lst(data['ψBa'])}\n  ψCb := {lst(data['ψCb'])}\n"
          f"  FP := {lst(f'{nm}_FP{k}' for k in range(len(data['FP'])))}\n"
          f"  FR := {lst(f'{nm}_FR{k}' for k in range(len(data['FR'])))}\n"
          f"  mA := {data['mA']}\n  mB := {data['mB']}\n  mG := {data['mG']}\n"
          + "".join(f"  {sn} := {lst(f'{nm}_{sn}{r}' for r in range(len(data[sn])))}\n" for sn in ("SA", "SB", "SG")))
    mod = f"CoulN7.{name}"
    single = len(fdefs) + sum(len(v) for v in sdefs.values()) + len(tc)
    split = split_mode or single > max_module
    files = {}
    tail = f"\nend CoulN7\nend {sec}\n"
    if not split:
        files["Data.lean"] = (header(["ThomsonGen.CertT"], src, sha, f"`TCert` data of the slab {name}.")
                              + f"open Real\n\nsection {sec}\n" + OPENS + fdefs + "\n" + sdefs["SA"] + "\n"
                              + sdefs["SB"] + "\n" + sdefs["SG"] + "\n" + tc + tail)
    else:
        for sn, fn in (("SA", "DataA"), ("SB", "DataB"), ("SG", "DataG")):
            files[f"{fn}.lean"] = (header(["ThomsonGen.CertT"], src, sha,
                                          f"`TCert` data of the slab {name}: SOS blocks `{sn}`.")
                                   + f"open Real\n\nsection {sec}\n" + OPENS + sdefs[sn] + tail)
        files["Data.lean"] = (header([f"{mod}.DataA", f"{mod}.DataB", f"{mod}.DataG"], src, sha,
                                     f"`TCert` data of the slab {name}: F-blocks and the certificate.")
                              + f"open Real\n\nsection {sec}\n" + OPENS + fdefs + "\n" + tc + tail)
    for suf, fn, what in (("meta", "checkMeta", "ChkMeta"), ("A", "chkA", "ChkA"), ("B", "chkB", "ChkB"),
                          ("G", "chkG", "ChkG")):
        files[f"{what}.lean"] = (header([f"{mod}.Data"], src, sha, f"Kernel check `{fn}` of the slab {name}.")
                                 + f"open Real\n\nsection {sec}\n" + OPENS
                                 + f"theorem {nm}_{suf} : {nm}.{fn} = true := by decide +kernel\n" + tail)
    for fn, txt in files.items():
        with open(os.path.join(outdir, fn), "w") as fh:
            fh.write(txt)
    return {fn: len(txt.encode()) for fn, txt in files.items()}


# ====================================================================== parse the emitted files back
HEX = r"(0x[0-9a-f]+)"


def parse(outdir, name):
    nm = "tc_" + name.lower()
    txt = ""
    for fn in sorted(os.listdir(outdir)):
        if fn.startswith("Data") and fn.endswith(".lean"):
            txt += open(os.path.join(outdir, fn), encoding="utf-8").read() + "\n"
    blks = {}
    for m in re.finditer(r"def (\S+) : Blk := mkBlk (\d+) (\d+) (\d+) (\d+)\s+" + HEX + r"\s+" + HEX + r"\s+" + HEX,
                         txt):
        r, Bd, Bl, BD = map(int, m.group(2, 3, 4, 5))
        blks[m.group(1)] = mkBlk(r, Bd, Bl, BD, *(int(m.group(i), 16) for i in (6, 7, 8)))
    tblks = {}
    for m in re.finditer(r"def (\S+) : TBlk :=\s+⟨\[([0-9, ]*)\], \[([0-9(), ]*)\], (\d+), (\d+), (\d+), (\d+),\s+"
                         + HEX + r",\s+" + HEX + r",\s+" + HEX + "⟩", txt):
        g = [int(x) for x in m.group(2).split(",") if x.strip()]
        z = [tuple(int(y) for y in t.split(",")) for t in re.findall(r"\(([0-9, ]+)\)", m.group(3))]
        r, Bd, Bl, BD = map(int, m.group(4, 5, 6, 7))
        tblks[m.group(1)] = TBlk(g, z, r, Bd, Bl, BD, *(int(m.group(i), 16) for i in (8, 9, 10)))
    body = txt[txt.index(f"def {nm} : TCert where"):]
    kw = {}
    for f in TCert.fields:
        m = re.search(r"\n  " + re.escape(f) + r" := (.*)\n", body)
        v = m.group(1).strip()
        if v.startswith("["):
            items = [x.strip() for x in v[1:-1].split(",") if x.strip()]
            if f in ("FP", "FR"):
                kw[f] = [blks[x] for x in items]
            elif f in ("SA", "SB", "SG"):
                kw[f] = [tblks[x] for x in items]
            else:
                kw[f] = [int(x) for x in items]
        else:
            kw[f] = int(v)
    return TCert(**kw), (len(blks), len(tblks))


# ====================================================================== --check
def blk_ent(r, b, a, cc):
    return sum(b.dq(q) * b.lq(q, a) * b.lq(q, cc) for q in range(r)) + b.dl(a, cc)


def compare_json(tc, J):
    """exact comparison of the parsed Lean data with the JSON certificate."""
    out = {}
    Lam = Fr(tc.Lam)
    lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
    out["cell"] = Fr(tc.an, tc.ad) == lo and Fr(tc.bn, tc.bd) == hi
    out["H"] = all([Fr(x) / Lam for x in getattr(tc, "H" + X)] == [Fr(y) for y in J["H"][X]] for X in "ABC")
    out["psi"] = ([Fr(x) / Lam for x in tc.ψBa] == [Fr(y) for y in J["psi"]["Ba"]]
                  and [Fr(x) / Lam for x in tc.ψCb] == [Fr(y) for y in J["psi"]["Cb"]])
    out["consts"] = (Fr(tc.e) / Lam == Fr(J["e"]) and Fr(tc.cal) / Lam == Fr(J["ca"])
                     and Fr(tc.cbe) / Lam == Fr(J["cb"]))
    okF_ = True
    for X, key in (("P", "FP"), ("R", "FR")):
        okF_ &= len(getattr(tc, key)) == len(J["F"][X])          # no silent truncation by zip/enumerate
        for k, M in enumerate(J["F"][X]):
            if k >= len(getattr(tc, key)):
                okF_ = False
                break
            b = getattr(tc, key)[k]
            r = tc.m(k)
            okF_ &= len(M) == r and all(len(row) == r for row in M) and all(
                Fr(blk_ent(r, b, a, cc)) / Lam == Fr(M[a][cc]) for a in range(r) for cc in range(r))
    out["F"] = okF_
    factor = {"A": 5, "B": 4, "G": 30}
    okS = True
    for tag, sname, mname in (("A", "SA", "mA"), ("B", "SB", "mB"), ("G", "SG", "mG")):
        bn_, bd_ = (tc.bn, tc.bd) if tag == "A" else (1, 1)
        S = getattr(tc, sname)
        okS &= len(S) == len(J["SOS"][tag])
        for s, blk in zip(S, J["SOS"][tag]):
            g = {tuple(int(x) for x in k2.split(",")): Fr(v) for k2, v in blk["g"].items()}
            P = code_poly(tc.an, tc.ad, bn_, bd_, s.g)
            k0 = next(iter(g))
            scale = P[k0] / g[k0]
            okS &= scale > 0 and set(P) == set(g) and all(P[k2] == scale * g[k2] for k2 in g)
            Z = monos_upto(blk["d"])
            pos = {t: i for i, t in enumerate(Z)}
            okS &= sorted(s.z) == sorted(Z) and len(s.z) == len(set(s.z))
            okS &= len(blk["B"]) == len(Z) and all(len(row) == len(Z) for row in blk["B"])
            b = s.B()
            f = factor[tag] * Lam * getattr(tc, mname) / scale
            r = len(s.z)
            for a in range(r):
                for cc in range(r):
                    if Fr(blk_ent(r, b, a, cc)) != f * Fr(blk["B"][pos[s.z[a]]][pos[s.z[cc]]]):
                        okS = False
    out["SOS"] = okS
    return out


def run_check(outdir, name, J=None, poly=True):
    tc, nb = parse(outdir, name)
    log(f"parsed {outdir}: {nb[0]} Blk, {nb[1]} TBlk; dd={tc.dd} Lam=2^{tc.Lam.bit_length() - 1} "
        f"mA={tc.mA} mB={tc.mB} mG={tc.mG}")
    res = {}
    info = {}
    res["checkMeta"] = (tc.checkMeta(info), info)
    log(f"checkMeta = {res['checkMeta'][0]}  {info}")
    for nmk, mkFx, S in (("chkA", tc.FA, tc.SA), ("chkB", tc.FB, tc.SB), ("chkG", tc.FG, tc.SG)):
        KEVSTAT[0] = 0
        info = {}
        t1 = time.time()
        Fx = mkFx()
        bn_, bd_ = (tc.bn, tc.bd) if nmk == "chkA" else (1, 1)
        ok = hybChk(Fx, tc.an, tc.ad, bn_, bd_, S, info)     # = TCert.chkA / chkB / chkG
        info["max_int_bits"] = KEVSTAT[0]
        info["time_s"] = round(time.time() - t1, 1)
        if poly:     # independent cross-check: collected polynomial identity of the same data
            lhs = dict(expand(Fx))
            for s in S:
                b = s.B()
                zz = {}
                r = len(s.z)
                for a in range(r):
                    for cc in range(r):
                        v = blk_ent(r, b, a, cc)
                        if v:
                            k3 = tuple(x + y for x, y in zip(s.z[a], s.z[cc]))
                            zz[k3] = zz.get(k3, 0) + v
                lhs = P_add(lhs, P_mul(expand(gT(tc.an, tc.ad, bn_, bd_, s.g)), zz), -1)
            info["poly_identity_exact"] = not lhs
            info["poly_max_degree"] = max((sum(k3) for k3 in expand(Fx)), default=0)
        res[nmk] = (ok, info)
        log(f"{nmk} = {ok}  {info}")
    if J is not None:
        res["json_equal"] = compare_json(tc, J)
        log(f"exact equality with JSON: {res['json_equal']}")
    allok = all(v[0] for k, v in res.items() if k != "json_equal") and (J is None or all(res["json_equal"].values()))
    if poly:     # the independent polynomial identity is part of the verdict
        allok = allok and all(res[n][1].get("poly_identity_exact") is True for n in ("chkA", "chkB", "chkG"))
    return allok, res, tc


# ====================================================================== --tcertn: facially reduced cap (ThomsonGen/Cert/NBlk.lean)
# NBlk  = ⟨N (m rows of r ints), r, Bd, Bl, BD, xd, xl, xD⟩   (reduced block B′ = mkBlk r …, okF r B′)
# TBlkN = ⟨g, z, nb, BDe, BD⟩ (BD = packM BDe m expandΔ, stored)  ;  TCertN = TCert fields with FP FR : List NBlk, SA SB SG : List TBlkN.
# checkMeta: positivity, FP/FR lengths = dd+1, okN of every block; chkX = upstream chkX of toTCert.
class NBlkS:
    def __init__(self, N, r, Bd, Bl, BD, xd, xl, xD):
        self.N, self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD = N, r, Bd, Bl, BD, xd, xl, xD

    def inner(self):
        return mkBlk(self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD)

    def n(self, a, i):
        return getD(getD(self.N, a, []), i, 0)

    def expandD(self, m):
        """expandΔ m: eent a c = sum_i sum_j n a i * ent_r(i,j) * n c j (same value as the Lean list sums)."""
        b = self.inner()
        r = self.r
        E = [[blk_ent(r, b, i, j) for j in range(r)] for i in range(r)]
        Nm = [[self.n(a, i) for i in range(r)] for a in range(m)]
        NE = [[sum(Nm[a][i] * E[i][j] for i in range(r) if Nm[a][i]) for j in range(r)] for a in range(m)]
        return [[sum(NE[a][j] * Nm[cc][j] for j in range(r) if Nm[cc][j]) for cc in range(m)] for a in range(m)]

    def okN(self):
        # NBlk.okN: every row of N has length <= r, and the reduced block passes okF r
        return all(len(row) <= self.r for row in self.N) and okF(self.r, self.inner())


NB_EMPTY = NBlkS([], 0, 1, 1, 1, 0, 0, 0)


def packI_lean(B, vs):
    """NBlk.lean packI: (v + offB B).toNat + (packI B vs <<< B)."""
    x = 0
    for v in reversed(vs):
        x = max(0, v + offB(B)) + (x << B)
    return x


def packM_lean(B, cols, rows):
    x = 0
    for row in reversed(rows):
        x = packI_lean(B, row) + (x << (B * cols))
    return x


class TBlkNS:
    def __init__(self, g, z, nb, BDe, BD=None):
        self.g, self.z, self.nb, self.BDe, self.BD = g, z, nb, BDe, BD
        self._E = None

    def m(self):
        return len(self.z)

    def E(self):
        if self._E is None:
            self._E = self.nb.expandD(self.m())
        return self._E

    def toTBlk(self):
        m = self.m()
        return TBlk(self.g, self.z, m, 1, 1, self.BDe, 2 ** m - 1, 2 ** (m * m) - 1,
                    packM_lean(self.BDe, m, self.E()) if self.BD is None else self.BD)

    def okN(self):
        tb = self.toTBlk().B()
        return (self.nb.okN() and len(self.nb.N) == self.m() and all(x == 0 for x in tb.d)
                and tb.D == self.E())


class TCertNS:
    def __init__(self, **kw):
        self.__dict__.update(kw)

    def K(self):
        return self.dd + 1

    def m(self, k):
        return self.dd + 1 - k

    def toTCert(self):
        FPx = [getD(self.FP, k, NB_EMPTY) for k in range(self.K())]
        FRx = [getD(self.FR, k, NB_EMPTY) for k in range(self.K())]
        ex = lambda nb, k: Blk([], [], nb.expandD(self.m(k)))
        return TCert(dd=self.dd, Lam=self.Lam, an=self.an, ad=self.ad, bn=self.bn, bd=self.bd, e=self.e, cal=self.cal,
                     cbe=self.cbe, HA=self.HA, HB=self.HB, HC=self.HC, ψBa=self.ψBa, ψCb=self.ψCb,
                     FP=[ex(nb, k) for k, nb in enumerate(FPx)], FR=[ex(nb, k) for k, nb in enumerate(FRx)],
                     mA=self.mA, mB=self.mB, mG=self.mG, SA=[s.toTBlk() for s in self.SA],
                     SB=[s.toTBlk() for s in self.SB], SG=[s.toTBlk() for s in self.SG])

    def checkMeta(self, info):
        parts = dict(Lam=0 < self.Lam, ad=0 < self.ad, bd=0 < self.bd, mA=0 < self.mA, mB=0 < self.mB,
                     mG=0 < self.mG, lenFP=len(self.FP) == self.K(), lenFR=len(self.FR) == self.K(),
                     rowsFP=all(len(getD(self.FP, k, NB_EMPTY).N) == self.m(k) for k in range(self.K())),
                     rowsFR=all(len(getD(self.FR, k, NB_EMPTY).N) == self.m(k) for k in range(self.K())),
                     FP=all(nb.okN() for nb in self.FP), FR=all(nb.okN() for nb in self.FR),
                     SA=all(s.okN() for s in self.SA), SB=all(s.okN() for s in self.SB),
                     SG=all(s.okN() for s in self.SG))
        info.update(parts)
        return all(parts.values())


def int_cols(N):
    k = len(N[0]) if N and N[0] else 0
    cs = []
    for c_ in range(k):
        L = 1
        for row in N:
            L = lcm(L, row[c_].denominator)
        cs.append(L)
    return [[int(row[c_] * cs[c_]) for c_ in range(k)] for row in N], cs


def build_n(J, log_fn=log):
    D = J["D"]
    dd = D // 2
    lo, hi = Fr(J["cell"][0]), Fr(J["cell"][1])
    an, ad, bn, bd = lo.numerator, lo.denominator, hi.numerator, hi.denominator
    H = {X: [Fr(x) for x in J["H"][X]] for X in "ABC"}
    psi = {k: [Fr(x) for x in J["psi"][k]] for k in ("Ba", "Cb")}
    ca, cb, e = Fr(J["ca"]), Fr(J["cb"]), Fr(J["e"])
    Fb = {}
    for X in "PR":
        for k, b in enumerate(J["F"][X]):
            m = b["m"]
            assert m == dd + 1 - k
            if b["red"]:
                Ni, cs = int_cols([[Fr(x) for x in row] for row in b["N"]])
                R = [[Fr(x) / (cs[i] * cs[j]) for j, x in enumerate(row)] for i, row in enumerate(b["red"])]
            else:
                Ni, R = [[] for _ in range(m)], []
            Fb[(X, k)] = (m, Ni, R)
    L0 = 1
    for xs in list(H.values()) + list(psi.values()) + [[ca, cb, e]]:
        for x in xs:
            L0 = lcm(L0, x.denominator)
    for (m, Ni, R) in Fb.values():
        for row in R:
            for x in row:
                L0 = lcm(L0, x.denominator)
    rep = {"Lam0_bits": L0.bit_length()}

    def dec_best(Mi, allow_perm):
        best = None
        orders = [None] + ([pivot_order(Mi)] if allow_perm and len(Mi) > 1 else [])
        for order in orders:
            out = decompose(Mi, order)
            if out is None:
                continue
            bits_ = packed_bits(len(Mi), out[1], out[2], out[3])[3]
            if best is None or bits_ < best[0]:
                best = (bits_, out)
        return None if best is None else best[1]

    for k in range(0, 60):
        Lam = L0 << k
        FB = {}
        ok = True
        for key, (m, Ni, R) in Fb.items():
            Mi = [[int(x * Lam) for x in row] for row in R]
            assert all(Fr(Mi[i][j]) == R[i][j] * Lam for i in range(len(R)) for j in range(len(R)))
            out = dec_best(Mi, True) if R else ([], [], [], [])
            if out is None:
                ok = False
                break
            FB[key] = (m, Ni, Mi, out)
        if ok:
            break
    rep["Lam_shift"] = k
    log_fn(f"TCertN: Lam = lcm(denominators) * 2^{k}, {Lam.bit_length()} bits; e*Lam integral: {(e * Lam).denominator == 1}")
    toI = lambda x: int(x * Lam) if (x * Lam).denominator == 1 else None

    def nblk(m, Ni, Mi, out):
        order, d, Lc, Dl = out
        r = len(d)
        Np = [[row[order[i]] for i in range(r)] for row in Ni] if r else [[] for _ in range(m)]
        Mp = [[Mi[order[i]][order[j]] for j in range(r)] for i in range(r)]
        assert verify_decomp(Mp, list(range(r)), d, Lc, Dl) if r else True
        return (Np, d, Lc, Dl)

    FP = [nblk(*FB[("P", k)]) for k in range(dd + 1)]
    FR = [nblk(*FB[("R", k)]) for k in range(dd + 1)]
    data = dict(dd=dd, Lam=Lam, an=an, ad=ad, bn=bn, bd=bd, e=toI(e), cal=toI(ca), cbe=toI(cb),
                HA=[toI(x) for x in H["A"]], HB=[toI(x) for x in H["B"]], HC=[toI(x) for x in H["C"]],
                ψBa=[toI(x) for x in psi["Ba"]], ψCb=[toI(x) for x in psi["Cb"]], FP=FP, FR=FR)
    for k2 in ("e", "cal", "cbe"):
        assert data[k2] is not None, k2
    for k2 in ("HA", "HB", "HC", "ψBa", "ψCb"):
        assert None not in data[k2], k2
    factor = {"A": 5, "B": 4, "G": 30}
    rep["codes"] = {}
    for tag, mname, sname in (("A", "mA", "SA"), ("B", "mB", "SB"), ("G", "mG", "SG")):
        bn_, bd_ = (bn, bd) if tag == "A" else (1, 1)
        meta = []
        m0 = 1
        for r_, blk in enumerate(J["SOS"][tag]):
            g = {tuple(int(x) for x in k2.split(",")): Fr(v) for k2, v in blk["g"].items()}
            codes, scale = match_codes(g, an, ad, bn_, bd_)
            if codes is None:
                raise SystemExit(f"multiplier {tag}{r_} not expressible")
            Z = monos_upto(blk["d"])
            if blk["red"]:
                Ni, cs = int_cols([[Fr(x) for x in row] for row in blk["N"]])
                R = [[Fr(x) / (cs[i] * cs[j]) for j, x in enumerate(row)] for i, row in enumerate(blk["red"])]
            else:
                Ni, R = [[] for _ in Z], []
            f = factor[tag] * Lam / scale
            for row in R:
                for x in row:
                    m0 = lcm(m0, (f * x).denominator)
            meta.append((codes, scale, Z, Ni, R))
            rep["codes"][f"{tag}{r_}"] = (blk["g"], codes, str(scale))
        for j in range(0, 60):
            mm = m0 << j
            res = []
            for codes, scale, Z, Ni, R in meta:
                f = factor[tag] * Lam * mm / scale
                Mi = [[int(f * x) for x in row] for row in R]
                assert all(Fr(Mi[i][jj]) == f * R[i][jj] for i in range(len(R)) for jj in range(len(R)))
                out = dec_best(Mi, True) if R else ([], [], [], [])
                if out is None:
                    res = None
                    break
                res.append((codes, Z, nblk(len(Z), Ni, Mi, out)))
            if res is not None:
                break
        log_fn(f"TCertN: {mname} = {m0} * 2^{j}")
        data[mname] = mm
        S = []
        for codes, Z, (Np, d, Lc, Dl) in res:
            nb = NBlkS(Np, len(d), *packed_bits(len(d), d, Lc, Dl)[:3], 0, 0, 0)
            r = len(d)
            b = Blk(d, Lc, Dl)
            E = [[blk_ent(r, b, i, jj) for jj in range(r)] for i in range(r)]
            NE = [[sum(Np[a][i] * E[i][jj] for i in range(r) if Np[a][i]) for jj in range(r)] for a in range(len(Z))]
            Ex = [[sum(NE[a][jj] * Np[cc][jj] for jj in range(r) if Np[cc][jj]) for cc in range(len(Z))] for a in range(len(Z))]
            BDe = width([x for row in Ex for x in row])
            S.append((codes, Z, (Np, d, Lc, Dl), BDe, packM_lean(BDe, len(Z), Ex)))
        data[sname] = S
    return data, rep


def emit_nblk_lit(Np, d, Lc, Dl, indent="  "):
    r = len(d)
    if r:
        Bd, Bl, BD, _ = packed_bits(r, d, Lc, Dl)
        xs = (packI(Bd, d), packM(Bl, Lc), packM(BD, Dl))
    else:
        Bd, Bl, BD, xs = 1, 1, 1, (0, 0, 0)
    Nl = "[" + ", ".join("[" + ", ".join(str(v) for v in row) + "]" for row in Np) + "]"
    return (f"⟨{Nl}, {r}, {Bd}, {Bl}, {BD},\n{indent}{hexs(xs[0])},\n{indent}{hexs(xs[1])},\n{indent}{hexs(xs[2])}⟩")


def emit_n(data, name, jpath, outdir, split_mode, max_module):
    nm = "tc_" + name.lower()
    sec = f"CoulN7_{name}_tc"
    src = os.path.basename(jpath)
    sha = hashlib.sha256(open(jpath, "rb").read()).hexdigest()
    os.makedirs(outdir, exist_ok=True)

    def hdr(imports, what):
        return ("".join(f"import {i}\n" for i in imports)
                + f"/-! {what}\n    Generated by `numerics/n7_interval/lean/gen/emit_tcert.py --tcertn` from `{src}` (sha256 {sha[:16]}…).\n"
                + "    Facially reduced typed certificate `TCertN` (ThomsonGen/Cert/NBlk.lean).  Regenerate; do not edit. -/\n\n")
    fdefs = "".join(f"def {nm}_F{X}{k} : NBlk :=\n  {emit_nblk_lit(*b)}\n" for X, key in (("P", "FP"), ("R", "FR"))
                    for k, b in enumerate(data[key]))
    sdefs = {}
    for sn in ("SA", "SB", "SG"):
        out = []
        for r, (codes, z, nbd, BDe, BDpk) in enumerate(data[sn]):
            zs = ", ".join(f"({a}, {b}, {c_})" for a, b, c_ in z)
            out.append(f"def {nm}_{sn}{r}_nb : NBlk :=\n  {emit_nblk_lit(*nbd)}\n"
                       f"def {nm}_{sn}{r} : TBlkN :=\n  ⟨[{', '.join(map(str, codes))}], [{zs}], {nm}_{sn}{r}_nb, {BDe}, 0x{BDpk:x}⟩\n")
        sdefs[sn] = "".join(out)
    tc = (f"def {nm} : TCertN where\n  dd := {data['dd']}\n  Lam := {data['Lam']}\n  an := {data['an']}\n"
          f"  ad := {data['ad']}\n  bn := {data['bn']}\n  bd := {data['bd']}\n  e := {data['e']}\n"
          f"  cal := {data['cal']}\n  cbe := {data['cbe']}\n  HA := {lst(data['HA'])}\n  HB := {lst(data['HB'])}\n"
          f"  HC := {lst(data['HC'])}\n  ψBa := {lst(data['ψBa'])}\n  ψCb := {lst(data['ψCb'])}\n"
          f"  FP := {lst(f'{nm}_FP{k}' for k in range(len(data['FP'])))}\n"
          f"  FR := {lst(f'{nm}_FR{k}' for k in range(len(data['FR'])))}\n"
          f"  mA := {data['mA']}\n  mB := {data['mB']}\n  mG := {data['mG']}\n"
          + "".join(f"  {sn} := {lst(f'{nm}_{sn}{r}' for r in range(len(data[sn])))}\n" for sn in ("SA", "SB", "SG")))
    mod = f"CoulN7.{name}"
    tail = f"\nend CoulN7\nend {sec}\n"
    body = lambda s: f"open Real\n\nsection {sec}\n" + OPENS + s + tail
    files = {}
    single = len(fdefs) + sum(len(v) for v in sdefs.values()) + len(tc)
    if not (split_mode or single > max_module):
        files["Data.lean"] = hdr(["ThomsonGen.Cert.NBlk"], f"`TCertN` data of {name}.") + body(
            fdefs + "\n" + sdefs["SA"] + "\n" + sdefs["SB"] + "\n" + sdefs["SG"] + "\n" + tc)
    else:
        for sn, fn in (("SA", "DataA"), ("SB", "DataB"), ("SG", "DataG")):
            files[f"{fn}.lean"] = hdr(["ThomsonGen.Cert.NBlk"], f"`TCertN` data of {name}: SOS blocks `{sn}`.") + body(sdefs[sn])
        files["Data.lean"] = hdr([f"{mod}.DataA", f"{mod}.DataB", f"{mod}.DataG"],
                                 f"`TCertN` data of {name}: kernel blocks and the certificate.") + body(fdefs + "\n" + tc)
    # checkMeta is checked row-wise per SOS block (ChkS<X><r>.lean + ChkMeta.lean): written by gen_capchk.py
    # from the Data modules below (a single `decide` over one 84x82 block exceeds ~10 GB in the kernel).
    for suf, fn, what in (("A", "chkA", "ChkA"), ("B", "chkB", "ChkB"), ("G", "chkG", "ChkG")):
        files[f"{what}.lean"] = hdr([f"{mod}.Data"], f"Kernel check `{fn}` of {name}.") + body(
            f"theorem {nm}_{suf} : {nm}.{fn} = true := by decide +kernel\n")
    for fn, txt in files.items():
        with open(os.path.join(outdir, fn), "w") as fh:
            fh.write(txt)
    import gen_capchk
    gen_capchk.main(name)
    return {fn: len(txt.encode()) for fn, txt in files.items()}


NBLK_RE = (r"def (\S+) : NBlk :=\s+⟨(\[(?:\[[-0-9, ]*\](?:, )?)*\]), (\d+), (\d+), (\d+), (\d+),\s+"
           + HEX + r",\s+" + HEX + r",\s+" + HEX + "⟩")


def parse_n(outdir, name):
    nm = "tc_" + name.lower()
    txt = ""
    for fn in sorted(os.listdir(outdir)):
        if fn.startswith("Data") and fn.endswith(".lean"):
            txt += open(os.path.join(outdir, fn), encoding="utf-8").read() + "\n"
    nbs = {}
    for mt in re.finditer(NBLK_RE, txt):
        N = [[int(v) for v in row.split(",") if v.strip()] for row in re.findall(r"\[([-0-9, ]*)\]", mt.group(2)[1:-1])]
        r, Bd, Bl, BD = map(int, mt.group(3, 4, 5, 6))
        nbs[mt.group(1)] = NBlkS(N, r, Bd, Bl, BD, *(int(mt.group(i), 16) for i in (7, 8, 9)))
    tbs = {}
    for mt in re.finditer(r"def (\S+) : TBlkN :=\s+⟨\[([0-9, ]*)\], \[([0-9(), ]*)\], (\S+), (\d+), 0x([0-9a-f]+)⟩", txt):
        g = [int(x) for x in mt.group(2).split(",") if x.strip()]
        z = [tuple(int(y) for y in t.split(",")) for t in re.findall(r"\(([0-9, ]+)\)", mt.group(3))]
        tbs[mt.group(1)] = TBlkNS(g, z, nbs[mt.group(4)], int(mt.group(5)), int(mt.group(6), 16))
    body = txt[txt.index(f"def {nm} : TCertN where"):]
    kw = {}
    for f in TCert.fields:
        mt = re.search(r"\n  " + re.escape(f) + r" := (.*)\n", body)
        v = mt.group(1).strip()
        if v.startswith("["):
            items = [x.strip() for x in v[1:-1].split(",") if x.strip()]
            kw[f] = ([nbs[x] for x in items] if f in ("FP", "FR") else
                     [tbs[x] for x in items] if f in ("SA", "SB", "SG") else [int(x) for x in items])
        else:
            kw[f] = int(v)
    return TCertNS(**kw), (len(nbs), len(tbs))


def compare_json_n(tcn, tc, J):
    """the expanded Lean data equals the JSON certificate exactly."""
    out = {}
    Lam = Fr(tc.Lam)
    out["cell"] = Fr(tc.an, tc.ad) == Fr(J["cell"][0]) and Fr(tc.bn, tc.bd) == Fr(J["cell"][1])
    out["H"] = all([Fr(x) / Lam for x in getattr(tc, "H" + X)] == [Fr(y) for y in J["H"][X]] for X in "ABC")
    out["psi"] = ([Fr(x) / Lam for x in tc.ψBa] == [Fr(y) for y in J["psi"]["Ba"]]
                  and [Fr(x) / Lam for x in tc.ψCb] == [Fr(y) for y in J["psi"]["Cb"]])
    out["consts"] = (Fr(tc.e) / Lam == Fr(J["e"]) and Fr(tc.cal) / Lam == Fr(J["ca"]) and Fr(tc.cbe) / Lam == Fr(J["cb"]))
    out["ef"] = str(Fr(tc.e) / Lam)

    def expandJ(b):
        N = [[Fr(x) for x in row] for row in b["N"]]
        R = [[Fr(x) for x in row] for row in b["red"]]
        m = len(N)
        if not R:
            return [[Fr(0)] * m for _ in range(m)]
        return congr(N, R)

    okF_ = True
    for X, key in (("P", "FP"), ("R", "FR")):
        okF_ &= len(getattr(tc, key)) == len(J["F"][X])          # no silent truncation
        for k, b in enumerate(J["F"][X]):
            if k >= len(getattr(tc, key)):
                okF_ = False
                break
            Fx = expandJ(b)
            bl = getattr(tc, key)[k]
            m = tc.m(k)
            okF_ &= len(Fx) == m and all(len(row) == m for row in Fx) and all(
                Fr(blk_ent(m, bl, a, cc)) / Lam == Fx[a][cc] for a in range(m) for cc in range(m))
    out["F"] = okF_
    factor = {"A": 5, "B": 4, "G": 30}
    okS = True
    for tag, sname, mname in (("A", "SA", "mA"), ("B", "SB", "mB"), ("G", "SG", "mG")):
        bn_, bd_ = (tc.bn, tc.bd) if tag == "A" else (1, 1)
        okS &= len(getattr(tcn, sname)) == len(J["SOS"][tag])     # equal block counts (zip would truncate)
        for s, blk in zip(getattr(tcn, sname), J["SOS"][tag]):
            g = {tuple(int(x) for x in k2.split(",")): Fr(v) for k2, v in blk["g"].items()}
            P = code_poly(tc.an, tc.ad, bn_, bd_, s.g)
            k0 = next(iter(g))
            scale = P[k0] / g[k0]
            okS &= (scale > 0 and set(P) == set(g) and all(P[k2] == scale * g[k2] for k2 in g)
                    and s.z == monos_upto(blk["d"]))
            f = factor[tag] * Lam * getattr(tc, mname) / scale
            Bx = expandJ(blk)
            E = s.E()
            n = len(s.z)
            okS &= (len(E) == n and all(len(row) == n for row in E) and len(Bx) == n
                    and all(len(row) == n for row in Bx))
            okS &= all(Fr(E[a][cc]) == f * Bx[a][cc] for a in range(len(E)) for cc in range(len(E)))
    out["SOS"] = okS
    return out


def congr(N, R):
    m, r = len(N), len(R)
    NR = [[sum(N[i][k] * R[k][j] for k in range(r) if N[i][k]) for j in range(r)] for i in range(m)]
    return [[sum(NR[i][k] * N[j][k] for k in range(r) if N[j][k]) for j in range(m)] for i in range(m)]


def run_check_n(outdir, name, J=None, poly=True, dumpE=None):
    tcn, nb = parse_n(outdir, name)
    log(f"parsed {outdir}: {nb[0]} NBlk, {nb[1]} TBlkN; dd={tcn.dd} Lam bits={tcn.Lam.bit_length()} "
        f"mA={tcn.mA} mB={tcn.mB} mG={tcn.mG}")
    res = {}
    info = {}
    res["checkMeta"] = (tcn.checkMeta(info), info)
    log(f"TCertN.checkMeta = {res['checkMeta'][0]}  {info}")
    tc = tcn.toTCert()
    for nmk, mkFx, S in (("chkA", tc.FA, tc.SA), ("chkB", tc.FB, tc.SB), ("chkG", tc.FG, tc.SG)):
        KEVSTAT[0] = 0
        info = {}
        t1 = time.time()
        Fx = mkFx()
        bn_, bd_ = (tc.bn, tc.bd) if nmk == "chkA" else (1, 1)
        ok = hybChk(Fx, tc.an, tc.ad, bn_, bd_, S, info)
        info["max_int_bits"] = KEVSTAT[0]
        info["time_s"] = round(time.time() - t1, 1)
        if poly:
            lhs = dict(expand(Fx))
            for s in S:
                b = s.B()
                zz = {}
                r = len(s.z)
                for a in range(r):
                    for cc in range(r):
                        v = blk_ent(r, b, a, cc)
                        if v:
                            k3 = tuple(x + y for x, y in zip(s.z[a], s.z[cc]))
                            zz[k3] = zz.get(k3, 0) + v
                lhs = P_add(lhs, P_mul(expand(gT(tc.an, tc.ad, bn_, bd_, s.g)), zz), -1)
            info["poly_identity_exact"] = not lhs
        res[nmk] = (ok, info)
        log(f"TCertN.{nmk} = {ok}  {info}")
    if dumpE:
        out = {"Lam": str(tcn.Lam), "note": "expanded remainders E = N ent(B') N^T (integers; real block = E/(scale))",
               "FP": [b.D for b in tc.FP], "FR": [b.D for b in tc.FR],
               "SA": [s.E() for s in tcn.SA], "SB": [s.E() for s in tcn.SB], "SG": [s.E() for s in tcn.SG],
               "BDe": {sn: [s.BDe for s in getattr(tcn, sn)] for sn in ("SA", "SB", "SG")},
               "BD_F": {key: [width([x for row in b.D for x in row]) for b in getattr(tc, key)] for key in ("FP", "FR")}}
        with open(dumpE, "w") as fh:
            json.dump(out, fh, default=str)
        log(f"expanded remainders written to {dumpE} ({os.path.getsize(dumpE) // 1024} KiB)")
    if J is not None:
        res["json_equal"] = compare_json_n(tcn, tc, J)
        log(f"exact equality with JSON: {res['json_equal']}")
    allok = all(v[0] for k, v in res.items() if k != "json_equal") and (
        J is None or all(v for k, v in res["json_equal"].items() if k != "ef"))
    if poly:     # the independent polynomial identity is part of the verdict
        allok = allok and all(res[n][1].get("poly_identity_exact") is True for n in ("chkA", "chkB", "chkG"))
    return allok, res, tcn


# ====================================================================== main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json")
    ap.add_argument("name")
    ap.add_argument("--check-only", action="store_true")
    ap.add_argument("--no-check", action="store_true")
    ap.add_argument("--split", action="store_true")
    ap.add_argument("--max-module", type=int, default=1_000_000)
    ap.add_argument("--no-poly", action="store_true")
    ap.add_argument("--tcertn", action="store_true", help="facially reduced cap certificate -> TCertN (NBlk.lean)")
    ap.add_argument("--dump-E", default=None, help="--tcertn: write the expanded remainders E to this JSON file")
    a = ap.parse_args()
    outdir = os.path.join(LEANROOT, "CoulN7", a.name)
    if a.tcertn:
        J = json.load(open(a.json))
        if not a.check_only:
            data, rep = build_n(J)
            for k, v in rep["codes"].items():
                log(f"  multiplier {k}: g = {v[0]}  ->  codes {v[1]}  (gT = {v[2]} * g)")
            for key in ("FP", "FR"):
                for k, (Np, d, Lc, Dl) in enumerate(data[key]):
                    if d:
                        Bd, Bl, BD, bits_ = packed_bits(len(d), d, Lc, Dl)
                        log(f"  {key}{k}: m={len(Np)} r={len(d)} Bd={Bd} Bl={Bl} BD={BD}")
            for sn in ("SA", "SB", "SG"):
                for r, (codes, z, (Np, d, Lc, Dl), BDe, _BDpk) in enumerate(data[sn]):
                    Bd, Bl, BD, bits_ = packed_bits(len(d), d, Lc, Dl)
                    log(f"  {sn}{r}: codes={codes} m={len(z)} r={len(d)} Bd={Bd} Bl={Bl} BD={BD} BDe={BDe} "
                        f"({bits_ // 4 // 1024} KiB hex)")
            sizes = emit_n(data, a.name, a.json, outdir, a.split, a.max_module)
            log("wrote", outdir, json.dumps(sizes))
        if not a.no_check:
            allok, res, tcn = run_check_n(outdir, a.name, J, poly=not a.no_poly, dumpE=a.dump_E)
            log("EMIT_TCERTN", a.name, "ALL_OK" if allok else "FAILED")
            sys.exit(0 if allok else 1)
        return
    J = load_json(a.json)
    if not a.check_only:
        data, rep = build(J)
        log("build:", json.dumps({k: (v if k != "codes" else None) for k, v in rep.items()}, default=str))
        for k, v in rep["codes"].items():
            log(f"  multiplier {k}: g = {v[0]}  ->  codes {v[1]}  (gT = {v[2]} * g)")
        for key in ("FP", "FR"):
            for k, (Mi, d, Lc, Dl) in enumerate(data[key]):
                Bd, Bl, BD, bits = packed_bits(len(d), d, Lc, Dl)
                log(f"  {key}{k}: r={len(d)} Bd={Bd} Bl={Bl} BD={BD}")
        for sn in ("SA", "SB", "SG"):
            for r, (codes, z, d, Lc, Dl) in enumerate(data[sn]):
                Bd, Bl, BD, bits = packed_bits(len(d), d, Lc, Dl)
                log(f"  {sn}{r}: codes={codes} r={len(z)} Bd={Bd} Bl={Bl} BD={BD} ({bits // 4 // 1024} KiB hex)")
        sizes = emit(data, a.name, a.json, outdir, a.split, a.max_module)
        log("wrote", outdir, json.dumps(sizes))
    if not a.no_check:
        allok, res, tc = run_check(outdir, a.name, J, poly=not a.no_poly)
        log("EMIT_TCERT", a.name, "ALL_OK" if allok else "FAILED")
        sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
