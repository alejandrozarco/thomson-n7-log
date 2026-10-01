"""cert3_util.py -- exact integer mirror of upstream's Case 1 `Cert3` machinery (Python 3.9, no deps).

Mirrors, definition by definition, the Lean code of the ThomsonGen split of huwngtran/thomson-n7-lean
(`ThomsonGen/Kron.lean`, `Cert1.lean`, `Cert3.lean`, `CertF.lean` (`unpackI`/`unpackM`/`mkBlk`),
`Case1Stat.lean` (`c1Stat`, `c1Stat_idE`)).  Every Lean `def` used by a `decide +kernel` of the
Case 1 check has a Python twin here with the SAME tree shape (so that the l1-norm of the uncollected
coefficients, the structural degrees and the Kronecker value agree bit for bit):

  Lean                              Python
  Kron.Ex.{c,mon,add,mul}           c(), mon(), add(), mul()         (tuples, tags C/MON/ADD/MUL)
  Ex.{neg,sub,smul,sq,sumE,sumRange} neg, sub, smul, sq, sumE, sumRange
  Cert.smulNZ / sbst                smulNZ / sbst (lazy node SB, applied at the monomials)
  Cert.q3E fpE fkE sixE             q3E fpE fkE sixE
  Case1.c1FtotK                     c1FtotK
  Cert.codeE gE zt zmon zzmon sqfE  codeE gE zt zmon zzmon sqfE
  Cert.perm3 sblkE hE               perm3 sblkE hE
  Blk.{dq,lq,del,ent,ok}            Blk.{dq,lq,dl,ent,ok}
  Case1.c1Stat / c1Add / c1Mul ...  stat_l (w-free part), kev (Kronecker value), c1Add, c1Mul, ...
  Cert.chk                          chk_params (w = Nat.log2 l1 + 1, D = max deg + 1)
  Cert.unpackI / unpackM / mkBlk    unpackI / unpackM / mkBlk ; packI / packM (inverse)
"""
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(100000)

# ------------------------------------------------------------------ Kron.Ex
C, MON, ADD, MUL, SB = 0, 1, 2, 3, 4


def c(n):
    return (C, int(n))


def mon(a, b, d):
    return (MON, a, b, d)


def add(p, q):
    return (ADD, p, q)


def mul(p, q):
    return (MUL, p, q)


U = mon(1, 0, 0)
V = mon(0, 1, 0)
T = mon(0, 0, 1)


def neg(e):                 # Ex.neg e = mul (c (-1)) e
    return mul(c(-1), e)


def sub(e, f):              # Ex.sub e f = add e (neg f)
    return add(e, neg(f))


def smul(a, e):             # Ex.smul a e = mul (c a) e
    return mul(c(a), e)


def sq(e):                  # Ex.sq e = mul e e
    return mul(e, e)


def sumE(l):                # l.foldr add (c 0)
    r = c(0)
    for x in reversed(l):
        r = add(x, r)
    return r


def sumRange(r, f):         # sumE ((List.range r).map f)
    return sumE([f(i) for i in range(r)])


def smulNZ(a, e):           # if a = 0 then c 0 else smul a e
    return c(0) if a == 0 else smul(a, e)


def sbst(i, j, k, e):       # Cert.sbst, applied lazily (evaluated monomial by monomial)
    assert e[0] != SB, "nested sbst never occurs in Cert3"
    return (SB, (i, j, k), e)


def sbst_exps(ijk, a, b, d):
    i, j, k = ijk
    return ((a if i == 0 else 0) + (b if j == 0 else 0) + (d if k == 0 else 0),
            (a if i == 1 else 0) + (b if j == 1 else 0) + (d if k == 1 else 0),
            (a if i == 2 else 0) + (b if j == 2 else 0) + (d if k == 2 else 0))


# ------------------------------------------------------------------ Cert1 / Cert3 builders
_q3 = {}


def q3E(k):
    if k in _q3:
        return _q3[k]
    if k == 0:
        r = c(1)
    elif k == 1:
        r = sub(T, mul(U, V))
    else:
        r = sub(mul(smul(2, sub(T, mul(U, V))), q3E(k - 1)),
                mul(mul(sub(c(1), sq(U)), sub(c(1), sq(V))), q3E(k - 2)))
    _q3[k] = r
    return r


def getD(xs, i, dflt):
    return xs[i] if i < len(xs) else dflt


class Blk:
    """`structure Blk where d : List ℤ; l : List (List ℤ); Δ : List (List ℤ)`."""

    def __init__(self, d, l, D):
        self.d, self.l, self.D = list(d), [list(x) for x in l], [list(x) for x in D]

    def dq(self, q):
        return getD(self.d, q, 0)

    def lq(self, q, a):
        return getD(getD(self.l, q, []), a, 0)

    def dl(self, a, cc):
        return getD(getD(self.D, a, []), cc, 0)

    def ent(self, r, a, cc):
        return sum(self.dq(q) * self.lq(q, a) * self.lq(q, cc) for q in range(r)) + self.dl(a, cc)

    def ok(self, r):
        """Blk.ok: pivots >= 0, Δ symmetric, Δ diagonally dominant (all on range r)."""
        for i in range(r):
            if not (0 <= self.dq(i)):
                return False
            if not all(self.dl(i, j) == self.dl(j, i) for j in range(r)):
                return False
            if not (sum((0 if i == j else abs(self.dl(i, j))) for j in range(r)) <= self.dl(i, i)):
                return False
        return True

    def dd_slack(self, r):
        return min(self.dl(i, i) - sum(abs(self.dl(i, j)) for j in range(r) if j != i) for i in range(r))


def fpE(r, b):
    return add(sumRange(r, lambda q: smulNZ(b.dq(q),
                                           mul(sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(a, 0, 0))),
                                               sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(0, a, 0)))))),
               sumRange(r, lambda a: sumRange(r, lambda cc: smulNZ(b.dl(a, cc), mon(a, cc, 0)))))


def fkE(r, b, k):
    return mul(fpE(r, b), q3E(k))


def sixE(i, j, k, e):
    return add(add(add(add(add(sbst(i, j, k, e), sbst(i, k, j, e)), sbst(j, i, k, e)), sbst(j, k, i, e)),
                   sbst(k, i, j, e)), sbst(k, j, i, e))


def c1FtotK(n, e):
    return add(add(smul((n - 1) * (n - 2), sixE(0, 1, 2, e)),
                   smul(n - 1, add(add(sixE(0, 0, 3, e), sixE(1, 1, 3, e)), sixE(2, 2, 3, e)))),
               sixE(3, 3, 3, e))


def codeE(an, ad, code):
    if code == 0:
        return sub(c(1), sq(U))
    if code == 1:
        return sub(c(1), sq(V))
    if code == 2:
        return sub(c(1), sq(T))
    if code == 3:
        return sub(add(c(1), smul(2, mul(U, mul(V, T)))), add(sq(U), add(sq(V), sq(T))))
    if code == 4:
        return sub(c(1), U)
    if code == 5:
        return add(c(1), U)
    if code == 6:
        return sub(c(1), V)
    if code == 7:
        return add(c(1), V)
    if code == 8:
        return sub(c(1), T)
    if code == 9:
        return add(c(1), T)
    if code == 10:
        return sub(smul(ad, U), c(an))
    if code == 11:
        return sub(smul(ad, V), c(an))
    if code == 12:
        return sub(smul(ad, T), c(an))
    return c(1)


def gE(an, ad, g):
    r = c(1)
    for code in reversed(g):
        r = mul(codeE(an, ad, code), r)
    return r


def zt(zs, a):
    return getD(zs, a, (0, 0, 0))


def zmon(zs, a):
    t = zt(zs, a)
    return mon(t[0], t[1], t[2])


def zzmon(zs, a, cc):
    s, t = zt(zs, a), zt(zs, cc)
    return mon(s[0] + t[0], s[1] + t[1], s[2] + t[2])


def sqfE(b, zs):
    L = len(zs)
    return add(sumRange(L, lambda q: smulNZ(b.dq(q), sq(sumRange(L, lambda a: smulNZ(b.lq(q, a), zmon(zs, a)))))),
               sumRange(L, lambda a: sumRange(L, lambda cc: smulNZ(b.dl(a, cc), zzmon(zs, a, cc)))))


def perm3(s):
    return {0: (0, 1, 2), 1: (0, 2, 1), 2: (1, 0, 2), 3: (1, 2, 0), 4: (2, 0, 1)}.get(s, (2, 1, 0))


class SBlk:
    def __init__(self, g, sigma, z, B):
        self.g, self.sigma, self.z, self.B = list(g), sigma, [tuple(x) for x in z], B


def sblkE(an, ad, s):
    p = perm3(s.sigma)
    return sbst(p[0], p[1], p[2], mul(gE(an, ad, s.g), sqfE(s.B, s.z)))


def hE(h):
    return sumRange(len(h), lambda j: smulNZ(getD(h, j, 0), add(add(mon(j, 0, 0), mon(0, j, 0)), mon(0, 0, j))))


class Cert3:
    def __init__(self, n, Lam, an, ad, h, eps, F, S):
        self.n, self.Lam, self.an, self.ad, self.h, self.eps, self.F, self.S = n, Lam, an, ad, list(h), eps, F, S

    def blk(self, k):
        return getD(self.F, k, Blk([], [], []))

    def m(self, k):
        return len(self.blk(k).D)

    @property
    def K(self):
        return len(self.F)


def choose2(n):
    return n * (n - 1) // 2


# ------------------------------------------------------------------ c1Stat (Case1Stat.lean)
def c1Add(s, t):
    return (s[0] + t[0], max(s[1], t[1]), max(s[2], t[2]), max(s[3], t[3]), s[4] + t[4])


def c1Mul(s, t):
    return (s[0] * t[0], s[1] + t[1], s[2] + t[2], s[3] + t[3], s[4] * t[4])


def c1C(a):
    return (abs(a), 0, 0, 0, a)


def c1Sub(s, t):
    return c1Add(s, c1Mul(c1C(-1), t))


def c1Smul(a, s):
    return c1Mul(c1C(a), s)


def c1Sum(l):
    r = c1C(0)
    for x in reversed(l):
        r = c1Add(x, r)
    return r


def stat_l(e):
    """(l1, dx, dy, dz) of an Ex tree -- the w-independent part of c1Stat (Ex.l1, Ex.dx/dy/dz)."""
    memo = {}

    def go(e, ijk):
        key = (id(e), ijk)
        if key in memo:
            return memo[key][0]
        tg = e[0]
        if tg == C:
            r = (abs(e[1]), 0, 0, 0)
        elif tg == MON:
            a, b, d = e[1], e[2], e[3]
            if ijk is not None:
                a, b, d = sbst_exps(ijk, a, b, d)
            r = (1, a, b, d)
        elif tg == SB:
            r = go(e[2], e[1])
        else:
            p, q = go(e[1], ijk), go(e[2], ijk)
            if tg == ADD:
                r = (p[0] + q[0], max(p[1], q[1]), max(p[2], q[2]), max(p[3], q[3]))
            else:
                r = (p[0] * q[0], p[1] + q[1], p[2] + q[2], p[3] + q[3])
        memo[key] = (r, e)          # keep e alive so that id(e) is never reused while memo lives
        return r
    return go(e, None)


def kev(e, w, D):
    """Ex.kev w D: the integer value at u = 2^w, v = 2^(wD), t = 2^(wD^2)."""
    memo = {}
    pw = {}

    def go(e, ijk):
        key = (id(e), ijk)
        if key in memo:
            return memo[key][0]
        tg = e[0]
        if tg == C:
            r = e[1]
        elif tg == MON:
            a, b, d = e[1], e[2], e[3]
            if ijk is not None:
                a, b, d = sbst_exps(ijk, a, b, d)
            code = a + D * b + D * D * d
            r = pw.get(code)
            if r is None:
                r = pw[code] = 1 << (w * code)
        elif tg == SB:
            r = go(e[2], e[1])
        else:
            p, q = go(e[1], ijk), go(e[2], ijk)
            r = p + q if tg == ADD else p * q
        memo[key] = (r, e)
        return r
    return go(e, None)


def c1Stat(e, w, D):
    s = stat_l(e)
    return (s[0], s[1], s[2], s[3], kev(e, w, D))


def nat_log2(n):            # Nat.log2 (Nat.log2 0 = 0)
    return n.bit_length() - 1 if n > 0 else 0


def pieces(cf):
    """The 1 + K + |S| pieces of `c1Stat_idE`, in the order of the chunk modules, as (name, Lean lhs, Ex)."""
    out = [("H", None, hE(cf.h))]
    for k in range(cf.K):
        out.append((f"F{k}", k, c1FtotK(cf.n, fkE(cf.m(k), cf.blk(k), k))))
    for i, s in enumerate(cf.S):
        out.append((f"S{i}", i, sblkE(cf.an, cf.ad, s)))
    return out


def compose_idE(cf, stH, stF, stS):
    """c1Stat_idE: the statistics of cf.idE from those of its pieces (Case1Stat.lean)."""
    n, C2 = cf.n, choose2(cf.n)
    return c1Sub(c1Sub(c1Sub(c1Smul(2 * (n - 1) * C2, stH), c1C(6 * (n - 1) * cf.eps)),
                       c1Smul(C2, c1Sum(stF))),
                 c1Smul(6 * (n - 1) * C2, c1Sum(stS)))


def chk_params(l1, dx, dy, dz):
    """Cert.chk: w = Nat.log2 l1 + 1, D = max dx (max dy dz) + 1."""
    return nat_log2(l1) + 1, max(dx, max(dy, dz)) + 1


# ------------------------------------------------------------------ CertF packing
def unpackI(B, n, x):
    out = []
    for _ in range(n):
        out.append((x % (1 << B)) - (1 << (B - 1)))     # (B - 1) is Nat subtraction; B >= 1 enforced by caller
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


def field_width(vals, step=4):
    """Smallest multiple of `step` B >= 4 with every v in [-2^(B-1), 2^(B-1))."""
    B = step
    while not all(-(1 << (B - 1)) <= v < (1 << (B - 1)) for v in vals):
        B += step
    return B


def packI(B, vals):
    x = 0
    for i, v in enumerate(vals):
        f = v + (1 << (B - 1))
        assert 0 <= f < (1 << B)
        x |= f << (B * i)
    return x


def packM(B, rows):
    flat = [v for row in rows for v in row]
    return packI(B, flat)


# ------------------------------------------------------------------ PSD block -> LDL^T + DD remainder
def _isqrt_floor_log2(P):
    return P.bit_length() - 1


def pack_psd(M, theta=Fr(1, 2)):
    """Exact integer data (d, l, Δ) with sum_q d_q l_q l_q^T + Δ == M EXACTLY (M symmetric integer PD),
    l_q[a] = 0 for a < q, l_q[q] = 2^p_q, d_q >= 0, Δ symmetric; returns (Blk, info) -- the DD property of Δ
    (the only non-trivial condition of Blk.ok) is reported, not assumed.

    Scheme: ε = θ·λ_min(M) (float estimate, integer), A = M - εI, rounded LDL^T of A column by column in exact
    integer arithmetic (l_q = round(2^p A[:,q]/P), d_q = floor(P/4^p)), the Schur complement updated EXACTLY,
    and Δ = (final A) + εI.  Row q of Δ has off-diagonal errors ≲ |A_qa| 4^p/P + P/2^(p+1); p_q balances them."""
    import numpy as np
    r = len(M)
    for i in range(r):
        for j in range(r):
            assert M[i][j] == M[j][i]
    sc = max(abs(x) for row in M for x in row)
    e2 = sc.bit_length()
    Af = np.array([[float(Fr(x, 1 << e2)) for x in row] for row in M])
    lmin = float(np.linalg.eigvalsh(Af)[0])
    if lmin <= 0:
        return None, {"why": f"float lambda_min {lmin:.3e} <= 0"}
    eps = int(Fr(lmin) * theta * (1 << e2))
    A = [list(row) for row in M]
    for i in range(r):
        A[i][i] -= eps
    d, L = [], []
    for q in range(r):
        P = A[q][q]
        if P <= 0:
            return None, {"why": f"pivot {q} <= 0 after shift"}
        S = sum(abs(A[a][q]) for a in range(q + 1, r))
        lp = P.bit_length() - 1
        if S > 0:
            pstar = (2 * lp - (S.bit_length() - 1) + (r.bit_length() - 1) - 1) / 3.0
        else:
            pstar = lp / 2.0
        p = max(0, min(int(round(pstar)), lp // 2))
        lq = [0] * r
        lq[q] = 1 << p
        for a in range(q + 1, r):
            num = A[a][q] << p
            lq[a] = (2 * num + P) // (2 * P)        # round half up of num / P
        dq = P >> (2 * p)
        for a in range(q, r):
            if lq[a] == 0:
                continue
            fa = dq * lq[a]
            Aa = A[a]
            for cc in range(q, r):
                if lq[cc]:
                    Aa[cc] -= fa * lq[cc]
        d.append(dq)
        L.append(lq)
    for i in range(r):
        A[i][i] += eps
    b = Blk(d, L, A)
    for a in range(r):
        for cc in range(r):
            assert b.ent(r, a, cc) == M[a][cc], "packing identity broken"
    info = {"eps": eps, "lmin_rel": lmin, "ok": b.ok(r), "dd_slack": b.dd_slack(r)}
    return b, info


# ------------------------------------------------------------------ Lean literal helpers
def lint(v):
    return f"({v} : Int)"


def lnat(v):
    return f"({v} : Nat)"


def lint_list(xs):
    return "[" + ", ".join(lint(x) for x in xs) + "]"


def lz_list(zs):
    return "[" + ", ".join(f"({lnat(a)}, {lnat(b)}, {lnat(d)})" for (a, b, d) in zs) + "]"


def stat_lit(st):
    kv = st[4]
    kvs = f"({kv} : Int)" if kv >= 0 else f"((-{-kv}) : Int)"
    return f"({st[0]}, {st[1]}, {st[2]}, {st[3]}, {kvs})"
