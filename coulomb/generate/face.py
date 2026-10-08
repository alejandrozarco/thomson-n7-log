"""Exact (rational) facial reduction of the degree-12 cap SDP, including the SOFT (pucker) conditions.

Sharpness of the cap bound at P forces every nonnegative term of
    E(x) - e = sum (phi - H_cls)(t_ij) + sum_T lambda_T(x) + sum_roots (rho^T F rho + iota^T F iota)
to vanish at P, and (s = 0 has the soft pucker pair) to vanish to 2nd order along the pucker
x(a,b) (ring heights z_k = a cos(4 pi k/5) + b sin(4 pi k/5)).  For a PSD Gram block B with
    M(a,b) = sum_{P-triples p} g(p(a,b)) z(p(a,b)) z(p(a,b))^T
this means <B, M(0)> = 0 and <B, Lap M(0)> = 0, i.e. B = N B' N^T with
    N0 = null(M(0)),  N = N0 null(N0^T Lap M(0) N0).
Same for the kernel blocks F with M = sum_{roots of the type} sum_{j,l} Y_k(G_ij, G_il, G_jl).
M(0) and Lap M(0) are rational (the triple sets are Galois-stable under sqrt5 -> -sqrt5); we compute them
in 300-bit ball arithmetic along exact 2-jets of the Gram matrix and recognise the rationals (checked to
< 2^-200).  The resulting N is returned in echelon form (N[free,:] = I), so B' = B[free, free].
Soundness of the final certificate never depends on this file (the checker re-verifies everything);
the face only has to be right for the rounding to succeed.

output: face_D12.json  {block name: {"n":n, "free":[...], "N": [[p/q,...],...]}}
"""
import json, math, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, arb_mat, fmpq, fmpq_mat
import spec
import os
VALUE_ONLY = os.environ.get("VALUE_ONLY", "1") == "1"   # s = 1: no soft (pucker) conditions

flint.ctx.prec = 320
PI = arb.pi()


# ---------------------------------------------------------------- 2-jets in (a,b): (f, fa, fb, faa, fab, fbb)
class J:
    __slots__ = ("c",)

    def __init__(self, c):
        self.c = c

    @staticmethod
    def const(x):
        z = arb(0); return J([arb(x), z, z, z, z, z])

    def __add__(s, o):
        o = o if isinstance(o, J) else J.const(o)
        return J([x + y for x, y in zip(s.c, o.c)])
    __radd__ = __add__

    def __neg__(s):
        return J([-x for x in s.c])

    def __sub__(s, o):
        return s + (-(o if isinstance(o, J) else J.const(o)))

    def __rsub__(s, o):
        return (-s) + o

    def __mul__(s, o):
        if not isinstance(o, J):
            return J([x * o for x in s.c])
        f, fa, fb, faa, fab, fbb = s.c; g, ga, gb, gaa, gab, gbb = o.c
        return J([f * g, fa * g + f * ga, fb * g + f * gb,
                  faa * g + 2 * fa * ga + f * gaa, fab * g + fa * gb + fb * ga + f * gab,
                  fbb * g + 2 * fb * gb + f * gbb])
    __rmul__ = __mul__

    def unary(s, f0, f1, f2):
        """phi(s) given phi, phi', phi'' at s.c[0]."""
        f, fa, fb, faa, fab, fbb = s.c
        return J([f0, f1 * fa, f1 * fb, f2 * fa * fa + f1 * faa, f2 * fa * fb + f1 * fab, f2 * fb * fb + f1 * fbb])

    def lap(s):
        return s.c[3] + s.c[5]


def config_jets():
    """7 points: 0,1 poles (0,0,+-1), 2..6 ring; ring heights z_k = a cos(4 pi k/5) + b sin(4 pi k/5)."""
    X = [[J.const(0), J.const(0), J.const(1)], [J.const(0), J.const(0), J.const(-1)]]
    for k in range(5):
        th = 2 * PI * k / 5; ph = 4 * PI * k / 5
        z = J([arb(0), ph.cos(), ph.sin(), arb(0), arb(0), arb(0)])
        n2 = z * z + 1                                    # 1 + z^2, value 1
        r = n2.unary(arb(1), arb(-0.5), arb(0.75))        # (1+z^2)^(-1/2) at 1
        X.append([r * th.cos(), r * th.sin(), r * z])
    G = [[None] * 7 for _ in range(7)]
    for i in range(7):
        for j in range(7):
            G[i][j] = X[i][0] * X[j][0] + X[i][1] * X[j][1] + X[i][2] * X[j][2]
    return G


def triples(G, kind):
    R = range(2, 7)
    if kind == "A":
        idx = [(0, 1, r) for r in R] + [(1, 0, r) for r in R]
    elif kind == "B":
        idx = [(p, r, q) for p in (0, 1) for r in R for q in R if r != q]
    else:
        idx = [(i, j, l) for i in R for j in R for l in R if len({i, j, l}) == 3]
    return [(G[i][j], G[i][l], G[j][l]) for (i, j, l) in idx]


def jpow_table(x, d):
    P = [J.const(1)]
    for _ in range(d):
        P.append(P[-1] * x)
    return P


def poly_jet(p, pw):
    """exact dict poly evaluated on jets (power tables pw = (U^k, V^k, T^k))."""
    out = J.const(0)
    for (a, b, c), co in p.items():
        out = out + pw[0][a] * pw[1][b] * pw[2][c] * arb(fmpq(co.numerator, co.denominator))
    return out


def amat(rows):
    return arb_mat(rows)


def recognise(M, name):
    """arb_mat -> fmpq_mat, rational recognition with a hard accuracy check."""
    n, m = M.nrows(), M.ncols()
    out = []
    worst = 0
    for i in range(n):
        for j in range(m):
            x = M[i, j]
            mid = x.mid()
            man, ex = mid.man_exp()
            fx = Fr(int(man)) * (Fr(2) ** int(ex))
            q = fx.limit_denominator(10 ** 30)
            err = abs(fx - q)
            worst = max(worst, float(err) if err else 0.0)
            if err > Fr(1, 2 ** 200) or float(x.rad()) > 1e-60:
                raise ValueError(f"{name}[{i},{j}] not recognised: {float(fx)} err {float(err)} rad {x.rad()}")
            out.append(fmpq(q.numerator, q.denominator))
    return fmpq_mat(n, m, out)


def nullspace_q(M):
    """basis (columns) of the rational null space of fmpq_mat M (n x n)."""
    R, rank = M.rref()
    n = M.ncols()
    piv = []
    r = 0
    for c in range(n):
        if r < rank and R[r, c] != 0:
            piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    cols = []
    for f in free:
        v = [fmpq(0)] * n; v[f] = fmpq(1)
        for i, pc in enumerate(piv):
            v[pc] = -R[i, f]
        cols.append(v)
    if not cols:
        return fmpq_mat(n, 0)
    return fmpq_mat(n, len(cols), [cols[j][i] for i in range(n) for j in range(len(cols))])


def echelon(N):
    """same column space, N[free,:] = I, free coordinates preferring the LAST coordinates
    (high-degree monomials) so that the dependent (low-degree) ones are expressed with O(1) coefficients."""
    n, k = N.nrows(), N.ncols()
    if k == 0:
        return [], fmpq_mat(n, 0)
    Nt = N.transpose()
    rev = fmpq_mat(k, n, [Nt[i, n - 1 - j] for i in range(k) for j in range(n)])
    R, rank = rev.rref()
    assert rank == k
    free_rev = []
    r = 0
    for c in range(n):
        if r < rank and R[r, c] != 0:
            free_rev.append(c); r += 1
    free = [n - 1 - c for c in free_rev]
    E = fmpq_mat(n, k, [R[j, n - 1 - i] for i in range(n) for j in range(k)])
    for j, f in enumerate(free):
        for jj in range(k):
            assert E[f, jj] == (1 if jj == j else 0)
    return free, E


def reduce_block(M0, M2, n, name):
    N0 = nullspace_q(M0)
    if N0.ncols() == 0 or VALUE_ONLY:
        return N0
    K = N0.transpose() * M2 * N0
    N1 = nullspace_q(K)
    return N0 * N1


def sos_faces(G):
    blocks = spec.multipliers()
    out = {}
    for kind, bl in blocks.items():
        tr = triples(G, kind)
        pws = []
        for (u, v, t) in tr:
            pws.append((jpow_table(u, 13), jpow_table(v, 13), jpow_table(t, 13)))
        for r, (gname, g, d) in enumerate(bl):
            Z = spec.monos_upto(d); n = len(Z)
            # rows: per triple the jet components of g and z
            Z0, Za, Zb, ZL = [], [], [], []
            g0, ga, gb, gL = [], [], [], []
            for pw in pws:
                gj = poly_jet(g, pw)
                zj = [pw[0][a] * pw[1][b] * pw[2][c] for (a, b, c) in Z]
                Z0.append([z.c[0] for z in zj]); Za.append([z.c[1] for z in zj]); Zb.append([z.c[2] for z in zj])
                ZL.append([z.lap() for z in zj])
                g0.append(gj.c[0]); ga.append(gj.c[1]); gb.append(gj.c[2]); gL.append(gj.lap())
            m = len(pws)
            A0, Aa, Ab, AL = amat(Z0), amat(Za), amat(Zb), amat(ZL)
            dg = lambda w: arb_mat(m, m, [w[i] if i == j else arb(0) for i in range(m) for j in range(m)])
            D0, Da, Db, DL = dg(g0), dg(ga), dg(gb), dg(gL)
            A0t = A0.transpose()
            M0 = A0t * D0 * A0
            X = Aa.transpose() * Da * A0 + Ab.transpose() * Db * A0
            Y = AL.transpose() * D0 * A0
            M2 = A0t * DL * A0 + 2 * (X + X.transpose()) + (Y + Y.transpose()) \
                + 2 * (Aa.transpose() * D0 * Aa + Ab.transpose() * D0 * Ab)
            # sanity: first-order term must vanish (terms are >= 0 along the curve), g >= 0 at P
            assert all(float(x.mid()) > -1e-30 for x in g0), (kind, gname)
            M0q = recognise(M0, f"{kind}{r}M0"); M2q = recognise(M2, f"{kind}{r}M2")
            N = reduce_block(M0q, M2q, n, f"{kind}{r}")
            out[f"{kind}_B{r}"] = (n, N)
            print(f"  SOS {kind} block {r} ({gname}, n={n}): kept {N.ncols()}", flush=True)
    return out


def Q_jets(u, v, t, kmax):
    Q = [J.const(1), t - u * v]
    W = (1 - u * u) * (1 - v * v)
    while len(Q) <= kmax:
        Q.append(2 * (t - u * v) * Q[-1] - W * Q[-2])
    return Q


def F_faces(G):
    roots = {"P": [0, 1], "R": [2, 3, 4, 5, 6]}
    out = {}
    kmax = len(spec.SIZES) - 1
    for X, rs in roots.items():
        acc = {k: [[J.const(0) for _ in range(m)] for _ in range(m)] for k, m in enumerate(spec.SIZES)}
        for i in rs:
            for j in range(7):
                for l in range(7):
                    u, v, t = G[i][j], G[i][l], G[j][l]
                    Q = Q_jets(u, v, t, kmax)
                    up = jpow_table(u, 7); vp = jpow_table(v, 7)
                    for k, m in enumerate(spec.SIZES):
                        for a in range(m):
                            for b in range(m):
                                acc[k][a][b] = acc[k][a][b] + up[a] * vp[b] * Q[k]
        for k, m in enumerate(spec.SIZES):
            M0 = arb_mat([[acc[k][a][b].c[0] for b in range(m)] for a in range(m)])
            M2 = arb_mat([[acc[k][a][b].lap() for b in range(m)] for a in range(m)])
            M0q = recognise(M0, f"F{X}{k}M0"); M2q = recognise(M2, f"F{X}{k}M2")
            N = reduce_block(M0q, M2q, m, f"F{X}{k}")
            out[f"F{X}{k}"] = (m, N)
            print(f"  F{X}{k} (m={m}): kept {N.ncols()}", flush=True)
    return out


if __name__ == "__main__":
    t0 = time.time()
    G = config_jets()
    # sanity: soft mode really soft? (energy Laplacian ~ 0 is checked in local/, here just Gram values)
    faces = {}
    faces.update(F_faces(G))
    faces.update(sos_faces(G))
    js = {}
    for name, (n, N) in faces.items():
        free, E = echelon(N)
        mx = max([abs(Fr(int(E[i, j].p), int(E[i, j].q))) for i in range(n) for j in range(E.ncols())] or [0])
        js[name] = {"n": n, "free": free,
                    "N": [[str(E[i, j]) for j in range(E.ncols())] for i in range(n)]}
        print(f"{name}: n={n} kept={len(free)} max|N|={float(mx):.3g}")
    with open("face_D12_val.json" if VALUE_ONLY else "face_D12.json", "w") as fh:
        json.dump(js, fh)
    print("time", time.time() - t0)
