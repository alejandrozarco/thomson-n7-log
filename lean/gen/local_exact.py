"""Exact Taylor data of the log minorant at P over K = Q(alpha), alpha = sqrt(10+2 sqrt5) = 4 sin 72deg.

Adapted from local/check_local_rigorous.py (steps 0-3; same conventions, same frames, same chart).
Returns H (14x14), Gam (14x3: grad F3 at s = sg1*s1hat + sg2*s2hat, columns for m = (sg1^2, sg1 sg2, sg2^2)),
the 5 kernel vectors (3 rotation fields, s1hat, s2hat), the cubic/quartic parts F3, F4 as sparse polys.
Every quantity is an exact element of K.  Used by the Lean exporters in this folder.
"""
from itertools import combinations
from fractions import Fraction as Fr
from sympy import sqrt as ssqrt, QQ
from sympy.polys.rings import ring
from sympy.polys.matrices import DomainMatrix

alpha_expr = ssqrt(10 + 2 * ssqrt(5))
K = QQ.algebraic_field(alpha_expr)
AL = K.from_sympy(alpha_expr)
assert list(K.mod.to_list()) == [1, 0, -20, 0, 80]


def kcoeffs(z):
    """element of K -> [c0, c1, c2, c3] (Fractions via sympy QQ) with z = c0 + c1 a + c2 a^2 + c3 a^3"""
    lst = K.convert(z).to_list()              # high -> low
    lst = [Fr(int(q.numerator), int(q.denominator)) for q in lst]
    lst = [Fr(0)] * (4 - len(lst)) + lst
    return lst[::-1]


def build(DMAX=4):
    r5 = (AL * AL - K(10)) / K(2)
    c72, s72 = (r5 - K(1)) / K(4), AL / K(4)
    c144, s144 = -(r5 + K(1)) / K(4), r5 / AL
    Z, O = K(0), K(1)
    cs = [(O, Z), (c72, s72), (c144, s144), (c144, -s144), (c72, -s72)]
    P = [[c, s, Z] for c, s in cs] + [[Z, Z, O], [Z, Z, -O]]
    E1 = [[Z, Z, O]] * 5 + [[O, Z, Z]] * 2
    E2 = [[-s, c, Z] for c, s in cs] + [[Z, O, Z]] * 2
    dot = lambda u, v: sum((x * y for x, y in zip(u, v)), K(0))
    g = [[dot(P[i], P[j]) for j in range(7)] for i in range(7)]
    W = [[(K(1) / (K(2) * (K(1) - g[i][j])) if i != j else Z) for j in range(7)] for i in range(7)]
    mu = [sum((W[i][j] * g[i][j] for j in range(7) if j != i), K(0)) for i in range(7)]

    R14, *X = ring(','.join(f'x{m}' for m in range(14)), K)

    def tr(p, d=DMAX):
        return R14({m: c for m, c in p.items() if sum(m) <= d})

    nu, h = [], []
    for i in range(7):
        rr = X[2 * i] ** 2 + X[2 * i + 1] ** 2
        n_ = tr(-rr * K(QQ(1, 2)) - rr ** 2 * K(QQ(1, 8)) - rr ** 3 * K(QQ(1, 16)))
        nu.append(n_)
        h.append([X[2 * i] * E1[i][m] + X[2 * i + 1] * E2[i][m] + n_ * P[i][m] for m in range(3)])
    Pmin = R14(0)
    for i in range(7):
        Pmin += nu[i] * mu[i]
    for i, j in combinations(range(7), 2):
        hh = tr(sum((h[i][m] * h[j][m] for m in range(3)), R14(0)))
        ell = sum((h[i][m] * P[j][m] + h[j][m] * P[i][m] for m in range(3)), R14(0))
        u = (ell + hh) * (K(1) / (K(1) - g[i][j]))
        psi5, up = R14(0), R14(1)
        for k in range(1, 6):
            up = tr(up * u)
            if k >= 2:
                psi5 += up * K(QQ(1, k))
        Pmin += hh * W[i][j] + psi5 * K(QQ(1, 2))
    hom = {d: R14({m: c for m, c in Pmin.items() if sum(m) == d}) for d in range(DMAX + 1)}
    assert not hom[0] and not hom[1]
    F2, F3 = hom[2], hom[3]
    H = [[K.convert(2 * F2.coeff(X[p] ** 2) if p == q else F2.coeff(X[p] * X[q])) for q in range(14)]
         for p in range(14)]

    def cross(u, v):
        return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]

    rot = []
    for ax in ([O, Z, Z], [Z, O, Z], [Z, Z, O]):
        v = []
        for i in range(7):
            w_ = cross(ax, P[i]); v += [dot(w_, E1[i]), dot(w_, E2[i])]
        rot.append(v)
    cos4 = [O, c144, c72, c72, c144]; sin4 = [Z, s144, -s72, s72, -s144]
    s1 = [Z] * 14; s2 = [Z] * 14
    for k in range(5):
        s1[2 * k], s2[2 * k] = cos4[k], sin4[k]
    kern = rot + [s1, s2]
    matvec = lambda A, v: [sum((A[p][q] * v[q] for q in range(14)), K(0)) for p in range(14)]
    assert all(all(x == Z for x in matvec(H, v)) for v in kern)

    R2, sg1, sg2 = ring('sg1,sg2', K)

    def compose(p, forms):
        out = R2(0)
        for m, c in p.items():
            term = R2(c)
            for k, e in enumerate(m):
                if e:
                    term *= forms[k] ** e
            out += term
        return out

    sform = [sg1 * s1[m] + sg2 * s2[m] for m in range(14)]
    assert compose(F3, sform) == 0
    Gpolys = [compose(F3.diff(X[m]), sform) for m in range(14)]
    mons = [(2, 0), (1, 1), (0, 2)]
    Gam = [[K.convert(Gpolys[m].coeff(sg1 ** a * sg2 ** b)) for (a, b) in mons] for m in range(14)]
    # projectors (for the checker-style variant)
    KG = DomainMatrix([[dot(u, v) for v in kern] for u in kern], (5, 5), K)
    KGinv = KG.inv().to_list()
    return dict(K=K, H=H, Gam=Gam, kern=kern, KGinv=KGinv, F3=F3, F4=hom.get(4), X=X, R14=R14,
                s1=s1, s2=s2, P=P, E1=E1, E2=E2, g=g, W=W, mu=mu, Pmin=Pmin)
