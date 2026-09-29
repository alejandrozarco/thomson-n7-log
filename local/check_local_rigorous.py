"""Rigorous re-derivation of every constant in the quartic local lemma (LOCAL_LEMMA.md, log kernel),
with enclosures, and an exact check of every inequality used.  Prints PASS/FAIL per step.

Arithmetic used
  * exact: sympy over K = Q(alpha), alpha = sqrt(10+2 sqrt5) = 4 sin 72deg (minpoly x^4-20x^2+80);
           sqrt5 = (alpha^2-10)/2, sin 36deg = sqrt5/alpha.  All of P, the frames, W_ij, mu_i, the
           Taylor polynomial of the minorant to degree 6, H, the kernel, the projectors and the
           coupling live in K.
  * balls: python-flint arb (320 bits).  Elements of K are evaluated with an arb enclosure of alpha;
           every derived quantity (orthonormal bases by ball Gram-Schmidt, tensor contractions,
           Frobenius norms, sqrt, the majorant tail with sqrt(1-rho^2)) is an enclosure of the
           exact value.  A constant is used only through a rational bound read off the ball.
  * rational: fractions.Fraction.  PSD certificates are exact LDL^T over Q of a dyadic rounding of the
           (ball-enclosed) matrix, shifted by a rigorous bound on the rounding error (Frobenius).
           The scalar arguments of section 3 / 3' are evaluated in exact rationals.
usage: OMP_NUM_THREADS=1 python3 check_local_rigorous.py
"""
import sys, time
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import factorial, ceil, isqrt
import numpy as np
from flint import arb, fmpq, ctx
from sympy import sqrt as ssqrt, QQ, symbols, Poly, factor
from sympy.polys.rings import ring
from sympy.polys.matrices import DomainMatrix

ctx.prec = 320
T0 = time.time()
RES = []


def check(name, cond, detail=''):
    RES.append((name, bool(cond)))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"  --  {detail}" if detail else ''), flush=True)


def info(msg):
    print('       ' + msg, flush=True)


# ---------------------------------------------------------------- helpers: K -> arb -> Q
alpha_expr = ssqrt(10 + 2 * ssqrt(5))
K = QQ.algebraic_field(alpha_expr)
AL = K.from_sympy(alpha_expr)
ALPHA = (arb(10) + 2 * arb(5).sqrt()).sqrt()


def K2arb(z):
    v = arb(0)
    for q in K.convert(z).to_list():
        v = v * ALPHA + arb(fmpq(int(q.numerator), int(q.denominator)))
    return v


def ex2fr(x):                      # exact arb -> Fraction
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Fr(m * 2 ** e) if e >= 0 else Fr(m, 2 ** (-e))


def upQ(x):                        # rational upper bound of a ball: mid + rad (both exact)
    return ex2fr(x.mid()) + ex2fr(x.rad())


def loQ(x):
    return ex2fr(x.mid()) - ex2fr(x.rad())


def dec_up(q, digits):             # round a Fraction up to `digits` decimals
    s = 10 ** digits
    return Fr(ceil(q * s), s)


def fr2arb(q):
    return arb(fmpq(q.numerator, q.denominator))


def round_dyadic(x, bits=64):
    """ball x -> (dyadic rational r, rigorous bound e >= |x_exact - r|)"""
    mid = ex2fr(x.mid())
    r = Fr(round(mid * 2 ** bits), 2 ** bits)
    return r, abs(mid - r) + ex2fr(x.rad())


def ldl_pd(M):
    """exact LDL^T over Q; True iff M (list of lists of Fractions, symmetric) is positive definite.
    Returns (ok, min pivot)."""
    n = len(M)
    A = [row[:] for row in M]
    piv = []
    for k in range(n):
        d = A[k][k]
        if d <= 0:
            return False, d
        piv.append(d)
        for i in range(k + 1, n):
            f = A[i][k] / d
            if f:
                for j in range(k + 1, i + 1):
                    A[i][j] -= f * A[j][k]
        for i in range(k + 1, n):
            for j in range(k + 1, i + 1):
                A[j][i] = A[i][j]
    return True, min(piv)


def psd_margin_cert(Marb, shift):
    """Certify  M_exact - shift*I  > 0  for a symmetric ball matrix Marb (numpy object array of arb):
    round to dyadics Mt, e_F >= ||M_exact - Mt||_F (hence >= ||.||_op), then exact LDL^T of
    Mt - (shift + e_F) I.  Returns (ok, e_F, min pivot)."""
    n = Marb.shape[0]
    Mt = [[None] * n for _ in range(n)]
    e2 = Fr(0)
    for i in range(n):
        for j in range(i, n):
            r, e = round_dyadic(Marb[i, j] if i <= j else Marb[j, i])
            if i != j:
                r2, e2_ = round_dyadic(Marb[j, i])
                e = max(e, e2_ + abs(r2 - r))
            Mt[i][j] = Mt[j][i] = r
            e2 += e * e * (1 if i == j else 2)
    eF = Fr(isqrt(ceil(e2 * 10 ** 80)) + 1, 10 ** 40)           # >= sqrt(e2)
    assert eF * eF >= e2
    for i in range(n):
        Mt[i][i] -= shift + eF
    ok, mp_ = ldl_pd(Mt)
    return ok, eF, mp_


# ================================================================ STEP 0: exact geometry
print('== Step 0: exact configuration P, tangent frames, kernel data in K = Q(alpha)')
assert K.ext.minpoly.as_expr().free_symbols and list(K.mod.to_list()) == [1, 0, -20, 0, 80]
r5 = (AL * AL - K(10)) / K(2)
c72, s72 = (r5 - K(1)) / K(4), AL / K(4)
c144, s144 = -(r5 + K(1)) / K(4), r5 / AL
Z, O = K(0), K(1)
cs = [(O, Z), (c72, s72), (c144, s144), (c144, -s144), (c72, -s72)]
P = [[c, s, Z] for c, s in cs] + [[Z, Z, O], [Z, Z, -O]]
E1 = [[Z, Z, O]] * 5 + [[O, Z, Z]] * 2
E2 = [[-s, c, Z] for c, s in cs] + [[Z, O, Z]] * 2
dot = lambda u, v: sum((x * y for x, y in zip(u, v)), K(0))
ok = r5 * r5 == K(5) and all(dot(P[i], P[i]) == O and dot(E1[i], E1[i]) == O and dot(E2[i], E2[i]) == O
                             and dot(P[i], E1[i]) == Z and dot(P[i], E2[i]) == Z and dot(E1[i], E2[i]) == Z
                             for i in range(7))
check('0.1 P on S^2, (E1_i,E2_i,P_i) orthonormal frames, exactly', ok)
g = [[dot(P[i], P[j]) for j in range(7)] for i in range(7)]
W = [[(K(1) / (K(2) * (K(1) - g[i][j])) if i != j else Z) for j in range(7)] for i in range(7)]
mu = [sum((W[i][j] * g[i][j] for j in range(7) if j != i), K(0)) for i in range(7)]
crit = all(all(sum((W[i][j] * P[j][m] for j in range(7) if j != i), K(0)) == mu[i] * P[i][m] for m in range(3))
           for i in range(7))
check('0.2 criticality  sum_j W_ij P_j = mu_i P_i as vectors; mu_ring = 0, mu_pole = -1/4 (exact)',
      crit and all(mu[i] == Z for i in range(5)) and mu[5] == K(QQ(-1, 4)) and mu[6] == K(QQ(-1, 4)))

# ================================================================ STEP 1: exact Taylor polynomial of the minorant
print('== Step 1: exact expansion of the minorant  sum mu_i nu_i + sum_{i<j} [W<h_i,h_j> + 1/2 psi5(u_ij)]  to degree 6')
R14, *X = ring(','.join(f'x{m}' for m in range(14)), K)
DMAX = 6


def tr(p, d=DMAX):
    return R14({m: c for m, c in p.items() if sum(m) <= d})


nu, h = [], []
for i in range(7):
    rr = X[2 * i] ** 2 + X[2 * i + 1] ** 2
    n_ = tr(-rr * K(QQ(1, 2)) - rr ** 2 * K(QQ(1, 8)) - rr ** 3 * K(QQ(1, 16)))   # sqrt(1-r^2)-1 to deg 6
    nu.append(n_)
    h.append([X[2 * i] * E1[i][m] + X[2 * i + 1] * E2[i][m] + n_ * P[i][m] for m in range(3)])
Pmin = R14(0)
lin_sum = R14(0)
for i in range(7):
    Pmin += nu[i] * mu[i]
for i, j in combinations(range(7), 2):
    hh = tr(sum((h[i][m] * h[j][m] for m in range(3)), R14(0)))
    ell = sum((h[i][m] * P[j][m] + h[j][m] * P[i][m] for m in range(3)), R14(0))
    lin_sum += ell * W[i][j]
    u = (ell + hh) * (K(1) / (K(1) - g[i][j]))
    psi5, up = R14(0), R14(1)
    for k in range(1, 6):
        up = tr(up * u)
        if k >= 2:
            psi5 += up * K(QQ(1, k))
    Pmin += hh * W[i][j] + psi5 * K(QQ(1, 2))
check('1.1 identity (1): sum_{i<j} W_ij l_ij = sum_i mu_i nu_i as polynomials (deg<=6)',
      tr(lin_sum - sum((nu[i] * mu[i] for i in range(7)), R14(0))) == 0)
hom = {d: {m: c for m, c in Pmin.items() if sum(m) == d} for d in range(DMAX + 1)}
check('1.2 no constant or linear terms (P critical in the chart)', not hom[0] and not hom[1],
      f'{len(Pmin)} monomials, {time.time() - T0:.1f}s')
F2, F3, F4 = (R14(hom[d]) for d in (2, 3, 4))

# ================================================================ STEP 2: Hessian, kernel, spectrum
print('== Step 2: Hessian H (14x14 over K), kernel, spectrum on W')
H = [[(2 * F2.coeff(X[p] ** 2) if p == q else F2.coeff(X[p] * X[q])) for q in range(14)] for p in range(14)]
H = [[K.convert(x) for x in row] for row in H]
Hm = DomainMatrix(H, (14, 14), K)


def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]


rot = []
for ax in ([O, Z, Z], [Z, O, Z], [Z, Z, O]):
    v = []
    for i in range(7):
        w_ = cross(ax, P[i]); v += [dot(w_, E1[i]), dot(w_, E2[i])]
    rot.append(v)
cos4 = [O, c144, c72, c72, c144]; sin4 = [Z, s144, -s72, s72, -s144]      # cos, sin (4 pi k / 5)
s1 = [Z] * 14; s2 = [Z] * 14
for k in range(5):
    s1[2 * k], s2[2 * k] = cos4[k], sin4[k]
kern = rot + [s1, s2]
matvec = lambda A, v: [sum((A[p][q] * v[q] for q in range(14)), K(0)) for p in range(14)]
check('2.1 H r = 0 (3 rotation fields) and H s1 = H s2 = 0, as vectors in R^14',
      all(all(x == Z for x in matvec(H, v)) for v in kern))
check('2.2 s1, s2 orthogonal to rotations and to each other; |s1|^2 = |s2|^2 = 5/2',
      all(dot(sv, r) == Z for sv in (s1, s2) for r in rot) and dot(s1, s2) == Z
      and dot(s1, s1) == K(QQ(5, 2)) and dot(s2, s2) == K(QQ(5, 2)))
KG = DomainMatrix([[dot(u, v) for v in kern] for u in kern], (5, 5), K)
check('2.3 kernel vectors independent (Gram det != 0)', KG.det() != Z)
lam = symbols('lam')
cp = Poly([K.to_sympy(c) for c in Hm.charpoly()], lam)
target = Poly(lam ** 5 * (lam - 3) ** 5 * (4 * lam - 9) ** 2 * (4 * lam - 3) ** 2 / 256, lam)
check('2.4 charpoly(H) = lam^5 (lam-3)^5 (4lam-9)^2 (4lam-3)^2 / 256  =>  spec(H|_W) = {3/4 x2, 9/4 x2, 3 x5}, lam_W = 3/4',
      cp == target, f'{time.time() - T0:.1f}s')
LAMW = Fr(3, 4)

# projectors (exact, over K)
Kmat = DomainMatrix([[kern[a][m] for a in range(5)] for m in range(14)], (14, 5), K)
PiK = Kmat.matmul(KG.inv()).matmul(Kmat.transpose())
PiK_l = PiK.to_list()
PiW_l = [[(O if p == q else Z) - PiK_l[p][q] for q in range(14)] for p in range(14)]
check('2.5 Pi_ker is an exact orthogonal projector (Pi^2 = Pi, Pi k = k)',
      PiK.matmul(PiK) == PiK and all(matvec(PiK_l, v) == v for v in kern))

# ================================================================ STEP 3: data on S (+) W, exact
print('== Step 3: cubic/quartic on S, coupling, exact square')
R2, sg1, sg2 = ring('sg1,sg2', K)


def compose(p, forms):          # p in R14, forms: 14 elements of R2
    out = R2(0)
    for m, c in p.items():
        term = R2(c)
        for k, e in enumerate(m):
            if e:
                term *= forms[k] ** e
        out += term
    return out


sform = [sg1 * s1[m] + sg2 * s2[m] for m in range(14)]         # s = sg1 s1 + sg2 s2, |s|^2 = 5/2 |sg|^2
sig4 = (sg1 ** 2 + sg2 ** 2) ** 2
check('3.1 C(s,s,s) = 0 identically on S', compose(F3, sform) == 0)
Qpoly = compose(F4, sform)
check('3.2 D(s,s,s,s) = (13/40)|s|^4 identically (Q = 13/40)', Qpoly == sig4 * K(QQ(13, 40) * QQ(25, 4)))
# coupling G(sigma) = grad F3 at s = 3 C(s,s,.) ; columns for m = (sg1^2, sg1 sg2, sg2^2)
Gpolys = [compose(F3.diff(X[m]), sform) for m in range(14)]
mons = [(2, 0), (1, 1), (0, 2)]
Gam = [[K.convert(Gpolys[m].coeff(sg1 ** a * sg2 ** b)) for (a, b) in mons] for m in range(14)]
check('3.3 3C(s,s,.) is a quadratic form in sigma (no other monomials)',
      all(sum((Gam[m][k] * sg1 ** a * sg2 ** b for k, (a, b) in enumerate(mons)), R2(0)) == Gpolys[m] for m in range(14)))
GamW = [[sum((PiW_l[p][q] * Gam[q][k] for q in range(14)), K(0)) for k in range(3)] for p in range(14)]
Mreg = Hm + Kmat.matmul(Kmat.transpose())            # = H on W, K K^T on ker ; Mreg^{-1} G_W = H_W^{-1} G_W
Minv = Mreg.inv().to_list()
Xs = [[sum((Minv[p][q] * GamW[q][k] for q in range(14)), K(0)) for k in range(3)] for p in range(14)]   # H_W^{-1} Gamma_W
N3 = [[sum((GamW[p][k] * Xs[p][l] for p in range(14)), K(0)) for l in range(3)] for k in range(3)]     # <G_W, H^-1 G_W>
V3 = [[sum((Xs[p][k] * Xs[p][l] for p in range(14)), K(0)) for l in range(3)] for k in range(3)]       # |w*|^2
C3 = [[sum((GamW[p][k] * GamW[p][l] for p in range(14)), K(0)) for l in range(3)] for k in range(3)]   # |G_W|^2
mvec = [sg1 ** 2, sg1 * sg2, sg2 ** 2]
qf = lambda A: sum((A[k][l] * mvec[k] * mvec[l] for k in range(3) for l in range(3)), R2(0))
s4 = sig4 * K(QQ(25, 4))                                                                           # |s|^4
check('3.4 W-projection check: H_W^{-1}G_W in W and H (H_W^{-1}G_W) = G_W exactly',
      all(sum((kern[a][p] * Xs[p][k] for p in range(14)), K(0)) == Z for a in range(5) for k in range(3))
      and all(sum((H[p][q] * Xs[q][k] for q in range(14)), K(0)) == GamW[p][k] for p in range(14) for k in range(3)))
check('3.5 |c(s)|^2 = |G_W|^2/9 = (23/480)|s|^4 identically', qf(C3) * K(QQ(1, 9)) == s4 * K(QQ(23, 480)))
check('3.6 exact square: Q|s|^4 - 1/2 <G_W, H_W^{-1} G_W> = (1/10)|s|^4 identically (Q_eff = 1/10)',
      Qpoly - qf(N3) * K(QQ(1, 2)) == s4 * K(QQ(1, 10)))
check('3.7 |w*(s)|^2 = |H_W^{-1} G_W|^2 = (67/120)|s|^4 identically (kappa^2 = 67/120)',
      qf(V3) == s4 * K(QQ(67, 120)))
KAP2 = Fr(67, 120)
KAPU = Fr(747218, 10 ** 6)
check('3.8 kappa <= 0.747218 (rational upper bound: 0.747218^2 >= 67/120)', KAPU ** 2 >= KAP2)
print(f'       ({time.time() - T0:.1f}s)')

# ================================================================ STEP 4: ball tensors on S (+) W
print('== Step 4: orthonormal bases of S and W (ball Gram-Schmidt of exact data), tensor block norms')


def arbvec(v):
    return [K2arb(x) for x in v]


def gs_ball(cands):
    out, acc = [], []
    for idx, c in enumerate(cands):
        v = list(c)
        for o in out:
            p = sum((a * b for a, b in zip(v, o)), arb(0))
            v = [a - p * b for a, b in zip(v, o)]
        n2 = sum((a * a for a in v), arb(0))
        if n2 > 0:                       # certified positive (ball excludes 0)
            nv = n2.sqrt()
            out.append([a / nv for a in v]); acc.append(idx)
    return out, acc


cands = [arbvec(v) for v in kern] + [[arb(int(p == q)) for p in range(14)] for q in range(14)]
ONB, acc = gs_ball(cands)
check('4.1 ball Gram-Schmidt accepted rot1-3, s1, s2 first and 9 unit vectors after (=> exact ONB of W enclosed)',
      len(ONB) == 14 and acc[:5] == [0, 1, 2, 3, 4])
Bs = ONB[3:5] + ONB[5:]          # 11 vectors: S (2) then W (9)
Bn = np.empty((14, 11), dtype=object)
for a in range(11):
    for m in range(14):
        Bn[m, a] = Bs[a][m]


def dense(pol, d):
    T = np.empty((14,) * d, dtype=object); T.fill(arb(0))
    for m, c in pol.items():
        idx = []
        for k, e in enumerate(m):
            idx += [k] * e
        ps = set(permutations(idx)); val = K2arb(c) / len(ps)
        for p in ps:
            T[p] = val
    return T


def contract(T, d):
    Xt = T
    for _ in range(d):
        Xt = np.tensordot(Xt, Bn, axes=([0], [0]))
    return Xt


Hb = contract(dense(F2, 2), 2) * 2
C = contract(dense(F3, 3), 3)
D = contract(dense(F4, 4), 4)
sI, wI = [0, 1], list(range(2, 11))
dev = max(float(abs(Hb[2 + a, 2 + b])) for a in range(9) for b in range(9) if a != b)
info(f'(H in the W-ONB is not diagonal -- basis is not an eigenbasis; max offdiag {dev:.3f}; not needed)')
cmax = max(float(abs(C[a, b, c].upper())) for a in sI for b in sI for c in sI)
check('4.2 C(s,s,s) block encloses 0 (consistent with exact 3.1)', all(C[a, b, c].contains(0) for a in sI for b in sI for c in sI),
      f'max |ball| {cmax:.1e}')


def frob_up(T, blocks, digits=6):
    import itertools
    tot = arb(0)
    for idx in itertools.product(*blocks):
        tot += T[idx] * T[idx]          # (arb ** 2 of a ball around 0 is nan in python-flint)
    ub = upQ(tot.sqrt())
    return dec_up(ub, digits), tot


G2, _ = frob_up(C, [wI, wI, wI])
D1, _ = frob_up(D, [sI, sI, sI, wI])
D2, _ = frob_up(D, [sI, sI, wI, wI])
D3, _ = frob_up(D, [sI, wI, wI, wI])
D4, _ = frob_up(D, [wI, wI, wI, wI])
G1F, _ = frob_up(C, [sI, wI, wI])
doc = dict(g2=Fr('1.319020'), d1=Fr('0.147314'), d2=Fr('0.625011'), d3=Fr('0.517257'), d4=Fr('1.840589'))
for nm, val, dv in [('gamma2 = |C_www|_F', G2, doc['g2']), ('delta1 = |D_sssw|_F', D1, doc['d1']),
                    ('delta2 = |D_ssww|_F', D2, doc['d2']), ('delta3 = |D_swww|_F', D3, doc['d3']),
                    ('delta4 = |D_wwww|_F', D4, doc['d4'])]:
    check(f'4.3 {nm} <= {float(val):.6f}  (certified upper bound; old doc value {float(dv):.6f})', abs(val - dv) <= Fr(2, 10 ** 6))
info(f'|C_sww|_F <= {float(G1F):.6f}  (Frobenius fallback for gamma1)')
# c_q: 6 d2 a^2 + 4 d3 a b + d4 b^2 <= CQ (a^2+b^2)
CQ = Fr('4.203074')
okq = CQ >= 6 * D2 and CQ >= D4 and (CQ - 6 * D2) * (CQ - D4) >= 4 * D3 * D3
check('4.4 c_q = 4.203074 >= lambda_max[[6d2,2d3],[2d3,d4]] (exact 2x2 PSD test with the rational bounds)', okq)

# exact Frobenius norms (basis-free, over K): |T|_{blocks}|_F^2 = < T, T x_1 Pi_1 x_2 ... >
PiS_l = [[K(QQ(2, 5)) * (s1[p] * s1[q] + s2[p] * s2[q]) for q in range(14)] for p in range(14)]
PSo, PWo = np.array(PiS_l, dtype=object), np.array(PiW_l, dtype=object)


def denseK(pol, d):
    T = np.empty((14,) * d, dtype=object); T.fill(K(0))
    for m, c in pol.items():
        idx = []
        for k, e in enumerate(m):
            idx += [k] * e
        ps = set(permutations(idx)); val = c * K(QQ(1, len(ps)))
        for p_ in ps:
            T[p_] = val
    return T


def fro2_exact(T, projs):
    Xt = T
    for Pm in projs:
        Xt = np.tensordot(Xt, Pm, axes=([0], [0]))
    v = sum((a * b for a, b in zip(T.flat, Xt.flat)), K(0))
    lst = K.convert(v).to_list()
    assert all(q == 0 for q in lst[:-1]), 'Frobenius^2 not rational'
    return Fr(int(lst[-1].numerator), int(lst[-1].denominator)) if lst else Fr(0)


T3K, T4K = denseK(F3, 3), denseK(F4, 4)
EX = dict(g1F=fro2_exact(T3K, [PSo, PWo, PWo]), g2=fro2_exact(T3K, [PWo, PWo, PWo]),
          d1=fro2_exact(T4K, [PSo, PSo, PSo, PWo]), d2=fro2_exact(T4K, [PSo, PSo, PWo, PWo]),
          d3=fro2_exact(T4K, [PSo, PWo, PWo, PWo]), d4=fro2_exact(T4K, [PWo, PWo, PWo, PWo]))
info('exact squared Frobenius norms (rational): ' + ', '.join(f'{k}^2 = {v}' for k, v in EX.items()))
check('4.5 exact Frobenius^2 (over K, via exact projectors) are <= the squares of the bounds used',
      G1F ** 2 >= EX['g1F'] and G2 ** 2 >= EX['g2'] and D1 ** 2 >= EX['d1'] and D2 ** 2 >= EX['d2']
      and D3 ** 2 >= EX['d3'] and D4 ** 2 >= EX['d4'], f'{time.time() - T0:.1f}s')

# ================================================================ STEP 5: gamma1 via certified operator norms
print('== Step 5: gamma1 = sqrt(sum_alpha ||C(e_alpha,.,.)|_W||_op^2), op norms certified by exact LDL^T over Q')
opn = []
for a in sI:
    Mf = np.array([[float(C[a, 2 + k, 2 + l].mid()) for l in range(9)] for k in range(9)])
    ev = np.linalg.eigvalsh(Mf)
    c_a = dec_up(Fr(float(max(abs(ev)))) + Fr(1, 10 ** 8), 8)
    oks = []
    for sgn in (1, -1):
        Mb = np.empty((9, 9), dtype=object)
        for k in range(9):
            for l in range(9):
                Mb[k, l] = (fr2arb(c_a) if k == l else arb(0)) - sgn * C[a, 2 + k, 2 + l]
        ok_, eF, mp_ = psd_margin_cert(Mb, Fr(0))
        oks.append(ok_)
    opn.append(c_a)
    check(f'5.{a + 1} ||C(e_{a + 1},.,.)|_W||_op <= {float(c_a):.8f}:  c I -/+ C_alpha > 0 (exact LDL^T, rounding err {float(eF):.1e})',
          all(oks), f'float spectrum [{ev.min():.6f}, {ev.max():.6f}]')
G1 = Fr('0.387896')
check('5.3 gamma1 <= 0.387896 (= doc value), since 0.387896^2 >= c_1^2 + c_2^2', G1 * G1 >= opn[0] ** 2 + opn[1] ** 2,
      f'sqrt(c1^2+c2^2) = {float((opn[0] ** 2 + opn[1] ** 2)) ** 0.5:.8f}')

# ================================================================ STEP 6: Bombieri norms, exact
print('== Step 6: Bombieri norms of the degree-5 and -6 parts (exact in K, then enclosed)')
BB = {}
for d in (5, 6):
    b2 = K(0)
    for m, c in hom[d].items():
        w_ = 1
        for e in m:
            w_ *= factorial(e)
        b2 += c * c * K(QQ(w_, factorial(d)))
    BB[d] = b2
    info(f'B{d}^2 = {K.to_sympy(b2)}  (exact element of K)')
B5 = dec_up(upQ(K2arb(BB[5]).sqrt()), 6)
B6 = dec_up(upQ(K2arb(BB[6]).sqrt()), 6)
check(f'6.1 B5 <= {float(B5):.6f}, B6 <= {float(B6):.6f}  (doc 3.12270, 9.96131)', B5 <= Fr('3.12270') and B6 <= Fr('9.96131'))

# ================================================================ STEP 7: majorant tail (degree >= 7), balls
print('== Step 7: per-pair majorant tail K7 at rho = 1/100 (arb; sqrt(1-g^2), N(rho) = 1 - sqrt(1-rho^2) enclosed)')
RHO = Fr(1, 100)
rho_b = fr2arb(RHO)


def ipow(x, k):
    r = arb(1)
    for _ in range(k):
        r = r * x
    return r


def smul(a, b, D_):
    r = [arb(0)] * (D_ + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:D_ + 1 - i]):
            r[i + j] += x * y
    return r


def Kij(gb, kstart, rho=rho_b, DS=8):
    """(F(rho) - [F]_{<kstart}(rho)) / rho^kstart ;  F = W HH + 1/2 sum_{k=2}^5 U^k/k  (majorant of f_ij)"""
    sg = (1 - gb * gb).sqrt() if not (1 - gb * gb).contains(0) else arb(0)
    ag = abs(gb); Wb_ = 1 / (2 * (1 - gb))
    Rv = [arb(0)] * (DS + 1); Rv[1] = arb(1)
    Nv = [arb(0)] * (DS + 1)
    binabs = [Fr(1, 2), Fr(1, 8), Fr(1, 16), Fr(5, 128)]          # |binom(1/2,k)|, k = 1..4
    for k in range(1, DS // 2 + 1):
        Nv[2 * k] = fr2arb(binabs[k - 1])
    RR, RN, NN = smul(Rv, Rv, DS), smul(Rv, Nv, DS), smul(Nv, Nv, DS)
    HH = [x / 2 + 2 * sg * y + ag * z for x, y, z in zip(RR, RN, NN)]
    U = [(arb(2).sqrt() * sg * x + ag * y + z) / (1 - gb) for x, y, z in zip(Rv, Nv, HH)]
    Fs = [Wb_ * x for x in HH]
    up = [arb(1)] + [arb(0)] * DS
    for k in range(1, 6):
        up = smul(up, U, DS)
        if k >= 2:
            Fs = [f + x / (2 * k) for f, x in zip(Fs, up)]
    N = 1 - (1 - rho * rho).sqrt()
    hh = rho * rho / 2 + 2 * sg * rho * N + ag * N * N
    u = (arb(2).sqrt() * sg * rho + ag * N + hh) / (1 - gb)
    Fc = Wb_ * hh + sum((ipow(u, k) / (2 * k) for k in range(2, 6)), arb(0))
    rem = Fc - sum((Fs[k] * ipow(rho, k) for k in range(kstart)), arb(0))
    return rem / ipow(rho, kstart)


gb = [[K2arb(g[i][j]) for j in range(7)] for i in range(7)]
kvals = {}
rows7, rows5 = [], []
for i in range(7):
    t7, t5 = arb(0), arb(0)
    for j in range(7):
        if j != i:
            t7 += Kij(gb[i][j], 7); t5 += Kij(gb[i][j], 5)
    rows7.append(upQ(t7)); rows5.append(upQ(t5))
K7 = dec_up(max(rows7), 4)
K5a = dec_up(max(rows5), 3)
check(f'7.1 K7 = max_i sum_j K_ij <= {float(K7):.4f} at rho = 1/100 (doc 70.97)', K7 <= Fr('70.974'))
info(f'route (a): K = max_i sum_j K_ij(deg>=5) <= {float(K5a):.3f} at rho = 1/100 (not used)')
KK = B5 + B6 * RHO + K7 * RHO ** 2
KKu = dec_up(KK, 5)
check(f'7.2 K = B5 + B6 rho + K7 rho^2 <= {float(KKu):.5f} (doc 3.2294)', KKu <= Fr('3.2295'))
check('7.3 pole point terms: mu_pole < 0 and all Taylor coeffs of sqrt(1-x)-1 are < 0 => dropped tail >= 0; ring mu = 0',
      all(mu[i] == Z for i in range(5)) and all(K2arb(mu[i]) < 0 for i in (5, 6)))
print(f'       ({time.time() - T0:.1f}s)')

# ================================================================ STEP 8: Lemma L (|v|^2 form), exact scalar argument
print('== Step 8: Lemma L (section 3): scalar argument in exact rationals with the certified constants')
info(f'constants used: rho=1/100, lam_W=3/4, Q_eff=1/10, kappa<={KAPU}, kappa^2=67/120, gamma1<={G1}, gamma2<={G2},')
info(f'                delta1<={D1}, c_q<={CQ}, K<={KKu} (B5<={B5}, B6<={B6}, K7<={K7})')


def scalar_v(g1, A, eta, rho=RHO, Kc=KKu):
    bb = (3 * g1 + G2) * rho + CQ * rho ** 2 + 2 * Kc * rho ** 3          # coefficient of b^2
    cx = bb * (1 + eta) + 2 * D1 * rho / A                               # x^2 errors
    ca = Kc * rho + 4 * D1 * KAPU * rho + 2 * D1 * rho * A + bb * (1 + 1 / eta) * KAP2   # a^4 errors
    return bb, LAMW / 2 - cx, Fr(1, 10) - ca


bb, cxL, caL = scalar_v(G1, Fr(1, 16), Fr(4))
check('8.1 b^2-coefficient beta_b = (3g1+g2)rho + c_q rho^2 + 2K rho^3', True, f'beta_b = {float(bb):.7f}')
check('8.2 Lemma L:  x^2-coefficient  3/8 - 5 beta_b - 32 delta1 rho >= 0.2015', cxL >= Fr('0.2015'), f'= {float(cxL):.6f}')
check('8.3 Lemma L:  a^4-coefficient  1/10 - (K rho + 4 d1 kappa rho + d1 rho/8 + (5/4) kappa^2 beta_b) >= 0.0454',
      caL >= Fr('0.0454'), f'= {float(caL):.6f}')
_, cxF, caF = scalar_v(G1F, Fr(1, 16), Fr(4))
check('8.4 robustness: Frobenius fallback gamma1 <= |C_sww|_F still closes (x^2 >= 0.1434, a^4 >= 0.0373)',
      cxF >= Fr('0.1434') and caF >= Fr('0.0373'), f'x^2 {float(cxF):.6f}, a^4 {float(caF):.6f}')

# ================================================================ STEP 9: Lean form (|w|^2): margin PSD certificate + scalar argument
print("== Step 9: Lemma L' (Lean form, |w|^2 and |s|^4): exact-rational PSD certificate + scalar argument in (a, b)")
EPS, QP, THETA = Fr(1, 16), Fr(29, 500), None
QK = Fr(13, 40)
# choose the Gram parameter theta (float search), then certify exactly
PiW_b = [[K2arb(x) for x in row] for row in PiW_l]
PiK_b = [[K2arb(x) for x in row] for row in PiK_l]
H_b = [[K2arb(x) for x in row] for row in H]
GW_b = [[K2arb(x) for x in row] for row in GamW]


def cert_matrix(eps, qp, theta):
    M = np.empty((17, 17), dtype=object)
    for p in range(14):
        for q in range(14):
            M[p, q] = H_b[p][q] / 2 - fr2arb(eps) * PiW_b[p][q] + PiK_b[p][q]
        for k in range(3):
            M[p, 14 + k] = M[14 + k, p] = GW_b[p][k] / 2
    Gt = [[1, 0, theta], [0, 2 - 2 * theta, 0], [theta, 0, 1]]
    for k in range(3):
        for l in range(3):
            M[14 + k, 14 + l] = fr2arb((QK - qp) * Fr(25, 4) * Fr(Gt[k][l]))
    return M


Mbase = np.array([[float(x.mid()) for x in row] for row in cert_matrix(EPS, QP, Fr(0))])
best = None
for k in range(-20000, 20001):          # theta = k/20000; choose the Gram parameter maximising lambda_min (float)
    th = k / 20000
    Mf = Mbase.copy()
    Mf[14, 16] = Mf[16, 14] = float((QK - QP) * Fr(25, 4)) * th
    Mf[15, 15] = float((QK - QP) * Fr(25, 4)) * (2 - 2 * th)
    lm = np.linalg.eigvalsh(Mf).min()
    if best is None or lm > best[0]:
        best = (lm, Fr(k, 20000))
THETA = best[1]
okc, eF, mpv = psd_margin_cert(cert_matrix(EPS, QP, THETA), Fr(0))
check(f"9.1 PSD certificate (17x17, exact LDL^T over Q of a 2^-64 rounding, err {float(eF):.1e}):  for all w in W, sigma:\n"
      f"         1/2<w,Hw> + 3C(s,s,w) + (13/40)|s|^4 >= {EPS}|w|^2 + {QP}|s|^4   (Gram theta = {THETA})",
      okc, f'float lambda_min {best[0]:.2e}, min pivot {float(mpv):.2e}')
qmax = QK - Fr(9, 2) * (Fr(49, 1440) / (LAMW - 2 * EPS) + Fr(1, 72) / (3 - 2 * EPS))
info(f'(exact optimum for eps = {EPS}: q\' < {float(qmax):.6f}, from the eigen-weights 49/1440 (lam 3/4), 1/72 (lam 3))')
A_w = Fr(1)
cw = EPS - bb - 2 * D1 * RHO / A_w
cs = QP - KKu * RHO - 2 * D1 * RHO * A_w
check("9.2 Lemma L': b^2-coefficient  eps - beta_b - 2 d1 rho/A >= 0.0342  (A = 1)", cw >= Fr('0.0342'), f'= {float(cw):.6f}')
check("9.3 Lemma L': a^4-coefficient  q' - K rho - 2 d1 rho A >= 0.0227", cs >= Fr('0.0227'), f'= {float(cs):.6f}')
bbF = (3 * G1F + G2) * RHO + CQ * RHO ** 2 + 2 * KKu * RHO ** 3
cwF = EPS - bbF - 2 * D1 * RHO / A_w
check("9.4 Lemma L' with the Frobenius fallback gamma1 <= |C_sww|_F (no op-norm certificate): b^2 >= 0.0226, a^4 >= 0.0227",
      cwF >= Fr('0.0226') and cs >= Fr('0.0227'), f'b^2 {float(cwF):.6f}')

# ================================================================ STEP 10: handoff to the cap (upstream section 7.2)
print('== Step 10: handoff constants (exact)')
check('10.1 localMinAt_of_sq: 7 (1/300)^2 <= (1/100)^2  (sup radius 1/300 => l2 radius <= rho)', 7 * Fr(1, 300) ** 2 <= RHO ** 2)
check('10.2 localGram_of_localMinAt: (11/2) tau = 1/300 at tau = 1/1650, and tau <= 1/10', Fr(11, 2) * Fr(1, 1650) == Fr(1, 300) and Fr(1, 1650) <= Fr(1, 10))
check('10.3 chart valid: rho^2 < 2 (<y_i,P_i> > 0)', RHO ** 2 < 2)
mind2 = min(K2arb(2 - 2 * g[i][j]) for i, j in combinations(range(7), 2))
check('10.4 u_ij < 1 on the ball: min |P_i-P_j| - 2 rho > 0', (mind2.sqrt() - 2 * rho_b) > 0, f'min |P_i-P_j|^2 = 2-2cos72 = {float(mind2.mid()):.6f}')

# ================================================================ STEP 11: sanity (not part of the proof)
print('== Step 11: sanity, direct 50-digit energy (information only; not part of the proof)')
import mpmath as mpm
mpm.mp.dps = 50
toM = lambda x: mpm.mpf(str(x.mid().str(60, radius=False)))
Pm = [[toM(K2arb(x)) for x in row] for row in P]
E1m = [[toM(K2arb(x)) for x in row] for row in E1]
E2m = [[toM(K2arb(x)) for x in row] for row in E2]


def energy(t):
    Y = []
    for i in range(7):
        x, y = t[2 * i], t[2 * i + 1]
        c = mpm.sqrt(1 - x * x - y * y)
        Y.append([c * Pm[i][m] + x * E1m[i][m] + y * E2m[i][m] for m in range(3)])
    return sum(-mpm.log(sum((Y[i][m] - Y[j][m]) ** 2 for m in range(3))) / 2 for i, j in combinations(range(7), 2))


E0 = -mpm.log(1600 * mpm.sqrt(5))
info(f'E(P) + log(1600 sqrt5) = {mpm.nstr(energy([0] * 14) - E0, 3)}')
HWf = np.array([[float(Hb[2 + a, 2 + b].mid()) for b in range(9)] for a in range(9)])
evw, U = np.linalg.eigh(HWf)
Wm = [[toM(Bs[2 + a][m]) for m in range(14)] for a in range(9)]
Sm = [[toM(Bs[a][m]) for m in range(14)] for a in range(2)]
rat = []
for ang in range(8):                     # directions in the 2-dim lam = 3/4 eigenspace of H_W
    cvec = np.cos(np.pi * ang / 8) * U[:, 0] + np.sin(np.pi * ang / 8) * U[:, 1]
    for r in (mpm.mpf(1) / 100, mpm.mpf(1) / 1000):
        for sgn in (1, -1):
            t = [sgn * r * sum(mpm.mpf(cvec[a]) * Wm[a][m] for a in range(9)) for m in range(14)]
            rat.append(((energy(t) - E0) / (mpm.mpf('0.2015') * r * r), float(r)))
info(f'(eigenvalues of H_W used: {evw[0]:.6f}, {evw[1]:.6f})')
mr = min(rat)
info(f'lam_W-eigendirection of W (s = 0, v = w): min (E-E(P))/(0.2015|v|^2) = {mpm.nstr(mr[0], 6)} at |t| = {mr[1]}  (limit (3/8)/0.2015 = {0.375 / 0.2015:.4f})')
# centre manifold t = s + w*(s): ratio to 0.0454 a^4
sig = [mpm.mpf(1), mpm.mpf(0)]
for a_ in (mpm.mpf(1) / 100, mpm.mpf(1) / 300):
    # w* = -H_W^{-1} G_W with G_W(sigma) in the unnormalised sigma-coordinates: s = sg1 s1 + sg2 s2, |s1|^2 = 5/2
    sg_ = [a_ / mpm.sqrt(mpm.mpf(5) / 2), mpm.mpf(0)]
    mv = [sg_[0] ** 2, sg_[0] * sg_[1], sg_[1] ** 2]
    s_un = [sg_[0] * toM(K2arb(s1[m])) for m in range(14)]
    wst = [-sum(toM(K2arb(Xs[m][k])) * mv[k] for k in range(3)) for m in range(14)]
    t = [s_un[m] + wst[m] for m in range(14)]
    info(f'centre manifold, a = {mpm.nstr(a_, 3)}: (E-E(P))/a^4 = {mpm.nstr((energy(t) - E0) / a_ ** 4, 6)}  (Q_eff = 0.1; ratio to 0.0454: {mpm.nstr((energy(t) - E0) / a_ ** 4 / mpm.mpf("0.0454"), 5)})')

# ================================================================ summary
nf = sum(1 for _, ok_ in RES if not ok_)
print(f'\n== SUMMARY: {len(RES) - nf}/{len(RES)} checks PASS, {nf} FAIL  ({time.time() - T0:.1f}s)')
print('ALL_PASS' if nf == 0 else 'SOME_FAIL')
sys.exit(0 if nf == 0 else 1)
