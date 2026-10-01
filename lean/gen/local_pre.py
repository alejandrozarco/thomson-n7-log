"""Exact constants of Lemma L' along the Lean-friendly (projector-free, per-pair) route.

Everything the Lean proof will *compute in the kernel* is re-derived here exactly over K = Q(alpha),
alpha = sqrt(10 + 2 sqrt 5) = 4 sin 72deg (sympy), and every square root is replaced by a rational
upper bound checked by squaring.  No floating point enters a constant (floats only *propose* the
LDL^T certificate for gamma1, which is then re-checked exactly, mirroring the Lean check).

Route (lean/LOCAL_LEAN_DESIGN.md section 7, three levels):
  atom level : f_ij = Phi_g(A, B, C, C', ri2, rj2, ei, ej), g = <P_i,P_j> in {c72, c144, 0, -1};
               nu = nhat(r^2) + e,  nhat = -r^2/2 - r^4/8 - r^6/16,  0 >= e >= -c_e r^8;
               T6_g = weight-<=6 part (weights A,C,C' = 1; B,ri2,rj2 = 2; e = 8);
               remainder bounded by the *structural* majorant (products of univariate majorants).
  pair level : p_ij(x) = T6_g(atoms_ij(x)) in the 4 global-frame coordinates; homogeneous parts d=2..6;
               per-pair Bombieri squares (exact in K) for d = 5, 6.
  global     : sum of pairs + point terms == checker's minorant to degree 6 (asserted);
               H, F3, F4 as in local_exact.py.
Point terms (poles, mu = -1/4): -nu/4 >= r^2/8 + r^4/32 (+ r^6/64 >= 0, dropped); the r^2/8 goes to H,
the r^4/32 to F4 (so F4 == checker's F4), nothing at degree 6 -> per-pair B6 has no point term.

Constants (Lean-cheap):
  gamma1 : |3C(s,w,w)| = |sg1 w^T A1 w + sg2 w^T A2 w| <= c (|sg1|+|sg2|) b^2 <= (2c/sqrt5) a b^2,
           A_al = (1/2) D^2F3(shat_al), certified by  c I -/+ A_al + K K^T >= 0 (penalty PSD, 14x14),
           exact LDL^T mirror of the Lean check (dyadic L, D; remainder E diagonally dominant on the alpha box).
  gamma2 : ||F3||_B (unprojected Bombieri norm on R^14), exact.
  delta1 : 4D(s,s,s,w) = <g(sg), w> = <g - Pi_ker g, w>;  |g - Pi_ker g|^2 = c6 |sg|^6 exactly (C5-invariance).
  c_q    : 6D(ssww) <= ||B(sg)||_F b^2, ||B||_F^2 = c22 |sg|^4;  4D(swww) <= ||T_sg||_B b^3, ||T||_B^2 = c13 |sg|^2;
           D(wwww) <= ||F4||_B b^4;  then the exact 2x2 lambda_max test on rational bounds.
  B5, B6 : per pair (max_i sum_j) and global (for comparison);  K7 : per pair, e-form structural majorant.
Then the scalar argument of L' (A = 1, as LocalScalar.scalar_param) at rho = 1/100, and the largest closing rho.

usage: nice -n 19 python3 lean/gen/local_pre.py     (~1-2 min, one core)
Writes lean/gen/local_pre_out.json (constants + exported polynomials for the Lean generators).
"""
import os, sys, time, json
from fractions import Fraction as Fr
from itertools import combinations
from math import factorial, isqrt
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from local_exact import build, kcoeffs, K, AL
from sympy import QQ
from sympy.polys.rings import ring

T0 = time.time()
mp.mp.dps = 40
HERE = os.path.dirname(os.path.abspath(__file__))
RHO = Fr(1, 100)


def log(msg):
    print(f'[{time.time() - T0:6.1f}s] {msg}', flush=True)


# ------------------------------------------------------------------ K helpers
def kq(z):
    """K element that is rational -> Fraction (assert)."""
    c = kcoeffs(z)
    assert c[1] == 0 and c[2] == 0 and c[3] == 0, f'not rational: {c}'
    return c[0]


ALPHA = mp.sqrt(10 + 2 * mp.sqrt(5))


def kfloat(z):
    return sum(mp.mpf(c.numerator) / c.denominator * ALPHA ** k for k, c in enumerate(kcoeffs(z)))


# alpha box (same as LocalCert)
LO, HI = Fr(380422606518, 10 ** 11), Fr(380422606519, 10 ** 11)
S5LO, S5HI = Fr(2236067977499789, 10 ** 15), Fr(2236067977499790, 10 ** 15)
assert S5LO ** 2 <= 5 <= S5HI ** 2 and LO ** 2 <= 10 + 2 * S5LO and 10 + 2 * S5HI <= HI ** 2


def kel_lo(c):
    mn = lambda a, b: a if a <= b else b
    return c[0] + mn(c[1] * LO, c[1] * HI) + mn(c[2] * LO ** 2, c[2] * HI ** 2) + mn(c[3] * LO ** 3, c[3] * HI ** 3)


def kel_hi(c):
    mx = lambda a, b: b if a <= b else a
    return c[0] + mx(c[1] * LO, c[1] * HI) + mx(c[2] * LO ** 2, c[2] * HI ** 2) + mx(c[3] * LO ** 3, c[3] * HI ** 3)


def khi(z):
    return kel_hi(kcoeffs(z))


def klo(z):
    return kel_lo(kcoeffs(z))


def sqrt_up(q, digits=9):
    """rational upper bound of sqrt(q) (q Fraction >= 0), checked by squaring"""
    q = Fr(q)
    assert q >= 0
    s = 10 ** digits
    r = Fr(isqrt(int(q * s * s)) + 1, s)
    assert r * r >= q
    return r


def sqrt_up_K(z, digits=9):
    """rational upper bound of sqrt(z) for z in K (via the alpha box)"""
    return sqrt_up(khi(z), digits)


# ------------------------------------------------------------------ geometry (from local_exact.build, DMAX=6 for the check)
log('building exact data (local_exact.build, DMAX=6) ...')
D = build(DMAX=6)
P, E1, E2, g, W, mu = D['P'], D['E1'], D['E2'], D['g'], D['W'], D['mu']
R14, X = D['R14'], D['X']
kern, s1, s2, H, Gam, F3, F4 = D['kern'], D['s1'], D['s2'], D['H'], D['Gam'], D['F3'], D['F4']
Pmin_checker = D['Pmin']
dot = lambda u, v: sum((x * y for x, y in zip(u, v)), K(0))
Z, O = K(0), K(1)
log(f'checker minorant: {len(Pmin_checker)} monomials to degree 6')

# ------------------------------------------------------------------ atom level: Phi_g and T6_g
AT, A_, B_, C_, Cp_, ri2_, rj2_, ei_, ej_ = ring('A,B,C,Cp,ri2,rj2,ei,ej', K)
WGT = (1, 2, 1, 1, 2, 2, 8, 8)


def wdeg(m):
    return sum(w * e for w, e in zip(WGT, m))


def wtr(p, d=6):
    return AT({m: c for m, c in p.items() if wdeg(m) <= d})


def nu_poly(r2, e):
    return -r2 * K(QQ(1, 2)) - r2 ** 2 * K(QQ(1, 8)) - r2 ** 3 * K(QQ(1, 16)) + e


# structural majorants: univariate polynomials in R with nonnegative Fraction coefficients (dict deg -> coeff)
def madd(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + v
    return r


def mmul(a, b):
    r = {}
    for i, x in a.items():
        for j, y in b.items():
            r[i + j] = r.get(i + j, 0) + x * y
    return r


def mscale(q, a):
    return {k: q * v for k, v in a.items()}


def mev(a, R):
    return sum((v * R ** k for k, v in a.items()), Fr(0))


def mtail(a, dmin, R):
    return sum((v * R ** k for k, v in a.items() if k >= dmin), Fr(0))


# rational upper bounds of the square roots that appear in the atom bounds
SQ2 = sqrt_up(Fr(2))
CE = Fr(5, 128) / (1 - RHO ** 2)                # |e| <= CE r^8  (|binom(1/2,k)| <= 5/128 for k >= 4, decreasing)
CE = Fr(CE.numerator * 10 ** 12 // CE.denominator + 1, 10 ** 12)


def class_data(gK):
    """g in K -> (|g| upper bound, 1/(1-g) upper bound, sqrt(1-g^2) upper bound, W = 1/(2(1-g)) in K)"""
    absg = max(khi(gK), -klo(gK))
    absg = max(absg, Fr(0))
    inv1g = Fr(1) / (1 - khi(gK))               # 1-g >= 1-hi(g) > 0
    s2 = O - gK * gK                            # sin^2 in K
    sg = sqrt_up_K(s2) if khi(s2) > 0 else Fr(0)
    return absg, inv1g, sg, K(1) / (K(2) * (K(1) - gK))


def atom_level(gK):
    """returns Phi_g (full, in the 8 atoms), T6_g, structural majorant M (dict), monomial-wise majorant value info"""
    absg, inv1g, sg, Wg = class_data(gK)
    nui, nuj = nu_poly(ri2_, ei_), nu_poly(rj2_, ej_)
    hh = B_ + nuj * Cp_ + nui * C_ + nui * nuj * gK
    ell = A_ + (nui + nuj) * gK
    u = (ell + hh) * (K(1) / (K(1) - gK))
    Phi = hh * Wg
    up = AT(1)
    for k in range(1, 6):
        up = up * u
        if k >= 2:
            Phi += up * K(QQ(1, 2 * k))
    # structural majorant in R (R^2 = ri^2 + rj^2; each r <= R)
    MA = {1: SQ2 * sg}; MB = {2: Fr(1, 2)}; MC = {1: sg}; MCp = {1: sg}; Mr2 = {2: Fr(1)}; Me = {8: CE}
    Mnu = madd({2: Fr(1, 2), 4: Fr(1, 8), 6: Fr(1, 16)}, Me)
    Mhh = madd(madd(MB, mmul(Mnu, MCp)), madd(mmul(Mnu, MC), mscale(absg, mmul(Mnu, Mnu))))
    Mell = madd(MA, mscale(2 * absg, Mnu))
    Mu = mscale(inv1g, madd(Mell, Mhh))
    Wup = khi(Wg)
    MPhi = mscale(Wup, Mhh)
    upM = {0: Fr(1)}
    for k in range(1, 6):
        upM = mmul(upM, Mu)
        if k >= 2:
            MPhi = madd(MPhi, mscale(Fr(1, 2 * k), upM))
    # monomial-wise majorant of the weight >= 7 part (tighter; for information only)
    bnd = (SQ2 * sg, Fr(1, 2), sg, sg, Fr(1), Fr(1), CE, CE)
    mono7 = Fr(0)
    for m, c in Phi.items():
        w = wdeg(m)
        if w >= 7:
            t = max(khi(c), -klo(c))
            for e_, bb in zip(m, bnd):
                t *= bb ** e_
            mono7 += t * RHO ** (w - 7)
    K_struct = mtail(MPhi, 7, RHO) / RHO ** 7
    return dict(Phi=Phi, T6=wtr(Phi), M=MPhi, K7=K_struct, K7mono=mono7, nmono=len(Phi), nT6=len(wtr(Phi)),
                absg=absg, inv1g=inv1g, sg=sg, W=Wg)


c72, c144 = g[0][1], g[0][2]
CLASSES = {'ring_adj': c72, 'ring_diag': c144, 'pole_ring': Z, 'pole_pole': -O}
CL = {}
for nm, gK in CLASSES.items():
    CL[nm] = atom_level(gK)
    c = CL[nm]
    log(f'class {nm:10s}: g={mp.nstr(kfloat(gK), 8):>12s}  Phi_g {c["nmono"]:6d} monomials, T6_g {c["nT6"]:4d};  '
        f'K7 structural {float(c["K7"]):.4f}, monomial-wise {float(c["K7mono"]):.4f}')


def pair_class(i, j):
    gij = g[i][j]
    for nm, gK in CLASSES.items():
        if gij == gK:
            return nm
    raise ValueError


# ------------------------------------------------------------------ pair level
R4, y1, y2, y3, y4 = ring('y1,y2,y3,y4', K)          # (x_i1, x_i2, x_j1, x_j2)
YV = [y1, y2, y3, y4]


def atoms_xy(i, j):
    """the 6 atoms A,B,C,Cp,ri2,rj2 of pair (i,j) as polynomials in the 4 local coordinates"""
    ti = [y1 * E1[i][m] + y2 * E2[i][m] for m in range(3)]
    tj = [y3 * E1[j][m] + y4 * E2[j][m] for m in range(3)]
    C = sum((P[i][m] * tj[m] for m in range(3)), R4(0))
    Cp = sum((ti[m] * P[j][m] for m in range(3)), R4(0))
    B = sum((ti[m] * tj[m] for m in range(3)), R4(0))
    return [C + Cp, B, C, Cp, y1 ** 2 + y2 ** 2, y3 ** 2 + y4 ** 2]


def compose4(T6, atoms):
    out = R4(0)
    for m, c in T6.items():
        assert m[6] == 0 and m[7] == 0
        term = R4(c)
        for k in range(6):
            if m[k]:
                term *= atoms[k] ** m[k]
        out += term
    return out


def bomb2(p, d):
    """Bombieri norm squared of the homogeneous degree-d polynomial p (element of K)"""
    tot = K(0)
    for m, c in p.items():
        w = 1
        for e in m:
            w *= factorial(e)
        tot += c * c * K(QQ(w, factorial(d)))
    return tot


PAIRS = list(combinations(range(7), 2))
pairs = {}
Psum = R14(0)
for (i, j) in PAIRS:
    nm = pair_class(i, j)
    at = atoms_xy(i, j)
    p = compose4(CL[nm]['T6'], at)
    hom = {d: R4({m: c for m, c in p.items() if sum(m) == d}) for d in range(7)}
    assert not hom[0] and not hom[1]
    b5, b6 = bomb2(hom[5], 5), bomb2(hom[6], 6)
    pairs[(i, j)] = dict(cls=nm, atoms=at, p=p, hom=hom, B5sq=b5, B6sq=b6,
                         B5=sqrt_up_K(b5), B6=sqrt_up_K(b6), nmono=len(p))
    # embed into R14: y1,y2 -> x_{2i}, x_{2i+1}; y3,y4 -> x_{2j}, x_{2j+1}
    sub = [X[2 * i], X[2 * i + 1], X[2 * j], X[2 * j + 1]]
    for m, c in p.items():
        term = R14(c)
        for k in range(4):
            if m[k]:
                term *= sub[k] ** m[k]
        Psum += term
# point terms of the poles: -nu/4 -> r^2/8 + r^4/32 + r^6/64 (checker keeps all three)
Ppoint = R14(0)
for i in (5, 6):
    rr = X[2 * i] ** 2 + X[2 * i + 1] ** 2
    Ppoint += rr * K(QQ(1, 8)) + rr ** 2 * K(QQ(1, 32)) + rr ** 3 * K(QQ(1, 64))
assert Psum + Ppoint == Pmin_checker, 'sum of pair T6 + point terms != checker minorant'
log(f'pair level: 21 pairs, sum + point terms == checker minorant (2188 monomials) [exact]')
for (i, j), d in sorted(pairs.items()):
    log(f'  pair ({i},{j}) {d["cls"]:10s}: {d["nmono"]:3d} monomials; B5 <= {float(d["B5"]):.5f}, B6 <= {float(d["B6"]):.5f}')

# per-pair summation constants: max_i sum_{j != i}
def rowmax(f):
    best = Fr(0)
    for i in range(7):
        s = sum((f(*sorted((i, j))) for j in range(7) if j != i), Fr(0))
        best = max(best, s)
    return best


B5pp = rowmax(lambda i, j: pairs[(i, j)]['B5'])
B6pp = rowmax(lambda i, j: pairs[(i, j)]['B6'])
def dec_up(x, digits=4):
    sc = 10 ** digits
    return Fr(-(-x.numerator * sc // x.denominator), sc)


K7pp = dec_up(rowmax(lambda i, j: CL[pairs[(i, j)]['cls']]['K7']))
K7mono = dec_up(rowmax(lambda i, j: CL[pairs[(i, j)]['cls']]['K7mono']))
for c in CL.values():
    c['K7'], c['K7mono'] = dec_up(c['K7']), dec_up(c['K7mono'])
# global Bombieri (for comparison): degree-5/6 parts of the sum of pairs (no degree-6 point term) and of the checker's
hom14 = lambda p, d: R14({m: c for m, c in p.items() if sum(m) == d})
B5g_sq, B6g_sq = kq(bomb2(hom14(Psum, 5), 5)), kq(bomb2(hom14(Psum, 6), 6))
B6chk_sq = kq(bomb2(hom14(Pmin_checker, 6), 6))
assert B5g_sq == Fr(7801, 800) and B6chk_sq == Fr(2857757, 28800)
B5g, B6g = sqrt_up(B5g_sq), sqrt_up(B6g_sq)
log(f'B5: per-pair rowmax {float(B5pp):.5f} | global {float(B5g):.5f} (sq {B5g_sq})')
log(f'B6: per-pair rowmax {float(B6pp):.5f} | global w/o pole r^6 {float(B6g):.5f} (sq {B6g_sq}) | checker {float(sqrt_up(B6chk_sq)):.5f}')
log(f'K7: per-pair rowmax structural {float(K7pp):.4f} | monomial-wise {float(K7mono):.4f} | checker 70.9738')

# ------------------------------------------------------------------ global level: H, F3, F4 identities
# kernel orthogonality (Gram diagonal) -> Pi_ker = sum k k^T / |k|^2
KG = [[dot(u, v) for v in kern] for u in kern]
assert all(KG[a][b] == Z for a in range(5) for b in range(5) if a != b)
knorm2 = [kq(KG[a][a]) for a in range(5)]
log(f'kernel Gram diagonal: {knorm2}  (rotations 9/2, 9/2, 5; shat 5/2, 5/2)')
R2, sg1, sg2 = ring('sg1,sg2', K)
sform = [sg1 * s1[m] + sg2 * s2[m] for m in range(14)]


def compose14(p, forms, Rout):
    out = Rout(0)
    for m, c in p.items():
        term = Rout(c)
        for k, e in enumerate(m):
            if e:
                term *= forms[k] ** e
        out += term
    return out


# gamma2 = ||F3||_B
G2sq = kq(bomb2(F3, 3))
G2 = sqrt_up(G2sq)
log(f'gamma2^2 = ||F3||_B^2 = {G2sq} -> gamma2 <= {float(G2):.7f}')
# ||F4||_B
C04sq = kq(bomb2(F4, 4))
assert C04sq == Fr(35261, 3840)
C04 = sqrt_up(C04sq)
log(f'||F4||_B^2 = {C04sq} -> {float(C04):.7f}')
# A_alpha = (1/2) D^2 F3 (shat_alpha): entries (1/2) sum_r d^3F3/dp dq dr shat[r]
def hess_at(F, v):
    """(1/2) D^2 F at the vector v (v: list of K), as 14x14 K matrix; F cubic -> linear in v"""
    M = [[K(0)] * 14 for _ in range(14)]
    for p_ in range(14):
        dp = F.diff(X[p_])
        for q_ in range(p_, 14):
            dpq = dp.diff(X[q_])          # linear form in x for cubic F
            val = K(0)
            for m, c in dpq.items():
                r_ = [k for k, e in enumerate(m) if e]
                assert sum(m) == 1
                val += c * v[r_[0]]
            M[p_][q_] = M[q_][p_] = val * K(QQ(1, 2))
    return M


A1, A2 = hess_at(F3, s1), hess_at(F3, s2)
# sanity: w^T A_al w = 3 C(shat_al, w, w): check <Gam m, .> consistency:  d/dsg_al of F3(sg shat + z)|... skip; check symmetry only
Af = [[[kfloat(x) for x in row] for row in A] for A in (A1, A2)]
Kf = mp.matrix([[kfloat(kern[b][i]) for b in range(5)] for i in range(14)])
PiKf = Kf * (Kf.T * Kf) ** -1 * Kf.T
PiWf = mp.eye(14) - PiKf
opW = [max(abs(e) for e in mp.eigsy(PiWf * mp.matrix(A) * PiWf)[0]) for A in Af]
log(f'float op norms of A_alpha on W: {mp.nstr(opW[0], 10)}, {mp.nstr(opW[1], 10)}  (checker: 3 sqrt(5/2) 0.27428359 = {mp.nstr(3 * mp.sqrt(mp.mpf(5) / 2) * mp.mpf("0.27428359"), 10)})')

# ---- gamma1 certificate (exact mirror of the Lean check), 4 matrices  c I -/+ A_al + lam K K^T
Z4 = (Fr(0),) * 4


def kmul(x, y):
    p = [Fr(0)] * 7
    for i in range(4):
        for j in range(4):
            p[i + j] += x[i] * y[j]
    return (p[0] - 80 * p[4] - 1600 * p[6], p[1] - 80 * p[5], p[2] + 20 * p[4] + 320 * p[6], p[3] + 20 * p[5])


kadd = lambda x, y: tuple(a + b for a, b in zip(x, y))
ksub = lambda x, y: tuple(a - b for a, b in zip(x, y))
ksmul = lambda q, x: tuple(q * a for a in x)
kofq = lambda q: (Fr(q), Fr(0), Fr(0), Fr(0))
kaub = lambda x: max(kel_hi(x), -kel_lo(x))
kevf = lambda x: sum(mp.mpf(c.numerator) / c.denominator * ALPHA ** k for k, c in enumerate(x))

Kd = [[tuple(kcoeffs(kern[b][i])) for b in range(5)] for i in range(14)]
Ad = [[[tuple(kcoeffs(z)) for z in row] for row in A] for A in (A1, A2)]


def pen(i, j):
    acc = Z4
    for b in range(5):
        acc = kadd(acc, kmul(Kd[i][b], Kd[j][b]))
    return acc


PEN = [[pen(i, j) for j in range(14)] for i in range(14)]
CG1 = Fr(1305, 1000)          # c: op-norm bound for A_alpha on W (float 1.30104125); margin absorbs the finite penalty
LAM = Fr(100)                  # penalty weight (lambda_min(c I -/+ A + lam K K^T) = 2.8e-3 at lam = 100)
DELTA, BITS = Fr(1, 20000), 40


def cert_matrix(al, sgn):
    return [[kadd(ksub(kofq(CG1 if i == j else 0), ksmul(Fr(sgn), Ad[al][i][j])), ksmul(LAM, PEN[i][j]))
             for j in range(14)] for i in range(14)]


def ldl_round(Mex):
    N = len(Mex)
    Mf = mp.matrix(N, N)
    for i in range(N):
        for j in range(N):
            Mf[i, j] = kevf(Mex[i][j])
    lmin = min(mp.eigsy(Mf)[0])
    A = Mf - mp.mpf(DELTA.numerator) / DELTA.denominator * mp.eye(N)
    Lf = mp.matrix(N, N); Df = [mp.mpf(0)] * N
    for k in range(N):
        Df[k] = A[k, k] - sum(Lf[k, q] ** 2 * Df[q] for q in range(k))
        Lf[k, k] = 1
        for i in range(k + 1, N):
            Lf[i, k] = (A[i, k] - sum(Lf[i, q] * Lf[k, q] * Df[q] for q in range(k))) / Df[k]
    S = 2 ** BITS
    rnd = lambda x: Fr(int(mp.nint(x * S)), S)
    Dd = [rnd(Df[q]) for q in range(N)]
    Ld = [[(Fr(1) if i == q else (rnd(Lf[i, q]) if i > q else Fr(0))) for i in range(N)] for q in range(N)]
    ldl = lambda i, j: sum((Dd[q] * Ld[q][i] * Ld[q][j] for q in range(N)), Fr(0))
    E = [[ksub(Mex[i][j], kofq(ldl(i, j))) for j in range(N)] for i in range(N)]
    ok_d = all(d >= 0 for d in Dd)
    ok_s = all(E[i][j] == E[j][i] for i in range(N) for j in range(N))
    slack = [kel_lo(E[i][i]) - sum((kaub(E[i][j]) for j in range(N) if j != i), Fr(0)) for i in range(N)]
    return dict(lmin=lmin, Dd=Dd, Ld=Ld, ok=ok_d and ok_s and min(slack) >= 0, minslack=min(slack), minpiv=min(Df))


G1CERT = {}
for al in (0, 1):
    for sgn in (1, -1):
        r = ldl_round(cert_matrix(al, sgn))
        G1CERT[(al, sgn)] = r
        log(f'gamma1 cert alpha={al + 1} sign={sgn:+d}: float lmin {mp.nstr(r["lmin"], 4)}, min pivot {mp.nstr(r["minpiv"], 4)}, '
            f'exact mirror {"OK" if r["ok"] else "FAIL"}, min dd slack {float(r["minslack"]):.2e}')
assert all(r['ok'] for r in G1CERT.values())
# |3C(s,w,w)| <= c (|sg1|+|sg2|) b^2 <= c sqrt2 |sg| b^2 = c sqrt2 sqrt(2/5) a b^2 = (2c/sqrt5) a b^2  =: 3 gamma1 a b^2
G1x3 = sqrt_up(4 * CG1 ** 2 / 5, 9)         # 3 gamma1 >= 2c/sqrt5
G1 = G1x3 / 3
log(f'gamma1: c = {CG1} -> 3 gamma1 <= {float(G1x3):.7f}, gamma1 <= {float(G1):.7f} (checker 0.387896)')

# ---- delta1: g(sg) = grad F4 at s;  gt = g - Pi_ker g;  |gt|^2 = c6 |sg|^6
gpol = [compose14(F4.diff(X[m]), sform, R2) for m in range(14)]
proj = [sum((kern[b][m] * gpol[m] for m in range(14)), R2(0)) * K(QQ(1) / QQ(knorm2[b].numerator, knorm2[b].denominator))
        for b in range(5)]
gt = [gpol[m] - sum((proj[b] * kern[b][m] for b in range(5)), R2(0)) for m in range(14)]
gS = [gpol[m] - sum((proj[b] * kern[b][m] for b in (3, 4)), R2(0)) for m in range(14)]
n6 = (sg1 ** 2 + sg2 ** 2) ** 3
gt2 = sum((x * x for x in gt), R2(0))
gS2 = sum((x * x for x in gS), R2(0))

def is_c_times(p2, n, name):
    """p2 == c * n for a rational c ?  returns c (Fraction) or raises"""
    # pick a monomial of n, read off c, check
    m0, c0 = next(iter(n.items()))
    c = p2.coeff(R2({m0: K(1)}) ) if False else None
    cK = p2[m0] / c0 if m0 in p2 else K(0)
    assert p2 == n * cK, f'{name}: not a multiple of |sg|^k'
    return kq(cK)


c6_ker = is_c_times(gt2, n6, '|g - Pi_ker g|^2')
c6_S = is_c_times(gS2, n6, '|g - Pi_S g|^2')
# 4 delta1 a^3 b >= |<gt, w>| <= sqrt(c6) |sg|^3 b = sqrt(c6) (2/5)^{3/2} a^3 b
D1x4 = sqrt_up(c6_ker * Fr(8, 125), 9)
D1 = D1x4 / 4
log(f'delta1: |g - Pi_ker g|^2 = {c6_ker} |sg|^6, |g - Pi_S g|^2 = {c6_S} |sg|^6 -> 4 delta1 <= {float(D1x4):.7f}, '
    f'delta1 <= {float(D1):.7f} (checker 0.147314; design S-only {float(sqrt_up(c6_S * Fr(8, 125)) / 4):.6f})')

# ---- c_q pieces
# B(sg) = (1/2) D^2F4 at s (quadratic in sg): entries (1/2) d^2/dx_p dx_q F4 composed with s
Bpq = {}
c22sum = R2(0)
for p_ in range(14):
    dp = F4.diff(X[p_])
    for q_ in range(p_, 14):
        e = compose14(dp.diff(X[q_]), sform, R2) * K(QQ(1, 2))
        c22sum += e * e * (1 if p_ == q_ else 2)
n4 = (sg1 ** 2 + sg2 ** 2) ** 2
c22 = is_c_times(c22sum, n4, '||B(sg)||_F^2')
# T_sg(w) = 4 D(s,w,w,w) = <s, grad F4(w)> = sum_r s_r dF4/dx_r (w): cubic form in w with coefficients linear in sg
Tpol = R14(0)
# represent as polynomial in x with coefficients in R2: build dict monomial -> R2 element
Tcoef = {}
for r_ in range(14):
    if s1[r_] == Z and s2[r_] == Z:
        continue
    dr = F4.diff(X[r_])
    lin = sg1 * s1[r_] + sg2 * s2[r_]
    for m, c in dr.items():
        Tcoef[m] = Tcoef.get(m, R2(0)) + lin * c
c13sum = R2(0)
for m, cpol in Tcoef.items():
    w = 1
    for e_ in m:
        w *= factorial(e_)
    c13sum += cpol * cpol * K(QQ(w, factorial(3)))
n2 = sg1 ** 2 + sg2 ** 2
c13 = is_c_times(c13sum, n2, '||T_sg||_B^2')
# convert |sg| -> a = |s| = sqrt(5/2)|sg|:  |sg|^2 = (2/5) a^2
CQ22 = sqrt_up(c22 * Fr(4, 25), 9)          # coefficient of a^2 b^2
CQ13 = sqrt_up(c13 * Fr(2, 5), 9)           # coefficient of a b^3
CQ04 = C04                                   # coefficient of b^4
# c_q >= lambda_max [[CQ22, CQ13/2],[CQ13/2, CQ04]]
def lam_max_up(a, b, c, digits=6):
    disc = (a - c) ** 2 + 4 * b * b
    lm = (a + c + sqrt_up(disc, 12)) / 2
    s = 10 ** digits
    return Fr(-(-lm.numerator * s // lm.denominator), s)


CQ = lam_max_up(CQ22, CQ13 / 2, CQ04)
assert CQ >= CQ22 and CQ >= CQ04 and (CQ - CQ22) * (CQ - CQ04) >= (CQ13 / 2) ** 2
log(f'c_q: ||B||_F^2 = {c22}|sg|^4, ||T||_B^2 = {c13}|sg|^2, ||F4||_B^2 = {C04sq};  a^2b^2 {float(CQ22):.6f}, '
    f'ab^3 {float(CQ13):.6f}, b^4 {float(CQ04):.6f} -> c_q <= {float(CQ):.6f} (checker 4.203074)')

# ------------------------------------------------------------------ closure of L' (A = 1, as LocalScalar.scalar_param)
EPS, QP = Fr(1, 16), Fr(29, 500)


def closure(rho, B5, B6, K7, A=Fr(1)):
    KK = B5 + B6 * rho + K7 * rho ** 2
    bb = (G1x3 + G2) * rho + CQ * rho ** 2 + 2 * KK * rho ** 3
    cw = EPS - bb - 2 * D1 * rho / A
    cs = QP - KK * rho - 2 * D1 * rho * A
    return KK, cw, cs


ROUTES = {'per-pair (B5,B6 rowmax; K7 structural rowmax)': (B5pp, B6pp, K7pp),
          'per-pair, K7 monomial-wise (info)': (B5pp, B6pp, K7mono),
          'global B5,B6 (pairs only) + per-pair K7': (B5g, B6g, K7pp)}
RESULTS = {}
for nm, (b5, b6, k7) in ROUTES.items():
    KK, cw, cs = closure(RHO, b5, b6, k7)
    RESULTS[nm] = dict(K=KK, cw=cw, cs=cs)
    log(f'closure rho=1/100, {nm}: K <= {float(KK):.5f};  |w|^2 coeff {float(cw):.6f}, |s|^4 coeff {float(cs):.6f}  '
        f'{"CLOSES" if cw > 0 and cs > 0 else "FAILS"}')
# K7 depends on rho (mildly); recompute the structural K7 at other rho for the rho-scan
def K7_at(rho):
    return dec_up(rowmax(lambda i, j: mtail(CL[pairs[(i, j)]['cls']]['M'], 7, rho) / rho ** 7))


best = None
for k in range(50, 400):
    rho = Fr(k, 10000)
    KK, cw, cs = closure(rho, B5pp, B6pp, K7_at(rho))
    if cw > 0 and cs > 0:
        best = rho
rho_max = best
KK, cw, cs = closure(rho_max, B5pp, B6pp, K7_at(rho_max))
log(f'largest closing rho (per-pair route, A=1, step 1e-4): {rho_max} = {float(rho_max):.4f}  (cw {float(cw):.5f}, cs {float(cs):.5f});  '
    f'handoff needs rho >= sqrt7/300 = {float(mp.sqrt(7) / 300):.5f}')
# optimise A at rho = 1/100 for the per-pair route (balanced margin), information only
bestA = None
for k in range(1, 400):
    A = Fr(k, 100)
    KK, cw, cs = closure(RHO, B5pp, B6pp, K7pp, A)
    m = min(cw, cs)
    if bestA is None or m > bestA[0]:
        bestA = (m, A, cw, cs)
log(f'A-optimised (info): A = {bestA[1]}, cw {float(bestA[2]):.6f}, cs {float(bestA[3]):.6f}')

# ------------------------------------------------------------------ export
def kser(z):
    return [str(c) for c in kcoeffs(z)]


def pser(p):
    return [[list(m), kser(c)] for m, c in sorted(p.items())]


out = dict(
    rho=str(RHO), alpha_box=[str(LO), str(HI)],
    constants=dict(G1x3=str(G1x3), G1=str(G1), c_op=str(CG1), G2=str(G2), G2sq=str(G2sq), D1=str(D1), D1x4=str(D1x4),
                   c6_ker=str(c6_ker), c6_S=str(c6_S), CQ=str(CQ), CQ22=str(CQ22), CQ13=str(CQ13), CQ04=str(CQ04),
                   c22=str(c22), c13=str(c13), C04sq=str(C04sq),
                   B5pp=str(B5pp), B6pp=str(B6pp), K7pp=str(K7pp), K7mono=str(K7mono), B5g=str(B5g), B6g=str(B6g),
                   B5g_sq=str(B5g_sq), B6g_sq=str(B6g_sq), CE=str(CE), SQ2=str(SQ2)),
    results={nm: {k: str(v) for k, v in r.items()} for nm, r in RESULTS.items()},
    rho_max=str(rho_max),
    classes={nm: dict(g=kser(CLASSES[nm]), T6=pser(c['T6']), nPhi=c['nmono'], K7=str(c['K7']), K7mono=str(c['K7mono']),
                      M=[[k, str(v)] for k, v in sorted(c['M'].items())], absg=str(c['absg']), inv1g=str(c['inv1g']),
                      sg=str(c['sg']), W=kser(c['W'])) for nm, c in CL.items()},
    pairs={f'{i},{j}': dict(cls=d['cls'], atoms=[pser(a) for a in d['atoms']], p=pser(d['p']),
                            B5sq=kser(d['B5sq']), B6sq=kser(d['B6sq']), B5=str(d['B5']), B6=str(d['B6']))
           for (i, j), d in pairs.items()},
    gamma1_cert={f'{al + 1},{sgn:+d}': dict(D=[str(x) for x in r['Dd']], L=[[str(x) for x in row] for row in r['Ld']])
                 for (al, sgn), r in G1CERT.items()},
    A1=[[kser(z) for z in row] for row in A1], A2=[[kser(z) for z in row] for row in A2],
    Kd=[[kser(kern[b][i]) for b in range(5)] for i in range(14)],
    gamma1_params=dict(c=str(CG1), lam=str(LAM), delta=str(DELTA), bits=BITS),
)
json.dump(out, open(os.path.join(HERE, 'local_pre_out.json'), 'w'))
log(f'wrote local_pre_out.json')
