"""Global level (T1/T5–T8) of Lemma L': exact data for the Lean modules LocalPairData / LocalGlobData, and a Python
mirror of every kernel check those modules ask `decide` to perform.

Contents (all exact over K = Q(alpha)):
  frames     P, E1, E2 (Kel), classes and W of the 21 pairs, kernel vectors Kd (14x5), Gram diag;
  pairs      p_ij split into homogeneous parts p_ij,d (d = 2..6) in the 4 local coordinates (sorted lex);
             the six atom polynomials as Lean computes them from the frames (checked against local_pre);
             Bombieri data D5_ij, D6_ij (monomial, constant coefficient, weight d!/m!), squares B5sq, B6sq;
  global     F_d = sum_pairs embed(p_ij,d) + poles_d (d = 2,3,4) as 14-variable lists (checked == checker);
             the (sigma, w) expansion G_d = F_d(sigma1 s1 + sigma2 s2 + w) in 16 variables, split by sigma-degree;
             structured forms of each piece: qfPoly(H)/2, sigma_al qfPoly(A_al), <Gamma m, w>, DP data with
             2-variable coefficient polynomials for the F4 pieces, projected g~ and the kernel components q_b;
  bombieri   bombSq of every DP == c * (sigma1^2 + sigma2^2)^k  (c exact), rational upper bounds.
Every `eqPoly`/`wsub`/`check` the Lean files decide is re-run here with the mirror (sp_mirror.py); kernel op counts
are printed.  usage: nice -n 19 python3 lean/gen/local_global.py   (writes lean/gen/local_global_out.json)
"""
import os, sys, json, time
from fractions import Fraction as Fr
from itertools import combinations
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from local_exact import build, kcoeffs, K, AL
from sympy import QQ
from sympy.polys.rings import ring
import sp_mirror as SP

HERE = os.path.dirname(os.path.abspath(__file__))
T0 = time.time()
J = json.load(open(os.path.join(HERE, 'local_pre_out.json')))


def log(msg):
    print(f'[{time.time() - T0:6.1f}s] {msg}', flush=True)


def kc(z):
    return tuple(kcoeffs(z))


def kq(z):
    c = kc(z)
    assert c[1] == 0 and c[2] == 0 and c[3] == 0, c
    return c[0]


LO, HI = Fr(J['alpha_box'][0]), Fr(J['alpha_box'][1])


def kel_hi(c):
    mx = lambda a, b: b if a <= b else a
    return c[0] + mx(c[1] * LO, c[1] * HI) + mx(c[2] * LO ** 2, c[2] * HI ** 2) + mx(c[3] * LO ** 3, c[3] * HI ** 3)


def sqrt_up(q, digits=9):
    from math import isqrt
    q = Fr(q); s = 10 ** digits
    r = Fr(isqrt(int(q * s * s)) + 1, s)
    assert r * r >= q
    return r


# ---------------------------------------------------------------- exact data
log('build(DMAX=6) ...')
D = build(DMAX=6)
P, E1, E2, g, W, mu = D['P'], D['E1'], D['E2'], D['g'], D['W'], D['mu']
R14, X = D['R14'], D['X']
kern, s1, s2, H, Gam, F3, F4, Pmin = D['kern'], D['s1'], D['s2'], D['H'], D['Gam'], D['F3'], D['F4'], D['Pmin']
Z, O = K(0), K(1)
dot = lambda u, v: sum((x * y for x, y in zip(u, v)), K(0))
hom = lambda p, d: R14({m: c for m, c in p.items() if sum(m) == d})
F2 = hom(Pmin, 2)
assert hom(Pmin, 3) == F3 and hom(Pmin, 4) == F4

# frames: orthonormal, P unit
for i in range(7):
    fr = [P[i], E1[i], E2[i]]
    for a in range(3):
        for b in range(3):
            assert dot(fr[a], fr[b]) == (O if a == b else Z)
            # completeness: sum_v v_a v_b = delta_ab
            assert sum((v[a] * v[b] for v in fr), Z) == (O if a == b else Z)
# criticality: sum_{j != i} W_ij P_j = mu_i P_i ; mu ring = 0, pole = -1/4
for i in range(7):
    lhs = [sum((W[i][j] * P[j][m] for j in range(7) if j != i), Z) for m in range(3)]
    assert lhs == [mu[i] * P[i][m] for m in range(3)]
    assert mu[i] == (Z if i < 5 else -K(QQ(1, 4)))
# rotation fields = first three kernel vectors: r_c[2i+k] = <e_c x P_i, E_k,i>
def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]
for c in range(3):
    ec = [O if m == c else Z for m in range(3)]
    for i in range(7):
        v = cross(ec, P[i])
        assert kern[c][2 * i] == dot(v, E1[i]) and kern[c][2 * i + 1] == dot(v, E2[i])
        # v = r[2i] E1 + r[2i+1] E2 (v is tangent)
        assert v == [kern[c][2 * i] * E1[i][m] + kern[c][2 * i + 1] * E2[i][m] for m in range(3)]
# shat: s1, s2 = kern[3], kern[4]; Gram
KG = [[dot(u, v) for v in kern] for u in kern]
gram = [kq(KG[b][b]) for b in range(5)]
assert all(KG[a][b] == Z for a in range(5) for b in range(5) if a != b)
assert gram == [Fr(9, 2), Fr(9, 2), Fr(5), Fr(5, 2), Fr(5, 2)]
log('frames, criticality, rotation fields, Gram: OK')

CLASSES = {'ring_adj': g[0][1], 'ring_diag': g[0][2], 'pole_ring': Z, 'pole_pole': -O}
SHORT = {'ring_adj': 'adj', 'ring_diag': 'diag', 'pole_ring': 'pole', 'pole_pole': 'pp'}
PAIRS = list(combinations(range(7), 2))


def pair_class(i, j):
    for nm, gK in CLASSES.items():
        if g[i][j] == gK:
            return nm
    raise ValueError

# ---------------------------------------------------------------- pairs
R4, y1, y2, y3, y4 = ring('y1,y2,y3,y4', K)
pairs_out = {}
dotK = lambda u, v: kc(dot(u, v))
Fsum = {d: [] for d in (2, 3, 4)}     # kernel-mirrored sums of embedded parts
SP.reset_ops()


def embed(i, j, p):
    """4-var Poly -> 14-var Poly (lex order preserved since 2i < 2j)"""
    out = []
    for m, c in p:
        mm = [0] * 14
        mm[2 * i], mm[2 * i + 1], mm[2 * j], mm[2 * j + 1] = m
        out.append((mm, c))
    out.sort(key=lambda t: t[0])
    return out


def bomb_data(p, d, nvars):
    """DP entries (mono, weight d!/m!) and Bombieri square (K) of a homogeneous degree-d Poly"""
    tot = K(0)
    ent = []
    for m, c in p:
        w = Fr(factorial(d))
        for e in m:
            w /= factorial(e)
        ent.append((m, str(w)))
        # c as K element
        cK = sum((K(QQ(x.numerator, x.denominator)) * AL ** k for k, x in enumerate(c)), K(0))
        tot += cK * cK * K(QQ(1) / QQ(w.numerator, w.denominator))
    return ent, tot


for (i, j) in PAIRS:
    pd = J['pairs'][f'{i},{j}']
    p = [(m, tuple(Fr(x) for x in c)) for m, c in pd['p']]
    p.sort(key=lambda t: t[0])
    parts = {d: [(m, c) for m, c in p if sum(m) == d] for d in range(2, 7)}
    assert sum(len(v) for v in parts.values()) == len(p)
    # atoms as Lean computes them: A = [x4: P_i.E2_j, x3: P_i.E1_j, x2: E2_i.P_j, x1: E1_i.P_j]
    atA = [([0, 0, 0, 1], dotK(P[i], E2[j])), ([0, 0, 1, 0], dotK(P[i], E1[j])),
           ([0, 1, 0, 0], dotK(E2[i], P[j])), ([1, 0, 0, 0], dotK(E1[i], P[j]))]
    atB = [([0, 1, 0, 1], dotK(E2[i], E2[j])), ([0, 1, 1, 0], dotK(E2[i], E1[j])),
           ([1, 0, 0, 1], dotK(E1[i], E2[j])), ([1, 0, 1, 0], dotK(E1[i], E1[j]))]
    atC = [([0, 0, 0, 1], dotK(P[i], E2[j])), ([0, 0, 1, 0], dotK(P[i], E1[j]))]
    atCp = [([0, 1, 0, 0], dotK(E2[i], P[j])), ([1, 0, 0, 0], dotK(E1[i], P[j]))]
    atRi = [([0, 2, 0, 0], SP.KONE), ([2, 0, 0, 0], SP.KONE)]
    atRj = [([0, 0, 0, 2], SP.KONE), ([0, 0, 2, 0], SP.KONE)]
    # check against local_pre's atoms (drop zeros)
    for mine, ref in zip((atA, atB, atC, atCp, atRi, atRj), pd['atoms']):
        refl = sorted(((m, tuple(Fr(x) for x in c)) for m, c in ref), key=lambda t: t[0])
        assert [t for t in mine if t[1] != SP.KZ] == refl, (i, j)
    # kernel mirror of the pair identity: compose6 T6 atoms == merge of parts
    nm = pair_class(i, j)
    T6 = [(tuple(m[:6]), tuple(Fr(x) for x in c)) for m, c in J['classes'][nm]['T6']]
    ops0 = dict(SP.OPS)
    comp = []
    for m6, c in reversed(T6):
        term = SP.ONE
        for e, at in zip(reversed(m6), reversed((atA, atB, atC, atCp, atRi, atRj))):
            term = SP.mul(SP.pw(at, e), term)
        comp = SP.merge(SP.smul(c, term), comp)
    pmerged = []
    for d in (6, 5, 4, 3, 2):
        pmerged = SP.merge(parts[d], pmerged)
    assert SP.eq_poly(comp, pmerged), f'pair {(i, j)} identity FAILS in mirror'
    kops = SP.OPS['kmul'] - ops0['kmul']
    # Bombieri data for d = 5, 6
    ent5, b5 = bomb_data(parts[5], 5, 4)
    ent6, b6 = bomb_data(parts[6], 6, 4)
    assert kc(b5) == tuple(Fr(x) for x in pd['B5sq']) and kc(b6) == tuple(Fr(x) for x in pd['B6sq'])
    B5, B6 = Fr(pd['B5']), Fr(pd['B6'])
    assert B5 ** 2 >= kel_hi(kc(b5)) and B6 ** 2 >= kel_hi(kc(b6))
    for d in (2, 3, 4):
        Fsum[d] = SP.merge(embed(i, j, parts[d]), Fsum[d])
    pairs_out[f'{i},{j}'] = dict(cls=nm, W=kc(W[i][j]), g=kc(g[i][j]),
                                 parts={d: [[m, [str(x) for x in c]] for m, c in parts[d]] for d in range(2, 7)},
                                 w5=[w for _, w in ent5], w6=[w for _, w in ent6],
                                 B5sq=[str(x) for x in kc(b5)], B6sq=[str(x) for x in kc(b6)], B5=str(B5), B6=str(B6),
                                 kops=kops)
    log(f'pair {(i, j)} {nm:10s}: identity mirror OK ({kops} Kel mults); parts sizes '
        f'{[len(parts[d]) for d in range(2, 7)]}; B5 {float(B5):.5f} B6 {float(B6):.5f}')

# pole point terms and the global lists F2, F3, F4
def mono14(**kw):
    m = [0] * 14
    for k, v in kw.items():
        m[int(k[1:])] = v
    return m


poles2 = sorted([(mono14(x10=2), SP.kofq(Fr(1, 8))), (mono14(x11=2), SP.kofq(Fr(1, 8))),
                 (mono14(x12=2), SP.kofq(Fr(1, 8))), (mono14(x13=2), SP.kofq(Fr(1, 8)))], key=lambda t: t[0])
poles4 = []
for a, b in ((10, 11), (12, 13)):
    ma, mb = [0] * 14, [0] * 14
    ma[a] = 4; mb[b] = 4
    mab = [0] * 14; mab[a] = 2; mab[b] = 2
    poles4 += [(ma, SP.kofq(Fr(1, 32))), (mb, SP.kofq(Fr(1, 32))), (mab, SP.kofq(Fr(1, 16)))]
poles4.sort(key=lambda t: t[0])
Fl = {2: SP.from_sympy(F2, kcoeffs), 3: SP.from_sympy(F3, kcoeffs), 4: SP.from_sympy(F4, kcoeffs)}
assert SP.eq_poly(SP.merge(Fsum[2], poles2), Fl[2])
assert SP.eq_poly(Fsum[3], Fl[3])
assert SP.eq_poly(SP.merge(Fsum[4], poles4), Fl[4])
log(f'global: sum of embedded pair parts (+ poles) == F2 ({len(Fl[2])}), F3 ({len(Fl[3])}), F4 ({len(Fl[4])}) [mirror]')

# F2 == (1/2) qfPoly(H)
Hd = lambda p, q: kc(H[p][q])
SP.reset_ops()
qfH = SP.qf_poly(Hd, 14, 0, 14)
assert SP.eq_poly(Fl[2], SP.smul(SP.kofq(Fr(1, 2)), qfH))
log(f'F2 == 1/2 x^T H x [mirror, {SP.OPS["kmul"]} kmul {SP.OPS["cmp"]} cmp]')

# ---------------------------------------------------------------- (sigma, w) expansion in 16 variables
R16, *ZV = ring(','.join(['sg1', 'sg2'] + [f'w{p}' for p in range(14)]), K)
sg1, sg2 = ZV[0], ZV[1]
WV = ZV[2:]
forms_sym = [sg1 * s1[p] + sg2 * s2[p] + WV[p] for p in range(14)]
forms_lean = [[] for _ in range(14)]
for p in range(14):
    f = []
    if kc(s1[p]) != SP.KZ:
        f.append((SP.unit(16, 0), kc(s1[p])))
    if kc(s2[p]) != SP.KZ:
        f.append((SP.unit(16, 1), kc(s2[p])))
    f.append((SP.unit(16, 2 + p), SP.KONE))
    forms_lean[p] = f            # already lex sorted: unit 0 < unit 1 < unit (2+p)


def compose_sym(F):
    out = R16(0)
    for m, c in F.items():
        term = R16(c)
        for k, e in enumerate(m):
            if e:
                term *= forms_sym[k] ** e
        out += term
    return out


def sigdeg(m):
    return m[0] + m[1]


G = {}
Gp = {}
for d in (2, 3, 4):
    Gd = compose_sym({2: F2, 3: F3, 4: F4}[d])
    G[d] = SP.from_sympy(Gd, kcoeffs)
    Gp[d] = {k: [(m, c) for m, c in G[d] if sigdeg(m) == k] for k in range(d + 1)}
    # kernel mirror of compose (op count) for d = 2, 3 (F4 is chunked below)
    SP.reset_ops()
    comp = SP.compose(Fl[d], lambda p: forms_lean[p])
    assert SP.eq_poly(comp, G[d])
    merged = []
    for k in reversed(range(d + 1)):
        merged = SP.merge(Gp[d][k], merged)
    assert SP.eq_poly(comp, merged)
    log(f'expansion G{d}: {len(G[d])} monomials, sigma-degree sizes {[len(Gp[d][k]) for k in range(d + 1)]}; '
        f'compose mirror {SP.OPS["kmul"]} kmul, {SP.OPS["cmp"]} cmp')

# F4 chunks for the kernel: split F4 list into NCH consecutive chunks; export compose of each
NCH = 4
chunks = [Fl[4][k::NCH] for k in range(NCH)]      # interleaved so that chunk sizes/costs balance
chunks = [sorted(c, key=lambda t: t[0]) for c in chunks]
Gchunks = []
for k, ch in enumerate(chunks):
    SP.reset_ops()
    gc = SP.compose(ch, lambda p: forms_lean[p])
    Gchunks.append(gc)
    log(f'  F4 chunk {k}: {len(ch)} monomials -> {len(gc)}; compose mirror {SP.OPS["kmul"]} kmul, {SP.OPS["cmp"]} cmp')
acc = []
for gc in reversed(Gchunks):
    acc = SP.merge(gc, acc)
assert SP.eq_poly(acc, G[4])
allch = []
for ch in reversed(chunks):
    allch = SP.merge(ch, allch)
assert SP.eq_poly(allch, Fl[4])

# ---- structured pieces
# F2: sigma^0 = 1/2 qfPoly(H) shifted (off 2); sigma^1, sigma^2 empty
SP.reset_ops()
assert SP.eq_poly(Gp[2][0], SP.smul(SP.kofq(Fr(1, 2)), SP.qf_poly(Hd, 16, 2, 14)))
assert Gp[2][1] == [] and Gp[2][2] == []
# F3: sigma^0 = shift F3; sigma^1 = sg1 qf(A1) + sg2 qf(A2); sigma^2 = <Gamma m, w>; sigma^3 = 0
A1 = [[tuple(Fr(x) for x in z) for z in row] for row in J['A1']]
A2 = [[tuple(Fr(x) for x in z) for z in row] for row in J['A2']]
shift2 = lambda p: [([0, 0] + m, c) for m, c in p]
assert SP.eq_poly(Gp[3][0], shift2(Fl[3]))
q1 = SP.mul([(SP.unit(16, 0), SP.KONE)], SP.qf_poly(lambda p, q: A1[p][q], 16, 2, 14))
q2 = SP.mul([(SP.unit(16, 1), SP.KONE)], SP.qf_poly(lambda p, q: A2[p][q], 16, 2, 14))
assert SP.eq_poly(Gp[3][1], SP.merge(q1, q2))
Gd_ = [[tuple(Fr(x) for x in kc(z)) for z in row] for row in Gam]
msig = [[2, 0], [1, 1], [0, 2]]
gam = []
for k in range(3):
    mk = [msig[k][0], msig[k][1]] + [0] * 14
    gam = SP.merge(gam, SP.mul([(mk, SP.KONE)], SP.lin_poly(lambda p, k=k: Gd_[p][k], 16, 2, 14)))
assert SP.eq_poly(Gp[3][2], gam)
assert Gp[3][3] == []
log(f'pieces of G2, G3 match the structured forms (H, A1, A2, Gamma) [mirror, {SP.OPS["kmul"]} kmul]')

# F4 pieces as DP data: entries (mono16 (w part), coefficient poly in sg1, sg2 (vars 0,1), weight d!/m!)
def dp_of_piece(piece, d):
    """group a 16-var piece of w-degree d by its w-monomial; coefficient polys in (sg1, sg2)"""
    groups = {}
    for m, c in piece:
        wm = tuple([0, 0] + m[2:])
        groups.setdefault(wm, []).append(([m[0], m[1]] if m[0] + m[1] > 0 else [], c))
    ent = []
    for wm in sorted(groups):
        coef = sorted(groups[wm], key=lambda t: t[0])
        w = Fr(factorial(d))
        for e in wm[2:]:
            w /= factorial(e)
        ent.append((list(wm), coef, w))
    return ent


def flat_dp(ent):
    acc = []
    for wm, coef, w in reversed(ent):
        acc = SP.merge(SP.mul(coef, [(wm, SP.KONE)]), acc)
    return acc


def bomb_sq(ent):
    acc = []
    for wm, coef, w in reversed(ent):
        acc = SP.merge(SP.smul(SP.kofq(1 / w), SP.mul(coef, coef)), acc)
    return acc


def norm_pow(k, n=2):
    """(sg1^2 + sg2^2)^k as a Poly with monomials of length n (2 for coefficient polys, 16 for expansion pieces)"""
    if k == 0:
        return SP.ONE
    n2 = [([2, 0] + [0] * (n - 2), SP.KONE), ([0, 2] + [0] * (n - 2), SP.KONE)]
    return SP.pw(n2, k)


def is_c_times(p, base):
    """p == c * base for a Kel c?  return c"""
    if not p:
        return SP.KZ
    m0, c0 = base[0]
    for m, c in p:
        if m == m0:
            cK = c
            break
    else:
        raise ValueError
    assert c0 == SP.KONE
    assert SP.eq_poly(p, SP.smul(cK, base)), 'not a multiple'
    return cK


DP = {}
# F3(w): sigma^0 piece of G3, degree 3, constant coefficients
DP['F3w'] = dp_of_piece(Gp[3][0], 3)
DP['F4w'] = dp_of_piece(Gp[4][0], 4)
DP['F4s1'] = dp_of_piece(Gp[4][1], 3)
DP['F4s2'] = dp_of_piece(Gp[4][2], 2)
# sigma^3 piece: <g(sigma), w> with g_m cubic; projected version g~ = g - Pi_ker g
g3 = dp_of_piece(Gp[4][3], 1)                       # entries: (unit(16, 2+m), g_m(sigma) poly, 1)
gpol = {}
for wm, coef, w in g3:
    m = wm.index(1) - 2
    gpol[m] = coef
for m in range(14):
    gpol.setdefault(m, [])
# q_b(sigma) = <k_b, g(sigma)> / |k_b|^2  (2-var cubic), g~_m = g_m - sum_b q_b k_b[m]
Kd = [[kc(kern[b][i]) for b in range(5)] for i in range(14)]
qb = []
for b in range(5):
    acc = []
    for m in range(14):
        acc = SP.merge(SP.smul(Kd[m][b], gpol[m]), acc)
    qb.append(SP.smul(SP.kofq(1 / gram[b]), acc))
gt = []
for m in range(14):
    acc = gpol[m]
    for b in range(5):
        acc = SP.merge(acc, SP.smul(SP.kofq(-1), SP.smul(Kd[m][b], qb[b])))
    acc = [t for t in acc if t[1] != SP.KZ]
    gt.append(acc)
DP['F4s3t'] = sorted([(SP.unit(16, 2 + m), gt[m], Fr(1)) for m in range(14) if gt[m]], key=lambda t: t[0])
# identity: G4^(3) == flat(D~) + sum_b q_b(sigma) * <k_b, w>
SP.reset_ops()
proj = []
for b in range(5):
    proj = SP.merge(proj, SP.mul(qb[b], SP.lin_poly(lambda p, b=b: Kd[p][b], 16, 2, 14)))
assert SP.eq_poly(Gp[4][3], SP.merge(flat_dp(DP['F4s3t']), proj))
# sigma^4 piece == (13/40)(25/4)(sg1^2+sg2^2)^2
assert SP.eq_poly(Gp[4][4], SP.smul(SP.kofq(Fr(13, 40) * Fr(25, 4)), norm_pow(2, 16)))
for nm, piece, d in (('F3w', Gp[3][0], 3), ('F4w', Gp[4][0], 4), ('F4s1', Gp[4][1], 3), ('F4s2', Gp[4][2], 2)):
    assert SP.eq_poly(flat_dp(DP[nm]), piece), nm
log(f'F4 pieces: DP flattenings match; g~ projection identity holds [mirror, {SP.OPS["kmul"]} kmul]')

# Bombieri squares: bombSq(DP) == c (sg1^2+sg2^2)^k
BS = {}
SP.reset_ops()
for nm, k in (('F3w', 0), ('F4w', 0), ('F4s1', 1), ('F4s2', 2), ('F4s3t', 3)):
    bs = bomb_sq(DP[nm])
    c = is_c_times(bs, norm_pow(k))
    BS[nm] = (c, k)
    log(f'  bombSq {nm}: {[str(x) for x in c]} * |sigma|^{2*k}')
assert BS['F3w'][0] == SP.kofq(5) and BS['F4w'][0] == SP.kofq(Fr(35261, 3840))
assert BS['F4s1'][0] == SP.kofq(Fr(J['constants']['c13'])) and BS['F4s2'][0] == SP.kofq(Fr(J['constants']['c22']))
assert BS['F4s3t'][0] == SP.kofq(Fr(J['constants']['c6_ker']))
log(f'Bombieri squares agree with local_pre (5, 35261/3840, c13, c22, c6) [mirror, {SP.OPS["kmul"]} kmul]')

# wsub checks: doubled DP monomials form a subsequence of S_d = pow(sumsq(16, 2, 14), d) with the right weights
def wsub(Dw, S):
    i = 0
    for m, w in Dw:
        while i < len(S) and S[i][0] != m:
            i += 1
        if i >= len(S) or S[i][1] != SP.kofq(w):
            return False
        i += 1
    return True


SP.reset_ops()
Sd = {}
for d in (1, 2, 3, 4):
    Sd[d] = SP.pw(SP.sumsq(16, 2, 14), d)
for nm, d in (('F3w', 3), ('F4w', 4), ('F4s1', 3), ('F4s2', 2), ('F4s3t', 1)):
    assert wsub([([2 * e for e in wm], w) for wm, coef, w in DP[nm]], Sd[d]), nm
S4 = {d: SP.pw(SP.sumsq(4, 0, 4), d) for d in (5, 6)}
for key, pd in pairs_out.items():
    for d in (5, 6):
        ent = [([2 * e for e in m], Fr(w)) for (m, c), w in zip([(m, c) for m, c in pd['parts'][d]], pd[f'w{d}'])]
        assert wsub(ent, S4[d]), (key, d)
log(f'wsub checks OK (S_d sizes {[len(Sd[d]) for d in (1, 2, 3, 4)]}, pair S5/S6 {len(S4[5])}/{len(S4[6])}) '
    f'[mirror, {SP.OPS["kmul"]} kmul]')

# rational upper bounds used by the scalar argument (from local_pre, re-asserted)
C = J['constants']
G2, C04, CQ22, CQ13, CQ, D1x4, G1x3 = (Fr(C[k]) for k in ('G2', 'CQ04', 'CQ22', 'CQ13', 'CQ', 'D1x4', 'G1x3'))
assert G2 ** 2 >= 5 and C04 ** 2 >= Fr(35261, 3840)
assert CQ22 ** 2 >= Fr(C['c22']) * Fr(4, 25) and CQ13 ** 2 >= Fr(C['c13']) * Fr(2, 5)
assert D1x4 ** 2 >= Fr(C['c6_ker']) * Fr(8, 125)
assert CQ >= CQ22 and CQ >= C04 and (CQ - CQ22) * (CQ - C04) >= (CQ13 / 2) ** 2
B5pp, B6pp = Fr(C['B5pp']), Fr(C['B6pp'])
def rowmax(f):
    return max(sum((f(*sorted((i, j))) for j in range(7) if j != i), Fr(0)) for i in range(7))
assert rowmax(lambda i, j: Fr(pairs_out[f'{i},{j}']['B5'])) == B5pp
assert rowmax(lambda i, j: Fr(pairs_out[f'{i},{j}']['B6'])) == B6pp

# ---------------------------------------------------------------- export
def pser(p):
    return [[m, [str(x) for x in c]] for m, c in p]


def dpser(ent):
    return [[wm, pser(coef), str(w)] for wm, coef, w in ent]


out = dict(
    P=[[list(map(str, kc(P[i][m]))) for m in range(3)] for i in range(7)],
    E1=[[list(map(str, kc(E1[i][m]))) for m in range(3)] for i in range(7)],
    E2=[[list(map(str, kc(E2[i][m]))) for m in range(3)] for i in range(7)],
    Kd=[[list(map(str, Kd[i][b])) for b in range(5)] for i in range(14)],
    gram=[str(x) for x in gram],
    mu=[list(map(str, kc(mu[i]))) for i in range(7)],
    pairs={k: dict(cls=v['cls'], W=list(map(str, v['W'])), g=list(map(str, v['g'])), parts=v['parts'],
                   w5=v['w5'], w6=v['w6'], B5sq=v['B5sq'], B6sq=v['B6sq'], B5=v['B5'], B6=v['B6'], kops=v['kops'])
           for k, v in pairs_out.items()},
    poles2=pser(poles2), poles4=pser(poles4),
    F={d: pser(Fl[d]) for d in (2, 3, 4)},
    F4chunks=[pser(c) for c in chunks], G4chunks=[pser(c) for c in Gchunks],
    Gp={d: {k: pser(Gp[d][k]) for k in range(d + 1)} for d in (2, 3, 4)},
    DP={nm: dpser(ent) for nm, ent in DP.items()},
    qb=[pser(q) for q in qb],
    BS={nm: dict(c=[str(x) for x in c], k=k) for nm, (c, k) in BS.items()},
    constants=dict(G2=str(G2), C04=str(C04), CQ22=str(CQ22), CQ13=str(CQ13), CQ=str(CQ), D1x4=str(D1x4),
                   G1x3=str(G1x3), B5pp=str(B5pp), B6pp=str(B6pp), c13=C['c13'], c22=C['c22'], c6=C['c6_ker']),
)
json.dump(out, open(os.path.join(HERE, 'local_global_out.json'), 'w'))
log('wrote local_global_out.json')
