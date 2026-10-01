"""Atom level (T2) of Lemma L' -- exact Python mirror of the Lean evaluator `LocalAtom.lean`.

A `Rep` is a pair (T, err): T a sparse polynomial in the six atoms A B C C' ri2 rj2 (weights 1 2 1 1 2 2), kept to
weight <= 6, coefficients in K = Q(alpha); err a rational.  Semantics (Lean `LocalAtom.Ok`):
    |q - T(atoms)| <= err * R^7
under the atom bounds |A| <= bA R, |B| <= bB R^2, |C|,|C'| <= bC R, 0 <= ri2, rj2 <= R^2, 0 <= R <= rho,
and |e_i|, |e_j| <= CE R^8 (represented as T = 0, err = CE rho).
Operations: add, smul (by a K constant, err scaled by |c|_ub), mul (truncated product; the dropped monomials of weight
w >= 7 contribute |c_t|_ub |c_s|_ub beta^m rho^(w-7) to err; cross terms via `bnd`, the monomial-wise bound of T at rho).
The class polynomial Phi_g (= f_ij in the atoms) is built with these operations exactly as in Lean; the result's T
must equal T6_g of local_pre.py and its err is the class constant K_g (Lean: `decide`).

Also counts the kernel work (Kel multiplications, monomial comparisons) and re-runs the closure of L' with the new K7.
usage: nice -n 19 python3 lean/gen/local_atom.py     (writes lean/gen/local_atom_out.json)
"""
import os, json, time
from fractions import Fraction as Fr
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
J = json.load(open(os.path.join(HERE, 'local_pre_out.json')))
T0 = time.time()
RHO = Fr(1, 100)
LO, HI = Fr(J['alpha_box'][0]), Fr(J['alpha_box'][1])

# ---------------------------------------------------------------- Kel (mirror of LocalKel)
def kmul(x, y):
    p = [Fr(0)] * 7
    for i in range(4):
        for j in range(4):
            p[i + j] += x[i] * y[j]
    return (p[0] - 80 * p[4] - 1600 * p[6], p[1] - 80 * p[5], p[2] + 20 * p[4] + 320 * p[6], p[3] + 20 * p[5])


kadd = lambda x, y: tuple(a + b for a, b in zip(x, y))
kofq = lambda q: (Fr(q), Fr(0), Fr(0), Fr(0))
KZ = kofq(0)


def kel_lo(c):
    mn = lambda a, b: a if a <= b else b
    return c[0] + mn(c[1] * LO, c[1] * HI) + mn(c[2] * LO ** 2, c[2] * HI ** 2) + mn(c[3] * LO ** 3, c[3] * HI ** 3)


def kel_hi(c):
    mx = lambda a, b: b if a <= b else a
    return c[0] + mx(c[1] * LO, c[1] * HI) + mx(c[2] * LO ** 2, c[2] * HI ** 2) + mx(c[3] * LO ** 3, c[3] * HI ** 3)


def kaub(c):
    return max(kel_hi(c), -kel_lo(c))


def sqrt_up(q, digits=9):
    q = Fr(q)
    s = 10 ** digits
    r = Fr(isqrt(int(q * s * s)) + 1, s)
    assert r * r >= q
    return r


# ---------------------------------------------------------------- op counters
OPS = {'kmul': 0, 'cmp': 0, 'aub': 0}


def cmul(x, y):
    OPS['kmul'] += 1
    return kmul(x, y)


def caub(c):
    OPS['aub'] += 1
    return kaub(c)


# ---------------------------------------------------------------- Poly6: sorted list of (mono(list of 6), Kel)
WGT = (1, 2, 1, 1, 2, 2)


def wdeg(m):
    return sum(w * e for w, e in zip(WGT, m))


def mlt(m, n):
    OPS['cmp'] += 1
    return m < n          # lexicographic, as Lean `ltM`


def merge(p, q):
    out = []
    i = j = 0
    while i < len(p) and j < len(q):
        if p[i][0] == q[j][0]:
            out.append((p[i][0], kadd(p[i][1], q[j][1]))); i += 1; j += 1
        elif mlt(p[i][0], q[j][0]):
            out.append(p[i]); i += 1
        else:
            out.append(q[j]); j += 1
    out.extend(p[i:]); out.extend(q[j:])
    return out


class Cls:
    """class constants: atom bounds and rho (rational)"""
    def __init__(self, bA, bB, bC, CE):
        self.bA, self.bB, self.bC, self.CE = bA, bB, bC, CE

    def betapow(self, m):
        return self.bA ** m[0] * self.bB ** m[1] * self.bC ** (m[2] + m[3])   # ri2, rj2 have beta = 1


def bnd(T, cl):
    """monomial-wise bound of |T(atoms)| at R <= rho"""
    return sum((caub(c) * cl.betapow(m) * RHO ** wdeg(m) for m, c in T), Fr(0))


def mul_row(t, q, cl):
    """(row of kept products, dropped bound)"""
    m, c = t
    kept, drop = [], Fr(0)
    ac = caub(c)
    for n, d in q:
        mn = [a + b for a, b in zip(m, n)]
        w = wdeg(mn)
        if w <= 6:
            kept.append((mn, cmul(c, d)))
        else:
            drop += ac * caub(d) * cl.betapow(mn) * RHO ** (w - 7)
    return kept, drop


def mulT(p, q, cl):
    acc, drop = [], Fr(0)
    for t in p:
        kept, d = mul_row(t, q, cl)
        acc = merge(kept, acc)
        drop += d
    return acc, drop


class Rep:
    def __init__(self, T, err):
        self.T, self.err = T, err


def radd(r, s):
    return Rep(merge(r.T, s.T), r.err + s.err)


def rsmul(c, r):
    return Rep([(m, cmul(c, d)) for m, d in r.T], caub(c) * r.err)


def rmul(r, s, cl):
    P, d = mulT(r.T, s.T, cl)
    return Rep(P, d + r.err * (bnd(s.T, cl) + s.err * RHO ** 7) + bnd(r.T, cl) * s.err)


def atom(k):
    m = [0] * 6; m[k] = 1
    return Rep([(m, kofq(1))], Fr(0))


def e_atom(cl):
    return Rep([], cl.CE * RHO)


def nu_rep(r2, e, cl):
    """nu = -r2/2 - r2^2/8 - r2^3/16 + e"""
    r4 = rmul(r2, r2, cl)
    r6 = rmul(r4, r2, cl)
    return radd(radd(radd(rsmul(kofq(Fr(-1, 2)), r2), rsmul(kofq(Fr(-1, 8)), r4)), rsmul(kofq(Fr(-1, 16)), r6)), e)


def phi_rep(g, W, inv, cl):
    A, B, C, Cp, ri2, rj2 = (atom(k) for k in range(6))
    ei, ej = e_atom(cl), e_atom(cl)
    nui, nuj = nu_rep(ri2, ei, cl), nu_rep(rj2, ej, cl)
    hh = radd(radd(radd(B, rmul(nuj, Cp, cl)), rmul(nui, C, cl)), rsmul(g, rmul(nui, nuj, cl)))
    ell = radd(A, rsmul(g, radd(nui, nuj)))
    u = rsmul(inv, radd(ell, hh))
    u2 = rmul(u, u, cl)
    u3 = rmul(u2, u, cl)
    u4 = rmul(u3, u, cl)
    u5 = rmul(u4, u, cl)
    psi = radd(radd(radd(rsmul(kofq(Fr(1, 4)), u2), rsmul(kofq(Fr(1, 6)), u3)), rsmul(kofq(Fr(1, 8)), u4)),
               rsmul(kofq(Fr(1, 10)), u5))
    return radd(rsmul(W, hh), psi), dict(nu=len(nui.T), hh=len(hh.T), u=len(u.T), u2=len(u2.T), u3=len(u3.T),
                                          u4=len(u4.T), u5=len(u5.T))


# ---------------------------------------------------------------- constants
# CE: |e| <= CE r^8 where nu = nhat(r^2) + e (LocalAtom / LocalGeom prove CE = 391/10000 for r^2 <= rho^2)
CE = Fr(391, 10000)
SQ2 = sqrt_up(Fr(2))
CLS = {}
for nm, c in J['classes'].items():
    g = tuple(Fr(x) for x in c['g'])
    W = tuple(Fr(x) for x in c['W'])
    inv = kmul(kofq(2), W)                       # 1/(1-g) = 2W
    one_minus_g = kadd(kofq(1), tuple(-x for x in g))
    assert kmul(inv, one_minus_g) == kofq(1), nm
    sg = Fr(c['sg'])                             # >= sqrt(1-g^2)
    cl = Cls(SQ2 * sg, Fr(1, 2), sg, CE)
    for k in OPS: OPS[k] = 0
    t0 = time.time()
    rep, sizes = phi_rep(g, W, inv, cl)
    T6 = sorted(([m[:6] for m in [e]][0], tuple(Fr(x) for x in cc)) for e, cc in c['T6'])
    T6 = [(list(m), cc) for m, cc in T6]
    mine = [(m, cc) for m, cc in rep.T if cc != KZ]
    assert mine == T6, f'{nm}: T mismatch'
    print(f'[{time.time()-T0:5.1f}s] class {nm:10s}: T == T6_g ({len(T6)} monomials, {len(rep.T)} incl. zeros); '
          f'K_g = {float(rep.err):.4f} (design structural {float(Fr(c["K7"])):.4f}); '
          f'ops kmul {OPS["kmul"]}, cmp {OPS["cmp"]}, aub {OPS["aub"]}; sizes {sizes}; {time.time()-t0:.2f}s')
    CLS[nm] = dict(g=g, W=W, inv=inv, sg=sg, K=rep.err, T=rep.T, ops=dict(OPS), sizes=sizes, absg=Fr(c['absg']))

# per-pair rowmax of K_g and closure (mirror of local_pre.closure, A = 1)
def dec_up(x, digits=4):
    sc = 10 ** digits
    return Fr(-(-x.numerator * sc // x.denominator), sc)


Kcls = {nm: dec_up(d['K']) for nm, d in CLS.items()}
pairs = {tuple(int(t) for t in k.split(',')): v for k, v in J['pairs'].items()}
def rowmax(f):
    return max(sum((f(*sorted((i, j))) for j in range(7) if j != i), Fr(0)) for i in range(7))


K7pp = rowmax(lambda i, j: Kcls[pairs[(i, j)]['cls']])
B5pp, B6pp = Fr(J['constants']['B5pp']), Fr(J['constants']['B6pp'])
G1x3, G2, D1, CQ = (Fr(J['constants'][k]) for k in ('G1x3', 'G2', 'D1', 'CQ'))
KK = B5pp + B6pp * RHO + K7pp * RHO ** 2
bb = (G1x3 + G2) * RHO + CQ * RHO ** 2 + 2 * KK * RHO ** 3
cw = Fr(1, 16) - bb - 2 * D1 * RHO
cs = Fr(29, 500) - KK * RHO - 2 * D1 * RHO
print(f'K7 rowmax {float(K7pp):.4f} (design 85.2620); K = {float(KK):.5f}; closure at rho=1/100: '
      f'cw {float(cw):.6f}, cs {float(cs):.6f}  {"CLOSES" if cw > 0 and cs > 0 else "FAILS"}')
# rounded-down targets that the Lean file will state
cw_st, cs_st = Fr(268, 10000), Fr(200, 10000)
assert cw >= cw_st and cs >= cs_st
KKup = dec_up(KK, 5)

out = dict(CE=str(CE), SQ2=str(SQ2), rho=str(RHO), K7pp=str(K7pp), K=str(KKup), cw=str(cw), cs=str(cs),
           classes={nm: dict(g=[str(x) for x in d['g']], W=[str(x) for x in d['W']], inv=[str(x) for x in d['inv']],
                             sg=str(d['sg']), absg=str(d['absg']), K=str(Kcls[nm]), Kexact=str(d['K']), ops=d['ops'],
                             sizes=d['sizes'], T=[[m, [str(x) for x in c]] for m, c in d['T']])
                    for nm, d in CLS.items()})
json.dump(out, open(os.path.join(HERE, 'local_atom_out.json'), 'w'))
print(f'[{time.time()-T0:5.1f}s] wrote local_atom_out.json')
