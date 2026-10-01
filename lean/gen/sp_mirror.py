"""Exact Python mirror of the Lean kernel library `LocalSP` (sparse polynomials over K = Q(alpha), monomials = lists
of exponents, lexicographic merge order).  Used by local_global.py to (a) predict every `eqPoly … = true` that the
Lean files ask the kernel to decide, and (b) count the kernel work (Kel multiplications, monomial comparisons).
"""
from fractions import Fraction as Fr

OPS = {'kmul': 0, 'cmp': 0}


def kmul(x, y):
    OPS['kmul'] += 1
    p = [Fr(0)] * 7
    for i in range(4):
        for j in range(4):
            p[i + j] += x[i] * y[j]
    return (p[0] - 80 * p[4] - 1600 * p[6], p[1] - 80 * p[5], p[2] + 20 * p[4] + 320 * p[6], p[3] + 20 * p[5])


def kadd(x, y):
    return tuple(a + b for a, b in zip(x, y))


def kofq(q):
    return (Fr(q), Fr(0), Fr(0), Fr(0))


KZ = kofq(0)
KONE = kofq(1)


def madd(m, n):
    if len(m) < len(n):
        m, n = n, m
    return [a + (n[i] if i < len(n) else 0) for i, a in enumerate(m)]


def mlt(m, n):
    OPS['cmp'] += 1
    return m < n           # Python list comparison == Lean `Mono.lt` (lexicographic, shorter-prefix first)


def merge(p, q):
    out, i, j = [], 0, 0
    while i < len(p) and j < len(q):
        if p[i][0] == q[j][0]:
            out.append((p[i][0], kadd(p[i][1], q[j][1]))); i += 1; j += 1
        elif mlt(p[i][0], q[j][0]):
            out.append(p[i]); i += 1
        else:
            out.append(q[j]); j += 1
    out.extend(p[i:]); out.extend(q[j:])
    return out


def smul(c, p):
    return [(m, kmul(c, d)) for m, d in p]


def mul_row(t, q):
    return [(madd(t[0], s[0]), kmul(t[1], s[1])) for s in q]


def mul(p, q):
    acc = []
    for t in reversed(p):          # Lean: mul (t :: p) q = merge (mulRow t q) (mul p q)
        acc = merge(mul_row(t, q), acc)
    return acc


ONE = [([], KONE)]


def pw(p, n):
    acc = ONE
    for _ in range(n):
        acc = mul(p, acc)
    return acc


def all_zero(p):
    return all(c == KZ for _, c in p)


def eq_poly(p, q):
    return all_zero(merge(p, smul(kofq(-1), q)))


def mono_poly(m, i, f):
    if not m:
        return ONE
    return mul(pw(f(i), m[0]), mono_poly(m[1:], i + 1, f))


def compose(p, f):
    acc = []
    for t in reversed(p):
        acc = merge(smul(t[1], mono_poly(t[0], 0, f)), acc)
    return acc


def unit(n, k):
    return [1 if i == k else 0 for i in range(n)]


def sumsq(n, off, m):
    """sum_{p<m} x_{off+p}^2 as a sorted Poly in n variables"""
    acc = []
    for p in range(m):
        acc = merge(acc, [([2 * e for e in unit(n, off + p)], KONE)])
    return acc


def lin_poly(v, n, off, m):
    """sum_{p<m} v(p) x_{off+p}  (v : p -> Kel)"""
    acc = []
    for p in range(m):
        acc = merge(acc, [(unit(n, off + p), v(p))])
    return acc


def qf_poly(H, n, off, m):
    """sum_{p<m} sum_{q<m} H(p,q) x_{off+p} x_{off+q}"""
    acc = []
    for p in range(m):
        row = []
        for q in range(m):
            row = merge(row, [(madd(unit(n, off + p), unit(n, off + q)), H(p, q))])
        acc = merge(acc, row)
    return acc


def from_sympy(poly, kcoeffs, nvars=None):
    """sympy ring element -> sorted Poly (list of (exps list, Kel tuple))"""
    out = [(list(m) if nvars is None else list(m)[:nvars], tuple(kcoeffs(c))) for m, c in poly.items()]
    out.sort(key=lambda t: t[0])
    return [t for t in out if t[1] != KZ]


def reset_ops():
    for k in OPS:
        OPS[k] = 0
