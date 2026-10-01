"""Exporter for lean/LogLean/LocalCert.lean: certificate (C') of local/LOCAL_LEMMA.md section 3'.

Builds the exact data H (14x14), Gam (14x3) and the kernel vectors K (14x5) over K = Q(alpha)
(local_exact.py, adapted from local/check_local_rigorous.py steps 0-3), forms the 17x17 matrix

    M = [[ H/2 - eps I + K K^T , Gam/2 ],
         [ Gam^T/2             , cG * G_theta ]],   cG = (13/40 - q') * 25/4,

exactly as LocalCert.lean does (same Kel arithmetic, alpha^4 = 20 alpha^2 - 80), computes a float
LDL^T of M - delta I, rounds D and L to dyadics 2^-BITS, and re-runs the Lean check in exact rationals:
  E = M - L^T diag(D) L  (entrywise, an element of K), enclosed on alpha in [LO, HI];
  D >= 0, E symmetric, E diagonally dominant with the enclosures.
Then writes LocalCert.lean from LocalCert.template.lean.

Design choice vs the checker (step 9.1): the checker uses  H/2 - eps Pi_W + Pi_ker  and  Gam_W = Pi_W Gam.
Here the penalty is K K^T (rank-5, no inverse Gram matrix) and Gam is unprojected; both are equal on W
(Pi_ker Gam = 0 exactly is not needed: for w in W, <Gam m, w> = <Gam_W m, w> anyway).  The float
lambda_min is the same 2.66e-4 (see explore notes in LOCAL_LEAN_DESIGN.md).

usage: nice -n 19 python3 export_local_cert.py            (about 5 s)
"""
import os, sys, time
from fractions import Fraction as Fr
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from local_exact import build, kcoeffs

T0 = time.time()
mp.mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', 'LogLean')

EPS, QP, THETA = Fr(1, 16), Fr(29, 500), Fr(-4999, 5000)
CG = (Fr(13, 40) - QP) * Fr(25, 4)
DELTA = Fr(1, 10000)          # LDL of M - DELTA*I: the remainder E is ~ DELTA*I + rounding
BITS = 40
# alpha = sqrt(10 + 2 sqrt 5) = 3.80422606518061...; box proved in Lean from sqrt bounds
LO, HI = Fr(380422606518, 10 ** 11), Fr(380422606519, 10 ** 11)

# ------------------------------------------------------------------ Kel arithmetic (mirror of Lean)
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


def mn(a, b):
    return a if a <= b else b


def mx(a, b):
    return b if a <= b else a


def klo(x):
    return x[0] + mn(x[1] * LO, x[1] * HI) + mn(x[2] * LO ** 2, x[2] * HI ** 2) + mn(x[3] * LO ** 3, x[3] * HI ** 3)


def khi(x):
    return x[0] + mx(x[1] * LO, x[1] * HI) + mx(x[2] * LO ** 2, x[2] * HI ** 2) + mx(x[3] * LO ** 3, x[3] * HI ** 3)


def kaub(x):
    u, v = khi(x), -klo(x)
    return v if u <= v else u


ALPHA = mp.sqrt(10 + 2 * mp.sqrt(5))
kev = lambda x: sum(mp.mpf(c.numerator) / c.denominator * ALPHA ** k for k, c in enumerate(x))

# ------------------------------------------------------------------ exact data
D = build(DMAX=3)
Hd = [[tuple(kcoeffs(z)) for z in row] for row in D['H']]
Gd = [[tuple(kcoeffs(z)) for z in row] for row in D['Gam']]
Kd = [[tuple(kcoeffs(D['kern'][b][i])) for b in range(5)] for i in range(14)]     # Kd[i][b]
Gth = [[Fr(1), Fr(0), THETA], [Fr(0), 2 - 2 * THETA, Fr(0)], [THETA, Fr(0), Fr(1)]]
assert mp.mpf(LO.numerator) / LO.denominator < ALPHA < mp.mpf(HI.numerator) / HI.denominator
S5LO, S5HI = Fr(2236067977499789, 10 ** 15), Fr(2236067977499790, 10 ** 15)   # sqrt5 box (as upstream)
assert S5LO ** 2 <= 5 <= S5HI ** 2 and LO ** 2 <= 10 + 2 * S5LO and 10 + 2 * S5HI <= HI ** 2


def pen(i, j):
    acc = Z4
    for b in range(5):
        acc = kadd(acc, kmul(Kd[i][b], Kd[j][b]))
    return acc


def Mk(i, j):
    if i < 14:
        if j < 14:
            return kadd(ksub(ksmul(Fr(1, 2), Hd[i][j]), kofq(EPS if i == j else 0)), pen(i, j))
        return ksmul(Fr(1, 2), Gd[i][j - 14])
    if j < 14:
        return ksmul(Fr(1, 2), Gd[j][i - 14])
    return kofq(CG * Gth[i - 14][j - 14])


N = 17
Mex = [[Mk(i, j) for j in range(N)] for i in range(N)]
Mf = mp.matrix(N, N)
for i in range(N):
    for j in range(N):
        Mf[i, j] = kev(Mex[i][j])
ev = mp.eigsy(Mf)[0]
lmin = min(ev)
print(f'float lambda_min(M) = {mp.nstr(lmin, 6)}  (checker step 9.1: 2.66e-04)')

# ------------------------------------------------------------------ LDL^T of M - delta I, rounded
A = Mf - mp.mpf(DELTA.numerator) / DELTA.denominator * mp.eye(N)
Lf = mp.matrix(N, N); Df = [mp.mpf(0)] * N
for k in range(N):
    Df[k] = A[k, k] - sum(Lf[k, q] ** 2 * Df[q] for q in range(k))
    Lf[k, k] = 1
    for i in range(k + 1, N):
        Lf[i, k] = (A[i, k] - sum(Lf[i, q] * Lf[k, q] * Df[q] for q in range(k))) / Df[k]
print(f'min float pivot = {mp.nstr(min(Df), 6)}')
S = 2 ** BITS
rnd = lambda x: Fr(int(mp.nint(x * S)), S)
Dd = [rnd(Df[q]) for q in range(N)]
Ld = [[(Fr(1) if i == q else (rnd(Lf[i, q]) if i > q else Fr(0))) for i in range(N)] for q in range(N)]  # Ld[q][i]


def ldl(i, j):
    return sum((Dd[q] * Ld[q][i] * Ld[q][j] for q in range(N)), Fr(0))


E = [[ksub(Mex[i][j], kofq(ldl(i, j))) for j in range(N)] for i in range(N)]
ok_d = all(d >= 0 for d in Dd)
ok_s = all(E[i][j] == E[j][i] for i in range(N) for j in range(N))
slack = []
for i in range(N):
    off = sum((kaub(E[i][j]) for j in range(N) if j != i), Fr(0))
    slack.append(klo(E[i][i]) - off)
ok_dd = all(s >= 0 for s in slack)
print(f'check mirror: D>=0 {ok_d}, E symmetric {ok_s}, E diag. dominant {ok_dd}; min dd slack {float(min(slack)):.3e}')
assert ok_d and ok_s and ok_dd

# ------------------------------------------------------------------ emit Lean


def q(x):
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def kel(x):
    return '⟨' + ', '.join(q(c) for c in x) + '⟩'


def mat(rows, f):
    return '[' + ',\n  '.join('[' + ', '.join(f(x) for x in r) + ']' for r in rows) + ']'


data = []
data.append(f'/-- `H` (14×14 over K): Hessian of the minorant 𝒫 in the frame chart `t ∈ ℝ¹⁴` (F₂ = ½ tᵀHt). -/')
data.append(f'def Hdat : List (List Kel) :=\n  {mat(Hd, kel)}')
data.append(f'/-- `Γ` (14×3 over K): ∇F₃ at s = σ₁ŝ₁ + σ₂ŝ₂, columns for m = (σ₁², σ₁σ₂, σ₂²). -/')
data.append(f'def Gdat : List (List Kel) :=\n  {mat(Gd, kel)}')
data.append(f'/-- Kernel vectors (14×5 over K): rotation fields r₁ r₂ r₃ and ŝ₁ ŝ₂; row `i` = coordinate `i`. -/')
data.append(f'def Kdat : List (List Kel) :=\n  {mat(Kd, kel)}')
data.append(f'/-- LDLᵀ data (dyadic, 2^-{BITS}) of M − {q(DELTA)}·I: pivots. -/')
data.append(f'def Ddat : List ℚ := [{", ".join(q(d) for d in Dd)}]')
data.append(f'/-- LDLᵀ data: row `q` is the column vector l_q (unit lower triangular L). -/')
data.append(f'def Ldat : List (List ℚ) :=\n  {mat(Ld, q)}')
data.append(f'/-- Rational box for α = √(10 + 2√5). -/')
data.append(f'def aLo : ℚ := {q(LO)}\ndef aHi : ℚ := {q(HI)}')
body = '\n\n'.join(data)
tmpl = open(os.path.join(LEAN, 'LocalCert.template.lean')).read()
out = tmpl.replace('-- @@DATA@@', body)
open(os.path.join(LEAN, 'LocalCert.lean'), 'w').write(out)
print(f'wrote LocalCert.lean ({out.count(chr(10)) + 1} lines), {time.time() - T0:.1f}s')
