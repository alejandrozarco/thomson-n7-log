"""Probe (float, 50 digits; NOT a certificate): Lean-cheap bounds for the error blocks of Lemma L'.

For each block we compare the checker's constant (projected Frobenius / op-norm, needs exact projectors
or an ONB of W) with a bound that needs only *unprojected* data on R^14 plus C5-invariance identities,
which in Lean are finite sums of squares of K-elements (no projector, no ONB):
  gamma1 : sup_{|u|=1} |3C(u_S,w,w)|  <- ||A_alpha||_F (unprojected 14x14), or penalty-PSD op norm on W
  gamma2 : |C(w,w,w)| <= ||F3||_B |w|^3 on all of R^14
  delta1 : |4D(s,s,s,w)| = |<g(sigma), w>| <= |g~(sigma)| b, g~ = g minus its S-component (exact in K)
  c_q    : 6D(ssww)+4D(swww)+D(wwww) via ||B(sigma)||_F, ||T(sigma,.)||_B, ||F4||_B (unprojected)
Then re-runs the scalar argument of L' (steps 9.2/9.3) with these constants.
usage: nice -n 19 python3 probe_error_blocks.py   (~10 s)
"""
import sys, os
from fractions import Fraction as Fr
from math import factorial
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from local_exact import build, kcoeffs

mp.mp.dps = 30
D = build(DMAX=4)
al = mp.sqrt(10 + 2 * mp.sqrt(5))
fv = lambda z: float(sum(mp.mpf(c.numerator) / c.denominator * al ** k for k, c in enumerate(kcoeffs(z))))
F3, F4 = D['F3'], D['F4']
s1 = np.array([fv(x) for x in D['s1']]); s2 = np.array([fv(x) for x in D['s2']])
Kv = np.array([[fv(x) for x in v] for v in D['kern']]).T


def dense(pol, d):
    T = np.zeros((14,) * d)
    from itertools import permutations
    for m, c in pol.items():
        idx = []
        for k, e in enumerate(m):
            idx += [k] * e
        ps = set(permutations(idx)); val = fv(c) / len(ps)
        for p in ps:
            T[p] = val
    return T


def bomb(pol, d):
    tot = 0.0
    for m, c in pol.items():
        w = 1
        for e in m:
            w *= factorial(e)
        tot += fv(c) ** 2 * w / factorial(d)
    return tot ** 0.5


C = dense(F3, 3); Dt = dense(F4, 4)
PiK = Kv @ np.linalg.inv(Kv.T @ Kv) @ Kv.T; PiW = np.eye(14) - PiK
e1, e2 = s1 / np.linalg.norm(s1), s2 / np.linalg.norm(s2)          # ONB of S
# gamma1
A = [3 * np.einsum('ijk,i->jk', C, e) for e in (e1, e2)]          # 3C(e_alpha,.,.)
opW = [np.abs(np.linalg.eigvalsh(PiW @ a @ PiW)).max() for a in A]
fro = [np.linalg.norm(a) for a in A]; opR = [np.abs(np.linalg.eigvalsh(a)).max() for a in A]
g1_W = np.sqrt(sum(o ** 2 for o in opW)) / 3; g1_R = np.sqrt(sum(o ** 2 for o in opR)) / 3; g1_F = np.sqrt(sum(o ** 2 for o in fro)) / 3
print(f'gamma1: op on W {g1_W:.6f} (checker 0.387896) | op on R^14 {g1_R:.6f} | unprojected Frobenius {g1_F:.6f}')
# gamma2
print(f'gamma2: projected Frobenius {np.linalg.norm(np.einsum("ijk,ia,jb,kc->abc", C, PiW, PiW, PiW)):.6f} (checker 1.319021) | unprojected ||F3||_B {bomb(F3, 3):.6f}')
g2_R = bomb(F3, 3)
# delta1: 4D(s,s,s,w) = <g(s), w>, g = grad F4 at s; |g~| / |s|^3 with g~ = g - S-part (sample, invariant)
th = np.linspace(0, 2 * np.pi, 13)[:-1]
vals_W, vals_S = [], []
for t in th:
    s = np.cos(t) * e1 + np.sin(t) * e2
    g = 4 * np.einsum('ijkl,i,j,k->l', Dt, s, s, s)
    gS = (g @ e1) * e1 + (g @ e2) * e2
    vals_W.append(np.linalg.norm(PiW @ g)); vals_S.append(np.linalg.norm(g - gS))
d1_W, d1_S = max(vals_W) / 4, max(vals_S) / 4
print(f'delta1 (op-type): |Pi_W g|/4 {d1_W:.6f} (range {min(vals_W)/4:.6f}..) | |g - Pi_S g|/4 {d1_S:.6f} (checker Frobenius 0.147314)')
# c_q pieces, unprojected; normalise s = unit in S
c22 = max(np.linalg.norm(6 * np.einsum('ijkl,i,j->kl', Dt, np.cos(t) * e1 + np.sin(t) * e2, np.cos(t) * e1 + np.sin(t) * e2)) for t in th)
T13 = []
for t in th:
    s = np.cos(t) * e1 + np.sin(t) * e2
    T3 = 4 * np.einsum('ijkl,i->jkl', Dt, s)          # cubic form in w: T(w) = T3[w,w,w]
    T13.append(np.linalg.norm(T3))                   # Frobenius of symmetric tensor = Bombieri of the form
c13 = max(T13); c04 = bomb(F4, 4)
cq = max(np.linalg.eigvalsh(np.array([[c22, c13 / 2], [c13 / 2, c04]])))
print(f'c_q pieces unprojected: c22 {c22:.4f} c13 {c13:.4f} c04 {c04:.4f} -> c_q {cq:.4f} (checker 4.203074)')
# scalar argument of L' with these constants
rho, eps, qp, Kc = 0.01, 1 / 16, 0.058, 3.22942
for nm, g1, g2, d1, c in [('checker constants', 0.387896, 1.319021, 0.147314, 4.203074),
                          ('Lean-cheap, g1 via PSD on W', 0.387896, g2_R, d1_S, cq),
                          ('Lean-cheap, g1 unprojected Frobenius', g1_F, g2_R, d1_S, cq)]:
    bb = (3 * g1 + g2) * rho + c * rho ** 2 + 2 * Kc * rho ** 3
    print(f'  {nm:40s}: b^2 coeff {eps - bb - 2 * d1 * rho:.6f}, a^4 coeff {qp - Kc * rho - 2 * d1 * rho:.6f}')
