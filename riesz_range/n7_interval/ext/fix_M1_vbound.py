#!/usr/bin/env python3
"""REVIEW_ext_fable.md M1 (2026-11-07): sup over s of |v_k''(s)| and |v_k'''(s)| for the cap kernel data
v(s) = (beta0, beta1, alpha0, a0, b0, x1, y1), using check_capR.vdata itself (read-only import, no bytecode written) on
1000 arb sub-intervals of each range.  Each printed value is the largest arb upper endpoint, hence an upper bound
(slightly above the true sup).  Documentation aid for RANGE_ASSEMBLY.md section 4 and capR/DESIGN.md 1; not an input
of any check.  usage: python3 ext/fix_M1_vbound.py   (seconds)"""
import os, sys
from fractions import Fraction as Fr
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "capR"))
import check_capR as C
import math

NAMES = ("beta0", "beta1", "alpha0", "a0", "b0", "x1", "y1")


def sup(n, lo, hi, N=1000):
    best, where = [0.0] * 7, [None] * 7
    for i in range(N):
        a, b = lo + (hi - lo) * Fr(i, N), lo + (hi - lo) * Fr(i + 1, N)
        v = C.vdata(n, C.ball(a, b))
        for k in range(7):
            u = float(abs(v[k]).upper())
            if u > best[k]:
                best[k], where[k] = u, (a, b)
    return best, where


for lo, hi in ((Fr(1, 2), Fr(3, 2)), (Fr(1, 3), Fr(7, 4)), (Fr(1, 4), Fr(2)), (Fr(1, 4), Fr(19, 10))):
    for n in (2, 3):
        b, w = sup(n, lo, hi)
        k = max(range(7), key=lambda j: b[j])
        print(f"[{lo}, {hi}] sup |v^({n})| <= {b[k]:.4f} ({NAMES[k]}, s in [{float(w[k][0]):.4f}, {float(w[k][1]):.4f}]);"
              f" per component: " + ", ".join(f"{NAMES[j]} {b[j]:.4f}" for j in range(7)))
for s in (Fr(1, 4), Fr(1, 3), Fr(17, 48), Fr(1, 2)):
    v = C.vdata(2, C.A(s))
    print(f"v''({s}) = " + ", ".join(f"{NAMES[j]} {float(v[j].mid()):+.4f}" for j in range(7))
          + f";  (ln 2)^2 2^-s = {math.log(2) ** 2 * 2 ** -float(s):.4f}")
