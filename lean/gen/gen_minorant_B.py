"""
Generator (development; superseded by emit_minor.py) for: the quartic contact certificate at t=0
for the cap's H_B minorant (numerics/hp/cert_cap_log_D12.json).

Computes, EXACTLY in Fractions:
  - HB(t) := the degree-12 polynomial with the JSON's H.B coefficients.
  - lowerbound(t) := (1/2) * sum_{k=1}^{13} t^k/k   (the n=13 odd-Taylor truncation, with the
    "-1/2*hi_log2" additive constant OMITTED -- it cancels against c0).
  - Q(t) := lowerbound(t) + HB(0) - HB(t). By construction Q has zero coefficients at
    t^0, t^1, t^2, t^3 (checked below) because HB's derivatives at 0 match lowerbound's
    through order 3 exactly (h1,h2,h3 = 1/2,1/4,1/6).
  - G(t) := Q(t) / t^4, a degree-9 polynomial (10 rational coefficients).
  - A Bernstein-basis certificate that G(t) >= kappa on [-1/20, 1/20]: convert G to the
    Bernstein basis on that interval (via the affine substitution t = w*(2s-1), s in [0,1])
    and check that every Bernstein coefficient is >= kappa. This is a sufficient condition
    for G(t) >= kappa on the whole interval (nonneg convex combination), and is exactly the
    "Bernstein/interval certificate" route.

Prints Lean-ready literals: the HB coefficients, kappa, the Bernstein coefficients (as a
sanity check only -- the Lean proof re-derives G from HB and lowerbound by `ring`, then
certifies G's positivity from HB's coefficients directly via nlinarith / a Horner interval
argument, so nothing here is trusted; this script is just how the constants were chosen).
"""
import json
from fractions import Fraction as Fr
from math import comb

J = json.load(open("numerics/hp/cert_cap_log_D12.json"))
HB = [Fr(x) for x in J["H"]["B"]]
assert len(HB) == 13
assert HB[1] == Fr(1, 2) and HB[2] == Fr(1, 4) and HB[3] == Fr(1, 6)

N = 13  # odd truncation order for the log series
# lowerbound(t) - HB(t) + HB(0), coefficient by coefficient (index 0..13)
deg = max(N, 12)
Q = [Fr(0)] * (deg + 1)
for k in range(1, N + 1):
    Q[k] += Fr(1, 2) / k
for i, c in enumerate(HB):
    Q[i] -= c
Q[0] += HB[0]  # + HB(0) cancels the constant term of (-HB(t)) at i=0, i.e. Q[0] = HB[0]-HB[0] = 0
assert Q[0] == 0 and Q[1] == 0 and Q[2] == 0 and Q[3] == 0, Q[:4]

G = Q[4:]  # G(t) = Q(t)/t^4, degree 9 (10 coeffs), G[j] = Q[4+j]
print("G coefficients (index 0..%d):" % (len(G) - 1))
for j, c in enumerate(G):
    print(f"  G[{j}] = {c}  ({float(c):.6g})")

w = Fr(1, 20)
kappa = Fr(147, 50000)

# Bernstein coefficients of G on [-w, w]: t = w*(2s-1), s in [0,1].
# First get G as a polynomial in s: substitute t = w*(2s-1) and expand.
# g_coeffs_s[m] = coefficient of s^m in G(w*(2s-1))
d = len(G) - 1
g_s = [Fr(0)] * (d + 1)
for j, cj in enumerate(G):
    # (w*(2s-1))^j = w^j * sum_{m=0}^j C(j,m) (2s)^m (-1)^(j-m)
    for m in range(j + 1):
        g_s[m] += cj * (w ** j) * comb(j, m) * (2 ** m) * ((-1) ** (j - m))

# Bernstein coefficients b_i of a degree-d polynomial p(s) = sum a_m s^m:
#   b_i = sum_{m=0}^{i} C(i,m) / C(d,m) * a_m      (standard power->Bernstein change of basis)
bern = []
for i in range(d + 1):
    bi = Fr(0)
    for m in range(i + 1):
        bi += Fr(comb(i, m), comb(d, m)) * g_s[m]
    bern.append(bi)

print("\nBernstein coefficients on [-1/20,1/20] (degree %d):" % d)
worst = min(bern)
for i, b in enumerate(bern):
    print(f"  b[{i}] = {b}  ({float(b):.6g})")
print("\nmin Bernstein coeff =", float(worst), " kappa =", float(kappa),
      " OK (min >= kappa):", worst >= kappa)

print("\nHB coefficients:")
for i, c in enumerate(HB):
    print(f"  HB[{i}] = {c}")

# --- item (iii): plain piece on [1/20, 1/2]: min of (lowerbound(t) - HB(t)) there, no shift needed
# (center 0 still valid since t=1/2 < 1). Just report a numeric lower bound via sampling +
# the same Bernstein technique on this interval, target margin 1e-10.
a, b = Fr(1, 20), Fr(1, 2)
P = [Fr(0)] * (deg + 1)
for k in range(1, N + 1):
    P[k] += Fr(1, 2) / k
for i, c in enumerate(HB):
    P[i] -= c
# P(t) = lowerbound(t) - HB(t) (no c0 shift here; just need P(t) >= 1e-10 on [a,b])
dP = len(P) - 1
p_s = [Fr(0)] * (dP + 1)
half = (b - a) / 2
mid = (a + b) / 2
for j, cj in enumerate(P):
    for m in range(j + 1):
        p_s[m] += cj * (mid ** (j - m)) * comb(j, m) * (half ** m) if False else Fr(0)
# do it properly: t = mid + half*(2s-1) = (mid-half) + 2*half*s = a + (b-a)*s
for m in range(dP + 1):
    p_s[m] = Fr(0)
for j, cj in enumerate(P):
    # t^j = (a + (b-a)*s)^j = sum_m C(j,m) a^(j-m) (b-a)^m s^m
    for m in range(j + 1):
        p_s[m] += cj * comb(j, m) * (a ** (j - m)) * ((b - a) ** m)
bernP = []
for i in range(dP + 1):
    bi = Fr(0)
    for m in range(i + 1):
        bi += Fr(comb(i, m), comb(dP, m)) * p_s[m]
    bernP.append(bi)
print("\nitem (iii): plain piece [1/20,1/2], min Bernstein coeff of (lowerbound-HB) =",
      float(min(bernP)), " target 1e-10 OK:", min(bernP) >= Fr(1, 10**10))
