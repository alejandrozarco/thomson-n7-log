"""Local lemma for the Coulomb (s = 1) cap, N = 7, by ball arithmetic (python-flint arb, 256 bits).

Statement (L1).  Let P be the pentagonal bipyramid and z = (z_1..z_7) unit vectors with
    (gauge)  sum_i P_i z_i^T symmetric,        (radius)  |w| <= r,  w := z - P in R^21 (Euclidean norm).
Then E(z) >= E(P), with equality only for z = P.   E(x) = sum_{i<j} phi(<x_i, x_j>), phi(t) = (2 - 2t)^(-1/2).

Proof checked here (all constants are rigorous arb bounds):
  1. P is a critical point of E on (S^2)^7: grad_i F(P) = mu_i P_i, with F(x) = sum phi(<x_i,x_j>) on (R^3)^7 and
     mu_i = sum_j phi'(t_ij) t_ij.  Exact reason: grad_i F(P) is invariant under the stabiliser of P_i in the
     symmetry group D_5h of P, whose fixed space is the line R P_i (poles: the 5-fold axis; ring points: the
     intersection of the horizontal mirror plane with the vertical mirror plane through P_i).  (Also checked
     numerically: the tangential part of every grad_i F(P) is a ball containing 0.)
  2. L(x) := F(x) - sum_i mu_i (|x_i|^2 - 1)/2.  For unit z:  E(z) - E(P) = L(z) - L(P) = (1/2) w^T M w + R3(w),
     M = Hess L(P),  |R3| <= C3 |w|^3 / 6  with C3 a bound of the third derivative of F on the segment [P, z]
     (the multiplier term is quadratic, so it has no third derivative).
  3. Split w = u + n, n_i = <w_i, P_i> P_i (normal part), u tangent.  |z_i| = |P_i| = 1 gives
     <w_i, P_i> = -|w_i|^2/2, so |n| <= |w|^2/2 and |u| >= |w| - |w|^2/2.
     The gauge condition says the skew part of sum_i w_i P_i^T vanishes, i.e. w is orthogonal to every rotation
     mode (A P_i)_i, A skew; the rotation modes are tangent and n is normal, so u lies in S := tangent ∩ rot^⊥.
  4. lambda := a certified lower bound of u^T M u / |u|^2 on S: the matrix
        A = Pi_S M Pi_S - lambda Pi_S + kappa (I - Pi_S)      (Pi_S the orthogonal projector onto S, kappa = 1)
     is shown positive definite by an LDL^T factorisation in arb with all pivots > 0.
  5. (1/2) w^T M w >= (1/2)(lambda |u|^2 - 2 |M| |u||n| - |M| |n|^2), |M| <= Frobenius norm, so
        E(z) - E(P) >= |w|^2 * ( (1/2)[lambda (1 - r/2)^2 - |M| (r + r^2/4)] - C3 r / 6 ) =: |w|^2 * G,
     and G > 0 gives the lemma (strict inequality for w != 0).
Third derivative: for a pair term phi(t), t = <x_i, x_j>, along a direction (a_i, a_j):
  d^3/ds^3 phi(t(s)) = phi''' t'^3 + 3 phi'' t' t'',  t' = <a_i, x_j> + <x_i, a_j>,  t'' = 2 <a_i, a_j>,
  with |x| <= 1 + r on the segment; |t'| <= (1+r)(|a_i| + |a_j|), |t''| <= 2|a_i||a_j| <= (|a_i| + |a_j|)^2 / 2.
  So |d^3| <= (|phi'''| (1+r)^3 + 1.5 |phi''| (1+r)) (|a_i| + |a_j|)^3, and sum_{i<j} (|a_i| + |a_j|)^3
  <= 4 sum_{i<j} (|a_i|^3 + |a_j|^3) = 24 sum_i |a_i|^3 <= 24 |a|^3 (each point is in 6 pairs).
  phi'', phi''' are positive and increasing on t < 1, so they are bounded by their values at
  max t_ij(P) + 2r + r^2 (max t_ij(P) = c1 < 1).

usage: python3 check_local1.py [r]     (default r = sqrt(7) * (11/2) * 1e-6, the cap chain with tau = 1e-6)
"""
import json, sys, time
import flint
from flint import arb, arb_mat

flint.ctx.prec = 256


def phi_d(t, k):
    """k-th derivative of (2-2t)^(-1/2) = (2k-1)!! (2-2t)^(-1/2-k)."""
    fac = 1
    for j in range(k):
        fac *= 2 * j + 1
    return arb(fac) / ((2 - 2 * t) ** k * (2 - 2 * t).sqrt())


def bipyramid():
    pi = arb.pi()
    pts = [[arb(0), arb(0), arb(1)], [arb(0), arb(0), arb(-1)]]
    for k in range(5):
        a = 2 * pi * k / 5
        pts.append([a.cos(), a.sin(), arb(0)])
    return pts


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), arb(0))


def ldl_pd(A, n):
    """True if every pivot of the LDL^T factorisation (no pivoting) is a ball > 0 (=> A positive definite)."""
    A = [[A[i, j] for j in range(n)] for i in range(n)]
    minpiv = None
    for k in range(n):
        d = A[k][k]
        if not d > 0:
            return False, None
        minpiv = d if minpiv is None or d.upper() < minpiv.upper() else minpiv
        for i in range(k + 1, n):
            l = A[i][k] / d
            for j in range(k + 1, i + 1):
                A[i][j] -= l * A[j][k]
                A[j][i] = A[i][j]
    return True, minpiv


def main(r=None):
    t0 = time.time()
    r = arb(7).sqrt() * arb(11) / 2 * arb(10) ** -6 if r is None else arb(r)
    P = bipyramid()
    n = 7
    T = [[dot(P[i], P[j]) for j in range(n)] for i in range(n)]
    rep = {"r": r.str(6)}
    # 1. criticality and multipliers
    mu = []
    crit_ok = True
    for i in range(n):
        g = [sum((phi_d(T[i][j], 1) * P[j][k] for j in range(n) if j != i), arb(0)) for k in range(3)]
        m = sum((phi_d(T[i][j], 1) * T[i][j] for j in range(n) if j != i), arb(0))
        mu.append(m)
        tang = [g[k] - m * P[i][k] for k in range(3)]
        crit_ok &= all(x.contains(0) for x in tang)
    rep["critical_point"] = crit_ok
    # 2. Hessian of L at P (21 x 21)
    N = 3 * n
    M = arb_mat(N, N)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            p2, p1 = phi_d(T[i][j], 2), phi_d(T[i][j], 1)
            for a in range(3):
                for b in range(3):
                    # d^2/dx_i dx_i : phi'' x_j x_j^T ;  d^2/dx_i dx_j : phi'' x_j x_i^T + phi' I
                    M[3 * i + a, 3 * i + b] += p2 * P[j][a] * P[j][b]
                    M[3 * i + a, 3 * j + b] += p2 * P[j][a] * P[i][b] + (p1 if a == b else 0)
        for a in range(3):
            M[3 * i + a, 3 * i + a] -= mu[i]
    # 3. projector onto S = tangent ∩ rot^⊥
    PiT = arb_mat(N, N)
    for i in range(n):
        for a in range(3):
            for b in range(3):
                PiT[3 * i + a, 3 * i + b] = (1 if a == b else 0) - P[i][a] * P[i][b]
    E = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    def cross(u, v):
        return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]
    R = arb_mat(N, 3)
    for k in range(3):
        for i in range(n):
            c = cross([arb(x) for x in E[k]], P[i])
            for a in range(3):
                R[3 * i + a, k] = c[a]
    G = R.transpose() * R
    PiS = PiT - R * G.inv() * R.transpose()
    I = arb_mat(N, N)
    for k in range(N):
        I[k, k] = 1
    # 4. lambda by bisection on a float guess, certified by LDL^T
    best = None
    lo, hi = 0.0, 1.0
    for _ in range(40):
        lam = (lo + hi) / 2
        A = PiS * M * PiS - arb(lam) * PiS + (I - PiS)
        ok, piv = ldl_pd(A, N)
        if ok:
            best, lo = lam, lam
        else:
            hi = lam
    lam = arb(best)
    rep["lambda_S_certified"] = best
    # 5. |M| (Frobenius), C3
    fro = sum((M[i, j] ** 2 for i in range(N) for j in range(N)), arb(0)).sqrt()
    tmin = min(T[i][j].lower() for i in range(n) for j in range(n) if i != j)
    tmax = max(T[i][j].upper() for i in range(n) for j in range(n) if i != j)
    span = 2 * r + r * r
    # phi'' and phi''' are positive and increasing on t < 1, so their maxima on the t-range are at its top
    ttop = arb(tmax) + span
    assert ttop < 1
    p2max, p3max = phi_d(ttop, 2).upper(), phi_d(ttop, 3).upper()
    C3 = 24 * (arb(p3max) * (1 + r) ** 3 + arb(1.5) * arb(p2max) * (1 + r))
    Gc = (lam * (1 - r / 2) ** 2 - fro * (r + r * r / 4)) / 2 - C3 * r / 6
    rep.update(M_frobenius=fro.str(6), t_range=[float(tmin), float(tmax)], phi2_max=float(p2max),
               phi3_max=float(p3max), C3=C3.str(6), G=Gc.str(6), G_positive=bool(Gc > 0))
    # largest radius that this argument covers (float, for information)
    lamf, frof, C3f = best, float(fro.upper()), float(C3.upper())
    rmax = lamf / (2 * (frof + C3f / 3 + lamf))
    rep["r_max_approx"] = rmax
    rep["LOCAL_OK"] = bool(crit_ok and Gc > 0)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    rep = main(float(sys.argv[1]) if len(sys.argv) > 1 else None)
    print(json.dumps(rep, indent=1))
    sys.exit(0 if rep["LOCAL_OK"] else 1)
