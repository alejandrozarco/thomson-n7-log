"""Second-order local lemma for the Riesz s-energy, N = 7, uniformly on an s-interval (python-flint arb, 256 bits).

Same statement and proof as ../cap1/check_local1.py (read its docstring), with phi_s(t) = (2 - 2t)^(-s/2) and the
exponent s an arb ball: every bound below is valid simultaneously for all s in [s_lo, s_hi].  Changes for general s:
  phi_s^(k)(t) = prod_{i<k} (s + 2i) * (2 - 2t)^(-s/2 - k)  (positive and increasing in t < 1 for s > 0, k = 2, 3);
  criticality of P holds for every s by the D_5h symmetry argument of check_local1.py (also checked: the tangential
  part of grad_i F(P) is a ball containing 0).
lambda on an s-interval [s0, s1] (h = s1 - s0) by chord + remainder: M(s) is linear in the 8 kernel values
f_{k,m}(s) = phi_s^(m)(t_k), m = 1, 2, t_k in {-1, 0, c1, c2} (the multipliers mu_i too), so with B = Pi_S M Pi_S and
theta = (s - s0)/h,  B(s) = (1 - theta) B(s0) + theta B(s1) + E(s),  ||E(s)||_2 <= (h^2/8) sum_{k,m} max|f_{k,m}''| ||B_{k,m}||_F
(B_{k,m} = Pi_S M(e_{k,m}) Pi_S).  So u^T B(s) u >= lambda |u|^2 on S for all s in [s0, s1] once B(s0) and B(s1) are
certified with lambda + eps (LDL^T as above, eps the bound on ||E||).  The remainder constants (|M|_F, C3) are
evaluated with s as a ball (upper bounds, valid on the whole piece).

usage: python3 check_localS.py grid                  # pointwise table, s = 0.05 .. 1.95
       python3 check_localS.py cover a b n [tau]     # n equal s-pieces of [a, b]; G > 0 on each, r from tau
       python3 check_localS.py one s_lo s_hi [tau]   # one interval (naive ball in s: too wide, use cover2)
       python3 check_localS.py cover2 a b [tau]      # adaptive chord+remainder cover of [a, b] -> cover2_*.jsonl
       python3 check_localS.py cover2q a b tau       # same, exact rational endpoints and tau -> cover2q_*.jsonl
tau (default 1e-6) is the coercivity window; r = sqrt(7) * (11/2) * tau as in the s = 1 chain.
Hygiene (REVIEW_range_fable.md M1): no min()/max() over arb balls: lambda bisection values are floats, and tmax is a
max over exact upper endpoints (exact points compare exactly).
Provenance (review S1): check_piece records carry `provenance` = sha256 of this file (the checker has no input files),
argv / command line / cwd and the call (s0, s1, tau); range_check.py compares the hash with the current file.
"""
import json, sys, time
from fractions import Fraction
import flint
from flint import arb, arb_mat

flint.ctx.prec = 256


_SELF_SHA = None


def provenance(call):
    """S1: bind a piece record to this checker's source (sha256, taken once per process) and to how it was run."""
    global _SELF_SHA
    import hashlib, os, platform, shlex
    me = os.path.abspath(__file__)
    if _SELF_SHA is None:
        _SELF_SHA = hashlib.sha256(open(me, "rb").read()).hexdigest()
    return dict(checker="check_localS.py", checker_path=me, checker_sha256=_SELF_SHA, inputs=[], call=call,
                argv=list(sys.argv), cmdline=shlex.join([sys.executable] + list(sys.argv)), cwd=os.getcwd(),
                python=platform.python_version(), flint=flint.__version__, started=time.strftime("%Y-%m-%d %H:%M:%S"))


def qarb(x):
    """arb ball containing the exact rational x (Fraction), or arb(x) for str/float."""
    from fractions import Fraction
    if isinstance(x, Fraction):
        return arb(x.numerator) / arb(x.denominator)
    return arb(x)


def sball(lo, hi):
    lo, hi = qarb(lo), qarb(hi)
    return (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())


def phi_d(t, k, s):
    fac = arb(1)
    for i in range(k):
        fac *= s + 2 * i
    u = 2 - 2 * t
    return fac * u ** (-s / 2 - k)


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
    A = [[A[i, j] for j in range(n)] for i in range(n)]
    for k in range(n):
        d = A[k][k]
        if not d > 0:
            return False
        for i in range(k + 1, n):
            l = A[i][k] / d
            for j in range(k + 1, i + 1):
                A[i][j] -= l * A[j][k]
                A[j][i] = A[i][j]
    return True


def frob(A, n1, n2):
    """Rigorous upper bound of the Frobenius norm (entrywise |x| <= upper, so balls around 0 do not give NaN)."""
    tot = arb(0)
    for i in range(n1):
        for j in range(n2):
            u = arb(abs(A[i, j]).upper())
            tot += u * u
    return arb(tot.upper()).sqrt()


P = bipyramid()
n, N = 7, 21
T = [[dot(P[i], P[j]) for j in range(n)] for i in range(n)]


def projector():
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
    return PiT - R * (R.transpose() * R).inv() * R.transpose()


PiS = projector()
I = arb_mat(N, N)
for k in range(N):
    I[k, k] = 1


def check(s, tau=1e-6, lam_hi=1.0):
    r = arb(7).sqrt() * arb(11) / 2 * arb(tau)
    mu, crit = [], True
    for i in range(n):
        g = [sum((phi_d(T[i][j], 1, s) * P[j][k] for j in range(n) if j != i), arb(0)) for k in range(3)]
        m = sum((phi_d(T[i][j], 1, s) * T[i][j] for j in range(n) if j != i), arb(0))
        mu.append(m)
        crit &= all((g[k] - m * P[i][k]).contains(0) for k in range(3))
    M = arb_mat(N, N)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            p2, p1 = phi_d(T[i][j], 2, s), phi_d(T[i][j], 1, s)
            for a in range(3):
                for b in range(3):
                    M[3 * i + a, 3 * i + b] += p2 * P[j][a] * P[j][b]
                    M[3 * i + a, 3 * j + b] += p2 * P[j][a] * P[i][b] + (p1 if a == b else 0)
        for a in range(3):
            M[3 * i + a, 3 * i + a] -= mu[i]
    B = PiS * M * PiS
    lo, hi, best = 0.0, lam_hi, None
    for _ in range(36):
        lam = (lo + hi) / 2
        if ldl_pd(B - arb(lam) * PiS + (I - PiS), N):
            best, lo = lam, lam
        else:
            hi = lam
    if best is None:
        return dict(LOCAL_OK=False, critical_point=crit, lambda_S=None)
    lam = arb(best)
    fro = frob(M, N, N)
    tmax = max(T[i][j].upper() for i in range(n) for j in range(n) if i != j)
    ttop = arb(tmax) + 2 * r + r * r
    assert ttop < 1
    p2max, p3max = phi_d(ttop, 2, s).upper(), phi_d(ttop, 3, s).upper()
    C3 = 24 * (arb(p3max) * (1 + r) ** 3 + arb(1.5) * arb(p2max) * (1 + r))
    G = (lam * (1 - r / 2) ** 2 - fro * (r + r * r / 4)) / 2 - C3 * r / 6
    rmax = best / (2 * (float(fro.upper()) + float(C3.upper()) / 3 + best))
    tau_max = rmax / (7 ** 0.5 * 5.5)
    return dict(s=s.str(5), lambda_S=best, fro=float(fro.upper()), C3=float(C3.upper()), G=G.str(4),
                r_max=rmax, tau_max=tau_max, critical_point=crit, LOCAL_OK=bool(crit and G > 0))


if __name__ == "__main__":
    t0 = time.time()
    mode = sys.argv[1]
    if mode == "grid":
        for s in [0.01, 0.05, 0.1, 0.25, 0.5, 0.75, 1, 1.25, 1.5, 1.75, 1.9, 1.95, 1.99]:
            print(json.dumps(check(arb(s))), flush=True)
    elif mode == "one":
        tau = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-6
        print(json.dumps(check(sball(sys.argv[2], sys.argv[3]), tau)))
    elif mode == "cover":
        a, b, m = float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
        tau = float(sys.argv[5]) if len(sys.argv) > 5 else 1e-6
        ok = True
        for k in range(m):
            lo, hi = a + (b - a) * k / m, a + (b - a) * (k + 1) / m
            rep = check(sball(repr(lo), repr(hi)), tau)
            ok &= rep["LOCAL_OK"]
            print(json.dumps(dict(piece=[lo, hi], **rep)), flush=True)
        print(json.dumps(dict(cover=[a, b], pieces=m, tau=tau, ALL_OK=ok, time_s=round(time.time() - t0, 1))))


# ---- interval mode: chord + remainder (see docstring) ----
C1V, C2V = (arb(5).sqrt() - 1) / 4, -(1 + arb(5).sqrt()) / 4
TCLS = [arb(-1), arb(0), C1V, C2V]


def tclass(t):
    for k, c in enumerate(TCLS):
        if (t - c).contains(0) or abs(float(t.mid()) - float(c.mid())) < 1e-30:
            return k
    raise ValueError(t)


TIDX = [[tclass(T[i][j]) if i != j else None for j in range(n)] for i in range(n)]


def hess_from(vals):
    """M as a function of vals[(k, m)] = phi^(m)(t_k), m = 1, 2 (linear)."""
    mu = [sum((vals[(TIDX[i][j], 1)] * T[i][j] for j in range(n) if j != i), arb(0)) for i in range(n)]
    M = arb_mat(N, N)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            p2, p1 = vals[(TIDX[i][j], 2)], vals[(TIDX[i][j], 1)]
            for a in range(3):
                for b in range(3):
                    M[3 * i + a, 3 * i + b] += p2 * P[j][a] * P[j][b]
                    M[3 * i + a, 3 * j + b] += p2 * P[j][a] * P[i][b] + (p1 if a == b else 0)
        for a in range(3):
            M[3 * i + a, 3 * i + a] -= mu[i]
    return M


def kvals(s):
    return {(k, m): phi_d(TCLS[k], m, s) for k in range(4) for m in (1, 2)}


def f_dd(k, m, s):
    """d^2/ds^2 of phi_s^(m)(t_k) = c(s) exp(-(s/2 + m) L), c(s) = prod_{i<m} (s + 2i), L = log(2 - 2 t_k)."""
    L = (2 - 2 * TCLS[k]).log()
    # c, c', c'' for m = 1: s ; m = 2: s (s + 2)
    if m == 1:
        c, c1, c2 = s, arb(1), arb(0)
    else:
        c, c1, c2 = s * (s + 2), 2 * s + 2, arb(2)
    e = (-(s / 2 + m) * L).exp()
    return (c2 - c1 * L + c * L * L / 4) * e


BBASIS = {}
for k in range(4):
    for m in (1, 2):
        v = {(kk, mm): arb(1 if (kk, mm) == (k, m) else 0) for kk in range(4) for mm in (1, 2)}
        Bk = PiS * hess_from(v) * PiS
        BBASIS[(k, m)] = frob(Bk, N, N)


def lam_point(s, lam_hi=1.0, shift=0.0):
    B = PiS * hess_from(kvals(s)) * PiS
    lo, hi, best = 0.0, lam_hi, None
    for _ in range(36):
        lam = (lo + hi) / 2
        if ldl_pd(B - (arb(lam) + shift) * PiS + (I - PiS), N):     # shift: arb (rigorous upper bound) or float
            best, lo = lam, lam
        else:
            hi = lam
    return best


def check_piece(s0, s1, tau=1e-6):
    from fractions import Fraction
    prov = provenance(dict(function="check_localS.check_piece", s0=str(s0), s1=str(s1), tau=str(tau),
                           exact=isinstance(s0, Fraction) and isinstance(s1, Fraction) and isinstance(tau, Fraction)))
    if not isinstance(s0, Fraction):
        s0, s1 = repr(s0), repr(s1)
    sb = sball(s0, s1)
    h = qarb(s1) - qarb(s0)
    eps = h * h / 8 * sum((abs(f_dd(k, m, sb)) * BBASIS[(k, m)] for k in range(4) for m in (1, 2)), arb(0))
    eps_f = float(eps.upper())
    l0, l1 = lam_point(qarb(s0), shift=eps.upper()), lam_point(qarb(s1), shift=eps.upper())   # exact upper bound, no rounding
    if l0 is None or l1 is None:
        return dict(LOCAL_OK=False, eps=eps_f, lambda_S=None, provenance=prov)
    best = min(l0, l1)          # floats from the bisection (each certified with the shift), not balls
    lam = arb(best)
    r = arb(7).sqrt() * arb(11) / 2 * qarb(tau)
    M = hess_from(kvals(sb))
    fro = frob(M, N, N)
    tmax = max(T[i][j].upper() for i in range(n) for j in range(n) if i != j)
    ttop = arb(tmax) + 2 * r + r * r
    assert ttop < 1
    p2max, p3max = phi_d(ttop, 2, sb).upper(), phi_d(ttop, 3, sb).upper()
    C3 = 24 * (arb(p3max) * (1 + r) ** 3 + arb(1.5) * arb(p2max) * (1 + r))
    G = (lam * (1 - r / 2) ** 2 - fro * (r + r * r / 4)) / 2 - C3 * r / 6
    return dict(eps=eps_f, lambda_S=best, G=G.str(4), LOCAL_OK=bool(G > 0), provenance=prov)


def cover2(a, b, tau=1e-6, h0=0.02):
    """Adaptive cover of [a, b]; halves a piece until it passes (down to 1e-6), then tries to grow."""
    pieces, s, h, ok = [], a, h0, True
    while s < b - 1e-15:
        s1 = min(b, s + h)
        rep = check_piece(s, s1, tau)
        if rep["LOCAL_OK"]:
            pieces.append(dict(piece=[s, s1], **rep))
            s, h = s1, h * 1.5
        else:
            h /= 2
            if h < 1e-6:
                ok = False
                pieces.append(dict(piece=[s, s1], FAILED=True, **rep))
                break
    return ok, pieces


def cover2q(a, b, tau, h0):
    """cover2 with exact rational piece endpoints and exact rational tau (Fractions): the certified pieces are the
    closed intervals [s, s1] with s, s1 rational exactly as written, and r = sqrt7 (11/2) tau for the exact tau."""
    pieces, s, h, ok = [], a, h0, True
    while s < b:
        s1 = min(b, s + h)
        rep = check_piece(s, s1, tau)
        if rep["LOCAL_OK"]:
            pieces.append(dict(piece=[str(s), str(s1)], **rep))
            s, h = s1, h * 3 / 2
        else:
            h /= 2
            if h < Fraction(1, 10**6):
                ok = False
                pieces.append(dict(piece=[str(s), str(s1)], FAILED=True, **rep))
                break
    return ok, pieces


if __name__ == "__main__" and sys.argv[1] == "cover2q":
    # python3 check_localS.py cover2q a b tau     (a, b, tau exact decimals or p/q, e.g. 1/2 3/2 1e-6)
    from fractions import Fraction
    t0 = time.time()
    a, b, tau = Fraction(sys.argv[2]), Fraction(sys.argv[3]), Fraction(sys.argv[4])
    ok, pieces = cover2q(a, b, tau, Fraction(1, 50))
    fn = f"cover2q_{sys.argv[2].replace('/', 'o')}_{sys.argv[3].replace('/', 'o')}_tau{sys.argv[4]}.jsonl"
    with open(fn, "w") as f:
        for p in pieces:
            f.write(json.dumps(p) + "\n")
    print(json.dumps(dict(cover=[str(a), str(b)], tau=str(tau), exact=True, pieces=len(pieces), ALL_OK=ok,
                          last=pieces[-1], time_s=round(time.time() - t0, 1))))

if __name__ == "__main__" and sys.argv[1] == "cover2":
    t0 = time.time()
    a, b = float(sys.argv[2]), float(sys.argv[3])
    tau = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-6
    ok, pieces = cover2(a, b, tau)
    with open(f"cover2_{a}_{b}_tau{tau}.jsonl", "w") as f:
        for p in pieces:
            f.write(json.dumps(p) + "\n")
    print(json.dumps(dict(cover=[a, b], tau=tau, pieces=len(pieces), ALL_OK=ok, last=pieces[-1],
                          time_s=round(time.time() - t0, 1))))
