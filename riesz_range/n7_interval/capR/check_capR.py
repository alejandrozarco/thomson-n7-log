"""Rigorous piece check for the N = 7 cap certificate on an s-interval [a, b] (capR/DESIGN.md, section 2).

usage: python3 check_capR.py CERT_a.json[.gz] CERT_b.json[.gz] cert_dirs_D12.json a b [delta] [TAU_DEN]
       (a, b rational strings such as 11/12 1; delta default 1e-16; TAU_DEN default 10^6; exit status 0 iff PIECE_OK)
       env NSUB=n (default 1): PSD step P also uses the sampled chord bound (S_n) on n equal sub-intervals, see P below;
       NSUB=1 is the original P step, unchanged.  env M_TWOSIDED=1: the original two-sided s-remainder in M (default:
       one-sided, see M below).  NSUB=1 M_TWOSIDED=1 is the original checker.

Self-contained: exact rationals (python-flint fmpq) and ball arithmetic (arb, 256 bits); no other file of this
project is imported.  Kernel phi_s(t) = (2 - 2t)^(-s/2), 0 < s < 2; cap cell t01 in [-1, -99/100]; contacts
t in {-1, 0, c1, c2}, c1 = (-1 + sqrt5)/4, c2 = (-1 - sqrt5)/4; E_s(P) = phi_s(-1) + 10 phi_s(0) + 5 phi_s(c1) + 5 phi_s(c2).

OBJECTS.  A "certificate vector" C consists of reduced kernel blocks R (F = N R N^T), reduced SOS blocks R_r
(B_r = N_r R_r N_r^T), polynomials H_A, H_B, H_C, psi_Ba, psi_Cb of degree 12 (rational monomial coefficients), and
scalars c_alpha, c_beta, e.  Input: two node certificates C_a, C_b (format of ../capS/round_capS.py, with exact PSD
data L, d per block) and seven directions C_1..C_7 (format of round_dirs.py, no PSD data).
The kernel data of phi_s is the vector
    v(s) = ( phi_s(0), phi_s'(0), phi_s(-1), Re phi_s(c1), Im phi_s(c1), Re phi_s'(c1), Im phi_s'(c1) ),
Re/Im with respect to Q(sqrt5): x = Re + Im sqrt5 (so Re phi(c1) = (phi(c1) + phi(c2))/2 etc.).  The pin map
    Pin(C) = ( H_B(0), H_B'(0), H_A(-1), Re H_C(c1), Im H_C(c1), Re H_C'(c1), Im H_C'(c1) )
is linear with rational coefficients (c1^j = x_j + y_j sqrt5 with x_j, y_j rational).  Since H_C has rational
coefficients, Pin(C) = v(s) implies H_C(c2) = phi_s(c2), H_C'(c2) = phi_s'(c2) (Galois conjugation).

WHAT IS CHECKED EXACTLY (over Q):
  E1. all nine objects have the cap's multipliers, the same face matrices N, and satisfy the three polynomial
      identities lambda_T = sum_r g_r z^T B_r z of check_capS.py coefficientwise (with c_gamma from (6));
  E2. the e-row  e = H_A(-1) + 10 H_B(0) + 10 Re H_C(c1)  for all nine objects;
  E3. Pin(C_k) = e_k for the seven directions;  v~_a := Pin(C_a), v~_b := Pin(C_b) are recorded;
  E4. for both nodes and every block, R = L diag(d) L^T + Delta with d >= 0 and Delta diagonally dominant with row
      slack >= sigma_blk > 0, hence R >= sigma_blk I.  In addition mu_j >= sigma_j is certified by an arb LDL^T
      of R_j - mu_j I (every matrix in the ball is PD, R_j exact);  mu_blk := min(mu_a, mu_b).
THE FAMILY.  For s in [a, b], h = b - a, lambda = (s - a)/h,
    C(s) := (1 - lambda) C_a + lambda C_b + sum_k rho_k(s) C_k,   rho_k(s) := v_k(s) - (1 - lambda) v~_{a,k} - lambda v~_{b,k}.
By linearity and E1-E3: C(s) satisfies the identities and (6) exactly, Pin(C(s)) = v(s), and by E2
e(s) = phi_s(-1) + 10 phi_s(0) + 10 Re phi_s(c1) = E_s(P), for every s.  So f_X(t, s) := phi_s(t) - H_X(t; s) has
f_B(0, s) = f_B'(0, s) = 0, f_C(c_i, s) = f_C'(c_i, s) = 0, f_A(-1, s) = 0 for every s (' = d/dt).
WHAT IS CHECKED IN BALL ARITHMETIC (every bound valid simultaneously for all s in [a, b]):
  P.  PSD of every reduced block R(s) = (1 - lambda) R_a + lambda R_b + sum_k rho_k(s) R_k.  With the mean-value
      form of the linear interpolation error, rho_k(s) = -lambda(1 - lambda)(h^2/2) v_k''(xi_k) + delta_k(s),
      xi_k in [a, b], |delta_k| <= eps_k := max_j |v_k(s_j) - v~_{j,k}|.  With w := v''(s_m), s_m = (a + b)/2, and
      |v_k''(xi_k) - w_k| <= (h/2) M3_k, M3_k >= sup_[a,b] |v_k'''|, one gets for every block
         R(s) >= [ mu_blk - (h^2/8) ( tau_blk + (h/2) sum_k M3_k F_k ) - sum_k eps_k F_k ] I =: slackW_blk I,
      where tau_blk >= lambda_max(sum_k w_k R_k) is certified by an arb LDL^T of tau I - sum_k w_k R_k, and
      F_k >= ||R_k||_2 is the Frobenius norm.  This is bound (W).
      Sampled chord bound (S_n), only if NSUB = n >= 2.  Put d = h/n, s_i = a + i d (rational), lambda_i = i/n.
      Write R(s) = A(s) + sum_k v_k(s) R_k with A(s) := (1 - lambda) R_a + lambda R_b - sum_k [(1 - lambda) v~_{a,k}
      + lambda v~_{b,k}] R_k, which is affine in s.  On [s_i, s_{i+1}], theta = (s - s_i)/d, the chord of the affine A
      is A itself, so exactly
         R(s) = (1 - theta) R(s_i) + theta R(s_{i+1}) + sum_k [v_k(s) - (1 - theta) v_k(s_i) - theta v_k(s_{i+1})] R_k,
      and the bracket is -theta(1 - theta)(d^2/2) v_k''(xi_k) with xi_k in [s_i, s_{i+1}] (v_k is C^2).  Since xi_k
      is still in [a, b], |v_k''(xi_k) - w_k| <= (h/2) M3_k with the same w = v''(s_m) and M3, so the same argument as
      for (W) gives sum_k [...] R_k >= -theta(1 - theta)(d^2/2) (tau_blk + (h/2) sum_k M3_k F_k) I (tau_blk > 0 and
      the cubic sum are >= 0, theta(1 - theta) <= 1/4), and the chord part is >= min(m_i, m_{i+1}) I.  Hence
         R(s) >= [ min_{0<=i<=n} m_i - (h^2/(8 n^2)) ( tau_blk + (h/2) sum_k M3_k F_k ) ] I =: slackS_blk I
      for all s in [a, b], where m_i <= lambda_min(R(s_i)) is certified by an arb LDL^T of R(s_i) - m_i I for the
      ball matrix R(s_i) = (1 - lambda_i) R_a + lambda_i R_b + sum_k rho_k(s_i) R_k, rho_k(s_i) = v_k(s_i) -
      (1 - lambda_i) v~_{a,k} - lambda_i v~_{b,k} (exact R_a, R_b, R_k, v~; arb v_k(s_i)): this is the exact family
      at s_i, so no pin-error term appears (at i = 0, n it contains the pin error itself).  tau_blk and the cubic sum
      are reused unchanged at length d (valid, slightly conservative: the cubic factor stays h/2, not d/2).
      Checked: slack_blk > 0 for every block, where slack_blk = slackW_blk (NSUB = 1) or max(slackW_blk, slackS_blk)
      (NSUB >= 2; both are valid lower bounds of lambda_min(R(s)) on [a, b]).
  M.  Minorants.  For fixed t, f(t, s) = g_t(s) - (1 - lambda) H^_a(t) - lambda H^_b(t) with
      g_t(s) = phi_s(t) - sum_k v_k(s) H_k(t) and s-free H^_j = H_j - sum_k v~_{j,k} H_k, so
         f(t, s) >= min(f(t, a), f(t, b)) - (h^2/8) G_t^+,   G_t^+ >= max(0, sup_[a,b] d^2 g_t/ds^2)   (one-sided).
      Proof: E(s) := f(t, s) - [(1 - lambda) f(t, a) + lambda f(t, b)] has E(a) = E(b) = 0 and, since f - g_t is affine
      in s, E'' = g_t'' <= G_t^+ on [a, b].  So E + (G_t^+/2)(s - a)(b - s) is concave with zero ends, hence >= 0, i.e.
      E >= -(G_t^+/2)(s - a)(b - s) >= -(h^2/8) G_t^+, and the chord is >= min(f(t, a), f(t, b)).  Only the positive
      part of g_t'' costs (where f is concave in s it lies above its chord).  The upper bound is Taylor in s about s_m:
         sup_[a,b] g_t'' <= upper( g_t''(s_m) ) + (h/2) |g_t'''(s_m)| + (h^2/8) sup_[a,b] |g_t''''|,
      evaluated in arb with t the whole t-cell (a ball) of the bisection, s_m exact, and s the ball [a, b] in the last
      term; G_t^+ := max(0, that upper bound), so it bounds sup g_t'' over the (t, s) box.  With M_TWOSIDED=1 the
      original two-sided bound is used instead: G_t := |g_t''(s_m)| + (h/2) |g_t'''(s_m)| + (h^2/8) sup |g_t''''|
      >= sup_[a,b] |g_t''| (always G_t >= G_t^+).  Derivatives in s of phi_s^(m)(t) = P_m(s) u^(-s/2-m), u = 2 - 2t,
      P_m(s) = prod_{i<m} (s + 2i), are explicit.  The same holds for d/dt and d^2/dt^2 of f (the window conditions),
      with g_t^(m) in place of g_t, since f^(m) - g_t^(m) is affine in s as well.
      Node values f(t, s_j) use the mean-value form in t.  Checked, by adaptive bisection in t:
      outside the contact windows (|t| <= rB for B, |t - c_i| <= rC for C, t + 1 <= rA for A): f > delta;
      on the windows: f'' >= mB > 0 (B), f'' >= mC > 0 (C), f' >= mA > 0 (A), hence, with the exact double zeros,
      f >= (mB/2) t^2, f >= (mC/2)(t - c_i)^2, f >= mA (t + 1) there;  near t = 1: phi_s(t) >= (2 eps1)^(-a/2) > sup H.
      Together: H_A(.; s) <= phi_s on [-1, -99/100] and H_B, H_C(.; s) <= phi_s on [-1, 1) for all s in [a, b].
  K.  Coercivity: f_X(t, s) <= delta implies |t - c| <= tau for a contact c of X, with
      tau_B = sqrt(2 delta / mB), tau_C = sqrt(2 delta / mC), tau_A = delta / mA; decided exactly: tau <= 1/TAU_DEN.
      (delta >= E_s(P) - e(s) = 0 holds for every delta >= 0.)
  Hygiene (REVIEW_range_fable.md, 2026-11-07).  M1: lower bounds over several balls are combined with lo_min (the
      exact smallest lower endpoint), upper bounds with hi_max (the exact largest upper endpoint), never with
      Python's min()/max() on arb (for overlapping balls both a < b and b < a are False, so min() would silently keep
      its first argument).  M2: every reduced block (nodes and directions) is checked to be exactly symmetric when
      loaded (ldl_pd reads only the lower triangle).  Both only make the checker stricter.
  Provenance (S1): the report carries `provenance` = sha256 of this file, sha256 of every input file (two node
      certificates, the directions file), argv / command line / cwd, and the effective settings (NSUB, M_TWOSIDED,
      NWIN, N0, MAXDEPTH, RB, RC, RA, precision); range_check.py compares these hashes with the current files.
PIECE_OK := E1-E4 and P and M and K.  P is checked by (W), or with NSUB >= 2 by (W) or (S_n) per block; M and the
window bounds use the one-sided s-remainder G^+ (default) or the two-sided G (M_TWOSIDED=1).  The variants differ only in
how sharp the bounds are, not in what they conclude: every reduced block of C(s) is positive definite, and f_X(., s)
satisfies the minorant, window and coercivity bounds of M and K, for every s in [a, b].  It means: for every s in [a, b], C(s) is an exact three-point cap certificate
for phi_s with e(s) = E_s(P), PSD blocks and valid minorants, and the coercivity windows have width <= 1/TAU_DEN;
these are precisely the cap facts consumed by the single-s chain (cap1/STATUS_s1.md: K2-K4 with delta, then K6-K9 and
the local lemma localS/check_localS.py).
Not checked here: the local lemma, the cells, and that 1/TAU_DEN is small enough for them.
"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq, fmpz

flint.ctx.prec = 256
NWIN = int(os.environ.get("NWIN", "400"))       # env RB, RC, RA: contact window radii (rationals), see main()       # subdivisions of each contact window (mean-value form, so 400 suffices)
N0 = int(os.environ.get("N0", "64"))            # initial pieces of the adaptive covers
NSUB = int(os.environ.get("NSUB", "1"))         # P step: sub-intervals of the sampled chord bound (S_n); 1 = bound (W) only
M_TWOSIDED = os.environ.get("M_TWOSIDED", "0") == "1"   # M step: 1 = original two-sided s-remainder (h^2/8) sup|g''|
MAXDEPTH = 40
T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


# ============================================================ provenance (S1)
def sha256_file(p):
    import hashlib
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def provenance(inputs):
    """S1: bind the report to this checker's source and to the exact input files (sha256), plus how it was run."""
    import platform, shlex
    me = os.path.abspath(__file__)
    settings = dict(NSUB=NSUB, M_TWOSIDED=M_TWOSIDED, NWIN=NWIN, N0=N0, MAXDEPTH=MAXDEPTH, prec=flint.ctx.prec,
                    **{k: os.environ.get(k, d) for k, d in (("RB", "1/20"), ("RC", "1/50"), ("RA", "1/500"))})
    return dict(checker="check_capR.py", checker_path=me, checker_sha256=sha256_file(me),
                inputs=[dict(path=p, name=os.path.basename(p), sha256=sha256_file(p)) for p in inputs],
                argv=list(sys.argv), cmdline=shlex.join([sys.executable] + list(sys.argv)), cwd=os.getcwd(),
                settings=settings, python=platform.python_version(), flint=flint.__version__,
                started=time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(T0)))


# ============================================================ sound min / max over balls (M1)
def lo_min(xs):
    """M1: an exact ball (radius 0) at the smallest lower endpoint of the balls xs, i.e. a lower bound valid for every
    one of them.  Python's min() is not sound for arb: if two balls overlap, a < b and b < a are both False and min()
    keeps its first argument even when another ball reaches lower.  Lower endpoints are exact points, which compare
    exactly; a non-finite lower endpoint (infinite or NaN ball) gives -inf, which fails every test `> need`."""
    out = None
    for x in xs:
        l_ = x.lower()
        if not l_.is_finite():
            return arb(float("-inf"))
        if out is None or l_ < out:
            out = l_
    return arb(out)


def hi_max(xs):
    """M1: an exact ball at the largest upper endpoint of the balls xs (an upper bound valid for every one of them);
    a non-finite upper endpoint gives +inf."""
    out = None
    for x in xs:
        u_ = x.upper()
        if not u_.is_finite():
            return arb(float("inf"))
        if out is None or u_ > out:
            out = u_
    return arb(out)


def argmin_lower(xs):
    """M1: index of a ball with the smallest lower endpoint (ties: the first); used only to keep report fields
    (piece counts) attached to the bound that is reported."""
    lows = [x.lower() for x in xs]
    k = 0
    for i, l_ in enumerate(lows):
        if not l_.is_finite():
            return i
        if l_ < lows[k]:
            k = i
    return k


def is_symmetric(R):
    """M2: exact symmetry of a reduced block (fmpq entries)."""
    n = len(R)
    return all(len(R[i]) == n for i in range(n)) and all(R[i][j] == R[j][i] for i in range(n) for j in range(i))


# ============================================================ exact polynomials {(a,b,c): fmpq}
Q0 = fmpq(0)


def Qs(s):
    f = Fr(s)
    return fmpq(fmpz(f.numerator), fmpz(f.denominator))


def P_add(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        w = r.get(k, Q0) + c * v
        if w == 0:
            r.pop(k, None)
        else:
            r[k] = w
    return r


def P_scale(p, c):
    return {k: v * c for k, v in p.items()} if c != 0 else {}


def P_mul(p, q):
    r = {}
    for (a1, b1, c1), v1 in p.items():
        for (a2, b2, c2), v2 in q.items():
            k = (a1 + a2, b1 + b2, c1 + c2)
            r[k] = r.get(k, Q0) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}


def P_perm(p, order):
    r = {}
    for e, v in p.items():
        ne = [0, 0, 0]
        for slot in range(3):
            ne[order[slot]] += e[slot]
        ne = tuple(ne)
        r[ne] = r.get(ne, Q0) + v
    return {k: v for k, v in r.items() if v != 0}


def P_subst_diag(p, one_slot):
    r = {}
    for e, v in p.items():
        deg = sum(e[s] for s in range(3) if s != one_slot)
        k = (deg, 0, 0)
        r[k] = r.get(k, Q0) + v
    return {k: v for k, v in r.items() if v != 0}


def P_at111(p):
    return sum(p.values(), Q0)


def univ(coefs, var):
    out = {}
    for j, c in enumerate(coefs):
        if c != 0:
            e = [0, 0, 0]; e[var] = j
            out[tuple(e)] = c
    return out


ONE = {(0, 0, 0): fmpq(1)}
Uu = {(1, 0, 0): fmpq(1)}; Vv = {(0, 1, 0): fmpq(1)}; Tt = {(0, 0, 1): fmpq(1)}


def Qk_list(kmax):
    W = P_mul(P_add(ONE, P_mul(Uu, Uu), -1), P_add(ONE, P_mul(Vv, Vv), -1))
    tuv = P_add(Tt, P_mul(Uu, Vv), -1)
    Q = [ONE, tuv]
    while len(Q) <= kmax:
        Q.append(P_add(P_scale(P_mul(tuv, Q[-1]), fmpq(2)), P_mul(W, Q[-2]), -1))
    return Q


def form(Fs, Q):
    s = {}
    for k, F in enumerate(Fs):
        m = len(F)
        Puv = {}
        for a in range(m):
            for b in range(m):
                if F[a][b] != 0:
                    Puv[(a, b, 0)] = Puv.get((a, b, 0), Q0) + F[a][b]
        if Puv:
            s = P_add(s, P_mul(Puv, Q[k]))
    return s


def lam_polys(c):
    """exactly check_capS.lam_polys (fmpq arithmetic)."""
    kmax = max(len(c["FP"]), len(c["FR"])) - 1
    Q = Qk_list(kmax)
    sP = form(c["FP"], Q); sR = form(c["FR"], Q)
    gm = {}
    for X, s in (("P", sP), ("R", sR)):
        gm[X] = P_add(P_add(P_subst_diag(s, 0), P_subst_diag(s, 1)), P_subst_diag(s, 2))
    oneP, oneR = P_at111(sP), P_at111(sR)
    cg = (c["e"] + 2 * oneP + 5 * oneR - 5 * c["ca"] - 20 * c["cb"]) * fmpq(1, 10)
    PsiA = P_add(univ(c["hA"], 0), gm["P"], -2)
    PsiB = P_add(P_add(univ(c["hB"], 0), gm["P"], -1), gm["R"], -1)
    PsiC = P_add(univ(c["hC"], 0), gm["R"], -2)
    pBa = univ(c["pBa"], 0); pCb = univ(c["pCb"], 0)
    to_v = lambda p: P_perm(p, (1, 0, 2)); to_t = lambda p: P_perm(p, (2, 1, 0))
    kerA = P_add(P_add(sP, P_perm(sP, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    kerB = P_add(P_add(sP, P_perm(sR, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    kerG = P_add(P_add(sR, P_perm(sR, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    lamA = P_add(P_add(P_add(P_scale(PsiA, fmpq(1, 5)), to_v(pBa)), to_t(pBa)), {(0, 0, 0): c["ca"]}, -1)
    lamA = P_add(lamA, kerA, -2)
    QB = P_scale(P_add(PsiB, pBa, -1), fmpq(1, 4))
    lamB = P_add(P_add(P_add(QB, to_v(QB)), to_t(pCb)), {(0, 0, 0): c["cb"]}, -1)
    lamB = P_add(lamB, kerB, -2)
    QC = P_scale(P_add(PsiC, pCb, -2), fmpq(1, 3))
    lamG = P_add(P_add(P_add(QC, to_v(QC)), to_t(QC)), {(0, 0, 0): cg}, -1)
    lamG = P_add(lamG, kerG, -2)
    return dict(A=lamA, B=lamB, G=lamG, cg=cg)


def monos_upto(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


def required_multipliers(lo, hi, dA):
    d5, d4, d3 = dA
    lin = lambda var, c0: P_add(univ([Q0, fmpq(1)], var), {(0, 0, 0): c0}, -1)
    om = lambda var: P_add(ONE, univ([Q0, fmpq(1)], var), -1)
    detG = P_add(P_add(P_add(P_add(ONE, P_mul(P_mul(Uu, Vv), Tt), 2), P_mul(Uu, Uu), -1), P_mul(Vv, Vv), -1), P_mul(Tt, Tt), -1)
    him = P_add({(0, 0, 0): hi}, Uu, -1)
    A = [(ONE, d5), (lin(0, lo), d4), (him, d4), (lin(1, lo), d4), (lin(2, lo), d4), (om(1), d4), (om(2), d4),
         (detG, d3), (P_mul(lin(0, lo), him), d4)]
    BG = [(ONE, d5), (lin(0, lo), d4), (lin(1, lo), d4), (lin(2, lo), d4), (om(0), d4), (om(1), d4), (om(2), d4), (detG, d3)]
    return {"A": A, "B": BG, "G": BG}


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0]) if B else 0
    Bt = list(zip(*B)) if B else []
    return [[sum((A[i][l] * Bt[j][l] for l in range(k) if A[i][l] != 0 and Bt[j][l] != 0), Q0) for j in range(m)]
            for i in range(n)]


def congruence(N, X):
    if not N or not N[0]:
        n = len(N); return [[Q0] * n for _ in range(n)]
    NX = matmul(N, X)
    Nt = [list(r) for r in zip(*N)]
    return matmul(NX, Nt)


def psd_slack(X, L, d):
    """X == L diag(d) L^T + Delta, d >= 0, Delta diagonally dominant with row slack >= sigma  =>  X >= sigma I.
    returns (ok, sigma) with sigma the minimal row slack (fmpq)."""
    n = len(X)
    if n == 0:
        return True, None
    if any(x < 0 for x in d):
        return False, "negative pivot"
    for i in range(n):
        if L[i][i] != 1 or any(L[i][j] != 0 for j in range(i + 1, n)):
            return False, "L not unit lower triangular"
        if X[i] != [X[j][i] for j in range(n)]:
            return False, "not symmetric"
    worst = None
    for i in range(n):
        row = []
        for j in range(n):
            s = sum((L[i][q] * d[q] * L[j][q] for q in range(min(i, j) + 1) if L[i][q] != 0 and L[j][q] != 0), Q0)
            row.append(X[i][j] - s)
        slack = row[i] - sum(abs(row[j]) for j in range(n) if j != i)
        worst = slack if worst is None else min(worst, slack)
    return worst > 0, worst


def Qmat(M):
    return [[Qs(x) for x in row] for row in M]


def sqrt5_powers(n=13):
    pw = [(fmpq(1), Q0)]
    for _ in range(n):
        x, y = pw[-1]; pw.append((x * fmpq(-1, 4) + 5 * y * fmpq(1, 4), x * fmpq(1, 4) + y * fmpq(-1, 4)))
    return pw


PW = sqrt5_powers()


def pin_map(hA, hB, hC):
    """Pin(C) as 7 fmpq."""
    return [hB[0], hB[1], sum((hA[j] * (-1) ** j for j in range(13)), Q0),
            sum((hC[j] * PW[j][0] for j in range(13)), Q0), sum((hC[j] * PW[j][1] for j in range(13)), Q0),
            sum((hC[j] * j * PW[j - 1][0] for j in range(1, 13)), Q0), sum((hC[j] * j * PW[j - 1][1] for j in range(1, 13)), Q0)]


def load_object(J, name, req, Nref, want_psd):
    """exact checks E1 (identities, multipliers, face), E2 (e-row), and for nodes E4; returns a dict."""
    rep = {}
    c = {"hA": [Qs(x) for x in J["H"]["A"]], "hB": [Qs(x) for x in J["H"]["B"]], "hC": [Qs(x) for x in J["H"]["C"]],
         "pBa": [Qs(x) for x in J["psi"]["Ba"]], "pCb": [Qs(x) for x in J["psi"]["Cb"]],
         "ca": Qs(J["ca"]), "cb": Qs(J["cb"]), "e": Qs(J["e"])}
    assert all(len(c[k]) == 13 for k in ("hA", "hB", "hC", "pBa", "pCb"))
    red = {}; N = {}; sigma = {}
    ok = True
    # M2: every reduced block must be exactly symmetric, for the nodes AND the directions (want_psd = False skips
    # psd_slack, which was the only symmetry test).  ldl_pd below reads only the lower triangle and the identities
    # only see the symmetric part of N R N^T, so a non-symmetric R_k would otherwise pass E1 while P certified a
    # different matrix than the one entering z^T B(s) z.
    asym = []
    for X in "PR":
        mats = []
        for k, blk in enumerate(J["F"][X]):
            nm = f"F{X}{k}"; Nm = Qmat(blk["N"]); R = Qmat(blk["red"])
            N[nm] = Nm; red[nm] = R
            if R and not is_symmetric(R):
                asym.append(nm); ok = False
            if R:
                if want_psd:
                    good, sg = psd_slack(R, Qmat(blk["L"]), [Qs(x) for x in blk["d"]])
                    ok &= good; sigma[nm] = sg
                mats.append(congruence(Nm, R))
            else:
                mats.append([[Q0] * blk["m"] for _ in range(blk["m"])])
        c["F" + X] = mats
    lam = lam_polys(c)
    for tag in ("A", "B", "G"):
        rhs = {}
        blocks = J["SOS"][tag]
        assert len(blocks) == len(req[tag]), f"{name}: wrong number of SOS blocks in {tag}"
        for r, blk in enumerate(blocks):
            nm = f"{tag}_B{r}"
            g = {tuple(int(x) for x in k.split(",")): Qs(v) for k, v in blk["g"].items()}
            greq, dreq = req[tag][r]
            assert g == greq and blk["d"] == dreq, f"{name}: multiplier mismatch {nm}"
            Z = monos_upto(blk["d"])
            Nm = Qmat(blk["N"]); R = Qmat(blk["red"])
            N[nm] = Nm; red[nm] = R
            if not R:
                continue
            if not is_symmetric(R):                    # M2 (see above)
                asym.append(nm); ok = False
            if want_psd:
                good, sg = psd_slack(R, Qmat(blk["L"]), [Qs(x) for x in blk["d_piv"]])
                ok &= good; sigma[nm] = sg
            B = congruence(Nm, R)
            zz = {}
            n = len(Z)
            for i in range(n):
                for j in range(n):
                    if B[i][j] != 0:
                        e = (Z[i][0] + Z[j][0], Z[i][1] + Z[j][1], Z[i][2] + Z[j][2])
                        zz[e] = zz.get(e, Q0) + B[i][j]
            zz = {k: v for k, v in zz.items() if v != 0}
            rhs = P_add(rhs, P_mul(g, zz))
        diff = P_add(lam[tag], rhs, -1)
        rep[f"identity_{tag}"] = (len(diff) == 0)
        ok &= (len(diff) == 0)
    if Nref is not None:
        same = all(N[nm] == Nref[nm] for nm in Nref) and set(N) == set(Nref)
        rep["same_face"] = same; ok &= same
    pins = pin_map(c["hA"], c["hB"], c["hC"])
    erow = (c["e"] == pins[2] + 10 * pins[0] + 10 * pins[3])
    rep["e_row"] = erow; ok &= erow
    rep["blocks_symmetric"] = not asym
    if asym:
        rep["asymmetric_blocks"] = asym
    rep["ok"] = ok
    log(f"{name}: identities {[rep[f'identity_{t}'] for t in 'ABG']}, e-row {erow}, symmetric blocks {not asym}" +
        (f", min sigma {float(Fr(str(min(sigma.values()))))if sigma else None:.3e}" if want_psd else ""))
    return dict(rep=rep, c=c, red=red, N=N, sigma=sigma, pins=pins, ok=ok)


# ============================================================ ball arithmetic
def A(q):
    """arb from fmpq / Fraction / int / str."""
    f = Fr(str(q)) if not isinstance(q, Fr) else q
    return arb(fmpq(fmpz(f.numerator), fmpz(f.denominator)))


def ball(lo, hi):
    lo, hi = A(lo), A(hi)
    m = (lo + hi) / 2
    return arb(m.mid(), ((hi - lo) / 2).upper() + m.rad())


def up(x):
    return arb(abs(x).upper())


def poly_eval(coefs, t, der=0):
    cs = list(coefs)
    for _ in range(der):
        cs = [j * cs[j] for j in range(1, len(cs))]
    acc = arb(0)
    for cj in reversed(cs):
        acc = acc * t + cj
    return acc


SPOLY = {0: [1], 1: [0, 1], 2: [0, 2, 1], 3: [0, 8, 6, 1]}   # P_m(s) = prod_{i<m} (s + 2i), monomial coefficients
from math import comb


def Phi(m, n, t, s):
    """d^n/ds^n of phi_s^(m)(t) = P_m(s) u^(-s/2-m), u = 2 - 2t (t, s arb)."""
    u = 2 - 2 * t
    L = u.log()
    E = (-(s / 2 + m) * L).exp()
    tot = arb(0)
    P = [arb(x) for x in SPOLY[m]]
    for j in range(n + 1):
        cs = P
        for _ in range(j):
            cs = [i * cs[i] for i in range(1, len(cs))]
        if not cs:
            break
        Pj = arb(0)
        for cj in reversed(cs):
            Pj = Pj * s + cj
        tot += comb(n, j) * Pj * (-L / 2) ** (n - j)
    return tot * E


S5 = arb(5).sqrt(); C1 = (S5 - 1) / 4; C2 = (-S5 - 1) / 4


def vdata(n, s):
    """d^n/ds^n of the kernel data vector v(s) (7 arb)."""
    p = lambda m, t: Phi(m, n, t, s)
    return [p(0, arb(0)), p(1, arb(0)), p(0, arb(-1)), (p(0, C1) + p(0, C2)) / 2, (p(0, C1) - p(0, C2)) / (2 * S5),
            (p(1, C1) + p(1, C2)) / 2, (p(1, C1) - p(1, C2)) / (2 * S5)]


def ldl_pd(M, n):
    """True iff every symmetric matrix in the ball matrix M is positive definite (all LDL^T pivots > 0)."""
    M = [[M[i][j] for j in range(n)] for i in range(n)]
    for k in range(n):
        d = M[k][k]
        if not d > 0:
            return False
        for i in range(k + 1, n):
            l = M[i][k] / d
            for j in range(k + 1, i + 1):
                M[i][j] -= l * M[j][k]
                M[j][i] = M[i][j]
    return True


# ============================================================ main
def main(path_a, path_b, path_dirs, sa, sb, delta=1e-16, tau_den=10 ** 6):
    rep = {"nodes": [path_a, path_b], "dirs": path_dirs, "a": sa, "b": sb, "delta": delta, "tau": f"1/{tau_den}"}
    rep["provenance"] = provenance([path_a, path_b, path_dirs])      # S1: hashes taken before the inputs are read
    if not M_TWOSIDED:
        rep["M_remainder"] = "one-sided"
    qa, qb = Fr(sa), Fr(sb)
    assert 0 < qa < qb < 2
    def jload(path):
        import gzip
        return json.load(gzip.open(path, "rt") if path.endswith(".gz") else open(path))
    Ja, Jb, JD = jload(path_a), jload(path_b), jload(path_dirs)
    def s_of(J):
        """the certificate's s; the cap1 Coulomb certificate (no "s" field) is s = 1."""
        if "s" in J:
            return Fr(J["s"])
        assert J["kernel"].startswith("coulomb"), "certificate without s and not coulomb"
        return Fr(1)
    assert s_of(Ja) == qa and s_of(Jb) == qb, "node certificates are for other s"
    for J in (Ja, Jb, JD):
        assert (Fr(J["cell"][0]), Fr(J["cell"][1])) == (Fr(-1), Fr(-99, 100)) and J["D"] == 12
        assert tuple(J["dA"]) == tuple(Ja["dA"])
    req = required_multipliers(fmpq(-1), fmpq(-99, 100), tuple(Ja["dA"]))
    assert len(JD["dirs"]) == 7
    # ---- exact part
    Oa = load_object(Ja, "node a", req, None, True)
    Ob = load_object(Jb, "node b", req, Oa["N"], True)
    Od = [load_object(JD["dirs"][k], f"dir {k}", req, Oa["N"], False) for k in range(7)]
    exact_ok = Oa["ok"] and Ob["ok"] and all(o["ok"] for o in Od)
    pins_ok = all(Od[k]["pins"] == [fmpq(int(i == k)) for i in range(7)] for k in range(7))
    rep["E1_E2_E4"] = exact_ok; rep["E3_pins"] = pins_ok
    rep["M2_blocks_symmetric"] = all(o["rep"]["blocks_symmetric"] for o in [Oa, Ob] + Od)   # also inside E1_E2_E4
    log(f"exact: identities/e-row/face/PSD {exact_ok}, Pin(C_k) = e_k {pins_ok}")
    if not (exact_ok and pins_ok):
        rep["PIECE_OK"] = False; return rep
    bnames = [nm for nm in Oa["red"] if Oa["red"][nm]]
    # certified node margins: R_j >= mu_j I by an arb LDL^T of R_j - mu_j I (R_j exact), mu_j a dyadic just below the
    # float smallest eigenvalue; the exact DD slack sigma_j (E4) is the fallback.  mu_blk = min over the two nodes.
    import numpy as np
    def cert_margin(R, sigma):
        n = len(R)
        lam = float(np.linalg.eigvalsh(np.array([[float(Fr(str(x))) for x in row] for row in R], float))[0])
        for fac in (0.97, 0.9, 0.75, 0.5):
            cand = Fr(int(lam * fac * 2 ** 60), 2 ** 60)
            if cand <= Fr(str(sigma)):
                break
            M = [[A(R[i][j]) - (A(cand) if i == j else arb(0)) for j in range(n)] for i in range(n)]
            if ldl_pd(M, n):
                return cand
        return Fr(str(sigma))
    mu = {nm: min(cert_margin(Oa["red"][nm], Oa["sigma"][nm]), cert_margin(Ob["red"][nm], Ob["sigma"][nm])) for nm in bnames}
    rep["mu_min"] = float(min(mu.values()))
    log(f"certified node margins: min over blocks {rep['mu_min']:.3e} (DD slacks {float(Fr(str(min(Oa['sigma'].values())))):.2e}, {float(Fr(str(min(Ob['sigma'].values())))):.2e})")
    # ---- kernel data
    aA, bA = A(qa), A(qb)
    h = bA - aA; sm = (aA + bA) / 2; S = ball(qa, qb)
    va, vb = vdata(0, aA), vdata(0, bA)
    vta, vtb = [A(x) for x in Oa["pins"]], [A(x) for x in Ob["pins"]]
    # M1: eps_k is an upper bound over the two nodes -> hi_max (largest upper endpoint), not max() on balls
    eps = [hi_max([up(va[k] - vta[k]), up(vb[k] - vtb[k])]) for k in range(7)]
    w = vdata(2, sm)
    M3 = [up(x) for x in vdata(3, S)]
    rep["pin_err_max"] = float(hi_max(eps).upper()); rep["v2_mid"] = [float(x.mid()) for x in w]; rep["M3"] = [float(x.upper()) for x in M3]
    # ---- P: PSD per block
    Rk = [Od[k]["red"] for k in range(7)]
    worst = None; blkrep = {}
    if NSUB > 1:
        # sample points s_i = a + i h/n (exact rationals) and the family's coefficients there:
        # R(s_i) = (1 - i/n) R_a + (i/n) R_b + sum_k rho_k(s_i) R_k,  rho_k(s_i) = v_k(s_i) - (1 - i/n) v~_a,k - (i/n) v~_b,k
        ssub = [qa + (qb - qa) * Fr(i, NSUB) for i in range(NSUB + 1)]
        coef_sub = []
        for i, si in enumerate(ssub):
            li = Fr(i, NSUB); c0, c1 = A(1 - li), A(li)
            vi = vdata(0, A(si))
            coef_sub.append((c0, c1, [vi[k] - c0 * vta[k] - c1 * vtb[k] for k in range(7)]))
        rep["P_nsub"] = NSUB; rep["P_sub_points"] = [f"{x.numerator}/{x.denominator}" for x in ssub]

    def cert_margin_ball(M, n):
        """dyadic m with every matrix in the ball matrix M minus m I positive definite (arb LDL^T), m just below
        the float smallest eigenvalue of mid(M) (also when that is negative); None if not certified."""
        lam = float(np.linalg.eigvalsh(np.array([[float(M[i][j].mid()) for j in range(n)] for i in range(n)], float))[0])
        for fac in (0.999, 0.99, 0.97, 0.9, 0.75, 0.5):
            cand = Fr(int((lam - abs(lam) * (1 - fac)) * 2 ** 60), 2 ** 60)
            Mc = [[M[i][j] - (A(cand) if i == j else arb(0)) for j in range(n)] for i in range(n)]
            if ldl_pd(Mc, n):
                return cand
        return None
    for nm in bnames:
        n = len(Oa["red"][nm])
        Fk = []
        for k in range(7):
            fro = sum((x * x for row in Rk[k][nm] for x in row), Q0)
            Fk.append(A(fro).sqrt())
        Rw = [[sum((w[k] * A(Rk[k][nm][i][j]) for k in range(7)), arb(0)) for j in range(n)] for i in range(n)]
        lam_f = float(np.linalg.eigvalsh(np.array([[x.mid() for x in row] for row in Rw], float))[-1])
        tau = None
        for mult in (1.0, 1.5, 3.0, 10.0):
            cand = max(lam_f, 0.0) * (1 + 1e-3 * mult) + 1e-10 * mult
            M = [[(arb(cand) if i == j else arb(0)) - Rw[i][j] for j in range(n)] for i in range(n)]
            if ldl_pd(M, n):
                tau = arb(cand); break
        if tau is None:
            blkrep[nm] = "lambda_max(R_w) not certified"
            worst = arb(-1) if worst is None else lo_min([worst, arb(-1)]); continue
        cubic = sum((M3[k] * Fk[k] for k in range(7)), arb(0))
        epsterm = sum((eps[k] * Fk[k] for k in range(7)), arb(0))
        slack = A(mu[nm]) - h * h / 8 * (tau + h / 2 * cubic) - epsterm
        blkrep[nm] = dict(mu=float(mu[nm]), tau=float(tau.upper()), cubic=float(cubic.upper()), slack=float(slack.lower()))
        if NSUB > 1:
            # (S_n): min_i m_i - (h^2/(8 n^2)) (tau + (h/2) cubic), m_i certified on the exact family at s_i (docstring P)
            slackW = slack
            Ra = [[arb(x) for x in row] for row in Oa["red"][nm]]; Rb = [[arb(x) for x in row] for row in Ob["red"][nm]]
            Rka = [[[arb(x) for x in row] for row in Rk[k][nm]] for k in range(7)]
            ms = []
            for c0, c1, rho in coef_sub:
                Mi = [[c0 * Ra[i][j] + c1 * Rb[i][j] + sum((rho[k] * Rka[k][i][j] for k in range(7)), arb(0))
                       for j in range(n)] for i in range(n)]
                ms.append(cert_margin_ball(Mi, n))
            if any(m is None for m in ms):
                blkrep[nm].update(slackW=float(slackW.lower()), m_sub=[None if m is None else float(m) for m in ms],
                                  slackS=None)
            else:
                d = h / NSUB
                slackS = A(min(ms)) - d * d / 8 * (tau + h / 2 * cubic)
                if slackS.lower() > slackW.lower():
                    slack = slackS
                blkrep[nm].update(slackW=float(slackW.lower()), m_sub=[float(m) for m in ms], slackS=float(slackS.lower()),
                                  slack=float(slack.lower()))
        # M1: running minimum of the block slacks by lower endpoint (an exact ball), not min() on balls: if a later
        # block's slack ball overlapped `worst` and reached lower, min() would keep `worst` and psd_ok could pass
        # without that block being certified.
        worst = slack if worst is None else lo_min([worst, slack])
    psd_ok = bool(worst > 0)
    rep["P_blocks"] = blkrep; rep["P_min_slack"] = float(worst.lower()); rep["P_ok"] = psd_ok
    log(f"P: min block slack {float(worst.lower()):+.3e} -> {psd_ok}; worst blocks " +
        str(sorted(((v["slack"], k) for k, v in blkrep.items() if isinstance(v, dict)))[:3]))
    # ---- M, K: minorants
    H = {X: {"a": [A(x) for x in Oa["c"][f"h{X}"]], "b": [A(x) for x in Ob["c"][f"h{X}"]],
             "k": [[A(x) for x in Od[k]["c"][f"h{X}"]] for k in range(7)]} for X in "ABC"}
    pe = poly_eval

    def node_f(X, j, T, m):
        """f_j^(m)(T) = phi_{s_j}^(m)(T) - H_j^(m)(T) - sum_k (v_k(s_j) - v~_{j,k}) H_k^(m)(T)  (ball)."""
        s_, v_, vt_ = (aA, va, vta) if j == "a" else (bA, vb, vtb)
        out = Phi(m, 0, T, s_) - pe(H[X][j], T, m)
        for k in range(7):
            out -= (v_[k] - vt_[k]) * pe(H[X]["k"][k], T, m)
        return out

    def G_bound(X, T, m):
        """one-sided (default): >= max(0, sup_{t in T, s in [a,b]} d^2/ds^2 g_t^(m)(s)) (docstring M);
        M_TWOSIDED=1: >= sup_{t in T, s in [a,b]} |d^2/ds^2 g_t^(m)(s)|;  g_t^(m)(s) = phi_s^(m)(t) - sum_k v_k(s) H_k^(m)(t)."""
        Hk = [pe(H[X]["k"][k], T, m) for k in range(7)]
        def g(n, s_):
            return Phi(m, n, T, s_) - sum((vdata(n, s_)[k] * Hk[k] for k in range(7)), arb(0))
        if M_TWOSIDED:
            return up(g(2, sm)) + h / 2 * up(g(3, sm)) + h * h / 8 * up(g(4, S))
        sup2 = (g(2, sm) + h / 2 * up(g(3, sm)) + h * h / 8 * up(g(4, S))).upper()    # exact arb >= sup g''
        # M1 (same family): a NaN upper endpoint compares False with 0 and would have been replaced by 0; keep any
        # non-finite value, so that the lower bound becomes non-finite and the piece is bisected / fails.
        return sup2 if (sup2 > 0 or not sup2.is_finite()) else arb(0)

    def lower_bound(X, lo, hi, m):
        """rigorous lower bound (arb) of f^(m)(t, s) on [lo, hi] x [a, b] (lo, hi arb)."""
        T = ball_arb(lo, hi); mid = (lo + hi) / 2; r = ((hi - lo) / 2)
        # M3 (review): no change needed.  The ball `mid` contains the true midpoint m* of the t-piece and r.upper()
        # bounds the true half-width, so |t - m*| <= r.upper() for every t in the piece and node_f(mid) encloses
        # f(m*); the mean-value form is centred at m*, not at a point of the ball, so rad(mid) needs no extra term.
        # (Likewise s_m and h in G_bound / the P step: the balls contain the true midpoint and width.)
        lbs = [node_f(X, j, mid, m) - up(node_f(X, j, T, m + 1)) * arb(r.upper()) for j in ("a", "b")]
        best = lo_min(lbs)          # M1: the smaller of the two node bounds by lower endpoint, not min() on balls
        return best - h * h / 8 * G_bound(X, T, m)

    def ball_arb(lo, hi):
        mid = (lo + hi) / 2
        return arb(mid.mid(), ((hi - lo) / 2).upper() + mid.rad())

    def cover(X, lo, hi, need, m=0, n0=N0):
        """prove f^(m) > need on [lo, hi] (arb endpoints) for all s; returns (min certified lower bound, pieces)."""
        stack = [(lo + (hi - lo) * k / n0, lo + (hi - lo) * (k + 1) / n0, 0) for k in range(n0)]
        worst = None; npieces = 0
        while stack:
            l_, h_, dep = stack.pop()
            lb = lower_bound(X, l_, h_, m)
            if lb > need:
                # M1: reported minimum by lower endpoint (each piece already passed lb > need on its own)
                worst = lb if worst is None else lo_min([worst, lb]); npieces += 1
                continue
            if dep >= MAXDEPTH:
                raise RuntimeError(f"cannot certify f_{X}^({m}) > {need} on [{float(l_.lower())}, {float(h_.upper())}]: lb {float(lb.lower())}")
            md = (l_ + h_) / 2
            stack += [(l_, md, dep + 1), (md, h_, dep + 1)]
        return worst, npieces

    def window_min(X, c, r, m, n=NWIN):
        """certified lower bound of f_X^(m) on [c - r, c + r] x [a, b] (c arb) by n subdivisions."""
        lbs = []
        for j in range(n):
            l_ = c - r + 2 * r * j / n; h_ = c - r + 2 * r * (j + 1) / n
            lbs.append(lower_bound(X, l_, h_, m))
        # M1: the window bound is the smallest lower endpoint over all n sub-pieces (an exact ball); with min() on
        # overlapping balls a sub-piece reaching lower could be skipped, and mB, mC, mA (hence the exact tau
        # decision of K) would be too large.
        return lo_min(lbs)

    # contact window radii (env RB, RC, RA as rationals; defaults are the floors' windows of sdp_capS.py).  Any radii
    # are sound: the argument only needs f'' > 0 (f' > 0 for A) on the window, which is what is certified.
    rB, rC, rA = (arb(Qs(os.environ.get(k, d))) for k, d in (("RB", "1/20"), ("RC", "1/50"), ("RA", "1/500")))
    dl = arb(delta)
    mB = window_min("B", arb(0), rB, 2)
    mC = lo_min([window_min("C", C1, rC, 2), window_min("C", C2, rC, 2)])     # M1: both C windows, by lower endpoint
    mA = window_min("A", arb(-1), rA, 1)
    rep["windows"] = dict(rB=float(rB), rC=float(rC), rA=float(rA), min_fB2=float(mB.lower()), min_fC2=float(mC.lower()), min_fA1=float(mA.lower()))
    log(f"windows: f_B'' >= {float(mB.lower()):.3e}, f_C'' >= {float(mC.lower()):.3e}, f_A' >= {float(mA.lower()):.3e}")
    win_ok = bool(mB > 0 and mC > 0 and mA > 0)
    if not win_ok:
        rep["M_ok"] = False; rep["K_ok"] = False; rep["PIECE_OK"] = False
        rep["FAIL"] = "contact window curvature / slope not positive on the piece"
        return rep
    # outside the windows: f > delta
    eps1 = arb(fmpq(1, 10 ** 6)); pad = arb(fmpq(1, 10 ** 15))
    cov = {}

    def cov_min(parts):
        """M1: combine (bound, pieces) results of several segments: the bound is the smallest lower endpoint over the
        segments (min() on (arb, int) tuples compared overlapping balls and could keep the wrong one); the piece count
        is that of a segment attaining it, as before.  (cover() already certified bound > delta on every segment.)"""
        k = argmin_lower([p[0] for p in parts])
        return (lo_min([p[0] for p in parts]), parts[k][1])
    try:
        cov["A"] = cover("A", arb(-1) + rA, arb(fmpq(-99, 100)), dl)
        cov["B"] = cov_min([cover("B", arb(-1), -rB, dl), cover("B", rB, 1 - eps1, dl)])
        segsC = [(arb(-1), C2 - rC + pad), (C2 + rC - pad, C1 - rC + pad), (C1 + rC - pad, 1 - eps1)]
        cov["C"] = cov_min([cover("C", l_, h_, dl) for (l_, h_) in segsC])
    except RuntimeError as ex:
        rep["M_ok"] = False; rep["K_ok"] = False; rep["PIECE_OK"] = False; rep["FAIL"] = str(ex)
        log("FAIL:", ex)
        return rep
    rep["cover_min"] = {X: float(v[0].lower()) for X, v in cov.items()}
    rep["cover_pieces"] = {X: v[1] for X, v in cov.items()}
    log("outside windows: min f lower bounds", rep["cover_min"], "pieces", rep["cover_pieces"])
    # near t = 1: phi_s(t) >= (2 eps1)^(-a/2) for s >= a; H(t; s) <= max_j UB(H^_j) + sum_k UB|v_k(S)| UB|H_k|
    T1 = ball_arb(1 - eps1, arb(1))
    vS = [up(x) for x in vdata(0, S)]
    top_ok = True; top = {}
    for X in "BC":
        hat = []
        for j, vt_ in (("a", vta), ("b", vtb)):
            hj = pe(H[X][j], T1) - sum((vt_[k] * pe(H[X]["k"][k], T1) for k in range(7)), arb(0))
            hat.append(arb(hj.upper()))
        # M1: largest upper endpoint over the two nodes (hat entries are exact points anyway), not max() on balls
        Hmax = hi_max(hat) + sum((vS[k] * up(pe(H[X]["k"][k], T1)) for k in range(7)), arb(0))
        phimin = (2 * eps1) ** (-aA / 2)
        top[X] = float((phimin - Hmax).lower()); top_ok &= bool(phimin - Hmax > dl)
    rep["near_1_margin"] = top
    m_ok = bool(win_ok and all(v[0] > dl for v in cov.values()) and top_ok)
    rep["M_ok"] = m_ok
    # K: coercivity windows, exact decision with rational lower bounds of mB, mC, mA
    def exact_lower(x):
        """exact rational (dyadic) lower bound of the ball x."""
        lo_ = x.lower()
        assert lo_.is_exact()
        man, ex = lo_.man_exp()
        return Fr(int(man)) * Fr(2) ** int(ex)
    qmB, qmC, qmA = (exact_lower(x) for x in (mB, mC, mA))
    T = Fr(1, tau_den); dq = Fr(delta)
    tau_ok = dict(B=(qmB * T * T >= 2 * dq), C=(qmC * T * T >= 2 * dq), A=(qmA * T >= dq))
    rep["coercivity"] = dict(tauB=float((2 * dl / mB).sqrt().upper()), tauC=float((2 * dl / mC).sqrt().upper()),
                             tauA=float((dl / mA).upper()), tau_ok_exact=tau_ok, outside_windows_f_gt_delta=bool(all(v[0] > dl for v in cov.values())))
    k_ok = bool(all(tau_ok.values()) and all(v[0] > dl for v in cov.values()) and top_ok)
    rep["K_ok"] = k_ok
    rep["PIECE_OK"] = bool(exact_ok and pins_ok and psd_ok and m_ok and k_ok)
    rep["time_s"] = round(time.time() - T0, 1)
    return rep


if __name__ == "__main__":
    args = sys.argv[1:]
    rep = main(args[0], args[1], args[2], args[3], args[4],
               float(args[5]) if len(args) > 5 else 1e-16, int(args[6]) if len(args) > 6 else 10 ** 6)
    print(json.dumps(rep, indent=1, default=str))
    print("PIECE_OK" if rep.get("PIECE_OK") else "PIECE_FAIL")
    sys.exit(0 if rep.get("PIECE_OK") else 1)
