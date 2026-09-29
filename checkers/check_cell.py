"""Exact checker for the non-cap cells (Case 1 and the Case-2 slabs), log or Coulomb kernel.

usage: python3 check_cell.py cert_*.json [...]

Exact (fractions.Fraction) throughout, except E(P) (mpmath, 60 digits) and the random-configuration
sanity test (mpmath, 40 digits).  Reuses only the polynomial helpers and lam_polys of the independent
cap checker check_cert.py (same directory) (which do not depend on any generator code).  Checks:

  1. the SOS multipliers are exactly the ones required for the cell (PAPER.md 5.2 / 6.4):
       case1 (cut a):  1, u-a, v-a, t-a, 1-u, 1-v, 1-t, detG
       slab [lo,hi]:   A: 1, u-lo, hi-u, v-lo, t-lo, 1-v, 1-t, detG, (u-lo)(hi-u)
                       B, Gamma: 1, u-lo, v-lo, t-lo, 1-u, 1-v, 1-t, detG
     with monomial vectors z of degree D/2, D/2-1, D/2-2 as upstream;
  2. every kernel block F and every SOS Gram block B is positive DEFINITE: symmetric, and all leading
     principal minors > 0 (Sylvester), computed exactly by fraction-free Bareiss elimination;
  3. the polynomial identities  slack == sum_r g_r z^T B_r z  (case1)  resp.
     lambda_T == sum_r g_r z^T B_r z, T = A, B, Gamma, and constraint (6) (slab), coefficient by coefficient;
  4. e - E(P) > 0, with E(P) = -log(1600 sqrt5) (log) resp. the closed form (Coulomb), at 60 digits;
  5. sanity (not needed for soundness, guards against transcription errors of PAPER.md 5.1 / 6.3):
     on random 7-point configurations, the combinatorial identity
       case1:  dsum(slack) + 5 Sigma_all = 10 (sum_{i<j} H(t_ij) - e)
       slab:   sum_T lambda_T + Sigma_all = sum_{i<j} H_cls(t_ij) - e
     holds to 1e-25, where Sigma_all is evaluated independently from the root form of Lemma 4.1
     (sum_roots rho^T F rho + iota^T F iota, complex numbers, no Q_k polynomials), and Sigma_all >= 0.
The minorant inequalities H <= phi are checked separately (check_minorant_cell.py, ball arithmetic).
"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr
from math import lcm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_cert import (P_add, P_mul, P_perm, P_scale, P_subst_diag, P_at111, univ, ONE, Uu, Vv, Tt,
                        Qk_list, form, lam_polys, monos_upto, required_multipliers)


# ------------------------------------------------------------------ exact models
def detG():
    return P_add(P_add(P_add(P_add(ONE, P_mul(P_mul(Uu, Vv), Tt), 2), P_mul(Uu, Uu), -1), P_mul(Vv, Vv), -1),
                 P_mul(Tt, Tt), -1)


def case1_multipliers(a, D):
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    lin = lambda var: P_add(univ([Fr(0), Fr(1)], var), {(0, 0, 0): a}, -1)
    om = lambda var: P_add(ONE, univ([Fr(0), Fr(1)], var), -1)
    return [(ONE, d5), (lin(0), d4), (lin(1), d4), (lin(2), d4), (om(0), d4), (om(1), d4), (om(2), d4), (detG(), d3)]


def sym_form(Fs, Q):
    """s = sum_k <F_k, S_k>,  S_k = average of Y_k over the 6 permutations of (u,v,t)."""
    s = form(Fs, Q)
    out = {}
    for o in itertools.permutations(range(3)):
        out = P_add(out, P_perm(s, o))
    return P_scale(out, Fr(1, 6))


def case1_slack(H, e, Fs, n=7):
    """slack = (H(u)+H(v)+H(t))/3 - e/C(n,2) - R_s,  R_s = (n-2)s + s(u,u,1)+s(v,v,1)+s(t,t,1) + s(1,1,1)/(n-1)."""
    Q = Qk_list(len(Fs) - 1)
    s = sym_form(Fs, Q)
    su = P_subst_diag(s, 2)                         # s(x, x, 1) as a polynomial in u
    R = P_add(P_add(P_add(P_scale(s, n - 2), su), P_perm(su, (1, 0, 2))), P_perm(su, (2, 1, 0)))
    R = P_add(R, {(0, 0, 0): P_at111(s) / (n - 1)})
    Hs = P_add(P_add(univ(H, 0), univ(H, 1)), univ(H, 2))
    sl = P_add(P_scale(Hs, Fr(1, 3)), {(0, 0, 0): e / (n * (n - 1) // 2)}, -1)
    return P_add(sl, R, -1), s


# ------------------------------------------------------------------ exact PD test
def bareiss_pd(M):
    """M rational symmetric. Returns (True, None) iff all leading principal minors are > 0."""
    n = len(M)
    for i in range(n):
        for j in range(i):
            if M[i][j] != M[j][i]:
                return False, "not symmetric"
    L = 1
    for row in M:
        for x in row:
            L = lcm(L, x.denominator)
    A = [[int(x * L) for x in row] for row in M]
    prev = 1
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False, f"leading minor {k + 1} <= 0"
        for i in range(k + 1, n):
            Aik = A[i][k]; Ai = A[i]; Ak = A[k]
            for j in range(k + 1, n):
                Ai[j] = (Ai[j] * piv - Aik * Ak[j]) // prev
        prev = piv
    return True, None


def gram_poly(B, Z):
    zz = {}
    n = len(Z)
    for i in range(n):
        for j in range(n):
            if B[i][j] != 0:
                e = (Z[i][0] + Z[j][0], Z[i][1] + Z[j][1], Z[i][2] + Z[j][2])
                zz[e] = zz.get(e, 0) + B[i][j]
    return {k: v for k, v in zz.items() if v != 0}


def Fmat(M):
    return [[Fr(x) for x in row] for row in M]


# ------------------------------------------------------------------ E(P)
def EP(kernel, mp):
    s5 = mp.sqrt(5)
    if kernel == "log":
        return -mp.log(1600 * s5)
    f = lambda t: 1 / mp.sqrt(2 - 2 * t)
    return f(-1) + 10 * f(0) + 5 * f((s5 - 1) / 4) + 5 * f((-s5 - 1) / 4)


# ------------------------------------------------------------------ random-configuration sanity test
def sanity(J, c, polys, ntest=3, seed=7):
    import mpmath as mp
    import random
    mp.mp.dps = 40
    rnd = random.Random(seed)
    tomp = lambda q: mp.mpf(q.numerator) / q.denominator
    def peval(p, u, v, t):
        return sum(tomp(cf) * u ** a * v ** b * t ** d for (a, b, d), cf in p.items())
    def hval(H, x):
        return sum(tomp(cf) * x ** j for j, cf in enumerate(H))
    worst = mp.mpf(0); minall = None
    for _ in range(ntest):
        X = []
        for i in range(7):
            v = [mp.mpf(rnd.gauss(0, 1)) for _ in range(3)]
            nv = mp.sqrt(sum(x * x for x in v)); X.append([x / nv for x in v])
        G = [[sum(X[i][k] * X[j][k] for k in range(3)) for j in range(7)] for i in range(7)]
        # Sigma_all from Lemma 4.1 (root form): sum_i sum_k rho^T F rho + iota^T F iota
        def root_sum(i, Fs):
            xi = X[i]
            a = [1, 0, 0] if abs(xi[0]) < 0.9 else [0, 1, 0]
            e1 = [xi[1] * a[2] - xi[2] * a[1], xi[2] * a[0] - xi[0] * a[2], xi[0] * a[1] - xi[1] * a[0]]
            ne = mp.sqrt(sum(x * x for x in e1)); e1 = [x / ne for x in e1]
            e2 = [xi[1] * e1[2] - xi[2] * e1[1], xi[2] * e1[0] - xi[0] * e1[2], xi[0] * e1[1] - xi[1] * e1[0]]
            tot = mp.mpf(0)
            for k, F in enumerate(Fs):
                m = len(F)
                rho = [mp.mpf(0)] * m; iota = [mp.mpf(0)] * m
                for j in range(7):
                    uj = G[i][j]
                    z = mp.mpc(sum(X[j][q] * e1[q] for q in range(3)), sum(X[j][q] * e2[q] for q in range(3))) ** k
                    for aa in range(m):
                        rho[aa] += uj ** aa * z.real; iota[aa] += uj ** aa * z.imag
                tot += sum(tomp(F[aa][bb]) * (rho[aa] * rho[bb] + iota[aa] * iota[bb]) for aa in range(m) for bb in range(m))
            return tot
        if J["kind"] == "case1":
            Sall = sum(root_sum(i, c["F"]) for i in range(7))
            sl = polys["S"]
            ds = sum(peval(sl, G[i][j], G[i][l], G[j][l]) for i in range(7) for j in range(7) for l in range(7)
                     if len({i, j, l}) == 3)
            rhs = 10 * (sum(hval(c["H"], G[i][j]) for i in range(7) for j in range(i + 1, 7)) - tomp(c["e"]))
            err = ds + 5 * Sall - rhs
        else:
            Sall = sum(root_sum(i, c["FP"] if i < 2 else c["FR"]) for i in range(7))
            lamsum = sum(peval(polys["A"], G[0][1], G[0][r], G[1][r]) for r in range(2, 7))
            lamsum += sum(peval(polys["B"], G[p][r], G[p][q], G[r][q]) for p in (0, 1)
                          for r in range(2, 7) for q in range(r + 1, 7))
            lamsum += sum(peval(polys["G"], G[r][q], G[r][w], G[q][w]) for r in range(2, 7)
                          for q in range(r + 1, 7) for w in range(q + 1, 7))
            Hs = {"A": c["hA"], "B": c["hB"], "C": c["hC"]}
            cls = lambda i, j: "A" if (i < 2 and j < 2) else ("B" if (i < 2 or j < 2) else "C")
            rhs = sum(hval(Hs[cls(i, j)], G[i][j]) for i in range(7) for j in range(i + 1, 7)) - tomp(c["e"])
            err = lamsum + Sall - rhs
        worst = max(worst, abs(err))
        minall = Sall if minall is None else min(minall, Sall)
    return dict(max_identity_error=mp.nstr(worst, 3), identity_ok=bool(worst < mp.mpf(10) ** -25),
                min_Sigma_all=mp.nstr(minall, 5), Sigma_all_nonneg=bool(minall > -mp.mpf(10) ** -25))


# ------------------------------------------------------------------ main check
def load_exact(J):
    """exact data c (as for check_cert.lam_polys / case1_slack) from a certificate."""
    if J["kind"] == "case1":
        return dict(H=[Fr(x) for x in J["H"]], e=Fr(J["e"]), F=[Fmat(M) for M in J["F"]])
    c = {k: [Fr(x) for x in J["H"][k[1]]] for k in ("hA", "hB", "hC")}
    c["pBa"] = [Fr(x) for x in J["psi"]["Ba"]]; c["pCb"] = [Fr(x) for x in J["psi"]["Cb"]]
    for k in ("ca", "cb", "e"):
        c[k] = Fr(J[k])
    c["FP"] = [Fmat(M) for M in J["F"]["P"]]; c["FR"] = [Fmat(M) for M in J["F"]["R"]]
    return c


def lhs_polys(J, c):
    if J["kind"] == "case1":
        sl, _ = case1_slack(c["H"], c["e"], c["F"])
        return {"S": sl}
    lam = lam_polys(c)
    return {"A": lam["A"], "B": lam["B"], "G": lam["G"], "cg": lam["cg"], "oneP": lam["oneP"], "oneR": lam["oneR"]}


def required(J):
    D = J["D"]
    if J["kind"] == "case1":
        return {"S": case1_multipliers(Fr(J["cell"]["a"]), D)}
    return required_multipliers(Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"]), (D // 2, D // 2 - 1, D // 2 - 2))


def check(path, verbose=True, do_sanity=True):
    t0 = time.time()
    J = json.load(open(path))
    rep = {"cert": os.path.basename(path), "kind": J["kind"], "kernel": J["kernel"], "cell": J["cell"], "D": J["D"]}
    ok = True
    D = J["D"]
    c = load_exact(J)
    # ---- cell sanity
    if J["kind"] == "case1":
        ok &= Fr(J["cell"]["a"]) < 0
    else:
        lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
        ok &= (-1 < lo < hi < 0)
    # ---- degrees of H
    for H in ([c["H"]] if J["kind"] == "case1" else [c["hA"], c["hB"], c["hC"], c["pBa"], c["pCb"]]):
        ok &= len(H) == D + 1
    # ---- kernel blocks PD
    Fl = c["F"] if J["kind"] == "case1" else c["FP"] + c["FR"]
    sizes_expected = ([D // 2 + 1 - k for k in range(D // 2 - 1)] if J["kind"] == "case1"
                      else 2 * list(range(D // 2 + 1, 0, -1)))
    ok &= [len(F) for F in Fl] == sizes_expected
    pd_fail = []
    for k, F in enumerate(Fl):
        good, why = bareiss_pd(F)
        if not good:
            pd_fail.append((f"F{k}", why))
    # ---- lhs
    L = lhs_polys(J, c)
    if J["kind"] == "slab":
        cg = Fr(J["cg"])
        six = (cg == L["cg"]) and (5 * c["ca"] + 20 * c["cb"] + 10 * cg == c["e"] + 2 * L["oneP"] + 5 * L["oneR"])
        rep["constraint_6"] = six; ok &= six
    # ---- identities
    req = required(J)
    sos = J.get("SOS", {})
    if set(sos) != set(req) or not set(req) <= set(L):
        ok = False; rep["sos_tags"] = f"expected {sorted(req)}, found {sorted(sos)}"
    for tag in req:
        blocks = sos.get(tag, [])
        if len(blocks) != len(req[tag]):
            ok = False; rep[f"blocks_{tag}"] = "wrong blocks"; continue
        rhs = {}
        for r, blk in enumerate(blocks):
            g = {tuple(int(x) for x in k.split(",")): Fr(v) for k, v in blk["g"].items()}
            greq, dreq = req[tag][r]
            if g != greq or blk["d"] != dreq:
                ok = False; rep[f"mult_{tag}{r}"] = "multiplier mismatch"
            Z = monos_upto(blk["d"])
            B = Fmat(blk["B"])
            if len(B) != len(Z):
                ok = False; rep[f"size_{tag}{r}"] = "wrong size"; continue
            good, why = bareiss_pd(B)
            if not good:
                pd_fail.append((f"{tag}{r}", why))
            rhs = P_add(rhs, P_mul(g, gram_poly(B, Z)))
        diff = P_add(L[tag], rhs, -1)
        rep[f"identity_{tag}"] = "EXACT" if not diff else f"FAIL (max coeff diff {float(max(abs(v) for v in diff.values()))})"
        ok &= not diff
        if verbose:
            print(f"  {rep['cert']}: identity {tag} {'EXACT' if not diff else 'FAIL'} ({time.time() - t0:.0f}s)", flush=True)
    rep["all_blocks_positive_definite"] = not pd_fail
    if pd_fail:
        rep["pd_fail"] = pd_fail
    ok &= not pd_fail
    # ---- margin
    import mpmath as mp
    mp.mp.dps = 60
    e = c["e"]
    margin = mp.mpf(e.numerator) / e.denominator - EP(J["kernel"], mp)
    rep["e"] = str(e)
    rep["e_minus_EP"] = mp.nstr(margin, 60)
    rep["e_gt_EP"] = bool(margin > 0)
    ok &= rep["e_gt_EP"]
    if do_sanity:
        rep["sanity"] = sanity(J, c, L)
        ok &= rep["sanity"]["identity_ok"] and rep["sanity"]["Sigma_all_nonneg"]
    rep["ALL_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    allok = True
    for p in sys.argv[1:]:
        rep = check(p)
        print(json.dumps(rep, indent=1), flush=True)
        allok &= rep["ALL_OK"]
    print("CHECK_CELL", "ALL_OK" if allok else "FAILED")
    sys.exit(0 if allok else 1)
