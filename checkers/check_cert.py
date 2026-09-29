"""Independent exact checker for the typed three-point cap certificate (log kernel).

usage: python3 checkers/check_cert.py [certificates/cert_cap_log_D12.json]

Uses only fractions (exact) and mpmath (for the transcendental E(P)); does not import any other file
of this project.  Checks, following upstream PAPER.md section 6:
  1. multipliers g_r are exactly the ones required on the cap (lo = -1, hi = -99/100);
  2. every kernel block F_X^(k) = N F' N^T and every SOS block B_r = N B' N^T with F', B' PSD
     (exact: B' = L diag(d) L^T + Delta with d >= 0 and Delta symmetric, diagonally dominant with
     nonnegative diagonal);
  3. the three polynomial identities  lambda_T(u,v,t) == sum_r g_r z_r^T B_r z_r  (T = A, B, Gamma);
  4. the constraint (6): 5 c_alpha + 20 c_beta + 10 c_gamma = e + 2 s_P(1,1,1) + 5 s_R(1,1,1);
  5. contact data of H_B at 0 (value/derivatives) and of H_C at c1, c2, H_A at -1 (exact in Q(sqrt5));
  6. e - E(P), with E(P) = -log(1600 sqrt 5) at 60 digits.
The minorant inequality H <= phi is checked separately (check_minorant.py, interval arithmetic).
"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr

# ------------------------------------------------------------------ polynomials: {(a,b,c): Fraction}


def P_add(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        w = r.get(k, 0) + c * v
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
            r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}


def P_perm(p, order):
    """q(x0,x1,x2) = p(x[order[0]], x[order[1]], x[order[2]])"""
    r = {}
    for e, v in p.items():
        ne = [0, 0, 0]
        for slot in range(3):
            ne[order[slot]] += e[slot]
        ne = tuple(ne)
        r[ne] = r.get(ne, 0) + v
    return {k: v for k, v in r.items() if v != 0}


def P_subst_diag(p, one_slot):
    """univariate q(x) = p with slot `one_slot` := 1 and the other two slots := x (returned in variable u)."""
    r = {}
    for e, v in p.items():
        deg = sum(e[s] for s in range(3) if s != one_slot)
        k = (deg, 0, 0)
        r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v != 0}


def P_at111(p):
    return sum(p.values(), Fr(0))


def univ(coefs, var):
    out = {}
    for j, c in enumerate(coefs):
        if c != 0:
            e = [0, 0, 0]; e[var] = j
            out[tuple(e)] = c
    return out


ONE = {(0, 0, 0): Fr(1)}
Uu = {(1, 0, 0): Fr(1)}; Vv = {(0, 1, 0): Fr(1)}; Tt = {(0, 0, 1): Fr(1)}


def Qk_list(kmax):
    W = P_mul(P_add(ONE, P_mul(Uu, Uu), -1), P_add(ONE, P_mul(Vv, Vv), -1))
    tuv = P_add(Tt, P_mul(Uu, Vv), -1)
    Q = [ONE, tuv]
    while len(Q) <= kmax:
        Q.append(P_add(P_scale(P_mul(tuv, Q[-1]), 2), P_mul(W, Q[-2]), -1))
    return Q


def form(Fs, Q):
    """s(u,v,t) = sum_k <F_k, Y_k>,  Y_k[a,b] = u^a v^b Q_k."""
    s = {}
    for k, F in enumerate(Fs):
        m = len(F)
        Puv = {}
        for a in range(m):
            for b in range(m):
                if F[a][b] != 0:
                    Puv[(a, b, 0)] = Puv.get((a, b, 0), 0) + F[a][b]
        if Puv:
            s = P_add(s, P_mul(Puv, Q[k]))
    return s


def lam_polys(c):
    """c: dict with exact data: hA,hB,hC,pBa,pCb (monomial coeff lists), ca, cb, e, FP, FR (full matrices).
    returns dict of lambda_A, lambda_B, lambda_G polynomials and derived quantities."""
    kmax = max(len(c["FP"]), len(c["FR"])) - 1
    Q = Qk_list(kmax)
    sP = form(c["FP"], Q); sR = form(c["FR"], Q)
    gm = {}
    for X, s in (("P", sP), ("R", sR)):
        gm[X] = P_add(P_add(P_subst_diag(s, 0), P_subst_diag(s, 1)), P_subst_diag(s, 2))
    oneP, oneR = P_at111(sP), P_at111(sR)
    cg = (c["e"] + 2 * oneP + 5 * oneR - 5 * c["ca"] - 20 * c["cb"]) / 10
    PsiA = P_add(univ(c["hA"], 0), gm["P"], -2)
    PsiB = P_add(P_add(univ(c["hB"], 0), gm["P"], -1), gm["R"], -1)
    PsiC = P_add(univ(c["hC"], 0), gm["R"], -2)
    pBa = univ(c["pBa"], 0); pCb = univ(c["pCb"], 0)
    to_v = lambda p: P_perm(p, (1, 0, 2)); to_t = lambda p: P_perm(p, (2, 1, 0))
    kerA = P_add(P_add(sP, P_perm(sP, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    kerB = P_add(P_add(sP, P_perm(sR, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    kerG = P_add(P_add(sR, P_perm(sR, (0, 2, 1))), P_perm(sR, (1, 2, 0)))
    lamA = P_add(P_add(P_add(P_scale(PsiA, Fr(1, 5)), to_v(pBa)), to_t(pBa)), {(0, 0, 0): c["ca"]}, -1)
    lamA = P_add(lamA, kerA, -2)
    QB = P_scale(P_add(PsiB, pBa, -1), Fr(1, 4))
    lamB = P_add(P_add(P_add(QB, to_v(QB)), to_t(pCb)), {(0, 0, 0): c["cb"]}, -1)
    lamB = P_add(lamB, kerB, -2)
    QC = P_scale(P_add(PsiC, pCb, -2), Fr(1, 3))
    lamG = P_add(P_add(P_add(QC, to_v(QC)), to_t(QC)), {(0, 0, 0): cg}, -1)
    lamG = P_add(lamG, kerG, -2)
    return dict(A=lamA, B=lamB, G=lamG, cg=cg, oneP=oneP, oneR=oneR)


# ------------------------------------------------------------------ multipliers required on the cap
def monos_upto(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


def required_multipliers(lo, hi, dA):
    d5, d4, d3 = dA
    lin = lambda var, c0: P_add(univ([Fr(0), Fr(1)], var), {(0, 0, 0): c0}, -1)
    om = lambda var: P_add(ONE, univ([Fr(0), Fr(1)], var), -1)
    detG = P_add(P_add(P_add(P_add(ONE, P_mul(P_mul(Uu, Vv), Tt), 2), P_mul(Uu, Uu), -1), P_mul(Vv, Vv), -1), P_mul(Tt, Tt), -1)
    him = P_add({(0, 0, 0): hi}, Uu, -1)
    A = [(ONE, d5), (lin(0, lo), d4), (him, d4), (lin(1, lo), d4), (lin(2, lo), d4), (om(1), d4), (om(2), d4),
         (detG, d3), (P_mul(lin(0, lo), him), d4)]
    BG = [(ONE, d5), (lin(0, lo), d4), (lin(1, lo), d4), (lin(2, lo), d4), (om(0), d4), (om(1), d4), (om(2), d4), (detG, d3)]
    return {"A": A, "B": BG, "G": BG}


# ------------------------------------------------------------------ exact linear algebra helpers
def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0]) if B else 0
    Bt = list(zip(*B)) if B else []
    return [[sum((A[i][l] * Bt[j][l] for l in range(k) if A[i][l] != 0 and Bt[j][l] != 0), Fr(0)) for j in range(m)]
            for i in range(n)]


def congruence(N, X):
    """N X N^T for rational matrices (N: n x k, X: k x k)."""
    if not N or not N[0]:
        n = len(N); return [[Fr(0)] * n for _ in range(n)]
    NX = matmul(N, X)
    Nt = [list(r) for r in zip(*N)]
    return matmul(NX, Nt)


def psd_check(X, L, d):
    """X == L diag(d) L^T + Delta with d >= 0, Delta diagonally dominant with nonneg diagonal => X PSD."""
    n = len(X)
    if n == 0:
        return True, 0
    if any(x < 0 for x in d):
        return False, "negative pivot"
    for i in range(n):
        if L[i][i] != 1 or any(L[i][j] != 0 for j in range(i + 1, n)):
            return False, "L not unit lower triangular"
    worst = None
    for i in range(n):
        if X[i] != [X[j][i] for j in range(n)]:
            return False, "not symmetric"
    for i in range(n):
        row = []
        for j in range(n):
            s = sum((L[i][q] * d[q] * L[j][q] for q in range(min(i, j) + 1) if L[i][q] != 0 and L[j][q] != 0), Fr(0))
            row.append(X[i][j] - s)
        off = sum(abs(row[j]) for j in range(n) if j != i)
        slack = row[i] - off
        if slack < 0:
            return False, f"row {i} not diagonally dominant ({float(row[i])} < {float(off)})"
        worst = slack if worst is None else min(worst, slack)
    return True, worst


def Fq(s):
    return Fr(s)


def Fmat(M):
    return [[Fr(x) for x in row] for row in M]


# ------------------------------------------------------------------ main
def check(path, verbose=True):
    t0 = time.time()
    J = json.load(open(path))
    ok = True
    rep = {}
    lo, hi = Fr(J["cell"][0]), Fr(J["cell"][1])
    assert (lo, hi) == (Fr(-1), Fr(-99, 100)), "not the cap cell"
    dA = tuple(J["dA"])
    c = {k: [Fr(x) for x in J["H"][k[1]]] for k in ("hA", "hB", "hC")}
    c["pBa"] = [Fr(x) for x in J["psi"]["Ba"]]; c["pCb"] = [Fr(x) for x in J["psi"]["Cb"]]
    for k in ("ca", "cb", "e"):
        c[k] = Fr(J[k])
    # ---- kernel blocks
    psd_ok = True; psd_slack = {}
    for X in "PR":
        mats = []
        for k, blk in enumerate(J["F"][X]):
            m = blk["m"]
            N = Fmat(blk["N"]); R = Fmat(blk["red"])
            F = congruence(N, R) if R else [[Fr(0)] * m for _ in range(m)]
            if R:
                good, sl = psd_check(R, Fmat(blk["L"]), [Fr(x) for x in blk["d"]])
                psd_ok &= good; psd_slack[f"F{X}{k}"] = sl if not good else float(sl)
            mats.append(F)
        c["F" + X] = mats
    # ---- lambda polynomials
    lam = lam_polys(c)
    # (6)
    cg_json = Fr(J["cg"])
    six = (5 * c["ca"] + 20 * c["cb"] + 10 * cg_json == c["e"] + 2 * lam["oneP"] + 5 * lam["oneR"]) and cg_json == lam["cg"]
    rep["constraint_6"] = six; ok &= six
    # ---- SOS identities
    req = required_multipliers(lo, hi, dA)
    for tag in ("A", "B", "G"):
        rhs = {}
        blocks = J["SOS"][tag]
        if len(blocks) != len(req[tag]):
            ok = False; rep[f"id_{tag}"] = "wrong number of blocks"; continue
        for r, blk in enumerate(blocks):
            g = {tuple(int(x) for x in k.split(",")): Fr(v) for k, v in blk["g"].items()}
            greq, dreq = req[tag][r]
            if g != greq or blk["d"] != dreq:
                ok = False; rep[f"mult_{tag}{r}"] = "multiplier mismatch"
            Z = monos_upto(blk["d"])
            N = Fmat(blk["N"]); R = Fmat(blk["red"])
            if not R:
                continue
            good, sl = psd_check(R, Fmat(blk["L"]), [Fr(x) for x in blk["d_piv"]])
            psd_ok &= good; psd_slack[f"{tag}{r}"] = sl if not good else float(sl)
            B = congruence(N, R)
            zz = {}
            n = len(Z)
            for i in range(n):
                for j in range(n):
                    if B[i][j] != 0:
                        e = (Z[i][0] + Z[j][0], Z[i][1] + Z[j][1], Z[i][2] + Z[j][2])
                        zz[e] = zz.get(e, 0) + B[i][j]
            zz = {k: v for k, v in zz.items() if v != 0}
            rhs = P_add(rhs, P_mul(g, zz))
        diff = P_add(lam[tag], rhs, -1)
        rep[f"identity_{tag}"] = (len(diff) == 0)
        if diff:
            rep[f"identity_{tag}_maxdiff"] = float(max(abs(v) for v in diff.values()))
        ok &= (len(diff) == 0)
        if verbose:
            print(f"identity {tag}: {'EXACT' if not diff else 'FAIL'}  ({time.time() - t0:.0f}s)", flush=True)
    rep["psd"] = psd_ok; rep["psd_min_dd_slack"] = min(v for v in psd_slack.values() if isinstance(v, float)) if psd_slack else None
    if not psd_ok:
        rep["psd_fail"] = {k: v for k, v in psd_slack.items() if not isinstance(v, float)}
    ok &= psd_ok
    # ---- contact data (exact, Q(sqrt5) arithmetic as pairs (x, y) = x + y sqrt5)
    def ev(coefs, a, b):          # evaluate at a + b sqrt5
        x, y = Fr(0), Fr(0); px, py = Fr(1), Fr(0)
        for cf in coefs:
            x += cf * px; y += cf * py
            px, py = px * a + 5 * py * b, px * b + py * a
        return x, y
    def deriv(coefs):
        return [j * coefs[j] for j in range(1, len(coefs))]
    hB = c["hB"]
    rep["HB_contact"] = dict(h1=str(hB[1]), h2=str(hB[2]), h3=str(hB[3]),
                             matches_phi_to_3rd=(hB[1], hB[2], hB[3]) == (Fr(1, 2), Fr(1, 4), Fr(1, 6)))
    # phi'(c1) = 1/(2(1-c1)), c1 = (-1+sqrt5)/4 ;  1/(2(1-c1)) = 2/(5-sqrt5) = (5+sqrt5)/10
    dC = ev(deriv(c["hC"]), Fr(-1, 4), Fr(1, 4))
    rep["HC_contact"] = dict(dHC_c1=[str(dC[0]), str(dC[1])], matches_phi_prime=(dC == (Fr(1, 2), Fr(1, 10))))
    dA_m1 = sum(j * c["hA"][j] * (-1) ** (j - 1) for j in range(1, len(c["hA"])))
    rep["HA_contact"] = dict(dHA_at_m1=str(dA_m1), phi_prime_at_m1="1/4", slope_ok=(dA_m1 <= Fr(1, 4)))
    ok &= rep["HA_contact"]["slope_ok"]
    ok &= rep["HB_contact"]["matches_phi_to_3rd"] and rep["HC_contact"]["matches_phi_prime"]
    # ---- e vs E(P)
    import mpmath as mp
    mp.mp.dps = 60
    EP = -mp.log(1600 * mp.sqrt(5))
    e = c["e"]
    diff = mp.mpf(e.numerator) / e.denominator - EP
    rep["e"] = str(e); rep["e_minus_EP"] = mp.nstr(diff, 15)
    rep["e_le_EP"] = bool(diff < 0)
    # the value gaps at P's inner products (these add up to E(P) - e)
    hC_c1 = ev(c["hC"], Fr(-1, 4), Fr(1, 4))
    s5 = mp.sqrt(5)
    phi = lambda t: -mp.log(2 - 2 * t) / 2
    val = lambda q: mp.mpf(q.numerator) / q.denominator
    hA_m1 = sum(c["hA"][j] * (-1) ** j for j in range(len(c["hA"])))
    gaps = dict(A=phi(-1) - val(hA_m1), B=phi(0) - val(hB[0]),
                C1=phi((s5 - 1) / 4) - (val(hC_c1[0]) + val(hC_c1[1]) * s5),
                C2=phi((-s5 - 1) / 4) - (val(hC_c1[0]) - val(hC_c1[1]) * s5))
    rep["gaps_at_P"] = {k: mp.nstr(v, 6) for k, v in gaps.items()}
    total = gaps["A"] + 10 * gaps["B"] + 5 * gaps["C1"] + 5 * gaps["C2"]
    rep["sum_gaps_minus_(EP-e)"] = mp.nstr(total - (EP - val(e)), 5)
    ok &= rep["e_le_EP"]
    rep["ALL_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    rep = check(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "certificates", "cert_cap_log_D12.json"))
    print(json.dumps(rep, indent=1))
    sys.exit(0 if rep["ALL_OK"] else 1)
