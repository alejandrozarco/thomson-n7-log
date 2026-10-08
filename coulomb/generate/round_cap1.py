"""[s = 1 (Coulomb) adaptation: value-only face, first-order dyadic contact at 0 and c1,2]
Exact rounding of the float cap solution (sdp_soft.py) to a rational certificate (Peyrl-Parrilo style,
on the exact face of face.py).

    SHIFT_A=4.5e-7 python3 round_exact.py sol_mu_contact.npz [ETA_EXP]      -> cert_cap_log_D12.json
(SHIFT_A: exact-compatible downward shift of H_A that creates room at t = -99/100, see code)

Unknowns: reduced kernel blocks F', reduced SOS blocks B' (B = N B' N^T), H_A, H_B, H_C, psi_Ba, psi_Cb
(monomial coefficients), c_alpha, c_beta, e.  Linear equations (all over Q):
  * the three identities lambda_T == sum_r g_r z^T B_r z, coefficient by coefficient;
  * H_B(0) = beta0, H_B'(0) = 1/2, H_B''(0)/2 = 1/4, H_B'''(0)/6 = 1/6       (3rd-order contact)
  * H_A(-1) = alpha0;  H_C(c1) = a0 + b0 sqrt5, H_C'(c1) = phi'(c1)  (2 rational eqs each; the c2
    conditions are the Galois conjugates);  e = e0 := alpha0 + 10 beta0 + 10 a0.
alpha0, beta0, a0 +- b0 sqrt5 are dyadic rationals just below phi(-1), phi(0), phi(c1), phi(c2), so that
E(P) - e0 = sum of the gaps ~ 21 * 2^-ETA_EXP.
Procedure: float min-norm polish of the solver output -> round to 2^-80 -> exact solve for a well
conditioned set of pivot unknowns on an exact row basis (flint) -> verify all equations exactly ->
PSD of all reduced blocks via exact L D L^T + diagonally dominant remainder.
"""
import os, sys, json, time
os.environ.setdefault("POLYD", "12")
import numpy as np
import scipy.linalg as sla
import scipy.sparse as sp
from numpy.polynomial import chebyshev as C
from fractions import Fraction as Fr
import mpmath as mp
import flint
from flint import fmpq, fmpq_mat, fmpz, nmod_mat
sys.path.insert(1, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "hp"))
import spec
import check_cert as CC

HERE = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 60
PRIME = 2305843009213693951  # 2^61 - 1
KROUND = 80
SHIFT_A = float(os.environ.get("SHIFT_A", "0"))
PIN_SLOPE_A = os.environ.get("PIN_SLOPE_A", "0") == "1"


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


def load_face():
    js = json.load(open(os.path.join(HERE, "face_D12_val.json")))
    return {k: (v["n"], [[Fr(x) for x in row] for row in v["N"]]) for k, v in js.items()}


def dyadic_below(x, k):
    """largest m/2^k <= x (x mpf)."""
    return Fr(int(mp.floor(x * mp.mpf(2) ** k)), 2 ** k)


def main(solfile, eta_exp=58):
    face = load_face()
    sol = np.load(solfile)
    rows_mon = spec.monos_upto(spec.D)
    rows_mon = [e for e in rows_mon]                 # 455 monomials of degree <= 12
    ridx = {e: i for i, e in enumerate(rows_mon)}
    NR = len(rows_mon)
    TAGS = ("A", "B", "G")
    # ---------------- unknown layout
    var = []          # (kind, key, i, j) ; kind in {"F","B","h","c"}
    xf = []           # float values
    def sym_entries(name, M):
        n = M.shape[0]
        for i in range(n):
            for j in range(i, n):
                var.append(("M", name, i, j)); xf.append(float(M[i, j]))
    lhs_names = []
    for X in "PR":
        for k in range(len(spec.SIZES)):
            nm = f"F{X}{k}"
            if len(face[nm][1][0]) if face[nm][1] else 0:
                sym_entries(nm, sol[nm]); lhs_names.append(nm)
    for nm in ("hA", "hB", "hC", "pBa", "pCb"):
        mono = C.cheb2poly(sol[nm])
        mono = np.concatenate([mono, np.zeros(spec.D + 1 - len(mono))])
        for j in range(spec.D + 1):
            var.append(("h", nm, j, None)); xf.append(float(mono[j]))
    for nm in ("ca", "cb", "e"):
        var.append(("c", nm, None, None)); xf.append(float(sol[nm][0]))
    nL = len(var)
    blk_names = {}
    for tag in TAGS:
        blk_names[tag] = []
        for r in range(len(spec.multipliers()[tag])):
            nm = f"{tag}_B{r}"
            if face[nm][1] and len(face[nm][1][0]):
                sym_entries(nm, sol[nm]); blk_names[tag].append((r, nm))
    nV = len(var)
    xf = np.array(xf)
    # optional exact-compatible shift: H_A -= SHIFT_A * 100 (t+1)  and  B^A_1[0,0] -= 20 SHIFT_A
    # (lambda_A drops by 20 SHIFT_A (u+1), which is exactly the multiplier u - lo of block A_B1 times z_0^2 = 1);
    # this raises phi - H_A by SHIFT_A at t = -99/100 and keeps H_A(-1).
    if SHIFT_A:
        nA, NA = face["A_B1"]
        k0 = [k for k in range(len(NA[0])) if NA[0][k] == 1 and all(NA[i][k] == 0 for i in range(1, nA))]
        assert len(k0) == 1 and all(NA[0][k] == 0 for k in range(len(NA[0])) if k != k0[0]); k0 = k0[0]
        for j, (kind, nm, a, b) in enumerate(var):
            if kind == "h" and nm == "hA" and a in (0, 1):
                xf[j] -= SHIFT_A * 100
            if kind == "M" and nm == "A_B1" and a == k0 and b == k0:
                xf[j] -= 20 * SHIFT_A
        log(f"applied SHIFT_A = {SHIFT_A}")
    log(f"unknowns: {nV} ({nL} lhs)")
    # ---------------- exact columns: list of dicts row -> Fraction ; rows: tag-major identities
    cols = [dict() for _ in range(nV)]
    def rowof(tag, e):
        return TAGS.index(tag) * NR + ridx[e]
    # LHS columns through check_cert.lam_polys (affine, zero at zero)
    zeroF = {X: [[[Fr(0)] * m for _ in range(m)] for m in spec.SIZES] for X in "PR"}
    base = dict(hA=[Fr(0)] * 13, hB=[Fr(0)] * 13, hC=[Fr(0)] * 13, pBa=[Fr(0)] * 13, pCb=[Fr(0)] * 13,
                ca=Fr(0), cb=Fr(0), e=Fr(0), FP=zeroF["P"], FR=zeroF["R"])
    for j in range(nL):
        kind, nm, a, b = var[j]
        c = dict(base)
        if kind == "M":
            X = nm[1]; k = int(nm[2:]); m = spec.SIZES[k]; N = face[nm][1]
            Fk = [[N[p][a] * N[q][b] + (N[p][b] * N[q][a] if a != b else 0) for q in range(m)] for p in range(m)]
            Fs = [row for row in zeroF[X]]; Fs = list(Fs); Fs[k] = Fk
            c["F" + X] = Fs
        elif kind == "h":
            v = [Fr(0)] * 13; v[a] = Fr(1); c[nm] = v
        else:
            c[nm] = Fr(1)
        lam = CC.lam_polys(c)
        for tag in TAGS:
            for e, v in lam[tag].items():
                cols[j][rowof(tag, e)] = v
    log("lhs columns done")
    mults = spec.multipliers()
    for tag in TAGS:
        for (r, nm) in blk_names[tag]:
            _, g, d = mults[tag][r]
            Z = spec.monos_upto(d); n, N = face[nm]
            kept = len(N[0])
            w = []
            for kk in range(kept):
                w.append({Z[i]: N[i][kk] for i in range(n) if N[i][kk] != 0})
            gw = [spec.pmul(g, wk) for wk in w]
            j = next(jj for jj in range(nL, nV) if var[jj][1] == nm)
            for a in range(kept):
                for b in range(a, kept):
                    assert var[j][1] == nm and var[j][2] == a and var[j][3] == b
                    pol = spec.pmul(gw[a], w[b])
                    f = -2 if a != b else -1
                    cols[j] = {rowof(tag, e): f * v for e, v in pol.items()}
                    j += 1
        log(f"rhs columns {tag} done")
    # ---------------- pins
    phi = lambda t: (2 - 2 * t) ** mp.mpf(-0.5)
    dphi = lambda t: (2 - 2 * t) ** mp.mpf(-1.5)
    s5 = mp.sqrt(5); c1 = (s5 - 1) / 4; c2 = (-s5 - 1) / 4
    alpha0 = dyadic_below(phi(-1) - mp.mpf(2) ** (-eta_exp), eta_exp + 8)
    beta0 = dyadic_below(phi(0) - mp.mpf(2) ** (-eta_exp), eta_exp + 8)
    A0 = (phi(c1) + phi(c2)) / 2 - mp.mpf(2) ** (-eta_exp)
    B0 = (phi(c1) - phi(c2)) / (2 * s5)
    a0 = dyadic_below(A0, eta_exp + 8); b0 = Fr(int(mp.nint(B0 * mp.mpf(2) ** (eta_exp + 8))), 2 ** (eta_exp + 8))
    e0 = alpha0 + 10 * beta0 + 10 * a0
    v = lambda q: mp.mpf(q.numerator) / q.denominator
    assert v(alpha0) < phi(-1) and v(beta0) < phi(0) and v(a0) + v(b0) * s5 < phi(c1) and v(a0) - v(b0) * s5 < phi(c2)
    EP = phi(-1) + 10 * phi(0) + 5 * phi(c1) + 5 * phi(c2)
    log("E(P) - e0 =", mp.nstr(EP - v(e0), 8))
    hidx = {(var[j][1], var[j][2]): j for j in range(nL) if var[j][0] == "h"}
    cidx = {var[j][1]: j for j in range(nL) if var[j][0] == "c"}
    pins = []   # (dict col->coef, rhs)
    # s = 1: first-order contact at 0, slope pinned to a dyadic within 2^-(eta+8) of phi'(0) = 2^(-3/2)
    beta1 = Fr(int(mp.nint(dphi(0) * mp.mpf(2) ** (eta_exp + 8))), 2 ** (eta_exp + 8))
    for jj, val in ((0, beta0), (1, beta1)):
        pins.append(({hidx[("hB", jj)]: Fr(1)}, val))
    pins.append(({hidx[("hA", jj)]: Fr((-1) ** jj) for jj in range(13)}, alpha0))
    if PIN_SLOPE_A:   # H_A'(-1) = phi'(-1) = 1/4
        pins.append(({hidx[("hA", jj)]: Fr(jj * (-1) ** (jj - 1)) for jj in range(1, 13)}, Fr(1, 4)))
    # powers of c1 = -1/4 + 1/4 sqrt5 as x + y sqrt5
    pw = [(Fr(1), Fr(0))]
    for _ in range(13):
        x, y = pw[-1]; pw.append((x * Fr(-1, 4) + 5 * y * Fr(1, 4), x * Fr(1, 4) + y * Fr(-1, 4)))
    pins.append(({hidx[("hC", jj)]: pw[jj][0] for jj in range(13)}, a0))
    pins.append(({hidx[("hC", jj)]: pw[jj][1] for jj in range(13)}, b0))
    # derivative: sum j h_j c1^(j-1) = x1 + y1 sqrt5 ~ phi'(c1) (conjugate ~ phi'(c2)); s = 1: dyadic, not exact
    X1 = (dphi(c1) + dphi(c2)) / 2; Y1 = (dphi(c1) - dphi(c2)) / (2 * s5)
    x1 = Fr(int(mp.nint(X1 * mp.mpf(2) ** (eta_exp + 8))), 2 ** (eta_exp + 8))
    y1 = Fr(int(mp.nint(Y1 * mp.mpf(2) ** (eta_exp + 8))), 2 ** (eta_exp + 8))
    pins.append(({hidx[("hC", jj)]: jj * pw[jj - 1][0] for jj in range(1, 13)}, x1))
    pins.append(({hidx[("hC", jj)]: jj * pw[jj - 1][1] for jj in range(1, 13)}, y1))
    pins.append(({cidx["e"]: Fr(1)}, e0))
    nEq = 3 * NR + len(pins)
    for p, (dct, _) in enumerate(pins):
        for j, cf in dct.items():
            if cf != 0:
                cols[j][3 * NR + p] = cf
    bvec = [Fr(0)] * (3 * NR) + [val for (_, val) in pins]
    # ---------------- float polish
    I, Jc, Vv = [], [], []
    for j, cd in enumerate(cols):
        for i, cf in cd.items():
            I.append(i); Jc.append(j); Vv.append(float(cf))
    Af = sp.csr_matrix((Vv, (I, Jc)), shape=(nEq, nV))
    bf = np.array([float(x) for x in bvec])
    log("float residual of solver output:", np.abs(Af @ xf - bf).max())
    AAt = (Af @ Af.T).toarray()
    w_, Q_ = np.linalg.eigh(AAt)
    keep = w_ > w_.max() * 1e-13
    log(f"numerical rank {keep.sum()} of {nEq}, eig range kept {w_[keep].min():.3g}..{w_.max():.3g}")
    pinvAAt = (Q_[:, keep] / w_[keep]) @ Q_[:, keep].T
    x = xf.copy()
    for it in range(3):
        r = bf - Af @ x
        x = x + Af.T @ (pinvAAt @ r)
        log(f"polish {it}: residual {np.abs(bf - Af @ x).max():.3g}, |dx| {np.abs(Af.T @ (pinvAAt @ r)).max():.3g}")
    # ---------------- row basis: float pivoted QR on A^T (exactness is verified afterwards: a singular
    # pivot system makes the exact solve fail, and every equation is re-checked exactly at the end)
    rank = int(keep.sum())
    Rr, pivr = sla.qr(Af.T.toarray(), mode="r", pivoting=True)
    rowbasis = sorted(pivr[:rank].tolist())
    log(f"row basis: rank {rank}; dropped rows {nEq - rank}; |R_ii| min {np.abs(np.diag(Rr))[:rank].min():.3g}")
    del Rr
    # ---------------- pivot columns: float QR with pivoting on the row-basis submatrix
    Asub = Af[rowbasis, :].toarray()
    # scale columns by 1 (plain) ; prefer SOS entries and h/psi, exclude pinned-only e
    Rq, piv = sla.qr(Asub, mode="r", pivoting=True)
    S = sorted(piv[:rank].tolist())
    dg = np.abs(np.diag(Rq))
    log(f"pivot QR: |R_ii| range {dg[:rank].min():.3g}..{dg[0]:.3g}")
    # ---------------- round & exact solve
    xq = [None] * nV
    for j in range(nV):
        xq[j] = Fr(int(mp.nint(mp.mpf(x[j]) * mp.mpf(2) ** KROUND)), 2 ** KROUND)
    Sset = set(S)
    rhs = [bvec[i] for i in rowbasis]
    pos = {i: p for p, i in enumerate(rowbasis)}
    rhs_q = [fmpq(int(q.numerator), int(q.denominator)) for q in rhs]
    for j in range(nV):
        if j in Sset:
            continue
        xj = fmpq(int(xq[j].numerator), int(xq[j].denominator))
        if xj == 0:
            continue
        for i, cf in cols[j].items():
            if i in pos:
                rhs_q[pos[i]] -= fmpq(int(cf.numerator), int(cf.denominator)) * xj
    AS = fmpq_mat(rank, rank)
    Spos = {j: p for p, j in enumerate(S)}
    for j in S:
        for i, cf in cols[j].items():
            if i in pos:
                AS[pos[i], Spos[j]] = fmpq(int(cf.numerator), int(cf.denominator))
    log("exact solve", rank, "x", rank)
    xs = AS.solve(fmpq_mat(rank, 1, rhs_q))
    log("solved")
    xe = [fmpq(int(q.numerator), int(q.denominator)) for q in xq]
    dmax = 0.0
    for j in S:
        val = xs[Spos[j], 0]
        dmax = max(dmax, abs(float(Fr(int(val.p), int(val.q))) - x[j]))
        xe[j] = val
    log(f"max pivot change vs polished float: {dmax:.3g}")
    # ---------------- verify ALL equations exactly
    res = [fmpq(0)] * nEq
    for j, cd in enumerate(cols):
        if xe[j] == 0:
            continue
        for i, cf in cd.items():
            res[i] += fmpq(int(cf.numerator), int(cf.denominator)) * xe[j]
    bad = [i for i in range(nEq) if res[i] != fmpq(int(bvec[i].numerator), int(bvec[i].denominator))]
    log(f"exact equation check: {len(bad)} violated rows")
    if bad:
        raise SystemExit(f"inconsistent rows: {bad[:20]}")
    # ---------------- assemble reduced blocks, PSD certificates
    def fq2s(q):
        return str(q)
    blocks = {}
    for j, (kind, nm, a, b) in enumerate(var):
        if kind == "M":
            blocks.setdefault(nm, {})[(a, b)] = xe[j]
    psd = {}
    minev = {}
    for nm, ent in blocks.items():
        n = max(a for a, b in ent) + 1
        M = fmpq_mat(n, n)
        for (a, b), val in ent.items():
            M[a, b] = val; M[b, a] = val
        Mf = np.array([[float(Fr(int(M[i, j].p), int(M[i, j].q))) for j in range(n)] for i in range(n)])
        ev = np.linalg.eigvalsh(Mf); minev[nm] = float(ev[0])
        eps = ev[0] / 2
        # float LDL^T of M - eps I (no pivoting; M is PD)
        Lf, dfl = ldl_nopiv(Mf - eps * np.eye(n))
        L = [[Fr(int(round(Lf[i, j] * 2.0 ** 52)), 2 ** 52) if j < i else Fr(int(i == j)) for j in range(n)] for i in range(n)]
        dd = [max(Fr(0), Fr(int(round(dfl[i] * 2.0 ** 60)), 2 ** 60)) for i in range(n)]
        # exact DD check with flint
        Lq = fmpq_mat(n, n, [fmpq(int(L[i][j].numerator), int(L[i][j].denominator)) for i in range(n) for j in range(n)])
        Dq = fmpq_mat(n, n, [fmpq(int(dd[i].numerator), int(dd[i].denominator)) if i == j else fmpq(0) for i in range(n) for j in range(n)])
        Delta = M - Lq * Dq * Lq.transpose()
        slack = min(Delta[i, i] - sum((abs(Delta[i, j]) for j in range(n) if j != i), fmpq(0)) for i in range(n))
        if slack < 0:
            raise SystemExit(f"PSD certificate failed for {nm}: slack {float(Fr(int(slack.p), int(slack.q)))}, min eig {ev[0]}")
        psd[nm] = (M, L, dd, float(Fr(int(slack.p), int(slack.q))))
    log("PSD certificates OK; min eigenvalues:", {k: f"{v:.2e}" for k, v in sorted(minev.items(), key=lambda kv: kv[1])[:6]})
    # ---------------- write certificate
    def matstr(M, n):
        return [[str(M[i, j]) for j in range(n)] for i in range(n)]
    hv = {nm: [None] * 13 for nm in ("hA", "hB", "hC", "pBa", "pCb")}
    cv = {}
    for j, (kind, nm, a, b) in enumerate(var):
        if kind == "h":
            hv[nm][a] = str(xe[j])
        elif kind == "c":
            cv[nm] = xe[j]
    Fout = {}
    for X in "PR":
        Fout[X] = []
        for k, m in enumerate(spec.SIZES):
            nm = f"F{X}{k}"; n, N = face[nm]
            ent = {"m": m, "N": [[str(x) for x in row] for row in N]}
            if nm in psd:
                Mq, L, dd, sl = psd[nm]; kk = Mq.nrows()
                ent.update(red=matstr(Mq, kk), L=[[str(x) for x in row] for row in L], d=[str(x) for x in dd])
            else:
                ent.update(red=[], L=[], d=[])
            Fout[X].append(ent)
    SOS = {}
    for tag in TAGS:
        SOS[tag] = []
        for r, (gname, g, d) in enumerate(mults[tag]):
            nm = f"{tag}_B{r}"; n, N = face[nm]
            ent = {"mult": gname, "g": {f"{a},{b},{c}": str(v) for (a, b, c), v in g.items()}, "d": d,
                   "N": [[str(x) for x in row] for row in N]}
            if nm in psd:
                Mq, L, dd, sl = psd[nm]; kk = Mq.nrows()
                ent.update(red=matstr(Mq, kk), L=[[str(x) for x in row] for row in L], d_piv=[str(x) for x in dd])
            else:
                ent.update(red=[], L=[], d_piv=[])
            SOS[tag].append(ent)
    # c_gamma from (6)
    cfull = dict(hA=[Fr(s) for s in hv["hA"]], hB=[Fr(s) for s in hv["hB"]], hC=[Fr(s) for s in hv["hC"]],
                 pBa=[Fr(s) for s in hv["pBa"]], pCb=[Fr(s) for s in hv["pCb"]],
                 ca=Fr(str(cv["ca"])), cb=Fr(str(cv["cb"])), e=Fr(str(cv["e"])))
    zero = lambda m: [[Fr(0)] * m for _ in range(m)]
    for X in "PR":
        mats = []
        for k, m in enumerate(spec.SIZES):
            nm = f"F{X}{k}"; n, N = face[nm]
            if nm in psd:
                Mq = psd[nm][0]; kk = Mq.nrows()
                R = [[Fr(str(Mq[i, j])) for j in range(kk)] for i in range(kk)]
                mats.append(CC.congruence(N, R))
            else:
                mats.append(zero(m))
        cfull["F" + X] = mats
    lam = CC.lam_polys(cfull)
    cert = {"kernel": "coulomb  phi(t) = (2-2t)^(-1/2)", "cell": ["-1", "-99/100"], "D": spec.D,
            "sizes": list(spec.SIZES), "dA": list(spec.DA),
            "H": {"A": hv["hA"], "B": hv["hB"], "C": hv["hC"]}, "psi": {"Ba": hv["pBa"], "Cb": hv["pCb"]},
            "ca": str(cv["ca"]), "cb": str(cv["cb"]), "cg": str(lam["cg"]), "e": str(cv["e"]),
            "pins": {"alpha0": str(alpha0), "beta0": str(beta0), "beta1": str(beta1), "a0": str(a0), "b0": str(b0), "x1": str(x1), "y1": str(y1)},
            "F": Fout, "SOS": SOS}
    out = os.path.join(HERE, "cert_cap_coulomb_D12.json")
    with open(out, "w") as fh:
        json.dump(cert, fh)
    log("wrote", out, os.path.getsize(out) // 1024, "KiB;  e - E(P) =", mp.nstr(v(Fr(str(cv["e"]))) - EP, 8))
    return cert


def ldl_nopiv(M):
    n = M.shape[0]
    L = np.eye(n); d = np.zeros(n); A = M.copy()
    for k in range(n):
        d[k] = A[k, k]
        L[k + 1:, k] = A[k + 1:, k] / d[k]
        A[k + 1:, k + 1:] -= np.outer(L[k + 1:, k], A[k, k + 1:])
    return L, d


if __name__ == "__main__":
    T0 = time.time()
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "sol_mu.npz"),
         int(sys.argv[2]) if len(sys.argv) > 2 else 58)
