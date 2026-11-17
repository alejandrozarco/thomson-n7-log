"""capR prototype: the N = 7 cap certificate as an affine function of the kernel-data vector v(s).

Float only (numpy, one thread, < 1 GB).  Nothing here is a proof; it measures the quantities that decide the
piece width of the method described in DESIGN.md.

Layout of the certificate vector x (identical to ../capS/round_capS.py): reduced kernel blocks F'_X^(k) (upper
triangle), H_A, H_B, H_C, psi_Ba, psi_Cb (13 monomial coefficients each), c_alpha, c_beta, e, reduced SOS blocks
B'_r (upper triangle).  nV = 39454.
Linear structure:   L x = 0      (3 x 455 identity rows + the e-row  e - H_A(-1) - 10 H_B(0) - 10 Re H_C(c1) = 0)
                    Pin x = v    (7 rows: H_B(0), H_B'(0), H_A(-1), Re/Im H_C(c1), Re/Im H_C'(c1) in Q(sqrt5))
with v(s) = (beta0, beta1, alpha0, a0, b0, x1, y1)(s) the kernel data of phi_s.  L and Pin do not depend on s.

usage:  OMP_NUM_THREADS=1 python3 affine_cap.py build      # builds and caches sys_D12.npz (~10 s)
        OMP_NUM_THREADS=1 python3 affine_cap.py measure    # directions C_k, norms, margins along the curve
        OMP_NUM_THREADS=1 python3 affine_cap.py minorant   # node minorant margins vs needed margins, contact curvature
        OMP_NUM_THREADS=1 python3 affine_cap.py optimise   # per-block rigorous piece width, block reweighting
Run on the Mac with nice -n 19 taskpolicy -b; see DESIGN.md for the method and the numbers.
"""
import os, sys, json, time
os.environ.setdefault("POLYD", "12")
import numpy as np
import scipy.sparse as sp
import scipy.linalg as sla
from fractions import Fraction as Fr
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
CAPS = os.path.join(HERE, "..", "capS")
CAP1 = os.path.join(HERE, "..", "cap1")
sys.path.insert(0, CAPS)
sys.path.insert(1, os.path.join(HERE, "..", "..", "hp"))
import spec
import check_cert as CC

mp.mp.dps = 40
T0 = time.time()
NPIN = 7
PIN_NAMES = ("beta0=H_B(0)", "beta1=H_B'(0)", "alpha0=H_A(-1)", "a0=Re H_C(c1)", "b0=Im H_C(c1)", "x1=Re H_C'(c1)", "y1=Im H_C'(c1)")


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


def load_face():
    js = json.load(open(os.path.join(CAPS, "face_D12_val.json")))
    return {k: (v["n"], [[Fr(x) for x in row] for row in v["N"]]) for k, v in js.items()}


def layout(face):
    """list of (kind, name, i, j) exactly as round_capS.main."""
    var = []
    def sym(name, k):
        for i in range(k):
            for j in range(i, k):
                var.append(("M", name, i, j))
    lhs_names = []
    for X in "PR":
        for k in range(len(spec.SIZES)):
            nm = f"F{X}{k}"
            kept = len(face[nm][1][0]) if face[nm][1] else 0
            if kept:
                sym(nm, kept); lhs_names.append(nm)
    for nm in ("hA", "hB", "hC", "pBa", "pCb"):
        for j in range(spec.D + 1):
            var.append(("h", nm, j, None))
    for nm in ("ca", "cb", "e"):
        var.append(("c", nm, None, None))
    nL = len(var)
    blk = {}
    for tag in ("A", "B", "G"):
        blk[tag] = []
        for r in range(len(spec.multipliers()[tag])):
            nm = f"{tag}_B{r}"
            if face[nm][1] and len(face[nm][1][0]):
                sym(nm, len(face[nm][1][0])); blk[tag].append((r, nm))
    return var, nL, blk


def sqrt5_powers(n=13):
    """c1^j = x + y sqrt5 with c1 = (-1 + sqrt5)/4."""
    pw = [(Fr(1), Fr(0))]
    for _ in range(n):
        x, y = pw[-1]; pw.append((x * Fr(-1, 4) + 5 * y * Fr(1, 4), x * Fr(1, 4) + y * Fr(-1, 4)))
    return pw


def build():
    face = load_face()
    var, nL, blk = layout(face)
    nV = len(var)
    rows_mon = spec.monos_upto(spec.D); ridx = {e: i for i, e in enumerate(rows_mon)}; NR = len(rows_mon)
    TAGS = ("A", "B", "G")
    rowof = lambda tag, e: TAGS.index(tag) * NR + ridx[e]
    I, J, V = [], [], []
    zeroF = {X: [[[Fr(0)] * m for _ in range(m)] for m in spec.SIZES] for X in "PR"}
    base = dict(hA=[Fr(0)] * 13, hB=[Fr(0)] * 13, hC=[Fr(0)] * 13, pBa=[Fr(0)] * 13, pCb=[Fr(0)] * 13,
                ca=Fr(0), cb=Fr(0), e=Fr(0), FP=zeroF["P"], FR=zeroF["R"])
    for j in range(nL):
        kind, nm, a, b = var[j]
        c = dict(base)
        if kind == "M":
            X = nm[1]; k = int(nm[2:]); m = spec.SIZES[k]; N = face[nm][1]
            Fk = [[N[p][a] * N[q][b] + (N[p][b] * N[q][a] if a != b else 0) for q in range(m)] for p in range(m)]
            Fs = list(zeroF[X]); Fs[k] = Fk; c["F" + X] = Fs
        elif kind == "h":
            v = [Fr(0)] * 13; v[a] = Fr(1); c[nm] = v
        else:
            c[nm] = Fr(1)
        lam = CC.lam_polys(c)
        for tag in TAGS:
            for e, v in lam[tag].items():
                I.append(rowof(tag, e)); J.append(j); V.append(float(v))
    log("lhs columns done")
    mults = spec.multipliers()
    for tag in TAGS:
        for (r, nm) in blk[tag]:
            _, g, d = mults[tag][r]
            Z = spec.monos_upto(d); n, N = face[nm]; kept = len(N[0])
            w = [{Z[i]: N[i][kk] for i in range(n) if N[i][kk] != 0} for kk in range(kept)]
            gw = [spec.pmul(g, wk) for wk in w]
            j = next(jj for jj in range(nL, nV) if var[jj][1] == nm)
            for a in range(kept):
                for b in range(a, kept):
                    assert var[j] == ("M", nm, a, b)
                    pol = spec.pmul(gw[a], w[b]); f = -2 if a != b else -1
                    for e, v in pol.items():
                        I.append(rowof(tag, e)); J.append(j); V.append(f * float(v))
                    j += 1
        log(f"rhs columns {tag} done")
    # e-row (homogeneous) and the 7 pin rows
    hidx = {(var[j][1], var[j][2]): j for j in range(nL) if var[j][0] == "h"}
    cidx = {var[j][1]: j for j in range(nL) if var[j][0] == "c"}
    pw = sqrt5_powers()
    pins = [
        {hidx[("hB", 0)]: Fr(1)},
        {hidx[("hB", 1)]: Fr(1)},
        {hidx[("hA", jj)]: Fr((-1) ** jj) for jj in range(13)},
        {hidx[("hC", jj)]: pw[jj][0] for jj in range(13)},
        {hidx[("hC", jj)]: pw[jj][1] for jj in range(13)},
        {hidx[("hC", jj)]: jj * pw[jj - 1][0] for jj in range(1, 13)},
        {hidx[("hC", jj)]: jj * pw[jj - 1][1] for jj in range(1, 13)},
    ]
    erow = {cidx["e"]: Fr(1)}
    for d, cf in ((pins[2], -1), (pins[0], -10), (pins[3], -10)):
        for j, v in d.items():
            erow[j] = erow.get(j, Fr(0)) + cf * v
    rE = 3 * NR
    for j, v in erow.items():
        I.append(rE); J.append(j); V.append(float(v))
    for p, d in enumerate(pins):
        for j, v in d.items():
            I.append(rE + 1 + p); J.append(j); V.append(float(v))
    nEq = rE + 1 + NPIN
    A = sp.csr_matrix((V, (I, J)), shape=(nEq, nV))
    A.sum_duplicates()
    sp.save_npz(os.path.join(HERE, "sys_D12.npz"), A)
    json.dump(dict(var=var, nL=nL, nEq=nEq, nV=nV, nLrows=rE + 1), open(os.path.join(HERE, "sys_D12_layout.json"), "w"))
    log(f"saved A: {A.shape}, nnz {A.nnz}")
    return A, var


def load_system():
    A = sp.load_npz(os.path.join(HERE, "sys_D12.npz")).tocsr()
    lay = json.load(open(os.path.join(HERE, "sys_D12_layout.json")))
    var = [tuple(v) for v in lay["var"]]
    return A, var, lay


def cert_vector(path, var):
    """exact certificate JSON -> float vector in the layout."""
    J = json.load(open(path))
    x = np.zeros(len(var))
    red = {}
    for X in "PR":
        for k, b in enumerate(J["F"][X]):
            red[f"F{X}{k}"] = b["red"]
    for tag in ("A", "B", "G"):
        for r, b in enumerate(J["SOS"][tag]):
            red[f"{tag}_B{r}"] = b["red"]
    hv = {"hA": J["H"]["A"], "hB": J["H"]["B"], "hC": J["H"]["C"], "pBa": J["psi"]["Ba"], "pCb": J["psi"]["Cb"]}
    for j, (kind, nm, a, b) in enumerate(var):
        if kind == "M":
            x[j] = float(Fr(red[nm][a][b]))
        elif kind == "h":
            x[j] = float(Fr(hv[nm][a]))
        else:
            x[j] = float(Fr(J[nm]))
    return x, J


# ---------------- kernel data v(s) and its s-derivatives (mpmath)
def pins_mp(s):
    s = mp.mpf(s)
    s5 = mp.sqrt(5); c1 = (s5 - 1) / 4; c2 = (-s5 - 1) / 4
    phi = lambda t: (2 - 2 * t) ** (-s / 2)
    dphi = lambda t: s * (2 - 2 * t) ** (-s / 2 - 1)
    return [phi(0), dphi(0), phi(-1), (phi(c1) + phi(c2)) / 2, (phi(c1) - phi(c2)) / (2 * s5),
            (dphi(c1) + dphi(c2)) / 2, (dphi(c1) - dphi(c2)) / (2 * s5)]


def pins(s, order=0):
    if order == 0:
        return np.array([float(x) for x in pins_mp(s)])
    return np.array([float(mp.diff(lambda z: pins_mp(z)[k], s, order)) for k in range(NPIN)])


def EP(s):
    v = pins_mp(s)
    return float(v[2] + 10 * v[0] + 10 * v[3])


# ---------------- blocks from a vector
def blocks_of(x, var):
    out = {}
    for j, (kind, nm, a, b) in enumerate(var):
        if kind != "M":
            continue
        if nm not in out:
            out[nm] = {}
        out[nm][(a, b)] = x[j]
    mats = {}
    for nm, ent in out.items():
        n = max(a for a, b in ent) + 1
        M = np.zeros((n, n))
        for (a, b), v in ent.items():
            M[a, b] = v; M[b, a] = v
        mats[nm] = M
    return mats


def hpoly(x, var, nm):
    return np.array([x[j] for j, (kind, n2, a, b) in enumerate(var) if kind == "h" and n2 == nm])


def mineig(mats, names=None):
    names = names or mats.keys()
    return {nm: float(np.linalg.eigvalsh(mats[nm])[0]) for nm in names}


def specnorm(M):
    w = np.linalg.eigvalsh(M)
    return float(max(-w[0], w[-1]))


def measure():
    A, var, lay = load_system()
    nEq, nV, nLrows = lay["nEq"], lay["nV"], lay["nLrows"]
    log(f"system {A.shape}, L rows {nLrows}, pin rows {NPIN}")
    # ---- node certificates
    nodes = {Fr(1, 2): os.path.join(CAPS, "cert_cap_s1_2_D12.json"),
             Fr(3, 4): os.path.join(CAPS, "cert_cap_s3_4_D12.json"),
             Fr(1): os.path.join(CAP1, "cert_cap_coulomb_D12.json")}
    X = {}
    for s, p in nodes.items():
        x, J = cert_vector(p, var)
        r = A @ x
        v = pins(float(s))
        log(f"node s={s}: |L x|_max {np.abs(r[:nLrows]).max():.2e}, pins - v(s): {np.abs(r[nLrows:] - v).max():.2e} "
            f"(dyadic pins below phi), e - E(P) {x[[j for j,v_ in enumerate(var) if v_[1]=='e'][0]] - EP(float(s)):.2e}")
        X[s] = x
    blocks = {s: blocks_of(x, var) for s, x in X.items()}
    bnames = list(blocks[Fr(1)].keys())
    mu = {s: min(mineig(blocks[s]).values()) for s in X}
    log("node min eigenvalues (reduced blocks):", {str(s): f"{m:.3e}" for s, m in mu.items()})
    # ---- weighted min-norm directions C_k:  min |W x|  s.t.  L x = 0, Pin x = e_k
    w = np.ones(nV)
    for j, (kind, nm, a, b) in enumerate(var):
        if kind == "M":
            w[j] = 1.0 if a == b else np.sqrt(2)      # Frobenius norm of the symmetric block
        else:
            w[j] = float(os.environ.get("WH", "1e-3"))   # h's and c's nearly free
    Winv2 = sp.diags(1.0 / w ** 2)
    G = (A @ Winv2 @ A.T).toarray()
    ev, Q = np.linalg.eigh(G)
    keep = ev > ev.max() * 1e-12
    log(f"Gram rank {keep.sum()} of {nEq}")
    Gp = (Q[:, keep] / ev[keep]) @ Q[:, keep].T
    C = []
    for k in range(NPIN):
        rhs = np.zeros(nEq); rhs[nLrows + k] = 1.0
        xk = Winv2 @ (A.T @ (Gp @ rhs))
        res = A @ xk - rhs
        C.append(xk)
        log(f"C_{k} ({PIN_NAMES[k]}): residual {np.abs(res).max():.1e}, |blocks|_F {np.linalg.norm(w[:]*xk):.3e}")
    Cb = [blocks_of(c, var) for c in C]
    normk = [max(specnorm(Cb[k][nm]) for nm in bnames) for k in range(NPIN)]
    log("max_block ||B_k||_2:", [f"{n:.3e}" for n in normk])
    for k in range(NPIN):
        top = sorted(((specnorm(Cb[k][nm]), nm) for nm in bnames), reverse=True)[:3]
        log(f"   C_{k}: top blocks {[(nm, f'{v:.2e}') for v, nm in top]}")
    # ---- combined direction for w = v''(s_m)
    out = {"normk": normk, "mu": {str(s): m for s, m in mu.items()}}
    for sm in (0.625, 0.875, 0.5, 1.0, 1.5):
        v2 = pins(sm, 2)
        Bw = {nm: sum(v2[k] * Cb[k][nm] for k in range(NPIN)) for nm in bnames}
        lmax = max(float(np.linalg.eigvalsh(Bw[nm])[-1]) for nm in bnames)
        lmin = min(float(np.linalg.eigvalsh(Bw[nm])[0]) for nm in bnames)
        bound_sum = sum(abs(v2[k]) * normk[k] for k in range(NPIN))
        mu_ref = 3.8e-6
        log(f"s_m={sm}: v''={np.round(v2, 4)}; B_w: lambda_max {lmax:.3e}, lambda_min {lmin:.3e}; "
            f"sum|v_k''| |B_k| {bound_sum:.3e};  h_max(lin, mu=3.8e-6) = sqrt(8 mu/lmax) = {np.sqrt(8 * mu_ref / lmax):.3e}, "
            f"with sum-bound {np.sqrt(8 * mu_ref / bound_sum):.3e}")
        out[f"Bw_{sm}"] = dict(lmax=lmax, lmin=lmin, bound_sum=bound_sum)
    # ---- along-curve test on the two available pieces (h = 1/4): chord vs chord + correction
    for (a, b) in ((Fr(1, 2), Fr(3, 4)), (Fr(3, 4), Fr(1))):
        xa, xb = X[a], X[b]
        va = A[nLrows:] @ xa; vb = A[nLrows:] @ xb      # the nodes' (dyadic) pins
        h = float(b - a)
        log(f"piece [{a}, {b}] (h = {h}): chord-only pin overshoot at midpoint "
            f"{np.round((va + vb) / 2 - pins(float(a) + h / 2), 6)} (predicted h^2/8 v'' = {np.round(h*h/8*pins(float(a)+h/2,2), 6)})")
        rows = []
        for lam in np.linspace(0, 1, 11):
            s = float(a) + lam * h
            xc = (1 - lam) * xa + lam * xb
            rho = pins(s) - ((1 - lam) * va + lam * vb)
            xcorr = xc + sum(rho[k] * C[k] for k in range(NPIN))
            mc = min(mineig(blocks_of(xc, var)).values())
            mm = mineig(blocks_of(xcorr, var)); mcor = min(mm.values()); arg = min(mm, key=mm.get)
            # H_B(0) - phi_s(0) for the two
            vc = A[nLrows:] @ xc; vcor = A[nLrows:] @ xcorr
            rows.append((s, mc, mcor, arg, float(vc[0] - pins(s)[0]), float(vcor[0] - pins(s)[0])))
        for r in rows:
            log(f"   s={r[0]:.4f}: mineig chord {r[1]:+.3e}, chord+corr {r[2]:+.3e} ({r[3]}); H_B(0)-phi: chord {r[4]:+.2e}, corr {r[5]:+.1e}")
        out[f"piece_{a}_{b}"] = [list(map(float, r[:3])) + [r[3]] for r in rows]
    # ---- 3-node quadratic: Delta = B_m - (B_a + B_b)/2 at h = 1/4 (nodes 1/2, 3/4, 1)
    xa, xm, xb = X[Fr(1, 2)], X[Fr(3, 4)], X[Fr(1)]
    D = blocks_of(xm - (xa + xb) / 2, var)
    dmin = mineig(D); dmax = {nm: float(np.linalg.eigvalsh(D[nm])[-1]) for nm in bnames}
    log(f"quadratic: Delta = B_3/4 - (B_1/2 + B_1)/2: min eig {min(dmin.values()):+.3e} ({min(dmin, key=dmin.get)}), "
        f"max eig {max(dmax.values()):+.3e}; |Delta| ~ h^2/8 |B''| => |B''|_2 ~ {max(max(-min(dmin.values()),max(dmax.values())) / (0.5**2/8),0):.3e}")
    rows = []
    for lam in np.linspace(0, 1, 11):
        s = 0.5 + lam * 0.5
        l0, l1, l2 = 2 * (lam - .5) * (lam - 1), -4 * lam * (lam - 1), 2 * lam * (lam - .5)
        xq = l0 * xa + l1 * xm + l2 * xb
        rho = pins(s) - (A[nLrows:] @ xq)
        xcorr = xq + sum(rho[k] * C[k] for k in range(NPIN))
        rows.append((s, min(mineig(blocks_of(xq, var)).values()), min(mineig(blocks_of(xcorr, var)).values()), np.abs(rho).max()))
    for r in rows:
        log(f"   quad s={r[0]:.3f}: mineig quad {r[1]:+.3e}, quad+corr {r[2]:+.3e}, |rho|_max {r[3]:.2e}")
    out["quad_1/2_3/4_1"] = [list(map(float, r)) for r in rows]
    np.savez(os.path.join(HERE, 'directions.npz'), **{f'C{k}': C[k] for k in range(NPIN)},
             **{f'x_{s_}': X[s_] for s_ in X})
    json.dump(out, open(os.path.join(HERE, "measure.json"), "w"), indent=1)
    log("wrote measure.json")


def d2s(fun, s):
    return float(mp.diff(fun, s, 2))


def minorant():
    """Node minorant margins against the margin the s-interpolation needs; contact curvature along s;
    the Bernstein middle control block of the quadratic variant; the bound on the third s-derivative of v."""
    A, var, lay = load_system(); nLrows = lay["nLrows"]
    D = np.load(os.path.join(HERE, "directions.npz"))
    C = [D[f"C{k}"] for k in range(NPIN)]
    X = {Fr(1, 2): D["x_1/2"], Fr(3, 4): D["x_3/4"], Fr(1): D["x_1"]}
    s5 = np.sqrt(5); c1 = (s5 - 1) / 4; c2 = -(s5 + 1) / 4
    ranges = {"hA": (-1, -0.99, [(-1.0, 0.002)]), "hB": (-1, 0.9999, [(0.0, 0.05)]),
              "hC": (-1, 0.9999, [(c1, 0.02), (c2, 0.02)])}
    tgrid = np.unique(np.concatenate([np.linspace(-1, 0.9999, 40001), -1 + np.logspace(-7, -2, 200)]))
    Hk = {nm: [hpoly(C[k], var, nm) for k in range(NPIN)] for nm in ranges}
    out = {}
    sg = np.linspace(0.25, 1.9, 34)
    v3 = np.array([np.abs(pins(s_, 3)) for s_ in sg]).max(axis=0)
    log("max |v_k^(3)| on [0.25,1.9]:", np.round(v3, 4))
    out["v3max"] = v3.tolist()
    for s_node, x in X.items():
        s = float(s_node)
        log(f"=== node s = {s_node}")
        v2 = pins(s, 2)
        for nm, (lo, hi, conts) in ranges.items():
            h_ = hpoly(x, var, nm)
            phi = (2 - 2 * tgrid) ** (-s / 2)
            f = phi - np.polyval(h_[::-1], tgrid)
            Lt = np.log(2 - 2 * tgrid)
            g2 = (Lt / 2) ** 2 * phi - sum(v2[k] * np.polyval(Hk[nm][k][::-1], tgrid) for k in range(NPIN))
            m = (tgrid >= lo) & (tgrid <= hi)
            for c, r in conts:
                m &= np.abs(tgrid - c) > r
            fm = f[m]; tm = tgrid[m]; g2m = np.abs(g2[m])
            hmax = np.sqrt(8 * np.maximum(fm, 0) / np.maximum(g2m, 1e-300))
            i = int(np.argmin(hmax))
            log(f"  {nm}: min f outside windows {fm.min():.3e} at t={tm[np.argmin(fm)]:.5f}; max|d2s g| {g2m.max():.3e}; "
                f"h_max(t) min = {hmax[i]:.4f} at t={tm[i]:.5f} (f={fm[i]:.2e}, |g2|={g2m[i]:.2e}); "
                f"max|H_k| on range: {[f'{np.abs(np.polyval(Hk[nm][k][::-1], tm)).max():.1e}' for k in range(NPIN)]}")
            tight = tm[fm < 1e-6]
            if len(tight):
                log(f"     tight (f < 1e-6) outside windows: t in [{tight.min():.4f}, {tight.max():.4f}] ({len(tight)} pts)")
            out[f"{s_node}_{nm}"] = dict(minf=float(fm.min()), hmax_min=float(hmax[i]), t_at=float(tm[i]))
            for c, r in conts:
                if c > -1:
                    d2 = s * (s + 2) * (2 - 2 * c) ** (-s / 2 - 2) - np.polyval(np.polyder(h_[::-1], 2), c)
                    g2tt = d2s(lambda z: z * (z + 2) * (2 - 2 * c) ** (-z / 2 - 2), s) \
                        - sum(v2[k] * np.polyval(np.polyder(Hk[nm][k][::-1], 2), c) for k in range(NPIN))
                    log(f"     contact t={c:+.4f}: f''(c) = {d2:.3e}; d2/ds2 f''(c) along the family = {g2tt:+.3e}"
                        f" => h_max(curv) = {np.sqrt(8 * d2 / abs(g2tt)):.4f}")
                else:
                    d1 = s * (2 - 2 * c) ** (-s / 2 - 1) - np.polyval(np.polyder(h_[::-1], 1), c)
                    g2t = d2s(lambda z: z * (2 - 2 * c) ** (-z / 2 - 1), s) \
                        - sum(v2[k] * np.polyval(np.polyder(Hk[nm][k][::-1], 1), c) for k in range(NPIN))
                    log(f"     contact t=-1: f'(-1) = {d1:.3e}; d2/ds2 f'(-1) along the family = {g2t:+.3e}"
                        f" => h_max = {np.sqrt(8 * d1 / abs(g2t)):.4f}")
    for (a, b) in ((Fr(1, 2), Fr(3, 4)), (Fr(3, 4), Fr(1))):
        xa, xb = X[a], X[b]; va = A[nLrows:] @ xa; vb = A[nLrows:] @ xb; h = float(b - a)
        rows = []
        for lam in np.linspace(0, 1, 9):
            s = float(a) + lam * h
            rho = pins(s) - ((1 - lam) * va + lam * vb)
            xc = (1 - lam) * xa + lam * xb + sum(rho[k] * C[k] for k in range(NPIN))
            rec = [s]
            for nm, (lo, hi, conts) in ranges.items():
                h_ = hpoly(xc, var, nm); phi = (2 - 2 * tgrid) ** (-s / 2)
                f = phi - np.polyval(h_[::-1], tgrid)
                m = (tgrid >= lo) & (tgrid <= hi)
                for c, r in conts:
                    m &= np.abs(tgrid - c) > r
                rec.append(float(f[m].min()))
                for c, r in conts:
                    if c > -1:
                        rec.append(float(s * (s + 2) * (2 - 2 * c) ** (-s / 2 - 2) - np.polyval(np.polyder(h_[::-1], 2), c)))
                    else:
                        rec.append(float(s * (2 - 2 * c) ** (-s / 2 - 1) - np.polyval(np.polyder(h_[::-1], 1), c)))
            rows.append(rec)
        log(f"piece [{a},{b}] corrected chord:  s | A: min f, f'(-1) | B: min f, f''(0) | C: min f, f''(c1), f''(c2)")
        for r in rows:
            log("   " + "  ".join(f"{v:+.3e}" for v in r))
        out[f"minorant_piece_{a}_{b}"] = rows
    xa, xm, xb = X[Fr(1, 2)], X[Fr(3, 4)], X[Fr(1)]
    P1 = blocks_of(2 * xm - (xa + xb) / 2, var)
    e1 = mineig(P1)
    log(f"quadratic Bernstein P_1 = 2 B_m - (B_a+B_b)/2: min eig {min(e1.values()):+.3e} ({min(e1, key=e1.get)}); "
        f"blocks with min eig < 0: {sum(v < 0 for v in e1.values())} of {len(e1)}")
    out["P1_mineig"] = e1
    json.dump(out, open(os.path.join(HERE, "minorant.json"), "w"), indent=1, default=float)
    log("wrote minorant.json")


def optimise():
    """Per-block piece width from the rigorous bound
        h^2/8 * [ lambda_max(B_w,blk) + (h/2) sum_k max|v_k'''| ||B_k,blk||_2 ] <= mu_blk,
    for (i) the plain min-Frobenius directions, (ii) block-reweighted directions (weights 1/mu_blk, iterated)."""
    A, var, lay = load_system(); nEq, nV, nLrows = lay["nEq"], lay["nV"], lay["nLrows"]
    D = np.load(os.path.join(HERE, "directions.npz"))
    X = {Fr(1, 2): D["x_1/2"], Fr(3, 4): D["x_3/4"], Fr(1): D["x_1"]}
    blocks = {s: blocks_of(x, var) for s, x in X.items()}
    bnames = list(blocks[Fr(1)].keys())
    bidx = {nm: [] for nm in bnames}; offd = {nm: [] for nm in bnames}
    for j, (kind, nm, a, b) in enumerate(var):
        if kind == "M":
            bidx[nm].append(j); offd[nm].append(a != b)
    sg = np.linspace(0.25, 1.9, 34)
    v3 = np.array([np.abs(pins(s_, 3)) for s_ in sg]).max(axis=0)
    WH = float(os.environ.get("WH", "1e-3"))

    def solve_dirs(blockw, rhs_list):
        w = np.full(nV, WH)
        bmin = min(blockw.values())
        for nm in bnames:
            w[bidx[nm]] = np.where(offd[nm], np.sqrt(2), 1.0) * blockw[nm] / bmin
        Winv2 = sp.diags(1.0 / w ** 2)
        G = (A @ Winv2 @ A.T).toarray()
        ev, Q = np.linalg.eigh(G); keep = ev > ev.max() * 1e-12
        Gp = (Q[:, keep] / ev[keep]) @ Q[:, keep].T
        outs = []
        for rhs in rhs_list:
            r = np.zeros(nEq); r[nLrows:] = rhs
            x = Winv2 @ (A.T @ (Gp @ r))
            res_ = np.abs(A @ x - r).max()
            if res_ > 1e-8:
                log(f"   (direction residual {res_:.1e})")
            outs.append(x)
        outs.append(res_)
        return outs

    def table(Cw, Ck, mu_blk, label):
        res = []
        for nm in bnames:
            Bw = blocks_of(Cw, var)[nm]
            lmax = max(float(np.linalg.eigvalsh(Bw)[-1]), 0.0)
            cub = sum(v3[k] * specnorm(blocks_of(Ck[k], var)[nm]) for k in range(NPIN))
            # solve h^2/8 (lmax + h/2 cub) = mu for h (monotone): bisection
            lo_, hi_ = 0.0, 10.0
            for _ in range(60):
                h = (lo_ + hi_) / 2
                if h * h / 8 * (lmax + h / 2 * cub) <= mu_blk[nm]:
                    lo_ = h
                else:
                    hi_ = h
            res.append((lo_, nm, lmax, cub, mu_blk[nm]))
        res.sort()
        log(f"{label}: piece width h_max = {res[0][0]:.4f}; binding blocks: " +
            "; ".join(f"{nm} h={h:.3f} (mu {mu:.1e}, lmax(B_w) {l:.1e}, cubic coef {c:.1e})" for h, nm, l, c, mu in res[:4]))
        return res[0][0]

    for (a, b) in ((Fr(1, 2), Fr(3, 4)), (Fr(3, 4), Fr(1))):
        sm = (float(a) + float(b)) / 2
        wv = pins(sm, 2)
        mu_blk = {nm: min(float(np.linalg.eigvalsh(blocks[s][nm])[0]) for s in (a, b)) for nm in bnames}
        log(f"=== piece around s_m = {sm} (nodes {a}, {b}); min_blk mu = {min(mu_blk.values()):.2e}")
        unit = {nm: 1.0 for nm in bnames}
        Ck = solve_dirs(unit, [np.eye(NPIN)[k] for k in range(NPIN)])[:NPIN]
        Cw = sum(wv[k] * Ck[k] for k in range(NPIN))
        h0 = table(Cw, Ck, mu_blk, "plain min-Frobenius")
        # reweighted: weight block by 1/sqrt(mu_blk) (penalise change where margin is small), then by the ratio
        bw = {nm: 1.0 / np.sqrt(mu_blk[nm]) for nm in bnames}
        for it in range(3):
            *Ck, res_ = solve_dirs(bw, [np.eye(NPIN)[k] for k in range(NPIN)])
            if res_ > 1e-5:
                log(f"reweighted it{it}: weighted system too ill-conditioned (residual {res_:.1e}); result INVALID, stop")
                break
            Cw = sum(wv[k] * Ck[k] for k in range(NPIN))
            h1 = table(Cw, Ck, mu_blk, f"reweighted it{it}")
            for nm in bnames:
                Bw = blocks_of(Cw, var)[nm]
                lm = max(float(np.linalg.eigvalsh(Bw)[-1]), 1e-12)
                bw[nm] *= np.sqrt(lm / mu_blk[nm] * 1e2 + 1.0)
        # a B_w with lambda_max <= 0 would make the h^2 term vanish: how negative can we make it cheaply?
        Bw = blocks_of(Cw, var)
        log("   spectrum of B_w per block (lmin, lmax) for the 5 worst: " + "; ".join(
            f"{nm} ({np.linalg.eigvalsh(Bw[nm])[0]:+.1e}, {np.linalg.eigvalsh(Bw[nm])[-1]:+.1e})"
            for nm in sorted(bnames, key=lambda n: -np.linalg.eigvalsh(Bw[n])[-1] / mu_blk[n])[:5]))


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build()
    elif sys.argv[1] == "measure":
        measure()
    elif sys.argv[1] == "minorant":
        minorant()
    elif sys.argv[1] == "optimise":
        optimise()
