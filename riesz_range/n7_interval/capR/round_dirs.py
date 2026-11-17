"""Exact pin-response directions C_1..C_7 of the N = 7 cap certificate (DESIGN.md section 2).

    python3 round_dirs.py            -> cert_dirs_D12.json

Each direction C_k is a rational vector in the certificate layout of ../capS/round_capS.py (reduced kernel blocks F',
H_A, H_B, H_C, psi_Ba, psi_Cb, c_alpha, c_beta, e, reduced SOS blocks B') with
    L C_k = 0      (the three identities coefficientwise, and the e-row  e = H_A(-1) + 10 H_B(0) + 10 Re H_C(c1)),
    Pin C_k = e_k  (the 7 contact pins: H_B(0), H_B'(0), H_A(-1), Re H_C(c1), Im H_C(c1), Re H_C'(c1), Im H_C'(c1),
                    Re/Im with respect to Q(sqrt5), c1 = (-1 + sqrt5)/4).
No positivity is required of a direction.  Procedure (as round_capS.py): float directions from affine_cap.py
(directions.npz, weighted min-norm), rounded to 2^-80; a well conditioned set of pivot unknowns (float pivoted QR of
the exact system) is then solved exactly over Q (flint) so that every row holds exactly; all rows are re-verified
exactly.  The output stores every block as N R N^T with the face matrices N copied from face_D12_val.json, so the
piece checker can verify L C_k = 0 and Pin C_k = e_k on its own.
Mac: run through ../heavy_lock.py (dense 1373 x 39454 QR, ~0.6 GB; exact solve ~3-5 min).
"""
import os, sys, json, time
os.environ.setdefault("POLYD", "12")
import numpy as np
import scipy.linalg as sla
import scipy.sparse as sp
from fractions import Fraction as Fr
from flint import fmpq, fmpq_mat

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import affine_cap as AC
from affine_cap import spec, CC, NPIN, PIN_NAMES

KROUND = 80
T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


def exact_columns(face, var, nL, blk):
    """exact sparse columns {row: Fraction} of [L; Pin], rows: 3*455 identities, e-row, 7 pins."""
    nV = len(var)
    rows_mon = spec.monos_upto(spec.D); ridx = {e: i for i, e in enumerate(rows_mon)}; NR = len(rows_mon)
    TAGS = ("A", "B", "G")
    rowof = lambda tag, e: TAGS.index(tag) * NR + ridx[e]
    cols = [dict() for _ in range(nV)]
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
                cols[j][rowof(tag, e)] = v
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
                    cols[j] = {rowof(tag, e): f * v for e, v in pol.items()}
                    j += 1
    hidx = {(var[j][1], var[j][2]): j for j in range(nL) if var[j][0] == "h"}
    cidx = {var[j][1]: j for j in range(nL) if var[j][0] == "c"}
    pw = AC.sqrt5_powers()
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
        if v != 0:
            cols[j][rE] = v
    for p, d in enumerate(pins):
        for j, v in d.items():
            if v != 0:
                cols[j][rE + 1 + p] = v
    return cols, rE + 1 + NPIN, rE + 1


def main():
    face = AC.load_face()
    var, nL, blk = AC.layout(face)
    nV = len(var)
    cols, nEq, nLrows = exact_columns(face, var, nL, blk)
    log(f"exact columns: {nV} unknowns, {nEq} rows")
    Dn = np.load(os.path.join(HERE, "directions.npz"))
    XF = np.stack([Dn[f"C{k}"] for k in range(NPIN)], axis=1)        # nV x 7 float directions
    I, J, V = [], [], []
    for j, cd in enumerate(cols):
        for i, cf in cd.items():
            I.append(i); J.append(j); V.append(float(cf))
    Af = sp.csr_matrix((V, (I, J)), shape=(nEq, nV))
    RHS = np.zeros((nEq, NPIN))
    for k in range(NPIN):
        RHS[nLrows + k, k] = 1.0
    log("float residuals of the directions:", np.abs(Af @ XF - RHS).max(axis=0))
    # ---- row basis and pivot columns (float, verified exactly afterwards)
    AAt = (Af @ Af.T).toarray()
    w_, Q_ = np.linalg.eigh(AAt)
    rank = int((w_ > w_.max() * 1e-13).sum())
    Rr, pivr = sla.qr(Af.T.toarray(), mode="r", pivoting=True)
    rowbasis = sorted(pivr[:rank].tolist())
    log(f"row basis: rank {rank} of {nEq}; |R_ii| min {np.abs(np.diag(Rr))[:rank].min():.3g}")
    del Rr
    Asub = Af[rowbasis, :].toarray()
    Rq, piv = sla.qr(Asub, mode="r", pivoting=True)
    S = sorted(piv[:rank].tolist()); del Rq, Asub
    # the pin rows must be in the row basis (otherwise the right-hand sides e_k are not representable)
    for k in range(NPIN):
        assert nLrows + k in rowbasis, f"pin row {k} not in the row basis"
    # ---- round, exact solve for the pivot unknowns with 7 right-hand sides
    xq = [[Fr(int(round(XF[j, k] * 2.0 ** KROUND)), 2 ** KROUND) for k in range(NPIN)] for j in range(nV)]
    pos = {i: p for p, i in enumerate(rowbasis)}
    Sset = set(S); Spos = {j: p for p, j in enumerate(S)}
    Q = lambda q: fmpq(int(q.numerator), int(q.denominator))
    rhs = fmpq_mat(rank, NPIN)
    for k in range(NPIN):
        i = nLrows + k
        rhs[pos[i], k] = fmpq(1)
    for j in range(nV):
        if j in Sset:
            continue
        for i, cf in cols[j].items():
            if i in pos:
                qcf = Q(cf)
                for k in range(NPIN):
                    if xq[j][k] != 0:
                        rhs[pos[i], k] -= qcf * Q(xq[j][k])
    AS = fmpq_mat(rank, rank)
    for j in S:
        for i, cf in cols[j].items():
            if i in pos:
                AS[pos[i], Spos[j]] = Q(cf)
    log(f"exact solve {rank} x {rank} with {NPIN} right-hand sides")
    xs = AS.solve(rhs)
    log("solved")
    xe = [[Q(xq[j][k]) for k in range(NPIN)] for j in range(nV)]
    dmax = 0.0
    for j in S:
        for k in range(NPIN):
            val = xs[Spos[j], k]
            dmax = max(dmax, abs(float(Fr(int(val.p), int(val.q))) - XF[j, k]))
            xe[j][k] = val
    log(f"max pivot change vs float: {dmax:.3g}")
    # ---- verify ALL rows exactly, for every direction
    res = [[fmpq(0)] * NPIN for _ in range(nEq)]
    for j, cd in enumerate(cols):
        for i, cf in cd.items():
            qcf = Q(cf)
            for k in range(NPIN):
                if xe[j][k] != 0:
                    res[i][k] += qcf * xe[j][k]
    bad = []
    for i in range(nEq):
        for k in range(NPIN):
            want = fmpq(1) if i == nLrows + k else fmpq(0)
            if res[i][k] != want:
                bad.append((i, k))
    log(f"exact row check: {len(bad)} violations")
    if bad:
        raise SystemExit(f"inconsistent rows: {bad[:20]}")
    # ---- write
    mults = spec.multipliers()
    dirs = []
    for k in range(NPIN):
        hv = {nm: [None] * 13 for nm in ("hA", "hB", "hC", "pBa", "pCb")}
        cv = {}
        blocks = {}
        for j, (kind, nm, a, b) in enumerate(var):
            if kind == "h":
                hv[nm][a] = str(xe[j][k])
            elif kind == "c":
                cv[nm] = str(xe[j][k])
            else:
                blocks.setdefault(nm, {})[(a, b)] = xe[j][k]
        def red(nm):
            if nm not in blocks:
                return []
            ent = blocks[nm]; n = max(a for a, b in ent) + 1
            M = [[None] * n for _ in range(n)]
            for (a, b), v in ent.items():
                M[a][b] = str(v); M[b][a] = str(v)
            return M
        Fout = {}
        for X in "PR":
            Fout[X] = []
            for kk, m in enumerate(spec.SIZES):
                nm = f"F{X}{kk}"; n, N = face[nm]
                Fout[X].append({"m": m, "N": [[str(x) for x in row] for row in N], "red": red(nm)})
        SOS = {}
        for tag in ("A", "B", "G"):
            SOS[tag] = []
            for r, (gname, g, d) in enumerate(mults[tag]):
                nm = f"{tag}_B{r}"; n, N = face[nm]
                SOS[tag].append({"mult": gname, "g": {f"{a},{b},{c}": str(v) for (a, b, c), v in g.items()}, "d": d,
                                 "N": [[str(x) for x in row] for row in N], "red": red(nm)})
        dirs.append({"pin": k, "pin_name": PIN_NAMES[k], "H": {"A": hv["hA"], "B": hv["hB"], "C": hv["hC"]},
                     "psi": {"Ba": hv["pBa"], "Cb": hv["pCb"]}, "ca": cv["ca"], "cb": cv["cb"], "e": cv["e"],
                     "F": Fout, "SOS": SOS})
    out = {"kind": "cap pin-response directions", "cell": ["-1", "-99/100"], "D": spec.D, "sizes": list(spec.SIZES),
           "dA": list(spec.DA), "pins": list(PIN_NAMES),
           "erow": "e = H_A(-1) + 10 H_B(0) + 10 Re H_C(c1)", "dirs": dirs}
    path = os.path.join(HERE, "cert_dirs_D12.json")
    with open(path, "w") as fh:
        json.dump(out, fh)
    log("wrote", path, os.path.getsize(path) // 1024, "KiB")


if __name__ == "__main__":
    main()
