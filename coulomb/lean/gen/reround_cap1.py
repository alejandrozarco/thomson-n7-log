#!/usr/bin/env python3
"""[N = 7 Coulomb (s = 1) adaptation of numerics/hp/reround_cap2.py (= lean/gen_riesz2/reround_cap2.py)]
Re-round the (facially reduced, non-sharp: E(P) − e ≤ 1e−16) typed cap certificate cap1/cert_cap_coulomb_D12.json so that every
number is SHORT (dyadic up to small 2,3,5-smooth factors), keeping the format of cap1/round_cap1.py, so that the
ORIGINAL exact checkers accept it unchanged:
    numerics/n7_interval/cap1/check_cap1.py   and   numerics/n7_interval/cap1/check_coerc1.py

usage (nice -n 19, OMP_NUM_THREADS=1, from numerics/n7_interval):
  python3 lean/gen/reround_cap1.py cap1/cert_cap_coulomb_D12.json cap1/cert_cap_coulomb_D12_short.json \
      [--face cap1/face_D12_val.json] [--K 64] [--int-N]

Differences to the log template: exact helpers come from cap1/check_cap1.py (same API as hp/check_cert.py:
monos_upto, required_multipliers, lam_polys, congruence, P_add, P_mul); the pins are EXACTLY the quantities of the
input's "pins" dict (Coulomb: H_A(-1) = alpha0, H_B(0) = beta0, H_B'(0) = beta1, H_C(c1) = a0 + b0 sqrt5,
H_C'(c1) = x1 + y1 sqrt5; H_A'(-1) only if the input has "alpha1"), each asserted to hold for the input's H, plus
e = input e.  Nothing in the solve is kernel-specific otherwise (the kernel only enters through the pins).

Why the old certificates have ~1000-bit denominators: round_cap2/round_exact solve ONE exact square system
A_S x_S = b for a QR-chosen pivot set S (rank ~ 1300); the solution denominators divide det(A_S).

Here the solve is organised so that no large determinant ever appears:
  * N is already in echelon form (face.py: N[free,:] = I, and in each column the free row is the LAST
    non-zero row).  The monomial list monos_upto(d) is in lex order, a monomial order, so every SOS generator
        G = g_r * w_a * w_b  (w = N^T z, factor 2 for a != b)
    has lex-leading monomial LM(g_r) * z_free(a) * z_free(b) with leading coefficient +-1 or +-2.
  * For every monomial m of degree <= D one generator with LM = m is DESIGNATED (preferring the g = 1 block,
    diagonal entries, i.e. coefficient 1).  Reduction by designated generators in decreasing lex order
    (normal form NF_T) divides only by +-1, +-2.
  * Stage 1 (small system, LHS unknowns only): NF_T(lambda_T(x_lhs)) = NF_T(SOS_T(rounded)) on the monomials
    that are not designated, plus the pins (taken EXACTLY from the input certificate: H_B(0..3), H_A(-1)
    [and H_A'(-1) if pinned], H_C(c1), H_C'(c1) as x + y sqrt5, e).  Solved by Gauss-Jordan with GREEDY
    SMOOTH PIVOTS (entries whose numerator and denominator are 2,3,5-smooth, largest first); all other LHS
    unknowns stay at their 2^-K roundings.  Denominators of the solution then divide a smooth number.
  * Stage 2: the residual lambda_T(x_lhs) - SOS_T(rounded) is reduced by the designated generators; the
    reduction coefficients are added to the designated reduced-Gram entries.  The remainder must be exactly 0.
  * PSD certificates (L, d) of every reduced block as in round_cap2 (float LDL^T of M - eps I, L rounded to
    2^-52, d to 2^-60, exact DD check of the remainder), c_gamma from (6).
--int-N: scale every column k of N by the lcm c_k of its denominators (red_ab /= c_a c_b); N red N^T unchanged.
"""
import argparse
import json
import os
import sys
import time
from fractions import Fraction as Fr
from math import lcm

import numpy as np
from flint import fmpq, fmpq_mat

HERE = os.path.dirname(os.path.abspath(__file__))
CAP1 = os.path.normpath(os.path.join(HERE, "..", "..", "cap1"))      # numerics/n7_interval/cap1
sys.path.insert(0, CAP1)
import check_cap1 as CC   # noqa: E402  (exact helpers only: polynomials, lam_polys, multipliers, congruence)

T0 = time.time()


def log(*a):
    print(f"[{time.strftime('%H:%M:%S')} +{time.time() - T0:7.1f}s]", *a, flush=True)


def smooth_part(n):
    n = abs(n)
    for p in (2, 3, 5):
        while n and n % p == 0:
            n //= p
    return n


def is_smooth(q):
    return q != 0 and smooth_part(q.numerator) == 1 and smooth_part(q.denominator) == 1


def rnd(x, K):
    return Fr(round(x * (1 << K)), 1 << K)


def bits(q):
    q = Fr(q)
    return max(abs(q.numerator).bit_length(), q.denominator.bit_length())


def odd_bits(q):
    return smooth_part(Fr(q).denominator).bit_length()


def pscale(p, c):
    return {k: v * c for k, v in p.items()} if c else {}


# ====================================================================== load
def load(path):
    J = json.load(open(path))
    lo, hi = Fr(J["cell"][0]), Fr(J["cell"][1])
    req = CC.required_multipliers(lo, hi, tuple(J["dA"]))
    return J, lo, hi, req


def mat(M):
    return [[Fr(x) for x in row] for row in M]


def echelon_cols(N, Z):
    """w_k = sum_i N_ik z_i; check the echelon property, return (list of dict polys, free rows)."""
    k = len(N[0]) if N and N[0] else 0
    W, free = [], []
    for c in range(k):
        sup = [i for i in range(len(N)) if N[i][c] != 0]
        f = max(sup)
        if N[f][c] != 1 or any(N[f][cc] != 0 for cc in range(k) if cc != c):
            raise SystemExit("N is not in echelon form (free row = last non-zero row, unit)")
        W.append({Z[i]: N[i][c] for i in sup})
        free.append(f)
    return W, free


# ====================================================================== main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("out")
    ap.add_argument("--face", default=None)
    ap.add_argument("--K", type=int, default=64)
    ap.add_argument("--int-N", action="store_true")
    a = ap.parse_args()
    K = a.K
    J, lo, hi, req = load(a.cert)
    D = J["D"]
    MON = CC.monos_upto(D)
    DESC = sorted(MON, reverse=True)
    TAGS = ("A", "B", "G")
    log(f"{a.cert}: kernel {J['kernel']!r} D={D} K={K}")
    if a.face:                       # optional cross-check: the certificate's N are the face's N
        face = json.load(open(a.face))
        for X in "PR":
            for k, b in enumerate(J["F"][X]):
                assert mat(face[f"F{X}{k}"]["N"]) == mat(b["N"]), f"F{X}{k}: N differs from face"
        for T in TAGS:
            for r, b in enumerate(J["SOS"][T]):
                assert mat(face[f"{T}_B{r}"]["N"]) == mat(b["N"]), f"{T}{r}: N differs from face"
        log("N of every block equals the face file")
    # ---------------- exact input values
    H0 = {nm: [Fr(x) for x in J["H"][nm[1]]] for nm in ("hA", "hB", "hC")}
    H0["pBa"] = [Fr(x) for x in J["psi"]["Ba"]]
    H0["pCb"] = [Fr(x) for x in J["psi"]["Cb"]]
    C0 = {k: Fr(J[k]) for k in ("ca", "cb", "e")}
    nH = len(H0["hA"])
    # ---------------- LHS unknowns
    var = []            # ("h", nm, j) | ("c", nm) | ("F", X, k, a, b)
    x0 = []
    for nm in ("hA", "hB", "hC", "pBa", "pCb"):
        for j in range(nH):
            var.append(("h", nm, j)); x0.append(H0[nm][j])
    for nm in ("ca", "cb", "e"):
        var.append(("c", nm)); x0.append(C0[nm])
    Fblk = {}
    for X in "PR":
        for k, b in enumerate(J["F"][X]):
            N = mat(b["N"]); R = mat(b["red"]) if b["red"] else []
            Fblk[(X, k)] = (b["m"], N, R)
            for i in range(len(R)):
                for j in range(i, len(R)):
                    var.append(("F", X, k, i, j)); x0.append(R[i][j])
    nV = len(var)
    log(f"LHS unknowns: {nV}")
    # ---------------- lambda columns of the LHS unknowns (lam_polys is affine and 0 at 0)
    sizes = [Fblk[("P", k)][0] for k in range(len(J["F"]["P"]))]
    zeroF = {X: [[[Fr(0)] * m for _ in range(m)] for m in sizes] for X in "PR"}
    base = {nm: [Fr(0)] * nH for nm in ("hA", "hB", "hC", "pBa", "pCb")}
    base.update(ca=Fr(0), cb=Fr(0), e=Fr(0), FP=zeroF["P"], FR=zeroF["R"])
    cols = []
    for v in var:
        c = dict(base)
        if v[0] == "h":
            h = [Fr(0)] * nH; h[v[2]] = Fr(1); c[v[1]] = h
        elif v[0] == "c":
            c[v[1]] = Fr(1)
        else:
            _, X, k, i, j = v
            m, N, R = Fblk[(X, k)]
            Fk = [[N[p][i] * N[q][j] + (N[p][j] * N[q][i] if i != j else 0) for q in range(m)] for p in range(m)]
            Fs = list(zeroF[X]); Fs[k] = Fk
            c["F" + X] = Fs
        lam = CC.lam_polys(c)
        cols.append({T: lam[T] for T in TAGS})
    log("lambda columns done")
    # ---------------- SOS generators, designation
    blocks = {}          # T -> list of dict(g, W, free, Z, red)
    desig = {}           # T -> {m: (r, a, b, lc, poly)}
    for T in TAGS:
        bl = []
        cand = {}
        for r, b in enumerate(J["SOS"][T]):
            g = {tuple(int(x) for x in kk.split(",")): Fr(v) for kk, v in b["g"].items()}
            greq, dreq = req[T][r]
            assert g == greq and b["d"] == dreq, f"multiplier {T}{r} is not the required one"
            Z = CC.monos_upto(b["d"])
            N = mat(b["N"])
            R = mat(b["red"]) if b["red"] else []
            W, free = echelon_cols(N, Z) if R else ([], [])
            lmg = max(g)
            for i in range(len(W)):
                for j in range(i, len(W)):
                    fi, fj = Z[free[i]], Z[free[j]]
                    m = tuple(lmg[t] + fi[t] + fj[t] for t in range(3))
                    lc = g[lmg] * (1 if i == j else 2)
                    key = (r != 0, abs(lc), r, i, j)          # prefer g = 1, then coefficient 1
                    if m not in cand or key < cand[m][0]:
                        cand[m] = (key, (r, i, j, lc))
            bl.append(dict(g=g, W=W, free=free, Z=Z, red=R, N=N))
        blocks[T] = bl
        dz = {}
        for m, (key, (r, i, j, lc)) in cand.items():
            assert lc in (1, -1, 2, -2), (T, m, lc)
            gpol = CC.P_mul(bl[r]["g"], CC.P_mul(bl[r]["W"][i], bl[r]["W"][j]))
            if i != j:
                gpol = pscale(gpol, 2)
            assert max(gpol) == m and gpol[m] == lc
            dz[m] = (r, i, j, lc, gpol)
        desig[T] = dz
        log(f"{T}: {len(dz)} designated leading monomials, {len(MON) - len(dz)} free monomials")

    def NF(T, p, record=None):
        p = dict(p)
        dz = desig[T]
        for m in DESC:
            v = p.get(m)
            if not v or m not in dz:
                continue
            r, i, j, lc, gpol = dz[m]
            cf = v / lc
            for mm, w in gpol.items():
                y = p.get(mm, 0) - cf * w
                if y:
                    p[mm] = y
                else:
                    p.pop(mm, None)
            if record is not None:
                record[(T, r, i, j)] = record.get((T, r, i, j), 0) + cf
        return p

    # ---------------- rounding
    xr = [rnd(v, K) for v in x0]
    for T in TAGS:
        for bdat in blocks[T]:
            bdat["red"] = [[rnd(x, K) for x in row] for row in bdat["red"]]
            R = bdat["red"]
            for i in range(len(R)):          # keep symmetric
                for j in range(i):
                    R[i][j] = R[j][i]

    def sos_poly(T):
        tot = {}
        for bdat in blocks[T]:
            if not bdat["red"]:
                continue
            B = CC.congruence(bdat["N"], bdat["red"])
            Z = bdat["Z"]
            zz = {}
            for i in range(len(Z)):
                for j in range(len(Z)):
                    if B[i][j]:
                        e = (Z[i][0] + Z[j][0], Z[i][1] + Z[j][1], Z[i][2] + Z[j][2])
                        zz[e] = zz.get(e, 0) + B[i][j]
            tot = CC.P_add(tot, CC.P_mul(bdat["g"], zz))
        return tot

    # ---------------- stage 1 rows
    rows, rhs, rname = [], [], []
    for T in TAGS:
        nfs = sos_poly(T)
        nfs = NF(T, nfs)
        colnf = [NF(T, cols[j][T]) for j in range(nV)]
        free_m = [m for m in MON if m not in desig[T]]
        for m in free_m:
            row = {j: colnf[j][m] for j in range(nV) if colnf[j].get(m)}
            rows.append(row); rhs.append(nfs.get(m, Fr(0))); rname.append(f"NF_{T}{m}")
        log(f"stage-1 rows for {T}: {len(free_m)}")
    hidx = {(v[1], v[2]): j for j, v in enumerate(var) if v[0] == "h"}
    cidx = {v[1]: j for j, v in enumerate(var) if v[0] == "c"}
    # pins: exactly the quantities of the input's "pins" dict (round_cap1.py), values taken from the input's H
    # and asserted equal to the recorded pin values.
    JP = {k: Fr(v) for k, v in J["pins"].items()}
    known = {"alpha0", "alpha1", "a0", "b0", "x1", "y1"} | {f"beta{jj}" for jj in range(nH)}
    assert set(JP) <= known, f"unknown pins {set(JP) - known}"
    pins = []
    for jj in range(nH):
        if f"beta{jj}" in JP:
            assert H0["hB"][jj] == JP[f"beta{jj}"], f"beta{jj}"
            pins.append(({hidx[("hB", jj)]: Fr(1)}, H0["hB"][jj], f"hB[{jj}]"))
    vA = sum(H0["hA"][jj] * (-1) ** jj for jj in range(nH))
    assert vA == JP["alpha0"], "alpha0"
    pins.append(({hidx[("hA", jj)]: Fr((-1) ** jj) for jj in range(nH)}, vA, "hA(-1)"))
    dA_m1 = sum(jj * H0["hA"][jj] * (-1) ** (jj - 1) for jj in range(1, nH))
    if "alpha1" in JP:
        assert dA_m1 == JP["alpha1"], "alpha1"
        pins.append(({hidx[("hA", jj)]: Fr(jj * (-1) ** (jj - 1)) for jj in range(1, nH)}, dA_m1, "hA'(-1)"))
    pw = [(Fr(1), Fr(0))]                     # powers of c1 = -1/4 + 1/4 sqrt5 as x + y sqrt5
    for _ in range(nH):
        x, y = pw[-1]
        pw.append((x * Fr(-1, 4) + 5 * y * Fr(1, 4), x * Fr(1, 4) + y * Fr(-1, 4)))
    hC = H0["hC"]
    vx = sum(hC[jj] * pw[jj][0] for jj in range(nH)); vy = sum(hC[jj] * pw[jj][1] for jj in range(nH))
    dx = sum(jj * hC[jj] * pw[jj - 1][0] for jj in range(1, nH)); dy = sum(jj * hC[jj] * pw[jj - 1][1] for jj in range(1, nH))
    assert (vx, vy) == (JP["a0"], JP["b0"]), "a0, b0"
    pins.append(({hidx[("hC", jj)]: pw[jj][0] for jj in range(nH)}, vx, "hC(c1).x"))
    pins.append(({hidx[("hC", jj)]: pw[jj][1] for jj in range(nH)}, vy, "hC(c1).y"))
    if "x1" in JP:
        assert (dx, dy) == (JP["x1"], JP["y1"]), "x1, y1"
        pins.append(({hidx[("hC", jj)]: jj * pw[jj - 1][0] for jj in range(1, nH)}, dx, "hC'(c1).x"))
        pins.append(({hidx[("hC", jj)]: jj * pw[jj - 1][1] for jj in range(1, nH)}, dy, "hC'(c1).y"))
    pins.append(({cidx["e"]: Fr(1)}, C0["e"], "e"))
    log("pins (exact, from the input):", {nm: str(v) for _, v, nm in pins})
    for dct, val, nm in pins:
        rows.append({j: cf for j, cf in dct.items() if cf}); rhs.append(val); rname.append("pin " + nm)
    # move the fixed (non-pivot) values to the right-hand side later: solve for deltas
    # residual of rows at the rounded point:
    res = []
    for row, b in zip(rows, rhs):
        res.append(b - sum(cf * xr[j] for j, cf in row.items()))
    # ---------------- stage 1: Gauss-Jordan with greedy smooth pivots on  A dx = res
    A = [dict(r) for r in rows]
    bvec = list(res)
    nR = len(A)
    used_rows, piv = set(), {}          # row -> col
    nonsmooth = []
    while True:
        best = None
        for i in range(nR):
            if i in used_rows:
                continue
            for j, v in A[i].items():
                if not v or j in piv.values():
                    continue
                sm = is_smooth(v)
                p2 = sm and smooth_part(v.numerator * 1) == 1 and (v.denominator & (v.denominator - 1) == 0) \
                    and (abs(v.numerator) & (abs(v.numerator) - 1) == 0)
                key = (sm, p2, float(abs(v)))
                if best is None or key > best[0]:
                    best = (key, i, j)
        if best is None:
            break
        (sm, p2, _), i, j = best
        if not sm:
            nonsmooth.append((rname[i], var[j], str(A[i][j])))
        pv = A[i][j]
        rowi = {jj: vv / pv for jj, vv in A[i].items()}
        bi = bvec[i] / pv
        A[i] = rowi; bvec[i] = bi
        for k in range(nR):
            if k != i and A[k].get(j):
                f = A[k][j]
                rk = A[k]
                for jj, vv in rowi.items():
                    y = rk.get(jj, 0) - f * vv
                    if y:
                        rk[jj] = y
                    else:
                        rk.pop(jj, None)
                bvec[k] -= f * bi
        used_rows.add(i); piv[i] = j
    incons = [rname[i] for i in range(nR) if i not in used_rows and bvec[i] != 0]
    log(f"stage 1: {len(piv)} pivots of {nR} rows; non-smooth pivots: {len(nonsmooth)}; "
        f"inconsistent dependent rows: {len(incons)}")
    if nonsmooth:
        log("  non-smooth pivots:", nonsmooth[:20])
    if incons:
        raise SystemExit(f"inconsistent rows {incons[:20]}")
    x = list(xr)
    for i, j in piv.items():
        # row i: dx_j + sum_{non-pivot jj} A dx_jj = b, non-pivot dx = 0
        x[j] = xr[j] + bvec[i]
    dmax = max((abs(float(x[j] - x0[j])) for j in range(nV)), default=0)
    log(f"stage 1 solved; max |x - x_input| over LHS unknowns {dmax:.3g}; "
        f"max bits {max(bits(v) for v in x)}; pivot vars: {sorted(set(var[j][1] if var[j][0] != 'F' else 'F' for j in piv.values()))}")
    # verify stage-1 rows exactly
    for row, b, nm in zip(rows, rhs, rname):
        assert sum(cf * x[j] for j, cf in row.items()) == b, nm
    # ---------------- stage 2
    lhs = {nm: [Fr(0)] * nH for nm in ("hA", "hB", "hC", "pBa", "pCb")}
    cv = {}
    Fr_ = {X: [None] * len(sizes) for X in "PR"}
    redF = {key: [[Fr(0)] * len(R) for _ in range(len(R))] for key, (m, N, R) in Fblk.items()}
    for j, v in enumerate(var):
        if v[0] == "h":
            lhs[v[1]][v[2]] = x[j]
        elif v[0] == "c":
            cv[v[1]] = x[j]
        else:
            _, X, k, i, jj = v
            redF[(X, k)][i][jj] = x[j]; redF[(X, k)][jj][i] = x[j]
    for (X, k), (m, N, R) in Fblk.items():
        Fr_[X][k] = CC.congruence(N, redF[(X, k)]) if R else [[Fr(0)] * m for _ in range(m)]
    cfull = dict(hA=lhs["hA"], hB=lhs["hB"], hC=lhs["hC"], pBa=lhs["pBa"], pCb=lhs["pCb"],
                 ca=cv["ca"], cb=cv["cb"], e=cv["e"], FP=Fr_["P"], FR=Fr_["R"])
    lam = CC.lam_polys(cfull)
    for T in TAGS:
        rec = {}
        rem = NF(T, CC.P_add(lam[T], sos_poly(T), -1), rec)
        if rem:
            raise SystemExit(f"stage 2 {T}: non-zero remainder on {len(rem)} monomials")
        for (_, r, i, j), cf in rec.items():
            # residual = sum cf * G  where G = g w_i w_j (x2 off-diagonal)  ->  red_ij += cf (sym)
            R = blocks[T][r]["red"]
            R[i][j] += cf
            if i != j:
                R[j][i] += cf
        # exact re-check
        diff = CC.P_add(lam[T], sos_poly(T), -1)
        assert not diff, T
        log(f"stage 2 {T}: identity exact, {len(rec)} designated entries corrected")
    # ---------------- optional integer N
    def int_scale(N, R):
        k = len(N[0]) if N and N[0] else 0
        cs = []
        for c in range(k):
            L = 1
            for i in range(len(N)):
                L = lcm(L, N[i][c].denominator)
            cs.append(L)
        N2 = [[N[i][c] * cs[c] for c in range(k)] for i in range(len(N))]
        R2 = [[R[i][j] / (cs[i] * cs[j]) for j in range(len(R))] for i in range(len(R))]
        return N2, R2
    # ---------------- PSD certificates
    def psd_cert(R, nm):
        n = len(R)
        Mf = np.array([[float(v) for v in row] for row in R])
        ev = np.linalg.eigvalsh(Mf)
        eps = ev[0] / 2
        A_ = Mf - eps * np.eye(n)
        Lf = np.eye(n); dfl = np.zeros(n)
        for k in range(n):
            dfl[k] = A_[k, k]
            Lf[k + 1:, k] = A_[k + 1:, k] / dfl[k]
            A_[k + 1:, k + 1:] -= np.outer(Lf[k + 1:, k], A_[k, k + 1:])
        L = [[Fr(int(round(Lf[i, j] * 2.0 ** 52)), 2 ** 52) if j < i else Fr(int(i == j)) for j in range(n)]
             for i in range(n)]
        dd = [max(Fr(0), Fr(int(round(dfl[i] * 2.0 ** 60)), 2 ** 60)) for i in range(n)]
        q = lambda v: fmpq(v.numerator, v.denominator)
        Mq = fmpq_mat(n, n, [q(v) for row in R for v in row])
        Lq = fmpq_mat(n, n, [q(v) for row in L for v in row])
        Dq = fmpq_mat(n, n, [q(dd[i]) if i == j else fmpq(0) for i in range(n) for j in range(n)])
        Dl = Mq - Lq * Dq * Lq.transpose()
        slack = min(Dl[i, i] - sum((abs(Dl[i, j]) for j in range(n) if j != i), fmpq(0)) for i in range(n))
        if slack < 0:
            raise SystemExit(f"PSD certificate failed for {nm}: min eig {ev[0]}")
        return L, dd, float(ev[0])
    minev = {}
    Fout = {}
    for X in "PR":
        Fout[X] = []
        for k, b in enumerate(J["F"][X]):
            m, N, R = Fblk[(X, k)]
            ent = {"m": m}
            if R:
                Rn = redF[(X, k)]
                Nn = N
                if a.int_N:
                    Nn, Rn = int_scale(N, Rn)
                L, dd, ev0 = psd_cert(Rn, f"F{X}{k}"); minev[f"F{X}{k}"] = ev0
                ent.update(N=[[str(v) for v in row] for row in Nn], red=[[str(v) for v in row] for row in Rn],
                           L=[[str(v) for v in row] for row in L], d=[str(v) for v in dd])
            else:
                ent.update(N=b["N"], red=[], L=[], d=[])
            Fout[X].append(ent)
    SOS = {}
    for T in TAGS:
        SOS[T] = []
        for r, b in enumerate(J["SOS"][T]):
            bdat = blocks[T][r]
            ent = {"mult": b["mult"], "g": b["g"], "d": b["d"]}
            if bdat["red"]:
                Nn, Rn = bdat["N"], bdat["red"]
                if a.int_N:
                    Nn, Rn = int_scale(Nn, Rn)
                L, dd, ev0 = psd_cert(Rn, f"{T}{r}"); minev[f"{T}{r}"] = ev0
                ent.update(N=[[str(v) for v in row] for row in Nn], red=[[str(v) for v in row] for row in Rn],
                           L=[[str(v) for v in row] for row in L], d_piv=[str(v) for v in dd])
            else:
                ent.update(N=b["N"], red=[], L=[], d_piv=[])
            SOS[T].append(ent)
    log("PSD certificates OK; smallest eigenvalues:",
        {k: f"{v:.2e}" for k, v in sorted(minev.items(), key=lambda kv: kv[1])[:5]})
    cert = dict(J)
    cert.update(H={"A": [str(v) for v in lhs["hA"]], "B": [str(v) for v in lhs["hB"]], "C": [str(v) for v in lhs["hC"]]},
                psi={"Ba": [str(v) for v in lhs["pBa"]], "Cb": [str(v) for v in lhs["pCb"]]},
                ca=str(cv["ca"]), cb=str(cv["cb"]), cg=str(lam["cg"]), e=str(cv["e"]), F=Fout, SOS=SOS)
    cert["rerounded_from"] = os.path.basename(a.cert)
    cert["reround"] = {"K": K, "int_N": a.int_N, "script": "numerics/n7_interval/lean/gen/reround_cap1.py"}
    with open(a.out, "w") as fh:
        json.dump(cert, fh)
    log(f"wrote {a.out} ({os.path.getsize(a.out) // 1024} KiB)")
    # ---------------- size table
    def groups(C):
        g = {}
        def put(name, vals):
            vals = [Fr(v) for v in vals]
            if not vals:
                return
            o = g.setdefault(name, [0, 0, 0])
            o[0] = max(o[0], max(bits(v) for v in vals)); o[1] = max(o[1], max(odd_bits(v) for v in vals)); o[2] += len(vals)
        for X in "ABC":
            put("H_" + X, C["H"][X])
        put("psi_Ba", C["psi"]["Ba"]); put("psi_Cb", C["psi"]["Cb"])
        for k in ("ca", "cb", "e", "cg"):
            put(k, [C[k]])
        put("pins", list(C["pins"].values()))
        for X in "PR":
            for b in C["F"][X]:
                put("F red", [v for row in b["red"] for v in row]); put("F N", [v for row in b["N"] for v in row])
                put("F L,d", [v for row in b["L"] for v in row] + list(b["d"]))
        for T in TAGS:
            for b in C["SOS"][T]:
                put(f"SOS {T} red", [v for row in b["red"] for v in row]); put("SOS N", [v for row in b["N"] for v in row])
                put("SOS L,d", [v for row in b["L"] for v in row] + list(b["d_piv"]))
        return g
    gb, ga = groups(J), groups(cert)
    log("size table: group | max bits before | max odd-den bits before | max bits after | max odd-den bits after | #")
    for k in gb:
        log(f"  {k:12s} {gb[k][0]:6d} {gb[k][1]:6d}   {ga[k][0]:6d} {ga[k][1]:6d}   {gb[k][2]}")
    for X in "ABC":
        old = [Fr(v) for v in J["H"][X]]; new = [Fr(v) for v in cert["H"][X]]
        log(f"  H_{X} coefficient bits before {[bits(v) for v in old]}")
        log(f"  H_{X} coefficient bits after  {[bits(v) for v in new]}")
        log(f"  H_{X} changed coefficients {[j for j in range(len(old)) if old[j] != new[j]]}, "
            f"max |change| {max(abs(float(new[j] - old[j])) for j in range(len(old))):.3g}")


if __name__ == "__main__":
    main()
