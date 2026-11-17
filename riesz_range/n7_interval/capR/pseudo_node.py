"""Pseudo-node: an exact cap certificate at s_b = s_a + eta, built from a node certificate at s_a by the affine family
(positive control for check_capR.py, no SDP solve needed).

    python3 pseudo_node.py NODE_a.json s_a s_b [KBITS]      -> cert_cap_s<p>_<q>_D12_pseudo.json

C_b := C_a + sum_k d_k C_k with d_k the dyadic (2^-KBITS) rounding of v_k(s_b) - Pin(C_a)_k.  By linearity C_b
satisfies the identities and the e-row exactly and has pins within 2^-KBITS of v(s_b).  Its blocks are
R_a + sum_k d_k R_k, positive definite as long as |d| ||R_k|| << mu_a (eta ~ 1e-6: |d| ~ 3e-7, ||R_k|| <= 0.26).
PSD data (L, d, exact diagonally dominant remainder) are produced as in ../capS/round_capS.py.  The minorant
property H_b <= phi_{s_b} is NOT guaranteed by construction; check_capR.py decides it (together with everything else)
for the piece [s_a, s_b].  Output format: that of round_capS.py (a node certificate), kernel label "riesz".
"""
import json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 60
T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


def sqrt5_powers(n=13):
    pw = [(Fr(1), Fr(0))]
    for _ in range(n):
        x, y = pw[-1]; pw.append((x * Fr(-1, 4) + 5 * y * Fr(1, 4), x * Fr(1, 4) + y * Fr(-1, 4)))
    return pw


PW = sqrt5_powers()


def pin_map(hA, hB, hC):
    return [hB[0], hB[1], sum(hA[j] * (-1) ** j for j in range(13)),
            sum(hC[j] * PW[j][0] for j in range(13)), sum(hC[j] * PW[j][1] for j in range(13)),
            sum(hC[j] * j * PW[j - 1][0] for j in range(1, 13)), sum(hC[j] * j * PW[j - 1][1] for j in range(1, 13))]


def vdata(s):
    s = mp.mpf(s.numerator) / s.denominator
    s5 = mp.sqrt(5); c1 = (s5 - 1) / 4; c2 = (-s5 - 1) / 4
    phi = lambda t: (2 - 2 * t) ** (-s / 2)
    dphi = lambda t: s * (2 - 2 * t) ** (-s / 2 - 1)
    return [phi(0), dphi(0), phi(-1), (phi(c1) + phi(c2)) / 2, (phi(c1) - phi(c2)) / (2 * s5),
            (dphi(c1) + dphi(c2)) / 2, (dphi(c1) - dphi(c2)) / (2 * s5)]


def ldl_nopiv(M):
    n = M.shape[0]
    L = np.eye(n); d = np.zeros(n); A = M.copy()
    for k in range(n):
        d[k] = A[k, k]
        L[k + 1:, k] = A[k + 1:, k] / d[k]
        A[k + 1:, k + 1:] -= np.outer(L[k + 1:, k], A[k, k + 1:])
    return L, d


def psd_data(M):
    """M: list of lists of Fractions (PD).  Returns (L, d) strings with exact DD remainder, as round_capS."""
    n = len(M)
    Mf = np.array([[float(x) for x in row] for row in M])
    ev = np.linalg.eigvalsh(Mf)
    eps = ev[0] / 2
    assert ev[0] > 0, f"block not PD: {ev[0]}"
    Lf, dfl = ldl_nopiv(Mf - eps * np.eye(n))
    L = [[Fr(int(round(Lf[i, j] * 2.0 ** 52)), 2 ** 52) if j < i else Fr(int(i == j)) for j in range(n)] for i in range(n)]
    dd = [max(Fr(0), Fr(int(round(dfl[i] * 2.0 ** 60)), 2 ** 60)) for i in range(n)]
    slack = None
    for i in range(n):
        row = [M[i][j] - sum(L[i][q] * dd[q] * L[j][q] for q in range(min(i, j) + 1)) for j in range(n)]
        sl = row[i] - sum(abs(row[j]) for j in range(n) if j != i)
        slack = sl if slack is None else min(slack, sl)
    assert slack > 0, f"DD remainder failed: {float(slack)}"
    return [[str(x) for x in row] for row in L], [str(x) for x in dd], float(slack)


def main(path_a, sa, sb, kbits=70):
    sa, sb = Fr(sa), Fr(sb)
    Ja = json.load(open(path_a))
    JD = json.load(open(os.path.join(HERE, "cert_dirs_D12.json")))
    dirs = JD["dirs"]; assert len(dirs) == 7
    hA = [Fr(x) for x in Ja["H"]["A"]]; hB = [Fr(x) for x in Ja["H"]["B"]]; hC = [Fr(x) for x in Ja["H"]["C"]]
    vt = pin_map(hA, hB, hC)
    vb = vdata(sb)
    d = [Fr(int(mp.nint((vb[k] - mp.mpf(vt[k].numerator) / vt[k].denominator) * mp.mpf(2) ** kbits)), 2 ** kbits) for k in range(7)]
    log("d_k =", [mp.nstr(mp.mpf(x.numerator) / x.denominator, 6) for x in d])

    def comb(get):
        """get(J) -> Fraction; returns get(J_a) + sum_k d_k get(dir_k)."""
        return get(Ja) + sum(d[k] * get(dirs[k]) for k in range(7))

    def comb_list(get, n):
        return [comb(lambda J: Fr(get(J)[i])) for i in range(n)]

    def comb_mat(get):
        Ra = get(Ja)
        if not Ra:
            return []
        n = len(Ra)
        return [[comb(lambda J: Fr(get(J)[i][j])) for j in range(n)] for i in range(n)]

    out = {"kernel": f"riesz  phi(t) = (2-2t)^(-s/2), s = {sb}", "s": str(sb), "cell": Ja["cell"], "D": Ja["D"],
           "sizes": Ja["sizes"], "dA": Ja["dA"], "pseudo_node_from": [os.path.basename(path_a), str(sa)],
           "H": {X: [str(x) for x in comb_list(lambda J, X=X: J["H"][X], 13)] for X in "ABC"},
           "psi": {X: [str(x) for x in comb_list(lambda J, X=X: J["psi"][X], 13)] for X in ("Ba", "Cb")},
           "ca": str(comb(lambda J: Fr(J["ca"]))), "cb": str(comb(lambda J: Fr(J["cb"]))), "e": str(comb(lambda J: Fr(J["e"])))}
    log("scalars and polynomials done")
    F = {}; oneP = None
    for X in "PR":
        F[X] = []
        for k, blk in enumerate(Ja["F"][X]):
            R = comb_mat(lambda J, X=X, k=k: J["F"][X][k]["red"])
            ent = {"m": blk["m"], "N": blk["N"], "red": [[str(x) for x in row] for row in R]}
            if R:
                L, dd, sl = psd_data(R); ent.update(L=L, d=dd)
            else:
                ent.update(L=[], d=[])
            F[X].append(ent)
            if X == "P" and k == 0:
                # oneP = s_P(1,1,1) = sum of the entries of F_P^(0) = N R N^T  (Q_k(1,1,1) = 0 for k >= 1)
                N = [[Fr(x) for x in row] for row in blk["N"]]
                oneP = sum(sum(N[p][a] * R[a][b] * N[q][b] for a in range(len(R)) for b in range(len(R))) for p in range(len(N)) for q in range(len(N)))
        log(f"F{X} blocks done")
    RR0 = comb_mat(lambda J: J["F"]["R"][0]["red"])
    N = [[Fr(x) for x in row] for row in Ja["F"]["R"][0]["N"]]
    oneR = sum(sum(N[p][a] * RR0[a][b] * N[q][b] for a in range(len(RR0)) for b in range(len(RR0))) for p in range(len(N)) for q in range(len(N)))
    out["cg"] = str((Fr(out["e"]) + 2 * oneP + 5 * oneR - 5 * Fr(out["ca"]) - 20 * Fr(out["cb"])) / 10)
    SOS = {}
    for tag in ("A", "B", "G"):
        SOS[tag] = []
        for r, blk in enumerate(Ja["SOS"][tag]):
            R = comb_mat(lambda J, tag=tag, r=r: J["SOS"][tag][r]["red"])
            ent = {"mult": blk["mult"], "g": blk["g"], "d": blk["d"], "N": blk["N"], "red": [[str(x) for x in row] for row in R]}
            if R:
                L, dd, sl = psd_data(R); ent.update(L=L, d_piv=dd)
            else:
                ent.update(L=[], d_piv=[])
            SOS[tag].append(ent)
        log(f"SOS {tag} blocks done")
    out["F"] = F; out["SOS"] = SOS
    path = os.path.join(HERE, f"cert_cap_s{sb.numerator}_{sb.denominator}_D12_pseudo.json")
    with open(path, "w") as fh:
        json.dump(out, fh)
    log("wrote", path, os.path.getsize(path) // 1024, "KiB")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 70)
