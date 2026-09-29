"""Exact rounding of a float interior solution (sdp_cell.py, mode mu) to a rational certificate.

usage: python3 round_cell.py sol/<tag>.npz OUT.json [KBITS]

Peyrl-Parrilo style, simpler than the cap (no face, no pins, strictly positive margin):
  1. round every LHS unknown (H's, psi's, c_alpha, c_beta, e, kernel blocks F) and every SOS Gram block to
     dyadics 2^-KBITS (default 64); e is rounded DOWN;
  2. build the exact LHS polynomial(s) (check_cell.case1_slack / check_cert.lam_polys) and the exact residual
     r = LHS - sum_r g_r z^T B_r z  (degree <= D);
  3. absorb r into the unconstrained block (g = 1, z = all monomials of degree <= D/2): for every monomial m,
     B_0[i,j] += r_m / #{(i,j): z_i z_j = m} over all those ordered pairs (the orthogonal projection);
  4. verify exactly: identities, and every block positive definite (Bareiss), then write the certificate.
"""
import json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
from numpy.polynomial import chebyshev as C
import mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkers"))
import check_cell as CK
from check_cell import P_add, P_mul, monos_upto

T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:6.1f}s]", *a, flush=True)


def dy(x, K, down=False):
    s = mp.mpf(float(x)) * mp.mpf(2) ** K
    return Fr(int(mp.floor(s) if down else mp.nint(s)), 2 ** K)


def dymat(M, K):
    M = (np.asarray(M) + np.asarray(M).T) / 2
    n = M.shape[0]
    return [[dy(M[i, j], K) for j in range(n)] for i in range(n)]


def cheb_to_mono(c, D):
    m = C.cheb2poly(np.asarray(c, float))
    return np.concatenate([m, np.zeros(D + 1 - len(m))])


def main(solfile, out, K=64):
    sol = np.load(solfile)
    meta = json.loads(str(sol["meta"]))
    D = meta["D"]; kind = meta["kind"]
    kernel = "log" if meta["ker"] == 0 else "coulomb"
    log(f"{solfile}: {kind} D={D} kernel={kernel} mu={float(sol['mu'][0]) if 'mu' in sol else None}")
    J = {"kind": kind, "kernel": kernel, "D": D}
    if kind == "case1":
        a = Fr(meta["cell"].split(":")[1]).limit_denominator(1000)
        J["cell"] = {"a": str(a)}
        K1 = len(meta["sizes"])
        J["H"] = [str(dy(x, K)) for x in cheb_to_mono(sol["h"], D)]
        J["e"] = str(dy(sol["e"][0], K, down=True))
        J["F"] = [[[str(x) for x in row] for row in dymat(sol[f"F{k}"], K)] for k in range(K1)]
        tags = ["S"]
    else:
        lo = Fr(str(meta["lo"])).limit_denominator(1000); hi = Fr(str(meta["hi"])).limit_denominator(1000)
        J["cell"] = {"lo": str(lo), "hi": str(hi)}
        J["H"] = {X: [str(dy(x, K)) for x in cheb_to_mono(sol["h" + X], D)] for X in "ABC"}
        J["psi"] = {nm: [str(dy(x, K)) for x in cheb_to_mono(sol["p" + nm], D)] for nm in ("Ba", "Cb")}
        J["ca"] = str(dy(sol["ca"][0], K)); J["cb"] = str(dy(sol["cb"][0], K))
        J["e"] = str(dy(sol["e"][0], K, down=True))
        J["F"] = {X: [[[str(x) for x in row] for row in dymat(sol[f"F{X}{k}"], K)] for k in range(len(meta["sizes"]))]
                  for X in "PR"}
        tags = ["A", "B", "G"]
    c = CK.load_exact(J)
    L = CK.lhs_polys(J, c)
    if kind == "slab":
        J["cg"] = str(L["cg"])
    log("exact LHS built")
    req = CK.required(J)
    J["SOS"] = {}
    for tag in tags:
        blocks = []
        rhs = {}
        Bq = []
        for r, (g, d) in enumerate(req[tag]):
            B = dymat(sol[f"{tag}_B{r}"], K)
            Bq.append(B)
            rhs = P_add(rhs, P_mul(g, CK.gram_poly(B, monos_upto(d))))
        res = P_add(L[tag], rhs, -1)
        rmax = max((abs(float(v)) for v in res.values()), default=0.0)
        # absorb into block 0 (g = 1)
        g0, d0 = req[tag][0]
        assert g0 == CK.ONE
        Z = monos_upto(d0)
        pairs = {}
        for i, zi in enumerate(Z):
            for j, zj in enumerate(Z):
                pairs.setdefault((zi[0] + zj[0], zi[1] + zj[1], zi[2] + zj[2]), []).append((i, j))
        B0 = Bq[0]
        for m, v in res.items():
            pl = pairs[m]
            w = v / len(pl)
            for (i, j) in pl:
                B0[i][j] += w
        ev = np.linalg.eigvalsh(np.array([[float(x) for x in row] for row in B0]))
        log(f"identity {tag}: rounding residual max |coef| {rmax:.3g} absorbed; min eig of B0 now {ev[0]:.3g}")
        for r, (g, d) in enumerate(req[tag]):
            blocks.append({"mult_index": r, "g": {f"{k[0]},{k[1]},{k[2]}": str(v) for k, v in g.items()}, "d": d,
                           "B": [[str(x) for x in row] for row in Bq[r]]})
        J["SOS"][tag] = blocks
    J["generated_from"] = os.path.basename(solfile)
    with open(out, "w") as fh:
        json.dump(J, fh)
    log(f"wrote {out} ({os.path.getsize(out) // 1024} KiB); checking ...")
    rep = CK.check(out, verbose=True, do_sanity=False)
    log(json.dumps({k: rep[k] for k in rep if k not in ("e",)}))
    return rep


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 64)
