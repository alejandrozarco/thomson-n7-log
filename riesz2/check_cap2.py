"""Exact checker for the EXACTLY SHARP typed three-point cap certificate, Riesz s = 2 (phi2(t) = 1/(2-2t)),
cell -1 <= t01 <= -99/100.

usage: python3 check_cap2.py cert_cap_riesz2_D12.json

Imports only the exact helpers of the independent cap checker ../checkers/check_cert.py (polynomial arithmetic,
lam_polys = PAPER.md section 6.3 lambda polynomials, required multipliers, congruence, LDL^T+DD PSD test) and
minorant2.py.  Checks, all in exact rational arithmetic (no floating point in any decision):
  1. multipliers g_r are exactly the ones required on the cap (lo = -1, hi = -99/100), SOS tag set exact;
  2. every kernel block F = N F' N^T and SOS block B = N B' N^T with F', B' PSD (L diag(d) L^T + DD remainder);
  3. the three identities lambda_T == sum_r g_r z^T B_r z  (T = A, B, Gamma), coefficient by coefficient;
  4. constraint (6);
  5. e == E(P) = 41/4 EXACTLY;
  6. exact contact values at P: H_A(-1) = 1/4, H_B(0) = 1/2, H_C(c1) = phi2(c1), H_C(c2) = phi2(c2) (in Q(sqrt5));
  7. exact minorants with prescribed touching (minorant2.py):
       phi2 - H_A = (t+1) q_A / (2-2t),          q_A > 0 on [-1, -99/100];
       phi2 - H_B = t^4 q_B / (2-2t),            q_B > 0 on [-1, 1];
       phi2 - H_C = (4t^2+2t-1)^2 q_C / (2-2t),  q_C > 0 on [-1, 1]      (c1, c2 = roots of 4t^2+2t-1).
Consequence (equality case, KLT style): on the cap, E(x) - E(P) = sum_{ij} (phi2 - H_cls)(t_ij) + sum_T lambda_T
+ Sigma_all >= 0, and E(x) = E(P) forces t01 = -1, every pole-ring t = 0 and every ring-ring t in {c1, c2}, i.e.
x = P up to rotation.  No local lemma / coercivity step is needed for the cap at s = 2.
"""
import json, os, sys, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "checkers"))
from check_cert import (P_add, P_mul, lam_polys, monos_upto, required_multipliers, congruence, psd_check, Fmat)
import minorant2


def ev(coefs, a, b):
    """evaluate polynomial at a + b sqrt5, result (x, y) = x + y sqrt5."""
    x, y = Fr(0), Fr(0); px, py = Fr(1), Fr(0)
    for cf in coefs:
        x += cf * px; y += cf * py
        px, py = px * a + 5 * py * b, px * b + py * a
    return x, y


def check(path, verbose=True):
    t0 = time.time()
    J = json.load(open(path))
    ok = True
    rep = {"cert": os.path.basename(path), "kernel": J["kernel"]}
    assert J["kernel"].startswith("riesz2")
    lo, hi = Fr(J["cell"][0]), Fr(J["cell"][1])
    assert (lo, hi) == (Fr(-1), Fr(-99, 100)), "not the cap cell"
    dA = tuple(J["dA"])
    c = {k: [Fr(x) for x in J["H"][k[1]]] for k in ("hA", "hB", "hC")}
    c["pBa"] = [Fr(x) for x in J["psi"]["Ba"]]; c["pCb"] = [Fr(x) for x in J["psi"]["Cb"]]
    for k in ("ca", "cb", "e"):
        c[k] = Fr(J[k])
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
    lam = lam_polys(c)
    cg_json = Fr(J["cg"])
    six = (5 * c["ca"] + 20 * c["cb"] + 10 * cg_json == c["e"] + 2 * lam["oneP"] + 5 * lam["oneR"]) and cg_json == lam["cg"]
    rep["constraint_6"] = six; ok &= six
    req = required_multipliers(lo, hi, dA)
    sos = J.get("SOS", {})
    if set(sos) != {"A", "B", "G"}:
        ok = False; rep["sos_tags"] = f"expected ['A', 'B', 'G'], found {sorted(sos)}"
    for tag in ("A", "B", "G"):
        rhs = {}
        blocks = sos.get(tag, [])
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
        ok &= (len(diff) == 0)
        if verbose:
            print(f"identity {tag}: {'EXACT' if not diff else 'FAIL'}  ({time.time() - t0:.0f}s)", flush=True)
    rep["psd"] = psd_ok
    rep["psd_min_dd_slack"] = min((v for v in psd_slack.values() if isinstance(v, float)), default=None)
    if not psd_ok:
        rep["psd_fail"] = {k: v for k, v in psd_slack.items() if not isinstance(v, float)}
    ok &= psd_ok
    # ---- e == E(P) exactly
    rep["e"] = str(c["e"]); rep["e_equals_EP_41_4"] = (c["e"] == Fr(41, 4)); ok &= rep["e_equals_EP_41_4"]
    # ---- exact values at P's inner products
    hA_m1 = sum(c["hA"][j] * (-1) ** j for j in range(len(c["hA"])))
    vals = dict(HA_m1=(hA_m1 == Fr(1, 4)), HB_0=(c["hB"][0] == Fr(1, 2)),
                HC_c1=(ev(c["hC"], Fr(-1, 4), Fr(1, 4)) == (Fr(1, 2), Fr(1, 10))),
                HC_c2=(ev(c["hC"], Fr(-1, 4), Fr(-1, 4)) == (Fr(1, 2), Fr(-1, 10))))
    rep["values_at_P_exact"] = vals; ok &= all(vals.values())
    rep["HB_taylor_0..4"] = [str(x) for x in c["hB"][:5]]
    # ---- exact minorants with touching
    mins = {}
    for nm, H, a, b, fac in (("A", c["hA"], lo, hi, "t+1"), ("B", c["hB"], Fr(-1), Fr(1), "t^4"),
                             ("C", c["hC"], Fr(-1), Fr(1), "(4t^2+2t-1)^2")):
        r, q = minorant2.check(H, a, b, fac)
        mins[nm] = r; ok &= r["OK"]
        if verbose:
            print(f"minorant {nm}: {'OK' if r['OK'] else 'FAIL'} {r}", flush=True)
    rep["minorant_exact"] = mins
    # ---- sanity (not needed for soundness): global identity on random configurations, Sigma_all from the
    # root form of Lemma 4.1 (../cells/check_cell.py), sum_T lambda_T + Sigma_all = sum H_cls(t_ij) - e
    sys.path.insert(0, os.path.join(HERE, "..", "checkers"))
    import check_cell as CK
    san = CK.sanity({"kind": "slab"}, c, {"A": lam["A"], "B": lam["B"], "G": lam["G"]})
    rep["sanity"] = san; ok &= san["identity_ok"] and san["Sigma_all_nonneg"]
    rep["ALL_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    rep = check(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "cert_cap_riesz2_D12.json"))
    print(json.dumps(rep, indent=1))
    sys.exit(0 if rep["ALL_OK"] else 1)
