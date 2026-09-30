"""Exact checker for the non-cap cells (Case 1 and the Case-2 slabs), RIESZ s = 2 kernel phi2(t) = 1/(2-2t).

usage: python3 check_cell2.py cert_*.json [...]

Same checks as ../checkers/check_cell.py (whose exact helpers it imports: multipliers, Bareiss PD test, identities,
random-configuration sanity test of the global identities), with the s = 2 specifics:
  * e - E(P) > 0 decided EXACTLY in rationals: E(P) = 41/4 (= 1/4 + 10*1/2 + 5*(phi2(c1) + phi2(c2)),
    phi2(c1) + phi2(c2) = (5+sqrt5)/10 + (5-sqrt5)/10 = 1);
  * the minorant H <= phi2 on the whole range ([a,1) for Case 1; H_A on [lo,hi], H_B, H_C on [lo,1)) decided
    EXACTLY by minorant2.py (p = 1 - (2-2t)H has no root in the closed range and is positive at its left end).
No floating point is involved in any decision.
"""
import json, os, sys, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "checkers"))
import check_cell as CK
import minorant2

EP2 = Fr(41, 4)


def EP2_from_pairs():
    """E(P) recomputed in Q(sqrt5) from the Gram multiset of P: -1 (x1), 0 (x10), c1 (x5), c2 (x5)."""
    # phi2(c) = 1/(2-2c); c1 = (-1+sqrt5)/4 -> 2-2c1 = (5-sqrt5)/2 -> phi2 = (5+sqrt5)/10 ; c2 conjugate
    x1, y1 = Fr(1, 2), Fr(1, 10)       # phi2(c1) = 1/2 + sqrt5/10
    x2, y2 = Fr(1, 2), Fr(-1, 10)      # phi2(c2) = 1/2 - sqrt5/10
    tot_x = Fr(1, 4) + 10 * Fr(1, 2) + 5 * x1 + 5 * x2
    tot_y = 5 * y1 + 5 * y2
    assert tot_y == 0
    # double-check phi2(c1): (2 - 2 c1) * phi2(c1) == 1 in Q(sqrt5)
    a, b = Fr(2) - 2 * Fr(-1, 4), -2 * Fr(1, 4)          # 2 - 2 c1 = a + b sqrt5
    assert (a * x1 + 5 * b * y1, a * y1 + b * x1) == (1, 0)
    return tot_x


def check(path, verbose=True, do_sanity=True, minorant=True):
    t0 = time.time()
    J = json.load(open(path))
    assert J["kernel"] == "riesz2", "not a Riesz s=2 certificate"
    rep = {"cert": os.path.basename(path), "kind": J["kind"], "kernel": J["kernel"], "cell": J["cell"], "D": J["D"]}
    ok = True
    D = J["D"]
    c = CK.load_exact(J)
    if J["kind"] == "case1":
        ok &= Fr(J["cell"]["a"]) < 0
    else:
        lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
        ok &= (-1 < lo < hi < 0)
    for H in ([c["H"]] if J["kind"] == "case1" else [c["hA"], c["hB"], c["hC"], c["pBa"], c["pCb"]]):
        ok &= len(H) == D + 1
    Fl = c["F"] if J["kind"] == "case1" else c["FP"] + c["FR"]
    sizes_expected = ([D // 2 + 1 - k for k in range(D // 2 - 1)] if J["kind"] == "case1"
                      else 2 * list(range(D // 2 + 1, 0, -1)))
    ok &= [len(F) for F in Fl] == sizes_expected
    pd_fail = []
    for k, F in enumerate(Fl):
        good, why = CK.bareiss_pd(F)
        if not good:
            pd_fail.append((f"F{k}", why))
    L = CK.lhs_polys(J, c)
    if J["kind"] == "slab":
        cg = Fr(J["cg"])
        six = (cg == L["cg"]) and (5 * c["ca"] + 20 * c["cb"] + 10 * cg == c["e"] + 2 * L["oneP"] + 5 * L["oneR"])
        rep["constraint_6"] = six; ok &= six
    req = CK.required(J)
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
            Z = CK.monos_upto(blk["d"])
            B = CK.Fmat(blk["B"])
            if len(B) != len(Z):
                ok = False; rep[f"size_{tag}{r}"] = "wrong size"; continue
            good, why = CK.bareiss_pd(B)
            if not good:
                pd_fail.append((f"{tag}{r}", why))
            rhs = CK.P_add(rhs, CK.P_mul(g, CK.gram_poly(B, Z)))
        diff = CK.P_add(L[tag], rhs, -1)
        rep[f"identity_{tag}"] = "EXACT" if not diff else f"FAIL (max coeff diff {float(max(abs(v) for v in diff.values()))})"
        ok &= not diff
        if verbose:
            print(f"  {rep['cert']}: identity {tag} {'EXACT' if not diff else 'FAIL'} ({time.time() - t0:.0f}s)", flush=True)
    rep["all_blocks_positive_definite"] = not pd_fail
    if pd_fail:
        rep["pd_fail"] = pd_fail
    ok &= not pd_fail
    # ---- margin, exact
    assert EP2_from_pairs() == EP2
    e = c["e"]
    rep["e"] = str(e)
    rep["e_minus_EP"] = str(e - EP2)
    rep["e_minus_EP_float"] = float(e - EP2)
    rep["e_gt_EP"] = e > EP2
    ok &= rep["e_gt_EP"]
    # ---- minorants, exact
    if minorant:
        items = ([("H", c["H"], Fr(J["cell"]["a"]), Fr(1))] if J["kind"] == "case1" else
                 [("H_A", c["hA"], lo, hi), ("H_B", c["hB"], lo, Fr(1)), ("H_C", c["hC"], lo, Fr(1))])
        mrep = {}
        for nm, H, a, b in items:
            r, _ = minorant2.check(H, a, b, "none")
            mrep[nm] = r
            ok &= r["OK"]
        rep["minorant_exact"] = mrep
        rep["MINORANT_OK"] = all(r["OK"] for r in mrep.values())
    if do_sanity:
        rep["sanity"] = CK.sanity(J, c, L)
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
    print("CHECK_CELL2", "ALL_OK" if allok else "FAILED")
    sys.exit(0 if allok else 1)
