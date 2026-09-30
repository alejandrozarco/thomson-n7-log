"""Run all exact s = 2 checks and print the coverage table (markdown) used in STATUS.md.
usage: python3 make_coverage2.py > logs/coverage2.md
"""
import json, os, sys, hashlib
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_cell2, check_cap2

CELLS = json.load(open(os.path.join(HERE, "cells2.json")))   # [{"name", "cert", "range"}]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()[:12]


rows, allok = [], True
cap = os.path.join(HERE, "cert_cap_riesz2_D12.json")
if os.path.exists(cap):
    r = check_cap2.check(cap, verbose=False)
    m = r["minorant_exact"]
    rows.append(("cap (Case 2)", "t01 in [-1, -99/100]", 12, "0 (exactly sharp: e = 41/4)",
                 "ALL_OK" if r["ALL_OK"] else "FAIL",
                 "exact: " + ", ".join(f"{k}: {v['factor']}*q, q>0" + ("" if v["OK"] else " FAIL") for k, v in m.items()),
                 os.path.basename(cap), sha(cap)))
    allok &= r["ALL_OK"]
else:
    rows.append(("cap (Case 2)", "t01 in [-1, -99/100]", 12, "-", "MISSING", "-", "-", "-")); allok = False
for c in CELLS:
    p = os.path.join(HERE, c["cert"])
    if not os.path.exists(p):
        rows.append((c["name"], c["range"], "-", "-", "MISSING", "-", c["cert"], "-")); allok = False
        continue
    r = check_cell2.check(p, verbose=False)
    allok &= r["ALL_OK"]
    rows.append((c["name"], c["range"], r["D"], f"{r['e_minus_EP']} (= {r['e_minus_EP_float']:.3g})",
                 "ALL_OK" if r["ALL_OK"] else "FAIL",
                 "exact: no root of 1-(2-2t)H in the closed range" if r.get("MINORANT_OK") else "FAIL",
                 c["cert"], sha(p)))
# tiling
Js = [json.load(open(os.path.join(HERE, c["cert"]))) for c in CELLS if os.path.exists(os.path.join(HERE, c["cert"]))]
slabs = sorted((Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])) for J in Js if J["kind"] == "slab")
case1 = [Fr(J["cell"]["a"]) for J in Js if J["kind"] == "case1"]
chain = [(Fr(-1), Fr(-99, 100))] + slabs
tiling = (case1 == [Fr(-9, 10)] and chain[-1][1] == Fr(-9, 10)
          and all(chain[k][1] == chain[k + 1][0] for k in range(len(chain) - 1)))
allok &= tiling
print("| cell | range | D | e - E(P) (exact) | exact checker | minorant (exact) | certificate (sha256/12) |")
print("|---|---|---|---|---|---|---|")
for r in rows:
    print("| " + " | ".join(str(x) for x in r[:6]) + f" | `{r[6]}` ({r[7]}) |")
print()
print("Tiling: " + " -> ".join(f"[{a}, {b}]" for a, b in chain) + f"; Case 1: all t_ij >= -9/10 -- {'OK' if tiling else 'FAIL'}")
print()
print(f"**Overall: {'ALL CELLS OK' if allok else 'INCOMPLETE / FAIL'}**")
