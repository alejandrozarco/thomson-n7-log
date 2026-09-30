"""Tamper controls for the s = 2 checkers: every tampered certificate must be rejected.
usage: python3 controls2.py            -> CONTROLS_OK / CONTROLS_FAIL
"""
import copy, json, os, sys, tempfile
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_cap2, check_cell2

res = []
def run(name, J, checker, expect):
    fd, p = tempfile.mkstemp(suffix=".json"); os.close(fd)
    json.dump(J, open(p, "w"))
    try:
        ok = checker(p)["ALL_OK"]
    except Exception as ex:
        ok = False
    os.remove(p)
    res.append((name, ok == expect)); print(name, "accepted" if ok else "rejected", "OK" if ok == expect else "UNEXPECTED", flush=True)

cap = json.load(open(os.path.join(HERE, "cert_cap_riesz2_D12.json")))
cc = lambda p: check_cap2.check(p, verbose=False)
T = copy.deepcopy(cap); T["e"] = str(Fr(T["e"]) + Fr(1, 10 ** 30)); run("cap: e + 1e-30", T, cc, False)
T = copy.deepcopy(cap); T["H"]["B"][4] = str(Fr(T["H"]["B"][4]) + Fr(1, 10 ** 20)); run("cap: H_B t^4 coeff perturbed", T, cc, False)
T = copy.deepcopy(cap); T["H"]["A"][0] = str(Fr(T["H"]["A"][0]) + Fr(1, 10 ** 6)); T["H"]["A"][1] = str(Fr(T["H"]["A"][1]) + Fr(1, 10 ** 6)); run("cap: H_A raised by 1e-6 (t+1)", T, cc, False)
T = copy.deepcopy(cap); T["SOS"]["G"] = T["SOS"]["G"][:-1]; run("cap: last Gamma block removed", T, cc, False)
T = copy.deepcopy(cap); T["SOS"] = {}; run("cap: SOS empty", T, cc, False)
cells = [os.path.join(HERE, c["cert"]) for c in json.load(open(os.path.join(HERE, "cells2.json")))]
cells = [p for p in cells if os.path.exists(p)]
ck = lambda p: check_cell2.check(p, verbose=False, do_sanity=False)
if cells:
    J = json.load(open(cells[0]))
    T = copy.deepcopy(J); T["SOS"] = {}; run(f"{os.path.basename(cells[0])}: SOS empty", T, ck, False)
    T = copy.deepcopy(J); T["e"] = str(Fr(T["e"]) + Fr(1, 10 ** 30)); run(f"{os.path.basename(cells[0])}: e + 1e-30", T, ck, False)
    T = copy.deepcopy(J)
    H = T["H"] if J["kind"] == "case1" else T["H"]["B"]
    H[0] = str(Fr(H[0]) + 1); run(f"{os.path.basename(cells[0])}: H raised by 1", T, ck, False)
run("cap untampered", cap, cc, True)
print("CONTROLS_OK" if all(ok for _, ok in res) else "CONTROLS_FAIL")
