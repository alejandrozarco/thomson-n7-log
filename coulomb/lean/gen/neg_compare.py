#!/usr/bin/env python3
"""Negative controls for compare_json / compare_json_n (Astra FIX a): dropping an emitted SOS block, dropping a
kernel block, or truncating a JSON SOS block must make the exact JSON comparison fail."""
import copy, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import emit_tcert as et
NUM = os.path.normpath(os.path.join(HERE, "..", ".."))
ok = True
# cap (TCertN)
J = json.load(open(os.path.join(NUM, "cap1", "cert_cap_coulomb_D12_short.json")))
tcn, _ = et.parse_n(os.path.join(et.LEANROOT, "CoulN7", "Cap"), "Cap"); tc = tcn.toTCert()
base = et.compare_json_n(tcn, tc, J); print("cap baseline", {k: v for k, v in base.items() if k != "ef"})
ok &= all(v for k, v in base.items() if k != "ef")
t2 = copy.copy(tcn); t2.SA = tcn.SA[:-1]
r = et.compare_json_n(t2, tc, J); print("cap, emitted SA block dropped -> SOS", r["SOS"]); ok &= not r["SOS"]
J2 = copy.deepcopy(J); J2["SOS"]["G"] = J2["SOS"]["G"][:-1]
r = et.compare_json_n(tcn, tc, J2); print("cap, JSON G block dropped -> SOS", r["SOS"]); ok &= not r["SOS"]
J3 = copy.deepcopy(J); J3["F"]["P"] = J3["F"]["P"][:-1]
r = et.compare_json_n(tcn, tc, J3); print("cap, JSON F_P block dropped -> F", r["F"]); ok &= not r["F"]
# slab (TCert)
Js = json.load(open(os.path.join(NUM, "cells1", "certs", "cert_slab_99_98_coulomb_D10.json")))
ts, _ = et.parse(os.path.join(et.LEANROOT, "CoulN7", "S9998"), "S9998")
base = et.compare_json(ts, Js); print("S9998 baseline", base); ok &= all(base.values())
Js2 = copy.deepcopy(Js); Js2["SOS"]["B"] = Js2["SOS"]["B"][:-1]
r = et.compare_json(ts, Js2); print("S9998, JSON B block dropped -> SOS", r["SOS"]); ok &= not r["SOS"]
print("NEG_COMPARE", "ALL_OK" if ok else "FAILED"); sys.exit(0 if ok else 1)
