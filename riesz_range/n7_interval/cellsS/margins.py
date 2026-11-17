"""Slab margins from mu-mode target scans (D10, ETA 1e-6): m(s) ~ zero crossing of the line through (T, mu(T)).
Also the linear-design width w_max = sqrt(8 (m/s) / |Ehat''(s)|) and a practical width using 60% of m.
Reads ../results.jsonl (older scan, float riesz_s) and results.jsonl (this directory)."""
import json, math
from fractions import Fraction as Fr
pts = {}
for fn in ("../results.jsonl", "results.jsonl"):
    for l in open(fn):
        d = json.loads(l)
        tag = d.get("tag", "")
        if not tag.startswith("slab") or "_D10_" not in tag or d.get("mu") is None or "_mu" not in tag:
            continue
        if d.get("gw", 0) not in (0, 0.0, None) or "pieceB" in tag:
            continue
        s = float(Fr(str(d["riesz_s"])))
        cell = "_".join(tag.split("_")[1:3])
        pts.setdefault((s, cell), {})[round(d["e_minus_EP"], 7)] = d["mu"]
EH = {0.5: 0.563, 0.75: 0.505, 1.0: 0.456, 1.5: 0.371}
print("s     cell            points (T: mu)                         margin m   m/s      w_max  w(60%)")
for (s, cell), P in sorted(pts.items()):
    T = sorted(P)
    if len(T) < 2:
        print(f"{s:<5} {cell:<15} {P}"); continue
    (t1, m1), (t2, m2) = (T[0], P[T[0]]), (T[-1], P[T[-1]])
    m = t1 + m1 * (t2 - t1) / (m1 - m2) if m1 != m2 else float("nan")
    eh = EH.get(s, 0.46)
    w = math.sqrt(8 * m / s / eh) if m > 0 else 0; w6 = math.sqrt(8 * 0.6 * m / s / eh) if m > 0 else 0
    print(f"{s:<5} {cell:<15} {', '.join(f'{t:.0e}: {P[t]:.2e}' for t in T):<38} {m:.2e}  {m/s:.2e}  {w:.3f}  {w6:.3f}")
