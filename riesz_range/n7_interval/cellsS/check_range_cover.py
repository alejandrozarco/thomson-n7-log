"""Mechanical coverage check for the cells part of the [1/2, 3/2] argument (work package C; not reviewed).

usage: python3 check_range_cover.py [--recheck] [--pieces range_pieces.jsonl] [--a 1/2 --b 3/2]

Reads the piece records (range_driver.py -> range_pieces.jsonl) and, for every record with PIECE_OK:
  - both certificate files exist and their sha256 equals the one recorded when the piece was checked;
  - both certificates are of the target cell (kind and exact cell bounds) and D agree, and their kernels are
    riesz:a and riesz:b with a < b exactly the piece's endpoints (and the report's s_range);
  - with --recheck: check_piece.check(cert_a, cert_b) is run again from the certificate files (exact node checks
    of identities / PD / e > E_s(P), and the ball-arithmetic (H) and (E) interpolation checks) and must be PIECE_OK.
Then, per cell (Case 1 with cut -9/10 and the six slabs), the union of the accepted closed s-intervals must cover
[a, b] = [1/2, 3/2] exactly (rational endpoints, sweep).
Tiling at every s (RANGE_ASSEMBLY.md C2): B = all piece endpoints of all cells plus a, b; on each elementary
interval J between consecutive points of B, the accepted pieces containing J must include a Case 1 piece whose node
certificates have cut exactly -9/10, and slab pieces whose [lo, hi], read from the node certificates' `cell` fields
(not from file names or record labels), cover t01 in [-99/100, -9/10] with exact rational endpoints (chain from
-99/100; overlapping extra slabs are harmless).  Prints CELLS_RANGE_OK, or the gaps / problems.
(The cap {t01 < -99/100} is not part of this check; it is work package E.)
Provenance (REVIEW_range_fable.md S1): if a record's report carries `provenance` (check_piece.py since 2026-11-07),
the sha256 it records for check_piece.py, check_cell.py, check_minorant_cell.py, ../hp/check_cert.py and for both
certificates must equal the current files'; reports without provenance are counted and listed as NOHASH.
"""
import argparse, hashlib, json, os, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
CELLS = {"case1": ("case1", {"a": Fr(-9, 10)})}
for n, lo, hi in (("99_98", "-99/100", "-49/50"), ("98_96", "-49/50", "-24/25"), ("96_94", "-24/25", "-47/50"),
                  ("94_93", "-47/50", "-93/100"), ("93_915", "-93/100", "-183/200"), ("915_90", "-183/200", "-9/10")):
    CELLS["slab_" + n] = ("slab", {"lo": Fr(lo), "hi": Fr(hi)})


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


CHECKER_FILES = [os.path.join(HERE, f) for f in ("check_piece.py", "check_cell.py", "check_minorant_cell.py")] + \
    [os.path.join(HERE, "..", "..", "hp", "check_cert.py")]


def prov_problems(prov, paths):
    """S1: sha256 of checker sources and inputs recorded in the report vs the current files."""
    bad = []
    rec = {prov.get("checker"): prov.get("checker_sha256")}
    for d in prov.get("deps") or []:
        rec[d.get("name")] = d.get("sha256")
    for f in CHECKER_FILES:
        nm = os.path.basename(f)
        if rec.get(nm) != sha(f):
            bad.append(f"checker {nm} sha256 differs from the one recorded in the report")
    recin = {(d.get("name"), d.get("sha256")) for d in prov.get("inputs") or []}
    for p in paths:
        if (os.path.basename(p), sha(p)) not in recin:
            bad.append(f"input {os.path.basename(p)} sha256 not recorded in the report's provenance")
    return bad


def riesz(J):
    k = J["kernel"]
    assert k.startswith("riesz:"), k
    return Fr(k.split(":", 1)[1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--recheck", action="store_true")
    ap.add_argument("--pieces", default=os.path.join(HERE, "range_pieces.jsonl"))
    ap.add_argument("--a", default="1/2"); ap.add_argument("--b", default="3/2")
    o = ap.parse_args()
    A, B = Fr(o.a), Fr(o.b)
    problems = []
    acc = {c: [] for c in CELLS}
    recs = [json.loads(l) for l in open(o.pieces)]
    if o.recheck:
        import check_piece
    seen = set()
    nohash = []
    tiles = []      # (a, b, kind, cell bounds from the node certificate)
    for r in recs:
        if not r.get("PIECE_OK"):
            continue
        cell = r["cell"]
        key = (cell, r["a"], r["b"], tuple(r["certs"]))
        if key in seen:
            continue
        seen.add(key)
        if cell not in CELLS:
            problems.append(f"unknown cell {cell}"); continue
        kind, bounds = CELLS[cell]
        a, b = Fr(r["a"]), Fr(r["b"])
        paths = [os.path.join(HERE, p) for p in r["certs"]]
        bad = []
        for p, h in zip(paths, r["sha"]):
            if not os.path.exists(p):
                bad.append(f"missing {p}")
            elif sha(p) != h:
                bad.append(f"sha256 changed: {p}")
        if not bad:
            Ja, Jb = (json.load(open(p)) for p in paths)
            for J in (Ja, Jb):
                if J["kind"] != kind or {k: Fr(v) for k, v in J["cell"].items()} != bounds:
                    bad.append(f"cert cell {J['kind']} {J['cell']} is not {cell}")
            if Ja["D"] != Jb["D"]:
                bad.append("D differs")
            if not (riesz(Ja) == a and riesz(Jb) == b and a < b):
                bad.append(f"kernels {Ja['kernel']}, {Jb['kernel']} do not match [{a}, {b}]")
            rep = r.get("report") or {}
            if [Fr(x) for x in rep.get("s_range", [])] != [a, b] or not rep.get("PIECE_OK"):
                bad.append("report does not match the record")
            if isinstance(rep.get("provenance"), dict):
                bad += prov_problems(rep["provenance"], paths)
            else:
                nohash.append(f"{cell} [{a}, {b}]")
            if not bad and o.recheck:
                rr = check_piece.check(paths[0], paths[1])
                print(f"recheck {cell} [{a}, {b}]: PIECE_OK={rr['PIECE_OK']} ({rr['time_s']} s)", flush=True)
                if not rr["PIECE_OK"]:
                    bad.append("recheck failed")
        if bad:
            problems.append(f"{cell} [{a}, {b}]: " + "; ".join(bad)); continue
        acc[cell].append((a, b))
        cb = {k: Fr(v) for k, v in Ja["cell"].items()}
        tiles.append((a, b, Ja["kind"], cb))
    gaps = {}
    for cell, iv in acc.items():
        cur, g = A, []
        for a, b in sorted(iv):
            if a > cur:
                g.append((cur, min(a, B)))
            cur = max(cur, b)
            if cur >= B:
                break
        if cur < B:
            g.append((cur, B))
        g = [(x, y) for x, y in g if x < y and y > A and x < B]
        if g:
            gaps[cell] = g
        print(f"{cell:16s} {len(iv):3d} OK pieces  " + ("covers [%s, %s]" % (A, B) if not g else
              "GAPS " + ", ".join(f"[{x}, {y}]" for x, y in g)))
    # tiling at every s, from the certificates' cell fields
    Bset = sorted({A, B} | {x for a, b, _, _ in tiles for x in (a, b) if A <= x <= B})
    tgaps = []
    for x, y in zip(Bset, Bset[1:]):
        inJ = [(k, c) for a, b, k, c in tiles if a <= x and y <= b]
        c1 = any(k == "case1" and c == {"a": Fr(-9, 10)} for k, c in inJ)
        sl = sorted((c["lo"], c["hi"]) for k, c in inJ if k == "slab")
        cur = Fr(-99, 100)
        for lo, hi in sl:
            if lo <= cur < hi:
                cur = hi
        if not c1 or cur < Fr(-9, 10):
            tgaps.append(f"s in [{x}, {y}]: " + ("" if c1 else "no Case 1 (cut -9/10); ")
                         + ("" if cur >= Fr(-9, 10) else f"slabs cover t01 only up to {cur}"))
    print(f"tiling: {len(Bset) - 1} elementary s-intervals, " + ("all tiled: Case 1 (cut -9/10) + slabs chaining "
          "-99/100 -> -9/10" if not tgaps else f"{len(tgaps)} not tiled"))
    for g in tgaps:
        problems.append("tiling " + g)
    if nohash:
        print(f"NOHASH {len(nohash)} accepted record(s) whose report has no provenance (sha256 of checker / inputs): "
              + ", ".join(nohash[:4]) + (" ..." if len(nohash) > 4 else ""))
    for p in problems:
        print("PROBLEM", p)
    if not gaps and not problems:
        print(f"CELLS_RANGE_OK  s in [{A}, {B}] x {{Case 1, six slabs tiling t01 in [-99/100, -9/10]}}"
              + ("  (pieces re-checked)" if o.recheck else "  (records + sha256; run --recheck to re-verify)"))
        return 0
    print("CELLS_RANGE_INCOMPLETE")
    return 1


if __name__ == "__main__":
    sys.exit(main())
