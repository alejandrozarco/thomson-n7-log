"""Queue driver for the cells part of the s-range extension beyond [1/2, 3/2] (../EXTENSION_sizing.md, section 2.2).
AI-written, not reviewed.  Same steps and checkers as range_driver.py (which is imported and left unchanged):
mu-mode node solve (sdp_cellS.py, GW = largest adjacent piece width), exact rounding (round_cell.py), check_cell.py
with sanity, then check_piece.py on adjacent node pairs.  Every heavy step goes through ./hjob.sh (../heavy_lock.py,
slot from .heavy_slot).

usage: EXT_RANGE=3/2,5/3 python3 range_driver_ext.py      (only nodes / pieces inside [lo, hi]; default 1/3,7/4)
       python3 range_driver_ext.py --table                (only rewrite RANGE_TABLE_ext.md)
Stop after the current job: touch STOP_RANGE_EXT.

Grids (per cell, contiguous segments; the existing [1/2, 3/2] end nodes are reused: slab nodes at 1/2 (GW 1/16) and
3/2 (GW 1/12) from range_nodes.jsonl, Case 1 nodes at 1/2 and 3/2 (certs_lin/, w = 1/8)):
  slabs 96_94, 94_93, 93_915 (the three middle slabs): 1/48 on [1/3, 5/12], 1/24 on [5/12, 1/2];
  slabs 99_98, 98_96, 915_90: 1/24 on [1/3, 1/2];
  all six slabs and Case 1: 1/12 on [3/2, 7/4];  Case 1 on [1/3, 1/2]: 1/3, 5/12, 1/2.
Records: new nodes -> range_nodes_ext.jsonl (range_nodes.jsonl is only read); pieces are appended to
range_pieces.jsonl (the file range_check.py and check_range_cover.py read; existing lines are never rewritten);
state (breakpoints after refinement) -> range_state_ext.json; table -> RANGE_TABLE_ext.md.
TARGET (e - E_s(P) - s EM_w in plain units): 1e-5 for s < 1/2 (sizing 2.2), 2e-5 for s > 3/2 (as on [1/2, 3/2]).
Refinement as in range_driver.py: a failed node halves its adjacent maximal gaps, a failed piece gets its midpoint.
"""
import json, os, sys, time
from fractions import Fraction as Fr

import range_driver as R          # chdir to cellsS/, helpers (hjob, jline, sha, jl, append, log, check_cell_node)
import fcntl

_slot_orig = R.slot


def _b_free():
    """True if nobody holds ../.mac_heavy_B.lock right now (non-blocking probe, released at once)."""
    with open(os.path.join(R.HERE, "..", ".mac_heavy_B.lock"), "a") as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return False
        fcntl.flock(f, fcntl.LOCK_UN)
        return True


def _slot_ext():
    """slot from .heavy_slot (range_driver.slot), but a job never waits on slot B: if B is held (by the other
    project), the job goes to slot A instead (2026-11-07 coordinator grant of B for the extension's cell nodes)."""
    v = os.environ.get("EXT_SLOT") or _slot_orig()
    if v == "B" and not _b_free():
        R.log("  slot B busy -> this job on slot A")
        return "A"
    return v


R.slot = _slot_ext                # R.hjob looks slot() up at call time

# EXT_STATE / EXT_CELLS / EXT_SLOT (2026-11-07, two drivers in parallel, one per Mac slot): a driver works only on
# the cells in EXT_CELLS (default all), keeps its breakpoints in EXT_STATE (two concurrent drivers must use different
# state files and disjoint (cell, range) work), and EXT_SLOT=A|B pins its jobs to that slot.
STATE = os.environ.get("EXT_STATE", "range_state_ext.json")
NODES_EXT, PIECES = "range_nodes_ext.jsonl", R.PIECES
TABLE = STATE.replace("range_state_ext", "RANGE_TABLE_ext").replace(".json", ".md")
STOPF = "STOP_RANGE_EXT"
MINW = Fr(1, 128)
TOL = R.TOL
SLABS = {n: (lo, hi) for lo, hi, n in R.SLABS}
CELLNAMES = ["case1"] + [n for _, _, n in R.SLABS]
if os.environ.get("EXT_CELLS"):
    _sel = os.environ["EXT_CELLS"].split(",")
    assert all(c in CELLNAMES for c in _sel), _sel
    CELLNAMES = [c for c in CELLNAMES if c in _sel]
MIDDLE = ("96_94", "94_93", "93_915")


def grid(a, b, h):
    a, b, h = Fr(a), Fr(b), Fr(h)
    n = (b - a) / h
    assert n.denominator == 1
    return [a + k * h for k in range(int(n) + 1)]


def initial_segments():
    up = grid("3/2", "7/4", "1/12")
    seg = {}
    for n in CELLNAMES:
        if n == "case1":
            low = [Fr(1, 3), Fr(5, 12), Fr(1, 2)]
        elif n in MIDDLE:
            low = grid("1/3", "5/12", "1/48") + grid("5/12", "1/2", "1/24")[1:]
        else:
            low = grid("1/3", "1/2", "1/24")
        seg[n] = [low, up]
    return seg


def target(s):
    return "1e-05" if s < Fr(1, 2) else "2e-05"


def sn(s):
    return R.sn(s)


def load_state():
    if os.path.exists(STATE):
        st = json.load(open(STATE))
        st["seg_fr"] = {n: [sorted(Fr(x) for x in sg) for sg in v] for n, v in st["segs"].items()}
        for n, v in initial_segments().items():
            st["seg_fr"].setdefault(n, v)
    else:
        st = {"refinements": [], "decision": {}}
        st["seg_fr"] = initial_segments()
    return st


def save_state(st):
    out = {k: v for k, v in st.items() if k != "seg_fr"}
    out["segs"] = {n: [[str(x) for x in sg] for sg in v] for n, v in st["seg_fr"].items()}
    tmp = STATE + ".tmp"
    json.dump(out, open(tmp, "w"), indent=1)
    os.replace(tmp, STATE)


def rng():
    v = os.environ.get("EXT_RANGE", "1/3,7/4").split(",")
    return Fr(v[0]), Fr(v[1])


def inside(s, r):
    return r[0] <= s <= r[1]


def required_gw(sg, s):
    i = sg.index(s)
    gaps = ([s - sg[i - 1]] if i > 0 else []) + ([sg[i + 1] - s] if i + 1 < len(sg) else [])
    return max(gaps)


def ok_nodes(cell):
    """{s: rec} of usable node certificates: new ones (range_nodes_ext.jsonl), the [1/2, 3/2] slab nodes
    (range_nodes.jsonl, read only), and the certs_lin Case 1 nodes at 1/2 and 3/2 (w = 1/8)."""
    best = {}
    recs = R.jl(NODES_EXT) + ([r for r in R.jl(R.NODES)] if cell != "case1" else [])
    for r in recs:
        if r["slab"] != cell or r["status"] != "OK":
            continue
        s = Fr(r["s"])
        if s not in best or r["gw"] > best[s]["gw"]:
            best[s] = r
    if cell == "case1":
        for s in (Fr(1, 2), Fr(3, 2)):
            c = f"certs_lin/cert_case1_s{sn(s)}_w1o8_D10.json"
            if s not in best and os.path.exists(c):
                best[s] = dict(slab="case1", s=str(s), gw=0.125, status="OK", cert=c, sha=R.sha(c), source="certs_lin")
    return best


def failed(cell, s, w):
    return any(r["slab"] == cell and Fr(r["s"]) == s and r["status"] == "FAIL" and r["gw"] <= float(w) * (1 + TOL)
               for r in R.jl(NODES_EXT))


def piece_done(pc, a, b, ca, cb):
    return R.piece_done(pc, a, b, ca, cb)


def pcell(cell):
    return "case1" if cell == "case1" else f"slab_{cell}"


def run_node(cell, s, w):
    gwf = float(w)
    T = target(s)
    if cell == "case1":
        spec, name = "case1:-0.9", "case1_-0.9"
    else:
        lo, hi = SLABS[cell]
        spec, name = f"slab:{lo}:{hi}", f"slab_{lo}_{hi}"
    tag = f"{name}_D10_s{sn(s)}_w{gwf:g}_mu_t{float(T):g}"
    cert = f"certs_range/cert_{pcell(cell)}_s{sn(s)}_w{R.wn(w)}_D10.json"
    assert not os.path.exists(cert), f"{cert} exists (refusing to overwrite)"
    R.log(f"NODE {cell} s={s} GW={w} target={T}")
    rec = dict(slab=cell, s=str(s), gw=gwf, gw_exact=str(w), target=T, cert=cert, source="range_ext",
               time=time.strftime("%Y-%m-%d %H:%M"))
    rc, out = R.hjob([f"RIESZ_S={s}", f"GW={gwf!r}", "POLYD=10", "python3", "sdp_cellS.py", spec, "mu", T], "solve")
    res = R.jline(out, '{"riesz_s"')
    if res:
        rec.update(mu=res.get("mu"), e_minus_EP=res.get("e_minus_EP"), status_solver=res.get("status"),
                   solve_time=res.get("time"))
    if rc == 3:
        rec.update(status="FAIL", reason="RSS_LIMIT"); R.append(NODES_EXT, rec); return "rss"
    if rc != 0 or not res:
        rec.update(status="FAIL", reason=f"solve rc={rc}: {out.strip().splitlines()[-3:] if out.strip() else ''}")
        R.append(NODES_EXT, rec); return "fail"
    if res["mu"] is None or res["mu"] <= 0:
        rec.update(status="FAIL", reason="mu<=0"); R.append(NODES_EXT, rec); return "fail"
    rc, out = R.hjob(["python3", "round_cell.py", f"sol/{tag}.npz", cert], "round")
    if rc != 0 or '"ALL_OK": true' not in out:
        rec.update(status="FAIL", reason=f"round rc={rc}")
        if os.path.exists(cert):                      # move aside, never delete
            os.replace(cert, cert + ".round_failed")
        R.append(NODES_EXT, rec); return "fail"
    good, out = R.check_cell_node(cert)
    if not good:
        rec.update(status="FAIL", reason="check_cell")
        os.replace(cert, cert + ".check_failed")
        R.append(NODES_EXT, rec); return "fail"
    rec.update(status="OK", sha=R.sha(cert)); R.append(NODES_EXT, rec)
    R.log(f"  node OK mu={rec.get('mu'):.3g} e-E={rec.get('e_minus_EP'):.4g}")
    return "ok"


def stop():
    return os.path.exists(STOPF)


def refine(st, cell, k, gaps, why):
    sg = st["seg_fr"][cell][k]
    added = []
    for a, b in gaps:
        m = (a + b) / 2
        if b - a < 2 * MINW:
            st["decision"][cell] = f"width below {MINW} needed on [{a}, {b}] ({why})"
            R.log(f"DECISION {cell}: {st['decision'][cell]}")
            save_state(st); return False
        if m not in sg:
            sg.append(m); added.append(str(m))
    sg.sort()
    st["refinements"].append(dict(cell=cell, why=why, gaps=[[str(a), str(b)] for a, b in gaps], added=added,
                                  time=time.strftime("%Y-%m-%d %H:%M")))
    R.log(f"REFINE {cell} ({why}): added {added}")
    save_state(st)
    return True


def pieces_pass(st, r):
    for cell in CELLNAMES:
        if cell in st["decision"]:
            continue
        nodes = ok_nodes(cell)
        for k, sg in enumerate(st["seg_fr"][cell]):
            for a, b in zip(sg, sg[1:]):
                if not (inside(a, r) and inside(b, r)):
                    continue
                ra, rb = nodes.get(a), nodes.get(b)
                if not (ra and rb and ra["gw"] >= float(b - a) * (1 - TOL) and rb["gw"] >= float(b - a) * (1 - TOL)):
                    continue
                if piece_done(pcell(cell), a, b, ra["cert"], rb["cert"]) is None:
                    if stop():
                        return
                    good = R.run_piece(pcell(cell), a, b, ra["cert"], rb["cert"])
                    write_table(st)
                    if not good:
                        refine(st, cell, k, [(a, b)], f"piece [{a}, {b}] failed")
                        return pieces_pass(st, r)


PRIORITY = [Fr(1, 3), Fr(19, 12), Fr(5, 3), Fr(7, 4), Fr(17, 48), Fr(3, 8), Fr(19, 48), Fr(5, 12), Fr(11, 24)]


def next_node(st, r):
    cands = []
    for ci, cell in enumerate(CELLNAMES):
        if cell in st["decision"]:
            continue
        nodes = ok_nodes(cell)
        for k, sg in enumerate(st["seg_fr"][cell]):
            for s in sg:
                if not inside(s, r):
                    continue
                w = required_gw(sg, s)
                rr = nodes.get(s)
                if rr and rr["gw"] >= float(w) * (1 - TOL):
                    continue
                if failed(cell, s, w):
                    continue
                pri = (PRIORITY.index(s),) if s in PRIORITY else (-1,)      # refinement nodes first
                cands.append((pri, ci, s, w, cell, k))
    return min(cands) if cands else None


def write_table(st):
    L = ["# RANGE_TABLE_ext: cells, extension of [1/2, 3/2] (generated by range_driver_ext.py; not reviewed)", "",
         f"Updated {time.strftime('%Y-%m-%d %H:%M')}. Same method as RANGE_TABLE.md (linear interpolation between exact "
         "node certificates, check_piece.py). E, H margins in hat units.", ""]
    P = {}
    for r in R.jl(PIECES):
        P.setdefault((r["cell"], r["a"], r["b"]), []).append(r)
    allext = R.jl(NODES_EXT)
    for cell in CELLNAMES:
        L += [f"## {pcell(cell)}", ""]
        if cell in st["decision"]:
            L += [f"**DECISION NEEDED:** {st['decision'][cell]}", ""]
        okn = ok_nodes(cell)
        L += ["| node s | GW | status | mu | e - E_s(P) | cert |", "|---|---|---|---|---|---|"]
        for sg in st["seg_fr"][cell]:
            for s in sg:
                recs = [x for x in allext if x["slab"] == cell and Fr(x["s"]) == s]
                if s in okn:
                    x = okn[s]
                    L.append(f"| {s} | {x.get('gw_exact', R.fmt(x['gw']))} | OK ({x.get('source')}) | {R.fmt(x.get('mu'))} | "
                             f"{R.fmt(x.get('e_minus_EP'))} | {os.path.basename(x['cert'])} |")
                elif recs:
                    x = recs[-1]
                    L.append(f"| {s} | {x.get('gw_exact')} | FAIL ({x.get('reason')}) | {R.fmt(x.get('mu'))} | "
                             f"{R.fmt(x.get('e_minus_EP'))} | - |")
                else:
                    L.append(f"| {s} | {required_gw(sg, s)} | pending | - | - | - |")
        L += ["", "| s-piece | status | E margin (hat) | H margin (hat) | check time |", "|---|---|---|---|---|"]
        for sg in st["seg_fr"][cell]:
            for a, b in zip(sg, sg[1:]):
                rs = P.get((pcell(cell), str(a), str(b)))
                if not rs:
                    L.append(f"| [{a}, {b}] | pending | - | - | - |"); continue
                x = rs[-1]; rep = x["report"] or {}
                em = [v for kk, v in rep.items() if kk.startswith("E_margin_hat")]
                hm = [v["min"] for kk, v in rep.items() if kk.startswith("H") and isinstance(v, dict)]
                L.append(f"| [{a}, {b}] | {'PIECE OK' if x['PIECE_OK'] else 'PIECE FAIL'} | "
                         f"{R.fmt(min(em) if em else None)} | {R.fmt(min(hm) if hm else None)} | {rep.get('time_s', '-')} s |")
        L.append("")
    if st["refinements"]:
        L += ["## Refinements", ""] + [f"- {x['time']} {x['cell']}: {x['why']}; added {x['added']}"
                                        for x in st["refinements"]] + [""]
    open(TABLE + ".tmp", "w").write("\n".join(L) + "\n")
    os.replace(TABLE + ".tmp", TABLE)


def main():
    st = load_state(); save_state(st)
    if "--table" in sys.argv:
        write_table(st); return
    r = rng()
    R.log(f"start ext; range [{r[0]}, {r[1]}]; slot {R.slot()}")
    write_table(st)
    while not stop():
        pieces_pass(st, r)
        if stop():
            break
        nx = next_node(st, r)
        if nx is None:
            break
        _, _, s, w, cell, k = nx
        res = run_node(cell, s, w)
        if res == "rss":
            st["decision"][cell] = f"3 GB watchdog at s = {s}"; save_state(st)
        elif res == "fail":
            sg = st["seg_fr"][cell][k]; i = sg.index(s)
            gaps = [(sg[j], sg[j + 1]) for j in (i - 1, i) if 0 <= j < len(sg) - 1]
            gaps = [g for g in gaps if g[1] - g[0] == w]
            refine(st, cell, k, gaps, f"node s = {s} GW = {w} failed")
        write_table(st)
    write_table(st)
    if stop():
        R.log("STOP_RANGE_EXT seen, stopping"); return
    R.log(f"queue empty for [{r[0]}, {r[1]}]")
    p = __import__("subprocess").run(["python3", "check_range_cover.py", "--a", str(r[0]), "--b", str(r[1])],
                                     capture_output=True, text=True)
    print(p.stdout + p.stderr, flush=True)
    R.log("RANGE_DRIVER_EXT_DONE")


if __name__ == "__main__":
    main()
