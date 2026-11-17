"""Queue driver for the [1/2, 3/2] cells design (NOTES.md section 6, "Revised design"): six D10 slabs, linear
interpolation between exact node certificates in the normalised gauge, node grid 1/16 on [1/2, 1] and 1/12 on
[1, 3/2]; Case 1 = the existing certs_lin nodes (w = 1/8).

usage: python3 range_driver.py            (normally via run_range.sh, in the background; restartable)
       python3 range_driver.py --table    (only rewrite RANGE_TABLE.md from the records)

Every heavy step (solve, rounding, check_cell, check_piece) runs through ./hjob.sh (../heavy_lock.py), one at a
time.  The slot is read before every job from the file .heavy_slot (contents "A" or "B") if it exists, else from
$HEAVY_SLOT.  A file STOP_RANGE in this directory stops the driver after the current job.

State (all in this directory):
  range_state.json   breakpoints per slab (exact rationals), refinement log
  range_nodes.jsonl  one line per node attempt: slab, s, required gw, OK/FAIL, mu, e - E_s(P), cert, sha256
  range_pieces.jsonl one line per piece check: cell, [a, b], certs + sha256, PIECE_OK, the check_piece report
  logs/range.log     driver log (run_range.sh)
Node: mu-mode solve (target 2e-5, ETA 1e-6) with GW = max of the adjacent piece widths, exact rounding
(round_cell.py: identities + Bareiss PD + e > E_s(P)), then check_cell.py with the random-configuration sanity test.
Refinement ("halve the local width in that stretch only"):
  node failure (solver error, mu <= 0, rounding not ALL_OK) at s: halve every adjacent gap of maximal width;
  piece failure on [a, b]: insert (a+b)/2.  Existing nodes stay valid (their GW is >= the new widths).
  Below MINW, or on the 3 GB watchdog, the slab is flagged DECISION and left alone.
"""
import hashlib, json, os, subprocess, sys, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
SLABS = [("-0.99", "-0.98", "99_98"), ("-0.98", "-0.96", "98_96"), ("-0.96", "-0.94", "96_94"),
         ("-0.94", "-0.93", "94_93"), ("-0.93", "-0.915", "93_915"), ("-0.915", "-0.9", "915_90")]
SLABNAMES = [n for _, _, n in SLABS]
LO, HI = Fr(1, 2), Fr(3, 2)
BASE = sorted(set([Fr(1, 2) + Fr(k, 16) for k in range(9)] + [Fr(1) + Fr(k, 12) for k in range(7)]))
# solve order: binding end s = 1/2 first, then s = 3/2, then inward from both ends
ORDER = [Fr(1, 2), Fr(3, 2), Fr(9, 16), Fr(17, 12), Fr(5, 8), Fr(4, 3), Fr(11, 16), Fr(7, 6), Fr(13, 16),
         Fr(13, 12), Fr(7, 8), Fr(1), Fr(15, 16), Fr(3, 4), Fr(5, 4)]
assert sorted(ORDER) == BASE
TARGET = "2e-05"
MINW = Fr(1, 128)
TOL = 1e-6          # relative slack when comparing a node's float GW with a required exact width
STATE, NODES, PIECES = "range_state.json", "range_nodes.jsonl", "range_pieces.jsonl"
CASE1_NODES = [Fr(1, 2) + Fr(k, 8) for k in range(9)]


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def sn(s):
    return str(s).replace("/", "o")


def wn(w):
    return f"{w.numerator}o{w.denominator}"


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def jl(path):
    return [json.loads(l) for l in open(path)] if os.path.exists(path) else []


def append(path, rec):
    with open(path, "a") as fh:
        fh.write(json.dumps(rec) + "\n")


def load_state():
    if os.path.exists(STATE):
        st = json.load(open(STATE))
    else:
        st = {"bps": {n: [str(s) for s in BASE] for n in SLABNAMES}, "refinements": [], "decision": {}}
    st["bps_fr"] = {n: sorted(Fr(x) for x in v) for n, v in st["bps"].items()}
    return st


def save_state(st):
    out = {k: v for k, v in st.items() if k != "bps_fr"}
    out["bps"] = {n: [str(x) for x in st["bps_fr"][n]] for n in SLABNAMES}
    tmp = STATE + ".tmp"
    json.dump(out, open(tmp, "w"), indent=1)
    os.replace(tmp, STATE)


def slot():
    if os.path.exists(".heavy_slot"):
        v = open(".heavy_slot").read().strip()
        if v in ("A", "B"):
            return v
    return os.environ.get("HEAVY_SLOT", "A")


def hjob(args, label):
    env = dict(os.environ, HEAVY_SLOT=slot())
    t0 = time.time()
    p = subprocess.run(["./hjob.sh"] + args, env=env, capture_output=True, text=True)
    out = p.stdout + p.stderr
    peak = [l for l in out.splitlines() if l.startswith("HJOB_PEAK_RSS_KB")]
    log(f"  [{label}] rc={p.returncode} {time.time() - t0:.0f}s slot={env['HEAVY_SLOT']} {peak[-1] if peak else ''}")
    return p.returncode, out


def jline(out, prefix):
    for l in reversed(out.splitlines()):
        l = l.strip()
        if l.startswith(prefix):
            try:
                return json.loads(l)
            except json.JSONDecodeError:
                pass
    return None


def required_gw(bps, s):
    i = bps.index(s)
    gaps = ([s - bps[i - 1]] if i > 0 else []) + ([bps[i + 1] - s] if i + 1 < len(bps) else [])
    return max(gaps)


def ok_nodes(name):
    """latest OK record per s for this slab: {s: rec} (keeps the one with the largest gw)."""
    best = {}
    for r in jl(NODES):
        if r["slab"] != name or r["status"] != "OK":
            continue
        s = Fr(r["s"])
        if s not in best or r["gw"] > best[s]["gw"]:
            best[s] = r
    return best


def failed(name, s, w):
    return any(r["slab"] == name and Fr(r["s"]) == s and r["status"] == "FAIL" and r["gw"] <= float(w) * (1 + TOL)
               for r in jl(NODES))


def piece_done(cell, a, b, ca, cb):
    for r in jl(PIECES):
        if r["cell"] == cell and r["a"] == str(a) and r["b"] == str(b) and r["certs"] == [ca, cb]:
            return r
    return None


# ------------------------------------------------------------------ steps
def check_cell_node(cert):
    rc, out = hjob(["python3", "check_cell.py", cert], "check_cell")
    return rc == 0 and "CHECK_CELL ALL_OK" in out, out


def register_existing(st):
    """the s = 3/4 (w = 1/16) and s = 5/4 (w = 1/12) nodes in certs_pt/ (run_s34*.sh, run_next.sh)."""
    have = {(r["slab"], r["s"]) for r in jl(NODES) if r["status"] == "OK"}
    for s, w in ((Fr(3, 4), Fr(1, 16)), (Fr(5, 4), Fr(1, 12))):
        for lo, hi, n in SLABS:
            if (n, str(s)) in have:
                continue
            cert = f"certs_pt/cert_slab_{n}_s{sn(s)}_w{wn(w)}_D10.json"
            if not os.path.exists(cert):
                continue
            J = json.load(open(cert))
            good, out = check_cell_node(cert)
            append(NODES, dict(slab=n, s=str(s), gw=float(J.get("solve_gw", 0)), status="OK" if good else "FAIL",
                               reason=None if good else "check_cell", mu=None, cert=cert, sha=sha(cert),
                               source="existing", time=time.strftime("%Y-%m-%d %H:%M")))
            log(f"registered existing {cert}: {'OK' if good else 'FAIL'}")


def run_node(st, n, lo, hi, s, w):
    gwf = float(w)
    tag = f"slab_{lo}_{hi}_D10_s{sn(s)}_w{gwf:g}_mu_t{float(TARGET):g}"
    cert = f"certs_range/cert_slab_{n}_s{sn(s)}_w{wn(w)}_D10.json"
    log(f"NODE slab {n} s={s} GW={w}")
    rec = dict(slab=n, s=str(s), gw=gwf, gw_exact=str(w), cert=cert, source="range",
               time=time.strftime("%Y-%m-%d %H:%M"))
    rc, out = hjob([f"RIESZ_S={s}", f"GW={gwf!r}", "POLYD=10", "python3", "sdp_cellS.py", f"slab:{lo}:{hi}", "mu",
                    TARGET], "solve")
    res = jline(out, '{"riesz_s"')
    if res:
        rec.update(mu=res.get("mu"), e_minus_EP=res.get("e_minus_EP"), status_solver=res.get("status"),
                   solve_time=res.get("time"))
    if rc == 3:
        rec.update(status="FAIL", reason="RSS_LIMIT"); append(NODES, rec); return "rss"
    if rc != 0 or not res:
        rec.update(status="FAIL", reason=f"solve rc={rc}: {out.strip().splitlines()[-3:] if out.strip() else ''}")
        append(NODES, rec); return "fail"
    if res["mu"] is None or res["mu"] <= 0:
        rec.update(status="FAIL", reason="mu<=0"); append(NODES, rec); return "fail"
    os.makedirs("certs_range", exist_ok=True)
    rc, out = hjob(["python3", "round_cell.py", f"sol/{tag}.npz", cert], "round")
    if rc != 0 or '"ALL_OK": true' not in out:
        rec.update(status="FAIL", reason=f"round rc={rc}"); append(NODES, rec); return "fail"
    good, out = check_cell_node(cert)
    if not good:
        rec.update(status="FAIL", reason="check_cell"); append(NODES, rec); return "fail"
    rec.update(status="OK", sha=sha(cert)); append(NODES, rec)
    log(f"  node OK mu={rec.get('mu'):.3g} e-E={rec.get('e_minus_EP'):.4g}")
    return "ok"


def run_piece(cell, a, b, ca, cb):
    rc, out = hjob(["python3", "check_piece.py", ca, cb], "check_piece")
    rep = jline(out, '{"certs"')
    good = rc == 0 and rep is not None and rep.get("PIECE_OK") is True
    append(PIECES, dict(cell=cell, a=str(a), b=str(b), certs=[ca, cb], sha=[sha(ca), sha(cb)], PIECE_OK=good,
                        report=rep, time=time.strftime("%Y-%m-%d %H:%M")))
    log(f"PIECE {cell} [{a}, {b}]: {'OK' if good else 'FAIL'}"
        + (f" Emin {min(v for k, v in rep.items() if k.startswith('E_margin_hat')):.3g}" if rep and good else ""))
    return good


def refine(st, n, gaps, why):
    bps = st["bps_fr"][n]
    added = []
    for a, b in gaps:
        m = (a + b) / 2
        if b - a < 2 * MINW:
            st["decision"][n] = f"width below {MINW} needed on [{a}, {b}] ({why})"
            log(f"DECISION slab {n}: {st['decision'][n]}")
            save_state(st); return False
        if m not in bps:
            bps.append(m); added.append(str(m))
    bps.sort()
    st["refinements"].append(dict(slab=n, why=why, gaps=[[str(a), str(b)] for a, b in gaps], added=added,
                                  time=time.strftime("%Y-%m-%d %H:%M")))
    log(f"REFINE slab {n} ({why}): added {added}")
    save_state(st)
    return True


def pieces_pass(st):
    for lo, hi, n in SLABS:
        if n in st["decision"]:
            continue
        bps = st["bps_fr"][n]
        nodes = ok_nodes(n)
        for a, b in zip(bps, bps[1:]):
            ra, rb = nodes.get(a), nodes.get(b)
            if not (ra and rb and ra["gw"] >= float(b - a) * (1 - TOL) and rb["gw"] >= float(b - a) * (1 - TOL)):
                continue
            r = piece_done(f"slab_{n}", a, b, ra["cert"], rb["cert"])
            if r is None:
                if stop():
                    return
                good = run_piece(f"slab_{n}", a, b, ra["cert"], rb["cert"])
                write_table(st)
                if not good:
                    refine(st, n, [(a, b)], f"piece [{a}, {b}] failed")
                    return pieces_pass(st)


def next_node(st):
    cands = []
    for k, (lo, hi, n) in enumerate(SLABS):
        if n in st["decision"]:
            continue
        bps = st["bps_fr"][n]
        nodes = ok_nodes(n)
        for s in bps:
            w = required_gw(bps, s)
            r = nodes.get(s)
            if r and r["gw"] >= float(w) * (1 - TOL):
                continue
            if failed(n, s, w):
                continue   # refinement pending / decision
            pri = (0, 0) if s not in BASE else (1, ORDER.index(s))
            cands.append((pri, k, s, w, lo, hi, n))
    return min(cands) if cands else None


def stop():
    return os.path.exists("STOP_RANGE")


def case1_pieces():
    for a, b in zip(CASE1_NODES, CASE1_NODES[1:]):
        ca, cb = (f"certs_lin/cert_case1_s{sn(x)}_w1o8_D10.json" for x in (a, b))
        if piece_done("case1", a, b, ca, cb) is None:
            run_piece("case1", a, b, ca, cb)


# ------------------------------------------------------------------ table
def fmt(x, f=".3g"):
    return "-" if x is None else format(x, f)


def write_table(st):
    L = ["# RANGE_TABLE: cells over s in [1/2, 3/2] (work package C; generated by range_driver.py; not reviewed)", "",
         f"Updated {time.strftime('%Y-%m-%d %H:%M')}. Linear interpolation in the normalised gauge between exact node "
         "certificates (check_piece.py). Margins in hat units: E = min_j (ehat_j - Ehat_j(P) - w^2/8 M) over the two "
         "nodes; H = smallest certified lower bound of psi_s - Hhat - (chord term) over the minorant ranges.", ""]
    P = {}
    for r in jl(PIECES):
        P[(r["cell"], r["a"], r["b"], tuple(r["certs"]))] = r

    def hmin(rep):
        vals = [v["min"] for k, v in rep.items() if k.startswith("H") and isinstance(v, dict)]
        return min(vals) if vals else None

    def emin(rep):
        vals = [v for k, v in rep.items() if k.startswith("E_margin_hat")]
        return min(vals) if vals else None
    cells = [("case1", "Case 1 (t >= -9/10)", CASE1_NODES)] + \
            [(f"slab_{n}", f"slab t01 in [{lo}, {hi}]", st["bps_fr"][n]) for lo, hi, n in SLABS]
    nodes_all = jl(NODES)
    for cell, title, bps in cells:
        L += [f"## {title}", ""]
        if cell != "case1":
            n = cell[5:]
            if n in st["decision"]:
                L += [f"**DECISION NEEDED:** {st['decision'][n]}", ""]
            okn = ok_nodes(n)
            L += ["| node s | GW | status | mu | e - E_s(P) | cert |", "|---|---|---|---|---|---|"]
            for s in bps:
                recs = [r for r in nodes_all if r["slab"] == n and Fr(r["s"]) == s]
                if s in okn:
                    r = okn[s]
                    L.append(f"| {s} | {r.get('gw_exact', fmt(r['gw']))} | OK | {fmt(r.get('mu'))} | "
                             f"{fmt(r.get('e_minus_EP'))} | {os.path.basename(r['cert'])} |")
                elif recs:
                    r = recs[-1]
                    L.append(f"| {s} | {r.get('gw_exact', fmt(r['gw']))} | FAIL ({r.get('reason')}) | "
                             f"{fmt(r.get('mu'))} | {fmt(r.get('e_minus_EP'))} | - |")
                else:
                    L.append(f"| {s} | {required_gw(bps, s)} | pending | - | - | - |")
            L.append("")
        L += ["| s-piece | status | E margin (hat) | H margin (hat) | check time |", "|---|---|---|---|---|"]
        for a, b in zip(bps, bps[1:]):
            rs = [r for (c, ra, rb, _), r in P.items() if c == cell and ra == str(a) and rb == str(b)]
            if not rs:
                L.append(f"| [{a}, {b}] | pending | - | - | - |"); continue
            r = rs[-1]; rep = r["report"] or {}
            L.append(f"| [{a}, {b}] | {'PIECE OK' if r['PIECE_OK'] else 'PIECE FAIL'} | {fmt(emin(rep))} | "
                     f"{fmt(hmin(rep))} | {rep.get('time_s', '-')} s |")
        # failed pieces that were refined away
        for (c, ra, rb, _), r in P.items():
            if c == cell and not r["PIECE_OK"]:
                L.append(f"| [{ra}, {rb}] (refined) | PIECE FAIL | {fmt(emin(r['report'] or {}))} | - | - |")
        L.append("")
    if st["refinements"]:
        L += ["## Refinements", ""] + [f"- {r['time']} slab {r['slab']}: {r['why']}; added nodes {r['added']}"
                                        for r in st["refinements"]] + [""]
    open("RANGE_TABLE.md.tmp", "w").write("\n".join(L) + "\n")
    os.replace("RANGE_TABLE.md.tmp", "RANGE_TABLE.md")


# ------------------------------------------------------------------ main
def main():
    st = load_state(); save_state(st)
    if "--table" in sys.argv:
        write_table(st); return
    log(f"start; slot {slot()}; breakpoints per slab {len(BASE)}")
    register_existing(st)
    case1_pieces()
    write_table(st)
    while not stop():
        pieces_pass(st)
        if stop():
            break
        nx = next_node(st)
        if nx is None:
            break
        _, _, s, w, lo, hi, n = nx
        res = run_node(st, n, lo, hi, s, w)
        if res == "rss":
            st["decision"][n] = f"3 GB watchdog at s = {s}"; save_state(st)
        elif res == "fail":
            bps = st["bps_fr"][n]; i = bps.index(s)
            gaps = [(bps[j], bps[j + 1]) for j in (i - 1, i) if 0 <= j < len(bps) - 1]
            gaps = [g for g in gaps if g[1] - g[0] == w]
            refine(st, n, gaps, f"node s = {s} GW = {w} failed")
        write_table(st)
    write_table(st)
    if stop():
        log("STOP_RANGE seen, stopping"); return
    log("queue empty; coverage check")
    p = subprocess.run(["python3", "check_range_cover.py"], capture_output=True, text=True)
    print(p.stdout + p.stderr, flush=True)
    log("RANGE_DRIVER_DONE")


if __name__ == "__main__":
    main()
