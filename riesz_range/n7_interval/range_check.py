#!/usr/bin/env python3
"""Top-level coverage checker for the N = 7 Riesz s-range warrant (default range [1/2, 3/2], the reviewed core; the current
claim is --range 1/3 7/4) (RANGE_ASSEMBLY.md, sections 4, 7 and 8).

AI-written, not reviewed.  Reads the reports of the component checkers and decides, in exact rational arithmetic,
whether the certified pieces cover the s-range component by component and fit together (C1-C7).  It never solves
and never re-runs a checker unless --recheck / --selftest-rerun is given (those go through ../heavy_lock.py).

usage: python3 range_check.py [--range 1/2 3/2] [--route local|exact] [--cell-report FILE ...] [--cap-dir DIR ...]
                              [--local-file FILE ...] [--local-legacy] [--no-freshness] [--tau-reading binary|decimal]
                              [--local-endpoints decimal|binary|strict] [--json-out FILE | --no-json]
       python3 range_check.py --selftest          (light: S0 identities (G5), engine tests, acceptance test)
       python3 range_check.py --selftest-rerun    (heavy: re-runs one cell piece and one local piece; not run by default)
       python3 range_check.py --recheck           (heavy: re-runs every used piece through ../heavy_lock.py; hours)
       python3 range_check.py --range A B --recheck --recheck-new OLD.json   (heavy: skips only pieces that OLD.json
                                          records as used + rechecked with an identical report; see below)

Components and sources (paths relative to this directory):
  cells  cellsS/check_piece.py and check_bern.py reports, from (a) --cell-report FILE (JSON or JSONL), (b)
         cellsS/results.jsonl records with "check" in {check_piece, check_bern}, (c) cellsS/logs/check_piece_*.txt and
         check_bern_*.txt, (d) cellsS/range_pieces.jsonl (range_driver.py; certificate paths + sha256 recorded).
         Kind and cell of a piece are read from its node certificates (certs_lin/, certs_pt/, certs_bern/,
         certs_range/), never from labels; a report without `certs` is ignored.
  cap    capR/pieces/check_capR_*.txt and capR/pieces_nsub/check_capR_*.txt (or --cap-dir).
  local  localS/cover2q_*_tau*.jsonl (exact "p/q" endpoints, exact tau from the file name); the float
         localS/cover2_*_tau*.jsonl files only with --local-legacy (or --local-file).
  range_check.json also records the sha256 of every checker script; a changed hash vs the previous run is printed.
Provenance cross-check (review_ext M2): a cover2q record's provenance.call (function, s0, s1, tau, exact) must equal
the record's endpoints and the tau of the file name, and a cap report's provenance.argv (a, b, TAU_DEN) must equal its
a, b, tau.  A record without provenance.call is dropped; a contradicting one is dropped and fails the run
(PROVENANCE_MISMATCH line, RANGE_FAIL), whatever the range.
Self record (review_ext M3): the sha256 of range_check.py, the python / python-flint versions of this run and the
versions recorded by the used reports go into the output (NOTE lines) and the JSON; a change against the previous JSON
(--json-out) is printed as WARN.  A WARN does not fail the run.
--recheck-new BASELINE (review_ext M4) skips a piece only if the baseline JSON marks it `used` and `rechecked` (re-run by
a --recheck, or carried forward from one) and its report sha256 there equals the current report's.  A baseline
written before per-piece recheck status existed (no `piece_recheck_status`) skips nothing.
Freshness (C6, review S1): a report that carries `provenance` (written by the current checkers) is fresh iff the
sha256 it records for its checker source (and the modules the checker relies on) equals the current file's and the
sha256 it records for every input file equals the current input's.  Reports without provenance fall back to the old
mtime rule and are flagged (NOHASH lines).  --recheck re-runs every used piece and rewrites its report in place
(originals copied to pre_recheck/<time>/ first), so that the next plain run sees hash-authenticated reports.
Output: a table, DROPPED / WARN / CHECK lines, then RANGE_OK [lo, hi] route=<r>, or UNCOVERED <component> <interval>
lines (exact rationals; '[' / '(' mark closed / open ends of a gap) and RANGE_FAIL.  Exit status 0 iff RANGE_OK.
Writes range_check.json (inventory: which report certified which interval, and why a report was dropped).
See "Implementation notes" in RANGE_ASSEMBLY.md for the decisions taken where the spec did not fit the files.
"""
import argparse, glob, gzip, hashlib, json, os, re, shutil, subprocess, sys, time
from fractions import Fraction as Fr

sys.dont_write_bytecode = True          # importing check_cell in --selftest must not write into cellsS/

HERE = os.path.dirname(os.path.abspath(__file__))
CELLS_DIR = os.path.join(HERE, "cellsS")
CERT_DIRS = ["certs_lin", "certs_pt", "certs_bern", "certs_range"]
CAP_LO, CAP_HI = Fr(-1), Fr(-99, 100)       # cap cell, hard-coded in check_capR.py (multipliers of T6)
CASE1_CUT = Fr(-9, 10)                       # Case 1 cut of the written chain
K6_TAU_MAX = Fr(1, 10)                       # K6 (ring rigidity) needs tau <= 1/10
MARGIN = 2.0                                 # seconds: process start + imports before the checker's own clock starts
SCRIPTS = {
    "check_piece": [os.path.join(CELLS_DIR, f) for f in ("check_piece.py", "check_cell.py", "check_minorant_cell.py")]
                   + [os.path.join(HERE, "..", "hp", "check_cert.py")],
    "check_bern": [os.path.join(CELLS_DIR, f) for f in ("check_bern.py", "check_piece.py", "check_cell.py",
                                                        "check_minorant_cell.py")]
                  + [os.path.join(HERE, "..", "hp", "check_cert.py")],
    "check_capR": [os.path.join(HERE, "capR", "check_capR.py")],
    "check_localS": [os.path.join(HERE, "localS", "check_localS.py")],
}


def rel(p):
    try:
        r = os.path.relpath(p, HERE)
    except ValueError:
        return p
    return os.path.abspath(p) if r.startswith("..") and not r.startswith(os.path.join("..", "hp")) else r


def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


_JCACHE = {}


def load_json(p):
    st = os.stat(p)
    key = (p, st.st_mtime, st.st_size)
    if key not in _JCACHE:
        with (gzip.open(p, "rt") if p.endswith(".gz") else open(p)) as f:
            _JCACHE[key] = json.load(f)
    return _JCACHE[key]


_SHACACHE = {}


def sha_cached(p):
    st = os.stat(p)
    key = (p, st.st_mtime, st.st_size)
    if key not in _SHACACHE:
        _SHACACHE[key] = sha256(p)
    return _SHACACHE[key]


def rec_sha(R):
    """sha256 of a parsed report record (canonical JSON), used to recognise an unchanged report (M4)."""
    return hashlib.sha256(json.dumps(R, sort_keys=True, separators=(",", ":"), default=str).encode()).hexdigest()


def text_sha(txt):
    return hashlib.sha256(txt.encode()).hexdigest()


def json_records(path, parse_float=None):
    """a JSON file (one object) or JSONL / log text: every line that parses as a JSON object, with its line number."""
    txt = open(path).read()
    try:
        J = json.loads(txt, parse_float=parse_float)
        if isinstance(J, dict):
            return [(0, J)], []
        if isinstance(J, list):
            return [(i, x) for i, x in enumerate(J) if isinstance(x, dict)], []
    except json.JSONDecodeError:
        pass
    out, bad = [], []
    for i, line in enumerate(txt.splitlines()):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            J = json.loads(line, parse_float=parse_float)
        except json.JSONDecodeError:
            bad.append(i + 1); continue           # e.g. a line being appended right now
        if isinstance(J, dict):
            out.append((i + 1, J))
    return out, bad


# ====================================================================== pieces
class Piece:
    """one report (or record) claiming a component on the closed s-interval [a, b]."""

    def __init__(self, comp, src, idx, checker):
        self.comp, self.src, self.idx, self.checker = comp, src, idx, checker
        self.a = self.b = None
        self.info = {}
        self.problems = []        # reasons to drop (soundness / bookkeeping)
        self.ok_claim = False     # the report itself says OK
        self.fresh = None         # freshness note

    @property
    def used(self):
        return self.ok_claim and not self.problems and self.a is not None

    def drop(self, why):
        self.problems.append(why)

    def key(self):
        """identity of a piece across runs: (source, record, a, b) as in range_check.json."""
        return (rel(self.src), self.idx, None if self.a is None else str(self.a), None if self.b is None else str(self.b))

    def label(self):
        if self.comp == "slab":
            return f"slab[{self.info['lo']}, {self.info['hi']}]"
        if self.comp == "case1":
            return "case1" + ("" if self.info.get("cut") == CASE1_CUT else f"(cut {self.info.get('cut')})")
        return self.comp

    def as_json(self):
        return dict(component=self.comp, label=self.label(), a=None if self.a is None else str(self.a),
                    b=None if self.b is None else str(self.b), source=rel(self.src), record=self.idx,
                    checker=self.checker, report_ok=self.ok_claim, used=self.used, problems=self.problems,
                    freshness=self.fresh, **{k: (str(v) if isinstance(v, Fr) else v) for k, v in self.info.items()})


def mtime(p):
    return os.stat(p).st_mtime


def tfmt(t):
    return time.strftime("%m-%d %H:%M:%S", time.localtime(t))


def freshness(P, end, run_s, inputs, scripts, sha_verified=(), exact_end=True, opts=None):
    """C6.  end: time the report was written (upper bound if not exact_end); run_s: the checker's own run time.
    Inputs must predate the run's start (unless their sha256 was verified against the record), scripts too."""
    if opts is not None and opts.no_freshness:
        P.fresh = "not checked (--no-freshness)"; return
    start = end - (run_s or 0) - MARGIN
    bad = []
    for p in inputs:
        if p in sha_verified:
            continue
        if not os.path.exists(p):
            continue                                   # reported elsewhere
        if mtime(p) >= start:
            bad.append(f"input {rel(p)} modified {tfmt(mtime(p))} >= run start ~{tfmt(start)}")
    for p in scripts:
        if os.path.exists(p) and mtime(p) >= start:
            bad.append(f"checker {rel(p)} modified {tfmt(mtime(p))} >= run start ~{tfmt(start)}")
    P.fresh = ("ok" if not bad else "STALE") + ("" if exact_end else " (heuristic: multi-record file, file mtime "
                                                                     "used as the record's end time)")
    for b in bad:
        P.drop("stale: " + b)


def hash_auth(P, prov, inputs, checker):
    """S1: decide freshness from the hashes a report records (its `provenance`).  Fresh iff the recorded sha256 of the
    checker source and of every module in SCRIPTS[checker] equals the current file's, and the recorded (name, sha256)
    of the inputs equal those of the current input files (same number of inputs).  Returns False (undecided) if the
    report carries no provenance; the caller then applies the mtime fallback."""
    if not isinstance(prov, dict) or not prov.get("checker_sha256"):
        return False
    bad = []
    rec = {prov.get("checker"): prov.get("checker_sha256")}
    for d in prov.get("deps") or []:
        rec[d.get("name")] = d.get("sha256")
    for p in SCRIPTS[checker]:
        nm = os.path.basename(p)
        if not os.path.exists(p):
            bad.append(f"checker file {rel(p)} missing now")
        elif nm not in rec:
            bad.append(f"report records no sha256 for checker file {nm}")
        elif rec[nm] != sha_cached(p):
            bad.append(f"checker {rel(p)} changed: sha256 {str(rec[nm])[:12]} recorded, {sha_cached(p)[:12]} now")
    recin = [(d.get("name"), d.get("sha256")) for d in prov.get("inputs") or []]
    for p in inputs:
        if not os.path.exists(p):
            continue                                   # reported elsewhere (missing input)
        cur = (os.path.basename(p), sha_cached(p))
        if cur not in recin:
            was = [str(h)[:12] for n, h in recin if n == cur[0]]
            bad.append(f"input {rel(p)}: sha256 {cur[1][:12]} now, recorded {was or 'nothing for this name'}")
    if len(recin) != len(inputs):
        bad.append(f"report records {len(recin)} input file(s), the piece has {len(inputs)}")
    P.info["auth"] = "sha256"
    P.info["versions"] = f"python {prov.get('python')}, python-flint {prov.get('flint')}"     # M3 (review_ext)
    P.fresh = "ok (sha256 of checker and inputs)" if not bad else "STALE (sha256)"
    for b in bad:
        P.drop("stale (sha256): " + b)
    return True


def authenticate(P, prov, end, run_s, inputs, checker, sha_verified=(), exact_end=True, opts=None):
    """C6: sha256 provenance if the report has it (S1), else the mtime rule as a flagged fallback."""
    if opts is not None and opts.no_freshness:
        P.fresh = "not checked (--no-freshness)"; P.info["auth"] = "off"; return
    if hash_auth(P, prov, inputs, checker):
        return
    freshness(P, end, run_s, inputs, SCRIPTS[checker], sha_verified, exact_end, opts)
    P.info["auth"] = "mtime-fallback"
    P.fresh = "mtime fallback (report has no hashes): " + P.fresh


# ---------------------------------------------------------------------- cells
def riesz_s(kernel):
    if not isinstance(kernel, str) or not kernel.startswith("riesz:"):
        return None
    return Fr(kernel.split(":", 1)[1])


def cellfr(c):
    return {k: Fr(v) for k, v in c.items()} if isinstance(c, dict) else None


def resolve_cert(name, explicit=None):
    """-> (path, problem).  Basenames are looked up in the cellsS certificate directories; a basename present in
    several directories is accepted only if all copies are byte-identical."""
    if explicit is not None:
        p = explicit if os.path.isabs(explicit) else os.path.join(CELLS_DIR, explicit)
        return (p, None) if os.path.exists(p) else (None, f"certificate {explicit} missing")
    if os.path.dirname(name):
        p = name if os.path.isabs(name) else os.path.join(CELLS_DIR, name)
        return (p, None) if os.path.exists(p) else (None, f"certificate {name} missing")
    cands = [os.path.join(CELLS_DIR, d, name) for d in CERT_DIRS if os.path.exists(os.path.join(CELLS_DIR, d, name))]
    if not cands:
        return None, f"certificate {name} not found in {CERT_DIRS}"
    if len({sha_cached(p) for p in cands}) > 1:
        return None, f"certificate {name} ambiguous: differing copies in {[rel(c) for c in cands]}"
    return cands[0], None


def cell_piece(rep, src, idx, opts, end, exact_end, cert_paths=None, shas=None, rec=None):
    if "PIECE_OK" in rep:
        checker = "check_piece"
    elif "BERN_OK" in rep:
        checker = "check_bern"
    else:
        return None
    P = Piece("cell", src, idx, checker)
    P.ok_claim = rep.get("PIECE_OK") is True or rep.get("BERN_OK") is True
    if rec is not None:
        P.ok_claim &= rec.get("PIECE_OK") is True
    sr = rep.get("s_range")
    try:
        P.a, P.b = Fr(sr[0]), Fr(sr[1])
    except Exception:
        P.drop("no s_range"); P.a = None
    if rec is not None and P.a is not None and (Fr(rec["a"]), Fr(rec["b"])) != (P.a, P.b):
        P.drop("record [a, b] differs from the report's s_range")
    names = rep.get("certs")
    if not names:
        P.drop("report has no `certs` (cell labels are not trusted)"); P.comp = "cell?"; return P
    paths, sha_ok = [], set()
    for k, nm in enumerate(names):
        p, prob = resolve_cert(nm, cert_paths[k] if cert_paths else None)
        if prob:
            P.drop(prob); continue
        if shas is not None:
            if sha_cached(p) != shas[k]:
                P.drop(f"sha256 of {rel(p)} differs from the one recorded when the piece was checked")
            else:
                sha_ok.add(p)
        paths.append(p)
    P.info["certs"] = [rel(p) for p in paths]
    if len(paths) != len(names):
        P.comp = "cell?"; return P
    Js = [load_json(p) for p in paths]
    J0 = Js[0]
    kind, cell, D = J0.get("kind"), cellfr(J0.get("cell")), J0.get("D")
    for J in Js:
        if J.get("kind") != kind or cellfr(J.get("cell")) != cell or J.get("D") != D:
            P.drop("node certificates differ in kind / cell / D")
    if cellfr(rep.get("cell")) != cell:
        P.drop("report's cell differs from the certificates' cell")
    if checker == "check_piece":
        if len(Js) != 2:
            P.drop("check_piece report must name two certificates")
        else:
            sa, sb = riesz_s(Js[0].get("kernel")), riesz_s(Js[1].get("kernel"))
            if sa is None or sb is None:
                P.drop(f"kernels {Js[0].get('kernel')}, {Js[1].get('kernel')} are not riesz:p/q")
            elif P.a is not None and not (sa == P.a and sb == P.b and 0 < sa < sb):
                P.drop(f"certificate kernels riesz:{sa}, riesz:{sb} do not match s_range [{P.a}, {P.b}]")
            for nm in names:
                nd = rep.get("node_" + os.path.basename(nm))
                if not (isinstance(nd, dict) and nd.get("ALL_OK") is True):
                    P.drop(f"exact node check of {os.path.basename(nm)} not recorded as ALL_OK (skip_exact run?)")
    else:
        m = rep.get("m")
        if m != len(Js) - 1:
            P.drop("Bernstein degree m does not match the number of controls")
        for k, J in enumerate(Js):
            if J.get("kernel") != "hat":
                P.drop(f"control {k} kernel {J.get('kernel')} is not 'hat'")
            if J.get("solve_control") != k or J.get("solve_m") != m:
                P.drop(f"control {k} has solve_control/solve_m {J.get('solve_control')}/{J.get('solve_m')}")
            try:
                if P.a is not None and (Fr(J["solve_a"]), Fr(J["solve_b"])) != (P.a, P.b):
                    P.drop(f"control {k} solve_a/solve_b differ from s_range")
            except KeyError:
                P.drop(f"control {k} has no solve_a/solve_b")
        if rep.get("controls_identities_PD") is not True:
            P.drop("controls_identities_PD not true (skip_exact run?)")
    if P.a is not None and not (0 < P.a < P.b):
        P.drop("need 0 < a < b")
    if kind == "case1" and cell is not None and "a" in cell:
        P.comp = "case1"; P.info["cut"] = cell["a"]
    elif kind == "slab" and cell is not None and "lo" in cell and "hi" in cell:
        P.comp = "slab"; P.info["lo"], P.info["hi"] = cell["lo"], cell["hi"]
        if not (-1 < cell["lo"] < cell["hi"] < 0):
            P.drop("slab cell must satisfy -1 < lo < hi < 0")
    else:
        P.comp = "cell?"; P.drop(f"unknown kind/cell {kind} {J0.get('cell')}")
    P.info["D"] = D
    authenticate(P, rep.get("provenance"), end, rep.get("time_s"), paths, checker, sha_ok, exact_end, opts)
    return P


def collect_cells(opts, warns):
    pieces = []
    srcs = []
    for f in opts.cell_report or []:
        srcs.append(("arg", os.path.abspath(f)))
    srcs.append(("results", os.path.join(CELLS_DIR, "results.jsonl")))
    for pat in ("check_piece_*.txt", "check_bern_*.txt"):
        for f in sorted(glob.glob(os.path.join(CELLS_DIR, "logs", pat))):
            srcs.append(("log", f))
    srcs.append(("range_pieces", os.path.join(CELLS_DIR, "range_pieces.jsonl")))
    nocerts = {}
    for kind, f in srcs:
        if not os.path.exists(f):
            if kind == "arg":
                warns.append(f"--cell-report {f} does not exist")
            continue
        recs, bad = json_records(f)
        if bad:
            warns.append(f"{rel(f)}: unparsable JSON line(s) {bad[:5]} ignored (being written?)")
        multi = len(recs) > 1
        end = mtime(f)
        for i, R in recs:
            if kind == "range_pieces":
                rep = R.get("report") or {}
                if not isinstance(rep, dict) or "PIECE_OK" not in rep:
                    P = Piece("cell?", f, i, "check_piece"); P.drop("record without report"); pieces.append(P)
                    continue
                try:
                    t_rec = time.mktime(time.strptime(R["time"], "%Y-%m-%d %H:%M"))   # floor of the end time
                except Exception:
                    t_rec = end
                P = cell_piece(rep, f, i, opts, t_rec, True, cert_paths=R.get("certs"), shas=R.get("sha"), rec=R)
            else:
                if kind == "results" and R.get("check") not in ("check_piece", "check_bern"):
                    continue
                if "PIECE_OK" not in R and "BERN_OK" not in R:
                    continue
                if not R.get("certs"):
                    nocerts[rel(f)] = nocerts.get(rel(f), 0) + 1
                P = cell_piece(R, f, i, opts, end, not multi)
            if P is not None:
                P.info["report_sha256"] = rec_sha(R)
                pieces.append(P)
    for f, n in nocerts.items():
        warns.append(f"{f}: {n} piece record(s) without `certs` ignored (cell labels are not trusted)")
    return pieces


# ---------------------------------------------------------------------- cap
CAP_JSON = re.compile(r"(?:^|\n)(\{\n.*?\n\})\n(PIECE_OK|PIECE_FAIL)?", re.S)


def cap_node_s(J):
    if "s" in J:
        return Fr(J["s"])
    if str(J.get("kernel", "")).startswith("coulomb"):
        return Fr(1)
    return None


def cap_argv_mismatch(prov, a, b, tau):
    """M2 (review_ext): the a, b, TAU_DEN check_capR was called with (provenance.argv, written by the checker from
    sys.argv) must equal the report's a, b, tau.  Returns '' if consistent or if the report has no provenance argv
    (mtime-fallback reports; nothing to compare), else the reason."""
    if not isinstance(prov, dict) or prov.get("argv") is None:
        return ""
    argv = prov.get("argv")
    try:
        i0 = next(i for i, x in enumerate(argv) if str(x).endswith("check_capR.py"))
        ca, cb = Fr(argv[i0 + 4]), Fr(argv[i0 + 5])
        ctau = Fr(1, int(argv[i0 + 7])) if len(argv) > i0 + 7 else Fr(1, 10 ** 6)
    except Exception as ex:
        return f"provenance.argv {argv} does not parse as check_capR.py A B DIRS a b [delta [TAU_DEN]] ({ex})"
    bad = []
    if (ca, cb) != (a, b):
        bad.append(f"called with s in [{ca}, {cb}], report says [{a}, {b}]")
    if ctau != tau:
        bad.append(f"called with 1/TAU_DEN = {ctau}, report says tau = {tau}")
    return "; ".join(bad)


def cap_piece_from_text(txt, src, idx, opts, end, sub_mtime=None):
    P = Piece("cap", src, idx, "check_capR")
    P.info["report_sha256"] = text_sha(txt)
    m = CAP_JSON.search(txt)
    if not m:
        P.drop("no JSON block (still running, or crashed)"); P.comp = "cap"; return P
    try:
        J = json.loads(m.group(1))
    except json.JSONDecodeError as ex:
        P.drop(f"JSON block does not parse: {ex}"); return P
    P.ok_claim = J.get("PIECE_OK") is True and m.group(2) != "PIECE_FAIL"
    for k in ("E1_E2_E4", "E3_pins", "P_ok", "M_ok", "K_ok"):
        if k in J and J[k] is not True:
            P.ok_claim = False
    tok = (J.get("coercivity") or {}).get("tau_ok_exact") or {}
    if P.ok_claim and not (tok and all(v is True for v in tok.values())):
        P.drop("coercivity tau_ok_exact not all true")
    try:
        P.a, P.b = Fr(J["a"]), Fr(J["b"])
        T = Fr(J["tau"])
        assert T > 0
    except Exception as ex:
        P.drop(f"bad a / b / tau fields ({ex})"); P.a = None; return P
    delta = J.get("delta")
    try:
        dq = Fr(delta) if not isinstance(delta, str) else Fr(delta)
    except Exception:
        dq = None
    if dq is None or dq < 0:
        P.drop(f"delta {delta!r} is not a number >= 0")
    pm = cap_argv_mismatch(J.get("provenance"), P.a, P.b, T)
    if pm:
        P.info["prov_mismatch"] = pm; P.drop("provenance mismatch: " + pm)
    P.info.update(tau=T, tau_den=(T.denominator if T.numerator == 1 else None), delta=delta,
                  nsub=J.get("P_nsub", 1), P_min_slack=J.get("P_min_slack"),
                  M_remainder=J.get("M_remainder", "two-sided"), windows=J.get("windows"),
                  settings=(J.get("provenance") or {}).get("settings"))
    if not (0 < P.a < P.b):
        P.drop("need 0 < a < b")
    nodes = J.get("nodes") or []
    inputs = []
    if len(nodes) != 2:
        P.drop("report must name two node certificates")
    for k, nd in enumerate(nodes[:2]):
        cands = [nd] if os.path.isabs(nd) else [os.path.join(HERE, nd), os.path.join(HERE, "capR", nd)]
        p = next((c for c in cands if os.path.exists(c)), None)
        if p is None:
            P.drop(f"node certificate {nd} missing"); continue
        inputs.append(p)
        N = load_json(p)
        s = cap_node_s(N)
        want = (P.a, P.b)[k]
        if s != want:
            P.drop(f"node {rel(p)} has s = {s}, report endpoint is {want}")
        try:
            cell_ok = (Fr(N["cell"][0]), Fr(N["cell"][1])) == (CAP_LO, CAP_HI) and N.get("D") == 12
        except Exception:
            cell_ok = False
        if not cell_ok:
            P.drop(f"node {rel(p)} cell/D is not [-1, -99/100], 12")
    P.info["nodes"] = [rel(p) for p in inputs]
    dirs = J.get("dirs")
    if dirs:
        pd = dirs if os.path.isabs(dirs) else os.path.join(HERE, dirs)
        if not os.path.exists(pd):
            alt = os.path.join(HERE, "capR", os.path.basename(dirs))
            pd = alt if os.path.exists(alt) else None
        if pd is None:
            P.drop(f"directions file {dirs} missing")
        else:
            inputs.append(pd)
            P.info["dirs"] = rel(pd)
    else:
        P.drop("report names no directions file")
    authenticate(P, J.get("provenance"), end, J.get("time_s"), inputs, "check_capR", (), True, opts)
    return P


def collect_cap(opts, warns):
    dirs = opts.cap_dir or [d for d in (os.path.join(HERE, "capR", "pieces"), os.path.join(HERE, "capR", "pieces_nsub"))
                            if os.path.isdir(d)]
    pieces = []
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(d, "check_capR_*.txt"))):
            P = cap_piece_from_text(open(f).read(), f, 0, opts, mtime(f))
            pieces.append(P)
    return pieces


# ---------------------------------------------------------------------- local
TAU_RE = re.compile(r"tau([0-9.eE+o/-]+?)\.jsonl$")
QTOK = re.compile(r"^-?[0-9]+(/[0-9]+)?$")          # exact rational token "p/q" or "n" (cover2q)


def local_interval(lo_tok, hi_tok, mode):
    """C7: the checker parsed repr(float) as a decimal for the s-ball (sball) but used the binary floats for the chord
    nodes (lam_point(arb(s0))) and h.  decimal = the spec's reading; binary; strict = intersection of both."""
    dl, dh = Fr(lo_tok), Fr(hi_tok)
    bl, bh = Fr(float(lo_tok)), Fr(float(hi_tok))
    if mode == "decimal":
        return dl, dh
    if mode == "binary":
        return bl, bh
    return max(dl, bl), min(dh, bh)


def local_files(opts):
    if opts.local_file:
        return opts.local_file
    files = sorted(glob.glob(os.path.join(HERE, "localS", "cover2q_*_tau*.jsonl")))
    if opts.local_legacy:
        files += sorted(glob.glob(os.path.join(HERE, "localS", "cover2_*_tau*.jsonl")))
    return files


def local_call_mismatch(prov, a, b, tau):
    """M2 (review_ext): a cover2q record must have been produced by check_localS.check_piece called exactly with the
    record's endpoints and the tau of the file name (provenance.call, written by the checker from its own arguments).
    -> (missing, mismatch): missing = no provenance.call to compare (drop the piece); mismatch = the call contradicts
    the record or the file name (drop the piece and fail the run)."""
    call = prov.get("call") if isinstance(prov, dict) else None
    if not isinstance(call, dict):
        return "record has no provenance.call (s0, s1, tau, exact) to cross-check endpoints and tau", ""
    bad = []
    if call.get("function") != "check_localS.check_piece":
        bad.append(f"call.function {call.get('function')!r} is not check_localS.check_piece")
    if call.get("exact") is not True:
        bad.append(f"call.exact is {call.get('exact')!r}, not true (float endpoints or tau)")
    for nm, want in (("s0", a), ("s1", b), ("tau", tau)):
        try:
            got = Fr(str(call.get(nm)))
        except (ValueError, ZeroDivisionError, TypeError):
            bad.append(f"call.{nm} = {call.get(nm)!r} is not a rational"); continue
        if got != want:
            bad.append(f"call.{nm} = {got}, but the " + ("file name says tau = " if nm == "tau" else "record says ")
                       + str(want))
    return "", "; ".join(bad)


def collect_local(opts, warns):
    """cover2q files (exact rational endpoints "p/q" and exact tau, check_localS.py cover2q) are the default; the float
    cover2 files only with --local-legacy (C7 readings via --local-endpoints / --tau-reading apply to them only)."""
    pieces = []
    for f in local_files(opts):
        exact = os.path.basename(f).startswith("cover2q_")
        m = TAU_RE.search(os.path.basename(f))
        if not m:
            warns.append(f"{rel(f)}: no tau in the file name, ignored"); continue
        tok = m.group(1)
        if exact:
            tau = Fr(tok.replace("o", "/"))         # cover2q: tau = Fraction(argv) exactly, r uses arb(p)/arb(q)
            reading = "exact"
        else:
            tau = Fr(float(tok)) if opts.tau_reading == "binary" else Fr(tok)
            reading = opts.tau_reading
        recs, bad = json_records(f, parse_float=str)
        if bad:
            warns.append(f"{rel(f)}: unparsable line(s) {bad[:5]} ignored")
        prev_hi = None
        for i, R in recs:
            pc = R.get("piece")
            if not (isinstance(pc, list) and len(pc) == 2):
                continue
            P = Piece("local", f, i, "check_localS")
            P.ok_claim = R.get("LOCAL_OK") is True and not R.get("FAILED")
            lo_tok, hi_tok = str(pc[0]), str(pc[1])
            if exact:
                if not (isinstance(pc[0], str) and isinstance(pc[1], str) and QTOK.match(lo_tok)
                        and QTOK.match(hi_tok)):
                    P.drop(f"cover2q endpoints {pc} are not exact rational strings")
                    P.a = P.b = None; pieces.append(P); continue
                P.a, P.b = Fr(lo_tok), Fr(hi_tok)
            else:
                P.a, P.b = local_interval(lo_tok, hi_tok, opts.local_endpoints)
            P.info.update(tau=tau, tau_token=tok, tau_reading=reading, exact=exact, endpoints=[lo_tok, hi_tok],
                          report_sha256=rec_sha(R))
            if not P.a < P.b:
                P.drop("empty interval")
            if exact:                                  # M2 (review_ext): bind tau / endpoints to the actual call
                miss, pm = local_call_mismatch(R.get("provenance"), P.a, P.b, tau)
                if miss:
                    P.drop(miss)
                if pm:
                    P.info["prov_mismatch"] = pm; P.drop("provenance mismatch: " + pm)
            if P.ok_claim:
                if prev_hi is not None and Fr(lo_tok) != prev_hi:
                    warns.append(f"{rel(f)} line {i}: piece starts at {lo_tok}, previous OK piece ended at "
                                 f"{prev_hi} (no chain)")
                prev_hi = Fr(hi_tok)
            authenticate(P, R.get("provenance"), mtime(f), 0, [], "check_localS", (), True, opts)
            pieces.append(P)
    return pieces


# ====================================================================== coverage engine
def merge(iv):
    """union of closed intervals (a, b), exact: merge when next.a <= cur.b."""
    out = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def elementary(B):
    """atoms of the line between the sorted points B: ('pt', x) and ('iv', x, y) (open), in order."""
    B = sorted(set(B))
    out = []
    for k, x in enumerate(B):
        out.append(("pt", x, x))
        if k + 1 < len(B):
            out.append(("iv", x, B[k + 1]))
    return out


def contains(a, b, atom):
    return a <= atom[1] and atom[2] <= b


def gaps_from(atoms, bad):
    """maximal runs of failing atoms -> list of (lo, lo_closed, hi, hi_closed, atom indices)."""
    out, run = [], []
    for k, at in enumerate(atoms):
        if bad[k]:
            run.append(k)
        elif run:
            out.append(run); run = []
    if run:
        out.append(run)
    res = []
    for r in out:
        f, l = atoms[r[0]], atoms[r[-1]]
        res.append((f[1], f[0] == "pt", l[2], l[0] == "pt", r))
    return res


def short(items, k=4):
    if not items:
        return "-"
    if len(items) <= k:
        return ", ".join(items)
    return ", ".join(items[:2]) + f", ... ({len(items)} intervals; UNCOVERED lines / range_check.json)"


def fmt_gap(g):
    lo, lc, hi, hc = g[:4]
    if lo == hi:
        return f"{{{lo}}}"
    return f"{'[' if lc else '('}{lo}, {hi}{']' if hc else ')'}"


def cover(pieces, lo, hi):
    """gaps of [lo, hi] not covered by the union of the closed intervals `pieces` (spec 7, pseudo-signature)."""
    B = [lo, hi] + [x for a, b in pieces for x in (a, b) if lo <= x <= hi]
    atoms = elementary(B)
    bad = [not any(contains(a, b, at) for a, b in pieces) for at in atoms]
    return [g[:4] for g in gaps_from(atoms, bad)]


def tiling_reach(slabs, start=CAP_HI):
    """largest t such that the union of the closed slabs covers [start, t] (start itself counts); None if not even
    start is covered.  Overlaps are harmless (a slab certificate covers every m in its [lo, hi])."""
    cur, moved = start, False
    for lo, hi in sorted(slabs):
        if lo <= cur and hi >= cur:
            cur, moved = max(cur, hi), True
    return cur if moved else None


def tiling_ok(slabs, cut=CASE1_CUT):
    r = tiling_reach(slabs)
    return r is not None and r >= cut


def evaluate(pieces, lo, hi, route):
    """per-atom checks C1-C3 -> dict check -> list of gaps (with details)."""
    used = [P for P in pieces if P.used and P.a <= hi and P.b >= lo]
    B = {lo, hi} | {x for P in used for x in (P.a, P.b) if lo <= x <= hi}
    atoms = elementary(B)
    byc = {c: [P for P in used if P.comp == c] for c in ("case1", "slab", "cap", "local")}
    checks = ["case1", "slabs", "slab_tiling", "cap"] + (["local", "tau_compat"] if route == "local" else [])
    bad = {c: [False] * len(atoms) for c in checks}
    detail = {c: [None] * len(atoms) for c in checks}
    for k, at in enumerate(atoms):
        c1 = [P for P in byc["case1"] if contains(P.a, P.b, at)]
        sl = [P for P in byc["slab"] if contains(P.a, P.b, at)]
        cp = [P for P in byc["cap"] if contains(P.a, P.b, at)]
        lc = [P for P in byc["local"] if contains(P.a, P.b, at)]
        cuts = [P.info["cut"] for P in c1 if CAP_HI < P.info["cut"] < 0]
        if not cuts:
            bad["case1"][k] = True
        target = min(cuts) if cuts else CASE1_CUT
        if target > CAP_HI:
            if not sl:
                bad["slabs"][k] = True
            else:
                r = tiling_reach([(P.info["lo"], P.info["hi"]) for P in sl])
                if r is None or r < target:
                    bad["slab_tiling"][k] = True
                    detail["slab_tiling"][k] = ("no slab contains t01 = -99/100" if r is None else
                                                f"slabs cover t01 in [-99/100, {r}] only, need up to {target}")
        if not cp:
            bad["cap"][k] = True
        if route == "local":
            if not lc:
                bad["local"][k] = True
            if cp and lc:
                good = any(P.info["tau"] <= K6_TAU_MAX and P.info["tau"] <= L.info["tau"] for P in cp for L in lc)
                if not good:
                    bad["tau_compat"][k] = True
                    detail["tau_compat"][k] = ("cap 1/TAU_DEN in {" + ", ".join(sorted({str(P.info['tau']) for P in cp}))
                                               + "} vs local tau in {" + ", ".join(sorted({str(L.info['tau']) for L in lc}))
                                               + "}: no (cap, local) pair with 1/TAU_DEN <= tau_local and "
                                               "1/TAU_DEN <= 1/10")
    res = {}
    for c in checks:
        gs = gaps_from(atoms, bad[c])
        res[c] = [(g[:4], sorted({detail[c][i] for i in g[4] if detail[c][i]})) for g in gs]
    return res, atoms


# ====================================================================== hygiene (source greps)
def source_checks(legacy=False):
    out = []
    p = SCRIPTS["check_capR"][0]
    src = open(p).read() if os.path.exists(p) else ""
    out.append(("cap cell [-1, -99/100] hard-coded in check_capR.py (fmpq(-99, 100), Fr(-99, 100) assert)",
                "fmpq(-99, 100)" in src and "(Fr(-1), Fr(-99, 100))" in src))
    p = SCRIPTS["check_localS"][0]
    src = open(p).read() if os.path.exists(p) else ""
    m = re.search(r"\ndef check_piece\(.*?(?=\ndef )", src, re.S)
    body = m.group(0) if m else ""
    out.append(("check_localS.check_piece uses r = sqrt7 (11/2) tau, tau exact (qarb)",
                "r = arb(7).sqrt() * arb(11) / 2 * qarb(tau)" in body))
    q = re.search(r"\ndef qarb\(.*?(?=\ndef )", src, re.S)
    out.append(("check_localS.qarb: Fraction -> arb(num) / arb(den)",
                bool(q) and "arb(x.numerator) / arb(x.denominator)" in q.group(0)))
    m2 = re.search(r'sys.argv\[1\] == "cover2q":.*?(?=\nif __name__)', src, re.S)
    out.append(("check_localS cover2q reads a, b, tau as Fractions",
                bool(m2) and "Fraction(sys.argv[2]), Fraction(sys.argv[3]), Fraction(sys.argv[4])" in m2.group(0)))
    if legacy:
        out.append(("check_localS cover2 (legacy) reads tau as a binary float (tau = float(sys.argv[4]))",
                    "tau = float(sys.argv[4])" in src))
    out.append(("cell boundaries -1 < -99/100 < -9/10", CAP_LO < CAP_HI < CASE1_CUT))
    return out


# ====================================================================== heavy (flags only)
def heavy(cmd, cwd, env=None):
    """run cmd through heavy_lock.py (one heavy job at a time, 1 thread, nice 19) -> (rc, stdout, stderr)."""
    p = subprocess.run([sys.executable, os.path.join(HERE, "heavy_lock.py")] + cmd, cwd=cwd, capture_output=True,
                       text=True, env=None if env is None else dict(os.environ, **env))
    return p.returncode, p.stdout, p.stderr


def last_json(out):
    for line in reversed(out.strip().splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                pass
    return None


CAP_DEFAULT_WINDOWS = (0.05, 0.02, 0.002)


def recheck_piece(P):
    """re-run the checker of one used piece from its input files (heavy; through heavy_lock.py), with the settings
    the report records -> (ok, note, payload).  payload is the new report: the full check_capR output text for cap
    pieces, the report dict otherwise (a dict with PIECE_OK / LOCAL_OK false and `error` if the checker crashed)."""
    if P.checker in ("check_piece", "check_bern"):
        certs = [os.path.relpath(os.path.join(HERE, c), CELLS_DIR) for c in P.info["certs"]]
        if P.checker == "check_piece":
            cmd, flag = ["python3", "check_piece.py"] + certs, "PIECE_OK"
        else:
            rep = [r for i, r in json_records(P.src)[0] if i == P.idx]
            nsub = str(rep[0].get("nsub", 200)) if rep else "200"
            cmd, flag = ["python3", "check_bern.py", nsub] + certs, "BERN_OK"
        rc, out, err = heavy(cmd, CELLS_DIR)
        J = last_json(out)
        if J is None:
            J = {"certs": [os.path.basename(c) for c in certs], "s_range": [str(P.a), str(P.b)], flag: False,
                 "error": "no JSON output (rc %d): %s" % (rc, (out + err).strip()[-500:])}
        ok = rc == 0 and J.get(flag) is True
        return ok, f"{flag}={J.get(flag)} ({J.get('time_s')} s)", J
    if P.checker == "check_capR":
        st = P.info.get("settings") or {}
        env = {"NSUB": str(st.get("NSUB", P.info.get("nsub", 1))),
               "M_TWOSIDED": "1" if (st.get("M_TWOSIDED") if st else P.info.get("M_remainder") != "one-sided") else "0"}
        for k in ("NWIN", "N0", "RB", "RC", "RA"):
            if k in st:
                env[k] = str(st[k])
        win = P.info.get("windows") or {}
        if not st and tuple(win.get(k) for k in ("rB", "rC", "rA")) != CAP_DEFAULT_WINDOWS:
            return False, f"window radii {win} are not the defaults and the report records no settings", None
        cmd = ["python3", "capR/check_capR.py"] + list(P.info["nodes"]) + \
              [P.info["dirs"], str(P.a), str(P.b), str(P.info["delta"]), str(P.info["tau_den"] or 10 ** 6)]
        rc, out, err = heavy(cmd, HERE, env)
        text = out + (("\n[stderr]\n" + err) if err.strip() else "")
        ok = rc == 0 and out.strip().endswith("PIECE_OK")
        last = out.strip().splitlines()[-1] if out.strip() else "(no output)"
        return ok, f"{last} (env {' '.join(f'{k}={v}' for k, v in env.items())})", text
    if P.checker == "check_localS":
        lo, hi = P.info["endpoints"]
        if P.info.get("exact"):
            code = ("import json, check_localS as L; from fractions import Fraction as F; "
                    f"print(json.dumps(L.check_piece(F('{lo}'), F('{hi}'), F('{P.info['tau']}'))))")
        else:
            code = ("import json, check_localS as L; "
                    f"print(json.dumps(L.check_piece({float(lo)!r}, {float(hi)!r}, {float(P.info['tau_token'])!r})))")
        rc, out, err = heavy(["python3", "-c", code], os.path.join(HERE, "localS"))
        J = last_json(out)
        if J is None:
            J = {"LOCAL_OK": False, "error": "no JSON output (rc %d): %s" % (rc, (out + err).strip()[-500:])}
        return J.get("LOCAL_OK") is True, f"LOCAL_OK={J.get('LOCAL_OK')} lambda_S={J.get('lambda_S')}", J
    return False, "unknown checker", None


# ---------------------------------------------------------------------- regenerate reports in place (--recheck)
_BACKUP = []


def backup(path):
    """copy the original report file to pre_recheck/<time>/<relpath> once per run (never deleted, never moved back)."""
    if not _BACKUP:
        _BACKUP.append(os.path.join(HERE, "pre_recheck", time.strftime("%Y%m%d_%H%M%S")))
    dst = os.path.join(_BACKUP[0], os.path.relpath(path, HERE))
    if not os.path.exists(dst):
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(path, dst)
    return dst


def write_atomic(path, text):
    tmp = path + ".recheck_tmp"
    with open(tmp, "w") as f:
        f.write(text)
    os.replace(tmp, path)


def old_report(P):
    """the report of piece P as currently stored (for the before/after comparison)."""
    if P.comp == "cap":
        m = CAP_JSON.search(open(P.src).read())
        return json.loads(m.group(1)) if m else None
    recs = dict(json_records(P.src)[0])
    R = recs.get(P.idx)
    if R is None:
        return None
    if os.path.basename(P.src) == "range_pieces.jsonl":
        return R.get("report")
    if P.comp == "local":
        return {k: v for k, v in R.items() if k != "piece"}
    return R


def regenerate(P, payload):
    """write the re-run report of P into P's report file, in the same format (original copied aside first)."""
    backup(P.src)
    if P.comp == "cap":
        write_atomic(P.src, payload); return
    txt = open(P.src).read()
    lines = txt.split("\n")
    if P.idx == 0:                                  # the whole file is one JSON object
        write_atomic(P.src, json.dumps(payload) + "\n"); return
    R = json.loads(lines[P.idx - 1])
    if os.path.basename(P.src) == "range_pieces.jsonl":
        R2 = dict(R)
        R2.update(report=payload, PIECE_OK=payload.get("PIECE_OK") is True, time=time.strftime("%Y-%m-%d %H:%M"),
                  rechecked_by="range_check.py --recheck", previous_time=R.get("time"))
    elif P.comp == "local":
        R2 = dict(piece=R["piece"], **payload)
    else:
        R2 = ({"check": R["check"]} if "check" in R else {}) | payload
    lines[P.idx - 1] = json.dumps(R2)
    write_atomic(P.src, "\n".join(lines))


SKIP_CMP = {"time_s", "provenance", "nodes", "dirs", "time", "error"}


def flat(x, pre=""):
    out = {}
    if isinstance(x, dict):
        for k, v in x.items():
            if k not in SKIP_CMP:
                out.update(flat(v, f"{pre}.{k}" if pre else str(k)))
    elif isinstance(x, list):
        for i, v in enumerate(x):
            out.update(flat(v, f"{pre}[{i}]"))
    else:
        out[pre] = x
    return out


def compare_reports(old, new, flag):
    """before/after: verdict flag, and the numeric leaves present in both (max relative difference)."""
    if old is None or new is None:
        return dict(verdict_old=None if old is None else old.get(flag), verdict_new=None if new is None else
                    new.get(flag), n_common=0, n_diff=0, max_rel=None, diff_keys=[])
    fo, fn = flat(old), flat(new)
    nd, mx, keys = 0, 0.0, []
    for k in sorted(set(fo) & set(fn)):
        a, b = fo[k], fn[k]
        if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, (int, float)) or \
                not isinstance(b, (int, float)):
            if a != b:
                nd += 1; keys.append(k)
            continue
        if a != b:
            nd += 1; keys.append(k)
            mx = max(mx, abs(a - b) / max(abs(a), abs(b), 1e-300))
    return dict(verdict_old=old.get(flag), verdict_new=new.get(flag), n_common=len(set(fo) & set(fn)), n_diff=nd,
                max_rel=mx, diff_keys=keys[:6])


def recheckable(P):
    """a piece that would be used if its report were fresh: the report claims OK, the bookkeeping is sound, and the
    only reasons to drop it are staleness (old checker version / changed inputs by mtime or sha256)."""
    return P.ok_claim and P.a is not None and all(q.startswith("stale") for q in P.problems)


def recheck_skip(pieces, baseline):
    """M4 (review_ext): the pieces --recheck-new may skip, given a baseline range_check.json (path or dict).
    A piece is skipped only if the baseline lists it (same source, record, a, b) as `used`, as `rechecked` (re-run OK by
    a --recheck, or carried forward from one with an identical report) and with a `report_sha256` equal to the sha256
    of the piece's current report.  A baseline without per-piece recheck status (`piece_recheck_status` absent: written
    before 2026-11-07 evening) proves nothing about which pieces were re-run, so nothing is skipped (conservative).
    -> (skip: dict key -> rechecked label, counts: dict reason -> n)."""
    B = json.load(open(baseline)) if isinstance(baseline, str) else baseline
    counts = dict(skipped=0, not_listed=0, listed_not_used=0, listed_not_rechecked=0, report_changed=0, legacy=0)
    skip = {}
    if not B.get("piece_recheck_status"):
        counts["legacy"] = len(pieces)
        return skip, counts
    ents = {(q.get("source"), q.get("record"), q.get("a"), q.get("b")): q for q in B.get("pieces") or []}
    for P in pieces:
        q = ents.get(P.key())
        if q is None:
            counts["not_listed"] += 1
        elif q.get("used") is not True:
            counts["listed_not_used"] += 1
        elif not q.get("rechecked"):
            counts["listed_not_rechecked"] += 1
        elif not q.get("report_sha256") or q.get("report_sha256") != P.info.get("report_sha256"):
            counts["report_changed"] += 1
        else:
            counts["skipped"] += 1; skip[P.key()] = q["rechecked"]
    return skip, counts


def carry_rechecked(pieces, prev):
    """M4: carry the per-piece recheck status forward from a previous range_check.json (path or dict) for pieces whose
    report is byte-identical (same report_sha256) to the one that was re-checked; a plain run thus keeps the record of
    which reports were produced by a --recheck.  Returns the number of pieces carried."""
    try:
        skip, _ = recheck_skip(pieces, prev)
    except Exception:
        return 0
    for P in pieces:
        if P.key() in skip and P.used:
            P.info["rechecked"] = skip[P.key()]
    return len([P for P in pieces if P.key() in skip and P.used])


def run_recheck(pieces, baseline=None, dry_run=False):
    """--recheck: re-run every used (or only-stale) piece, rewrite its report in place, compare with the stored one.
    baseline (--recheck-new FILE, a range_check.json inventory): skip the pieces recheck_skip() accepts (listed there as
    used and rechecked, with an identical report), re-run all others.  dry_run: return the list of pieces that would
    be re-run (selftest), nothing is run.  Returns (stats, marks): marks = key -> recheck label for every piece re-run
    OK here or skipped as rechecked in the baseline."""
    used = [P for P in pieces if recheckable(P)]
    marks = {}
    if baseline is not None:
        skip, cnt = recheck_skip(used, baseline)
        n0 = len(used)
        used = [P for P in used if P.key() not in skip]
        marks.update(skip)
        if not dry_run:
            print(f"recheck: --recheck-new {rel(baseline) if isinstance(baseline, str) else 'baseline'}: "
                  f"{n0 - len(used)} of {n0} pieces skipped (used + rechecked + identical report there); re-run: "
                  f"{cnt['not_listed']} not listed, {cnt['listed_not_used']} listed but not used, "
                  f"{cnt['listed_not_rechecked']} listed but not rechecked, {cnt['report_changed']} report changed"
                  + (f", {cnt['legacy']} because the baseline records no per-piece recheck status" if cnt["legacy"]
                     else ""), flush=True)
    if dry_run:
        return used
    t0 = time.time()
    label = "range_check.py --recheck " + time.strftime("%Y-%m-%d %H:%M:%S")
    print(f"recheck: {len(used)} pieces (used, or dropped only as stale); reports are rewritten in place, originals copied to "
          f"pre_recheck/<time>/", flush=True)
    stats = dict(ok=0, failed=0, verdict_changed=0)
    changed = []
    for k, P in enumerate(used, 1):
        flag = {"cap": "PIECE_OK", "local": "LOCAL_OK"}.get(P.comp, "BERN_OK" if P.checker == "check_bern" else
                                                             "PIECE_OK")
        old = old_report(P)
        t1 = time.time()
        ok, note, payload = recheck_piece(P)
        new = payload
        if P.comp == "cap" and isinstance(payload, str):
            m = CAP_JSON.search(payload)
            new = json.loads(m.group(1)) if m else None
        if payload is not None:
            regenerate(P, payload)
        if ok:
            marks[P.key()] = label
        c = compare_reports(old, new, flag)
        vchg = c["verdict_old"] != c["verdict_new"]
        stats["ok" if ok else "failed"] += 1
        if vchg:
            stats["verdict_changed"] += 1; changed.append(P)
        print(f"recheck {k}/{len(used)} {P.label()} [{P.a}, {P.b}] {rel(P.src)}" + (f" line {P.idx}" if P.idx else "")
              + f": {'OK' if ok else 'FAILED'} {note}; verdict {c['verdict_old']} -> {c['verdict_new']}"
              + (" CHANGED" if vchg else "") + f"; {c['n_diff']}/{c['n_common']} report fields differ"
              + (f" (max rel {c['max_rel']:.1e}: {', '.join(c['diff_keys'])})" if c["n_diff"] else "")
              + f" [{time.time() - t1:.0f} s]", flush=True)
    print(f"recheck done: {stats['ok']} OK, {stats['failed']} FAILED, verdict changed vs the stored reports: "
          f"{stats['verdict_changed']}" + (f" ({', '.join(f'{P.label()} [{P.a}, {P.b}]' for P in changed)})"
                                           if changed else "")
          + f"; originals in {rel(_BACKUP[0]) if _BACKUP else '-'}; {time.time() - t0:.0f} s", flush=True)
    return stats, marks


# ====================================================================== main run
def run(opts, quiet=False, inject_cap=None):
    lo, hi = Fr(opts.range[0]), Fr(opts.range[1])
    warns = []
    cells = collect_cells(opts, warns)
    cap = collect_cap(opts, warns) if inject_cap is None else inject_cap
    local = collect_local(opts, warns) if opts.route == "local" else []
    pieces = cells + cap + local
    srcchk = source_checks(opts.local_legacy or bool(opts.local_file)) if opts.route == "local" else \
        [c for c in source_checks() if not c[0].startswith("check_localS")]
    rstats = None
    marks = {}
    if opts.recheck:
        # re-run every used piece, rewrite its report in place, then decide from the regenerated reports only
        rstats, marks = run_recheck(pieces, opts.recheck_new)
        warns = []
        _JCACHE.clear(); _SHACACHE.clear()
        cells = collect_cells(opts, warns)
        cap = collect_cap(opts, warns) if inject_cap is None else inject_cap
        local = collect_local(opts, warns) if opts.route == "local" else []
        pieces = cells + cap + local
    # M4 (review_ext): per-piece recheck status: re-run OK here, skipped as rechecked in the --recheck-new baseline,
    # or carried forward from the previous JSON for an identical report; None otherwise
    prevJ = None
    if not opts.no_json and os.path.exists(opts.json_out):
        try:
            prevJ = json.load(open(opts.json_out))
        except Exception:
            prevJ = None
    for P in pieces:
        P.info["rechecked"] = None
    if prevJ is not None:
        carry_rechecked(pieces, prevJ)
    for P in pieces:
        if P.used and P.key() in marks:
            P.info["rechecked"] = marks[P.key()]
    # M2 (review_ext): a report whose recorded call contradicts its own record / file name fails the run
    mism = [P for P in pieces if P.ok_claim and P.info.get("prov_mismatch")]
    res, atoms = evaluate(pieces, lo, hi, opts.route)
    L = []
    pr = L.append
    pr(f"range_check: s in [{lo}, {hi}], route={opts.route}, local="
       + ("cover2q (exact)" if not (opts.local_legacy or opts.local_file) else
          f"cover2q + legacy cover2 (tau reading {opts.tau_reading}, endpoints {opts.local_endpoints})")
       + f", freshness={'off' if opts.no_freshness else 'on'}")
    pr("")
    pr(f"{'component':28s} {'used':>4s} {'dropped':>7s}  certified (within range)      gaps")
    rows = [("case1 (cut -9/10)", lambda P: P.comp == "case1" and P.info.get("cut") == CASE1_CUT)]
    slabkeys = sorted({(P.info["lo"], P.info["hi"]) for P in pieces if P.comp == "slab"})
    for key in slabkeys:
        rows.append((f"slab [{key[0]}, {key[1]}]", lambda P, key=key: P.comp == "slab" and
                     (P.info["lo"], P.info["hi"]) == key))
    if not slabkeys:
        rows.append(("slabs (none found)", lambda P: P.comp == "slab"))
    rows += [("cap [-1, -99/100]", lambda P: P.comp == "cap")]
    if opts.route == "local":
        rows += [("local lemma", lambda P: P.comp == "local")]
    for name, sel in rows:
        ps = [P for P in pieces if sel(P)]
        us = [P for P in ps if P.used]
        iv = [(max(P.a, lo), min(P.b, hi)) for P in us if P.a <= hi and P.b >= lo]
        un = merge(iv)
        gp = cover(iv, lo, hi)
        pr(f"{name:28s} {len(us):4d} {len([P for P in ps if P.problems or not P.ok_claim]):7d}  "
           f"{short([f'[{a}, {b}]' for a, b in un]):28s}  {short([fmt_gap(g) for g in gp])}")
    pr("")
    for P in pieces:
        if P.comp == "local" or any(q.startswith("report has no `certs`") for q in P.problems):
            continue                                  # summarised below / in a WARN line
        where = f"{P.label()} [{P.a}, {P.b}] {rel(P.src)}" + (f" line {P.idx}" if P.idx else "")
        if P.ok_claim and P.problems:
            pr(f"DROPPED {where}: " + "; ".join(P.problems))
        elif not P.ok_claim:
            pr(f"NOT_OK  {where}: " + ("; ".join(P.problems) if P.problems else "the report itself is not OK"))
    for P in local:
        if P.ok_claim and P.problems:
            pr(f"DROPPED local [{P.a}, {P.b}] {rel(P.src)} line {P.idx}: " + "; ".join(P.problems))
    nlf = len([P for P in local if not P.ok_claim])
    if nlf:
        pr(f"NOT_OK  local: {nlf} piece record(s) with LOCAL_OK false or FAILED (ignored)")
    for w in warns:
        pr("WARN " + w)
    # S1: how the used pieces were authenticated (sha256 provenance, or the flagged mtime fallback)
    usedP = [P for P in pieces if P.used]
    nh = [P for P in usedP if P.info.get("auth") == "sha256"]
    nm = [P for P in usedP if P.info.get("auth") == "mtime-fallback"]
    pr(f"NOTE authentication of the {len(usedP)} used pieces: {len(nh)} by sha256 (checker + inputs), {len(nm)} by the "
       f"mtime fallback (reports without hashes)" + (", freshness off" if opts.no_freshness else ""))
    bysrc = {}
    for P in nm:
        bysrc.setdefault(rel(P.src), []).append(P)
    for f, ps in sorted(bysrc.items()):
        pr(f"NOHASH {f}: {len(ps)} used piece(s) authenticated only by the mtime rule (run --recheck to regenerate)")
    if rstats is not None:
        pr(f"NOTE recheck: {rstats['ok']} OK, {rstats['failed']} FAILED, verdict changed vs the stored reports: "
           f"{rstats['verdict_changed']}; regenerated reports read back from disk; originals in "
           f"{rel(_BACKUP[0]) if _BACKUP else '-'}")
    allsrc = True
    for name, ok in srcchk:
        pr(f"CHECK {'ok  ' if ok else 'FAIL'} {name}")
        allsrc &= ok
    if opts.route == "local":
        taus = sorted({(P.info["tau"], P.info["tau_token"], P.info["tau_reading"]) for P in local if P.used})
        for t, tok, rd in taus:
            pr(f"NOTE local tau from file name '{tok}' read as {rd}: {t}"
               + (f" (= {float(t):.20e})" if t.denominator > 10 ** 12 else ""))
        files = sorted({rel(P.src) for P in local})
        pr("NOTE local files: " + ", ".join(files) + ("" if opts.local_legacy or opts.local_file else
                                                      "  (float cover2 files only with --local-legacy)"))
    ck = checker_hashes()
    me = self_info()
    vers = report_versions(usedP)
    pr(f"NOTE range_check.py sha256 {me['sha256']} (this run: python {me['python']}, python-flint {me['flint']})")
    pr("NOTE versions recorded by the used reports: " + "; ".join(f"{v} ({n})" for v, n in sorted(vers.items())))
    if len(vers) > 1:
        pr(f"WARN the used reports record {len(vers)} different python / python-flint version pairs")
    nrc = len([P for P in usedP if P.info.get("rechecked")])
    pr(f"NOTE recheck status: {nrc} of the {len(usedP)} used pieces are recorded as re-run by a --recheck with the "
       f"current report (what --recheck-new may skip)")
    if not opts.no_json:
        for line in checker_changes(opts.json_out, ck) + self_changes(opts.json_out, prevJ, me, vers):
            pr(line)
    for P in mism:
        pr(f"PROVENANCE_MISMATCH {P.label()} [{P.a}, {P.b}] {rel(P.src)}" + (f" line {P.idx}" if P.idx else "")
           + f": {P.info['prov_mismatch']}")
    pr("")
    out = []
    names = {"case1": "case1", "slabs": "slabs", "slab_tiling": "slab_tiling", "cap": "cap", "local": "local",
             "tau_compat": "tau_compat"}
    for c, gs in res.items():
        for g, det in gs:
            out.append(f"UNCOVERED {names[c]} {fmt_gap(g)}" + (f"   ({'; '.join(det)})" if det else ""))
    ok = not out and allsrc and not mism
    L += out
    L.append(f"RANGE_OK [{lo}, {hi}] route={opts.route}" if ok else "RANGE_FAIL")
    if not quiet:
        print("\n".join(L), flush=True)
    if not opts.no_json:
        J = dict(range=[str(lo), str(hi)], route=opts.route, local_legacy=bool(opts.local_legacy),
                 tau_reading=opts.tau_reading, local_endpoints=opts.local_endpoints, freshness=not opts.no_freshness,
                 checkers=ck, range_check=me, report_versions=vers, recheck=rstats,
                 recheck_new=None if not opts.recheck_new else rel(opts.recheck_new), piece_recheck_status=True,
                 provenance_mismatch=[dict(piece=P.key(), why=P.info["prov_mismatch"]) for P in mism],
                 authentication=dict(sha256=len(nh), mtime_fallback=len(nm)),
                 time=time.strftime("%Y-%m-%d %H:%M:%S"), result="RANGE_OK" if ok else "RANGE_FAIL",
                 uncovered=out, source_checks=[dict(check=n, ok=o) for n, o in srcchk], warnings=warns,
                 pieces=[P.as_json() for P in pieces])
        tmp = opts.json_out + ".tmp"
        with open(tmp, "w") as f:
            json.dump(J, f, indent=1)
        os.replace(tmp, opts.json_out)
    return ok, res, pieces, L


# ====================================================================== checker hashes
def checker_hashes():
    """sha256 and mtime of every checker script range_check relies on (recorded in range_check.json)."""
    out = {}
    for p in sorted({os.path.normpath(q) for v in SCRIPTS.values() for q in v}):
        if os.path.exists(p):
            out[rel(p)] = dict(sha256=sha256(p), mtime=time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(mtime(p))))
        else:
            out[rel(p)] = dict(sha256=None, mtime=None)
    return out


def self_info():
    """M3 (review_ext): sha256 of this file and the interpreter / python-flint versions of this run."""
    import platform
    try:
        import flint
        fv = flint.__version__
    except Exception:
        fv = None
    me = os.path.abspath(__file__)
    return dict(path=rel(me), sha256=sha256(me), python=platform.python_version(), flint=fv)


def report_versions(used):
    """M3: how many used reports record which python / python-flint versions in their provenance."""
    out = {}
    for P in used:
        v = P.info.get("versions") or "not recorded (no provenance)"
        out[v] = out.get(v, 0) + 1
    return out


def self_changes(path, prev, me, vers):
    """M3: WARN lines if range_check.py, this run's versions or the reports' recorded versions differ from the previous
    JSON at `path` (loaded as `prev`).  Information only: a WARN does not fail the run."""
    if prev is None:
        return []
    old = prev.get("range_check")
    if not old:
        return [f"NOTE previous {rel(path)} ({prev.get('time')}) records no range_check.py sha256 / versions; "
                f"recorded now"]
    lines = []
    if old.get("sha256") != me["sha256"]:
        lines.append(f"WARN range_check.py changed since the previous run ({prev.get('time')}): sha256 "
                     f"{str(old.get('sha256'))[:12]} -> {me['sha256'][:12]}")
    for k, nm in (("python", "python"), ("flint", "python-flint")):
        if old.get(k) != me[k]:
            lines.append(f"WARN {nm} version of this run changed since the previous run: {old.get(k)} -> {me[k]}")
    pv = prev.get("report_versions")
    if pv is not None and pv != vers:
        lines.append(f"WARN versions recorded by the used reports changed since the previous run: {pv} -> {vers}")
    if not lines:
        lines.append(f"NOTE range_check.py sha256 and versions unchanged since the previous run ({prev.get('time')})")
    return lines


def checker_changes(prev_json, now):
    """NOTE lines for checkers whose sha256 differs from the previous range_check.json (information only: whether
    a report was produced by the current checker version still needs the checker's own self-hash, not yet there)."""
    if not os.path.exists(prev_json):
        return [f"NOTE no previous {rel(prev_json)}: checker hashes recorded for the first time"]
    try:
        old = json.load(open(prev_json))
    except Exception:
        return [f"NOTE previous {rel(prev_json)} unreadable; checker hashes re-recorded"]
    prev = old.get("checkers")
    if not prev:
        return [f"NOTE previous {rel(prev_json)} ({old.get('time')}) has no checker hashes; recorded now"]
    lines = []
    for p, d in now.items():
        o = prev.get(p)
        if o is None:
            lines.append(f"NOTE checker {p}: new since the previous run ({old.get('time')})")
        elif o.get("sha256") != d["sha256"]:
            lines.append(f"CHECKER_CHANGED {p}: sha256 {str(o.get('sha256'))[:12]} ({o.get('mtime')}) -> "
                         f"{str(d['sha256'])[:12]} ({d['mtime']}) since the previous run ({old.get('time')})")
    if not lines:
        lines.append(f"NOTE all {len(now)} checker scripts unchanged (sha256) since the previous run ({old.get('time')})")
    return lines


# ====================================================================== self-test
def selftest_S0():
    """G5: the normalised-gauge shift S0 = (H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2, psi = 0, F = B = 0; slab
    c_gamma = 1 from (6)) has all cell identities' LHS identically 0 (check_cell's own polynomial code)."""
    sys.path.insert(0, CELLS_DIR)
    import check_cell as CK
    res = []
    for D in (10, 12):
        z = lambda n: [[Fr(0)] * n for _ in range(n)]
        one = [Fr(1)] + [Fr(0)] * D
        # Case 1: slack polynomial (the only identity), cut irrelevant for the LHS
        J = {"kind": "case1", "D": D, "cell": {"a": "-9/10"}}
        c = dict(H=one, e=Fr(21), F=[z(D // 2 + 1 - k) for k in range(D // 2 - 1)])
        Lp = CK.lhs_polys(J, c)
        req = CK.required(J)
        zero = all(all(v == 0 for v in Lp[tag].values()) for tag in req)
        res.append((f"S0 case1 D{D}: identity LHS == 0 for tags {sorted(req)}", zero))
        # slab: lambda_A, lambda_B, lambda_Gamma and (6)
        for lo_, hi_ in (("-99/100", "-49/50"), ("-93/100", "-9/10")):
            J = {"kind": "slab", "D": D, "cell": {"lo": lo_, "hi": hi_}}
            sizes = list(range(D // 2 + 1, 0, -1))
            c = dict(hA=one, hB=one, hC=one, pBa=[Fr(0)] * (D + 1), pCb=[Fr(0)] * (D + 1), ca=Fr(1, 5), cb=Fr(1, 2),
                     e=Fr(21), FP=[z(n) for n in sizes], FR=[z(n) for n in sizes])
            Lp = CK.lhs_polys(J, c)
            req = CK.required(J)
            zero = all(all(v == 0 for v in Lp[tag].values()) for tag in req)
            cg = Lp["cg"]
            six = (cg == 1) and (5 * c["ca"] + 20 * c["cb"] + 10 * cg == c["e"] + 2 * Lp["oneP"] + 5 * Lp["oneR"])
            res.append((f"S0 slab [{lo_}, {hi_}] D{D}: lambda_A/B/Gamma LHS == 0 for tags {sorted(req)}, "
                        f"c_gamma = {cg}, (6) holds", zero and six))
        # negative controls (the test is not vacuous): e = 22 resp. c_alpha = 1/4 must leave a nonzero LHS
        J = {"kind": "case1", "D": D, "cell": {"a": "-9/10"}}
        c = dict(H=one, e=Fr(22), F=[z(D // 2 + 1 - k) for k in range(D // 2 - 1)])
        Lp = CK.lhs_polys(J, c)
        res.append((f"S0 negative control case1 D{D} (e = 22): LHS != 0", any(v != 0 for v in Lp["S"].values())))
        J = {"kind": "slab", "D": D, "cell": {"lo": "-99/100", "hi": "-49/50"}}
        c = dict(hA=one, hB=one, hC=one, pBa=[Fr(0)] * (D + 1), pCb=[Fr(0)] * (D + 1), ca=Fr(1, 4), cb=Fr(1, 2),
                 e=Fr(21), FP=[z(n) for n in sizes], FR=[z(n) for n in sizes])
        Lp = CK.lhs_polys(J, c)
        res.append((f"S0 negative control slab D{D} (c_alpha = 1/4): lambda_A != 0",
                    any(v != 0 for v in Lp["A"].values())))
    return res


def selftest_engine():
    F = Fr
    res = []
    g = cover([(F(1, 2), F(1)), (F(1), F(3, 2))], F(1, 2), F(3, 2))
    res.append(("cover: adjacent closed pieces cover [1/2, 3/2]", g == []))
    g = cover([(F(1, 2), F(3, 4)), (F(4, 5), F(3, 2))], F(1, 2), F(3, 2))
    res.append(("cover: gap (3/4, 4/5) is open", [fmt_gap(x) for x in g] == ["(3/4, 4/5)"]))
    g = cover([(F(11, 12), F(1)), (F(1), F(13, 12))], F(1, 2), F(3, 2))
    res.append(("cover: gaps [1/2, 11/12) and (13/12, 3/2]", [fmt_gap(x) for x in g] == ["[1/2, 11/12)",
                                                                                          "(13/12, 3/2]"]))
    g = cover([(F(1, 2), F(1))], F(1, 2), F(3, 2))
    res.append(("cover: end point 3/2 uncovered", [fmt_gap(x) for x in g] == ["(1, 3/2]"]))
    g = cover([(F(1, 2), F(1, 2) + F(1, 10 ** 20)), (F(1, 2) + F(2, 10 ** 20), F(3, 2))], F(1, 2), F(3, 2))
    res.append(("cover: tiny gap detected", len(g) == 1))
    six = [(F(-99, 100), F(-49, 50)), (F(-49, 50), F(-24, 25)), (F(-24, 25), F(-47, 50)), (F(-47, 50), F(-93, 100)),
           (F(-93, 100), F(-183, 200)), (F(-183, 200), F(-9, 10))]
    five = [(F(-99, 100), F(-49, 50)), (F(-49, 50), F(-24, 25)), (F(-24, 25), F(-47, 50)), (F(-47, 50), F(-93, 100)),
            (F(-93, 100), F(-9, 10))]
    res.append(("tiling: six-slab", tiling_ok(six)))
    res.append(("tiling: five-slab", tiling_ok(five)))
    res.append(("tiling: missing middle slab fails", not tiling_ok(six[:2] + six[3:])))
    res.append(("tiling: overlap harmless", tiling_ok(six + [(F(-19, 20), F(-91, 100))])))
    res.append(("tiling: must start at -99/100", not tiling_ok(six[1:])))
    res.append(("tiling: must reach -9/10", not tiling_ok(six[:-1])))
    # C7 decimal parse
    a, b = local_interval("0.55", "0.5950000000000001", "decimal")
    res.append(("C7: decimal endpoint", b == F(5950000000000001, 10 ** 16) and a == F(11, 20)))
    a2, b2 = local_interval("0.55", "0.5950000000000001", "binary")
    res.append(("C7: binary endpoint differs from decimal", b2 == F(0.5950000000000001) and b2 != b))
    res.append(("tau: float(1e-06) < 1/10^6 exactly", F(float("1e-06")) < F(1, 10 ** 6) == F("1e-06")))
    m = TAU_RE.search("cover2q_1o2_3o2_tau1e-6.jsonl")
    res.append(("cover2q: tau token '1e-6' -> exactly 1/10^6", bool(m) and F(m.group(1).replace("o", "/")) ==
                F(1, 10 ** 6)))
    m = TAU_RE.search("cover2q_1o2_3o2_tau1o250000.jsonl")
    res.append(("cover2q: tau token '1o250000' -> 1/250000", bool(m) and F(m.group(1).replace("o", "/")) ==
                F(1, 250000)))
    res.append(("cover2q: endpoint tokens must be p/q", bool(QTOK.match("37060327/26214400")) and
                not QTOK.match("0.5950000000000001")))
    # per-atom engine: tiling may change between elementary intervals; tau compat
    class O: pass
    def mk(comp, a, b, **kw):
        P = Piece(comp, "synthetic", 0, "x"); P.a, P.b = F(a), F(b); P.ok_claim = True; P.info.update(kw); return P
    ps = [mk("case1", "1/2", "3/2", cut=F(-9, 10))]
    ps += [mk("slab", "1/2", "1", lo=l, hi=h) for l, h in five] + [mk("slab", "1", "3/2", lo=l, hi=h) for l, h in six]
    ps += [mk("cap", "1/2", "1", tau=F(1, 10 ** 6)), mk("cap", "1", "3/2", tau=F(1, 250000))]
    ps += [mk("local", "1/2", "3/2", tau=F(1, 10 ** 6))]
    r, _ = evaluate(ps, F(1, 2), F(3, 2), "local")
    res.append(("engine: five-slab then six-slab tiles; tau_compat fails exactly on [1, 3/2]",
                all(not r[c] for c in ("case1", "slabs", "slab_tiling", "cap", "local")) and
                [fmt_gap(g) for g, _ in r["tau_compat"]] == ["(1, 3/2]"]))
    ps[-1] = mk("local", "1/2", "3/2", tau=F(1, 250000))
    r, _ = evaluate(ps, F(1, 2), F(3, 2), "local")
    res.append(("engine: all OK with local tau 4e-6", all(not v for v in r.values())))
    r, _ = evaluate(ps[:-1], F(1, 2), F(3, 2), "exact")
    res.append(("engine: route exact ignores local", all(not v for v in r.values())))
    ps2 = [P for P in ps if not (P.comp == "slab" and P.a == F(1) and P.info["lo"] == F(-93, 100))]
    r, _ = evaluate(ps2, F(1, 2), F(3, 2), "local")
    res.append(("engine: slab_tiling gap (1, 3/2] but point s = 1 covered by the five-slab pieces",
                [fmt_gap(g) for g, _ in r["slab_tiling"]] == ["(1, 3/2]"]))
    return res


def selftest_acceptance(opts):
    """spec 7 acceptance, adapted to the present inventory (review M4).  With the cap component replaced by the two
    k/12 capR reports marked OK by hand (in memory; files untouched), the cap gaps are [1/2, 11/12) and (13/12, 3/2];
    case1 and local are covered (they are certified on all of [1/2, 3/2] today); the slab verdicts are exactly those
    of the run with the real cap reports (injecting cap pieces must not change any cell check: the expectation is
    computed from the present inventory, not hard-coded); tau_compat: none with the exact cover2q files (default),
    none with the legacy float files read as decimals (spec), and on [11/12, 13/12] with the legacy files read as
    binary floats.  Freshness is off here: the test is about parsing and the coverage engine, not about the reports'
    age (that is tested in selftest_auth).  If the two k/12 reports are absent the cap part is reported as SKIP."""
    res = []
    files = [os.path.join(HERE, "capR", "pieces", f) for f in ("check_capR_11_12__1_1.txt", "check_capR_1_1__13_12.txt")]
    if not all(os.path.exists(f) for f in files):
        return [("acceptance: SKIP (capR k/12 piece reports absent)", True)]
    import copy
    legacy = sorted(glob.glob(os.path.join(HERE, "localS", "cover2_*_tau*.jsonl")))
    if not glob.glob(os.path.join(HERE, "localS", "cover2q_*_tau*.jsonl")):
        res.append(("acceptance: exact cover2q files present", False))
    for reading in ("exact", "decimal", "binary"):
        if reading != "exact" and not legacy:
            res.append((f"acceptance ({reading} tau): SKIP (no legacy cover2 files)", True)); continue
        o = copy.copy(opts); o.route = "local"; o.no_json = True; o.no_freshness = True; o.recheck = False
        o.local_endpoints = "decimal"; o.cap_dir = None; o.local_legacy = False
        o.tau_reading = "binary" if reading == "exact" else reading
        o.local_file = None if reading == "exact" else legacy
        _, r0, _, _ = run(o, quiet=True)                     # the real inventory (cap included)
        cap = []
        for f in files:
            txt = open(f).read()
            txt = txt.replace('"P_ok": false', '"P_ok": true').replace('"PIECE_OK": false', '"PIECE_OK": true')
            txt = txt.replace("\nPIECE_FAIL", "\nPIECE_OK")
            cap.append(cap_piece_from_text(txt, f, 0, o, time.time()))
        ok, r, _, _ = run(o, quiet=True, inject_cap=cap)
        capg = [fmt_gap(g) for g, _ in r["cap"]]
        res.append((f"acceptance ({reading} tau): cap gaps {capg} == ['[1/2, 11/12)', '(13/12, 3/2]']",
                    capg == ["[1/2, 11/12)", "(13/12, 3/2]"]))
        res.append((f"acceptance ({reading} tau): case1 and local covered", not r["case1"] and not r["local"]))
        tc = [fmt_gap(g) for g, _ in r["tau_compat"]]
        want = ["[11/12, 13/12]"] if reading == "binary" else []
        res.append((f"acceptance ({reading} tau): tau_compat gaps {tc} == {want}", tc == want))
        for c in ("slabs", "slab_tiling"):
            g0, g1 = [fmt_gap(g) for g, _ in r0[c]], [fmt_gap(g) for g, _ in r[c]]
            res.append((f"acceptance ({reading} tau): {c} gaps {g1} == present inventory {g0}", g0 == g1))
        res.append((f"acceptance ({reading} tau): not RANGE_OK", not ok))
    return res


def selftest_auth():
    """S1: the sha256 freshness rule on synthetic files (scratch directory; no project file is touched):
    matching hashes -> fresh; changed checker, changed input, missing input record, no provenance -> stale / fallback."""
    import tempfile
    res = []
    with tempfile.TemporaryDirectory() as d:
        chk = os.path.join(d, "check_capR.py"); inp = os.path.join(d, "node_a.json")
        open(chk, "w").write("# checker v1\n"); open(inp, "w").write('{"s": "1"}\n')
        saved = SCRIPTS["check_capR"]
        SCRIPTS["check_capR"] = [chk]
        try:
            def prov():
                return dict(checker="check_capR.py", checker_sha256=sha256(chk),
                            inputs=[dict(name="node_a.json", sha256=sha256(inp))])
            P = Piece("cap", "synthetic", 0, "check_capR")
            res.append(("auth: matching sha256 -> fresh", hash_auth(P, prov(), [inp], "check_capR") and not P.problems))
            pv = prov()
            open(chk, "w").write("# checker v2\n")
            P = Piece("cap", "synthetic", 0, "check_capR")
            res.append(("auth: changed checker -> stale", hash_auth(P, pv, [inp], "check_capR") and
                        any("checker" in q for q in P.problems)))
            pv = prov()
            open(inp, "w").write('{"s": "2"}\n')
            P = Piece("cap", "synthetic", 0, "check_capR")
            res.append(("auth: changed input -> stale", hash_auth(P, pv, [inp], "check_capR") and
                        any("input" in q for q in P.problems)))
            pv = prov(); pv["inputs"] = []
            P = Piece("cap", "synthetic", 0, "check_capR")
            res.append(("auth: unrecorded input -> stale", hash_auth(P, pv, [inp], "check_capR") and P.problems))
            P = Piece("cap", "synthetic", 0, "check_capR")
            res.append(("auth: no provenance -> undecided (mtime fallback)", not hash_auth(P, None, [inp], "check_capR")))
            class O: no_freshness = False
            P = Piece("cap", "synthetic", 0, "check_capR")
            authenticate(P, None, time.time() + 100, 0, [inp], "check_capR", opts=O())
            res.append(("auth: fallback is flagged", P.info.get("auth") == "mtime-fallback" and
                        P.fresh.startswith("mtime fallback")))
        finally:
            SCRIPTS["check_capR"] = saved
    return res


def selftest_review_ext(opts):
    """review_ext M2-M4 (2026-11-07), with negative controls.  Synthetic files live in a temporary directory; project
    files are only read.  M2: cover2q call vs record / file-name tau (a renamed tau file must fail the run), cap argv vs
    a, b, tau.  M3: range_check.py sha256 and versions in the JSON, WARN (not FAIL) on change.  M4: --recheck-new skips
    only pieces the baseline marks used + rechecked with an identical report (a listed but not rechecked piece is
    re-run; a legacy baseline skips nothing)."""
    import copy, tempfile
    res = []
    real_local = sorted(glob.glob(os.path.join(HERE, "localS", "cover2q_*_tau*.jsonl")))
    lsha = sha256(SCRIPTS["check_localS"][0])

    def lrec(s0="1/2", s1="3/2", tau="1/1000000", exact=True, prov=True, piece=("1/2", "3/2")):
        R = dict(piece=list(piece), eps=1e-9, lambda_S=0.1, G=0.05, LOCAL_OK=True)
        if prov:
            R["provenance"] = dict(checker="check_localS.py", checker_sha256=lsha, inputs=[], python="3.9.6",
                                   flint="0.6.0", call=dict(function="check_localS.check_piece", s0=s0, s1=s1,
                                                            tau=tau, exact=exact))
        return R

    def lopts(files):
        o = copy.copy(opts); o.local_file = files; o.local_legacy = False; o.no_freshness = False
        o.tau_reading = "binary"; o.local_endpoints = "decimal"
        return o

    with tempfile.TemporaryDirectory() as d:
        def wfile(sub, name, R):
            os.makedirs(os.path.join(d, sub), exist_ok=True)
            p = os.path.join(d, sub, name)
            with open(p, "w") as f:
                f.write(json.dumps(R) + "\n")
            return p
        name = "cover2q_1o2_3o2_tau1e-6.jsonl"
        good = wfile("good", name, lrec())
        ren = wfile("ren", "cover2q_1o2_3o2_tau1e-5.jsonl", lrec())      # produced at 1e-6, renamed to 1e-5
        nonex = wfile("nonexact", name, lrec(exact=False))
        badend = wfile("badend", name, lrec(s1="7/5"))
        noprov = wfile("noprov", name, lrec(prov=False))
        w = []
        P = collect_local(lopts([good]), w)[0]
        res.append(("M2 local: call matches record and file-name tau -> used", P.used and not P.info.get("prov_mismatch")))
        P = collect_local(lopts([ren]), w)[0]
        res.append(("M2 local (negative control): tau file renamed 1e-6 -> 1e-5 -> provenance mismatch, dropped",
                    not P.used and "call.tau" in (P.info.get("prov_mismatch") or "")))
        P = collect_local(lopts([nonex]), w)[0]
        res.append(("M2 local (negative control): call.exact false -> mismatch, dropped",
                    not P.used and "call.exact" in (P.info.get("prov_mismatch") or "")))
        P = collect_local(lopts([badend]), w)[0]
        res.append(("M2 local (negative control): call.s1 != record endpoint -> mismatch, dropped",
                    not P.used and "call.s1" in (P.info.get("prov_mismatch") or "")))
        P = collect_local(lopts([noprov]), w)[0]
        res.append(("M2 local: record without provenance.call -> dropped (no mismatch claimed)",
                    not P.used and not P.info.get("prov_mismatch")))
        # run level: the real files cover; adding the renamed file must turn RANGE_OK into RANGE_FAIL
        o = lopts(real_local); o.route = "local"; o.no_json = True; o.recheck = False; o.cap_dir = None
        o.range = ["1/2", "3/2"]
        ok0, _, _, L0 = run(o, quiet=True)
        o2 = copy.copy(o); o2.local_file = real_local + [ren]
        ok1, _, _, L1 = run(o2, quiet=True)
        res.append(("M2 run: real cover2q files -> RANGE_OK", ok0 and L0[-1].startswith("RANGE_OK")))
        res.append(("M2 run (negative control): + renamed tau file -> PROVENANCE_MISMATCH and RANGE_FAIL although "
                    "covered", not ok1 and L1[-1] == "RANGE_FAIL" and any(x.startswith("PROVENANCE_MISMATCH local")
                                                                         for x in L1)
                    and not any(x.startswith("UNCOVERED") for x in L1)))

        # cap argv cross-check on a real report (parsed and re-dumped in memory)
        f = os.path.join(HERE, "capR", "pieces", "check_capR_1_3__3_8.txt")
        if os.path.exists(f):
            m = CAP_JSON.search(open(f).read())
            J = json.loads(m.group(1))
            def cap_with(J2):
                return cap_piece_from_text(json.dumps(J2, indent=1) + "\nPIECE_OK\n", f, 0, lopts(None), time.time())
            P = cap_with(J)
            res.append(("M2 cap: argv matches a, b, TAU_DEN -> used", P.used and not P.info.get("prov_mismatch")))
            J2 = copy.deepcopy(J); i0 = [i for i, x in enumerate(J2["provenance"]["argv"])
                                         if x.endswith("check_capR.py")][0]
            J2["provenance"]["argv"][i0 + 5] = "2/5"
            P = cap_with(J2)
            res.append(("M2 cap (negative control): argv b = 2/5 vs report b = 3/8 -> mismatch, dropped",
                        not P.used and "called with s in" in (P.info.get("prov_mismatch") or "")))
            J3 = copy.deepcopy(J); J3["provenance"]["argv"][i0 + 7] = "250000"
            P = cap_with(J3)
            res.append(("M2 cap (negative control): argv TAU_DEN 250000 vs tau 1/1000000 -> mismatch, dropped",
                        not P.used and "TAU_DEN" in (P.info.get("prov_mismatch") or "")))
        else:
            res.append(("M2 cap: SKIP (capR/pieces/check_capR_1_3__3_8.txt absent)", True))

        # M3: own sha256 and versions in the JSON; WARN on change, not FAIL
        me = self_info()
        res.append(("M3: self_info sha256 == sha256(range_check.py), python version recorded",
                    me["sha256"] == sha256(os.path.abspath(__file__)) and bool(me["python"])))
        jo = os.path.join(d, "rc.json")
        o3 = copy.copy(o); o3.no_json = False; o3.json_out = jo
        ok2, _, _, L2 = run(o3, quiet=True)
        J = json.load(open(jo))
        res.append(("M3: JSON records range_check sha256 / python / flint and report versions",
                    J.get("range_check", {}).get("sha256") == me["sha256"] and J["range_check"].get("python")
                    == me["python"] and sum((J.get("report_versions") or {}).values()) ==
                    J["authentication"]["sha256"] + J["authentication"]["mtime_fallback"]))
        res.append(("M3: NOTE line with the full sha256 printed", any(x.startswith("NOTE range_check.py sha256 "
                                                                                 + me["sha256"]) for x in L2)))
        ok3, _, _, L3 = run(o3, quiet=True)
        res.append(("M3: unchanged since previous JSON -> NOTE, no WARN",
                    ok3 and any("unchanged since the previous run" in x for x in L3 if x.startswith("NOTE range_check"))
                    and not any(x.startswith("WARN range_check.py") for x in L3)))
        J["range_check"]["sha256"] = "0" * 64; J["range_check"]["flint"] = "0.0.0"
        J["report_versions"] = {"python 3.9.6, python-flint 0.5.0": 1}
        json.dump(J, open(jo, "w"))
        ok4, _, _, L4 = run(o3, quiet=True)
        res.append(("M3 (negative control): changed range_check sha256 / flint / report versions -> three WARN lines, "
                    "run still RANGE_OK", ok4 and any(x.startswith("WARN range_check.py changed") for x in L4)
                    and any(x.startswith("WARN python-flint version") for x in L4)
                    and any(x.startswith("WARN versions recorded by the used reports") for x in L4)))

        # M4: skip set of --recheck-new
        def mk(i, sha="s"):
            P = Piece("local", os.path.join(HERE, f"synthetic_{i}.jsonl"), 1, "check_localS")
            P.a, P.b = Fr(i), Fr(i + 1); P.ok_claim = True; P.info["report_sha256"] = sha + str(i)
            return P
        ps = [mk(i) for i in range(5)]
        def ent(P, **kw):
            q = dict(source=rel(P.src), record=P.idx, a=str(P.a), b=str(P.b), used=True, rechecked="T",
                     report_sha256=P.info["report_sha256"]); q.update(kw); return q
        base = dict(piece_recheck_status=True, pieces=[ent(ps[0]), ent(ps[1], rechecked=None),
                                                        ent(ps[2], report_sha256="other"), ent(ps[3], used=False)])
        todo = run_recheck(ps, base, dry_run=True)
        res.append(("M4: used + rechecked + identical report in the baseline -> skipped", ps[0] not in todo))
        res.append(("M4 (negative control): baseline lists the piece but did not recheck it -> re-run", ps[1] in todo))
        res.append(("M4 (negative control): rechecked in the baseline but report changed since -> re-run", ps[2] in todo))
        res.append(("M4 (negative control): listed but not used in the baseline -> re-run", ps[3] in todo))
        res.append(("M4: not listed -> re-run", ps[4] in todo))
        legacy = dict(pieces=[ent(P) for P in ps])
        legacy["pieces"] = [{k: v for k, v in q.items() if k not in ("rechecked", "report_sha256")}
                            for q in legacy["pieces"]]
        res.append(("M4 (negative control): legacy baseline without per-piece recheck status -> nothing skipped",
                    run_recheck(ps, legacy, dry_run=True) == ps))
        for P in ps:
            P.info["rechecked"] = None
        n = carry_rechecked(ps, base)
        res.append(("M4: recheck status carried forward only for the identical, rechecked report",
                    n == 1 and ps[0].info["rechecked"] == "T" and all(P.info["rechecked"] is None for P in ps[1:])))
    return res


def selftest_rerun():
    """heavy (through heavy_lock.py): re-run one stored cell piece and one stored local piece, compare."""
    res = []
    f = os.path.join(CELLS_DIR, "logs", "check_piece_case1.txt")
    recs, _ = json_records(f)
    if recs:
        rep = recs[0][1]
        certs = [resolve_cert(n)[0] for n in rep["certs"]]
        rc, out = heavy(["python3", "check_piece.py"] + certs, CELLS_DIR)
        res.append((f"rerun check_piece {rep['s_range']}: PIECE_OK as stored", ('"PIECE_OK": true' in out) ==
                    (rep["PIECE_OK"] is True)))
    f = os.path.join(HERE, "localS", "cover2q_1o2_3o2_tau1e-6.jsonl")
    recs, _ = json_records(f, parse_float=str) if os.path.exists(f) else ([], [])
    if recs:
        R = recs[0][1]
        lo, hi = R["piece"]
        code = ("import json, check_localS as L; from fractions import Fraction as F; "
                f"print(json.dumps(L.check_piece(F('{lo}'), F('{hi}'), F(1, 10**6))))")
        rc, out = heavy(["python3", "-c", code], os.path.join(HERE, "localS"))
        res.append((f"rerun check_localS piece [{lo}, {hi}]: LOCAL_OK and lambda_S as stored",
                    '"LOCAL_OK": true' in out and str(R["lambda_S"]) in out))
    return res


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--range", nargs=2, default=["1/2", "3/2"])
    ap.add_argument("--route", choices=["local", "exact"], default="local")
    ap.add_argument("--cell-report", action="append")
    ap.add_argument("--cap-dir", action="append")
    ap.add_argument("--local-file", action="append")
    ap.add_argument("--local-legacy", action="store_true",
                    help="also read the float cover2_*.jsonl files (default: only exact cover2q_*.jsonl)")
    ap.add_argument("--no-freshness", action="store_true")
    ap.add_argument("--tau-reading", choices=["binary", "decimal"], default="binary",
                    help="legacy cover2 files only: tau as the binary float check_localS multiplied with "
                         "(default, sound) or the decimal of the file name (spec C3 reading)")
    ap.add_argument("--local-endpoints", choices=["decimal", "binary", "strict"], default="decimal",
                    help="legacy cover2 files only: endpoints decimal (spec C7), binary, or strict = intersection")
    ap.add_argument("--json-out", default=os.path.join(HERE, "range_check.json"))
    ap.add_argument("--no-json", action="store_true")
    ap.add_argument("--recheck", action="store_true", help="HEAVY: re-run every used piece via heavy_lock.py")
    ap.add_argument("--recheck-new", metavar="BASELINE_JSON", default=None,
                    help="with --recheck: skip the pieces this range_check.json records as used and rechecked "
                         "with a report identical to the current one; re-run all others (a baseline without "
                         "per-piece recheck status skips nothing)")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--selftest-rerun", action="store_true", help="HEAVY: re-run one cell and one local piece")
    opts = ap.parse_args(argv)
    if opts.selftest or opts.selftest_rerun:
        t0 = time.time()
        tests = []
        if opts.selftest:
            tests += selftest_engine()
            tests += selftest_S0()
            tests += selftest_auth()
            tests += selftest_acceptance(opts)
            tests += selftest_review_ext(opts)
        if opts.selftest_rerun:
            tests += selftest_rerun()
        for name, ok in tests:
            print(f"{'ok  ' if ok else 'FAIL'} {name}")
        allok = all(ok for _, ok in tests)
        print(f"SELFTEST_{'OK' if allok else 'FAIL'} ({len(tests)} tests, {time.time() - t0:.1f} s)")
        return 0 if allok else 1
    ok, _, _, _ = run(opts)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
