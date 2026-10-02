#!/usr/bin/env python3
"""emit_cert3.py -- log kernel, Case 1: exact JSON certificate -> upstream `Cert3` Lean data + chunked checks.

usage (from anywhere; always `nice -n 19`, OMP_NUM_THREADS=1):
  python3 emit_cert3.py <cert_case1_riesz2.json> [--pack hex|lists] [--outdir DIR] [--budget BYTES]
  python3 emit_cert3.py --check [--outdir DIR] [--json <cert.json>]   # re-read the EMITTED .lean files, re-run
                                                                       # every Lean Bool check in Python
  python3 emit_cert3.py --selftest-upstream <ThomsonGen dir>          # simulator vs upstream Case1 literals

Output (default DIR = lean/LogN7/Case1 of this worktree), mirroring upstream's Case 1 chunking
(Case1Data / Case1Stat / Case1ChkF / Case1ChkS03 / Case1ChkS47 / Case1):
  Data.lean    `LogN7.Case1Data.cf : ThomsonN7.Cert.Cert3` (+ `h_`, `lam_`, `eps_`, blocks `F0..`, `S0..`)
  Stat.lean    reuses the data-independent `ThomsonN7.Case1.c1Stat` machinery of upstream `Case1Stat`
  ChkF.lean    `c1Stat w D (hE cf.h) = lit`, `c1Stat w D (c1FtotK cf.n (fkE (cf.m k) (cf.blk k) k)) = lit`
  ChkS03.lean  `c1Stat w D (sblkE cf.an cf.ad S_i) = lit`, i = 0..3        (one `decide +kernel` each)
  ChkS47.lean  i = 4..7
  Check.lean   composition (`c1Stat_idE`), `chk`, `Blk.ok` of all blocks, `cf.check = true`
  Claim.lean   application of `ThomsonGen.case1Claim_of_threePoint_cut` (1-D hypothesis `hH` and E(P) = 41/4
               left as named hypotheses: proved in other modules)

Semantics of the JSON (numerics/riesz2/check_cell2.py, ../cells/check_cell.py):
  slack(u,v,t) = (H(u)+H(v)+H(t))/3 - e/21 - Σ_k <F_k, R_k(u,v,t)>  ==  Σ_r g_r(u,v,t) z_r^T B_r z_r,
  z_r = monos_upto(d_r).  Upstream `Cert3` with common denominator Λ: h = ΛH, eps = Λe, F_k = ent_k/Λ, and an SOS
  block with multiplier code list `g` contributes codeE(g)·z^T (ent/Λ) z.  Our g_r = codeE(g)/c_r (c_r = ad = 10 for
  the cut multipliers u-a, v-a, t-a, else 1), so ent_r = Λ·B_r/c_r.  Λ = lcm of all denominators · 2^s.
"""
from decimal import Decimal as _Dec, getcontext as _gc
import argparse, hashlib, itertools, json, os, sys, time
from fractions import Fraction as Fr
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cert3_util as U
import cert3_parse as P

WT = os.path.abspath(os.path.join(HERE, "..", ".."))                 # worktree root
DEF_OUT = os.path.join(WT, "lean", "LogN7", "Case1")
_gc().prec = 60
# rational upper bound for E(P) = -(6 log 2 + 5/2 log 5) (log kernel), 1e-40 above the true value
EP_HI = Fr(str((-(6 * _Dec(2).ln() + _Dec(5) / 2 * _Dec(5).ln())).quantize(_Dec(10) ** -45))) + Fr(1, 10 ** 40)
NUMERICS = os.environ.get("THOMSON_NUMERICS", "numerics")  # development tree: numerics/cells, numerics/hp
T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:6.1f}s]", *a, flush=True)


# ------------------------------------------------------------------ exact polynomial of an Ex (for the code table)
def expand(e):
    """Collected polynomial {(a,b,d): int} of an Ex tree (no sbst)."""
    tg = e[0]
    if tg == U.C:
        return {(0, 0, 0): e[1]} if e[1] else {}
    if tg == U.MON:
        return {(e[1], e[2], e[3]): 1}
    p, q = expand(e[1]), expand(e[2])
    r = {}
    if tg == U.ADD:
        for k, v in list(p.items()) + list(q.items()):
            r[k] = r.get(k, 0) + v
    else:
        for k1, v1 in p.items():
            for k2, v2 in q.items():
                k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v}


def code_of(g, an, ad):
    """(code list, c) with codeE(code list) == c * g exactly (c > 0 rational); upstream codes 0..12 and []."""
    cands = [[]] + [[k] for k in range(13)]
    for cl in cands:
        pe = expand(U.gE(an, ad, cl))
        if set(pe) != set(g):
            continue
        ratios = {Fr(pe[k]) / g[k] for k in g}
        if len(ratios) == 1:
            cst = ratios.pop()
            if cst > 0:
                return cl, cst
    return None, None


def monos_upto(d):          # == numerics/hp/check_cert.monos_upto
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


CODE_NAMES = {(): "1", (0,): "1-u^2", (1,): "1-v^2", (2,): "1-t^2", (3,): "detG = 1+2uvt-u^2-v^2-t^2",
              (4,): "1-u", (5,): "1+u", (6,): "1-v", (7,): "1+v", (8,): "1-t", (9,): "1+t",
              (10,): "ad*u-an", (11,): "ad*v-an", (12,): "ad*t-an"}


# ------------------------------------------------------------------ JSON -> integer Cert3
def exact_int(q):
    assert q.denominator == 1, "Λ does not clear a denominator"
    return q.numerator


def build(J, s_start=0, s_step=8, s_max=160, theta=Fr(1, 2)):
    assert J["kind"] == "case1" and J["kernel"] == "log"
    a = Fr(J["cell"]["a"])
    an, ad = a.numerator, a.denominator
    H = [Fr(x) for x in J["H"]]
    e = Fr(J["e"])
    Fs = [[[Fr(x) for x in row] for row in M] for M in J["F"]]
    blocks = J["SOS"]["S"]
    table = []
    Bs = []
    for blk in blocks:
        g = {tuple(int(x) for x in k.split(",")): Fr(v) for k, v in blk["g"].items()}
        cl, cst = code_of(g, an, ad)
        if cl is None:
            raise SystemExit(f"multiplier {blk['g']} (mult_index {blk['mult_index']}) is not an upstream code")
        z = monos_upto(blk["d"])
        B = [[Fr(x) for x in row] for row in blk["B"]]
        assert len(B) == len(z)
        Bs.append((cl, cst, z, [[x / cst for x in row] for row in B]))
        table.append(dict(mult_index=blk["mult_index"], g=blk["g"], d=blk["d"], size=len(z), codes=cl, c=str(cst),
                          name=CODE_NAMES[tuple(cl)]))
    L0 = 1
    for x in H + [e] + [x for M in Fs for row in M for x in row] + [x for (_, _, _, B) in Bs for row in B for x in row]:
        L0 = lcm(L0, x.denominator)
    s = s_start
    while True:
        Lam = L0 << s
        log(f"trying Λ = Λ0·2^{s} (Λ0 = {L0}, {Lam.bit_length()} bits)")
        good = True
        Fb, Sb, infos = [], [], []
        for k, M in enumerate(Fs):
            Mi = [[exact_int(x * Lam) for x in row] for row in M]
            b, info = U.pack_psd(Mi, theta)
            infos.append((f"F{k}", info))
            if b is None or not info["ok"]:
                good = False
                break
            Fb.append(b)
        if good:
            for i, (cl, cst, z, B) in enumerate(Bs):
                Mi = [[exact_int(x * Lam) for x in row] for row in B]
                b, info = U.pack_psd(Mi, theta)
                infos.append((f"S{i}", info))
                if b is None or not info["ok"]:
                    good = False
                    break
                Sb.append(U.SBlk(cl, 0, z, b))
        if good:
            break
        log(f"  packing failed at {infos[-1][0]}: {infos[-1][1].get('why', 'Δ not diagonally dominant')}")
        s += s_step
        if s > s_max:
            raise SystemExit("no Λ found")
    cf = U.Cert3(7, Lam, an, ad, [exact_int(x * Lam) for x in H], exact_int(e * Lam), Fb, Sb)
    assert Fr(cf.eps, Lam) == e
    meta = dict(L0=L0, s=s, theta=str(theta), table=table,
                pack={nm: {"eps_shift": str(inf["eps"]), "lmin_rel": inf["lmin_rel"], "dd_slack": str(inf["dd_slack"])}
                      for nm, inf in infos})
    return cf, meta


# ------------------------------------------------------------------ the Lean Bool checks, simulated
def simulate(cf, want_kev=True):
    """Blk.ok of every block, the piece statistics, the composition c1Stat_idE, chk.  Returns a report dict."""
    rep = {}
    rep["n_ge_3"] = 3 <= cf.n
    rep["Lam_pos"] = 0 < cf.Lam
    rep["ad_pos"] = 0 < cf.ad
    rep["F_ok"] = [cf.blk(k).ok(cf.m(k)) for k in range(cf.K)]
    rep["S_ok"] = [s.B.ok(len(s.z)) for s in cf.S]
    pcs = U.pieces(cf)
    lst = {nm: U.stat_l(e) for nm, _, e in pcs}
    zero = lambda nm: lst[nm] + (0,)
    tot = U.compose_idE(cf, zero("H"), [zero(f"F{k}") for k in range(cf.K)], [zero(f"S{i}") for i in range(len(cf.S))])
    w, D = U.chk_params(*tot[:4])
    rep["w"], rep["D"], rep["l1_total"] = w, D, tot[0]
    rep["pieces"] = {}
    if want_kev:
        st = {}
        for nm, _, e in pcs:
            st[nm] = lst[nm] + (U.kev(e, w, D),)
            rep["pieces"][nm] = st[nm]
        tot = U.compose_idE(cf, st["H"], [st[f"F{k}"] for k in range(cf.K)], [st[f"S{i}"] for i in range(len(cf.S))])
        rep["total"] = tot
        rep["kev_total_zero"] = tot[4] == 0
        rep["chk"] = (tot[4] == 0) and U.chk_params(*tot[:4]) == (w, D)
    rep["check"] = (rep["n_ge_3"] and rep["Lam_pos"] and rep["ad_pos"] and all(rep["F_ok"]) and all(rep["S_ok"])
                    and rep.get("chk", False))
    return rep


def rational_identity(cf, J=None):
    """Independent cross-check with the numerics' exact polynomial code: the rationals encoded by cf
    (H = h/Λ, e = eps/Λ, F_k = ent/Λ, block r: codeE(g_r) z^T (ent/Λ) z) satisfy the Case 1 identity exactly,
    all blocks are PD (Bareiss), e > E(P) = 41/4; and (if J is given) they coincide with the JSON rationals."""
    sys.path.insert(0, os.path.join(NUMERICS, "cells"))
    sys.path.insert(0, os.path.join(NUMERICS, "hp"))
    import check_cell as CK
    Lam = cf.Lam
    H = [Fr(x, Lam) for x in cf.h]
    e = Fr(cf.eps, Lam)
    Fs = [[[Fr(cf.blk(k).ent(cf.m(k), a, b), Lam) for b in range(cf.m(k))] for a in range(cf.m(k))]
          for k in range(cf.K)]
    sl, _ = CK.case1_slack(H, e, Fs)
    rhs = {}
    pd = True
    same = True
    for i, s in enumerate(cf.S):
        r = len(s.z)
        B = [[Fr(s.B.ent(r, a, b), Lam) for b in range(r)] for a in range(r)]
        g = {k: Fr(v) for k, v in expand(U.gE(cf.an, cf.ad, s.g)).items()}
        pd &= CK.bareiss_pd(B)[0]
        rhs = CK.P_add(rhs, CK.P_mul(g, CK.gram_poly(B, [tuple(z) for z in s.z])))
        if J is not None:
            blk = J["SOS"]["S"][i]
            gj = {tuple(int(x) for x in kk.split(",")): Fr(v) for kk, v in blk["g"].items()}
            cl, cst = code_of(gj, cf.an, cf.ad)
            same &= (cl == s.g) and [[x / cst for x in row] for row in CK.Fmat(blk["B"])] == B \
                and [tuple(z) for z in s.z] == monos_upto(blk["d"])
    for F in Fs:
        pd &= CK.bareiss_pd(F)[0]
    diff = CK.P_add(sl, rhs, -1)
    out = dict(identity_exact=not diff, all_pd=pd, e_gt_EP=e > EP_HI, e_minus_EP=str(float(e - EP_HI)))
    if J is not None:
        same &= H == [Fr(x) for x in J["H"]] and e == Fr(J["e"]) and Fs == [CK.Fmat(M) for M in J["F"]]
        out["equals_json"] = bool(same)
    return out


# ------------------------------------------------------------------ Lean emission
HDR = "/-! {what}\n\nGenerated by `lean/gen_log/emit_cert3.py` from `{src}`\n(sha256 {sha}).  Do not edit; regenerate. -/\n"


def blk_lean(name, b, r, pack):
    if pack == "lists":
        lines = [f"def {name}_d : List Int := {U.lint_list(b.d)}"]
        for q, col in enumerate(b.l):
            lines.append(f"def {name}_l_{q} : List Int := {U.lint_list(col)}")
        lines.append(f"def {name}_l : List (List Int) := [" + ", ".join(f"{name}_l_{q}" for q in range(len(b.l))) + "]")
        for q, row in enumerate(b.D):
            lines.append(f"def {name}_D_{q} : List Int := {U.lint_list(row)}")
        lines.append(f"def {name}_D : List (List Int) := [" + ", ".join(f"{name}_D_{q}" for q in range(len(b.D))) + "]")
        lines.append(f"def {name} : Blk := ⟨{name}_d, {name}_l, {name}_D⟩")
        return "\n".join(lines), None
    assert len(b.d) == r and len(b.l) == r and len(b.D) == r and all(len(x) == r for x in b.l + b.D)
    Bd = U.field_width(b.d)
    Bl = U.field_width([v for col in b.l for v in col])
    BD = U.field_width([v for row in b.D for v in row])
    xd, xl, xD = U.packI(Bd, b.d), U.packM(Bl, b.l), U.packM(BD, b.D)
    back = U.mkBlk(r, Bd, Bl, BD, xd, xl, xD)
    assert back.d == b.d and back.l == b.l and back.D == b.D, "mkBlk round trip"
    txt = f"def {name} : Blk := mkBlk {r} {Bd} {Bl} {BD}\n  {hex(xd)}\n  {hex(xl)}\n  {hex(xD)}"
    return txt, (Bd, Bl, BD, len(hex(xd)) + len(hex(xl)) + len(hex(xD)))


def emit(cf, meta, rep, src, sha, outdir, pack, budget):
    os.makedirs(outdir, exist_ok=True)
    w, D = rep["w"], rep["D"]
    files = {}
    # ---------------- Data.lean
    L = []
    L.append("import ThomsonGen.CertF" if pack == "hex" else "import ThomsonGen.Cert3")
    L.append(HDR.format(what="log kernel, Case 1 (all pair inner products `≥ -9/10`): the exact cut three-point "
                             "certificate\nin upstream's `ThomsonN7.Cert.Cert3` format (common denominator `Λ = lam_`).\n\n"
                             "* minorant: `H x = (∑_{j<11} h_j x^j) / lam_` = `cf.Hf x` = `LogN7.Minor.peval h_ x / lam_`;\n"
                             "* margin: `eps_ / lam_ = e`, `e - logEnergy pentBipyramid > 0`;\n"
                             "* `F0..F3`: kernel blocks, `F_k = ent_k / lam_`, `ent = ∑_q d_q l_q l_qᵀ + Δ` (`Δ` diagonally dominant);\n"
                             "* `S0..S7`: SOS blocks (multiplier codes of `Cert.codeE`, identity permutation, basis `z`).\n"
                             + ("Blocks are packed by `ThomsonN7.Cert.mkBlk` (offset-binary fields, least significant first)."
                                if pack == "hex" else "Blocks are plain integer lists (upstream `Case1Data` format)."),
                        src=src, sha=sha))
    L.append("namespace LogN7")
    L.append("namespace Case1Data")
    L.append("open ThomsonN7.Cert\n")
    L.append(f"def h_ : List Int := {U.lint_list(cf.h)}")
    L.append(f"def lam_ : Nat := {cf.Lam}")
    L.append(f"def eps_ : Int := {U.lint(cf.eps)}")
    packinfo = {}
    for k, b in enumerate(cf.F):
        t, pi = blk_lean(f"F{k}", b, cf.m(k), pack)
        L.append(t)
        packinfo[f"F{k}"] = pi
    for i, s in enumerate(cf.S):
        L.append(f"def S{i}_z : List (Nat × Nat × Nat) := {U.lz_list(s.z)}")
        t, pi = blk_lean(f"S{i}_B", s.B, len(s.z), pack)
        L.append(t)
        packinfo[f"S{i}"] = pi
        g = "[" + ", ".join(U.lnat(x) for x in s.g) + "]"
        L.append(f"def S{i} : SBlk := ⟨{g}, {U.lnat(s.sigma)}, S{i}_z, S{i}_B⟩")
    L.append("def cf : Cert3 :=")
    L.append(f"  {{ n := {U.lnat(cf.n)}, Lam := lam_, an := {U.lint(cf.an)}, ad := {U.lnat(cf.ad)}, h := h_, eps := eps_,")
    L.append("    F := [" + ", ".join(f"F{k}" for k in range(cf.K)) + "],")
    L.append("    S := [" + ", ".join(f"S{i}" for i in range(len(cf.S))) + "] }")
    L.append("\nend Case1Data")
    L.append("end LogN7\n")
    files["Data.lean"] = "\n".join(L)
    # ---------------- Stat.lean
    files["Stat.lean"] = "\n".join([
        "import ThomsonGen.Case1Stat",
        "import LogN7.Case1.Data",
        HDR.format(what="log kernel, Case 1: statistics machinery for the chunked Kronecker check.\n\n"
                        "Upstream's `ThomsonN7.Case1.c1Stat` (one structural pass computing `(ℓ¹, deg u, deg v, deg t, kev)`),\n"
                        "`c1Stat_eq`, `c1FtotK` and the composition lemma `c1Stat_idE` (module `ThomsonGen.Case1Stat`) are\n"
                        "data-independent (they import only `Cert3`) and are reused verbatim.  For this certificate the\n"
                        f"Kronecker parameters of `Cert.chk` are `w = Nat.log2 ℓ¹ + 1 = {w}` and `D = max deg + 1 = {D}`.",
                   src=src, sha=sha)])
    # ---------------- chunks
    stats = rep["pieces"]
    stmt = {}
    stmt["H"] = f"ThomsonN7.Case1.c1Stat {w} {D} (hE LogN7.Case1Data.cf.h)"
    for k in range(cf.K):
        stmt[f"F{k}"] = (f"ThomsonN7.Case1.c1Stat {w} {D} (ThomsonN7.Case1.c1FtotK LogN7.Case1Data.cf.n "
                         f"(fkE (LogN7.Case1Data.cf.m {k}) (LogN7.Case1Data.cf.blk {k}) {k}))")
    for i in range(len(cf.S)):
        stmt[f"S{i}"] = (f"ThomsonN7.Case1.c1Stat {w} {D} (sblkE LogN7.Case1Data.cf.an LogN7.Case1Data.cf.ad "
                         f"LogN7.Case1Data.S{i})")
    thm = {nm: f"theorem r2c1_stat_{nm} :\n    {stmt[nm]} = {U.stat_lit(stats[nm])} := by\n  decide +kernel\n"
           for nm in stmt}
    head = lambda what: "\n".join(["import LogN7.Case1.Stat", HDR.format(what=what, src=src, sha=sha),
                                   "namespace LogN7", "namespace Case1", "open ThomsonN7.Cert ThomsonN7.Cert.Cert3\n"])
    tail = "end Case1\nend LogN7\n"
    # log port: finer groups (upstream-shaped ChkS03 reached 9.45 GB for Riesz2; HARD cap 9 GB)
    groups = [("ChkF", ["H"] + [f"F{k}" for k in range(cf.K)]), ("ChkS0", ["S0"]),
              ("ChkS13", [f"S{i}" for i in range(1, 4)]), ("ChkS47", [f"S{i}" for i in range(4, len(cf.S))])]
    sizes = {g: sum(len(thm[nm]) for nm in nms) for g, nms in groups}
    if max(sizes.values()) > budget:                      # fall back to greedy chunks under the byte budget
        order = list(stmt)
        groups, cur, acc = [], [], 0
        for nm in order:
            if cur and acc + len(thm[nm]) > budget:
                groups.append((f"ChkP{len(groups)}", cur)); cur, acc = [], 0
            cur.append(nm); acc += len(thm[nm])
        groups.append((f"ChkP{len(groups)}", cur))
    for g, nms in groups:
        files[f"{g}.lean"] = head(f"log kernel, Case 1: Kronecker statistics of the pieces {', '.join(nms)}\n"
                                  f"(`w = {w}`, `D = {D}`), one `decide +kernel` per declaration.") + \
            "\n".join(thm[nm] for nm in nms) + "\n" + tail
    # ---------------- Check.lean
    tot = rep["total"]
    pieces_rw = ", ".join(f"r2c1_stat_{nm}" for nm in stmt)
    Slist = ", ".join(f"LogN7.Case1Data.S{i}" for i in range(len(cf.S)))
    rng = ", ".join(str(k) for k in range(cf.K))
    chk = "\n".join([
        "\n".join(f"import LogN7.Case1.{g}" for g, _ in groups),
        HDR.format(what="log kernel, Case 1: assembly of the chunked check (mirrors upstream `Case1.lean`, first half).\n"
                        f"`LogN7.Case1Data.cf.check = true`: all blocks `Blk.ok`, and `chk cf.idE` with ℓ¹ < 2^{w}, degrees < {D},\n"
                        "Kronecker value 0 (soundness: `Kron.Ex.ev_eq_zero_of_kev`).", src=src, sha=sha),
        "namespace LogN7", "namespace Case1", "open ThomsonN7.Cert ThomsonN7.Cert.Cert3\n",
        f"theorem r2c1_K : LogN7.Case1Data.cf.K = {cf.K} := rfl\n",
        f"theorem r2c1_S : LogN7.Case1Data.cf.S = [{Slist}] := rfl\n",
        f"theorem r2c1_range : List.range {cf.K} = [{rng}] := rfl\n",
        f"/-- The statistics of the whole identity expression: `ℓ¹`-norm below `2 ^ {w}`, degrees "
        f"`{tot[1]}, {tot[2]}, {tot[3]}`, Kronecker value `0`. -/",
        f"theorem r2c1_idE_stat : ThomsonN7.Case1.c1Stat {w} {D} LogN7.Case1Data.cf.idE = "
        f"({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int)) := by",
        "  rw [ThomsonN7.Case1.c1Stat_idE, r2c1_K, r2c1_S, r2c1_range]",
        "  simp only [List.map_cons, List.map_nil]",
        f"  rw [{pieces_rw}]",
        "  decide +kernel\n",
        "/-- The Kronecker check of the identity expression. -/",
        "theorem r2c1_cf_chk : chk LogN7.Case1Data.cf.idE = true := by",
        f"  have h := ThomsonN7.Case1.c1Stat_eq {w} {D} LogN7.Case1Data.cf.idE",
        "  rw [r2c1_idE_stat] at h",
        "  simp only [Prod.mk.injEq] at h",
        "  obtain ⟨hl, hx, hy, hz, hk⟩ := h",
        "  unfold chk",
        "  rw [← hl, ← hx, ← hy, ← hz]",
        f"  have hW : Nat.log2 {tot[0]} + 1 = {w} := by decide +kernel",
        f"  have hD : max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {D} := by decide +kernel",
        "  rw [hW, hD]",
        "  exact decide_eq_true hk.symm\n",
        "/-- The positive-semidefiniteness certificates of the `F`-blocks (per block: `ChkBF`). -/",
        "theorem r2c1_cf_blocks :",
        "    (List.range LogN7.Case1Data.cf.K).all",
        "      (fun k => (LogN7.Case1Data.cf.blk k).ok (LogN7.Case1Data.cf.m k)) = true := by",
        f"  rw [r2c1_K, r2c1_range]; simp only [List.all_cons, List.all_nil, {', '.join(f'r2c1_blk_F{k}' for k in range(cf.K))}, Bool.and_self, Bool.and_true]\n",
        "/-- The positive-semidefiniteness certificates of the `S`-blocks (per block: `ChkBS0`, `ChkBS1`). -/",
        "theorem r2c1_cf_sos : LogN7.Case1Data.cf.S.all (fun s => s.B.ok s.z.length) = true := by",
        f"  rw [r2c1_S]; simp only [List.all_cons, List.all_nil, {', '.join(f'r2c1_blk_S{i}' for i in range(len(cf.S)))}, Bool.and_self, Bool.and_true]\n",
        "/-- The Case 1 certificate passes upstream's exact check. -/",
        "theorem r2c1_cf_ok : LogN7.Case1Data.cf.check = true := by",
        "  unfold Cert3.check",
        "  rw [r2c1_cf_chk, r2c1_cf_blocks, r2c1_cf_sos]",
        "  decide +kernel\n",
        "end Case1", "end LogN7\n"])
    files["Check.lean"] = chk.replace("\n".join(f"import LogN7.Case1.{g}" for g, _ in groups),
        "\n".join(f"import LogN7.Case1.{g}" for g, _ in groups) + "\nimport LogN7.Case1.ChkBF\nimport LogN7.Case1.ChkBS0\nimport LogN7.Case1.ChkBS1", 1)
    bhead = lambda what: "\n".join(["import LogN7.Case1.Data", HDR.format(what=what, src=src, sha=sha),
                                    "namespace LogN7", "namespace Case1", "open ThomsonN7.Cert ThomsonN7.Cert.Cert3\n"])
    fb = "\n".join(f"theorem r2c1_blk_F{k} : (LogN7.Case1Data.cf.blk {k}).ok (LogN7.Case1Data.cf.m {k}) = true := by\n  decide +kernel\n" for k in range(cf.K))
    sb = lambda i: f"theorem r2c1_blk_S{i} : LogN7.Case1Data.S{i}.B.ok LogN7.Case1Data.S{i}.z.length = true := by\n  decide +kernel\n"
    files["ChkBF.lean"] = bhead("log kernel, Case 1: `Blk.ok` of the F-blocks, one `decide +kernel` per block.") + fb + tail
    files["ChkBS0.lean"] = bhead("log kernel, Case 1: `Blk.ok` of the S-block S0.") + sb(0) + tail
    files["ChkBS1.lean"] = bhead("log kernel, Case 1: `Blk.ok` of the S-blocks S1..S7, one `decide +kernel` per block.") + \
        "\n".join(sb(i) for i in range(1, len(cf.S))) + tail
    pass  # Claim.lean is hand-written for the log port (LogN7/Case1/Claim.lean)
    for nm, txt in files.items():
        with open(os.path.join(outdir, nm), "w") as fh:
            fh.write(txt)
    return files, groups, packinfo


def claim_lean(cf, src, sha):
    return "\n".join([
        "import LogN7.Case1.Check",
        "import ThomsonGen.Generic.Glue",
        "import LogN7.MinorCore",
        HDR.format(what="log kernel, Case 1 claim from the exact cut three-point certificate (SKETCH, not yet built).\n\n"
                        "Applies `ThomsonGen.case1Claim_of_threePoint_cut` with `H = cf.Hf`, `η = eps/Λ - 41/4 > 0`,\n"
                        "`F = cf.Fm` (`fmat_psd` of the checked blocks) and `hpt` from `Cert3.hpt_cut`.  The two inputs\n"
                        "proved elsewhere are NAMED HYPOTHESES here:\n"
                        "* `hEP`: `pairEnergy phi2 pentBipyramid = 41/4` (statement module);\n"
                        "* `hH` : `H ≤ phi2` on `[-9/10, 1)` for `H t = LogN7.Minor.peval h_ t / lam_` — TODO: 1-D module\n"
                        "  (`LogN7.Minor.class_le_one` with `Hn = LogN7.Case1Data.h_`, `Hd = LogN7.Case1Data.lam_`).",
                   src=src, sha=sha),
        "open Real",
        "open scoped InnerProductSpace",
        "namespace LogN7",
        "namespace Case1",
        "open ThomsonN7.Cert ThomsonN7.Cert.Cert3\n",
        "/-- `LogN7.Minor.peval` is the monomial sum (proof verbatim from upstream `CutOneD.peval_eq_sum`). -/",
        "theorem r2_peval_eq_sum (Q : List ℤ) (x : ℝ) :",
        "    LogN7.Minor.peval Q x = ∑ j ∈ Finset.range Q.length, (Q.getD j 0 : ℝ) * x ^ j := by",
        "  induction Q with",
        "  | nil => simp [LogN7.Minor.peval]",
        "  | cons a as ih =>",
        "    rw [List.length_cons, Finset.sum_range_succ', LogN7.Minor.peval, ih, Finset.mul_sum]",
        "    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]",
        "    rw [add_comm]",
        "    congr 1",
        "    refine Finset.sum_congr rfl fun j _ => ?_",
        "    ring\n",
        "/-- `cf.Hf` is `peval cf.h / cf.Lam` (`cf.h = h_`, `cf.Lam = lam_` by `rfl`). -/",
        "theorem r2c1_Hf_eq (t : ℝ) :",
        "    LogN7.Case1Data.cf.Hf t",
        "      = LogN7.Minor.peval LogN7.Case1Data.cf.h t / (LogN7.Case1Data.cf.Lam : ℝ) := by",
        "  unfold Cert3.Hf",
        "  rw [r2_peval_eq_sum]\n",
        "/-- **Case 1 (log kernel).**  Every configuration all of whose pair inner products are `≥ -9/10` has",
        "`phi2`-energy strictly above `E(P) = 41/4` (margin `eps/Λ - 41/4`). -/",
        "theorem case1Claim_riesz2",
        "    (hEP : ThomsonGen.pairEnergy LogN7.Minor.phi2 ThomsonN7.pentBipyramid = 41 / 4)",
        "    (hH : ∀ t : ℝ, -9 / 10 ≤ t → t < 1 →",
        "      LogN7.Minor.peval LogN7.Case1Data.h_ t / (LogN7.Case1Data.lam_ : ℝ) ≤ LogN7.Minor.phi2 t) :",
        "    ThomsonGen.Case1Claim LogN7.Minor.phi2 := by",
        "  have hL : (0 : ℝ) < (LogN7.Case1Data.cf.Lam : ℝ) := by",
        "    have : 0 < LogN7.Case1Data.cf.Lam := by decide +kernel",
        "    exact_mod_cast this",
        "  have hI : (41 : ℤ) * (LogN7.Case1Data.cf.Lam : ℤ) < 4 * LogN7.Case1Data.cf.eps := by decide +kernel",
        "  have hR : (41 : ℝ) * (LogN7.Case1Data.cf.Lam : ℝ) < 4 * (LogN7.Case1Data.cf.eps : ℝ) := by",
        "    exact_mod_cast hI",
        "  have hη : (0 : ℝ) < (LogN7.Case1Data.cf.eps : ℝ) / (LogN7.Case1Data.cf.Lam : ℝ) - 41 / 4 := by",
        "    have h41 : (41 : ℝ) / 4 < (LogN7.Case1Data.cf.eps : ℝ) / (LogN7.Case1Data.cf.Lam : ℝ) := by",
        "      rw [div_lt_div_iff₀ (by norm_num) hL]",
        "      linarith",
        "    linarith",
        "  have han : ((LogN7.Case1Data.cf.an : ℤ) : ℝ) / (LogN7.Case1Data.cf.ad : ℝ) = -9 / 10 := by",
        f"    show ((({cf.an} : ℤ) : ℝ)) / ((({cf.ad} : ℕ) : ℝ)) = -9 / 10",
        "    norm_num",
        "  have hC : (0 : ℝ) < ((Nat.choose 7 2 : ℕ) : ℝ) := by",
        "    exact_mod_cast Nat.choose_pos (by norm_num)",
        "  refine ThomsonGen.case1Claim_of_threePoint_cut LogN7.Minor.phi2 (H := LogN7.Case1Data.cf.Hf) hη",
        "    LogN7.Case1Data.cf.K LogN7.Case1Data.cf.m LogN7.Case1Data.cf.Fm",
        "    (fun k hk => fmat_psd LogN7.Case1Data.cf.Lam ((check_parts r2c1_cf_ok).2.2.2.1 k hk)) ?_ ?_",
        "  · intro u v t hg hu hv ht",
        "    have h := Cert3.hpt_cut LogN7.Case1Data.cf r2c1_cf_ok hg (by rw [han]; exact hu)",
        "      (by rw [han]; exact hv) (by rw [han]; exact ht)",
        "    have hdiv : (ThomsonGen.pairEnergy LogN7.Minor.phi2 ThomsonN7.pentBipyramid",
        "          + ((LogN7.Case1Data.cf.eps : ℝ) / (LogN7.Case1Data.cf.Lam : ℝ) - 41 / 4))",
        "          / ((Nat.choose 7 2 : ℕ) : ℝ)",
        "        ≤ ((LogN7.Case1Data.cf.eps : ℝ) / (LogN7.Case1Data.cf.Lam : ℝ)) / ((Nat.choose 7 2 : ℕ) : ℝ) := by",
        "      apply div_le_div_of_nonneg_right _ hC.le",
        "      linarith [hEP]",
        "    have hn : LogN7.Case1Data.cf.n = 7 := rfl",
        "    rw [hn] at h",
        "    linarith",
        "  · intro t h1 h2",
        "    have hh : LogN7.Minor.peval LogN7.Case1Data.cf.h t / (LogN7.Case1Data.cf.Lam : ℝ)",
        "        ≤ LogN7.Minor.phi2 t := hH t h1 h2",
        "    rw [r2c1_Hf_eq]",
        "    exact hh\n",
        "end Case1",
        "end LogN7\n"])


# ------------------------------------------------------------------ --check: re-read the emitted files
def check_emitted(outdir, J=None):
    ok = True
    data = open(os.path.join(outdir, "Data.lean")).read()
    cf, env = P.parse_data(data)
    log(f"parsed Data.lean: n={cf.n} Λ={cf.Lam} ({cf.Lam.bit_length()} bits) an/ad={cf.an}/{cf.ad} "
        f"|h|={len(cf.h)} K={cf.K} sizes F={[cf.m(k) for k in range(cf.K)]} S={[len(s.z) for s in cf.S]}")
    lits = {}
    for fn in sorted(os.listdir(outdir)):
        if fn.startswith("Chk") or fn == "Check.lean":
            lits.update(P.parse_stats(open(os.path.join(outdir, fn)).read()))
    rep = simulate(cf)
    w, D = rep["w"], rep["D"]
    log(f"Blk.ok F: {rep['F_ok']}  S: {rep['S_ok']}")
    ok &= all(rep["F_ok"]) and all(rep["S_ok"]) and rep["n_ge_3"] and rep["Lam_pos"] and rep["ad_pos"]
    for nm, st in rep["pieces"].items():
        key = f"r2c1_stat_{nm}"
        if key not in lits:
            log(f"  {key}: MISSING literal"); ok = False; continue
        lw, lD, lhs, lit = lits[key]
        good = (lw, lD) == (w, D) and lit == st
        ok &= good
        log(f"  {key}: {'MATCH' if good else 'MISMATCH'}  (l1 {st[0].bit_length()} bits, deg {st[1:4]}, "
            f"|kev| {abs(st[4]).bit_length()} bits)")
    tot = rep["total"]
    lw, lD, lhs, lit = lits["r2c1_idE_stat"]
    good = (lw, lD) == (w, D) and lit == tot and tot[4] == 0
    ok &= good
    log(f"  r2c1_idE_stat: {'MATCH' if good else 'MISMATCH'}; total l1 = {tot[0]} ({tot[0].bit_length()} bits) "
        f"< 2^{w}: {tot[0] < (1 << w)}; w = Nat.log2 l1 + 1 = {U.nat_log2(tot[0]) + 1}; D = {D}; kev(idE) = "
        f"{tot[4] if tot[4] == 0 else f'NONZERO ({abs(tot[4]).bit_length()} bits)'}")
    chk_txt = open(os.path.join(outdir, "Check.lean")).read()
    ok &= f"Nat.log2 {tot[0]} + 1 = {w}" in chk_txt and f"(max {tot[2]} {tot[3]}) + 1 = {D}" in chk_txt
    ok &= rep["check"]
    ri = rational_identity(cf, J)
    log(f"independent rational cross-check (numerics/cells/check_cell.py helpers): {ri}")
    ok &= ri["identity_exact"] and ri["all_pd"] and ri["e_gt_EP"] and ri.get("equals_json", True)
    big = max([abs(x) for x in cf.h] + [cf.eps, cf.Lam] +
              [abs(v) for b in cf.F + [s.B for s in cf.S] for v in b.d + [x for r in b.l + b.D for x in r]])
    sizes = {fn: os.path.getsize(os.path.join(outdir, fn)) for fn in sorted(os.listdir(outdir)) if fn.endswith(".lean")}
    log(f"largest data integer: {big.bit_length()} bits; largest kev literal: "
        f"{max(abs(s[4]).bit_length() for s in rep['pieces'].values())} bits; module sizes {sizes}")
    log("CHECK " + ("ALL_OK" if ok else "FAILED"))
    return ok, rep, sizes


def selftest_upstream(tgdir):
    cf, _ = P.parse_data(open(os.path.join(tgdir, "Case1Data.lean")).read())
    lits = {}
    for fn in ("Case1ChkF.lean", "Case1ChkS03.lean", "Case1ChkS47.lean"):
        lits.update(P.parse_stats(open(os.path.join(tgdir, fn)).read()))
    rep = simulate(cf)
    ok = rep["check"]
    for nm, st in rep["pieces"].items():
        lw, lD, _, lit = lits[f"c1_stat_{nm}"]
        good = (lw, lD) == (rep["w"], rep["D"]) and lit == st
        ok &= good
        log(f"  upstream c1_stat_{nm}: {'MATCH' if good else 'MISMATCH'}")
    log(f"  upstream total {rep['total'][:4]} kev {rep['total'][4]}, w = {rep['w']}, D = {rep['D']}")
    log("SELFTEST " + ("ALL_OK" if ok else "FAILED"))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", nargs="?")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--json", dest="json2")
    ap.add_argument("--selftest-upstream")
    ap.add_argument("--outdir", default=DEF_OUT)
    ap.add_argument("--pack", choices=["hex", "lists"], default="hex")
    ap.add_argument("--budget", type=int, default=1_000_000)
    ap.add_argument("--s0", type=int, default=0, help="initial extra power of 2 in Λ")
    args = ap.parse_args()
    if args.selftest_upstream:
        sys.exit(0 if selftest_upstream(args.selftest_upstream) else 1)
    if args.check:
        jp = args.json2 or args.json
        ok, _, _ = check_emitted(args.outdir, json.load(open(jp)) if jp else None)
        sys.exit(0 if ok else 1)
    raw = open(args.json, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    J = json.loads(raw)
    cf, meta = build(J, s_start=args.s0)
    log(f"Λ = Λ0·2^{meta['s']} = {cf.Lam} ({cf.Lam.bit_length()} bits)")
    for row in meta["table"]:
        log(f"  mult_index {row['mult_index']}: g = {row['g']} (d={row['d']}, |z|={row['size']}) -> codes {row['codes']} "
            f"({row['name']}), c = {row['c']}")
    rep = simulate(cf)
    log(f"simulation: check = {rep['check']}  w = {rep['w']}  D = {rep['D']}  kev(idE) = {rep['total'][4]}")
    if not rep["check"]:
        raise SystemExit("simulated Lean check FAILED; nothing emitted")
    files, groups, packinfo = emit(cf, meta, rep, os.path.basename(args.json), sha, args.outdir, args.pack, args.budget)
    for nm, txt in files.items():
        log(f"  wrote {os.path.join(args.outdir, nm)} ({len(txt.encode())} bytes)")
    summ = dict(json=os.path.abspath(args.json), sha256=sha, Lam=str(cf.Lam), Lam0=str(meta["L0"]), s=meta["s"],
                h=[str(x) for x in cf.h], eps=str(cf.eps), an=cf.an, ad=cf.ad, w=rep["w"], D=rep["D"],
                l1_total=str(rep["total"][0]), multipliers=meta["table"], pack=args.pack,
                packing={k: (meta["pack"][k], packinfo.get(k)) for k in meta["pack"]},
                groups=[(g, n) for g, n in groups])
    with open(os.path.join(HERE, "case1_cert3_summary.json"), "w") as fh:
        json.dump(summ, fh, indent=1)
    ok, _, _ = check_emitted(args.outdir, J)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
