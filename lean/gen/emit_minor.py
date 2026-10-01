"""Emit Lean minorant modules (routes A/B/C) for one cell certificate.  See MINORANT_PLAN.md.

usage (from the worktree root, nice -n 19):
  python3 lean/gen/emit_minor.py <cert.json> <Name> [--bench]
    writes lean/LogLean/Minor<Name>.lean            (route C, chain-level: production form)
    --bench also writes MinorBenchC/B/A.lean        (per-piece C, per-piece B, one route-A piece)

The piece partition comes from minor_design.py.  Every Bool check that Lean will run with
`decide +kernel` is first simulated here exactly (same list recursion, same integers), so a
failing piece is caught before the Lean build.
"""
import json
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial, lcm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import minor_design as md  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "LogLean")
# MINOR_OUT: output directory (default LEAN); MINOR_IMPORT=1: `import LogLean.MinorCore` instead of a core copy
OUT = os.environ.get("MINOR_OUT", LEAN)
DEN = md.DEN
l2, h2 = md.L2; l3, h3 = md.L3; l5, h5 = md.L5

# ---------------------------------------------------------------- exact simulation of MinorCore.lean


def padd(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p[0] + q[0]] + padd(p[1:], q[1:])


def pscale(c, p):
    return [c * x for x in p]


def pmul(p, q):
    if not p:
        return []
    return padd(pscale(p[0], q), [0] + pmul(p[1:], q))


def ppow(p, n):
    r = [1]
    for _ in range(n):
        r = pmul(p, r)
    return r


def homog(T, E, q, m):
    if not q:
        return []
    return padd(pscale(q[0], ppow(E, m)), pmul(T, homog(T, E, q[1:], max(m - 1, 0))))


def taylorPoly(a, R, L, n):
    r = []
    for k in range(n):                       # builds k+1 from k
        assert L % (k + 1) == 0
        r = padd(pscale(R, r), pscale(L // (k + 1), ppow(a, k + 1)))
    return r


def minorPoly(Hn, Hd, gn, gd, Ln, Ld, n):
    L = factorial(n); R = gd - gn
    return padd(padd([2 * Ln * Hd * L * R ** n], pscale(Ld * Hd, taylorPoly([-gn, gd], R, L, n))),
                pscale(-(2 * Ld * L * R ** n), Hn))


def nodeOK(gn, gd, e, Ln, Ld):
    a2, a3, a5, b2, b3, b5 = e
    ok1 = 2 * (gd - gn) * (2 ** b2 * 3 ** b3 * 5 ** b5) == gd * (2 ** a2 * 3 ** a3 * 5 ** a5)
    ok2 = 2 * DEN * Ln <= -(Ld * (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5))
    return ok1 and ok2


def piece_check(Hn, Hd, D, p):
    q = minorPoly(Hn, Hd, p["gn"], p["gd"], p["Ln"], p["Ld"], p["n"])
    S = homog([p["A"], p["B"]], [D, D], q, len(q) - 1)
    ok = (0 < p["gd"] and p["gn"] < p["gd"] and 0 < p["Ld"] and p["n"] % 2 == 1 and p["B"] <= D
          and nodeOK(p["gn"], p["gd"], p["e"], p["Ln"], p["Ld"]) and all(c >= 0 for c in S))
    return ok, q, S


def tail_check(Hn, Hd, D, c):
    q = padd([Hd * c["Ln"]], pscale(-c["Ld"], Hn))
    S = homog([c["T0"], D], [D, D], q, len(q) - 1)
    ok = c["T0"] < D and 0 < c["Ld"] and nodeOK(c["T0"], D, c["e"], c["Ln"], c["Ld"]) and all(x >= 0 for x in S)
    return ok


def chain_check(Hn, Hd, D, ps, l, r):
    for p in ps:
        if not (piece_check(Hn, Hd, D, p)[0] and p["A"] <= l):
            return False
        l = p["B"]
    return r <= l


def bernSum(a, b, n, i, bs):
    out = []
    for k, beta in enumerate(bs):
        out = padd(out, pscale(beta, pmul(ppow(a, i + k), ppow(b, n - (i + k)))))
    return out

# ---------------------------------------------------------------- data


def lnode_int(e):
    """Ln/Ld = floor(-X 2^LBITS / (2 DEN)) / 2^LBITS, X = sum a h - sum b l."""
    a2, a3, a5, b2, b3, b5 = e
    X = a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5
    Ld = 2 ** md.LBITS
    return (-X * Ld) // (2 * DEN), Ld


def int_H(Hq):
    Hd = 1
    for c in Hq:
        Hd = lcm(Hd, c.denominator)
    return [int(c * Hd) for c in Hq], Hd


def make_piece(p, D):
    g = p["g"]; A = p["a"] * D; B = p["b"] * D
    assert A.denominator == 1 and B.denominator == 1
    Ln, Ld = lnode_int(p["e"])
    assert Fr(Ln, Ld) == md.Lnode(p["e"])
    return dict(A=int(A), B=int(B), gn=g.numerator, gd=g.denominator, n=p["n"], e=p["e"], Ln=Ln, Ld=Ld)


def make_tail(t0, e, D):
    T0 = t0 * D
    assert T0.denominator == 1
    Ln, Ld = lnode_int(e)
    return dict(T0=int(T0), e=e, Ln=Ln, Ld=Ld)


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_piece(p):
    e = p["e"]
    return (f"⟨{p['A']}, {p['B']}, {p['gn']}, {p['gd']}, {p['n']}, {e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]}, "
            f"{e[5]}, {p['Ln']}, {p['Ld']}⟩")


def lean_tail(c):
    e = c["e"]
    return f"⟨{c['T0']}, {e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]}, {e[5]}, {c['Ln']}, {c['Ld']}⟩"


def core_text():
    if os.environ.get("MINOR_IMPORT"):
        return "import LogLean.MinorCore\n\nopen Finset\n\nnamespace LogLean.Minor\n"
    s = open(os.path.join(LEAN, "MinorCore.lean")).read()
    return s[:s.rindex("end LogLean.Minor")]


def design(J, ns, D):
    lo = Fr(J["cell"]["lo"]) if "lo" in J["cell"] else Fr(J["cell"]["a"])
    hi = Fr(J["cell"]["hi"]) if "hi" in J["cell"] else None
    classes = [("A", J["H"]["A"], hi), ("B", J["H"]["B"], None), ("C", J["H"]["C"], None)] \
        if isinstance(J["H"], dict) else [("H", J["H"], None)]
    out = []
    for cls, Hs, h in classes:
        des = md.Designer(Hs, D, ns=ns)
        if h is None:
            t0, tinfo = md.tail_start(des)
            pcs = des.cover(lo, t0)
            tail = make_tail(t0, tinfo["e"], D)
            r = tail["T0"]
        else:
            pcs = des.cover(lo, h + Fr(1, D))
            tail = None
            r = int(h * D) + 1
        Hn, Hd = int_H([Fr(x) for x in Hs])
        P = [make_piece(p, D) for p in pcs]
        for p, pd in zip(P, pcs):
            p["N"] = pd["N"]
        out.append(dict(cls=cls, Hn=Hn, Hd=Hd, pieces=P, tail=tail, lo=int(lo * D), r=r, hi=h,
                        Hq=[Fr(x) for x in Hs], raw=pcs))
    return lo, out


def verify(D, classes):
    for c in classes:
        assert chain_check(c["Hn"], c["Hd"], D, c["pieces"], c["lo"], c["r"]), c["cls"]
        if c["tail"]:
            assert tail_check(c["Hn"], c["Hd"], D, c["tail"]), c["cls"]


def fr_lean(q):
    return f"({q.numerator} : ℝ) / {q.denominator}" if q.denominator != 1 else f"({q.numerator} : ℝ)"


def emit_production(name, J, lo, D, classes, path):
    L = [core_text(), f"\n/-! # Data: `{J.get('generated_from', name)}` cell {J['cell']} (generated by lean/gen/emit_minor.py) -/\n",
         f"namespace {name}\n", "set_option profiler true", "set_option profiler.threshold 200\n",
         f"def D : ℕ := {D}\n"]
    for c in classes:
        k = c["cls"]
        L.append(f"def H{k} : List ℤ := {lean_list(c['Hn'])}")
        L.append(f"def Hd{k} : ℕ := {c['Hd']}")
        L.append(f"def pieces{k} : List Piece := [\n  " + ",\n  ".join(lean_piece(p) for p in c["pieces"]) + "]")
        L.append(f"theorem chain{k} : chainOK H{k} Hd{k} D pieces{k} ({c['lo']}) ({c['r']}) = true := by decide +kernel")
        if c["tail"]:
            L.append(f"def tail{k} : Tail := {lean_tail(c['tail'])}")
            L.append(f"theorem tail{k}_ok : tail{k}.check H{k} Hd{k} D = true := by decide +kernel")
            L.append(f"""/-- class {k}: `H_{k} ≤ φ` on `[{c['lo']}/D, 1)`. -/
theorem H{k}_le_phi {{t : ℝ}} (h0 : (({c['lo']} : ℤ) : ℝ) ≤ D * t) (h1 : t < 1) :
    peval H{k} t / Hd{k} ≤ phi t :=
  class_sound H{k} Hd{k} D (by decide) (by decide) pieces{k} tail{k} ({c['lo']}) chain{k} tail{k}_ok h0 h1
""")
        else:
            L.append(f"""/-- class {k}: `H_{k} ≤ φ` on `[{c['lo']}/D, {c['r']}/D)` (⊇ the closed cell range). -/
theorem H{k}_le_phi {{t : ℝ}} (h0 : (({c['lo']} : ℤ) : ℝ) ≤ D * t) (h1 : (D : ℝ) * t < (({c['r']} : ℤ) : ℝ)) :
    peval H{k} t / Hd{k} ≤ phi t :=
  chain_sound H{k} Hd{k} D (by decide) (by decide) pieces{k} ({c['lo']}) ({c['r']}) chain{k} t h0 h1
""")
    L.append(f"end {name}\n\nend LogLean.Minor\n")
    open(path, "w").write("\n".join(L))


def emit_bench_C(J, D, classes, path):
    L = [core_text(), "\n/-! # Benchmark route C: one `decide +kernel` per piece -/\n", "namespace BenchC",
         "set_option profiler true", "set_option profiler.threshold 50\n", f"def D : ℕ := {D}\n"]
    for c in classes:
        k = c["cls"]
        L.append(f"def H{k} : List ℤ := {lean_list(c['Hn'])}")
        L.append(f"def Hd{k} : ℕ := {c['Hd']}")
        for i, p in enumerate(c["pieces"]):
            L.append(f"def p{k}{i} : Piece := {lean_piece(p)}")
            L.append(f"theorem ok{k}{i} : p{k}{i}.check H{k} Hd{k} D = true := by decide +kernel  -- N={p['N']} n={p['n']}")
        if c["tail"]:
            L.append(f"def tail{k} : Tail := {lean_tail(c['tail'])}")
            L.append(f"theorem tail{k}_ok : tail{k}.check H{k} Hd{k} D = true := by decide +kernel")
    L.append("end BenchC\n\nend LogLean.Minor\n")
    open(path, "w").write("\n".join(L))


def emit_bench_B(J, D, classes, path):
    L = [core_text(), "\n/-! # Benchmark route B: stored Bernstein data (upstream `BPiece`), one `decide +kernel` per piece -/\n",
         "namespace BenchB", "set_option profiler true", "set_option profiler.threshold 50\n", f"def D : ℕ := {D}\n"]
    nb = 0
    for c in classes:
        k = c["cls"]
        L.append(f"def H{k} : List ℤ := {lean_list(c['Hn'])}")
        L.append(f"def Hd{k} : ℕ := {c['Hd']}")
        for i, p in enumerate(c["pieces"]):
            if p["B"] >= D:
                continue
            ok, q, S = piece_check(c["Hn"], c["Hd"], D, p)
            N = len(q) - 1
            assert all(x == 0 for x in S[N + 1:])      # homog pads with zeros (pmul T [] = [0, 0])
            S = S[:N + 1]                               # BPiece uses n = β.length - 1
            Lam = D ** N * (p["B"] - p["A"]) ** N
            # upstream identity: Lam q - sum beta_i (D t - A)^i (B - D t)^(N-i) = 0
            diff = padd(pscale(Lam, q), pscale(-1, bernSum([-p["A"], D], [p["B"], -D], N, 0, S)))
            assert all(x == 0 for x in diff) and all(x >= 0 for x in S)
            nb += sum(x.bit_length() for x in S)
            L.append(f"def p{k}{i} : Piece := {lean_piece(p)}")
            L.append(f"def β{k}{i} : List ℕ := {lean_list(S)}")
            L.append(f"theorem ok{k}{i} : p{k}{i}.checkB H{k} Hd{k} D {Lam} β{k}{i} = true := by decide +kernel  -- N={N}")
    L.append("end BenchB\n\nend LogLean.Minor\n")
    open(path, "w").write("\n".join(L))
    return nb


def emit_bench_A(J, D, c, i, path):
    """route A: one piece, `ring` identity + `nlinarith` Bernstein positivity ."""
    p = c["pieces"][i]; raw = c["raw"][i]
    Hq = c["Hq"]; g = raw["g"]; a, b = raw["a"], raw["b"]
    P = md.minor_poly(Hq, g, p["e"], p["n"])
    N = len(P) - 1
    S = md.mobius(P, a, b, N)
    beta = [S[k] / comb(N, k) for k in range(N + 1)]
    assert min(beta) >= 0
    gn, gd = g.numerator, g.denominator
    Lg = Fr(p["Ln"], p["Ld"])
    u = f"(({gd} : ℝ) * t - {gn}) / {gd - gn}"
    Hexpr = " + ".join(f"({fr_lean(q)}) * t ^ {j}" for j, q in enumerate(Hq))
    Texpr = " + ".join(f"u ^ {k} / {k}" for k in range(1, p["n"] + 1))
    Bexpr = "\n    + ".join(f"({fr_lean(beta[k])}) * {comb(N, k)} * s ^ {k} * (1 - s) ^ {N - k}" for k in range(N + 1))
    hints = ", ".join([f"pow_nonneg hs0 {k}" for k in range(2, N + 1)] + [f"pow_nonneg h1s {k}" for k in range(2, N + 1)] +
                      [f"mul_nonneg (pow_nonneg hs0 {k}) (pow_nonneg h1s {N - k})" for k in range(0, N + 1)])
    txt = f"""{core_text()}
/-! # Benchmark route A: one piece [{a}, {b}] of class {c['cls']} (node g = {g}, n = {p['n']}, degree {N}):
exact `ring` identity to an explicit Bernstein form + `nlinarith` positivity. -/
namespace BenchA
set_option profiler true
set_option profiler.threshold 50

noncomputable def Hr (t : ℝ) : ℝ := {Hexpr}

noncomputable def bern (t : ℝ) : ℝ :=
  let s := (t - {fr_lean(a)}) / ({fr_lean(b - a)})
  {Bexpr}

theorem logTaylor_eq (u : ℝ) : logTaylor {p['n']} u = {Texpr} := by
  simp only [logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

set_option maxHeartbeats 20000000 in
theorem key (t : ℝ) :
    ({fr_lean(Lg)}) + 1 / 2 * logTaylor {p['n']} (((({gd} : ℕ) : ℝ) * t - (({gn} : ℤ) : ℝ)) / ((({gd} : ℕ) : ℝ) - (({gn} : ℤ) : ℝ)))
      - Hr t = bern t := by
  rw [logTaylor_eq]
  unfold Hr bern
  push_cast
  ring

set_option maxHeartbeats 20000000 in
theorem bern_nonneg {{t : ℝ}} (ha : {fr_lean(a)} ≤ t) (hb : t ≤ {fr_lean(b)}) : 0 ≤ bern t := by
  have hs0 : (0:ℝ) ≤ (t - {fr_lean(a)}) / ({fr_lean(b - a)}) :=
    div_nonneg (by linarith) (by norm_num)
  have hs1 : (t - {fr_lean(a)}) / ({fr_lean(b - a)}) ≤ 1 := by
    rw [div_le_one (by norm_num)]; linarith
  have h1s : (0:ℝ) ≤ 1 - (t - {fr_lean(a)}) / ({fr_lean(b - a)}) := by linarith
  unfold bern
  nlinarith [{hints}]

theorem piece_le_phi {{t : ℝ}} (ha : {fr_lean(a)} ≤ t) (hb : t ≤ {fr_lean(b)}) : Hr t ≤ phi t := by
  have ht1 : t < 1 := by linarith
  have hk := key t
  have hb0 := bern_nonneg ha hb
  have s2 := phi_ge_node (gn := {gn}) (gd := {gd}) (by norm_num) (by norm_num) (n := {p['n']}) ⟨{(p['n'] - 1) // 2}, by norm_num⟩ ht1
  have s3 := Lnode_le (gn := {gn}) (gd := {gd}) (a2 := {p['e'][0]}) (a3 := {p['e'][1]}) (a5 := {p['e'][2]})
    (b2 := {p['e'][3]}) (b3 := {p['e'][4]}) (b5 := {p['e'][5]}) (Ln := {p['Ln']}) (Ld := {p['Ld']}) (by decide +kernel) (by norm_num) (by norm_num)
  have e3 : ((({p['Ln']} : ℤ) : ℝ) / (({p['Ld']} : ℕ) : ℝ)) = {fr_lean(Lg)} := by push_cast; norm_num
  rw [e3] at s3
  linarith
end BenchA

end LogLean.Minor
"""
    open(path, "w").write(txt)


def main():
    path, name = sys.argv[1], sys.argv[2]
    bench = "--bench" in sys.argv
    J = json.load(open(path))
    D = 100 * 2 ** 12
    ns = (5, 7, 9, 11, 13)
    lo, classes = design(J, ns, D)
    verify(D, classes)
    tot = sum(len(c["pieces"]) for c in classes)
    print(f"{name}: {tot} pieces + {sum(1 for c in classes if c['tail'])} tails, all Bool checks pass in simulation")
    for c in classes:
        print(" ", c["cls"], [(float(Fr(p['A'], D)), p['n'], p['N']) for p in c["pieces"]],
              "tail" if c["tail"] else "", float(Fr(c["tail"]["T0"], D)) if c["tail"] else "")
    emit_production(f"Cell{name}", J, lo, D, classes, os.path.join(OUT, f"Minor{name}.lean"))
    if bench:
        emit_bench_C(J, D, classes, os.path.join(LEAN, "MinorBenchC.lean"))
        nb = emit_bench_B(J, D, classes, os.path.join(LEAN, "MinorBenchB.lean"))
        print("route B stored beta bits:", nb)
        cB = [c for c in classes if c["cls"] == "B"][0]
        i = max(range(len(cB["pieces"])), key=lambda j: cB["raw"][j]["b"] - cB["raw"][j]["a"])
        emit_bench_A(J, D, cB, i, os.path.join(LEAN, "MinorBenchA.lean"))


if __name__ == "__main__":
    main()
