"""Minorant margin profiles for capS node solves (float; planning aid, not part of any proof).

usage: python3 margin_profile.py GRID.json S [S ...]  [--h 1/12] [--range LO HI] [--m0 M0] [--base C] [--tag TAG]
                                  [--phicap C] [--out DIR] [--check CERT ...]
  GRID.json: the minorant sample grid of the node solve, written by
             (cd ../capS && env DENSE=6000 EXCL=1 python3 sdp_capS.py grid GRID.json)   (same DENSE, EXCL as the solve;
             the factory grid is ../capS/minorant_grid_DENSE6000_EXCL1.json, independent of s)
  S:         node exponents (rationals such as 2/3); one profile file per S: DIR/margin_profile_s<p>_<q>_h<1/h>.json
  --range:   only pieces inside [LO, HI] count (default: both neighbours [S - h, S], [S, S + h])
  --m0, --base: m = max(m0, 1.2 need + base); defaults m0 = 2.5e-6 (s < 1) / 5e-6 (s >= 1), base = 1e-6
  --tag:     suffix of the file name (margin_profile_s<p>_<q>_h<1/h><TAG>.json)
  --phicap:  capped profile for large s (2026-11-07, extension beyond 3/2): sdp_capS imposes H <= min(phi, PHICAP) - m
             (PHICAP = 20 by default there), so where phi_s(t) > C the raw demand m is replaced by
             m' = max(m0, m - max(0, phi_s(t) - C)).  H <= C - m' implies H <= phi - m, so the checker's need is still
             met; without the cap the rows near t -> 1 would ask for H <= C - m with m >> C.  Pass C = the solve's
             PHICAP (20).  Default: off (profiles unchanged).
  --check:   node certificates (json[.gz]); report min over t of f_X(t) - need_X(t) at the node's own s (float).

What a node at s needs.  check_capR.py's minorant step M (one-sided s-remainder, see its docstring) proves, for a
piece [a, b] of width h and every t outside the contact windows,
    f(t, s) >= min(f(t, a), f(t, b)) - (h^2/8) G+(t),  G+(t) = max(0, g''(s_m) + (h/2)|g'''(s_m)| + (h^2/8) sup|g''''|),
with g_t(s) = phi_s(t) - sum_k v_k(s) H_k(t) (H_k: the seven fixed directions of cert_dirs_D12.json, v(s): the kernel data
at the contacts, s_m = (a + b)/2, sup over [a, b]).  G+ depends only on the directions and the piece, not on the nodes.
A node at s is an end of the pieces [s - h, s] and [s, s + h] (those inside --range), so it needs
f(t, s) > (h^2/8) max(G+_left, G+_right).
The profile written here is
    m_X(t; s) = max( m0(s), 1.2 * (h^2/8) * max(G+_left(t), G+_right(t)) + base ),   by default m0 = 2.5e-6 (s < 1),
    5e-6 (s >= 1), base = 1e-6 (so m >= 1e-6 whatever m0 is; to go lower pass --base as well),
on exactly the grid points t_X of GRID.json, X = A, B, C (H_A, H_B, H_C use the same directions' H_k^X).  sdp_capS.py
(MARGIN_PROFILE=<file>, scalar margin 0) multiplies m_X by its contact weights w_X(t) (which vanish at the contacts, where
the checker uses curvature instead); the output also records need_X, w_X and where m_X * w_X < need_X.
The node's own value f(t, s) is what the solve controls; the window conditions (f'' / f' floors) are the CONTACT floors
and are not part of this profile.  Float only: G+ is computed with numpy at the grid points (t exact points, no t-ball),
with sup|g''''| over 9 sample points of each piece; the 1.2 factor and the 1e-6 absorb that and the checker's t-cells.
Output JSON: {"s": "p/q", "h": "1/12", "pieces": [...], "m0": m0, "A": {"t": [...], "m": [...], "need": [...]}, "B": ...,
              "C": ..., "summary": {...}}  (sdp_capS.load_margin_profile reads s and X.t, X.m; m is unweighted).
"""
import gzip, json, math, os, sys
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SQ5 = math.sqrt(5.0); C1 = (SQ5 - 1) / 4; C2 = (-SQ5 - 1) / 4
SPOLY = {0: [1.0], 1: [0.0, 1.0]}          # P_m(s) = prod_{i<m} (s + 2i), monomial coefficients (m <= 1 needed)


def Phi(m, n, t, s):
    """d^n/ds^n of phi_s^(m)(t) = P_m(s) u^(-s/2-m), u = 2 - 2t (float / numpy)."""
    L = np.log(2.0 - 2.0 * np.asarray(t, float))
    E = np.exp(-(s / 2 + m) * L)
    tot = 0.0
    P = list(SPOLY[m])
    for j in range(n + 1):
        cs = P
        for _ in range(j):
            cs = [i * cs[i] for i in range(1, len(cs))]
        if not cs:
            break
        Pj = sum(c * s ** i for i, c in enumerate(cs))
        tot = tot + math.comb(n, j) * Pj * (-L / 2) ** (n - j)
    return tot * E


def vdata(n, s):
    """d^n/ds^n of v(s) = (phi(0), phi'(0), phi(-1), Re phi(c1), Im phi(c1), Re phi'(c1), Im phi'(c1)) (float)."""
    p = lambda m, t: float(Phi(m, n, t, s))
    return np.array([p(0, 0.0), p(1, 0.0), p(0, -1.0), (p(0, C1) + p(0, C2)) / 2, (p(0, C1) - p(0, C2)) / (2 * SQ5),
                     (p(1, C1) + p(1, C2)) / 2, (p(1, C1) - p(1, C2)) / (2 * SQ5)])


def jload(path):
    return json.load(gzip.open(path, "rt") if path.endswith(".gz") else open(path))


def fl(x):
    return float(Fr(str(x)))


def load_dirs(path):
    """H_k^X monomial coefficients (float) of the seven directions."""
    J = jload(path)
    assert len(J["dirs"]) == 7
    return {X: np.array([[fl(c) for c in J["dirs"][k]["H"][X]] for k in range(7)]) for X in "ABC"}


def polyval(coefs, t):
    out = np.zeros_like(t)
    for c in coefs[::-1]:
        out = out * t + c
    return out


def g_der(n, t, s, HkT):
    """d^n/ds^n g_t(s) = d^n/ds^n phi_s(t) - sum_k v_k^(n)(s) H_k(t)  (HkT: 7 x len(t) values H_k(t))."""
    return Phi(0, n, t, s) - vdata(n, s) @ HkT


def Gplus(t, a, b, HkT):
    """the checker's one-sided bound G+(t) on the piece [a, b] (float, t points)."""
    h = b - a; sm = (a + b) / 2
    g4 = np.max(np.abs([g_der(4, t, a + h * i / 8, HkT) for i in range(9)]), axis=0)
    return np.maximum(0.0, g_der(2, t, sm, HkT) + h / 2 * np.abs(g_der(3, t, sm, HkT)) + h * h / 8 * g4)


def raised_regions(t, m, m0, need):
    """maximal runs of grid points with m > m0: [t_lo, t_hi, max m, t at max m, max need]."""
    out = []; i = 0; n = len(t)
    while i < n:
        if m[i] > m0:
            j = i
            while j + 1 < n and m[j + 1] > m0:
                j += 1
            k = i + int(np.argmax(m[i:j + 1]))
            out.append([float(t[i]), float(t[j]), float(m[k]), float(t[k]), float(need[i:j + 1].max())])
            i = j + 1
        else:
            i += 1
    return out


def profile(s, h, grid, Hk, rng=None, m0=None, base=1e-6, phicap=None):
    if m0 is None:
        m0 = 2.5e-6 if s < 1 else 5e-6
    pieces = [(s - h, s), (s, s + h)]
    if rng is not None:
        pieces = [(a, b) for a, b in pieces if rng[0] <= a and b <= rng[1]]
    assert pieces, f"no piece of width {h} at {s} inside {rng}"
    out = {"s": f"{s.numerator}/{s.denominator}", "h": f"{h.numerator}/{h.denominator}",
           "pieces": [[f"{a.numerator}/{a.denominator}", f"{b.numerator}/{b.denominator}"] for a, b in pieces], "m0": m0,
           "base": base, "formula": "m = max(m0, 1.2 * (h^2/8) * G+ + base)"}
    if phicap is not None:
        out["phicap"] = phicap
        out["formula"] += (f"; capped m' = max(m0, m - max(0, phi - PHICAP)), PHICAP = {phicap:g} "
                           "(H <= min(phi, PHICAP) - m' implies H <= phi - m)")
    summ = {}
    for X in "ABC":
        t = np.asarray(grid[X]["t"], float); w = np.asarray(grid[X]["w"], float)
        HkT = np.array([polyval(Hk[X][k], t) for k in range(7)])
        G = np.max([Gplus(t, float(a), float(b), HkT) for a, b in pieces], axis=0)
        need = float(h * h / 8) * G
        m = np.maximum(m0, 1.2 * need + base)
        if phicap is not None:
            m_raw = m
            m = np.maximum(m0, m - np.maximum(0.0, Phi(0, 0, t, float(s)) - phicap))
        assert np.all(np.diff(t) > 0) and np.all(np.isfinite(m)) and np.all(m >= 0)
        short = m * w < need
        out[X] = {"t": t.tolist(), "m": m.tolist(), "need": need.tolist()}
        summ[X] = dict(n=len(t), m_max=float(m.max()), frac_above_m0=float(np.mean(m > m0)),
                       **({"m_raw_max": float(m_raw.max()), "n_capped": int(np.sum(m < m_raw))} if phicap is not None
                          else {}),
                       raised=raised_regions(t, m, m0, need),
                       n_weighted_short=int(np.sum(short)), t_weighted_short=[float(x) for x in t[short][:5]])
    out["summary"] = summ
    return out


def check_node(path, prof_by_s, h, Hk):
    """float: min over the grid of f_X(t, s) - need_X(t) for a node certificate (outside the checker's windows)."""
    J = jload(path)
    s = Fr(J["s"]) if "s" in J else Fr(1)
    P = prof_by_s.get(s)
    if P is None:
        return f"{path}: no profile for s = {s}"
    res = {}
    for X in "ABC":
        t = np.asarray(P[X]["t"]); need = np.asarray(P[X]["need"])
        H = np.array([fl(c) for c in J["H"][X]])
        f = Phi(0, 0, t, float(s)) - polyval(H, t)
        outside = (t + 1 > 0.002) if X == "A" else (np.abs(t) > 0.05) if X == "B" else \
            ((np.abs(t - C1) > 0.02) & (np.abs(t - C2) > 0.02))
        d = (f - need)[outside]; tt = t[outside]
        i = int(np.argmin(d))
        res[X] = f"min(f - need) {d[i]:+.2e} at t = {tt[i]:+.4f} (f {f[outside][i]:.2e}, need {need[outside][i]:.2e}); " \
                 f"{int(np.sum(d <= 0))} grid points with f <= need"
    return f"{path} (s = {s}): " + "; ".join(f"{X}: {v}" for X, v in res.items())


def main(argv):
    h = Fr(1, 12); out_dir = HERE; checks = []; svals = []; rng = None; m0 = None; base = 1e-6; tag = ""; phicap = None
    grid_path = argv[0]; rest = argv[1:]; i = 0
    while i < len(rest):
        if rest[i] == "--h":
            h = Fr(rest[i + 1]); i += 2
        elif rest[i] in ("--m0", "--base", "--tag"):
            if rest[i] == "--m0": m0 = float(rest[i + 1])
            elif rest[i] == "--base": base = float(rest[i + 1])
            else: tag = rest[i + 1]
            i += 2
        elif rest[i] == "--phicap":
            phicap = float(rest[i + 1]); i += 2
        elif rest[i] == "--range":
            rng = (Fr(rest[i + 1]), Fr(rest[i + 2])); i += 3
        elif rest[i] == "--out":
            out_dir = rest[i + 1]; i += 2
        elif rest[i] == "--check":
            i += 1
            while i < len(rest) and not rest[i].startswith("--"):
                checks.append(rest[i]); i += 1
        else:
            svals.append(Fr(rest[i])); i += 1
    grid = json.load(open(grid_path))
    Hk = load_dirs(os.path.join(HERE, "cert_dirs_D12.json"))
    # self-test against the arb values of the diagnosis (piece [2/3, 3/4], s_m = 17/24)
    for X, tq, ref in (("B", -0.335, -3.16e-3), ("C", -0.44, 3.73e-3), ("B", 0.944, 2.63)):
        HkT = np.array([polyval(Hk[X][k], np.array([tq])) for k in range(7)])
        val = float(g_der(2, np.array([tq]), 17 / 24, HkT)[0])
        assert abs(val - ref) <= 0.02 * abs(ref), (X, tq, val, ref)
    prof_by_s = {}
    for s in svals:
        P = profile(s, h, grid, Hk, rng, m0, base, phicap)
        prof_by_s[s] = P
        os.makedirs(out_dir, exist_ok=True)
        fn = os.path.join(out_dir, f"margin_profile_s{s.numerator}_{s.denominator}_h{h.denominator}{tag}.json")
        json.dump(P, open(fn, "w"))
        print(f"wrote {fn}: " + json.dumps(P["summary"]), flush=True)
    for c in checks:
        print(check_node(c, prof_by_s, h, Hk), flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
