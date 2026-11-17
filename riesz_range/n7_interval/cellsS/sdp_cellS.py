"""[cellsS] Riesz-s version with interval margins (see NOTES.md). Changes vs ../sdp_cell.py:
  RIESZ_S may be a fraction string ("1/2"); GW = w >= 0 is the s-piece width this node must serve
  (pieces [s-w, s] and [s, s+w]); the minorant constraint becomes H <= phi_s - s*G_w(t) - ETA on [lo, T1]
  and H <= 1 + s*psi_{s-w}(t) - ETA on [T1, 1), psi_s = (phi_s - 1)/s (normalised gauge), and in mu mode
  e = E_s(P) + s*EM_w + TARGET, with G_w, EM_w the chord-gap bounds of NOTES.md. mode maxe also accepts MU0
  (fix the eigenvalue floor mu = MU0, regularises the slab maxe solves).
Original docstring:
Float (Clarabel) solve of a NON-cap cell of the case split (PAPER.md sections 5-7), for rounding.

cells:
    case1:A          untyped three-point bound (section 5) on {all t_ij >= A}, H <= phi on [A, 1)
    slab:LO:HI       typed three-point bound (section 6) on {LO <= t01 <= HI, all t_ij >= LO},
                     H_A <= phi on [LO, HI], H_B, H_C <= phi on [LO, 1)
modes:
    maxe             maximise e (minorant H <= phi on a dense grid)                -> the float optimum
    mu  TARGET       fix e = E(P) + TARGET and maximise mu, the smallest eigenvalue of every PSD block
                     (F and SOS Gram blocks are X + mu I, X PSD), with H <= phi - ETA on the grid.
                     This gives an interior point that survives exact rounding (round_cell.py).

usage: python3 sdp_cell.py CELL MODE [TARGET]      env: POLYD (default 10), KER (0 = log, 1 = Coulomb),
       ETA (minorant margin in mu mode, default 1e-6), VERB=1, THREADS (default 2)
output: sol/<cellname>_<mode>.npz and a json line in results.jsonl
"""
import os, sys, json, time, warnings
os.environ.setdefault("POLYD", "10")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
import numpy as np
from numpy.polynomial import chebyshev as C
import cvxpy as cp
import mpmath as mp
import polyk
from polyk import *

warnings.filterwarnings("ignore")
mp.mp.dps = 40
KER = int(os.environ.get("KER", "0"))
from fractions import Fraction as _Fr
RS_STR = os.environ.get("RIESZ_S")
RS = float(_Fr(RS_STR)) if RS_STR else None
GW = float(os.environ.get("GW", "0"))          # piece width served by this node
T1 = float(os.environ.get("T1", "0.8"))        # G-lemma on [lo, T1], monotonicity on [T1, 1)
MU0 = os.environ.get("MU0")
CLOPTS = json.loads(os.environ.get("CLOPTS", "{}"))   # extra Clarabel settings, e.g. {"chordal_decomposition_enable": false}
PW_B = float(_Fr(os.environ["PIECE_B"])) if os.environ.get("PIECE_B") else None   # approach (i), e vs E_a(P)


def Ir2(c):
    """int_0^1 r^2 e^{c r} dr (vectorised, stable)."""
    c = np.asarray(c, float)
    out = np.empty_like(c)
    sm = np.abs(c) < 1e-3
    cs = c[sm]; out[sm] = 1 / 3 + cs / 4 + cs ** 2 / 10
    cb = c[~sm]; out[~sm] = (np.exp(cb) * (cb ** 2 - 2 * cb + 2) - 2) / cb ** 3
    return out


def Gpos(t, s, w):
    """max over sigma in [s-w, s+w] of (d^2/dsigma^2 psi_sigma(t))^+, psi = (u^-sigma/2 - 1)/sigma:
    = x^3 I(sigma x) for x = -ln(u)/2 > 0 (increasing in sigma), 0 for x <= 0; bounded by x^3 e^{(s+w)x}/3
    (the same bound as check_piece.py)."""
    x = -0.5 * np.log(2 - 2 * np.asarray(t, float))
    return np.where(x > 0, x ** 3 * np.exp((s + w) * np.maximum(x, 0)) / 3, 0.0)   # I(c) <= e^c/3 (c > 0)


def EMw(s, w):
    """max over sigma in [s-w, s+w] of -d^2/dsigma^2 Ehat_sigma(P) (attained at sigma = s-w), times w^2/8."""
    s5 = np.sqrt(5)
    us = [(4.0, 1), (2.0, 10), (2 - (s5 - 1) / 2, 5), (2 + (s5 + 1) / 2, 5)]
    sg = max(s - w, 0.0)
    tot = 0.0
    for u, m in us:
        x = -0.5 * np.log(u)
        tot += m * (-x ** 3) * float(Ir2(np.array([sg * x]))[0])
    return w * w / 8 * tot


def psi(t, s):
    u = 2 - 2 * np.asarray(t, float)
    return (u ** (-s / 2) - 1) / s if s > 0 else -0.5 * np.log(u)
ETA = float(os.environ.get("ETA", "1e-6"))
THREADS = int(os.environ.get("THREADS", "2"))
C1 = (np.sqrt(5) - 1) / 4; C2 = -(1 + np.sqrt(5)) / 4


def phi(t):
    t = np.asarray(t, float)
    if RS is not None:
        if PW_B is not None:      # approach (i): kernel min(phi_a, phi_b) on the piece [a, b] = [RIESZ_S, PIECE_B]
            return np.minimum((2 - 2 * t) ** (-RS / 2), (2 - 2 * t) ** (-PW_B / 2))
        return (2 - 2 * t) ** (-RS / 2)
    return -0.5 * np.log(2 - 2 * t) if KER == 0 else (2 - 2 * t) ** -0.5


def EP():
    s5 = mp.sqrt(5)
    if RS is not None:
        f = lambda t: (2 - 2 * t) ** (-(mp.mpf(_Fr(RS_STR).numerator) / _Fr(RS_STR).denominator) / 2)
        return f(-1) + 10 * f(0) + 5 * f((s5 - 1) / 4) + 5 * f((-s5 - 1) / 4)
    if KER == 0:
        return -mp.log(1600 * s5)
    f = lambda t: (2 - 2 * t) ** mp.mpf(-0.5)
    return f(-1) + 10 * f(0) + 5 * f((s5 - 1) / 4) + 5 * f((-s5 - 1) / 4)


def parse_cell(s):
    p = s.split(":")
    if p[0] == "case1":
        return dict(kind="case1", lo=float(p[1]), name=f"case1_{p[1]}")
    return dict(kind="slab", lo=float(p[1]), hi=float(p[2]), name=f"slab_{p[1]}_{p[2]}")


class Prob(SOSProblem):
    """PSD variables X; the actual block is X + mu I (mu = 0 in maxe mode)."""

    def __init__(self, use_mu):
        super().__init__()
        self.use_mu = use_mu
        self.mu = cp.Variable(1, name="mu") if use_mu else None
        if use_mu:
            self.vars["mu"] = self.mu
        self.psdnames = []

    def psd(self, name, n):
        X = cp.Variable((n, n), PSD=True, name=name)
        self.vars[name] = X; self.psdnames.append(name)
        return X

    def kernel_form(self, name, cols, m):
        """<F, Y> with F = X + mu I; cols: N3 x m^2."""
        self.psd(name, m)
        lp = LinPoly({name: cols})
        if self.use_mu:
            lp = lp + LinPoly({"mu": (cols @ np.eye(m).ravel())[:, None]})
        return lp

    def add_identity(self, lp, blocks, tag, reducers=None):
        rows = LOWROWS
        for k, M in lp.terms.items():
            assert np.abs(M[HIGHROWS]).max(initial=0) < 1e-12, (tag, k)
        expr = lp.const[rows]
        for k, M in lp.terms.items():
            expr = expr + np.asarray(M)[rows] @ self.vecexpr(k)
        rhs = 0; Bs = []
        for r, (g, d) in enumerate(blocks):
            Mg, n = sos_columns(g, d)
            B = self.psd(f"{tag}_B{r}", n)
            Bs.append((B, Mg, g, d, None))
            rhs = rhs + Mg[rows] @ cp.vec(B, order='C')
            if self.use_mu:
                rhs = rhs + (Mg[rows] @ np.eye(n).ravel()) * self.mu[0]
        self.cons.append(expr == rhs)
        self.sos.append((tag, lp, Bs))

    def blocks_value(self):
        mu = float(self.mu.value[0]) if self.use_mu else 0.0
        return {nm: self.vars[nm].value + mu * np.eye(self.vars[nm].shape[0]) for nm in self.psdnames}


def residuals(pr, xs):
    """l1 norm of (lhs - sum g z^T B z) per identity, with the actual blocks X + mu I."""
    out = {}
    for tag, lp, Bs in pr.sos:
        p = lp.value({k: v.value for k, v in pr.vars.items()})   # raw X (+ mu terms inside lp)
        rhs = np.zeros(N3)
        for B, Mg, g, d, N in Bs:
            rhs = rhs + Mg @ xs[B.name()].ravel()
        out[tag] = (float(np.abs(p - rhs).sum()),)
    return out


def univ(name, var):
    return LinPoly({name: univ_embed(var) @ cheb2mono()})


def cst(name, c=1.0):
    return LinPoly({name: pconst(c)[:, None]})


def to_var(lp_u, var):
    order = {0: (0, 1, 2), 1: (1, 0, 2), 2: (2, 1, 0)}[var]
    return lp_u.apply(PERM_M[order])


DETG = ONE + 2 * pmul(pmul(U, V), T) - pmul(U, U) - pmul(V, V) - pmul(T, T)


def build_case1(pr, a):
    K = D // 2 - 1                       # D=10: blocks sizes 6,5,4,3 (upstream)
    sizes = [D // 2 + 1 - k for k in range(K)]
    sform = LinPoly()
    for k, m in enumerate(sizes):
        sform = sform + pr.kernel_form(f"F{k}", np.asarray(SYM_AVG @ Yk_columns(k, m)), m)
    R = (7 - 2) * sform + sform.apply(subst_matrix((0, 0, 1.0))) + sform.apply(subst_matrix((1, 1, 1.0))) \
        + sform.apply(subst_matrix((2, 2, 1.0))) + sform.apply(subst_matrix((1.0, 1.0, 1.0))) * (1.0 / 6)
    pr.free("h", D + 1); pr.free("e", 1)
    Hsum = LinPoly({"h": (univ_embed(0) + univ_embed(1) + univ_embed(2)) @ cheb2mono() / 3.0})
    slack = Hsum + LinPoly({"e": -pconst(1.0 / 21)[:, None]}) - R
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    blocks = [(ONE, d5), (U - a * ONE, d4), (V - a * ONE, d4), (T - a * ONE, d4), (ONE - U, d4), (ONE - V, d4),
              (ONE - T, d4), (DETG, d3)]
    pr.add_identity(slack, blocks, "S")
    return dict(sizes=sizes, minorants={"h": (a, 1.0)})


def build_slab(pr, lo, hi):
    sizes = list(range(D // 2 + 1, 0, -1))
    forms = {}
    for X in "PR":
        f = LinPoly()
        for k, m in enumerate(sizes):
            f = f + pr.kernel_form(f"F{X}{k}", Yk_columns(k, m), m)
        forms[X] = f
    sP, sR = forms["P"], forms["R"]
    P = lambda f, o: f.apply(PERM_M[o])
    gm = {X: forms[X].apply(subst_matrix((1.0, 0, 0))) + forms[X].apply(subst_matrix((0, 1.0, 0)))
             + forms[X].apply(subst_matrix((0, 0, 1.0))) for X in "PR"}
    one = {X: forms[X].apply(subst_matrix((1.0, 1.0, 1.0))) for X in "PR"}
    for nm in ("hA", "hB", "hC", "pBa", "pCb"):
        pr.free(nm, D + 1)
    for nm in ("ca", "cb", "e"):
        pr.free(nm, 1)
    PsiA = univ("hA", 0) - 2 * gm["P"]
    PsiB = univ("hB", 0) - gm["P"] - gm["R"]
    PsiC = univ("hC", 0) - 2 * gm["R"]
    pBa = univ("pBa", 0); pCb = univ("pCb", 0)
    ca = cst("ca"); cb = cst("cb")
    cg = (cst("e") + 2 * one["P"] + 5 * one["R"] - 5 * ca - 20 * cb) * 0.1   # (6)
    lamA = PsiA * 0.2 + to_var(pBa, 1) + to_var(pBa, 2) - ca - 2 * (sP + P(sP, (0, 2, 1)) + P(sR, (1, 2, 0)))
    QB = (PsiB - pBa) * 0.25
    lamB = QB + to_var(QB, 1) + to_var(pCb, 2) - cb - 2 * (sP + P(sR, (0, 2, 1)) + P(sR, (1, 2, 0)))
    QC = (PsiC - 2 * pCb) * (1.0 / 3)
    lamG = QC + to_var(QC, 1) + to_var(QC, 2) - cg - 2 * (sR + P(sR, (0, 2, 1)) + P(sR, (1, 2, 0)))
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    blocksA = [(ONE, d5), (U - lo * ONE, d4), (hi * ONE - U, d4), (V - lo * ONE, d4), (T - lo * ONE, d4),
               (ONE - V, d4), (ONE - T, d4), (DETG, d3), (pmul(U - lo * ONE, hi * ONE - U), d4)]
    blocksBG = [(ONE, d5), (U - lo * ONE, d4), (V - lo * ONE, d4), (T - lo * ONE, d4),
                (ONE - U, d4), (ONE - V, d4), (ONE - T, d4), (DETG, d3)]
    pr.add_identity(lamA, blocksA, "A")
    pr.add_identity(lamB, blocksBG, "B")
    pr.add_identity(lamG, blocksBG, "G")
    return dict(sizes=sizes, minorants={"hA": (lo, hi), "hB": (lo, 1.0), "hC": (lo, 1.0)})


def grid(lo, hi, n=6000):
    g = [np.linspace(lo, hi, n), (lo + hi) / 2 + (hi - lo) / 2 * np.cos(np.linspace(0, np.pi, 2001)),
         np.linspace(max(lo, -0.02), min(hi, 0.02), 801)]
    for c in (C1, C2):
        g.append(np.linspace(c - 0.02, c + 0.02, 801))
    g = np.unique(np.concatenate(g))
    return g[(g >= lo) & (g <= hi)]


def main(cellspec, mode, target=None):
    cell = parse_cell(cellspec)
    t0 = time.time()
    pr = Prob(mode == "mu" or MU0 is not None)
    info = build_case1(pr, cell["lo"]) if cell["kind"] == "case1" else build_slab(pr, cell["lo"], cell["hi"])
    eta = ETA if mode == "mu" else 0.0
    for nm, (a, b) in info["minorants"].items():
        tt = grid(a, min(b, 0.9999))
        if GW > 0:
            lo_ = tt <= T1
            rhs = np.where(lo_, phi(tt) - RS * GW * GW / 8 * Gpos(tt, RS, GW), 1 + RS * psi(tt, max(RS - GW, 0.0)))
        else:
            rhs = phi(tt)
        pr.cons.append(C.chebvander(tt, D) @ pr.vars[nm] <= rhs - eta)
    E = float(EP())
    EM = RS * EMw(RS, GW) if GW > 0 else 0.0
    if mode == "mu":
        pr.cons.append(pr.vars["e"][0] == E + EM + target)
        pr.cons.append(pr.mu[0] <= 1.0)
        obj = pr.mu[0]
    else:
        if MU0 is not None:
            pr.cons.append(pr.mu[0] == float(MU0))
        obj = pr.vars["e"][0]
    print(f"built {time.time() - t0:.0f}s", flush=True)
    if os.environ.get("PROFILE_BUILD"):          # memory probe: canonicalise only, report peak RSS, exit
        import resource
        r0 = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 30
        data, _, _ = cp.Problem(cp.Maximize(obj), pr.cons).get_problem_data(cp.CLARABEL)
        r1 = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 30
        print(json.dumps(dict(profile=cellspec, D=D, rss_after_build_GB=round(r0, 2), rss_after_canon_GB=round(r1, 2),
                              A_shape=list(data["A"].shape), A_nnz=int(data["A"].nnz), dims=str(data["dims"]),
                              time=round(time.time() - t0))), flush=True)
        return
    for tol in (1e-10, 1e-8, 1e-7):
        try:
            prob = pr.solve(obj, verbose=bool(int(os.environ.get("VERB", "0"))), tol_gap_abs=tol, tol_gap_rel=tol,
                            tol_feas=tol, max_iter=400, max_threads=THREADS, **CLOPTS)
            break
        except cp.error.SolverError as ex:
            print(f"solver failed at tol {tol}: {ex}", flush=True)
    else:
        raise SystemExit("solver failed")
    xs = pr.xs(); xs.update(pr.blocks_value())
    rr = residuals(pr, xs)
    out = {k: np.asarray(v) for k, v in xs.items() if v is not None}
    meta = dict(riesz_s=RS_STR, gw=GW, t1=T1, mu0=MU0, em=EM, cell=cellspec, kind=cell["kind"], lo=cell["lo"], hi=cell.get("hi"), D=D, ker=KER, mode=mode,
                target=target, eta=eta, sizes=info["sizes"], minorants=info["minorants"])
    os.makedirs(os.path.join(HERE, "sol"), exist_ok=True)
    tag = f"{cell['name']}_D{D}_s{RS_STR.replace('/', 'o')}_w{GW:g}_{mode}" + (f"_pieceB{PW_B:g}" if PW_B else "") + (f"_t{target:g}" if target is not None else "") + (f"_mu{MU0}" if MU0 else "")
    np.savez(os.path.join(HERE, "sol", tag + ".npz"), meta=json.dumps(meta), **out)
    e = float(xs["e"][0])
    viol = {}
    for nm, (a, b) in info["minorants"].items():
        tf = np.linspace(a, min(b, 1 - 1e-6), 1_000_001)
        viol[nm] = float((C.chebval(tf, xs[nm]) - phi(tf)).max())
    res = dict(riesz_s=RS_STR, gw=GW, em=EM, mu0=MU0, D=D, tag=tag, status=prob.status, e=e, e_minus_EP=e - E,
               mu=None if pr.mu is None else float(pr.mu.value[0]),
               resid={k: v[0] for k, v in rr.items()}, max_H_minus_phi=viol,
               mineig=min(float(np.linalg.eigvalsh(xs[k])[0]) for k in pr.psdnames),
               time=round(time.time() - t0))
    print(json.dumps(res), flush=True)
    with open(os.path.join(HERE, "results.jsonl"), "a") as fh:
        fh.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], float(sys.argv[3]) if len(sys.argv) > 3 else None)
