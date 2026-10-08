"""[s = 1 adaptation: value-only face face_D12_val.json, first-order contact, kernel (2-2t)^(-S/2)]
Float (Clarabel) solve of the degree-12 RIESZ s=2 cap SDP, t01 in [-1, -99/100], on the exact face of
../hp/face.py (value + soft/pucker conditions; kernel independent), with exact contact constraints:
    H_B^(j)(0) = phi^(j)(0) = j!/2, j = 1,2,3   (3rd-order contact; phi = 1/(2-2t))
    H_C'(c_i)  = phi'(c_i) = 1/(2(1-c_i)^2),  i = 1,2
(adapted copy of ../hp/sdp_soft.py; only the kernel-specific lines differ)
usage:
    python3 sdp_soft.py maxe            # values free, maximise e            -> sol_maxe.npz
    python3 sdp_soft.py mu [margin]     # values pinned at phi(P), maximise the smallest eigenvalue mu of
                                        # all reduced blocks (interior point for rounding) -> sol_mu.npz
env: VERB=1 for solver output; CONTACT=K4,K2,KA curvature floors (default 0.003,0.002,0.002):
     f'''' >= 24 K4 on |t|<=.05 (B), f'' >= 2 K2 on |t-c|<=.02 (C), f' >= KA on [-1,-.998] (A), f = phi - H.
"""
import os, sys, json, time, warnings, math
os.environ.setdefault("POLYD", "12")
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "sdp"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numpy.polynomial import chebyshev as C
import cvxpy as cp
import scipy.sparse as sp
import mpmath as mp
from fractions import Fraction as Fr
import polyk
from polyk import *
import spec

warnings.filterwarnings("ignore")
assert polyk.D == spec.D
mp.mp.dps = 40
C1 = (np.sqrt(5) - 1) / 4; C2 = -(1 + np.sqrt(5)) / 4
CONTACT = tuple(float(x) for x in os.environ.get("CONTACT", "0.003,0.002,0.002").split(","))
HERE = os.path.dirname(os.path.abspath(__file__))


S = float(os.environ.get("RIESZ_S", "1"))


def phi(t):
    return (2 - 2 * np.asarray(t, float)) ** (-S / 2)


def dphi(t, k):
    """k-th derivative of (2-2t)^(-S/2): prod_{i<k} (S + 2i) * (2-2t)^(-S/2-k)."""
    c = 1.0
    for i in range(k):
        c *= S + 2 * i
    return c * (2 - 2 * np.asarray(t, float)) ** (-S / 2 - k)


def load_face():
    js = json.load(open(os.path.join(HERE, "face_D12_val.json")))
    out = {}
    for k, v in js.items():
        n = v["n"]; kept = len(v["free"])
        N = np.array([[float(Fr(x)) for x in row] for row in v["N"]]) if kept else np.zeros((n, 0))
        out[k] = N.reshape(n, kept)
    return out


class Prob(SOSProblem):
    """PSD blocks declared as symmetric variables; B - mu I >> 0 added at the end (mu = 0 -> plain PSD)."""

    def __init__(self, use_mu):
        super().__init__()
        self.use_mu = use_mu
        self.mu = cp.Variable(1, name="mu") if use_mu else None
        self.psdnames = []

    def psd(self, name, n):
        X = cp.Variable((n, n), PSD=True, name=name)   # with mu: the block is X + mu I
        self.vars[name] = X; self.psdnames.append(name)
        return X

    def add_identity(self, lp, blocks, tag, reducers):
        """as SOSProblem.add_identity (monomial basis), with sparse kron(N, N)."""
        import scipy.linalg as sla
        rows = LOWROWS
        Lcols = {k: np.asarray(M) for k, M in lp.terms.items()}
        Rcols = []
        for r, (g, d) in enumerate(blocks):
            Mg, n = sos_columns(g, d)
            N = reducers[r]
            if N.shape[1] == 0:
                continue
            Ns = sp.csr_matrix(N)
            Mg = sp.csr_matrix(Mg @ sp.kron(Ns, Ns, format="csr"))
            Rcols.append((r, g, d, N, Mg, N.shape[1]))
        Mfull = np.hstack([Lc[LOWROWS] for Lc in Lcols.values()] + [Mg[LOWROWS].toarray() for (_, _, _, _, Mg, _) in Rcols])
        Q, R, piv = sla.qr(Mfull.T, mode='economic', pivoting=True)
        dg = np.abs(np.diag(R)); rk = int((dg > 1e-10 * dg[0]).sum())
        rows = LOWROWS[np.sort(piv[:rk])]
        self.dropped = getattr(self, "dropped", {}); self.dropped[tag] = len(LOWROWS) - rk
        lhs = lp.const[rows]
        expr = 0
        for k, Lc in Lcols.items():
            expr = expr + Lc[rows] @ self.vecexpr(k)
        rhs = 0; Bs = []
        for (r, g, d, N, Mg, n) in Rcols:
            B = self.psd(f"{tag}_B{r}", n)
            Bs.append((B, Mg, g, d, None))
            rhs = rhs + Mg[rows] @ cp.vec(B, order='C')
            if self.use_mu:
                rhs = rhs + (Mg[rows] @ np.eye(n).ravel()) * self.mu[0]
        self.cons.append(expr + lhs == rhs)
        self.sos.append((tag, lp, Bs))

    def finish(self):
        pass

    def blocks_value(self):
        """actual block values (X + mu I)."""
        mu = float(self.mu.value[0]) if self.use_mu else 0.0
        return {nm: self.vars[nm].value + mu * np.eye(self.vars[nm].shape[0]) for nm in self.psdnames}


def univ(name, var):
    return LinPoly({name: univ_embed(var) @ cheb2mono()})


def cst(name, c=1.0):
    return LinPoly({name: pconst(c)[:, None]})


def to_var(lp_u, var):
    order = {0: (0, 1, 2), 1: (1, 0, 2), 2: (2, 1, 0)}[var]
    return lp_u.apply(PERM_M[order])


def pypoly_to_dense(p):
    out = np.zeros(N3)
    for (a, b, c), v in p.items():
        out[fidx(a, b, c)] += float(v)
    return out


def build(mode, margin=0.0, nsamp=1500):
    face = load_face()
    pr = Prob(mode == "mu")
    if mode == "mu":
        pr.vars["mu"] = pr.mu
    sizes = spec.SIZES
    forms = {}
    for X in "PR":
        f = LinPoly()
        for k, m in enumerate(sizes):
            N = face[f"F{X}{k}"]
            if N.shape[1] == 0:
                continue
            cols = Yk_columns(k, m) @ np.kron(N, N)
            pr.psd(f"F{X}{k}", N.shape[1])
            f = f + LinPoly({f"F{X}{k}": cols})
            if mode == "mu":
                f = f + LinPoly({"mu": (cols @ np.eye(N.shape[1]).ravel())[:, None]})
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
    lamA = PsiA * 0.2 + to_var(pBa, 1) + to_var(pBa, 2) - ca \
        - 2 * (sP + P(sP, (0, 2, 1)) + P(sR, (1, 2, 0)))
    QB = (PsiB - pBa) * 0.25
    lamB = QB + to_var(QB, 1) + to_var(pCb, 2) - cb \
        - 2 * (sP + P(sR, (0, 2, 1)) + P(sR, (1, 2, 0)))
    QC = (PsiC - 2 * pCb) * (1.0 / 3)
    lamG = QC + to_var(QC, 1) + to_var(QC, 2) - cg \
        - 2 * (sR + P(sR, (0, 2, 1)) + P(sR, (1, 2, 0)))
    mults = spec.multipliers()
    for tag, lp in (("A", lamA), ("B", lamB), ("G", lamG)):
        blocks = [(pypoly_to_dense(g), d) for (_, g, d) in mults[tag]]
        reds = [face[f"{tag}_B{r}"] for r in range(len(blocks))]
        pr.add_identity(lp, blocks, tag, reds)
    # ---- contact constraints (exact targets)
    def row(t, j):
        return C.chebval(t, C.chebder(np.eye(D + 1), j) if j else np.eye(D + 1))
    pr.cons.append(row(0.0, 1) @ pr.vars["hB"] == dphi(0.0, 1))     # s = 1: first-order contact only
    for c in (C1, C2):
        pr.cons.append(row(c, 1) @ pr.vars["hC"] == dphi(c, 1))
    if mode == "mu":
        pr.cons.append(pr.mu[0] <= 10.0)
        pr.cons.append(row(-1.0, 0) @ pr.vars["hA"] == phi(-1.0))
        pr.cons.append(row(0.0, 0) @ pr.vars["hB"] == phi(0.0))
        for c in (C1, C2):
            pr.cons.append(row(c, 0) @ pr.vars["hC"] == phi(c))
    # ---- contact curvature, so that H <= phi survives rounding near the touching points (f = phi - H):
    #   B: f'' >= 2 K4 on |t| <= 0.05 (s = 1: quadratic contact);  C: f'' >= 2 K2 on |t - c| <= 0.02;
    #   A: f' >= KA on [-1, -0.998] (linear contact at the endpoint)
    K4, K2, KA = CONTACT
    fder = dphi
    def dvander(t, k):
        return np.array([C.chebval(x, C.chebder(np.eye(D + 1), k)) for x in t])
    if K4 > 0:
        tt = np.linspace(-0.05, 0.05, 101)
        pr.cons.append(dvander(tt, 2) @ pr.vars["hB"] <= fder(tt, 2) - 2 * K4)
    if K2 > 0:
        for c in (C1, C2):
            tt = np.linspace(c - 0.02, c + 0.02, 81)
            pr.cons.append(dvander(tt, 2) @ pr.vars["hC"] <= fder(tt, 2) - 2 * K2)
    if KA > 0:
        tt = np.linspace(-1.0, -0.998, 41)
        pr.cons.append(dvander(tt, 1) @ pr.vars["hA"] <= fder(tt, 1) - KA)
    # ---- minorant by sampling
    lo, hi = -1.0, -0.99
    tA = np.unique(np.concatenate([sample_grid(lo, hi, 80, [], 0.0), -1 + np.logspace(-8, -2.5, 60)]))
    tB = sample_grid(lo, 0.9999, nsamp, [0.0, C1, C2, -1.0], 0.02, 400)
    tB = np.unique(np.concatenate([tB] + [c + s * np.logspace(-6, -2, 40) for c in (0.0, C1, C2) for s in (-1, 1)]))

    def marg(t):
        if margin == 0:
            return 0.0
        d = np.min(np.abs(np.subtract.outer(t, np.array([0.0, C1, C2]))), axis=1)
        return margin * np.minimum(1.0, (d / 0.05) ** 4)
    pr.cons.append(C.chebvander(tA, D) @ pr.vars["hA"] <= phi(tA) - (margin * np.minimum(1, (tA + 1) / 0.002) if margin else 0))
    PHICAP = float(os.environ.get("PHICAP", "20"))   # H <= min(phi, PHICAP): stronger, keeps the rows well scaled
    for nm in ("hB", "hC"):
        pr.cons.append(C.chebvander(tB, D) @ pr.vars[nm] <= np.minimum(phi(tB), PHICAP) - marg(tB))
    pr.finish()
    return pr


if __name__ == "__main__":
    mode = sys.argv[1]
    margin = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
    t0 = time.time()
    pr = build(mode, margin)
    print("built", time.time() - t0, flush=True)
    obj = pr.vars["e"][0] if mode == "maxe" else pr.mu[0]
    prob = pr.solve_rowreduced(obj, verbose=bool(int(os.environ.get("VERB", "1"))), tol=1e-10, max_iter=400)
    xs = pr.xs()
    xs.update(pr.blocks_value())
    E = float(phi(-1.0) + 10 * phi(0.0) + 5 * phi(C1) + 5 * phi(C2))
    out = {k: np.asarray(v) for k, v in xs.items()}
    if pr.mu is not None:
        out["mu"] = np.array(pr.mu.value)
    np.savez(os.path.join(HERE, f"sol_cap1_s{S}_{mode}{os.environ.get('TAG', '')}.npz"), **out)
    rr = pr.residual_report() if mode == "maxe" else {k: (float("nan"), 0) for k in "ABG"}
    res = dict(mode=mode, margin=margin, contact=CONTACT, status=prob.status, e=float(xs["e"][0]), e_minus_EP=float(xs["e"][0]) - E,
               mu=None if pr.mu is None else float(pr.mu.value[0]), eq_drop=getattr(pr, "eq_drop", None),
               resid={k: rr[k][0] for k in rr},
               mineig={k: float(np.linalg.eigvalsh(xs[k])[0]) for k in pr.psdnames},
               gaps=dict(A=float(phi(-1.0) - C.chebval(-1.0, xs["hA"])), B=float(phi(0.0) - C.chebval(0.0, xs["hB"])),
                         C1=float(phi(C1) - C.chebval(C1, xs["hC"])), C2=float(phi(C2) - C.chebval(C2, xs["hC"]))),
               time=time.time() - t0)
    print(json.dumps(res))
    with open(os.path.join(HERE, "results_cap1.jsonl"), "a") as fh:
        fh.write(json.dumps(res) + "\n")
