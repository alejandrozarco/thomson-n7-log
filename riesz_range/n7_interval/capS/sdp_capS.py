"""[capS: copy of ../cap1/sdp_cap1.py for general s; own Clarabel driver solve_cl() (see NOTES.md)]
[s = 1 adaptation: value-only face face_D12_val.json, first-order contact, kernel (2-2t)^(-S/2)]
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


SYM = int(os.environ.get("SYM", "0"))
# variable permutations o (q(x) = p(x[o])) that fix lambda_A (v <-> t), lambda_B (u <-> v), lambda_G (all of S3)
SYM_GROUP = {"A": [(0, 1, 2), (0, 2, 1)], "B": [(0, 1, 2), (1, 0, 2)], "G": list(PERMS)}


def sym_perm(o, d):
    """Pi_o with z(x[o]) = Pi_o z(x), z = monomials of degree <= d (monos_upto order)."""
    Z = monos_upto(d); idx = {tuple(z): i for i, z in enumerate(Z)}
    P = np.zeros((len(Z), len(Z)))
    for i, z in enumerate(Z):
        nz = [0, 0, 0]
        for slot in range(3):
            nz[o[slot]] += z[slot]
        P[i, idx[tuple(nz)]] = 1
    return P


def isotypic(Rm):
    """Rm: {o: orthogonal k x k matrix} for a subgroup H of S3 acting on R^k.  Returns a list of lists of k x m
    orthonormal matrices; every H-invariant symmetric X equals sum_i sum_{U in list_i} U G_i U^T (G_i = U_i0^T X U_i0)."""
    k = next(iter(Rm.values())).shape[0]
    def eigsp(M, thr=0.5):
        w, V = np.linalg.eigh((M + M.T) / 2)
        return V[:, w > thr]
    if len(Rm) == 1:
        return [[np.eye(k)]]
    if len(Rm) == 2:
        tau = [o for o in Rm if o != (0, 1, 2)][0]
        R = Rm[tau]
        out = [[eigsp(R)], [eigsp(-R)]]
    else:
        assert len(Rm) == 6
        sgn = lambda o: 1 if o in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1
        Pt = sum(Rm.values()) / 6; Ps = sum(sgn(o) * R for o, R in Rm.items()) / 6
        Pstd = np.eye(k) - Pt - Ps
        Ua = eigsp(Pstd @ (np.eye(k) + Rm[(1, 0, 2)]) / 2)
        Ub = (Rm[(1, 2, 0)] @ Ua + Ua / 2) * (2 / np.sqrt(3))
        out = [[eigsp(Pt)], [eigsp(Ps)], [Ua, Ub]]
    U = np.hstack([u for l in out for u in l])
    assert U.shape == (k, k) and np.abs(U.T @ U - np.eye(k)).max() < 1e-9, "isotypic basis not orthonormal"
    # check on a random invariant matrix X = avg R Y R^T: it is rebuilt exactly from its blocks G_i = U_i0^T X U_i0
    Y = np.random.default_rng(0).standard_normal((k, k)); Y = Y + Y.T
    X = sum(R @ Y @ R.T for R in Rm.values()) / len(Rm)
    Xr = sum(u @ (l[0].T @ X @ l[0]) @ u.T for l in out for u in l)
    assert np.abs(X - Xr).max() < 1e-9 * max(1, np.abs(X).max()), "isotypic decomposition does not rebuild X"
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

    def add_identity_sym(self, lp, blocks, tag, reducers):
        """SYM=1: as add_identity, but with the SOS Gram matrices restricted to the symmetric ones and block-diagonalised.
        The identity lambda_tag is invariant under the variable permutations SYM_GROUP[tag] (checked: symtest.py), the
        multipliers are permuted among themselves and the face is permutation invariant (asserted below).  Averaging any
        certificate over the group therefore gives another one (and keeps mu, lambda_min being concave), so restricting to
        invariant Gram matrices loses nothing.  Per orbit of multipliers one representative r with stabiliser H:
            B_r = sum_i sum_{U in Us_i} (Q U) G_i (Q U)^T,      Q = orthonormal basis of range(N_r),
        (isotypic blocks G_i of H: S2 -> 2 blocks, S3 -> trivial, sign, standard (one G for its two copies)), and for the
        other members r' = r o:  B_r' = Pi_o^T B_r Pi_o  (z(x[o]) = Pi_o z(x)).  Only the G_i are solver variables;
        the original reduced blocks B'_r = B_r[free, free] (N echelon, N[free,:] = I) are rebuilt for the sol file, so
        the certificate format, round_capS.py and check_capS.py are unchanged."""
        import scipy.linalg as sla
        grp = SYM_GROUP[tag]
        gs = [g for g, d in blocks]
        img = {}                                   # (r, o) -> r' with g_r(x[o]) = g_r'(x)
        for r, g in enumerate(gs):
            for o in grp:
                gp = PERM_M[o] @ g
                m = [j for j, g2 in enumerate(gs) if np.abs(g2 - gp).max() < 1e-12]
                assert len(m) == 1, (tag, r, o)
                img[r, o] = m[0]
        done = set(); Lcols = {k: np.asarray(M) for k, M in lp.terms.items()}
        Gcols = []                                 # (Gname, m, column block (LOWROWS x m^2))
        self.symmap = getattr(self, "symmap", {})  # original block name -> list of (Gname, W)
        for r in range(len(gs)):
            if r in done or reducers[r].shape[1] == 0:
                continue
            g, d = blocks[r]
            orbit = {}
            for o in grp:
                orbit.setdefault(img[r, o], o)
            done |= set(orbit)
            H = [o for o in grp if img[r, o] == r]
            Q, _ = np.linalg.qr(reducers[r])
            Rm = {o: Q.T @ sym_perm(o, d).T @ Q for o in H}
            for o in H:
                assert np.abs(Rm[o] @ Rm[o].T - np.eye(Q.shape[1])).max() < 1e-9, ("face not invariant", tag, r, o)
            Us = isotypic(Rm)
            for i, ulist in enumerate(Us):
                m = ulist[0].shape[1]
                if m == 0:
                    continue
                Gname = f"{tag}_B{r}_s{i}"
                col = 0
                for r2, o in orbit.items():
                    Pi = sym_perm(o, d)
                    Mg, n = sos_columns(blocks[r2][0], d)
                    Mg = sp.csr_matrix(Mg)[LOWROWS]
                    N2 = reducers[r2]
                    for U in ulist:
                        W = Pi.T @ Q @ U
                        res = W - N2 @ np.linalg.lstsq(N2, W, rcond=None)[0]
                        assert np.abs(res).max() < 1e-9, ("image face mismatch", tag, r, r2)
                        col = col + Mg @ np.kron(W, W)
                        self.symmap.setdefault(f"{tag}_B{r2}", []).append((Gname, W))
                col = np.asarray(col)
                col[np.abs(col) < 1e-11 * np.abs(col).max()] = 0     # float noise of the kron products
                Gcols.append((Gname, m, col))
        Mfull = np.hstack([Lc[LOWROWS] for Lc in Lcols.values()] + [c for (_, _, c) in Gcols])
        Q_, R_, piv = sla.qr(Mfull.T, mode='economic', pivoting=True)
        dg = np.abs(np.diag(R_)); rk = int((dg > 1e-10 * dg[0]).sum())
        sel = np.sort(piv[:rk]); rows = LOWROWS[sel]
        del Q_, R_, Mfull
        self.dropped = getattr(self, "dropped", {}); self.dropped[tag] = len(LOWROWS) - rk
        expr = 0
        for k, Lc in Lcols.items():
            expr = expr + Lc[rows] @ self.vecexpr(k)
        # mu metric (MU_METRIC=1, default): the margin that matters is lambda_min of the ORIGINAL reduced blocks
        # B'_r = T_r D T_r^T (echelon face coordinates; T_r = [W[free]] over the (G_i, W) of block r, D = blockdiag(G_i),
        # standard copies repeated).  B'_r >= mu I <=> D >= mu S_r with S_r = T_r^-1 T_r^-T.
        #  * A, B: S_r is block diagonal and the same for all members of an orbit (the echelon metric is invariant), so
        #    G_i >= mu S_r,ii is EXACTLY B'_r >= mu I.
        #  * G (S3): S_r is not block diagonal (symmetric_metric.py).  Sufficient: D >= mu kappa_r blockdiag(S_r,ii),
        #    kappa_r = lambda_max(blockdiag(S_r,ii)^-1/2 S_r blockdiag^-1/2) (1.66 .. 1.75), one constraint per member r
        #    and per standard copy.  So lambda_min(B'_r) >= mu always; for G it may be up to kappa_r larger.
        #  G_i = Gv_i + mu M_i0 (Gv_i PSD) with M_i0 the first metric; the others as extra LMIs Gv_i + mu (M_i0 - M_ik) >> 0.
        import scipy.linalg as sla2
        self.mumetric = getattr(self, "mumetric", {})
        extra = {}
        if int(os.environ.get("MU_METRIC", "1")):
            free = {k: v["free"] for k, v in json.load(open(os.path.join(HERE, "face_D12_val.json"))).items()}
            mets = {}
            for nm, lst in self.symmap.items():
                if not nm.startswith(tag + "_"):
                    continue
                T = np.hstack([W[free[nm]] for (_, W) in lst]); Ti = np.linalg.inv(T); Sr = Ti @ Ti.T; Sr = (Sr + Sr.T) / 2
                sizes = [W.shape[1] for (_, W) in lst]; idx = np.cumsum([0] + sizes)
                M = np.zeros_like(Sr)
                for a in range(len(sizes)):
                    M[idx[a]:idx[a + 1], idx[a]:idx[a + 1]] = Sr[idx[a]:idx[a + 1], idx[a]:idx[a + 1]]
                kap = max(1.0, float(sla2.eigh(Sr, M, eigvals_only=True)[-1]))
                kap = 1.0 if kap < 1 + 1e-9 else kap * (1 + 1e-9)
                self.kappa = getattr(self, "kappa", {}); self.kappa[nm] = kap
                for a, (Gn, _) in enumerate(lst):
                    Mi = kap * M[idx[a]:idx[a + 1], idx[a]:idx[a + 1]]
                    L = mets.setdefault(Gn, [])
                    if not any(np.abs(Mi - X).max() <= 1e-10 * np.abs(X).max() for X in L):
                        L.append(Mi)
            for Gn, L in mets.items():
                self.mumetric[Gn] = L[0]; extra[Gn] = L[1:]
        rhs = 0
        for (Gname, m, c) in Gcols:
            Gv = self.psd(Gname, m)
            rhs = rhs + c[sel] @ cp.vec(Gv, order='C')
            if self.use_mu:
                M = self.mumetric.get(Gname, np.eye(m))
                rhs = rhs + (c[sel] @ M.ravel()) * self.mu[0]
                for Mk in extra.get(Gname, []):
                    self.cons.append(Gv + self.mu[0] * (M - Mk) >> 0)
        nx = sum(len(v) for v in extra.values())
        if nx:
            print(f"[sym] {tag}: {nx} extra metric LMIs; kappa max {max(self.kappa[k] for k in self.kappa if k.startswith(tag + '_')):.4f}", flush=True)
        self.cons.append(expr + lp.const[rows] == rhs)
        self.sos.append((tag, lp, []))
        print(f"[sym] {tag}: G blocks {[m for (_, m, _) in Gcols]}, rows kept {rk}/{len(LOWROWS)}", flush=True)

    def finish(self):
        pass

    def blocks_value(self):
        """actual block values (X + mu I); with SYM also the original reduced blocks B'_r = B_r[free, free]."""
        mu = float(self.mu.value[0]) if self.use_mu else 0.0
        mm = getattr(self, "mumetric", {})
        out = {nm: self.vars[nm].value + mu * mm.get(nm, np.eye(self.vars[nm].shape[0])) for nm in self.psdnames}
        if getattr(self, "symmap", None):
            free = {k: v["free"] for k, v in json.load(open(os.path.join(HERE, "face_D12_val.json"))).items()}
            for nm, lst in self.symmap.items():
                B = sum(W @ out[Gn] @ W.T for (Gn, W) in lst)
                f = free[nm]
                out[nm] = (B[np.ix_(f, f)] + B[np.ix_(f, f)].T) / 2
        return out


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
        # SYM_TAGS (default ABG): identities reduced by symmetry (G unreduced: exact mu metric, but 3.6 GB peak)
        (pr.add_identity_sym if SYM and tag in os.environ.get("SYM_TAGS", "ABG") else pr.add_identity)(lp, blocks, tag, reds)
    # ---- contact constraints (exact targets)
    def row(t, j):
        return C.chebval(t, C.chebder(np.eye(D + 1), j) if j else np.eye(D + 1))
    pr.cons.append(row(0.0, 1) @ pr.vars["hB"] == dphi(0.0, 1))     # s = 1: first-order contact only
    for c in (C1, C2):
        pr.cons.append(row(c, 1) @ pr.vars["hC"] == dphi(c, 1))
    if mode == "mu":
        pr.cons.append(pr.mu[0] <= float(os.environ.get("MUCAP", "10")))
        VS = float(os.environ.get("VALSHIFT", "0"))   # diagnostic: pin values at phi(P) - VS (e = E(P) - 21 VS)
        pr.cons.append(row(-1.0, 0) @ pr.vars["hA"] == phi(-1.0) - VS)
        pr.cons.append(row(0.0, 0) @ pr.vars["hB"] == phi(0.0) - VS)
        for c in (C1, C2):
            pr.cons.append(row(c, 0) @ pr.vars["hC"] == phi(c) - VS)
    # ---- contact curvature, so that H <= phi survives rounding near the touching points (f = phi - H):
    #   B: f'' >= 2 K4 on |t| <= 0.05 (s = 1: quadratic contact);  C: f'' >= 2 K2 on |t - c| <= 0.02;
    #   A: f' >= KA on [-1, -0.998] (linear contact at the endpoint)
    K4, K2, KA = CONTACT
    fder = dphi
    def dvander(t, k):
        return np.array([C.chebval(x, C.chebder(np.eye(D + 1), k)) for x in t])
    EXCL = int(os.environ.get("EXCL", "0"))   # 1: floors always on (also K = 0), no samples inside the windows
    if K4 > 0 or EXCL:
        tt = np.linspace(-0.05, 0.05, 101)
        pr.cons.append(dvander(tt, 2) @ pr.vars["hB"] <= fder(tt, 2) - 2 * K4)
    if K2 > 0 or EXCL:
        for c in (C1, C2):
            tt = np.linspace(c - 0.02, c + 0.02, 81)
            pr.cons.append(dvander(tt, 2) @ pr.vars["hC"] <= fder(tt, 2) - 2 * K2)
    if KA > 0 or EXCL:
        tt = np.linspace(-1.0, -0.998, 41)
        pr.cons.append(dvander(tt, 1) @ pr.vars["hA"] <= fder(tt, 1) - KA)
    # ---- minorant by sampling: H_X <= phi - m_X on the sample grid of minorant_grid()
    tA, tBB, tBC = minorant_grid(nsamp)
    mA, mB, mC = minorant_margins(tA, tBB, tBC, margin)
    pr.margin_profile = MARGIN_PROFILE_INFO
    pr.cons.append(C.chebvander(tA, D) @ pr.vars["hA"] <= phi(tA) - mA)
    PHICAP = float(os.environ.get("PHICAP", "20"))   # H <= min(phi, PHICAP): stronger, keeps the rows well scaled
    for nm, tB, mX in (("hB", tBB, mB), ("hC", tBC, mC)):
        pr.cons.append(C.chebvander(tB, D) @ pr.vars[nm] <= np.minimum(phi(tB), PHICAP) - mX)
    pr.finish()
    return pr


def minorant_grid(nsamp=1500):
    """sample points of the minorant rows: tA (H_A on [-1, -0.99]), tBB (H_B), tBC (H_C) on [-1, 0.9999];
    depends on the env knobs DENSE and EXCL only (and nsamp)."""
    lo, hi = -1.0, -0.99
    tA = np.unique(np.concatenate([sample_grid(lo, hi, 80, [], 0.0), -1 + np.logspace(-8, -2.5, 60)]))
    tB = sample_grid(lo, 0.9999, nsamp, [0.0, C1, C2, -1.0], 0.02, 400)
    tB = np.unique(np.concatenate([tB] + [c + s * np.logspace(-6, -2, 40) for c in (0.0, C1, C2) for s in (-1, 1)]))
    DENSE = int(os.environ.get("DENSE", "0"))   # extra uniform samples on [0.5, 0.995] (phi'' is large there: the Chebyshev
    if DENSE:                                    # spacing ~8e-4 near t = 0.93 let H_B dip 4.7e-6 below phi between samples)
        tB = np.unique(np.concatenate([tB, np.linspace(0.5, 0.995, DENSE)]))
    if int(os.environ.get("EXCL", "0")):
        # near-active sample rows inside the contact windows (slack ~ f''/2 d^2 down to 1e-13, and the exact
        # duplicate t = -1 of the pin H_A(-1) = phi(-1)) make the KKT system degenerate; inside the windows
        # f >= 0 already follows from the pinned value + slope and the curvature / slope floor rows.
        tA = tA[tA >= -0.998]
        tBB = tB[np.abs(tB) >= 0.05]
        tBC = tB[(np.abs(tB - C1) >= 0.02) & (np.abs(tB - C2) >= 0.02)]
    else:
        tBB = tBC = tB
    return tA, tBB, tBC


def contact_weights(tA, tBB, tBC):
    """contact-distance weights of the margin (they vanish at the touching points, where f = phi - H = 0 is pinned).
    A: min(1, (t+1)/0.002) in both modes.  CONTACT_W (env):
      "all" (default; every node up to 2026-11-07): B, C: min(1, (d/0.05)^4), d = distance to the nearest of 0, c1, c2;
      "kernel": each kernel only by its own contacts, reaching 1 at its own window radius:
                B: min(1, (|t|/0.05)^4);  C: min(1, (d/0.02)^4), d = distance to the nearer of c1, c2."""
    def w(t, pts, r):
        d = np.min(np.abs(np.subtract.outer(t, np.array(pts))), axis=1)
        return np.minimum(1.0, (d / r) ** 4)
    mode = os.environ.get("CONTACT_W", "all")
    assert mode in ("all", "kernel"), f"CONTACT_W must be all or kernel, not {mode}"
    wA = np.minimum(1.0, (tA + 1) / 0.002)
    if mode == "kernel":
        return wA, w(tBB, [0.0], 0.05), w(tBC, [C1, C2], 0.02)
    return wA, w(tBB, [0.0, C1, C2], 0.05), w(tBC, [0.0, C1, C2], 0.05)


MARGIN_PROFILE_INFO = None


def load_margin_profile(path):
    """MARGIN_PROFILE=<file> (.json or .npz): per-kernel margin profiles m_X(t) >= 0 for X = A, B, C, given at points
    t_X (strictly increasing).  JSON: {"s": "2/3", "A": {"t": [...], "m": [...]}, "B": {...}, "C": {...}};
    npz: arrays tA, mA, tB, mB, tC, mC (and optionally s).  An "s" entry must equal RIESZ_S.  Returns {X: (t, m)}."""
    import hashlib
    raw = open(path, "rb").read()
    if path.endswith(".npz"):
        z = np.load(path, allow_pickle=False)
        prof = {X: (np.asarray(z["t" + X], float), np.asarray(z["m" + X], float)) for X in "ABC"}
        s_ = str(z["s"]) if "s" in z.files else None
    else:
        J = json.loads(raw)
        prof = {X: (np.asarray(J[X]["t"], float), np.asarray(J[X]["m"], float)) for X in "ABC"}
        s_ = J.get("s")
    if s_ is not None:
        assert abs(float(Fr(str(s_))) - S) < 1e-12, f"margin profile is for s = {s_}, RIESZ_S = {S}"
    for X, (tt, mm) in prof.items():
        assert tt.ndim == 1 and tt.shape == mm.shape and len(tt) >= 2, f"profile {X}: bad shape"
        assert np.all(np.diff(tt) > 0), f"profile {X}: t not strictly increasing"
        assert np.all(np.isfinite(mm)) and np.all(mm >= 0), f"profile {X}: margins must be finite and >= 0"
    info = dict(file=os.path.abspath(path), sha256=hashlib.sha256(raw).hexdigest(), contact_w=os.environ.get("CONTACT_W", "all"),
                max={X: float(prof[X][1].max()) for X in "ABC"}, min={X: float(prof[X][1].min()) for X in "ABC"})
    return prof, info


def minorant_margins(tA, tBB, tBC, margin):
    """margins m_X at the sample points: scalar `margin` (as before) or MARGIN_PROFILE, times the contact weights.
    The profile is linearly interpolated onto the samples (exact where it is given on the grid of `sdp_capS.py grid`);
    every sample must lie in the profile's t range."""
    global MARGIN_PROFILE_INFO
    wA, wB, wC = contact_weights(tA, tBB, tBC)
    path = os.environ.get("MARGIN_PROFILE")
    if not path:
        if margin == 0:
            return 0.0, 0.0, 0.0
        return margin * wA, margin * wB, margin * wC
    assert margin == 0, "MARGIN_PROFILE replaces the scalar margin: pass margin 0"
    prof, info = load_margin_profile(path)
    out = []
    for X, tt, w in (("A", tA, wA), ("B", tBB, wB), ("C", tBC, wC)):
        pt, pm = prof[X]
        assert pt[0] <= tt.min() + 1e-12 and tt.max() <= pt[-1] + 1e-12, \
            f"profile {X} covers [{pt[0]}, {pt[-1]}], samples need [{tt.min()}, {tt.max()}]"
        m = np.interp(tt, pt, pm)
        info.setdefault("lost_to_weights", {})[X] = float(np.max(m * (1 - w)))   # margin removed by the contact weights
        out.append(m * w)
    MARGIN_PROFILE_INFO = info
    print(f"[margin profile] {info['file']} sha256 {info['sha256'][:12]}; CONTACT_W {info['contact_w']}; max A/B/C "
          f"{info['max']['A']:.3g}/{info['max']['B']:.3g}/{info['max']['C']:.3g}; largest margin removed by the contact "
          f"weights A/B/C {info['lost_to_weights']['A']:.3g}/{info['lost_to_weights']['B']:.3g}/"
          f"{info['lost_to_weights']['C']:.3g}", flush=True)
    return tuple(out)


def solve_dualform(A, b, q, dims, nz, st):
    """Solve the conic DUAL of  min q^T x, A x + s = b, s in K  (K = Zero^nz x R+^nn x PSD...) and recover x.
    Why: in the primal the Gram entries are cvxpy variables x_g with PSD rows s_S = T x_g (T = -A_S,g, one entry per
    row/column) and ~1350 equality rows couple all of them; the KKT fill (faer and qdldl alike) is ~5 GB.  Writing
    z_S = T^-T (A_Z,g^T z_Z + q_g) the dual has only the variables y = (z_Z, z_N) (~7k) with the PSD cones as slacks
    (image form), which factorises cheaply.  Dual (Clarabel form):
        min  b_Z^T z_Z + b_N^T z_N
        s.t. [A_Z,f^T  A_N,f^T] y = -q_f                    (zero cone; one row per non-Gram primal column)
             -z_N + s = 0,  s >= 0
             -[T^-T A_Z,g^T, 0] y + s = T^-T q_g,  s in PSD   (same PSD cones, same svec convention)
    Recovery from its multipliers z' = (z'_f, z'_N, z'_S):  x_f = -z'_f,  x_g = T^-1 z'_S  (and s_N = z'_N)."""
    import clarabel
    nn = dims.nonneg
    assert not dims.soc and not getattr(dims, "exp", 0) and not getattr(dims, "p3d", []), "unexpected cones"
    A = A.tocsr()
    AZ, AN, AS = A[:nz], A[nz:nz + nn], A[nz + nn:]
    bZ, bN, bS = b[:nz], b[nz:nz + nn], b[nz + nn:]
    assert np.abs(bS).max(initial=0) == 0
    gcols = np.unique(AS.tocoo().col)
    fmask = np.ones(A.shape[1], bool); fmask[gcols] = False
    fcols = np.where(fmask)[0]
    assert len(gcols) == AS.shape[0], "PSD rows and Gram columns do not match one to one"
    assert abs(AN[:, gcols]).sum() == 0, "nonneg rows touch Gram columns"
    T = (-AS[:, gcols]).tocsr()
    assert np.all(np.diff(T.indptr) == 1) and len(np.unique(T.indices)) == T.shape[0], "T is not monomial"
    # T = P D (row r has its entry at column c_r):  T^-1 = D^-1 P^T
    Tinv = sp.csr_matrix((1.0 / T.data, (T.indices, np.arange(T.shape[0]))), shape=T.shape)
    TinvT = Tinv.T.tocsr()
    AZg, AZf, ANf = AZ[:, gcols], AZ[:, fcols], AN[:, fcols]
    ny = nz + nn; nS = AS.shape[0]; nf = len(fcols)
    A1 = sp.hstack([AZf.T, ANf.T]).tocsr()
    A2 = sp.hstack([sp.csr_matrix((nn, nz)), -sp.identity(nn, format="csr")]).tocsr()
    A3 = sp.hstack([-(TinvT @ AZg.T), sp.csr_matrix((nS, nn))]).tocsr()
    Ad = sp.vstack([A1, A2, A3]).tocsc()
    bd = np.concatenate([-q[fcols], np.zeros(nn), TinvT @ q[gcols]])
    cd = np.concatenate([bZ, bN])
    cones = [clarabel.ZeroConeT(nf), clarabel.NonnegativeConeT(nn)] + [clarabel.PSDTriangleConeT(k) for k in dims.psd]
    Pd = sp.csc_matrix((ny, ny))
    print(f"[dualform] vars {ny}, rows {Ad.shape[0]} (zero {nf}, nonneg {nn}, psd {nS}), nnz {Ad.nnz}", flush=True)
    sol = clarabel.DefaultSolver(Pd, cd, Ad, bd, cones, st).solve()
    zd = np.array(sol.z); y = np.array(sol.x)
    x = np.zeros(A.shape[1])
    x[fcols] = -zd[:nf]
    x[gcols] = Tinv @ zd[nf + nn:]
    z = np.concatenate([y[:nz], y[nz:], TinvT @ (AZg.T @ y[:nz] + q[gcols])])
    return x, z, sol


def solve_cl(pr, objective, verbose=False):
    """Clarabel directly on the cvxpy problem data, after removing linearly dependent equality rows.
    Never raises on a bad status (returns it).  env knobs (defaults = cap1 behaviour):
      TOL (1e-10), MAXIT (400), THREADS (2), EQUI (1), EQUI_IT (10), STATREG (1e-8), DYNREG (1),
      PRESOLVE (1), CHORDAL (1), RTOL (1e-11; rank tol of the equality rows), ROWSCALE (0: off; 1: scale
      every inequality row of the linear (nonneg) cone to unit inf-norm, and every equality row likewise)."""
    import copy, clarabel, scipy.linalg as sla
    from types import SimpleNamespace
    from cvxpy.reductions.solvers.conic_solvers.clarabel_conif import dims_to_solver_cones
    g = lambda k, d: os.environ.get(k, d)
    prob = cp.Problem(cp.Maximize(objective), pr.cons)
    data, chain, inv = prob.get_problem_data(cp.CLARABEL)
    A = data["A"].tocsr().copy(); b = data["b"].copy(); q = data["c"]; dims0 = data["dims"]; nz = dims0.zero
    A.data[np.abs(A.data) < 1e-14] = 0; A.eliminate_zeros()
    # memory: R-only pivoted QR, no Q and no dense least-squares (the Mac limit is 3 GB RSS per solve);
    # consistency of the dropped rows is checked after the solve (eq_resid_all)
    R, piv = sla.qr(A[:nz].toarray().T, mode="r", pivoting=True, overwrite_a=True)
    dg = np.abs(np.diag(R)); rk = int((dg > float(g("RTOL", "1e-11")) * dg[0]).sum())
    keep = np.sort(piv[:rk])
    del R, piv
    import gc; gc.collect()
    pr.eq_drop = (nz - rk,)
    rows = np.concatenate([keep, np.arange(nz, A.shape[0])])
    dims = copy.copy(dims0); dims.zero = rk
    A2 = A[rows].tocsr(); b2 = b[rows].copy()
    nlin = rk + dims.nonneg
    rs = np.ones(A2.shape[0])
    if int(g("ROWSCALE", "0")):
        rn = np.asarray(abs(A2[:nlin]).max(axis=1).todense()).ravel()
        rs[:nlin] = 1.0 / np.where(rn > 0, rn, 1.0)
        A2 = sp.diags(rs) @ A2; b2 = rs * b2
    st = clarabel.DefaultSettings()
    st.verbose = verbose; st.max_iter = int(g("MAXIT", "400")); st.max_threads = int(g("THREADS", "1"))
    tol = float(g("TOL", "1e-10"))
    st.tol_gap_abs = tol; st.tol_gap_rel = tol; st.tol_feas = tol
    st.equilibrate_enable = bool(int(g("EQUI", "1"))); st.equilibrate_max_iter = int(g("EQUI_IT", "10"))
    st.static_regularization_constant = float(g("STATREG", "1e-8"))
    st.dynamic_regularization_enable = bool(int(g("DYNREG", "1")))
    st.presolve_enable = bool(int(g("PRESOLVE", "1")))
    st.chordal_decomposition_enable = bool(int(g("CHORDAL", "1")))
    st.equilibrate_min_scaling = float(g("EQ_MIN", "1e-4")); st.equilibrate_max_scaling = float(g("EQ_MAX", "1e4"))
    st.iterative_refinement_max_iter = int(g("IR_MAX", "10"))
    st.max_step_fraction = float(g("MAXSTEP", "0.99"))
    st.reduced_tol_gap_abs = float(g("RTOL_GAP", "5e-5")); st.reduced_tol_gap_rel = float(g("RTOL_GAP", "5e-5"))
    st.reduced_tol_feas = float(g("RTOL_FEAS", "1e-4"))
    if g("DSM", ""):
        st.direct_solve_method = g("DSM", "")
    n = A.shape[1]
    Pm = data.get("P"); Pm = sp.csc_matrix((n, n)) if Pm is None else sp.csc_matrix(Pm)
    A2c = A2.tocsc(); del A2; gc.collect()
    if g("FORM", "primal") == "dual":
        assert not int(g("ROWSCALE", "0"))
        xsol, zsol, sol = solve_dualform(A2c, b2, q, dims, rk, st)
    else:
        sol = clarabel.DefaultSolver(Pm, q, A2c, b2, dims_to_solver_cones(dims), st).solve()
        xsol = np.array(sol.x); zsol = np.array(sol.z)
    eq_resid_all = float(np.abs(A[:nz] @ xsol - b[:nz]).max()) if np.all(np.isfinite(xsol)) else float("nan")
    z = np.zeros(A.shape[0]); z[rows] = zsol * rs
    status = str(sol.status)
    ns = SimpleNamespace(status=sol.status, solve_time=sol.solve_time, iterations=sol.iterations,
                         obj_val=sol.obj_val, x=xsol, z=z)
    try:
        prob.unpack_results(ns, chain, inv)
        ok = True
    except Exception as ex:   # bad status: unpack the primal by hand so it can still be inspected
        ok = False
    pr.prob = prob
    return dict(status=status, ok=ok, iters=int(sol.iterations), solve_time=float(sol.solve_time),
                obj=float(sol.obj_val), obj_dual=float(sol.obj_val_dual), r_prim=float(sol.r_prim), r_dual=float(sol.r_dual), nlin=int(nlin), nrows=int(A2c.shape[0]), ncols=int(n),
                Arange=[float(abs(A2c).data.min()), float(abs(A2c).data.max())], eq_resid_all=eq_resid_all,
                brange=[float(np.abs(b2[b2 != 0]).min()), float(np.abs(b2).max())])


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "grid":
        # python3 sdp_capS.py grid OUT.json : the minorant sample grid (same env knobs DENSE, EXCL as the solve) and the
        # contact weights, for building a MARGIN_PROFILE on exactly these points; no SDP is built
        tA, tBB, tBC = minorant_grid()
        wA, wB, wC = contact_weights(tA, tBB, tBC)
        json.dump(dict(s=S, DENSE=os.environ.get("DENSE", "0"), EXCL=os.environ.get("EXCL", "0"),
                       CONTACT_W=os.environ.get("CONTACT_W", "all"),
                       A=dict(t=tA.tolist(), w=wA.tolist()), B=dict(t=tBB.tolist(), w=wB.tolist()),
                       C=dict(t=tBC.tolist(), w=wC.tolist())), open(sys.argv[2], "w"))
        print(f"wrote {sys.argv[2]}: {len(tA)} / {len(tBB)} / {len(tBC)} samples (A / B / C)")
        sys.exit(0)
    margin = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
    t0 = time.time()
    pr = build(mode, margin)
    print("built", time.time() - t0, flush=True)
    obj = pr.vars["e"][0] if mode == "maxe" else pr.mu[0]
    pr.sos = []   # LinPoly copies only needed for residual_report (maxe); frees memory before the solve
    if os.environ.get("SOLVER", "CLARABEL") == "SCS":
        # memory-light first-order alternative (no dense W^T W blocks in a KKT system)
        prob = cp.Problem(cp.Maximize(obj), pr.cons)
        ts = time.time()
        prob.solve(solver=cp.SCS, verbose=bool(int(os.environ.get("VERB", "1"))), eps_abs=float(os.environ.get("TOL", "1e-9")),
                   eps_rel=float(os.environ.get("TOL", "1e-9")), max_iters=int(os.environ.get("MAXIT", "1000000")),
                   time_limit_secs=float(os.environ.get("TLIM", "1800")))
        pr.prob = prob
        info = dict(status=str(prob.status), ok=prob.status in ("optimal", "optimal_inaccurate"), solver="SCS",
                    solve_time=time.time() - ts, iters=int(prob.solver_stats.num_iters or 0),
                    obj=float(prob.value) if prob.value is not None else None)
    else:
        info = solve_cl(pr, obj, verbose=bool(int(os.environ.get("VERB", "1"))))
    E = float(phi(-1.0) + 10 * phi(0.0) + 5 * phi(C1) + 5 * phi(C2))
    res = dict(s=S, mode=mode, margin=margin, contact=CONTACT, phicap=float(os.environ.get("PHICAP", "20")),
               knobs={k: os.environ[k] for k in ("TOL", "MAXIT", "EQUI", "EQUI_IT", "STATREG", "DYNREG", "PRESOLVE",
                                                 "CHORDAL", "RTOL", "ROWSCALE", "VALSHIFT", "MUCAP", "EXCL", "EQ_MIN", "EQ_MAX", "IR_MAX", "MAXSTEP", "RTOL_GAP", "RTOL_FEAS", "DSM", "PHICAP", "FORM", "SOLVER", "TLIM", "SYM", "DENSE", "SYM_TAGS", "MU_METRIC", "MARGIN_PROFILE", "CONTACT_W") if k in os.environ},
               EP=E, **info, eq_drop=getattr(pr, "eq_drop", None), time=time.time() - t0,
               margin_profile=getattr(pr, "margin_profile", None), contact_w=os.environ.get("CONTACT_W", "all"))
    if info["ok"]:
        xs = pr.xs()
        xs.update(pr.blocks_value())
        out = {k: np.asarray(v) for k, v in xs.items()}
        if pr.mu is not None:
            out["mu"] = np.array(pr.mu.value)
        np.savez(os.path.join(HERE, f"sol_capS_s{S}_{mode}{os.environ.get('TAG', '')}.npz"), **out)
        mine = {k: float(np.linalg.eigvalsh(xs[k])[0]) for k in pr.psdnames}
        res.update(e=float(xs["e"][0]), e_minus_EP=float(xs["e"][0]) - E,
                   mu=None if pr.mu is None else float(pr.mu.value[0]),
                   mineig_min=min(mine.values()), mineig_argmin=min(mine, key=mine.get),
                   mineig_orig=min(float(np.linalg.eigvalsh(xs[k])[0]) for k in xs if k.startswith("F") or
                                   (k[:3] in ("A_B", "B_B", "G_B") and "_s" not in k)),
                   gaps=dict(A=float(phi(-1.0) - C.chebval(-1.0, xs["hA"])), B=float(phi(0.0) - C.chebval(0.0, xs["hB"])),
                             C1=float(phi(C1) - C.chebval(C1, xs["hC"])), C2=float(phi(C2) - C.chebval(C2, xs["hC"]))))
    print(json.dumps(res))
    with open(os.path.join(HERE, os.environ.get("RESFILE", "results_runs.jsonl")), "a") as fh:
        fh.write(json.dumps(res) + "\n")
