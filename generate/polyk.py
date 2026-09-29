"""Small toolkit for the three-point SDP bounds (rebuild of PAPER.md sections 4-6).

Polynomials in (u,v,t) of total degree <= D are dense flat vectors indexed by (a,b,c) in
{0..D}^3 (coefficient of u^a v^b t^c).  Linear maps (variable permutations, substitutions,
multiplication by a fixed polynomial) are precomputed sparse matrices.  A LinPoly is a
polynomial whose coefficients are affine in the SDP decision variables:
    p = const + sum_name M[name] @ x[name].
"""
import itertools
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
from numpy.polynomial import chebyshev as C

import os as _os
D = int(_os.environ.get("POLYD", "10"))
L = D + 1
N3 = L ** 3


def fidx(a, b, c):
    return (a * L + b) * L + c


EXPS = np.array(list(itertools.product(range(L), repeat=3)))  # row k <-> fidx
TOTDEG = EXPS.sum(1)
LOWROWS = np.where(TOTDEG <= D)[0]
HIGHROWS = np.where(TOTDEG > D)[0]


# ---------------------------------------------------------------- dense polys
def pconst(c):
    p = np.zeros(N3); p[0] = c; return p


def pmono(a, b, c, coef=1.0):
    p = np.zeros(N3); p[fidx(a, b, c)] = coef; return p


U = pmono(1, 0, 0); V = pmono(0, 1, 0); T = pmono(0, 0, 1); ONE = pconst(1.0)


def pmul(p, q):
    A = p.reshape(L, L, L); B = q.reshape(L, L, L)
    out = np.zeros((2 * L - 1,) * 3)
    for (a, b, c) in zip(*np.nonzero(A)):
        out[a:a + L, b:b + L, c:c + L] += A[a, b, c] * B
    assert np.abs(out[L:, :, :]).max(initial=0) == 0 and np.abs(out[:, L:, :]).max(initial=0) == 0 \
        and np.abs(out[:, :, L:]).max(initial=0) == 0, "degree overflow"
    r = out[:L, :L, :L].reshape(-1)
    assert np.abs(r[HIGHROWS]).max(initial=0) == 0, "total degree overflow"
    return r


def ppow(p, k):
    r = ONE.copy()
    for _ in range(k):
        r = pmul(r, p)
    return r


def peval(p, u, v, t):
    A = p.reshape(L, L, L)
    pu = np.power.outer(np.atleast_1d(u), np.arange(L))
    pv = np.power.outer(np.atleast_1d(v), np.arange(L))
    pt = np.power.outer(np.atleast_1d(t), np.arange(L))
    return np.einsum('abc,na,nb,nc->n', A, pu, pv, pt)


# ---------------------------------------------------------------- linear maps
def perm_matrix(order):
    """q(x0,x1,x2) = p(x[order[0]], x[order[1]], x[order[2]])."""
    rows, cols = [], []
    for k, e in enumerate(EXPS):
        ne = [0, 0, 0]
        for slot in range(3):
            ne[order[slot]] += e[slot]
        if max(ne) <= D:
            rows.append(fidx(*ne)); cols.append(k)
    return sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(N3, N3))


def subst_matrix(spec):
    """spec[slot] in {0,1,2} (variable index) or a float constant.  q = p(spec)."""
    rows, cols, vals = [], [], []
    for k, e in enumerate(EXPS):
        ne = [0, 0, 0]; coef = 1.0
        for slot in range(3):
            s = spec[slot]
            if isinstance(s, int):
                ne[s] += e[slot]
            else:
                coef *= float(s) ** e[slot]
        if coef != 0 and max(ne) <= D and sum(ne) <= D:
            rows.append(fidx(*ne)); cols.append(k); vals.append(coef)
    return sp.csr_matrix((vals, (rows, cols)), shape=(N3, N3))


def univ_embed(var, deg=D):
    """N3 x (deg+1) matrix: monomial coefficients h_j -> polynomial h(x_var)."""
    M = np.zeros((N3, deg + 1))
    for j in range(deg + 1):
        e = [0, 0, 0]; e[var] = j
        M[fidx(*e), j] = 1.0
    return M


def cheb2mono(deg=D):
    """(deg+1)x(deg+1): chebyshev coefficients -> monomial coefficients."""
    M = np.zeros((deg + 1, deg + 1))
    for j in range(deg + 1):
        e = np.zeros(deg + 1); e[j] = 1
        m = C.cheb2poly(e); M[:len(m), j] = m
    return M


PERMS = list(itertools.permutations(range(3)))
PERM_M = {o: perm_matrix(o) for o in PERMS}
SYM_AVG = sum(PERM_M.values()) / 6.0


# ---------------------------------------------------------------- kernels
def Qk(kmax):
    Q = [ONE.copy(), T - pmul(U, V)]
    W = pmul(ONE - pmul(U, U), ONE - pmul(V, V))
    while len(Q) <= kmax:
        Q.append(2 * pmul(T - pmul(U, V), Q[-1]) - pmul(W, Q[-2]))
    return Q


def Yk_columns(k, m):
    """N3 x m^2 : column a*m+b = u^a v^b Q_k (unsymmetrised)."""
    Q = Qk(k)[k]
    cols = np.zeros((N3, m * m))
    for a in range(m):
        for b in range(m):
            cols[:, a * m + b] = pmul(pmul(ppow(U, a), ppow(V, b)), Q)
    return cols


# ---------------------------------------------------------------- LinPoly
class LinPoly:
    def __init__(self, terms=None, const=None):
        self.terms = dict(terms or {})
        self.const = np.zeros(N3) if const is None else const.copy()

    def copy(self):
        return LinPoly({k: v.copy() for k, v in self.terms.items()}, self.const)

    def __add__(self, o):
        r = self.copy()
        if isinstance(o, LinPoly):
            for k, v in o.terms.items():
                r.terms[k] = r.terms[k] + v if k in r.terms else v.copy()
            r.const = r.const + o.const
        else:
            r.const = r.const + o
        return r

    __radd__ = __add__

    def __neg__(self):
        return self * (-1.0)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, c):
        return LinPoly({k: v * c for k, v in self.terms.items()}, self.const * c)

    __rmul__ = __mul__

    def apply(self, M):
        """apply linear map (N3xN3) to the polynomial."""
        return LinPoly({k: np.asarray(M @ v) for k, v in self.terms.items()}, M @ self.const)

    def value(self, xs):
        p = self.const.copy()
        for k, v in self.terms.items():
            p = p + v @ np.ravel(xs[k])
        return p


# ---------------------------------------------------------------- SOS blocks
def sample_grid(lo, hi, n, focus=(), width=0.01, nloc=200):
    """Chebyshev nodes on [lo,hi] plus uniform local grids of nloc points in +-width around focus
    points (where H is expected to touch phi)."""
    g = [(lo + hi) / 2 + (hi - lo) / 2 * np.cos(np.linspace(0, np.pi, n))]
    for c in focus:
        if width > 0:
            g.append(np.linspace(max(lo, c - width), min(hi, c + width), nloc))
    g = np.unique(np.concatenate(g))
    return g[(g >= lo) & (g <= hi)]


def monos_upto(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


def _m2c_1d():
    M = np.zeros((L, L))
    for j in range(L):
        e = np.zeros(L); e[j] = 1
        c = C.poly2cheb(e); M[:len(c), j] = c
    return M


M2C_1D = _m2c_1d()
M2C = sp.csr_matrix(np.kron(np.kron(M2C_1D, M2C_1D), M2C_1D))  # monomial -> tensor Chebyshev coeffs
BASIS = "mono"   # identity rows and z-vectors in Chebyshev tensor basis ("mono" = plain monomials)


def sos_columns_cheb(g, d):
    """N3 x n^2 sparse (in Chebyshev coefficient space) for g * z^T B z with
    z_i = T_a(u)T_b(v)T_c(t), a+b+c <= d.  Uses T_x T_y T_w = 1/4 sum over the 4 sign patterns."""
    Z = np.array(monos_upto(d)); n = len(Z)
    gc = M2C @ g
    gnz = np.nonzero(np.abs(gc) > 1e-15)[0]
    ii, jj = np.meshgrid(np.arange(n), np.arange(n), indexing='ij'); ii = ii.ravel(); jj = jj.ravel()
    X = Z[ii]; Y = Z[jj]
    rows, cols, vals = [], [], []
    for k in gnz:
        W = EXPS[k]
        cand = [X + Y + W, np.abs(X + Y - W), np.abs(X - Y) + W, np.abs(np.abs(X - Y) - W)]
        for c0 in range(4):
            for c1 in range(4):
                for c2 in range(4):
                    e0 = cand[c0][:, 0]; e1 = cand[c1][:, 1]; e2 = cand[c2][:, 2]
                    rows.append((e0 * L + e1) * L + e2); cols.append(ii * n + jj)
                    vals.append(np.full(len(ii), gc[k] / 64.0))
    M = sp.coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
                      shape=(N3, n * n)).tocsr()
    return M, n


def sos_columns(g, d):
    """N3 x n^2 sparse matrix for g * z^T B z, z = monomials of degree <= d."""
    Z = np.array(monos_upto(d)); n = len(Z)
    gnz = np.nonzero(g)[0]
    rows, cols, vals = [], [], []
    ii, jj = np.meshgrid(np.arange(n), np.arange(n), indexing='ij')
    ii = ii.ravel(); jj = jj.ravel()
    E = Z[ii] + Z[jj]
    for k in gnz:
        e = E + EXPS[k]
        assert e.max() <= D and e.sum(1).max() <= D
        rows.append((e[:, 0] * L + e[:, 1]) * L + e[:, 2]); cols.append(ii * n + jj)
        vals.append(np.full(len(ii), g[k]))
    M = sp.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
                      shape=(N3, n * n))
    return M, n


class SOSProblem:
    """collects cvxpy variables / constraints."""

    def __init__(self):
        self.vars = {}
        self.cons = []
        self.sos = []  # (name, block list)

    def psd(self, name, n):
        X = cp.Variable((n, n), PSD=True, name=name)
        self.vars[name] = X
        return X

    def free(self, name, n):
        x = cp.Variable(n, name=name)
        self.vars[name] = x
        return x

    def vecexpr(self, name):
        X = self.vars[name]
        return cp.vec(X, order='C') if X.ndim == 2 else X

    def add_identity(self, lp, blocks, tag, reducers=None):
        """lp == sum_r g_r z_r^T B_r z_r  as polynomial identity; blocks: list of (g, d).
        lp is in monomial coordinates; rows are compared in the BASIS coordinates.
        reducers[r] (optional, n x n' matrix N): facial reduction B_r = N B'_r N^T."""
        for k, M in lp.terms.items():
            assert np.abs(M[HIGHROWS]).max(initial=0) < 1e-12, (tag, k)
        Tm = M2C if BASIS == "cheb" else sp.identity(N3, format='csr')
        rows = LOWROWS
        Lcols = {k: np.asarray(Tm @ M) for k, M in lp.terms.items()}
        Rcols = []
        for r, (g, d) in enumerate(blocks):
            Mg, n = (sos_columns_cheb if BASIS == "cheb" else sos_columns)(g, d)
            N = None if reducers is None else reducers[r]
            if N is not None:
                if N.shape[1] == 0:
                    continue
                Mg = sp.csr_matrix(Mg @ np.kron(N, N))
                n = N.shape[1]
            Rcols.append((r, g, d, N, Mg, n))
        if reducers is not None:
            # facial reduction makes some coefficient rows linearly dependent: keep a row basis
            import scipy.linalg as sla
            Mfull = np.hstack([Lc[LOWROWS] for Lc in Lcols.values()] +
                              [Mg[LOWROWS].toarray() for (_, _, _, _, Mg, _) in Rcols])
            Q, R, piv = sla.qr(Mfull.T, mode='economic', pivoting=True)
            dg = np.abs(np.diag(R)); rk = int((dg > 1e-10 * dg[0]).sum())
            rows = LOWROWS[np.sort(piv[:rk])]
            self.dropped = getattr(self, "dropped", {}); self.dropped[tag] = len(LOWROWS) - rk
        lhs = (Tm @ lp.const)[rows]
        expr = 0
        for k, Lc in Lcols.items():
            expr = expr + Lc[rows] @ self.vecexpr(k)
        rhs = 0
        Bs = []
        for (r, g, d, N, Mg, n) in Rcols:
            B = self.psd(f"{tag}_B{r}", n)
            Bs.append((B, Mg, g, d, N))
            rhs = rhs + Mg[rows] @ cp.vec(B, order='C')
        self.cons.append(expr + lhs == rhs)
        self.sos.append((tag, lp, Bs))

    def solve(self, objective, solver='CLARABEL', verbose=False, **kw):
        prob = cp.Problem(cp.Maximize(objective), self.cons)
        opts = dict(tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11, max_iter=500, max_threads=2) \
            if solver == 'CLARABEL' else {}
        opts.update(kw)
        prob.solve(solver=solver, verbose=verbose, **opts)
        self.prob = prob
        return prob

    def solve_rowreduced(self, objective, verbose=False, tol=1e-10, max_iter=500, rtol=1e-11):
        """Solve with Clarabel directly after removing linearly dependent equality rows
        (facial reduction makes the equality system rank deficient, which breaks the KKT solve)."""
        import copy, clarabel, scipy.linalg as sla
        from types import SimpleNamespace
        from cvxpy.reductions.solvers.conic_solvers.clarabel_conif import dims_to_solver_cones
        prob = cp.Problem(cp.Maximize(objective), self.cons)
        data, chain, inv = prob.get_problem_data(cp.CLARABEL)
        A = data["A"].tocsr().copy(); b = data["b"]; q = data["c"]; nz = data["dims"].zero
        A.data[np.abs(A.data) < 1e-14] = 0; A.eliminate_zeros()
        Aeq = A[:nz].toarray()
        _, R, piv = sla.qr(Aeq.T, mode="economic", pivoting=True)
        dg = np.abs(np.diag(R)); rk = int((dg > rtol * dg[0]).sum())
        keep = np.sort(piv[:rk])
        x_ls = np.linalg.lstsq(Aeq[keep], b[:nz][keep], rcond=None)[0]
        self.eq_drop = (nz - rk, float(np.abs(Aeq @ x_ls - b[:nz]).max()))
        rows = np.concatenate([keep, np.arange(nz, A.shape[0])])
        dims = copy.copy(data["dims"]); dims.zero = rk
        st = clarabel.DefaultSettings()
        st.verbose = verbose; st.max_iter = max_iter; st.max_threads = 2
        st.tol_gap_abs = tol; st.tol_gap_rel = tol; st.tol_feas = tol
        n = A.shape[1]
        Pm = data.get("P"); Pm = sp.csc_matrix((n, n)) if Pm is None else sp.csc_matrix(Pm)
        sol = clarabel.DefaultSolver(Pm, q, A[rows].tocsc(), b[rows], dims_to_solver_cones(dims), st).solve()
        z = np.zeros(A.shape[0]); z[rows] = np.array(sol.z)
        ns = SimpleNamespace(status=sol.status, solve_time=sol.solve_time, iterations=sol.iterations,
                             obj_val=sol.obj_val, x=np.array(sol.x), z=z)
        prob.unpack_results(ns, chain, inv)
        self.prob = prob
        return prob

    def xs(self):
        return {k: v.value for k, v in self.vars.items()}

    def residual_report(self):
        """For each identity: l1 norm of (lp - SOS) coefficients, and PSD defect bound on the box."""
        xs = self.xs(); out = {}
        for tag, lp, Bs in self.sos:
            p = lp.value(xs)
            if BASIS == "cheb":
                p = M2C @ p   # |T_j| <= 1 on the box, so l1 of Chebyshev coeffs bounds |p|
            rhs = np.zeros(N3); defect = 0.0
            for B, Mg, g, d, N in Bs:
                Bv = B.value
                rhs = rhs + Mg @ Bv.ravel()
                lam = np.linalg.eigvalsh((Bv + Bv.T) / 2)[0]
                if lam < 0:
                    nz = len(monos_upto(d))
                    defect += -lam * nz * np.abs(g).sum()  # |z|^2<=nz on box, |g|<=l1(g)
            out[tag] = (np.abs(p - rhs).sum(), defect)
        return out


def min_eigs(xs, names):
    return {n: float(np.linalg.eigvalsh(xs[n])[0]) for n in names}
