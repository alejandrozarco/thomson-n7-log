"""[cellsS] Joint SDP for a certificate polynomial in s (Bernstein form) on a cell, s in [a, b].

Normalised gauge: psi_s = (phi_s - 1)/s, Ehat_s(P) = (E_s(P) - 21)/s. Control certificates Chat_0..Chat_m, each
satisfying the (s-independent, linear homogeneous) cell identities with PSD blocks; the certificate at s is
    Chat(s) = sum_k b_k(lambda) Chat_k,   b_k = Bernstein basis of degree m, lambda = (s-a)/(b-a),
so identities hold identically in s and the blocks are PSD for every s in [a, b] automatically (b_k >= 0).
Semi-infinite constraints, discretised:  Hhat(s_j, t) <= psi_{s_j}(t) - ETA/s_j on (s-grid) x (t-grid),
and  s_j (ehat(s_j) - Ehat_{s_j}(P)) >= tau  on a fine s-grid.

usage: RIESZ_A=1/2 RIESZ_B=3/2 BDEG=m [POLYD THREADS ETA NSH NSE MU0] python3 sdp_bern.py CELL maxm
       ... python3 sdp_bern.py CELL mu TAU        (fix tau, maximise the common eigenvalue floor mu)
m = 1 is the joint version of the linear-interpolation design.  output: sol/bern_*.npz, results.jsonl
"""
import os, sys, json, time
from fractions import Fraction as Fr
from math import comb
os.environ.setdefault("RIESZ_S", "1")      # dummy for sdp_cellS import (kernel unused here)
import numpy as np
from numpy.polynomial import chebyshev as C
import cvxpy as cp
import mpmath as mp
import sdp_cellS as S

A_ = Fr(os.environ["RIESZ_A"]); B_ = Fr(os.environ["RIESZ_B"])
a, b = float(A_), float(B_)
M = int(os.environ.get("BDEG", "2"))
ETA = float(os.environ.get("ETA", "1e-6"))
NSH = int(os.environ.get("NSH", str(2 * M + 5)))     # s-points for the minorant constraints
NSE = int(os.environ.get("NSE", "81"))               # s-points for the energy constraint
MU0 = os.environ.get("MU0")
HERE = os.path.dirname(os.path.abspath(__file__))


def bern(lam):
    return np.array([comb(M, k) * lam ** k * (1 - lam) ** (M - k) for k in range(M + 1)])


def psi(t, s):
    u = 2 - 2 * np.asarray(t, float)
    return (u ** (-s / 2) - 1) / s


def EPhat(s):
    s5 = mp.sqrt(5)
    f = lambda t: (2 - 2 * t) ** (-mp.mpf(s) / 2)
    E = f(-1) + 10 * f(0) + 5 * f((s5 - 1) / 4) + 5 * f((-s5 - 1) / 4)
    return float((E - 21) / s)


def sgrid(n):
    # Chebyshev-Lobatto points on [a, b] (ends included)
    return a + (b - a) * (1 - np.cos(np.pi * np.arange(n) / (n - 1))) / 2


def main(cellspec, mode, tau=None):
    t0 = time.time()
    cell = S.parse_cell(cellspec)
    use_mu = (mode == "mu") or (MU0 is not None)
    prs, infos = [], []
    for k in range(M + 1):
        pr = S.Prob(use_mu)
        info = S.build_case1(pr, cell["lo"]) if cell["kind"] == "case1" else S.build_slab(pr, cell["lo"], cell["hi"])
        prs.append(pr); infos.append(info)
    cons = sum((pr.cons for pr in prs), [])
    mu = cp.Variable(1, name="mu") if use_mu else None
    if use_mu:
        cons += [pr.mu == mu for pr in prs]
        cons += [mu <= 1.0] if mode == "mu" else [mu == float(MU0)]
    # minorants
    for nm, (lo, hi) in infos[0]["minorants"].items():
        tt = S.grid(lo, min(hi, 0.9999))
        V = C.chebvander(tt, S.D)
        for s in sgrid(NSH):
            w = bern((s - a) / (b - a))
            Hs = sum(w[k] * (V @ prs[k].vars[nm]) for k in range(M + 1))
            cons.append(Hs <= psi(tt, s) - ETA / s)
    # energy
    tauv = cp.Variable(1, name="tau")
    for s in sgrid(NSE):
        w = bern((s - a) / (b - a))
        es = sum(w[k] * prs[k].vars["e"][0] for k in range(M + 1))
        cons.append(s * (es - EPhat(s)) >= tauv[0])
    if mode == "mu":
        cons.append(tauv[0] == tau); obj = mu[0]
    else:
        obj = tauv[0]
    print(f"built {time.time() - t0:.0f}s, {len(cons)} constraint groups", flush=True)
    prob = cp.Problem(cp.Maximize(obj), cons)
    for tol in (1e-10, 1e-8, 1e-7):
        try:
            prob.solve(solver="CLARABEL", verbose=bool(int(os.environ.get("VERB", "0"))), tol_gap_abs=tol,
                       tol_gap_rel=tol, tol_feas=tol, max_iter=400, max_threads=S.THREADS)
            break
        except cp.error.SolverError as ex:
            print(f"solver failed at tol {tol}: {ex}", flush=True)
    else:
        raise SystemExit("solver failed")
    tag = f"bern_{cell['name']}_D{S.D}_a{str(A_).replace('/', 'o')}_b{str(B_).replace('/', 'o')}_m{M}_{mode}" + \
          (f"_t{tau:g}" if tau is not None else "") + (f"_mu{MU0}" if MU0 else "")
    out = {}
    mins = []
    for k, pr in enumerate(prs):
        xs = pr.xs(); xs.update(pr.blocks_value())
        for nm, v in xs.items():
            if v is not None:
                out[f"c{k}__{nm}"] = np.asarray(v)
        mins.append(min(float(np.linalg.eigvalsh(xs[q])[0]) for q in pr.psdnames))
    # a-posteriori margins on a fine s grid
    sf = np.linspace(a, b, 401)
    emarg = []
    for s in sf:
        w = bern((s - a) / (b - a))
        emarg.append(s * (sum(w[k] * float(prs[k].vars["e"].value[0]) for k in range(M + 1)) - EPhat(s)))
    hviol = -1e9
    for nm, (lo, hi) in infos[0]["minorants"].items():
        tf = np.linspace(lo, min(hi, 1 - 1e-6), 20001)
        for s in np.linspace(a, b, 41):
            w = bern((s - a) / (b - a))
            Hs = sum(w[k] * C.chebval(tf, prs[k].vars[nm].value) for k in range(M + 1))
            hviol = max(hviol, float((Hs - psi(tf, s)).max()))
    meta = dict(cell=cellspec, kind=cell["kind"], lo=cell["lo"], hi=cell.get("hi"), D=S.D, a=str(A_), b=str(B_),
                m=M, mode=mode, tau=tau, eta=ETA, sizes=infos[0]["sizes"], minorants=infos[0]["minorants"])
    os.makedirs(os.path.join(HERE, "sol"), exist_ok=True)
    np.savez(os.path.join(HERE, "sol", tag + ".npz"), meta=json.dumps(meta), **out)
    res = dict(tag=tag, status=prob.status, tau=float(tauv.value[0]), mu=None if mu is None else float(mu.value[0]),
               min_emargin_fine=min(emarg), max_Hhat_minus_psi_fine=hviol, mineig=min(mins),
               time=round(time.time() - t0))
    print(json.dumps(res), flush=True)
    with open(os.path.join(HERE, "results.jsonl"), "a") as fh:
        fh.write(json.dumps(res) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], float(sys.argv[3]) if len(sys.argv) > 3 else None)
