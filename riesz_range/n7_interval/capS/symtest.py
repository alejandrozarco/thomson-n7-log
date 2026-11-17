"""SYM check (2026-11-06): lambda_A, lambda_B, lambda_G are invariant under v<->t, u<->v, S3 (acting on symmetric Gram
variables), the multipliers are permuted among themselves, and the faces satisfy Pi_o range(N_r) = range(N_r o).
usage: python3 ../heavy_lock.py python3 symtest.py   (run from capS/; output: logs/symtest.txt)"""
import sys, os
sys.path.insert(0, os.getcwd())
import numpy as np
import sdp_capS as S
from polyk import PERM_M
cap = {}
def grab(self, lp, blocks, tag, reds):
    cap[tag] = (lp, blocks, reds)
S.Prob.add_identity = grab
pr = S.build("mu", 0.0)
def symcols(M, name):
    M = np.asarray(M if not hasattr(M, "toarray") else M.toarray())
    if name in pr.psdnames or name.startswith("F"):
        k = int(round(np.sqrt(M.shape[1])))
        if k * k == M.shape[1]:
            sw = np.arange(k * k).reshape(k, k).T.ravel()
            return (M + M[:, sw]) / 2
    return M
for tag, perms in (("A", [(0,2,1)]), ("B", [(1,0,2)]), ("G", [(1,0,2),(0,2,1)])):
    lp, blocks, reds = cap[tag]
    for o in perms:
        q = lp.apply(PERM_M[o])
        for k in lp.terms:
            d = np.abs(symcols(q.terms[k], k) - symcols(lp.terms[k], k)).max()
            if d > 1e-9: print(tag, o, k, d)
        print(tag, o, "checked")
# face invariance: for block r and its image r', P_o^T range(N_r) == range(N_r')
from polyk import monos_upto
face = S.load_face()
import spec
mults = spec.multipliers()
def Pi(o, d):
    Z = monos_upto(d); idx = {tuple(z): i for i, z in enumerate(Z)}
    P = np.zeros((len(Z), len(Z)))
    for i, z in enumerate(Z):
        nz = [0, 0, 0]
        for slot in range(3): nz[o[slot]] += z[slot]
        P[idx[tuple(nz)], i] = 1   # z(x[o])_i = x[o]^z = x^{nz}: row i of Pi has 1 at nz
    return P.T
for tag, perms in (("A", [(0,2,1)]), ("B", [(1,0,2)]), ("G", [(1,0,2),(0,2,1)])):
    lp, blocks, reds = cap[tag]
    from polyk import PERM_M as PM
    for o in perms:
        for r, (g, d) in enumerate(blocks):
            gp = PM[o] @ g
            r2 = [j for j, (g2, _) in enumerate(blocks) if np.abs(g2 - gp).max() < 1e-12][0]
            P = Pi(o, d)
            N1, N2 = reds[r], reds[r2]
            X = P @ N1  # candidate image
            res = X - N2 @ np.linalg.lstsq(N2, X, rcond=None)[0]
            X2 = P.T @ N1
            res2 = X2 - N2 @ np.linalg.lstsq(N2, X2, rcond=None)[0]
            print(tag, o, r, "->", r2, "resid P", np.abs(res).max(), "P^T", np.abs(res2).max())
