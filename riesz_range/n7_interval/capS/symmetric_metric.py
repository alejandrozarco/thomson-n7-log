"""Is the echelon metric compatible with the symmetry?  For every original block r: B'_r = T_r D T_r^T with
T_r = [W[free] for each (G_i, W) of r] and D = blockdiag(G_i, with the standard copies repeated).  B'_r >= mu I  <=>
D >= mu S_r,  S_r = T_r^-1 T_r^-T.  Reports: off-block-diagonal part of S_r, copy mismatch, and whether S agrees
across the orbit (same G_i)."""
import os, sys, json
os.environ["SYM"] = "1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import sdp_capS as S
pr = S.build("mu", 0.0)
free = {k: v["free"] for k, v in json.load(open(os.path.join(S.HERE, "face_D12_val.json"))).items()}
Sdiag = {}
worst_off = 0
for nm, lst in sorted(pr.symmap.items()):
    T = np.hstack([W[free[nm]] for (_, W) in lst])
    Sr = np.linalg.inv(T) @ np.linalg.inv(T).T
    sizes = [W.shape[1] for (_, W) in lst]; idx = np.cumsum([0] + sizes)
    off = Sr.copy()
    for a in range(len(sizes)):
        off[idx[a]:idx[a+1], idx[a]:idx[a+1]] = 0
    rel = np.abs(off).max() / np.abs(Sr).max()
    worst_off = max(worst_off, rel)
    for a, (Gn, W) in enumerate(lst):
        blk = Sr[idx[a]:idx[a+1], idx[a]:idx[a+1]]
        Sdiag.setdefault(Gn, []).append((nm, blk))
    print(f"{nm}: k={T.shape[0]} cond(T)={np.linalg.cond(T):.3g} sigma_min(T)^2={np.linalg.svd(T, compute_uv=False)[-1]**2:.3g} offblock/max={rel:.2e}")
print("worst off-block ratio", worst_off)
mis = 0
for Gn, L in Sdiag.items():
    d = max(np.abs(b - L[0][1]).max() / np.abs(L[0][1]).max() for _, b in L)
    mis = max(mis, d)
    if d > 1e-9: print("S differs within", Gn, [n for n, _ in L], f"{d:.2e}")
print("worst copy/orbit mismatch", mis)
# loss factor of the block-diagonal majorant: kappa_r = lambda_max(M^-1/2 S_r M^-1/2), M = blockdiag(S_ii)
import scipy.linalg as sla
for nm, lst in sorted(pr.symmap.items()):
    T = np.hstack([W[free[nm]] for (_, W) in lst]); Ti = np.linalg.inv(T); Sr = Ti @ Ti.T
    sizes = [W.shape[1] for (_, W) in lst]; idx = np.cumsum([0] + sizes)
    M = np.zeros_like(Sr)
    for a in range(len(sizes)):
        M[idx[a]:idx[a+1], idx[a]:idx[a+1]] = Sr[idx[a]:idx[a+1], idx[a]:idx[a+1]]
    kap = sla.eigh(Sr, M, eigvals_only=True)[-1]
    print(f"kappa {nm}: {kap:.4f}")
