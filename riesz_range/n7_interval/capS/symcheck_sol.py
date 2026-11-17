"""SYM consistency check: take a NON-symmetric float solution (sdp_capS.py without SYM), average every SOS Gram matrix
over the symmetry group, project to the SYM variables (G_i = W^T B W for the first W of each block), and evaluate the
SYM problem's identity constraints at that point.  Small residuals = the reduction maps certificates to certificates.
usage: SYM=1 RIESZ_S=1 python3 symcheck_sol.py sol_capS_s1.0_mu_base.npz"""
import os, sys, json
os.environ["SYM"] = "1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import sdp_capS as S
sol = np.load(sys.argv[1])
pr = S.build("mu", 0.0)
face = json.load(open(os.path.join(S.HERE, "face_D12_val.json")))
def full(nm):    # monomial-basis Gram B = N B' N^T
    N = np.array([[float(S.Fr(x)) for x in row] for row in face[nm]["N"]])
    return N @ sol[nm] @ N.T
# averaged full Grams: for B_r' = Pi_o^T B_r Pi_o: avg over group of the images
Gval = {}
for nm, lst in pr.symmap.items():
    pass
# the SYM variables only need the representative's G: G_i = U^T (avg B_r) U with W = Pi^T Q U for each member;
# avg over the orbit: G_i = mean over members r' and their W of W^T B_r' W
acc = {}
for nm, lst in pr.symmap.items():
    B = full(nm)
    seen = set()
    for Gn, W in lst:
        acc.setdefault(Gn, []).append(W.T @ B @ W)
for Gn, L in acc.items():
    pr.vars[Gn].value = sum(L) / len(L)
for k in sol.files:
    if k in pr.vars and k not in acc and k != "mu":
        v = sol[k]
        pr.vars[k].value = v if pr.vars[k].shape == v.shape else v.reshape(pr.vars[k].shape)
pr.mu.value = np.zeros(1)
mu0 = float(sol["mu"][0]) if "mu" in sol.files else 0.0
# F blocks in sol are X + mu I already (blocks_value); the SOS blocks too; so mu = 0 here
for c in pr.cons[:3]:
    print("identity constraint residual", float(np.abs(c.residual).max()), "rows", c.shape)
mins = {Gn: float(np.linalg.eigvalsh(pr.vars[Gn].value)[0]) for Gn in acc}
print("min eig of averaged G blocks", min(mins.values()), min(mins, key=mins.get))
