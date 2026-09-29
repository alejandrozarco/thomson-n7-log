"""Rigorous check of the 1-D minorant inequalities H_X <= phi(t) = -1/2 log(2-2t) for the cap certificate,
by ball arithmetic (python-flint / arb, 256 bits), plus the contact constants used for coercivity.

usage: python3 checkers/check_minorant.py [certificates/cert_cap_log_D12.json] [delta]

Ranges: H_A on [-1, -99/100];  H_B, H_C on [-1, 1).   f_X := phi - H_X.
Contact windows (Taylor with exact vanishing derivatives, which check_cert.py verifies exactly):
  B at 0:        f(0) = eta_B > 0, f'(0)=f''(0)=f'''(0)=0  =>  f >= eta_B + (min f''''/24) t^4 on [-rB, rB]
  C at c1, c2:   f(c) = eta_C > 0, f'(c)=0                  =>  f >= eta_C + (min f''/2)(t-c)^2
  A at -1:       f(-1) = eta_A > 0                          =>  f >= eta_A + (min f')(t+1)   (if min f' > 0)
Elsewhere: adaptive bisection with the mean-value form f(m) - |f'(I)| rad(I) > 0.
Near t = 1: phi is increasing and -> +inf, so on [1-eps, 1) f >= phi(1-eps) - max H.
Coercivity: with delta >= E(P) - e, report tau_X such that f_X <= delta  =>  |t - touch| <= tau_X.
"""
import json, os, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq

flint.ctx.prec = 256


def A(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


def poly_eval(coefs, t, der=0):
    """k-th derivative of sum c_j t^j on the ball t (Horner)."""
    cs = list(coefs)
    for _ in range(der):
        cs = [j * cs[j] for j in range(1, len(cs))]
    acc = arb(0)
    for cj in reversed(cs):
        acc = acc * t + cj
    return acc


def phi_der(t, k):
    if k == 0:
        return -(2 - 2 * t).log() / 2
    fac = 1
    for j in range(1, k):
        fac *= j
    return arb(fac) / (2 * (1 - t) ** k)


def iv(a, b):
    """ball containing [a,b] (a,b Fractions or floats)."""
    a = A(a); b = A(b)
    m = (a + b) / 2
    r = (b - a) / 2
    return arb(m.mid(), r.upper() + m.rad())


def lower(x):
    return float(x.lower())


def f_lower_mv(H, a, b):
    """rigorous lower bound of phi - H on [a, b] (mean value form)."""
    I = iv(a, b)
    m = (A(a) + A(b)) / 2
    fm = phi_der(m, 0) - poly_eval(H, m)
    d1 = phi_der(I, 1) - poly_eval(H, I, 1)
    h = (A(b) - A(a)) / 2
    return fm - abs(d1) * h


def cover(H, a, b, n0=64, maxdepth=40, need=0.0, stats=None):
    """prove f > need on [a,b]; returns min certified lower bound (float) over the pieces."""
    stack = [(Fr(a) + (Fr(b) - Fr(a)) * k / n0, Fr(a) + (Fr(b) - Fr(a)) * (k + 1) / n0, 0) for k in range(n0)]
    worst = float("inf"); npieces = 0
    while stack:
        lo, hi, dep = stack.pop()
        lb = f_lower_mv(H, lo, hi)
        if lb > need:
            worst = min(worst, float(lb.lower())); npieces += 1
            continue
        if dep >= maxdepth:
            raise RuntimeError(f"cannot certify f > {need} on [{float(lo)}, {float(hi)}]: lb {float(lb.lower())}")
        mid = (lo + hi) / 2
        stack += [(lo, mid, dep + 1), (mid, hi, dep + 1)]
    if stats is not None:
        stats.append(npieces)
    return worst


def derivative_min(H, k, a, b, n=200):
    """rigorous lower bound of f^(k) on [a,b] by subdivision (plain interval evaluation)."""
    lo = float("inf")
    for j in range(n):
        I = iv(Fr(a) + (Fr(b) - Fr(a)) * j / n, Fr(a) + (Fr(b) - Fr(a)) * (j + 1) / n)
        v = phi_der(I, k) - poly_eval(H, I, k)
        lo = min(lo, float(v.lower()))
    return lo


def main(path, delta=None):
    t0 = time.time()
    J = json.load(open(path))
    HA = [A(x) for x in J["H"]["A"]]; HB = [A(x) for x in J["H"]["B"]]; HC = [A(x) for x in J["H"]["C"]]
    HAq = [Fr(x) for x in J["H"]["A"]]; HBq = [Fr(x) for x in J["H"]["B"]]; HCq = [Fr(x) for x in J["H"]["C"]]
    s5 = arb(5).sqrt(); c1 = (s5 - 1) / 4; c2 = (-s5 - 1) / 4
    EP = -(arb(1600) * s5).log()
    e = A(J["e"])
    gapE = EP - e
    rep = {"E(P)-e": gapE.str(10)}
    if delta is None:
        delta = float(gapE.upper()) * 1.0000001
    dl = arb(delta)
    assert (dl - gapE) > 0
    rep["delta"] = delta
    # --- exact contact values
    eta = {"A": phi_der(arb(-1), 0) - poly_eval(HA, arb(-1)), "B": phi_der(arb(0), 0) - poly_eval(HB, arb(0)),
           "C1": phi_der(c1, 0) - poly_eval(HC, c1), "C2": phi_der(c2, 0) - poly_eval(HC, c2)}
    for k, v in eta.items():
        assert v > 0, (k, v)
    rep["eta"] = {k: v.str(5) for k, v in eta.items()}
    # derivative data at the touching points (exact vanishing verified in check_cert; here as balls)
    rep["fB_derivs_at_0"] = [(phi_der(arb(0), k) - poly_eval(HB, arb(0), k)).str(5) for k in range(1, 5)]
    rep["fC_d1_at_c1_c2"] = [(phi_der(c, 1) - poly_eval(HC, c, 1)).str(5) for c in (c1, c2)]
    rep["fA_d1_at_-1"] = (phi_der(arb(-1), 1) - poly_eval(HA, arb(-1), 1)).str(8)
    # --- windows
    rB, rC, rA = Fr(1, 20), Fr(1, 50), Fr(1, 500)
    m4 = derivative_min(HB, 4, -rB, rB, 400)
    c1q = Fr(-1, 4) + Fr(1, 4) * Fr(2236067977499789696, 10 ** 18)   # rational near c1 (window centre only)
    c2q = Fr(-1, 4) - Fr(1, 4) * Fr(2236067977499789696, 10 ** 18)
    m2 = [derivative_min(HC, 2, c - rC, c + rC, 400) for c in (c1q, c2q)]
    m1A = derivative_min(HA, 1, Fr(-1), Fr(-1) + rA, 200)
    rep["window"] = dict(rB=float(rB), rC=float(rC), rA=float(rA), min_fB4=m4, min_fC2=m2, min_fA1=m1A)
    # Taylor at the exact points: f >= eta + (m/k!) |t - touch|^k on the windows (k = 4, 2, 1)
    assert m4 > 0 and min(m2) > 0 and m1A > 0
    # the windows around c are centred at rational c_q with |c_q - c| < 1e-18; use half-width rC - 1e-17
    # f >= eta + m/2 (t-c)^2 holds on [c - rC + 1e-17, c + rC - 1e-17] by Taylor at the exact c.
    # --- cover the rest
    eps1 = Fr(1, 10 ** 6)
    stats = []
    pad = Fr(1, 10 ** 15)
    lbA = cover(HA, Fr(-1) + rA, Fr(-99, 100), 16, stats=stats)
    segs = [(Fr(-1), -rB), (rB, c1q - rC + pad), (c1q + rC - pad, 1 - eps1)]
    # c2 ~ -0.809 lies in [-1, -rB]: split
    segs = [(Fr(-1), c2q - rC + pad), (c2q + rC - pad, -rB)] + segs[1:]
    lbB = min(cover(HB, a, b, 256, stats=stats) for (a, b) in
              [(Fr(-1), -rB), (rB, 1 - eps1)])
    lbC = min(cover(HC, a, b, 256, stats=stats) for (a, b) in segs)
    # windows for B / C also cover the other function's windows? H_B must be checked on C-windows too (done:
    # H_B segments are [-1,-rB] and [rB,1-eps1]); H_C must be checked on the B-window [-rB, rB]:
    lbC0 = cover(HC, -rB, rB, 64, stats=stats)
    lbC = min(lbC, lbC0)
    # near t = 1
    top = {}
    for nm, H in (("B", HB), ("C", HC)):
        Hmax = poly_eval(H, iv(1 - eps1, 1)).upper()
        top[nm] = float((phi_der(A(1 - eps1), 0) - Hmax).lower())
        assert top[nm] > 0
    rep["cover_min_lower_bounds"] = dict(A=lbA, B=lbB, C=lbC, near1=top, pieces=sum(stats))
    # --- coercivity windows: tau such that f <= delta => |t - touch| <= tau
    tauB = (delta / (m4 / 24)) ** 0.25
    tauC = (2 * delta / min(m2)) ** 0.5
    tauA = delta / m1A
    rep["contact"] = dict(kappa4_B_local=float(Fr(1, 8) - HBq[4]), kappa4_B_certified=m4 / 24,
                          kappa2_C_certified=min(m2) / 2, slopeA_certified=m1A,
                          min_f_outside_windows=dict(A=lbA, B=lbB, C=lbC))
    ok_outside = min(lbA, lbB, lbC) > delta
    rep["coercivity"] = dict(tauB=tauB, tauC=tauC, tauA=tauA, outside_windows_f_gt_delta=ok_outside,
                             tau_needed=1 / 1650, OK=bool(ok_outside and max(tauB, tauC, tauA) <= 1 / 1650))
    rep["MINORANT_OK"] = True
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    rep = main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "certificates", "cert_cap_log_D12.json"),
               float(sys.argv[2]) if len(sys.argv) > 2 else None)
    print(json.dumps(rep, indent=1))
    ok = rep.get("MINORANT_OK", False) and (rep.get("coercivity") is None or rep["coercivity"].get("OK", False))
    sys.exit(0 if ok else 1)
