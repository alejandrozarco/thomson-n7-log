"""Coercivity for the Coulomb (s = 1) N = 7 cap certificate (port of ../../hp/check_minorant.py, log kernel),
by ball arithmetic (python-flint / arb, 256 bits) with an exact rational final decision.

usage: python3 check_coerc1.py cert_cap_coulomb_D12.json [delta]       (exit status 0 iff coercivity OK)

phi(t) = (2-2t)^(-1/2).  Ranges: H_A on [-1, -99/100];  H_B, H_C on [-1, 1).   f_X := phi - H_X.
(H <= phi itself is decided exactly by check_cap1.py, Sturm sequences; here it is re-checked on the windows and by
bisection elsewhere.)
Contact windows (Taylor at the exact touching points; the contact slopes are dyadic, so f' there is a tiny
certified mismatch d instead of 0):
  B at 0, C at c1, c2:  f(c) = eta > 0, |f'(c)| <= d  =>  f >= eta - d|t-c| + (min f''/2)(t-c)^2 on the window
                        (>= eta - d^2/(2 min f'') > 0, checked);
  A at -1:              f(-1) = eta_A > 0  =>  f >= eta_A + (min f')(t+1)   (min f' > 0).
Elsewhere: adaptive bisection with the mean-value form f(m) - |f'(I)| rad(I) > 0.
Near t = 1: phi is increasing and -> +inf, so on [1-eps, 1) f >= phi(1-eps) - max H.
Coercivity: with delta >= E(P) - e, f_X <= delta  =>  |t - touch| <= tau = 1/TAU_DEN = 1e-6, decided exactly:
  u <= T  <=  (m/2) T^2 - d T - delta > 0 and d/m < T.
"""
import json, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq

flint.ctx.prec = 256
TAU_DEN = 1000000         # s = 1: target window tau = 1e-6; check_local1.py covers r = sqrt7 (11/2) tau


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
    """k-th derivative of (2-2t)^(-1/2): (2k-1)!! (2-2t)^(-1/2-k)."""
    fac = 1
    for j in range(k):
        fac *= 2 * j + 1
    return arb(fac) / ((2 - 2 * t) ** k * (2 - 2 * t).sqrt())


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
    EP = phi_der(arb(-1), 0) + 10 * phi_der(arb(0), 0) + 5 * phi_der(c1, 0) + 5 * phi_der(c2, 0)
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
    # derivative data at the touching points (dyadic contact slopes: f' is a tiny mismatch, bounded here)
    rep["fB_derivs_at_0"] = [(phi_der(arb(0), k) - poly_eval(HB, arb(0), k)).str(5) for k in range(1, 3)]
    dB = abs(phi_der(arb(0), 1) - poly_eval(HB, arb(0), 1)).upper()                       # tiny slope mismatch
    dC = max(abs(phi_der(c, 1) - poly_eval(HC, c, 1)).upper() for c in (c1, c2))
    rep["fC_d1_at_c1_c2"] = [(phi_der(c, 1) - poly_eval(HC, c, 1)).str(5) for c in (c1, c2)]
    rep["fA_d1_at_-1"] = (phi_der(arb(-1), 1) - poly_eval(HA, arb(-1), 1)).str(8)
    # --- windows
    rB, rC, rA = Fr(1, 20), Fr(1, 50), Fr(1, 500)
    m4 = derivative_min(HB, 2, -rB, rB, 400)     # s = 1: quadratic contact at 0 (name kept)
    c1q = Fr(-1, 4) + Fr(1, 4) * Fr(2236067977499789696, 10 ** 18)   # rational near c1 (window centre only)
    c2q = Fr(-1, 4) - Fr(1, 4) * Fr(2236067977499789696, 10 ** 18)
    m2 = [derivative_min(HC, 2, c - rC, c + rC, 400) for c in (c1q, c2q)]
    m1A = derivative_min(HA, 1, Fr(-1), Fr(-1) + rA, 200)
    rep["window"] = dict(rB=float(rB), rC=float(rC), rA=float(rA), min_fB2=m4, min_fC2=m2, min_fA1=m1A,
                         slope_mismatch_B=float(dB), slope_mismatch_C=float(dC))
    # Taylor at the exact points: f >= eta - d|t - c| + (m/2)(t - c)^2 (B, C) and f >= eta_A + m1A (t+1) (A)
    assert m4 > 0 and min(m2) > 0 and m1A > 0
    # the windows around c are centred at rational c_q with |c_q - c| < 1e-18; use half-width rC - 1e-17;
    # the Taylor bound holds on [c - rC + 1e-17, c + rC - 1e-17] by Taylor at the exact c.
    # minorant on the windows: eta - d^2/(2m) > 0
    win_min = {"B": eta["B"] - arb(float(dB)) ** 2 / (2 * arb(m4)),
               "C1": eta["C1"] - arb(float(dC)) ** 2 / (2 * arb(min(m2))),
               "C2": eta["C2"] - arb(float(dC)) ** 2 / (2 * arb(min(m2))), "A": eta["A"]}
    rep["window_min_lower"] = {k: v.str(5) for k, v in win_min.items()}
    windows_pos = all(v > 0 for v in win_min.values())
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
        assert top[nm] > delta, f"near-1 margin {top[nm]} not > delta"
    rep["cover_min_lower_bounds"] = dict(A=lbA, B=lbB, C=lbC, near1=top, pieces=sum(stats))
    # --- coercivity windows: tau such that f <= delta => |t - touch| <= tau.
    # s = 1: f(t) >= eta - d|u| + (m/2) u^2 on the window (u = t - touch, d = |f'(touch)|, eta > 0), hence
    # f <= delta  =>  (m/2) u^2 - d u - delta <= 0  =>  u <= (d + sqrt(d^2 + 2 m delta)) / m.
    tauB = (float(dB) + (float(dB) ** 2 + 2 * m4 * delta) ** 0.5) / m4
    tauC = (float(dC) + (float(dC) ** 2 + 2 * min(m2) * delta) ** 0.5) / min(m2)
    tauA = delta / m1A
    rep["contact"] = dict(kappa2_B_certified=m4 / 2,
                          kappa2_C_certified=min(m2) / 2, slopeA_certified=m1A,
                          min_f_outside_windows=dict(A=lbA, B=lbB, C=lbC))
    ok_outside = min(lbA, lbB, lbC, *top.values()) > delta
    # exact rational decision (no floating-point tau): lower bounds shrunk by 2^-50 relative, then
    # f <= delta  =>  |t - touch| <= tau  with  tau <= 1/TAU_DEN  checked as rational inequalities.
    # u <= T  <=  (m/2) T^2 - d T - delta > 0  (the quadratic is increasing past its vertex d/m << T)
    _s = 1 - Fr(1, 2 ** 50); _T = Fr(1, TAU_DEN); _d = Fr(delta)
    _q = lambda m, d: (Fr(m) * _s / 2) * _T ** 2 - Fr(d) * (1 + Fr(1, 2 ** 50)) * _T - _d > 0 and Fr(d) / Fr(m) < _T
    tau_ok_exact = dict(B=_q(m4, float(dB)), C=_q(min(m2), float(dC)), A=_d / (Fr(m1A) * _s) <= _T)
    rep["coercivity"] = dict(tauB=tauB, tauC=tauC, tauA=tauA, outside_windows_f_gt_delta=ok_outside,
                             tau_needed=1 / TAU_DEN, tau_ok_exact=tau_ok_exact,
                             OK=bool(ok_outside and all(tau_ok_exact.values())))
    rep["MINORANT_OK"] = bool(windows_pos and min(lbA, lbB, lbC, *top.values()) > 0)
    rep["ALL_OK"] = bool(rep["MINORANT_OK"] and rep["coercivity"]["OK"])
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    rep = main(sys.argv[1] if len(sys.argv) > 1 else "cert_cap_coulomb_D12.json",
               float(sys.argv[2]) if len(sys.argv) > 2 else None)
    print(json.dumps(rep, indent=1))
    sys.exit(0 if rep["ALL_OK"] else 1)
