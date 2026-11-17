"""Rigorous check of a Bernstein-in-s certificate (sdp_bern.py -> round_bern.py) for a cell on s in [a, b].

usage: python3 check_bern.py NSUB CTRL_0.json ... CTRL_m.json

Control certificates Chat_k (normalised gauge, kernel label "hat") each satisfy the cell identities exactly with
positive definite blocks (check_cell.check).  For s in [a, b], lambda = (s-a)/(b-a), Chat(s) = sum_k b_k(lambda) Chat_k
(b_k Bernstein, >= 0, sum 1) satisfies the identities with PD blocks, and C(s) = S0 + s Chat(s)
(S0 = (H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2, F = B = 0), see check_piece.py) is a certificate for phi_s if
  (E) ehat(s) = sum_k b_k ehat_k > Ehat_s(P) = (E_s(P) - 21)/s for all s in [a, b]:
      adaptive bisection in s with the mean-value form (arb);
  (H) Hhat(s, t) = sum_k b_k Hhat_k(t) <= psi_s(t) = (phi_s(t) - 1)/s on [a, b] x range:
      f(s) = psi_s(t) - Hhat(s, t) has f'' <= K(t) := Gmax(t) + m(m-1)/(b-a)^2 max_k |Delta^2 Hhat_k(t)|
      (Gmax as in check_piece.py; d^2/dlambda^2 sum c_k b_k = m(m-1) sum Delta^2 c_k b_{k,m-2}), so on each of the
      NSUB sub-intervals [s_i, s_i+1] (length delta): f >= min(f(s_i), f(s_i+1)) - delta^2/8 K  (lemma bound);
      for t > 1/2 also f >= psi_{s_i}(t) - Hhat([s_i, s_i+1], t)  (mono bound; psi_s increasing in s, Hhat
      enclosed by evaluating the Bernstein form on the lambda-ball).  Per sub-interval, every t-piece of
      [lo, 1 - 2^-20] is certified by one of the two bounds (adaptive bisection, mean-value form in t), and
      [1 - 2^-20, 1) by psi_{s_i}(1 - 2^-20) - Hhat(ball, ball) > NEED.
Provenance (REVIEW_range_fable.md S1): the report carries `provenance` (sha256 of this file, of check_piece.py,
check_cell.py, check_minorant_cell.py, ../hp/check_cert.py and of every control certificate; argv, cwd, NSUB).
"""
import json, os, sys, time
from math import comb
from fractions import Fraction as Fr
import flint
from flint import arb
import check_cell as CK
from check_minorant_cell import A, poly, ball
from check_piece import lnu, cover, Gmax, ranges, NEED, provenance

flint.ctx.prec = 256


def psi(s, t):
    return ((lnu(t) * (-A(s) / 2)).exp() - 1) / A(s)


def dpsi(s, t):
    return (lnu(t) * (-A(s) / 2 - 1)).exp()


def EPhat_and_der(S):
    """S: arb ball of s > 0. returns (Ehat_S(P), d/ds Ehat_S(P)) enclosures."""
    s5 = arb(5).sqrt()
    v = arb(0); d = arb(0)
    for t, m in ((arb(-1), 1), (arb(0), 10), ((s5 - 1) / 4, 5), ((-s5 - 1) / 4, 5)):
        x = -lnu(t) / 2
        ex = (S * x).exp()
        v += m * (ex - 1) / S
        d += m * (S * x * ex - ex + 1) / (S * S)
    return v, d


def bern(m, lam):
    return [comb(m, k) * lam ** k * (1 - lam) ** (m - k) for k in range(m + 1)]


def dbern(m, lam):
    if m == 0:
        return [arb(0)]
    lo = bern(m - 1, lam)
    return [m * ((lo[k - 1] if k >= 1 else 0) - (lo[k] if k <= m - 1 else 0)) for k in range(m + 1)]


def check(nsub, paths, T1=Fr(4, 5), skip_exact=False):
    t0 = time.time()
    prov = provenance(paths, dict(function="check_bern.check", nsub=nsub, T1=str(Fr(T1)), skip_exact=bool(skip_exact)),
                      checker_file=__file__, deps=("check_piece", "check_cell", "check_minorant_cell", "check_cert"))
    Js = [json.load(open(p)) for p in paths]
    m = len(Js) - 1
    a, b = Fr(Js[0]["solve_a"]), Fr(Js[0]["solve_b"])
    w = b - a
    rep = {"certs": [os.path.basename(p) for p in paths], "s_range": [str(a), str(b)], "m": m, "cell": Js[0]["cell"],
           "nsub": nsub, "provenance": prov}
    ok = all(J["kernel"] == "hat" and J["cell"] == Js[0]["cell"] and J["kind"] == Js[0]["kind"] and
             J["D"] == Js[0]["D"] and J.get("solve_control") == k and J["solve_m"] == m for k, J in enumerate(Js))
    ok &= 0 < a < b
    if not skip_exact:
        allpd = True
        for p in paths:
            r = CK.check(p, verbose=False, do_sanity=False)
            allpd &= r["ALL_OK"]
        rep["controls_identities_PD"] = bool(allpd); ok &= allpd
    # (E)
    eh = [A(Fr(J["e"])) for J in Js]
    def g_mid(S):
        lam = (S - A(a)) / A(w)
        v, _ = EPhat_and_der(S)
        return sum(bk * ek for bk, ek in zip(bern(m, lam), eh)) - v
    def g_der(S):
        lam = (S - A(a)) / A(w)
        _, d = EPhat_and_der(S)
        return sum(bk * ek for bk, ek in zip(dbern(m, lam), eh)) / A(w) - d
    try:
        worst, pcs = cover(g_mid, g_der, lambda I: arb(0), a, b, n0=64)
        rep["E"] = dict(min_ehat_minus_EPhat=worst, pieces=pcs)
    except RuntimeError as ex:
        rep["E"] = str(ex); ok = False
    # (H)
    delta = w / nsub
    for nm, lo, top in ranges(Js[0]):
        Hs = [[A(x) for x in (J["H"] if nm == "H" else J["H"][nm])] for J in Js]
        D2 = [[Hs[k + 2][j] - 2 * Hs[k + 1][j] + Hs[k][j] for j in range(len(Hs[0]))] for k in range(m - 1)]
        def K(I):
            v = Gmax(I, b)
            if m >= 2:
                mx = max((abs(poly(c, I)).upper() for c in D2))
                v = v + arb(m * (m - 1)) / A(w) ** 2 * arb(mx)
            return arb((A(delta) ** 2 / 8 * v).upper())
        Hsub = []
        for i in range(nsub + 1):
            bb = bern(m, A(Fr(i, nsub)))
            Hsub.append([sum(bb[k] * Hs[k][j] for k in range(m + 1)) for j in range(len(Hs[0]))])
        ttop = min(top, 1 - Fr(1, 2 ** 20))
        worst_all = None; pcs = {"lemma": 0, "mono": 0}; near1 = None
        try:
            for i in range(nsub):
                s0, s1 = a + i * delta, a + (i + 1) * delta
                Lb = ball(Fr(i, nsub), Fr(i + 1, nsub))          # lambda over the sub-interval
                bbI = bern(m, Lb)
                HI = [sum(bbI[k] * Hs[k][j] for k in range(m + 1)) for j in range(len(Hs[0]))]
                def lb_piece(lo_, hi_):
                    mm = A((lo_ + hi_) / 2); I = ball(lo_, hi_); r = A((hi_ - lo_) / 2)
                    lem = None
                    for s, Hc in ((s0, Hsub[i]), (s1, Hsub[i + 1])):
                        v = psi(s, mm) - poly(Hc, mm) - abs(dpsi(s, I) - poly(Hc, I, 1)) * r
                        lem = v if lem is None else (v if v.lower() < lem.lower() else lem)
                    lem = lem - K(I)
                    if lo_ >= Fr(1, 2):     # psi_s >= psi_s0 on the sub-interval; Hhat(s, t) in HI (ball in lambda)
                        mono = psi(s0, mm) - poly(HI, mm) - abs(dpsi(s0, I) - poly(HI, I, 1)) * r
                        if mono.lower() > lem.lower():
                            return mono, "mono"
                    return lem, "lemma"
                stack = [(lo + (ttop - lo) * k / 256, lo + (ttop - lo) * (k + 1) / 256, 0) for k in range(256)]
                while stack:
                    l_, h_, dep = stack.pop()
                    v, kind = lb_piece(l_, h_)
                    if v > NEED:
                        fv = float(v.lower()); worst_all = fv if worst_all is None else min(worst_all, fv); pcs[kind] += 1
                        continue
                    if dep >= 40:
                        raise RuntimeError(f"H{nm}: s in [{s0}, {s1}]: cannot certify t in [{float(l_)}, {float(h_)}] "
                                           f"(lb {float(v.lower())})")
                    md = (l_ + h_) / 2
                    stack += [(l_, md, dep + 1), (md, h_, dep + 1)]
                if top == 1:
                    v = (psi(s0, A(ttop)) - poly(HI, ball(ttop, Fr(1)))).lower()
                    near1 = v if near1 is None else min(near1, v)
            rep[f"H{nm}"] = dict(range=[str(lo), str(top)], min=worst_all, pieces=pcs,
                                 near1=None if near1 is None else float(near1))
            if near1 is not None:
                ok &= near1 > NEED
        except RuntimeError as ex:
            rep[f"H{nm}"] = str(ex); ok = False
    rep["BERN_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    r = check(int(sys.argv[1]), sys.argv[2:])
    print(json.dumps(r), flush=True)
    sys.exit(0 if r["BERN_OK"] else 1)
