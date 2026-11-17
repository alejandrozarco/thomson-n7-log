"""Rigorous check that two node certificates of the same cell, at rational s = a < b, cover every s in [a, b]
by linear interpolation in the normalised gauge (NOTES.md, "design").

usage: python3 check_piece.py CERT_a.json CERT_b.json [T1]

Argument.  psi_s(t) = (phi_s(t) - 1)/s, u = 2 - 2t, x = -ln(u)/2, so psi_s = (e^{sx} - 1)/s and
    d^2/ds^2 psi_s(t) = x^3 I(sx),  I(c) = int_0^1 r^2 e^{cr} dr  (> 0 iff x > 0 iff t > 1/2).
A certificate C = (H's, e, c_alpha, c_beta, F's, B's) satisfies identities that are linear and homogeneous in C,
and so does the shift S0 = (H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2, F = B = 0) (all its LHS vanish).
Hence the normalised node certificates Chat_j = (C_j - S0)/s_j satisfy them, and for s in [a, b],
lambda = (s-a)/(b-a),
    C(s) = S0 + s [ (1-lambda) Chat_a + lambda Chat_b ]
satisfies the identities, and its F and B blocks are s(1-lambda)/a F_a + s lambda/b F_b, positive definite.
So C(s) is a three-point certificate for phi_s on the cell as soon as
  (H) H(s, t) <= phi_s(t) on the minorant ranges, i.e. Hhat(s,t) := (1-lambda) Hhat_a + lambda Hhat_b <= psi_s(t);
  (E) e(s) > E_s(P), i.e. ehat(s) := (1-lambda) ehat_a + lambda ehat_b > Ehat_s(P) = (E_s(P) - 21)/s.
(H): f(s) = psi_s(t) - Hhat(s,t) has f'' = x^3 I(sx) <= Gmax(t) := x^3 e^{bx}/3 for x > 0 (I(c) <= e^c/3),
     f'' <= 0 for x <= 0; so f >= min(f(a), f(b)) - (b-a)^2/8 Gmax(t).  We check, by ball arithmetic,
       on [lo, T1]:  phi_j - H_j - s_j (b-a)^2/8 Gmax > 0   (j = a, b;  equivalent to psi_j - Hhat_j > (b-a)^2/8 Gmax);
     and on [T1, 1) (only where t > 1/2, so psi_s is increasing in s): psi_a - Hhat_j > 0 (j = a, b), which gives
       Hhat(s,t) <= max_j Hhat_j <= psi_a <= psi_s.
(E): g(s) = ehat(s) - Ehat_s(P) has g'' = -Ehat'' = sum_P m |x|^3 I(s x) (x < 0), <= M := sum_P m |x|^3 I(a x);
     we check ehat_j - Ehat_j(P) > (b-a)^2/8 M for j = a, b (arb).
Identities and positive definiteness of each node certificate: check_cell.check (exact; its bareiss_pd tests exact
symmetry of every block before the minors, so review item M2 needs no change here).
Hygiene (REVIEW_range_fable.md M1): every minimum over balls below is taken by lower endpoint (`lem`, `mono`) or over
floats / exact endpoints, never min() on arb balls.
Provenance (review S1): every report carries `provenance` = sha256 of this file and of the modules it relies on
(check_cell.py, check_minorant_cell.py, ../hp/check_cert.py), sha256 of both certificate files, argv / command line /
cwd and the call parameters (T1, skip_exact); range_check.py compares these hashes with the current files.
"""
import json, os, sys, time
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq
import check_cell as CK
from check_minorant_cell import A, poly, ball

flint.ctx.prec = 256
NEED = 1e-8


def sha256_file(p):
    import hashlib
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def provenance(inputs, call, checker_file=None, deps=("check_cell", "check_minorant_cell", "check_cert")):
    """S1: bind a report to the checker sources (this file + the imported modules it relies on) and to the exact
    input files (sha256), plus how it was run."""
    import platform, shlex
    me = os.path.abspath(checker_file or __file__)
    dep = []
    for name in deps:
        f = os.path.abspath(sys.modules[name].__file__)
        dep.append(dict(name=os.path.basename(f), path=f, sha256=sha256_file(f)))
    return dict(checker=os.path.basename(me), checker_path=me, checker_sha256=sha256_file(me), deps=dep,
                inputs=[dict(path=p, name=os.path.basename(p), sha256=sha256_file(p)) for p in inputs],
                call=call, argv=list(sys.argv), cmdline=shlex.join([sys.executable] + list(sys.argv)),
                cwd=os.getcwd(), python=platform.python_version(), flint=flint.__version__,
                started=time.strftime("%Y-%m-%d %H:%M:%S"))


def sof(J):
    return CK.riesz_s(J["kernel"])


def lnu(t):
    return (2 - 2 * t).log()


def phi(s, t):
    return (lnu(t) * (-A(s) / 2)).exp()


def dphi(s, t):
    return A(s) * (lnu(t) * (-A(s) / 2 - 1)).exp()


def Gmax(t, b):
    """upper bound of x^3 e^{bx}/3 for x = -ln(u)/2 over the ball t (0 where x <= 0)."""
    x = -lnu(t) / 2
    xu = x.upper()
    if xu <= 0:
        return arb(0)
    xx = arb(xu) if x.lower() < 0 else x
    v = xx ** 3 * (A(b) * xx).exp() / 3
    return arb(v.upper())


def cover(f_mid, f_der, extra, a, b, n0=256, maxdepth=50, need=NEED):
    """certify f - extra > need on [a, b] (rationals); f by mean-value form, extra(ball) an upper bound."""
    stack = [(a + (b - a) * k / n0, a + (b - a) * (k + 1) / n0, 0) for k in range(n0)]
    worst = None; pieces = 0
    while stack:
        lo, hi, dep = stack.pop()
        m = A((lo + hi) / 2); I = ball(lo, hi)
        lb = f_mid(m) - abs(f_der(I)) * A((hi - lo) / 2) - extra(I)
        if lb > need:
            v = float(lb.lower()); worst = v if worst is None else min(worst, v); pieces += 1
            continue
        if dep >= maxdepth:
            raise RuntimeError(f"cannot certify on [{float(lo)}, {float(hi)}] (lb {float(lb.lower())})")
        mid = (lo + hi) / 2
        stack += [(lo, mid, dep + 1), (mid, hi, dep + 1)]
    return worst, pieces


def ranges(J):
    if J["kind"] == "case1":
        return [("H", Fr(J["cell"]["a"]), Fr(1))]
    lo, hi = Fr(J["cell"]["lo"]), Fr(J["cell"]["hi"])
    return [("A", lo, hi), ("B", lo, Fr(1)), ("C", lo, Fr(1))]


def Hcoefs(J, nm):
    return [A(x) for x in (J["H"] if nm == "H" else J["H"][nm])]


def EP_hat(s):
    return (CK.EP_arb("riesz:" + str(s)) - 21) / A(s)


def Mbound(a):
    s5 = arb(5).sqrt()
    tot = arb(0)
    for t, m in ((arb(-1), 1), (arb(0), 10), ((s5 - 1) / 4, 5), ((-s5 - 1) / 4, 5)):
        x = -lnu(t) / 2                       # < 0
        c = A(a) * x
        I = ((c.exp() * (c * c - 2 * c + 2)) - 2) / (c ** 3)
        tot += m * (-x) ** 3 * I
    return tot


def check(pa, pb, T1=Fr(4, 5), skip_exact=False):
    t0 = time.time()
    prov = provenance([pa, pb], dict(function="check_piece.check", T1=str(Fr(T1)), skip_exact=bool(skip_exact)))
    Ja, Jb = json.load(open(pa)), json.load(open(pb))
    a, b = sof(Ja), sof(Jb)
    rep = {"certs": [os.path.basename(pa), os.path.basename(pb)], "s_range": [str(a), str(b)], "kind": Ja["kind"],
           "cell": Ja["cell"], "provenance": prov}
    ok = (Ja["kind"] == Jb["kind"]) and (Ja["cell"] == Jb["cell"]) and (Ja["D"] == Jb["D"]) and (0 < a < b)
    w = b - a
    w2 = A(w) ** 2 / 8
    # node certificates: exact identities, PD, e > E_s(P)
    if not skip_exact:
        for p in (pa, pb):
            r = CK.check(p, verbose=False, do_sanity=False)
            rep["node_" + os.path.basename(p)] = {"ALL_OK": r["ALL_OK"], "e_minus_EP": r["e_minus_EP"][:12]}
            ok &= r["ALL_OK"]
    # (E)
    M = Mbound(a)
    rep["E_curv_bound_M"] = float(M.mid())
    for J, s in ((Ja, a), (Jb, b)):
        eh = (A(Fr(J["e"])) - 21) / A(s)
        marg = eh - EP_hat(s) - w2 * M
        rep[f"E_margin_hat_s{s}"] = float(marg.lower())
        ok &= bool(marg > 0)
    # (H): on each t-piece accept if the G-lemma bound OR (for t > 1/2) the monotonicity bound is > NEED
    T1 = Fr(T1)
    for nm, lo, top in ranges(Ja):
        Hn = [(Hcoefs(J, nm), s) for J, s in ((Ja, a), (Jb, b))]
        def lb_piece(lo_, hi_):
            m = A((lo_ + hi_) / 2); I = ball(lo_, hi_); r = A((hi_ - lo_) / 2)
            G = w2 * Gmax(I, b)
            lem = None
            for H, s in Hn:        # (psi_s - Hhat_s) - w^2/8 Gmax, hat units
                v = ((phi(s, m) - poly(H, m)) - abs(dphi(s, I) - poly(H, I, 1)) * r) / A(s) - G
                lem = v if lem is None else (v if v.lower() < lem.lower() else lem)
            if lo_ >= Fr(1, 2):    # psi_a - Hhat_j, j = a, b
                mono = None
                for H, s in Hn:
                    v = ((phi(a, m) - 1) / A(a) - (poly(H, m) - 1) / A(s)) - \
                        abs(dphi(a, I) / A(a) - poly(H, I, 1) / A(s)) * r
                    mono = v if mono is None else (v if v.lower() < mono.lower() else mono)
                if mono.lower() > lem.lower():
                    return mono, "mono"
            return lem, "lemma"
        ttop = min(top, 1 - Fr(1, 2 ** 20))
        stack = [(lo + (ttop - lo) * k / 512, lo + (ttop - lo) * (k + 1) / 512, 0) for k in range(512)]
        worst = None; pcs = {"lemma": 0, "mono": 0}
        try:
            while stack:
                l_, h_, dep = stack.pop()
                v, kind = lb_piece(l_, h_)
                if v > NEED:
                    worst = float(v.lower()) if worst is None else min(worst, float(v.lower())); pcs[kind] += 1
                    continue
                if dep >= 50:
                    raise RuntimeError(f"H{nm}: cannot certify on [{float(l_)}, {float(h_)}] (lb {float(v.lower())})")
                md = (l_ + h_) / 2
                stack += [(l_, md, dep + 1), (md, h_, dep + 1)]
            info = dict(range=[str(lo), str(top)], min=worst, pieces=pcs)
            if top == 1:
                near1 = min(((phi(a, A(ttop)) - 1) / A(a) - ((poly(H, ball(ttop, Fr(1))) - 1) / A(s)).upper()).lower()
                            for H, s in Hn)
                info["near1"] = float(near1); ok &= near1 > NEED
            rep[f"H{nm}"] = info
        except RuntimeError as ex:
            rep[f"H{nm}"] = str(ex); ok = False
    rep["PIECE_OK"] = bool(ok)
    rep["time_s"] = round(time.time() - t0, 1)
    return rep


if __name__ == "__main__":
    try:
        r = check(sys.argv[1], sys.argv[2], Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(4, 5))
    except RuntimeError as ex:
        r = {"certs": sys.argv[1:3], "PIECE_OK": False, "error": str(ex)}
    print(json.dumps(r), flush=True)
    sys.exit(0 if r["PIECE_OK"] else 1)
