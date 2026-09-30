"""EXACT check of the 1-D minorant inequalities H <= phi2(t) = 1/(2-2t) (Riesz s = 2), by polynomial algebra.

For t < 1:  phi2(t) - H(t) = p(t) / (2 - 2t),   p(t) := 1 - (2 - 2t) H(t)   (a polynomial, deg H + 1).
So H <= phi2 on [a, b) (b <= 1) iff p >= 0 on [a, b].  We prescribe the touching points (exact factor F >= 0
on [a, b]), check exactly that F divides p, and that the quotient q = p / F has NO real root in the closed
interval [a, b] (Sturm sequence, sympy count_roots, exact rational arithmetic) and q(a) > 0.  Hence
    phi2 - H = F q / (2 - 2t) >= 0 on [a, b),  with equality exactly at the zeros of F.
Also returns a rigorous lower bound q_min of q on [a, b] (interval bisection in exact rationals, used for the
coercivity / contact constants) -- this bound is not needed for the soundness of H <= phi2.

No floating point is involved in the decision.
"""
from fractions import Fraction as Fr
import sympy as sp

t = sp.symbols("t")


def p_of(H):
    """p(t) = 1 - (2-2t) H(t), H = list of Fractions (monomial coefficients)."""
    Hp = sp.Poly([sp.Rational(c.numerator, c.denominator) for c in reversed(H)], t, domain="QQ")
    return sp.Poly(1, t, domain="QQ") - sp.Poly(2 - 2 * t, t, domain="QQ") * Hp


FACTORS = {
    "none": sp.Poly(1, t, domain="QQ"),
    "t^4": sp.Poly(t ** 4, t, domain="QQ"),                        # B-contact at 0, order 4
    "(4t^2+2t-1)^2": sp.Poly((4 * t ** 2 + 2 * t - 1) ** 2, t, domain="QQ"),  # C-contact at c1, c2 (roots of 4t^2+2t-1)
    "t+1": sp.Poly(t + 1, t, domain="QQ"),                         # A-contact at -1 (endpoint), F >= 0 on [-1, .]
}


def qmin_lower(q, a, b):
    """certified lower bound of min_{[a,b]} q (exact rationals): the minimum is attained at a or b or at a real root
    of q' in (a,b).  Each root of q' is isolated (sympy, exact) in [l,r] of width w <= 2^-60; on it |q'| <= M2 w with
    M2 >= max|q''| (crude coefficient bound), so q >= q(m) - M2 w^2 there."""
    a = sp.Rational(a); b = sp.Rational(b)
    dq = q.diff(t); d2 = dq.diff(t)
    c2 = [abs(sp.Rational(c)) for c in d2.all_coeffs()[::-1]]
    vals = [q.eval(a), q.eval(b)]
    for (l, r), _ in dq.intervals(inf=a, sup=b, eps=sp.Rational(1, 2 ** 60)):
        l, r = sp.Rational(l), sp.Rational(r)
        w = r - l; M = max(abs(l), abs(r))
        M2 = sum(c * M ** j for j, c in enumerate(c2))
        vals.append(q.eval((l + r) / 2) - M2 * w * w)
    return min(vals)


def check(H, a, b, factor="none", want_qmin=True):
    """H <= phi2 on [a, b) with touching factor.  a, b Fractions, b <= 1.  Returns dict with 'OK'."""
    a = sp.Rational(Fr(a).numerator, Fr(a).denominator); b = sp.Rational(Fr(b).numerator, Fr(b).denominator)
    assert b <= 1 and a < b
    p = p_of(H)
    F = FACTORS[factor]
    q, r = sp.div(p, F)
    rep = {"factor": factor, "range": [str(a), str(b) + (")" if b == 1 else "]")]}
    rep["divisible"] = r.is_zero
    if not r.is_zero:
        rep["OK"] = False
        return rep, None
    # F >= 0 on [a, b]
    Fok = {"none": True, "t^4": True, "(4t^2+2t-1)^2": True, "t+1": bool(a >= -1)}[factor]
    nroots = q.count_roots(a, b)
    qa = q.eval(a)
    rep.update(F_nonneg=Fok, roots_of_q_in_closed_interval=int(nroots), q_at_a=float(qa))
    ok = bool(Fok and nroots == 0 and qa > 0)
    if want_qmin and ok:
        qm = qmin_lower(q, a, b)
        rep["q_min_lower"] = float(qm)
        # q at the touching points (the contact constants)
        if factor == "t^4":
            rep["q(0)"] = float(q.eval(0))
        if factor == "t+1":
            rep["q(-1)"] = float(q.eval(-1))
    rep["OK"] = ok
    return rep, q

