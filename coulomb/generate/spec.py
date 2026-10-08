"""Exact specification of the degree-12 typed cap certificate (log kernel, cell -1 <= t01 <= -99/100).

Shared by face.py (facial reduction), sdp_soft.py (float solve) and round_exact.py (rounding).
The independent checker check_cert.py does NOT import this file.
"""
import itertools
from fractions import Fraction as Fr

D = 12                                   # total degree of the identities
SIZES = tuple(range(D // 2 + 1, 0, -1))  # kernel blocks F_X^(k), k = 0..6, sizes 7..1
DA = (D // 2, D // 2 - 1, D // 2 - 2)    # SOS monomial degrees (6,5,4)
LO = Fr(-1)
HI = Fr(-99, 100)


def monos_upto(d):
    """same order as numerics/sdp/polyk.py"""
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


# ---- sparse exact polynomials in (u,v,t): dict {(a,b,c): Fraction}
def padd(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + c * v
        if r[k] == 0:
            del r[k]
    return r


def pmul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
            r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}


ONE = {(0, 0, 0): Fr(1)}
U = {(1, 0, 0): Fr(1)}
V = {(0, 1, 0): Fr(1)}
T = {(0, 0, 1): Fr(1)}


def cst(c):
    return {(0, 0, 0): Fr(c)} if c != 0 else {}


def lin(var, c0):          # x_var - c0
    return padd({(1 if var == 0 else 0, 1 if var == 1 else 0, 1 if var == 2 else 0): Fr(1)}, cst(c0), -1)


DETG = padd(padd(padd(padd(ONE, pmul(pmul(U, V), T), 2), pmul(U, U), -1), pmul(V, V), -1), pmul(T, T), -1)


def multipliers():
    """blocks per identity: list of (name, g, d) exactly as numerics/sdp/typed.py (extra_mult=True)."""
    d5, d4, d3 = DA
    one_minus = lambda var: padd(ONE, lin(var, 0), -1)
    A = [("1", ONE, d5), ("u-lo", lin(0, LO), d4), ("hi-u", padd(cst(HI), U, -1), d4),
         ("v-lo", lin(1, LO), d4), ("t-lo", lin(2, LO), d4), ("1-v", one_minus(1), d4),
         ("1-t", one_minus(2), d4), ("detG", DETG, d3),
         ("(u-lo)(hi-u)", pmul(lin(0, LO), padd(cst(HI), U, -1)), d4)]
    BG = [("1", ONE, d5), ("u-lo", lin(0, LO), d4), ("v-lo", lin(1, LO), d4), ("t-lo", lin(2, LO), d4),
          ("1-u", one_minus(0), d4), ("1-v", one_minus(1), d4), ("1-t", one_minus(2), d4),
          ("detG", DETG, d3)]
    return {"A": A, "B": BG, "G": BG}
