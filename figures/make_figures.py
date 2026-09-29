#!/usr/bin/env python3
"""Regenerate the figures in figures/ from the data in this repository (light and dark variants).
usage: python3 figures/make_figures.py        (needs matplotlib, mpmath, numpy)"""
import itertools, json, os
from fractions import Fraction as Fr
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "figures")
CERTS = os.path.join(ROOT, "certificates")
CAP = os.path.join(CERTS, "cert_cap_log_D12.json")
THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781", grid="#e1e0d9",
                  axis="#c3c2b7", empty="#f0efec", mark="#2a78d6", mark2="#d4661f", mark3="#2f9e6a"),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781", grid="#2c2c2a",
                 axis="#383835", empty="#262624", mark="#3987e5", mark2="#e8813a", mark3="#43b27e"),
}
SAVE = dict(metadata={"Date": None})


def style(ax, t):
    ax.set_facecolor(t["surface"])
    for s in ("top", "right", "left"):
        ax.spines[s].set_visible(False)
    ax.spines["bottom"].set_color(t["axis"])
    ax.tick_params(colors=t["muted"], labelsize=9, length=0, which="both")
    ax.xaxis.label.set_color(t["ink2"]); ax.yaxis.label.set_color(t["ink2"])


def title(ax, t, s):
    ax.set_title(s, color=t["ink"], fontsize=11, loc="left")


def sci(x, sign=True):
    """x as '+5.0·10⁻⁴' (mathtext)."""
    m, e = f"{abs(x):.1e}".split("e")
    s = ("+" if x > 0 else "−") if sign else ("−" if x < 0 else "")
    return f"{s}{m}$\\cdot 10^{{{int(e)}}}$"


# ---------------------------------------------------------------- data: cells and margins
def mpq(q):
    q = Fr(q)
    return mp.mpf(q.numerator) / q.denominator


def cell_data():
    """[(name, lo, hi, degree, e - E(P))] for the cap and the slabs, and the same for Case 1 (lo = cut a, hi = None).
    e - E(P) = e + log(1600 sqrt5), computed as in checkers/make_coverage.py."""
    mp.mp.dps = 60
    logEP = mp.log(1600 * mp.sqrt(5))
    J = json.load(open(CAP))
    rows = [("cap", float(Fr(J["cell"][0])), float(Fr(J["cell"][1])), J["D"], float(mpq(J["e"]) + logEP))]
    case1 = None
    for c in json.load(open(os.path.join(CERTS, "cells.json"))):
        K = json.load(open(os.path.join(CERTS, c["cert"])))
        m = float(mpq(K["e"]) + logEP)
        if K["kind"] == "case1":
            case1 = (c["name"], float(Fr(K["cell"]["a"])), None, K["D"], m)
        else:
            rows.append((c["name"], float(Fr(K["cell"]["lo"])), float(Fr(K["cell"]["hi"])), K["D"], m))
    return rows, case1


def fig_cells(t, name, data):
    rows, case1 = data
    fig, (ax, ax1) = plt.subplots(1, 2, figsize=(10, 4.6), sharey=True, gridspec_kw=dict(width_ratios=[6, 1]))
    fig.patch.set_facecolor(t["surface"])
    lin = 1e-17

    def bar(a, x0, w, m, D, lab):
        col = t["mark"] if m > 0 else t["mark2"]
        a.add_patch(plt.Rectangle((x0, 0), w, m, linewidth=1.5, edgecolor=t["surface"], facecolor=col))
        va, off = ("bottom", 1.6) if m > 0 else ("top", 1.6)
        a.text(x0 + w / 2, m * off, f"D = {D}\n{sci(m)}", ha="center", va=va, fontsize=8, color=t["ink2"])
        a.text(x0 + w / 2, -2e-18 if m > 0 else 2e-18, lab, ha="center", va="top" if m > 0 else "bottom",
               fontsize=8, color=t["ink2"])

    for nm, lo, hi, D, m in rows:
        bar(ax, lo, hi - lo, m, D, nm)
    brk = sorted({r[1] for r in rows} | {r[2] for r in rows})
    ax.set_xlim(brk[0] - 0.002, brk[-1] + 0.002)
    ax.set_xticks(brk); ax.set_xticklabels([f"{b:g}".replace("-", "−") for b in brk])
    ax.set_xlabel("$t_{01}$ (smallest inner product)")
    ax.set_ylabel("e − E(P)")
    ax.set_yscale("symlog", linthresh=lin, linscale=0.6)
    ax.set_ylim(-1e-13, 1e-1)
    ax.set_yticks([-1e-14, -1e-16, 0] + [10.0 ** k for k in range(-16, -1, 2)])
    nm, a, _, D, m = case1
    bar(ax1, 0.2, 0.6, m, D, nm)
    ax1.set_xlim(0, 1); ax1.set_xticks([0.5])
    ax1.set_xticklabels([f"all $t_{{ij}}$ ≥ {a:g}".replace("-", "−")])
    for a_ in (ax, ax1):
        style(a_, t)
        a_.axhline(0, color=t["axis"], linewidth=0.8)
        a_.grid(axis="y", color=t["grid"], linewidth=0.6); a_.set_axisbelow(True)
    title(ax, t, "Case 2: cap and slabs, by the range of $t_{01}$")
    title(ax1, t, "Case 1")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, name), facecolor=t["surface"], **SAVE)
    plt.close(fig)


# ---------------------------------------------------------------- data: k = 2 ring mode (as soft_mode/verify_soft_mode.py)
def pbp():
    X = [mp.matrix([0, 0, 1]), mp.matrix([0, 0, -1])]
    X += [mp.matrix([mp.cos(2 * mp.pi * k / 5), mp.sin(2 * mp.pi * k / 5), 0]) for k in range(5)]
    return X


def pucker(a):
    X = pbp()
    for k in range(5):
        v = X[2 + k].copy(); v[2] += a * mp.cos(2 * 2 * mp.pi * k / 5); X[2 + k] = v / mp.norm(v)
    return X


def energy(X, s):
    """sum over pairs of (d^-s - 1)/s  (= -log d at s = 0)."""
    E = 0
    for i, j in itertools.combinations(range(7), 2):
        L = mp.log(mp.norm(X[i] - X[j]))
        E += -L if s == 0 else mp.expm1(-s * L) / s
    return E


def soft_data():
    mp.mp.dps = 40
    h = mp.mpf("1e-8")
    X0, Xp, Xm = pbp(), pucker(h), pucker(-h)
    S = np.round(np.linspace(-1, 3, 81), 10)
    d2 = [float((energy(Xp, mp.mpf(s)) - 2 * energy(X0, mp.mpf(s)) + energy(Xm, mp.mpf(s))) / h ** 2) for s in S]
    mp.mp.dps = 50
    A = np.logspace(-4, -1, 25)
    dE = {}
    for s in (0, 1):
        E0 = energy(pbp(), s)
        dE[s] = [float(energy(pucker(mp.mpf(a)), s) - E0) for a in A]
    small = A <= 1e-2
    slope = {s: np.polyfit(np.log10(A[small]), np.log10(np.array(dE[s])[small]), 1)[0] for s in dE}
    return S, np.array(d2), A, dE, slope


def fig_soft(t, name, data):
    S, d2, A, dE, slope = data
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(10, 4.2))
    fig.patch.set_facecolor(t["surface"])
    ax.axhline(0, color=t["axis"], linewidth=0.8)
    ax.plot(S, d2, color=t["mark"], linewidth=1.6)
    for s0 in (0.0, 2.0):
        i = int(np.argmin(np.abs(S - s0)))
        ax.plot([S[i]], [d2[i]], "o", color=t["mark2"], markersize=5)
        ax.annotate(f"s = {S[i]:g}: {d2[i]:.1e}".replace("-", "−"), (S[i], d2[i]), textcoords="offset points",
                    xytext=(6, 8), fontsize=8, color=t["ink2"])
    ax.set_xlabel("s"); ax.set_ylabel(r"$\partial_a^2\, E_s(P_a)$ at $a = 0$")
    title(ax, t, "(a) second derivative along the k = 2 ring mode")
    for s, col, lab in ((0, t["mark"], "log (s = 0)"), (1, t["mark2"], "Coulomb (s = 1)")):
        bx.loglog(A, dE[s], "o-", color=col, markersize=3, linewidth=1.2,
                  label=f"{lab}: fitted slope {slope[s]:.2f} (a ≤ 0.01)")
    bx.set_xlabel("a"); bx.set_ylabel("$E_s(P_a) - E_s(P)$")
    title(bx, t, "(b) energy along the mode")
    leg = bx.legend(frameon=False, fontsize=8, loc="upper left")
    for tx in leg.get_texts():
        tx.set_color(t["ink2"])
    for a_ in (ax, bx):
        style(a_, t)
        a_.grid(color=t["grid"], linewidth=0.6); a_.set_axisbelow(True)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, name), facecolor=t["surface"], **SAVE)
    plt.close(fig)


# ---------------------------------------------------------------- data: cap minorants
def minorant_data():
    mp.mp.dps = 50
    J = json.load(open(CAP))
    H = {k: [mpq(c) for c in v] for k, v in J["H"].items()}
    phi = lambda x: -mp.log(2 - 2 * x) / 2
    f = lambda k, x: phi(x) - mp.polyval(H[k][::-1], x)
    c1, c2 = (mp.sqrt(5) - 1) / 4, (-mp.sqrt(5) - 1) / 4
    lo_cap, hi_cap = mpq(J["cell"][0]), mpq(J["cell"][1])
    off = [mp.mpf(10) ** k for k in np.linspace(-16, -1, 61)]
    touch = {"A": [lo_cap], "B": [mp.mpf(0)], "C": [c1, c2]}
    rng = {"A": (lo_cap, hi_cap), "B": (mp.mpf(-1), 1 - mp.mpf(10) ** -3), "C": (mp.mpf(-1), 1 - mp.mpf(10) ** -3)}
    out = {}
    for k in "ABC":
        a, b = rng[k]
        pts = set(mp.linspace(a, b, 800)) | set(touch[k])
        for c in touch[k]:
            pts |= {c + d for d in off} | {c - d for d in off}
        pts = sorted(p for p in pts if a <= p <= b)
        out[k] = (np.array([float(p) for p in pts]), np.array([float(f(k, p)) for p in pts]),
                  [(float(c), float(f(k, c))) for c in touch[k]], (float(a), float(b)))
    return out


def fig_minorant(t, name, data):
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(10, 4.4), gridspec_kw=dict(width_ratios=[2, 1]))
    fig.patch.set_facecolor(t["surface"])
    cols = {"A": t["mark3"], "B": t["mark"], "C": t["mark2"]}
    lab = {"A": "$\\varphi - H_A$", "B": "$\\varphi - H_B$", "C": "$\\varphi - H_C$"}
    for a_, keys in ((ax, "BC"), (bx, "A")):
        for k in keys:
            x, y, tp, _ = data[k]
            a_.semilogy(x, y, color=cols[k], linewidth=1.3, label=lab[k])
            for c, v in tp:
                a_.plot([c], [v], "o", color=cols[k], markersize=4)
                a_.axvline(c, color=t["axis"], linewidth=0.7, linestyle=":")
        style(a_, t)
        a_.grid(axis="y", color=t["grid"], linewidth=0.6); a_.set_axisbelow(True)
        a_.set_xlabel("t"); a_.set_ylim(1e-18, 1e1)
        leg = a_.legend(frameon=False, fontsize=9, loc="lower right")
        for tx in leg.get_texts():
            tx.set_color(t["ink2"])
    ax.set_ylabel(r"$\varphi(t) - H(t)$,  $\varphi(t) = -\frac{1}{2}\log(2-2t)$")
    ax.set_xticks([-1, data["C"][2][1][0], -0.5, 0, data["C"][2][0][0], 0.5, 1])
    ax.set_xticklabels(["−1", "$c_2$", "−0.5", "0", "$c_1$", "0.5", "1"])
    bx.set_xticks([-1, -0.995, -0.99]); bx.set_xticklabels(["−1", "−0.995", "−0.99"])
    title(ax, t, "$H_B$, $H_C$ on $[-1, 1)$; contact at 0 and at $c_1$, $c_2$")
    title(bx, t, "$H_A$ on $[-1, -99/100]$; contact at −1")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, name), facecolor=t["surface"], **SAVE)
    plt.close(fig)


# ---------------------------------------------------------------- configuration
def fig_configuration(t, name):
    X = np.array([[float(c) for c in v] for v in pbp()])
    D = np.array([[0, 0, 0]] * 2 + [[0, 0, np.cos(4 * np.pi * k / 5)] for k in range(5)])
    fig = plt.figure(figsize=(5, 5))
    fig.patch.set_facecolor(t["surface"])
    ax = fig.add_subplot(projection="3d")
    ax.set_facecolor(t["surface"])
    u = np.linspace(0, 2 * np.pi, 60)
    for z in np.linspace(-0.8, 0.8, 5):
        r = np.sqrt(1 - z * z)
        ax.plot(r * np.cos(u), r * np.sin(u), z + 0 * u, color=t["grid"], linewidth=0.6)
    for p in np.linspace(0, np.pi, 6, endpoint=False):
        ax.plot(np.cos(p) * np.sin(u), np.sin(p) * np.sin(u), np.cos(u), color=t["grid"], linewidth=0.6)
    d2 = np.linalg.norm(X[:, None] - X[None], axis=2)
    edge = sorted(set(np.round(d2[np.triu_indices(7, 1)], 9)))[:2]      # pole-ring and ring-neighbour distances
    for i, j in itertools.combinations(range(7), 2):
        if round(d2[i, j], 9) in edge:
            ax.plot(*X[[i, j]].T, color=t["ink2"], linewidth=1.0)
    ax.scatter(*X.T, color=t["mark"], s=40, depthshade=False)
    ax.quiver(*X[2:].T, *(0.45 * D[2:]).T, color=t["mark2"], linewidth=1.4, arrow_length_ratio=0.25)
    ax.set_box_aspect((1, 1, 1)); ax.view_init(elev=18, azim=35)
    ax.set_xlim(-1, 1); ax.set_ylim(-1, 1); ax.set_zlim(-1, 1)
    ax.set_axis_off()
    fig.subplots_adjust(0, 0, 1, 1)
    fig.savefig(os.path.join(OUT, name), facecolor=t["surface"], **SAVE)
    plt.close(fig)


if __name__ == "__main__":
    plt.rcParams.update({"font.family": "DejaVu Sans", "svg.fonttype": "none", "svg.hashsalt": "thomson-n7-log",
                         "mathtext.fontset": "dejavusans"})
    cd, sd, md = cell_data(), soft_data(), minorant_data()
    for mode, t in THEMES.items():
        fig_cells(t, f"cells_{mode}.svg", cd)
        fig_soft(t, f"soft_mode_{mode}.svg", sd)
        fig_minorant(t, f"minorant_cap_{mode}.svg", md)
        fig_configuration(t, f"configuration_{mode}.svg")
    print("fitted slopes (a <= 0.01):", {s: round(v, 3) for s, v in sd[4].items()})
    print("wrote figures to", OUT, "with matplotlib", matplotlib.__version__)
