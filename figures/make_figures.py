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
    """(a) orthographic view of P with the k = 2 ring mode; (b) vertical displacement of the ring points."""
    from matplotlib.patches import Circle, FancyArrowPatch
    X = np.array([[float(c) for c in v] for v in pbp()])               # 0 = N, 1 = S, 2..6 = ring k = 0..4
    th = 2 * np.pi * np.arange(5) / 5
    zk = np.cos(2 * th)                                                 # = cos(4 pi k / 5)
    A = 0.32                                                            # drawing amplitude (exaggerated)
    Y = np.array([[float(c) for c in v] for v in pucker(A)])            # displaced configuration P_a
    el, az = np.radians(15), np.radians(-80)
    w = np.array([np.cos(el) * np.cos(az), np.cos(el) * np.sin(az), np.sin(el)])   # towards the viewer
    r = np.cross([0, 0, 1], w); r /= np.linalg.norm(r); u = np.cross(w, r)
    pr = lambda P: np.stack([P @ r, P @ u], -1)
    dp = lambda P: P @ w

    fig = plt.figure(figsize=(9.2, 4.3))
    fig.patch.set_facecolor(t["surface"])
    ax = fig.add_axes([0.0, 0.0, 0.47, 0.9]); ax.set_aspect("equal"); ax.set_axis_off()
    ax.set_xlim(-1.32, 1.32); ax.set_ylim(-1.22, 1.3)
    ax.add_patch(Circle((0, 0), 1, facecolor=t["empty"], edgecolor=t["axis"], linewidth=1.0, zorder=0))
    s = np.linspace(0, 2 * np.pi, 361)
    for z0 in (0.0,) + tuple(np.sin(np.radians([-40, 40]))):          # equator and two latitude circles
        rr = np.sqrt(1 - z0 * z0); C = np.stack([rr * np.cos(s), rr * np.sin(s), z0 + 0 * s], -1)
        P2, front = pr(C), dp(C) >= 0
        for msk, ls in ((front, "-"), (~front, (0, (2, 3)))):
            Q = np.where(msk[:, None], P2, np.nan)
            ax.plot(*Q.T, color=t["grid"] if z0 else t["axis"], linewidth=0.8, linestyle=ls, zorder=1)
    edges = [(p, 2 + k) for p in (0, 1) for k in range(5)] + [(2 + k, 2 + (k + 1) % 5) for k in range(5)]
    for i, j in edges:
        back = dp(X[i]) + dp(X[j]) < -0.05
        ax.plot(*pr(X[[i, j]]).T, color=t["muted"] if back else t["ink2"], linewidth=0.9 if back else 1.3,
                linestyle=(0, (3, 3)) if back else "-", zorder=2 if back else 4)
    for k in range(5):                                                  # arrows to the displaced points
        a0, a1 = pr(X[2 + k]), pr(Y[2 + k])
        ax.add_patch(FancyArrowPatch(a0, a1, arrowstyle="-|>", mutation_scale=11, color=t["mark2"],
                                     linewidth=1.6, shrinkA=4, shrinkB=2, zorder=6))
        ax.scatter(*a1, s=34, facecolor="none", edgecolor=t["mark2"], linewidth=1.1, zorder=6)
    for i in range(7):
        back = dp(X[i]) < 0
        ax.scatter(*pr(X[i]), s=56 if not back else 40, color=t["mark"], alpha=0.6 if back else 1,
                   edgecolor=t["surface"], linewidth=1.0, zorder=5 if not back else 3)
    for i, lab, off in ((0, "N (fixed)", (10, 4)), (1, "S (fixed)", (10, -10))):
        ax.annotate(lab, pr(X[i]), xytext=off, textcoords="offset points", color=t["ink2"], fontsize=9, zorder=7)
    for k in range(5):                                                  # label outward, away from the arrow
        v = pr(X[2 + k]); d = v / np.linalg.norm(v)
        off, ha = (12 * d[0], -16 if zk[k] > 0 else 9), "left" if d[0] > 0.3 else "right" if d[0] < -0.3 else "center"
        if k == 2:                                                      # back point next to k = 3: label inward
            off, ha = (9, -13), "left"
        ax.annotate(f"k = {k}", v, xytext=off, textcoords="offset points", color=t["ink2"], fontsize=8.5, ha=ha,
                    zorder=7)
    fig.text(0.012, 0.93, "(a) P and the k = 2 ring mode (amplitude exaggerated)", color=t["ink"], fontsize=11)

    bx = fig.add_axes([0.6, 0.2, 0.38, 0.6]); style(bx, t)
    g = np.linspace(0, 2 * np.pi, 400)
    bx.axhline(0, color=t["axis"], linewidth=0.8)
    bx.plot(np.degrees(g), np.cos(2 * g), color=t["mark2"], linewidth=1.6, label=r"$\cos 2\theta$ (mode $s_1$)")
    bx.plot(np.degrees(g), np.sin(2 * g), color=t["muted"], linewidth=1.1, linestyle=(0, (4, 3)),
            label=r"$\sin 2\theta$ (mode $s_2$)")
    bx.vlines(np.degrees(th), 0, zk, color=t["mark2"], linewidth=1.0, alpha=0.6)
    bx.scatter(np.degrees(th), zk, s=40, color=t["mark"], edgecolor=t["surface"], linewidth=1.0, zorder=5)
    bx.set_xticks(np.degrees(th).tolist() + [360])
    bx.set_xticklabels([f"k = {k}\n{72 * k}°" for k in range(5)] + ["\n360°"])
    bx.set_yticks([-1, -0.5, 0, 0.5, 1]); bx.set_ylim(-1.15, 1.15); bx.set_xlim(-12, 372)
    bx.grid(axis="y", color=t["grid"], linewidth=0.6)
    bx.set_xlabel(r"ring point $k$ at azimuth $\theta_k = 2\pi k/5$")
    bx.set_ylabel(r"vertical displacement / $a$")
    leg = bx.legend(loc="lower left", fontsize=8.5, frameon=False, ncol=2, bbox_to_anchor=(-0.02, 1.0),
                    handlelength=2.2, columnspacing=1.5)
    for tx in leg.get_texts(): tx.set_color(t["ink2"])
    fig.text(0.535, 0.93, "(b) ring heights in the two flat directions", color=t["ink"], fontsize=11)
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
