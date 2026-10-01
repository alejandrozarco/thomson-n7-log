# Riesz $`s = 2`$, $`N = 7`$: exact certificates

Status: **computational certificates and a Lean 4 formalisation, not peer reviewed; produced by AI models** (see
[`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md)). Like the rest of this repository, this is an AI-produced warrant, not a
digested proof: we do not regard the statement as settled by it, and a human-readable treatment is welcome (see the
note at the top of [`../README.md`](../README.md)).

For seven points $`x_1,\dots,x_7`$ on the unit sphere $`S^2`$, write $`t_{ij} = \langle x_i, x_j\rangle`$ and

```math
\varphi_2(t) = \frac{1}{2-2t}, \qquad E_2(x) = \sum_{i \lt j} \varphi_2(t_{ij}).
```

The regular pentagonal bipyramid $`P`$ (one point at each pole, five equally spaced on the equator) has

```math
E_2(P) = \frac14 + 10\cdot\frac12 + 5\bigl(\varphi_2(c_1) + \varphi_2(c_2)\bigr) = \frac{41}{4}, \qquad c_{1,2} = \frac12 \pm \frac{\sqrt5}{10},
```

$`c_1, c_2`$ being the two equatorial inner products of $`P`$ ($`\cos 72^\circ`$, $`\cos 144^\circ`$). This directory contains
exact certificates and checkers for the statement: for every configuration of seven **pairwise distinct** points on
$`S^2`$, $`E_2(x) \ge 41/4`$, with equality iff $`x = P`$ up to $`O(3)`$ and relabelling. (Distinctness matters under any
convention where $`1/0`$ is given a finite value; with $`1/0 = 0`$, seven coincident points would give $`E_2 = 0`$.)

This reuses the case split, the typed three-point identity and the SOS/PSD checking machinery of the log-kernel
argument in the parent directory (`../checkers/check_cert.py`, `../checkers/check_cell.py`): those identities are
kernel-free, and only the minorants $`H \le \varphi_2`$ and the value $`e`$ vs. $`E_2(P)`$ depend on the kernel. See
`../METHOD.md` for the shared structure and `../README.md` for the log-kernel case.

The statement is also checked in Lean 4 (standard axioms only) in `lean/`; see `lean/README.md`.

## Headline

At $`s = 2`$ every value and derivative of $`\varphi_2`$ at the inner products of $`P`$ lies in $`\mathbb{Q}(\sqrt5)`$, and
the facial reduction of the cap is Galois stable, so the degree-12 typed cap certificate rounds with the pins
**exactly** at $`\varphi_2(P)`$: the cap bound is **exactly sharp**, $`e = E_2(P) = 41/4`$ with no gap. Every minorant
inequality is decided exactly (rational arithmetic, no floating point, no interval arithmetic): writing
$`\varphi_2(t) - H(t) = p(t)/(2-2t)`$ with $`p(t) = 1 - (2-2t)H(t)`$ a polynomial, $`p = F \cdot q`$ for an exact touching
factor $`F \ge 0`$ and a quotient $`q`$ with no root in the closed range and $`q(a) \gt 0`$ at the left endpoint (Sturm
sequence, exact rational coefficients). Since the cap bound is sharp, the equality case follows directly from the
touching factors of the cap minorants: no local lemma or coercivity/rigidity handoff is needed at $`s = 2`$ (it is used
as a backup route in the source project, not included here).

## Case split

| cell | range | $`D`$ | $`e - E_2(P)`$ (exact) | minorant (exact) |
|---|---|---|---|---|
| cap (Case 2) | $`t_{01} \in [-1,\, -99/100]`$ | 12 | $`0`$ (exactly sharp: $`e = 41/4`$) | $`A`$: factor $`t+1`$, $`q_A \gt 0`$; $`B`$: factor $`t^4`$, $`q_B \gt 0`$; $`C`$: factor $`(4t^2+2t-1)^2`$, $`q_C \gt 0`$ |
| Case 1 | all $`t_{ij} \ge -9/10`$ | 10 | $`140737488355/140737488355328`$ | no root of $`1-(2-2t)H`$ in the closed range |
| slab 1 | $`t_{01} \in [-99/100,\, -49/50]`$ | 10 | $`84442493013/281474976710656`$ | no root of $`1-(2-2t)H`$ in the closed range |
| slab 2 | $`t_{01} \in [-49/50,\, -24/25]`$ | 10 | $`28147497671/281474976710656`$ | no root of $`1-(2-2t)H`$ in the closed range |
| slab 3 | $`t_{01} \in [-24/25,\, -47/50]`$ | 10 | $`28147497671/281474976710656`$ | no root of $`1-(2-2t)H`$ in the closed range |
| slab 4 | $`t_{01} \in [-47/50,\, -93/100]`$ | 10 | $`7036874419/70368744177664`$ | no root of $`1-(2-2t)H`$ in the closed range |
| slab 5 | $`t_{01} \in [-93/100,\, -9/10]`$ | 12 | $`28147497663/562949953421312`$ | no root of $`1-(2-2t)H`$ in the closed range |

Tiling: $`[-1,-99/100] \to [-99/100,-49/50] \to [-49/50,-24/25] \to [-24/25,-47/50] \to [-47/50,-93/100] \to [-93/100,-9/10]`$,
and Case 1 covers all $`t_{ij} \ge -9/10`$. The full table with certificate hashes is regenerated in `COVERAGE.md`.
$`D`$ is the degree of the three-point certificate.

## Minorant factorisations

Every minorant is checked by the identity $`\varphi_2 - H = F q / (2-2t)`$ with $`F \ge 0`$ on the stated range and $`q`$
strictly positive there (no real root, positive at the left endpoint):

* cap, class $`A`$ (range $`[-1,-99/100]`$): $`F = t+1`$, i.e. $`H_A`$ touches $`\varphi_2`$ only at $`t=-1`$;
* cap, class $`B`$ (range $`[-1,1]`$): $`F = t^4`$, touching only at $`t=0`$ to order 4;
* cap, class $`C`$ (range $`[-1,1]`$): $`F = (4t^2+2t-1)^2`$, touching at the two roots $`c_1, c_2`$ of $`4t^2+2t-1`$, i.e.
  exactly the equatorial inner products of $`P`$;
* Case 1 and the five slabs: $`F = 1`$ (no prescribed touching point), only strict positivity of $`q`$ on the closed
  range is required.

## Files

| path | content |
|---|---|
| `cert_cap_riesz2_D12.json` | cap certificate (rationals) |
| `cert_cap_riesz2_D12_dyadic.json` | cap certificate re-rounded to dyadic (power-of-two denominator) coefficients |
| `certs/` | Case 1 and slab certificates |
| `cells2.json` | the non-cap cells of the case split, in covering order |
| `check_cap2.py` | exact checker for the cap certificate (imports `../checkers/check_cert.py`, `../checkers/check_cell.py`, `minorant2.py`) |
| `check_cell2.py` | exact checker for Case 1 and the slab certificates (imports `../checkers/check_cell.py`, `minorant2.py`) |
| `minorant2.py` | exact 1-D minorant check ($`H \le \varphi_2`$) by polynomial factorisation and Sturm sequences |
| `controls2.py` | tamper controls: every modified certificate is rejected |
| `make_coverage2.py` | regenerates `COVERAGE.md` from the certificates |
| `COVERAGE.md` | coverage table generated by `make_coverage2.py` |

## Reproduce

Requirements: Python 3 with `sympy` (used only by `minorant2.py`; everything else is `fractions.Fraction`). Versions
used: Python 3.9.6, sympy 1.14.0, on macOS arm64. Each checker runs on one core.

```sh
export OMP_NUM_THREADS=1
python3 riesz2/check_cap2.py riesz2/cert_cap_riesz2_D12.json          # cap, exact: ALL_OK               (~20 s)
python3 riesz2/check_cap2.py riesz2/cert_cap_riesz2_D12_dyadic.json   # cap, dyadic cert, exact: ALL_OK   (~20 s)
python3 riesz2/check_cell2.py riesz2/certs/cert_*_riesz2.json         # Case 1 + slabs, exact             (~1 min)
python3 riesz2/make_coverage2.py                                     # all cells, writes COVERAGE.md      (~1 min)
python3 riesz2/controls2.py                                          # tampered copies rejected: CONTROLS_OK (~1.5 min)
sha256sum -c MANIFEST.sha256                                         # or: shasum -a 256 -c MANIFEST.sha256
```

Each checker exits with status 0 only if all of its checks pass.
