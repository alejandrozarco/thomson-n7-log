# Coulomb $`s = 1`$, $`N = 7`$: exact certificates and a Lean 4 check

Status: **computational certificates and a Lean 4 formalisation, not peer reviewed; produced by AI models** (see
[`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md)). Like the rest of this repository, this is an AI-produced warrant, not a
digested proof (see the note at the top of [`../README.md`](../README.md)). Added 2026-10-08.

> [!NOTE]
> The statement here is the seven-electron case of Thomson's problem. A Lean 4 formalisation of it by Hung Tran
> ([huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean), September 2026) precedes this work, and the
> whole method of this repository is modelled on it. This directory is a **second check** of that statement with
> **its own certificates** (Case 1, five slabs and the cap). It is **not independent** of Hung Tran's development:
> the Lean version uses his local lemma near the bipyramid, his energy conversion, admissibility of $`P`$ and closed
> form of $`E(P)`$, and his generic machinery (ring rigidity, chart, gauge, certificate soundness): unchanged
> declarations are regenerated from his repository and not stored here, adapted ones are stored with per-declaration
> attribution (`../lean/README.md`, Upstream code; see [Licence](../README.md#licence)).

For seven points $`x_1,\dots,x_7`$ on the unit sphere $`S^2`$, write $`t_{ij} = \langle x_i, x_j\rangle`$ and

```math
\varphi_1(t) = (2-2t)^{-1/2}, \qquad E_1(x) = \sum_{i \lt j} \lVert x_i - x_j \rVert^{-1} = \sum_{i \lt j} \varphi_1(t_{ij}).
```

The regular pentagonal bipyramid $`P`$ has $`E_1(P) = \tfrac12 + \tfrac{10}{\sqrt2} + 5\varphi_1(c_1) + 5\varphi_1(c_2)
\approx 14.4529774142`$, with $`c_1 = \cos 72^\circ`$, $`c_2 = \cos 144^\circ`$. The statement: for every configuration
of seven **pairwise distinct** points on $`S^2`$, $`E_1(x) \ge E_1(P)`$, with equality iff $`x = P`$ up to $`O(3)`$ and
relabelling.

## The argument and what checks it

The case split, the typed three-point identities and the PSD checks are those of the log case in the parent
directory (they are kernel-free); only the minorants $`H \le \varphi_1`$, the values $`e`$ and the steps on the cap
depend on the kernel.

| piece | file | checker | result (`../verification/coulomb/`) |
|---|---|---|---|
| Case 1 (all $`t_{ij} \ge -9/10`$), degree 10 | `certs/cert_case1_coulomb_D10.json` | `../checkers/check_cell.py`, `../checkers/check_minorant_cell.py` | $`e - E_1(P) \approx 5\cdot10^{-4}`$; identities exact, blocks positive definite, $`\varphi_1 - H > 10^{-7}`$ (ball arithmetic) |
| five slabs, degrees 10, 10, 12, 12, 12 | `certs/cert_slab_*_coulomb_D*.json` | same | $`e - E_1(P) \approx 10^{-5}`$ each |
| cap $`t_{01} \in [-1, -99/100]`$, degree 12 | `cert_cap_coulomb_D12.json`; re-rounded to at most 120-bit numbers for Lean: `cert_cap_coulomb_D12_short.json` | `check_cap1.py` | identities and PSD exact; $`0 \lt E_1(P) - e \approx 7.3\cdot10^{-17} \lt 10^{-16}`$; minorants exact: $`p = 1 - (2-2t)H^2`$ has no root on the range (Sturm sequences over $`\mathbb{Q}`$), so $`|H| \lt \varphi_1`$ |
| coercivity on the cap | same | `check_coerc1.py` | $`\varphi_1 - H \le 10^{-16}`$ forces $`t`$ within $`10^{-6}`$ of an inner product of $`P`$ (certified: $`8.7\cdot10^{-7}`$, $`6.6\cdot10^{-7}`$, $`2.6\cdot10^{-14}`$ for the classes B, C, A) |
| local lemma (Python) | — | `check_local1.py` | second order: for gauge-fixed unit $`z`$ with $`0 \lt \lVert z - P\rVert \le \sqrt7 \cdot \tfrac{11}{2}\cdot 10^{-6}`$, $`E_1(z) \gt E_1(P)`$ (Hessian on the relevant subspace $`\ge 0.00919`$, ball arithmetic) |

The remaining deductions (relabelling, ring rigidity, Gram window to coordinates, gauge, sup to $`\ell^2`$ radius,
assembly) are the kernel-free ones of the log case (`../METHOD.md`, `../lean/OVERVIEW.md`).

Differences from the log and $`s = 2`$ cases:
- At $`s = 0`$ and $`s = 2`$ the bipyramid has a flat second-order ring deformation (`../soft_mode/`); at $`s = 1`$ it
  does not. So the cap needs no soft-mode conditions on its facial reduction (they would be infeasible here), the
  contact of the minorant $`H_B`$ at $`0`$ is quadratic rather than quartic, and a second-order local lemma suffices.
- The values of $`\varphi_1`$ at the inner products of $`P`$ lie in a degree-8 number field, so the cap certificate is
  rounded just below them (as for log, not exactly sharp as for $`s = 2`$); the contact slopes are dyadic, with a
  certified mismatch below $`1.2\cdot10^{-20}`$, which `check_coerc1.py` takes into account.

## Lean 4

`lean/` is a Lake workspace (Lean v4.34.1, Mathlib `d13f23b`). The statement, `lean/CoulN7/Challenge.lean`, is
Hung Tran's `thomson_seven` / `thomson_seven_unique` over his definitions (`coulombEnergy`, `SphereConfig`,
`pentBipyramid`, regenerated into `lean/ThomsonGen/Preamble.lean` by `lean/regen.sh`, not stored), renamed `ThomsonN7S1.coulomb_seven` and
`ThomsonN7S1.coulomb_seven_unique`. `CoulN7/Solution.lean` derives them from this directory's certificates through the
kernel-generic assembly of the log case (`ThomsonGen/Generic/`). On the cap, the local statement is Hung Tran's
`Reg.pent_local_min_sup` (sup radius $`1/30000`$), which covers the coercivity windows used here (tube width
$`\tau_0 = 1/165000`$; Lean windows at most $`4.77\cdot10^{-6}`$); `check_local1.py` above is not formalised.

Records (`../verification/lean/coulomb/record_2026-10-08.txt`; paths there that start with `../` or `numerics/` refer
to the development tree):
- clean build of all 130 modules, one at a time (`enzo/lakeseq.tsv`; peak memory 9.4 GB, `Case1/ChkS0`);
- `#print axioms`: both theorems `[propext, Classical.choice, Quot.sound]`; no `native_decide`;
- Comparator (`lean/comparator_coul.json`): "Your solution is okay!" (run without the landrun sandbox);
- second kernel: `lean4export` + nanoda checked 54624 declarations with no errors and rejected a copy with one
  certificate literal changed (type-checker failure, not a parse error);
- after these runs, comments in two files were edited (`CoulN7/Bridge.lean`, `CoulN7/Case1/Data.lean`); no statement,
  definition, proof term or certificate datum changed, and both files and their 20 dependents were recompiled on the Mac.

`lean/SHA256SUMS` lists the 98 `CoulN7` modules and the 6 stored dependencies. The certificate-derived modules were
written by the generators in `lean/gen/`, which were run in the development tree (paths there assume its layout); they
regenerate all 91 generated modules byte for byte (`../verification/lean/coulomb/regen_all_2026-10-08.sha256`) and are
not needed to build or check anything here. Build as in `../lean/README.md`: `./regen.sh` (regenerates the upstream
modules), then `lake build` (or one module at a time, as recorded).

## Reproduce

```sh
export OMP_NUM_THREADS=1
python3 ../checkers/check_cell.py certs/cert_*_coulomb_*.json            # Case 1 + slabs, exact: ALL_OK
python3 ../checkers/check_minorant_cell.py certs/cert_*_coulomb_*.json   # minorants, ball arithmetic
python3 check_cap1.py cert_cap_coulomb_D12.json                        # cap, exact (~10 s)
python3 check_cap1.py cert_cap_coulomb_D12_short.json                  # the re-rounded cap used by Lean
python3 check_coerc1.py cert_cap_coulomb_D12_short.json 1e-16          # coercivity windows (exit 0 iff OK)
python3 check_local1.py                                                # second-order local lemma
```

`generate/` holds the scripts that produced the certificates (float SDP solves, the value-only facial reduction
`face.py`, exact rounding); like `../generate/`, they are not needed for verification and assume the development layout.

## Context

The pentagonal bipyramid is believed to be the minimiser of the Riesz $`s`$-energy of seven points exactly for
$`0 \le s \le 2`$ (numerical studies: Melnyk, Knop and Smith 1977; Nerattini, Brauchart and Kiessling,
[arXiv:1307.2834](https://arxiv.org/abs/1307.2834), who describe bifurcations at $`s = 0`$ and $`s = 2`$). This
repository now has warrants for $`s = 0`$ (log), $`s = 1`$ (this directory) and $`s = 2`$ (`../riesz2/`). Nothing here
covers a range of exponents.

## Reviews

Two read-only reviews by gpt-6-astra (OpenAI): of the Python chain (no mathematical obstruction; three checker and
documentation fixes, applied) and of the Lean port (no mathematical defect found, statement faithful; four tooling,
reproducibility and wording fixes, applied). No human has checked this directory.

## References

- H. Tran, Lean formalisation of the seven-electron Thomson problem, [huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) (2026).
- L. Kryvonos, L. Liehr, M. A. Taylor, *Energy minimization for eight points on the sphere*, [arXiv:2609.22077](https://arxiv.org/abs/2609.22077).
- Tooby-Smith and Zughaid, [Thomson-N-8-Warrant](https://github.com/jstoobysmith/Thomson-N-8-Warrant).
- C. Bachoc, F. Vallentin, *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. 21 (2008), 909–924.
- R. Nerattini, J. S. Brauchart, M. K.-H. Kiessling, *"Magic" numbers in Smale's 7th problem*, [arXiv:1307.2834](https://arxiv.org/abs/1307.2834).
