# Riesz $`s`$-energy on the interval $`1/3 \le s \le 7/4`$, $`N = 7`$: certificates, checkers and a Lean 4 development

Status: **computational results and a Lean 4 formalisation, not peer reviewed; produced by AI models** (see
[`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md)). Added 2026-11-17.

> [!IMPORTANT]
> Like the rest of this repository, this directory is an AI-produced **warrant**: a machine-checked argument that no
> human has digested and that has not been peer reviewed. The repository owner does not regard the question as
> settled by it. Independent checks and human-readable arguments are welcome, and credit for a human-readable argument
> belongs to whoever writes one. Questions and corrections:
> [GitHub issues](https://github.com/alejandrozarco/thomson-n7-log/issues).

For seven points $`x_1,\dots,x_7`$ on the unit sphere $`S^2`$ and a real exponent $`s`$, write
$`t_{ij} = \langle x_i, x_j\rangle`$ and

```math
\varphi_s(t) = (2-2t)^{-s/2}, \qquad E_s(x) = \sum_{i \lt j} \lVert x_i - x_j \rVert^{-s} = \sum_{i \lt j} \varphi_s(t_{ij}).
```

$`P`$ is the regular pentagonal bipyramid, with
$`E_s(P) = \varphi_s(-1) + 10\,\varphi_s(0) + 5\,\varphi_s(c_1) + 5\,\varphi_s(c_2)`$, $`c_1 = \cos 72^\circ`$,
$`c_2 = \cos 144^\circ`$. This directory is directed at the statement: for every real $`s`$ with
$`1/3 \le s \le 7/4`$ and every configuration of seven pairwise distinct points on $`S^2`$, $`E_s(x) \ge E_s(P)`$,
with equality only if $`x`$ is the image of $`P`$ under an orthogonal map after a relabelling. The exponent is
quantified over the whole interval (real $`s`$, not a finite set of values). It contains

- exact Python checkers for the interval (`n7_interval/`), with a coverage checker `range_check.py`; their
  certificates and per-piece reports are in a separate data archive (see [Bulk data](#bulk-data-separate-archive));
- a Lean 4 development (`lean/`) in which this statement is stated and the kernel checks it, with the records of the
  build, the axiom checks, a second kernel and Comparator (`../verification/lean/riesz_range/`).

## Bulk data (separate archive)

The certificate files and per-piece reports are not stored in git. They are in a separate Zenodo archive,
**DOI: [10.5281/zenodo.24355941](https://doi.org/10.5281/zenodo.24355941)** (record 24355941, also set as
`ZENODO_RECORD` in `fetch_bulk.sh`). Git holds the Lean sources, the checkers and `range_check.py`, the documents, the recorded
outputs and inventories, the hash lists and the script that fetches and verifies the archive. A fresh clone
therefore needs one download step before `range_check.py` can run:

```sh
sh riesz_range/fetch_bulk.sh                         # from the Zenodo record; or:
sh riesz_range/fetch_bulk.sh path/to/riesz_range_bulk_v2.8.tar   # a local copy (or a URL)
```

The script checks the sha256 of the archive, unpacks it into the repository (all its paths start with
`riesz_range/`), checks every unpacked file against `BULK_SHA256SUMS` and ends with one line `BULK OK ...` or
`BULK FAIL ...`. `.gitignore` lists the unpacked paths, so `git status` stays clean.

| file of the record | bytes | sha256 | content |
|---|---|---|---|
| `riesz_range_bulk_v2.8.tar` | 452 655 616 | `e7fedde5e7b0a683f20334bb104ec763bdfde01cd604b9576d7882f3cecc9b1c` | 286 files (`BULK_SHA256SUMS`): the 227 certificate and report files of `n7_interval/` listed below, and `cap_rr/` (59 files) |
| `riesz_seven_range.ndjson.xz` | 337 318 704 | `2817d61623cb9e18f5664ebab11d78f8294f9d9cf2016472e56d22a05730bab0` | the lean4export export of the two `Full` theorems checked by nanoda and Comparator; decompressed 2 004 582 689 bytes, sha256 `e994407ff4fd90b0b57c28edc3ac1d2c66e8c28bb00a7a4d4bcdf4fe2fc3ba5a` |
| `riesz_seven_core.ndjson.xz` | 239 993 632 | `e92f21cf94cd969144cfbff6041ff435e48f89f94d03e300571234c11cfa8715` | the export of the two `Core12` theorems checked by nanoda; decompressed 1 465 454 494 bytes, sha256 `878884835761bf88f0523516938e0095b88ba9c506d9bc931b0b44cf34cf1883` |
| `BULK_SHA256SUMS` | | | the per-file list of this directory's `BULK_SHA256SUMS`, followed by the sha256 of the three files above |

The two exports are needed only to repeat the second-kernel and tamper checks; `sh riesz_range/fetch_bulk.sh
--exports` fetches them into `riesz_range/exports/` and checks their sha256 (decompress with `xz -d`, then compare
with the sha256 above).

What the archive holds, by role:
- in `n7_interval/`: every certificate file (`cellsS/certs_*/`, `capS/*.json.gz`, `capS/cert_cap_s3_4_D12.json`,
  `capR/cert_dirs_D12.json`, `cap1/cert_cap_coulomb_D12.json`; 185 files) and every per-piece report that
  `range_check.py` reads (`capR/pieces/`, `capR/pieces_nsub/`, `cellsS/results.jsonl`, `cellsS/range_pieces.jsonl`,
  `cellsS/logs/`, `localS/cover2q_*.jsonl`; 42 files), byte-identical to the files of the release candidate that
  were checked;
- `cap_rr/`: the re-rounded cap certificates from which the Lean cap modules were generated (see
  [The argument](#the-argument)): `nodes/` (24 node certificates; 22 of them are named by Lean modules, the other two,
  `s = 23/24` and `25/24`, were used only by the Python re-check), `dirs/cert_dirs_D12_rr.json` and the 7
  per-direction files `dirs/cert_dir{0..6}_D12_rr.json` named by the Lean modules, `capS/` (the exact node checks of
  the 24 re-rounded nodes), `range_check_rr.txt` and `range_check_rr.json` (output and inventory of the
  `range_check.py` run over the re-rounded cap, route `exact`, RANGE_OK on $`[1/3, 7/4]`$, 2026-11-07) and
  `RR_SHA256SUMS.txt` (the hash list written with them). The 29 files named by Lean modules have the sha256 prefixes
  that the module headers record.

Not in git and not in the archive: nine unused cap reports from superseded runs
(`capR/pieces/check_capR_{11_12__1_1,1_1__13_12,2_3__3_4}.txt` and six files in `capR/pieces_nsub/`; list in
`../verification/riesz_range/RC_EXACTNESS.txt`, section 5). `range_check.py` dropped them as stale and does not use
them; without them it gives the same verdicts with the same used pieces, all authenticated by sha256, and no
`NOT_OK ... stale` lines (`../verification/riesz_range/fresh_clone_with_bulk.txt`). The piece reports of the Python
re-check of the re-rounded cap are not included either; they are records of that development run and are not read by
anything in this release.

## The Lean statement

`lean/RieszN7/Release/FullChallenge.lean` (statements with `sorry`); `lean/RieszN7/Release/FullSolution.lean` has the
same statements over the same definitions, discharged by `RieszN7.Full.riesz_seven_range` and
`RieszN7.Full.riesz_seven_unique_range` of `lean/RieszN7/MainFull.lean`:

```lean
import RieszN7.Basic

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

theorem riesz_seven_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x := by
  sorry

theorem riesz_seven_unique_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7Riesz
```

(Module docstring omitted.) The same file pattern with `Core12` in place of `Full` states the sub-interval
$`1/2 \le s \le 3/2`$ (`ThomsonN7Riesz.riesz_seven_core`, `riesz_seven_unique_core`); see the records for what was run
on it.

**Trusted base** (what a reader has to accept in addition to the Lean kernel and Mathlib): the definitions the
statements use, in the four modules the challenge file imports.

| definition | module | content |
|---|---|---|
| `ThomsonN7.R3` | `ThomsonGen/Preamble.lean` (regenerated, see below) | `EuclideanSpace ℝ (Fin 3)` |
| `ThomsonN7.SphereConfig n` | same | `{x : Fin n → R3 \| (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}` |
| `ThomsonN7.cyl ρ θ h`, `ThomsonN7.pentBipyramid` | same | `cyl ρ θ h = !₂[ρ * cos θ, ρ * sin θ, h]`; `pentBipyramid i` = `cyl 1 (2 * π * i / 5) 0` for `i < 5`, `cyl 0 0 1` for `i = 5`, `cyl 0 0 (-1)` for `i = 6` |
| (not used by the statements) | `ThomsonGen/Base.lean` (regenerated) | `ThomsonN7.Base.phi`, `c1`, `c2`, `IsNode` and lemmas; imported on the way to `RieszN7.Basic` |
| (not used by the statements) | `lean/RieszN7/Core/Rpow.lean` | `RieszN7.phiS s t = (2 - 2 * t) ^ (-(s / 2))`, `xt`, `psi` and lemmas |
| `RieszN7.rieszEnergy s x` | `lean/RieszN7/Basic.lean` | `∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ (-s)` |

`ThomsonGen/Preamble.lean` and `ThomsonGen/Base.lean` are H. Tran's definitions
([huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) @ `25f2fa5`), regenerated by
`lean/regen.sh` and not stored here (as in `../lean/`, `../riesz2/lean/` and `../coulomb/lean/`).

**Conventions.**
- Pairwise distinct points: `SphereConfig` requires `Function.Injective x`.
- Real powers at $`0`$: `‖x i - x j‖ ^ (-s)` is `Real.rpow`, and Mathlib has `0 ^ y = 0` for `y ≠ 0`. A configuration
  with two coincident points would therefore get the value $`0`$ for that pair rather than $`+\infty`$; such
  configurations are excluded by injectivity. The Python side uses $`E_s = +\infty`$ for coincident points
  (`n7_interval/RANGE_ASSEMBLY.md`, section 1), the Lean statement excludes them.
- `s` is any real number with `1 / 3 ≤ s ∧ s ≤ 7 / 4`; both ends are included.

## The argument

The fixed-$`s`$ argument is the case split of the log, $`s = 1`$ and $`s = 2`$ cases (`../METHOD.md`) with
$`\varphi_s`$ in place of the kernel: the most nearly antipodal pair $`t_{01} = \min t_{ij}`$ either satisfies
$`t_{01} \ge -9/10`$ (Case 1), or lies in one of six slabs covering $`[-99/100, -9/10]`$ (breakpoints $`-99/100`$,
$`-49/50`$, $`-24/25`$, $`-47/50`$, $`-93/100`$, $`-183/200`$, $`-9/10`$), or in the cap $`[-1, -99/100]`$, which
contains $`P`$. To treat all $`s`$ in the interval, each component is covered by finitely many **pieces**
$`[a, b]`$ of the $`s`$-axis. A piece is certified for every real $`s \in [a, b]`$ from exact node certificates at
the ends, by checkers that bound the $`s`$-dependence (chord and Bernstein bounds in ball arithmetic, exact rational
identities). On the cap the certificate family is affine in $`s`$ and attains $`e(s) = E_s(P)`$ exactly, so the cap
needs no positive gap.

| component | checker (`n7_interval/`) | pieces used by `range_check.py` |
|---|---|---|
| Case 1, cut $`-9/10`$, degree 10 | `cellsS/check_piece.py`, `cellsS/check_bern.py` | 22 |
| six slabs, degree 10 | `cellsS/check_piece.py` | 21, 21, 23, 23, 23, 21 |
| cap $`[-1, -99/100]`$, degree 12, value-only face | `capR/check_capR.py` | 36 |
| local lemma near $`P`$ (Python route `local` only) | `localS/check_localS.py` (cover2q) | 77 |

The counts in this table are those of `range_check.py`. The Lean development has its own piece subdivision: 13
pieces for Case 1, 21, 21, 23, 23, 23, 21 for the six slabs and 21 for the cap (`lean/RieszN7/Range/CellsFull/*.lean`,
`lean/RieszN7/Range/CapFull.lean`).

`range_check.py` reads the per-piece reports, authenticates each by the sha256 of its checker sources and inputs, and
decides in exact rational arithmetic that the pieces cover $`[1/3, 7/4]`$ component by component and fit together.
The decisions taken and the bookkeeping conditions are in `n7_interval/RANGE_ASSEMBLY.md` (an internal document, see
below). Route `local` uses the local lemma on the cap; route `exact` uses that $`e(s) = E_s(P)`$ exactly on the cap and
needs no local lemma; both report RANGE_OK on $`[1/3, 7/4]`$ (`n7_interval/RANGE_CHECK_OUTPUT_ext.txt`).

The Lean development follows route `exact` (`MainFull.lean`: Case 1, the six slabs and the cap glued for every
$`s \in [1/3, 7/4]`$ by `seven_of_specs_sharp`, without a local lemma). It contains the certificate data as Lean
literals, in modules written by generator scripts that are not included and are not needed to check anything; every
certificate check is a `Bool` computation decided by `decide +kernel` (no `native_decide`). Each generated module names
the certificate files it was made from with a sha256 prefix. The Case 1 and slab certificates are the files of
`n7_interval/` (in the bulk archive); the cap modules were generated from re-rounded copies of the cap node and
direction certificates. These 29 files are in the bulk archive under `cap_rr/`, with the sha256 prefixes that the
module headers record (`../verification/riesz_range/RC_EXACTNESS.txt`, sections 8 and 12). The Python cap pieces of
`n7_interval/` and the Lean cap modules therefore use different roundings of the cap certificates: on the cap, the
Python check of `n7_interval/` and the Lean check are separate checks of different data. The re-rounded certificates
were also checked in Python (2026-11-07: exact node checks, `cap_rr/capS/`, and a `range_check.py` run over the
re-rounded cap, RANGE_OK on $`[1/3, 7/4]`$, route `exact`, `cap_rr/range_check_rr.txt`); the piece reports of that run
are not included.

## Which tool checked what

In the record column, the entries of the Lean rows (from `build/` on) are relative to
`../verification/lean/riesz_range/`; the other paths are relative to this directory.

| what | tool | record |
|---|---|---|
| node certificates and pieces (identities exact, PSD, minorants, the $`s`$-dependence) | Python checkers, exact rationals and arb balls (python-flint) | the reports in `n7_interval/` |
| every used piece re-run with the final checkers | `range_check.py --recheck` (2026-11-07; repeated 2026-11-17 on a Linux workstation, which wrote the reports in this release) | `n7_interval/RANGE_RECHECK_OUTPUT*.txt`, `../verification/riesz_range/range_recheck_2026-11-17.txt` |
| coverage of $`[1/3, 7/4]`$, authentication of the 267 used reports by the sha256 they record for their checker sources and inputs | `range_check.py` | `n7_interval/RANGE_CHECK_OUTPUT_ext.txt`; runs on the reports of this release: `../verification/riesz_range/range_check_after_recheck.txt`; earlier runs on the reports of 2026-11-07: `../verification/riesz_range/range_check_rc_run.txt`, `../verification/riesz_range/range_check_fresh_clone.txt` |
| the Lean development, including all certificate checks | Lean 4 kernel, v4.34.1 (build, one module at a time) | `build/` |
| axioms of the four main theorems: exactly `propext`, `Classical.choice`, `Quot.sound` | `#print axioms` | `axioms/` |
| statement of the solution = statement of the challenge; permitted axioms; replay in the Lean kernel (v4.35.0-rc3, see below) | Comparator (`lean/comparator_full.json`) | `full/` |
| a second kernel on an export of both theorems | lean4export + nanoda | `full/second-kernel/` |
| controls that must fail | Comparator with a changed statement and with an added axiom; nanoda on exports with one changed literal (an upstream literal, and a literal of this development's certificate data) | `full/`, `full/tamper-certificate-literal/` |
| the oleans of the trusted definitions correspond to the sources | `#print` comparison, olean reproduction, rebuild and byte-identical re-export; reproduction of the six oleans of the trusted closure from a fresh clone (2026-11-17) | `trusted-definitions/`, `rebuild-reexport/`, `route_check_2026-11-17.md` |

Summary of the recorded runs (details, dates and exit codes in
[`../verification/lean/riesz_range/record_2026-11-17.txt`](../verification/lean/riesz_range/record_2026-11-17.txt)):
- `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for `RieszN7.Full.riesz_seven_range`,
  `RieszN7.Full.riesz_seven_unique_range` and the two `Core12` theorems.
- nanoda: "Checked 159413 declarations with no errors" on the export of the two theorems
  (2 004 582 689 bytes, sha256 `e994407f…c3ba5a`); both tampered copies rejected by the type checker.
- Comparator, run 2 (2026-11-14 to 2026-11-15): "Lean default kernel accepts the solution", "Your solution is
  okay!", exit 0. Negative controls rejected. Run 1 was stopped by its own memory watchdog and is not counted.
- How Comparator ran: **without a sandbox** (Comparator's `fake-landrun` shim), and with a `lake` stand-in that compiles
  only the `RieszN7.Release.*` modules and takes every import as a prebuilt `.olean`. The link between the trusted
  definitions' oleans and their sources is therefore established separately (`trusted-definitions/`,
  `rebuild-reexport/`); the record explains the line "BASICFIX RESULT: FAIL basic" in `rebuild-reexport/basicfix.log`.
  Comparator was built with Lean v4.35.0-rc3, so its kernel replay is by that kernel, on an export written by
  lean4export built with v4.34.1; the v4.34.1 kernel checked every module at build time (`tools.txt`).
- For the sub-interval $`1/2 \le s \le 3/2`$ (`Core12`) nanoda and the negative controls ran, but no main Comparator
  run completed.

## Scope

- Nothing outside $`1/3 \le s \le 7/4`$ is treated here. Below $`1/3`$ the cap formulation used here is infeasible
  at $`s = 1/4`$ (float probe); above $`7/4`$ nothing was attempted.
- The pentagonal bipyramid is believed, from numerical studies, to minimise $`E_s`$ for seven points exactly for
  $`0 \le s \le 2`$ (Melnyk, Knop and Smith 1977; Nerattini, Brauchart and Kiessling,
  [arXiv:1307.2834](https://arxiv.org/abs/1307.2834)). This repository does not claim that statement. With
  `../lean/` (log energy, the $`s \to 0`$ case), `../coulomb/` ($`s = 1`$, a second check of H. Tran's theorem) and
  `../riesz2/` ($`s = 2`$), it treats the log energy, $`s = 2`$ and the interval $`1/3 \le s \le 7/4`$.
- The method is that of Kryvonos, Liehr and Taylor ([arXiv:2609.22077](https://arxiv.org/abs/2609.22077)) for
  $`N = 8`$, via H. Tran's $`N = 7`$ Coulomb formalisation and the $`N = 8`$ Lean development of Tooby-Smith and
  Zughaid. For eight points they treat the Riesz $`s`$-energy for all $`s \ge 0`$: in the article by a Lean-verified
  argument for all sufficiently large $`s`$, and in their companion repository by a computer-assisted argument that
  covers $`0 \le s \le 124`$ with finitely many closed intervals of $`s`$ and certificates valid uniformly in $`s`$
  (their Remark 7.2). The interval-in-$`s`$ treatment here follows that method.
- L. Shen ([arXiv:2611.09925](https://arxiv.org/abs/2611.09925)) gives an argument directed at the uniqueness
  statement for $`s = 1`$ alone, with exact rational certificates and not formalised; it was not checked here.
- The Lean development uses H. Tran's definitions and the generic machinery of this repository adapted from his code
  (ring rigidity, gauge, certificate soundness), so it is not independent of his work.

## Reproduce

**Python** (plain runs: Python 3.9.6, python-flint 0.6.0, macOS arm64, one core, an Apple M5; the `--recheck` run whose
reports are in this release: Linux, Python 3.12, python-flint 0.6.0, x86-64, one piece at a time):

```sh
sh riesz_range/fetch_bulk.sh                                     # certificates and reports (bulk archive): "BULK OK ..."
cd riesz_range/n7_interval
python3 range_check.py --range 1/3 7/4 --no-json                 # coverage + authentication: RANGE_OK (~6 s, about 1 GB)
python3 range_check.py --range 1/3 7/4 --route exact --no-json   # cap without the local lemma: RANGE_OK
python3 range_check.py --range 1/3 7/4 --recheck                 # re-runs all 267 used pieces (1 h 28 min on a Linux
                                                                 # workstation, 6.3 h on the Mac); rewrites the reports in place
```

`range_check.py` needs the files of the bulk archive (see [Bulk data](#bulk-data-separate-archive)); without them it
finds no piece reports. Without `--no-json` (or `--json-out FILE`) `range_check.py` rewrites `range_check.json`. The checkers import
`../hp/check_cert.py`, so keep `n7_interval/` and `hp/` side by side.

The two plain runs were repeated from a fresh `git clone` of this release after `fetch_bulk.sh` with a local copy of
the archive (both exit 0, RANGE_OK; 267 and 190 used pieces, all authenticated by sha256;
`../verification/riesz_range/fresh_clone_with_bulk.txt`). Earlier runs, before the bulk data were moved to the
archive: on the reports of this release, `../verification/riesz_range/range_check_after_recheck.txt`; on the reports
of 2026-11-07, `range_check_fresh_clone.txt` and `range_check_rc_run.txt` there. Those earlier runs also show nine
`NOT_OK ... stale` lines for the nine unused cap records that are not in this release (see
[Bulk data](#bulk-data-separate-archive)); they did not affect RANGE_OK. One thing in the output is expected:
- with `--no-json` no previous inventory is read, so the line "recheck status" reports 0 of the used pieces as re-run,
  and the two notes "unchanged since the previous run" are absent. To see the recorded status (267 of the 267 used
  pieces re-run by `--recheck`), pass `--json-out` a scratch copy of `ext/range_check_ext.json` (the file is
  overwritten).

`--recheck`: run it in a copy of the directory. It copies the original reports to `pre_recheck/<time>/` and rewrites
them with new provenance and times, and it creates the lock file `.mac_heavy.lock`; afterwards `MANIFEST.sha256` and
`git status` no longer match for the rewritten reports. Every piece runs through `heavy_lock.py`, which waits while
the 1-minute load average is 10 or more and calls the macOS command `taskpolicy` (on other systems put a stand-in on
`PATH` that drops its options and runs the rest of the command, as the Linux run did, rather than editing
`heavy_lock.py`). The checkers are started as `python3` from `PATH`, which must be the
interpreter that has python-flint. The `--route exact` and `--recheck` outputs in `n7_interval/` are those of the runs
of 2026-11-07, on the reports that the run of 2026-11-17 below replaced.

The `--recheck` was repeated on 2026-11-17 on a Linux workstation (Linux, Python 3.12, python-flint 0.6.0), from a
copy of `n7_interval/` and `hp/` in a directory whose path names no user, with `--json-out ext/range_check_ext.json`:
exit 0, `RANGE_OK [1/3, 7/4] route=local`, 267 of 267 used pieces re-run, 267 OK, 0 verdict changes, all 267
authenticated by sha256 afterwards; 5 274 s wall; peak memory 1.05 GiB for `range_check.py` and the running checker
together (0.78 GiB for the largest single process). The 41 report files of the 267 used pieces and
`ext/range_check_ext.json` in this release are the files this run wrote, unedited
(`../verification/riesz_range/range_recheck_2026-11-17.txt`: setup, the `taskpolicy` stand-in, and the full output).
Their cap reports differ from those of 2026-11-07 only in floating-point diagnostic fields computed outside the exact
and ball-arithmetic checks (relative difference at most 1.2e-6); no exact field and no verdict changed.

**Lean** (Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; pins and binary hashes of the lean,
lean4export, nanoda and Comparator builds: [`../verification/lean/riesz_range/tools.txt`](../verification/lean/riesz_range/tools.txt)).
The route below was tested from a fresh clone on 2026-11-17 for the trusted closure only (ThomsonGen.Preamble,
ThomsonGen.Base, RieszN7.Core.Rpow, RieszN7.Basic and the two Challenge files;
[`../verification/lean/riesz_range/route_check_2026-11-17.md`](../verification/lean/riesz_range/route_check_2026-11-17.md)).
The full library build was not repeated. What follows are the steps and the commands as they apply to a Lake
workspace, and what the recorded runs did.

```sh
cd riesz_range/lean
./regen.sh                 # fetches huwngtran/thomson-n7-lean @ 25f2fa5 and regenerates the upstream ThomsonGen modules
shasum -a 256 -c SHA256SUMS upstream_regenerated.sha256   # or: sha256sum -c SHA256SUMS upstream_regenerated.sha256
lake exe cache get         # Mathlib oleans for the pinned revision
lake build ThomsonGen.Preamble ThomsonGen.Base RieszN7.Core.Rpow RieszN7.Basic RieszN7.Release.FullChallenge RieszN7.Release.Core12Challenge
```

In the route check, Lake reproduced the checked `ThomsonGen.Preamble` and `ThomsonGen.Base` oleans byte for byte. Its
four `RieszN7` oleans have other bytes (Lake's own compile recipe, with default elaboration options), and the `#print`
of the trusted definitions against them is identical to that against the checked oleans. The recipe that built the
checked `RieszN7` oleans reproduces them byte for byte (all four, `RieszN7.Basic` included). It is run in
`riesz_range/lean` after the Lake step above (which built the `ThomsonGen` oleans and fetched Mathlib), with relative
source paths and outputs under `.lake/build/lib/lean` (absolute paths, as in the route check):

```sh
LP=$PWD/.lake/build/lib/lean; for p in $PWD/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
for M in RieszN7/Core/Rpow RieszN7/Basic RieszN7/Release/FullChallenge RieszN7/Release/Core12Challenge; do
  LEAN_PATH=$LP LEAN_NUM_THREADS=1 <elan>/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -DElab.async=false \
    -o $PWD/.lake/build/lib/lean/$M.olean -i $PWD/.lake/build/lib/lean/$M.ilean $M.lean
done
```

(`<elan>` is the elan directory, usually `~/.elan`.) Not tested: whether a later `lake build` keeps or rebuilds the
oleans this overwrites, and calling `lean` through the elan proxy rather than the toolchain binary (the same binary).
Costs in the route check: `lake exe cache get` cloned 9 repositories from GitHub, compiled the cache tool and
downloaded 8 908 files (18 min wall there; network-dependent). Each module of the closure that imports
`ThomsonGen.Preamble` (`import Mathlib`) peaks at about 6.8 GB. `.lake` needs about 7.2 GB (apparent size).

`regen.sh` writes the whole upstream Coulomb development, split into modules; it checks the 20 modules of
`ThomsonGen/scripts/generated.sha256`, and the 18 of them used here are those of `upstream_regenerated.sha256`. The
lakefile's default target is `RieszN7`; its `ThomsonGen` library takes every regenerated module, so `lake build
ThomsonGen` would compile the whole upstream development.

The recorded build did not use Lake for the `RieszN7` modules. It compiled each `RieszN7` module of `build_order.txt`
separately, in that order, with `LEAN_NUM_THREADS=1 lean -j1 -DElab.async=false -o <M>.olean -i <M>.ilean <M>.lean`
and a `LEAN_PATH` containing the build output, the `ThomsonGen` / `LogLean` oleans and Mathlib
(`../verification/lean/riesz_range/scripts_as_run/build_range.sh`, a record that does not run outside the recorded
machine). The 23 `ThomsonGen` / `LogLean` modules of `build_order.txt` were built by Lake in the dependency workspace.
`lakefile.toml` describes the same libraries for `lake build`; tested for the trusted closure (2026-11-17), not for
the full library. Memory: single module builds
peak at up to 8.0 GB, and 1 459 of the 5 072 recorded module builds peak above 6 GB (`build/build.tsv`), so a parallel
build needs about 8 GB per job.

In a built workspace, with `lean4export`, `nanoda_bin` and `comparator` on `PATH`, the checks are (the recorded runs
set `LEAN_PATH` themselves; `lake env` does the same in a Lake workspace):

```sh
lake env lean RieszN7/Check/AxiomsFull.lean    # #print axioms of RieszN7.Full.riesz_seven_range / _unique_range
lake env lean4export RieszN7.Release.FullSolution -- ThomsonN7Riesz.riesz_seven_range ThomsonN7Riesz.riesz_seven_unique_range > riesz_seven_range.ndjson
nanoda_bin config.json                         # config.json: see below
COMPARATOR_LEAN4EXPORT=<path of lean4export> COMPARATOR_LANDRUN=<path of landrun> comparator comparator_full.json
```

- `config.json` for nanoda: copy `../verification/lean/riesz_range/full/second-kernel/config.json` and set
  `export_file_path` to the path of `riesz_seven_range.ndjson` (the recorded file has a placeholder there).
- Comparator: the recorded invocation was the line above, with `COMPARATOR_LANDRUN` set to Comparator's non-sandboxing
  shim `scripts/fake-landrun.sh` and the `lake` stand-in `../verification/lean/riesz_range/scripts_as_run/shim/lake`
  first on `PATH` (`scripts_as_run/full_release.sh`, phase `comparator`). With a real landrun and the real `lake`,
  Comparator builds the two Release modules with `lake build`, which has not been tested.
- The tools, at the pins of `tools.txt` (steps recorded there; the binary sha256 to compare with are in `tools.txt`
  and `full/full_release.log`; the binary paths are those of `scripts_as_run/env_core.sh`; these steps were not
  repeated for this release):

```sh
git clone https://github.com/leanprover/lean4export && cd lean4export
git checkout 076e8e57707e813375e8f9da8bf989799ace9680
echo leanprover/lean4:v4.34.1 > lean-toolchain     # the pinned file says v4.34.0; the recorded build used v4.34.1
lake build                                         # .lake/build/bin/lean4export
cd .. && git clone https://github.com/ammkrn/nanoda_lib.git && cd nanoda_lib
git checkout 3a2407216ee84a75f9e1aead6803d0578be06ae7
cargo build --release                              # target/release/nanoda_bin (recorded: rustc and cargo 1.98.1)
cd .. && git clone https://github.com/leanprover/comparator && cd comparator
git checkout fd5d5bcf14177b187f66d4502071268d877887c3
lake build                                         # its own toolchain v4.35.0-rc3; .lake/build/bin/comparator
```

Measured costs (Linux x86_64, 6 cores, 19 GB RAM, CPU model not recorded; every step under nice 19 on a machine shared
with other jobs, so the walls are not those of an idle machine):

| step | wall | peak memory |
|---|---|---|
| build, 5 080 `RieszN7` modules, one at a time | about 42 h: the sum of the per-module wall times of the latest `build/build.tsv` lines, not a wall time; 1 789 of the module builds (1 787 distinct modules) ran on two other machines (`build/build_remote.tsv`) | 8.0 GB (`RieszN7.MainFull`) |
| `#print axioms` (AxiomsFull) | 12 s | 8.0 GB |
| lean4export of the two theorems | 4 h 42 min | 10.5 GB |
| nanoda, 3 threads | 6 h 45 min | 8.6 GB |
| nanoda on a tampered copy, 1 thread | 451 s (upstream literal); 18.4 h (certificate literal) | |
| Comparator, main run | 42 h 08 min | 10.4 GB (12.5 GB for the whole process session) |

Disk: `riesz_range/lean/` takes about 443 MiB and `riesz_range/n7_interval/` about 1.3 MiB in a checkout (before
`regen.sh`), and 270 MiB after `fetch_bulk.sh`, which also writes `cap_rr/` (163 MiB); the export is 2.0 GB, and a tamper control needs a second copy of it; the size of the built `.lake/build`
tree was not recorded.

## Files

| path | content |
|---|---|
| `fetch_bulk.sh`, `BULK_SHA256SUMS`, `.gitignore` | fetches and verifies the bulk archive; sha256 of its 286 files; the unpacked paths, ignored by git |
| `n7_interval/range_check.py` | coverage checker; `range_check.json` and `ext/range_check_ext.json`: recorded inventories |
| `n7_interval/RANGE_*OUTPUT*.txt` | recorded outputs (plain runs and `--recheck` runs) |
| `n7_interval/cellsS/` | Case 1 and slab checkers (`check_piece.py`, `check_bern.py`, `check_cell.py`, `check_minorant_cell.py`), node certificates (`certs_lin/`, `certs_pt/`, `certs_bern/`, `certs_range/`) and reports (`range_pieces.jsonl`, `results.jsonl`, `logs/`), both in the bulk archive; tables |
| `n7_interval/capR/`, `n7_interval/capS/`, `n7_interval/cap1/` | cap checker `check_capR.py`, its node certificates (`capS/`, `capR/cert_dirs_D12.json`, `cap1/`) and reports (`pieces/`, `pieces_nsub/`), certificates and reports in the bulk archive |
| `n7_interval/localS/` | local lemma checker; its two cover files are in the bulk archive |
| `cap_rr/` (bulk archive only) | the re-rounded cap certificates of the Lean cap modules and their Python checks |
| `n7_interval/ext/` | extension from $`[1/2, 3/2]`$ to $`[1/3, 7/4]`$: inventories, cell cover, one fix-up check |
| `hp/check_cert.py` | exact certificate routines imported by the checkers (development version; differs from `../checkers/check_cert.py`) |
| `lean/RieszN7/` | the 5 080 modules of the import closure of the release, main and axiom-check modules |
| `lean/ThomsonGen/`, `lean/LogLean/` | stored supporting modules and the regeneration scripts |
| `lean/comparator_*.json` | Comparator configurations (main runs and negative controls) |
| `lean/SHA256SUMS`, `lean/upstream_regenerated.sha256`, `lean/build_order.txt` | hashes of the stored and regenerated modules; a build order |
| `../verification/lean/riesz_range/` | the Lean records (logs, configurations, scripts as run; private paths replaced by placeholders). The scripts in `scripts_as_run/` are records of what ran: they use placeholders and helpers that are not included and do not run outside the recorded machine |
| `../verification/riesz_range/` | `RC_EXACTNESS.txt` (comparison with the checked originals, replacements, files left unedited), `range_recheck_2026-11-17.txt` (the `--recheck` run whose reports are in this release), `range_check_after_recheck.txt` (plain runs on these reports), `range_check_rc_run.txt`, `range_check_fresh_clone.txt` (plain runs on the reports of 2026-11-07), `fresh_clone_with_bulk.txt` (fresh clone, `fetch_bulk.sh`, plain runs, checksums) |

Internal documents: `n7_interval/RANGE_ASSEMBLY.md` (the assembly of the Python argument, 2026-11-07),
`cellsS/NOTES.md`, `capR/DESIGN.md`, `capR/REMAINDER.md` and `localS/NOTES.md` are working documents of the
development, reproduced with the text replacements listed in `RC_EXACTNESS.txt`. They refer to files that are not
included and use their own working vocabulary; the RANGE_ASSEMBLY.md row G9 ("nothing of the range is formalised")
predates `lean/`. The Lean and Python sources are byte-identical to the checked ones, including comments that call
them "Private" or "not reviewed" and comments that name internal planning files; those words describe the
development state and are not edited, so that the hashes stay those of the checked files. The full list of such
strings (a machine name, absolute paths, internal file names, development-state words) is in
`../verification/riesz_range/RC_EXACTNESS.txt`, section 5.

The reports of the 267 used pieces record, in their `provenance` fields, the paths of the directory of the
2026-11-17 `--recheck` run (`/mnt/ssd/thomson/rel/thomson-n7-log/riesz_range/...`), the interpreter `/usr/bin/python3`
and the working directory; no user name. `range_check.py` does not use the recorded paths. The published v2.7 already contains one such path
(`../coulomb/lean/gen/case1_cert3_summary.json`).

## Reviews

AI reviews (Claude Fable 5.1, read-only), not peer review: of the Python assembly for $`[1/2, 3/2]`$, of its
extension to $`[1/3, 7/4]`$, and of the Lean port. The errors they found and the fixes are listed in
`../AI_DISCLOSURE.md`. Four further read-only AI reviews of this release (two by Claude Fable 5.2, one by Claude
Opus 5.5, one by gpt-6-astra) covered statement fidelity, the trusted base, reproducibility and wording; documentation
corrections from them are in this version. No human has checked this directory.

## References

- L. Kryvonos, L. Liehr, M. A. Taylor, *Energy minimization for eight points on the sphere*, [arXiv:2609.22077](https://arxiv.org/abs/2609.22077).
- H. Tran, Lean formalisation of the seven-electron Thomson problem, [huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) (2026).
- J. Tooby-Smith, A. Zughaid, [Thomson-N-8-Warrant](https://github.com/jstoobysmith/Thomson-N-8-Warrant).
- T. W. Melnyk, O. Knop, W. R. Smith, *Extremal arrangements of points and unit charges on a sphere: equilibrium configurations revisited*, Can. J. Chem. 55 (1977), doi:10.1139/v77-246.
- R. Nerattini, J. S. Brauchart, M. K.-H. Kiessling, *"Magic" numbers in Smale's 7th problem*, [arXiv:1307.2834](https://arxiv.org/abs/1307.2834).
- L. Shen, *On the seven-particle clusters of Lennard-Jones and Thomson*, [arXiv:2611.09925](https://arxiv.org/abs/2611.09925).
- D. Armentano et al., J. Symbolic Comput. 137 (2026), 102570 (the log case, `../README.md`).
