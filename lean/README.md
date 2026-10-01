# Logarithmic energy, $`N = 7`$: Lean formalisation

Status: Lean 4 formalisation, checked by the Lean kernel (see Build test); not peer reviewed.

A readable overview of how the formal proof fits together, and what is new relative to the Coulomb formalisation:
[`OVERVIEW.md`](OVERVIEW.md).

`LogN7/Challenge.lean` states two theorems with `sorry`, and `LogN7/Solution.lean` proves the same two statements over the same definitions:

```lean
-- SphereConfig 7 = {x : Fin 7 → ℝ³ | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}
-- logEnergy x = ∑ i, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

theorem thomson_seven_log :
    ∀ x ∈ SphereConfig 7, logEnergy pentBipyramid ≤ logEnergy x

theorem thomson_seven_log_unique :
    ∀ x ∈ SphereConfig 7, logEnergy x = logEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i))
```

In words: among configurations of seven pairwise distinct points on $`S^2`$, the pentagonal bipyramid $`P`$ minimises
$`E`$. Every minimiser equals $`P`$ up to an orthogonal map of $`\mathbb{R}^3`$ and a relabelling. Injectivity in
`SphereConfig` excludes coincident points, where Lean's convention `Real.log 0 = 0` would apply. The definitions `R3`,
`SphereConfig`, `cyl` and `pentBipyramid` are those of the Coulomb formalisation (below).

`LogN7/Check/Axioms.lean` prints the axioms of both theorems: `[propext, Classical.choice, Quot.sound]`. The files
contain no `sorry` (apart from the two in `Challenge.lean`) and no `native_decide`. Every certificate check is a
`Bool` computation closed by `decide +kernel`.

## Structure

The formal proof follows the case split of `../README.md`:
- Case 1;
- the five slabs;
- the cap $`t_{01} \in [-1, -99/100]`$, which contains $`P`$. Here the certificate bound lies below $`E(P)`$, and
  the cap is treated with coercivity, ring rigidity and the quartic local lemma.

| module | content |
|---|---|
| `LogN7/Basic.lean`, `LogN7/Bridge.lean` | `logEnergy` as a sum of $`\varphi_0(t) = -\tfrac12\log(2-2t)`$ over inner products; value at $`P`$ |
| `LogN7/Minor/` | minorants $`H \le \varphi_0`$ of each cell, with exact piecewise checks |
| `LogN7/Case1/` | Case 1 (all $`t_{ij} \ge -9/10`$), from `../certificates/cells/cert_case1_log_D10.json` |
| `LogN7/S9998/` … `LogN7/S9390/` | the five slabs, from `../certificates/cells/cert_slab_*_log_*.json` |
| `LogN7/Cap/` | the cap, from `../certificates/cert_cap_log_D12_short.json` (facially reduced blocks, one module per block) |
| `LogLean/LogSeries.lean`, `LogLean/MinorCore.lean` | rational bounds for `Real.log` and the minorant calculus |
| `LogLean/Local*.lean` | the quartic local lemma near $`P`$ (`../local/LOCAL_LEMMA.md`, form L′; the Lean statement `LocalMain.Lprime` has the constants $`0.0268\,\lVert w\rVert^2 + 0.0200\,\lVert s\rVert^4`$, weaker than the Python-certified 0.0342, 0.0227) on the gauge-fixed ball, and its hand-off (`LocalHandoff.lean`): $`E(z) \ge E(P)`$ for every $`z`$ within sup distance $`1/300`$ of $`P`$, with equality only for $`z = g P`$ |
| `LogN7/Main.lean` | assembly: case split, coercivity on the cap, local lemma, minimality and uniqueness |
| `LogN7/Challenge.lean`, `LogN7/Solution.lean`, `LogN7/Check/Axioms.lean` | statement, solution, axiom check |
| `ThomsonGen/Cert/NBlk.lean`, `ThomsonGen/Cert/NBlkCap.lean`, `ThomsonGen/Cert/Split.lean` | facially reduced PSD blocks $`N B' N^\top`$ (positivity by congruence); the cap specification from such a certificate; per-block splitting of large kernel checks |
| `ThomsonGen/Generic/{Energy,Glue}.lean` | versions of the upstream glue lemmas that are generic in the kernel $`\varphi`$ |
| `ThomsonGen/*` (other modules) | regenerated from the upstream Coulomb formalisation by `regen.sh`, not stored here (see below) |

The certificate data in `LogN7/*/Data*.lean` was emitted from the certificates in `../certificates/` by the scripts in
`gen_log/` (minorants, local-lemma data and the cap pieces: `gen/`; see `gen/README.md`). The sha256 of
the source file is recorded in each header. `../certificates/cert_cap_log_D12_short.json` is the cap certificate
re-rounded to shorter rationals (at most 121 bits) for the kernel checks. Its bound is the same as that of
`cert_cap_log_D12.json` ($`e - E(P) = -7.294 \cdot 10^{-17}`$), and it passes the same checkers
(`../verification/check_cert_short.txt`, `../verification/check_minorant_short.txt`).

## Upstream code

Part of this package comes from the Lean formalisation of the Coulomb case,
[huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) at commit `25f2fa5`, file
`formal/lean/ThomsonN7/Solution.lean`. That repository has no licence file. Its declarations are used here in two
ways:
- unchanged declarations are regenerated from the pinned upstream file and are not stored in this repository;
- adapted declarations are stored, and each one names the upstream declaration it adapts.

Below, upstream names are relative to the namespace `ThomsonN7`.

### Regenerated (not stored)

`regen.sh` clones the upstream repository at the pinned commit, checks the sha256 of `Solution.lean`, and runs
`ThomsonGen/scripts/split.py`. The script writes the following modules, which are gitignored:

* `ThomsonGen/{Preamble,Base,ThreePoint,Kron,Cert1,Cert3,M2,M3,RegB,TwoRegime,Case1Stat,Typed,T4,GV,Gauge,CertF,CertT}.lean`.
  - These are upstream `Solution.lean` split at fixed points. Declarations not reachable from the upstream main
    theorems or from `ThomsonGen/scripts/gen_roots.txt` are left out.
  - They contain the statement definitions (`R3`, `SphereConfig`, `cyl`, `pentBipyramid`, in `Preamble`, which
    `LogN7/Challenge.lean` imports) and the certificate-checking machinery: the typed three-point identity, packed
    SOS blocks, ring rigidity, the gauge (Procrustes) lemma and the chart lemma.
  - `split.py` writes further modules that this build does not use.
* `ThomsonGen/Verbatim/Generic.lean`: `Glue.exists_perm_of_ne`, copied unchanged into the namespace `ThomsonGen`.
* `ThomsonGen/Verbatim/LogMinor.lean`: copied unchanged into the namespace `LogLean.Minor`, for use by
  `LogLean/MinorCore.lean`. It contains:
  - `CutOneD.peval`, `padd`, `pscale`, `pneg`, `pmul`, `peval_padd`, `peval_pscale`, `peval_pneg`, `peval_pmul` and
    `peval_eq_zero_of_all`;
  - `Glue.Coerce.ppow`, `peval_ppow`, `bernSum`, `bernSum_nonneg`, `BPiece`, `BPiece.diff`, `BPiece.check` and
    `BPiece.nonneg`.
* `ThomsonGen/Verbatim/LogLocal.lean`: `Cert.qform_dd_nonneg`, `Cert.Blk.list_sum_range_map`, `Reg.sqrt5_lo` and
  `Reg.sqrt5_hi`, copied unchanged into the namespace `LocalKel`, for use by `LogLean/LocalKel.lean`.

The lists for the `Verbatim` modules are in `ThomsonGen/scripts/verbatim/*.txt`. `regen.sh` checks all 20 modules
against `ThomsonGen/scripts/generated.sha256` and stops with an error on any mismatch.

### Adapted (stored, with attribution)

The following declarations are adapted from upstream: made generic in the kernel $`\varphi`$, specialised to the
logarithmic kernel, renamed, or given changed proofs. Each file names the upstream declaration that each one
adapts, in its header or in an attribution comment after its imports.

| file | declarations (upstream source) |
|---|---|
| `ThomsonGen/Generic/Glue.lean` | lemmas and definitions from `Glue.*` (e.g. `cls3`, `TubeRigid`, `exists_cell`, `typed7_cls3`, `tcert_bound`, `seven_of_specs`), `Case1.seven_of_case2`, `Case1.case1_margin` and `TwoRegime.margin_of_threePoint_cut` |
| `ThomsonGen/Generic/Energy.lean` | `pairEnergy` and its invariance lemmas (from `coulombEnergy`, `Base.*`); `Concl` (`Glue.Concl`); `LocalGram`, `LocalGramA`, `localMinAt_of_sq`, `localGram_of_localMinAt`, `localGramA_of_localGram`, `local_of_windowA` (`TwoRegime.*`) |
| `ThomsonGen/Cert/NBlk.lean` | `padd`, `pscale` (`SlabOneD.*`); `fmat_psd_expand` (`Cert.fmat_psd`); `tsum_nonneg_N` (`Cert.tsum_nonneg`); `alpha_nonneg'`, `beta_nonneg'`, `gamma_nonneg'` (`Cert.TCert.*`) |
| `ThomsonGen/Cert/NBlkCap.lean` | `capSpec_of_tcertN` (`Glue.capSpec_of_tcert`) |
| `LogN7/Challenge.lean`, `LogN7/Solution.lean` | `logEnergy` (`coulombEnergy`); the two statements follow `thomson_seven`, `thomson_seven_unique` |
| `LogN7/Basic.lean` | `logEnergy` (`coulombEnergy`); `sum_Ioi_seven` (`Reg.sum_Ioi_seven`) |
| `LogN7/Bridge.lean` | `peval_eq_sum` (`CutOneD.peval_eq_sum`) |
| `LogN7/Case1/Check.lean` | `r2c1_S`, `r2c1_cf_chk` and three comments (`Case1.*`) |
| `LogLean/MinorCore.lean` | `peval_nonneg_of_all` (`CutOneD.peval_eq_zero_of_all`) |
| `LogLean/LocalBridge.lean` | `cyl`, `pentBipyramid` restated (`cyl`, `pentBipyramid`) |
| `LogLean/LocalCert.lean`, `LogLean/LocalGamma1.lean` | the block-sum step of `M_psd` (`ThreePoint.dsum_pair12`) |

### Checking for upstream text

`ThomsonGen/scripts/scan_upstream.py` compares every stored `.lean` file with all of upstream `Solution.lean`,
declaration by declaration and including docstrings and comments, after normalising whitespace. Run it after
`regen.sh`:

```sh
python3 ThomsonGen/scripts/scan_upstream.py     # prints PASS or FAIL
```

The scan fails in two cases:

* a stored declaration is identical to an upstream one;
* a declaration has similarity ≥ 0.8 to an upstream one, contains 3 or more identical consecutive code lines, or
  shares comment text with upstream, and its file does not cite the upstream source.

Declarations that consist of one code line of at most 100 characters are exempt and listed. Examples are the
emitted `theorem … : … = true := by decide +kernel` checks and short data definitions. The upstream statement
definitions are never exempt.

## Build

Requirements: [elan](https://github.com/leanprover/elan), git, python3 and `shasum` or `sha256sum` (for `regen.sh`);
cargo for `scripts/second-kernel.sh`. The toolchain (`leanprover/lean4:v4.34.1`) and the Mathlib
revision are pinned in `lean-toolchain` and `lakefile.toml`.

```sh
./regen.sh                  # fetch upstream, regenerate ThomsonGen/*, check hashes: "regen OK"
lake exe cache get          # Mathlib build cache
lake build                  # builds LogN7.Challenge, LogN7.Solution and LogN7.Check.Axioms
```

`lake build` may compile several modules in parallel, and most modules need 6–9.5 GB of RAM each (table below). On a
machine with less than about 32 GB, compile one module at a time in dependency order with
`lake env lean -o <olean> -i <ilean> <file>`, as in the build test below.

## Build test

Each build ran in a fresh directory on Linux x86_64. It ran `regen.sh` and fetched a fresh Mathlib cache, then
compiled every module of the import closure of `LogN7.Solution`, `LogN7.Check.Axioms` and `LogN7.Challenge`
one at a time, in dependency order, with `lake env lean -j1 -DElab.async=false`.

* **2026-10-01:** the version before the changes described in [Upstream code](#upstream-code). In that version,
  22 upstream lemmas were still stored in `LogLean/MinorCore.lean` and `LogLean/LocalKel.lean`, and `Challenge.lean`
  restated the four statement definitions.
  - 154 modules, all exit code 0; 6.7 h of compile time in total.
  - Largest peak memory: 9.8 GB, in the regenerated `ThomsonGen/T4.lean`.
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]` for both theorems.
  - Per-module record: `../verification/lean/build_2026-10-01_pre_scrub.tsv`.
* **This version (157 modules):** the clean build is in progress. Its record will be added to
  `../verification/lean/`.
