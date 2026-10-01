# Riesz $`s = 2`$, $`N = 7`$: Lean formalisation

Status: **Lean 4 formalisation checked by the Lean kernel, not peer reviewed; produced by AI models** (see
[`../../AI_DISCLOSURE.md`](../../AI_DISCLOSURE.md)). Like the rest of this repository, this is an AI-produced warrant, not a
digested proof: we do not regard the statement as settled by it, and a human-readable treatment is welcome (see the
note at the top of [`../../README.md`](../../README.md)).

`Riesz2/Main.lean` states and the Lean kernel checks:

```lean
-- SphereConfig 7 = {x : Fin 7 → ℝ³ | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}
-- riesz2Energy x = ∑ i, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖ ^ 2)⁻¹

theorem riesz2_seven :
    ∀ x ∈ SphereConfig 7, riesz2Energy pentBipyramid ≤ riesz2Energy x

theorem riesz2_seven_unique :
    ∀ x ∈ SphereConfig 7, riesz2Energy x = riesz2Energy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i))
```

This means that among configurations of seven pairwise distinct points on $`S^2`$, the pentagonal bipyramid minimises
$`E_2`$ ($`E_2(P) = 41/4`$). Every minimiser equals it up to an orthogonal map of $`\mathbb{R}^3`$ and a relabelling.

`Riesz2/Check/Axioms.lean` prints the axioms of both theorems:
`[propext, Classical.choice, Quot.sound]`. There is no `sorry` and no `native_decide`. Every certificate check is a
`Bool` computation closed by `decide +kernel`.

## Structure

The formalisation follows the case split of `../README.md`: Case 1, a cap and five slabs.

| module | content |
|---|---|
| `Riesz2/Basic.lean`, `Riesz2/Minor*.lean` | energy, kernel $`\varphi_2`$, minorants and their exact checks |
| `Riesz2/Case1/` | Case 1 (all $`t_{ij} \ge -9/10`$), from the degree-10 certificate |
| `Riesz2/Cap/` | cap $`t_{01} \in [-1, -99/100]`$, from the degree-12 dyadic certificate `../cert_cap_riesz2_D12_dyadic.json` (facially reduced blocks) |
| `Riesz2/S9998/` … `Riesz2/S9390/` | the five slabs |
| `Riesz2/Sharp.lean`, `Riesz2/Final.lean` | sharp cap (exact contact) to minimality and uniqueness |
| `Riesz2/Main.lean`, `Riesz2/Check/Axioms.lean` | main theorems, axiom check |
| `ThomsonGen/Cert/NBlk.lean` | facially reduced PSD blocks $`N B' N^\top`$: positivity by congruence |
| `ThomsonGen/Generic/{Energy,Glue}.lean` | versions of the upstream glue lemmas that are generic in the kernel |
| `ThomsonGen/*` (other modules) | regenerated from the upstream Coulomb formalisation by `regen.sh`, not stored here |

The certificate data in `Riesz2/*/Data*.lean` was emitted from the certificates in `../`.

## Upstream code

Part of this package comes from the Lean formalisation of the Coulomb case,
[huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) at commit `25f2fa5`, file
`formal/lean/ThomsonN7/Solution.lean`. That repository has no licence file. Its declarations are used here in two
ways: unchanged declarations are regenerated from the pinned upstream file and are not stored in this repository;
adapted declarations are stored, and each one names the upstream declaration it adapts. Below, upstream names are
relative to the namespace `ThomsonN7`.

### Regenerated (not stored)

`regen.sh` clones the upstream repository at the pinned commit, checks the sha256 of `Solution.lean`, and runs
`ThomsonGen/scripts/split.py`. The script writes the following modules, which are gitignored:

* `ThomsonGen/{Preamble,Base,ThreePoint,Kron,Cert1,Cert3,M2,M3,RegB,TwoRegime,Case1Stat,Typed,T4,GV,CertF,CertT}.lean`:
  upstream `Solution.lean` split at fixed points, without the declarations that are not reachable from the upstream
  main theorems or from `ThomsonGen/scripts/gen_roots.txt`. These modules contain the statement definitions
  (`R3`, `SphereConfig`, `cyl`, `pentBipyramid`, in `Preamble`) and the certificate-checking machinery: the typed
  three-point identity, packed SOS blocks, ring rigidity and the chart lemma. `split.py` writes further modules
  that this build does not use.
* `ThomsonGen/Verbatim/Generic.lean`: `Glue.exists_perm_of_ne`, copied unchanged into the namespace `ThomsonGen`.
  `ThomsonGen/Generic/Glue.lean` uses it.
* `ThomsonGen/Verbatim/MinorPoly.lean`: `CutOneD.peval`, `CutOneD.padd`, `CutOneD.pscale`, `CutOneD.pneg`,
  `CutOneD.pmul`, `Glue.Coerce.ppow`, `CutOneD.peval_padd`, `CutOneD.peval_pscale`, `CutOneD.peval_pneg`,
  `CutOneD.peval_pmul`, `Glue.Coerce.peval_ppow` and `CutOneD.peval_eq_zero_of_all`, copied unchanged into the
  namespace `Riesz2.Minor`. `Riesz2/MinorCore.lean` uses them.

The lists for the two `Verbatim` modules are in `ThomsonGen/scripts/verbatim/*.txt`. `regen.sh` checks all 18
modules against `ThomsonGen/scripts/generated.sha256` and stops with an error on any mismatch.

### Adapted (stored, with attribution)

The following declarations are adapted from upstream. They are made generic in the kernel $`\varphi`$, specialised
to $`s = 2`$, renamed, or given changed proofs. The header of each file lists them with the upstream declaration
each one adapts.

| file | declarations (upstream source) |
|---|---|
| `ThomsonGen/Generic/Glue.lean` | 29 lemmas and definitions, from `Glue.*` (e.g. `cls3`, `TubeRigid`, `exists_cell`, `typed7_cls3`, `tcert_bound`, `seven_of_specs`), `Case1.seven_of_case2`, `Case1.case1_margin` and `TwoRegime.margin_of_threePoint_cut` |
| `ThomsonGen/Generic/Energy.lean` | `pairEnergy`, `pairEnergy_comp_isometry`, `pairEnergy_comp_perm` (from `coulombEnergy`, `Base.*`); `Concl` (`Glue.Concl`); `LocalGram`, `LocalGramA`, `localMinAt_of_sq`, `localGram_of_localMinAt`, `localGramA_of_localGram`, `local_of_windowA` (`TwoRegime.*`) |
| `ThomsonGen/Cert/NBlk.lean` | `padd`, `pscale` (`SlabOneD.*`); `length_unpackM` (`Cert.rowsN_length`); `fmat_psd_expand` (`Cert.fmat_psd`); `tsum_nonneg_N` (`Cert.tsum_nonneg`); `alpha_nonneg'`, `beta_nonneg'`, `gamma_nonneg'` (`Cert.TCert.*`) |
| `Riesz2/Basic.lean` | `riesz2Energy` (`coulombEnergy`); `norm_sub_sq_inv_eq_phi2`, `riesz2Energy_eq_sum_phi2` (`Base.*`); `sum_Ioi_seven` (`Reg.sum_Ioi_seven`) |
| `Riesz2/MinorCore.lean` | `peval_nonneg_of_all` (`CutOneD.peval_eq_zero_of_all`) |
| `Riesz2/Bridge.lean` | `peval_eq_sum` (`CutOneD.peval_eq_sum`) |
| `Riesz2/Case1/Check.lean` | `r2c1_S`, `r2c1_idE_stat`, `r2c1_cf_chk`, `r2c1_cf_blocks`, `r2c1_cf_sos` (`Case1.*`) |
| `Riesz2/Final.lean` | the list of breakpoints in the header (docstring of `Final.capspec_cap`) |
| `Riesz2/Main.lean` | `riesz2_seven`, `riesz2_seven_unique` (`thomson_seven`, `thomson_seven_unique`) |

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
emitted `theorem tc_cap_A : tc_cap.chkA = true := by decide +kernel`, records such as `def S0 : SBlk := ⟨…⟩` and
`hK`. The upstream statement definitions are never exempt.

## Build

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.34.1`) and Mathlib
revision are pinned in `lean-toolchain` and `lakefile.toml`.

```sh
./regen.sh                  # fetch upstream, regenerate ThomsonGen/*, check hashes: "regen OK"
lake exe cache get          # Mathlib build cache
lake build                  # builds Riesz2.Main and Riesz2.Check.Axioms
```

`lake build` may compile several modules in parallel. Many modules need 6–10 GB of RAM each, and the largest needs
15.5 GB (table below), so at least 16 GB is required, and more is safer. On a machine with less than about 32 GB, compile one module at a
time in dependency order with
`lake env lean -o <olean> -i <ilean> <file>`, as in the build test below.

## Build test

The build was tested on Linux x86_64 from a clean clone of this directory:

1. `regen.sh`;
2. a fresh Mathlib download with `lake exe cache get`;
3. every one of the 109 modules compiled in dependency order with `lake env lean -j1 -DElab.async=false`, one at a
   time.

All 109 modules compiled, and the axiom check printed the axioms stated above. Machine: Linux x86_64, one thread per
module, at low priority on a shared machine. Wall times are indicative only.

| modules | count | total wall time | peak RSS (largest module) |
|---|---|---|---|
| `ThomsonGen/*` (including the regenerated `Verbatim/*`) | 21 | 24 min | 9.5 GB |
| `Riesz2/Cap/*` (cap, 25 SOS blocks checked separately) | 34 | 3.3 h | 8.0 GB |
| `Riesz2/S*/*` (five slabs) | 33 | 37 min | 15.5 GB (`S9390/ChkMeta`; the others ≤ 10.3 GB) |
| `Riesz2/Case1/*` | 7 | 7 min | 9.3 GB |
| other `Riesz2/*` | 14 | 4 min | 6.4 GB |
| total | 109 | 4.5 h | 15.5 GB |
