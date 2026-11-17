# Route check: README Lean route from a fresh clone, trusted closure only (2026-11-17)

AI-produced record (Claude Opus 5.5). This check covers only the README's route to the trusted closure. It does not
rebuild the library and is not a review of the proof.

Note added for the release (2026-11-17): the commit named under Setup is a commit of the release candidate that is not
in the published history; its `riesz_range/lean/` tree is byte-identical to `riesz_range/lean/` in this release (same
`SHA256SUMS`). One sentence of the setup was made neutral ("shared with other jobs"); nothing else was changed. The
README corrections listed at the end have been applied to `riesz_range/README.md` and `record_2026-11-17.txt`.

## Setup

- Source: a fresh `git clone` of the release candidate (branch `rc-riesz-range`, commit
  `a0b8ddcdd5440f91e5883682625e709cb94ffcac`). Only `riesz_range/lean/` was copied, all 5 107 files, to `<work>/riesz_range/lean`
  on a Linux workstation (Linux 6.8.0 x86_64, 6 cores, 19 GB RAM, the same machine as the recorded build; exFAT
  filesystem). The machine was shared with other jobs. Every step ran at nice 19 under the
  MemAvailable < 3 GB watchdog, and every compile step held the shared Lean lock.
- Toolchain: elan 4.2.4, Lake 5.0.0-src+5045d00, Lean 4.34.1 (commit 5045d005…). The lean binary sha256
  `e8baaa71…5d5550` is the one in `tools.txt`. git 2.43.0, Python 3.12.3.
- The Mathlib and Lake caches were new and empty (`XDG_CACHE_HOME`, `MATHLIB_CACHE_DIR` and `LAKE_CACHE_DIR` under
  `<work>/`). `LEAN_NUM_THREADS` and `LEAN_PATH` were unset for the README steps.
- Reference: the deployed oleans that were checked. They are `<build>/.lake/build/lib/lean` for RieszN7 and
  `<deps>/.lake/build/lib/lean` and `<deps>/.lake/packages` for ThomsonGen and Mathlib. These trees were only read.
- Closure built: ThomsonGen.Preamble, ThomsonGen.Base, RieszN7.Core.Rpow, RieszN7.Basic,
  RieszN7.Release.FullChallenge and RieszN7.Release.Core12Challenge. No Cells, Cap or library target was built.

## Steps (times are UTC, 2026-11-17)

Wall time and peak RSS come from `/usr/bin/time -v`. Peak RSS is that of the largest single process.

| # | command (cwd `riesz_range/lean`) | as printed? | result | wall | peak RSS | network |
|---|---|---|---|---|---|---|
| 1 | `./regen.sh` | yes | rc 0, "regen OK", the 20 modules of `generated.sha256` OK | 9.6 s | 0.1 GB | GitHub clone of the upstream repository |
| 2 | `shasum -a 256 -c SHA256SUMS upstream_regenerated.sha256` | yes (`shasum` is present on this system) | rc 0, 5 103 OK | 4.6 s | — | none |
| 2' | `sha256sum -c SHA256SUMS upstream_regenerated.sha256` | yes | rc 0, 5 103 OK, 0 other lines | 2.0 s | — | none |
| 3 | `lake exe cache get` | yes | rc 0. It cloned mathlib and its 8 dependencies at the manifest revisions, compiled the `cache` executable (43 jobs) and downloaded and unpacked 8 908 files | 18 min 16 s | 0.96 GB | GitHub (9 git clones) and cache.mathlib.org (8 908 files) |
| 3b | `lake build --no-build Mathlib Mathlib.Analysis.Convex.SpecificFunctions.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real` (guard, not in the README) | — | rc 0, "All targets up-to-date (8923 jobs)", so nothing of Mathlib is compiled | 45 s | 0.96 GB | none |
| 4 | `lake build ThomsonGen.Preamble ThomsonGen.Base RieszN7.Core.Rpow RieszN7.Basic RieszN7.Release.FullChallenge RieszN7.Release.Core12Challenge` (**not printed in the README**) | no command printed | rc 0, "Build completed successfully (8929 jobs)". Six modules were compiled: Preamble 103 s, Base 13 s, Rpow 30 s, Basic 12 s, the challenges 10 s and 11 s. Warnings: two unused-`ring` linter warnings in Basic, and `declaration uses 'sorry'` twice in each Challenge (the statement placeholders, as expected) | 2 min 43 s | 6.8 GB | none |
| 5 | recorded `build_range.sh` recipe for the 4 RieszN7 modules, run from the root of the fresh workspace (below) | from `scripts_as_run/` | rc 0 for all 4. Rpow 9.8 s, Basic 16.8 s, FullChallenge 15.2 s, Core12Challenge 15.1 s | 57 s total | 2.5 GB (Rpow), 6.8 GB (others) | none |
| 6 | `#print` check, 3 oleans × 2 files | — | all identical (below) | 12 s each; 4 min 29 s for the first deployed read (cold page cache) | 6.5–6.8 GB | none |

The lowest MemAvailable seen by the watchdog during the Lake build was 14.4 GB. The watchdog never fired.

The step 5 recipe is the command of `scripts_as_run/build_range.sh`, with the build root set to the fresh workspace.
It ran in topological order, after Lake's oleans had been copied aside:

```sh
cd riesz_range/lean
LP=.lake/build/lib/lean; for p in .lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done   # absolute paths were used
for M in RieszN7/Core/Rpow RieszN7/Basic RieszN7/Release/FullChallenge RieszN7/Release/Core12Challenge; do
  LEAN_PATH=$LP LEAN_NUM_THREADS=1 <elan>/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -DElab.async=false \
    -o .lake/build/lib/lean/$M.olean -i .lake/build/lib/lean/$M.ilean $M.lean
done
```

The olean and ilean paths were absolute. The source path was relative to the workspace root, as in `build_range.sh`.
ThomsonGen was not rebuilt by a second recipe, because Lake's output already matched.

Disk use, by apparent size: `.lake/packages` 7.2 GB, the Mathlib download cache 431 MB, `.lake/build` 39 MB and
`.upstream` 25 MB. `du` on this exFAT filesystem (128 KiB clusters) reports 24 GB for `.lake`.

## Olean comparison (sha256, fresh vs deployed)

| module | Lake route (README) | build_range recipe from the fresh root | deployed olean sha256 |
|---|---|---|---|
| ThomsonGen.Preamble | **identical** | (not rebuilt; Lake = recorded recipe) | `2511e4e7d2decdada00b5c54c8497dc03a0c5efde1fb1a131e730e5b7661db79` |
| ThomsonGen.Base | **identical** | (not rebuilt) | `2a6813c8847dd866808d658c48685cbdbb41bcb5014601d157ff7ada2b69b674` |
| RieszN7.Core.Rpow | different (`7a17863c…`, 473 432 B vs 471 584 B) | **identical** | `2e308655a75a8e8f45cc436d28935ecdf7d6439c25a1a1d037a85106f951d0a6` |
| RieszN7.Basic | different (`8191d62a…`, 438 056 B vs 437 784 B) | **identical** | `be84f5679638d35b7a119e4e4330a7aed2bb6dc9337c592670bcb5e14ff804e7` |
| RieszN7.Release.FullChallenge | different (`ff1bea49…`, 31 712 B vs 31 608 B) | **identical** | `d6e687c10c017648165a1aaf8443840e08e604b87b29bde6d1fc04c077622b31` |
| RieszN7.Release.Core12Challenge | different (`29db978c…`, 31 280 B vs 31 176 B) | **identical** | `5471bd31fedfc93c53a947fcd1d0c1d816349d5db3020a798717924e30d0aecb` |

- Every `.ilean` is identical to the deployed one on both routes.
- Dependencies: the package revisions after `lake exe cache get` equal those of the deployed dependency workspace for
  all 9 packages. Every package olean is byte-identical to the deployed one: mathlib 8 548, batteries 192, aesop 132,
  Qq 14, plausible 13, proofwidgets 13, importGraph 10, LeanSearchClient 4, Cli 0. None differ and none are missing.
- Lake builds every module with `lean <abs path> -o … -i … -c … --setup <json> --json`, with default elaboration
  options. For the ThomsonGen modules this is the same recipe as the deployed builds, and the bytes match. The RieszN7
  modules were checked as built by `lean -j1 -DElab.async=false`, so Lake's RieszN7 oleans have other bytes.
- RieszN7.Basic is reproduced byte for byte. The record says its olean "was not reproduced out of tree". Run from the
  root of a fresh clone, with the relative source path of `build_range.sh`, the committed recipe reproduces the deployed
  `be84f567…`. This is consistent with the record's guess that the earlier mismatch came from the build path. That
  mismatch came from a scratch directory with `--root` and absolute source paths. The cause was not investigated
  further.

## `#print` of the trusted definitions

The record's `PrintDefs.lean` was compiled against three sets of oleans: Lake route (LAKE), recipe route (RECIPE) and
deployed (DEPLOY). A second file, `PrintDefsExplicit.lean`, uses `pp.explicit`, `pp.universes` and
`pp.funBinderTypes`, adds `#print ThomsonN7.cyl` and `#print axioms ThomsonN7.pentBipyramid`, and shows the HPow, Norm
and PiLp instances.

| file | LAKE | RECIPE | DEPLOY |
|---|---|---|---|
| PrintDefs.lean (13 lines) | = DEPLOY | = DEPLOY | = recorded `trusted-definitions/print_DEPLOY.txt` |
| PrintDefsExplicit.lean (118 lines, no errors) | = DEPLOY | = DEPLOY | sha256 prefix `eb732da3e2cdb1b5` |

Both `#print axioms` lines give `[propext, Classical.choice, Quot.sound]`. The Lake-route oleans differ in bytes, but
the trusted definitions print the same as in the checked oleans, including with explicit instances.

## Verdict

The README route works as printed for the commands it prints (`./regen.sh`, the checksum line in either form,
`lake exe cache get`). It is incomplete, because it prints no build command. With the obvious `lake build` of the
closure, the ThomsonGen oleans are byte-identical to the checked ones, but the RieszN7 oleans are not. The recorded
`build_range` recipe, run from the root of the fresh clone, reproduces all four RieszN7 oleans of the trusted closure
byte for byte, RieszN7.Basic included. All six oleans of the trusted closure have therefore been reproduced from a fresh
clone, each by the recipe that built it.

## README corrections (riesz_range/README.md, "Reproduce", Lean)

1. Replace "**No route from a fresh clone to a built tree has been tested.**" with: "The route below was tested from a
   fresh clone on 2026-11-17 for the trusted closure only (ThomsonGen.Preamble, ThomsonGen.Base, RieszN7.Core.Rpow,
   RieszN7.Basic and the two Challenge files). The full library build was not repeated."
2. After `lake exe cache get`, add the build command for the closure:
   `lake build ThomsonGen.Preamble ThomsonGen.Base RieszN7.Core.Rpow RieszN7.Basic RieszN7.Release.FullChallenge RieszN7.Release.Core12Challenge`
   Then state that Lake reproduces the checked ThomsonGen oleans byte for byte, that its RieszN7 oleans have other bytes
   (Lake's recipe), and that the `#print` of the trusted definitions is identical.
3. Add the recipe that reproduces the checked RieszN7 bytes (the block in "Steps" above). It is run in
   `riesz_range/lean` with relative source paths and outputs under `.lake/build/lib/lean`, after the Lake step has
   built the ThomsonGen oleans and fetched Mathlib. Not tested: whether a later `lake build` keeps or rebuilds the
   oleans this overwrites, and calling `lean` through the elan proxy rather than the toolchain binary (same binary).
4. Replace "`lakefile.toml` describes the same libraries for `lake build`; it has not been tested" with "tested for the
   trusted closure (2026-11-17), not for the full library".
5. Add costs: `lake exe cache get` cloned 9 repositories from GitHub, compiled the cache tool and downloaded 8 908
   files (18 min wall here, network-dependent). Each module of the closure that imports `ThomsonGen.Preamble`
   (`import Mathlib`) peaks at about 6.8 GB. `.lake` needs about 7.2 GB (apparent size).
6. In `verification/lean/riesz_range/record_2026-11-17.txt` ("Trusted definitions"), extend the statement that the
   olean of RieszN7.Basic "was not reproduced out of tree": a build from a fresh clone by the committed recipe, in the
   workspace root, reproduces it (2026-11-17).
