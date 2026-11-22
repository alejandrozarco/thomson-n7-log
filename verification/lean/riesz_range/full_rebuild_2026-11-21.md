# Full rebuild of the Lean library from a fresh clone of v2.8 (2026-11-20 to 2026-11-21)

AI-produced record (Claude Opus 5.5). This record covers a rebuild of every module of `riesz_range/lean` from a fresh
clone of the published tag and a byte comparison with the checked build. It is not a review of the proof, and it does
not repeat the Comparator, lean4export or nanoda runs (those were run on the checked build; see
`record_2026-11-17.txt`).

Files in [`full_rebuild/`](full_rebuild/):

- `fb_run.sh`, `fb_sched.py`: the scripts as run. Machine-specific directories are replaced by placeholders:
  `<fresh>` is the directory of this rebuild, `<build>` and `<deps>` are the deployed trees of the checked build (as in
  `route_check_2026-11-17.md`), `<work>` holds the shared lock files.
- `fb.log`: the log of the run. One progress line of `lake exe cache get` (104 kB of carriage-return updates) is
  shortened to its last update; nothing else was changed.
- `build.tsv`: one line per RieszN7 module (module, exit code, wall seconds, peak RSS in kB, slot, end time).
- `cmp_all.tsv`: for each of the 5 103 modules of `build_order.txt`, the sha256 of the fresh and of the checked olean
  and ilean, and the result.
- `RieszN7.Check.AxiomsFull.log`, `RieszN7.Check.AxiomsCore.log`: the output of the two axiom-check modules of the
  fresh build.

## Setup

- Source: `git clone --depth 1 --branch v2.8` of the public repository; HEAD `49cda64` ("Release v2.8: dates in
  CHANGELOG, CITATION.cff and README"), tag `v2.8`.
- Machine: the Linux workstation of the recorded build and of the route check (Linux 6.8.0 x86_64, 6 cores, 19 GB RAM).
  It was shared with other jobs. Every step ran at nice 19 with idle I/O priority, in its own process group.
- Toolchain: Lake 5.0.0-src+5045d00, Lean 4.34.1 (commit 5045d005…); lean binary sha256 `e8baaa71…5d5550`, the one in
  `tools.txt`. Python 3.12.3.
- The Mathlib and Lake caches were new and empty (`XDG_CACHE_HOME`, `MATHLIB_CACHE_DIR` and `LAKE_CACHE_DIR` under
  `<fresh>/`). `LEAN_NUM_THREADS` and `LEAN_PATH` were unset for the Lake steps.
- Reference: the deployed oleans of the checked build (`<build>` for RieszN7, `<deps>` for ThomsonGen and LogLean).
  They were only read.

## Steps (times are UTC)

| phase | what | result | wall |
|---|---|---|---|
| A | `./regen.sh` | rc 0 | 17 s |
| A | `sha256sum -c SHA256SUMS upstream_regenerated.sha256` | rc 0, 5 103 OK, 0 other lines | 2 s |
| A | `lake exe cache get` | rc 0, 8 908 files downloaded and decompressed | 18 min 32 s |
| A | `lake build M` for each of the 23 modules of `build_order.txt` that are not RieszN7 (ThomsonGen and LogLean), one at a time, in the order of `build_order.txt` | rc 0 for all 23; peak RSS at most 9.0 GB (`ThomsonGen.M2`) | 19 min 24 s |
| B | the recorded recipe `LEAN_NUM_THREADS=1 lean -j1 -DElab.async=false -o <M>.olean -i <M>.ilean <M>.lean`, run in `riesz_range/lean` with a relative source path, for each of the 5 080 RieszN7 modules (at most two at a time, each started only after its RieszN7 imports were built; `fb_sched.py`) | rc 0 for all 5 080; no failure; the memory watchdog never stopped a job; peak RSS at most 7.99 GB (`RieszN7.MainFull`) | 39 h 25 min (62.3 h of compile time summed over modules) |
| C | sha256 comparison of every olean and ilean with the checked build; axiom output; `sorry` and `error` lines in the module logs | below | 7 min |

Start 2026-11-20 00:32:02, end 2026-11-21 16:43:57 (40 h 12 min). Exit code of `fb_run.sh`: 0.

## Results

**Byte comparison** (`cmp_all.tsv`):

- ilean: 5 103 of 5 103 identical.
- olean: 5 100 of 5 103 identical, among them all 5 080 RieszN7 oleans and 20 of the 23 Lake-built oleans.
- The 3 other oleans are Lake-built upstream modules: `ThomsonGen.ThreePoint`, `ThomsonGen.Typed` and
  `ThomsonGen.Cert.NBlk`. Each embeds the absolute path of its source file, and the path of the fresh clone is 29
  characters longer than that of the checked tree. The fresh oleans are 32, 32 and 24 bytes larger. After both paths
  are replaced by the same placeholder, the printable strings (`strings -n 4`) of the fresh and the checked olean are
  identical for all three. Every RieszN7 module that imports them was built against the fresh oleans and is
  byte-identical to the checked build.

**Axioms** (fresh build, `RieszN7.Check.AxiomsFull` and `RieszN7.Check.AxiomsCore`):
`RieszN7.Full.riesz_seven_range`, `RieszN7.Full.riesz_seven_unique_range`, `RieszN7.Core12.riesz_seven_core` and
`RieszN7.Core12.riesz_seven_unique_core` depend on `[propext, Classical.choice, Quot.sound]`. The printed statements
are those of the README.

**Warnings:** the only `sorry` or `error` lines in the 5 080 module logs are `declaration uses 'sorry'`, twice in each of
`RieszN7/Release/FullChallenge.lean`, `RieszN7/Release/Core12Challenge.lean`, `RieszN7/Release/FullNegStatement.lean`
and `RieszN7/Release/Core12NegStatement.lean`: the statement placeholders of the Comparator challenge and of its negative
control, as intended.

## What this does and does not show

It shows that the sources of the tag `v2.8`, with the pinned toolchain and Mathlib, rebuild to the oleans that were
checked, byte for byte for every RieszN7 module, on the machine of the recorded build. It does not show the same on
another machine or operating system, and it adds no check of the statements or of the kernel beyond those already
recorded.
