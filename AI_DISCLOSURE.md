# AI disclosure

AI models produced the content of this repository: the mathematics, certificates, checkers, Lean formalisation,
figures and text. The repository owner chose the problem, directed the work and decided on scope and publication.
The owner did not check the mathematics or the Lean code line by line.

**Models**
- Claude Opus 5.5 (Anthropic, via Claude Code) did the work up to v2.7, as several coordinated agents. For
  `riesz_range/` (2026-11-06 to 2026-11-17) the work was done by Claude Opus 5.5 and Claude Fable 5.1 agents.
- Reviews were run as separate read-only instances of Claude Opus 5.5, Claude Fable 5.1, Claude Fable 5.2
  (Anthropic) and gpt-6-astra (OpenAI, via the Codex CLI).
- The commits carry a `Co-Authored-By: Claude Opus 5.5` trailer.

**Reviews.** The AI reviews found real errors. The maintainers report that the listed findings were addressed (the
review reports themselves are not public):
- a checker that accepted a certificate with an empty SOS section (the tampered-certificate controls in
  `checkers/check_controls.py` were added as a result);
- gaps and wrong constants in written deductions;
- documentation that claimed more than was checked;
- upstream code stored in the repository, now regenerated or attributed (`lean/README.md`);
- for the Coulomb case (`coulomb/`, 2026-10-08; two gpt-6-astra reviews, of the Python chain and of the Lean port):
  a coercivity checker that exited with status 0 when coercivity failed; a Python cross-check of the emitted Lean
  data that could pass with missing blocks (Lean's own checks were not affected); a certified lower bound rounded up
  in a summary; stale descriptions carried over from the log case.
- for the Riesz interval $`1/3 \le s \le 7/4`$ (`riesz_range/`, 2026-11-17), three read-only Claude Fable 5.1 reviews
  (three reports, not public):
  - of the Python assembly for $`[1/2, 3/2]`$: piece reports were accepted on file modification times alone (sha256
    provenance of checker sources and inputs was added and every used piece was re-run); `min()`/`max()` over arb
    balls, which is not sound in python-flint; direction blocks of the cap not checked for symmetry; mean-value radii
    that ignored the radius of the midpoint value; a stale expectation in a self-test; documentation drift;
  - of the extension to $`[1/3, 7/4]`$: a document that still stated the old interval and a false constant
    ($`|v''| \le 0.34`$; the bound on $`[1/3, 7/4]`$ is $`0.382`$); the local-lemma tube width and piece ends read from
    file names without a cross-check against the recorded provenance; the coverage checker's own hash not recorded;
    an incremental re-check option that skipped too many pieces. All were fixed;
  - of the Lean port: the `lake` stand-in used with Comparator takes the oleans of the trusted definitions as given,
    so Comparator alone does not tie them to the sources (answered by a `#print` comparison, olean reproduction and
    a rebuild with byte-identical re-export, `verification/lean/riesz_range/`); no sandbox for Comparator (stated);
    the tamper control changed upstream material only (a second control on this development's certificate data was
    added); Comparator wording; "pairwise distinct" in the statement description; a trusted closure larger than
    planned; stale text; oleans built on more than one machine (recorded with their hashes); credit to Kryvonos,
    Liehr and Taylor and the licence of the upstream code.
- for the release of `riesz_range/` (2026-11-17), four read-only reviews (two by Claude Fable 5.2, one by Claude
  Opus 5.5, one by gpt-6-astra; reports not public): no error in the Lean statements was found; the documentation
  corrections included the Lean version of the kernel replay in Comparator (v4.35.0-rc3), reproduction commands that
  could not run as printed, which theorems `#print axioms` was run on, stale metadata, an incomplete description of
  the Kryvonos-Liehr-Taylor result, and wording.

AI reviews are not peer review, and no human expert has checked this work. In the terminology of the Lean community
this is a *warrant*, not a human-readable proof (see the note at the top of `README.md`).

**What is checked by software**
- The exact checkers in `checkers/`, `local/`, `riesz2/`, `coulomb/` and `riesz_range/n7_interval/` check the
  certificates and the local lemmas, in exact rational or ball arithmetic.
- The Lean 4 kernel checks the formalisations in `lean/`, `riesz2/lean/`, `coulomb/lean/` and `riesz_range/lean/`.
  `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.

What remains to be trusted:
- that the Lean statement files express the intended theorems;
- the Lean kernel and toolchain;
- for `riesz_range/lean/`: Comparator ran without a sandbox and with prebuilt imports, and nanoda with its natural
  number and string extensions (`verification/lean/riesz_range/tools.txt`, `record_2026-11-17.txt`);
- the definitions regenerated from the upstream formalisation, [huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean),
  which was itself produced with AI agents.
