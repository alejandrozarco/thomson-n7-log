# AI disclosure

AI models produced the content of this repository: the mathematics, certificates, checkers, Lean formalisation,
figures and text. The repository owner chose the problem, directed the work and decided on scope and publication.
The owner did not check the mathematics or the Lean code line by line.

**Models**
- Claude Opus 5.5 (Anthropic, via Claude Code) did all the work, as several coordinated agents.
- Reviews were run as separate read-only instances of Claude Opus 5.5, Claude Fable 5.1 (Anthropic) and gpt-6-astra
  (OpenAI, via the Codex CLI).
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

AI reviews are not peer review, and no human expert has checked this work. In the terminology of the Lean community
this is a *warrant*, not a human-readable proof (see the note at the top of `README.md`).

**What is checked by software**
- The exact checkers in `checkers/`, `local/`, `riesz2/` and `coulomb/` check the certificates and the local lemmas,
  in exact rational or ball arithmetic.
- The Lean 4 kernel checks the formalisations in `lean/`, `riesz2/lean/` and `coulomb/lean/`. `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`.

What remains to be trusted:
- that the Lean statement files express the intended theorems;
- the Lean kernel and toolchain;
- the definitions regenerated from the upstream formalisation, [huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean),
  which was itself produced with AI agents.
