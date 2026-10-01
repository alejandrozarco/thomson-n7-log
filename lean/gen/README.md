# Generators (not needed for the build)

These scripts produced the Lean sources in `../LogLean/` and `../LogN7/`. They emitted the certificate data from the
JSON certificates of `../../certificates/`, along with the minorant pieces, the local-lemma data and the per-block
splits. The generated Lean files name their generator in their header; the other files in `../LogLean/` and
`../LogN7/` are written by hand. `LocalCert.template.lean` and `LogPhi.lean` here are inputs of
`export_local_cert.py`/`export_local_bench.py` and `emit_cap.py`; they are not part of the build.

The scripts were run in the development tree, where the checker modules were in `numerics/cells/` and `numerics/hp/`
(here: `../../checkers/`). They are included for reference. `lake build` does not run them.

- `gen/` holds the minorant, local-lemma and cap generators.
- `gen_log/` holds the per-cell emitters (`emit_tcert.py`, `emit_cert3.py`), the per-block checks (`gen_capchk.py`,
  `gen_split.py`) and the cell specifications (`gen_spec_log.py`).
