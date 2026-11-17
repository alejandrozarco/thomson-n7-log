# Changelog

Earlier versions are listed on the Zenodo record and the GitHub releases page.

## Next release (candidate, 2026-11-17)

- `riesz_range/`: checkers, a coverage checker and a Lean 4 development for the Riesz $`s`$-energy of seven points on
  the interval $`1/3 \le s \le 7/4`$ (see [`riesz_range/README.md`](riesz_range/README.md)).
- The bulk data of `riesz_range/` (certificate files, per-piece reports, the re-rounded cap certificates of the Lean
  development, and the two Lean kernel exports) are not in git but in a separate Zenodo archive (DOI: see
  `riesz_range/README.md`, Bulk data; to be filled at release). `riesz_range/fetch_bulk.sh` downloads the archive,
  checks its sha256 and every file against `riesz_range/BULK_SHA256SUMS`; a fresh clone needs this step before
  `range_check.py` runs.
