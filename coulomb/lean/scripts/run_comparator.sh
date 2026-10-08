#!/usr/bin/env bash
# Run leanprover/comparator. It checks three things:
#   - the theorems named in the config (comparator.json: FivePointsRiesz2.five_riesz2(_unique), s = 2;
#     comparator_s1.json: FivePointsCoulomb.five_coulomb(_unique), s = 1) in the solution module have the same
#     statements as the sorry'd ones in the challenge module;
#   - they use only propext, Quot.sound and Classical.choice;
#   - the Lean kernel accepts them (replayed from a lean4export dump).
# Needs a built workspace (regen.sh, lake exe cache get, lake build), git, network for the first clone of the tools,
# and several GB of RAM. Comparator runs the solution under `landrun` (Linux Landlock). If `landrun` is not on PATH,
# Comparator's own non-sandboxing shim scripts/fake-landrun.sh is used; set COMPARATOR_LANDRUN to use a landrun binary.
# Adapted from ComparatorChallenges/run_comparator.sh of huwngtran/thomson-n7-lean.
# Usage: bash scripts/run_comparator.sh [CONFIG]   (default comparator.json)   Output: logs/<CONFIG without .json>.log
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
source scripts/tools.sh
export LAKE_ARTIFACT_CACHE=false
need_lean4export; need_comparator
export COMPARATOR_BIN COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT"
if [ -z "${COMPARATOR_LANDRUN:-}" ]; then
  if command -v landrun >/dev/null 2>&1; then COMPARATOR_LANDRUN="$(command -v landrun)"
  else COMPARATOR_LANDRUN="$TOOLS/comparator/scripts/fake-landrun.sh"; echo "WARNING: no landrun found, using the non-sandboxing shim $COMPARATOR_LANDRUN" >&2; fi
fi
export COMPARATOR_LANDRUN
mkdir -p logs
CFG="${1:-comparator.json}"; LOG="logs/$(basename "$CFG" .json).log"
/usr/bin/time -p lake env "$COMPARATOR_BIN" "$CFG" 2>&1 | tee "$LOG"
echo "COMPARATOR EXIT: ${PIPESTATUS[0]}"
