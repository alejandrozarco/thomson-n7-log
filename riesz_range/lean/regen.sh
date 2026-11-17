#!/bin/bash
# Regenerate the upstream-derived ThomsonGen modules (not stored here) from the Coulomb formalisation
# huwngtran/thomson-n7-lean at a pinned commit: the split modules ThomsonGen/*.lean and the verbatim
# modules ThomsonGen/Verbatim/*.lean (lists in ThomsonGen/scripts/verbatim/), and check them against
# ThomsonGen/scripts/generated.sha256.
set -euo pipefail
cd "$(dirname "$0")"
REPO=https://github.com/huwngtran/thomson-n7-lean.git
REV=25f2fa53119273458cfbb3c4230904bffdd61e53
SOL_SHA=6545e982abaeb4ca          # prefix of sha256(formal/lean/ThomsonN7/Solution.lean) at REV
U=.upstream
if [ ! -d $U ]; then git clone --quiet $REPO $U; fi
git -C $U checkout --quiet $REV
SOL=$U/formal/lean/ThomsonN7/Solution.lean
case "$(shasum -a 256 $SOL 2>/dev/null || sha256sum $SOL)" in
  $SOL_SHA*) ;; *) echo "unexpected Solution.lean" >&2; exit 1;;
esac
UPSTREAM_SOLUTION=$PWD/$SOL python3 ThomsonGen/scripts/split.py
shasum -a 256 -c ThomsonGen/scripts/generated.sha256 2>/dev/null || sha256sum -c ThomsonGen/scripts/generated.sha256
echo "regen OK"
