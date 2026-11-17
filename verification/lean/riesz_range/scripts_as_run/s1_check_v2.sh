#!/bin/bash
# s1_check.sh -- Fable review S1 (2026-11-12): tie the trusted definition oleans to the git sources.
# 1. waits (no lock) for <hb>/comparator_full.exit;
# 2. under lean.lock + guarded.sh: rebuilds ThomsonGen.Preamble, ThomsonGen.Base, RieszN7.Core.Rpow, RieszN7.Basic from
#    the git-HEAD sources in src/ into out/ (LEAN_PATH = out + Mathlib packages only, never the deployed build trees);
# 3. cmp's each fresh olean with the deployed one the release checks used (pub_n7c / pub_range);
# 4. compiles PrintDefs.lean against the deployed release LEAN_PATH and against out/, and diffs the two outputs.
# Result line "S1 RESULT: OK" / "S1 RESULT: FAIL ..." in s1check/s1.log.  Run under hb.sh (name s1_check).
set -u
W=<s1check>; LOG=$W/s1.log; N=<deps>; R=<build>
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
say() { echo "$(date -Is) $*" >> $LOG; }
say "start pid $$ (v2: lean --root, fix 2026-11-13 for 'input file must be contained in root directory')"
while [ ! -f <hb>/comparator_full.exit ]; do sleep 120; done
say "comparator_full exited: $(cat <hb>/comparator_full.exit)"
PK=""; for p in $N/.lake/packages/*; do PK=$PK:$p/.lake/build/lib/lean; done
FRESH=$W/out$PK
DEPLOY=$R/.lake/build/lib/lean:$N/.lake/build/lib/lean$PK
sha256sum $W/src/ThomsonGen/*.lean $W/src/RieszN7/*.lean $W/src/RieszN7/Core/*.lean >> $LOG
exec 9><work>/lean.lock; flock 9; say "lean.lock acquired"
fail=""
for M in ThomsonGen/Preamble ThomsonGen/Base RieszN7/Core/Rpow RieszN7/Basic; do
  mkdir -p $W/out/$(dirname $M)
  bash <work>/guarded.sh s1_${M//\//_} env LEAN_PATH=$FRESH LEAN_NUM_THREADS=1 \
    $LEAN --root=$W/src -j1 -DElab.async=false -o $W/out/$M.olean -i $W/out/$M.ilean $W/src/$M.lean
  rc=$(cat <logs>/s1_${M//\//_}.exit 2>/dev/null | awk '{print $NF}')
  case $M in ThomsonGen/*) D=$N/.lake/build/lib/lean/$M.olean;; *) D=$R/.lake/build/lib/lean/$M.olean;; esac
  if cmp -s $W/out/$M.olean $D; then r=identical; else r=DIFFERENT; fail="$fail $M"; fi
  say "$M build_exit=[$rc] fresh=$(sha256sum < $W/out/$M.olean | cut -c1-16) deployed=$(sha256sum < $D | cut -c1-16) olean $r"
done
for P in DEPLOY FRESH; do
  bash <work>/guarded.sh s1_print_$P env LEAN_PATH=${!P} LEAN_NUM_THREADS=1 $LEAN --root=$W -j1 -DElab.async=false $W/PrintDefs.lean
  cp <logs>/s1_print_$P.log $W/print_$P.txt
done
if diff -q $W/print_DEPLOY.txt $W/print_FRESH.txt >/dev/null && [ -s $W/print_DEPLOY.txt ]; then say "PrintDefs outputs identical ($(wc -l < $W/print_DEPLOY.txt) lines)"; else fail="$fail PrintDefs"; say "PrintDefs outputs differ or empty"; fi
grep -q "error" $W/print_DEPLOY.txt && fail="$fail PrintDefs-error"
[ -z "$fail" ] && say "S1 RESULT: OK" || say "S1 RESULT: FAIL$fail"
[ -z "$fail" ]
