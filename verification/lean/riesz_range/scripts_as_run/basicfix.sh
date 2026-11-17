#!/bin/bash
# basicfix.sh -- reproducible rebuild of RieszN7.Basic and everything that imports it (2026-11-13;
# condition: the Comparator must certify only oleans that a committed script can rebuild). S1 showed that the deployed
# RieszN7.Basic olean (built 2026-11-07 20:24 UTC by an uncommitted pre-v1 build script; same source sha 9d965b9c...)
# is not reproduced by any tried recipe, although its definitions print identically. This script supersedes the
# export phase of docfix.sh (stopped after its source install; the docstring edits are already installed):
# 1. waits until the PID given as $1 (an orphaned lean from the stopped docfix build, or 0) has exited;
# 2. copies the current olean/ilean of every module in mods.txt + release.txt to basicfix/_aside/before/ (nothing
#    deleted);
# 3. rebuilds mods.txt in topological order (RieszN7.Basic, its 354 dependents, and Range.Cover and the docfix leaf
#    modules) with build_range.sh (committed recipe, no --skip-built), skipping modules that were never deployed (no
#    olean before the run), then the 8 Release modules with the lake shim under lean.lock;
# 4. checks that the new Basic olean equals the committed-recipe rebuild from S1 (s1check/out_recipe), and the axiom
#    audits (exactly propext, Classical.choice, Quot.sound for the four main theorems);
# 5. re-exports Full and Core12 Solutions to new files; their sha256 must equal the certified exports (kernel content
#    unchanged by the docstring edits and the Basic rebuild).
# Result "BASICFIX RESULT: OK/FAIL ..." in basicfix/basicfix.log. Run under hb.sh (name basicfix). AI-written.
set -u
W=<basicfix>; LOG=$W/basicfix.log; D=<build>; L=<logs>
S=$D/release_core/scripts; B=$D/.lake/build/lib/lean
FULL_SHA=e994407ff4fd90b0b57c28edc3ac1d2c66e8c28bb00a7a4d4bcdf4fe2fc3ba5a
CORE_SHA=878884835761bf88f0523516938e0095b88ba9c506d9bc931b0b44cf34cf1883
say() { echo "$(date -Is) $*" >> $LOG; }
say "start pid $$ (wait for pid ${1:-0})"
[ "${1:-0}" != 0 ] && while kill -0 "$1" 2>/dev/null; do sleep 10; done
MODS=""; skipped=""
for M in $(cat $W/mods.txt); do
  if [ -f $B/${M//.//}.olean ]; then MODS="$MODS $M"; else skipped="$skipped $M"; fi
done
REL=$(sed 's/^RieszN7\.Release\.//' $W/release.txt)
say "$(echo $MODS | wc -w) modules to rebuild; never deployed, skipped:${skipped:- none}; release: $(echo $REL)"
mkdir -p $W/_aside/before
for M in $MODS $(sed 's/$//' $W/release.txt); do
  F=${M//.//}
  for x in $F.olean $F.ilean; do
    [ -f $B/$x ] && { mkdir -p $W/_aside/before/$(dirname $x); cp -p $B/$x $W/_aside/before/$x; }
  done
done
say "aside copies done"

KEEP_GOING=0 bash $D/build_range.sh $MODS >> $W/build.out 2>&1; BR=$?
say "build_range.sh rc=$BR"
[ $BR = 0 ] || { say "BASICFIX RESULT: FAIL build_range"; exit 1; }
exec 9><work>/lean.lock; flock 9; say "lean.lock acquired"
for r in $REL; do
  bash $S/run_step.sh basicfix_build_$r bash -c "source $S/env_core.sh; cd $D; lake build RieszN7.Release.$r" >> $LOG 2>&1 \
    || { say "BASICFIX RESULT: FAIL build $r"; exit 1; }
done
fail=""
grep -q "declaration uses 'sorry'" $L/basicfix_build_FullSolution.log $L/basicfix_build_Core12Solution.log && fail="$fail sorry"
if cmp -s $B/RieszN7/Basic.olean <s1check>/out_recipe/RieszN7/Basic.olean; then
  say "Basic olean = S1 committed-recipe rebuild ($(sha256sum < $B/RieszN7/Basic.olean | cut -c1-16))"
else say "Basic olean differs from the S1 committed-recipe rebuild"; fail="$fail basic"; fi
for a in AxiomsCore AxiomsFull; do
  G=$L/rg_RieszN7_Check_$a.log; cp $G $W/$a.log
  n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" $G); bad=$(grep -c "sorryAx\|depends on axioms" $G)
  say "$a: $n of 2 theorems with exactly [propext, Classical.choice, Quot.sound]"
  [ "$n" = 2 ] && [ "$bad" = 2 ] || fail="$fail axioms:$a"
done
for X in "full FullSolution riesz_seven_range riesz_seven_unique_range $FULL_SHA" \
         "core Core12Solution riesz_seven_core riesz_seven_unique_core $CORE_SHA"; do
  set -- $X; EXP=$W/export_$1.ndjson
  bash $S/run_step.sh basicfix_export_$1 bash -c "source $S/env_core.sh; cd $D; /usr/bin/time -v -o $W/export_$1.time \
    \$LEAN4EXPORT RieszN7.Release.$2 -- ThomsonN7Riesz.$3 ThomsonN7Riesz.$4 > $EXP" >> $LOG 2>&1 || fail="$fail export:$1"
  H=$(sha256sum < $EXP | cut -d' ' -f1)
  if [ "$H" = "$5" ]; then say "export $1: $(stat -c %s $EXP) bytes, sha256 $H = certified (identical)"
  else say "export $1: sha256 $H != certified $5"; fail="$fail export-differs:$1"; fi
done
[ -z "$fail" ] && say "BASICFIX RESULT: OK (Basic + dependents rebuilt by committed recipe, axioms clean, Full and Core12 exports byte-identical)" \
               || say "BASICFIX RESULT: FAIL$fail"
[ -z "$fail" ]
