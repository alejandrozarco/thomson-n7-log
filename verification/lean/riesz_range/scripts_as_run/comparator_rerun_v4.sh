#!/bin/bash
# comparator_rerun.sh -- relaunch of the main Full Comparator run (2026-11-13). Run 1 (2026-11-11 18:20 UTC) was
# stopped after 29.6 h by our own guarded.sh watchdog (MemAvailable < 3 GB while an unrelated C++ build ran; rc 143);
# it was an environment failure, not a check failure. This waiter, run under hb.sh (name comparator_full2):
# 1. waits (no lock) for hb/basicfix.exit and requires "BASICFIX RESULT: OK" (v2, 2026-11-13: basicfix.sh supersedes
#    docfix's rebuild/export phase and also rebuilds RieszN7.Basic and its dependents with the committed recipe, so the
#    Comparator certifies only reproducible, docstring-fixed oleans; otherwise it stops without running);
# 2. gate: no <other-build> processes and MemAvailable > 12 GB, for 10 consecutive minutes (run 1 peaked at
#    12.2 GB session RSS); no automatic retry if the watchdog trips again (report instead);
# 3. moves run 1's comparator_full.{log,time} to release_full/_aside/comparator_run1_killed/ (nothing deleted);
# 4. runs full_release.sh comparator unchanged (same pins, flags, lean.lock, nice 19, watchdog).
# AI-written 2026-11-13. Stops only its own children.
set -u
D=<build>; S=$D/release_core/scripts; RF=$D/release_full; H=<hb>
LOG=$RF/comparator_rerun.log
say() { echo "$(date -Is) $*" >> $LOG; }
say "start pid $$ (v4: v3 with the ERE parentheses escaped)"
while [ ! -f $H/basicfix.exit ]; do sleep 300; done
say "basicfix: $(grep 'BASICFIX RESULT' <basicfix>/basicfix.log | tail -1)"
# v3 (2026-11-13 22:20 UTC): basicfix's "basic" item is a false failure of its own check: the committed build_range.sh
# rebuilt RieszN7.Basic byte-identical to the deployed olean (be84f567...); only the S1 reference, compiled with
# --root and an absolute path, differs. So accept OK, or FAIL whose only item is "basic", and in both cases require
# both re-exports byte-identical and both axiom audits clean.
BF=<basicfix>/basicfix.log
R=$(grep 'BASICFIX RESULT' $BF | tail -1)
case "$R" in *"BASICFIX RESULT: OK"*|*"BASICFIX RESULT: FAIL basic") ;; *) say "basicfix not OK ($R): Comparator NOT relaunched"; exit 3 ;; esac
for k in "export full: .*= certified \\(identical\\)" "export core: .*= certified \\(identical\\)" \
         "AxiomsCore: 2 of 2" "AxiomsFull: 2 of 2" "Basic olean differs from the S1 committed-recipe rebuild|Basic olean = S1"; do
  grep -Eq "$k" $BF || { say "basicfix log lacks '$k': Comparator NOT relaunched"; exit 3; }
done
cmp -s <build>/.lake/build/lib/lean/RieszN7/Basic.olean <basicfix>/_aside/before/RieszN7/Basic.olean \
  || { say "Basic olean changed by the rebuild: Comparator NOT relaunched (investigate)"; exit 3; }
say "basicfix accepted: exports identical, axioms clean, Basic rebuilt by committed recipe = deployed bytes"
# Gate (condition of 2026-11-13): no process with "<other-build>" in its command line (cc1plus/lto1/ld of
# an unrelated C++ build on the machine; read-only pgrep, never touched) AND MemAvailable > 12 GB, both for 10 consecutive minutes.
ok=0
while [ $ok -lt 10 ]; do
  A=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
  if pgrep -f <other-build> >/dev/null || [ "$A" -le 12582912 ]; then ok=0; else ok=$((ok+1)); fi
  sleep 60
done
say "gate passed (10 min without <other-build> processes, MemAvailable > 12 GB; now $(awk '/^MemAvailable:/ {print $2}' /proc/meminfo) kB): starting"
mkdir -p $RF/_aside/comparator_run1_killed
for f in comparator_full.log comparator_full.time; do [ -f $RF/$f ] && mv $RF/$f $RF/_aside/comparator_run1_killed/; done
bash $S/full_release.sh comparator; RC=$?
say "full_release.sh comparator rc=$RC; $(grep -h 'COMPARATOR EXIT' $RF/full_release.log | tail -1)"
exit $RC
