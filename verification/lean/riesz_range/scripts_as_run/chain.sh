#!/bin/bash
# chain.sh -- after run 1 (hb nanoda_core: core_release.sh build export) exits rc 0, run on workstation slot 1:
#   hb comparator_core: core_release.sh neg          (two Comparator negative controls, light; checks the pipeline)
#   hb nanoda_core:     core_release.sh nanoda       (second kernel on the export + tampered-export control)
#   hb comparator_core: core_release.sh comparator   (main Comparator run)
# Each core_release.sh run takes lean.lock itself. Stops at the first nonzero rc. Log: release_core/chain.log.
H=<hb>; S=<build>/release_core/scripts; LOG=<build>/release_core/chain.log
say() { echo "$(date -Is) $*" >> $LOG; }
say "chain start pid $$"
while [ ! -f $H/nanoda_core.exit ]; do sleep 20; done
say "run 1 exit: $(cat $H/nanoda_core.exit)"
grep -q '^rc 0 ' $H/nanoda_core.exit || { say "run 1 failed, stop"; exit 1; }
for x in "comparator_core neg" "nanoda_core nanoda" "comparator_core comparator"; do
  set -- $x
  bash <ext>/hb.sh run $1 bash $S/core_release.sh $2
  say "$1 ($2): $(cat $H/$1.exit)"
  grep -q '^rc 0 ' $H/$1.exit || { say "stop"; exit 1; }
done
say "chain done"
