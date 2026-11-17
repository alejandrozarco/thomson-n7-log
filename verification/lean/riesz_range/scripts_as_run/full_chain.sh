#!/bin/bash
# full_chain.sh -- RieszN7.Full release checks on workstation slot 1, sequentially (2026-11-11; Full supersedes Core12):
#   hb nanoda_full:     full_release.sh build export   (four Release modules; lean4export of the Solution)
#   hb comparator_full: full_release.sh neg            (two Comparator negative controls)
#   hb nanoda_full:     full_release.sh nanoda         (second kernel + tampered-export control)
#   hb comparator_full: full_release.sh comparator     (main Comparator)
# Each full_release.sh run takes lean.lock itself (blocking flock). Stops at the first nonzero rc.
# Log: pub_range/release_full/chain.log.
H=<hb>; S=<build>/release_core/scripts; LOG=<build>/release_full/chain.log
say() { echo "$(date -Is) $*" >> $LOG; }
say "full_chain start pid $$"
for x in "nanoda_full build export" "comparator_full neg" "nanoda_full nanoda" "comparator_full comparator"; do
  set -- $x; N=$1; shift
  bash <ext>/hb.sh run $N bash $S/full_release.sh "$@"
  say "$N ($*): $(cat $H/$N.exit)"
  grep -q '^rc 0 ' $H/$N.exit || { say "stop"; exit 1; }
done
say "full_chain done"
