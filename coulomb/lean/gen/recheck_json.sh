#!/bin/bash
# Re-run the exact Lean-semantics simulation + JSON comparison (--check-only) for the cap and the five slabs, and the
# negative controls of neg_compare.py. Stops at the first failure; exit status nonzero on failure.
set -eu
G=$(cd "$(dirname "$0")" && pwd); NUM=$G/../..; LOGD=${LOGD:-$G/../logs}; mkdir -p $LOGD; cd $G
export OMP_NUM_THREADS=1
nice -n 19 python3 neg_compare.py > $LOGD/neg_compare.log 2>&1; echo "neg_compare rc=0"
nice -n 19 python3 emit_tcert.py $NUM/cap1/cert_cap_coulomb_D12_short.json Cap --tcertn --check-only > $LOGD/recheck_Cap.log 2>&1
echo "Cap recheck rc=0"
for p in "99_98 S9998 D10" "98_96 S9896 D10" "96_94 S9694 D12" "94_93 S9493 D12" "93_90 S9390 D12"; do
  set -- $p
  nice -n 19 python3 emit_tcert.py $NUM/cells1/certs/cert_slab_$1_coulomb_$3.json $2 --check-only > $LOGD/recheck_$2.log 2>&1
  echo "$2 recheck rc=0"
done
echo RECHECK_ALL_OK
