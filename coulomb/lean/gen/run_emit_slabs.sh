#!/bin/bash
# Emit the five Coulomb slab certificates (TCert) into $COULN7_LEAN/CoulN7/<Slab>/, then the per-block split checks.
# Stops at the first failing command and exits nonzero (emit_tcert.py exits 1 unless its simulation is ALL_OK).
set -euo pipefail
cd "$(dirname "$0")"; NUM=${COULN7_NUMERICS:-$(cd ../.. && pwd)}; C=$NUM/cells1/certs; LOGD=${LOGD:-../logs}; mkdir -p $LOGD
for p in "99_98 S9998 D10" "98_96 S9896 D10" "96_94 S9694 D12" "94_93 S9493 D12" "93_90 S9390 D12"; do
  set -- $p
  OMP_NUM_THREADS=1 nice -n 19 python3 emit_tcert.py $C/cert_slab_$1_coulomb_$3.json $2 > $LOGD/emit_$2.log 2>&1 \
    || { echo "$2 emit FAILED (see $LOGD/emit_$2.log)"; exit 1; }
  grep -q "EMIT_TCERT $2 ALL_OK" $LOGD/emit_$2.log || { echo "$2 emit not ALL_OK"; exit 1; }
  echo "$2 emit ALL_OK"
  OMP_NUM_THREADS=1 nice -n 19 python3 gen_split.py $2 > $LOGD/split_$2.log 2>&1 || { echo "$2 split FAILED"; exit 1; }
  echo "$2 split ok"
done
