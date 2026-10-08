#!/bin/bash
# Emit the (re-rounded, facially reduced) Coulomb cap certificate as TCertN into $COULN7_LEAN/CoulN7/Cap/, then the
# per-block checks. Stops at the first failing command and exits nonzero.
set -euo pipefail
cd "$(dirname "$0")"; NUM=${COULN7_NUMERICS:-$(cd ../.. && pwd)}; LOGD=${LOGD:-../logs}; mkdir -p $LOGD
OMP_NUM_THREADS=1 nice -n 19 python3 emit_tcert.py $NUM/cap1/cert_cap_coulomb_D12_short.json Cap --tcertn > $LOGD/emit_Cap.log 2>&1 \
  || { echo "Cap emit FAILED (see $LOGD/emit_Cap.log)"; exit 1; }
grep -q "EMIT_TCERTN Cap ALL_OK" $LOGD/emit_Cap.log || { echo "Cap emit not ALL_OK"; exit 1; }
echo "Cap emit ALL_OK"
OMP_NUM_THREADS=1 nice -n 19 python3 gen_capchk.py Cap > $LOGD/capchk_Cap.log 2>&1 || { echo "capchk FAILED"; exit 1; }
echo "capchk ok"
OMP_NUM_THREADS=1 nice -n 19 python3 gen_split.py Cap --tcertn > $LOGD/split_Cap.log 2>&1 || { echo "split FAILED"; exit 1; }
echo "split ok"
