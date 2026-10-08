#!/bin/bash
# Regenerate every certificate-derived CoulN7 module from the certificate JSONs into $COULN7_LEAN/CoulN7/ (default:
# the Mac build workspace). Order: Case 1 (emit_cert3.py), slabs, cap, minorants (gen_minor1.py), specs/claims
# (gen_spec1.py slabs case1 cap — the cap spec is requested explicitly). Stops and exits nonzero on any failure.
# Compare the result with ../CoulN7/SHA256SUMS (all generated modules regenerate byte-identically, 2026-10-08).
# Needs cap1/cert_cap_coulomb_D12_short.json (gunzip -k cap1/cert_cap_coulomb_D12_short.json.gz).
set -euo pipefail
cd "$(dirname "$0")"; NUM=${COULN7_NUMERICS:-$(cd ../.. && pwd)}; LOGD=${LOGD:-../logs}; mkdir -p $LOGD
export OMP_NUM_THREADS=1
nice -n 19 python3 emit_cert3.py $NUM/cells1/certs/cert_case1_coulomb_D10.json > $LOGD/emit_case1.log 2>&1 \
  || { echo "Case 1 emit FAILED"; exit 1; }
grep -q "CHECK ALL_OK" $LOGD/emit_case1.log || { echo "Case 1 emit not ALL_OK"; exit 1; }
echo "Case 1 emit ALL_OK"
./run_emit_slabs.sh
./run_emit_cap.sh
nice -n 19 python3 gen_minor1.py > $LOGD/gen_minor1.log 2>&1 || { echo "gen_minor1 FAILED"; exit 1; }
echo "minorants ok"
nice -n 19 python3 gen_spec1.py slabs case1 cap > $LOGD/gen_spec1.log 2>&1 || { echo "gen_spec1 FAILED"; exit 1; }
echo "specs ok"
echo REGEN_ALL_OK
