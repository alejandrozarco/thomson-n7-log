#!/bin/bash
# final_full.sh -- parent (2026-11-11): full-range [1/3, 7/4] assembly. Waits until the 7 chain modules
# RieszN7.Range.CellsFull.* and the 21 cap pieces RieszN7.Cap.P*.Closed have exit 0 in build.tsv (latest entry), then
# builds Range.CapFull, MainFull, Check.AxiomsFull through build_range.sh. Never holds lean.lock while waiting.
# Run under <ext>/hb.sh (heartbeat final_full).
cd <build> || exit 1
LOG=<logs>/final_full.log; TSV=<build>/build.tsv
echo "$(date -u +%FT%T) start pid $$" >> $LOG
ok() { awk -F'\t' -v m="$1" '$1==m {rc=$2} END {exit !(rc=="0")}' $TSV; }
NEED=""
for c in Case1 S99_98 S98_96 S96_94 S94_93 S93_915 S915_90; do NEED="$NEED RieszN7.Range.CellsFull.$c"; done
for P in P1o3_3o8 P3o8_5o12 P5o12_11o24 P11o24_1o2 P1o2_13o24 P13o24_7o12 P7o12_2o3 P2o3_17o24 P17o24_3o4 P3o4_5o6 P5o6_11o12 P11o12_1o1 P1o1_13o12 P13o12_7o6 P7o6_5o4 P5o4_4o3 P4o3_17o12 P17o12_3o2 P3o2_19o12 P19o12_5o3 P5o3_7o4; do NEED="$NEED RieszN7.Cap.$P.Closed"; done
last=""
while :; do
  miss=""; for m in $NEED; do ok $m || miss="$miss $m"; done
  [ -z "$miss" ] && break
  n=$(echo $miss | wc -w); [ "$n" != "$last" ] && echo "$(date -u +%FT%T) waiting: $n missing:$miss" >> $LOG; last=$n
  # give up waiting (nonzero exit -> alert) if both ext queues have exited and inputs are still missing
  [ -f <hb>/ext_cells.exit ] && [ -f <hb>/ext_cap.exit ] && { echo "$(date -u +%FT%T) ext queues exited, still missing:$miss" >> $LOG; exit 3; }
  sleep 300
done
echo "$(date -u +%FT%T) assembling" >> $LOG
bash build_range.sh RieszN7.Range.CapFull RieszN7.MainFull RieszN7.Check.AxiomsFull >> <logs>/final_full.out 2>&1; rc=$?
echo "$(date -u +%FT%T) done rc=$rc" >> $LOG
grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <logs>/rg_RieszN7_Check_AxiomsFull.log || rc=4
exit $rc
