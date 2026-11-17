#!/bin/bash
# final_core.sh -- parent (2026-11-08): M-core assembly. Waits until the 7 cell chain modules RieszN7.Range.Cells.*
# and the 14 core cap pieces RieszN7.Cap.P*.Closed have exit 0 in build.tsv (latest entry), then builds Range.Cap,
# MainCore, Check.AxiomsCore through build_range.sh. Never holds lean.lock while waiting.
cd <build> || exit 1
LOG=<logs>/final_core.log; TSV=<build>/build.tsv
echo "$(date -u +%FT%T) start pid $$" >> $LOG
ok() { awk -F'\t' -v m="$1" '$1==m {rc=$2} END {exit !(rc=="0")}' $TSV; }
NEED="RieszN7.Range.Cells.Case1 RieszN7.Range.Cells.S99_98 RieszN7.Range.Cells.S98_96 RieszN7.Range.Cells.S96_94 RieszN7.Range.Cells.S94_93 RieszN7.Range.Cells.S93_915 RieszN7.Range.Cells.S915_90"
for P in P1o2_13o24 P13o24_7o12 P7o12_2o3 P2o3_17o24 P17o24_3o4 P3o4_5o6 P5o6_11o12 P11o12_1o1 P1o1_13o12 P13o12_7o6 P7o6_5o4 P5o4_4o3 P4o3_17o12 P17o12_3o2; do NEED="$NEED RieszN7.Cap.$P.Closed"; done
while :; do
  miss=""; for m in $NEED; do ok $m || miss="$miss $m"; done
  [ -z "$miss" ] && break
  echo "$(date -u +%FT%T) waiting:$(echo $miss | wc -w) missing" >> $LOG; sleep 600
done
echo "$(date -u +%FT%T) assembling" >> $LOG
bash build_range.sh RieszN7.Range.Cap RieszN7.MainCore RieszN7.Check.AxiomsCore >> <logs>/final_core.out 2>&1
echo "$(date -u +%FT%T) done rc=$?" >> $LOG
