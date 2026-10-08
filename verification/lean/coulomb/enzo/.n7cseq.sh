#!/bin/bash
# N = 7 Coulomb package (copy of pub_n5/.n5seq.sh): `lake build +Module` one module at a time in the order of $1 (one per lean.lock acquisition,
# guarded.sh memory watchdog, nice 19 via env.sh conventions). Status in N7C_STATUS, per-module results in lakeseq.tsv.
source <buildroot>/env.sh
T=<workspace>; cd $T; ORDER=$1
L=<buildroot>/logs
n=0; N=$(wc -l < $ORDER)
while read f; do
  n=$((n+1)); m=${f%.lean}; m=${m//\//.}
  echo "RUNNING lakeseq $n/$N $m $(date +%H:%M)" > N7C_STATUS
  exec 9><buildroot>/lean.lock; flock 9
  bash <buildroot>/guarded.sh n7c_cur bash -c "cd $T && timeout --foreground -k 20 10800 lake build +$m"
  exec 9>&-
  rc=$(cat $L/n7c_cur.exit); w=$(grep -o "wall=[0-9]*s" $L/n7c_cur.watchdog | tr -dc 0-9); pk=$(grep "Maximum resident" $L/n7c_cur.time | tr -dc 0-9)
  printf "%s\t%s\t%s\t%s\n" "$f" "$rc" "$w" "$pk" >> lakeseq.tsv
  if [ "$rc" != 0 ] || grep -q KILLED_BY_WATCHDOG $L/n7c_cur.watchdog; then cp $L/n7c_cur.log logs_n7c_fail.log; echo "FAIL lakeseq $m $(date +%H:%M)" > N7C_STATUS; exit 1; fi
done < $ORDER
echo "DONE $ORDER $(date +%H:%M)" > N7C_STATUS
