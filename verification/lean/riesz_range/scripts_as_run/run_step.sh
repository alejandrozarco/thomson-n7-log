#!/bin/bash
# run_step.sh NAME CMD...  -- one Core12 release step on the workstation: guarded.sh (nice 19, ionice idle, /usr/bin/time -v,
# kills only its own process group if MemAvailable < 3 GB) plus a sampler of the job's total session RSS
# (peak -> <logs>/NAME.peak). The caller holds the lean lock.
L=<logs>; NAME=$1; shift
S=$(date +%s)
( while :; do [ -f $L/$NAME.pid ] && [ $(stat -c %Y $L/$NAME.pid) -ge $S ] && break; sleep 1; done
  J=$(cat $L/$NAME.pid); P=0; A0=999999999
  while kill -0 "$J" 2>/dev/null; do
    R=$(ps -o rss= --sid "$J" 2>/dev/null | awk '{s+=$1} END {print s+0}'); [ "$R" -gt $P ] && P=$R
    A=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo); [ "$A" -lt $A0 ] && A0=$A
    echo "peak_session_rss_kB=$P min_MemAvailable_kB=$A0 $(date -Is)" > $L/$NAME.peak; sleep 5
  done ) &
MON=$!
bash <work>/guarded.sh "$NAME" "$@"
wait $MON
RC=$(cat $L/$NAME.exit)
echo "$(date -Is) step $NAME rc=$RC $(tail -1 $L/$NAME.watchdog | sed 's/^end [^ ]* //') $(cat $L/$NAME.peak) $(awk -F': ' '/Maximum resident/ {print "max_rss_kB="$2}' $L/$NAME.time)"
exit $RC
