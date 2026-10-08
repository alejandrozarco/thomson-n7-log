#!/bin/bash
# mcheck.sh <Module.Path> [olean]  -- compile one module of the Mac build workspace, one Lean job at a time.
# Lock: mkdir $P/.mcheck.lock (waits). Own process group, nice 10, /usr/bin/time -l; memory watchdog stops ONLY this
# job's process group if system free memory < 8 %. Log: numerics/n7_interval/lean/logs/<Module>.log, final line
# "MCHECK rc=… wall=… peak_rss=…".  Never pattern-kills anything.
P=${COULN7_LEAN:-$HOME/claude_projects/thomson-n7-log-macbuild/lean}
LOGD=$(cd "$(dirname "$0")/.." && pwd)/logs; mkdir -p $LOGD
M=$1; F=$P/${M//.//}.lean; L=$LOGD/$M.log
export PATH=$HOME/.elan/bin:$PATH
until mkdir $P/.mcheck.lock 2>/dev/null; do
  o=$(cat $P/.mcheck.lock/pid 2>/dev/null); if [ -n "$o" ] && ! kill -0 $o 2>/dev/null; then rm -rf $P/.mcheck.lock; fi; sleep 3; done
echo $$ > $P/.mcheck.lock/pid
trap 'rm -rf $P/.mcheck.lock' EXIT
cd $P
OUT=""; if [ "$2" = olean ]; then d=.lake/build/lib/lean/$(dirname ${M//.//}); mkdir -p $d
  OUT="-o .lake/build/lib/lean/${M//.//}.olean -i .lake/build/lib/lean/${M//.//}.ilean"; fi
t0=$(date +%s)
nice -n 10 python3 -c 'import os,sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])' \
  /usr/bin/time -l lake env lean -j1 -DElab.async=false $OUT $F > $L 2>&1 &
J=$!; echo $J > $LOGD/$M.pid
while kill -0 $J 2>/dev/null; do
  FR=$(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/ {print $2+0}')
  if [ -n "$FR" ] && [ "$FR" -lt 8 ]; then echo "WATCHDOG free ${FR}% -> kill pgid $J" >> $L; kill -TERM -- -$J; sleep 3; kill -KILL -- -$J 2>/dev/null; fi
  sleep 3
done
wait $J; rc=$?
pk=$(awk '/maximum resident set size/ {print $1}' $L)
echo "MCHECK rc=$rc wall=$(( $(date +%s) - t0 ))s peak_rss=$((pk/1048576))MB" >> $L
tail -1 $L
exit $rc
