#!/bin/bash
# Usage: guarded.sh <name> <command...>
# Runs <command> at nice 19 / ionice idle under /usr/bin/time -v, with a memory
# watchdog that kills ONLY this job's process group if MemAvailable < 3 GB.
# Logs: <logs>/<name>.{log,time,watchdog,pid,exit}
# Launch with: nohup setsid bash guarded.sh NAME cmd... >/dev/null 2>&1 &
set -u
source <work>/env.sh
NAME=$1; shift
L=<logs>
LIMIT_KB=$((3*1024*1024))
cd "$PROJ"
echo "start $(date -Is) cmd: $*" > "$L/$NAME.watchdog"
START=$(date +%s)
# setsid gives the job its own process group, so kill -- -PGID reaches lean
# children spawned by lake, and nothing else.
setsid nice -n 19 ionice -c3 /usr/bin/time -v -o "$L/$NAME.time" "$@" > "$L/$NAME.log" 2>&1 < /dev/null &
JOB=$!
echo "$JOB" > "$L/$NAME.pid"
echo "job pid/pgid=$JOB guard pid=$$" >> "$L/$NAME.watchdog"
MINAVAIL=999999999
while kill -0 "$JOB" 2>/dev/null; do
  AVAIL=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
  [ "$AVAIL" -lt "$MINAVAIL" ] && MINAVAIL=$AVAIL
  if [ "$AVAIL" -lt "$LIMIT_KB" ]; then
    echo "$(date -Is) MemAvailable=${AVAIL}kB < ${LIMIT_KB}kB -> killing job pgid $JOB" >> "$L/$NAME.watchdog"
    kill -TERM -- "-$JOB" 2>/dev/null
    sleep 5
    kill -KILL -- "-$JOB" 2>/dev/null
    echo "KILLED_BY_WATCHDOG" >> "$L/$NAME.watchdog"
    break
  fi
  sleep 10
done
wait "$JOB"; RC=$?
END=$(date +%s)
echo "$RC" > "$L/$NAME.exit"
echo "end $(date -Is) rc=$RC wall=$((END-START))s min_MemAvailable=${MINAVAIL}kB" >> "$L/$NAME.watchdog"
