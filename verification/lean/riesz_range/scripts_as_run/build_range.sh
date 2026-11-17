#!/bin/bash
# Usage: bash <build>/build_range.sh [--skip-built] MOD [MOD ...]   (MOD dotted, e.g. RieszN7.Core.Rpow)
# Builds the given modules of the RieszN7 range port one at a time, in the order given (caller supplies a
# topological order). Each module: under a lean lock (flock) and guarded.sh (nice 19, ionice idle,
# MemAvailable < 3 GB watchdog, own process group), `lean -j1 -DElab.async=false`, LEAN_NUM_THREADS=1.
# Extra per-module cap: if the job's process group RSS exceeds the slot's cap the job's own process
# group (PGID read from logs/<NAME>.pid) is stopped (TERM, then KILL) and the module is logged as RSS_CAP_KILL.
# Imports resolve read-only against pub_n7c's built packages and oleans (ThomsonGen, LogLean, Mathlib);
# outputs go to pub_range/.lake/build/lib/lean/RieszN7/... Stops at the first failure unless KEEP_GOING=1.
# Summary lines: <build>/build.tsv (module, exit, wall_s, peak_rss_kB, user_s, date).
#
# v2 (THROUGHPUT agent, 2026-11-08; user-approved second workstation slot + remote workers). Installed by atomic mv, so
# build_range.sh processes started earlier keep running v1 from their open inode. Changes:
# - Two slots. Slot 1 = <work>/lean.lock (shared with other projects), cap RSS_CAP_KB (9 GiB).
#   Slot 2 = <work>/lean2.lock (RieszN7 only), cap RSS_CAP2_KB (5.5 GiB). A module whose expected workstation
#   peak (tp/expect.py: build.tsv history, else its class, max over its RieszN7 imports) is <= 5 GiB polls both
#   locks and takes slot 2 only if MemAvailable >= expected + 4 GiB; heavier/unknown modules block on slot 1.
#   A slot-2 job is stopped if it exceeds its cap or MemAvailable < 4 GiB (protects slot 1); it is then requeued
#   for slot 1 at once and nothing is written to build.tsv for that attempt (tp/slots.tsv records it).
# - Remote builds (two other machines, tp/dispatch.py): while pub_range/remote_claims/<MOD> exists and is fresh
#   (heartbeat < 600 s), wait (max 3 h, no lock held); then skip MOD if tp/fresh.py says its olean came from a
#   remote build (build_remote.tsv sha256 match) and is newer than its source and its RieszN7 imports' oleans.
#   The dispatcher appends the remote module's build.tsv line itself.
# - Lookahead mode (tp/lookahead_d.sh): SLOT2_ONLY=1 builds light modules in slot 2 only (heavy ones and slot-2
#   kills are left to the queues, nothing written to build.tsv); TP_IGNORE_CLAIM=1 skips the claim wait.
# - Option --skip-built (before the modules): skip a module whose latest build.tsv line has rc 0 and whose olean is
#   newer than its source and its RieszN7 imports' oleans (tp/fresh.py --built); for restarting long queues.
# - Queue state for the dispatcher: pub_range/qstate/<PID>.todo (argument list), <PID>.cur (index, module).
set -u
D=<build>
N=<deps>
L=<logs>
TP=<tp>
CAP=${RSS_CAP_KB:-9437184}
CAP2=${RSS_CAP2_KB:-5767168}
LIGHT=${SLOT2_MAX_EXPECT_KB:-5242880}
MARGIN=${SLOT2_MARGIN_KB:-4194304}
YIELD=${SLOT2_YIELD_AVAIL_KB:-4194304}
LP=$D/.lake/build/lib/lean:$N/.lake/build/lib/lean
for p in $N/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
SKIPB=0
while [ $# -gt 0 ] && [ "${1#--}" != "$1" ]; do
  case "$1" in --skip-built) SKIPB=1 ;; *) echo "build_range.sh: unknown option $1" >&2 ;; esac; shift
done
Q=$D/qstate
mkdir -p $Q $D/remote_claims
printf '%s\n' "$@" > $Q/$$.todo
memav() { awk '/^MemAvailable:/ {print $2}' /proc/meminfo; }
I=0
for M in "$@"; do
  I=$((I+1)); echo "$I $M $(date +%s)" > $Q/$$.cur
  F=${M//.//}
  NAME=rg_${M//./_}
  O=$D/.lake/build/lib/lean/$F
  mkdir -p "$(dirname "$O")"
  C=$D/remote_claims/$M; W0=$(date +%s)
  while [ "${TP_IGNORE_CLAIM:-0}" != 1 ] && [ -f "$C" ] && [ $(( $(date +%s) - $(stat -c %Y "$C" 2>/dev/null || echo 0) )) -lt 600 ] \
        && [ $(( $(date +%s) - W0 )) -lt 10800 ]; do sleep 15; done
  if [ $SKIPB = 1 ] && python3 -I $TP/fresh.py --built "$M" 2>/dev/null; then
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" skip "$$" "-" "skip-built: rc 0, olean current" "$(date -Is)" >> $TP/slots.tsv
    continue
  fi
  if python3 -I $TP/fresh.py "$M" 2>/dev/null; then
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" skip "$$" "-" "remote olean current" "$(date -Is)" >> $TP/slots.tsv
    continue
  fi
  E=$(python3 -I $TP/expect.py "$M" 2>/dev/null | cut -f2); [[ "$E" =~ ^[0-9]+$ ]] || E=99999999
  if [ "${SLOT2_ONLY:-0}" = 1 ] && [ "$E" -gt "$LIGHT" ]; then continue; fi
  FORCE1=0
  while :; do
    T0=$(date +%s)
    rm -f $L/$NAME.slot
    (
      SLOT=1
      if [ $FORCE1 = 0 ] && [ "$E" -le "$LIGHT" ]; then
        while :; do
          if [ "${SLOT2_ONLY:-0}" != 1 ]; then
            exec 9><work>/lean.lock
            if flock -n 9; then SLOT=1; break; fi
          fi
          exec 9><work>/lean2.lock
          if [ "$(memav)" -ge $((E+MARGIN)) ] && flock -n 9; then
            if [ "$(memav)" -ge $((E+MARGIN)) ]; then SLOT=2; break; fi
          fi
          exec 9>&-
          sleep 5
        done
      else
        exec 9><work>/lean.lock
        flock 9
      fi
      echo $SLOT > $L/$NAME.slot
      if [ $SLOT = 2 ]; then MYCAP=$CAP2; KTAG=SLOT2_RSS_CAP; else MYCAP=$CAP; KTAG=RSS_CAP_KILL; fi
      # RSS cap monitor for this job (started once the lock is held, so it watches only our job)
      (
        S=$(date +%s)
        while :; do
          if [ -f $L/$NAME.pid ] && [ $(stat -c %Y $L/$NAME.pid) -ge $S ]; then break; fi
          sleep 1
        done
        J=$(cat $L/$NAME.pid)
        while kill -0 "$J" 2>/dev/null; do
          R=$(ps -o rss= --sid "$J" 2>/dev/null | awk '{s+=$1} END {print s+0}')
          if [ "$R" -gt "$MYCAP" ]; then
            echo "$(date -Is) $KTAG rss=${R}kB > ${MYCAP}kB pgid=$J" >> $L/$NAME.watchdog
            kill -TERM -- "-$J" 2>/dev/null; sleep 5; kill -KILL -- "-$J" 2>/dev/null
            break
          fi
          if [ $SLOT = 2 ]; then
            A=$(memav)
            if [ "$A" -lt "$YIELD" ]; then
              echo "$(date -Is) SLOT2_MEM_YIELD MemAvailable=${A}kB < ${YIELD}kB pgid=$J" >> $L/$NAME.watchdog
              kill -TERM -- "-$J" 2>/dev/null; sleep 5; kill -KILL -- "-$J" 2>/dev/null
              break
            fi
          fi
          sleep 2
        done
      ) &
      MON=$!
      bash <work>/guarded.sh "$NAME" bash -c \
        "cd $D && LEAN_PATH=$LP LEAN_NUM_THREADS=1 $LEAN -j1 -DElab.async=false -o $O.olean -i $O.ilean $F.lean"
      wait $MON 2>/dev/null
    )
    SLOT=$(cat $L/$NAME.slot 2>/dev/null || echo 1)
    RC=$(cat $L/$NAME.exit 2>/dev/null || echo NA)
    WALL=$(awk -F': ' '/Elapsed \(wall clock\)/ {n=split($2,a,":"); s=0; for(i=1;i<=n;i++) s=s*60+a[i]; printf "%.0f", s}' $L/$NAME.time 2>/dev/null)
    USR=$(awk -F': ' '/User time/ {printf "%.0f", $2}' $L/$NAME.time 2>/dev/null)
    RSS=$(awk -F': ' '/Maximum resident/ {print $2}' $L/$NAME.time 2>/dev/null)
    if [ "$SLOT" = 2 ] && grep -qE 'SLOT2_RSS_CAP|SLOT2_MEM_YIELD|KILLED_BY_WATCHDOG' $L/$NAME.watchdog; then
      K=$(grep -oE 'SLOT2_RSS_CAP|SLOT2_MEM_YIELD|KILLED_BY_WATCHDOG' $L/$NAME.watchdog | tail -1)
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" "slot2-requeue:$K" "$E" "$WALL" "$RSS" "$(date -Is)" >> $TP/slots.tsv
      cp -f $L/$NAME.watchdog $L/$NAME.slot2.watchdog 2>/dev/null
      FORCE1=1
      [ "${SLOT2_ONLY:-0}" = 1 ] && break
      continue
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" "slot$SLOT" "$E" "$WALL" "$RSS" "$(date -Is)" >> $TP/slots.tsv
    break
  done
  # lookahead mode: slot-2 kills and failures are left to the queue (nothing in build.tsv; tp/slots.tsv has them)
  if [ "${SLOT2_ONLY:-0}" = 1 ] && { [ $FORCE1 = 1 ] || [ "$RC" != 0 ]; }; then
    [ "$RC" != 0 ] && printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" "lookahead-rc:$RC" "$E" "$WALL" "$RSS" "$(date -Is)" >> $TP/slots.tsv
    continue
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$M" "$RC" "$WALL" "$RSS" "$USR" "$(date -Is)" >> $D/build.tsv
  if grep -qE 'KILLED_BY_WATCHDOG|RSS_CAP_KILL' $L/$NAME.watchdog; then
    echo "$M KILLED $(grep -oE 'KILLED_BY_WATCHDOG|RSS_CAP_KILL' $L/$NAME.watchdog | tail -1)" >> $D/build.tsv
    [ "${KEEP_GOING:-0}" = 1 ] || exit 1
  fi
  [ "$RC" = 0 ] || [ "${KEEP_GOING:-0}" = 1 ] || exit 1
done
[ "${SLOT2_ONLY:-0}" = 1 ] || echo "ALL_DONE $*" | cut -c1-300 >> $D/build.tsv
