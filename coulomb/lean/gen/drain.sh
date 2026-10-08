#!/bin/bash
# drain.sh <listfile>: compile the modules of <listfile> (one per line, dotted names) in order with mcheck.sh (olean),
# skipping modules whose olean is newer than the source and than every listed predecessor built in this run;
# stops at the first failure. Status lines to stdout.
G=$(cd "$(dirname "$0")" && pwd); P=${COULN7_LEAN:-$HOME/claude_projects/thomson-n7-log-macbuild/lean}
while read M; do
  [ -z "$M" ] && continue; case "$M" in \#*) continue;; esac
  F=$P/${M//.//}.lean; O=$P/.lake/build/lib/lean/${M//.//}.olean
  if [ -f "$O" ] && [ "$O" -nt "$F" ] && [ -z "$REBUILT" ]; then echo "$M skip"; continue; fi
  r=$($G/mcheck.sh $M olean | tail -1); echo "$M $r"
  case "$r" in *"rc=0 "*) REBUILT=1;; *) echo "STOP at $M"; exit 1;; esac
done < "$1"
echo DONE
