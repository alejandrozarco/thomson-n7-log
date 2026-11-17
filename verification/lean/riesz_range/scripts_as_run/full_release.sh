#!/bin/bash
# full_release.sh PHASE... -- release-grade checks of RieszN7.Full (s in [1/3, 7/4]) on the workstation, slot 1. Generated from
# core_release.sh (Core12) by renaming only: release_full/, full_* step names, RieszN7.Release.Full* modules,
# ThomsonN7Riesz.riesz_seven_range(_unique_range), comparator_full*.json.
# Phases (in the order given, all under ONE hold of <work>/lean.lock):
#   build       compile RieszN7.Release.{FullChallenge,FullSolution,FullNegStatement,FullNegAxiom}
#   export      lean4export of the two Solution theorems -> sk/riesz_seven_range.ndjson (+ sha256, size, decl count)
#   nanoda      nanoda on that export (accept), then on a copy with one large Nat literal +1 (must be rejected)
#   comparator  Comparator, comparator_full.json (Challenge vs Solution, permitted axioms, Lean kernel replay)
#   neg         Comparator on comparator_full_neg_{statement,axiom}.json (each must be rejected)
# Lock: flock is not FIFO. A first try with a 0.5 s `flock -n` poll lost every release for 5 min (2026-11-10 14:27-14:33):
# the ext queues' heavy modules wait in a blocking flock(2) and are woken at once on release. So: blocking flock (we
# then race the other blocked waiters on each release), after a free `flock -n` attempt; wait time is logged. Each step runs through
# run_step.sh (guarded.sh: nice 19, ionice idle, MemAvailable < 3 GB watchdog on its own process group).
# Log: release_core/core_release.log; step logs <logs>/full_<step>.{log,time,watchdog,peak,exit}.
set -u
source <build>/release_core/scripts/env_core.sh
S=$RC/scripts; RC=$D/release_full; LOG=$RC/full_release.log; W=$RC/sk; mkdir -p $W
say() { echo "$(date -Is) $*" | tee -a $LOG; }
step() { local n=$1; shift; bash $S/run_step.sh "$n" bash -c "source $S/env_core.sh; cd $D; $*" | tee -a $LOG; return ${PIPESTATUS[0]}; }
say "full_release start pid $$ phases: $*"
check_pins >> $LOG 2>&1 || { say "PIN CHECK FAILED"; exit 2; }
# Deferral (2026-11-10 17:30 UTC): with release_core/comparator_after_ext present, a run that includes the comparator
# phase first waits (without the lock) until both ext queues have exited (hb ext_cells.exit and ext_cap.exit), so the
# main Comparator run (est. 9-19 h of slot 1) does not stall the [1/3, 7/4] extension by more than about a day.
if [ -f $RC/comparator_after_ext ] && [[ " $* " == *" comparator "* ]]; then
  say "comparator deferred: waiting for <hb>/ext_cells.exit and ext_cap.exit"
  while [ ! -f <hb>/ext_cells.exit ] || [ ! -f <hb>/ext_cap.exit ]; do sleep 60; done
  say "ext queues exited: cells $(cat <hb>/ext_cells.exit); cap $(cat <hb>/ext_cap.exit)"
fi
exec 9><work>/lean.lock
T0=$(date +%s); flock -n 9 || flock 9
say "lean.lock acquired after $(( $(date +%s) - T0 )) s"
RCALL=0
THMS="ThomsonN7Riesz.riesz_seven_range ThomsonN7Riesz.riesz_seven_unique_range"
EXP=$W/riesz_seven_range.ndjson
nanoda_cfg() {  # $1 export, $2 pp_declars, $3 print_axioms, $4 num_threads  (as pub_local1/scripts/second-kernel.sh,
  # plus num_threads: nanoda_lib checks declarations in parallel; Comparator's own nanoda call uses 4)
  cat <<JSON
{ "export_file_path": "$1", "use_stdin": false, "num_threads": $4,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": $2, "pp_to_stdout": true, "print_axioms": $3, "print_success_message": true }
JSON
}
for PH in "$@"; do
  case $PH in
    build)
      for M in FullChallenge FullSolution FullNegStatement FullNegAxiom; do
        step full_build_$M "lake build RieszN7.Release.$M" || { say "BUILD FAILED $M"; RCALL=1; break 2; }
      done ;;
    export)
      step full_export "/usr/bin/time -v -o $W/export.time $LEAN4EXPORT RieszN7.Release.FullSolution -- $THMS > $EXP" \
        || { say "EXPORT FAILED"; RCALL=1; break; }
      ls -l $EXP | tee -a $LOG; sha256sum $EXP | tee $W/export.sha256 | tee -a $LOG
      wc -lc $EXP | tee -a $LOG ;;
    nanoda)
      nanoda_cfg $EXP '["ThomsonN7Riesz.riesz_seven_range","ThomsonN7Riesz.riesz_seven_unique_range"]' true 3 > $W/config.json
      step full_nanoda "$NANODA_BIN $W/config.json > $W/nanoda-accept.out 2> $W/nanoda-accept.err"
      if grep -q "with no errors" $W/nanoda-accept.out; then say "NANODA ACCEPT: $(grep 'with no errors' $W/nanoda-accept.out)"
      else say "NANODA DID NOT ACCEPT"; RCALL=1; break; fi
      read -r LIT NEW < <(python3 -I - "$EXP" <<'PY'
import re,sys,collections
c=collections.Counter(); order=[]
for line in open(sys.argv[1]):
    for m in re.finditer(r'"natVal":"(\d+)"', line):
        v=m.group(1)
        if v not in c: order.append(v)
        c[v]+=1
lit=next(v for v in order if len(v)>=15 and c[v]==1)
new=int(lit)+1
while str(new) in c: new+=1
print(lit, new)
PY
)
      say "negative control: literal $LIT -> $NEW"
      sed "s/\"natVal\":\"$LIT\"/\"natVal\":\"$NEW\"/" $EXP > $W/riesz_seven_range.tampered.ndjson
      cmp -l $EXP $W/riesz_seven_range.tampered.ndjson | wc -l | sed 's/^/changed bytes: /' | tee -a $LOG
      nanoda_cfg $W/riesz_seven_range.tampered.ndjson '[]' false 1 > $W/config.tampered.json
      step full_nanoda_tampered "$NANODA_BIN $W/config.tampered.json > $W/nanoda-tampered.out 2> $W/nanoda-tampered.err"; TR=$?
      if [ $TR = 0 ]; then say "NEGATIVE CONTROL FAILED: nanoda accepted the tampered export"; RCALL=1
      elif grep -q "panicked at src/parser.rs" $W/nanoda-tampered.err; then say "NEGATIVE CONTROL INCONCLUSIVE (parser)"; RCALL=1
      else say "NANODA TAMPERED REJECTED (rc $TR): $(grep -m1 panicked $W/nanoda-tampered.err) / $(grep -m1 assert $W/nanoda-tampered.err)"; fi
      mkdir -p $RC/_aside; mv $W/riesz_seven_range.tampered.ndjson $RC/_aside/ ;;
    comparator)
      step full_comparator "COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN /usr/bin/time -v -o $RC/comparator_full.time $COMPARATOR_BIN $RC/comparator_full.json > $RC/comparator_full.log 2>&1"; CR=$?
      say "COMPARATOR EXIT: $CR; $(grep -E 'Your solution is okay|kernel accepts|rejects' $RC/comparator_full.log | tr '\n' ' ')"
      [ $CR = 0 ] || RCALL=1 ;;
    neg)
      for c in neg_statement neg_axiom; do
        case $c in
          neg_statement) WANT="theorem statement do not match: 'ThomsonN7Riesz.riesz_seven_range'" ;;
          neg_axiom) WANT="Illegal axiom detected: 'ThomsonN7Riesz.full_cheat'" ;;
        esac
        step full_comparator_$c "COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN /usr/bin/time -v -o $RC/comparator_full_$c.time $COMPARATOR_BIN $RC/comparator_full_$c.json > $RC/comparator_full_$c.log 2>&1"; NR=$?
        if [ $NR != 0 ] && grep -qF "$WANT" $RC/comparator_full_$c.log && ! grep -q "Your solution is okay" $RC/comparator_full_$c.log; then
          say "COMPARATOR NEG $c REJECTED as expected (exit $NR): $WANT"
        else say "COMPARATOR NEG $c: NOT REJECTED AS EXPECTED (exit $NR; wanted: $WANT)"; RCALL=1; fi
      done ;;
    *) say "unknown phase $PH"; RCALL=1 ;;
  esac
done
flock -u 9; exec 9>&-
say "full_release end rc=$RCALL (lean.lock released)"
exit $RCALL
