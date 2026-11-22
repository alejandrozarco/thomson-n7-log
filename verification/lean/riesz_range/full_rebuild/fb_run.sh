#!/bin/bash
# fb_run.sh -- full Lean rebuild of riesz_range/ from a fresh clone of the published tag v2.8 (AI-written 2026-11-20).
# Phase A: README route (regen.sh, checksums, lake exe cache get), Lake build of the 23 ThomsonGen/LogLean modules one
# at a time. Phase B: fb_sched.py builds the 5 080 RieszN7 modules with the recorded recipe (two slots).
# Phase C: byte comparison of every olean/ilean with the checked build, and the axiom output.
# Writes only under <fresh>. Reads the deployed trees (<build>, <deps>) only.
# Kills nothing except its own children's process groups (fb_sched.py).
set -u
R=<fresh>
W=$R/repo/riesz_range/lean
LOG=$R/fb.log
LOCK=<work>/lean.lock
PUBR=<build>
PUBN=<deps>
mkdir -p $R/cache $R/tmp $R/alogs
export PATH=$HOME/.elan/bin:$PATH XDG_CACHE_HOME=$R/cache MATHLIB_CACHE_DIR=$R/cache/mathlib LAKE_CACHE_DIR=$R/cache/lake TMPDIR=$R/tmp
unset LEAN_NUM_THREADS LEAN_PATH
say() { echo "$(date -u +%FT%TZ) $*" >> $LOG; }
loadgate() { while [ "$(awk '{print int($1)}' /proc/loadavg)" -ge 8 ]; do sleep 60; done; }
memgate() { while [ "$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)" -lt $1 ]; do sleep 60; done; }
# step NAME LOCK(0/1) CMD: nice 19, ionice idle, own process group, time -v; log in alogs/NAME.*
step() {
  local n=$1 lk=$2; shift 2
  loadgate
  say "step $n start (lock=$lk): $*"
  local pre=""; [ $lk = 1 ] && pre="flock $LOCK"
  ( cd $W && $pre setsid nice -n 19 ionice -c3 /usr/bin/time -v -o $R/alogs/$n.time bash -c "$*" > $R/alogs/$n.log 2>&1 < /dev/null )
  local rc=$?
  say "step $n rc=$rc wall=$(awk '/Elapsed \(wall/ {print $NF}' $R/alogs/$n.time 2>/dev/null) maxrss_kB=$(awk -F': ' '/Maximum resident/ {print $2}' $R/alogs/$n.time 2>/dev/null)"
  return $rc
}
say "start pid $$"
if [ ! -d $R/repo ]; then
  git clone -q --depth 1 --branch v2.8 https://github.com/alejandrozarco/thomson-n7-log $R/repo || { say "STOP: clone failed"; exit 1; }
fi
say "clone: $(git -C $R/repo log --oneline -1) tag $(git -C $R/repo describe --tags)"
( cd $W; echo "uname: $(uname -srm)"; echo "lean-toolchain: $(cat lean-toolchain)"; lake --version; lean --version
  echo "lean binary sha256: $(sha256sum $(elan which lean) | cut -d' ' -f1)"; python3 --version; nproc; free -g | head -2 ) >> $LOG 2>&1

if [ ! -f $R/phaseA.done ]; then
  step regen 0 "./regen.sh" || { say "STOP at regen"; exit 1; }
  step sums 0 "sha256sum -c SHA256SUMS upstream_regenerated.sha256"; RS=$?
  say "sha256sum -c: $(grep -c ': OK$' $R/alogs/sums.log) OK, $(grep -vc ': OK$' $R/alogs/sums.log) other lines (rc $RS)"
  [ $RS = 0 ] || { say "STOP at checksums"; exit 1; }
  step cacheget 1 "lake exe cache get" || { say "STOP at cache get"; exit 1; }
  tail -3 $R/alogs/cacheget.log >> $LOG
  # the 23 non-RieszN7 modules of build_order.txt, one Lake invocation each (no parallel heavy modules)
  for M in $(grep -v '^RieszN7\.' $W/build_order.txt); do
    memgate 13631488   # 13 GiB: the largest of these (ThomsonGen.T4) peaked at 9.8 GB
    step lake_$M 1 "lake build $M" || { say "STOP at lake build $M"; exit 1; }
  done
  touch $R/phaseA.done
fi

say "phase B start"
python3 -I $R/fb_sched.py >> $LOG 2>&1; RB=$?
say "phase B rc=$RB"
[ $RB = 0 ] || { say "STOP after phase B"; exit 1; }

say "phase C: olean/ilean comparison"
T=$R/cmp_all.tsv; printf 'module\tkind\tfresh_sha256\tchecked_sha256\tresult\n' > $T
B=$W/.lake/build/lib/lean
while read -r M; do
  F=${M//.//}
  case $M in RieszN7.*) D=$PUBR;; *) D=$PUBN;; esac
  for k in olean ilean; do
    f=$B/$F.$k; d=$D/.lake/build/lib/lean/$F.$k
    hf=$(sha256sum < $f 2>/dev/null | cut -d' ' -f1); hd=$(sha256sum < $d 2>/dev/null | cut -d' ' -f1)
    if [ ! -f $f ]; then r=missing-fresh; elif [ ! -f $d ]; then r=missing-checked; elif [ "$hf" = "$hd" ]; then r=identical; else r=DIFFERENT; fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$M" $k "$hf" "$hd" $r >> $T
  done
done < $W/build_order.txt
say "comparison: $(awk -F'\t' 'NR>1 {c[$5" "$2]++} END {for (k in c) printf "%s=%d; ", k, c[k]}' $T)"
say "RieszN7 oleans identical: $(awk -F'\t' 'NR>1 && $1 ~ /^RieszN7\./ && $2=="olean" && $5=="identical"' $T | wc -l) of $(grep -c '^RieszN7\.' $W/build_order.txt)"
for A in AxiomsFull AxiomsCore; do say "axiom output $A:"; cat $R/mlogs/RieszN7.Check.$A.log >> $LOG; done
grep -h -i -E 'sorry|error' $R/mlogs/*.log | sort | uniq -c | head -20 >> $LOG
say "DONE"
