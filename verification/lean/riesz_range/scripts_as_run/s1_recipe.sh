#!/bin/bash
# s1_recipe.sh -- S1 part 2b (2026-11-13). s1_check.sh v2 rebuilt the four trusted modules with build_range.sh flags
# against fresh imports; Rpow matched byte for byte, but Preamble/Base were originally built by Lake (pub_n7c), which
# uses a different recipe (default elaboration, -c, --setup <json>, --json), so their oleans differ, and Basic then
# differs through its imports. This check rebuilds EACH module from its git-HEAD copy (s1check/src) with the SAME recipe
# that produced the deployed olean and against the SAME deployed imports, writing to s1check/out_recipe/:
#   ThomsonGen.Preamble, ThomsonGen.Base: Lake's command from pub_n7c/.lake/build/lib/lean/ThomsonGen/<M>.trace
#     (same LEAN_PATH, lean binary, the deployed --setup json; cwd pub_n7c-like root = s1check/src);
#   RieszN7.Core.Rpow, RieszN7.Basic: build_range.sh's command (lean -j1 -DElab.async=false, LEAN_PATH = pub_range +
#     pub_n7c + packages, --root = s1check/src).
# Byte-identical oleans for all four, module by module against the deployed imports, tie the deployed closure to the
# git sources by induction (packages are pinned checkouts). Result "S1 RECIPE RESULT: OK/FAIL" in s1check/s1.log.
# Run under hb.sh (name s1_check3) after hb/s1_check2.exit; takes lean.lock. AI-written 2026-11-13.
set -u
W=<s1check>; LOG=$W/s1.log; N=<deps>; R=<build>; L=<logs>
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
say() { echo "$(date -Is) [recipe] $*" >> $LOG; }
say "start pid $$"
while [ ! -f <hb>/s1_check2.exit ]; do sleep 60; done
exec 9><work>/lean.lock; flock 9; say "lean.lock acquired"
O=$W/out_recipe; mkdir -p $O/ThomsonGen $O/RieszN7/Core $O/ir
fail=""
for m in Preamble Base; do
  LP=$(python3 -I -c "import json,sys; t=json.load(open(sys.argv[1])); m=t['log'][0]['message']; print(m.split('LEAN_PATH=')[1].split()[0])" $N/.lake/build/lib/lean/ThomsonGen/$m.trace)
  ( cd $W/src && bash <work>/guarded.sh s1r_$m env LEAN_PATH=$LP $LEAN --root=$W/src $W/src/ThomsonGen/$m.lean \
      -o $O/ThomsonGen/$m.olean -i $O/ThomsonGen/$m.ilean -c $O/ir/$m.c --setup $N/.lake/build/ir/ThomsonGen/$m.setup.json --json )
  D=$N/.lake/build/lib/lean/ThomsonGen/$m.olean
  if cmp -s $O/ThomsonGen/$m.olean $D; then r=identical; else r=DIFFERENT; fail="$fail ThomsonGen/$m"; fi
  say "ThomsonGen/$m (Lake recipe) exit=$(awk '{print $NF}' $L/s1r_$m.exit 2>/dev/null) fresh=$(sha256sum < $O/ThomsonGen/$m.olean | cut -c1-16) deployed=$(sha256sum < $D | cut -c1-16) olean $r"
done
PK=""; for p in $N/.lake/packages/*; do PK=$PK:$p/.lake/build/lib/lean; done
DEPLOY=$R/.lake/build/lib/lean:$N/.lake/build/lib/lean$PK
for M in RieszN7/Core/Rpow RieszN7/Basic; do
  bash <work>/guarded.sh s1r_${M//\//_} env LEAN_PATH=$DEPLOY LEAN_NUM_THREADS=1 \
    $LEAN --root=$W/src -j1 -DElab.async=false -o $O/$M.olean -i $O/$M.ilean $W/src/$M.lean
  D=$R/.lake/build/lib/lean/$M.olean
  if cmp -s $O/$M.olean $D; then r=identical; else r=DIFFERENT; fail="$fail $M"; fi
  say "$M (build_range recipe) exit=$(awk '{print $NF}' $L/s1r_${M//\//_}.exit 2>/dev/null) fresh=$(sha256sum < $O/$M.olean | cut -c1-16) deployed=$(sha256sum < $D | cut -c1-16) olean $r"
done
[ -z "$fail" ] && say "S1 RECIPE RESULT: OK (all four oleans byte-identical to rebuilds from git sources)" || say "S1 RECIPE RESULT: FAIL$fail"
[ -z "$fail" ]
