#!/bin/bash
# s1_basic_variants.sh -- S1 part 2c (2026-11-13). s1_recipe.sh matched Preamble, Base, Rpow byte for byte, but the
# deployed RieszN7.Basic olean (built 2026-11-07 20:24 UTC by an uncommitted pre-v1 build_range.sh, same source sha
# 9d965b9c...) differs from a rebuild with the committed build_range recipe. This rebuilds Basic from the git-HEAD copy
# against the deployed imports with a few flag variants, to find the recipe that reproduces the deployed bytes:
#   A: lean (defaults)        B: lean -j1        C: lean -DElab.async=false        D: A with LEAN_NUM_THREADS unset
# Result lines "[variants] ..." in s1check/s1.log. Run under hb.sh (name s1_check4); takes lean.lock. AI-written.
set -u
W=<s1check>; LOG=$W/s1.log; N=<deps>; R=<build>
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
say() { echo "$(date -Is) [variants] $*" >> $LOG; }
PK=""; for p in $N/.lake/packages/*; do PK=$PK:$p/.lake/build/lib/lean; done
DEPLOY=$R/.lake/build/lib/lean:$N/.lake/build/lib/lean$PK
D=$R/.lake/build/lib/lean/RieszN7/Basic.olean
exec 9><work>/lean.lock; flock 9; say "start pid $$, lean.lock acquired; deployed $(sha256sum < $D | cut -c1-16)"
O=$W/out_variants; mkdir -p $O
hit=""
for V in A B C D; do
  case $V in
    A) FL=""; TH="LEAN_NUM_THREADS=1" ;;
    B) FL="-j1"; TH="LEAN_NUM_THREADS=1" ;;
    C) FL="-DElab.async=false"; TH="LEAN_NUM_THREADS=1" ;;
    D) FL=""; TH="" ;;
  esac
  bash <work>/guarded.sh s1v_$V env LEAN_PATH=$DEPLOY $TH \
    $LEAN --root=$W/src $FL -o $O/Basic_$V.olean -i $O/Basic_$V.ilean $W/src/RieszN7/Basic.lean
  if cmp -s $O/Basic_$V.olean $D; then r=identical; hit="$hit $V"; else r=DIFFERENT; fi
  say "variant $V (flags '$FL' $TH) exit=$(awk '{print $NF}' <logs>/s1v_$V.exit 2>/dev/null) fresh=$(sha256sum < $O/Basic_$V.olean | cut -c1-16) olean $r"
done
[ -n "$hit" ] && say "S1 BASIC VARIANTS: deployed bytes reproduced by variant(s)$hit" || say "S1 BASIC VARIANTS: no variant reproduces the deployed bytes"
