#!/bin/bash
# N = 7 Coulomb: sequential module build (.n7cseq.sh .order.txt), lake build --no-build, axioms, Comparator,
# second kernel (lean4export + nanoda, with the negative control). Heavy steps under lean.lock and guarded.sh.
# Template: pub_n5/.n5chain_v4.sh. Tools: the pinned checkouts in pubtest_log/.tools (no downloads).
source <buildroot>/env.sh; export PATH=$HOME/.cargo/bin:$PATH
T=<workspace>; cd $T; export TOOLS=<tools>
L=<buildroot>/logs
: > lakeseq.tsv
bash .n7cseq.sh .order.txt || exit 1
lake build --no-build > nobuild.log 2>&1 || { echo "FAIL lake build --no-build" > N7C_STATUS; exit 1; }
( exec 9><buildroot>/lean.lock; flock 9; bash <buildroot>/guarded.sh n7c_axioms bash -c "cd $T && lake env lean -j1 -DElab.async=false CoulN7/Check/Axioms.lean" )
cp $L/n7c_axioms.log axioms.log
R="[axioms: $(grep -c 'propext, Classical.choice, Quot.sound' axioms.log)/2]"
echo "RUNNING comparator $(date +%H:%M) $R" > N7C_STATUS
( exec 9><buildroot>/lean.lock; flock 9; bash <buildroot>/guarded.sh n7c_comparator bash -c "cd $T && TOOLS=$TOOLS bash scripts/run_comparator.sh comparator_coul.json" )
R="$R [comparator: $(grep -h 'COMPARATOR EXIT' $L/n7c_comparator.log | tail -1)]"
echo "RUNNING second-kernel $(date +%H:%M) $R" > N7C_STATUS
( exec 9><buildroot>/lean.lock; flock 9; bash <buildroot>/guarded.sh n7c_sk bash -c "cd $T && TOOLS=$TOOLS TARGET=coul bash scripts/second-kernel.sh" )
R="$R [sk: $(grep -h 'SECOND KERNEL' $L/n7c_sk.log | tail -1)]"
echo "DONE $(date +%H:%M) $R" > N7C_STATUS
