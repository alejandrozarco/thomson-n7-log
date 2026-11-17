#!/bin/bash
# m2_tamper.sh -- Fable review M2 (2026-11-12): nanoda tamper control on this project's own data. Waits (no lock) for
# hb s1_check.exit (which itself waits for comparator_full), then under lean.lock + guarded.sh: picks a unique >= 15-digit
# literal owned by a RieszN7.Cap.*/Cells.* declaration (m2_pick.py, extension piece preferred), changes it by +1 in a
# copy of the Full export, and requires nanoda to reject the copy in the type checker (not the parser).
# Result line "M2 RESULT: ..." in <m2>/m2.log. Run under hb.sh (name m2_tamper).
set -u
M=<m2>; LOG=$M/m2.log; SK=<build>/release_full/sk; EXP=$SK/riesz_seven_range.ndjson
NANODA=<tools>/nanoda_lib/target/release/nanoda_bin
say() { echo "$(date -Is) $*" >> $LOG; }
say "start pid $$"
while [ ! -f <hb>/s1_check.exit ]; do sleep 120; done
say "s1_check exited: $(cat <hb>/s1_check.exit)"
exec 9><work>/lean.lock; flock 9; say "lean.lock acquired"
sha256sum -c $SK/export.sha256 >> $LOG 2>&1 || { say "M2 RESULT: FAIL (export sha256 mismatch)"; exit 1; }
bash <work>/guarded.sh m2_pick bash -c "python3 -I $M/m2_pick.py $EXP > $M/pick.txt"
read -r LIT NEW DECL LINE < $M/pick.txt || true
[ -n "${LIT:-}" ] || { say "M2 RESULT: FAIL (no candidate literal)"; exit 1; }
say "literal (${#LIT} digits, export line $LINE, owning declaration $DECL): ${LIT:0:24}... -> +1"
sed "${LINE}s/\"natVal\":\"$LIT\"/\"natVal\":\"$NEW\"/" $EXP > $M/tampered.ndjson
say "changed bytes: $(cmp -l $EXP $M/tampered.ndjson | wc -l)"
sed "s#\"export_file_path\": \"[^\"]*\"#\"export_file_path\": \"$M/tampered.ndjson\"#" $SK/config.tampered.json > $M/config.json
bash <work>/guarded.sh m2_nanoda bash -c "$NANODA $M/config.json > $M/nanoda.out 2> $M/nanoda.err"
TR=$(cat <logs>/m2_nanoda.exit)
if [ "$TR" = 0 ]; then say "M2 RESULT: FAIL (nanoda accepted the tampered export)"; R=1
elif grep -q "panicked at src/parser.rs" $M/nanoda.err; then say "M2 RESULT: INCONCLUSIVE (parser panic)"; R=1
else say "M2 RESULT: REJECTED as required (rc $TR): $(grep -m1 panicked $M/nanoda.err) / $(grep -m1 assert $M/nanoda.err)"; R=0; fi
mkdir -p $M/_aside; mv $M/tampered.ndjson $M/_aside/
exit $R
