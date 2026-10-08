#!/usr/bin/env bash
# Second-kernel check: export the two theorems of CoulN7/Solution.lean (TARGET=coul; the N = 5 targets s2/s1 of the
# template are kept but have no sources here)
# with lean4export and check the export with nanoda
# (an independent implementation of the Lean 4 type checker, in Rust). Negative control: a copy of the export with one
# large natural-number literal changed by +1 must be rejected.
# Needs a built workspace (lake build), git, cargo, network for the first clone. Output: logs/second-kernel/.
# Usage: bash scripts/second-kernel.sh   (CONTROL_ONLY=1: rerun only the negative control on an existing accepted export)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
source scripts/tools.sh
need_lean4export; need_nanoda
W="$ROOT/logs/second-kernel"; mkdir -p "$W"
case "${TARGET:-s2}" in
  coul) MOD=CoulN7.Solution; NS=ThomsonN7S1; T1=coulomb_seven; NAME=coulomb_seven; W="$W/coul"; mkdir -p "$W";;
  s2) MOD=N5R2.Solution; NS=FivePointsRiesz2; T1=five_riesz2; NAME=five_riesz2;;
  s1) MOD=N5R1.Solution; NS=FivePointsCoulomb; T1=five_coulomb; NAME=five_coulomb; W="$W/s1"; mkdir -p "$W";;
  *) echo "TARGET must be s2, s1 or coul"; exit 1;;
esac
THMS="$NS.$T1 $NS.${T1}_unique"
EXP="$W/$NAME.ndjson"
cfg() {  # $1 = export path, $2 = pp_declars, $3 = print_axioms
  cat <<JSON
{ "export_file_path": "$1", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": $2, "pp_to_stdout": true, "print_axioms": $3, "print_success_message": true }
JSON
}
if [ "${CONTROL_ONLY:-0}" != 1 ]; then
lake env "$LEAN4EXPORT" "$MOD" -- $THMS > "$EXP"
wc -lc "$EXP"; python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), sys.argv[1].split("/")[-1])' "$EXP" | tee "$W/export.sha256"
cfg "$EXP" "[\"$NS.$T1\",\"$NS.${T1}_unique\"]" true > "$W/config.json"
printf '\n== nanoda on the export (expected: axioms propext, Quot.sound, Classical.choice; "Checked N declarations with no errors")\n'
"$NANODA_BIN" "$W/config.json" | tee "$W/nanoda-accept.out"
fi
grep -q "with no errors" "$W/nanoda-accept.out" || { echo "SECOND KERNEL DID NOT ACCEPT"; exit 1; }
# Negative control: the first natural-number literal with at least 15 digits that occurs exactly once in the export,
# changed to the smallest larger value that does not occur as a literal anywhere in the export (a value that already
# occurs would make the parser reject a duplicate expression before any type checking).
read -r LIT NEW < <(python3 - "$EXP" <<'PY'
import re,sys,collections
c=collections.Counter(); order=[]
for m in re.finditer(r'"natVal":"(\d+)"', open(sys.argv[1]).read()):
    v=m.group(1)
    if v not in c: order.append(v)
    c[v]+=1
lit=next(v for v in order if len(v)>=15 and c[v]==1)
new=int(lit)+1
while str(new) in c: new+=1
print(lit, new)
PY
)
printf '\n== negative control: literal %s changed to %s\n' "$LIT" "$NEW"
sed "s/\"natVal\":\"$LIT\"/\"natVal\":\"$NEW\"/" "$EXP" > "$W/$NAME.tampered.ndjson"
cfg "$W/$NAME.tampered.ndjson" '[]' false > "$W/config.tampered.json"
if "$NANODA_BIN" "$W/config.tampered.json" > "$W/nanoda-tampered.out" 2> "$W/nanoda-tampered.err"; then
  echo "NEGATIVE CONTROL FAILED: nanoda accepted the tampered export"; exit 1
elif grep -q "panicked at src/parser.rs" "$W/nanoda-tampered.err"; then
  # nanoda reports type errors by panicking in the type checker (e.g. assert_def_eq in src/tc.rs); a panic in the
  # parser means the export was rejected before type checking, which does not test the checker.
  echo "NEGATIVE CONTROL INCONCLUSIVE: nanoda's parser rejected the export before type checking"; tail -n 3 "$W/nanoda-tampered.err"; exit 1
else
  echo "negative control ok: nanoda rejected the tampered export"; tail -n 3 "$W/nanoda-tampered.err"
fi
printf '\nSECOND KERNEL: OK (export accepted, tampered export rejected)\n'
