# Sourced by the Core12 release scripts on the workstation (installed in <build>/release_core/scripts).
# pub_range is not a Lake workspace: its oleans are built by raw `lean` (build_range.sh) with imports resolved against
# pub_n7c's packages. Same LEAN_PATH and lean binary as build_range.sh. Tools: the pinned checkout used for pub_local1
# (<tools>; revisions of pub_local1/scripts/tools.sh, checked below).
source <work>/env.sh
D=<build>; N=<deps>; RC=$D/release_core
LP=$D/.lake/build/lib/lean:$N/.lake/build/lib/lean
for p in $N/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
export LEAN_PATH=$LP
export PATH=$RC/scripts/shim:$HOME/.elan/bin:$PATH
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
TOOLS=<tools>
LEAN4EXPORT=$TOOLS/lean4export/.lake/build/bin/lean4export
NANODA_BIN=$TOOLS/nanoda_lib/target/release/nanoda_bin
COMPARATOR_BIN=$TOOLS/comparator/.lake/build/bin/comparator
COMPARATOR_LANDRUN=$TOOLS/comparator/scripts/fake-landrun.sh
check_pins() {
  local ok=1
  for x in "lean4export 076e8e57707e813375e8f9da8bf989799ace9680" "nanoda_lib 3a2407216ee84a75f9e1aead6803d0578be06ae7" \
           "comparator fd5d5bcf14177b187f66d4502071268d877887c3"; do
    set -- $x; local h; h=$(git -C $TOOLS/$1 rev-parse HEAD)
    if [ "$h" = "$2" ]; then echo "pin ok: $1 $h"; else echo "PIN MISMATCH: $1 $h != $2"; ok=0; fi
  done
  echo "lean4export toolchain: $(cat $TOOLS/lean4export/lean-toolchain); comparator toolchain: $(cat $TOOLS/comparator/lean-toolchain)"
  sha256sum $LEAN4EXPORT $NANODA_BIN $COMPARATOR_BIN $LEAN
  [ $ok = 1 ]
}
