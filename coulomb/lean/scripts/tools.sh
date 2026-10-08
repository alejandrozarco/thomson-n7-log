# Sourced by run_comparator.sh and second-kernel.sh (a copy of lean/scripts/tools.sh of alejandrozarco/thomson-n7-log). Fetches and builds the pinned external checkers into $TOOLS (default: .tools/).
# Same pins as the verification record of the Coulomb formalisation (huwngtran/thomson-n7-lean).
EXPORT_REV=076e8e57707e813375e8f9da8bf989799ace9680       # leanprover/lean4export, format 3.1.0
NANODA_REV=3a2407216ee84a75f9e1aead6803d0578be06ae7       # ammkrn/nanoda_lib 0.4.19
COMPARATOR_REV=fd5d5bcf14177b187f66d4502071268d877887c3   # leanprover/comparator; builds with its own toolchain
TOOLS="${TOOLS:-$ROOT/.tools}"; mkdir -p "$TOOLS"; TOOLS="$(cd "$TOOLS" && pwd)"

fetch() {  # fetch <dir> <url> <rev>
  if [ ! -d "$TOOLS/$1/.git" ]; then git clone --quiet "$2" "$TOOLS/$1"; fi
  git -C "$TOOLS/$1" checkout --quiet "$3"
  [ "$(git -C "$TOOLS/$1" rev-parse HEAD)" = "$3" ] || { echo "$1 is not at the pinned revision $3"; exit 1; }
}
need_lean4export() {
  fetch lean4export https://github.com/leanprover/lean4export "$EXPORT_REV"
  # lean4export must run on the Lean version that wrote the .olean files, so it is built with this project's
  # lean-toolchain (a one-line change in the tools checkout).
  if ! cmp -s "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; then
    cp "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; rm -rf "$TOOLS/lean4export/.lake/build"
  fi
  (cd "$TOOLS/lean4export" && lake build)
  LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"
}
need_nanoda() {
  fetch nanoda_lib https://github.com/ammkrn/nanoda_lib.git "$NANODA_REV"
  (cd "$TOOLS/nanoda_lib" && cargo build --release)
  NANODA_BIN="$TOOLS/nanoda_lib/target/release/nanoda_bin"
}
need_comparator() {
  fetch comparator https://github.com/leanprover/comparator "$COMPARATOR_REV"
  (cd "$TOOLS/comparator" && lake build)
  COMPARATOR_BIN="$TOOLS/comparator/.lake/build/bin/comparator"
}
