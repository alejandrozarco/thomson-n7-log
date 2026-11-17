#!/bin/sh
# fetch_bulk.sh: fetch and verify the bulk data of riesz_range/ (certificates, per-piece reports and the re-rounded
# cap certificates of the Lean development), which are kept in a separate Zenodo archive and not in git.
#
# Usage (from anywhere inside a clone of the repository):
#   sh riesz_range/fetch_bulk.sh                  download the archive from the Zenodo record below
#   sh riesz_range/fetch_bulk.sh PATH             use a local copy of riesz_range_bulk_v2.8.tar (or a directory
#                                                 that contains it)
#   sh riesz_range/fetch_bulk.sh URL              download the archive from URL
#   sh riesz_range/fetch_bulk.sh --exports [SRC]  also fetch the two compressed Lean kernel exports into
#                                                 riesz_range/exports/ (0.58 GB; 3.5 GB when decompressed);
#                                                 SRC is a local directory or a URL prefix that holds the .xz files
#                                                 (default: the Zenodo record). Not needed for range_check.py.
#
# The archive's sha256 is checked before it is unpacked, it is unpacked into the repository root (all its paths
# start with riesz_range/), and then every file it contains is checked against riesz_range/BULK_SHA256SUMS. The last
# line printed is "BULK OK ..." or "BULK FAIL ...", and the exit status is 0 only for OK.
# Needs: a POSIX sh, tar, curl or wget (for downloads), and sha256sum or shasum.

set -u

# Zenodo record of the bulk archive: set at release (record number, e.g. 12345678).
ZENODO_RECORD=REPLACE_AT_RELEASE

ARCHIVE=riesz_range_bulk_v2.8.tar
ARCHIVE_SHA256=e7fedde5e7b0a683f20334bb104ec763bdfde01cd604b9576d7882f3cecc9b1c
ARCHIVE_SIZE=452655616
NFILES=286
EXPORTS="riesz_seven_range.ndjson.xz:2817d61623cb9e18f5664ebab11d78f8294f9d9cf2016472e56d22a05730bab0 riesz_seven_core.ndjson.xz:e92f21cf94cd969144cfbff6041ff435e48f89f94d03e300571234c11cfa8715"

fail() { echo "BULK FAIL: $*"; exit 1; }

here=$(cd "$(dirname "$0")" && pwd) || fail "cannot locate the script directory"
root=$(cd "$here/.." && pwd) || fail "cannot locate the repository root"
[ -f "$root/riesz_range/BULK_SHA256SUMS" ] || fail "riesz_range/BULK_SHA256SUMS not found next to this script"

if command -v sha256sum >/dev/null 2>&1; then SHA="sha256sum"
elif command -v shasum >/dev/null 2>&1; then SHA="shasum -a 256"
else fail "neither sha256sum nor shasum found"; fi

sha_of() { $SHA "$1" | awk '{print $1}'; }

download() {  # download URL to FILE
    if command -v curl >/dev/null 2>&1; then curl -fL --retry 3 -o "$2" "$1"
    elif command -v wget >/dev/null 2>&1; then wget -O "$2" "$1"
    else echo "neither curl nor wget found" >&2; return 1; fi
}

zenodo_url() {  # zenodo_url NAME
    case "$ZENODO_RECORD" in
        REPLACE_AT_RELEASE) return 1 ;;
    esac
    echo "https://zenodo.org/records/$ZENODO_RECORD/files/$1?download=1"
}

want_exports=0
if [ "${1:-}" = "--exports" ]; then want_exports=1; shift; fi
src=${1:-}

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/fetch_bulk.XXXXXX") || fail "mktemp failed"
trap 'rm -rf "$tmpdir"' EXIT INT TERM

# ---- the exports (optional) ----
if [ "$want_exports" -eq 1 ]; then
    mkdir -p "$root/riesz_range/exports" || fail "cannot create riesz_range/exports"
    for e in $EXPORTS; do
        name=${e%%:*}; want=${e#*:}; dst="$root/riesz_range/exports/$name"
        case "$src" in
            http://*|https://*) download "${src%/}/$name" "$dst.part" || fail "download of $name failed" ;;
            "") url=$(zenodo_url "$name") || fail "no Zenodo record set in this script; pass a directory or URL prefix"
                download "$url" "$dst.part" || fail "download of $name failed" ;;
            *)  [ -f "$src/$name" ] || fail "$src/$name not found"
                cp "$src/$name" "$dst.part" || fail "copy of $name failed" ;;
        esac
        got=$(sha_of "$dst.part")
        [ "$got" = "$want" ] || { rm -f "$dst.part"; fail "$name: sha256 $got, expected $want"; }
        mv "$dst.part" "$dst"
        echo "export OK: riesz_range/exports/$name (sha256 $want)"
    done
    echo "EXPORTS OK: 2 files in riesz_range/exports/ (decompress with xz -d; the decompressed sha256 are listed in riesz_range/README.md)"
    exit 0
fi

# ---- the archive ----
case "$src" in
    http://*|https://*)
        tarfile="$tmpdir/$ARCHIVE"; download "$src" "$tarfile" || fail "download failed: $src" ;;
    "")
        url=$(zenodo_url "$ARCHIVE") || fail "no Zenodo record set in this script (ZENODO_RECORD); pass the path or URL of $ARCHIVE"
        tarfile="$tmpdir/$ARCHIVE"; download "$url" "$tarfile" || fail "download failed: $url" ;;
    *)
        if [ -d "$src" ]; then tarfile="$src/$ARCHIVE"; else tarfile=$src; fi
        [ -f "$tarfile" ] || fail "$tarfile not found" ;;
esac

got=$(sha_of "$tarfile")
[ "$got" = "$ARCHIVE_SHA256" ] || fail "archive sha256 $got, expected $ARCHIVE_SHA256 ($ARCHIVE, $ARCHIVE_SIZE bytes)"
echo "archive OK: $ARCHIVE (sha256 $ARCHIVE_SHA256)"

# every member must be a regular path under riesz_range/
bad=$(tar -tf "$tarfile" | awk '!/^riesz_range\// || /(^|\/)\.\.(\/|$)/' | head -n 1)
[ -z "$bad" ] || fail "unexpected path in the archive: $bad"

(cd "$root" && tar -xf "$tarfile") || fail "unpacking failed"

nbad=$(cd "$root" && $SHA -c riesz_range/BULK_SHA256SUMS 2>&1 | grep -v ': OK$' | tee "$tmpdir/bad.txt" | wc -l | tr -d ' ')
nlist=$(grep -c . "$root/riesz_range/BULK_SHA256SUMS")
if [ "$nbad" -eq 0 ] && [ "$nlist" -eq "$NFILES" ]; then
    echo "BULK OK: $nlist files verified against riesz_range/BULK_SHA256SUMS"
    exit 0
fi
head -n 20 "$tmpdir/bad.txt"
fail "$nbad problem line(s) checking riesz_range/BULK_SHA256SUMS ($nlist lines, expected $NFILES)"
