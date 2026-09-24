#!/usr/bin/env bash
set -euo pipefail
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project="$(CDPATH= cd -- "$here/../.." && pwd)"
source_dir="$project/build/pinned-sm64"
out="$project/build/instrumentation/tweester-transport"
version="${PROBE_VERSION:-US}"
case "$version" in US|JP) ;; *) exit 2;; esac
mkdir -p "$out"
python3 "$here/build_probe.py" "$source_dir" "$out"
gcc -std=c99 -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-function \
    -ffp-contract=off -fno-fast-math -fno-strict-aliasing \
    -D"VERSION_$version" -DAVOID_UB -DNON_MATCHING \
    -I"$source_dir/include" -I"$source_dir/src" -I"$source_dir/lib/src" \
    -I"$source_dir" -I"$out" "$here/probe.c" -lm -o "$out/probe-${version,,}"
"$out/probe-${version,,}" "$@"
