#!/usr/bin/env bash
set -euo pipefail
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project="$(CDPATH= cd -- "$here/../.." && pwd)"
source_dir="$project/build/pinned-sm64"
out="$project/build/instrumentation/shell-gap"
python3 "$here/build_probe.py" "$out"
for version in US JP; do
  gcc -std=c99 -O2 -Wall -Wextra -Wno-unused-parameter -ffp-contract=off -fno-fast-math \
    -D"VERSION_$version" -DAVOID_UB -DNON_MATCHING \
    -I"$source_dir/include" -I"$source_dir/src" -I"$source_dir/lib/src" \
    -I"$source_dir" -I"$out" "$here/probe.c" -lm -o "$out/probe-${version,,}"
  "$out/probe-${version,,}"
done
