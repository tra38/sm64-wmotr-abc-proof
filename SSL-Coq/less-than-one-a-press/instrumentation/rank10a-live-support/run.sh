#!/usr/bin/env bash
set -euo pipefail
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
source_dir="${SM64_SOURCE_DIR:-$project_dir/../../../reference-sm64-decomp}"
out="$project_dir/build/instrumentation/rank10a-live-support"
version="${PROBE_VERSION:-US}"
case "$version" in US|JP) ;; *) echo "PROBE_VERSION must be US or JP" >&2; exit 1;; esac
mkdir -p "$out"
python3 "$script_dir/build_probe.py" "$source_dir" "$out"
gcc -std=c99 -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-function \
    -ffp-contract=off -fno-fast-math -fno-strict-aliasing \
    -fsanitize=undefined -fno-sanitize-recover=all \
    -D"VERSION_$version" -DAVOID_UB -DNON_MATCHING \
    -I"$source_dir/include" -I"$source_dir/src" -I"$source_dir/lib/src" \
    -I"$source_dir" -I"$out" "$script_dir/probe.c" -lm -o "$out/probe-${version,,}"
"$out/probe-${version,,}" | tee "$out/result-${version,,}.json"
