#!/usr/bin/env bash
set -euo pipefail
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
source_dir="${SM64_SOURCE_DIR:-$project_dir/../../../reference-sm64-decomp}"
out="$project_dir/build/instrumentation/western-goomba-rng"
version="${PROBE_VERSION:-US}"
case "$version" in US|JP) ;; *) echo "PROBE_VERSION must be US or JP" >&2; exit 1;; esac
binary="$out/probe-${version,,}"
sanitize=()
if [[ "${PROBE_SANITIZE:-0}" == 1 ]]; then sanitize=(-fsanitize=undefined -fno-sanitize-recover=all); fi
mkdir -p "$out"
python3 "$script_dir/build_probe.py" "$source_dir" "$out"
gcc -std=c99 -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-function \
    -ffp-contract=off -fno-fast-math -fno-strict-aliasing \
    "${sanitize[@]}" -D"VERSION_$version" -DAVOID_UB -DNON_MATCHING -I"$source_dir/include" -I"$source_dir/src" \
    -I"$source_dir/lib/src" -I"$source_dir" -I"$out" \
    "$script_dir/probe.c" -lm -o "$binary"
"$binary" "$@"
