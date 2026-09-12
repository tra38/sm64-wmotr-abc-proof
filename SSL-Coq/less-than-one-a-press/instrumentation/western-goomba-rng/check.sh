#!/usr/bin/env bash
set -euo pipefail
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project="$(CDPATH= cd -- "$here/../.." && pwd)"
out="$project/build/instrumentation/western-goomba-rng"
for version in US JP; do
    PROBE_VERSION="$version" PROBE_SANITIZE=1 bash "$here/run.sh" --vertical
    "$out/probe-${version,,}" --vertical-pauses
    "$out/probe-${version,,}" 1 1
    "$out/probe-${version,,}" --replay-west "$out/west-replay-${version,,}.csv"
done
cmp "$out/west-replay-us.csv" "$out/west-replay-jp.csv"
echo "PASS: US/JP source diagnostics, undefined-behavior checks and granted-choice replay"
