#!/usr/bin/env bash
set -euo pipefail
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project="$(CDPATH= cd -- "$here/../.." && pwd)"
out="$project/build/instrumentation/tweester-transport"
version="${PROBE_VERSION:-US}"
bash "$here/run.sh" contact
binary="$out/probe-${version,,}"
for warmup in 15 20 45 60 90; do
    printf 'RUN,warmup=%s,horizon=9000,angleStep=512,stopAtContact=1\n' "$warmup"
    WARMUP="$warmup" HORIZON=9000 AVOID_CONTACT=1 "$binary"
done
printf 'RUN,warmup=30,horizon=9000,angleStep=64,actor=0,stopAtContact=1\n'
WARMUP=30 HORIZON=9000 ANGLE_STEP=64 ACTOR=0 AVOID_CONTACT=1 "$binary"
