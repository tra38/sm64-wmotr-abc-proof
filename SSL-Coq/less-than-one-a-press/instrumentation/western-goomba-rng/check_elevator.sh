#!/usr/bin/env bash
set -euo pipefail
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project="$(CDPATH= cd -- "$here/../.." && pwd)"
out="$project/build/instrumentation/western-goomba-rng/elevator-analysis"
mkdir -p "$out"

# Every singleton gets the same finite search budget. The target is the
# nearest point of the full base rectangle to its stock X/Z. Choosing this
# target does not claim that the search finds a globally shortest legal path.
# Triplet children cannot first spawn from the bucket under the checked
# stock-parent condition; testing fictitiously loaded children is separate.
target_x=(512 512 -511 512 512 -511)
target_z=(768 -255 768 768 -255 768)
for version in US JP; do
    tag="${version,,}"
    PROBE_VERSION="$version" PROBE_SANITIZE=1 bash "$here/run.sh" --scene "$out/elevator-$tag.csv" > "$out/scene-$tag.txt"
    binary="$project/build/instrumentation/western-goomba-rng/probe-$tag"
    "$binary" --stock-choices -3071 1928 4 2 1 "$out/west-direct-$tag.csv" 256 900 0 > "$out/west-direct-$tag.txt"
    for actor in 0 1 2 3 4 5; do
        "$binary" --stock-choices "${target_x[actor]}" "${target_z[actor]}" 8 "$actor" 1 \
            "$out/actor-$actor-$tag.csv" 128 900 1 > "$out/actor-$actor-$tag.txt"
        tail -n 2 "$out/actor-$actor-$tag.txt"
    done
done
cmp "$out/scene-us.txt" "$out/scene-jp.txt"
cmp "$out/elevator-us.csv" "$out/elevator-jp.csv"
cmp "$out/west-direct-us.txt" "$out/west-direct-jp.txt"
cmp "$out/west-direct-us.csv" "$out/west-direct-jp.csv"
for actor in 0 1 2 3 4 5; do
    cmp "$out/actor-$actor-us.txt" "$out/actor-$actor-jp.txt"
    cmp "$out/actor-$actor-us.csv" "$out/actor-$actor-jp.csv"
done
echo 'PASS: six bounded source searches, nine-actor census, direct rim test and elevator trace agree in US/JP'
