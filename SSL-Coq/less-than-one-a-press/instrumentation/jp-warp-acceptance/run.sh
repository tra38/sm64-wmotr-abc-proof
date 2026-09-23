#!/usr/bin/env bash
set -euo pipefail
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
rom="${1:?usage: $0 /path/to/authentic/baserom.jp.z64}"
python3 "$project_dir/instrumentation/jp-ranks13-18/verify.py" "$rom"
bash "$project_dir/instrumentation/jp-rank5-state-split/verify.sh" "$rom"
if grep -Eq 'DebugMemWrite|\bW32\b|\bW16\b|\bW8\b' "$script_dir/probe.c"; then
    printf '%s\n' 'refusing a probe with a game-memory write API' >&2
    exit 3
fi
mkdir -p "$project_dir/build/instrumentation/jp-warp-acceptance"
out="$(mktemp -d "$project_dir/build/instrumentation/jp-warp-acceptance/run.XXXXXX")"
mkdir -p "$out/config" "$out/data" "$out/shots"
gcc -shared -fPIC -std=c99 -Wall -Wextra -Werror -O2 \
    -DALLOW_SETUP_A=0 -DSEARCH_MODE=12 \
    -DRANK1_BOUNDARY_AUDIT=1 -DRANK1_BOUNDARY_REPEAT_UNTIL=349 \
    -DRANK5_STATE_SPLIT_AUDIT=1 -DRANK13_18_COPY_AUDIT=1 \
    "$script_dir/probe.c" -ldl -lm -o "$out/probe.so"
printf 'Output: %s\n' "$out"
printf 'run\n' | XDG_CONFIG_HOME="$out/config" XDG_DATA_HOME="$out/data" \
    LIBGL_ALWAYS_SOFTWARE=1 xvfb-run -a "${MUPEN64PLUS:-/usr/games/mupen64plus}" \
        --debug --emumode 0 --nosaveoptions --nospeedlimit \
        --audio dummy --input "$out/probe.so" --gfx mupen64plus-video-rice.so \
        --rsp mupen64plus-rsp-hle.so --cheats 6 --sshotdir "$out/shots" \
        --testshots 2850 "$rom" >"$out/raw.log" 2>&1
grep -a '^WARP_ACCEPT_' "$out/raw.log" >"$out/receipt.txt"
grep -a '^RANK5_' "$out/raw.log" >"$out/rank5.txt"
grep -a '^RANK13_' "$out/raw.log" >"$out/rank13.txt"
diff --strip-trailing-cr -u \
    "$project_dir/instrumentation/jp-rank5-state-split/expected-state-split-receipt.txt" "$out/rank5.txt"
diff --strip-trailing-cr -u \
    "$project_dir/instrumentation/jp-ranks13-18/expected-copy-interaction-receipt.txt" "$out/rank13.txt"
python3 "$script_dir/check.py" "$out/receipt.txt" "$out/raw.log"
diff --strip-trailing-cr -u "$script_dir/expected-receipt.txt" "$out/receipt.txt"
printf 'Receipt: %s\n' "$out/receipt.txt"
