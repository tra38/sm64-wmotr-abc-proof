#!/usr/bin/env bash
set -euo pipefail
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
rom="${1:?usage: $0 /path/to/authentic/baserom.jp.z64}"
test "$(sha256sum "$rom" | cut -d ' ' -f 1)" = 9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317
test "$(md5sum "$rom" | cut -d ' ' -f 1)" = 85d61f5525af708c9f1e84dce6dc10e9
emulator="${MUPEN64PLUS:-/usr/games/mupen64plus}"
mkdir -p "$project_dir/build/instrumentation/jp-vertical-retry"
out="$(mktemp -d "$project_dir/build/instrumentation/jp-vertical-retry/run.XXXXXX")"
mkdir -p "$out/config" "$out/data" "$out/shots"
gcc -shared -fPIC -std=c99 -Wall -Wextra -Werror -O2 \
    "$script_dir/jp_vertical_retry_probe.c" -ldl -lm -o "$out/probe.so"
printf 'Output: %s\n' "$out"
printf 'bp add 0x802c83f0 0 8\nrun\n' |
    XDG_CONFIG_HOME="$out/config" XDG_DATA_HOME="$out/data" LIBGL_ALWAYS_SOFTWARE=1 \
    xvfb-run -a "$emulator" --debug --emumode 0 --nosaveoptions --nospeedlimit \
        --audio dummy --input "$out/probe.so" --gfx mupen64plus-video-rice.so \
        --rsp mupen64plus-rsp-hle.so --cheats 6 --sshotdir "$out/shots" \
        --testshots 620 "$rom" >"$out/raw.log" 2>&1
grep -aoE '(VERTICAL_[A-Z_]+|TRACE_A1|FIRST_APPLY_ENTRY|FIRST_APPLY_RETURN|FIRST_AREA2_POLL|EXPLOSION_FREE|RESULT),.*' \
    "$out/raw.log" >"$out/trace.txt"
python3 "$script_dir/check.py" "$out/trace.txt" --snapshot-output "$out/floor-snapshot.json"
