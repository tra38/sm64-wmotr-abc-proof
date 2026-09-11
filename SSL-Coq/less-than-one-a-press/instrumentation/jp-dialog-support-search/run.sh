#!/usr/bin/env bash
set -euo pipefail
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
rom="${1:?usage: run.sh ROM [kind phase policy]}"
kind="${2:-2}"; phase="${3:-130}"; policy="${4:-0}"
[[ "$kind" =~ ^[0-5]$ && "$phase" =~ ^[0-9]+$ && "$policy" =~ ^[0-9]+$ ]]
(( phase <= 130 && policy <= 35 ))
test "$(sha256sum "$rom" | cut -d ' ' -f 1)" = 9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317
test "$(md5sum "$rom" | cut -d ' ' -f 1)" = 85d61f5525af708c9f1e84dce6dc10e9
mkdir -p "$project_dir/build/instrumentation/jp-dialog-support-search"
out="$(mktemp -d "$project_dir/build/instrumentation/jp-dialog-support-search/k${kind}-t${phase}-p${policy}.XXXXXX")"
mkdir -p "$out/config" "$out/data" "$out/shots"
gcc -shared -fPIC -std=c99 -Wall -Wextra -Werror -O2 "$script_dir/probe.c" -ldl -lm -o "$out/probe.so"
printf 'Output: %s\n' "$out"
printf 'bp add 0x802c83f0 0 8\nrun\n' |
    SUPPORT_RUN="k${kind}-t${phase}-p${policy}" SUPPORT_KIND="$kind" SUPPORT_PHASE="$phase" SUPPORT_POLICY="$policy" \
    XDG_CONFIG_HOME="$out/config" XDG_DATA_HOME="$out/data" LIBGL_ALWAYS_SOFTWARE=1 \
    timeout 240 xvfb-run -a "${MUPEN64PLUS:-/usr/games/mupen64plus}" \
        --debug --emumode 0 --nosaveoptions --nospeedlimit --audio dummy \
        --input "$out/probe.so" --gfx mupen64plus-video-rice.so --rsp mupen64plus-rsp-hle.so \
        --cheats 6 --sshotdir "$out/shots" --testshots 4500 "$rom" >"$out/raw.log" 2>&1
grep -aoE 'SUPPORT_[A-Z_]+,.*' "$out/raw.log" >"$out/trace.txt"
python3 "$script_dir/check.py" "$out/trace.txt" --output "$out/result.json"
