#!/usr/bin/env bash
# Active SSL build wrapper; never depends on the legacy root's default switch.
set -euo pipefail
cd "$(dirname "$0")/.."
source pipeline/env.sh
proof_memory_cap="${SM64_PROOF_VCAP_KB:-6815744}"
if [ "$proof_memory_cap" != 0 ]; then ulimit -S -v "$proof_memory_cap"; fi
exec make "$@"
