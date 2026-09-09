#!/usr/bin/env bash
set -euo pipefail

PROOF_SWITCH="${SM64_PROOF_SWITCH:-sm64-item-proof}"

if ! command -v opam >/dev/null 2>&1; then
  echo "opam is not on PATH" >&2
  return 1 2>/dev/null || exit 1
fi

if ! proof_environment="$(opam env --switch "$PROOF_SWITCH" --set-switch)"; then
  echo "Cannot activate proof toolchain '$PROOF_SWITCH'." >&2
  return 1 2>/dev/null || exit 1
fi
eval "$proof_environment"

if ! proof_coq_version="$(coqc --version)" ||
   ! proof_clight_version="$(clightgen -version 2>&1)"; then
  echo "Proof toolchain '$PROOF_SWITCH' lacks a working coqc/clightgen." >&2
  return 1 2>/dev/null || exit 1
fi

echo "Activated proof toolchain '$PROOF_SWITCH'."
echo "  coqc:      ${proof_coq_version%%$'\n'*}"
echo "  clightgen: ${proof_clight_version%%$'\n'*}"
