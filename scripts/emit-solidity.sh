#!/usr/bin/env bash
# Regenerates the Solidity emitted from Lean.  With --check, fails instead of
# writing when a committed file differs from what the current Lean sources emit.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
LAKE=${LAKE:-lake}
"$LAKE" build EraSpec.Codegen.Emit EraSpec.Codegen.BridgedTokenSlice.Specs.Program >/dev/null

emit() { # <lean script> <target>
  local tmp; tmp=$(mktemp)
  "$LAKE" env lean --run "$1" > "$tmp"
  if [ "${CHECK:-0}" = 1 ]; then
    if ! diff -u "$2" "$tmp"; then
      echo "error: $2 is stale; run scripts/emit-solidity.sh" >&2; rm -f "$tmp"; exit 1
    fi
    rm -f "$tmp"
  else
    mv "$tmp" "$2"; echo "wrote $2"
  fi
}
[ "${1:-}" = --check ] && CHECK=1
emit scripts/EmitSolidity.lean solidity/src/generated/BridgedTokenSlice.sol
emit scripts/EmitVectors.lean solidity/test/generated/LeanVectors.t.sol
