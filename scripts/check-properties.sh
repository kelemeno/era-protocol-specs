#!/usr/bin/env bash
# List every stated property (EraSpec/Properties/*) and whether it has a
# certificate — a theorem of exactly its type — anywhere in the package.
#
# The work is scripts/Properties.lean, which enumerates the Lean ENVIRONMENT.
# OPEN properties are a roadmap, not a failure: exit status is nonzero only if
# REQUIRE_ALL_PROVED=1 is set and something is open.
#
# Self-test in the failing direction: add `def Bogus : Prop := False` to a
# Properties file, rebuild, and it must show as OPEN.
set -euo pipefail

cd "$(dirname "$0")/.."
LAKE="${LAKE:-$HOME/.elan/bin/lake}"

echo "==> building EraSpec"
"$LAKE" build EraSpec

echo "==> properties"
OUT="${TMPDIR:-/tmp}/eraspec-properties.txt"
"$LAKE" env lean scripts/Properties.lean > "$OUT" 2>&1 || { cat "$OUT"; echo "FAIL: checker errored"; exit 1; }
cat "$OUT"

if [ "${REQUIRE_ALL_PROVED:-0}" = "1" ] && grep -qE '^\s*OPEN' "$OUT"; then
  echo "FAIL: open properties remain (REQUIRE_ALL_PROVED=1)"
  exit 1
fi
echo "==> OK"
