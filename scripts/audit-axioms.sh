#!/usr/bin/env bash
# Audit every theorem in EraSpec: what axioms does each actually depend on?
#
# A result is CLEAN if it depends only on Lean's standard three — propext,
# Quot.sound, Classical.choice. Anything else, above all `sorryAx`, is a finding.
# The audit also asserts that EraSpec declares NO axioms of its own.
#
# The real work is scripts/Audit.lean, which enumerates the ENVIRONMENT rather
# than grepping source text. That matters:
#
#   * An earlier regex-based version found 327 theorems and reported them all
#     clean. The environment finds 471. The regex was silently missing 144
#     declarations — every `private lemma`, plus anything whose namespace it
#     guessed wrongly — and a clean number with a hidden hole reads exactly like
#     success.
#   * `#print axioms` prints its axiom list in an unspecified ORDER and WRAPS
#     long lines, so parsing its text is fragile in two independent ways.
#     Audit.lean calls the same traversal (`CollectAxioms`) and gets a set.
#
# Self-tested in the failing direction: appending a `sorry` theorem and an
# `axiom` to a module makes it report `UNCLEAN … [sorryAx]` and
# `DECLARED AXIOM …`, and exit nonzero. Re-run that test if you change it.
set -euo pipefail

cd "$(dirname "$0")/.."
LAKE="${LAKE:-$HOME/.elan/bin/lake}"

echo "==> building EraSpec"
"$LAKE" build EraSpec

echo "==> auditing axioms"
OUT="${TMPDIR:-/tmp}/eraspec-audit.txt"
if "$LAKE" env lean scripts/Audit.lean > "$OUT" 2>&1; then
  cat "$OUT"
  # Belt and braces: Audit.lean throws on a finding, but a future edit could
  # weaken that, so re-check the reported numbers here too.
  if grep -qE '^(UNCLEAN|  UNCLEAN|  DECLARED AXIOM)' "$OUT"; then
    echo "FAIL: findings reported above"
    exit 1
  fi
  echo "==> OK"
else
  cat "$OUT"
  echo "FAIL: audit reported findings (see above)"
  exit 1
fi
