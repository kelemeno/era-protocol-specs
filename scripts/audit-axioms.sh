#!/usr/bin/env bash
# Audit every theorem in EraSpec: what axioms does each actually depend on?
#
# A result is CLEAN if it depends only on Lean's standard three — propext,
# Quot.sound, Classical.choice. Anything else, above all `sorryAx`, is a finding.
# Definitions and types are held to the same standard, used or not.
# The audit also asserts that EraSpec declares NO axioms of its own.
#
# Also checks every separated contract property has a theorem referencing its
# exact statement and proving it for all parameters and universe levels, not
# just a special case, and that Properties modules declare nothing but `def`s.
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
# Self-tested in the failing direction on every run: scripts/audit-selftest.sh
# plants each defect the audit must catch in a scratch package and requires the
# audit to reject it with that defect's finding. The defects are a `sorry`
# theorem, a declared axiom, an unused `sorry` def or type, a property proved at
# some universes only or for a special case, a missing, restated, opaque or
# non-Prop property, and a theorem in a Properties module. A valid control must
# pass. Add a case there when you add a check here.
set -euo pipefail

cd "$(dirname "$0")/.."
LAKE="${LAKE:-$HOME/.elan/bin/lake}"

echo "==> self-testing the audit on planted defects"
scripts/audit-selftest.sh

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
