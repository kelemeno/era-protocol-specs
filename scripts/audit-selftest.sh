#!/usr/bin/env bash
# Self-test of scripts/Audit.lean in the FAILING direction: an audit that has never
# failed has never been tested.
#
# Each directory under scripts/audit-selftest/EraSpec/AuditSelfTest/ is a small
# package fragment. Every case but `Accept` plants one defect the audit exists to
# catch. Its modules are named EraSpec.AuditSelfTest.<Case>.*, so the audit treats
# them as package modules, and a module named `Properties` as a Properties module.
#
# For each case this script compiles the fragment into a scratch directory and runs
# scripts/Audit.lean over it. The audit runs verbatim, except that its `import EraSpec`
# is replaced by `import Lean`, `import EraSpec.Core.Headline` (the real tag attributes, which
# the audit reads and fixtures may use) and the case's modules. A defect case passes only if
# the audit exits nonzero AND prints that case's finding, so it cannot pass by failing
# for another reason. `Accept` holds valid declarations of the shapes the stricter
# checks inspect, and the audit must accept it with its property count.
#
# The fixtures contain `sorry`, `axiom` and `opaque` on purpose. They live outside
# EraSpec/, and EraSpec.lean never imports them.
#
# AUDIT=<file> tests another version of the audit, e.g. to confirm that an older
# Audit.lean lets the newer cases through.
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT=$PWD
LEAN="${LEAN:-$HOME/.elan/bin/lean}"
AUDIT="${AUDIT:-scripts/Audit.lean}"
FIXTURES="$ROOT/scripts/audit-selftest"
CASES="$FIXTURES/EraSpec/AuditSelfTest"
WORK=$(mktemp -d "${TMPDIR:-/tmp}/eraspec-audit-selftest.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

# The audit under test: everything after its leading import block.
BODY="$WORK/AuditBody.lean"
awk 'body || !/^import / { body = 1; print }' "$AUDIT" > "$BODY"
grep -q 'run_cmd' "$BODY" || { echo "FAIL: no audit found in $AUDIT"; exit 1; }

# The real tag attributes, compiled from the package source. The audit refers to them, so
# every case imports this module; fixtures that tag properties import it too.
mkdir -p "$WORK/EraSpec/Core"
if ! LEAN_PATH="$WORK" "$LEAN" -R "$ROOT" -o "$WORK/EraSpec/Core/Headline.olean" \
    "$ROOT/EraSpec/Core/Headline.lean" > "$WORK/compile.log" 2>&1; then
  cat "$WORK/compile.log"
  echo "FAIL: EraSpec/Core/Headline.lean does not compile"
  exit 1
fi

# Compile fixture module $1 into $WORK, after the fixture modules it imports.
compile() {
  local mod=$1 rel=${1//.//}
  [ -e "$WORK/$rel.olean" ] && return 0
  local src="$FIXTURES/$rel.lean" dep
  [ -f "$src" ] || { echo "FAIL: no fixture source for $mod"; exit 1; }
  for dep in $(sed -n 's/^import \(EraSpec\.AuditSelfTest\.[A-Za-z0-9_.]*\).*/\1/p' "$src"); do
    compile "$dep"
  done
  mkdir -p "$(dirname "$WORK/$rel.olean")"
  if ! LEAN_PATH="$WORK" "$LEAN" -R "$FIXTURES" -o "$WORK/$rel.olean" "$src" \
      > "$WORK/compile.log" 2>&1; then
    cat "$WORK/compile.log"
    echo "FAIL: fixture module $mod does not compile"
    exit 1
  fi
}

# Run the audit over case $1, leaving its output in $WORK/$1.out; returns its status.
audit_case() {
  local case=$1 src mod
  local test="$WORK/Audit$case.lean"
  [ -d "$CASES/$case" ] || { echo "FAIL: no fixture directory for case $case"; exit 1; }
  printf 'import Lean\nimport EraSpec.Core.Headline\n' > "$test"
  # Every module of the case, nested folders included (a History/ folder, for example).
  for src in $(find "$CASES/$case" -name '*.lean' | sort); do
    mod=${src#"$FIXTURES/"}
    mod=${mod%.lean}
    mod=${mod//\//.}
    compile "$mod"
    echo "import $mod" >> "$test"
  done
  cat "$BODY" >> "$test"
  LEAN_PATH="$WORK" "$LEAN" "$test" > "$WORK/$case.out" 2>&1
}

failed=0
ran=()

# The audit must reject case $1, and its output must contain $2.
reject() {
  ran+=("$1")
  if audit_case "$1"; then
    echo "SURVIVED:     $1 (the audit accepted it)"
  elif ! grep -qF -- "$2" "$WORK/$1.out"; then
    echo "WRONG REASON: $1 (rejected, but the output lacks: $2)"
  else
    echo "rejected:     $1"
    return 0
  fi
  sed 's/^/    /' "$WORK/$1.out"
  failed=1
}

# The audit must accept case $1, and its output must contain each of $2, $3, ...
accept() {
  local case=$1 want
  shift
  ran+=("$case")
  if ! audit_case "$case"; then
    echo "REJECTED:     $case (a valid control)"
  else
    for want in "$@"; do
      if ! grep -qF -- "$want" "$WORK/$case.out"; then
        echo "WRONG COUNT:  $case (accepted, but the output lacks: $want)"
        sed 's/^/    /' "$WORK/$case.out"
        failed=1
        return 0
      fi
    done
    echo "accepted:     $case"
    return 0
  fi
  sed 's/^/    /' "$WORK/$case.out"
  failed=1
}

T=AuditSelfTest

# A property proved at some universes only
reject UniverseSpecialized \
  "theorem $T.UniverseSpecialized.P does not prove the full property $T.UniverseSpecialized.Properties.P"
reject UniverseSuccessor \
  "theorem $T.UniverseSuccessor.HasDistinct does not prove the full property $T.UniverseSuccessor.Properties.HasDistinct"
reject UniversePostponed \
  "theorem $T.UniversePostponed.HasDistinct does not prove the full property $T.UniversePostponed.Properties.HasDistinct"

# `sorry` in declarations that no theorem uses
reject UnusedSorryProof "UNCLEAN def $T.UnusedSorryProof.hiddenFalse : [sorryAx]"
reject UnusedSorryData "UNCLEAN def $T.UnusedSorryData.f : [sorryAx]"
reject UnusedSorryType "UNCLEAN constructor $T.UnusedSorryType.Bad.mk : [sorryAx]"

# Declaration kinds a Properties module may not contain
reject OpaqueProperty \
  "$T.OpaqueProperty.Properties.Unproved in EraSpec.$T.OpaqueProperty.Properties is opaque"
reject TheoremInProperties \
  "$T.TheoremInProperties.Properties.Smuggled in EraSpec.$T.TheoremInProperties.Properties (theorem)"
# Private declarations, whose `_private` prefix makes them look like Lean auxiliaries
reject PrivateProperty \
  "$T.PrivateProperty.Properties.Unproved in EraSpec.$T.PrivateProperty.Properties (def) is private"
reject PrivateTheorem \
  "$T.PrivateTheorem.Properties.Smuggled in EraSpec.$T.PrivateTheorem.Properties (theorem) is private"

# The earlier checks
reject SorryTheorem "UNCLEAN $T.SorryTheorem.bad : [sorryAx]"
reject DeclaredAxiom "DECLARED AXIOM $T.DeclaredAxiom.unproved"
reject MissingProof "property $T.MissingProof.Properties.Q has no theorem $T.MissingProof.Q"
reject SpecialCase \
  "theorem $T.SpecialCase.Q does not prove the full property $T.SpecialCase.Properties.Q"
reject Restated "theorem $T.Restated.Q does not reference statement $T.Restated.Properties.Q"
reject NotProp "property $T.NotProp.Properties.Q is not a proposition"

# Headline / witness / countermodel tags (EraSpec.Core.Headline)
reject TagOnSpecsDef \
  "MISPLACED TAG $T.TagOnSpecsDef.helper (def in EraSpec.$T.TagOnSpecsDef.Specs) carries @[headline]"
reject TagOnTheorem \
  "MISPLACED TAG $T.TagOnTheorem.Q (theorem in EraSpec.$T.TagOnTheorem.Proofs) carries @[witness]"
reject DoubleTag "DOUBLE TAG $T.DoubleTag.Properties.Q carries 2 of"
reject HistoryHeadline \
  "HISTORY HEADLINE $T.HistoryHeadline.History.Properties.Q in EraSpec.$T.HistoryHeadline.History.Properties"
reject HeadlineNoDocstring \
  "HEADLINE WITHOUT DOCSTRING $T.HeadlineNoDocstring.Properties.Q in EraSpec.$T.HeadlineNoDocstring.Properties"

# The control
accept Accept "properties proved    : 6 " \
  "headline properties  : 1 " "witness properties   : 1 " "countermodel props   : 2 " \
  "untagged properties  : 2 " "tag findings         : 0 " \
  "FOLDER AuditSelfTest.Accept : 1 / 1 / 2 / 2"

# A fixture directory that no line above runs would be a test that never runs.
for dir in "$CASES"/*/; do
  case=$(basename "$dir")
  listed=0
  for r in "${ran[@]}"; do [ "$r" = "$case" ] && listed=1; done
  if [ "$listed" = 0 ]; then
    echo "UNLISTED:     $case (fixture directory that the self-test does not run)"
    failed=1
  fi
done

if [ "$failed" != 0 ]; then
  echo "FAIL: the audit self-test found the problems above"
  exit 1
fi
echo "==> audit self-test OK: ${#ran[@]} cases"
