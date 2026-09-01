#!/usr/bin/env bash
# Verify that EraSpec/Word.lean's vendored declarations still match Clear's.
#
# Word.lean is a deliberate COPY of Clear/UInt256.lean, trimmed to the word type
# and its arithmetic (see that file's header for why).  A copy is only worth
# having while it is actually a copy: if Clear's definitions drift, a theorem
# proved here and a theorem proved in contracts-formal-verification stop being
# about the same type, and nothing else in either repo would notice.
#
# So: for every declaration Word.lean keeps, find the same declaration in Clear
# and compare the text. Report anything that differs or has disappeared.
#
# Extra declarations in Clear are EXPECTED (we trimmed the EVM opcodes on
# purpose) and are not reported. Extra declarations HERE are a finding — this
# file should never grow definitions of its own.
set -euo pipefail

cd "$(dirname "$0")/.."
CLEAR="${CLEAR_UINT256:-../contracts-formal-verification/Clear/Clear/UInt256.lean}"
MINE="EraSpec/Word.lean"

if [ ! -f "$CLEAR" ]; then
  echo "SKIP: Clear source not found at $CLEAR"
  echo "      set CLEAR_UINT256=<path> to check fidelity"
  exit 0
fi

python3 - "$CLEAR" "$MINE" <<'PY'
import re, sys

def decls(path):
    """Map declaration name -> normalized body text."""
    src = open(path).read()
    # Strip comments and doc-comments so formatting churn is not a finding.
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    out, cur, name = {}, [], None
    pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?'
                     r'(def|abbrev|lemma|theorem|instance|structure)\s+([\w\'!?.]+)?')
    for line in src.split('\n'):
        m = pat.match(line)
        if m:
            if name: out[name] = ' '.join(' '.join(cur).split())
            kind, nm = m.group(1), m.group(2)
            # anonymous instances are keyed by their type signature
            name = nm if nm else 'instance:' + ' '.join(line.split())
            cur = [line]
        elif name is not None:
            cur.append(line)
    if name: out[name] = ' '.join(' '.join(cur).split())
    return out

clear, mine = decls(sys.argv[1]), decls(sys.argv[2])
missing  = [n for n in mine if n not in clear]
differing = [n for n in mine if n in clear and mine[n] != clear[n]]

print(f"vendored declarations : {len(mine)}")
print(f"present in Clear      : {len(mine) - len(missing)}")
print(f"missing from Clear    : {len(missing)}")
for n in missing:  print(f"  MISSING  {n}")
print(f"text differs          : {len(differing)}")
for n in differing:
    print(f"  DIFFERS  {n}")
    print(f"    clear: {clear[n][:160]}")
    print(f"    mine : {mine[n][:160]}")

sys.exit(1 if (missing or differing) else 0)
PY
echo "==> OK: every vendored declaration matches Clear"
