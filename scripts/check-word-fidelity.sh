#!/usr/bin/env bash
# Check the local word declarations against their checked-in review baseline.
# No older repository or Clear checkout is required. This detects unreviewed
# definition changes; mathematical claims are checked by Lean, not by hashes.
# For an optional provenance comparison, pass an explicit source file as $1.
set -euo pipefail

cd "$(dirname "$0")/.."
REFERENCE="${1:-}"
MINE="EraSpec/Core/Word.lean"
BASELINE="scripts/word-baseline.json"

python3 - "$REFERENCE" "$MINE" "$BASELINE" <<'PY'
import hashlib, json, re, sys

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

mine = decls(sys.argv[2])
if sys.argv[1]:
    reference = decls(sys.argv[1])
    missing = sorted(set(mine) - set(reference))
    added = []  # A broader reference may contain intentionally omitted definitions.
    differing = [n for n in mine if n in reference and mine[n] != reference[n]]
    label = 'explicit reference'
else:
    with open(sys.argv[3]) as f:
        reference = json.load(f)['declarations_sha256']
    hashes = {n: hashlib.sha256(body.encode()).hexdigest() for n, body in mine.items()}
    missing = sorted(set(reference) - set(hashes))
    added = sorted(set(hashes) - set(reference))
    differing = [n for n in hashes if n in reference and hashes[n] != reference[n]]
    label = 'local review baseline'

print(f'word declarations checked against {label}: {len(mine)}')
for category, names in [('MISSING', missing), ('ADDED', added), ('CHANGED', differing)]:
    for name in names:
        print(f'  {category} {name}')
sys.exit(1 if missing or added or differing else 0)
PY
echo "==> OK: local word definitions match the selected baseline"
