#!/usr/bin/env bash
# Non-vacuity check for the comparison suite: plants one realistic emitter or
# transcription bug at a time in the GENERATED contract and requires the suite
# to fail on each. A suite that passes a planted bug is not evidence of anything.
# Restores the generated file afterwards whatever happens.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GEN="$ROOT/solidity/src/generated/BridgedTokenSlice.sol"
BACKUP=$(mktemp)
cp "$GEN" "$BACKUP"
trap 'cp "$BACKUP" "$GEN"; rm -f "$BACKUP"' EXIT

# name | perl substitution applied to the generated file
MUTANTS=(
  "zero-address check before authority|s/(        require\(msg.sender == _nativeTokenVault, Unauthorized\(msg.sender\)\);\n)(        require\(_to != address\(0\), \"ERC20: mint to the zero address\"\);\n)/\$2\$1/"
  "strict balance check in burn|s/accountBalance >= _amount/accountBalance > _amount/"
  "missing transfer-from-zero check|s/        require\(msg.sender != address\(0\), \"ERC20: transfer from the zero address\"\);\n//"
  "events emitted in the wrong order|s/(        emit Transfer\(address\(0\), _to, _amount\);\n)(        emit BridgeMint\(_to, _amount\);\n)/\$2\$1/"
  "unchecked supply increment|s/        _totalSupply = \(_totalSupply \+ _amount\);/        unchecked { _totalSupply = (_totalSupply + _amount); }/"
  "wrong error argument|s/Unauthorized\(msg.sender\)\);\n        require\(_to/Unauthorized(_to));\n        require(_to/"
  "recipient read before debit|s/uint256 fromBalance = _balances\[msg.sender\];/uint256 fromBalance = _balances[msg.sender]; uint256 toBefore = _balances[to];/; s/_balances\[to\] = \(_balances\[to\] \+ amount\)/_balances[to] = (toBefore + amount)/"
  "wrong revert message|s/ERC20: burn amount exceeds balance/ERC20: burn exceeds balance/"
)

cd "$ROOT/solidity"
survived=0
for m in "${MUTANTS[@]}"; do
  name=${m%%|*}; sub=${m#*|}
  cp "$BACKUP" "$GEN"
  perl -0pi -e "$sub" "$GEN"
  if cmp -s "$BACKUP" "$GEN"; then echo "BROKEN MUTANT (no change): $name"; survived=1; continue; fi
  if forge test --offline >/dev/null 2>&1; then
    echo "SURVIVED: $name"; survived=1
  else
    echo "killed:   $name"
  fi
done
exit $survived
