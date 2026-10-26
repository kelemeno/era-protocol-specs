#!/usr/bin/env bash
# Vendors the pinned Solidity sources the comparison suite needs into
# solidity/vendor/ (gitignored): era-contracts l1-contracts/contracts at the pin
# the models were reviewed against, and each library at the exact commit the pin's
# gitlink names. Nothing is fetched from the network; point ERA_CONTRACTS at a
# local clone of matter-labs/era-contracts whose lib/ submodules are checked out.
#
#   ERA_CONTRACTS=~/src/era-contracts scripts/fetch-solidity-deps.sh
set -euo pipefail

PIN=c67894b970a0dac6fe9144d8ebf4b0806e15a9af
ERA=${ERA_CONTRACTS:?set ERA_CONTRACTS to a local era-contracts clone containing $PIN}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
V="$ROOT/solidity/vendor"

git -C "$ERA" cat-file -e "${PIN}^{commit}" 2>/dev/null \
  || { echo "error: $ERA does not contain $PIN" >&2; exit 1; }

rm -rf "$V" && mkdir -p "$V/era-contracts"
git -C "$ERA" archive "$PIN" l1-contracts/contracts system-contracts/contracts l2-contracts/contracts lib/@matterlabs \
  | tar -x -C "$V/era-contracts"
{
  echo "era-contracts $PIN l1-contracts/contracts system-contracts/contracts l2-contracts/contracts lib/@matterlabs"
  for lib in openzeppelin-contracts-v4 openzeppelin-contracts-upgradeable-v4 forge-std; do
    want=$(git -C "$ERA" ls-tree "$PIN" "lib/$lib" | awk '{print $3}')
    [ -n "$want" ] || { echo "error: $PIN has no gitlink lib/$lib" >&2; exit 1; }
    git -C "$ERA/lib/$lib" cat-file -e "${want}^{commit}" 2>/dev/null \
      || { echo "error: $ERA/lib/$lib lacks commit $want (update the submodule)" >&2; exit 1; }
    mkdir -p "$V/$lib"
    git -C "$ERA/lib/$lib" archive "$want" | tar -x -C "$V/$lib"
    echo "$lib $want"
  done
} > "$V/PINS.txt"
cat "$V/PINS.txt"
