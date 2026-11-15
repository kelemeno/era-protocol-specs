#!/usr/bin/env bash
# Checks the source inventory that three InteropHandlerBase models take as their boundary,
# against a vendored era-contracts tree:
#
#   Specs/SelfCallAuthorityFaithful.lean    every way the handler calls itself (`Reaches`), the
#                                           dispatch arms (`pinnedTable`) and the check before
#                                           each self-call
#   Specs/BundleStatusMachineFaithful.lean  where the atomicity gate and the inclusion proof are
#                                           consulted (`LStep`'s labels)
#   Specs/ValueLedgerFaithful.lean          where base-token value is released (`releasedFor`)
#
# Usage:
#
#   scripts/check-interop-handler-inventory.sh [ERA_CONTRACTS_ROOT]
#
# ERA_CONTRACTS_ROOT is a directory holding `l1-contracts/contracts` (default: $ERA_SRC, else
# solidity/vendor/era-contracts as written by scripts/fetch-solidity-deps.sh). The expected sites
# are those of the pin c67894b970a0dac6fe9144d8ebf4b0806e15a9af. Any other layout fails and lists
# what moved, appeared or disappeared: the Lean models enumerate exactly these sites, so a change to
# them needs a fresh review rather than a silent pass. (At e561b9cc2 every section below fails.)
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="${1:-${ERA_SRC:-solidity/vendor/era-contracts}}"
D="$ROOT/l1-contracts/contracts/interop/interop-handler"
[ -d "$D" ] || { echo "error: $D not found (run scripts/fetch-solidity-deps.sh or pass a tree)" >&2; exit 2; }
cd "$D"

fail=0

# check NAME EXPECTED FOUND
check() {
  if [ "$2" = "$3" ]; then
    echo "ok   $1"
  else
    echo "FAIL $1"
    echo "  expected:"; printf '%s\n' "$2" | sed 's/^/    /'
    echo "  found:";    printf '%s\n' "$3" | sed 's/^/    /'
    fail=1
  fi
}

# hits REGEX FILE... -> "file:line:match" for every non-comment line matching REGEX
hits() {
  local re=$1; shift
  { grep -HnE "$re" "$@" 2>/dev/null || true; } \
    | { grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*|/\*)' || true; } \
    | while IFS=: read -r f n rest; do
        printf '%s:%s:%s\n' "$f" "$n" "$(printf '%s\n' "$rest" | grep -oE "$re" | head -n 1)"
      done
}

# fn_at FILE LINE -> "name@line" of the function declaration enclosing LINE (comment lines skipped)
fn_at() {
  awk -v L="$2" 'NR <= L && $0 !~ /^[[:space:]]*(\/\/|\*|\/\*)/ &&
      match($0, /function [A-Za-z_][A-Za-z0-9_]*\(/) {
      name = substr($0, RSTART + 9, RLENGTH - 10); at = NR }
    END { printf "%s@%d", name, at }' "$1"
}

# callers REGEX FILE... -> "file:line:enclosing-function" for every call (not declaration)
callers() {
  local re=$1; shift
  hits "$re" "$@" | while IFS=: read -r f n _; do
    if ! sed -n "${n}p" "$f" | grep -qE 'function[[:space:]]'; then
      printf '%s:%s:%s\n' "$f" "$n" "$(fn_at "$f" "$n" | cut -d@ -f1)"
    fi
  done
}

EXEC_CHECK='(executionChainId == senderChainId || executionChainId == 0) && executionAddress == senderAddress'
UNB_CHECK='(unbundlerChainId == senderChainId || unbundlerChainId == 0) && unbundlerAddress == senderAddress'

echo "==> self-calls (SelfCallAuthorityFaithful: Reaches.relayed, pinnedTable)"

check "the only this.<function>( call sites" \
"InteropHandlerBase.sol:391:this.executeBundle(
InteropHandlerBase.sol:401:this.verifyBundle(
InteropHandlerBase.sol:425:this.unbundleBundle(" \
"$(hits 'this\.[A-Za-z_]+\(' *.sol)"

check "receiveMessage's dispatch arms" \
"InteropHandlerBase.sol:351:if (selector == this.executeBundle.selector
InteropHandlerBase.sol:353:if (selector == this.verifyBundle.selector
InteropHandlerBase.sol:355:if (selector == this.unbundleBundle.selector" \
"$(hits 'if \(selector == [A-Za-z_.]+' *.sol)"

check "receiveMessage rejects every other selector" \
"InteropHandlerBase.sol:358:revert InvalidSelector(selector)" \
"$(hits 'revert InvalidSelector\(selector\)' *.sol)"

check "the msg.sender == address(this) occurrences (three gates, receiveMessage)" \
"InteropHandlerBase.sol:104:msg.sender == address(this)
InteropHandlerBase.sol:177:msg.sender == address(this)
InteropHandlerBase.sol:341:msg.sender == address(this)
L2InteropHandler.sol:67:msg.sender == address(this)" \
"$(hits 'msg\.sender == address\(this\)' *.sol)"

check "the functions holding them" \
"InteropHandlerBase.sol:104:executeBundle
InteropHandlerBase.sol:177:unbundleBundle
InteropHandlerBase.sol:341:receiveMessage
L2InteropHandler.sol:67:executeAtomicBundle" \
"$(callers 'msg\.sender == address\(this\)' *.sol)"

relay_table() {
  hits 'this\.[A-Za-z_]+\(' *.sol | while IFS=: read -r f n _; do
    fn=$(fn_at "$f" "$n"); name=${fn%@*}; start=${fn#*@}
    e=$(awk -v s="$start" -v n="$n" 'NR > s && NR < n' "$f" | grep -cF "$EXEC_CHECK" || true)
    u=$(awk -v s="$start" -v n="$n" 'NR > s && NR < n' "$f" | grep -cF "$UNB_CHECK" || true)
    printf '%s:%s:%s:execution-check=%s:unbundler-check=%s\n' "$f" "$n" "$name" "$e" "$u"
  done
}

check "the check before each self-call, in the same function (Branch.check)" \
"InteropHandlerBase.sol:391:_handleExecuteBundle:execution-check=1:unbundler-check=0
InteropHandlerBase.sol:401:_handleVerifyBundle:execution-check=0:unbundler-check=0
InteropHandlerBase.sol:425:_handleUnbundleBundle:execution-check=0:unbundler-check=1" \
"$(relay_table)"

check "the only call to a recipient's receiveMessage (the handler reaches its own only here)" \
"InteropHandlerBase.sol:282:_executeCalls" \
"$(callers '\.receiveMessage\{' *.sol)"

echo "==> gates consulted (BundleStatusMachineFaithful: LStep labels)"

check "requireFlowFinalized is called only by executeAtomicBundle" \
"L2InteropHandler.sol:83:executeAtomicBundle" \
"$(callers 'requireFlowFinalized\(' *.sol)"

check "_verifyBundle is called by executeBundle (fresh only) and verifyBundle" \
"InteropHandlerBase.sol:123:executeBundle
InteropHandlerBase.sol:160:verifyBundle" \
"$(callers '_verifyBundle\(' *.sol)"

check "executeBundle skips _verifyBundle for a Verified bundle" \
"InteropHandlerBase.sol:123:if (status != BundleStatus.Verified) _verifyBundle(" \
"$(hits 'if \(status != BundleStatus\.Verified\) _verifyBundle\(' *.sol)"

check "_proveInclusion is called only by _verifyBundle" \
"InteropHandlerBase.sol:310:_verifyBundle" \
"$(callers '_proveInclusion\(' *.sol)"

echo "==> value released (ValueLedgerFaithful: releasedFor)"

check "_handleCallValue is called only by _executeCalls" \
"InteropHandlerBase.sol:279:_executeCalls" \
"$(callers '_handleCallValue\(' *.sol)"

check "BaseTokenHolder.give is called only by _handleCallValue" \
"L2InteropHandler.sol:118:_handleCallValue" \
"$(callers '\.give\(' *.sol)"

if [ "$fail" -ne 0 ]; then
  echo "FAIL: the inventory differs from the pin's; re-review the three models before updating it"
  exit 1
fi
echo "==> OK: the inventory matches the pin c67894b9"
