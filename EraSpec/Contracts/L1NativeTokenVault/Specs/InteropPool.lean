import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the L1 vault's per-chain ledger and the interop pool, at draft/v0.35.0

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L1NativeTokenVault.Properties.InteropPool`, proofs in
`EraSpec.Contracts.L1NativeTokenVault.Proofs.InteropPool`.

Source: era-contracts `draft/v0.35.0` at `b17415d20` (paths under `l1-contracts/contracts/`).
`L1NativeTokenVault.sol`, `L1MessageRoot.sol` and `Config.sol` are byte-identical at `d9f678900`.
`main` at `70096e2ea` has none of the per-chain ledger or the pool: its `L1NativeTokenVault`
keeps only the aggregate `bridgedOut`, and its `L1MessageRoot` has no `enableInterop`.

The function shapes start from an earlier draft cap model (`CapStepV35`), re-checked line by line
against `b17415d20`. This model differs from it in four ways. Storage values are naturals, and each checked `+`, `+=` and `-` is a guard that makes
the call `none`, not error data. The interop answers are the message root's own flags in the
system state, not a free input per step. The system adds the message root's `interopEnabled`,
the Bridgehub's chain registry and the vault's initializer version, with their writers as steps.
And a ghost counter `directToPool` records the deposits credited to the pool's key.

## The storage (`bridge/ntv/L1NativeTokenVault.sol`)

    mapping(bytes32 assetId => uint256 amount) public bridgedOut;                              // :90
    mapping(uint256 chainId => mapping(bytes32 assetId => uint256 amount)) public chainTotalDeposited;  // :96
    mapping(uint256 chainId => mapping(bytes32 assetId => uint256 amount)) public chainTotalWithdrawn;  // :99
    mapping(uint256 chainId => mapping(bytes32 assetId => uint256 amount)) public chainBalanceBackfill; // :102
    mapping(uint256 chainId => mapping(bytes32 assetId => bool moved)) public chainBalanceInInteropPool; // :105
    mapping(uint256 chainId => bool pending) public chainBalanceBackfillPending;               // :108

The last five are new at v35 and follow `bridgedOutPopulated` (`:93`), the last variable at `main`,
so they are zero when the upgrade installs the v35 code. `L1MessageRoot.sol:49` adds
`mapping(uint256 chainId => bool enabled) internal interopEnabled`, also new at v35.

## The writers

Every write to these mappings (a grep of `l1-contracts/contracts` at `b17415d20`) is in one of the
functions below. Each is a `PoolCall`:

* **`toChain`**: `_handleBridgeToChain` (`:424-433`). `bridgedOut[a] += x` if the asset's origin
  is L1 (`:426-428`), then `chainTotalDeposited[key][a] += x` if the balance is tracked (`:429-432`).
  The vault calls it from `_getTokenAndBridgeToChain` (`NativeTokenVaultBase.sol:444, :447`), that
  is from every `bridgeBurn`, so from every deposit.
* **`fromChain`**: `_handleBridgeFromChain` (`:439-459`). The `bridgedOut` check and debit
  (`:441-446`), then, if tracked, `newWithdrawn = chainTotalWithdrawn[key][a] + x` (`:449`),
  the cap `newWithdrawn <= chainTotalDeposited[key][a] + chainBalanceBackfill[key][a]` unless
  `chainBalanceBackfillPending[key]` (`:450-456`), and the write (`:457`). It is called from
  `_bridgeMintToken` (`NativeTokenVaultBase.sol:240`) and `_disburseFailedTransfer` (`:276`):
  every finalized withdrawal and every claimed failed deposit.
* **`setBackfill`**: one entry of `setChainBalanceBackfill(c, assets, amounts)` (`:219-239`,
  `onlyOwner`). `c != INTEROP_POOL_CHAIN_ID` (`:224`); `chainBalanceBackfill[c][a] == 0` (`:229`);
  if `chainBalanceInInteropPool[c][a]`, the pool's deposits gain
  `_netChainBalance(c, a, x) - _netChainBalance(c, a, 0)` (`:230-235`); then
  `chainBalanceBackfill[c][a] = x` (`:236`). A successful call is the sequence of its entries, each
  of which reads what the previous one wrote; `ArrayLengthMismatch` (`:226`) only rejects.
* **`markBackfilled`**: `markBackfilled(c)` (`:242-246`, `onlyOwner`): requires the pending flag
  and clears it.
* **`move`**: `moveChainBalanceToInteropPool(c, a)` (`:249-258`, any caller):
  `isInteropEnabled(c)` (`:250`), not pending (`:251`), not yet moved (`:252`); the amount is
  `_netChainBalance(c, a, chainBalanceBackfill[c][a])` (`:254`); the flag is set (`:255`) and the
  pool's deposits gain the amount (`:256`).
* **`enableInterop`**: `L1MessageRoot.enableInterop(c, requireSecondProofSystem)`
  (`core/message-root/L1MessageRoot.sol:72-89`): only the Bridgehub owner (`:73`); `c` registered
  (`getZKChain(c) != 0`, `:74-75`); not already enabled (`:76`); the vault's
  `chainBalanceBackfillPending(c)` false (`:77-80`); optional second-proof-system checks
  (`:81-85`); then `interopEnabled[c] = true` (`:87`). Nothing else writes `interopEnabled`.
* **`initializeUpgrade`**: `initializeUpgrade()` (`:291-298`), OpenZeppelin v4
  `reinitializer(2)` plus a proxy-admin check (`:292`): every chain in
  `getAllZKChainChainIDs()` becomes pending (`:293-297`). Earlier vault versions (`main` at
  `70096e2ea`) use only `initializer` (version 1), so the call can succeed once. For a row with
  `callInitializeUpgrade`, the registry upgrade engine's `applyRows` runs it in the same
  transaction as the implementation switch
  (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:119-124`).
* **`populateBridgedOut`**: one entry of `populateBridgedOut(assetIds)` (`:189-212`, any caller):
  `bridgedOut[a] += legacyAmount` (`:207`). It writes `bridgedOut`, which the hooks read.
* **`register`**: the Bridgehub's `createNewChain` (`core/bridgehub/L1Bridgehub.sol:108-139`) and
  `registerAlreadyDeployedZKChain` (`:285-319`). Both run `_validateChainParams`
  (`core/bridgehub/BridgehubBase.sol:491-537`): nonzero (`:492-494`), at most `type(uint48).max`
  (`:496-499`, "Also keeps `INTEROP_POOL_CHAIN_ID` from ever being registered"), not
  `block.chainid` (`:501-503`), no chain type manager recorded yet
  (`chainTypeManager[_chainId] == address(0)`, `:534-536`; registration sets it together with the
  `zkChainMap` entry, so the model reads it as "not already registered"). The chain id joins
  `zkChainMap` (`:301-307`), whose keys are `getAllZKChainChainIDs()` (`:337-339`); nothing removes
  a key. The chain asset handler's `registerNewZKChain` (`ChainAssetHandlerBase.sol:405`) skips
  `_validateChainParams`, but on L1 it runs only for a chain arriving with
  `migrationNumber == MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER` (`:374-383`), which only a chain that
  left L1 has, and such a chain is already a key. That last argument is from source, not modelled.

`_trackedBalance(c, origin)` (`:468-477`) decides the key: `INTEROP_POOL_CHAIN_ID` with
`tracked = !isInteropEnabled(origin)` if `isInteropEnabled(c)`, and `c` with
`tracked = origin != c` otherwise. `_netChainBalance(c, a, b)` (`:484-488`) is
`chainTotalDeposited[c][a] + b` (checked) less `chainTotalWithdrawn[c][a]`, or zero if that is
negative. `INTEROP_POOL_CHAIN_ID = uint256(keccak256("interop.pool")) - 1` (`common/Config.sol:37`).

## What is modelled, and what is left out

`PoolSys` is the five vault mappings above, `bridgedOut`, the vault's initializer version, the
message root's `interopEnabled`, the Bridgehub's key set, and the ghost. `poolCall` is one
successful call; a revert is `none`, which `PoolRun` does not take as a step.

The model admits more runs than the contracts, never fewer, apart from the registry boundary
above and the version detail of `initialize()` below:

* Each call is one step. A hook finishes its writes before the vault's next external call that
  can change state (`NativeTokenVaultBase.sol:240-246, :276-285, :447-455`; the message-root reads
  are `view`), so a call re-entering the vault from a token or a recipient runs after the hook,
  as a separate step.
* The hooks are steps for **any** chain argument, any asset, any `uint256` amount and any
  value of `originChainId[asset]` (a per-call input: the token registry is not modelled). The
  callers that restrict them (the Bridgehub's `zkChainMap.get` on the deposit path,
  `BridgehubBase.sol:378`; withdrawal proofs; failed-deposit proofs) are not modelled.
* Caller checks are dropped: `onlyOwner` on the two backfill functions, the proxy-admin check
  of `initializeUpgrade`, the Bridgehub owner in `enableInterop`, and the Bridgehub's own
  `onlyOwnerOrAdmin`/`onlyOwner`. So are the second-proof-system checks of `enableInterop`, the
  CTM, asset and router checks of `_validateChainParams`, the chain-count limit, and pauses.
  Each only rejects.
* `isInteropEnabled` and `chainBalanceBackfillPending` are read as the flags in the state: the
  vault's message root (`_messageRoot()`, `:491-493`) and the message root's vault
  (`assetRouter().nativeTokenVault()`, `L1MessageRoot.sol:77-79`) are taken to be the modelled
  ones (`OPS-CONFIG`).
* `initialize()` (the `initializer`) is not a step: it writes neither the ledger nor the flags,
  and moves the version only from 0 to 1, below 2 either way.
* `bridgedOut` is kept because the hooks can revert on it; no statement here is about it.
* Events are not modelled.
-/

namespace Contracts.L1NativeTokenVault.InteropPool

/-- Chain ids are `uint256`. -/
abbrev ChainId := UInt256

/-- Asset ids are `bytes32`, here 256-bit words. -/
abbrev AssetId := UInt256

/-- `INTEROP_POOL_CHAIN_ID = uint256(keccak256("interop.pool")) - 1` (`common/Config.sol:37`),
computed off-line: `cast keccak "interop.pool"` is
`0x9cc761dc886485f14b36f25560c0fb8022a9b62e0778612e6cc02bf213382d0a`. Only the fact
`chainIdCap ≤ interopPoolChainId.val` is used, and the proofs check it by `decide`. -/
def interopPoolChainId : ChainId :=
  0x9cc761dc886485f14b36f25560c0fb8022a9b62e0778612e6cc02bf213382d09

/-- The Bridgehub's bound: `_chainId > type(uint48).max` reverts with `ChainIdTooBig`
(`core/bridgehub/BridgehubBase.sol:496-499`), so a registered chain id is below `2^48`. -/
def chainIdCap : ℕ := 2 ^ 48

/-- `map[k] = v` on a one-level mapping. -/
def setAt {β : Type} (f : UInt256 → β) (k : UInt256) (v : β) : UInt256 → β :=
  fun k' => if k' = k then v else f k'

/-- `map[c][a] = v` on a two-level mapping. -/
def setAt2 {β : Type} (f : ChainId → AssetId → β) (c : ChainId) (a : AssetId) (v : β) :
    ChainId → AssetId → β :=
  fun c' a' => if c' = c ∧ a' = a then v else f c' a'

/-- The last line of `_netChainBalance` (`:487`): `balance > withdrawn ? balance - withdrawn : 0`. -/
def netOf (balance withdrawn : ℕ) : ℕ :=
  if withdrawn < balance then balance - withdrawn else 0

/-! ## State -/

/-- The vault's ledger, the message root's interop flags, the Bridgehub's registry, and a ghost.
Storage values are naturals; every write below is checked against `2^256`, as the `uint256`
arithmetic is. -/
structure PoolSys where
  /-- `bridgedOut[assetId]` (`L1NativeTokenVault.sol:90`). -/
  bridgedOut : AssetId → ℕ
  /-- `chainTotalDeposited[chainId][assetId]` (`:96`). The pool's totals are at
  `interopPoolChainId`. -/
  deposited : ChainId → AssetId → ℕ
  /-- `chainTotalWithdrawn[chainId][assetId]` (`:99`). -/
  withdrawn : ChainId → AssetId → ℕ
  /-- `chainBalanceBackfill[chainId][assetId]` (`:102`). -/
  backfill : ChainId → AssetId → ℕ
  /-- `chainBalanceInInteropPool[chainId][assetId]` (`:105`). -/
  inPool : ChainId → AssetId → Bool
  /-- `chainBalanceBackfillPending[chainId]` (`:108`). -/
  pending : ChainId → Bool
  /-- The vault proxy's OpenZeppelin `_initialized` version. -/
  initVersion : ℕ
  /-- `L1MessageRoot.interopEnabled[chainId]` (`L1MessageRoot.sol:49`), what
  `isInteropEnabled` returns (`:92-94`). -/
  interop : ChainId → Bool
  /-- Whether the chain id is a key of the Bridgehub's `zkChainMap`
  (`BridgehubBase.sol:337-347`). -/
  registered : ChainId → Bool
  /-- **Ghost, not storage.** Written only by `toChain`, which adds to it what it adds to
  `chainTotalDeposited[INTEROP_POOL_CHAIN_ID][assetId]`; zero in a `PreUpgrade` state. So along a
  run from there it is the sum of the deposits credited to the pool's key. -/
  directToPool : AssetId → ℕ

/-! ## The functions -/

/-- `_trackedBalance(chain, origin)` (`L1NativeTokenVault.sol:468-477`): whether the asset's
balance is tracked, and the chain id whose totals record it. -/
def trackedBalance (s : PoolSys) (chain origin : ChainId) : Bool × ChainId :=
  if s.interop chain = true then (!s.interop origin, interopPoolChainId)
  else (decide (origin ≠ chain), chain)

/-- **`_handleBridgeToChain(chain, asset, amount)`** (`:424-433`), with `origin` the value of
`originChainId[asset]` and `l1` the value of `block.chainid`. The ghost gains the amount exactly
when it is credited to the pool's key. -/
def handleBridgeToChain (l1 : ChainId) (s : PoolSys) (chain asset : ChainId) (amount : UInt256)
    (origin : ChainId) : Option PoolSys :=
  if origin = l1 ∧ UInt256.size ≤ s.bridgedOut asset + amount.val then none
  else
    let bridgedOut' :=
      if origin = l1 then setAt s.bridgedOut asset (s.bridgedOut asset + amount.val)
      else s.bridgedOut
    if (trackedBalance s chain origin).1 = true then
      let key := (trackedBalance s chain origin).2
      if UInt256.size ≤ s.deposited key asset + amount.val then none
      else some { s with
        bridgedOut := bridgedOut'
        deposited := setAt2 s.deposited key asset (s.deposited key asset + amount.val)
        directToPool :=
          if key = interopPoolChainId then setAt s.directToPool asset (s.directToPool asset + amount.val)
          else s.directToPool }
    else some { s with bridgedOut := bridgedOut' }

/-- **`_handleBridgeFromChain(chain, asset, amount)`** (`:439-459`). The cap check runs unless
the key is pending; its sum is checked too. -/
def handleBridgeFromChain (l1 : ChainId) (s : PoolSys) (chain asset : ChainId) (amount : UInt256)
    (origin : ChainId) : Option PoolSys :=
  if origin = l1 ∧ s.bridgedOut asset < amount.val then none
  else
    let bridgedOut' :=
      if origin = l1 then setAt s.bridgedOut asset (s.bridgedOut asset - amount.val)
      else s.bridgedOut
    if (trackedBalance s chain origin).1 = true then
      let key := (trackedBalance s chain origin).2
      if UInt256.size ≤ s.withdrawn key asset + amount.val then none
      else if s.pending key = false ∧
          (UInt256.size ≤ s.deposited key asset + s.backfill key asset ∨
            s.deposited key asset + s.backfill key asset < s.withdrawn key asset + amount.val) then
        none
      else some { s with
        bridgedOut := bridgedOut'
        withdrawn := setAt2 s.withdrawn key asset (s.withdrawn key asset + amount.val) }
    else some { s with bridgedOut := bridgedOut' }

/-- **One entry of `setChainBalanceBackfill(chain, assets, amounts)`** (`:219-239`). For a pair
already in the pool, the pool's deposits gain
`_netChainBalance(chain, asset, amount) - _netChainBalance(chain, asset, 0)`. The first
`_netChainBalance` checks `deposited + amount`; once that passes, the second one's
`deposited + 0` cannot overflow, so it has no guard here. The subtraction and the `+=` are
checked. -/
def setChainBalanceBackfill (s : PoolSys) (chain asset : ChainId) (amount : UInt256) :
    Option PoolSys :=
  if chain = interopPoolChainId then none
  else if s.backfill chain asset ≠ 0 then none
  else if s.inPool chain asset = true then
    if UInt256.size ≤ s.deposited chain asset + amount.val then none
    else
      let n₁ := netOf (s.deposited chain asset + amount.val) (s.withdrawn chain asset)
      let n₀ := netOf (s.deposited chain asset + 0) (s.withdrawn chain asset)
      if n₁ < n₀ then none
      else if UInt256.size ≤ s.deposited interopPoolChainId asset + (n₁ - n₀) then none
      else some { s with
        deposited := setAt2 s.deposited interopPoolChainId asset
          (s.deposited interopPoolChainId asset + (n₁ - n₀))
        backfill := setAt2 s.backfill chain asset amount.val }
  else some { s with backfill := setAt2 s.backfill chain asset amount.val }

/-- **`markBackfilled(chain)`** (`:242-246`). -/
def markBackfilled (s : PoolSys) (chain : ChainId) : Option PoolSys :=
  if s.pending chain = true then some { s with pending := setAt s.pending chain false } else none

/-- **`moveChainBalanceToInteropPool(chain, asset)`** (`:249-258`). -/
def moveChainBalanceToInteropPool (s : PoolSys) (chain asset : ChainId) : Option PoolSys :=
  if s.interop chain = false then none
  else if s.pending chain = true then none
  else if s.inPool chain asset = true then none
  else if UInt256.size ≤ s.deposited chain asset + s.backfill chain asset then none
  else
    let amount := netOf (s.deposited chain asset + s.backfill chain asset) (s.withdrawn chain asset)
    if UInt256.size ≤ s.deposited interopPoolChainId asset + amount then none
    else some { s with
      inPool := setAt2 s.inPool chain asset true
      deposited := setAt2 s.deposited interopPoolChainId asset
        (s.deposited interopPoolChainId asset + amount) }

/-- **`L1MessageRoot.enableInterop(chain, _)`** (`L1MessageRoot.sol:72-89`), without the caller
and second-proof-system checks. -/
def enableInterop (s : PoolSys) (chain : ChainId) : Option PoolSys :=
  if s.registered chain = false then none
  else if s.interop chain = true then none
  else if s.pending chain = true then none
  else some { s with interop := setAt s.interop chain true }

/-- **`initializeUpgrade()`** (`L1NativeTokenVault.sol:291-298`): `reinitializer(2)` succeeds
only below version 2 and sets it; every registered chain becomes pending. -/
def initializeUpgrade (s : PoolSys) : Option PoolSys :=
  if s.initVersion < 2 then
    some { s with initVersion := 2, pending := fun c => s.pending c || s.registered c }
  else none

/-- **Chain registration** in the Bridgehub (`createNewChain`, `registerAlreadyDeployedZKChain`),
with `_validateChainParams`' chain-id checks (`BridgehubBase.sol:492-503, :534-536`). -/
def registerChain (l1 : ChainId) (s : PoolSys) (chain : ChainId) : Option PoolSys :=
  if chain.val = 0 ∨ chainIdCap ≤ chain.val ∨ chain = l1 ∨ s.registered chain = true then none
  else some { s with registered := setAt s.registered chain true }

/-- **One entry of `populateBridgedOut(assetIds)`** (`L1NativeTokenVault.sol:189-212`), with the
legacy amount as an input: `bridgedOut[asset] += amount`, checked (`:207`). The once-per-asset flag
(`:198-201`) and `legacyBridgedOut`'s L1-origin check (`:157`) only reject, and are dropped. It
writes nothing else this model keeps. -/
def populateBridgedOutEntry (s : PoolSys) (asset : AssetId) (amount : UInt256) : Option PoolSys :=
  if UInt256.size ≤ s.bridgedOut asset + amount.val then none
  else some { s with bridgedOut := setAt s.bridgedOut asset (s.bridgedOut asset + amount.val) }

/-! ## Calls and runs -/

/-- One call that writes the ledger or the flags. `origin` is the value of
`originChainId[asset]` when the hook runs. -/
inductive PoolCall where
  /-- `_handleBridgeToChain`, reached from a deposit's `bridgeBurn`. -/
  | toChain (chain asset : ChainId) (amount : UInt256) (origin : ChainId)
  /-- `_handleBridgeFromChain`, reached from a withdrawal or a failed-deposit claim. -/
  | fromChain (chain asset : ChainId) (amount : UInt256) (origin : ChainId)
  /-- One entry of the owner's `setChainBalanceBackfill`. -/
  | setBackfill (chain asset : ChainId) (amount : UInt256)
  /-- The owner's `markBackfilled`. -/
  | markBackfilled (chain : ChainId)
  /-- `moveChainBalanceToInteropPool`, by anyone. -/
  | move (chain asset : ChainId)
  /-- The Bridgehub owner's `L1MessageRoot.enableInterop`. -/
  | enableInterop (chain : ChainId)
  /-- The proxy admin's `initializeUpgrade`. -/
  | initializeUpgrade
  /-- Registration of a chain in the Bridgehub. -/
  | register (chain : ChainId)
  /-- One entry of `populateBridgedOut`, by anyone. -/
  | populateBridgedOut (asset : AssetId) (amount : UInt256)
  deriving DecidableEq

/-- **One successful call.** `none` is a revert. `l1` is L1's chain id (`block.chainid`). -/
def poolCall (l1 : ChainId) : PoolCall → PoolSys → Option PoolSys
  | .toChain c a x o, s => handleBridgeToChain l1 s c a x o
  | .fromChain c a x o, s => handleBridgeFromChain l1 s c a x o
  | .setBackfill c a x, s => setChainBalanceBackfill s c a x
  | .markBackfilled c, s => markBackfilled s c
  | .move c a, s => moveChainBalanceToInteropPool s c a
  | .enableInterop c, s => enableInterop s c
  | .initializeUpgrade, s => initializeUpgrade s
  | .register c, s => registerChain l1 s c
  | .populateBridgedOut a x, s => populateBridgedOutEntry s a x

/-- **A run**: the calls succeed in order. A reverted call is not a step. -/
inductive PoolRun (l1 : ChainId) : PoolSys → List PoolCall → PoolSys → Prop
  | nil (s : PoolSys) : PoolRun l1 s [] s
  | cons {s m t : PoolSys} {call : PoolCall} {calls : List PoolCall} :
      poolCall l1 call s = some m → PoolRun l1 m calls t → PoolRun l1 s (call :: calls) t

/-- The calls run one after another; `none` if one of them reverts. -/
def runPoolCalls (l1 : ChainId) : List PoolCall → PoolSys → Option PoolSys
  | [], s => some s
  | call :: calls, s => (poolCall l1 call s).bind (runPoolCalls l1 calls)

/-- The chain id a call names, if any: the hook's `chain` argument, the backfill's or move's
chain, or the chain enabled or registered. `initializeUpgrade` and `populateBridgedOut` name
none. -/
def PoolCall.chainArg : PoolCall → Option ChainId
  | .toChain c _ _ _ => some c
  | .fromChain c _ _ _ => some c
  | .setBackfill c _ _ => some c
  | .markBackfilled c => some c
  | .move c _ => some c
  | .enableInterop c => some c
  | .initializeUpgrade => none
  | .register c => some c
  | .populateBridgedOut _ _ => none

/-- What a call credits to the pool's deposits of `asset` as a direct deposit: the amount of a
`toChain` call for `asset` whose balance is tracked under the pool's key in `s`, else zero. -/
def poolKeyedDeposit (s : PoolSys) : PoolCall → AssetId → ℕ
  | .toChain c a' x o, a =>
      if a' = a ∧ trackedBalance s c o = (true, interopPoolChainId) then x.val else 0
  | _, _ => 0

/-! ## The pool's books -/

/-- What chain `chain` contributes to the pool for `asset`: `net(chain, asset, backfill)`
`= max(0, deposited + backfill - withdrawn)` if the pair was moved, else zero. -/
def netTerm (s : PoolSys) (asset : AssetId) (chain : ChainId) : ℕ :=
  if s.inPool chain asset = true then
    s.deposited chain asset + s.backfill chain asset - s.withdrawn chain asset
  else 0

/-- The moved balances of `asset`, summed over every chain id. -/
def movedNet (s : PoolSys) (asset : AssetId) : ℕ :=
  ∑ c : ChainId, netTerm s asset c

/-- **The flag invariant.** After the upgrade: the version is at least 2; the pool's key is not
registered; enabled and pending chains are registered; an enabled chain is not pending; a moved
pair's chain is enabled; the pool's key has no backfill. -/
structure PoolFlagInv (s : PoolSys) : Prop where
  upgraded : 2 ≤ s.initVersion
  poolUnregistered : s.registered interopPoolChainId = false
  interopRegistered : ∀ c, s.interop c = true → s.registered c = true
  pendingRegistered : ∀ c, s.pending c = true → s.registered c = true
  interopNotPending : ∀ c, s.interop c = true → s.pending c = false
  inPoolInterop : ∀ c a, s.inPool c a = true → s.interop c = true
  poolNoBackfill : ∀ a, s.backfill interopPoolChainId a = 0

/-- **The pool identity.** The pool's deposits of each asset are the direct deposits plus the
moved balances, each at its current backfill. -/
def PoolIdentity (s : PoolSys) : Prop :=
  ∀ a, s.deposited interopPoolChainId a = s.directToPool a + movedNet s a

/-- The pool's withdrawals of each asset are at most its deposits. -/
def PoolCovered (s : PoolSys) : Prop :=
  ∀ a, s.withdrawn interopPoolChainId a ≤ s.deposited interopPoolChainId a

/-- **The state just before `initializeUpgrade`, with no chain enabled yet.** Below version 2;
no chain enabled and no pair moved (`interopEnabled` and `chainBalanceInInteropPool` are new
at v35); a pending chain is registered (at the upgrade the flags are new and all false); the
pool's key is not registered (every registered id passed the `uint48` bound); the pool's totals
and backfill are zero, and so is the ghost. Other chains' totals are not constrained. -/
structure PreUpgrade (s : PoolSys) : Prop where
  version : s.initVersion < 2
  noInterop : ∀ c, s.interop c = false
  noneInPool : ∀ c a, s.inPool c a = false
  pendingRegistered : ∀ c, s.pending c = true → s.registered c = true
  poolUnregistered : s.registered interopPoolChainId = false
  poolDepositedZero : ∀ a, s.deposited interopPoolChainId a = 0
  poolWithdrawnZero : ∀ a, s.withdrawn interopPoolChainId a = 0
  poolBackfillZero : ∀ a, s.backfill interopPoolChainId a = 0
  noDirect : ∀ a, s.directToPool a = 0

end Contracts.L1NativeTokenVault.InteropPool
