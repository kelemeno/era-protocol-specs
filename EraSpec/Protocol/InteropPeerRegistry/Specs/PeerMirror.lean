import Mathlib.Tactic

/-!
# Model: the interop-peer whitelist on L1, its mirror in every chain's `L2Bridgehub`, and the
# `baseTokenAssetId` entries both write

**Commit.** matter-labs/era-contracts, branch `draft/v0.35.0` at
`b17415d20` (the v35 head). Paths are relative to `l1-contracts/contracts/` unless they start
with `protocol-docs/`. Abbreviations: `CRS` is `core/chain-registration/ChainRegistrationSender.sol`,
`L2BH` is `core/bridgehub/L2Bridgehub.sol`, `BB` is `core/bridgehub/BridgehubBase.sol`, `L1BH` is
`core/bridgehub/L1Bridgehub.sol`, `CAH` is `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
`MB` is `state-transition/chain-deps/facets/Mailbox.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.InteropPeerRegistry.Properties.PeerMirror`, proofs in
`EraSpec.Protocol.InteropPeerRegistry.Proofs.PeerMirror`.

## The code

On L1, `ChainRegistrationSender` keeps `interopPeerAllowed[c][p]` (`CRS:52`) and has three ways to
put an `L2Bridgehub` call into chain `c`'s priority queue:

    // allowInteropPeer(c, p), CRS:77-93
    require(getZKChain(c) != 0); require(msg.sender == admin(c));                     // :78-80
    _checkPeerPair(c, p);                                                              // :81
    require(getZKChain(p) != 0); require(!interopPeerAllowed[c][p]);                   // :82-83
    require(isInteropEnabled(c)); require(isInteropEnabled(p));                        // :84-86
    interopPeerAllowed[c][p] = true;                                                   // :88
    IMailbox(zkChain(c)).requestL2ServiceTransaction(L2_BRIDGEHUB_ADDR,
        _getL2RegistrationCalldata(p));                                                // :92

    // deregisterInteropPairs(c, ps), CRS:98-118 (owner or c's admin, :104)
    for p in ps: _checkPeerPair(c, p); delete interopPeerAllowed[c][p];                // :108-110
                 requestL2ServiceTransaction(L2_BRIDGEHUB_ADDR,
                     deregisterChainForInterop(p));                                    // :113-116

    // bridgehubDeposit(c, _, _, 0x02 ++ abi.encode(p)), CRS:124-153: the re-submission, called by
    // L1Bridgehub.requestL2TransactionTwoBridges(chainId = c, secondBridge = CRS) (L1BH:200-265)
    require(interopPeerAllowed[c][p]);                                                 // :139-142
    return {l2Contract: L2_BRIDGEHUB_ADDR, l2Calldata: _getL2RegistrationCalldata(p)}  // :144-152

    // _getL2RegistrationCalldata(p), CRS:159-168
    a = BRIDGE_HUB.baseTokenAssetId(p); require(a != 0);                               // :160-163
    require(messageRoot.chainTreeLeafCount(p) != 0);                                   // :164-166
    return abi.encodeCall(IL2Bridgehub.allowInteropPeer, (p, a));                       // :167

    // _checkPeerPair(c, p), CRS:174-182
    if (p == c || p == block.chainid || BRIDGE_HUB.settlementLayer(p) == c) revert;

The re-submission does not run `_checkPeerPair`. On chain `c`, both calls are guarded by
`onlyChainRegistrationSender` (`L2BH:45-53`: the aliased sender, or `SERVICE_TRANSACTION_SENDER`):

    function allowInteropPeer(uint256 p, bytes32 a) {                                 // L2BH:95-99
        require(a != 0); baseTokenAssetId[p] = a; isPeerAllowed[p] = true; }
    function deregisterChainForInterop(uint256 p) {                                    // L2BH:102-105
        delete baseTokenAssetId[p]; delete isPeerAllowed[p]; }

`baseTokenAssetId` has one more writer on every Bridgehub, the migration hook
`forwardedBridgeMint` (`BB:432-453`), and on L1 two creation writers (`L1BH:118`, `:312`), both
behind `chainTypeManager[p] == 0` (`BB:534-536`). `isPeerAllowed` has no other writer
(`grep -rn isPeerAllowed contracts/`).

## Where the queue entries come from

* A service transaction is written by `requestL2ServiceTransaction` (`MB:169-196`) into the
  priority tree of `c`'s diamond (`MB:291-303`, `:373-378`), with sender `SERVICE_TRANSACTION_SENDER`
  and gas limit `PRIORITY_TX_MAX_GAS_LIMIT`. Only the CRS and the L1 chain asset handler may call it
  (`state-transition/chain-deps/facets/ZKChainBase.sol:155-167`), and the handler's only call
  targets `L2_CHAIN_ASSET_HANDLER_ADDR` (`core/chain-asset-handler/L1ChainAssetHandler.sol:193-202`).
* A re-submission is an ordinary request of `L1BH.requestL2TransactionTwoBridges` with sender
  `CRS` (`L1BH:247-248`), aliased by `MB:270-272`, into the same priority tree (`MB:276`).
* A chain migrating onto a settlement layer `c` is an ordinary two-bridges request to `c` as well;
  its L2 call reaches `forwardedBridgeMint` on `c`.

So all entries for `c` sit in one FIFO queue: the priority tree of `c` (relayed unchanged to `c`'s
settlement layer when `c` settles on one, `MB:188-195`, `:277-284`). The operator executes its head;
the L2 call may succeed or fail (out of gas, `l2Value` sent to a non-payable function, or the
chain's `L2Bridgehub` not yet upgraded, `protocol-docs/interop-gating.md:172-173`), and either way
the entry is consumed.

## Migrations (latent at `b17415d20`)

`CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`), and the chain asset handler's
`bridgeBurn` and `bridgeMint` are `whenMigrationsEnabled` (`CAH:151-156`, `:201`, `:365`); only the
failure confirmation is not (`core/chain-asset-handler/L1ChainAssetHandler.sol:119-120`). The model
keeps the migration steps anyway, so the presence results below are about that disabled path: at
`b17415d20` their premise (`p` settles on `c`) can hold only for a chain that moved onto `c` before
v35. All other results hold with the migration steps enabled.

* **Out to a settlement layer `c`** (`CAH.bridgeBurn` on L1, `CAH:188-254`): the L1 Bridgehub's
  `forwardedBridgeBurnSetSettlementLayer` requires `settlementLayer[p] == block.chainid` and writes
  `settlementLayer[p] = c` (`BB:403-421`); `_buildBridgehubMintData` reads L1's
  `baseTokenAssetId(p)` (`CAH:322`) into the mint data, sent to `c`'s queue.
* **Arrival on `c`** (that queue entry): `CAH.bridgeMint` → `c`'s `forwardedBridgeMint`
  (`BB:432-453`): reverts `AlreadyCurrentSL` if `settlementLayer[p] == block.chainid`, then writes
  `settlementLayer[p] = c` and `baseTokenAssetId[p] = data.assetId`.
* **Back to L1** (on `c`): `CAH.bridgeBurn` → `c`'s `forwardedBridgeBurnSetSettlementLayer(p, L1)`
  requires `settlementLayer[p] == c` and writes `L1` (`BB:411-414`); `CAH:322` reads `c`'s
  `baseTokenAssetId(p)` into the withdrawal message (a settlement layer may only send to L1,
  `CAH:239-241`).
* **Finalization on L1**: `CAH.bridgeMint` → L1's `forwardedBridgeMint` writes `settlementLayer[p] =
  L1` and `baseTokenAssetId[p] = data.assetId` (`BB:441-447`), with nothing compared.
* **A failed arrival**: `L1ChainAssetHandler.bridgeConfirmTransferResult` with a failure proof
  (`core/chain-asset-handler/L1ChainAssetHandler.sol:122-172`) →
  `forwardedBridgeConfirmTransferResult` writes `settlementLayer[p] = L1` (`BB:459-468`).

## Modelling choices

* **One state for the ecosystem.** `L1State` holds the L1 Bridgehub's registry entries, the
  message root's two flags the sender reads, and the sender's map; `hub c` is chain `c`'s
  `L2Bridgehub`; `queue c` is `c`'s pending priority entries, oldest first. A revert is the absence
  of a step (`VM-REVERT`).
* **Ghost state.** `done c` logs every executed entry of `c` with its outcome, oldest first, and
  `mig p` is the migration message of `p` in flight (or `p` at home). They are not storage. `done`
  only lets the results name the executed entries; `mig` stands for the cross-chain migration
  messages, and the L1 steps that consume a message are guarded by it (`PROTO-EVIDENCE`: L1 accepts
  only messages the settlement layer sent). Every other guard is the deployed check.
* **Reject-only checks are omitted** where they read nothing modelled: admin and owner
  authorization, `whenNotPaused`, `nonReentrant`, the deposit pause of `MB:362-365`, the transaction
  filterer, migration numbers and pauses, CTM and asset-handler checks, `msg.value`, and the
  encoding byte of the re-submission. Omitting a check only adds runs. The message root's
  `isInteropEnabled` and `chainTreeLeafCount != 0` are kept as flags, so witness runs pass them too.
* **The retired registration is kept.** Pre-v35 `registerChain` queued
  `registerChainForInterop(p, baseTokenAssetId(p))` (main `70096e2ea`, CRS:69-81, :125-134); such an
  entry may still be queued at the upgrade, and fails once the chain's `L2Bridgehub` is upgraded
  (`protocol-docs/interop-gating.md:181-182`). `legacyRegister` stays enabled for the whole run; it
  writes `baseTokenAssetId` only. This adds runs.
* **The two checks the results depend on are switches** (`Config`): FIFO execution of the queue,
  and the `settlementLayer(p) == c` clause of `_checkPeerPair` in `deregisterInteropPairs`. The
  deployed system has both (`deployed`); each countermodel turns one off.
* **Registration is one flag.** `registered c` stands for both `getZKChain(c) != address(0)` and
  `chainTypeManager[c] != address(0)`, which L1's two creation paths set together (`L1BH:116`,
  `:133`; `:310`, `:315`) and nothing on L1 clears. `L1MessageRoot.enableInterop` requires it
  (`core/message-root/L1MessageRoot.sol:72-89`).
* **History before v35.** Runs start from fresh storage, and every step kind is enabled for the
  whole run, so the pre-v35 history (chain creation, the retired registration, migrations) is
  approximated by the same steps.
* **What is not modelled.** `chainTypeManager` and `zkChainMap` values, whitelisting of settlement
  layers (its consequence `c ≠ p` for a migration is a guard: `c` must be whitelisted and `p` must
  not be, `BB:407-418`), events, and other contracts' state. Upgrades of the sender, the Bridgehubs
  or the chain's `chainRegistrationSender` slot (`L2BH:127-139`, `BB:219-221`) are `OPS-CONFIG`.
  That no account other than the aliased sender and `SERVICE_TRANSACTION_SENDER` reaches the two
  `L2Bridgehub` entry points is the queue model itself (`MODEL-PEER-MIRROR` in ASSUMPTIONS.md).
-/

namespace Contracts.InteropPeerRegistry

/-! ## Words -/

/-- A chain id (`uint256`). -/
abbrev ChainId := ℕ

/-- An asset id (`bytes32`); `0` is `bytes32(0)`. -/
abbrev AssetId := ℕ

/-- Deployment constants. -/
structure Params where
  /-- `block.chainid` on L1, where the sender and the L1 Bridgehub run. -/
  l1 : ChainId

/-- Which of the two load-bearing mechanisms are present. -/
structure Config where
  /-- The operator executes `c`'s queue in order (priority tree, `MB:373-378`). -/
  fifo : Bool
  /-- `deregisterInteropPairs` runs the `settlementLayer(p) == c` clause of `_checkPeerPair`
  (`CRS:108`, `:178`). -/
  deregChecksSettlement : Bool

/-- The deployed system. -/
def deployed : Config := ⟨true, true⟩

/-- Countermodel: the queue's entries may execute in any order. -/
def withoutFifo : Config := ⟨false, true⟩

/-- Countermodel: `deregisterInteropPairs` without the `settlementLayer(p) == c` clause. -/
def withoutDeregSettlementCheck : Config := ⟨true, false⟩

/-! ## State -/

/-- What L1 holds. -/
structure L1State where
  /-- `getZKChain(c) != address(0)` (`BB:344-347`). -/
  registered : ChainId → Bool
  /-- The L1 Bridgehub's `baseTokenAssetId[c]` (`BB:96`). -/
  bt : ChainId → AssetId
  /-- The L1 Bridgehub's `settlementLayer[c]` (`BB:109`). -/
  sl : ChainId → ChainId
  /-- `L1MessageRoot.isInteropEnabled(c)` (`CRS:84-86`). -/
  interopEnabled : ChainId → Bool
  /-- `messageRoot.chainTreeLeafCount(c) != 0` (`CRS:164`). -/
  hasBatch : ChainId → Bool
  /-- `ChainRegistrationSender.interopPeerAllowed[c][p]` (`CRS:52`). -/
  allowed : ChainId → ChainId → Bool

/-- One chain's `L2Bridgehub`, per other chain `p`. -/
structure Hub where
  /-- `isPeerAllowed[p]` (`L2BH:43`). -/
  peer : ChainId → Bool
  /-- `baseTokenAssetId[p]` (`BB:96`). -/
  bta : ChainId → AssetId
  /-- `settlementLayer[p]` (`BB:109`). -/
  sl : ChainId → ChainId

/-- A priority-queue entry of a chain `c`, by the `L2Bridgehub` call it makes on `c`. -/
inductive Msg where
  /-- `allowInteropPeer(p, a)` (`L2BH:95-99`). `service` is `true` for the service transaction of
  `CRS.allowInteropPeer` (`CRS:92`) and `false` for the re-submission (`CRS:124-153`). -/
  | allow (p : ChainId) (a : AssetId) (service : Bool)
  /-- `deregisterChainForInterop(p)` (`L2BH:102-105`), from `CRS:113-116`. -/
  | dereg (p : ChainId)
  /-- The retired `registerChainForInterop(p, a)` (pre-v35). -/
  | legacy (p : ChainId) (a : AssetId)
  /-- A migration of `p` onto `c`, ending in `forwardedBridgeMint` (`BB:432-453`) with
  `data.assetId = a`. -/
  | mint (p : ChainId) (a : AssetId)
  /-- Any other entry (deposits, other contracts' calls): it writes none of these entries. -/
  | other
deriving DecidableEq

/-- The migration message of a chain in flight (ghost). -/
inductive Mig where
  /-- No migration message in flight: the chain settles on L1, or was never created. -/
  | home
  /-- The arrival on `c` is queued on `c`. -/
  | minting (c : ChainId)
  /-- It arrived on `c`, and has not started back. -/
  | settled (c : ChainId)
  /-- Its withdrawal from `c`, carrying `baseTokenAssetId = a`, awaits finalization on L1. -/
  | returning (c : ChainId) (a : AssetId)
  /-- Its arrival on `c` failed; the failure awaits confirmation on L1. -/
  | failed (c : ChainId)
deriving DecidableEq

/-- The settlement layer a migration status refers to. -/
def Mig.layer : Mig → Option ChainId
  | .home => none
  | .minting c => some c
  | .settled c => some c
  | .returning c _ => some c
  | .failed c => some c

/-- The modelled state of the whole ecosystem. -/
structure State where
  /-- L1. -/
  l1 : L1State
  /-- Each chain's `L2Bridgehub`. -/
  hub : ChainId → Hub
  /-- Each chain's pending priority entries, oldest first. -/
  queue : ChainId → List Msg
  /-- Ghost: each chain's executed entries with their outcome (`true` = the L2 call succeeded),
  oldest first. -/
  done : ChainId → List (Msg × Bool)
  /-- Ghost: each chain's migration message in flight. -/
  mig : ChainId → Mig

/-- Fresh L1 storage. -/
def L1State.fresh : L1State :=
  ⟨fun _ => false, fun _ => 0, fun _ => 0, fun _ => false, fun _ => false, fun _ _ => false⟩

/-- Fresh `L2Bridgehub` storage. -/
def Hub.fresh : Hub := ⟨fun _ => false, fun _ => 0, fun _ => 0⟩

/-- Fresh storage everywhere, nothing queued. -/
def init : State := ⟨L1State.fresh, fun _ => Hub.fresh, fun _ => [], fun _ => [], fun _ => .home⟩

/-! ## What an entry does on its chain -/

/-- The `L2Bridgehub` of chain `c` after a successful execution of the entry, or `none` if its L2
call reverts. `allowInteropPeer` reverts on `a = 0` (`L2BH:96`); `forwardedBridgeMint` reverts if `p`
already settles on `c` (`BB:441-443`). Every other revert is the environment's choice of a failed
execution. -/
def Msg.run (c : ChainId) : Msg → Hub → Option Hub
  | .allow p a _, h =>
      if a = 0 then none
      else some { h with peer := Function.update h.peer p true, bta := Function.update h.bta p a }
  | .dereg p, h => some { h with peer := Function.update h.peer p false, bta := Function.update h.bta p 0 }
  | .legacy p a, h => some { h with bta := Function.update h.bta p a }
  | .mint p a, h =>
      if h.sl p = c then none
      else some { h with sl := Function.update h.sl p c, bta := Function.update h.bta p a }
  | .other, h => some h

/-- The ghost migration status after `c` executes the entry with outcome `ok`. -/
def Msg.migAfter (c : ChainId) (ok : Bool) (M : ChainId → Mig) : Msg → ChainId → Mig
  | .mint p _ => Function.update M p (if ok then .settled c else .failed c)
  | _ => M

/-! ## Guards -/

/-- `_checkPeerPair(c, p)` (`CRS:174-182`), as `allowInteropPeer` runs it. -/
def PeerPairOk (P : Params) (L : L1State) (c p : ChainId) : Prop :=
  p ≠ c ∧ p ≠ P.l1 ∧ L.sl p ≠ c

/-- `_checkPeerPair(c, p)` as `deregisterInteropPairs` runs it (`CRS:108`); the settlement clause
is a switch. -/
def DeregPairOk (K : Config) (P : Params) (L : L1State) (c p : ChainId) : Prop :=
  p ≠ c ∧ p ≠ P.l1 ∧ (K.deregChecksSettlement = true → L.sl p ≠ c)

/-- `interopPeerAllowed` after `allowInteropPeer(c, p)` (`CRS:88`). -/
def setAllowed (A : ChainId → ChainId → Bool) (c p : ChainId) : ChainId → ChainId → Bool :=
  fun c' p' => if c' = c ∧ p' = p then true else A c' p'

/-- `interopPeerAllowed` after `deregisterInteropPairs(c, ps)` (`CRS:110`). -/
def clearAllowed (A : ChainId → ChainId → Bool) (c : ChainId) (ps : List ChainId) :
    ChainId → ChainId → Bool :=
  fun c' p' => if c' = c ∧ p' ∈ ps then false else A c' p'

/-! ## Steps -/

/-- The transaction labels. -/
inductive Action where
  /-- `L1Bridgehub.createNewChain` or `registerAlreadyDeployedZKChain` for chain `p` with base
  token `a` (`L1BH:108-139`, `:285-319`). -/
  | createChain (p : ChainId) (a : AssetId)
  /-- `L1MessageRoot.enableInterop(c)` (`core/message-root/L1MessageRoot.sol:72-89`). -/
  | enableInterop (c : ChainId)
  /-- A batch root of `c` enters L1's message root. -/
  | pushBatch (c : ChainId)
  /-- `CRS.allowInteropPeer(c, p)`. -/
  | allowInteropPeer (c p : ChainId)
  /-- `CRS.deregisterInteropPairs(c, ps)`. -/
  | deregisterInteropPairs (c : ChainId) (ps : List ChainId)
  /-- `L1Bridgehub.requestL2TransactionTwoBridges` to `c` with the sender as second bridge and
  data `0x02 ++ abi.encode(p)`. -/
  | resubmit (c p : ChainId)
  /-- The retired `registerChain(p, c)` (pre-v35). -/
  | legacyRegister (c p : ChainId)
  /-- Any other L1 request to `c`. -/
  | otherRequest (c : ChainId)
  /-- Chain `c` executes the entry at position `i` of its queue with outcome `ok`. -/
  | execute (c : ChainId) (i : ℕ) (ok : Bool)
  /-- On L1, `p` starts migrating to settlement layer `c`. -/
  | migrateToLayer (p c : ChainId)
  /-- On `c`, `p` starts migrating back to L1. -/
  | burnOnLayer (p c : ChainId)
  /-- On L1, `p`'s return is finalized. -/
  | finalizeReturn (p : ChainId)
  /-- On L1, `p`'s failed arrival is confirmed. -/
  | confirmFailedMigration (p : ChainId)

/-- One successful transaction. -/
inductive Step (K : Config) (P : Params) : State → Action → State → Prop where
  /-- Chain creation: `_validateChainParams` (`BB:491-537`) requires a nonzero id other than
  L1's, a nonzero asset id and no CTM yet; then `baseTokenAssetId[p] = a`,
  `settlementLayer[p] = block.chainid` (`L1BH:116-119`, `:310-313`). -/
  | createChain {S : State} {p : ChainId} {a : AssetId} :
      S.l1.registered p = false → p ≠ 0 → p ≠ P.l1 → a ≠ 0 →
      Step K P S (.createChain p a)
        { S with l1 := { S.l1 with
            registered := Function.update S.l1.registered p true
            bt := Function.update S.l1.bt p a
            sl := Function.update S.l1.sl p P.l1 } }
  /-- `isInteropEnabled(c)` becomes true (one-way). -/
  | enableInterop {S : State} {c : ChainId} :
      S.l1.registered c = true →
      Step K P S (.enableInterop c)
        { S with l1 := { S.l1 with interopEnabled := Function.update S.l1.interopEnabled c true } }
  /-- `chainTreeLeafCount(c)` becomes nonzero (it never decreases). -/
  | pushBatch {S : State} {c : ChainId} :
      S.l1.registered c = true →
      Step K P S (.pushBatch c)
        { S with l1 := { S.l1 with hasBatch := Function.update S.l1.hasBatch c true } }
  /-- `CRS.allowInteropPeer(c, p)` (`CRS:77-93`), with `_getL2RegistrationCalldata(p)`
  (`CRS:159-168`): the entry carries L1's `baseTokenAssetId(p)`. -/
  | allowInteropPeer {S : State} {c p : ChainId} :
      S.l1.registered c = true → PeerPairOk P S.l1 c p → S.l1.registered p = true →
      S.l1.allowed c p = false → S.l1.interopEnabled c = true → S.l1.interopEnabled p = true →
      S.l1.bt p ≠ 0 → S.l1.hasBatch p = true →
      Step K P S (.allowInteropPeer c p)
        { S with
          l1 := { S.l1 with allowed := setAllowed S.l1.allowed c p }
          queue := Function.update S.queue c (S.queue c ++ [.allow p (S.l1.bt p) true]) }
  /-- `CRS.deregisterInteropPairs(c, ps)` (`CRS:98-118`): all of `ps` pass, or nothing happens. -/
  | deregisterInteropPairs {S : State} {c : ChainId} {ps : List ChainId} :
      S.l1.registered c = true → (∀ p ∈ ps, DeregPairOk K P S.l1 c p) →
      Step K P S (.deregisterInteropPairs c ps)
        { S with
          l1 := { S.l1 with allowed := clearAllowed S.l1.allowed c ps }
          queue := Function.update S.queue c (S.queue c ++ ps.map Msg.dereg) }
  /-- The re-submission (`CRS:124-153` through `L1BH:200-265`): no `_checkPeerPair`. -/
  | resubmit {S : State} {c p : ChainId} :
      S.l1.registered c = true → S.l1.allowed c p = true → S.l1.bt p ≠ 0 →
      S.l1.hasBatch p = true →
      Step K P S (.resubmit c p)
        { S with queue := Function.update S.queue c (S.queue c ++ [.allow p (S.l1.bt p) false]) }
  /-- The retired registration: it queued `registerChainForInterop(p, baseTokenAssetId(p))`
  (main `70096e2ea`, CRS:125-134). -/
  | legacyRegister {S : State} {c p : ChainId} :
      S.l1.registered c = true → S.l1.bt p ≠ 0 → S.l1.hasBatch p = true →
      Step K P S (.legacyRegister c p)
        { S with queue := Function.update S.queue c (S.queue c ++ [.legacy p (S.l1.bt p)]) }
  /-- Any other request to `c`. -/
  | otherRequest {S : State} {c : ChainId} :
      S.l1.registered c = true →
      Step K P S (.otherRequest c) { S with queue := Function.update S.queue c (S.queue c ++ [.other]) }
  /-- `c` executes an entry and its L2 call succeeds. With `fifo` it must be the head. -/
  | executeOk {S : State} {c : ChainId} {pre post : List Msg} {m : Msg} {h : Hub} :
      S.queue c = pre ++ m :: post → (K.fifo = true → pre = []) → m.run c (S.hub c) = some h →
      Step K P S (.execute c pre.length true)
        { S with
          hub := Function.update S.hub c h
          queue := Function.update S.queue c (pre ++ post)
          done := Function.update S.done c (S.done c ++ [(m, true)])
          mig := m.migAfter c true S.mig }
  /-- `c` executes an entry and its L2 call fails: the entry is consumed, nothing is written. -/
  | executeFail {S : State} {c : ChainId} {pre post : List Msg} {m : Msg} :
      S.queue c = pre ++ m :: post → (K.fifo = true → pre = []) →
      Step K P S (.execute c pre.length false)
        { S with
          queue := Function.update S.queue c (pre ++ post)
          done := Function.update S.done c (S.done c ++ [(m, false)])
          mig := m.migAfter c false S.mig }
  /-- On L1, `p` leaves for `c` (`CAH:188-254`, `BB:403-421`): `p` must settle on L1, and the
  queued arrival carries L1's `baseTokenAssetId(p)` (`CAH:322`). -/
  | migrateToLayer {S : State} {p c : ChainId} :
      S.l1.registered p = true → S.l1.registered c = true → c ≠ p → c ≠ P.l1 →
      S.l1.sl p = P.l1 →
      Step K P S (.migrateToLayer p c)
        { S with
          l1 := { S.l1 with sl := Function.update S.l1.sl p c }
          queue := Function.update S.queue c (S.queue c ++ [.mint p (S.l1.bt p)])
          mig := Function.update S.mig p (.minting c) }
  /-- On `c`, `p` leaves for L1: `c`'s `settlementLayer[p]` must be `c` (`BB:411-413`); the
  withdrawal carries `c`'s `baseTokenAssetId(p)` (`CAH:322`). -/
  | burnOnLayer {S : State} {p c : ChainId} :
      S.l1.registered c = true → (S.hub c).sl p = c →
      Step K P S (.burnOnLayer p c)
        { S with
          hub := Function.update S.hub c { S.hub c with sl := Function.update (S.hub c).sl p P.l1 }
          mig := Function.update S.mig p (.returning c ((S.hub c).bta p)) }
  /-- On L1, the withdrawal from `c` is finalized: `forwardedBridgeMint` (`BB:441-447`) requires
  `settlementLayer[p] != block.chainid` and copies the carried asset id. -/
  | finalizeReturn {S : State} {p c : ChainId} {a : AssetId} :
      S.mig p = .returning c a → S.l1.sl p ≠ P.l1 →
      Step K P S (.finalizeReturn p)
        { S with
          l1 := { S.l1 with sl := Function.update S.l1.sl p P.l1, bt := Function.update S.l1.bt p a }
          mig := Function.update S.mig p .home }
  /-- On L1, a failed arrival on `c` is confirmed (`BB:459-468`). -/
  | confirmFailedMigration {S : State} {p c : ChainId} :
      S.mig p = .failed c →
      Step K P S (.confirmFailedMigration p)
        { S with
          l1 := { S.l1 with sl := Function.update S.l1.sl p P.l1 }
          mig := Function.update S.mig p .home }

/-- The states reachable from fresh storage. -/
inductive Reach (K : Config) (P : Params) : State → Prop where
  | init : Reach K P init
  | step {S S' : State} {a : Action} : Reach K P S → Step K P S a S' → Reach K P S'

/-- `S'` follows `S` by a finite sequence of steps. -/
inductive Steps (K : Config) (P : Params) : State → State → Prop where
  | refl (S : State) : Steps K P S S
  | step {S S' S'' : State} {a : Action} : Steps K P S S' → Step K P S' a S'' → Steps K P S S''

/-! ## Reading the queue and the log -/

/-- The value an entry writes to `isPeerAllowed[p]` when it succeeds, if it writes it. -/
def Msg.peerWrite (p : ChainId) : Msg → Option Bool
  | .allow q _ _ => if q = p then some true else none
  | .dereg q => if q = p then some false else none
  | _ => none

/-- A service transaction of the sender (`CRS:92`, `:113-116`), as opposed to a re-submission. -/
def Msg.isService : Msg → Bool
  | .allow _ _ s => s
  | .dereg _ => true
  | _ => false

/-- The value the last entry of `l` that writes `isPeerAllowed[p]` writes. -/
def lastPeerWrite (p : ChainId) (l : List Msg) : Option Bool :=
  l.foldl (fun acc m => (m.peerWrite p).or acc) none

/-- Whether the last executed entry that writes `isPeerAllowed[p]` succeeded (`true` if there is
none). -/
def lastPeerEntryOk (p : ChainId) (d : List (Msg × Bool)) : Bool :=
  d.foldl (fun acc e => if (e.1.peerWrite p).isSome then e.2 else acc) true

/-- No pending entry writes `isPeerAllowed[p]`. -/
def NoPendingPeerEntry (p : ChainId) (q : List Msg) : Prop :=
  ∀ m ∈ q, m.peerWrite p = none

end Contracts.InteropPeerRegistry
