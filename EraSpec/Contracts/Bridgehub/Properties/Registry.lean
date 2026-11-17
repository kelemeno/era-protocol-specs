import EraSpec.Contracts.Bridgehub.Specs.Registry

/-!
# Properties: `L1Bridgehub`

Statements about `EraSpec.Contracts.Bridgehub.Specs.Registry`. Proofs are in
`EraSpec.Contracts.Bridgehub.Proofs.Registry`. Every run-level statement quantifies over
`Run`, so over every entry point of the model and every interleaving of callers.

## Chain registration

* A chain id is registered at most once in any run, from any starting state, and never
  if it already has a CTM (`ChainIdRegisteredOnce`). The reason is that no entry point
  ever clears `chainTypeManager[c]` (`CtmNeverCleared`).
* Every chain with a CTM uses a registered base-token asset id (`ChainBaseTokenRegistered`),
  and its CTM was added by `addChainTypeManager` earlier in the run
  (`ChainCtmWasApproved`). The CTM need not still be registered: `removeChainTypeManager`
  does not touch existing chains, by design.
* A successful `createNewChain` / `registerAlreadyDeployedZKChain` had a registered CTM
  and a registered base-token asset id at that moment, sets exactly that chain's CTM, base
  token, settlement layer (this chain) and diamond, and leaves every other chain alone
  (`CreateNewChainPostcondition`, `RegisterDeployedPostcondition`). No entry point
  unregisters an asset id (`AssetIdNeverUnregistered`).
* Outside `forwardedBridgeMint`, a registered chain's CTM and base token never change
  (`CtmAndBaseTokenFixedOutsideBridgeMint`). `forwardedBridgeMint`, callable only by the
  chain asset handler, rewrites both (`BridgeMintRewritesBaseToken`): the Bridgehub trusts
  the handler for that.
* While a chain settles here, nothing changes its CTM or base token, `forwardedBridgeMint`
  included: they can change only after a `forwardedBridgeBurnSetSettlementLayer` for that
  chain (`CtmAndBaseTokenFixedWhileSettlingHere`). The `AlreadyCurrentSL` check in the mint
  hook and the `BridgeHubAlreadyRegistered` check in `_validateChainParams` are
  load-bearing (`WithoutCurrentSLCheckBaseTokenRewritten`,
  `WithoutAlreadyRegisteredCheckChainReRegistered`).
* Without the chain asset handler's two registry writers, `zkChainMap` and
  `chainTypeManager` describe the same chains, every key has a nonzero diamond, and the
  chain count stays within `MAX_NUMBER_OF_ZK_CHAINS` (`RegistryConsistentWithoutHandler`,
  `ChainCountBounded`). With them, `createNewChain` silently overwrites a map entry the
  handler wrote (`HandlerEntryOverwrittenByCreate`).
* `zkChainMap` only grows, and `get` succeeds exactly for its keys, whatever is called
  (`ChainMapOnlyGrows`). A chain's diamond changes only through the handler's
  `registerNewZKChain` for that chain, or through its own registration while it has no CTM
  (`DiamondChangesOnlyByRegistration`); so once a chain has a CTM its diamond is fixed in
  any run without a `registerNewZKChain` for it (`DiamondFixedAfterRegistration`). That
  handler call does replace it: the Bridgehub ignores `set`'s return value
  (`HandlerRegisterReplacesDiamond`).
* `ctmAssetIdFromAddress` then `ctmAssetIdToAddress` returns the CTM, unless the asset-id
  hash collides at two CTM addresses, provided every `setCTMAssetAddress` passes the CTM
  address as its data, as `CTMDeploymentTracker` does (`CtmAssetIdRoundTrip`). The
  Bridgehub does not enforce that discipline (`CtmAssetIdRoundTripNeedsDiscipline`).

## Settlement layers

* Every whitelisted settlement layer other than this chain settles on this chain
  (`WhitelistedSettlementLayersSettleHere`). The `SettlementLayersMustSettleOnL1` check
  in `forwardedBridgeBurnSetSettlementLayer` is load-bearing
  (`WithoutCheckWhitelistedLayerLeaves`).
* A chain's settlement layer moves away from this chain only through the chain asset
  handler's `forwardedBridgeBurnSetSettlementLayer`, to a whitelisted layer, and only for
  a chain that settled here (`MigrationOutOnlyToWhitelisted`).
* Run level: a settlement layer other than `0` and this chain was written by a burn for
  that chain in the run, and is never the chain itself
  (`RemoteSettlementLayerCameFromBurn`); the target of a burn settles here at that moment
  (`MigrationTargetSettlesHere`).
* Not guaranteed: that the layer a chain is recorded on still settles here later. Once the
  owner removes a layer from the whitelist, the handler can migrate it away with chains
  still recorded on it (`SettlementLayerOfAChainNeedNotSettleHere`).

## Requests

* Both request paths forward all of `msg.value` and keep none; the asset router receives
  exactly `mintValue` in ETH for an ETH-based chain and nothing otherwise; the base-token
  deposit and the Mailbox request carry the same `mintValue`, for the same chain, in that
  chain's base token (`DirectRequestAccounting`, `TwoBridgesRequestAccounting`).
* In a run without the handler's registry writers, a request reaches the registered,
  nonzero diamond of a chain with a CTM and is charged in a registered asset
  (`RequestsReachRegisteredChains`). With them allowed too, a request still needs a
  `zkChainMap` key and goes to that key's diamond (`RequestNeedsMapEntry`). After
  `createNewChain(c, _, a, _, d)` and no later `forwardedBridgeMint` for `c`, a request for
  `c` is charged in `a`; with no later `registerNewZKChain` for `c` it goes to `d`
  (`RequestChargesCreationBaseToken`).
* The two-bridges L2 sender is the second bridge and lies above
  `BRIDGEHUB_MIN_SECOND_BRIDGE_ADDRESS`; without that check a reserved low address can be
  the L2 sender (`WithoutMinAddressCheckLowSender`).

## Authority and pause

* Only the owner changes the CTM registry or the settlement-layer whitelist; only the
  owner, admin or chain asset handler changes a chain's CTM or settlement layer
  (`RegistryWritesAuthorized`). A paused Bridgehub creates no chain and serves no request
  (`PauseBlocksCreationAndRequests`).

## Scope of a source comment (internal; do not report upstream without Kalman)

* `removeChainTypeManager`'s NatSpec says it "stops new Chains from using the CTM". That
  holds for `createNewChain` and `registerAlreadyDeployedZKChain`, which check
  registration. `forwardedBridgeMint` does not, so a chain id this Bridgehub has never
  seen can still be given a removed CTM (`RemovedCtmStillAssignedByBridgeMint`). On L1 the
  chain asset handler only lets a chain that left L1 come back
  (`ChainAssetHandlerBase.sol:374-383`), and such a chain was created with a registered
  CTM, so the run in the theorem needs a handler call the deployed handler does not make.
  `L2Bridgehub` (a settlement layer receiving chains for the first time) shares this code
  and is outside this model.

## Non-vacuity

`RegistrationWitness` reaches a state with two registered chains, one whitelisted as a
settlement layer and the other migrated to it; `RequestWitness` serves both request kinds
for a registered ETH-based chain.
-/

namespace Contracts.Bridgehub

/-! ## Chain registration -/

/-- **NO ENTRY POINT CLEARS A CHAIN'S CTM.** In any run from any state, a chain with a
nonzero `chainTypeManager` entry keeps a nonzero entry. -/
def Properties.CtmNeverCleared : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t →
    ∀ c, s.chainTypeManager c ≠ 0 → t.chainTypeManager c ≠ 0

/-- **A CHAIN ID IS REGISTERED AT MOST ONCE.** In any run from any state, at most one
successful `createNewChain` / `registerAlreadyDeployedZKChain` names chain `c`, and none
does if `c` already had a CTM. -/
def Properties.ChainIdRegisteredOnce : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t → ∀ c,
    (l.filter fun k => k.2.registers c).length ≤ 1 ∧
    (s.chainTypeManager c ≠ 0 → (l.filter fun k => k.2.registers c) = [])

/-- **EVERY CHAIN'S BASE TOKEN IS A REGISTERED ASSET.** In every reachable state, a chain
with a CTM has `assetIdIsRegistered[baseTokenAssetId[c]]`. -/
def Properties.ChainBaseTokenRegistered : Prop :=
  ∀ (cfg : Config) (s : State), Reachable cfg s →
    ∀ c, s.chainTypeManager c ≠ 0 → s.assetIdRegistered (s.baseTokenAssetId c) = true

/-- **EVERY CHAIN'S CTM WAS APPROVED.** In every run from an initialized Bridgehub, the
CTM of each chain was added by a successful `addChainTypeManager` call in that run. -/
def Properties.ChainCtmWasApproved : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    ∀ c, s.chainTypeManager c ≠ 0 →
      ∃ caller, (caller, Action.addChainTypeManager (s.chainTypeManager c)) ∈ l

/-- **CTM AND BASE TOKEN ARE FIXED OUTSIDE `forwardedBridgeMint`.** In any run from any
state that contains no `forwardedBridgeMint` for chain `c`, a chain that had a CTM at the
start ends with the same CTM and the same base-token asset id. -/
def Properties.CtmAndBaseTokenFixedOutsideBridgeMint : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t → ∀ c,
    (∀ k ∈ l, k.2.bridgeMintFor c = false) → s.chainTypeManager c ≠ 0 →
      t.chainTypeManager c = s.chainTypeManager c ∧
      t.baseTokenAssetId c = s.baseTokenAssetId c

/-- **`forwardedBridgeMint` REWRITES A REGISTERED CHAIN'S BASE TOKEN.** The boundary of
`CtmAndBaseTokenFixedOutsideBridgeMint`: a reachable state where chain `c` is registered
with base token `a`, migrated away, and the chain asset handler's `forwardedBridgeMint`
brings it back with a different base token `b`. The Bridgehub does not compare the new
value with the old one (`BB:447`). -/
def Properties.BridgeMintRewritesBaseToken : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (aid : AssetId) (c : ChainId) (b : AssetId),
    Reachable cfg s ∧ s.chainTypeManager c ≠ 0 ∧ b ≠ s.baseTokenAssetId c ∧
    exec cfg caller (.forwardedBridgeMint aid c b) s = some s' ∧
    s'.baseTokenAssetId c = b

/-- **`zkChainMap` AND `chainTypeManager` AGREE WITHOUT THE HANDLER'S WRITERS.** In a run
from an initialized Bridgehub with no `registerNewZKChain` and no `forwardedBridgeMint`,
a chain id is a key of `zkChainMap` exactly when it has a CTM, and a stored diamond is
nonzero exactly for the keys. -/
def Properties.RegistryConsistentWithoutHandler : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    (∀ k ∈ l, k.2.handlerRegistryWrite = false) →
    ∀ c, (c ∈ s.zkKeys ↔ s.chainTypeManager c ≠ 0) ∧ (c ∈ s.zkKeys ↔ s.zkAddr c ≠ 0)

/-- **`createNewChain` OVERWRITES A HANDLER-WRITTEN ENTRY.** A reachable state where chain
`c` has a `zkChainMap` entry (written by the handler's `registerNewZKChain`) but no CTM,
and `createNewChain(c, …)` succeeds in this model and replaces the stored diamond.
`createNewChain` checks only `chainTypeManager[c] == 0` (`BB:534`); `EnumerableMap.set`'s
return value is ignored (`BB:302-303`). This is about the Bridgehub's own checks: in the
deployed system the handler registers the chain with the message root too
(`ChainAssetHandlerBase.sol:405-409`), and `createNewChain`'s later
`messageRoot.addNewChain` then reverts with `ChainExists` (`MessageRootBase.sol:146-148`),
a revert this model does not include. -/
def Properties.HandlerEntryOverwrittenByCreate : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (c : ChainId) (m : Address) (a : AssetId)
    (adm d : Address),
    Reachable cfg s ∧ c ∈ s.zkKeys ∧ s.chainTypeManager c = 0 ∧ s.zkAddr c ≠ 0 ∧
    exec cfg caller (.createNewChain c m a adm d) s = some s' ∧
    s'.zkAddr c = d ∧ d ≠ s.zkAddr c

/-- **THE CHAIN COUNT STAYS WITHIN THE LIMIT.** In a run from an initialized Bridgehub
with no `registerNewZKChain(_, _, false)`, `zkChainMap.length() ≤ MAX_NUMBER_OF_ZK_CHAINS`. -/
def Properties.ChainCountBounded : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    (∀ k ∈ l, k.2.uncheckedRegistration = false) → s.zkKeys.card ≤ cfg.maxChains

/-- **THE CTM ASSET ID ROUND-TRIPS, UP TO A PINNED COLLISION.** In a run from an
initialized Bridgehub where every `setCTMAssetAddress(data, m)` has `data = m` (what
`CTMDeploymentTracker` sends), every CTM `m` with a nonzero `ctmAssetIdFromAddress[m]`
satisfies `ctmAssetIdToAddress[ctmAssetIdFromAddress[m]] = m`, unless the asset-id hash
maps `m` and some other address `m'` (with some senders) to the same id. No injectivity
is assumed. -/
def Properties.CtmAssetIdRoundTrip : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    (∀ k ∈ l, k.2.ctmAssetDisciplined = true) →
    ∀ m, s.ctmAssetIdFromAddress m ≠ 0 →
      s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) = m ∨
      ∃ m' dep dep', m' ≠ m ∧
        cfg.encodeAssetId cfg.thisChain m dep = cfg.encodeAssetId cfg.thisChain m' dep'

/-- **THE ROUND TRIP NEEDS THE CALLER'S DISCIPLINE.** With an injective asset-id hash, so
no collision at all, two `setCTMAssetAddress` calls with the same data for different CTMs
reach a state where the round trip fails. -/
def Properties.CtmAssetIdRoundTripNeedsDiscipline : Prop :=
  ∃ (cfg : Config) (s : State) (m : Address),
    (∀ x y d d', cfg.encodeAssetId x d y = cfg.encodeAssetId x d' y → d = d') ∧
    Reachable cfg s ∧ s.ctmAssetIdFromAddress m ≠ 0 ∧
    s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) ≠ m

/-! ## The chain map -/

/-- **`zkChainMap` ONLY GROWS.** In any run from any state, a key of `zkChainMap` stays a
key (no entry point removes one). In every reachable state a chain id with a nonzero
stored diamond is a key, so `zkChainMap.get(c)` succeeds exactly for the keys. Every entry
point is allowed, the chain asset handler's included. -/
def Properties.ChainMapOnlyGrows : Prop :=
  (∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t →
    ∀ c, c ∈ s.zkKeys → c ∈ t.zkKeys) ∧
  (∀ (cfg : Config) (s : State), Reachable cfg s → ∀ c, ZkGetOk s c ↔ c ∈ s.zkKeys)

/-- **WHO CHANGES A CHAIN'S DIAMOND.** For every successful call of every entry point: if
`getZKChain(c)` changes, the call is either the chain asset handler's
`registerNewZKChain(c, …)`, or a `createNewChain` / `registerAlreadyDeployedZKChain` for
`c`, by the owner or the admin, at a moment when `c` had no CTM. -/
def Properties.DiamondChangesOnlyByRegistration : Prop :=
  ∀ (cfg : Config) (caller : Address) (a : Action) (s s' : State) (c : ChainId),
    exec cfg caller a s = some s' → getZKChain s' c ≠ getZKChain s c →
    (∃ z chk, a = .registerNewZKChain c z chk ∧ caller = s.chainAssetHandler) ∨
    (a.registers c = true ∧ s.chainTypeManager c = 0 ∧ (caller = s.owner ∨ caller = s.admin))

/-- **A REGISTERED CHAIN'S DIAMOND IS FIXED, EXCEPT BY THE HANDLER'S `registerNewZKChain`.**
In any run from any state that contains no `registerNewZKChain` for chain `c`: if `c` had a
CTM at the start, `getZKChain(c)` is the same at the end. Every other entry point,
including `forwardedBridgeMint` and `registerNewZKChain` for other chains, is allowed. -/
def Properties.DiamondFixedAfterRegistration : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t → ∀ c,
    (∀ k ∈ l, k.2.handlerRegistersFor c = false) → s.chainTypeManager c ≠ 0 →
      getZKChain t c = getZKChain s c

/-- **THE HANDLER'S `registerNewZKChain` REPLACES A REGISTERED CHAIN'S DIAMOND.** The
boundary of `DiamondFixedAfterRegistration`: a reachable state where chain `c` has a CTM
and a nonzero diamond, and the chain asset handler's `registerNewZKChain(c, z, _)`
succeeds and makes `getZKChain(c) = z`, a different address. `_registerNewZKChain` ignores
`EnumerableMap.set`'s return value (`BB:302-303`), so the Bridgehub does not notice that
the key existed. The deployed handler calls it only when `forwardedBridgeMint` returned a
zero diamond (`ChainAssetHandlerBase.sol:397-405`), which this model does not include. -/
def Properties.HandlerRegisterReplacesDiamond : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (c : ChainId) (z : Address) (chk : Bool),
    Reachable cfg s ∧ s.chainTypeManager c ≠ 0 ∧ getZKChain s c ≠ 0 ∧
    exec cfg caller (.registerNewZKChain c z chk) s = some s' ∧
    getZKChain s' c = z ∧ z ≠ getZKChain s c

/-! ## Settlement layers -/

/-- **WHITELISTED SETTLEMENT LAYERS SETTLE HERE.** In every reachable state, a whitelisted
settlement layer is this chain or has `settlementLayer = block.chainid`. -/
def Properties.WhitelistedSettlementLayersSettleHere : Prop :=
  ∀ (cfg : Config) (s : State), Reachable cfg s →
    ∀ c, s.whitelistedSL c = true → c = cfg.thisChain ∨ s.settlementLayer c = cfg.thisChain

/-- **THE `SettlementLayersMustSettleOnL1` CHECK IS LOAD-BEARING.** Without it
(`burnNoSettlementLayerCheck`), a reachable whitelisted settlement layer other than this
chain migrates away and stays whitelisted. -/
def Properties.WithoutCheckWhitelistedLayerLeaves : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (c sl : ChainId),
    Reachable cfg s ∧
    burnNoSettlementLayerCheck cfg caller s c sl = some s' ∧
    s'.whitelistedSL c = true ∧ c ≠ cfg.thisChain ∧ s'.settlementLayer c ≠ cfg.thisChain

/-- **A CHAIN LEAVES ONLY FOR A WHITELISTED LAYER, AND ONLY FROM HERE.** For every
successful call of every entry point: if chain `c`'s settlement layer changes to anything
other than this chain, the call is the chain asset handler's
`forwardedBridgeBurnSetSettlementLayer(c, sl)`, `sl` was whitelisted, `c` settled here
before, and `sl` is the new value. -/
def Properties.MigrationOutOnlyToWhitelisted : Prop :=
  ∀ (cfg : Config) (caller : Address) (a : Action) (s s' : State) (c : ChainId),
    exec cfg caller a s = some s' →
    s'.settlementLayer c ≠ s.settlementLayer c → s'.settlementLayer c ≠ cfg.thisChain →
    ∃ sl, a = .burnSetSettlementLayer c sl ∧ caller = s.chainAssetHandler ∧
      s.whitelistedSL sl = true ∧ s.settlementLayer c = cfg.thisChain ∧
      s'.settlementLayer c = sl

/-! ## Registration effects, and what holds while a chain settles here -/

/-- **WHAT A SUCCESSFUL `createNewChain` ESTABLISHES.** If `createNewChain(c, m, a, adm)`
succeeds with the CTM returning diamond `d`: the caller was the owner or the admin and the
Bridgehub was not paused; `c` is nonzero, fits in 48 bits, is not this chain and had no CTM;
`m` was a nonzero registered CTM and `a` a nonzero registered asset id at that moment;
afterwards `c` has
CTM `m`, base token `a`, settles on this chain, and `getZKChain(c) = d ≠ 0`; the chain
count is within `MAX_NUMBER_OF_ZK_CHAINS`; and no other chain's CTM, base token, settlement
layer or diamond changed. -/
def Properties.CreateNewChainPostcondition : Prop :=
  ∀ (cfg : Config) (caller : Address) (s s' : State) (c : ChainId) (m : Address) (a : AssetId)
    (adm d : Address),
    exec cfg caller (.createNewChain c m a adm d) s = some s' →
    (caller = s.owner ∨ caller = s.admin) ∧ s.paused = false ∧
    c ≠ 0 ∧ c.val < 2 ^ 48 ∧ c ≠ cfg.thisChain ∧ s.chainTypeManager c = 0 ∧
    m ≠ 0 ∧ s.ctmRegistered m = true ∧ a ≠ 0 ∧ s.assetIdRegistered a = true ∧
    s'.chainTypeManager c = m ∧ s'.baseTokenAssetId c = a ∧
    s'.settlementLayer c = cfg.thisChain ∧ getZKChain s' c = d ∧ d ≠ 0 ∧
    s'.zkKeys.card ≤ cfg.maxChains ∧
    ∀ c', c' ≠ c →
      s'.chainTypeManager c' = s.chainTypeManager c' ∧
      s'.baseTokenAssetId c' = s.baseTokenAssetId c' ∧
      s'.settlementLayer c' = s.settlementLayer c' ∧ getZKChain s' c' = getZKChain s c'

/-- **WHAT A SUCCESSFUL `registerAlreadyDeployedZKChain` ESTABLISHES.** If
`registerAlreadyDeployedZKChain(c, z)` succeeds, with the diamond `z` reporting `info`: the
caller was the owner; `z` reported chain id `c` and this Bridgehub; `c` was not a key of
`zkChainMap`, had no CTM, is nonzero, fits in 48 bits and is not this chain; the reported
CTM and base token were nonzero and registered at that moment; afterwards `c` has that CTM and base
token, settles on this chain, and `getZKChain(c) = z ≠ 0`; the chain count is within the
limit; and no other chain's CTM, base token, settlement layer or diamond changed. -/
def Properties.RegisterDeployedPostcondition : Prop :=
  ∀ (cfg : Config) (caller : Address) (s s' : State) (c : ChainId) (z : Address)
    (info : DeployedChainInfo),
    exec cfg caller (.registerAlreadyDeployed c z info) s = some s' →
    caller = s.owner ∧ info.chainId = c ∧ info.bridgehub = cfg.self ∧
    c ∉ s.zkKeys ∧ s.chainTypeManager c = 0 ∧
    c ≠ 0 ∧ c.val < 2 ^ 48 ∧ c ≠ cfg.thisChain ∧
    info.ctm ≠ 0 ∧ s.ctmRegistered info.ctm = true ∧
    info.baseTokenAssetId ≠ 0 ∧ s.assetIdRegistered info.baseTokenAssetId = true ∧
    s'.chainTypeManager c = info.ctm ∧ s'.baseTokenAssetId c = info.baseTokenAssetId ∧
    s'.settlementLayer c = cfg.thisChain ∧ getZKChain s' c = z ∧ z ≠ 0 ∧
    s'.zkKeys.card ≤ cfg.maxChains ∧
    ∀ c', c' ≠ c →
      s'.chainTypeManager c' = s.chainTypeManager c' ∧
      s'.baseTokenAssetId c' = s.baseTokenAssetId c' ∧
      s'.settlementLayer c' = s.settlementLayer c' ∧ getZKChain s' c' = getZKChain s c'

/-- **NO ENTRY POINT UNREGISTERS AN ASSET ID.** In any run from any state a registered
asset id stays registered; in every reachable state the ETH asset id is registered. -/
def Properties.AssetIdNeverUnregistered : Prop :=
  (∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t →
    ∀ a, s.assetIdRegistered a = true → t.assetIdRegistered a = true) ∧
  (∀ (cfg : Config) (s : State), Reachable cfg s → s.assetIdRegistered cfg.ethAssetId = true)

/-- **CTM AND BASE TOKEN ARE FIXED WHILE THE CHAIN SETTLES HERE.** In any run from any
state that contains no `forwardedBridgeBurnSetSettlementLayer` for chain `c` (by anyone,
with any target): if `c` had a CTM and settled on this chain at the start, then at the end
it has the same CTM, the same base-token asset id, and still settles on this chain. So the
base token fixed at registration can only change after the chain asset handler has
migrated the chain away. Every other entry point, including `forwardedBridgeMint`, is
allowed in the run. -/
def Properties.CtmAndBaseTokenFixedWhileSettlingHere : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t → ∀ c,
    (∀ k ∈ l, k.2.burnFor c = false) →
    s.chainTypeManager c ≠ 0 → s.settlementLayer c = cfg.thisChain →
      t.chainTypeManager c = s.chainTypeManager c ∧
      t.baseTokenAssetId c = s.baseTokenAssetId c ∧
      t.settlementLayer c = cfg.thisChain

/-- **THE `AlreadyCurrentSL` CHECK IS LOAD-BEARING.** Without it
(`forwardedBridgeMintNoCurrentSLCheck`), in a reachable state where chain `c` has a CTM
and settles on this chain, the mint hook rewrites `c`'s base token to a different asset
id; with the check the same call reverts. -/
def Properties.WithoutCurrentSLCheckBaseTokenRewritten : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (aid : AssetId) (c : ChainId) (b : AssetId),
    Reachable cfg s ∧ s.chainTypeManager c ≠ 0 ∧ s.settlementLayer c = cfg.thisChain ∧
    b ≠ s.baseTokenAssetId c ∧
    forwardedBridgeMintNoCurrentSLCheck cfg caller s aid c b = some s' ∧
    s'.baseTokenAssetId c = b ∧
    exec cfg caller (.forwardedBridgeMint aid c b) s = none

/-- **THE `BridgeHubAlreadyRegistered` CHECK IS LOAD-BEARING.** Without it
(`createNewChainNoDupCheck`), in a reachable state where chain `c` is registered,
`createNewChain(c, …)` succeeds a second time and replaces `c`'s CTM, base token and
diamond; with the check the same call reverts. -/
def Properties.WithoutAlreadyRegisteredCheckChainReRegistered : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (c : ChainId) (m : Address) (a : AssetId)
    (adm d : Address),
    Reachable cfg s ∧ s.chainTypeManager c ≠ 0 ∧
    m ≠ s.chainTypeManager c ∧ a ≠ s.baseTokenAssetId c ∧ d ≠ s.zkAddr c ∧
    createNewChainNoDupCheck cfg caller s c m a d = some s' ∧
    s'.chainTypeManager c = m ∧ s'.baseTokenAssetId c = a ∧ s'.zkAddr c = d ∧
    exec cfg caller (.createNewChain c m a adm d) s = none

/-! ## Settlement layers, run level -/

/-- **A REMOTE SETTLEMENT LAYER WAS SET BY A BURN.** In every run from an initialized
Bridgehub, if `settlementLayer[c]` is neither `0` nor this chain, then it is not `c`
itself, and the run contains a successful
`forwardedBridgeBurnSetSettlementLayer(c, settlementLayer[c])`. -/
def Properties.RemoteSettlementLayerCameFromBurn : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    ∀ c, s.settlementLayer c ≠ 0 → s.settlementLayer c ≠ cfg.thisChain →
      s.settlementLayer c ≠ c ∧
      ∃ caller, (caller, Action.burnSetSettlementLayer c (s.settlementLayer c)) ∈ l

/-- **A MIGRATION TARGET SETTLES HERE WHEN THE CHAIN MOVES.** In a reachable state, a
successful `forwardedBridgeBurnSetSettlementLayer(c, sl)` leaves `c` on `sl`, and `sl` is
this chain or itself settles on this chain right after the call. -/
def Properties.MigrationTargetSettlesHere : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (c sl : ChainId), Reachable cfg s →
    exec cfg caller (.burnSetSettlementLayer c sl) s = some s' →
    s'.settlementLayer c = sl ∧ (sl = cfg.thisChain ∨ s'.settlementLayer sl = cfg.thisChain)

/-- **A CHAIN'S RECORDED SETTLEMENT LAYER NEED NOT STILL SETTLE HERE.** The boundary of
`WhitelistedSettlementLayersSettleHere` and `MigrationTargetSettlesHere`: they protect a
layer only while it is whitelisted. A reachable state where `settlementLayer[c] = g`,
`g` is not whitelisted, and `settlementLayer[g] = h`, with `g` and `h` distinct and both
different from this chain. (The run: `c` migrates to the whitelisted `g`; the owner removes
`g` from the whitelist; the handler migrates `g` to `h`. Neither
`setSettlementLayerStatus(g, false)`, `L1:94-100`, nor the burn hook for `g`, `BB:403-421`,
looks at the chains recorded on `g`.) -/
def Properties.SettlementLayerOfAChainNeedNotSettleHere : Prop :=
  ∃ (cfg : Config) (s : State) (c g h : ChainId),
    Reachable cfg s ∧ g ≠ cfg.thisChain ∧ h ≠ cfg.thisChain ∧ h ≠ g ∧
    s.settlementLayer c = g ∧ s.settlementLayer g = h ∧ s.whitelistedSL g = false

/-! ## Requests -/

/-- **`requestL2TransactionDirect` ACCOUNTING AND ROUTING.** A successful direct request
for chain `c`: deposits `mintValue` of `c`'s base token for `c` from the caller, attaches
all of `msg.value` to that deposit and nothing to anything else, attaches exactly
`mintValue` in ETH if `c`'s base token is ETH and nothing otherwise, asks `c`'s stored
diamond to mint the same `mintValue` on L2 with the caller as sender, keeps an explicit
refund recipient, and happens only while unpaused. -/
def Properties.DirectRequestAccounting : Prop :=
  ∀ (cfg : Config) (s : State) (caller : Address) (env : CallEnv) (req : DirectRequest)
    (o : Outcome), requestDirect cfg s caller env req = some o →
    s.paused = false ∧ ZkGetOk s req.chainId ∧
    o.depositChainId = req.chainId ∧ o.depositAssetId = s.baseTokenAssetId req.chainId ∧
    o.depositSender = caller ∧ o.depositAmount = req.mintValue ∧
    o.ethToAssetRouter + o.ethToSecondBridge = env.msgValue.val ∧
    o.ethToAssetRouter =
      (if s.baseTokenAssetId req.chainId = cfg.ethAssetId then req.mintValue.val else 0) ∧
    o.target = s.zkAddr req.chainId ∧ o.l2Sender = caller ∧
    o.mintValue = o.depositAmount ∧ o.l2Value = req.l2Value ∧
    (req.refundRecipient ≠ 0 → o.refundRecipient = req.refundRecipient)

/-- **`requestL2TransactionTwoBridges` ACCOUNTING AND ROUTING.** A successful two-bridges
request for chain `c`: the ETH sent to the asset router and to the second bridge add up to
`msg.value`; the router gets `mintValue` in ETH for an ETH-based chain and nothing
otherwise; the second bridge gets `secondBridgeValue`; the deposit and the Mailbox request
carry the same `mintValue` for `c` in `c`'s base token; the L2 sender is the second bridge,
which lies above `BRIDGEHUB_MIN_SECOND_BRIDGE_ADDRESS`; the bridge returned the magic
value; and this happens only while unpaused. -/
def Properties.TwoBridgesRequestAccounting : Prop :=
  ∀ (cfg : Config) (s : State) (caller : Address) (env : CallEnv) (req : TwoBridgesRequest)
    (reply : SecondBridgeReply) (o : Outcome),
    requestTwoBridges cfg s caller env req reply = some o →
    s.paused = false ∧ ZkGetOk s req.chainId ∧
    o.depositChainId = req.chainId ∧ o.depositAssetId = s.baseTokenAssetId req.chainId ∧
    o.depositSender = caller ∧ o.depositAmount = req.mintValue ∧
    o.ethToAssetRouter + o.ethToSecondBridge = env.msgValue.val ∧
    o.ethToAssetRouter =
      (if s.baseTokenAssetId req.chainId = cfg.ethAssetId then req.mintValue.val else 0) ∧
    o.ethToSecondBridge = req.secondBridgeValue.val ∧
    o.target = s.zkAddr req.chainId ∧
    o.l2Sender = req.secondBridgeAddress ∧ minSecondBridgeAddress < req.secondBridgeAddress ∧
    reply.magicValue = cfg.twoBridgesMagic ∧ o.l2Contract = reply.l2Contract ∧
    o.mintValue = o.depositAmount ∧ o.l2Value = req.l2Value ∧
    (req.refundRecipient ≠ 0 → o.refundRecipient = req.refundRecipient)

/-- **REQUESTS REACH REGISTERED CHAINS.** In a run from an initialized Bridgehub without
the handler's registry writers, a successful request of either kind for chain `c` goes to
a nonzero diamond of a chain that has a CTM, and is charged in a registered asset. -/
def Properties.RequestsReachRegisteredChains : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    (∀ k ∈ l, k.2.handlerRegistryWrite = false) →
    ∀ (caller : Address) (env : CallEnv) (o : Outcome) (c : ChainId),
      ((∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg s caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg s caller env req reply = some o)) →
      s.chainTypeManager c ≠ 0 ∧ o.target ≠ 0 ∧ o.target = getZKChain s c ∧
      s.assetIdRegistered o.depositAssetId = true

/-- **A REQUEST NEEDS A `zkChainMap` ENTRY.** In every reachable state, with every entry
point allowed in the run (the chain asset handler's included), a successful request of
either kind for chain `c` has `c` as a key of `zkChainMap` and is sent to `getZKChain(c)`.
Equivalently, a request for a chain id that is not a key reverts. -/
def Properties.RequestNeedsMapEntry : Prop :=
  ∀ (cfg : Config) (s : State), Reachable cfg s →
    ∀ (caller : Address) (env : CallEnv) (o : Outcome) (c : ChainId),
      ((∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg s caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg s caller env req reply = some o)) →
      c ∈ s.zkKeys ∧ o.target = getZKChain s c

/-- **A REQUEST IS CHARGED IN THE BASE TOKEN FIXED AT CREATION.** In any run (from any
state) of the form `l₁ ++ [createNewChain(c, m, a, adm, d)] ++ l₂` with no
`forwardedBridgeMint` for `c` in `l₂`, a successful request of either kind for `c` at the
end deposits asset `a`; if `l₂` has no `registerNewZKChain` for `c`, it goes to `d`, the
diamond the CTM returned at creation. -/
def Properties.RequestChargesCreationBaseToken : Prop :=
  ∀ (cfg : Config) (s t : State) (l₁ l₂ : List Call) (caller₀ : Address) (c : ChainId)
    (m : Address) (a : AssetId) (adm d : Address),
    Run cfg s (l₁ ++ [(caller₀, .createNewChain c m a adm d)] ++ l₂) t →
    (∀ k ∈ l₂, k.2.bridgeMintFor c = false) →
    ∀ (caller : Address) (env : CallEnv) (o : Outcome),
      ((∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg t caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg t caller env req reply = some o)) →
      o.depositAssetId = a ∧ ((∀ k ∈ l₂, k.2.handlerRegistersFor c = false) → o.target = d)

/-- **THE MINIMUM SECOND-BRIDGE ADDRESS CHECK IS LOAD-BEARING.** Without it
(`requestTwoBridgesNoMinAddress`), a request in a reachable state succeeds with a reserved
low address (`≤ 0xFFFF`) as the L2 sender. -/
def Properties.WithoutMinAddressCheckLowSender : Prop :=
  ∃ (cfg : Config) (s : State) (caller : Address) (env : CallEnv) (req : TwoBridgesRequest)
    (reply : SecondBridgeReply) (o : Outcome),
    Reachable cfg s ∧ requestTwoBridgesNoMinAddress cfg s caller env req reply = some o ∧
    o.l2Sender ≤ minSecondBridgeAddress ∧
    requestTwoBridges cfg s caller env req reply = none

/-! ## Authority and pause -/

/-- **WHO WRITES THE REGISTRIES.** For every successful call of every entry point:
only the owner changes `chainTypeManagerIsRegistered` or the settlement-layer whitelist;
only the owner, the admin or the chain asset handler changes a chain's CTM or settlement
layer; only the owner, the admin or the chain asset handler changes `assetIdIsRegistered`. -/
def Properties.RegistryWritesAuthorized : Prop :=
  ∀ (cfg : Config) (caller : Address) (a : Action) (s s' : State),
    exec cfg caller a s = some s' →
    (s'.ctmRegistered ≠ s.ctmRegistered → caller = s.owner) ∧
    (s'.whitelistedSL ≠ s.whitelistedSL → caller = s.owner) ∧
    (s'.chainTypeManager ≠ s.chainTypeManager →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.settlementLayer ≠ s.settlementLayer →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.assetIdRegistered ≠ s.assetIdRegistered →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler)

/-- **PAUSE BLOCKS CREATION AND REQUESTS.** While paused, `createNewChain` and both
request entry points revert. -/
def Properties.PauseBlocksCreationAndRequests : Prop :=
  ∀ (cfg : Config) (s : State), s.paused = true → ∀ (caller : Address),
    (∀ c m a adm d, exec cfg caller (.createNewChain c m a adm d) s = none) ∧
    (∀ env req, requestDirect cfg s caller env req = none) ∧
    (∀ env req reply, requestTwoBridges cfg s caller env req reply = none)

/-! ## Source comment refuted -/

/-- **A REMOVED CTM IS STILL ASSIGNED TO A CHAIN BY `forwardedBridgeMint`.**
`removeChainTypeManager`'s NatSpec (`BB:240`) says removal "stops new Chains from using
the CTM". In a reachable state where CTM `m` has been removed and chain `c` has no CTM,
the chain asset handler's `forwardedBridgeMint` succeeds and makes `m` the CTM of `c`:
the Bridgehub alone does not stop it. On L1 the deployed handler does not make this call
for a chain that never left L1 (`ChainAssetHandlerBase.sol:374-383`). -/
def Properties.RemovedCtmStillAssignedByBridgeMint : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (aid : AssetId) (c : ChainId)
    (b : AssetId) (m : Address),
    Reachable cfg s ∧ s.ctmRegistered m = false ∧ s.chainTypeManager c = 0 ∧
    exec cfg caller (.forwardedBridgeMint aid c b) s = some s' ∧
    s'.chainTypeManager c = m ∧ m ≠ 0

/-! ## Non-vacuity -/

/-- **REGISTRATION WITNESS.** A reachable state with two chains `g ≠ c` registered through
`createNewChain`, both with CTMs, `g` whitelisted as a settlement layer, and `c` migrated
to settle on `g`. -/
def Properties.RegistrationWitness : Prop :=
  ∃ (cfg : Config) (s : State) (g c : ChainId),
    Reachable cfg s ∧ g ≠ c ∧ g ≠ cfg.thisChain ∧
    s.chainTypeManager g ≠ 0 ∧ s.chainTypeManager c ≠ 0 ∧
    s.whitelistedSL g = true ∧ s.settlementLayer c = g ∧ s.zkKeys.card = 2

/-- **REQUEST WITNESS.** In a reachable state with a registered ETH-based chain, a direct
request with `mintValue > 0` and a two-bridges request with nonzero ETH to both the asset
router and the second bridge both succeed. -/
def Properties.RequestWitness : Prop :=
  ∃ (cfg : Config) (s : State) (caller : Address) (env₁ env₂ : CallEnv) (r₁ : DirectRequest)
    (r₂ : TwoBridgesRequest) (reply : SecondBridgeReply) (o₁ o₂ : Outcome),
    Reachable cfg s ∧ s.baseTokenAssetId r₁.chainId = cfg.ethAssetId ∧
    requestDirect cfg s caller env₁ r₁ = some o₁ ∧ 0 < o₁.ethToAssetRouter ∧
    requestTwoBridges cfg s caller env₂ r₂ reply = some o₂ ∧
    0 < o₂.ethToAssetRouter ∧ 0 < o₂.ethToSecondBridge

end Contracts.Bridgehub
