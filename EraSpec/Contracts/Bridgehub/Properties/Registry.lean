import EraSpec.Contracts.Bridgehub.Specs.Registry

/-!
# Properties: `L1Bridgehub`

Statements about `EraSpec.Contracts.Bridgehub.Specs.Registry` (`draft/v0.35.0` at
`b17415d20`, identical to `d9f6789` for every cited file). Proofs are in
`EraSpec.Contracts.Bridgehub.Proofs.Registry`. Every run-level statement quantifies over
`Run`, so over every entry point of the model and every interleaving of callers. All of them
are about the model: the external calls are inputs or assumed not to revert or write the
Bridgehub's storage (ASSUMPTIONS `MODEL-BRIDGEHUB`).

## Chain registration

* A chain id is registered at most once in any run, from any starting state, and never
  if it already has a CTM (`ChainIdRegisteredOnce`). The reason is that no entry point
  ever clears `chainTypeManager[c]` (`CtmNeverCleared`).
* Every chain with a CTM uses a registered base-token asset id (`ChainBaseTokenRegistered`),
  and its CTM was added by `addChainTypeManager` earlier in the run
  (`ChainCtmWasApproved`). The CTM need not still be registered: `removeChainTypeManager`
  does not touch existing chains, and `forwardedBridgeMint` assigns a CTM without reading
  `chainTypeManagerIsRegistered` (`RemovedCtmStillAssignedByBridgeMint`).
* A successful `createNewChain` / `registerAlreadyDeployedZKChain` had a registered CTM
  and a registered base-token asset id at that moment, sets exactly that chain's CTM, base
  token, settlement layer (this chain) and diamond, and leaves every other chain alone
  (`CreateNewChainPostcondition`, `RegisterDeployedPostcondition`). No entry point
  unregisters an asset id (`AssetIdNeverUnregistered`).
* Outside `forwardedBridgeMint`, a registered chain's CTM and base token never change
  (`CtmAndBaseTokenFixedOutsideBridgeMint`). `forwardedBridgeMint`, callable only by the
  chain asset handler, rewrites both (`BridgeMintRewritesBaseToken`).
* While a chain settles here, nothing changes its CTM or base token, `forwardedBridgeMint`
  included: they can change only after a `forwardedBridgeBurnSetSettlementLayer` for that
  chain (`CtmAndBaseTokenFixedWhileSettlingHere`). The `AlreadyCurrentSL` check in the mint
  hook and the `BridgeHubAlreadyRegistered` check in `_validateChainParams` are
  load-bearing (`WithoutCurrentSLCheckBaseTokenRewritten`,
  `WithoutAlreadyRegisteredCheckChainReRegistered`).
* Without the chain asset handler's two registry writers, `zkChainMap` and
  `chainTypeManager` describe the same chains, every key has a nonzero diamond, and the
  chain count stays within `MAX_NUMBER_OF_ZK_CHAINS` (`RegistryConsistentWithoutHandler`,
  `ChainCountBounded`). With them, the Bridgehub's own checks let `createNewChain`
  overwrite a map entry the handler wrote (`HandlerEntryOverwrittenByCreate`).
* `ctmAssetIdFromAddress` then `ctmAssetIdToAddress` returns the CTM, unless two
  `setCTMAssetAddress` calls of the run, for different CTMs, hash to the same asset id
  (a logged collision; no injectivity premise), provided every `setCTMAssetAddress` passes
  the CTM address as its data, as `CTMDeploymentTracker` does (`CtmAssetIdRoundTrip`). The
  Bridgehub does not enforce that discipline (`CtmAssetIdRoundTripNeedsDiscipline`), and the
  collision disjunct is needed (`CtmAssetIdCollisionFires`).

## The chain map

* `zkChainMap` only grows, and in every reachable state `get` succeeds exactly for its keys,
  whatever is called (`ChainMapOnlyGrows`). A chain's diamond changes only through the
  handler's `registerNewZKChain` for that chain, or through its own registration while it has
  no CTM (`DiamondChangesOnlyByRegistration`); so once a chain has a CTM its diamond is fixed
  in any run without a `registerNewZKChain` for it (`DiamondFixedAfterRegistration`). That
  handler call does replace it: the Bridgehub ignores `set`'s return value
  (`HandlerRegisterReplacesDiamond`).

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
* The two results above hold for a layer only while it is whitelisted. A chain can be
  recorded on a layer that is no longer whitelisted and itself settles elsewhere
  (`SettlementLayerOfAChainNeedNotSettleHere`).

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

* Every write to the Bridgehub's storage is by the caller its modifiers name: the owner for
  the CTM registry, the whitelist and pausing; the owner, the admin or the chain asset
  handler for a chain's CTM, base token, settlement layer, diamond and the asset registry;
  the CTM deployer for the CTM asset maps; the owner or the upgrader for the ecosystem
  addresses; and the two-step handovers for owner and admin (`RegistryWritesAuthorized`).
  A paused Bridgehub creates no chain and serves no request
  (`PauseBlocksCreationAndRequests`).

## Non-vacuity

Every property with premises is instantiated on the concrete runs of the Specs file
(`wRegistryRun`, then `wRegistryHandlerRun`), with nonempty runs and nonzero entries:
`RegistryRunWitness` (the run-level premises without the handler's writers),
`HandlerRunWitness` (the run-level premises that allow them, on a run where the excluded
calls occur for other chains), `RegistryStepWitness` (the per-step premises and the paused
state) and `RequestWitness` (the request premises, for both kinds and both base-token
branches). `RegistryRunWitness` also shows the collision disjunct of `CtmAssetIdRoundTrip`
false on its run, and `CtmAssetIdCollisionFires` shows it true on another. The other
existential properties are countermodels or boundaries.
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

/-- **`forwardedBridgeMint` DOES NOT READ THE CTM REGISTRY.** The boundary of the
registration check in `_validateChainParams` (`BB:523-525`): `forwardedBridgeMint` takes
the CTM from `ctmAssetIdToAddress` (`BB:437-446`) and does not read
`chainTypeManagerIsRegistered`. A reachable state where CTM `m` is not registered (in the
proof's run, `removeChainTypeManager` removed it) and chain `c` has no CTM, and the chain
asset handler's `forwardedBridgeMint` makes `m` the CTM of `c`. This is about the Bridgehub's own checks:
on L1 the deployed handler lets only a chain that left L1 come back
(`ChainAssetHandlerBase.sol:374-383`), a precondition this model does not include. -/
def Properties.RemovedCtmStillAssignedByBridgeMint : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (aid : AssetId) (c : ChainId)
    (b : AssetId) (m : Address),
    Reachable cfg s ∧ s.ctmRegistered m = false ∧ s.chainTypeManager c = 0 ∧
    exec cfg caller (.forwardedBridgeMint aid c b) s = some s' ∧
    s'.chainTypeManager c = m ∧ m ≠ 0

/-- **CTM AND BASE TOKEN ARE FIXED OUTSIDE `forwardedBridgeMint`.** In any run from any
state that contains no `forwardedBridgeMint` for chain `c`, a chain that had a CTM at the
start ends with the same CTM and the same base-token asset id. -/
def Properties.CtmAndBaseTokenFixedOutsideBridgeMint : Prop :=
  ∀ (cfg : Config) (s t : State) (l : List Call), Run cfg s l t → ∀ c,
    (∀ k ∈ l, k.2.bridgeMintFor c = false) → s.chainTypeManager c ≠ 0 →
      t.chainTypeManager c = s.chainTypeManager c ∧
      t.baseTokenAssetId c = s.baseTokenAssetId c

/-- **`forwardedBridgeMint` REWRITES A REGISTERED CHAIN'S BASE TOKEN.** The boundary of
`CtmAndBaseTokenFixedOutsideBridgeMint`: a reachable state where chain `c` has a CTM and a
base token, and the chain asset handler's `forwardedBridgeMint` succeeds and sets a
different base token `b`. The Bridgehub does not compare the new value with the old one
(`BB:447`). (In the proof's run `c` was migrated away first, which the call requires.) -/
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
`c` has a `zkChainMap` entry with a nonzero diamond but no CTM (in the proof's run, written
by the handler's `registerNewZKChain`), and `createNewChain(c, …)` succeeds in this model
and replaces the stored diamond.
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

/-- **THE CTM ASSET ID ROUND-TRIPS, UP TO A LOGGED COLLISION.** In a run from an
initialized Bridgehub where every `setCTMAssetAddress(data, m)` has `data = m` (what
`CTMDeploymentTracker` sends), every CTM `m` with a nonzero `ctmAssetIdFromAddress[m]`
satisfies `ctmAssetIdToAddress[ctmAssetIdFromAddress[m]] = m`, unless the run has a logged
collision at `m` (`CtmAssetIdLoggedCollision`): a call `setCTMAssetAddress(m, m)` and a call
`setCTMAssetAddress(m', m')` with `m' ≠ m`, both in the run, whose hash inputs give the same
asset id. No injectivity is assumed. -/
def Properties.CtmAssetIdRoundTrip : Prop :=
  ∀ (cfg : Config) (owner : Address) (l : List Call) (s : State), Run cfg (init cfg owner) l s →
    (∀ k ∈ l, k.2.ctmAssetDisciplined = true) →
    ∀ m, s.ctmAssetIdFromAddress m ≠ 0 →
      s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) = m ∨
      CtmAssetIdLoggedCollision cfg l m

/-- **THE ROUND TRIP NEEDS THE CALLER'S DISCIPLINE.** With an asset-id hash that is
injective in its data argument for each chain and sender, a run from an initialized
Bridgehub reaches a state where the round trip fails at CTM `m` and the run has no logged
collision at `m`. (In the proof's run, two `setCTMAssetAddress` calls by the same sender
with the same data `5`, for CTMs `60` and `61`, hash the same input: the second overwrites
`ctmAssetIdToAddress` at CTM `60`'s asset id.) -/
def Properties.CtmAssetIdRoundTripNeedsDiscipline : Prop :=
  ∃ (cfg : Config) (l : List Call) (s : State) (m : Address),
    (∀ x y d d', cfg.encodeAssetId x d y = cfg.encodeAssetId x d' y → d = d') ∧
    Run cfg (init cfg 1) l s ∧ ¬ CtmAssetIdLoggedCollision cfg l m ∧
    s.ctmAssetIdFromAddress m ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) ≠ m

/-- **THE LOGGED-COLLISION DISJUNCT OF `CtmAssetIdRoundTrip` FIRES.** The disjunct is not
vacuous: a run from an initialized Bridgehub in which every `setCTMAssetAddress` passes the
CTM address as data reaches a state where the round trip fails at a CTM `m` with a nonzero
`ctmAssetIdFromAddress[m]`, and the run has a logged collision at `m`. So
`CtmAssetIdRoundTrip` is false without its collision disjunct. (In the proof's run the
asset-id hash ignores the chain and the sender, maps the data `60` and `61` to the same id,
and is injective on the other data; the CTM deployer sets CTM `60`'s asset id, then CTM
`61`'s, which overwrites `ctmAssetIdToAddress` at that id.) -/
def Properties.CtmAssetIdCollisionFires : Prop :=
  ∃ (cfg : Config) (l : List Call) (s : State) (m : Address),
    Run cfg (init cfg 1) l s ∧ (∀ k ∈ l, k.2.ctmAssetDisciplined = true) ∧
    s.ctmAssetIdFromAddress m ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress m) ≠ m ∧
    CtmAssetIdLoggedCollision cfg l m

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
(`burnNoSettlementLayerCheck`), in a reachable state a whitelisted settlement layer `c`
other than this chain migrates away and stays whitelisted, so the post-state breaks the
invariant of `WhitelistedSettlementLayersSettleHere`; with the check the same call
reverts. -/
def Properties.WithoutCheckWhitelistedLayerLeaves : Prop :=
  ∃ (cfg : Config) (s s' : State) (caller : Address) (c sl : ChainId),
    Reachable cfg s ∧
    burnNoSettlementLayerCheck cfg caller s c sl = some s' ∧
    s'.whitelistedSL c = true ∧ c ≠ cfg.thisChain ∧ s'.settlementLayer c ≠ cfg.thisChain ∧
    exec cfg caller (.burnSetSettlementLayer c sl) s = none

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
afterwards `c` has CTM `m`, base token `a`, settles on this chain, and
`getZKChain(c) = d ≠ 0`; the chain count is within `MAX_NUMBER_OF_ZK_CHAINS`; and no other
chain's CTM, base token, settlement layer or diamond changed. -/
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
caller was the owner; `z` reported chain id `c` and this Bridgehub; `zkChainMap.tryGet(c)`
reported no entry (no key `c` and no nonzero stored value); `c` had no CTM, is nonzero,
fits in 48 bits and is not this chain; the reported CTM and base token were nonzero and
registered at that moment; afterwards `c` has that CTM and base token, settles on this
chain, and `getZKChain(c) = z ≠ 0`; the chain count is within the limit; and no other
chain's CTM, base token, settlement layer or diamond changed. -/
def Properties.RegisterDeployedPostcondition : Prop :=
  ∀ (cfg : Config) (caller : Address) (s s' : State) (c : ChainId) (z : Address)
    (info : DeployedChainInfo),
    exec cfg caller (.registerAlreadyDeployed c z info) s = some s' →
    caller = s.owner ∧ info.chainId = c ∧ info.bridgehub = cfg.self ∧
    ¬ ZkGetOk s c ∧ s.chainTypeManager c = 0 ∧
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
base token fixed at registration can change only in a run that contains the chain asset
handler's `forwardedBridgeBurnSetSettlementLayer` for that chain. Every other entry point,
including `forwardedBridgeMint`, is allowed in the run. -/
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
`WhitelistedSettlementLayersSettleHere` and `MigrationTargetSettlesHere`, which hold for a
layer only while it is whitelisted: a reachable state where `settlementLayer[c] = g`, `g`
is not whitelisted, and `settlementLayer[g] = h`, with `g` and `h` distinct and both
different from this chain. (The proof's run: `c` migrates to the whitelisted `g`; the owner
removes `g` from the whitelist; the handler migrates `g` to `h`. Neither
`setSettlementLayerStatus` (`L1:94-100`) nor the burn hook (`BB:403-421`) reads the
settlement layers of other chains.) -/
def Properties.SettlementLayerOfAChainNeedNotSettleHere : Prop :=
  ∃ (cfg : Config) (s : State) (c g h : ChainId),
    Reachable cfg s ∧ g ≠ cfg.thisChain ∧ h ≠ cfg.thisChain ∧ h ≠ g ∧
    s.settlementLayer c = g ∧ s.settlementLayer g = h ∧ s.whitelistedSL g = false

/-! ## Requests -/

/-- **`requestL2TransactionDirect` ACCOUNTING AND ROUTING.** A successful direct request
for chain `c`: deposits `mintValue` of `c`'s base token for `c` from the caller, attaches
all of `msg.value` to that deposit (the ETH to the asset router and to a second bridge add up
to `msg.value`, and the second bridge gets none), attaches exactly `mintValue` in ETH if
`c`'s base token is ETH and nothing otherwise, asks `c`'s stored diamond to mint the same
`mintValue` on L2 with the caller as sender, keeps an explicit refund recipient, and happens
only while unpaused and when `zkChainMap.get(c)` succeeds. -/
def Properties.DirectRequestAccounting : Prop :=
  ∀ (cfg : Config) (s : State) (caller : Address) (env : CallEnv) (req : DirectRequest)
    (o : Outcome), requestDirect cfg s caller env req = some o →
    s.paused = false ∧ ZkGetOk s req.chainId ∧
    o.depositChainId = req.chainId ∧ o.depositAssetId = s.baseTokenAssetId req.chainId ∧
    o.depositSender = caller ∧ o.depositAmount = req.mintValue ∧
    o.ethToAssetRouter + o.ethToSecondBridge = env.msgValue.val ∧
    o.ethToAssetRouter =
      (if s.baseTokenAssetId req.chainId = cfg.ethAssetId then req.mintValue.val else 0) ∧
    o.ethToSecondBridge = 0 ∧
    o.target = s.zkAddr req.chainId ∧ o.l2Sender = caller ∧
    o.mintValue = o.depositAmount ∧ o.l2Value = req.l2Value ∧
    (req.refundRecipient ≠ 0 → o.refundRecipient = req.refundRecipient)

/-- **`requestL2TransactionTwoBridges` ACCOUNTING AND ROUTING.** A successful two-bridges
request for chain `c`: the ETH sent to the asset router and to the second bridge add up to
`msg.value`; the router gets `mintValue` in ETH for an ETH-based chain and nothing
otherwise; the second bridge gets `secondBridgeValue`; the deposit and the Mailbox request
carry the same `mintValue` for `c` in `c`'s base token; the L2 sender is the second bridge,
which lies above `BRIDGEHUB_MIN_SECOND_BRIDGE_ADDRESS`; the bridge returned the magic
value; and this happens only while unpaused and when `zkChainMap.get(c)` succeeds. -/
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
low address (`≤ 0xFFFF`) as the L2 sender; with the check the same request reverts. -/
def Properties.WithoutMinAddressCheckLowSender : Prop :=
  ∃ (cfg : Config) (s : State) (caller : Address) (env : CallEnv) (req : TwoBridgesRequest)
    (reply : SecondBridgeReply) (o : Outcome),
    Reachable cfg s ∧ requestTwoBridgesNoMinAddress cfg s caller env req reply = some o ∧
    o.l2Sender ≤ minSecondBridgeAddress ∧
    requestTwoBridges cfg s caller env req reply = none

/-! ## Authority and pause -/

/-- **WHO WRITES THE BRIDGEHUB'S STORAGE.** For every successful call of every entry point,
each changed part of the storage was changed by a caller the source's modifiers admit:
* `chainTypeManagerIsRegistered`, the settlement-layer whitelist and `paused`: the owner;
* a chain's CTM, base token, settlement layer, `zkChainMap` (keys or values) and
  `assetIdIsRegistered`: the owner, the admin or the chain asset handler;
* the two CTM asset maps: the CTM deployer `l1CtmDeployer`;
* the asset router, CTM deployer, message root, chain asset handler and registration-sender
  addresses: the owner or the upgrader `L2_COMPLEX_UPGRADER_ADDR`;
* the owner: the owner (renouncing) or the pending owner (accepting); the pending owner: the
  owner or the pending owner (accepting clears it); the admin: the pending admin; the pending
  admin: the owner, the admin or the pending admin (accepting clears it). -/
def Properties.RegistryWritesAuthorized : Prop :=
  ∀ (cfg : Config) (caller : Address) (a : Action) (s s' : State),
    exec cfg caller a s = some s' →
    (s'.ctmRegistered ≠ s.ctmRegistered → caller = s.owner) ∧
    (s'.whitelistedSL ≠ s.whitelistedSL → caller = s.owner) ∧
    (s'.paused ≠ s.paused → caller = s.owner) ∧
    (s'.chainTypeManager ≠ s.chainTypeManager →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.baseTokenAssetId ≠ s.baseTokenAssetId →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.settlementLayer ≠ s.settlementLayer →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.zkKeys ≠ s.zkKeys ∨ s'.zkAddr ≠ s.zkAddr →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.assetIdRegistered ≠ s.assetIdRegistered →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.chainAssetHandler) ∧
    (s'.ctmAssetIdToAddress ≠ s.ctmAssetIdToAddress ∨
        s'.ctmAssetIdFromAddress ≠ s.ctmAssetIdFromAddress →
      caller = s.l1CtmDeployer) ∧
    (s'.assetRouter ≠ s.assetRouter ∨ s'.l1CtmDeployer ≠ s.l1CtmDeployer ∨
        s'.messageRoot ≠ s.messageRoot ∨ s'.chainAssetHandler ≠ s.chainAssetHandler ∨
        s'.chainRegistrationSender ≠ s.chainRegistrationSender →
      caller = s.owner ∨ caller = cfg.upgrader) ∧
    (s'.owner ≠ s.owner → caller = s.owner ∨ caller = s.pendingOwner) ∧
    (s'.pendingOwner ≠ s.pendingOwner → caller = s.owner ∨ caller = s.pendingOwner) ∧
    (s'.admin ≠ s.admin → caller = s.pendingAdmin) ∧
    (s'.pendingAdmin ≠ s.pendingAdmin →
      caller = s.owner ∨ caller = s.admin ∨ caller = s.pendingAdmin)

/-- **PAUSE BLOCKS CREATION AND REQUESTS.** While paused, `createNewChain` and both
request entry points revert. -/
def Properties.PauseBlocksCreationAndRequests : Prop :=
  ∀ (cfg : Config) (s : State), s.paused = true → ∀ (caller : Address),
    (∀ c m a adm d, exec cfg caller (.createNewChain c m a adm d) s = none) ∧
    (∀ env req, requestDirect cfg s caller env req = none) ∧
    (∀ env req reply, requestTwoBridges cfg s caller env req reply = none)

/-! ## Non-vacuity -/

/-- **RUN-LEVEL PREMISES WITHOUT THE HANDLER'S REGISTRY WRITERS.** The run `wRegistryRun`
succeeds from an initialized Bridgehub (`wRegistryCfg`, owner `1`). None of its calls is a
registry write of the chain asset handler or an unchecked registration, and every
`setCTMAssetAddress` in it passes the CTM address as data. It registers chain `10` exactly
once. At its end chains `10`, `11` and `12` have CTMs `60`, `60` and `61` and base tokens
`7`, `7` and `8`; asset id `8` was not registered at the start and is at the end;
`zkChainMap` has three keys; both CTM asset ids are set and round-trip, with no logged
collision at either CTM; chain `10` is a whitelisted settlement layer other than this chain,
and chain `11` is recorded on it. This meets the premises of `ChainIdRegisteredOnce`,
`ChainBaseTokenRegistered`, `ChainCtmWasApproved`, `RegistryConsistentWithoutHandler`,
`ChainCountBounded`, `CtmAssetIdRoundTrip`, `WhitelistedSettlementLayersSettleHere`,
`RemoteSettlementLayerCameFromBurn` and `AssetIdNeverUnregistered`. -/
def Properties.RegistryRunWitness : Prop :=
  ∃ s, Run wRegistryCfg (init wRegistryCfg 1) wRegistryRun s ∧
    (∀ k ∈ wRegistryRun, k.2.handlerRegistryWrite = false ∧
      k.2.uncheckedRegistration = false ∧ k.2.ctmAssetDisciplined = true) ∧
    (wRegistryRun.filter fun k => k.2.registers 10).length = 1 ∧
    s.chainTypeManager 10 = 60 ∧ s.chainTypeManager 11 = 60 ∧ s.chainTypeManager 12 = 61 ∧
    s.baseTokenAssetId 10 = 7 ∧ s.baseTokenAssetId 11 = 7 ∧ s.baseTokenAssetId 12 = 8 ∧
    (init wRegistryCfg 1).assetIdRegistered 8 = false ∧ s.assetIdRegistered 8 = true ∧
    s.zkKeys.card = 3 ∧
    s.ctmAssetIdFromAddress 60 ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 60) = 60 ∧
    s.ctmAssetIdFromAddress 61 ≠ 0 ∧ s.ctmAssetIdToAddress (s.ctmAssetIdFromAddress 61) = 61 ∧
    ¬ CtmAssetIdLoggedCollision wRegistryCfg wRegistryRun 60 ∧
    ¬ CtmAssetIdLoggedCollision wRegistryCfg wRegistryRun 61 ∧
    s.whitelistedSL 10 = true ∧ (10 : ChainId) ≠ wRegistryCfg.thisChain ∧
    s.settlementLayer 11 = 10

/-- **THE CHAIN-COUNT LIMIT BINDS.** With `wRegistryCfg`'s limit lowered to `3`, the run
`wRegistryRun` followed by the handler's checked `registerNewZKChain(12, 82, true)` (a key
already present) succeeds and meets `ChainCountBounded`'s premise; at its end `zkChainMap`
has exactly `3` keys, and both a checked `registerNewZKChain(13, 73, true)` for a fourth chain
and `createNewChain(14, 60, 7, 0)` (which succeeds at the limit `10`, `RegistryStepWitness`)
revert (`ZKChainLimitReached`, `BB:301-307`). So the bound of `ChainCountBounded` is reached
and the next checked registration is refused. -/
def Properties.ChainCountLimitWitness : Prop :=
  ∃ s, Run { wRegistryCfg with maxChains := 3 } (init { wRegistryCfg with maxChains := 3 } 1)
      (wRegistryRun ++ [(53, .registerNewZKChain 12 82 true)]) s ∧
    (∀ k ∈ wRegistryRun ++ [(53, .registerNewZKChain 12 82 true)],
      k.2.uncheckedRegistration = false) ∧
    s.zkKeys.card = 3 ∧
    exec { wRegistryCfg with maxChains := 3 } 53 (.registerNewZKChain 13 73 true) s = none ∧
    exec { wRegistryCfg with maxChains := 3 } 1 (.createNewChain 14 60 7 0 74) s = none

/-- **RUN-LEVEL PREMISES WITH THE HANDLER'S WRITERS.** From the end of `wRegistryRun`, the
handler run `wRegistryHandlerRun` succeeds. At its start chains `10`, `11` and `12` have
CTMs and chain `10` settles here. The run contains a burn for chain `12` but none for `10`;
a `forwardedBridgeMint` for chain `11` but none for `10` or `12`; `registerNewZKChain` for
chains `13` and `12` but none for `10` or `11`; and no registration of chain `10`. Over
it: chain `11`'s CTM changes from `60` to `61` and its base token from `7` to `8`; chain
`12`'s diamond changes from `72` to `82`; chain `11`'s diamond stays `71`; every key stays a
key, and chain `13` becomes a key with diamond `73` and no CTM; asset id `8` is registered
at the start and at the end. This meets the premises of `CtmNeverCleared`, the second half
of `ChainIdRegisteredOnce`, `CtmAndBaseTokenFixedOutsideBridgeMint` (chains `10` and `12`),
`CtmAndBaseTokenFixedWhileSettlingHere` (chain `10`), `DiamondFixedAfterRegistration`
(chain `11`), both halves of `ChainMapOnlyGrows` and the first half of
`AssetIdNeverUnregistered` (asset id `8`, on a run containing `forwardedBridgeMint`, the
other writer of `assetIdIsRegistered`), on a run in which the excluded calls occur for other
chains. -/
def Properties.HandlerRunWitness : Prop :=
  ∃ s t, Run wRegistryCfg (init wRegistryCfg 1) wRegistryRun s ∧
    Run wRegistryCfg s wRegistryHandlerRun t ∧
    s.chainTypeManager 10 ≠ 0 ∧ s.chainTypeManager 11 = 60 ∧ s.chainTypeManager 12 ≠ 0 ∧
    s.settlementLayer 10 = wRegistryCfg.thisChain ∧
    (∀ k ∈ wRegistryHandlerRun, k.2.burnFor 10 = false ∧ k.2.bridgeMintFor 10 = false ∧
      k.2.bridgeMintFor 12 = false ∧ k.2.handlerRegistersFor 10 = false ∧
      k.2.handlerRegistersFor 11 = false ∧ k.2.registers 10 = false) ∧
    (∃ k ∈ wRegistryHandlerRun, k.2.burnFor 12 = true) ∧
    (∃ k ∈ wRegistryHandlerRun, k.2.bridgeMintFor 11 = true) ∧
    (∃ k ∈ wRegistryHandlerRun, k.2.handlerRegistersFor 12 = true) ∧
    t.chainTypeManager 11 = 61 ∧ s.baseTokenAssetId 11 = 7 ∧ t.baseTokenAssetId 11 = 8 ∧
    getZKChain s 12 = 72 ∧ getZKChain t 12 = 82 ∧ getZKChain t 11 = 71 ∧
    s.zkKeys ⊆ t.zkKeys ∧ (13 : ChainId) ∉ s.zkKeys ∧ (13 : ChainId) ∈ t.zkKeys ∧
    t.chainTypeManager 13 = 0 ∧ getZKChain t 13 = 73 ∧
    s.assetIdRegistered 8 = true ∧ t.assetIdRegistered 8 = true

/-- **PER-STEP PREMISES.** Each step below starts from a state a prefix of the witness runs
reaches, and succeeds:
* `createNewChain(10, 60, 7, 0)` with the CTM returning `70`, after `wRegistryPrelude`: it
  changes the `chainTypeManager` and `settlementLayer` maps and chain `10`'s diamond
  (premises of `CreateNewChainPostcondition`, `DiamondChangesOnlyByRegistration` and
  `RegistryWritesAuthorized`);
* `registerAlreadyDeployedZKChain(12, 72)` with the diamond reporting chain `12`, CTM `61`,
  base token `8` and this Bridgehub (premise of `RegisterDeployedPostcondition`);
* the handler's `forwardedBridgeBurnSetSettlementLayer(11, 10)`, which moves chain `11`
  from this chain to `10` (premises of `MigrationOutOnlyToWhitelisted` and
  `MigrationTargetSettlesHere`);
* the handler's `registerNewZKChain(12, 82, true)`, which changes chain `12`'s diamond from
  `72` (the other disjunct of `DiamondChangesOnlyByRegistration`);
* the owner's `pause` at the end of `wRegistryRun`, from a state in which
  `createNewChain(14, 60, 7, 0)` with the CTM returning `74` succeeds (premise of
  `PauseBlocksCreationAndRequests`).
Of `RegistryWritesAuthorized`'s implications, the stated facts instantiate the antecedents
on `chainTypeManager` and `settlementLayer` (the `createNewChain` step) and the diamond write;
no step here is stated to change the CTM registry, the whitelist, the address slots, the owner
or admin slots or the CTM asset maps, so those antecedents are not exhibited. -/
def Properties.RegistryStepWitness : Prop :=
  (∃ s s', Run wRegistryCfg (init wRegistryCfg 1) wRegistryPrelude s ∧
    exec wRegistryCfg 1 (.createNewChain 10 60 7 0 70) s = some s' ∧
    s'.chainTypeManager ≠ s.chainTypeManager ∧ s'.settlementLayer ≠ s.settlementLayer ∧
    getZKChain s 10 = 0 ∧ getZKChain s' 10 = 70) ∧
  (∃ s s', Run wRegistryCfg (init wRegistryCfg 1)
      (wRegistryPrelude ++ [wRegistryCreate10, (1, .createNewChain 11 60 7 0 71)]) s ∧
    exec wRegistryCfg 1 (.registerAlreadyDeployed 12 72 ⟨12, 61, 8, 99⟩) s = some s') ∧
  (∃ s s', Run wRegistryCfg (init wRegistryCfg 1)
      (wRegistryPrelude ++ [wRegistryCreate10] ++ wRegistryRest) s ∧
    exec wRegistryCfg 53 (.burnSetSettlementLayer 11 10) s = some s' ∧
    s.settlementLayer 11 = wRegistryCfg.thisChain ∧ s'.settlementLayer 11 = 10) ∧
  (∃ s s', Run wRegistryCfg (init wRegistryCfg 1) (wRegistryRun ++ wRegistryHandlerPrefix) s ∧
    exec wRegistryCfg 53 (.registerNewZKChain 12 82 true) s = some s' ∧
    getZKChain s 12 = 72 ∧ getZKChain s' 12 = 82) ∧
  (∃ s s', Run wRegistryCfg (init wRegistryCfg 1) wRegistryRun s ∧
    (exec wRegistryCfg 1 (.createNewChain 14 60 7 0 74) s).isSome ∧
    exec wRegistryCfg 1 .pause s = some s' ∧ s'.paused = true)

/-- **REQUEST PREMISES.** At the end `s` of `wRegistryRun`:
* a direct request for the ETH-based chain `10` with `msg.value = mintValue = 3` succeeds
  and sends `3` ETH to the asset router; one for chain `12`, whose base token is `8`, with
  no ETH, succeeds, deposits asset `8` and sends no ETH;
* a two-bridges request for chain `10` with `mintValue = 3`, `secondBridgeValue = 2` and
  `msg.value = 5` succeeds, with `3` ETH to the router and `2` to the second bridge; one for
  chain `12` with `secondBridgeValue = msg.value = 2` succeeds, deposits asset `8`, and sends
  nothing to the router and `2` to the bridge.
At the end `t` of `wRegistryPrelude ++ [wRegistryCreate10] ++ l₂`, with
`l₂ = wRegistryRest ++ [wRegistryBurn11] ++ wRegistryHandlerRun` (which contains no
`forwardedBridgeMint` and no `registerNewZKChain` for chain `10`), a direct request for
chain `10` deposits asset `7` and goes to `70`; and a direct request for chain `13`, which
has a `zkChainMap` key but no CTM, succeeds and goes to `73`. These meet the premises of
`DirectRequestAccounting`, `TwoBridgesRequestAccounting`, `RequestsReachRegisteredChains`
(with `RegistryRunWitness`), `RequestNeedsMapEntry` and `RequestChargesCreationBaseToken`.
The request for chain `13` shows that `RequestsReachRegisteredChains` needs its premise
excluding the handler's writers. -/
def Properties.RequestWitness : Prop :=
  ∃ s t, Run wRegistryCfg (init wRegistryCfg 1) wRegistryRun s ∧
    Run wRegistryCfg (init wRegistryCfg 1) (wRegistryPrelude ++ [wRegistryCreate10] ++
      (wRegistryRest ++ [wRegistryBurn11] ++ wRegistryHandlerRun)) t ∧
    (∀ k ∈ wRegistryRest ++ [wRegistryBurn11] ++ wRegistryHandlerRun,
      k.2.bridgeMintFor 10 = false ∧ k.2.handlerRegistersFor 10 = false) ∧
    (∃ o, requestDirect wRegistryCfg s 1 ⟨3, 0⟩
        { chainId := 10, mintValue := 3, l2Contract := 0, l2Value := 0, refundRecipient := 0 }
          = some o ∧ o.ethToAssetRouter = 3) ∧
    (∃ o, requestDirect wRegistryCfg s 1 ⟨0, 0⟩
        { chainId := 12, mintValue := 3, l2Contract := 0, l2Value := 0, refundRecipient := 0 }
          = some o ∧ o.depositAssetId = 8 ∧ o.ethToAssetRouter = 0) ∧
    (∃ o, requestTwoBridges wRegistryCfg s 1 ⟨5, 0⟩
        { chainId := 10, mintValue := 3, l2Value := 0, refundRecipient := 0,
          secondBridgeAddress := 70000, secondBridgeValue := 2 } ⟨5, 0⟩ = some o ∧
      o.ethToAssetRouter = 3 ∧ o.ethToSecondBridge = 2) ∧
    (∃ o, requestTwoBridges wRegistryCfg s 1 ⟨2, 0⟩
        { chainId := 12, mintValue := 3, l2Value := 0, refundRecipient := 0,
          secondBridgeAddress := 70000, secondBridgeValue := 2 } ⟨5, 0⟩ = some o ∧
      o.depositAssetId = 8 ∧ o.ethToAssetRouter = 0 ∧ o.ethToSecondBridge = 2) ∧
    (∃ o, requestDirect wRegistryCfg t 1 ⟨3, 0⟩
        { chainId := 10, mintValue := 3, l2Contract := 0, l2Value := 0, refundRecipient := 0 }
          = some o ∧ o.depositAssetId = 7 ∧ o.target = 70) ∧
    (∃ o, requestDirect wRegistryCfg t 1 ⟨0, 0⟩
        { chainId := 13, mintValue := 0, l2Contract := 0, l2Value := 0, refundRecipient := 0 }
          = some o ∧ (13 : ChainId) ∈ t.zkKeys ∧ t.chainTypeManager 13 = 0 ∧ o.target = 73)

end Contracts.Bridgehub
