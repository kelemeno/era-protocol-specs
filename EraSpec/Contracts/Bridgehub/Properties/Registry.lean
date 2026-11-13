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
* Outside `forwardedBridgeMint`, a registered chain's CTM and base token never change
  (`CtmAndBaseTokenFixedOutsideBridgeMint`). `forwardedBridgeMint`, callable only by the
  chain asset handler, rewrites both (`BridgeMintRewritesBaseToken`): the Bridgehub trusts
  the handler for that.
* Without the chain asset handler's two registry writers, `zkChainMap` and
  `chainTypeManager` describe the same chains, every key has a nonzero diamond, and the
  chain count stays within `MAX_NUMBER_OF_ZK_CHAINS` (`RegistryConsistentWithoutHandler`,
  `ChainCountBounded`). With them, `createNewChain` silently overwrites a map entry the
  handler wrote (`HandlerEntryOverwrittenByCreate`).
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

## Requests

* Both request paths forward all of `msg.value` and keep none; the asset router receives
  exactly `mintValue` in ETH for an ETH-based chain and nothing otherwise; the base-token
  deposit and the Mailbox request carry the same `mintValue`, for the same chain, in that
  chain's base token (`DirectRequestAccounting`, `TwoBridgesRequestAccounting`).
* In a run without the handler's registry writers, a request reaches the registered,
  nonzero diamond of a chain with a CTM and is charged in a registered asset
  (`RequestsReachRegisteredChains`). After `createNewChain(c, _, a, _, d)` and no later
  `forwardedBridgeMint` for `c`, a request for `c` is charged in `a`; with no later
  handler registry write it goes to `d` (`RequestChargesCreationBaseToken`).
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

/-- **A REQUEST IS CHARGED IN THE BASE TOKEN FIXED AT CREATION.** In any run (from any
state) of the form `l₁ ++ [createNewChain(c, m, a, adm, d)] ++ l₂` with no
`forwardedBridgeMint` for `c` in `l₂`, a successful request of either kind for `c` at the
end deposits asset `a`; if `l₂` also has no handler registry write, it goes to `d`. -/
def Properties.RequestChargesCreationBaseToken : Prop :=
  ∀ (cfg : Config) (s t : State) (l₁ l₂ : List Call) (caller₀ : Address) (c : ChainId)
    (m : Address) (a : AssetId) (adm d : Address),
    Run cfg s (l₁ ++ [(caller₀, .createNewChain c m a adm d)] ++ l₂) t →
    (∀ k ∈ l₂, k.2.bridgeMintFor c = false) →
    ∀ (caller : Address) (env : CallEnv) (o : Outcome),
      ((∃ req : DirectRequest, req.chainId = c ∧ requestDirect cfg t caller env req = some o) ∨
       (∃ (req : TwoBridgesRequest) (reply : SecondBridgeReply), req.chainId = c ∧
          requestTwoBridges cfg t caller env req reply = some o)) →
      o.depositAssetId = a ∧ ((∀ k ∈ l₂, k.2.handlerRegistryWrite = false) → o.target = d)

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
