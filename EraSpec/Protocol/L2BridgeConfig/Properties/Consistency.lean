import EraSpec.Protocol.L2BridgeConfig.Specs.Consistency

/-!
# Properties: the L2 bridge configuration words stay consistent

Statements about `EraSpec.Protocol.L2BridgeConfig.Specs.Consistency` (`b17415d20`).  Proofs are
in `EraSpec.Protocol.L2BridgeConfig.Proofs.Consistency`.

`ConfigConsistent E l1 a weth w` says that the nine L1 chain id words equal `l1 ≠ 0`, the four
base asset id copies equal `a ≠ 0`, both ETH asset ids are `encodeNTVAssetId(l1, ETH)`, the
vault's WETH is `weth ≠ 0`, the vault maps `a` to the base-token system contract and back,
every built-in is initialized, and the router's recorded trackers are zero or the vault.  It
says nothing about the base token's origin data; `BaseOriginIs` is that.

## What is proved

1. **Genesis establishes it.**  A successful genesis transaction from all-zero storage leaves
   `ConfigConsistent` with the input's `l1ChainId` and base asset id, the base id routed to
   the vault, and the input's origin data in the vault
   (`GenesisEstablishesConfigConsistent`).  The two ids are nonzero because of two checks in
   the genesis sequence: `AtomicFlowManager.initL2` refuses a zero L1 chain id, and WETH's
   `initializeV3` refuses a zero base asset id.  Witness:
   `GenesisEstablishesConfigConsistentWitness`.
2. **Every step preserves it** (`StepPreservesConfigConsistent`), given the two run premises of
   `ConfigCall.Admissible`: the upgrader makes no direct `initL2`/`updateL2` call (its calls are
   the helper's), and a logged vault registration does not register a token whose vault id on
   this chain is `a`.  A default upgrade from a consistent state succeeds only with the stored
   `l1` and `a` (`DefaultUpgradeKeepsL1AndBaseIds`); the vault's two freezes are what refuse
   anything else.  With those ids it succeeds whatever origin data it carries, and the vault
   takes that data (`DefaultUpgradeAdoptsAnyBaseOrigin`).  A second genesis reverts
   (`GenesisRevertsOnConsistentState`).  The base id stays routed to the vault under every
   call except the counterpart's write at that id (`BaseRouteMovesOnlyByCounterpart`; no run
   premise).
3. **Who writes the words.**  The scalar words change only in an upgrade transaction sent by
   `L2_FORCE_DEPLOYER_ADDR` or in a direct call whose sender is `L2_COMPLEX_UPGRADER_ADDR`, from
   any state (`OnlyUpgraderWritesScalarConfig`).  From a consistent state, the base id's
   registry entries and route change only by a default upgrade, a direct vault `updateL2` by the
   upgrader, a vault registration whose vault id is `a`, or the counterpart's write at `a`
   (`BaseEntriesWritersFromConsistent`).
4. **Runs.**  Along every run after genesis that meets the two run premises, the state stays
   consistent with the genesis ids, every logged default upgrade carries those ids, and with no
   counterpart write at `a` the base id stays routed to the vault
   (`ConfigConsistentAlongRuns`).  If in addition every logged default upgrade carries the
   genesis origin data, that data stays in the vault, and the vault's native test for the base
   token gives the genesis answer (`BaseOriginPinnedAlongRuns`).  Witness: `ConfigRunWitness`,
   a run with a default upgrade that changes the router's `L1_ASSET_ROUTER`, a vault
   registration, a bridged-token deployment, a counterpart write and a fallback write.

## Countermodels for the premises

* `NoBaseFreezeLeavesTrackerOnOldBase`: with the vault's base-id freeze removed, a default
  upgrade with a new base id succeeds from every consistent state, and the tracker and WETH keep
  the old id; the state is consistent for no ids.  The deployed vault refuses the same upgrade.
* `NoL1FreezeLeavesTrackerOnOldL1`: the same for the L1 chain id freeze, with the tracker,
  interop center, base token and flow manager keeping the old id.
* `SameBaseOriginRewriteFlipsNativeTest`: a default upgrade with the stored ids and origin chain
  `block.chainid` succeeds from every consistent state whose base token is not native, stays
  consistent, and makes the vault's (and the tracker's) native test true for the base token.
* `RouterUpdateOutsideHelperDivergesBase`: `L2AssetRouter.updateL2` called by the upgrader
  outside the helper with a new base id succeeds from every consistent state and leaves the
  router's id different from the vault's; the state is consistent for no ids.
* `ConfigCountermodelWitness`: a consistent state reached by genesis whose base token is not
  native, on which the flip and the divergence happen, and on which the default upgrade with
  origin chain `block.chainid` changes the base id's registry entries.
-/

namespace Contracts.L2BridgeConfig

open Contracts.AssetRouter (Chain AssetId Address)

/-! ## (1) Genesis -/

/-- **GENESIS ESTABLISHES THE INVARIANT.**  If the genesis transaction succeeds from all-zero
storage, then its sender is `L2_FORCE_DEPLOYER_ADDR`, the state is `ConfigConsistent` with the
input's `l1ChainId`, base asset id and the created WETH proxy, the base id is routed to the
vault, and the vault holds the input's origin chain and origin token for it.  Premise: the
base-token system contract address is nonzero. -/
def Properties.GenesisEstablishesConfigConsistent : Prop :=
  ∀ (E : ConfigEnv) (s : Address) (c : Chain) (u : UpgradeInput) (w : ConfigWorld),
    E.baseTokenAddr ≠ 0 →
    configExec E s ConfigWorld.fresh (.upgrade (.genesis c u)) = some w →
    s = E.forceDeployer ∧
    ConfigConsistent E u.l1ChainId u.base.assetId (E.wethProxy u) w ∧
    BaseRoutedToVault E u.base.assetId w ∧
    BaseOriginIs u.base.originChainId u.base.originToken u.base.assetId w

/-- **GENESIS CAN SUCCEED, ON A REALISTIC INPUT.**  Some environment with a nonzero base-token
address and some input, whose L1 chain id and base-token origin chain differ from this chain
and whose base asset id is the vault id of its origin token, make the genesis transaction
succeed.  The environment's encoding is a toy (chain plus sender plus data); no property of
keccak is used. -/
def Properties.GenesisEstablishesConfigConsistentWitness : Prop :=
  ∃ (E : ConfigEnv) (c : Chain) (u : UpgradeInput) (w : ConfigWorld),
    E.baseTokenAddr ≠ 0 ∧
    configExec E E.forceDeployer ConfigWorld.fresh (.upgrade (.genesis c u)) = some w ∧
    u.l1ChainId ≠ E.thisChain ∧ u.base.originChainId ≠ E.thisChain ∧
    u.base.assetId = E.encNTV u.base.originChainId u.base.originToken

/-! ## (2) Preservation -/

/-- **EVERY STEP PRESERVES THE INVARIANT.**  From a `ConfigConsistent` state, every successful
call that meets `ConfigCall.Admissible` for the base id leaves a `ConfigConsistent` state with
the same ids and WETH. -/
def Properties.StepPreservesConfigConsistent : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (c : ConfigCall) (w' : ConfigWorld),
    ConfigConsistent E l1 a weth w → c.Admissible E a →
    configExec E c.sender w c.op = some w' → ConfigConsistent E l1 a weth w'

/-- **A DEFAULT UPGRADE SUCCEEDS ONLY WITH THE STORED IDS.**  From a `ConfigConsistent` state, a
successful default upgrade carries the stored L1 chain id and base asset id.  No other
premise. -/
def Properties.DefaultUpgradeKeepsL1AndBaseIds : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (s : Address) (u : UpgradeInput) (w' : ConfigWorld),
    ConfigConsistent E l1 a weth w →
    configExec E s w (.upgrade (.default u)) = some w' →
    u.l1ChainId = l1 ∧ u.base.assetId = a

/-- **WITH THE STORED IDS, A DEFAULT UPGRADE SUCCEEDS WHATEVER ORIGIN DATA IT CARRIES.**  From a
`ConfigConsistent` state, a default upgrade sent by the force deployer with the stored ids, a
nonzero governance and a nonzero L1 asset router succeeds in the model; the result is consistent
with the same ids and WETH, the vault holds the upgrade's origin chain and origin token for the
base id, and the router holds the upgrade's L1 asset router.  The parts of the default upgrade
the model omits (`_setupProxyAdmin`, `InteropHandler.updateL2`, `Bridgehub.setAddresses`, the
owner resets) do not read the origin data. -/
def Properties.DefaultUpgradeAdoptsAnyBaseOrigin : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (u : UpgradeInput),
    ConfigConsistent E l1 a weth w →
    u.l1ChainId = l1 → u.base.assetId = a → u.governance ≠ 0 → u.l1AssetRouter ≠ 0 →
    ∃ w', configExec E E.forceDeployer w (.upgrade (.default u)) = some w' ∧
      ConfigConsistent E l1 a weth w' ∧
      BaseOriginIs u.base.originChainId u.base.originToken a w' ∧
      w'.router.l1AssetRouter = u.l1AssetRouter

/-- **GENESIS DOES NOT RUN AGAIN.**  On a `ConfigConsistent` state every genesis transaction
reverts (the message root's lock is set). -/
def Properties.GenesisRevertsOnConsistentState : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (s : Address) (c : Chain) (u : UpgradeInput),
    ConfigConsistent E l1 a weth w →
    configExec E s w (.upgrade (.genesis c u)) = none

/-- **THE BASE ID STAYS ROUTED TO THE VAULT EXCEPT THROUGH THE COUNTERPART.**  From a
`ConfigConsistent` state whose router points `a` at the vault, every successful call other than
the counterpart's `setAssetHandlerAddress` at `a` leaves `a` pointed at the vault.  Any sender,
no run premise. -/
def Properties.BaseRouteMovesOnlyByCounterpart : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (c : ConfigCall) (w' : ConfigWorld),
    ConfigConsistent E l1 a weth w → BaseRoutedToVault E a w →
    configExec E c.sender w c.op = some w' → ¬ c.op.IsCounterpartAt a →
    BaseRoutedToVault E a w'

/-! ## (3) Writers -/

/-- **ONLY THE UPGRADER WRITES THE SCALAR WORDS.**  From any state, a successful modelled call
(`configExec`) that changes a scalar word is an upgrade transaction sent by
`L2_FORCE_DEPLOYER_ADDR`, or a direct `initL2`/`updateL2` call whose sender is
`L2_COMPLEX_UPGRADER_ADDR`.  The modelled calls include every writer of these words found at
`b17415d20` (see the Specs header). -/
def Properties.OnlyUpgraderWritesScalarConfig : Prop :=
  ∀ (E : ConfigEnv) (s : Address) (w : ConfigWorld) (op : ConfigOp) (w' : ConfigWorld),
    configExec E s w op = some w' → w'.scalars ≠ w.scalars →
    ((∃ p, op = .upgrade p) ∧ s = E.forceDeployer) ∨ ((∃ d, op = .direct d) ∧ s = E.upgrader)

/-- **WHO WRITES THE BASE ID'S ENTRIES.**  From a `ConfigConsistent` state, a successful modelled
call that changes `tokenAddress[a]`, `assetId[L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR]`,
`originChainId[a]` or the router's handler of `a` is one of: a default upgrade sent by the force
deployer; a direct vault `updateL2` by the upgrader; a vault registration of a token whose vault
id on this chain is `a`; the counterpart's write at `a`, from the chain `l1` and a sender whose
un-aliased address is the router's `L1_ASSET_ROUTER`. -/
def Properties.BaseEntriesWritersFromConsistent : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (s : Address) (op : ConfigOp) (w' : ConfigWorld),
    ConfigConsistent E l1 a weth w →
    configExec E s w op = some w' → w'.baseEntries E a ≠ w.baseEntries E a →
    ((∃ u, op = .upgrade (.default u)) ∧ s = E.forceDeployer) ∨
    ((∃ l1' weth' b, op = .direct (.vaultUpdate l1' weth' b)) ∧ s = E.upgrader) ∨
    (∃ t, op = .vaultRegister t ∧ E.encNTV E.thisChain t = a) ∨
    (∃ h, op = .counterpartSet l1 a h ∧ E.undoAlias s = w.router.l1AssetRouter)

/-! ## (4) Runs -/

/-- **THE INVARIANT ALONG RUNS.**  After a successful genesis from all-zero storage (with a
nonzero base-token address), along every run whose calls meet `ConfigCall.Admissible` for the
genesis base id: the final state is `ConfigConsistent` with the genesis ids and the created
WETH; every logged default upgrade carries the genesis ids; and if no logged call is the
counterpart's write at the base id, that id is still routed to the vault. -/
def Properties.ConfigConsistentAlongRuns : Prop :=
  ∀ (E : ConfigEnv) (s : Address) (c : Chain) (u : UpgradeInput) (w0 : ConfigWorld)
    (cs : List ConfigCall) (w : ConfigWorld),
    E.baseTokenAddr ≠ 0 →
    configExec E s ConfigWorld.fresh (.upgrade (.genesis c u)) = some w0 →
    ConfigRun E w0 cs w → (∀ call ∈ cs, call.Admissible E u.base.assetId) →
    ConfigConsistent E u.l1ChainId u.base.assetId (E.wethProxy u) w ∧
    (∀ call ∈ cs, ∀ u', call.op = .upgrade (.default u') →
      u'.l1ChainId = u.l1ChainId ∧ u'.base.assetId = u.base.assetId) ∧
    ((∀ call ∈ cs, ¬ call.op.IsCounterpartAt u.base.assetId) →
      BaseRoutedToVault E u.base.assetId w)

/-- **REPAIRED FORM FOR THE ORIGIN DATA.**  In the setting of `ConfigConsistentAlongRuns`, if
also every logged default upgrade carries the genesis origin chain and origin token, the vault
still holds them for the base id, and the vault's native test for the base token is true exactly
when the genesis origin chain is this chain. -/
def Properties.BaseOriginPinnedAlongRuns : Prop :=
  ∀ (E : ConfigEnv) (s : Address) (c : Chain) (u : UpgradeInput) (w0 : ConfigWorld)
    (cs : List ConfigCall) (w : ConfigWorld),
    E.baseTokenAddr ≠ 0 →
    configExec E s ConfigWorld.fresh (.upgrade (.genesis c u)) = some w0 →
    ConfigRun E w0 cs w → (∀ call ∈ cs, call.Admissible E u.base.assetId) →
    (∀ call ∈ cs, call.KeepsBaseOrigin u.base.originChainId u.base.originToken) →
    BaseOriginIs u.base.originChainId u.base.originToken u.base.assetId w ∧
    (BaseNativeHere E w ↔ u.base.originChainId = E.thisChain)

/-- **THE RUN PREMISES HOLD ON A RUN THAT USES EVERY KIND OF WRITER.**  A successful genesis,
then a run of five calls, all admissible, none the counterpart's write at the base id, every
default upgrade carrying the genesis origin data: a default upgrade sent by the force deployer
that changes the router's L1 asset router; a vault registration; a bridged-token deployment; a
counterpart write; a fallback write.  The scalar words differ between the start and the end of
the run. -/
def Properties.ConfigRunWitness : Prop :=
  ∃ (E : ConfigEnv) (c : Chain) (u : UpgradeInput) (w0 : ConfigWorld) (cs : List ConfigCall)
    (w : ConfigWorld),
    E.baseTokenAddr ≠ 0 ∧
    configExec E E.forceDeployer ConfigWorld.fresh (.upgrade (.genesis c u)) = some w0 ∧
    ConfigRun E w0 cs w ∧
    (∀ call ∈ cs, call.Admissible E u.base.assetId) ∧
    (∀ call ∈ cs, call.KeepsBaseOrigin u.base.originChainId u.base.originToken) ∧
    (∀ call ∈ cs, ¬ call.op.IsCounterpartAt u.base.assetId) ∧
    (∃ u', ConfigCall.mk E.forceDeployer (.upgrade (.default u')) ∈ cs ∧
      u'.l1AssetRouter ≠ u.l1AssetRouter) ∧
    (∃ s t, ConfigCall.mk s (.vaultRegister t) ∈ cs) ∧
    (∃ s id o ot tok, ConfigCall.mk s (.vaultDeploy id o ot tok) ∈ cs) ∧
    (∃ s src id h, ConfigCall.mk s (.counterpartSet src id h) ∈ cs) ∧
    (∃ s id, ConfigCall.mk s (.finalizeFallback id) ∈ cs) ∧
    w.scalars ≠ w0.scalars

/-! ## Countermodels -/

/-- **WITHOUT THE BASE-ID FREEZE THE TRACKER KEEPS THE OLD ID.**  From every
`ConfigConsistent` state, a default upgrade with the stored L1 chain id, a different base asset
id, a nonzero governance and a nonzero L1 asset router is refused by the deployed vault, but
succeeds with the vault's base-id freeze (`NTV/L2NativeTokenVault.sol:152-155`) removed.  Then
the router and the vault hold the new id, the tracker and WETH the old one, and the state is
`ConfigConsistent` for no ids. -/
def Properties.NoBaseFreezeLeavesTrackerOnOldBase : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (u : UpgradeInput),
    ConfigConsistent E l1 a weth w →
    u.l1ChainId = l1 → u.base.assetId ≠ a → u.governance ≠ 0 → u.l1AssetRouter ≠ 0 →
    defaultUpgrade E u w = none ∧
    ∃ w', defaultUpgradeWith ⟨true, false⟩ E u w = some w' ∧
      w'.router.base = u.base.assetId ∧ w'.vault.base = u.base.assetId ∧
      w'.tracker.base = a ∧ w'.weth.base = a ∧
      ∀ l1' a' weth', ¬ ConfigConsistent E l1' a' weth' w'

/-- **WITHOUT THE L1-ID FREEZE THE GENESIS-ONLY CONTRACTS KEEP THE OLD L1 ID.**  From every
`ConfigConsistent` state, a default upgrade with a different L1 chain id, the stored base asset
id, a nonzero governance and a nonzero L1 asset router is refused by the deployed vault, but
succeeds with the vault's L1 freeze (`NTV/L2NativeTokenVault.sol:148`) removed.  Then the
message root, bridgehub, router, vault and chain asset handler hold the new id, the tracker,
interop center, base token and flow manager the old one, and the state is `ConfigConsistent`
for no ids. -/
def Properties.NoL1FreezeLeavesTrackerOnOldL1 : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (u : UpgradeInput),
    ConfigConsistent E l1 a weth w →
    u.l1ChainId ≠ l1 → u.base.assetId = a → u.governance ≠ 0 → u.l1AssetRouter ≠ 0 →
    defaultUpgrade E u w = none ∧
    ∃ w', defaultUpgradeWith ⟨false, true⟩ E u w = some w' ∧
      w'.messageRoot.l1 = u.l1ChainId ∧ w'.bridgehub.l1 = u.l1ChainId ∧
      w'.router.l1 = u.l1ChainId ∧ w'.vault.l1 = u.l1ChainId ∧
      w'.chainAssetHandler.l1 = u.l1ChainId ∧
      w'.tracker.l1 = l1 ∧ w'.center.l1 = l1 ∧ w'.baseToken.l1 = l1 ∧ w'.flowManager.l1 = l1 ∧
      ∀ l1' a' weth', ¬ ConfigConsistent E l1' a' weth' w'

/-- **SAME BASE ID, NEW ORIGIN CHAIN: THE NATIVE TEST FLIPS.**  From every `ConfigConsistent`
state whose base token is not native to this chain, a default upgrade sent by the force deployer
with the stored ids, origin chain `block.chainid`, a nonzero governance and a nonzero L1 asset
router succeeds in the model; the result is still `ConfigConsistent` with the same ids and WETH,
and the vault's native test for the base token (read by the tracker too) is now true.  So
`ConfigConsistent` does not pin the origin data; `BaseOriginPinnedAlongRuns` is the form that
does, under its premise on the upgrade data. -/
def Properties.SameBaseOriginRewriteFlipsNativeTest : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (u : UpgradeInput),
    ConfigConsistent E l1 a weth w → ¬ BaseNativeHere E w →
    u.l1ChainId = l1 → u.base.assetId = a → u.base.originChainId = E.thisChain →
    u.governance ≠ 0 → u.l1AssetRouter ≠ 0 →
    ∃ w', configExec E E.forceDeployer w (.upgrade (.default u)) = some w' ∧
      ConfigConsistent E l1 a weth w' ∧ BaseNativeHere E w'

/-- **THE ROUTER'S `updateL2` OUTSIDE THE HELPER SPLITS THE BASE ID.**  From every
`ConfigConsistent` state, `L2AssetRouter.updateL2(l1, r, a')` called directly by
`L2_COMPLEX_UPGRADER_ADDR` with a nonzero `r` and `a' ≠ a` succeeds.  Then the router holds `a'`
while the vault and the tracker hold `a`, and the state is `ConfigConsistent` for no ids. -/
def Properties.RouterUpdateOutsideHelperDivergesBase : Prop :=
  ∀ (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address) (w : ConfigWorld)
    (r : Address) (a' : AssetId),
    ConfigConsistent E l1 a weth w → r ≠ 0 → a' ≠ a →
    ∃ w', configExec E E.upgrader w (.direct (.routerUpdate l1 r a')) = some w' ∧
      w'.router.base = a' ∧ w'.vault.base = a ∧ w'.tracker.base = a ∧
      ∀ l1' a'' weth', ¬ ConfigConsistent E l1' a'' weth' w'

/-- **THE COUNTERMODEL PREMISES HOLD.**  A genesis from all-zero storage reaches a
`ConfigConsistent` state whose base token is not native to this chain.  On it, a default upgrade
with the stored ids and origin chain `block.chainid` succeeds, changes the base id's registry
entries and flips the native test; and a direct router `updateL2` by the upgrader with another
base id succeeds and leaves the router's id different from the vault's. -/
def Properties.ConfigCountermodelWitness : Prop :=
  ∃ (E : ConfigEnv) (c : Chain) (u : UpgradeInput) (w : ConfigWorld),
    configExec E E.forceDeployer ConfigWorld.fresh (.upgrade (.genesis c u)) = some w ∧
    ConfigConsistent E u.l1ChainId u.base.assetId (E.wethProxy u) w ∧
    ¬ BaseNativeHere E w ∧
    (∃ u' w', u'.l1ChainId = u.l1ChainId ∧ u'.base.assetId = u.base.assetId ∧
      u'.base.originChainId = E.thisChain ∧
      configExec E E.forceDeployer w (.upgrade (.default u')) = some w' ∧
      w'.baseEntries E u.base.assetId ≠ w.baseEntries E u.base.assetId ∧ BaseNativeHere E w') ∧
    (∃ r a' w', configExec E E.upgrader w (.direct (.routerUpdate u.l1ChainId r a')) = some w' ∧
      w'.router.base ≠ w'.vault.base)

end Contracts.L2BridgeConfig
