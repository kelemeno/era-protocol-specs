import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Model: the L1 asset router at `draft/v0.35.0` — the asset-handler gate

Source: era-contracts branch `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.
Paths are relative to `l1-contracts/contracts/`; `bridge/asset-router/` is shortened to `AR/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.HandlerGateAtV35` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.HandlerGateAtV35`.  It changes nothing in
`AllWriters`.  It reuses `AllWriters`' configuration (`Cfg`), writes (`setHandler`, `pointAt`,
`recordTracker`) and operations (`Op`), for an L1 configuration (`side = .l1`).

## The check v35 adds to the L1 router

`_checkAssetHandlerAllowed` is new at v35.

    // AR/L1AssetRouter.sol:276-288
    function _checkAssetHandlerAllowed(uint256 _chainId, bytes32 _assetId) internal view {
        address assetHandler = assetHandlerAddress[_assetId];
        if (assetHandler == address(0) || assetHandler == address(nativeTokenVault)
            || assetHandler == BRIDGE_HUB.chainAssetHandler()) { return; }
        if (!IL1MessageRoot(address(BRIDGE_HUB.messageRoot())).isInteropEnabled(_chainId)) {
            revert AssetHandlerNotAllowed(_chainId, _assetId, assetHandler);
        }
    }

It runs first in four entry points, each of which then moves the asset through
`assetHandlerAddress[_assetId]`:

| Entry point | Gate | What follows |
|---|---|---|
| `bridgehubDepositBaseToken` (`AR/L1AssetRouter.sol:190-198`, `onlyBridgehub`) | `:196` | `_bridgehubDepositBaseToken`: handler `≠ 0` (`AR/AssetRouterBase.sol:104`), its `bridgeBurn` (`:107-113`) |
| `bridgehubDeposit` with `NEW_ENCODING_VERSION` (`AR/L1AssetRouter.sol:201-241`, `onlyBridgehub`) | `:228-232` | `_bridgehubDeposit` → `_bridgehubDepositNonBaseTokenAsset` → `_burn` (`AR/AssetRouterBase.sol:118-138, 140-183, 303-331`) |
| `finalizeDeposit` (`AR/L1AssetRouter.sol:291-299`, `onlySelf`) | `:296` | `_finalizeDeposit` (`AR/AssetRouterBase.sol:267-283`) |
| `bridgeConfirmTransferResult` (`AR/L1AssetRouter.sol:306-325`, `onlyNullifier`) | `:313` | the handler's `bridgeConfirmTransferResult` (`:314-320`) |

The chain the gate checks is a deposit's destination, a withdrawal's source (`receiveMessage`
requires `_sourceChainId` to be the proven sender's chain, `AR/AssetRouterBase.sol:235-239`),
or a failed deposit's destination.

The router's other entry points are not part of this model; none of them writes the router's
maps (`AllWriters` lists the writers).

Not gated, and moving no asset: `setAssetHandlerAddressThisChain`
(`AR/L1AssetRouter.sol:145-150`), `setAssetDeploymentTracker` (`:135-142`),
`setNativeTokenVault` (`:116-121`), and the `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION`
branch of `bridgehubDeposit` (`:216-226`), which only builds an L2 message
(`_setAssetHandlerAddressOnCounterpart` is `view`, `:158-183`).  Every other encoding version
reverts: `_bridgehubDeposit` accepts only `NEW_ENCODING_VERSION` (`UnsupportedEncodingVersion`,
`AR/AssetRouterBase.sol:125-137`).  A grep of `assetHandlerAddress` over the v35 `contracts/`
tree finds no other L1 read that moves an asset through the handler:
`core/bridgehub/BridgehubBase.sol:316-323` asks a base token's handler for the token's address
(a `view` call), and `governance/PermanentRestriction.sol:355` compares a chain asset's handler
with the Bridgehub.

## What the gate reads

* `address(nativeTokenVault)`, the router's own vault: `Cfg.ntv`.
* `BRIDGE_HUB.chainAssetHandler()` (`core/bridgehub/BridgehubBase.sol:124`), written only by
  `L1Bridgehub.setAddresses` (`core/bridgehub/L1Bridgehub.sol:268-280`, owner or upgrader).
* `isInteropEnabled(c)` of the current `BRIDGE_HUB.messageRoot()`
  (`core/message-root/L1MessageRoot.sol:92-94`).  The flag is written only by
  `enableInterop(c, requireSecondProofSystem)` (`:72-89`): Bridgehub owner only (`:73`), chain
  registered (`:74-75`), not yet enabled (`:76`), no pending `chainBalanceBackfill`
  (`:77-80`), and on request the second-proof-system checks (`:81-85`).  It sets the flag
  (`:87`) and nothing in the contract clears it.  `setAddresses` can also replace the message
  root itself (`L1Bridgehub.sol:277`), and the gate then reads the new root's flags, so the
  model lets it replace the whole flag table.

`Env` holds the last two.  `enableInterop` and `setAddresses` are the only events that
change it.

## The step relation

`StepV35` is `AllWriters.AStep` on the L1 side, with three changes:

* The fallback `finalize` carries its source chain and runs the gate first.  The gate
  always passes there: the fallback is taken only when the handler is unset.
* The four gated entry points are events (`Ev.gated`) that move an asset through the
  registered handler and write neither router map.  They need a nonzero handler: the
  base-token deposit requires it (`AR/AssetRouterBase.sol:104`); a withdrawal takes the live
  branch of `_finalizeDeposit` (`:275`); and `bridgeConfirmTransferResult` calls the handler
  through an interface function that returns nothing
  (`bridge/interfaces/IL1AssetHandler.sol:16-22`), so Solidity rejects a call to an address
  without code (`SOL-CONTROL`, `VM-CALL`).  For a deposit, `_burn` registers an unset asset on
  the fly (`AR/AssetRouterBase.sol:312-321`): that is the vault's
  `setAssetHandlerAddressThisChain` (`bridge/ntv/NativeTokenVaultBase.sol:321-335, 492-499`),
  which must write `_assetId` (`:334`).  The model logs it as the vault's own `register` event
  before the deposit.  The gate saw the unset handler and passed; after the registration the
  handler is the vault, which the gate exempts too.
* `enableInterop` and `setAddresses` change the environment and nothing else.  The
  counterpart message branch changes nothing on L1.

The handlers' own calls (`bridgeBurn`, `bridgeMint`, `bridgeConfirmTransferResult`) are taken
to succeed, and the entry points' other reverts are not modelled: the modifiers
(`onlyBridgehub`, `onlySelf`, `onlyNullifier`, `whenNotPaused`, `nonReentrant`),
`receiveMessage`'s checks, `msg.value`, and the base-token check of
`_bridgehubDepositNonBaseTokenAsset` (`AR/AssetRouterBase.sol:150`).  So the model has at
least the runs of the code, up to the split of an on-the-fly registration into its own event,
which is what the safety results need.  Its enabledness results are statements about the gate
and the handler-set check only.

## Writers at v35

A grep of `_setAssetHandler(` and `assetDeploymentTracker[` over the whole v35 tree finds
`AllWriters`' writers and nothing else outside the tests (no contract inherits either
router): `AR/AssetRouterBase.sol:74-75` (`register`), `:278` (`finalize`),
`AR/L1AssetRouter.sol:120` (`seed`), `:140` (`setTracker`), `AR/L2AssetRouter.sol:162` (L2
`seed`), `:203` (L2 `counterpartSet`).  `AllWriters`' L1 operations are therefore complete at v35, and every v35 run
projects onto an `AllWriters` L1 run (`Properties.RunProjectsToAllWriters`).

## Boundaries

* `Cfg.ntv` is the router's vault for the whole run.  Before `setNativeTokenVault` the
  source's `nativeTokenVault` is zero, so its exemption set is smaller there and the model has
  more runs, not fewer.
* Who may call `setAddresses`, `enableInterop`, `setNativeTokenVault` and
  `setAssetDeploymentTracker` is not tracked: each is an event any run may contain.
  `enableInterop`'s guards other than `!interopEnabled[c]` are abstracted, so the model admits
  every enabling the source admits, and more.
* Router, Bridgehub and message-root upgrades are out of scope (`OPS-CONFIG`).
* `msg.value`, pause, `nonReentrant`, events, and the handlers' internal state are not
  modelled.  For instance the L1 vault's per-chain balance cap
  (`bridge/ntv/L1NativeTokenVault.sol:439-459`) is not part of this model; the upstream
  documentation gives it as the reason for the gate (era-contracts
  `protocol-docs/interop-gating.md:143-144` at `b17415d20`).
-/

namespace Contracts.AssetRouter.HandlerGateAtV35

open Contracts.AssetRouter.AllWriters (Cfg Op pointAt recordTracker)

/-! ## The environment the gate reads -/

/-- What `_checkAssetHandlerAllowed` reads outside the router. -/
structure Env where
  /-- `BRIDGE_HUB.chainAssetHandler()` (`core/bridgehub/BridgehubBase.sol:124`). -/
  cah : Address
  /-- `isInteropEnabled(c)` of the current message root
  (`core/message-root/L1MessageRoot.sol:92-94`). -/
  ie : Chain → Bool

/-- The L1 router's two maps, and the environment. -/
structure St where
  /-- `assetHandlerAddress` / `assetDeploymentTracker`. -/
  router : Router
  /-- The chain asset handler and the interop flags. -/
  env : Env

/-- `enableInterop(c)`'s write (`core/message-root/L1MessageRoot.sol:87`). -/
def enable (E : Env) (c : Chain) : Env :=
  { E with ie := fun x => if x = c then true else E.ie x }

/-! ## The gate -/

/-- **`_checkAssetHandlerAllowed(c, a)` returns** (`AR/L1AssetRouter.sol:276-288`): the
handler is unset, the vault, or the chain asset handler, or `c` is interop-enabled. -/
def Allowed (K : Cfg) (E : Env) (R : Router) (c : Chain) (a : AssetId) : Prop :=
  R.handler a = 0 ∨ R.handler a = K.ntv ∨ R.handler a = E.cah ∨ E.ie c = true

instance (K : Cfg) (E : Env) (R : Router) (c : Chain) (a : AssetId) :
    Decidable (Allowed K E R c a) := by
  unfold Allowed
  infer_instance

/-- A handler the gate does not exempt: not unset, not the vault, not the chain asset
handler. -/
def Custom (K : Cfg) (E : Env) (h : Address) : Prop :=
  h ≠ 0 ∧ h ≠ K.ntv ∧ h ≠ E.cah

instance (K : Cfg) (E : Env) (h : Address) : Decidable (Custom K E h) := by
  unfold Custom
  infer_instance

/-- **Every gated movement of asset `a` to or from chain `c` reverts in `S`**: the asset's
handler is custom and `c` is not interop-enabled. -/
def Stranded (K : Cfg) (S : St) (c : Chain) (a : AssetId) : Prop :=
  Custom K S.env (S.router.handler a) ∧ S.env.ie c = false

instance (K : Cfg) (S : St) (c : Chain) (a : AssetId) : Decidable (Stranded K S c a) := by
  unfold Stranded
  infer_instance

/-! ## Events -/

/-- The gated entry points that move an asset through its registered handler and write
neither router map. -/
inductive Gated where
  /-- `bridgehubDeposit` with `NEW_ENCODING_VERSION` (`AR/L1AssetRouter.sol:228-240`); the
  handler's `bridgeBurn` (`AR/AssetRouterBase.sol:324-330`).  A deposit to chain `c`. -/
  | deposit
  /-- `bridgehubDepositBaseToken` (`AR/L1AssetRouter.sol:190-198`); the handler's
  `bridgeBurn` (`AR/AssetRouterBase.sol:107-113`).  A base-token deposit to chain `c`. -/
  | depositBase
  /-- `finalizeDeposit` (`AR/L1AssetRouter.sol:291-299`) on a registered handler; its
  `bridgeMint` (`AR/AssetRouterBase.sol:275-276`).  A withdrawal from chain `c`. -/
  | finalizeLive
  /-- `bridgeConfirmTransferResult` (`AR/L1AssetRouter.sol:306-325`); the handler's
  `bridgeConfirmTransferResult` (`:314-320`).  The result of a deposit to chain `c`: a
  failed deposit's refund, or a confirmation. -/
  | confirm
  deriving DecidableEq

/-- One successful call on the L1 side at v35. -/
inductive Ev where
  /-- `setAssetHandlerAddressThisChain(d, h)` by `caller` (`AR/L1AssetRouter.sol:145-150`,
  `AR/AssetRouterBase.sol:65-77`).  Not gated. -/
  | register (caller : Address) (d : AssetData) (h : Address)
  /-- `setNativeTokenVault`'s write (`AR/L1AssetRouter.sol:116-121`, write `:120`). -/
  | seed
  /-- `setAssetDeploymentTracker(d, t)` (`AR/L1AssetRouter.sol:135-142`, write `:140`). -/
  | setTracker (d : AssetData) (t : Address)
  /-- `finalizeDeposit(c, a, _)` taking `_finalizeDeposit`'s fallback
  (`AR/AssetRouterBase.sol:277-282`, write `:278`): a withdrawal from chain `c` of an asset
  with no handler. -/
  | finalize (c : Chain) (a : AssetId)
  /-- A gated entry point at chain `c` and asset `a`, moving the asset through its handler. -/
  | gated (g : Gated) (c : Chain) (a : AssetId)
  /-- `bridgehubDeposit` with `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION`
  (`AR/L1AssetRouter.sol:216-226`): builds the L2 `setAssetHandlerAddress(.., a, h)` for chain
  `c`; writes nothing on L1. -/
  | counterpartMsg (c : Chain) (a : AssetId) (h : Address)
  /-- `L1MessageRoot.enableInterop(c, _)` (`core/message-root/L1MessageRoot.sol:72-89`). -/
  | enableInterop (c : Chain)
  /-- `L1Bridgehub.setAddresses` (`core/bridgehub/L1Bridgehub.sol:268-280`): a new chain asset
  handler and a new message root, hence a new interop table. -/
  | setAddresses (cah : Address) (ie : Chain → Bool)

/-- **One successful call at v35.**  A revert is the absence of a step.  Meant for an L1
configuration (`K.side = .l1`): the tracker write is L1's. -/
inductive StepV35 (K : Cfg) : Ev → St → St → Prop
  /-- The ungated registration, exactly `AllWriters`' (`AR/AssetRouterBase.sol:70-75`). -/
  | register {S : St} {caller : Address} {d : AssetData} {h : Address} :
      SetGuard K.enc K.thisChain K.ntv K.ntvAddr S.router caller d →
      StepV35 K (.register caller d h) S
        ⟨setHandler K.enc K.thisChain K.ntv K.ntvAddr S.router caller d h, S.env⟩
  /-- `setNativeTokenVault`'s route to the vault. -/
  | seed {S : St} : StepV35 K .seed S ⟨pointAt S.router K.seedId K.ntv, S.env⟩
  /-- The owner's tracker write. -/
  | setTracker {S : St} {d : AssetData} {t : Address} :
      StepV35 K (.setTracker d t) S ⟨recordTracker K S.router d t, S.env⟩
  /-- `finalizeDeposit`: the gate (`AR/L1AssetRouter.sol:296`), then the fallback on an unset
  handler, whose vault `bridgeMint` succeeds. -/
  | finalize {S : St} {c : Chain} {a : AssetId} :
      Allowed K S.env S.router c a → S.router.handler a = 0 → K.ntvMints a →
      StepV35 K (.finalize c a) S ⟨pointAt S.router a K.ntv, S.env⟩
  /-- A gated entry point: the gate passes and the handler is set.  The maps are unchanged. -/
  | gated {S : St} {g : Gated} {c : Chain} {a : AssetId} :
      Allowed K S.env S.router c a → S.router.handler a ≠ 0 →
      StepV35 K (.gated g c a) S S
  /-- The counterpart branch writes nothing on L1. -/
  | counterpartMsg {S : St} {c : Chain} {a : AssetId} {h : Address} :
      StepV35 K (.counterpartMsg c a h) S S
  /-- `enableInterop(c)`: `require(!interopEnabled[c])` (`L1MessageRoot.sol:76`), then the
  flag is set (`:87`). -/
  | enableInterop {S : St} {c : Chain} :
      S.env.ie c = false → StepV35 K (.enableInterop c) S ⟨S.router, enable S.env c⟩
  /-- `setAddresses`: any chain asset handler, any message root. -/
  | setAddresses {S : St} {cah : Address} {ie : Chain → Bool} :
      StepV35 K (.setAddresses cah ie) S ⟨S.router, ⟨cah, ie⟩⟩

/-- A v35 run with every call logged, oldest first. -/
inductive RunV35 (K : Cfg) : St → List Ev → St → Prop
  | nil {S : St} : RunV35 K S [] S
  | snoc {S T U : St} {evs : List Ev} {e : Ev} :
      RunV35 K S evs T → StepV35 K e T U → RunV35 K S (evs ++ [e]) U

/-! ## Classifying events -/

/-- The `AllWriters` operation an event performs on the router's maps, if any. -/
def Ev.op : Ev → Option Op
  | .register caller d h => some (.register caller d h)
  | .seed => some .seed
  | .setTracker d t => some (.setTracker d t)
  | .finalize _ a => some (.finalize a)
  | .gated _ _ _ => none
  | .counterpartMsg _ _ _ => none
  | .enableInterop _ => none
  | .setAddresses _ _ => none

/-- The router-writing calls of a v35 log, as an `AllWriters` log. -/
def ops (evs : List Ev) : List Op := evs.filterMap Ev.op

/-- The (chain, asset) an asset-moving event checks: `finalizeDeposit`'s source chain, a
deposit's destination, a confirmation's chain.  `none` for an event that moves no asset. -/
def Ev.gatedAt : Ev → Option (Chain × AssetId)
  | .finalize c a => some (c, a)
  | .gated _ c a => some (c, a)
  | _ => none

/-- The handler an asset-moving event, run from `S`, moves its asset through: the registered
handler for a gated entry point, the router's vault for the fallback
(`AR/AssetRouterBase.sol:278-281`).  `none` for an event that moves no asset. -/
def Ev.through (K : Cfg) (S : St) : Ev → Option Address
  | .finalize _ _ => some K.ntv
  | .gated _ _ a => some (S.router.handler a)
  | _ => none

/-- The owner's (or upgrader's) `setAddresses`. -/
def Ev.IsSetAddresses : Ev → Prop
  | .setAddresses _ _ => True
  | _ => False

/-- The calls that can write the handler of `a` once it is set: a registration whose
derived id is `a` (`AR/AssetRouterBase.sol:72-74`), and `setNativeTokenVault` when `a` is the
seeded id (`AR/L1AssetRouter.sol:120`).  The fallback writes only an unset handler.  The
condition is on the call's arguments only, not on whether its guard passes. -/
def Ev.RewritesHandler (K : Cfg) (a : AssetId) : Ev → Prop
  | .register caller d _ => writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d = a
  | .seed => K.seedId = a
  | _ => False

/-- The calls that can end a stranding at `(c, a)`: one that can rewrite `a`'s handler,
`enableInterop(c)`, and `setAddresses`. -/
def Ev.MayUnstrand (K : Cfg) (c : Chain) (a : AssetId) (e : Ev) : Prop :=
  e.RewritesHandler K a ∨ e = .enableInterop c ∨ e.IsSetAddresses

end Contracts.AssetRouter.HandlerGateAtV35
