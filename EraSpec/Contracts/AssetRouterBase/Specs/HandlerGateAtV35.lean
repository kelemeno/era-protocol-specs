import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistrationRuns

/-!
# Model: the L1 asset router at draft/v0.35.0 — the asset-handler gate

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`.  Paths
are relative to `l1-contracts/contracts/`; `bridge/asset-router/` is shortened to `AR/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.HandlerGateAtV35` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.HandlerGateAtV35`.  It does not change the pin
models; it reuses `AllWriters`' configuration, operations and step relation.

## What v35 adds to the L1 router

One internal check, absent at the pin and on `main`:

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
| `bridgehubDepositBaseToken` (`AR/L1AssetRouter.sol:190-198`) | `:196` | `_bridgehubDepositBaseToken`: handler `≠ 0` (`AR/AssetRouterBase.sol:104`), `bridgeBurn` (`:107-113`) |
| `bridgehubDeposit`, `NEW_ENCODING_VERSION` (`AR/L1AssetRouter.sol:201-241`) | `:228-232` | `_bridgehubDeposit` → `_burn` (`AR/AssetRouterBase.sol:118-138, 303-331`) |
| `finalizeDeposit` (`AR/L1AssetRouter.sol:291-299`, `onlySelf`) | `:296` | `_finalizeDeposit` (`AR/AssetRouterBase.sol:267-283`) |
| `bridgeConfirmTransferResult` (`AR/L1AssetRouter.sol:306-325`, `onlyNullifier`) | `:313` | the handler's `bridgeConfirmTransferResult` (`:314-320`) |

Not gated: `setAssetHandlerAddressThisChain` (`AR/L1AssetRouter.sol:145-150`),
`setAssetDeploymentTracker` (`:135-142`), `setNativeTokenVault` (`:116-121`), and the
`SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION` branch of `bridgehubDeposit` (`:216-226`),
which only builds an L2 message (`_setAssetHandlerAddressOnCounterpart` is `view`,
`:158-183`).  Every other encoding version reverts in `_bridgehubDeposit`
(`UnsupportedEncodingVersion`, `AR/AssetRouterBase.sol:126-137`), so no legacy deposit path
skips the gate.  A grep of `assetHandlerAddress` over the v35 tree finds no other L1 read
that moves an asset (the remaining reader, `core/bridgehub/BridgehubBase.sol:316`, is a
`view` lookup of a base token's address).

## What the gate reads

* `BRIDGE_HUB.chainAssetHandler()` (`core/bridgehub/BridgehubBase.sol:124`), written only by
  `L1Bridgehub.setAddresses` (`core/bridgehub/L1Bridgehub.sol:268-280`, `onlyOwnerOrUpgrader`).
* `isInteropEnabled(c)` of the current `BRIDGE_HUB.messageRoot()`
  (`core/message-root/L1MessageRoot.sol:92-94`).  Its flag is written only by `enableInterop`
  (`:72-89`): the Bridgehub owner only (`:73`), the chain must be registered (`:74-75`), not
  yet enabled (`:76`), with no pending `chainBalanceBackfill` (`:77-80`); it is set to `true`
  (`:87`) and nothing ever clears it.  `setAddresses` can also replace the message root
  itself (`L1Bridgehub.sol:277`), so the model lets it replace the whole flag table.

`Env` holds these two; `enableInterop` and `setAddresses` are the only events that change it.

## The step relation

`StepV35` is `AllWriters.AStep` on the L1 side, with three changes:

* the fallback `finalize` carries its source chain and runs the gate first.  The gate always
  passes there: the fallback is taken only when the handler is unset.
* the four gated entry points are events (`Ev.gated`) that move an asset through the
  registered handler and write neither router map.  They need a nonzero handler (the
  deposit's on-the-fly vault registration, `AR/AssetRouterBase.sol:313-321`, is the vault's
  own `register` step, logged before the deposit; after it the handler is the vault, which the
  gate exempts, just as the gate exempts the unset handler it saw).
* `enableInterop` and `setAddresses` change the environment and nothing else; the counterpart
  message branch changes nothing on L1 (what it may send is `CounterpartGateAtV35`'s topic).

The handlers' own calls (`bridgeBurn`, `bridgeMint`, `bridgeConfirmTransferResult`) are
over-approximated as succeeding: a gated event is enabled exactly when the router's own checks
pass.  So the model has at least the runs of the code, which is what the safety results need,
and its liveness results are statements about the router's checks.

## Writers at v35

A grep of `_setAssetHandler(` and `assetDeploymentTracker[` over the whole v35 tree finds the
pin's writers at new lines and nothing else (no contract inherits either router):
`AR/AssetRouterBase.sol:74, 75` (`register`), `:278` (`finalize`), `AR/L1AssetRouter.sol:120`
(`seed`), `:140` (`setTracker`), `AR/L2AssetRouter.sol:162` (L2 `seed`), `:203` (L2
`counterpartSet`).  `AllWriters`' operations are therefore still complete at v35.

## Boundaries

* Router, Bridgehub and message-root upgrades are out of scope (`OPS-CONFIG`).
* `msg.value`, pause, `nonReentrant`, events, and the handlers' internal state (for instance
  the L1 vault's per-chain balance cap, `bridge/ntv/L1NativeTokenVault.sol:439-459`, which only
  shrinks `Cfg.ntvMints`) are not modelled.
* `enableInterop`'s guards other than `!interopEnabled[c]` are abstracted.
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

/-- **A gated movement of asset `a` to or from chain `c` is stranded in `S`**: its handler is
custom and `c` is not interop-enabled, so the gate reverts it. -/
def Stranded (K : Cfg) (S : St) (c : Chain) (a : AssetId) : Prop :=
  Custom K S.env (S.router.handler a) ∧ S.env.ie c = false

/-! ## Events -/

/-- The gated entry points that move an asset through its registered handler and write
neither router map. -/
inductive Gated where
  /-- `bridgehubDeposit` with `NEW_ENCODING_VERSION` (`AR/L1AssetRouter.sol:228-240`); the
  handler's `bridgeBurn` (`AR/AssetRouterBase.sol:324-330`). -/
  | deposit
  /-- `bridgehubDepositBaseToken` (`AR/L1AssetRouter.sol:190-198`); the handler's
  `bridgeBurn` (`AR/AssetRouterBase.sol:107-113`). -/
  | depositBase
  /-- `finalizeDeposit` (`AR/L1AssetRouter.sol:291-299`) on a registered handler; its
  `bridgeMint` (`AR/AssetRouterBase.sol:275-276`).  An L2 → L1 withdrawal. -/
  | finalizeLive
  /-- `bridgeConfirmTransferResult` (`AR/L1AssetRouter.sol:306-325`); the handler's
  `bridgeConfirmTransferResult` (`:314-320`).  A failed-deposit refund or a deposit
  confirmation. -/
  | confirm
  deriving DecidableEq

/-- One successful call on the L1 side at v35. -/
inductive Ev where
  /-- `setAssetHandlerAddressThisChain(d, h)` by `caller` (`AR/L1AssetRouter.sol:145-150`,
  `AR/AssetRouterBase.sol:65-77`).  Not gated. -/
  | register (caller : Address) (d : AssetData) (h : Address)
  /-- `setNativeTokenVault` (`AR/L1AssetRouter.sol:116-121`, write `:120`). -/
  | seed
  /-- `setAssetDeploymentTracker(d, t)` (`AR/L1AssetRouter.sol:135-142`, write `:140`). -/
  | setTracker (d : AssetData) (t : Address)
  /-- `finalizeDeposit(c, a, _)` taking `_finalizeDeposit`'s fallback
  (`AR/AssetRouterBase.sol:277-282`, write `:278`). -/
  | finalize (c : Chain) (a : AssetId)
  /-- A gated entry point at chain `c` and asset `a`, moving the asset through its handler. -/
  | gated (g : Gated) (c : Chain) (a : AssetId)
  /-- `bridgehubDeposit` with `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION`
  (`AR/L1AssetRouter.sol:216-226`): builds the L2 `setAssetHandlerAddress(.., a, h)` for chain
  `c`; writes nothing on L1. -/
  | counterpartMsg (c : Chain) (a : AssetId) (h : Address)
  /-- `L1MessageRoot.enableInterop(c)` (`core/message-root/L1MessageRoot.sol:72-89`). -/
  | enableInterop (c : Chain)
  /-- `L1Bridgehub.setAddresses` (`core/bridgehub/L1Bridgehub.sol:268-280`): a new chain asset
  handler and a new message root, hence a new interop table. -/
  | setAddresses (cah : Address) (ie : Chain → Bool)

/-- **One successful call at v35.**  A revert is the absence of a step. -/
inductive StepV35 (K : Cfg) : Ev → St → St → Prop
  /-- The ungated registration, exactly `AllWriters`' (`AR/AssetRouterBase.sol:73-75`). -/
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

/-! ## Projections onto the pin models -/

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

/-- The registration a v35 event is, if any, as a `HandlerRegistrationRuns` call. -/
def Ev.call : Ev → Option Call
  | .register caller d h => some ⟨caller, d, h⟩
  | _ => none

/-- The registrations of a v35 log, oldest first. -/
def calls (evs : List Ev) : List Call := evs.filterMap Ev.call

/-- An event that writes the router's maps only by registering, or not at all. -/
def Ev.RegisterOrSilent (e : Ev) : Prop :=
  ∀ op, e.op = some op → ∃ caller d h, op = .register caller d h

/-- The (chain, asset) a gated event checks: `finalizeDeposit`'s source chain, a deposit's
destination, a confirmation's chain. -/
def Ev.gatedAt : Ev → Option (Chain × AssetId)
  | .finalize c a => some (c, a)
  | .gated _ c a => some (c, a)
  | _ => none

/-- The owner's `setAddresses`. -/
def Ev.IsSetAddresses : Ev → Prop
  | .setAddresses _ _ => True
  | _ => False

/-! ## `bridgehubDeposit`'s dispatch -/

/-- What `bridgehubDeposit` decodes from `_data` (`AR/L1AssetRouter.sol:215-232`). -/
inductive DepositData where
  /-- First byte `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION`: `(assetId, handler)`
  (`:216-219`). -/
  | counterpart (a : AssetId) (h : Address)
  /-- First byte `NEW_ENCODING_VERSION`: the asset id (`:228-230`). -/
  | newEncoding (a : AssetId)
  /-- Any other first byte. -/
  | other

/-- The event a `bridgehubDeposit(c, _, _, data)` call is, or `none` when it reverts: any
other encoding version reaches `_bridgehubDeposit`, which reverts with
`UnsupportedEncodingVersion` (`AR/AssetRouterBase.sol:126-137`). -/
def bridgehubDepositEv (c : Chain) : DepositData → Option Ev
  | .counterpart a h => some (.counterpartMsg c a h)
  | .newEncoding a => some (.gated .deposit c a)
  | .other => none

end Contracts.AssetRouter.HandlerGateAtV35
