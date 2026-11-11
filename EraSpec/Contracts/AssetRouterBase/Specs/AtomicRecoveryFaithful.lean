import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Model: the router-produced bundle call's target depends on its destination

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`contracts/` below is
`l1-contracts/contracts/`).  The upgrade tree `e561b9cc2` is cited only for the fix.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryFaithful` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryFaithful`.

## What `AtomicRecovery` merges

`AtomicRecovery.Config.router` is documented as "the target of every router-produced bundle
call", and `AtomicRecovery.routerCall` hard-codes that target.  The router chooses the target by
destination (`bridge/asset-router/L2AssetRouter.sol:333-341`, inside `initiateIndirectCall`):

    address destinationAssetRouter = _chainId == L1_CHAIN_ID ? address(L1_ASSET_ROUTER) : request.l2Contract;
    interopCallStarter = InteropCallStarter({
        to: InteroperableAddress.formatEvmV1(destinationAssetRouter),
        data: request.l2Calldata, callAttributes: attributes });

Here `request.l2Contract = _l2AssetRouterAddress(_chainId) = L2_ASSET_ROUTER_ADDR`
(`AssetRouterBase.sol:363-366, 374-376`).  `L1_ASSET_ROUTER` and `L1_CHAIN_ID` are storage slots
(`L2AssetRouter.sol:44, 54`) that `updateL2` writes (`:186-188`, with `L1_ASSET_ROUTER` required
nonzero).  The data is the same `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)` on
both branches (`AssetRouterBase.sol:361, 378-384`).  The center copies the returned address into
the bundle call's `to`, and sets `from` to the starter's recipient and `value` to the starter's
`interopCallValue` (`interop/InteropCenter.sol:732-740`).  So an L2→L1 router-produced call targets
the L1 router's address on L1, not `L2_ASSET_ROUTER_ADDR`.  The `L2AssetRouter.sol:233-234` that
`Config.router`'s docstring cites for "the same address on every chain" is a comment in
`_isValidInteropSender` about ZK chains only.

## An atomic L2→L1 leg is admitted at the pin

`sendBundle` (`InteropCenter.sol:262-327`) checks the destination in two places:

* `_ensureValidDestination` (`:378-385`): `L1_CHAIN_ID != block.chainid`,
  `_destinationChainId != block.chainid`, and an L1 destination has exactly one call;
* `_sendBundle`'s loop (`:520-538`), for an L1 destination: the call is indirect, its starter's
  recipient is `L2_ASSET_ROUTER_ADDR`, and its `interopCallValue` is zero.

Nothing at the pin compares atomicity with the destination.  `parseAttributes` (`:843-854`)
accepts the `atomicBundle` attribute once, like any bundle attribute.  `_parseAtomicSend`
(`:874-883`) sets `isAtomic` from it.  `_dispatchBundle` (`:639-659`) sends an atomic bundle
through `_validateAtomicBundle` (`:670-677`, values only) and `IAtomicFlowManager.append`
(`:650-655`), and publishes only a non-atomic bundle to L1 (`_sendBundleToL1`, `:657`).

L1 never executes such a leg.  `executeAtomicBundle` exists only in
`interop/interop-handler/L2InteropHandler.sol:49`.  `L1InteropHandler` executes only bundles proven
as L2→L1 messages from the interop center (`InteropHandlerBase.sol:86-123, 296-316`;
`L1InteropHandler.sol:68-77`), and unbundles only verified ones (`InteropHandlerBase.sol:195`).
An atomic bundle is never sent as such a message.  That step rests on message-inclusion
soundness (`PROTO-EVIDENCE`) and is argued from source, not modelled.

The upgrade rejects the combination at the top of `_sendBundle` (upgrade
`interop/InteropCenter.sol:550-554`):

    if (_atomicSend.isAtomic) { require(_destinationChainId != L1_CHAIN_ID, AtomicBundleToL1NotSupported()); }
    else { require(_destinationChainId == L1_CHAIN_ID, NonAtomicSendUnsupported()); }

The upgrade's `_recoverBundle` also rejects an L1-destined bundle (upgrade
`atomic-interop/AtomicFlowManager.sol:295`).

## Its refund does not reach the router

`_recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) calls
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` with no `try/catch`.  For an
L2→L1 leg, `c.to` is the L1 router's address, so the call goes to that address on L2.  The vault's
refund is `onlyAssetRouter` (`bridge/ntv/NativeTokenVaultBase.sol:106-109, 217`), so no code at
that address can run it.

Whether that address has code on L2 is an environment fact (`VM-CALL`), stated here as a premise
(`CodelessAt`).  Without code there the call reverts.  Solidity 0.8.28 skips the `extcodesize`
check for a call that returns data, and decoding the `bool` from empty return data reverts.  On
EraVM a codeless address runs the default account, whose fallback returns no data to a
non-bootloader caller (`system-contracts/contracts/DefaultAccount.sol:266-271`), and the decoding
reverts the same way.  The results that need no such premise state the refund as exactly what the
code at that address does (`L1LegRefundBypassesRouter`, `L1LegClaimOnlyByForeignCode`).

## What is modelled, and what is not

* `FConfig` is `AtomicRecovery.Config` plus the router's `L1_CHAIN_ID` and `L1_ASSET_ROUTER`.
  `base.router` is `L2_ASSET_ROUTER_ADDR`, which is both the router's own address on this chain and
  the target of every call to another L2.  The recovery side is `AtomicRecovery`'s, unchanged
  (`recoverCall`, `recoverBundle`, `claimRefund`).
* `routerCallTo` is the call the router produces for a destination.  For a destination other than
  `l1Chain` it is `AtomicRecovery.routerCall` exactly.  For `l1Chain` it differs from
  `AtomicRecovery.routerCall` in its target alone.
* The send-side model (`PinSendChecks`, `pinSend`) keeps the checks of `sendBundle` that restrict
  an L1 destination (`_ensureValidDestination` and the loop checks, as listed above) and the one
  check that only an atomic send runs (`_validateAtomicBundle`).  The other checks are left out,
  and none of them reads the atomic flag.  So each treats an atomic send like the same send without
  the `atomicBundle` attribute.  They are: pause and reentrancy, ERC-7930 parsing, attribute
  parsing, the salt, the destination base token (`:491-497`, which rejects only an unregistered
  destination other than L1), the router's own `initiateIndirectCall` and burn, fees and
  `msg.value` (`:548-567`, where an L1 destination is fee-free on both paths).  The one exception is
  the manager's `append`, which runs only for an atomic send.  It needs an `Unset` leg and an
  accepted commitment-tree insertion (`AtomicFlowManager.sol:87-102`).  The salt makes the bundle
  hash fresh (`:479-483, 507`), and the sender supplies the low-nullifier index.  So the admission
  results say that the L1-destination and atomicity checks accept the send, and that the omitted
  checks cannot tell it from the canonical L2→L1 withdrawal.  They do not say that every send
  succeeds.
* `UpgradeAtomicityGuard` is only the upgrade's new check.  The rest of the upgrade's send path is
  not modelled.
* `msg.value`, events, the asset tracker's L1 accounting, and the flow-level proofs that move a
  leg to `Revertable` are not modelled.  The stranding results hold for every leg state.
-/

namespace Contracts.AssetRouter.AtomicRecoveryFaithful

open Contracts.AssetRouter.AtomicRecovery

/-! ## Configuration -/

/-- The source chain's fixed addresses, as `AtomicRecovery.Config`, plus the two
`L2AssetRouter` storage slots `initiateIndirectCall` reads to choose a call's target. -/
structure FConfig where
  /-- `block.chainid`, `L2_ASSET_ROUTER_ADDR`, the vault, the manager and the metadata decoder,
  as in `AtomicRecovery`.  `base.router` is the router's own address on this chain and
  `_l2AssetRouterAddress(dest)` for every destination (`AssetRouterBase.sol:374-376`), so it is the
  target of every router-produced call to another L2.  It is not the target of a call to L1. -/
  base : Config
  /-- `L2AssetRouter.L1_CHAIN_ID` (`L2AssetRouter.sol:44`, written by `updateL2`, `:187`). -/
  l1Chain : Chain
  /-- `address(L2AssetRouter.L1_ASSET_ROUTER)` (`L2AssetRouter.sol:54`, written by `updateL2`,
  `:188`, nonzero by `:186`): the L1 router's address on L1. -/
  l1Router : Address

/-! ## The router-produced call -/

/-- `initiateIndirectCall`'s choice of target (`L2AssetRouter.sol:336`):
`_chainId == L1_CHAIN_ID ? address(L1_ASSET_ROUTER) : request.l2Contract`, where
`request.l2Contract` is `L2_ASSET_ROUTER_ADDR` (`AssetRouterBase.sol:365, 374-376`). -/
def destinationRouter (cfg : FConfig) (dest : Chain) : Address :=
  if dest = cfg.l1Chain then cfg.l1Router else cfg.base.router

/-- The bundle call a router-routed indirect starter to `dest` produces (`InteropCenter.sol:714-740`,
`L2AssetRouter.sol:318-341`).  `target` is `destinationRouter cfg dest`.  `from` is the router, the
starter's recipient, which must be `L2_ASSET_ROUTER_ADDR` for an L1 destination (`:530-533`).
`value` is zero, which `_validateAtomicBundle` requires anyway and which `:534-537` requires for L1.
`data` is `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)` on both branches. -/
def routerCallTo (cfg : FConfig) (dest : Chain) (assetId : AssetId) (md : MintData) : Call :=
  ⟨destinationRouter cfg dest, cfg.base.router, 0,
    .finalizeDeposit cfg.base.thisChain assetId (some md)⟩

/-! ## The environment premise -/

/-- **No code at `addr`** on this chain (`VM-CALL`), as the manager's refund loop sees it: every
`recoverAtomicCall(destChainId, data)` call to `addr` reverts, in every world.  Solidity 0.8.28
skips the `extcodesize` check for a call with return data, so the decoding of the `bool` return
from empty return data reverts.  On EraVM a codeless address runs the default account, which
returns no data to a non-bootloader caller.  The premise concerns this one address only. -/
def CodelessAt {X : Type} (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (addr : Address) : Prop :=
  ∀ w dest d, other addr w dest d = none

/-! ## The send side at the pin -/

/-- One call starter of `sendBundle` after attribute parsing (`InteropCallStarterInternal`,
`InteropCenter.sol:284-303`), with the fields the destination checks read. -/
structure Starter where
  /-- The parsed recipient (`InteropCallStarterInternal.to`). -/
  recipient : Address
  /-- `callAttributes.indirectCall`. -/
  indirect : Bool
  /-- `callAttributes.interopCallValue`, which becomes the formed call's `value` (`:738, :747`). -/
  callValue : UInt256

/-- The interop center's chain parameters. -/
structure CenterEnv where
  /-- `block.chainid`. -/
  thisChain : Chain
  /-- `InteropCenter.L1_CHAIN_ID` (`InteropCenter.sol:90`, written by `initL2`, `:199`).  It is a
  different storage slot from the router's `L1_CHAIN_ID`.  The results that join the two sides
  take their equality as a premise. -/
  l1Chain : Chain
  /-- `L2_ASSET_ROUTER_ADDR`. -/
  l2Router : Address

/-- The router-routed indirect starter of a deposit or withdrawal: recipient the L2 router,
indirect, zero `interopCallValue`. -/
def routerStarter (env : CenterEnv) : Starter := ⟨env.l2Router, true, 0⟩

/-- **The checks of `sendBundle` at the pin that restrict an L1 destination, and the atomic-only
check.**  `_ensureValidDestination` (`InteropCenter.sol:378-385`); for an L1 destination, the loop
checks `:520-538`; and, for an atomic send, `_validateAtomicBundle` (`:649, :670-677`) on the formed
calls' values, which are the starters' `interopCallValue`s (`:738, :747`).  No conjunct compares the
atomic flag with the destination. -/
def PinSendChecks (env : CenterEnv) (dest : Chain) (starters : List Starter) (isAtomic : Bool) :
    Prop :=
  env.l1Chain ≠ env.thisChain
  ∧ dest ≠ env.thisChain
  ∧ (dest = env.l1Chain → starters.length = 1)
  ∧ (dest = env.l1Chain →
      ∀ s ∈ starters, s.indirect = true ∧ s.recipient = env.l2Router ∧ s.callValue = 0)
  ∧ (isAtomic = true → ∀ s ∈ starters, s.callValue = 0)

instance (env : CenterEnv) (dest : Chain) (starters : List Starter) (isAtomic : Bool) :
    Decidable (PinSendChecks env dest starters isAtomic) := by
  unfold PinSendChecks
  infer_instance

/-- Where `_dispatchBundle` sends a bundle (`InteropCenter.sol:646-658`). -/
inductive Dispatch where
  /-- `IAtomicFlowManager.append` (`:650-655`): the leg is committed in the manager and nothing
  is sent to L1. -/
  | appendToFlow
  /-- `_sendBundleToL1` (`:657`): the bundle is published as an L2→L1 message. -/
  | publishToL1
  deriving DecidableEq

/-- `_dispatchBundle`'s branch on `_atomicSend.isAtomic` (`:646`). -/
def dispatchOf : Bool → Dispatch
  | true => .appendToFlow
  | false => .publishToL1

/-- `sendBundle` at the pin, as far as `PinSendChecks` and `_dispatchBundle`'s branch: `none` is a
revert, `some d` a dispatch to `d`.  The omitted checks are listed in the header. -/
def pinSend (env : CenterEnv) (dest : Chain) (starters : List Starter) (isAtomic : Bool) :
    Option Dispatch :=
  if PinSendChecks env dest starters isAtomic then some (dispatchOf isAtomic) else none

/-- **The upgrade's added check** (upgrade `interop/InteropCenter.sol:550-554`): an atomic send
must not go to L1 (`AtomicBundleToL1NotSupported`), and a non-atomic send must go to L1
(`NonAtomicSendUnsupported`). -/
def UpgradeAtomicityGuard (env : CenterEnv) (dest : Chain) (isAtomic : Bool) : Prop :=
  (isAtomic = true → dest ≠ env.l1Chain) ∧ (isAtomic = false → dest = env.l1Chain)

end Contracts.AssetRouter.AtomicRecoveryFaithful
