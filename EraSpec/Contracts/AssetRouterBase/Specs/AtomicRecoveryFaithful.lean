import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Model: the router-produced bundle call's target depends on its destination

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`contracts/` below is
`l1-contracts/contracts/`).  One check is read from another tree, `e561b9cc2`, the snapshot of
`feat/upgrade-simplification` that this repository's upgrade models pin.  That tree is not a
successor of the pin: the two diverge at `76f40b530`, with 20 commits only on the pin's side and
752 only on the other's.  It is "the other tree" below, and it is cited only for that check
and the matching check in its `_recoverBundle`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryFaithful` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryFaithful`.

## What `AtomicRecovery` merges

Before this topic, `AtomicRecovery.Config.router` was documented as "the target of every
router-produced bundle call".  `AtomicRecovery.routerCall` still hard-codes that target.  The
router chooses the target by destination (`bridge/asset-router/L2AssetRouter.sol:333-341`, inside
`initiateIndirectCall`):

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
the L1 router's address on L1, not `L2_ASSET_ROUTER_ADDR`.  The old docstring cited
`L2AssetRouter.sol:233-234` for "the same address on every chain".  That is a comment on
`_isValidInteropSender` about ZKsync chains only.  The docstring now gives the target by
destination.

`AtomicRecovery.routerCall` is unchanged, and so are the two topics built on it,
`AssetRouterBase/PausedRecovery` and `Protocol/AssetBridgePreparation/FullRecovery`.  Their
statements are about calls that target the router.  A router-produced call to L1 is not one.

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
An atomic bundle is never sent as such a message: the only `sendToL1` of a bundle is on the
non-atomic branch (`InteropCenter.sol:626, 657`).  This chain's half of that is already proved in
the center's model, as `Contracts.InteropCenter.History.Properties.AtomicBytesNeverPublished`: along a run
whose encoder separates its bundles (`EncInjOn`), the bytes of an atomic dispatch differ from the
bytes of every public dispatch, unless the two dispatches are a cross-sender salt clash
(`CrossSenderSaltClash`).  No result of this topic uses it.  What stays argued from source is the
L1 side: that L1 executes nothing but included messages rests on message-inclusion soundness
(`PROTO-EVIDENCE`), and bundles published by other chains are outside the center's one-chain
model.

The other tree rejects the combination at the top of `_sendBundle` (other tree,
`interop/InteropCenter.sol:550-554`):

    if (_atomicSend.isAtomic) { require(_destinationChainId != L1_CHAIN_ID, AtomicBundleToL1NotSupported()); }
    else { require(_destinationChainId == L1_CHAIN_ID, NonAtomicSendUnsupported()); }

Its `_recoverBundle` also rejects an L1-destined bundle (other tree,
`atomic-interop/AtomicFlowManager.sol:295`).

## Its refund does not reach the router

`_recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) calls
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` with no `try/catch`.  For an
L2→L1 leg, `c.to` is the L1 router's address, so the call goes to that address on L2.  The vault's
refund is `onlyAssetRouter` (`bridge/ntv/NativeTokenVaultBase.sol:107-110, 217`), so no code at
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
* `formedCall` is the bundle call the center forms from one starter that is routed through this
  router (`_processCallStarter`, `InteropCenter.sol:709-740`).  For the router's own starter
  (`routerStarter`) it is `routerCallTo` exactly when the center's `L2_ASSET_ROUTER_ADDR` is the
  router's address.  Calls formed from a direct starter, or through another
  `IL2CrossChainSender`, are not modelled.  For an L1 destination the pin admits neither.
* The send-side model (`PinSendChecks`, `pinSend`) keeps the checks of `sendBundle` that restrict
  an L1 destination (`_ensureValidDestination` and the loop checks, as listed above), and
  `_validateAtomicBundle`, which only an atomic send runs.  The other checks are left out.  They
  are: pause and reentrancy (`:266`), ERC-7930 parsing (`:268-272, 285-288`), attribute parsing
  (`:294-308, 318`), the salt (`:479-483`), the destination base token (`:491-497`, which rejects
  only an unregistered destination other than L1), the router's own `initiateIndirectCall` and
  burn (`:714-716`), the center's parse of the returned call attributes (`:719-722`), its check
  that the router returned the starter's `interopCallValue` (`IndirectCallValueMismatch`,
  `:723-729`), its parse of the returned address (`:732`), fees and `msg.value` (`:548-567`, where an L1 destination is fee-free on both paths),
  and the manager's `append` (`:650-655`).
* Two of the omitted steps depend on atomicity.  Attribute parsing decodes the three fields of
  the `atomicBundle` attribute only when it is present (`:877-880`, `AttributesDecoder.sol:21-25`)
  and rejects a second one (`:844`).  A well-formed attribute passes.  `append` runs only for an
  atomic send (`:646-655`).  It needs an `Unset` leg and an accepted commitment-tree insertion
  (`AtomicFlowManager.sol:87-102`).  The salt makes the bundle hash fresh (`:479-483, 507`), and
  the sender supplies the low-nullifier index.  The other omitted checks do not read the atomic
  flag, which is set at `:252` and `:880` and read only at `:646`.
* So the admission results say only that the modelled checks accept the send.  That the omitted
  checks treat an atomic send to L1 like the canonical L2→L1 withdrawal, apart from the two steps
  above, is argued here from the source.  No Lean result states it, and none says that every
  send succeeds.
* `UpgradeAtomicityGuard` is only the check the other tree has.  The rest of that tree's send
  path is not modelled.
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

/-- The interop center's chain parameters.  The center and the router are separate contracts on
one chain, and the two sides are kept as separate records.  `Properties.RouterStarterFormsRouterCall`
and `Properties.AdmittedAtomicL1LegNeverRefunded` take the agreement they need as a premise. -/
structure CenterEnv where
  /-- `block.chainid`, as the center reads it (`InteropCenter.sol:380-381`).  No universally
  quantified result compares it with the router's `block.chainid` (`FConfig.base.thisChain`): the
  stranding of an L1 leg does not depend on the source chain id in the call's data.  The concrete
  instances have the two equal. -/
  thisChain : Chain
  /-- `InteropCenter.L1_CHAIN_ID` (`InteropCenter.sol:90`, written by `initL2`, `:199`).  It is a
  different storage slot from the router's `L1_CHAIN_ID`.  `Properties.AdmittedAtomicL1LegNeverRefunded`
  takes their equality as a premise. -/
  l1Chain : Chain
  /-- `L2_ASSET_ROUTER_ADDR`, as the center reads it (`InteropCenter.sol:531`).  At the source this
  is one compile-time constant (`common/l2-helpers/L2ContractAddresses.sol:94`), the address
  `FConfig.base.router` also stands for.  The model keeps the two fields apart, and the results
  that join the two sides take `l2Router = base.router` as a premise. -/
  l2Router : Address

/-- The router-routed indirect starter of a deposit or withdrawal: recipient the L2 router,
indirect, zero `interopCallValue`. -/
def routerStarter (env : CenterEnv) : Starter := ⟨env.l2Router, true, 0⟩

/-- **The bundle call the center forms from one starter routed through this router**
(`_processCallStarter`, indirect branch, `InteropCenter.sol:709-740`), given the `assetId` and the
`bridgeMintCalldata` of the burn that the router's `initiateIndirectCall` made for the starter
(`L2AssetRouter.sol:320-326`).  `to` is the address the router returned (`:732, :736`;
`L2AssetRouter.sol:336-338`), which is `destinationRouter cfg dest`.  `from` is the starter's
recipient (`:739`), the contract whose `initiateIndirectCall` the center called.  `value` is the
starter's `interopCallValue` (`:738`).  `data` is the returned
`finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)` (`:737`; `L2AssetRouter.sol:339`).

This is the formed call only for an indirect starter whose recipient is the router that `cfg`
describes.  A direct starter (`:741-750`) and an indirect starter through another
`IL2CrossChainSender` form other calls, which are not modelled.  For an L1 destination the pin
admits neither (`:529-533`; `Properties.PinL1SendIsRouterStarter`).  The statements apply
`formedCall` to `routerStarter` only.  The mint data is taken as decodable (`some md`), as in
`routerCall`. -/
def formedCall (cfg : FConfig) (dest : Chain) (s : Starter) (assetId : AssetId) (md : MintData) :
    Call :=
  ⟨destinationRouter cfg dest, s.recipient, s.callValue,
    .finalizeDeposit cfg.base.thisChain assetId (some md)⟩

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

/-- **The check the other tree has** (`e561b9cc2`, `interop/InteropCenter.sol:550-554`): an
atomic send must not go to L1 (`AtomicBundleToL1NotSupported`), and a non-atomic send must go to L1
(`NonAtomicSendUnsupported`).  "Upgrade" in the name is that tree's branch,
`feat/upgrade-simplification`.  The tree is not a successor of the pin (see the header). -/
def UpgradeAtomicityGuard (env : CenterEnv) (dest : Chain) (isAtomic : Bool) : Prop :=
  (isAtomic = true → dest ≠ env.l1Chain) ∧ (isAtomic = false → dest = env.l1Chain)

end Contracts.AssetRouter.AtomicRecoveryFaithful
