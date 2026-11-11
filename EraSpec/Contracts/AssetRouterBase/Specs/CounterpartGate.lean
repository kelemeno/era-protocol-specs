import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Model: the L1 side of the counterpart path

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), paths
relative to `l1-contracts/contracts/`, with `bridge/asset-router/` shortened to `AR/` and
`bridge/ntv/` to `NTV/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.CounterpartGate` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.CounterpartGate`.

## Why

`AllWriters` treats `L2AssetRouter.setAssetHandlerAddress` as a trusted exception: on L2
its only check is that the caller is the aliased L1 asset router
(`AR/L2AssetRouter.sol:91-102, 200-206`).  This file models what the L1 router checks
before it sends that call, which narrows the exception.

## The L1 side

The L1 router builds that L2 call in exactly one place, `_setAssetHandlerAddressOnCounterpart`
(`AR/L1AssetRouter.sol:182-206`).  It is reached from `bridgehubDeposit` when the data's
first byte is `SET_ASSET_HANDLER_COUNTERPART_ENCODING_VERSION` (:236-248).  Every other
L2 call the L1 router builds is a `finalizeDeposit`:

    IL1AssetDeploymentTracker(assetDeploymentTracker[_assetId]).bridgeCheckCounterpartAddress(
        _chainId, _assetId, _originalCaller, _assetHandlerAddressOnCounterpart);     // :188-193
    bytes memory l2Calldata = abi.encodeCall(IL2AssetRouter.setAssetHandlerAddress,
        (block.chainid, _assetId, _assetHandlerAddressOnCounterpart));                // :195-198

So the id's tracker *in the L1 router's state* decides, and the L1 router's state is an
`AllWriters` run on the L1 side.  The trackers at the pin:

* `L1NativeTokenVault.bridgeCheckCounterpartAddress` (`NTV/L1NativeTokenVault.sol:146-153`)
  lets through only `L2_NATIVE_TOKEN_VAULT_ADDR`.
* `CTMDeploymentTracker.bridgeCheckCounterpartAddress`
  (`core/ctm-deployment/CTMDeploymentTracker.sol:140-149`) lets through only
  `L2_CHAIN_ASSET_HANDLER_ADDR`, and only for its owner.
* Any other tracker is whatever the owner recorded with `setAssetDeploymentTracker`.
* A zero tracker reverts.  `IL1AssetDeploymentTracker` declares the function with no
  return values (`bridge/interfaces/IL1AssetDeploymentTracker.sol:8-13`), so Solidity
  checks that the target has code (`SOL-CONTROL`, `VM-CALL`).

`Approvals` abstracts the trackers' code: `approves t a h` says the call to tracker `t`,
for id `a` and handler `h`, returns.  `VaultApprovals` is what the narrowing needs of it.

## Boundaries

* **Message authenticity** (`PROTO-EVIDENCE`): an L2 `setAssetHandlerAddress` executes
  only as an L1 → L2 transaction sent by the L1 router, after the L1 router sent it from a
  state its own run reached.  The composition result takes, for each counterpart write
  in the L2 log, such an L1 run as a premise.
* The L1 state is read when the message is sent.  The message may execute on L2 later;
  the L2 router applies it as is.
* No code at `L2_NATIVE_TOKEN_VAULT_ADDR` (`0x10004`) on L1 is assumed in
  `VaultApprovals.vaultAddr`.  On L1, that address can be a tracker only if the owner
  records it.  A registration by the L1 vault hashes as that address
  (`senderOf`, `AR/AssetRouterBase.sol:78-80`), so the two share an id space.
-/

namespace Contracts.AssetRouter.AllWriters

/-- The trackers' code, as far as `bridgeCheckCounterpartAddress` goes: `approves t a h`
says the call to tracker `t`, for id `a` and handler `h`, returns without reverting. -/
abbrev Approvals := Address → AssetId → Address → Prop

/-- The L1 router, in state `R1`, can send `setAssetHandlerAddress(block.chainid, a, h)`
to L2: the id's L1 tracker lets `h` through (`AR/L1AssetRouter.sol:188-193`). -/
def L1Emits (approves : Approvals) (R1 : Router) (a : AssetId) (h : Address) : Prop :=
  approves (R1.tracker a) a h

/-- What the narrowing needs of the trackers' code. -/
structure VaultApprovals (K1 : Cfg) (approves : Approvals) : Prop where
  /-- A zero tracker has no code, so the call reverts. -/
  zero : ∀ a h, ¬ approves 0 a h
  /-- The L1 vault lets through only `L2_NATIVE_TOKEN_VAULT_ADDR`
  (`NTV/L1NativeTokenVault.sol:146-153`). -/
  vault : ∀ a h, approves K1.ntv a h → h = K1.ntvAddr
  /-- Whatever sits at `L2_NATIVE_TOKEN_VAULT_ADDR` on L1 lets nothing else through.  (No
  contract is expected there on L1, in which case the call reverts.) -/
  vaultAddr : ∀ a h, approves K1.ntvAddr a h → h = K1.ntvAddr

/-- The route of the id of triple `q` is accountable: it is unset, or it has a nonzero
tracker, or it points at the vault. -/
def TripleAccountable (K : Cfg) (R : Router) (q : Chain × Address × AssetData) : Prop :=
  R.handler (K.enc q.1 q.2.1 q.2.2) ≠ 0 →
    R.tracker (K.enc q.1 q.2.1 q.2.2) ≠ 0 ∨ R.handler (K.enc q.1 q.2.1 q.2.2) = K.ntv

end Contracts.AssetRouter.AllWriters
