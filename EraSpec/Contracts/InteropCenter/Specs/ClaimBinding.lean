import EraSpec.Contracts.InteropCenter.Specs.Dispatch

/-!
# Model: the bytes `claimRefund` is given, and the calls `_recoverBundle` makes

Source: `l1-contracts/contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts
tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), with `interop/InteropDataEncoding.sol`,
`interop/InteropCenter.sol`, `atomic-interop/IAtomicFlowManager.sol` and
`atomic-interop/IAtomicRecoverable.sol` from the same tree. A bare `:N` is a line of
`AtomicFlowManager.sol`.

**This file is definitions only.** It adds no state and no step to
`EraSpec.Contracts.InteropCenter.Specs.Dispatch`: it names what one `claimRefund` transaction
computes from its arguments. The results are in
`EraSpec.Contracts.InteropCenter.Properties.ClaimBinding` and are proved in
`EraSpec.Contracts.InteropCenter.Proofs.ClaimBinding`.

## The code

    function claimRefund(bytes32 _flowId, bytes calldata _bundle) external {             // :165
        InteropBundle memory bundle = abi.decode(_bundle, (InteropBundle));              // :166
        bytes32 bundleHash =
            InteropDataEncoding.encodeInteropBundleHash(bundle.sourceChainId, _bundle);   // :167
        LegState s = _state[_flowId][bundleHash];                                         // :169
        if (s != LegState.Revertable)
            revert ManagerLegNotRevertable(_flowId, bundleHash, s);                       // :170
        _state[_flowId][bundleHash] = LegState.Reverted;                                  // :175
        _recoverBundle(_flowId, bundleHash, bundle);                                      // :177
        emit FlowRefunded(_flowId, bundleHash);                                           // :179
    }

    function _recoverBundle(bytes32 _flowId, bytes32 _bundleHash, InteropBundle memory _bundle)
        internal {                                                                        // :219
        uint256 destChainId = _bundle.destinationChainId;                                 // :220
        uint256 callsLen = _bundle.calls.length;                                          // :221
        uint256 recovered = 0;
        for (uint256 i = 0; i < callsLen; ++i) {
            InteropCall memory c = _bundle.calls[i];                                      // :224
            if (IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)) {        // :225
                ++recovered;
            }
        }
        if (recovered == 0) revert ManagerNoRecoverableCalls(_flowId, _bundleHash);       // :229
    }

`encodeInteropBundleHash(c, b)` is `keccak256(abi.encode(c, b))` (`InteropDataEncoding.sol:11-13`).
The center computed the leg's hash differently (`InteropCenter.sol:643-644`):

    bytes memory interopBundleBytes = abi.encode(_bundle);
    bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, interopBundleBytes);

The two computations differ twice. The manager takes the source chain from the DECODED bundle,
not from `block.chainid`; and it hashes the bytes AS GIVEN, not a re-encoding of the decoded
bundle. `claimRefund` is permissionless (`IAtomicFlowManager.sol:65-69`), so the bytes are the
caller's choice: all that ties them to a dispatch is that their hash must find a `Revertable` leg.

## The documented claims this topic makes precise

* `IAtomicFlowManager.sol:68`: `_bundle` is "The ABI-encoded {InteropBundle} of the source leg
  (hashes to the committed leg)".
* `IAtomicRecoverable.sol:15-16`: "`_callData` is the original `InteropCall.data`", and
  `_destChainId` is "The bundle's destination chain id (the chain the original call targeted)".
* `IAtomicFlowManager.sol:21-24`: the timeout path recovers "the burned source funds to the
  depositor by asking each of the bundle's call targets to reverse itself".

## Modelling choices

* **A claim is a `Step.claim`.** A successful `claimRefund(f, x)` from state `S` is the step
  `Step.claim f (claimRefundHash P dec x)` of the dispatch model: its guard is :169-170 and its
  write :175. The recovery calls are external, and `_recoverBundle` writes no manager storage;
  a call nested in them is a later step, as `Specs/Dispatch.lean` already models it.
* **`dec` is `abi.decode`, as any total function.** Where `abi.decode` reverts, `claimRefund` has
  no step (`VM-REVERT`), so the value of `dec` there is never used by the code; every result holds
  for every total `dec`. A result that needs the decoder to invert the encoder says so, on the
  run's own bundles only (`DecodesDispatchedBundles`, a `SOL-ABI` premise).
* **Which calls, not their outcomes.** `recoverBundleCalls` lists the external calls
  `_recoverBundle` makes. Whether each returns `true`, returns `false` or reverts is the subject of
  `AttackVectors.RecoveryLimits` and `Contracts.AssetRouter.AtomicRecovery`.
* **Collisions are pinned.** The only collision a conclusion allows is `ClaimHashCollision`: keccak
  equal on two named, different preimages, namely the bytes this claim hashed and the bytes the
  center hashed for a logged atomic dispatch of the same flow.
-/

namespace Contracts.InteropCenter

/-- The bundle hash `claimRefund(_flowId, x)` computes from the bytes `x` it is given (:166-167):
`keccak256(abi.encode(bundle.sourceChainId, x))` with `bundle = abi.decode(x)`. The leg the claim
reads (:169) and writes (:175) is `(_flowId, claimRefundHash P dec x)`. -/
def claimRefundHash (P : Params) (dec : List UInt8 → Bundle) (x : List UInt8) : Word :=
  P.keccak (claimPreimage dec x)

/-- One external call of `_recoverBundle`:
`IAtomicRecoverable(target).recoverAtomicCall(destChainId, data)` (:225). -/
structure ClaimRecoveryCall where
  /-- `c.to`: the contract asked, on this (the source) chain, to reverse the call. -/
  target : Address
  /-- `_bundle.destinationChainId` (:220), the same for every call of the bundle. -/
  destChainId : Word
  /-- `c.data`. -/
  data : List UInt8
deriving DecidableEq

/-- The external calls `_recoverBundle(_, _, b)` makes, in order (:220-228). It reads nothing else
of the bundle: not the calls' `from` or `value`, not the salts, not the attributes. -/
def recoverBundleCalls (b : Bundle) : List ClaimRecoveryCall :=
  b.calls.map fun c => ⟨c.target, b.destinationChainId, c.data⟩

/-- **THE `SOL-ABI` ROUND TRIP ON A RUN'S BUNDLES.** `abi.decode(abi.encode(b)) = b` for the bundle
`b` of every dispatch in the log. It is, by name, the decoder premise of
`ClaimedBundleValidatedOrCollision`. -/
def DecodesDispatchedBundles (P : Params) (dec : List UInt8 → Bundle) (log : List Dispatch) :
    Prop :=
  ∀ d ∈ log, dec (P.enc d.bundle) = d.bundle

/-- **THE CLAIMED BYTES ARE A DISPATCHED BUNDLE'S.** Some atomic dispatch of flow `f` in the log has
canonical bytes `abi.encode(bundle)` equal to `x`, and `x` decodes to that dispatch's bundle. These
are the bytes the center hashed (`InteropCenter.sol:643`), for the bundle it emitted
(`InteropCenter.sol:585`). -/
def ClaimRecoversDispatch (P : Params) (dec : List UInt8 → Bundle) (log : List Dispatch)
    (f : Word) (x : List UInt8) : Prop :=
  ∃ d ∈ log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧ x = P.enc d.bundle ∧ dec x = d.bundle

/-- **A PINNED CLAIM COLLISION.** keccak collides on exactly two named, different preimages: the
bytes `claimRefund(f, x)` hashed (:167), and the bytes the center hashed (`InteropCenter.sol:644`)
for an atomic dispatch of flow `f` in the log. That dispatch committed the leg the claim reads, and
it is the only logged atomic dispatch that did (`EachLegAppendedOnce`). -/
def ClaimHashCollision (P : Params) (dec : List UInt8 → Bundle) (log : List Dispatch) (f : Word)
    (x : List UInt8) : Prop :=
  ∃ d ∈ log, d.isAtomic = true ∧ d.atomicSend.flowId = f ∧
    claimPreimage dec x ≠ bundlePreimage P d.bundle ∧
    claimRefundHash P dec x = bundleHash P d.bundle

end Contracts.InteropCenter
