import Mathlib.Tactic
import EraSpec.Core.Word
import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtV35

/-!
# Contract spec: the flow preimage and `_validateAndComputeFlowId` (`FlowCanonicalAtHead`)

Source: matter-labs/era-contracts `draft/v0.35.0` at `b17415d20`. Paths are relative to
`l1-contracts/contracts/atomic-interop/`. The topic was first written against `main` `3605e82`,
where the two functions below are the same text at other lines.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonicalAtHead`, proofs in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtHead`.

**One model.** The contract's canonical transcription of this code is `Contracts.FlowCanonicalAtV35`
(`Specs/FlowCanonicalAtV35.lean`). The types here are a field-by-field copy of its types, kept
because `Protocol/InteropAtomicity` topic `FlowBindingAtHead` is built on them; `FlowPreimage.toV35`
and `PreimageV35.toHead` are inverse bijections, and under them `validateAndComputeFlowId`,
`CheckFlowId` and `PreimageAccepted` are `validateV35`, `CheckFlowIdV35` and `AcceptedV35`
(`Properties.ToV35Bijective`, `Properties.ValidateAgreesWithV35`, `Properties.CheckFlowIdAgreesWithV35`,
`Properties.AcceptedIffAcceptedV35`).

## The code at `b17415d20`

    // IAtomicInterop.sol:50-56
    struct AtomicFlowPreimage {
        bytes1 version;
        uint64 deadline;
        uint256 settlementLayerChainId;
        bytes32[] legBundleHashes;
        uint256[] legSourceChainIds;
    }
    // IAtomicInterop.sol:64-67
    struct AtomicFlow { bytes32 flowId; AtomicFlowPreimage preimage; }
    // IAtomicInterop.sol:91
    bytes1 constant ATOMIC_FLOW_PREIMAGE_VERSION = 0x01;
    // IAtomicInterop.sol:99
    uint256 constant MAX_ATOMIC_FLOW_LEGS = 8;

    // AtomicFlowManager.sol:360-379
    function _validateAndComputeFlowId(AtomicFlowPreimage calldata _preimage) internal pure returns (bytes32) {
        if (_preimage.version != ATOMIC_FLOW_PREIMAGE_VERSION) revert ManagerFlowPreimageVersionMismatch(..); // :361-363
        uint256 n = _preimage.legBundleHashes.length;                                                     // :364
        if (n > MAX_ATOMIC_FLOW_LEGS) revert ManagerTooManyLegs(MAX_ATOMIC_FLOW_LEGS, n);                   // :367-369
        for (uint256 i = 1; i < n; ++i) {
            if (_preimage.legBundleHashes[i] <= _preimage.legBundleHashes[i - 1]) revert ManagerBundleHashesNotSorted();
        }                                                                                                 // :370-374
        if (_preimage.legSourceChainIds.length != n) revert ManagerLegSourceChainIdsLengthMismatch(..);     // :375-377
        return keccak256(abi.encode(_preimage));                                                          // :378
    }
    // AtomicFlowManager.sol:348-353
    function _checkFlowId(AtomicFlow calldata _flow) internal pure {
        bytes32 computed = _validateAndComputeFlowId(_flow.preimage);
        if (computed != _flow.flowId) revert ManagerFlowIdMismatch(_flow.flowId, computed);
    }

The function has three callers: `append` computes the flow id from the sender's preimage
(`AtomicFlowManager.sol:109`), and `requireFlowFinalized` (`:182`) and `authorizeRefund`
(`:217`) check a presented flow through `_checkFlowId`. Its NatSpec says it is "shared by
the send path (`append`) and `_checkFlowId`, so canonicalization cannot drift" (`:359`).
The version constant's NatSpec (`IAtomicInterop.sol:84-90`) says each version is validated
under its own rules and "today the only accepted one" is `0x01`. The cap's NatSpec
(`IAtomicInterop.sol:93-98`) says an oversized flow "is rejected identically on the
append, finalize and refund paths and can never commit a leg".

At the older pin `c67894b9` only the sort check and the length check ran (in `_checkFlowId`),
over a differently encoded preimage, and `append` ran neither. Those two checks are
`AttackVectors.FlowCanonical.Valid`; the version byte and the cap are new.

## Modelling choices

* `keccak256(abi.encode(preimage))` is the free parameter `enc : PreimageHash`. No
  property of it is assumed. Results that need binding state a `PreimageClash` on two
  named preimages instead, so they never assume global injectivity, which no hash into
  256-bit words has (`CRYPTO-PAIR-INJ` in `ASSUMPTIONS.md`).
* `bytes1` is `UInt8`; `bytes32`/`uint256` words are `UInt256`; `uint64 deadline` is `ℕ`,
  as in `Contracts.Atomicity.Flow`.
* A revert is `none`. Which error is raised is not modelled, only that the call reverts.
* The sort check is `AttackVectors.FlowCanonical.Ascending`, the transcription of the
  neighbour loop.
-/

namespace Contracts.FlowCanonicalAtHead

open AttackVectors.FlowCanonical

/-- `AtomicFlowPreimage` (`IAtomicInterop.sol:50-56`). -/
structure FlowPreimage where
  /-- `bytes1 version`. -/
  version : UInt8
  /-- `uint64 deadline`, a settlement-layer timestamp. -/
  deadline : ℕ
  /-- `uint256 settlementLayerChainId`. -/
  settlementLayerChainId : UInt256
  /-- `bytes32[] legBundleHashes`, required strictly ascending. -/
  legBundleHashes : List UInt256
  /-- `uint256[] legSourceChainIds`, aligned 1:1 with `legBundleHashes`. -/
  legSourceChainIds : List UInt256
deriving DecidableEq

/-- `AtomicFlow` (`IAtomicInterop.sol:64-67`): the claimed id next to its preimage. -/
structure AtomicFlow where
  /-- `bytes32 flowId`; recomputed from `preimage` and matched before use. -/
  flowId : UInt256
  /-- `AtomicFlowPreimage preimage`. -/
  preimage : FlowPreimage
deriving DecidableEq

/-- `ATOMIC_FLOW_PREIMAGE_VERSION` (`IAtomicInterop.sol:91`). -/
def ATOMIC_FLOW_PREIMAGE_VERSION : UInt8 := 0x01

/-- `MAX_ATOMIC_FLOW_LEGS` (`IAtomicInterop.sol:99`). -/
def MAX_ATOMIC_FLOW_LEGS : ℕ := 8

/-- `keccak256(abi.encode(preimage))` (`AtomicFlowManager.sol:378`), kept abstract. -/
abbrev PreimageHash := FlowPreimage → UInt256

/-- The two arrays of a preimage, as an `AttackVectors.FlowCanonical.Flow`. -/
def FlowPreimage.arrays (P : FlowPreimage) : Flow UInt256 UInt256 :=
  ⟨P.legBundleHashes, P.legSourceChainIds⟩

/-- The legs, positionally: leg `i` is `(legBundleHashes[i], legSourceChainIds[i])`. -/
def FlowPreimage.legPairs (P : FlowPreimage) : List (UInt256 × UInt256) :=
  P.legBundleHashes.zip P.legSourceChainIds

/-- The preimage lists bundle hash `b` with declared source chain `c`, at one index. -/
def FlowPreimage.Declares (P : FlowPreimage) (b c : UInt256) : Prop :=
  (b, c) ∈ P.legPairs

/-- The sort check is decidable: it is a neighbour scan. -/
instance (l : List UInt256) : Decidable (Ascending l) :=
  inferInstanceAs (Decidable (l.IsChain (· < ·)))

instance (P : FlowPreimage) (b c : UInt256) : Decidable (P.Declares b c) :=
  inferInstanceAs (Decidable ((b, c) ∈ P.legPairs))

/-- **`_validateAndComputeFlowId`** (`AtomicFlowManager.sol:360-379`), in source order: the
version byte, the leg cap, the neighbour sort check, the length check, then the hash. `none`
is a revert. -/
def validateAndComputeFlowId (enc : PreimageHash) (P : FlowPreimage) : Option UInt256 :=
  if P.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION then none
  else if MAX_ATOMIC_FLOW_LEGS < P.legBundleHashes.length then none
  else if ¬ Ascending P.legBundleHashes then none
  else if P.legSourceChainIds.length ≠ P.legBundleHashes.length then none
  else some (enc P)

/-- **`_checkFlowId`** (`AtomicFlowManager.sol:348-353`): the preimage is accepted and its
hash is the claimed id. -/
def CheckFlowId (enc : PreimageHash) (F : AtomicFlow) : Prop :=
  validateAndComputeFlowId enc F.preimage = some F.flowId

/-- The four checks of `_validateAndComputeFlowId`, as one proposition. -/
structure PreimageAccepted (P : FlowPreimage) : Prop where
  /-- `ManagerFlowPreimageVersionMismatch` (`:361-363`). -/
  version : P.version = ATOMIC_FLOW_PREIMAGE_VERSION
  /-- `ManagerTooManyLegs` (`:367-369`). -/
  legCap : P.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS
  /-- `ManagerBundleHashesNotSorted` (`:370-374`). -/
  sorted : Ascending P.legBundleHashes
  /-- `ManagerLegSourceChainIdsLengthMismatch` (`:375-377`). -/
  lengths : P.legSourceChainIds.length = P.legBundleHashes.length

/-- **A NAMED PREIMAGE COLLISION.** `enc` maps two distinct preimages to one id. For two
preimages whose deadlines fit in `uint64`, as every calldata preimage's does, this is a
keccak collision on their two `abi.encode` images, which differ because the encoding is
injective on such values. It is false for a hash that separates those two preimages. -/
def PreimageClash (enc : PreimageHash) (P P' : FlowPreimage) : Prop :=
  P ≠ P' ∧ enc P = enc P'

/-- **BOUNDED PREIMAGE-HASH INJECTIVITY.** No two preimages of the explicit finite list `Ps`
clash. Satisfiable for every list shorter than `2^256`
(`Contracts.FlowCanonicalAtHead.Properties.PreimageHashInjOnSatisfiable`). -/
def PreimageHashInjOn (enc : PreimageHash) (Ps : List FlowPreimage) : Prop :=
  ∀ P ∈ Ps, ∀ P' ∈ Ps, ¬ PreimageClash enc P P'

/-- A preimage hash honest about one preimage `P0`: `id` on `P0`, `id + 1` everywhere
else. Used to show the clash disjuncts are not tautologies. -/
def honestPreimageHash (P0 : FlowPreimage) (id : UInt256) : PreimageHash :=
  fun P => if P = P0 then id else id + 1

/-! ## The bijection onto the canonical model `Contracts.FlowCanonicalAtV35` -/

/-- A preimage as the canonical model's `PreimageV35`, field by field. -/
def FlowPreimage.toV35 (P : FlowPreimage) : Contracts.FlowCanonicalAtV35.PreimageV35 :=
  ⟨P.version, P.deadline, P.settlementLayerChainId, P.legBundleHashes, P.legSourceChainIds⟩

/-- The canonical model's preimage as a `FlowPreimage`, field by field. -/
def _root_.Contracts.FlowCanonicalAtV35.PreimageV35.toHead (p : Contracts.FlowCanonicalAtV35.PreimageV35) :
    FlowPreimage :=
  ⟨p.version, p.deadline, p.settlementLayerChainId, p.legBundleHashes, p.legSourceChainIds⟩

/-- A flow as the canonical model's `AtomicFlowV35`. -/
def AtomicFlow.toV35 (F : AtomicFlow) : Contracts.FlowCanonicalAtV35.AtomicFlowV35 :=
  ⟨F.flowId, F.preimage.toV35⟩

/-- A preimage hash of this model, read on the canonical model's preimages. -/
def PreimageHash.toV35 (enc : PreimageHash) : Contracts.FlowCanonicalAtV35.PreimageHashV35 :=
  fun p => enc p.toHead

end Contracts.FlowCanonicalAtHead
