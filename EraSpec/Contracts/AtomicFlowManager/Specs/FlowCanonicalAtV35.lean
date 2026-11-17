import EraSpec.Core.Word
import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonical

/-!
# Contract spec at `draft/v0.35.0`: the flow preimage and `_validateAndComputeFlowId`

Source: matter-labs/era-contracts, branch `draft/v0.35.0` at commit `d9f678900`
(short sha `d9f6789`).  Paths are relative to `l1-contracts/contracts/` at that commit.
The pin model (`Specs/FlowCanonical.lean`, era-contracts `c67894b9`) is not changed;
this file models the v35 code next to it.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.FlowCanonicalAtV35`, proofs in
`EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtV35`.

## The code at `d9f6789`

    // atomic-interop/IAtomicInterop.sol:50-56
    struct AtomicFlowPreimage {
        bytes1 version;
        uint64 deadline;
        uint256 settlementLayerChainId;
        bytes32[] legBundleHashes;
        uint256[] legSourceChainIds;
    }
    // IAtomicInterop.sol:64-67
    struct AtomicFlow { bytes32 flowId; AtomicFlowPreimage preimage; }
    // IAtomicInterop.sol:91 and :99
    bytes1 constant ATOMIC_FLOW_PREIMAGE_VERSION = 0x01;
    uint256 constant MAX_ATOMIC_FLOW_LEGS = 8;

    // atomic-interop/AtomicFlowManager.sol:360-379
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

Callers at `d9f6789`: `append` (`AtomicFlowManager.sol:109`, directly), and
`requireFlowFinalized` (`:182`) and `authorizeRefund` (`:217`) through `_checkFlowId`.
`claimRefund` (`:250-265`) calls neither: a claim is keyed by `(flowId, bundleHash)`
alone, so the pin docstring's "guards every delivery and every reclaim" is still not
true of the reclaim step.

These lines are byte-identical to `main` at `3605e82` (there `:346-365` and `:334-339`;
v35 is shifted by the import and the 14 lines of `_checkLegSourceAllowed`).  So the
`main` model `Contracts.FlowCanonicalAtHead` (backlog topic H-3, written concurrently)
describes the same code.  Once both are merged, `AcceptedV35` is its `PreimageAccepted`
and the statements of this topic can become aliases of the `AtHead` ones.

## What changed from the pin

At `c67894b9` (`AtomicFlowManager.sol:247-259`) `_checkFlowId` ran the neighbour sort
check and the length check, then hashed
`abi.encode(legBundleHashes, legSourceChainIds, deadline, settlementLayerChainId)`, and
`append` took an opaque `flowId` and ran neither.  At `d9f6789`:

1. the preimage is one struct with a version byte, hashed as a whole (`:378`), with a
   new field order;
2. two checks are new and come first: the version byte (`:361-363`) and the leg cap
   (`:367-369`);
3. the sort check and the length check are unchanged (`:370-377`);
4. one function serves all three entry points, `append` included.

So the pin's `Valid` is still NECESSARY for acceptance but no longer SUFFICIENT.  The
pin docstring's pairing with `BundleHashEncoding.abiEncode_inj` does not cover the new
layout: that lemma is about a different `abi.encode` argument list, and no
`abi.encode` injectivity for this five-field struct is proved anywhere.  Here the whole
composite `keccak256 ∘ abi.encode` is the free parameter `enc`, and binding results
name a `PreimageClashV35` on two given preimages instead of assuming injectivity.

## Modelling choices

* `bytes1 version` and `uint64 deadline` are `ℕ`; `bytes32`/`uint256` words are
  `UInt256`.  Only equality with `0x01` is ever tested on the version.
* A revert is `none`.  Which error is raised is not modelled.
* The sort check is `AttackVectors.FlowCanonical.Ascending`, the pin's transcription of
  the same neighbour loop; the two arrays form the pin's `AttackVectors.FlowCanonical.Flow`.
-/

namespace Contracts.FlowCanonicalAtV35

open AttackVectors.FlowCanonical

/-- `AtomicFlowPreimage` (`atomic-interop/IAtomicInterop.sol:50-56`). -/
structure PreimageV35 where
  /-- `bytes1 version`. -/
  version : ℕ
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
structure AtomicFlowV35 where
  /-- `bytes32 flowId`, recomputed from `preimage` and matched before use. -/
  flowId : UInt256
  /-- `AtomicFlowPreimage preimage`. -/
  preimage : PreimageV35
deriving DecidableEq

/-- `ATOMIC_FLOW_PREIMAGE_VERSION = 0x01` (`IAtomicInterop.sol:91`). -/
def ATOMIC_FLOW_PREIMAGE_VERSION_V35 : ℕ := 1

/-- `MAX_ATOMIC_FLOW_LEGS = 8` (`IAtomicInterop.sol:99`). -/
def MAX_ATOMIC_FLOW_LEGS_V35 : ℕ := 8

/-- `keccak256(abi.encode(preimage))` (`AtomicFlowManager.sol:378`), kept abstract. -/
abbrev PreimageHashV35 := PreimageV35 → UInt256

/-- The two arrays of a preimage, as the pin's `AttackVectors.FlowCanonical.Flow`. -/
def PreimageV35.arrays (p : PreimageV35) : Flow UInt256 UInt256 :=
  ⟨p.legBundleHashes, p.legSourceChainIds⟩

/-- The sort check is decidable: it is a neighbour scan. -/
instance (l : List UInt256) : Decidable (Ascending l) :=
  inferInstanceAs (Decidable (l.IsChain (· < ·)))

/-- **`_validateAndComputeFlowId`** (`AtomicFlowManager.sol:360-379`), in source order:
the version byte (`:361-363`), the leg cap (`:367-369`), the neighbour sort check
(`:370-374`), the length check (`:375-377`), then the hash (`:378`).  `none` is a
revert. -/
def validateV35 (enc : PreimageHashV35) (p : PreimageV35) : Option UInt256 :=
  if p.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION_V35 then none
  else if MAX_ATOMIC_FLOW_LEGS_V35 < p.legBundleHashes.length then none
  else if ¬ Ascending p.legBundleHashes then none
  else if p.legSourceChainIds.length ≠ p.legBundleHashes.length then none
  else some (enc p)

/-- **`_checkFlowId`** (`AtomicFlowManager.sol:348-353`): the preimage is accepted and
its hash is the claimed id. -/
def CheckFlowIdV35 (enc : PreimageHashV35) (F : AtomicFlowV35) : Prop :=
  validateV35 enc F.preimage = some F.flowId

/-- The four checks of `_validateAndComputeFlowId` at v35, as one proposition. -/
structure AcceptedV35 (p : PreimageV35) : Prop where
  /-- `ManagerFlowPreimageVersionMismatch` (`:361-363`). -/
  version : p.version = ATOMIC_FLOW_PREIMAGE_VERSION_V35
  /-- `ManagerTooManyLegs` (`:367-369`). -/
  legCap : p.legBundleHashes.length ≤ MAX_ATOMIC_FLOW_LEGS_V35
  /-- `ManagerBundleHashesNotSorted` (`:370-374`). -/
  sorted : Ascending p.legBundleHashes
  /-- `ManagerLegSourceChainIdsLengthMismatch` (`:375-377`). -/
  lengths : p.legSourceChainIds.length = p.legBundleHashes.length

/-- **A NAMED PREIMAGE COLLISION.**  `enc` maps the two given, distinct preimages to one
id.  This is a keccak collision on two named `abi.encode` images (or an `abi.encode`
non-injectivity on them); it is false for any hash that separates the two. -/
def PreimageClashV35 (enc : PreimageHashV35) (p q : PreimageV35) : Prop :=
  p ≠ q ∧ enc p = enc q

/-- A preimage hash that is honest about one preimage `p0`: `id` on `p0`, `id + 1`
everywhere else.  Used to show the clash disjuncts are not tautologies. -/
def honestPreimageHashV35 (p0 : PreimageV35) (id : UInt256) : PreimageHashV35 :=
  fun p => if p = p0 then id else id + 1

end Contracts.FlowCanonicalAtV35
