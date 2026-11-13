import EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBinding
import EraSpec.Contracts.InteropCenter.Specs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Model: where the atomic path's source binding comes from, computed

Source: era-contracts at the pin `c67894b9`, `l1-contracts/contracts/`:
`interop/interop-handler/InteropHandlerBase.sol` and `L2InteropHandler.sol`,
`atomic-interop/AtomicFlowManager.sol`, `atomic-interop/libraries/AtomicInteropProof.sol`,
`interop/InteropCenter.sol`, `interop/InteropDataEncoding.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.L2InteropHandler.Properties.AtomicSourceBindingStrong` and are proved in
`EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingStrong`.

## Why this file exists

`Properties.atomic_source_bound` (topic `AtomicSourceBinding`) concludes `declared h = c` from
`commit h ∈ tree c` under `HonestCommits declared commit tree`, which is
`∀ c h, commit h ∈ tree c → declared h = c`: the premise is the conclusion, quantified. And
`declared : Hash → Chain` takes for granted that a bundle hash determines its source chain,
which is global injectivity of keccak in disguise (no such map exists at `bytes32`, topic
`BundleHashPinned`). Neither the validator, nor its two call sites, nor the hash computation, nor
the flow gate is modelled there. This file models them.

## The code

    _getBundleData (InteropHandlerBase.sol:242-251)
        interopBundle = abi.decode(_bundle, (InteropBundle));
        bundleHash = InteropDataEncoding.encodeInteropBundleHash(interopBundle.sourceChainId, _bundle);
            // = keccak256(abi.encode(interopBundle.sourceChainId, _bundle))   InteropDataEncoding.sol:11-13

    _validateBundleDestinationContext(bundleHash, b, proofChainId)   (:428-451)
        require(b.sourceChainId == proofChainId);                          // (1)
        require(b.destinationChainId == block.chainid);
        require(b.destinationBaseTokenAssetId == _expectedDestinationBaseTokenAssetId());

    call sites    executeBundle :92, verifyBundle :154    proofChainId = _proof.chainId
                  executeAtomicBundle L2InteropHandler.sol:57    proofChainId = interopBundle.sourceChainId

    requireFlowFinalized(bundleHash, _finality)   (AtomicFlowManager.sol:105-132)
        for each leg i:  proofs[i].sourceChainId == legSourceChainIds[i]               // :124-126
                         verifyInclusion(proofs[i], commitValue(flowId, legBundleHashes[i]), ...)  // :127-128
        some leg i has legBundleHashes[i] == bundleHash                                // :123, :131
    commitValue(flowId, h) = uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, h)))
                                                                    // AtomicInteropProof.sol:100-102

    _executeCalls  sender: InteroperableAddress.formatEvmV1(_sourceChainId, interopCall.from)
                   with _sourceChainId = interopBundle.sourceChainId     // :284, L2InteropHandler.sol:92

On the source chain `c`, `AtomicFlowManager.append` inserts `commitValue(flowId, bundleHash)` into
`c`'s tree (`:97-99`), and the center's `_dispatchBundle` computes that `bundleHash` with
`block.chainid = c` (`InteropCenter.sol:644`).

## Modelling choices

* **The decoded field is the bundle's own.** `src` is `interopBundle.sourceChainId`, decoded from
  the presented bytes `x`; it is what both `_getBundleData`'s hash and the recipient's `sender`
  use. Nothing relates `src` to anything else up front.
* **Keccak is one function, `P.keccak`,** the same on every chain; nothing is assumed about it.
  Every collision a result mentions is on two byte strings it names.
* **The vouching tree is a set of words** (the IMT's keys, `0` the sentinel). Its root's
  authentication against the settlement layer (`_authenticateRoot`) is not modelled: membership
  in chain `c`'s tree is what a passing `verifyInclusion` against `c`'s root means.
* **Honest insertion of one tree** (`TreeHoldsOwnLegs`): every key of chain `c`'s tree is the
  sentinel or the commit value of an atomic dispatch logged by `c`'s center, with the bundle hash
  that center computed. For a chain running the deployed center it follows from the tree/manager
  link (`TreeBackedByManager`, LocalHonesty's links 1–2, which
  `Contracts.AppendPath.RunKeysAreLoggedCommitValues` proves for the append-path model) and
  `Contracts.InteropCenter.CommittedLegsAreValidatedDispatches` (link 3):
  `Properties.CenterRunTreeHoldsOwnLegs`.
-/

namespace AttackVectors.AtomicSourceBinding

open AttackVectors.BundleHashEncoding (abiEncode word)
open Contracts.InteropCenter (Params Dispatch Word bundleHash)
open Contracts.AtomicFlowManager (LegState)

/-! ## The validator and its two call sites -/

/-- The fields of a decoded `InteropBundle` that `_validateBundleDestinationContext` reads. -/
structure DestCtx where
  sourceChainId : Word
  destinationChainId : Word
  destinationBaseTokenAssetId : Word

/-- `_validateBundleDestinationContext(_, b, proofChainId)` does not revert, on a chain whose
`block.chainid` is `blockChainId` and whose base-token asset id is `baseTokenAssetId`. -/
def DestContextValid (blockChainId baseTokenAssetId : Word) (b : DestCtx) (proofChainId : Word) :
    Prop :=
  b.sourceChainId = proofChainId ∧ b.destinationChainId = blockChainId ∧
    b.destinationBaseTokenAssetId = baseTokenAssetId

/-- The validator's call sites. -/
inductive CtxSite
  /-- `executeBundle` (`:92`) and `verifyBundle` (`:154`): `proofChainId = _proof.chainId`. -/
  | publicSite (proofChainId : Word)
  /-- `executeAtomicBundle` (`L2InteropHandler.sol:57`):
  `proofChainId = interopBundle.sourceChainId`. -/
  | atomicSite

/-- The `proofChainId` a call site passes for bundle `b`. -/
def CtxSite.proofChainId (b : DestCtx) : CtxSite → Word
  | .publicSite c => c
  | .atomicSite => b.sourceChainId

/-! ## The hashes -/

/-- **WHAT THE DESTINATION KEYS THE PRESENTED BYTES BY**:
`encodeInteropBundleHash(src, x) = keccak256(abi.encode(src, x))`, with `src` the decoded
`sourceChainId` of `x` (`:249`). -/
def destBundleHash (keccak : List UInt8 → Word) (src : Word) (x : List UInt8) : Word :=
  keccak (abiEncode src.val x)

/-- `abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)`: three words. -/
def commitPreimage (tag flowId bundleHash : Word) : List UInt8 :=
  word tag.val ++ (word flowId.val ++ word bundleHash.val)

/-- `commitValue(flowId, bundleHash)` (`AtomicInteropProof.sol:100-102`). -/
def commitValue (keccak : List UInt8 → Word) (tag flowId bundleHash : Word) : Word :=
  keccak (commitPreimage tag flowId bundleHash)

/-! ## The vouching tree -/

/-- **CHAIN `P`'S TREE HOLDS ONLY ITS OWN CENTER'S LEGS.** Every key of the tree `T` is the
sentinel `0` or the commit value of an atomic dispatch in `log`, chain `P`'s center log, with the
bundle hash that center computed, `keccak(abi.encode(P.chainId, abi.encode(bundle)))`. This is
`HonestInsertion` for this one tree. -/
def TreeHoldsOwnLegs (P : Params) (tag : Word) (log : List Dispatch) (T : Set Word) : Prop :=
  ∀ v ∈ T, v = 0 ∨ ∃ d ∈ log, d.isAtomic = true ∧
    v = commitValue P.keccak tag d.atomicSend.flowId (bundleHash P d.bundle)

/-- **THE TREE/MANAGER LINK.** Every key of chain `P`'s tree `T` is the sentinel or the commit
value of a leg that chain `P`'s flow manager has moved out of `Unset`: the tree's only inserter is
the manager (`L2InteropCommitmentTree.sol:54`), which inserts only in `append`, right after
committing the leg (`AtomicFlowManager.sol:95-99`). -/
def TreeBackedByManager (P : Params) (tag : Word) (S : Contracts.InteropCenter.State)
    (T : Set Word) : Prop :=
  ∀ v ∈ T, v = 0 ∨ ∃ f h, S.manager.legState f h ≠ .Unset ∧ v = commitValue P.keccak tag f h

/-- **WHAT `requireFlowFinalized(h, _finality)` ESTABLISHES WHEN IT RETURNS.** `legs` pairs each
leg's bundle hash with its declared source chain (`legBundleHashes[i]`, `legSourceChainIds[i]`).
Some leg is the executing bundle, and each leg's commit value is in the tree of the leg's
declared chain: each proof's chain must be the leg's (`:124-126`) and `verifyInclusion` proves the
value against that chain's root (`:127-128`). The flow-id, settlement-layer and deadline checks
are omitted (they only reject). -/
structure FlowGatePassed (keccak : List UInt8 → Word) (tag : Word) (trees : Word → Set Word)
    (flowId : Word) (legs : List (Word × Word)) (h : Word) : Prop where
  executingIsLeg : ∃ c, (h, c) ∈ legs
  included : ∀ p ∈ legs, commitValue keccak tag flowId p.1 ∈ trees p.2

/-! ## Witness data

On the honest InteropCenter witness chain `wParams` (chain `324`, keccak = the last word), after
`wD1` (an atomic leg of flow `7`) is dispatched (`wS1`). -/

/-- The commit tag of the witnesses. -/
def wTag : Word := 5

/-- Chain `324`'s tree after `wD1`'s `append`: the sentinel and `wD1`'s commit value. -/
def wTree : Set Word :=
  {v | v = 0 ∨ v = commitValue Contracts.InteropCenter.wParams.keccak wTag 7
    (bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle)}

/-- Bytes declaring source chain `325`, presented to the destination. -/
def wForeignBytes : List UInt8 := word 5

/-- A tree of chain `324` that also holds the commit value of a leg whose bundle hash was
computed with source chain `325` — what a chain not running an unmodified deployment could
insert. -/
def wForeignTree : Set Word :=
  {v | v = 0 ∨ v = commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (bundleHash Contracts.InteropCenter.wParams Contracts.InteropCenter.wD1.bundle) ∨
    v = commitValue Contracts.InteropCenter.wParams.keccak wTag 7
      (destBundleHash Contracts.InteropCenter.wParams.keccak 325 wForeignBytes)}

end AttackVectors.AtomicSourceBinding
