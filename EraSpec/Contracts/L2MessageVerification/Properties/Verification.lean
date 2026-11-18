import EraSpec.Contracts.L2MessageVerification.Specs.Verification
import EraSpec.Contracts.FullMerkle.Specs.Model

/-!
# Properties: `L2MessageVerification`

Statements about `EraSpec.Contracts.L2MessageVerification.Specs.Verification`; proofs are in
`EraSpec.Contracts.L2MessageVerification.Proofs.Verification`.  Source: era-contracts
`draft/v0.35.0` head `b17415d20` (identical at `d9f6789`; the code is the same at `main` `70096e2`
and `c67894b9`, see the Specs header).

No result here takes a premise about the hashes beyond the pinned inequalities stated in
`HonestOneHopProofAccepted`; none assumes injectivity.  The results say what the verifier
computes and which storage it reads, not that an accepted proof opens a tree: that is the
`Merkle` folder's subject, and `CalculateRootMemoryIsMerkleSpecWalk` identifies the walk here
with that folder's `MerkleSpec.walkPure`.

## What holds

* **One storage read** (`ProveIsOneStorageRead`): the verdict is a storage-independent
  computation (`anchorRec`: parse, walks, recursion, reverts) followed by one comparison against
  `interopRoots(key).root` at the key that computation names.  So whether a call reverts does not
  depend on the storage (`RevertIsStorageIndependent`), and a call is accepted exactly when the
  root stored at that key is the recomputed root and nonzero (`AcceptedIffStoredRootAtAnchor`).
* **The fuel is not a restriction** (`FuelIrrelevant`): with more fuel than the proof has words,
  the result is the one the entry points compute.
* **What the depth-0 entry point accepts** (`SharedEntryAnchorIff`, `SharedEntryAcceptsIff`):
  `proveL2LeafInclusionShared`, the entry point the in-tree consumer
  `AtomicInteropProof._authenticateRoot` calls (`atomic-interop/libraries/AtomicInteropProof.sol:164`
  at `b17415d20`), accepts exactly a direct proof
  (a final step whose recomputed root is stored at the call's own key) or a proof with one
  self-call (a non-final step, then a final step on the rest of the proof whose recomputed root is
  stored at the settlement-layer key the first step's words name).  At `_depth = 1` only the
  direct form is accepted (`DepthOneAnchorIff`).
* **The consumer's later read** (`SettlementLayerReferenceIsTheAnchorKey`): for a proof with one
  self-call, the settlement-layer block and chain that `readSettlementLayerReference` reads from
  the proof are the key whose root the verifier compared.
* **What the compared root is built from** (`SharedEntryRootShape`): nested walks of the call's
  leaf, its batch number with the timestamp the consumer reads, and its chain id.
* **Against the storage's runs** (`L2InteropRootStorage`): an accepted proof stays accepted in
  every later state (`AcceptanceSurvivesRuns`); a proof that becomes accepted along a logged run was
  accepted at its start or names a key that the run's log imported with exactly the recomputed
  root (`AcceptedAfterRunWasAcceptedOrImported`); along a logged run from fresh storage, every
  accepted proof names a key that a logged bootloader call imported with exactly the recomputed
  root (`AcceptedFromFreshStorageWasImported`), and that key's stored timestamp is nonzero
  (`AcceptedAnchorHasNonzeroTimestamp`).

## Why the zero check is there (countermodel)

* `WithoutNonzeroCheckUnimportedKeyAccepts` — with `correctBatchRoot != bytes32(0)` deleted, a
  one-word final-node proof of the zero leaf is accepted at every key that holds no root, for every
  hash; the contract rejects it there.

## Non-vacuity

* `HonestOneHopProofAccepted` (for every hash meeting three pinned inequalities) and
  `OneHopProofWitness` (one concrete hash): the one-self-call proof `oneHopExampleProof` is
  rejected (not reverted) on fresh storage and accepted once the bootloader has imported its
  recomputed root at the settlement-layer key `(1, 42)` it names; the witness also shows the
  verdict surviving a further import.  It instantiates the premises of
  `AcceptedFromFreshStorageWasImported`, `AcceptedAnchorHasNonzeroTimestamp`,
  `AcceptedAfterRunWasAcceptedOrImported` (with the first disjunct false),
  `AcceptanceSurvivesRuns`, `SettlementLayerReferenceIsTheAnchorKey` and `SharedEntryRootShape`
  (in its one-self-call case).
-/

namespace Contracts.MessageVerification

open Contracts.InteropRootStorage

/-! ## The verifier's structure -/

/-- **THE VERDICT IS ONE STORAGE READ AFTER A STORAGE-INDEPENDENT COMPUTATION.**  For every hash,
storage, fuel, arguments and depth, `proveRecursive` is `anchorRec` (which takes no storage)
followed by the comparison `anchorHolds`: `interopRoots(a.chainId, a.blockOrBatchNumber).root`
equals the anchor's recomputed root and is nonzero. -/
def Properties.ProveIsOneStorageRead : Prop :=
  ∀ (H : Hashes) (S : State) (fuel : ℕ) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    proveRecursive H S fuel chainId blockOrBatchNumber leafProofMask leaf proof depth =
      (anchorRec H fuel chainId blockOrBatchNumber leafProofMask leaf proof depth).map (anchorHolds S)

/-- **THE FUEL IS NOT A RESTRICTION.**  With `proof.length + k` fuel, for any `k`, `anchorRec` and
`proveRecursive` return what they return with `proof.length`, which is what the entry points
use. -/
def Properties.FuelIrrelevant : Prop :=
  ∀ (H : Hashes) (S : State) (k : ℕ) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    anchorRec H (proof.length + k) chainId blockOrBatchNumber leafProofMask leaf proof depth =
      anchorRec H proof.length chainId blockOrBatchNumber leafProofMask leaf proof depth ∧
    proveRecursive H S (proof.length + k) chainId blockOrBatchNumber leafProofMask leaf proof depth =
      proveRecursive H S proof.length chainId blockOrBatchNumber leafProofMask leaf proof depth

/-- **WHETHER A CALL REVERTS DOES NOT DEPEND ON THE STORAGE.**  For any caller-chosen depth, the
external call reverts in one state exactly when it reverts in any other. -/
def Properties.RevertIsStorageIndependent : Prop :=
  ∀ (H : Hashes) (S S' : State) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = none ↔
      proveL2LeafInclusionSharedRecursive H S' chainId blockOrBatchNumber leafProofMask leaf proof
        depth = none

/-- **ACCEPTED EXACTLY WHEN THE ROOT STORED AT THE ANCHOR IS THE RECOMPUTED ONE AND NONZERO.**
For any caller-chosen depth: the external call returns `true` exactly when the call has an anchor
and the root stored at the anchor's key is the anchor's recomputed root, which is nonzero. -/
def Properties.AcceptedIffStoredRootAtAnchor : Prop :=
  ∀ (H : Hashes) (S : State) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true ↔
      ∃ a, anchor H chainId blockOrBatchNumber leafProofMask leaf proof depth = some a ∧
        (interopRoots S a.chainId a.blockOrBatchNumber).root = a.computedRoot ∧ a.computedRoot ≠ 0

/-- **THE DEPTH-0 ENTRY: A DIRECT PROOF OR ONE SELF-CALL, NOTHING ELSE.**  The anchor of
`proveL2LeafInclusionShared` (depth 0) is `a` exactly when the proof parses (`getProofData`) and
either that step is final and `a` is the call's own key with the step's recomputed root and no
self-call, or that step is non-final, the rest of the proof (`proof.drop pd.ptr`) parses as a
final step for the settlement-layer chain, block, mask and chain-id leaf the first step produced,
and `a` is that settlement-layer key with the second step's recomputed root and one self-call. -/
def Properties.SharedEntryAnchorIff : Prop :=
  ∀ (H : Hashes) (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (a : Anchor),
    anchor H chainId blockOrBatchNumber leafProofMask leaf proof 0 = some a ↔
      ∃ pd, getProofData H chainId blockOrBatchNumber leafProofMask leaf proof = some pd ∧
        ((pd.finalProofNode = true ∧ a = ⟨chainId, blockOrBatchNumber, pd.batchSettlementRoot, 0⟩) ∨
         (pd.finalProofNode = false ∧
          ∃ pd', getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
              pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) = some pd' ∧
            pd'.finalProofNode = true ∧
            a = ⟨pd.settlementLayerChainId, pd.settlementLayerBatchNumber,
              pd'.batchSettlementRoot, 1⟩))

/-- **AT DEPTH 1, ONLY A DIRECT PROOF.**  The anchor at caller depth 1 is `a` exactly when the proof
parses as a final step and `a` is the call's own key with that step's recomputed root and no
self-call (a non-final step reverts, `DepthMoreThanOneForRecursiveMerkleProof`). -/
def Properties.DepthOneAnchorIff : Prop :=
  ∀ (H : Hashes) (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (a : Anchor),
    anchor H chainId blockOrBatchNumber leafProofMask leaf proof 1 = some a ↔
      ∃ pd, getProofData H chainId blockOrBatchNumber leafProofMask leaf proof = some pd ∧
        pd.finalProofNode = true ∧ a = ⟨chainId, blockOrBatchNumber, pd.batchSettlementRoot, 0⟩

/-- **WHAT `proveL2LeafInclusionShared` ACCEPTS.**  It returns `true` exactly when the proof parses
and either that step is final and the root stored at the call's own key
`(chainId, blockOrBatchNumber)` is the step's recomputed root and nonzero, or that step is
non-final, the rest of the proof parses as a final step for the settlement-layer data the first
step produced, and the root stored at the settlement-layer key
`(settlementLayerChainId, settlementLayerBatchNumber)` that the first step read from the proof is
the second step's recomputed root and nonzero. -/
def Properties.SharedEntryAcceptsIff : Prop :=
  ∀ (H : Hashes) (S : State) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256),
    proveL2LeafInclusionShared H S chainId blockOrBatchNumber leafProofMask leaf proof = some true ↔
      ∃ pd, getProofData H chainId blockOrBatchNumber leafProofMask leaf proof = some pd ∧
        ((pd.finalProofNode = true ∧
            (interopRoots S chainId blockOrBatchNumber).root = pd.batchSettlementRoot ∧
            pd.batchSettlementRoot ≠ 0) ∨
         (pd.finalProofNode = false ∧
          ∃ pd', getProofData H pd.settlementLayerChainId pd.settlementLayerBatchNumber
              pd.settlementLayerBatchRootMask pd.chainIdLeaf (proof.drop pd.ptr) = some pd' ∧
            pd'.finalProofNode = true ∧
            (interopRoots S pd.settlementLayerChainId pd.settlementLayerBatchNumber).root =
              pd'.batchSettlementRoot ∧
            pd'.batchSettlementRoot ≠ 0))

/-- **THE MERKLE WALK IS THE `Merkle` FOLDER'S.**  `calculateRootMemory` returns `r` exactly when the
path is shorter than 256, the index is below `2 ^ path.length`, and `r` is
`MerkleSpec.walkPure` (`FullMerkle/Specs/Model.lean`) of the path read as a sibling stream from
level 0, for `path.length` levels. -/
def Properties.CalculateRootMemoryIsMerkleSpecWalk : Prop :=
  ∀ (h : UInt256 → UInt256 → UInt256) (path : List UInt256) (index item r : UInt256),
    calculateRootMemory h path index item = some r ↔
      path.length < 256 ∧ index.val < 2 ^ path.length ∧
        r = MerkleSpec.walkPure h (fun l => path.getD l 0) 0 path.length index.val item

/-- **THE SETTLEMENT-LAYER WORDS THE CONSUMER READS AFTERWARDS ARE THE ANCHOR'S KEY.**  If the
depth-0 entry's anchor has one self-call, then the first step of the proof parses as a non-final
step and `readSettlementLayerReference` on the same proof returns the anchor's block and chain,
with that step's `l1BatchTimestamp` (the value hashed into its batch leaf).  At `b17415d20`
`AtomicInteropProof._authenticateRoot` returns exactly these three words after the verifier accepted
(`atomic-interop/libraries/AtomicInteropProof.sol:164-188`); that consumer is not modelled here. -/
def Properties.SettlementLayerReferenceIsTheAnchorKey : Prop :=
  ∀ (H : Hashes) (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (a : Anchor),
    anchor H chainId blockOrBatchNumber leafProofMask leaf proof 0 = some a → a.hops = 1 →
      ∃ pd, getProofData H chainId blockOrBatchNumber leafProofMask leaf proof = some pd ∧
        pd.finalProofNode = false ∧
        readSettlementLayerReference proof =
          some ⟨a.blockOrBatchNumber, a.chainId, pd.l1BatchTimestamp⟩

/-- **WHAT THE COMPARED ROOT IS BUILT FROM.**  The recomputed root of the depth-0 entry's anchor is
either, with no self-call and at the call's own key, a Merkle walk (`walk`, the loop of
`calculateRootMemory`) of the call's leaf; or, with one self-call, a walk of the chain-id leaf
`chainIdLeaf(·, chainId)` of a walk of the batch leaf `batchLeaf(·, blockOrBatchNumber, ts)` of a
walk of the call's leaf, where `ts` is the `l1BatchTimestamp` that `readSettlementLayerReference`
reads from the proof next to the anchor's key.  The paths and masks are the prover's; the call's
`leaf`, `leafProofMask`, `chainId` and `blockOrBatchNumber` enter as shown.  Whether two different
calls can lead to one root is a question about the hashes, which are uninterpreted here. -/
def Properties.SharedEntryRootShape : Prop :=
  ∀ (H : Hashes) (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (a : Anchor),
    anchor H chainId blockOrBatchNumber leafProofMask leaf proof 0 = some a →
      (a.hops = 0 ∧ a.chainId = chainId ∧ a.blockOrBatchNumber = blockOrBatchNumber ∧
        ∃ logPath : List UInt256, a.computedRoot = walk H.node logPath leafProofMask.val leaf) ∨
      (a.hops = 1 ∧
        ∃ (logPath batchPath slPath : List UInt256) (batchMask slMask ts : UInt256),
          a.computedRoot = walk H.node slPath slMask.val
            (H.chainIdLeaf (walk H.node batchPath batchMask.val
              (H.batchLeaf (walk H.node logPath leafProofMask.val leaf) blockOrBatchNumber ts))
              chainId) ∧
          readSettlementLayerReference proof = some ⟨a.blockOrBatchNumber, a.chainId, ts⟩)

/-! ## Against the storage's runs -/

/-- **AN ACCEPTED PROOF STAYS ACCEPTED.**  If a call (any depth) returns `true` in a state, it
returns `true` in every state reachable from it by the storage contract's runs. -/
def Properties.AcceptanceSurvivesRuns : Prop :=
  ∀ (H : Hashes) (S S' : State) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    Reach S S' →
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true →
    proveL2LeafInclusionSharedRecursive H S' chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true

/-- **A PROOF BECOMES ACCEPTED ONLY BY AN IMPORT AT ITS ANCHOR.**  If a call (any depth) returns
`true` after a logged run from `S₀`, then it returned `true` in `S₀`, or its anchor's key held no
root in `S₀` and an import of the run's log names that key with `sides[0]` equal to the anchor's
recomputed root. -/
def Properties.AcceptedAfterRunWasAcceptedOrImported : Prop :=
  ∀ (H : Hashes) (S₀ S : State) (log : List (Address × Call))
    (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (depth : UInt256),
    ReachLog S₀ S log →
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true →
      proveL2LeafInclusionSharedRecursive H S₀ chainId blockOrBatchNumber leafProofMask leaf proof
          depth = some true ∨
      ∃ a, anchor H chainId blockOrBatchNumber leafProofMask leaf proof depth = some a ∧
        (interopRoots S₀ a.chainId a.blockOrBatchNumber).root = 0 ∧
        ∃ r ∈ imports log, r.key = (a.chainId, a.blockOrBatchNumber) ∧ r.sides.headD 0 = a.computedRoot

/-- **FROM FRESH STORAGE, EVERY ACCEPTED PROOF IS ANCHORED AT A ROOT THE BOOTLOADER IMPORTED.**
Along any logged run of the storage contract from fresh storage, if a call (any depth) returns
`true`, then some logged call, made by `L2_BOOTLOADER_ADDRESS`, imported an `InteropRoot` at the
anchor's key whose `sides` is exactly `[anchor's recomputed root]`. -/
def Properties.AcceptedFromFreshStorageWasImported : Prop :=
  ∀ (H : Hashes) (S : State) (log : List (Address × Call))
    (chainId blockOrBatchNumber leafProofMask leaf : UInt256) (proof : List UInt256)
    (depth : UInt256),
    ReachLog empty S log →
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true →
      ∃ a, anchor H chainId blockOrBatchNumber leafProofMask leaf proof depth = some a ∧
        ∃ p ∈ log, p.1 = L2_BOOTLOADER_ADDRESS ∧
          ∃ r ∈ p.2.roots, r.key = (a.chainId, a.blockOrBatchNumber) ∧ r.sides = [a.computedRoot]

/-- **ALONG RUNS FROM FRESH STORAGE, AN ACCEPTED ANCHOR'S KEY HAS A NONZERO TIMESTAMP.**  If a call
(any depth) returns `true` in a state reachable from fresh storage, the timestamp stored at its
anchor's key is nonzero (`L2InteropRootStorage`'s `ZeroTimestampIffUnsetInvariant`).  With
`SettlementLayerReferenceIsTheAnchorKey`, that key is the one whose timestamp
`AtomicInteropProof.verifyTimeoutAbsence` reads and tests against zero right after
`_authenticateRoot` (`atomic-interop/libraries/AtomicInteropProof.sol:89-97` at `b17415d20`). -/
def Properties.AcceptedAnchorHasNonzeroTimestamp : Prop :=
  ∀ (H : Hashes) (S : State) (chainId blockOrBatchNumber leafProofMask leaf : UInt256)
    (proof : List UInt256) (depth : UInt256),
    Reach empty S →
    proveL2LeafInclusionSharedRecursive H S chainId blockOrBatchNumber leafProofMask leaf proof depth
        = some true →
      ∃ a, anchor H chainId blockOrBatchNumber leafProofMask leaf proof depth = some a ∧
        (interopRoots S a.chainId a.blockOrBatchNumber).timestamp ≠ 0

/-! ## Countermodel: the zero check is load-bearing -/

/-- **WITHOUT `correctBatchRoot != bytes32(0)`, AN UNIMPORTED KEY ACCEPTS THE ZERO LEAF.**  For every
hash, every state and every key holding a zero root (every key of fresh storage, for instance):
`proveL2LeafInclusionShared` with leaf `0`, mask `0` and the one-word final-node proof
`zeroLeafDirectProof` returns `false`, and the same call of the mutant returns `true`. -/
def Properties.WithoutNonzeroCheckUnimportedKeyAccepts : Prop :=
  ∀ (H : Hashes) (S : State) (chainId blockOrBatchNumber : UInt256),
    (interopRoots S chainId blockOrBatchNumber).root = 0 →
      proveL2LeafInclusionShared H S chainId blockOrBatchNumber 0 0 zeroLeafDirectProof = some false ∧
      proveL2LeafInclusionSharedNoZeroCheck H S chainId blockOrBatchNumber 0 0 zeroLeafDirectProof
        = some true

/-! ## Witnesses -/

/-- **THE ONE-SELF-CALL EXAMPLE PROOF, FOR EVERY HASH MEETING THREE PINNED INEQUALITIES.**  Let
`R = H.chainIdLeaf (H.batchLeaf leaf 3 100) 7`.  If `leaf` and `R` are not
`L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` and `R ≠ 0`, then for the call
`proveL2LeafInclusionShared(7, 3, 0, leaf, oneHopExampleProof)`: its anchor is the
settlement-layer key `(1, 42)` with recomputed root `R` and one self-call; on fresh storage it
returns `false`; and in every state whose root at `(1, 42)` is `R` it returns `true`. -/
def Properties.HonestOneHopProofAccepted : Prop :=
  ∀ (H : Hashes) (leaf : UInt256),
    leaf ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH →
    H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH →
    H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 ≠ 0 →
      anchor H 7 3 0 leaf oneHopExampleProof 0 =
          some ⟨1, 42, H.chainIdLeaf (H.batchLeaf leaf 3 100) 7, 1⟩ ∧
      proveL2LeafInclusionShared H empty 7 3 0 leaf oneHopExampleProof = some false ∧
      ∀ S : State, (interopRoots S 1 42).root = H.chainIdLeaf (H.batchLeaf leaf 3 100) 7 →
        proveL2LeafInclusionShared H S 7 3 0 leaf oneHopExampleProof = some true

/-- **A CONCRETE RUN IN WHICH THE EXAMPLE PROOF BECOMES ACCEPTED.**  For one concrete hash meeting
the inequalities of `HonestOneHopProofAccepted`, and leaf 1: the call's anchor has one self-call,
and `readSettlementLayerReference` reads `(42, 1, 100)` from the proof; on fresh storage, which
holds no root at `(1, 42)`, the call returns `false`; after one logged bootloader import at
`(1, 42)` it returns `true`; after a further logged import at another key it still returns
`true`. -/
def Properties.OneHopProofWitness : Prop :=
  ∃ (H : Hashes) (S₁ S₂ : State) (log₁ log₂ : List (Address × Call)),
    1 ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH ∧
    H.chainIdLeaf (H.batchLeaf 1 3 100) 7 ≠ L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH ∧
    H.chainIdLeaf (H.batchLeaf 1 3 100) 7 ≠ 0 ∧
    (∃ a, anchor H 7 3 0 1 oneHopExampleProof 0 = some a ∧ a.hops = 1) ∧
    readSettlementLayerReference oneHopExampleProof = some ⟨42, 1, 100⟩ ∧
    ReachLog empty S₁ log₁ ∧ log₁.length = 1 ∧ ReachLog S₁ S₂ log₂ ∧ log₂.length = 1 ∧
    (interopRoots empty 1 42).root = 0 ∧
    proveL2LeafInclusionShared H empty 7 3 0 1 oneHopExampleProof = some false ∧
    proveL2LeafInclusionShared H S₁ 7 3 0 1 oneHopExampleProof = some true ∧
    proveL2LeafInclusionShared H S₂ 7 3 0 1 oneHopExampleProof = some true

end Contracts.MessageVerification
