import Mathlib.Tactic
import EraSpec.Core.Word
import EraSpec.Contracts.AtomicFlowManager.Specs.Model

/-!
# Model: one chain's `append` gate, `authorizeRefund`, and `L2InteropRootStorage` (v35 head)

**Commit.** matter-labs/era-contracts, branch `draft/v0.35.0` at `b17415d20`.  Paths are relative
to `l1-contracts/contracts/`.  `A:N` is a line of `atomic-interop/AtomicFlowManager.sol`, `P:N` of
`atomic-interop/libraries/AtomicInteropProof.sol`, `R:N` of `interop/L2InteropRootStorage.sol`.
The leg map is the `Manager` of `Specs/Model.lean`, the folder's one leg machine.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.AtomicFlowManager.Properties.RefundClosesAppend`, proofs in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RefundClosesAppend`.

## The claim under test

`append` reads the root storage before it commits a leg (A:112-125):

    // ... What it enforces unconditionally is ordering on this chain: reverting a leg requires
    // importing a root with `timestamp > deadline` (see {AtomicInteropProof.verifyTimeoutAbsence})
    // and the tracked timestamp is a monotone maximum, so once a leg of the flow was reverted here,
    // no new leg can ever be committed here.
    uint256 latestImportedRootTimestamp = L2_INTEROP_ROOT_STORAGE.latestInteropRootTimestamp(
        _flowPreimage.settlementLayerChainId);
    if (latestImportedRootTimestamp > _flowPreimage.deadline) {
        revert ManagerFlowDeadlinePassed(_flowPreimage.deadline, latestImportedRootTimestamp);
    }

`protocol-docs/atomicity/flow.md:67-72` repeats it.  The argument needs three contracts to read
one key:

* `authorizeRefund` (A:216-247) checks the flow's settlement layer against `L1_CHAIN_ID`
  (A:218, `_checkSettlementLayerIsL1`, A:329-333) and calls `verifyTimeoutAbsence` with that
  settlement layer as `_expectedSlChainId` (A:234);
* `verifyTimeoutAbsence` (P:77-124) requires the proof's `slChainId` to equal it (P:90-92) and
  reads `interopRoots(slChainId, slBlock).timestamp`, which must be nonzero and `> deadline`
  (P:94-100);
* `_addInteropRoot` (R:70-103) writes each key's root and timestamp at most once (R:89-93) and
  raises `latestInteropRootTimestamp[chainId]` to the imported timestamp when it is larger
  (R:98-100);
* `append` (A:104-173) checks the same settlement layer against `L1_CHAIN_ID` (A:110) and reads
  `latestInteropRootTimestamp` under it (A:120-125).

The flow id is a hash of the whole preimage, `deadline` and `settlementLayerChainId` included:
`flowId = keccak256(abi.encode(preimage))` (A:355-379; `IAtomicInterop.sol:50-56`), recomputed by
both entry points (`_validateAndComputeFlowId` at A:109, `_checkFlowId` at A:217, A:348-353).  The
model keeps the hash abstract, so "the same flow" is stated on the preimage, and a statement keyed
on the flow id carries the case of two preimages with one hash.

## The code (the parts the model transcribes)

    function append(bytes32 _bundleHash, uint256 _lowNullifierIndex,
                    AtomicFlowPreimage calldata _flowPreimage) external onlyInteropCenter {   // A:104-108
        bytes32 flowId = _validateAndComputeFlowId(_flowPreimage);                           // A:109
        _checkSettlementLayerIsL1(_flowPreimage.settlementLayerChainId);                     // A:110
        ... expired-flow gate, above ...                                                     // A:120-125
        ... legIndex = first i with legBundleHashes[i] == _bundleHash, else
            ManagerCommittedBundleNotInFlow                                                  // A:130-140
        if (_flowPreimage.legSourceChainIds[legIndex] != block.chainid) revert ...;          // A:141-147
        for each i: legSourceChainId != block.chainid
                    && L2_BRIDGEHUB.baseTokenAssetId(legSourceChainId) == 0 → revert ...;     // A:152-160
        if (_state[flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted; // A:162-164
        _state[flowId][_bundleHash] = LegState.Committed;                                    // A:166
        (uint256 index, ) = IL2InteropCommitmentTree(commitmentTree())
            .insert(AtomicInteropProof.commitValue(flowId, _bundleHash), _lowNullifierIndex); // A:168-170
    }

    function authorizeRefund(AtomicFlow calldata _flow, uint256 _missingLegIndex,
                             ImtProof calldata _absence) external {                          // A:216
        _checkFlowId(_flow);                                                                 // A:217
        _checkSettlementLayerIsL1(_flow.preimage.settlementLayerChainId);                    // A:218
        if (_missingLegIndex >= preimage.legBundleHashes.length) revert ...;                 // A:224-226
        if (_absence.sourceChainId != preimage.legSourceChainIds[_missingLegIndex]) revert;  // A:227-230
        _checkLegSourceAllowed(missingLegChainId);                                           // A:231
        AtomicInteropProof.verifyTimeoutAbsence(_absence,
            commitValue(_flow.flowId, preimage.legBundleHashes[_missingLegIndex]),
            preimage.deadline, preimage.settlementLayerChainId);                             // A:233-234
        for each i: if (_state[flowId][legBundleHashes[i]] == Committed) set Revertable;     // A:238-246
    }

    function verifyTimeoutAbsence(...) internal view {                                       // P:77-82
        (slBlock, slChainId, l1BatchTimestamp) = _authenticateRoot(_absence, leafIndex);     // P:85-89
        if (slChainId != _expectedSlChainId) revert ProofSettlementLayerMismatch(...);       // P:90-92
        uint256 rootTimestamp = L2_INTEROP_ROOT_STORAGE.interopRoots(slChainId, slBlock).timestamp; // P:94
        if (rootTimestamp == 0) revert ProofSettlementLayerInteropRootNotImported(...);      // P:95-97
        if (rootTimestamp <= _deadline) revert ProofInteropRootNotAfterDeadline(...);        // P:98-100
        begin branch: l1BatchTimestamp <= _deadline reverts;                                 // P:103-106
        end branch:   l1BatchTimestamp > _deadline reverts; _verifyLastBatchInRoot(...);    // P:107-114
        IndexedMerkleTree.verifyNonInclusion(...) must hold;                                 // P:116-123
    }

    function _addInteropRoot(chainId, blockOrBatchNumber, timestamp, sides) private {        // R:70-75
        sides.length != 1 → SidesLengthNotOne; sides[0] == 0 → MessageRootIsZero;            // R:77-82
        timestamp == 0 → InteropRootTimestampIsZero;                                         // R:85-87
        storedInteropRoots[chainId][blockOrBatchNumber].root != 0 → InteropRootAlreadyExists; // R:89-91
        storedInteropRoots[chainId][blockOrBatchNumber] = StoredInteropRoot(sides[0], timestamp); // R:93
        if (timestamp > latestInteropRootTimestamp[chainId])
            latestInteropRootTimestamp[chainId] = timestamp;                                 // R:98-100
    }

## Every writer of the modelled state (checked against `b17415d20`)

* `_state` (A:61): `append` (A:166), `authorizeRefund` (A:244) and `claimRefund` (A:260); no
  other assignment exists (`grep -n '_state\[' atomic-interop/AtomicFlowManager.sol`).
* `L1_CHAIN_ID` (A:65): `initL2` (A:76-85), `onlyUpgrader`, and only while it is zero.
* `storedInteropRoots` and `latestInteropRootTimestamp` (R:32, R:36): `_addInteropRoot` only,
  reached from `addSingleInteropRoot` (R:50-52) and `addInteropRootsInBatch` (R:56-68), both
  `onlyCallFromBootloader` (R:20-25).  Outside `dev-contracts/test/`, `latestInteropRootTimestamp`
  has one reader, A:120.  No contract inherits `AtomicFlowManager` or `L2InteropRootStorage`.
* The commitment tree is written by `insert`, which reverts for any caller but the manager
  (`atomic-interop/L2InteropCommitmentTree.sol:51-54`), and by its own `initL2` (`:45`,
  `onlyUpgrader`), which seeds it once at genesis.

`requireFlowFinalized` (A:176-213) is `view`.  `claimRefund`'s `_recoverBundle` (A:292-325) calls
the asset router; a call it makes into these entry points runs after the claim's write (A:260), so
it is the step sequence "claim, then that call" (the same argument as `InteropCenter`'s
`Specs/Dispatch.lean`).  The external calls of `authorizeRefund` are `view` calls.

## What is modelled

* **One chain's state** (`ChainState`): the manager's `_state` (reusing
  `Contracts.AtomicFlowManager.Manager`) and `L1_CHAIN_ID`, the commitment tree as an abstract
  state of type `τ`, and the root storage's two mappings (`RootStore`, transcribed from
  `L2InteropRootStorage.sol` R:32-103 at `b17415d20`; here
  with `ℕ` numbers and the maximum as a switch).
* **Every entry point that writes it**, with its guards in source order (`ChainCall`, `execCall`):
  `initL2`, `append`, `authorizeRefund`, `claimRefund`, `addSingleInteropRoot`,
  `addInteropRootsInBatch`, plus the view `requireFlowFinalized` as a call that changes nothing.
  A revert is `none` (for `append`, an `AppendError` naming the revert).  `ChainRun` is any finite
  sequence of successful calls, by any caller, with any arguments, in any order.
* **`append`'s revert reasons**, in source order (`AppendError`), because the claim is about
  which check fires.
* **`verifyTimeoutAbsence`'s storage reads, literally** (`TimeoutAbsenceVerified`): the settlement
  layer check, both timestamp checks against the stored root, and the branch comparisons.
* **Four checks are switches** (`Checks`): the expired-flow gate (A:120-125), the maximum in the
  root storage (R:98-100), the proof's settlement-layer check (P:90-92) and the strictness of the
  root-timestamp check (P:98-100).  The deployed code has all four (`deployed`); each mutant turns
  one off.  The mutants are not the contract; the countermodels use them.

## Modelling choices

* **Hashes and the commitment tree are parameters** (`ChainParams`): `flowHash` is
  `keccak256(abi.encode(preimage))` (A:378), `commitValue` is `AtomicInteropProof.commitValue`
  (P:34-36), and `treeInsert` is the tree's `insert` (deterministic in its state, value and hint).
  No positive result takes a premise on any of them.  Where a conclusion is keyed on the flow id,
  the case of two different preimages with one hash is a disjunct naming both preimages.
* **The proof checks that do not read the root storage's timestamps are oracles**:
  `rootAuthenticated` is `_authenticateRoot` (P:155-189: the depth check, the inclusion proof
  against `interopRoots(...).root`, which is why it receives the root storage, and the final-node
  rejection); `lastBatchInRoot` is `_verifyLastBatchInRoot` (P:113, P:130-143); `absent` is the
  IMT non-inclusion check (P:116-123).  The words `_authenticateRoot` and
  `readSettlementLayerReference` parse from `settlementProof` (`slBlock`, `slChainId`,
  `l1BatchTimestamp`, P:183-188) are fields of `AbsenceProof`; everything else in the proof is
  `rest`.  The results hold for every oracle.
* **Other contracts' storage read by these calls is a per-call input**: `L2_BRIDGEHUB.baseTokenAssetId`
  (A:157, as `registered`) and `L2_BRIDGEHUB.isPeerAllowed` (A:340, as `peerAllowed`) can be
  anything at each call, and so can whether `claimRefund`'s decoding and recovery return
  (`recoveryReturns`) and whether `requireFlowFinalized` passes.  Callers are inputs; the
  addresses they are compared with are parameters.
* **Numbers are `ℕ`** (chain ids, block numbers, timestamps, the `uint64` deadline, roots);
  only comparisons and equalities are used, so no overflow arises.  Flow ids and bundle hashes are
  `UInt256` (`bytes32`), compared as unsigned integers, as Solidity compares `bytes32`.
* **Fresh storage** (`RootStore.fresh`, `Contracts.AtomicFlowManager.empty`) is all zero.  The
  results that need a start state assume only `LatestBoundsStored`, which every storage with
  all stored timestamps zero satisfies.  That includes, argued from source and not modelled, the
  storage an upgrade from v31 leaves: R:29-31 says the mapping was empty then, an entry carried
  over in the old `bytes32` slot would read with a zero timestamp (the struct keeps `root` in that
  slot), and `latestInteropRootTimestamp` is a mapping appended after it (R:35), so it starts
  at zero.

## Not modelled

Events; gas; ABI decoding (calldata is given as decoded fields); the `bytes1`/`uint64` widths;
the tree's internals and its `initL2`; who the bootloader is and what it imports (any import
sequence is a run); other chains (their managers, trees and views of the clock); upgrades of
either contract by the complex upgrader (`OPS-CONFIG`).
-/

namespace Contracts.AtomicFlowManager.RefundClosesAppend

/-- `bytes32` words: flow ids, bundle hashes, commit values. -/
abbrev Word := UInt256

/-- `ATOMIC_FLOW_PREIMAGE_VERSION = 0x01` (`IAtomicInterop.sol:91`). -/
def ATOMIC_FLOW_PREIMAGE_VERSION : ℕ := 1

/-- `MAX_ATOMIC_FLOW_LEGS = 8` (`IAtomicInterop.sol:99`). -/
def MAX_ATOMIC_FLOW_LEGS : ℕ := 8

/-! ## Which checks are present -/

/-- The four checks the argument rests on, as switches.  `true` is the deployed code. -/
structure Checks where
  /-- `append`'s expired-flow gate (`A:120-125`). -/
  deadlineGate : Bool
  /-- `_addInteropRoot` raises the tracked timestamp only to a larger value (`R:98-100`).
  `false` is the mutant that stores the last imported timestamp. -/
  latestKeepsMax : Bool
  /-- `verifyTimeoutAbsence`'s `ProofSettlementLayerMismatch` check (`P:90-92`). -/
  proofSettlementLayerBound : Bool
  /-- `ProofInteropRootNotAfterDeadline` reverts on `rootTimestamp <= deadline` (`P:98-100`).
  `false` is the mutant that reverts only on `rootTimestamp < deadline`. -/
  rootStrictlyAfterDeadline : Bool

/-- The code at `b17415d20`: all four checks present. -/
def deployed : Checks := ⟨true, true, true, true⟩

/-- The mutant without the expired-flow gate (`A:120-125` deleted). -/
def withoutDeadlineGate : Checks := { deployed with deadlineGate := false }

/-- The mutant root storage that keeps the last imported timestamp instead of the maximum
(`R:98-100` replaced by `latestInteropRootTimestamp[chainId] = timestamp`). -/
def lastValueLatest : Checks := { deployed with latestKeepsMax := false }

/-- The mutant proof library without the settlement-layer check (`P:90-92` deleted). -/
def unboundProofSettlementLayer : Checks := { deployed with proofSettlementLayerBound := false }

/-- The mutant proof library whose root-timestamp check reverts only on `rootTimestamp < deadline`
(`P:98` with `<=` replaced by `<`). -/
def nonStrictRootTimestamp : Checks := { deployed with rootStrictlyAfterDeadline := false }

/-! ## `L2InteropRootStorage` -/

/-- `StoredInteropRoot` (`common/Messaging.sol:161-164`). -/
structure StoredRoot where
  /-- `bytes32 root`. -/
  root : ℕ
  /-- `uint256 timestamp`: the root's creation time on its settlement layer. -/
  timestamp : ℕ
deriving DecidableEq

/-- `InteropRoot` (`common/Messaging.sol:147-154`), the argument of both import entry points. -/
structure ImportedRoot where
  chainId : ℕ
  blockOrBatchNumber : ℕ
  timestamp : ℕ
  /-- `bytes32[] sides`; in this release exactly the root (`R:76-79`). -/
  sides : List ℕ
deriving DecidableEq

/-- The root storage's two mappings (`R:32`, `R:36`), as total functions (an unset slot is zero). -/
structure RootStore where
  /-- `storedInteropRoots[chainId][blockOrBatchNumber]`. -/
  storedInteropRoots : ℕ → ℕ → StoredRoot
  /-- `latestInteropRootTimestamp[chainId]`. -/
  latestInteropRootTimestamp : ℕ → ℕ

/-- Fresh storage: every slot zero. -/
def RootStore.fresh : RootStore where
  storedInteropRoots := fun _ _ => ⟨0, 0⟩
  latestInteropRootTimestamp := fun _ => 0

/-- The writes of `R:93-100`, with no guard checked: the pair is stored at the key and the chain's
tracked timestamp is raised to `timestamp` if it was below it (with `latestKeepsMax`), or set to
`timestamp` (without). -/
def RootStore.write (K : Checks) (R : RootStore) (chainId blockOrBatchNumber timestamp root : ℕ) :
    RootStore where
  storedInteropRoots := fun c b =>
    if c = chainId ∧ b = blockOrBatchNumber then ⟨root, timestamp⟩ else R.storedInteropRoots c b
  latestInteropRootTimestamp := fun c =>
    if c = chainId then
      (if K.latestKeepsMax = true then
        (if R.latestInteropRootTimestamp chainId < timestamp then timestamp
          else R.latestInteropRootTimestamp chainId)
      else timestamp)
    else R.latestInteropRootTimestamp c

/-- `_addInteropRoot` (`R:70-103`), guards in source order; `none` is a revert.  `sides.headD 0`
is `sides[0]`, read only after the length check. -/
def addInteropRoot (K : Checks) (R : RootStore) (chainId blockOrBatchNumber timestamp : ℕ)
    (sides : List ℕ) : Option RootStore :=
  if sides.length ≠ 1 then none                                              -- R:77 SidesLengthNotOne
  else if sides.headD 0 = 0 then none                                        -- R:80 MessageRootIsZero
  else if timestamp = 0 then none                                            -- R:85 InteropRootTimestampIsZero
  else if (R.storedInteropRoots chainId blockOrBatchNumber).root ≠ 0 then none -- R:89 InteropRootAlreadyExists
  else some (R.write K chainId blockOrBatchNumber timestamp (sides.headD 0)) -- R:93-100

/-- The loop of `addInteropRootsInBatch` (`R:57-67`): the roots in order, the whole call
reverting if one does. -/
def addInteropRoots (K : Checks) (R : RootStore) : List ImportedRoot → Option RootStore
  | [] => some R
  | r :: rs =>
    match addInteropRoot K R r.chainId r.blockOrBatchNumber r.timestamp r.sides with
    | none => none
    | some R' => addInteropRoots K R' rs

/-- **THE TRACKED TIMESTAMP BOUNDS EVERY STORED ONE.**  For every chain id, every stored
timestamp is at most `latestInteropRootTimestamp`.  This is the upper-bound half of the
interface's "the maximum creation timestamp over all roots imported for `chainId`"
(`IL2InteropRootStorage.sol:23-26`); the other half (the maximum is attained) is not used. -/
def LatestBoundsStored (R : RootStore) : Prop :=
  ∀ c b, (R.storedInteropRoots c b).timestamp ≤ R.latestInteropRootTimestamp c

/-! ## The flow preimage and the absence proof -/

/-- `AtomicFlowPreimage` (`IAtomicInterop.sol:50-56`). -/
structure FlowPreimage where
  /-- `bytes1 version`. -/
  version : ℕ
  /-- `uint64 deadline`: a settlement-layer timestamp. -/
  deadline : ℕ
  /-- `uint256 settlementLayerChainId`. -/
  settlementLayerChainId : ℕ
  /-- `bytes32[] legBundleHashes`. -/
  legBundleHashes : List Word
  /-- `uint256[] legSourceChainIds`. -/
  legSourceChainIds : List ℕ
deriving DecidableEq

/-- The four reverts of `_validateAndComputeFlowId` (`A:360-377`). -/
inductive PreimageError
  /-- `ManagerFlowPreimageVersionMismatch` (`A:361-363`). -/
  | versionMismatch
  /-- `ManagerTooManyLegs` (`A:367-369`). -/
  | tooManyLegs
  /-- `ManagerBundleHashesNotSorted` (`A:370-374`). -/
  | notSorted
  /-- `ManagerLegSourceChainIdsLengthMismatch` (`A:375-377`). -/
  | lengthMismatch
deriving DecidableEq

/-- The loop of `A:370-374` passes: every bundle hash is strictly above the one before it. -/
def strictlyAscending : List Word → Bool
  | a :: b :: t => decide (a < b) && strictlyAscending (b :: t)
  | _ => true

/-- `_validateAndComputeFlowId`'s checks (`A:360-377`), in source order: the first that fails,
or `none`.  On `none` the function returns `keccak256(abi.encode(preimage))` (`A:378`). -/
def preimageError? (p : FlowPreimage) : Option PreimageError :=
  if p.version ≠ ATOMIC_FLOW_PREIMAGE_VERSION then some .versionMismatch
  else if MAX_ATOMIC_FLOW_LEGS < p.legBundleHashes.length then some .tooManyLegs
  else if strictlyAscending p.legBundleHashes = false then some .notSorted
  else if p.legSourceChainIds.length ≠ p.legBundleHashes.length then some .lengthMismatch
  else none

/-- `ImtProof` (`IAtomicInterop.sol:28-37`), as far as `verifyTimeoutAbsence` reads it. -/
structure AbsenceProof where
  /-- `sourceChainId`. -/
  sourceChainId : ℕ
  /-- `provesAgainstBeginRoot`: the branch (`P:85-87`). -/
  provesAgainstBeginRoot : Bool
  /-- `slReference.settlementLayerChainId`, parsed from `settlementProof` (`P:183-187`). -/
  settlementLayerChainId : ℕ
  /-- `slReference.settlementLayerBatchNumber` (`slBlock`, `P:186`). -/
  settlementLayerBatchNumber : ℕ
  /-- `slReference.l1BatchTimestamp` (`P:188`). -/
  l1BatchTimestamp : ℕ
  /-- Every other word of the proof (`batchNumber`, `chainImtRoot`, the paths, the low leaf and
  its index); read only by the oracles. -/
  rest : ℕ
deriving DecidableEq

/-! ## Parameters and state -/

/-- One chain's constants, the hashes, the commitment tree's `insert`, and the proof checks that
the model does not transcribe (see the header). -/
structure ChainParams (τ : Type) where
  /-- `block.chainid`. -/
  chainId : ℕ
  /-- `L2_INTEROP_CENTER_ADDR`, the only caller `append` accepts (`A:88-93`, `A:278-280`). -/
  interopCenter : ℕ
  /-- `L2_COMPLEX_UPGRADER_ADDR`, the only caller `initL2` accepts (`A:68-73`). -/
  complexUpgrader : ℕ
  /-- `L2_BOOTLOADER_ADDRESS`, the only caller the imports accept (`R:20-25`). -/
  bootloader : ℕ
  /-- `keccak256(abi.encode(preimage))` (`A:378`). -/
  flowHash : FlowPreimage → Word
  /-- `AtomicInteropProof.commitValue(flowId, bundleHash)` (`P:34-36`). -/
  commitValue : Word → Word → Word
  /-- `IL2InteropCommitmentTree.insert(value, lowNullifierIndex)` from the tree's state (`A:170`);
  `none` is a revert. -/
  treeInsert : τ → Word → ℕ → Option τ
  /-- `_authenticateRoot` returns (`P:89`, `P:155-189`).  It reads `interopRoots(...).root`
  through `proveL2LeafInclusionShared`, so it receives the root storage. -/
  rootAuthenticated : RootStore → AbsenceProof → Bool
  /-- `_verifyLastBatchInRoot` returns (`P:113`, `P:130-143`). -/
  lastBatchInRoot : AbsenceProof → Bool
  /-- `IndexedMerkleTree.verifyNonInclusion` of the commit value holds (`P:116-123`). -/
  absent : AbsenceProof → Word → Bool

/-- One chain's modelled storage. -/
structure ChainState (τ : Type) where
  /-- `AtomicFlowManager._state` (`A:61`). -/
  legs : Manager
  /-- `AtomicFlowManager.L1_CHAIN_ID` (`A:65`); `0` until `initL2`. -/
  l1ChainId : ℕ
  /-- The commitment tree's state. -/
  tree : τ
  /-- `L2InteropRootStorage`'s storage. -/
  roots : RootStore

/-- Genesis: fresh manager and root storage, `L1_CHAIN_ID` unset, the tree in state `T₀`. -/
def genesis {τ : Type} (T₀ : τ) : ChainState τ :=
  ⟨Contracts.AtomicFlowManager.empty, 0, T₀, RootStore.fresh⟩

/-! ## `append` -/

/-- `append`'s reverts, in source order. -/
inductive AppendError
  /-- `ManagerNotInteropCenter` (`onlyInteropCenter`, `A:88-93`). -/
  | notInteropCenter
  /-- A revert of `_validateAndComputeFlowId` (`A:109`). -/
  | invalidPreimage (e : PreimageError)
  /-- `ManagerSettlementLayerNotL1` (`A:110`, `A:329-333`). -/
  | settlementLayerNotL1
  /-- `ManagerFlowDeadlinePassed(deadline, latestImportedRootTimestamp)` (`A:123-125`). -/
  | flowDeadlinePassed (deadline latest : ℕ)
  /-- `ManagerCommittedBundleNotInFlow` (`A:138-140`). -/
  | committedBundleNotInFlow
  /-- `ManagerCommittedLegSourceChainMismatch` (`A:141-147`). -/
  | committedLegSourceChainMismatch
  /-- `ManagerLegSourceChainNotRegistered` (`A:152-160`). -/
  | legSourceChainNotRegistered
  /-- `ManagerLegAlreadyCommitted` (`A:162-164`). -/
  | legAlreadyCommitted
  /-- The tree's `insert` reverted (`A:170`). -/
  | treeInsertReverted
deriving DecidableEq

/-- The leg index loop (`A:130-137`): the first index whose bundle hash is `b`. -/
def legIndexOf (hashes : List Word) (b : Word) : Option ℕ :=
  hashes.findIdx? (· == b)

/-- `append(_bundleHash, _lowNullifierIndex, _flowPreimage)` (`A:104-173`) called by `caller`,
with the Bridgehub's registration answer `registered` (`baseTokenAssetId(c) != 0`, `A:157`).
Checks in source order; the expired-flow gate only with `K.deadlineGate`. -/
def appendCall {τ : Type} (P : ChainParams τ) (K : Checks) (S : ChainState τ) (caller : ℕ)
    (registered : ℕ → Bool) (bundleHash : Word) (lowNullifierIndex : ℕ) (p : FlowPreimage) :
    Except AppendError (ChainState τ) :=
  if caller ≠ P.interopCenter then .error .notInteropCenter                       -- A:88-93
  else match preimageError? p with                                                -- A:109
  | some e => .error (.invalidPreimage e)
  | none =>
    if p.settlementLayerChainId ≠ S.l1ChainId then .error .settlementLayerNotL1  -- A:110
    else if K.deadlineGate = true ∧
        p.deadline < S.roots.latestInteropRootTimestamp p.settlementLayerChainId then  -- A:120-123
      .error (.flowDeadlinePassed p.deadline
        (S.roots.latestInteropRootTimestamp p.settlementLayerChainId))           -- A:124
    else match legIndexOf p.legBundleHashes bundleHash with                       -- A:130-137
    | none => .error .committedBundleNotInFlow                                    -- A:138-140
    | some i =>
      if p.legSourceChainIds.getD i 0 ≠ P.chainId then
        .error .committedLegSourceChainMismatch                                   -- A:141-147
      else if (p.legSourceChainIds.all fun c => c == P.chainId || registered c) = false then
        .error .legSourceChainNotRegistered                                       -- A:152-160
      else if S.legs.legState (P.flowHash p) bundleHash ≠ .Unset then
        .error .legAlreadyCommitted                                               -- A:162-164
      else match P.treeInsert S.tree (P.commitValue (P.flowHash p) bundleHash)
          lowNullifierIndex with                                                  -- A:168-170
      | none => .error .treeInsertReverted
      | some T => .ok { S with legs := S.legs.set (P.flowHash p) bundleHash .Committed,  -- A:166
                               tree := T }

/-! ## `authorizeRefund` -/

/-- `_checkLegSourceAllowed` (`A:338-344`) passes for leg source `c`: `c` is this chain, or the
Bridgehub allows it as a peer (`peerAllowed`). -/
def LegSourceAllowed {τ : Type} (P : ChainParams τ) (peerAllowed : ℕ → Bool) (c : ℕ) : Prop :=
  c = P.chainId ∨ peerAllowed c = true

instance {τ : Type} (P : ChainParams τ) (peerAllowed : ℕ → Bool) (c : ℕ) :
    Decidable (LegSourceAllowed P peerAllowed c) := by
  unfold LegSourceAllowed; infer_instance

/-- **`verifyTimeoutAbsence(a, value, deadline, expectedSl)` RETURNS** (`P:77-124`).  The
storage reads and comparisons are literal; the cryptographic checks are the oracles. -/
def TimeoutAbsenceVerified {τ : Type} (P : ChainParams τ) (K : Checks) (R : RootStore)
    (a : AbsenceProof) (value : Word) (deadline expectedSl : ℕ) : Prop :=
  -- `_authenticateRoot` (`P:89`)
  P.rootAuthenticated R a = true
  -- `ProofSettlementLayerMismatch` (`P:90-92`)
  ∧ (K.proofSettlementLayerBound = true → a.settlementLayerChainId = expectedSl)
  -- `ProofSettlementLayerInteropRootNotImported` (`P:94-97`)
  ∧ (R.storedInteropRoots a.settlementLayerChainId a.settlementLayerBatchNumber).timestamp ≠ 0
  -- `ProofInteropRootNotAfterDeadline` (`P:98-100`)
  ∧ (if K.rootStrictlyAfterDeadline = true then
        deadline < (R.storedInteropRoots a.settlementLayerChainId a.settlementLayerBatchNumber).timestamp
      else
        deadline ≤ (R.storedInteropRoots a.settlementLayerChainId a.settlementLayerBatchNumber).timestamp)
  -- the branch conditions (`P:103-114`)
  ∧ (if a.provesAgainstBeginRoot = true then deadline < a.l1BatchTimestamp
      else a.l1BatchTimestamp ≤ deadline ∧ P.lastBatchInRoot a = true)
  -- `ProofNonInclusionFailed` (`P:116-123`)
  ∧ P.absent a value = true

instance {τ : Type} (P : ChainParams τ) (K : Checks) (R : RootStore) (a : AbsenceProof)
    (value : Word) (deadline expectedSl : ℕ) :
    Decidable (TimeoutAbsenceVerified P K R a value deadline expectedSl) := by
  unfold TimeoutAbsenceVerified; infer_instance

/-- The marking loop of `authorizeRefund` (`A:238-246`): over the flow's bundle hashes in order,
each leg that is `Committed` becomes `Revertable`; the others are skipped. -/
def markCommittedRevertable (M : Manager) (flowId : Word) : List Word → Manager
  | [] => M
  | h :: hs =>
    markCommittedRevertable
      (if M.legState flowId h = .Committed then M.set flowId h .Revertable else M) flowId hs

/-- `authorizeRefund(AtomicFlow(flowId, p), i, a)` (`A:216-247`), with the Bridgehub's peer answer
`peerAllowed` (`A:340`).  `none` is a revert.  `getD` reads an index the earlier checks put in
range (`A:224-226` and `A:375-377`). -/
def authorizeRefundCall {τ : Type} (P : ChainParams τ) (K : Checks) (S : ChainState τ)
    (peerAllowed : ℕ → Bool) (flowId : Word) (p : FlowPreimage) (i : ℕ) (a : AbsenceProof) :
    Option (ChainState τ) :=
  if preimageError? p ≠ none then none                                     -- A:217, A:349
  else if P.flowHash p ≠ flowId then none                                  -- A:350-352 ManagerFlowIdMismatch
  else if p.settlementLayerChainId ≠ S.l1ChainId then none                 -- A:218
  else if p.legBundleHashes.length ≤ i then none                           -- A:224-226
  else if a.sourceChainId ≠ p.legSourceChainIds.getD i 0 then none         -- A:227-230
  else if ¬ LegSourceAllowed P peerAllowed (p.legSourceChainIds.getD i 0) then none  -- A:231
  else if ¬ TimeoutAbsenceVerified P K S.roots a
      (P.commitValue flowId (p.legBundleHashes.getD i 0)) p.deadline
      p.settlementLayerChainId then none                                   -- A:233-234
  else some { S with legs := markCommittedRevertable S.legs flowId p.legBundleHashes }  -- A:238-246

/-! ## The other entry points -/

/-- `initL2(_l1ChainId)` (`A:76-85`) called by `caller`. -/
def initL2Call {τ : Type} (P : ChainParams τ) (S : ChainState τ) (caller l1 : ℕ) :
    Option (ChainState τ) :=
  if caller ≠ P.complexUpgrader then none                                  -- A:68-73 onlyUpgrader
  else if S.l1ChainId ≠ 0 then none                                        -- A:77-79 ManagerAlreadyInitialized
  else if l1 = 0 then none                                                 -- A:81-83 ManagerL1ChainIdZero
  else some { S with l1ChainId := l1 }                                     -- A:84

/-- `claimRefund(_flowId, _bundle)` (`A:250-265`) for the bundle whose hash is `bundleHash`
(`A:252`).  `recoveryReturns` is whether decoding (`A:251`) and `_recoverBundle` (`A:262`)
return without reverting. -/
def claimRefundCall {τ : Type} (S : ChainState τ) (flowId bundleHash : Word)
    (recoveryReturns : Bool) : Option (ChainState τ) :=
  if S.legs.legState flowId bundleHash ≠ .Revertable then none             -- A:254-257
  else if recoveryReturns = false then none                                -- A:251, A:262
  else some { S with legs := S.legs.set flowId bundleHash .Reverted }      -- A:260

/-- `addSingleInteropRoot(r)` (`R:50-52`) called by `caller`. -/
def addSingleInteropRootCall {τ : Type} (P : ChainParams τ) (K : Checks) (S : ChainState τ)
    (caller : ℕ) (r : ImportedRoot) : Option (ChainState τ) :=
  if caller ≠ P.bootloader then none                                       -- R:20-25
  else (addInteropRoot K S.roots r.chainId r.blockOrBatchNumber r.timestamp r.sides).map
    fun R => { S with roots := R }

/-- `addInteropRootsInBatch(rs)` (`R:56-68`) called by `caller`: all or nothing. -/
def addInteropRootsInBatchCall {τ : Type} (P : ChainParams τ) (K : Checks) (S : ChainState τ)
    (caller : ℕ) (rs : List ImportedRoot) : Option (ChainState τ) :=
  if caller ≠ P.bootloader then none                                       -- R:20-25
  else (addInteropRoots K S.roots rs).map fun R => { S with roots := R }

/-! ## Runs -/

/-- One external call, with its arguments and the other contracts' answers it reads. -/
inductive ChainCall
  /-- `AtomicFlowManager.initL2(l1)` by `caller`. -/
  | initL2 (caller l1 : ℕ)
  /-- `AtomicFlowManager.append(bundleHash, lowNullifierIndex, preimage)` by `caller`. -/
  | append (caller : ℕ) (registered : ℕ → Bool) (bundleHash : Word) (lowNullifierIndex : ℕ)
      (preimage : FlowPreimage)
  /-- `AtomicFlowManager.authorizeRefund(AtomicFlow(flowId, preimage), missingLegIndex, absence)`;
  permissionless. -/
  | authorizeRefund (peerAllowed : ℕ → Bool) (flowId : Word) (preimage : FlowPreimage)
      (missingLegIndex : ℕ) (absence : AbsenceProof)
  /-- `AtomicFlowManager.claimRefund(flowId, bundle)`; permissionless. -/
  | claimRefund (flowId bundleHash : Word) (recoveryReturns : Bool)
  /-- `AtomicFlowManager.requireFlowFinalized(...)`: a view; it passes or reverts. -/
  | requireFlowFinalized (passes : Bool)
  /-- `L2InteropRootStorage.addSingleInteropRoot(r)` by `caller`. -/
  | addSingleInteropRoot (caller : ℕ) (r : ImportedRoot)
  /-- `L2InteropRootStorage.addInteropRootsInBatch(rs)` by `caller`. -/
  | addInteropRootsInBatch (caller : ℕ) (rs : List ImportedRoot)

/-- One call; `none` is a revert. -/
def execCall {τ : Type} (P : ChainParams τ) (K : Checks) (S : ChainState τ) :
    ChainCall → Option (ChainState τ)
  | .initL2 caller l1 => initL2Call P S caller l1
  | .append caller registered b idx p => (appendCall P K S caller registered b idx p).toOption
  | .authorizeRefund peer flowId p i a => authorizeRefundCall P K S peer flowId p i a
  | .claimRefund flowId b ok => claimRefundCall S flowId b ok
  | .requireFlowFinalized passes => if passes = true then some S else none
  | .addSingleInteropRoot caller r => addSingleInteropRootCall P K S caller r
  | .addInteropRootsInBatch caller rs => addInteropRootsInBatchCall P K S caller rs

/-- A run: the calls in order, every one successful.  Any caller, any arguments, any order. -/
inductive ChainRun {τ : Type} (P : ChainParams τ) (K : Checks) :
    ChainState τ → List ChainCall → ChainState τ → Prop
  | nil {S : ChainState τ} : ChainRun P K S [] S
  | cons {S S₁ S₂ : ChainState τ} {c : ChainCall} {cs : List ChainCall} :
      execCall P K S c = some S₁ → ChainRun P K S₁ cs S₂ → ChainRun P K S (c :: cs) S₂

/-- The calls run one after another; `none` if one reverts.  `ChainRun` relates exactly the
states this returns (`Properties.ChainRunIffRunCalls`). -/
def runCalls {τ : Type} (P : ChainParams τ) (K : Checks) :
    ChainState τ → List ChainCall → Option (ChainState τ)
  | S, [] => some S
  | S, c :: cs =>
    match execCall P K S c with
    | none => none
    | some S' => runCalls P K S' cs

/-- `c` is an `append` call for leg `bundleHash` of flow id `flowId` with preimage `q`: its bundle
hash is `bundleHash` and `flowHash q = flowId`.  (In a run every call succeeds, so there such a
call committed that leg.) -/
def ChainCall.AppendsLeg {τ : Type} (P : ChainParams τ) (c : ChainCall) (flowId bundleHash : Word)
    (q : FlowPreimage) : Prop :=
  ∃ caller registered idx, c = .append caller registered bundleHash idx q ∧ P.flowHash q = flowId

/-- `c` is a `claimRefund` of leg `(flowId, bundleHash)`. -/
def ChainCall.isClaimOf (flowId bundleHash : Word) : ChainCall → Bool
  | .claimRefund f b _ => decide (f = flowId) && decide (b = bundleHash)
  | _ => false

end Contracts.AtomicFlowManager.RefundClosesAppend
