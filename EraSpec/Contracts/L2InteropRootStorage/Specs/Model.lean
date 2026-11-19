import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `L2InteropRootStorage` — imported settlement-layer roots, write-once, admitted by `ok`

Source: `l1-contracts/contracts/interop/L2InteropRootStorage.sol` at era-contracts
`draft/v0.35.0` head `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, with
`interop/IL2InteropRootStorage.sol`, `interop/L2MessageVerification.sol`, `common/Messaging.sol` and
`atomic-interop/libraries/AtomicInteropProof.sol` from the same tree. A bare `:N` is a line of
`L2InteropRootStorage.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.L2InteropRootStorage.Properties.Model` and are proved in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Model`.

## Relation to the canonical model

`Specs/Storage.lean` is the canonical model of this contract (both mappings, callers, `uint256`
words). This topic is a coarser view of the same code that the protocol topic
`Protocol/InteropAtomicity/Specs/SettlementRoots.lean` instantiates: `storedInteropRoots` alone,
keys and timestamps in `ℕ`, and an admission predicate `ok` on the imported tuples.
`Properties/Refinement.lean` proves that every successful call of the canonical model, read
through `toModel` (`Specs/Refinement.lean`), is a `Step ok` of this model for any `ok` its imports
meet, so the results here hold of the canonical model's runs. This topic was first written at `c67894b9`, where the
contract has no `latestInteropRootTimestamp`; the checks and the write it models are the same at
`b17415d20`.

## The code

    // storedInteropRoots[chainId][blockOrBatchNumber] = StoredInteropRoot{root, timestamp}   (:32)
    function addSingleInteropRoot(InteropRoot calldata interopRoot)
        external onlyCallFromBootloader                                                  // :50-52
    function addInteropRootsInBatch(InteropRoot[] calldata interopRootsInput)
        external onlyCallFromBootloader                                                  // :56-68
    {   for (uint256 i; i < amountOfRoots; ++i) _addInteropRoot(...); }

    function _addInteropRoot(chainId, blockOrBatchNumber, timestamp, sides) private {   // :70-103
        if (sides.length != 1) revert SidesLengthNotOne();                               // :77-79
        if (sides[0] == bytes32(0)) revert MessageRootIsZero();                          // :80-82
        if (timestamp == 0) revert InteropRootTimestampIsZero();                         // :85-87
        if (storedInteropRoots[chainId][blockOrBatchNumber].root != bytes32(0))
            revert InteropRootAlreadyExists();                                           // :89-91
        storedInteropRoots[chainId][blockOrBatchNumber] =
            StoredInteropRoot({root: sides[0], timestamp: timestamp});                   // :93
        if (timestamp > latestInteropRootTimestamp[chainId])
            latestInteropRootTimestamp[chainId] = timestamp;                             // :98-100
    }

The two readers the interop gates use:

* inclusion (`L2MessageVerification.sol:33-38`): a final proof node is accepted iff
  `interopRoots(chainId, n).root == batchSettlementRoot && root != 0` — the timestamp is not read;
* the timeout path (`AtomicInteropProof.sol:94-100`): `rootTimestamp = interopRoots(slChainId,
  slBlock).timestamp`; revert `ProofSettlementLayerInteropRootNotImported` if it is `0`, and
  `ProofInteropRootNotAfterDeadline` if it is `<= deadline`.

## Inventory

`storedInteropRoots` has one writer, :93, behind the four checks above, reached only through the
two `onlyCallFromBootloader` entry points (:20-25, :50, :56). A batch import is one call: if any
element fails a check, the call reverts and none of its writes persist (`VM-REVERT`).

## Modelling choices

* **`latestInteropRootTimestamp` is left out.** No check of the contract reads it (:98-100 is its
  only use), so dropping it leaves the behaviour on `storedInteropRoots` unchanged.
* **Imports are admitted by a predicate** `ok` on the imported tuple. For the contract alone
  `ok` is anything (`fun _ => True`); `Protocol/InteropAtomicity/Specs/SettlementRoots.lean`
  instantiates it with the settlement layer's Executor check (`AcceptedInRun`), which the
  importing L2 batch must pass when it executes on the settlement layer. The contract itself
  does not check `ok`: it is a premise about which imports a run contains.
* **Callers are not modelled.** Both entry points are `onlyCallFromBootloader`; every step is a
  bootloader call.
* **A revert is the absence of a step.** `AddsAll` is the batch entry point's loop: it exists only
  when every element passes, which is the all-or-nothing behaviour of one reverting call
  (`VM-REVERT`).
* **Numbers are `ℕ`.** `blockOrBatchNumber` and `timestamp` are `uint256` in the source.
* **Events are omitted** (:102).
* **Storage from earlier versions.** The source comment (:29-31) says the mapping was empty at the
  v31 upgrade (the v31 value type was a bare `bytes32`, so a carried-over entry would read as
  `(root, 0)`). The model's runs start from any storage; the results that need the clean start say
  `empty`.
-/

namespace Contracts.L2InteropRootStorage

/-- `bytes32` words. -/
abbrev Word := UInt256

/-- Chain ids. -/
abbrev ChainId := UInt256

/-- `StoredInteropRoot` (`Messaging.sol:161-164`). -/
structure Stored where
  /-- `root`; `0` is "nothing imported". -/
  root : Word
  /-- `timestamp`: the root's creation time on its settlement layer. -/
  ts : ℕ
deriving DecidableEq

/-- `InteropRoot` (`Messaging.sol:147-154`), one imported tuple. -/
structure RootIn where
  chainId : ChainId
  blockOrBatchNumber : ℕ
  ts : ℕ
  /-- In this release, exactly the root (:76-79). -/
  sides : List Word
deriving DecidableEq

/-- The contract's storage. -/
structure State where
  /-- `storedInteropRoots` (:32); default `(0, 0)`. -/
  entries : ChainId → ℕ → Stored

/-- Fresh storage. -/
def empty : State := ⟨fun _ _ => ⟨0, 0⟩⟩

/-- The checks of `_addInteropRoot` for tuple `x` with root `r` (:77-91). -/
structure AddGuard (st : State) (x : RootIn) (r : Word) : Prop where
  /-- `SidesLengthNotOne` (:77-79). -/
  sides : x.sides = [r]
  /-- `MessageRootIsZero` (:80-82). -/
  nonzero : r ≠ 0
  /-- `InteropRootTimestampIsZero` (:85-87). -/
  tsNonzero : x.ts ≠ 0
  /-- `InteropRootAlreadyExists` (:89-91). -/
  fresh : (st.entries x.chainId x.blockOrBatchNumber).root = 0

/-- The write at :93. -/
def State.write (st : State) (x : RootIn) (r : Word) : State :=
  ⟨Function.update st.entries x.chainId
    (Function.update (st.entries x.chainId) x.blockOrBatchNumber ⟨r, x.ts⟩)⟩

/-- `addInteropRootsInBatch`'s loop (:59-66) succeeds from `st` on the tuples `xs` and ends in
`st'`: each tuple is admitted and passes its checks against the storage the earlier ones left. -/
inductive AddsAll (ok : RootIn → Prop) : State → List RootIn → State → Prop
  | nil {st : State} : AddsAll ok st [] st
  | cons {st st' : State} {x : RootIn} {xs : List RootIn} (r : Word) :
      ok x → AddGuard st x r → AddsAll ok (st.write x r) xs st' → AddsAll ok st (x :: xs) st'

/-- One bootloader call that changes the storage. -/
inductive Step (ok : RootIn → Prop) : State → State → Prop
  /-- `addSingleInteropRoot` (:50-52). -/
  | single {st : State} (x : RootIn) (r : Word) :
      ok x → AddGuard st x r → Step ok st (st.write x r)
  /-- `addInteropRootsInBatch` (:56-68), all or nothing. -/
  | batch {st st' : State} (xs : List RootIn) : AddsAll ok st xs st' → Step ok st st'

/-- Reachability. -/
inductive Reach (ok : RootIn → Prop) : State → State → Prop
  | refl {st : State} : Reach ok st st
  | tail {st st' st'' : State} : Reach ok st st' → Step ok st' st'' → Reach ok st st''

/-! ## The two gates' reads -/

/-- `L2MessageVerification._proveL2LeafInclusionRecursive`'s final-node check
(`L2MessageVerification.sol:37-38`): root `x` is accepted for `(c, n)`. -/
def State.InclusionRootAccepts (st : State) (c : ChainId) (n : ℕ) (x : Word) : Prop :=
  (st.entries c n).root = x ∧ (st.entries c n).root ≠ 0

/-- `verifyTimeoutAbsence`'s root read passes for settlement layer `sl`, block `n` and deadline `D`
(`AtomicInteropProof.sol:94-100`): the timestamp is imported (`≠ 0`) and after the deadline. -/
def State.TimeoutRootPasses (st : State) (sl : ChainId) (n D : ℕ) : Prop :=
  (st.entries sl n).ts ≠ 0 ∧ D < (st.entries sl n).ts

end Contracts.L2InteropRootStorage
