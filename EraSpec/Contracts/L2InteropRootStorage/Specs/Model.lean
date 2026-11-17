import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `L2InteropRootStorage` — imported settlement-layer roots, write-once

Source: `l1-contracts/contracts/interop/L2InteropRootStorage.sol` in the pinned era-contracts tree
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), with `interop/IL2InteropRootStorage.sol`,
`interop/L2MessageVerification.sol`, `common/Messaging.sol` and
`atomic-interop/libraries/AtomicInteropProof.sol` from the same tree. A bare `:N` is a line of
`L2InteropRootStorage.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.L2InteropRootStorage.Properties.Model` and are proved in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.Model`.

## The code

    // storedInteropRoots[chainId][blockOrBatchNumber] = StoredInteropRoot{root, timestamp}   (:40)
    function addSingleInteropRoot(InteropRoot calldata interopRoot)
        external onlyCallFromBootloader                                                  // :58
    function addInteropRootsInBatch(InteropRoot[] calldata interopRootsInput)
        external onlyCallFromBootloader                                                  // :64-76
    {   for (uint256 i; i < amountOfRoots; ++i) _addInteropRoot(...); }

    function _addInteropRoot(chainId, blockOrBatchNumber, timestamp, sides) private {   // :78-106
        if (sides.length != 1) revert SidesLengthNotOne();                               // :85-87
        if (sides[0] == bytes32(0)) revert MessageRootIsZero();                          // :88-90
        if (timestamp == 0) revert InteropRootTimestampIsZero();                         // :93-95
        if (storedInteropRoots[chainId][blockOrBatchNumber].root != bytes32(0))
            revert InteropRootAlreadyExists();                                           // :98-100
        storedInteropRoots[chainId][blockOrBatchNumber] =
            StoredInteropRoot({root: sides[0], timestamp: timestamp});                   // :103
    }

The two readers the interop gates use:

* inclusion (`L2MessageVerification.sol:29-33`): a final proof node is accepted iff
  `interopRoots(chainId, n).root == batchSettlementRoot && root != 0` — the timestamp is not read;
* the timeout path (`AtomicInteropProof.sol:171-179`): `rootTimestamp = interopRoots(slChainId,
  slBlock).timestamp`; revert `ProofSettlementLayerInteropRootNotImported` if it is `0`, and
  `ProofInteropRootNotAfterDeadline` if it is `<= deadline`.

## Inventory

`storedInteropRoots` has one writer, :103, behind the four checks above, reached only through the
two `onlyCallFromBootloader` entry points (:20-25, :58, :64). A batch import is one call: if any
element fails a check, the call reverts and none of its writes persist (`VM-REVERT`).

## Modelling choices

* **Imports are admitted by a predicate** `ok` on the imported tuple. For the contract alone
  `ok` is anything; the protocol instantiates it with the settlement layer's Executor check
  (`Protocol/InteropAtomicity/Specs/AggregatesWeak.lean`), which is what an L2 batch must pass to
  settle.
* **A revert is the absence of a step.** `AddsAll` is the batch entry point's loop: it exists only
  when every element passes, which is the all-or-nothing behaviour.
* **Numbers are `ℕ`.** `blockOrBatchNumber` and `timestamp` are `uint256` in the source.
* **Events are omitted** (:105).
* **Storage from earlier versions.** The NatSpec (:35-39) says no roots were recorded before this
  version (the v31 value type was a bare `bytes32`, so a carried-over entry would read as
  `(root, 0)`). The model's runs start from any storage; the results that need the clean start say
  `empty`.
-/

namespace Contracts.L2InteropRootStorage

/-- `bytes32` words. -/
abbrev Word := UInt256

/-- Chain ids. -/
abbrev ChainId := UInt256

/-- `StoredInteropRoot` (`Messaging.sol:170-173`). -/
structure Stored where
  /-- `root`; `0` is "nothing imported". -/
  root : Word
  /-- `timestamp`: the root's creation time on its settlement layer. -/
  ts : ℕ
deriving DecidableEq

/-- `InteropRoot` (`Messaging.sol:150-157`), one imported tuple. -/
structure RootIn where
  chainId : ChainId
  blockOrBatchNumber : ℕ
  ts : ℕ
  /-- In this release, exactly the root (:52, :84-87). -/
  sides : List Word
deriving DecidableEq

/-- The contract's storage. -/
structure State where
  /-- `storedInteropRoots` (:40); default `(0, 0)`. -/
  entries : ChainId → ℕ → Stored

/-- Fresh storage. -/
def empty : State := ⟨fun _ _ => ⟨0, 0⟩⟩

/-- The checks of `_addInteropRoot` for tuple `x` with root `r` (:85-100). -/
structure AddGuard (st : State) (x : RootIn) (r : Word) : Prop where
  /-- `SidesLengthNotOne` (:85-87). -/
  sides : x.sides = [r]
  /-- `MessageRootIsZero` (:88-90). -/
  nonzero : r ≠ 0
  /-- `InteropRootTimestampIsZero` (:93-95). -/
  tsNonzero : x.ts ≠ 0
  /-- `InteropRootAlreadyExists` (:98-100). -/
  fresh : (st.entries x.chainId x.blockOrBatchNumber).root = 0

/-- The write at :103. -/
def State.write (st : State) (x : RootIn) (r : Word) : State :=
  ⟨Function.update st.entries x.chainId
    (Function.update (st.entries x.chainId) x.blockOrBatchNumber ⟨r, x.ts⟩)⟩

/-- `addInteropRootsInBatch`'s loop (:66-75) succeeds from `st` on the tuples `xs` and ends in
`st'`: each tuple is admitted and passes its checks against the storage the earlier ones left. -/
inductive AddsAll (ok : RootIn → Prop) : State → List RootIn → State → Prop
  | nil {st : State} : AddsAll ok st [] st
  | cons {st st' : State} {x : RootIn} {xs : List RootIn} (r : Word) :
      ok x → AddGuard st x r → AddsAll ok (st.write x r) xs st' → AddsAll ok st (x :: xs) st'

/-- One bootloader call that changes the storage. -/
inductive Step (ok : RootIn → Prop) : State → State → Prop
  /-- `addSingleInteropRoot` (:58-60). -/
  | single {st : State} (x : RootIn) (r : Word) :
      ok x → AddGuard st x r → Step ok st (st.write x r)
  /-- `addInteropRootsInBatch` (:64-76), all or nothing. -/
  | batch {st st' : State} (xs : List RootIn) : AddsAll ok st xs st' → Step ok st st'

/-- Reachability. -/
inductive Reach (ok : RootIn → Prop) : State → State → Prop
  | refl {st : State} : Reach ok st st
  | tail {st st' st'' : State} : Reach ok st st' → Step ok st' st'' → Reach ok st st''

/-! ## The two gates' reads -/

/-- `L2MessageVerification._proveL2LeafInclusionRecursive`'s final-node check
(`L2MessageVerification.sol:31-32`): root `x` is accepted for `(c, n)`. -/
def State.InclusionRootAccepts (st : State) (c : ChainId) (n : ℕ) (x : Word) : Prop :=
  (st.entries c n).root = x ∧ (st.entries c n).root ≠ 0

/-- `verifyTimeoutAbsence`'s root read passes for settlement layer `sl`, block `n` and deadline `D`
(`AtomicInteropProof.sol:171-179`): the timestamp is imported (`≠ 0`) and after the deadline. -/
def State.TimeoutRootPasses (st : State) (sl : ChainId) (n D : ℕ) : Prop :=
  (st.entries sl n).ts ≠ 0 ∧ D < (st.entries sl n).ts

end Contracts.L2InteropRootStorage
