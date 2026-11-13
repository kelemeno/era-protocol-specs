import EraSpec.Protocol.InteropAtomicity.Specs.Timeout

/-!
# Model: a chain-tree leaf's POSITION is not its batch NUMBER

`Contracts.Timeout.RootBacking` reads "leaf `i` of chain `c`'s tree is that chain's batch
`i`" (`upToLast : (leaves c).length = R.upTo c + 1`), and `Contracts.Timeout.LastBatchAccepted`
uses one `N` both as the Merkle path index and as the batch number whose clock and IMT state
the END branch reads.  The settlement layer does not build the tree that way.  This file
models the tree as it is built, with the leaf position and the batch number as separate
fields bound together only by `batchLeafHash`.

**This file is definitions only.**  The statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.BatchPosition`, the proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.BatchPosition`.

## What the source does (pinned `c67894b9`, `l1-contracts/contracts/`)

* `core/message-root/MessageRootBase.sol:339-350`, `_addNewChain(chainId, startingBatchNumber)`:
  `currentChainBatchNumber = _startingBatchNumber` and `chainTree.setup(...)`, an EMPTY tree.
* `:228-243`, `_recordChainBatchRoot`: the batch number must be `currentChainBatchNumber + 1`
  and not yet recorded (`NonConsecutiveBatchNumber`, `ChainBatchRootAlreadyExists`).
* `:247-259`, `_pushChainBatchRoot`: `chainTree.push(batchLeafHash(root, batchNumber,
  block.timestamp))`, so the leaf lands at the tree's next position (`_nextLeafIndex`)
  whatever its batch number is.
* `:199-205`, `addChainBatchRoot` (the v31 entry point) records and does NOT push;
  `:217-224`, `addChainBatchRootV32` records and pushes.
* `:178-183`, `setMigratingChainBatchNumber`: the number moves forward with no push.
* `core/message-root/L1MessageRoot.sol:99-117`, `saveV31UpgradeChainBatchNumber` (L1 only):
  from `currentChainBatchNumber == 0` the number is set to the chain's
  `getTotalBatchesExecuted()`, with no push.  Also a forward move.
* `:364-387`, `seedGenesisRoot`: returns at once for an EraVM chain (`!getZKsyncOS()`);
  for a ZKsync OS chain with `currentChainBatchNumber == 0` it pushes batch `0`.
* `common/libraries/MessageHashing.sol:195-207`: the verifier rebuilds the leaf as
  `batchLeafHash(batchSettlementRoot, _batchNumber, l1BatchTimestamp)` and walks it at the
  prover's `batchLeafProofMask`.  Number and position are independent inputs.
* `atomic-interop/libraries/AtomicInteropProof.sol:217-230`, `_verifyLastBatchInRoot`, reads
  the mask and the siblings only; `:256-290`, `_authenticateRoot`, hashes the separate
  `_proof.batchNumber` into that leaf.

Main `3605e82` keeps the same structure (`MessageRootBase.sol:154-166`, `:192-206`,
`:210-218`, `:284-294`, `:305-326`; `L1MessageRoot.sol:89-107`; `AtomicInteropProof.sol:113`,
`:130-143`), and so does `draft/v0.35.0` `d9f6789` (`MessageRootBase.sol:145-157`, `:183-197`,
`:201-209`, `:275-285`, `:296-313`; `AtomicInteropProof.sol:113`, `:130-143`), where
`saveV31UpgradeChainBatchNumber` no longer exists.

So a chain onboarded at batch `100` that settles batch `101` holds batch `101` at position
`0`; an EraVM chain registered at `0` holds batch `1` at position `0`; and the v31
record-only path and migrations open further gaps between position and number.  The old
composition cannot represent any of these: `Properties.CurrentCompositionCannotRepresentOnboardingAt100`.

## What this file models

* `BatchEntry` — a leaf's preimage `(batchRoot, batchNumber, l1Timestamp)`;
  `BatchLeafHash` is `MessageHashing.batchLeafHash`, abstract as every hash here.
* `PositionedBacking` — each chain's entries in push order (position = list index), with
  batch numbers strictly increasing and `R.upTo c` the LAST entry's batch number.  The
  leaves are `batchLeafHash` of the entries.
* `PositionedLastBatchAccepted` / `PositionedEndBranchAccepted` — the END branch with the
  mask `pos` and the submitted preimage `(r, N, t)` as separate inputs: the walk runs at
  `pos` on `batchLeafHash(r, N, t)`, the zero check reads `pos`, and the deadline is
  compared with the timestamp `t` bound into the leaf.  `EntriesTimed` links the tree's
  timestamps to `System.time`.
* `PositionedEndBreak` — the located failures: a `PinnedBreak` after `pos`, a
  `PathCollision` on the submitted path, or a `LeafPreimageClash`, a `batchLeafHash`
  collision between the entry stored at `pos` and the submitted preimage.
* `AggregatesBefore` — `Contracts.Timeout.Aggregates` with a strict comparison, which is
  all the timeout path uses (the root is created strictly after the deadline).
* `PushLog`, `AggregatesPushed`, `ClockFromPushes`, `GapsAfterRootLate` — the
  settlement layer's side restated over the batches actually pushed, with the batches never
  pushed to this layer (migration gaps, a halted chain) covered by an explicit hypothesis.
* `ChainTreeSlot` / `ChainTreeStep` — the numbering and push discipline of
  `MessageRootBase` for one chain, from which `PositionedBacking.numbersIncrease` is derived
  rather than assumed.
* `IdentityNumbered` — "position `i` holds batch `i`", the one numbering on which the old
  model is right (`Properties.IdentityNumberedBackingIsOldBacking`,
  `Properties.IdentityNumberingNeedsGenesis`).

The BEGIN branch is kept as `Contracts.Timeout.BeginBranchVerified`, as in
`Contracts.Timeout.LegRefundableAccepted`: it has no last-batch check, so the conflation
does not reach it.

The contract checks the mask only against the path length (`Merkle.sol:133-140`,
`_validatePathLengthForSingleProof`), not against the occupied range.
`PositionedLastBatchAccepted.inRange` keeps the occupied-range form of the old model;
`Properties.MaskBoundGivesOccupiedRange` derives it from the mask bound, or the submitted
leaf equals the empty-entry constant, or a `PathCollision`.

## What this file does not model

Inherited from `Contracts.Timeout`, unchanged here:

* **The batch root is not tied to the IMT.**  The contract authenticates `chainImtRoot` as a
  leaf of the submitted batch root `r` (`_authenticateRoot`, the fixed-depth
  `ChainBatchRootTree` path) and runs the absence check against that.  The gate below takes
  the absence check against `System.tree c N` directly, `N` being the submitted batch
  number.  So `r` only enters through the leaf hash, and "the batch root stored for batch
  `N` commits to `System.tree c N`" is not stated anywhere.
* **The path length is the tree's height.**  The prover chooses `batchLeafProofLen`; the
  model walks exactly `B.height c` levels.  The wrong-length question is the Merkle
  `Verifier` topic's (`AcceptForcesHeightOrBreak`).
* **The shared tree.**  `R` is abstract: the chain-id leaf, the shared-tree path and the
  import of the root on the destination are not modelled.
* **Which layer a batch settled on.**  `System.time` is one total clock per chain; see
  `GapsAfterRootLate`.
-/

namespace Contracts.BatchPosition

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier

/-! ## The chain tree's leaves -/

/-- The preimage of one chain-tree leaf, as `_pushChainBatchRoot` hashes it.

* `batchRoot` — the chain batch root (`batchSettlementRoot` on the verifier's side);
* `batchNumber` — `_batchNumber`, the number `_recordChainBatchRoot` accepted;
* `l1Timestamp` — `block.timestamp` of the push, the `l1BatchTimestamp` the timeout path
  compares with the deadline. -/
structure BatchEntry where
  batchRoot : UInt256
  batchNumber : ℕ
  l1Timestamp : ℕ
deriving DecidableEq

/-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)`:
`keccak256(abi.encodePacked(BATCH_LEAF_PADDING, batchRoot, batchNumber, l1Timestamp))`. -/
abbrev BatchLeafHash := UInt256 → ℕ → ℕ → UInt256

/-- The leaf an entry occupies. -/
def entryLeaf (bl : BatchLeafHash) (e : BatchEntry) : UInt256 :=
  bl e.batchRoot e.batchNumber e.l1Timestamp

/-- **THE PER-CHAIN BATCH TREES BEHIND A ROOT, WITH POSITIONS AND NUMBERS SEPARATE.**
`entries c` is chain `c`'s tree inside `R`, in push order: position `i` holds
`entries c` at index `i`, whatever batch number that entry carries.

* `numbersIncrease` — batch numbers strictly increase along the tree.  Consecutive except
  where the chain was registered at a nonzero starting batch, recorded batches through
  the v31 entry point, or migrated (`ChainTreeStep`; derived for reachable states in
  `Properties.ReachableSlotNumbersIncrease`).
* `upToLast` — `R.upTo c` is the batch number of the tree's LAST entry.  A chain whose
  tree is empty puts no constraint on `R.upTo c`; no END branch can name it.
* `capacity` — the tree fits its height.

`h` (node hash) and `ze` (`CHAIN_TREE_EMPTY_ENTRY_HASH`) only index the type, as in
`Contracts.Timeout.RootBacking`. -/
structure PositionedBacking (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot) where
  /-- Chain `c`'s entries inside this root, in push order. -/
  entries : Chain → List BatchEntry
  /-- The chain tree's height. -/
  height : Chain → ℕ
  /-- Batch numbers strictly increase with position. -/
  numbersIncrease : ∀ c, (entries c).Pairwise (fun a b => a.batchNumber < b.batchNumber)
  /-- `R.upTo c` is the last entry's batch number. -/
  upToLast : ∀ c e, (entries c).getLast? = some e → e.batchNumber = R.upTo c
  /-- The tree fits its height. -/
  capacity : ∀ c, (entries c).length ≤ 2 ^ height c

namespace PositionedBacking

variable {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}

/-- The chain tree's level-0 list: `batchLeafHash` of each entry, in push order. -/
def leaves (B : PositionedBacking h ze bl R) (c : Chain) : List UInt256 :=
  (B.entries c).map (entryLeaf bl)

/-- The entry at position `pos` (`⟨0, 0, 0⟩` past the end, where nothing reads it). -/
def entryAt (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) : BatchEntry :=
  (B.entries c).getD pos ⟨0, 0, 0⟩

end PositionedBacking

/-! ## The END branch, position and batch number apart -/

/-- `_verifyLastBatchInRoot` accepted for chain `c` at mask `pos`, on the leaf the verifier
rebuilt from the submitted preimage `(r, N, t)`.

* `inRange` — the mask is an occupied position (the old model's range check, now on the
  position; see `Properties.MaskBoundGivesOccupiedRange` for the contract's own bound);
* `authenticated` — `batchLeafHash(r, N, t)` walked at `pos` recomputes the chain tree's root;
* `zeroRightSiblings` — wherever the path goes left, the right sibling is that level's
  empty-subtree hash.

The batch number `N` enters only through the leaf hash: nothing here compares `N` with
`pos`. -/
structure PositionedLastBatchAccepted {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ) : Prop where
  inRange : pos < (B.entries c).length
  authenticated :
    walkPure h sibs 0 (B.height c) pos (bl r N t) = rootOf h ze (B.leaves c) (B.height c)
  zeroRightSiblings : ∀ l < B.height c, (pos / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l

/-- **THE END BRANCH AS THE CONTRACT RUNS IT, POSITION AND NUMBER APART.**  The root
post-dates the deadline, the timestamp `t` bound into the submitted leaf is at or before
it (`ProofTimeoutBranchMismatch(false, …)` reads `l1BatchTimestamp` from the same proof),
and the last-batch check passes at mask `pos`. -/
structure PositionedEndBranchAccepted {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (c : Chain) (D : ℕ) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootAfterDeadline : D < R.created
  /-- `ProofTimeoutBranchMismatch(false, …)`, on the timestamp bound into the leaf. -/
  onTime : t ≤ D
  /-- `_verifyLastBatchInRoot`. -/
  lastBatch : PositionedLastBatchAccepted B c pos sibs r N t

/-- **THE TREE'S CLOCK IS THE SYSTEM'S CLOCK.**  Every entry's bound timestamp is
`System.time` of the batch it carries: `System.time c n` is batch `n`'s `l1BatchTimestamp`,
and for a pushed batch that is the timestamp `_pushChainBatchRoot` hashed into its leaf. -/
def EntriesTimed {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot} (S : System)
    (B : PositionedBacking h ze bl R) : Prop :=
  ∀ c, ∀ e ∈ B.entries c, S.time c e.batchNumber = e.l1Timestamp

/-- The submitted preimage `(r, N, t)` IS the last entry of chain `c`'s tree in `R`. -/
def SubmittedIsLastEntry {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (c : Chain) (r : UInt256) (N t : ℕ) : Prop :=
  (B.entries c).getLast? = some ⟨r, N, t⟩

/-! ## Located breaks and bounded premises -/

/-- **A `batchLeafHash` COLLISION ON TWO NAMED PREIMAGES.**  The two entries differ and
occupy the same leaf.  Used with the entry stored at the proven position and the submitted
preimage, both fixed by the instance and the submission. -/
def LeafPreimageClash (bl : BatchLeafHash) (e e' : BatchEntry) : Prop :=
  e ≠ e' ∧ entryLeaf bl e = entryLeaf bl e'

/-- `batchLeafHash` is injective on the preimages satisfying `P`. -/
def BatchLeafInjOn (bl : BatchLeafHash) (P : BatchEntry → Prop) : Prop :=
  ∀ e e', P e → P e' → entryLeaf bl e = entryLeaf bl e' → e = e'

/-- The preimages one END-branch verification involves: chain `c`'s entries and the
submitted `(r, N, t)`.  At most `(B.entries c).length + 1` of them. -/
def LeafPreimage {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (c : Chain) (r : UInt256) (N t : ℕ) (e : BatchEntry) : Prop :=
  e ∈ B.entries c ∨ e = ⟨r, N, t⟩

/-- **WHAT AN ACCEPTED POSITIONED END BRANCH CAN FAIL ON.**  A `PinnedBreak` on the subtree
right after position `pos`, a `PathCollision` at a named level of the submitted path, or a
`LeafPreimageClash` between the entry stored at `pos` and the submitted preimage.  Every
compared value is determined by the instance and the submission. -/
def PositionedEndBreak {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ) : Prop :=
  PinnedBreak h ze (B.leaves c) pos
    ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) pos (bl r N t)
    ∨ LeafPreimageClash bl (B.entryAt c pos) ⟨r, N, t⟩

/-! ## The gate -/

/-- **THE TIMEOUT GATE FOR ONE SUBMITTED PROOF, POSITION AND NUMBER APART.**  As
`Contracts.Timeout.LegRefundableAcceptedBy`, except that the END branch is
`PositionedEndBranchAccepted`: the mask `pos` and the submitted leaf preimage
`(r, N, t)` are separate, and the IMT absence proof `p` is checked against batch `N`'s
END tree, `N` being the number the leaf hash binds. -/
def PositionedLegRefundableAcceptedBy (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (S : System) {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (B : PositionedBacking h ze bl R) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof)
    (pos : ℕ) (sibs : ℕ → UInt256) (r : UInt256) (t : ℕ) : Prop :=
  (BeginBranchVerified S R leg.chain F.deadline N ∧
      AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
        (legValue cv F leg) p)
    ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t ∧
        AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N)
          (legValue cv F leg) p)

/-! ## The settlement layer's side, over the batches actually pushed

`Contracts.Timeout.Aggregates S R` ranges over every batch number.  It is equivalent to
"every batch after `R.upTo c` settled after `R` was created", so batches before the last
entry (before onboarding, recorded through the v31 path) never matter to it.  What can
break it is a batch after the last entry that never reaches this layer's tree: a chain that
migrated away, or one that halted.  The predicates below separate the two kinds of batch
after the last entry.  Pushed batches are covered by how roots are built.  Batches never
pushed are covered by the explicit `GapsAfterRootLate`.
`Properties.AggregatesBeforeFromPushLog` derives the strict `AggregatesBefore` from them,
which is what the gate results take. -/

/-- **`Contracts.Timeout.Aggregates`, STRICT.**  A batch that settled strictly before a root
was created is inside that root.  `Aggregates` asks the same of a batch that settled in the
root's own block-timestamp; the timeout path never needs that, because it only uses roots
created strictly after the deadline and only asks about batches that settled by the deadline.
`Properties.AggregatesImpliesBefore`; `Properties.AggregatesBeforeIsWeaker`. -/
def AggregatesBefore (S : System) (R : SlRoot) : Prop :=
  ∀ c n, S.time c n < R.created → n ≤ R.upTo c

/-- The settlement layer's push history: `P c e` — entry `e` was pushed to chain `c`'s tree
on this layer (`AppendedChainBatchRoot`), at any time in the history the system covers. -/
abbrev PushLog := Chain → BatchEntry → Prop

/-- `R`'s entries were pushed. -/
def RootEntriesPushed {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (P : PushLog) (B : PositionedBacking h ze bl R) : Prop :=
  ∀ c, ∀ e ∈ B.entries c, P c e

/-- For a pushed batch, `System.time` is the timestamp bound into its leaf. -/
def ClockFromPushes (S : System) (P : PushLog) : Prop :=
  ∀ c e, P c e → S.time c e.batchNumber = e.l1Timestamp

/-- **AGGREGATION, OVER THE TREE.**  A batch pushed strictly before `R` was created is
inside `R`.  The intended justification: chain trees are append-only, a root is computed
from the trees as they stand, and `block.timestamp` does not decrease from block to block,
so a push with a strictly smaller timestamp happened in an earlier block.  The comparison is
strict so that nothing is claimed about a push in the root's own block, after the root was
computed.  This is a property of the settlement layer, not of the interop contracts, and is
not derived here. -/
def AggregatesPushed {h : Hash} {ze : UInt256} {bl : BatchLeafHash} {R : SlRoot}
    (P : PushLog) (B : PositionedBacking h ze bl R) : Prop :=
  ∀ c e, P c e → e.l1Timestamp < R.created → e ∈ B.entries c

/-- **THE MIGRATION-GAP HYPOTHESIS.**  A batch after `R`'s last one that was never pushed to
this layer's tree (settled on another layer, or never settled) is not given a time strictly
before `R` was created.  `System.time` is one total clock per chain and does not record which
layer a batch settled on, so this cannot be derived.  Both timeout branches and the finality
gate resolve against the flow's own settlement layer
(`ProofSettlementLayerMismatch`, `AtomicInteropProof.sol:123`, `:167`), so the reading under
which the hypothesis is natural is "`System.time c m` is when batch `m` entered this layer's
tree".  `Properties.MigrationGapIsLoadBearing` shows the composition needs the hypothesis. -/
def GapsAfterRootLate (S : System) (P : PushLog) (R : SlRoot) : Prop :=
  ∀ c m, R.upTo c < m → (∀ e, P c e → e.batchNumber ≠ m) → R.created ≤ S.time c m

/-! ## The numbering discipline of `MessageRootBase`, for one chain -/

/-- One chain's slice of `MessageRootBase` storage on one settlement layer:
`currentChainBatchNumber[c]`, which batch numbers `chainBatchRoots[c]` holds a nonzero root
for, and the chain tree's leaf preimages in push order. -/
structure ChainTreeSlot where
  current : ℕ
  recorded : ℕ → Bool
  pushed : List BatchEntry

/-- `_addNewChain(chainId, startingBatchNumber)`: an empty tree, nothing recorded, and the
numbering continuing from `s`. -/
def registeredSlot (s : ℕ) : ChainTreeSlot := ⟨s, fun _ => false, []⟩

/-- The storage writes that move a chain's numbering or its tree.  `zksyncOS` is the chain's
`getZKsyncOS()`, read by `seedGenesisRoot` at the call and taken here as fixed for the chain:
only a ZKsync OS chain can take the `seedGenesis` step.  The access modifiers,
`ChainBatchRootZero` and `MessageRootNotRegistered` do not affect the numbering or the tree
and are not modelled.  Every writer of `currentChainBatchNumber` and every `chainTree` push
at the pin is one of these four steps (`saveV31UpgradeChainBatchNumber` is an instance of
`migrate`). -/
inductive ChainTreeStep (zksyncOS : Bool) : ChainTreeSlot → ChainTreeSlot → Prop
  /-- `addChainBatchRoot` (v31): `_recordChainBatchRoot` only. -/
  | recordOnly (σ : ChainTreeSlot) (n : ℕ) :
      σ.recorded n = false → n = σ.current + 1 →
      ChainTreeStep zksyncOS σ ⟨n, Function.update σ.recorded n true, σ.pushed⟩
  /-- `addChainBatchRootV32`: `_recordChainBatchRoot`, then `_pushChainBatchRoot` at
  `block.timestamp = ts`. -/
  | recordAndPush (σ : ChainTreeSlot) (n : ℕ) (root : UInt256) (ts : ℕ) :
      σ.recorded n = false → n = σ.current + 1 →
      ChainTreeStep zksyncOS σ
        ⟨n, Function.update σ.recorded n true, σ.pushed ++ [⟨root, n, ts⟩]⟩
  /-- `setMigratingChainBatchNumber`: the number moves forward, nothing is pushed.  Also
  covers `L1MessageRoot.saveV31UpgradeChainBatchNumber`, which moves the number from `0` to
  `getTotalBatchesExecuted()` with no push; its extra guards only restrict when it runs. -/
  | migrate (σ : ChainTreeSlot) (n : ℕ) :
      σ.current ≤ n → ChainTreeStep zksyncOS σ ⟨n, σ.recorded, σ.pushed⟩
  /-- `seedGenesisRoot` on a ZKsync OS chain: batch `0` is recorded and pushed, and
  `currentChainBatchNumber` stays `0`.  On an EraVM chain the call returns before writing
  anything, so there is no step. -/
  | seedGenesis (σ : ChainTreeSlot) (root : UInt256) (ts : ℕ) :
      zksyncOS = true → σ.current = 0 → σ.recorded 0 = false →
      ChainTreeStep zksyncOS σ
        ⟨0, Function.update σ.recorded 0 true, σ.pushed ++ [⟨root, 0, ts⟩]⟩

/-- The slots reachable after registering the chain at starting batch `s`. -/
def SlotReachable (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot) : Prop :=
  Relation.ReflTransGen (ChainTreeStep zksyncOS) (registeredSlot s) σ

/-- The slot after `addNewChain(c, s)` and one `addChainBatchRootV32(c, s + 1, root)` at
`block.timestamp = ts`: batch `s + 1` at position `0`. -/
def onboardedSlot (s : ℕ) (root : UInt256) (ts : ℕ) : ChainTreeSlot :=
  ⟨s + 1, Function.update (fun _ => false) (s + 1) true, [⟨root, s + 1, ts⟩]⟩

/-- **POSITION `i` HOLDS BATCH `i`.**  The numbering `Contracts.Timeout.RootBacking`
assumes of every chain tree. -/
def IdentityNumbered (l : List BatchEntry) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), (l[i]'hi).batchNumber = i

/-- The slot of a ZKsync OS chain registered at batch `0`, after `seedGenesisRoot` (batch `0`,
root `root0`, at time `ts0`) and one `addChainBatchRootV32(c, 1, root1)` at time `ts1`:
batch `0` at position `0` and batch `1` at position `1`. -/
def seededSlot (root0 root1 : UInt256) (ts0 ts1 : ℕ) : ChainTreeSlot :=
  ⟨1, Function.update (Function.update (fun _ => false) 0 true) 1 true,
    [⟨root0, 0, ts0⟩, ⟨root1, 1, ts1⟩]⟩

/-- The root a settlement layer publishes over the slots `σ` at time `created`: each chain's
`upTo` is its tree's last batch number (`0` for an empty tree, which no END branch names). -/
def slotRoot (σ : Chain → ChainTreeSlot) (created : ℕ) : SlRoot where
  created := created
  upTo := fun c => (((σ c).pushed.getLast?).map BatchEntry.batchNumber).getD 0

/-! ## Concrete instances for the witnesses and countermodels

Node hash `demoHash` (it collides), empty-entry constant `0`, and the leaf hash `rootLeaf`,
which reads only the batch root and so collides on every batch number.  Nothing proved about
these instances can come from global injectivity. -/

/-- A leaf hash that ignores the batch number and the timestamp: `batchLeafHash` with the
binding of `N` and `t` removed. -/
def rootLeaf : BatchLeafHash := fun r _ _ => r

/-- A root created at time `1` whose every chain's last batch is `s + 1`. -/
def onboardedRoot (s : ℕ) : SlRoot where
  created := 1
  upTo := fun _ => s + 1

/-- Every chain onboarded at batch `s` with one push since: batch `s + 1`, root `5`, pushed at
time `0`, at position `0` of a height-1 tree. -/
def onboardedBacking (s : ℕ) : PositionedBacking demoHash 0 rootLeaf (onboardedRoot s) where
  entries := fun _ => [⟨5, s + 1, 0⟩]
  height := fun _ => 1
  numbersIncrease := fun _ => List.pairwise_singleton _ _
  upToLast := fun _ e he => by
    simp only [List.getLast?_singleton, Option.some.injEq] at he
    subst he
    rfl
  capacity := fun _ => by norm_num

/-- The push log of `onboardedBacking s`: batch `s + 1` and nothing else. -/
def onboardedPushes (s : ℕ) : PushLog := fun _ e => e = ⟨5, s + 1, 0⟩

/-- A system that never commits anything, with batches up to `s + 1` settled at time `0`
and later ones at time `2`. -/
def onboardedSystem (s : ℕ) : System where
  tree := fun _ _ => setup
  time := fun _ n => if n ≤ s + 1 then 0 else 2
  height := fun _ _ => 0

/-- The same clock, but the chain commits `a` during batch `s + 1`: it was onboarded at `s`
and delivers the leg in its first batch on this layer, on time. -/
def deliveringSystem (s : ℕ) (a : UInt256) : System where
  tree := fun _ n => if n ≤ s then setup else insert setup a 0
  time := fun _ n => if n ≤ s + 1 then 0 else 2
  height := fun _ n => if n ≤ s then 0 else 1

/-- `onboardedBacking s` at height `0`, for the countermodels quantified over every node
hash: one entry, batch `s + 1`, so the walk is the leaf itself. -/
def flatOnboardedBacking (s : ℕ) (h : Hash) : PositionedBacking h 0 rootLeaf (onboardedRoot s) where
  entries := fun _ => [⟨5, s + 1, 0⟩]
  height := fun _ => 0
  numbersIncrease := fun _ => List.pairwise_singleton _ _
  upToLast := fun _ e he => by
    simp only [List.getLast?_singleton, Option.some.injEq] at he
    subst he
    rfl
  capacity := fun _ => by norm_num

/-- A root created at time `1` whose every chain's last batch is `81`. -/
def gapRoot : SlRoot where
  created := 1
  upTo := fun _ => 81

/-- A chain tree with a gap inside it: batch `50`, then batch `81` (the chain migrated away
after batch `50` and came back with `setMigratingChainBatchNumber(80)`).  Roots `5`, `7`, so
the leaves are the `[5, 7]` of `Contracts.Timeout.demoBacking`, at height 2. -/
def gapBacking : PositionedBacking demoHash 0 rootLeaf gapRoot where
  entries := fun _ => [⟨5, 50, 0⟩, ⟨7, 81, 0⟩]
  height := fun _ => 2
  numbersIncrease := fun _ => by simp
  upToLast := fun _ e he => by
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at he
    subst he
    rfl
  capacity := fun _ => by norm_num

/-- A root created at time `1` whose every chain's last batch is `3`. -/
def threeRoot : SlRoot where
  created := 1
  upTo := fun _ => 3

/-- Three entries whose leaves are the `[5, 7, 9]` of `Contracts.Timeout.demoBacking3`, for
the non-tautology witness: position `1` is not last. -/
def threeBacking : PositionedBacking demoHash 0 rootLeaf threeRoot where
  entries := fun _ => [⟨5, 1, 0⟩, ⟨7, 2, 0⟩, ⟨9, 3, 0⟩]
  height := fun _ => 2
  numbersIncrease := fun _ => by simp
  upToLast := fun _ e he => by
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at he
    subst he
    rfl
  capacity := fun _ => by norm_num

/-- `Contracts.Timeout.staleRoot` (created at `1`, last batch `0`) backed by one entry,
batch `0` pushed at time `0`, at height `0`; for the migration-gap countermodel. -/
def staleBacking (h : Hash) : PositionedBacking h 0 rootLeaf staleRoot where
  entries := fun _ => [⟨5, 0, 0⟩]
  height := fun _ => 0
  numbersIncrease := fun _ => List.pairwise_singleton _ _
  upToLast := fun _ e he => by
    simp only [List.getLast?_singleton, Option.some.injEq] at he
    subst he
    rfl
  capacity := fun _ => by norm_num

/-- Its push log: batch `0` only.  Batch `1` settled, but never on this layer. -/
def stalePushes : PushLog := fun _ e => e = ⟨5, 0, 0⟩

end Contracts.BatchPosition
