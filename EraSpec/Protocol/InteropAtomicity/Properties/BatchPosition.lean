import EraSpec.Protocol.InteropAtomicity.Specs.BatchPosition

/-!
# Properties: the END-branch composition with leaf position and batch number apart

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.BatchPosition`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.BatchPosition`.

## What was wrong

`Contracts.Timeout.RootBacking` makes leaf `i` batch `i`, and `LastBatchAccepted` uses
one `N` as both the Merkle position and the batch number.  The settlement layer's chain tree
starts empty at whatever batch the chain is registered at, and `_pushChainBatchRoot`
appends at the next position.  `Properties.CurrentCompositionCannotRepresentOnboardingAt100`
is the countermodel: after `addNewChain(c, 100)` and one push of batch `101`, an old-model
backing with that one leaf forces `R.upTo c = 0`, accepts no END branch for batch `101`, and
makes `Aggregates` false.  `Properties.TreePositionBelowBatchNumber` shows this is the usual
case, not an edge case: for an EraVM chain, or any chain registered at a nonzero batch,
NO position holds its own batch number.

## What replaces it

The last-batch check identifies the last POSITION (`Contracts.AtomicInteropProof`'s
`LastLeaf` results, unchanged).  The leaf hash binds the batch number to it: the last
position, plus no `batchLeafHash` collision on the two named preimages, makes the
submitted preimage the tree's last entry, so `N = R.upTo c`
(`Properties.LastPositionFixesBatchNumber`, `Properties.SubmittedLastEntryIsUpTo`).  The
chain then runs as before, to `Contracts.Timeout.EndBranchVerified`, `IsLastOnTime` and the
looser `LegRefundableBy` every refund result is stated over.  Each step has a pinned form
(no hash premise; the escape is a `PositionedEndBreak` located on the submission) and a
bounded form (injectivity only on the pairs and preimages this verification touches).

`Properties.BatchNumberForgeryLocatesLeafClash` is why the leaf-hash premise is there.
With a leaf hash that does not bind the batch number, a prover names batch `0` for the
leaf holding batch `101`, passes every check at the last position, and refunds a leg that
was delivered on time.  The located break that carries it is the `LeafPreimageClash`.

## The settlement layer's side

The gate results take `AggregatesBefore`, the strict form of `Contracts.Timeout.Aggregates`
(`Properties.AggregatesImpliesBefore`, `Properties.AggregatesBeforeIsWeaker`,
`Properties.IsLastOnTimeFromAggregatesBefore`).  With `R.upTo c` the last entry's batch
number, neither form conflicts with onboarding: the witnesses below satisfy `Aggregates`
itself.  `Properties.AggregatesBeforeFromPushLog` derives `AggregatesBefore` from statements
about the batches actually pushed.  Those are: a batch pushed strictly before `R` was
created is in `R` (`AggregatesPushed`), and a pushed batch's `System.time` is its leaf's
timestamp (`ClockFromPushes`).  The batches never pushed to this layer are covered by the
explicit `GapsAfterRootLate`.  `Properties.MigrationGapIsLoadBearing` shows the composition
needs that hypothesis.

## The old model inside the new one

`Properties.IdentityNumberedBackingIsOldBacking`: when every chain's tree is non-empty and
position `i` holds batch `i`, the positioned backing is a `Contracts.Timeout.RootBacking`
with the same leaves, and the old END branch and gate at batch `N` are the positioned ones at
position `N`.  `Properties.IdentityNumberingNeedsGenesis`: that numbering is reachable, and
only for a ZKsync OS chain registered at batch `0` (the genesis leaf).  The old END-branch
results (`Contracts.Timeout`, `Contracts.Refund`, `Contracts.Operational`, the
`BurnMintBridge` `EndBranch` topic) are about that case.

## Witnesses

`Properties.OnboardedTimeoutWitness` satisfies every premise of the headline
`Properties.PushLogTimeoutMeansMissedDeadlineOrBreak` and of the bounded forms, for EVERY
starting batch `s`, with the zero check exercised (a one-level path whose only step goes
left).  Its `s = 100` instance holds batch
`101` at position `0` (`Properties.OnboardedAt100Composes`).  Its `s = 0` instance is an
EraVM chain with no genesis leaf, holding batch `1` at position `0`
(`Properties.EraVmNoGenesisComposes`).  `Properties.MigrationGapInsideTreeWitness` has a
migration gap inside the tree, with the zero check firing at a nonzero position.
-/

namespace Contracts.BatchPosition

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract

/-! ## The old composition cannot represent onboarding -/

/-- **THE CURRENT COMPOSITION CANNOT REPRESENT A CHAIN ONBOARDED AT BATCH 100.**  The
`MessageRootBase` state after `addNewChain(c, 100)` and one `addChainBatchRootV32(c, 101, _)`
is reachable and holds exactly one leaf, for batch `101`.  Every `Contracts.Timeout.RootBacking`
whose chain-`c` tree has that one leaf:

* forces `R.upTo c = 0` (`upToLast`);
* accepts an END branch only for batch `0`, and so none for batch `101` (`inRange` would
  need `101 < 1`);
* makes `Aggregates` false whenever batch `101` settled by the time the root was created
  (the statement takes that as a hypothesis; in the situation described it holds, the
  batch's leaf being inside the root).

So on this tree the old END-branch results either name batch `0`, which the leaf does not
hold, or take an `Aggregates` premise that is false. -/
def Properties.CurrentCompositionCannotRepresentOnboardingAt100 : Prop :=
  (∀ (zksyncOS : Bool) (root : UInt256) (ts : ℕ),
      SlotReachable zksyncOS 100 (onboardedSlot 100 root ts)
        ∧ (onboardedSlot 100 root ts).pushed = [⟨root, 101, ts⟩])
    ∧ ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (c : Chain),
      (B.leaves c).length = 1 →
        R.upTo c = 0
        ∧ (∀ (S : System) (D N : ℕ) (sibs : ℕ → UInt256) (x : UInt256),
            EndBranchAccepted B S c D N sibs x → N = 0)
        ∧ (∀ (S : System) (D : ℕ) (sibs : ℕ → UInt256) (x : UInt256),
            ¬ EndBranchAccepted B S c D 101 sibs x)
        ∧ (∀ S : System, S.time c 101 ≤ R.created → ¬ Aggregates S R)

/-! ## The tree `MessageRootBase` builds -/

/-- **BATCH NUMBERS STRICTLY INCREASE ALONG EVERY REACHABLE TREE.**
`_recordChainBatchRoot` accepts only `currentChainBatchNumber + 1`, the number never moves
back, and `seedGenesisRoot` pushes batch `0` only into an empty tree.  This is
`PositionedBacking.numbersIncrease`, derived. -/
def Properties.ReachableSlotNumbersIncrease : Prop :=
  ∀ (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot), SlotReachable zksyncOS s σ →
    σ.pushed.Pairwise (fun a b => a.batchNumber < b.batchNumber)

/-- **WITHOUT A GENESIS LEAF, THE TREE HOLDS ONLY BATCHES AFTER THE STARTING ONE.**  For an
EraVM chain (whatever its starting batch), or for any chain registered at a nonzero batch,
every pushed batch number exceeds the starting batch. -/
def Properties.TreeAboveStartWithoutGenesis : Prop :=
  ∀ (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot), SlotReachable zksyncOS s σ →
    (zksyncOS = false ∨ 0 < s) → ∀ e ∈ σ.pushed, s < e.batchNumber

/-- **NO POSITION HOLDS ITS OWN BATCH NUMBER.**  Under the same condition, position `i`
holds a batch number above `s + i`.  "Leaf `i` is batch `i`" fails at every position,
not just the first. -/
def Properties.TreePositionBelowBatchNumber : Prop :=
  ∀ (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot), SlotReachable zksyncOS s σ →
    (zksyncOS = false ∨ 0 < s) →
      ∀ (i : ℕ) (hi : i < σ.pushed.length), s + i < (σ.pushed[i]'hi).batchNumber

/-- **EVERY SNAPSHOT OF REACHABLE SLOTS IS A POSITIONED BACKING.**  For any chain-tree
heights with room for the leaves, the slots' trees back `slotRoot σ created`, with
`numbersIncrease` from `ReachableSlotNumbersIncrease`. -/
def Properties.ReachableSlotsBackARoot : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (zksyncOS : Chain → Bool) (s : Chain → ℕ)
    (σ : Chain → ChainTreeSlot) (created : ℕ) (height : Chain → ℕ),
    (∀ c, SlotReachable (zksyncOS c) (s c) (σ c)) →
    (∀ c, (σ c).pushed.length ≤ 2 ^ height c) →
      ∃ B : PositionedBacking h ze bl (slotRoot σ created),
        ∀ c, B.entries c = (σ c).pushed ∧ B.height c = height c

/-! ## The old model inside the new one -/

/-- **ON THE IDENTITY NUMBERING, THE OLD MODEL IS THE NEW ONE.**  If every chain's tree is
non-empty and position `i` holds batch `i`, there is a `Contracts.Timeout.RootBacking` with
the same leaves and heights (its `upToLast`, "`R.upTo c` is the last index", is then true).
For a submitted preimage `(r, N, t)` whose timestamp is `System.time` of batch `N`, the old
END branch at batch `N` on the leaf `batchLeafHash(r, N, t)` is the positioned END branch at
position `N`, and the old gate is the positioned gate.

The timestamp hypothesis is where the two models read the deadline comparison from: the old
one from `System.time c N`, the new one from the `t` bound into the leaf. -/
def Properties.IdentityNumberedBackingIsOldBacking : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R),
    (∀ c, B.entries c ≠ []) → (∀ c, IdentityNumbered (B.entries c)) →
      ∃ B' : RootBacking h ze R,
        (∀ c, B'.leaves c = B.leaves c ∧ B'.height c = B.height c)
        ∧ (∀ (S : System) (c : Chain) (D N : ℕ) (sibs : ℕ → UInt256) (r : UInt256) (t : ℕ),
            S.time c N = t →
              (EndBranchAccepted B' S c D N sibs (bl r N t)
                ↔ PositionedEndBranchAccepted B c D N sibs r N t))
        ∧ (∀ (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
            (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (r : UInt256) (t : ℕ),
            S.time leg.chain N = t →
              (LegRefundableAcceptedBy h z0 hl cv S B' F leg N p sibs (bl r N t)
                ↔ PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p N sibs r t))

/-- **THE IDENTITY NUMBERING IS REACHABLE, AND ONLY THROUGH THE GENESIS LEAF.**  A ZKsync OS
chain registered at batch `0`, seeded, with one push since, holds batch `0` at position `0`
and batch `1` at position `1`.  Conversely a reachable non-empty tree numbered by position
belongs to a ZKsync OS chain registered at batch `0`: for an EraVM chain, or any chain
registered at a nonzero batch, the old model's numbering never occurs. -/
def Properties.IdentityNumberingNeedsGenesis : Prop :=
  (∀ (root0 root1 : UInt256) (ts0 ts1 : ℕ),
      SlotReachable true 0 (seededSlot root0 root1 ts0 ts1)
        ∧ IdentityNumbered (seededSlot root0 root1 ts0 ts1).pushed)
    ∧ ∀ (zksyncOS : Bool) (s : ℕ) (σ : ChainTreeSlot), SlotReachable zksyncOS s σ →
        σ.pushed ≠ [] → IdentityNumbered σ.pushed → zksyncOS = true ∧ s = 0

/-! ## The last-batch proof, position and number apart -/

/-- Every entry's batch number is at most `R.upTo c`: with numbers increasing, the last
entry carries the largest. -/
def Properties.EntryNumbersBoundedByUpTo : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain), ∀ e ∈ B.entries c, e.batchNumber ≤ R.upTo c

/-- **THE LAST POSITION FIXES THE BATCH NUMBER, OR A NAMED LEAF COLLISION.**  If `pos` is
the tree's last position and the leaf there is `batchLeafHash(r, N, t)`, then the submitted
preimage IS the last entry, or the entry stored at `pos` and the submitted preimage
collide under `batchLeafHash`. -/
def Properties.LastPositionFixesBatchNumber : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (r : UInt256) (N t : ℕ),
    pos + 1 = (B.entries c).length → (B.leaves c).getD pos ze = bl r N t →
      SubmittedIsLastEntry B c r N t ∨ LeafPreimageClash bl (B.entryAt c pos) ⟨r, N, t⟩

/-- The last entry's batch number is `R.upTo c`. -/
def Properties.SubmittedLastEntryIsUpTo : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (r : UInt256) (N t : ℕ),
    SubmittedIsLastEntry B c r N t → N = R.upTo c

/-- With the tree's clock the system's, the last entry's bound timestamp is
`System.time` of its batch. -/
def Properties.SubmittedLastEntryTimed : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (r : UInt256) (N t : ℕ),
    EntriesTimed S B → SubmittedIsLastEntry B c r N t → S.time c N = t

/-- **THE MASK BOUND THE CONTRACT CHECKS GIVES THE OCCUPIED RANGE, OR A LOCATED BREAK.**
`Merkle.calculateRootMemory` only requires the mask below `2 ^ pathLength`.  An accepted
walk at a mask past the occupied range authenticates the padding constant, so the submitted
leaf hash IS `CHAIN_TREE_EMPTY_ENTRY_HASH`, or the walk carries a `PathCollision`.
So `PositionedLastBatchAccepted.inRange` follows from what the contract runs, up to those two
located escapes.  The gate results below take `inRange` as part of the accepted proof and do
not carry the two escapes themselves. -/
def Properties.MaskBoundGivesOccupiedRange : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ),
    pos < 2 ^ B.height c →
    walkPure h sibs 0 (B.height c) pos (bl r N t) = rootOf h ze (B.leaves c) (B.height c) →
      pos < (B.entries c).length ∨ bl r N t = ze
        ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) pos (bl r N t)

/-- **AN ACCEPTED LAST-BATCH PROOF IDENTIFIES THE LAST ENTRY, OR PINS A BREAK.**  No hash
premise.  The position is pinned to the end of the tree (`PinnedBreak`, `PathCollision`
otherwise), the leaf to the entry stored there (`PathCollision`), and the submitted
preimage to that entry (`LeafPreimageClash`). -/
def Properties.PositionedLastBatchIdentifiesLastEntryPinned : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ),
    PositionedLastBatchAccepted B c pos sibs r N t →
      SubmittedIsLastEntry B c r N t ∨ PositionedEndBreak B c pos sibs r N t

/-- **THE BREAKS ARE EXCLUDED BY A BOUNDED PREMISE.**  Injectivity of the node hash only on
this tree's pairs, its zero cascade and the pairs this verification hashed; of
`batchLeafHash` only on this tree's entries and the submitted preimage; and domain
separation only for this tree's leaves. -/
def Properties.NoPositionedEndBreakOn : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ),
    pos < (B.entries c).length →
    EntriesNotEmpty ze (B.leaves c) →
    PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p) →
    BatchLeafInjOn bl (LeafPreimage B c r N t) →
      ¬ PositionedEndBreak B c pos sibs r N t

/-- **UNDER THE BOUNDED PREMISE, THE ACCEPTED PROOF NAMES THE LAST BATCH.**  The submitted
preimage is the last entry, so its batch number is `R.upTo c`, whatever position it sits
at and whatever batch the chain was registered at. -/
def Properties.PositionedLastBatchIdentifiesLastBatchOn : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ),
    EntriesNotEmpty ze (B.leaves c) →
    PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p) →
    BatchLeafInjOn bl (LeafPreimage B c r N t) →
    PositionedLastBatchAccepted B c pos sibs r N t →
      SubmittedIsLastEntry B c r N t ∧ N = R.upTo c

/-- **THE END BRANCH AS RUN IMPLIES THE END BRANCH AS ASSUMED, OR PINS A BREAK.**  With the
tree's clock the system's, the positioned END branch for batch `N` is
`Contracts.Timeout.EndBranchVerified` for batch `N`: the root post-dates the deadline,
`System.time` of batch `N` is the timestamp the contract compared, and `N = R.upTo c`. -/
def Properties.PositionedEndBranchImpliesVerifiedPinned : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (D pos : ℕ)
    (sibs : ℕ → UInt256) (r : UInt256) (N t : ℕ),
    EntriesTimed S B → PositionedEndBranchAccepted B c D pos sibs r N t →
      EndBranchVerified S R c D N ∨ PositionedEndBreak B c pos sibs r N t

/-- The same, collapsed under the bounded premise. -/
def Properties.PositionedEndBranchImpliesVerifiedOn : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (D pos : ℕ)
    (sibs : ℕ → UInt256) (r : UInt256) (N t : ℕ),
    EntriesTimed S B →
    EntriesNotEmpty ze (B.leaves c) →
    PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) pos (bl r N t) p) →
    BatchLeafInjOn bl (LeafPreimage B c r N t) →
    PositionedEndBranchAccepted B c D pos sibs r N t → EndBranchVerified S R c D N

/-! ## The strict aggregation premise -/

/-- `Contracts.Timeout.Aggregates` implies its strict form. -/
def Properties.AggregatesImpliesBefore : Prop :=
  ∀ (S : System) (R : SlRoot), Aggregates S R → AggregatesBefore S R

/-- **THE STRICT FORM ASKS LESS.**  A root that omits a batch settled in the root's own
timestamp satisfies `AggregatesBefore` and not `Aggregates`: in `onboardedSystem 0` batch `1`
settles at time `0`, and the root created at time `0` stops at batch `0`. -/
def Properties.AggregatesBeforeIsWeaker : Prop :=
  ∃ (S : System) (R : SlRoot), Wf S ∧ AggregatesBefore S R ∧ ¬ Aggregates S R

/-- **`IsLastOnTime` FROM THE STRICT FORM.**  `Contracts.Timeout.Properties.IsLastOnTimeDerived`
with `Aggregates` weakened to `AggregatesBefore`: a batch after `R.upTo c` that settled by
the deadline settled strictly before `R` was created, so would be inside `R`. -/
def Properties.IsLastOnTimeFromAggregatesBefore : Prop :=
  ∀ (S : System) (R : SlRoot), AggregatesBefore S R →
    ∀ (c : Chain) (D N : ℕ), EndBranchVerified S R c D N → IsLastOnTime S c D N

/-! ## The gate -/

/-- **THE GATE AS RUN IMPLIES THE LOOSER PREDICATE, OR PINS A BREAK ON THE SUBMISSION.**
The positioned gate on `(N, p, pos, sibs, r, t)` is `Contracts.Atomicity.LegRefundableBy`
on `(N, p)`, the predicate the refund results are stated over, or its END branch carries a
`PositionedEndBreak`. -/
def Properties.PositionedAcceptedImpliesRefundablePinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R),
    AggregatesBefore S R → EntriesTimed S B →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (pos : ℕ) (sibs : ℕ → UInt256)
      (r : UInt256) (t : ℕ),
      PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t →
        LegRefundableBy h z0 hl cv S F leg N p
          ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
              ∧ PositionedEndBreak B leg.chain pos sibs r N t)

/-- The same, collapsed under the bounded premise on the submission. -/
def Properties.PositionedAcceptedImpliesRefundableOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R),
    AggregatesBefore S R → EntriesTimed S B →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (pos : ℕ) (sibs : ℕ → UInt256)
      (r : UInt256) (t : ℕ),
      EntriesNotEmpty ze (B.leaves leg.chain) →
      PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
        ∨ VerifiedPair h sibs (B.height leg.chain) pos (bl r N t) q) →
      BatchLeafInjOn bl (LeafPreimage B leg.chain r N t) →
      PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t →
        LegRefundableBy h z0 hl cv S F leg N p

/-- **A REFUNDED LEG REALLY MISSED ITS DEADLINE, OR A LOCATED BREAK.**  The positioned gate
as the contract runs it: the leg's commit value was absent at every on-time batch, or the
absence proof `p` carries an `AbsenceBreak`, or the END branch a `PositionedEndBreak`. -/
def Properties.PositionedTimeoutMeansMissedDeadlineOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R),
    AggregatesBefore S R → EntriesTimed S B →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (pos : ℕ) (sibs : ℕ → UInt256)
      (r : UInt256) (t : ℕ),
      PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t →
        (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
          ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
          ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
              ∧ PositionedEndBreak B leg.chain pos sibs r N t)

/-- **A POSITIONED TIMEOUT EXCLUDES FINALITY, OR A LOCATED BREAK.**  No inclusion proof `p'`
at an on-time batch `n` passes for a leg whose positioned timeout gate passed on
`(N, p, pos, sibs, r, t)`, unless `p'` or `p` carries a break, or the END branch a
`PositionedEndBreak`.  The counterpart of
`Contracts.Timeout.Properties.TimeoutExcludesFinalityOrBreak`. -/
def Properties.PositionedTimeoutExcludesFinalityOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R),
    AggregatesBefore S R → EntriesTimed S B →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (pos : ℕ) (sibs : ℕ → UInt256)
      (r : UInt256) (t : ℕ),
      PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t →
      ∀ (n : ℕ) (p' : ImtProof),
        ¬ LegFinalizedBy h z0 hl cv S F leg n p'
          ∨ InclusionBreak h z0 hl S leg.chain n p'
          ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
          ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
              ∧ PositionedEndBreak B leg.chain pos sibs r N t)

/-! ## The settlement layer's side, over the batches pushed -/

/-- **`AggregatesBefore` FROM THE PUSH LOG.**  A batch after `R.upTo c` was either pushed
(not strictly before `R` was created, by `AggregatesPushed`, since it is not among `R`'s
entries) or never pushed (not strictly before `R.created`, by `GapsAfterRootLate`); either
way it did not settle strictly before `R` was created. -/
def Properties.AggregatesBeforeFromPushLog : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (P : PushLog),
    AggregatesPushed P B → ClockFromPushes S P → GapsAfterRootLate S P R →
      AggregatesBefore S R

/-- The tree's clock is the system's, when `R`'s entries were pushed. -/
def Properties.EntriesTimedFromPushLog : Prop :=
  ∀ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (P : PushLog),
    RootEntriesPushed P B → ClockFromPushes S P → EntriesTimed S B

/-- **THE COMPLETE CHAIN, OVER THE BATCHES ACTUALLY PUSHED.**  No hash premise and no
`Aggregates`.  The premises are the settlement layer's push history (strict comparison) and
the explicit migration-gap hypothesis.  Conclusion: the leg missed its deadline, or a located break on
the absence proof or on the END-branch submission. -/
def Properties.PushLogTimeoutMeansMissedDeadlineOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R)
      (P : PushLog),
    RootEntriesPushed P B → ClockFromPushes S P → AggregatesPushed P B →
    GapsAfterRootLate S P R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (pos : ℕ) (sibs : ℕ → UInt256)
      (r : UInt256) (t : ℕ),
      PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg N p pos sibs r t →
        (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
          ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
          ∨ (PositionedEndBranchAccepted B leg.chain F.deadline pos sibs r N t
              ∧ PositionedEndBreak B leg.chain pos sibs r N t)

/-! ## Witnesses: the composition at an offset -/

/-- **EVERY PREMISE HOLDS, AT EVERY STARTING BATCH.**  For each `s`: the tree is the one
`MessageRootBase` holds after `addNewChain(c, s)` and one push (an EraVM chain, so no
genesis leaf), batch `s + 1` at position `0`.  The push-log premises of
`PushLogTimeoutMeansMissedDeadlineOrBreak` hold, and so do the bounded premises of the
`On` forms under the colliding `demoHash`.  The zero check fires at level `0`.  The
honest END branch for batch `s + 1` passes the gate, its absence proof carries no break,
the END branch carries no `PositionedEndBreak`, and the leg really missed its deadline.  The witness's leaf hash `rootLeaf` reads only the
batch root, so the bounded leaf premise is about this instance's one preimage, not about
`batchLeafHash` at large. -/
def Properties.OnboardedTimeoutWitness : Prop :=
  ∀ s : ℕ, ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System)
    (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot) (B : PositionedBacking h ze bl R)
    (P : PushLog) (F : Flow) (leg : FlowLeg) (p : ImtProof) (sibs : ℕ → UInt256)
    (r : UInt256) (t : ℕ),
      SlotReachable false s (onboardedSlot s r t)
      ∧ B.entries leg.chain = (onboardedSlot s r t).pushed
      ∧ Wf S ∧ RootEntriesPushed P B ∧ ClockFromPushes S P ∧ AggregatesPushed P B
      ∧ GapsAfterRootLate S P R
      ∧ EntriesNotEmpty ze (B.leaves leg.chain)
      ∧ PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
          ∨ VerifiedPair h sibs (B.height leg.chain) 0 (bl r (s + 1) t) q)
      ∧ BatchLeafInjOn bl (LeafPreimage B leg.chain r (s + 1) t)
      ∧ (∃ l < B.height leg.chain, (0 / 2 ^ l) % 2 = 0)
      ∧ PositionedEndBranchAccepted B leg.chain F.deadline 0 sibs r (s + 1) t
      ∧ PositionedLegRefundableAcceptedBy h z0 hl cv S B F leg (s + 1) p 0 sibs r t
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain (s + 1) p
      ∧ ¬ PositionedEndBreak B leg.chain 0 sibs r (s + 1) t
      ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))

/-- **ONBOARDED AT 100: POSITION 0 HOLDS BATCH 101, AND THE END BRANCH COMPOSES.**  The
counterpart of `CurrentCompositionCannotRepresentOnboardingAt100`: the same reachable tree
backs a root whose last batch is `101`, the honest END branch at position `0` for batch
`101` passes under the bounded premises, and it yields `EndBranchVerified` and
`IsLastOnTime` for batch `101`. -/
def Properties.OnboardedAt100Composes : Prop :=
  ∃ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (D : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (t : ℕ),
      SlotReachable false 100 (onboardedSlot 100 r t)
      ∧ B.entries c = (onboardedSlot 100 r t).pushed
      ∧ B.entryAt c 0 = ⟨r, 101, t⟩ ∧ R.upTo c = 101
      ∧ PositionedEndBranchAccepted B c D 0 sibs r 101 t
      ∧ EntriesTimed S B ∧ Aggregates S R
      ∧ EntriesNotEmpty ze (B.leaves c)
      ∧ PairInjOn h (fun q => TreePair h ze (B.leaves c) (B.height c) q
          ∨ VerifiedPair h sibs (B.height c) 0 (bl r 101 t) q)
      ∧ BatchLeafInjOn bl (LeafPreimage B c r 101 t)
      ∧ EndBranchVerified S R c D 101 ∧ IsLastOnTime S c D 101

/-- **AN ERAVM CHAIN WITH NO GENESIS LEAF: POSITION 0 HOLDS BATCH 1, AND THE END BRANCH
COMPOSES.**  Registered at `0`, `seedGenesisRoot` a no-op, one push: the honest END branch
at position `0` for batch `1` passes under the bounded premises and yields
`EndBranchVerified` and `IsLastOnTime` for batch `1`. -/
def Properties.EraVmNoGenesisComposes : Prop :=
  ∃ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (D : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (t : ℕ),
      SlotReachable false 0 (onboardedSlot 0 r t)
      ∧ B.entries c = (onboardedSlot 0 r t).pushed
      ∧ B.entryAt c 0 = ⟨r, 1, t⟩ ∧ R.upTo c = 1
      ∧ PositionedEndBranchAccepted B c D 0 sibs r 1 t
      ∧ EntriesTimed S B ∧ Aggregates S R
      ∧ EntriesNotEmpty ze (B.leaves c)
      ∧ PairInjOn h (fun q => TreePair h ze (B.leaves c) (B.height c) q
          ∨ VerifiedPair h sibs (B.height c) 0 (bl r 1 t) q)
      ∧ BatchLeafInjOn bl (LeafPreimage B c r 1 t)
      ∧ EndBranchVerified S R c D 1 ∧ IsLastOnTime S c D 1

/-- **A MIGRATION GAP INSIDE THE TREE.**  Registered at `49`, batch `50` pushed,
`setMigratingChainBatchNumber(80)`, batch `81` pushed: the tree is `[50, 81]`.  The honest
END branch at position `1` for batch `81` passes under the bounded premises.  The zero check
fires at level `1`.  It yields `EndBranchVerified` for batch `81`. -/
def Properties.MigrationGapInsideTreeWitness : Prop :=
  ∃ (σ : ChainTreeSlot) (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (S : System) (c : Chain) (D : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (t : ℕ),
      SlotReachable false 49 σ
      ∧ σ.pushed.map BatchEntry.batchNumber = [50, 81]
      ∧ B.entries c = σ.pushed
      ∧ PositionedEndBranchAccepted B c D 1 sibs r 81 t
      ∧ EntriesNotEmpty ze (B.leaves c)
      ∧ PairInjOn h (fun q => TreePair h ze (B.leaves c) (B.height c) q
          ∨ VerifiedPair h sibs (B.height c) 1 (bl r 81 t) q)
      ∧ BatchLeafInjOn bl (LeafPreimage B c r 81 t)
      ∧ (∃ l < B.height c, (1 / 2 ^ l) % 2 = 0)
      ∧ EntriesTimed S B ∧ Aggregates S R
      ∧ EndBranchVerified S R c D 81

/-! ## What is load-bearing -/

/-- **THE PINNED DISJUNCTS ARE NOT A TAUTOLOGY.**  An authenticated in-range path at a
position that is NOT last (position `1` of `[5, 7, 9]`, honest, under the colliding
`demoHash`), whose submitted preimage is the entry stored there: the submitted preimage
is not the last entry, and no `PositionedEndBreak` exists.  Only `zeroRightSiblings`
fails. -/
def Properties.PositionedConclusionNotAlways : Prop :=
  ∃ (h : Hash) (ze : UInt256) (bl : BatchLeafHash) (R : SlRoot)
    (B : PositionedBacking h ze bl R) (c : Chain) (pos : ℕ) (sibs : ℕ → UInt256)
    (r : UInt256) (N t : ℕ),
      pos < (B.entries c).length
      ∧ walkPure h sibs 0 (B.height c) pos (bl r N t) = rootOf h ze (B.leaves c) (B.height c)
      ∧ ¬ (SubmittedIsLastEntry B c r N t ∨ PositionedEndBreak B c pos sibs r N t)

/-- **WITHOUT THE LEAF HASH, THE POSITION DOES NOT FIX THE BATCH NUMBER.**  For every node
hash and IMT hash: a chain onboarded at `100` commits the leg's value during batch `101`,
on time.  Under the leaf hash `rootLeaf`, which does not bind the batch number, a prover
submits the preimage `(5, 0, 0)` for the leaf at position `0`, which holds batch `101`.
The walk, the zero check, the range and the deadline comparison all pass at the last
position.  The absence proof against batch `0`'s empty tree is honest.  The positioned gate
passes for a leg that was delivered.  `Aggregates` and `EntriesTimed` hold.  The located
break that carries the false conclusion is the `LeafPreimageClash`: no `AbsenceBreak`, no
`PinnedBreak`, no `PathCollision`. -/
def Properties.BatchNumberForgeryLocatesLeafClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a : UInt256), 0 < a →
    ∃ (cv : CommitValue) (F : Flow) (leg : FlowLeg) (p : ImtProof) (sibs : ℕ → UInt256),
      Wf (deliveringSystem 100 a)
      ∧ Aggregates (deliveringSystem 100 a) (onboardedRoot 100)
      ∧ EntriesTimed (deliveringSystem 100 a) (flatOnboardedBacking 100 h)
      ∧ PositionedLegRefundableAcceptedBy h z0 hl cv (deliveringSystem 100 a)
          (flatOnboardedBacking 100 h) F leg 0 p 0 sibs 5 0
      ∧ ¬ (∀ n, (deliveringSystem 100 a).time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs ((deliveringSystem 100 a).tree leg.chain n)))
      ∧ ¬ AbsenceBreak h z0 hl (deliveringSystem 100 a) F.deadline leg.chain 0 p
      ∧ ¬ PinnedBreak h 0 ((flatOnboardedBacking 100 h).leaves leg.chain) 0
      ∧ ¬ PathCollision h 0 ((flatOnboardedBacking 100 h).leaves leg.chain) sibs 0
          ((flatOnboardedBacking 100 h).height leg.chain) 0 (rootLeaf 5 0 0)
      ∧ LeafPreimageClash rootLeaf ((flatOnboardedBacking 100 h).entryAt leg.chain 0) ⟨5, 0, 0⟩

/-- **THE MIGRATION-GAP HYPOTHESIS IS LOAD-BEARING.**  For every node hash and IMT hash, in
`Contracts.Timeout.staleSystem a`: batch `0` is pushed at time `0`, and batch `1` settles
at time `0` with the leg's value but is never pushed to this layer.  `R` is
`Contracts.Timeout.staleRoot`, created at time `1`.  `RootEntriesPushed`, `ClockFromPushes`
and `AggregatesPushed` hold, `GapsAfterRootLate` fails.  The honest END branch at position `0`
for batch `0` passes the positioned gate with no located break of any kind, while the leg
was committed on time. -/
def Properties.MigrationGapIsLoadBearing : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a : UInt256), 0 < a →
    ∃ (cv : CommitValue) (F : Flow) (leg : FlowLeg) (p : ImtProof) (sibs : ℕ → UInt256),
      Wf (staleSystem a)
      ∧ RootEntriesPushed stalePushes (staleBacking h)
      ∧ ClockFromPushes (staleSystem a) stalePushes
      ∧ AggregatesPushed stalePushes (staleBacking h)
      ∧ ¬ GapsAfterRootLate (staleSystem a) stalePushes staleRoot
      ∧ PositionedLegRefundableAcceptedBy h z0 hl cv (staleSystem a) (staleBacking h) F leg 0 p
          0 sibs 5 0
      ∧ ¬ PositionedEndBreak (staleBacking h) leg.chain 0 sibs 5 0 0
      ∧ ¬ AbsenceBreak h z0 hl (staleSystem a) F.deadline leg.chain 0 p
      ∧ (staleSystem a).time leg.chain 1 ≤ F.deadline
      ∧ legValue cv F leg ∈ keys (toAbs ((staleSystem a).tree leg.chain 1))

end Contracts.BatchPosition
