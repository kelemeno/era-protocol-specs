import EraSpec.Protocol.InteropAtomicity.Specs.DispatchLiveness

/-!
# Properties: an informed sender's atomic dispatch is enabled, unless a pinned clash

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.DispatchLiveness`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.DispatchLiveness`.

## (a) How many hops a hint needs

In a valid tree the deployed search from a hint succeeds exactly when its fuel covers
`hopsNeeded`, the number of occupied leaves strictly between the hint's value and the inserted
value (`SearchSucceedsIffHopsWithinFuel`). So:

* the exact hint needs no hop, succeeds with any fuel, and the insert lands on it
  (`ExactHintSucceeds`, `ExactHintIffNoHops`); for every fresh nonzero value there is exactly
  one exact hint (`ExactHintExistsAndIsUnique`);
* the deployed insert flow succeeds iff the hint is at most `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5`
  hops away (`HintWithinFiveHopsSucceeds`);
* a hint that was exact when the sender read the tree still works after at most five other
  inserts landed first (`StaleExactHintSurvivesFiveInserts`): each insert adds at most one hop.

## (b) No constant fuel suffices

For every fuel `k` below the word size there is an honest tree, `chainTree (k + 1)`, on which a
valid starting hint needs `k + 1` hops (`HopsNeededUnbounded`). This is the general form that
`Contracts.InteropCommitmentTree.Properties.HonestInsertRevertsAtDeployedFuel` states for
`k = 5` only.

## (c) An honest atomic dispatch is enabled, or a pinned clash with the log

`Step` composes the center's salt check, `_validateAtomicBundle` and the whole `append` (manager
guard and tree insert). Its runs project onto runs of both component models
(`DispatchRunProjectsToCenter`, `DispatchRunProjectsToAppendPath`).

* **The manager's guard.** A fresh `(sender, salt)` dispatch passes
  `ManagerLegAlreadyCommitted`, or its leg was already committed by a logged dispatch with which
  it shares one leg through a cross-sender salt clash or a bundle-hash clash
  (`FreshDispatchPassesManagerGuardOrClash`, in `Contracts.InteropCenter`'s model alone). This
  is O1's open item 5.
* **Headline.** An atomic dispatch with an unused `(sender, salt)`, a well-formed and validated
  bundle, a nonzero commit value and the exact hint has a step, landing on that hint, or a
  `DispatchClash` with the log holds (`HonestDispatchEnabledOrClash`). The same holds for any hint
  within five hops (`DispatchWithinFiveHopsEnabledOrClash`).
* **Sharp.** No hint works iff a `DispatchClash` holds (`AtomicDispatchBlockedIffClash`). So a
  clash is the only thing that blocks the leg; it blocks only that exact `(flowId, bundleHash)`,
  and a re-send with another salt is a different leg.

## Non-vacuity and the disjuncts

`HonestDispatchWitness` meets every premise of the headline on a nonempty run, with the step
present and no clash. `CommitClashBlocksHonestDispatch` fires the `CommitClash` disjunct alone
(a constant commit value, as in `Contracts.AppendPath.Properties.ClashBlocksFreshLeg`), and
`LegClashBlocksHonestDispatch` fires the shared-leg disjunct alone, once through a cross-sender
salt clash and once through a bundle-hash clash, both under a constant keccak.
-/

namespace Contracts.DispatchLiveness

open IMTAbstract
open Contracts.InteropCommitmentTree (Tree Valid lowSearch InsertGuard maxLowIndexSearchAttempts
  chainTree Reaches Initialized toAbs setup)
open Contracts.AppendPath (ChainState AppendSucceeds InsertSucceeds)
open Contracts.InteropCenter (Params Dispatch FormedBy Validated bundleHash
  CrossSenderSaltClash BundleClash wParams collidingParams)
open Contracts.AtomicFlowManager (AppendGuard)
open Contracts.Atomicity (CommitValue)
open Contracts.Refund (CommitClash)

/-! ## (a) How many hops a hint needs -/

/-- **THE DEPLOYED SEARCH SUCCEEDS EXACTLY WHEN THE FUEL COVERS THE HOPS.** In a valid tree, from
any occupied hint, the loop `IndexedMerkleTree.sol:85-92` with `fuel` hops returns a leaf iff
`hopsNeeded` is at most `fuel`. Each hop moves to the immediate successor in the sorted list
(`GapSound`), so it passes exactly one of the leaves `hopsNeeded` counts. -/
def Properties.SearchSucceedsIffHopsWithinFuel : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (fuel hint : ℕ), hint < T.leafCount →
    ((∃ low, lowSearch T v fuel hint = some low) ↔ hopsNeeded T v hint ≤ fuel)

/-- **THE EXACT HINT SUCCEEDS WITH ANY FUEL, AND THE INSERT LANDS ON IT.** The loop exits at the
exact hint without a hop, so the search returns the hint itself whatever the fuel. In a valid
tree, for a nonzero value not yet registered, the deployed insert flow then passes every check
(`Contracts.AppendPath.InsertSucceeds`) with the hint as low leaf, and the guard the tree theory
assumes holds there. -/
def Properties.ExactHintSucceeds : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint : ℕ), ExactHint T v hint →
    (∀ fuel, lowSearch T v fuel hint = some hint) ∧
    (Valid T → v ≠ 0 → T.valueToIndex v = 0 →
      InsertSucceeds T v hint hint ∧ InsertGuard T v hint)

/-- **A HINT IS EXACT IFF IT NEEDS NO HOP.** For an occupied hint below `v` in a valid tree. -/
def Properties.ExactHintIffNoHops : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ), hint < T.leafCount →
    (T.leaf hint).value < v → (ExactHint T v hint ↔ hopsNeeded T v hint = 0)

/-- **EVERY FRESH VALUE HAS EXACTLY ONE EXACT HINT.** In a valid tree, for a nonzero value that is
not a key, there is one and only one exact hint: the leaf holding the largest value below it. So
"the exact hint" is well defined, and a sender who reads the tree can compute it. -/
def Properties.ExactHintExistsAndIsUnique : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256), v ≠ 0 → v ∉ keys (toAbs T) →
    ∃! hint, ExactHint T v hint

/-- **A HINT WITHIN FIVE HOPS SUCCEEDS; ONE FURTHER AWAY REVERTS.** In a valid tree, for a nonzero
value not yet registered and an occupied hint below it, the deployed insert flow (with
`MAX_LOW_INDEX_SEARCH_ATTEMPTS`) succeeds for some low leaf iff the hint needs at most five hops.
Past five it reverts with `IMTLowLeafNextTooSmall` (`IndexedMerkleTree.sol:86-88`), although a
correct low leaf exists. -/
def Properties.HintWithinFiveHopsSucceeds : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ), v ≠ 0 → T.valueToIndex v = 0 →
    hint < T.leafCount → (T.leaf hint).value < v →
      ((∃ low, InsertSucceeds T v hint low) ↔ hopsNeeded T v hint ≤ maxLowIndexSearchAttempts)

/-- **A HINT READ BEFORE AT MOST FIVE OTHER INSERTS STILL SUCCEEDS.** A sender computes the exact
hint for `v` on tree `T`. Before the transaction lands, `m ≤ 5` other guarded inserts happen
(`ReachesIn T m U`). If `v` is still not registered in `U`, the deployed insert flow from that
hint still succeeds in `U`: every insert adds at most one hop. -/
def Properties.StaleExactHintSurvivesFiveInserts : Prop :=
  ∀ (T U : Tree) (m : ℕ) (v : UInt256) (hint : ℕ), Valid T → ExactHint T v hint →
    ReachesIn T m U → m ≤ maxLowIndexSearchAttempts → v ≠ 0 → U.valueToIndex v = 0 →
      ∃ low, InsertSucceeds U v hint low

/-! ## (b) No constant fuel suffices -/

/-- **FOR EVERY FUEL, AN HONEST TREE WHOSE HINT NEEDS ONE HOP MORE.** For every `k` with
`k + 2` below the word size: the honest run `chainTree (k + 1)` (`setup`, then the values
`1, …, k + 1`, each through the previous leaf) is reachable, has `k + 2` leaves, and for the fresh
value `k + 2` the sentinel hint `0` is a valid starting hint that needs exactly `k + 1` hops. So
the search with fuel `k` reverts, while the exact hint `k + 1` works. With `k = 5` this is the
deployed constant: no fixed `MAX_LOW_INDEX_SEARCH_ATTEMPTS` makes every honest hint succeed. -/
def Properties.HopsNeededUnbounded : Prop :=
  ∀ k : ℕ, k + 2 < UInt256.size →
    Reaches setup (chainTree (k + 1)) ∧ (chainTree (k + 1)).leafCount = k + 2
      ∧ ((chainTree (k + 1)).leaf 0).value < ((k + 2 : ℕ) : UInt256)
      ∧ (chainTree (k + 1)).valueToIndex ((k + 2 : ℕ) : UInt256) = 0
      ∧ hopsNeeded (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) 0 = k + 1
      ∧ lowSearch (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) k 0 = none
      ∧ ExactHint (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) (k + 1)

/-! ## (c) The composed send path -/

/-- **THE CENTER HALF OF A SEND-PATH RUN IS A DEPLOYED CENTER RUN.** So every result of
`Contracts.InteropCenter.Properties` (topic `Dispatch`) holds of the composed model. -/
def Properties.DispatchRunProjectsToCenter : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X : State), Reach P cv genesis X →
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init X.center

/-- **THE MANAGER-AND-TREE HALF IS AN APPEND-PATH RUN, WITH THE ATOMIC DISPATCHES AS ITS LOG.**
So every result of `Contracts.AppendPath.Properties` (topic `OncePerLeg`) holds of the composed
model, for chain `P.chainId`. -/
def Properties.DispatchRunProjectsToAppendPath : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X : State), Reach P cv genesis X →
    Contracts.AppendPath.Steps cv P.chainId Contracts.AppendPath.genesis X.chain
      (appendLog P X.log)

/-- **A FRESH DISPATCH PASSES `ManagerLegAlreadyCommitted`, OR SHARES A LEG THROUGH A PINNED
CLASH.** In `Contracts.InteropCenter`'s deployed model, from fresh storage: a dispatch whose
`(sender, salt)` is unused and whose bundle is formed as `_sendBundle` forms it finds its leg
`Unset` (`AtomicFlowManager.sol:93`), or a logged atomic dispatch committed the same
`(flowId, bundleHash)` and the two are tied by a cross-sender salt clash (one bundle) or by a
bundle-hash clash (two bundles, one hash). -/
def Properties.FreshDispatchPassesManagerGuardOrClash : Prop :=
  ∀ (P : Params) (S : Contracts.InteropCenter.State),
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P Contracts.InteropCenter.init S →
    ∀ d : Dispatch, S.saltUsed d.sender d.salt = false → FormedBy P d →
      AppendGuard S.manager d.atomicSend.flowId (bundleHash P d.bundle) ∨
        ∃ d' ∈ S.log, d'.isAtomic = true ∧ d'.atomicSend.flowId = d.atomicSend.flowId ∧
          bundleHash P d'.bundle = bundleHash P d.bundle ∧
          (CrossSenderSaltClash P d d' ∨ BundleClash P d.bundle d'.bundle)

/-- **HEADLINE (c): AN INFORMED SENDER'S ATOMIC DISPATCH IS ENABLED, OR A PINNED CLASH.** On every
reachable state of the composed send path: an atomic dispatch whose `(sender, salt)` is unused,
whose bundle is formed as `_sendBundle` forms it and carries no native value, whose commit value
is nonzero, and whose hint is the exact hint for that commit value, has a step that lands on its
hint. Otherwise a `DispatchClash` with the log holds.

The commit value is `keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash))`
(`AtomicInteropProof.sol:100-102`), so "nonzero" is the pinned premise that keccak is not `0` on
that one preimage (`IMTValueZero`, `IndexedMerkleTree.sol:69-71`, would revert otherwise). The
checks `Contracts.InteropCenter` omits as reject-only (pause, destination registration, fees and
`msg.value`) are the sender's to meet and are not modelled (Specs header). -/
def Properties.HonestDispatchEnabledOrClash : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X : State), Reach P cv genesis X →
    ∀ d : Dispatch, d.isAtomic = true → X.saltUsed d.sender d.salt = false → FormedBy P d →
      Validated d.bundle → commitValueOf P cv d ≠ 0 →
      ExactHint X.chain.tree (commitValueOf P cv d) d.atomicSend.lowNullifierIndex →
      Step P cv X (X.afterAtomic P cv d d.atomicSend.lowNullifierIndex)
        ∨ DispatchClash P cv X.log d

/-- **THE SAME FOR ANY HINT WITHIN FIVE HOPS.** As the headline, with the exact hint relaxed to an
occupied hint below the commit value that needs at most `MAX_LOW_INDEX_SEARCH_ATTEMPTS` hops; the
step then lands on the leaf the search reaches. -/
def Properties.DispatchWithinFiveHopsEnabledOrClash : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X : State), Reach P cv genesis X →
    ∀ d : Dispatch, d.isAtomic = true → X.saltUsed d.sender d.salt = false → FormedBy P d →
      Validated d.bundle → commitValueOf P cv d ≠ 0 →
      d.atomicSend.lowNullifierIndex < X.chain.tree.leafCount →
      (X.chain.tree.leaf d.atomicSend.lowNullifierIndex).value < commitValueOf P cv d →
      hopsNeeded X.chain.tree (commitValueOf P cv d) d.atomicSend.lowNullifierIndex
        ≤ maxLowIndexSearchAttempts →
      (∃ low, Step P cv X (X.afterAtomic P cv d low)) ∨ DispatchClash P cv X.log d

/-- **NO HINT WORKS IFF A PINNED CLASH.** On every reachable state, for a dispatch whose
`(sender, salt)` is unused, whose bundle is formed as `_sendBundle` forms it and whose commit value
is nonzero: the composed `append` of its leg fails for every hint iff a `DispatchClash` with the
log holds. -/
def Properties.AtomicDispatchBlockedIffClash : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X : State), Reach P cv genesis X →
    ∀ d : Dispatch, X.saltUsed d.sender d.salt = false → FormedBy P d →
      commitValueOf P cv d ≠ 0 →
      ((∀ i, ¬ AtomicSendEnabled P cv X (withHint d i)) ↔ DispatchClash P cv X.log d)

/-! ## Non-vacuity and the disjuncts -/

/-- **A STALE HINT AT WORK.** On `setup` the sentinel `0` is the exact hint for the value `2`. One
other insert lands first (the value `1` through the sentinel, `ReachesIn setup 1`). The sentinel
is then no longer exact for `2`, needs one hop, and the deployed insert flow from it still
succeeds: the premises of `StaleExactHintSurvivesFiveInserts` hold with `m = 1`, and its
conclusion is not the exact-hint case. -/
def Properties.StaleHintWitness : Prop :=
  Valid setup ∧ ExactHint setup 2 0 ∧ ReachesIn setup 1 wOneInsertTree ∧
    wOneInsertTree.valueToIndex 2 = 0 ∧ ¬ ExactHint wOneInsertTree 2 0 ∧
    hopsNeeded wOneInsertTree 2 0 = 1 ∧ ∃ low, InsertSucceeds wOneInsertTree 2 0 low

/-- **THE HEADLINE'S PREMISES HOLD ON A NONEMPTY RUN, THE STEP EXISTS, AND NO CLASH.** On the honest
chain `wParams` with commit value `fun _ b => b`: after sender `1`'s atomic leg (bundle hash `1`),
sender `2`'s leg (bundle hash `2`) with the exact hint `1` meets every premise, has its step, and
no `DispatchClash` holds. The stale hint `0` (one hop) also works. -/
def Properties.HonestDispatchWitness : Prop :=
  Reach wParams bundleCv genesis wX1 ∧ wX1.log ≠ [] ∧
    wNext.isAtomic = true ∧ wX1.saltUsed wNext.sender wNext.salt = false ∧
    FormedBy wParams wNext ∧ Validated wNext.bundle ∧ commitValueOf wParams bundleCv wNext ≠ 0 ∧
    ExactHint wX1.chain.tree (commitValueOf wParams bundleCv wNext)
      wNext.atomicSend.lowNullifierIndex ∧
    Step wParams bundleCv wX1 (wX1.afterAtomic wParams bundleCv wNext 1) ∧
    ¬ DispatchClash wParams bundleCv wX1.log wNext ∧
    AtomicSendEnabled wParams bundleCv wX1 (withHint wNext 0)

/-- **THE `CommitClash` DISJUNCT FIRES ALONE.** With the constant commit value `1`, after sender
`1`'s atomic leg, sender `2`'s different leg meets every premise of the headline, with the exact
hint `0` for the value `1`, yet no hint lets it be appended: its commit value is already a key.
The clash is a `CommitClash` with the logged leg, and the two legs are different. -/
def Properties.CommitClashBlocksHonestDispatch : Prop :=
  ∃ (X : State) (d : Dispatch), Reach wParams constCv genesis X ∧ d.isAtomic = true ∧
    X.saltUsed d.sender d.salt = false ∧ FormedBy wParams d ∧ Validated d.bundle ∧
    commitValueOf wParams constCv d ≠ 0 ∧
    ExactHint X.chain.tree (commitValueOf wParams constCv d) d.atomicSend.lowNullifierIndex ∧
    (∀ i, ¬ AtomicSendEnabled wParams constCv X (withHint d i)) ∧
    DispatchClash wParams constCv X.log d ∧
    ∀ d' ∈ X.log, legOf wParams d' ≠ legOf wParams d

/-- **THE SHARED-LEG DISJUNCT FIRES ALONE, THROUGH EITHER CLASH.** Under a constant keccak
(`collidingParams`) and commit value `1`. (i) Senders `1` and `2` with one salt and one indirect
call form one bundle; after the first is dispatched, the second meets every premise of the
headline with its exact hint, but no hint works: the leg is already committed, and the tie is a
cross-sender salt clash. (ii) Sender `1` with salt `1` and then salt `2` forms two different
bundles with one hash; the second is blocked the same way, and the tie is a bundle-hash clash. In
both, no `CommitClash` holds against the log. -/
def Properties.LegClashBlocksHonestDispatch : Prop :=
  (∃ (X : State) (d : Dispatch), Reach collidingParams constCv genesis X ∧ d.isAtomic = true ∧
    X.saltUsed d.sender d.salt = false ∧ FormedBy collidingParams d ∧ Validated d.bundle ∧
    commitValueOf collidingParams constCv d ≠ 0 ∧
    ExactHint X.chain.tree (commitValueOf collidingParams constCv d)
      d.atomicSend.lowNullifierIndex ∧
    (∀ i, ¬ AtomicSendEnabled collidingParams constCv X (withHint d i)) ∧
    (∃ d' ∈ X.log, d'.isAtomic = true ∧ legOf collidingParams d' = legOf collidingParams d ∧
      CrossSenderSaltClash collidingParams d d') ∧
    ∀ d' ∈ X.log, ¬ CommitClash constCv (legOf collidingParams d) (legOf collidingParams d'))
  ∧
  (∃ (X : State) (d : Dispatch), Reach collidingParams constCv genesis X ∧ d.isAtomic = true ∧
    X.saltUsed d.sender d.salt = false ∧ FormedBy collidingParams d ∧ Validated d.bundle ∧
    commitValueOf collidingParams constCv d ≠ 0 ∧
    ExactHint X.chain.tree (commitValueOf collidingParams constCv d)
      d.atomicSend.lowNullifierIndex ∧
    (∀ i, ¬ AtomicSendEnabled collidingParams constCv X (withHint d i)) ∧
    (∃ d' ∈ X.log, d'.isAtomic = true ∧ legOf collidingParams d' = legOf collidingParams d ∧
      BundleClash collidingParams d.bundle d'.bundle ∧ ¬ CrossSenderSaltClash collidingParams d d') ∧
    ∀ d' ∈ X.log, ¬ CommitClash constCv (legOf collidingParams d) (legOf collidingParams d'))

end Contracts.DispatchLiveness
