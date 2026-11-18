import EraSpec.Protocol.InteropAtomicity.Specs.DispatchLiveness

/-!
# Properties: an informed sender's atomic dispatch is enabled, unless a pinned clash

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.DispatchLiveness`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.DispatchLiveness`. Everything here is about the pin
`c67894b9`; the Specs header ("At the current heads") lists what differs at the current heads.

## (a) How many hops a hint needs

In a valid tree the deployed search from an occupied hint succeeds exactly when its fuel covers
`hopsNeeded`, the number of occupied leaves strictly between the hint's value and the inserted
value (`SearchSucceedsIffHopsWithinFuel`), and that number is below `leafCount`
(`HopsNeededBelowLeafCount`). So:

* the exact hint needs no hop, succeeds with any fuel, and the insert lands on it
  (`ExactHintSucceeds`, `ExactHintIffNoHops`); it is the occupied leaf holding the largest value
  below the inserted one (`ExactHintIsLargestBelow`), and for every fresh nonzero value there is
  exactly one (`ExactHintExistsAndIsUnique`);
* the deployed insert flow succeeds iff the hint is at most `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5`
  hops away (`HintWithinFiveHopsSucceeds`);
* a hint that was exact when the sender read the tree still works after at most five other
  inserts landed first (`StaleExactHintSurvivesFiveInserts`): each insert adds at most one hop.

## (b) No constant fuel suffices

For every fuel `k` with `k + 2` below the word size there is an honest tree, `chainTree (k + 1)`,
on which a valid starting hint needs `k + 1` hops (`HopsNeededUnbounded`). This is the general
form of `Contracts.InteropCommitmentTree.Properties.HonestInsertRevertsAtDeployedFuel`, which
states `k = 5` on one tree.

## (c) An honest atomic dispatch is enabled, or a pinned clash with the log

`Step` composes the center's salt check, `_validateAtomicBundle` and the whole `append` (manager
guard and tree insert). Its runs project onto runs of both component models
(`DispatchRunProjectsToCenter`, `DispatchRunProjectsToAppendPath`).

* **The manager's guard.** A fresh `(sender, salt)` dispatch passes
  `ManagerLegAlreadyCommitted`, or its leg was already committed by a logged dispatch with which
  it shares one leg through a cross-sender salt clash or a bundle-hash clash
  (`FreshDispatchPassesManagerGuardOrClash`, in `Contracts.InteropCenter`'s model alone).
* **Headline.** An atomic dispatch with an unused `(sender, salt)`, a well-formed and validated
  bundle, a nonzero commit value and the exact hint has a step, landing on that hint, or a
  `DispatchClash` with the log holds (`HonestDispatchEnabledOrClash`). The same holds for any hint
  within five hops (`DispatchWithinFiveHopsEnabledOrClash`), and for a hint that was exact at an
  earlier state of the run, with at most five appends in between
  (`StaleHintDispatchEnabledOrClash`).
* **Sharp.** No hint works iff a `DispatchClash` holds (`AtomicDispatchBlockedIffClash`). So,
  given the center's own checks, a clash with the log is the only thing that blocks the leg's
  `append` on the modelled checks.

## Non-vacuity and the disjuncts

`HonestDispatchWitness` meets every premise of the headline, of
`DispatchWithinFiveHopsEnabledOrClash` (with a hint one hop away) and of
`FreshDispatchPassesManagerGuardOrClash` on a nonempty run, with the step present and no clash.
`StaleHintDispatchWitness` meets every premise of `StaleHintDispatchEnabledOrClash` with a hint read
at genesis and one append in between, at whose end the hint is no longer exact, again with the step
present and no clash. The counting results of (a) take premises that every reachable tree meets
for a fresh nonzero value and an occupied hint below it: `FiveHopBoundaryWitness` instantiates them
on both sides of the boundary of `HintWithinFiveHopsSucceeds` (five hops succeed, six do not), and
`StaleHintWitness` with an exact hint and one insert in between, meeting the premises of
`StaleExactHintSurvivesFiveInserts`. `CommitClashBlocksHonestDispatch` fires the `CommitClash` disjunct alone (a constant commit value,
as in `Contracts.AppendPath.Properties.ClashBlocksFreshLeg`), and `LegClashBlocksHonestDispatch`
fires the shared-leg disjunct alone, once through a cross-sender salt clash and once through a
bundle-hash clash, both under a constant keccak.
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

/-- **THE EXACT HINT IS THE PREDECESSOR.** In a valid tree, `hint` is an exact hint for `v` iff it
is an occupied leaf below `v` whose value is the largest among the occupied leaves below `v`. -/
def Properties.ExactHintIsLargestBelow : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ),
    (ExactHint T v hint ↔
      hint < T.leafCount ∧ (T.leaf hint).value < v ∧
        ∀ k < T.leafCount, (T.leaf k).value < v → (T.leaf k).value ≤ (T.leaf hint).value)

/-- **A HINT NEEDS FEWER HOPS THAN THERE ARE LEAVES.** From an occupied hint, the leaves
`hopsNeeded` counts are occupied and exclude the hint itself, so there are fewer than
`leafCount`. With `SearchSucceedsIffHopsWithinFuel`, in a valid tree a search from an occupied hint
with `leafCount - 1` hops or more returns a leaf: the exact count behind
`Contracts.InteropCommitmentTree.Properties.LowSearchTerminates`. -/
def Properties.HopsNeededBelowLeafCount : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint : ℕ), hint < T.leafCount → hopsNeeded T v hint < T.leafCount

/-- **EVERY FRESH VALUE HAS EXACTLY ONE EXACT HINT.** In a valid tree, for a nonzero value that is
not a key, there is one and only one exact hint (by `ExactHintIsLargestBelow`, the occupied leaf
holding the largest value below it). So "the exact hint" is well defined, and a sender who reads
the tree can compute it. -/
def Properties.ExactHintExistsAndIsUnique : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256), v ≠ 0 → v ∉ keys (toAbs T) →
    ∃! hint, ExactHint T v hint

/-- **A HINT WITHIN FIVE HOPS SUCCEEDS; ONE FURTHER AWAY REVERTS.** In a valid tree, for a nonzero
value not yet registered and an occupied hint below it, the deployed insert flow (with
`MAX_LOW_INDEX_SEARCH_ATTEMPTS`) succeeds for some low leaf iff the hint needs at most five hops.
Past five, every check before the loop passes and the loop reverts with `IMTLowLeafNextTooSmall`
(`IndexedMerkleTree.sol:86-88`). -/
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
value `k + 2` the sentinel hint `0` is an occupied leaf below it that needs exactly `k + 1` hops;
the search from it with fuel `k` returns nothing (a revert), and leaf `k + 1` is the exact hint,
which succeeds with any fuel (`ExactHintSucceeds`). With `k = 5` the fuel is the deployed
constant: no fixed `MAX_LOW_INDEX_SEARCH_ATTEMPTS` makes every occupied hint below a fresh value
succeed. -/
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
checks and writes this model leaves out (pause, destinations, fees and `msg.value`, attribute
parsing, an indirect call's sender contract, the `FullMerkle` writes, gas; Specs, "What 'enabled'
means here") are not part of the statement. -/
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

/-- **THE SAME FOR A HINT READ UP TO FIVE APPENDS EARLIER.** A sender reads the tree at a reachable
state `X` and takes the exact hint for its commit value there. Its transaction lands at a later
state `Y` of the same run, after at most `MAX_LOW_INDEX_SEARCH_ATTEMPTS` appends (the tree has at
most five more leaves). If at `Y` its `(sender, salt)` is unused, and its bundle is formed as
`_sendBundle` forms it and carries no native value, and its commit value is nonzero, then the
dispatch has a step at `Y`, landing on the leaf the search reaches, or a `DispatchClash` with `Y`'s
log holds. -/
def Properties.StaleHintDispatchEnabledOrClash : Prop :=
  ∀ (P : Params) (cv : CommitValue) (X Y : State), Reach P cv genesis X → Reach P cv X Y →
    Y.chain.tree.leafCount ≤ X.chain.tree.leafCount + maxLowIndexSearchAttempts →
    ∀ d : Dispatch, d.isAtomic = true → Y.saltUsed d.sender d.salt = false → FormedBy P d →
      Validated d.bundle → commitValueOf P cv d ≠ 0 →
      ExactHint X.chain.tree (commitValueOf P cv d) d.atomicSend.lowNullifierIndex →
      (∃ low, Step P cv Y (Y.afterAtomic P cv d low)) ∨ DispatchClash P cv Y.log d

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
sender `2`'s leg (bundle hash `2`) with the exact hint `1` meets every premise of
`HonestDispatchEnabledOrClash`, has its step, and no `DispatchClash` holds. The center's view of
the run is a deployed center run, so the same dispatch also meets every premise of
`FreshDispatchPassesManagerGuardOrClash`. The same dispatch with the hint `0` (`withHint` keeps
its sender, salt, bundle and flow) is formed alike, its hint is an occupied leaf below the commit
value that is not exact and needs one hop, so it meets every premise of
`DispatchWithinFiveHopsEnabledOrClash`, and its `append` is enabled. -/
def Properties.HonestDispatchWitness : Prop :=
  Reach wParams bundleCv genesis wX1 ∧ wX1.log ≠ [] ∧
    wNext.isAtomic = true ∧ wX1.saltUsed wNext.sender wNext.salt = false ∧
    FormedBy wParams wNext ∧ Validated wNext.bundle ∧ commitValueOf wParams bundleCv wNext ≠ 0 ∧
    ExactHint wX1.chain.tree (commitValueOf wParams bundleCv wNext)
      wNext.atomicSend.lowNullifierIndex ∧
    Step wParams bundleCv wX1 (wX1.afterAtomic wParams bundleCv wNext 1) ∧
    ¬ DispatchClash wParams bundleCv wX1.log wNext ∧
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed wParams
      Contracts.InteropCenter.init wX1.center ∧
    FormedBy wParams (withHint wNext 0) ∧
    (withHint wNext 0).atomicSend.lowNullifierIndex < wX1.chain.tree.leafCount ∧
    (wX1.chain.tree.leaf (withHint wNext 0).atomicSend.lowNullifierIndex).value
      < commitValueOf wParams bundleCv (withHint wNext 0) ∧
    hopsNeeded wX1.chain.tree (commitValueOf wParams bundleCv (withHint wNext 0))
      (withHint wNext 0).atomicSend.lowNullifierIndex = 1 ∧
    ¬ ExactHint wX1.chain.tree (commitValueOf wParams bundleCv (withHint wNext 0))
      (withHint wNext 0).atomicSend.lowNullifierIndex ∧
    AtomicSendEnabled wParams bundleCv wX1 (withHint wNext 0)

/-- **THE STALE-HINT FORM'S PREMISES HOLD, AND THE HINT IS NO LONGER EXACT WHEN IT LANDS.** On the
run of `HonestDispatchWitness`: sender `2` reads the tree at genesis, where the sentinel `0` is the
exact hint for its commit value `2` (`wStaleNext`), and sender `1`'s leg is appended first (`wX1`,
one leaf more). Every premise of `StaleHintDispatchEnabledOrClash` holds for `X = genesis` and
`Y = wX1`; at `wX1` the hint is not exact, the dispatch has a step, and no `DispatchClash` holds. -/
def Properties.StaleHintDispatchWitness : Prop :=
  Reach wParams bundleCv genesis genesis ∧ Reach wParams bundleCv genesis wX1 ∧
    wX1.chain.tree.leafCount = genesis.chain.tree.leafCount + 1 ∧
    wX1.chain.tree.leafCount ≤ genesis.chain.tree.leafCount + maxLowIndexSearchAttempts ∧
    wStaleNext.isAtomic = true ∧ wX1.saltUsed wStaleNext.sender wStaleNext.salt = false ∧
    FormedBy wParams wStaleNext ∧ Validated wStaleNext.bundle ∧
    commitValueOf wParams bundleCv wStaleNext ≠ 0 ∧
    ExactHint genesis.chain.tree (commitValueOf wParams bundleCv wStaleNext)
      wStaleNext.atomicSend.lowNullifierIndex ∧
    ¬ ExactHint wX1.chain.tree (commitValueOf wParams bundleCv wStaleNext)
      wStaleNext.atomicSend.lowNullifierIndex ∧
    (∃ low, Step wParams bundleCv wX1 (wX1.afterAtomic wParams bundleCv wStaleNext low)) ∧
    ¬ DispatchClash wParams bundleCv wX1.log wStaleNext

/-- **THE FIVE-HOP BOUNDARY, ON BOTH SIDES.** On the honest seven-leaf run `chainTree 6` (`setup`,
then `1, …, 6`; topic `HintSearch`), for the fresh value `7`: the occupied hint `1` needs exactly
five hops and the deployed insert flow from it succeeds; the occupied hint `0` needs six, and from
it the flow fails for every low leaf. Both meet every premise of `HintWithinFiveHopsSucceeds`, one
on each side of its boundary. -/
def Properties.FiveHopBoundaryWitness : Prop :=
  Valid (chainTree 6) ∧ (7 : UInt256) ≠ 0 ∧ (chainTree 6).valueToIndex 7 = 0 ∧
    1 < (chainTree 6).leafCount ∧ ((chainTree 6).leaf 1).value < 7 ∧
    hopsNeeded (chainTree 6) 7 1 = maxLowIndexSearchAttempts ∧
    (∃ low, InsertSucceeds (chainTree 6) 7 1 low) ∧
    0 < (chainTree 6).leafCount ∧ ((chainTree 6).leaf 0).value < 7 ∧
    hopsNeeded (chainTree 6) 7 0 = maxLowIndexSearchAttempts + 1 ∧
    ¬ ∃ low, InsertSucceeds (chainTree 6) 7 0 low

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
