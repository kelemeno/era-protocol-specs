import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# Model: the reclaim capstones read against the deployed absence check

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.IndexedMerkleTree.Properties.ReclaimGateFaithful`, proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful`.

## The gap this topic closes

The reclaim-side capstones of `Specs/Model.lean` (`reclaimable_iff_absent`,
`present_not_reclaimable`, `delivered_and_reclaimed_impossible`,
`delivered_leg_available_forever`, and their genesis-rooted forms
`guardedEvolution_reclaimable_iff_absent` / `guardedEvolution_delivered_available_forever`)
model the refund path's absence check as

    ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)          -- `MemberGate`

so the presented low leaf is a MEMBER of the snapshot by hypothesis.  In the contract the
low leaf is the prover's, and the check does not test membership.
`IndexedMerkleTree.verifyNonInclusion(_root, _value, _lowLeaf, _lowLeafIndex, _lowLeafProof)`
(c67894b9 `IndexedMerkleTree.sol:153-171`) reverts on `_value == 0`, on
`_lowLeaf.value >= _value` and on `_lowLeaf.nextValue != 0 && _lowLeaf.nextValue <= _value`,
and otherwise returns `Merkle.calculateRootMemory(_lowLeafProof, _lowLeafIndex,
hashLeaf(_lowLeaf)) == _root`.  The leaf, its index, the path and the path length are all
the prover's.  Which leaves the check accepts is therefore decided by the root, and the
root's padding constant decides what an EMPTY position authenticates:

* **c67894b9** (the source pin), `IndexedMerkleTree.sol:47-49`:

      bytes32 zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}));
      self.tree.setup(zeroLeafHash);
      self.tree.pushNewLeaf(zeroLeafHash);

  Every empty level-0 position of the `FullMerkle` tree hashes as `hashLeaf({0,0,0})`, so
  a padded index authenticates the leaf `{0,0,0}`.  Its window (`value = 0`,
  `nextValue = 0`) straddles every nonzero value, and once a value has been inserted its
  projection `⟨0, 0⟩` is not in the snapshot's leaf set
  (`IMTAbstract.ModelStrong.Properties.padding_leaf_forges_on_guarded_history`).
  In this model the pin's padding constant is `zeroLeafHash hl = hl ⟨0,0,0⟩`
  (`L2InteropCommitmentTree/Specs/CachedRoot.lean`).
* **b17415d20** (head of `draft/v0.35.0`), `IndexedMerkleTree.sol:51-52` and
  `Config.sol:141`:

      self.tree.setup(IMT_EMPTY_LEAF_HASH);
      self.tree.pushNewLeaf(hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0})));
      bytes32 constant IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf");

  The padding constant is a fixed value `z0` that is not defined through `hashLeaf`.
  `main` at 70096e2ea has the same `IndexedMerkleTree.sol` (the constant is at
  `Config.sol:90`), and so does e561b9cc2 (`IndexedMerkleTree.sol:51-52`, the constant at
  `Config.sol:134`); `Merkle.sol` and `FullMerkle.sol` are unchanged from c67894b9 at all
  three.  `DedicatedPadding hl z0` below is the one inequality between named constants
  this topic takes about the dedicated constant, and it holds for `keccak256`.  Computed
  off-line with Foundry's
  `cast keccak`: `keccak256(abi.encode(0,0,0))` (96 zero bytes) is
  `0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21`, and
  `IMT_EMPTY_LEAF_HASH` is
  `0x07a2eee29e5f66808854f031930e2c720a817e17f9ac7083092ef9c1fc8acf39`.

Apart from the padding constant the two revisions agree on what this topic models.  Both
`setup`s push the leaf hash `hashLeaf({0,0,0})` and write the sentinel `{0,0,0}`; both
`insert`s have the same guards and the same `updateLeaf`/`pushNewLeaf` writes.  The pin's
low-leaf search stops after `MAX_LOW_INDEX_SEARCH_ATTEMPTS` hops and b17415d20's
(`:90-93`) does not, which changes only which inserts revert: an insert that returns at
either revision has ended its search at a low leaf meeting `InsertGuard`
(`Contracts.InteropCommitmentTree.Properties.SearchYieldsGuard` holds for every search
length) and writes `Contracts.InteropCommitmentTree.insert`, so its runs are `HRun`s.

## What is modelled

* `DeployedGate h z0 hl S v`: `verifyNonInclusion` accepts SOME submission
  `(ℓ, idx, sibs, k)` for `v` against the root `S` publishes at its own `_height`
  (`HState.root`, padding `z0`).  This is the IMT absence check of the refund path as
  deployed; membership of the low leaf is not part of it.
* `BreakFreeGate h z0 hl S v`: the same check restricted to submissions on which no
  `TreeRootBreak` (`L2InteropCommitmentTree/Specs/TreeRoot.lean`) is located.
  `TreeRootBreak` is a predicate on the submission (siblings, length, index, leaf) and the
  snapshot's leaf-hash list and height: a wrong-length break, a node-hash collision on the
  submitted path, a `hashLeaf` collision with the occupied leaf, or a padding hit.
* `ReclaimDichotomyReading` / `DeliveryFinalityReading`: the readings of
  `guardedEvolution_reclaimable_iff_absent` and of part 2 of
  `guardedEvolution_delivered_available_forever` with `DeployedGate` in place of
  `MemberGate`, along every run from `setup` (`HRun` from `hSetup`, whose leaf-set
  projection `absHistory` is a `GuardedEvolution` from the genesis singleton).
* `cSetupPad` / `CReachesPad`: `IndexedMerkleTree.setup` and its reached states
  with `FullMerkle`'s whole storage and the padding constant as a parameter, so the root
  `IndexedMerkleTree.root()` returns at either revision can be compared with `HState.root`.

## Model boundary

* The root is `HState.root`, the fold over the leaf hashes at the state's own `_height`.
  That this is what the transcribed `root()` returns, on every state the transcribed
  contract reaches, at every padding constant, is `Properties.StoredRootAtPaddingIsPublished` with
  `Properties.ReachedStatesLiftAtPadding` (for the pin's constant also
  `Contracts.InteropCommitmentTree.Properties.CReachesRootIsPublished`).  That the compiled
  library executes the `FullMerkle` transcription is `MODEL-FULLMERKLE`, not proved here.
* `PathAccepts` omits `calculateRootMemory`'s `pathLength >= 256` revert
  (`Merkle.sol:134-136`).  So `DeployedGate` can accept a submission of length 256 or more
  that the contract rejects.  This only enlarges the set of submissions the located-break
  results cover.  The countermodels and witnesses here use the published height (at most
  2), and the liveness results use the published height, which stays below 256 until the
  tree holds more than `2^255` leaves (`MODEL-FULLMERKLE`).
* Only the IMT absence check is modelled.  The refund path's other checks (the timeout
  branches, the settlement-layer authentication of the root) are abstracted as in
  `Specs/Model.lean`: step `j`'s published root is the one the absence proof is checked
  against, and the deadline is the abstract pin `D < t (j + 1)` on a monotone settlement
  clock `t`, not a comparison the deployed gate makes.
* `keccak256` is not modelled.  Every statement quantifies over the node hash `h` and the
  leaf hash `hl`.  The hash premises are `DedicatedPadding`, an inequality between two named
  constants, and, in `Properties.DedicatedPaddingRefundOfDeliveredNeedsCollision`,
  `hl ℓ ≠ z0` for the one presented leaf; no global injectivity is assumed.
-/

namespace IMTAbstract.ReclaimGateFaithful

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The two gates -/

/-- The capstones' absence check on a leaf set: some MEMBER leaf's window straddles `v`.
This is the left-hand side of `IMTAbstract.Properties.guardedEvolution_reclaimable_iff_absent`. -/
def MemberGate (s : Finset AbsLeaf) (v : UInt256) : Prop :=
  ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- The leaf-set history the capstones reason about, read off a run: the projection
`toAbs` of each step's list state. -/
def absHistory (R : ℕ → HState) : ℕ → Finset AbsLeaf :=
  fun n => toAbs (R n).tree

/-- **The absence check as deployed.**  `IndexedMerkleTree.verifyNonInclusion` returns
`true` for `v` on SOME submitted low leaf `ℓ`, index `idx`, sibling stream `sibs` and path
length `k`, against the root `S` publishes at its own `_height`, with padding constant `z0`.
Nothing requires `ℓ` to be a leaf of `S`. -/
def DeployedGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256) :
    Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k

/-- **The absence check with the membership obligation made explicit.**  As
`DeployedGate`, restricted to submissions on which no `TreeRootBreak` is located against
`S`'s leaf-hash list and height.  The honest proof of an occupied low leaf (its own
siblings at the published height) is such a submission
(`Contracts.InteropCommitmentTree.Properties.HonestProofNoBreak`); at the pin's padding,
`Contracts.InteropCommitmentTree.Properties.ContractProofsAtStoredRoot` shows the same for
the contract's own `merklePath` output. -/
def BreakFreeGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256) :
    Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k
      ∧ ¬ TreeRootBreak h z0 hl S.tree S.height sibs k idx ℓ

/-! ## The padding premise of the later revision -/

/-- **The dedicated-padding premise, pinned.**  The padding constant is not the hash of the
zero leaf `{0,0,0}`: one inequality between two named 32-byte values.  At b17415d20 it reads
`hashLeaf({0,0,0}) ≠ IMT_EMPTY_LEAF_HASH`, which holds for `keccak256` (values in the module
header).  At c67894b9 it is false by construction, because the padding constant IS
`zeroLeafHash hl = hl ⟨0,0,0⟩`. -/
def DedicatedPadding (hl : LeafHash) (z0 : UInt256) : Prop :=
  hl ⟨0, 0, 0⟩ ≠ z0

/-! ## The capstones read with the deployed check -/

/-- **`guardedEvolution_reclaimable_iff_absent` read with the deployed check** (and
`reclaimable_iff_absent` / `present_not_reclaimable` on run snapshots), at padding `z0`:
along every run from `setup`, at every step, a nonzero value passes `DeployedGate` exactly
when it is absent.  This is the capstone's gloss "no false refunds, no missed refunds" for
the IMT absence check as deployed.  It is false at the pin's padding for every hash
(`History.Properties.PinnedReclaimDichotomyReadingFails`) and, under the toy hashes, at a dedicated
padding too (`Properties.DedicatedPaddingReadingsFailUnderToyHashes`); its "no missed refunds"
half holds at every padding (`Properties.DeployedGateLiveness`). -/
def ReclaimDichotomyReading (h : Hash) (z0 : UInt256) (hl : LeafHash) : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (DeployedGate h z0 hl (R j) v ↔ v ∉ keys (absHistory R j))

/-- **Part 2 of `guardedEvolution_delivered_available_forever` read with the deployed
check** (and `delivered_and_reclaimed_impossible`), at padding `z0`: along every run from
`setup` with a monotone settlement clock `t` and deadline `D`, a value delivered at an
on-time step fails `DeployedGate` at every step meeting the abstract pin `D < t (j + 1)`.
False at the pin's padding for every hash (`History.Properties.PinnedDeliveryFinalityReadingFails`). -/
def DeliveryFinalityReading (h : Hash) (z0 : UInt256) (hl : LeafHash) : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup →
    ∀ (t : ℕ → UInt256) (D v : UInt256) (i : ℕ), Monotone t → t i ≤ D →
      v ∈ keys (absHistory R i) →
        ∀ j : ℕ, D < t (j + 1) → ¬ DeployedGate h z0 hl (R j) v

/-! ## The stored root at either revision

The storage model with the padding constant as a parameter is `cSetupPad` / `CReachesPad`
(`L2InteropCommitmentTree/Specs/CachedRoot.lean`): `FullMerkle.setup(z0)`, then
`FullMerkle.pushNewLeaf(hashLeaf({0,0,0}))`, which is `b17415d20`'s `setup` (`:51-52`) at
`z0 = IMT_EMPTY_LEAF_HASH` and the pin's at `z0 = zeroLeafHash hl`. -/

/-! ## A settlement clock, for the witnesses -/

/-- Steps `0, 1, 2` settle at time `0`, every later step at time `1`.  With deadline `0`,
step `2` is the last on-time step, and it meets the abstract pin because step `3` settles
at time `1`. -/
def reclaimGateWitnessClock : ℕ → UInt256 := fun n => if n < 3 then 0 else 1

end IMTAbstract.ReclaimGateFaithful
