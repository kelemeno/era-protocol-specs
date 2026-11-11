import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# Model: the reclaim capstones read against the deployed refund gate

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.IndexedMerkleTree.Properties.ReclaimGateFaithful`, proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful`.

## The gap this topic closes

The reclaim-side capstones of `Specs/Model.lean` (`reclaimable_iff_absent`,
`present_not_reclaimable`, `delivered_and_reclaimed_impossible`,
`delivered_leg_available_forever`, and their genesis-rooted forms
`guardedEvolution_reclaimable_iff_absent` / `guardedEvolution_delivered_available_forever`)
model the refund gate as

    ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)          -- `MemberGate`

so the presented low leaf is a MEMBER of the snapshot by hypothesis.  The low leaf is
the prover's choice, and the deployed gate does not check membership.
`IndexedMerkleTree.verifyNonInclusion(_root, _value, _lowLeaf, _lowLeafIndex,
_lowLeafProof)` (c67894b9 `IndexedMerkleTree.sol:153-171`) reverts on `_value == 0`,
on `_lowLeaf.value >= _value` and on `_lowLeaf.nextValue != 0 && _lowLeaf.nextValue <=
_value`, and otherwise returns `Merkle.calculateRootMemory(_lowLeafProof,
_lowLeafIndex, hashLeaf(_lowLeaf)) == _root`.  The leaf, its index, the path and the
path length are all the prover's.  So which leaves the gate accepts is decided by the
root, and the root's padding constant decides whether an EMPTY position authenticates
a leaf:

* **c67894b9** (the source pin), `IndexedMerkleTree.sol:47-49`:

      bytes32 zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}));
      self.tree.setup(zeroLeafHash);
      self.tree.pushNewLeaf(zeroLeafHash);

  Every empty position of the `FullMerkle` tree hashes to `hashLeaf({0,0,0})`, so a
  padded index authenticates the NON-member leaf `{0,0,0}`, whose window
  (`nextValue = 0`) straddles every nonzero value, delivered ones included.  In this
  model the padding constant is `zeroLeafHash hl = hl ⟨0,0,0⟩` (from
  `L2InteropCommitmentTree/Specs/CachedRoot.lean`).
* **e561b9cc2** (the later revision), `IndexedMerkleTree.sol:51-52` and `Config.sol:134`:

      self.tree.setup(IMT_EMPTY_LEAF_HASH);
      self.tree.pushNewLeaf(hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0})));
      bytes32 constant IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf");

  The padding constant is a fixed value `z0` that is not tied to `hashLeaf`.
  `DedicatedPadding hl z0` is the one pinned inequality this revision needs, which
  holds for `keccak256`.  Computed off-line with Foundry's `cast keccak`:
  `keccak256(abi.encode(0,0,0))` (96 zero bytes) is
  `0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21`, and
  `IMT_EMPTY_LEAF_HASH` is
  `0x07a2eee29e5f66808854f031930e2c720a817e17f9ac7083092ef9c1fc8acf39`.

Apart from the padding constant, the two revisions agree on what this topic models.
Both `setup`s write the same sentinel leaf and the same first leaf hash
`hashLeaf({0,0,0})`.  Both `insert`s share the guards and the writes.  The pin's search
is bounded by `MAX_LOW_INDEX_SEARCH_ATTEMPTS` and the later one is not, but that only
changes when an insert reverts.  An insert that goes through produces
`Contracts.InteropCommitmentTree.insert` at the loop exit in both, and `HRun` admits
every guarded insert, so it covers the runs of both revisions.

## What is modelled

* `DeployedGate h z0 hl S v`: `verifyNonInclusion` accepts SOME submission
  `(ℓ, idx, sibs, k)` for `v` against the root `S` publishes at its own `_height`
  (`HState.root`, padding `z0`).  This is the refund gate as deployed: membership of
  the low leaf is not part of it.
* `BreakFreeGate h z0 hl S v`: the same gate restricted to submissions on which no
  `TreeRootBreak` is located.  `TreeRootBreak` (`L2InteropCommitmentTree/Specs/TreeRoot.lean`)
  is a statement about the submitted values only: a wrong-length break, a collision on
  the submitted path, a `hashLeaf` collision with the occupied leaf, or a padding hit.
  It is the explicit, checkable form of the capstones' `W ∈ S j`.
* `ReclaimDichotomyReading` / `DeliveryFinalityReading`: the real-contract readings of
  `guardedEvolution_reclaimable_iff_absent` and of part 2 of
  `guardedEvolution_delivered_available_forever`, with the deployed gate in place of
  `MemberGate`, along every run from `setup` (`HRun` from `hSetup`, whose leaf-set
  projection `absHistory` is a `GuardedEvolution` from the genesis singleton).

## Model boundary

* The root is `HState.root`, the fold over the leaf hashes at the run's own `_height`.
  That this is what `IndexedMerkleTree.root()` returns is
  `Contracts.InteropCommitmentTree.Properties.CRunRootIsPublished` (whole `FullMerkle`
  storage, pinned padding).  For a dedicated padding constant the same transcription
  applies with `IMT_EMPTY_LEAF_HASH` passed to `FullMerkle.setup`.  This topic does
  not restate it.
* The settlement layer (which root a chain verifies against, and when it settled) is
  abstracted, as in `Specs/Model.lean`: step `j`'s published root is the one the
  refund is checked against, and `t` is a monotone settlement clock.
* `keccak256` is not modelled.  Every statement quantifies over the node hash `h` and
  the leaf hash `hl`.  The only hash premise is `DedicatedPadding`, an inequality between
  two named constants; no global injectivity is assumed.
-/

namespace IMTAbstract.ReclaimGateFaithful

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The two gates -/

/-- The capstones' refund gate on a leaf set: some MEMBER leaf's window straddles `v`.
This is the left-hand side of `IMTAbstract.Properties.guardedEvolution_reclaimable_iff_absent`. -/
def MemberGate (s : Finset AbsLeaf) (v : UInt256) : Prop :=
  ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- The leaf-set history the capstones reason about, read off a run: the projection
`toAbs` of each step's list state. -/
def absHistory (R : ℕ → HState) : ℕ → Finset AbsLeaf :=
  fun n => toAbs (R n).tree

/-- **The refund gate as deployed.**  `IndexedMerkleTree.verifyNonInclusion` returns
`true` for `v` on SOME submitted low leaf `ℓ`, index `idx`, sibling stream `sibs` and
path length `k`, against the root `S` publishes at its own `_height`, with padding
constant `z0`.  Nothing requires `ℓ` to be a leaf of `S`. -/
def DeployedGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256) :
    Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k

/-- **The refund gate with the membership obligation made explicit.**  As
`DeployedGate`, restricted to submissions on which no `TreeRootBreak` is located.  The
contract's own `merklePath` output for an occupied low leaf is such a submission
(`Contracts.InteropCommitmentTree.Properties.HonestProofNoBreak`). -/
def BreakFreeGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256) :
    Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k
      ∧ ¬ TreeRootBreak h z0 hl S.tree S.height sibs k idx ℓ

/-! ## The padding premise of the later revision -/

/-- **The e561b9cc2 padding premise, pinned.**  The padding constant is not the hash of
the real zero leaf `{0,0,0}`.  It is one inequality between two named 32-byte values.
At e561b9cc2 it reads `hashLeaf({0,0,0}) ≠ IMT_EMPTY_LEAF_HASH`, which holds for
`keccak256` (values in the module header).  At c67894b9 it is false by construction,
because the padding constant IS `zeroLeafHash hl = hl ⟨0,0,0⟩`. -/
def DedicatedPadding (hl : LeafHash) (z0 : UInt256) : Prop :=
  hl ⟨0, 0, 0⟩ ≠ z0

/-! ## The real-contract readings of the capstones -/

/-- **The real-contract reading of `guardedEvolution_reclaimable_iff_absent`** (and of
`reclaimable_iff_absent` / `present_not_reclaimable` on run snapshots), at padding
`z0`: along every run from `setup`, at every step, a nonzero value passes the DEPLOYED
refund gate exactly when it is absent.  This is "no false refunds, no missed refunds"
as a statement about the contract. -/
def ReclaimDichotomyReading (h : Hash) (z0 : UInt256) (hl : LeafHash) : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (DeployedGate h z0 hl (R j) v ↔ v ∉ keys (absHistory R j))

/-- **The real-contract reading of part 2 of
`guardedEvolution_delivered_available_forever`** (and of
`delivered_and_reclaimed_impossible`), at padding `z0`: along every run from `setup`
with a monotone settlement clock `t` and deadline `D`, a value delivered at an on-time
step is refused by the DEPLOYED refund gate at every deadline-pinned step. -/
def DeliveryFinalityReading (h : Hash) (z0 : UInt256) (hl : LeafHash) : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup →
    ∀ (t : ℕ → UInt256) (D v : UInt256) (i : ℕ), Monotone t → t i ≤ D →
      v ∈ keys (absHistory R i) →
        ∀ j : ℕ, D < t (j + 1) → ¬ DeployedGate h z0 hl (R j) v

/-! ## A settlement clock, for the witnesses -/

/-- Steps `0, 1, 2` settle at time `0`, every later step at time `1`.  With deadline
`0`, step `2` is the last on-time step and is pinned by step `3`. -/
def witnessClock : ℕ → UInt256 := fun n => if n < 3 then 0 else 1

end IMTAbstract.ReclaimGateFaithful
