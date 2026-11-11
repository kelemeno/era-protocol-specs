import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.ChainTreeBacking

/-!
# Properties: DIM chain trees instantiate `Timeout.RootBacking`, and the last-leaf check

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.ChainTreeBacking`.  Proofs
are in `EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.ChainTreeBacking`.

* **The backing.**  `ChainTrees.backing` is a `Timeout.RootBacking` whose `upToLast` and
  `capacity` are discharged by the DIM runs, and the fold it is authenticated against is the root
  `root()` returns for that chain's storage.  The last batch's honest path is a
  `LastBatchAccepted` proof against it, so the timeout results stated over `RootBacking`
  (`LastBatchProofIdentifiesLastBatchPinned`, `EndBranchAcceptedImpliesVerifiedOn`, …) apply to
  the trees the `MessageRoot` actually keeps.
* **(g) `ContractPathLastIff`.**  On a DIM tree, the honest path of leaf `i` has a zero right
  side (the check `_verifyLastBatchInRoot` makes) iff `i` is the last leaf, under a bounded
  no-collision premise on the tree's own pairs and its leaves.  Without any premise: the last
  leaf always passes, and a passing leaf is the last or exhibits a `PinnedBreak` on the subtree
  right after it.
* **(h) `ChainZeroIsImtEmptyLeaf`.**  The chain tree's zero is the same literal as the shared
  tree's and as `EMPTY_IMT_ROOT`; under the documented identity
  `hashLeaf({0,0,0}) = EMPTY_IMT_ROOT`, the chain tree's whole zero cascade (what
  `_verifyLastBatchInRoot` compares against) is the interop commitment tree's padding cascade,
  and a freshly set-up commitment tree's root is the chain tree's level-0 zero.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf Contracts.Timeout

/-! ## The backing -/

/-- **THE BACKING IS THE STORED TREE.**  For every chain, the backing's leaves and height are
the DIM run's, its last batch index is the last leaf, and the fold `RootBacking` authenticates
against is the root `root()` returns for that chain's storage. -/
def Properties.ChainTreeBackingIsStored : Prop :=
  ∀ (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ) (c : Contracts.Atomicity.Chain),
    (T.backing created).leaves c = T.leaves c
      ∧ (T.backing created).height c = dimHeight (T.leaves c).length
      ∧ (T.slRoot created).upTo c + 1 = (T.leaves c).length
      ∧ root (T.state c)
          = some (rootOf h ze ((T.backing created).leaves c) ((T.backing created).height c))

/-- **THE LAST BATCH'S HONEST PATH IS ACCEPTED.**  Against the backing, batch `upTo c` with the
tree's own sibling stream meets every field of `LastBatchAccepted`: in range, authenticated
(the walk recomputes the stored root), and zero on the right wherever it turns left. -/
def Properties.DimLastBatchAccepted : Prop :=
  ∀ (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ) (c : Contracts.Atomicity.Chain),
    LastBatchAccepted (T.backing created) c ((T.slRoot created).upTo c)
      (honestSibs h ze (T.leaves c) ((T.slRoot created).upTo c))
      ((T.leaves c).getD ((T.slRoot created).upTo c) ze)

/-- **THE PREMISE IS SATISFIABLE.**  For every hash and zero value there are chain trees: every
chain with one leaf. -/
def Properties.ChainTreesExist : Prop :=
  ∀ (h : Hash) (ze : UInt256), Nonempty (ChainTrees h ze)

/-! ## (g) The last-leaf check on a DIM tree -/

/-- **THE LAST LEAF PASSES THE CHECK.**  On storage representing a nonempty `L` at `H`, the
honest path of the last leaf recomputes the stored root and has a zero right side. -/
def Properties.ContractPathLastHasZeroRightSide : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree),
    Represents h ze L H S → L ≠ [] →
      root S = some (rootOf h ze L H)
        ∧ walkPure h (honestSibs h ze L (L.length - 1)) 0 H (L.length - 1)
            (L.getD (L.length - 1) ze) = rootOf h ze L H
        ∧ ZeroRightSide h ze L H (L.length - 1)

/-- **A PASSING LEAF IS THE LAST, OR PINS A BREAK.**  No hash premise: if the honest path of
leaf `i` has a zero right side, then `i` is the last leaf or there is a `PinnedBreak` on the
subtree that starts at `i + 1`. -/
def Properties.ContractPathZeroRightSideIsLastOrPinnedBreak : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (i : ℕ),
    Represents h ze L H S → i < L.length → ZeroRightSide h ze L H i →
      i + 1 = L.length ∨ PinnedBreak h ze L i

/-- **(g) THE CHECK IS EXACTLY "LAST LEAF", UNDER A BOUNDED PREMISE.**  With no collision among
the tree's own pairs and its zero cascade (`TreePair`, a finite instance-determined set) and no
leaf equal to the zero value, the honest path of leaf `i` has a zero right side iff `i` is the
last leaf. -/
def Properties.ContractPathLastIff : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (i : ℕ),
    Represents h ze L H S → i < L.length → EntriesNotEmpty ze L →
    PairInjOn h (TreePair h ze L H) →
      (ZeroRightSide h ze L H i ↔ i + 1 = L.length)

/-- **ITS PREMISES ARE SATISFIABLE AND BOTH SIDES OCCUR.**  Two leaves pushed under the colliding
`demoHash`: the bounded premises hold, leaf 0 fails the check and leaf 1 passes it. -/
def Properties.ContractPathLastIffSatisfiable : Prop :=
  ∃ (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree),
    Run h ze L S ∧ Represents h ze L H S ∧ EntriesNotEmpty ze L ∧ PairInjOn h (TreePair h ze L H)
      ∧ ¬ ZeroRightSide h ze L H 0 ∧ ZeroRightSide h ze L H (L.length - 1) ∧ 0 < L.length - 1
      ∧ (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)

/-! ## (h) The empty-entry constants -/

/-- **(h) THE CHAIN TREE'S ZERO IS THE IMT'S EMPTY LEAF.**  The three source literals coincide;
and for any IMT leaf hash `hl` with the documented `hashLeaf({0,0,0}) = EMPTY_IMT_ROOT`, the
chain tree's zero cascade equals the commitment tree's padding cascade at every level, and a
freshly set-up commitment tree's root is the chain tree's zero. -/
def Properties.ChainZeroIsImtEmptyLeaf : Prop :=
  chainTreeEmptyEntryHash = sharedRootTreeEmptyHash ∧ chainTreeEmptyEntryHash = emptyImtRoot
    ∧ chainTreeEmptyEntryHash ≠ 0
    ∧ ∀ (h : Hash) (hl : Contracts.InteropCommitmentTree.LeafHash),
        Contracts.InteropCommitmentTree.zeroLeafHash hl = emptyImtRoot →
          (∀ l, zeros h chainTreeEmptyEntryHash l
              = zeros h (Contracts.InteropCommitmentTree.zeroLeafHash hl) l)
            ∧ ∃ S, Contracts.InteropCommitmentTree.cSetup h hl = some S
                ∧ S.root = some chainTreeEmptyEntryHash

/-- **ITS PREMISE IS SATISFIABLE.**  Some IMT leaf hash sends the sentinel to `EMPTY_IMT_ROOT`. -/
def Properties.ChainZeroPremiseSatisfiable : Prop :=
  ∃ hl : Contracts.InteropCommitmentTree.LeafHash,
    Contracts.InteropCommitmentTree.zeroLeafHash hl = emptyImtRoot

end Contracts.DynamicIncrementalMerkle
