import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.ChainTreeBacking

/-!
# Properties: DIM chain trees instantiate `Timeout.RootBacking`, and the last-leaf check

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.ChainTreeBacking`.  Proofs
are in `EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.ChainTreeBacking`.

* **The backing.**  `ChainTrees.backing` is a `Timeout.RootBacking` at the library's minimal
  height: `capacity` is proved from the DIM runs, `upToLast` holds by the choice of `upTo`, and
  the fold it is authenticated against is the value `root()` returns for that chain's storage
  (`ChainTreeBackingIsStored`).  The honest path of each chain's last leaf meets every field of
  `LastBatchAccepted` (`DimLastBatchAccepted`; with the zero check exercised in
  `DimLastBatchAcceptedThreeLeaves`).  Instantiating the timeout result
  `LastBatchProofIdentifiesLastBatchPinned` with this backing gives
  `DimLastBatchProofIdentifiesLastBatchPinned`: a proof `LastBatchAccepted` accepts is the chain's
  last pushed leaf, or exhibits a `PinnedBreak` or a `PathCollision`.  No hash premise.
  `LastBatchAccepted` fixes the walk's length to the tree height and the index to an occupied
  leaf, which the deployed check does not.
* **What the deployed check accepts against DIM storage.**  With the length and the mask free as
  well, `DimAcceptedLastLeafAnyLengthOrBreak` reads `LastLeafFaithful.AcceptedLastLeafAnyLengthOrBreak`
  against the `root()` of DIM storage: an accepted submission has the DIM height and opens the
  last pushed leaf, or exhibits a `LastLeafAnyLengthBreak` at the DIM height.  No hash premise.
  Each of its five outcomes occurs on a DIM run: the last leaf (`DimAcceptedLastLeafThreeLeaves`,
  which also meets every premise with the zero check exercised), a wrong length
  (`DimWrongLengthOccurs`), a padded entry (`DimPaddedEntryOccurs`), a pinned break
  (`DimPinnedBreakOccurs`) and a path collision (`DimPathCollisionOccurs`).  The last two are
  also accepted by `LastBatchAccepted` at a leaf that is not the last, with only the
  `PinnedBreak`, resp. only the `PathCollision`, disjunct of
  `DimLastBatchProofIdentifiesLastBatchPinned` true.
* **The check on the honest path.**  On storage representing a nonempty `L` at `H`, `root()` is
  the fold, and the honest path of the last leaf recomputes it and passes the zero check
  (`ContractPathLastHasZeroRightSide`).  The other two statements do not read storage: for every
  `L` that fits `H` (the capacity `Represents` includes), a leaf whose honest path passes the check
  is the last or exhibits a `PinnedBreak` (no hash premise), and under a bounded no-collision
  premise on the tree's own pairs, with no leaf equal to the zero value, the honest path of leaf
  `i` passes iff `i` is the last leaf (`ContractPathLastIff`).  They are
  `LastLeaf.last_leaf_or_pinned_break` and `LastLeaf.no_pinned_break_on` on the honest sibling
  stream.  `ContractPathLastIffSatisfiable` meets the premises on the storage `setup(0)` and three
  pushes leave under a colliding hash, with both sides of the iff occurring.

The break witnesses choose words the model leaves free.  On chain (`c67894b9`) the claimed leaf
hash is a batch-leaf hash, a keccak of 128 bytes (MessageHashing.sol:78-84, :195-199), and the
tree's leaves are pushed batch-leaf hashes (MessageRootBase.sol:257-259).  So the wrong-length
instance needs a claimed batch-leaf hash equal to a node hash, the padded-entry instance a claimed
one equal to `CHAIN_TREE_EMPTY_ENTRY_HASH`, the pinned instance a pushed one equal to that
constant, and the path-collision instance a collision of the node hash on the path, which the toy
`demoHash` (`a + 2b + 1`) has (`LastLeafFaithful`, model boundary).
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful
  Contracts.Timeout

/-! ## The backing -/

/-- **THE BACKING IS THE STORED TREE.**  For every chain, the backing's leaves and height are
the DIM run's, its last leaf index is `|leaves c| - 1`, and the fold `RootBacking` authenticates
against is the value `root()` returns for that chain's storage. -/
def Properties.ChainTreeBackingIsStored : Prop :=
  ∀ (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ) (c : Contracts.Atomicity.Chain),
    (T.backing created).leaves c = T.leaves c
      ∧ (T.backing created).height c = dimHeight (T.leaves c).length
      ∧ (T.slRoot created).upTo c + 1 = (T.leaves c).length
      ∧ root (T.state c)
          = some (rootOf h ze ((T.backing created).leaves c) ((T.backing created).height c))

/-- **THE LAST LEAF'S HONEST PATH IS ACCEPTED.**  Against the backing, leaf `upTo c` with the
tree's own sibling stream and its own entry meets every field of `LastBatchAccepted`: in range,
authenticated (the walk recomputes the stored fold), and the zero check. -/
def Properties.DimLastBatchAccepted : Prop :=
  ∀ (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ) (c : Contracts.Atomicity.Chain),
    LastBatchAccepted (T.backing created) c ((T.slRoot created).upTo c)
      (honestSibs h ze (T.leaves c) ((T.slRoot created).upTo c))
      ((T.leaves c).getD ((T.slRoot created).upTo c) ze)

/-- **CHAIN TREES EXIST FOR EVERY NONEMPTY LEAF LIST.**  For every hash, zero value and nonempty
list `L`, there are chain trees in which every chain has pushed exactly `L`. -/
def Properties.ChainTreesExist : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256), L ≠ [] →
    ∃ T : ChainTrees h ze, ∀ c, T.leaves c = L

/-- **A WITNESS WITH THE ZERO CHECK EXERCISED.**  For every hash, zero value and three leaves
there are chain trees in which every chain holds `[a, b, c]`, at DIM height 2 with last leaf
index 2.  Index 2 is a left child at level 0, so `zeroRightSiblings` asks the level-0 sibling to
be `ze`: the honest path for leaf 2, whose level-0 sibling is `ze`, is accepted. -/
def Properties.DimLastBatchAcceptedThreeLeaves : Prop :=
  ∀ (h : Hash) (ze a b c : UInt256), ∃ T : ChainTrees h ze,
    ∀ (created : ℕ) (ch : Contracts.Atomicity.Chain),
      T.leaves ch = [a, b, c] ∧ (T.backing created).height ch = 2
        ∧ (T.slRoot created).upTo ch = 2 ∧ (2 / 2 ^ 0) % 2 = 0
        ∧ honestSibs h ze [a, b, c] 2 0 = ze
        ∧ LastBatchAccepted (T.backing created) ch 2 (honestSibs h ze [a, b, c] 2) c

/-- **A LAST-BATCH PROOF `LastBatchAccepted` ACCEPTS AGAINST DIM CHAIN TREES IS THE LAST PUSHED
LEAF, OR PINS A COLLISION.**  `Timeout.LastBatchProofIdentifiesLastBatchPinned` with the backing
built from DIM runs: if `(N, sibs, x)` is accepted, then `N` is the index of the chain's last pushed
leaf, or there is a `PinnedBreak` on the subtree after `N`, or a `PathCollision` at a named level of
the submitted path (walked at the DIM height).  No hash premise.

`LastBatchAccepted` takes the walk's length to be the DIM height and `N` to be an occupied leaf;
the deployed check fixes neither (`DimAcceptedLastLeafAnyLengthOrBreak` drops both).  The second
and third disjuncts each occur alone (`DimPinnedBreakOccurs`, `DimPathCollisionOccurs`). -/
def Properties.DimLastBatchProofIdentifiesLastBatchPinned : Prop :=
  ∀ (h : Hash) (ze : UInt256) (T : ChainTrees h ze) (created : ℕ)
    (c : Contracts.Atomicity.Chain) (N : ℕ) (sibs : ℕ → UInt256) (x : UInt256),
    LastBatchAccepted (T.backing created) c N sibs x →
      N + 1 = (T.leaves c).length ∨ PinnedBreak h ze (T.leaves c) N
        ∨ PathCollision h ze (T.leaves c) sibs 0 (dimHeight (T.leaves c).length) N x

/-! ## What the deployed check accepts against DIM storage -/

/-- **AGAINST DIM STORAGE, AN ACCEPTED BATCH-LEAF PATH OF ANY LENGTH AND INDEX IS THE LAST PUSHED
LEAF, OR A LOCATED BREAK.**  `LastLeafFaithful.AcceptedLastLeafAnyLengthOrBreak` with the tree read
from a DIM run.  Take storage `S` reached by `setup(ze)` on fresh storage and successful pushes of a
nonempty `L` (each chain of a `ChainTrees` is such storage: `T.run c`, `T.nonempty c`).  Take a
submission whose length `k` and mask `j` are free: `j < 2^k`, the walk of `(sibs, j, x)` over `k`
levels recomputes the value `root()` returns for `S`, and at every one of the `k` levels where the
path turns left the sibling is that level's zero, from `ze`.  Then `k` is the DIM height
`dimHeight |L|`, `j` is the last pushed leaf and `x` is its entry, or a `LastLeafAnyLengthBreak`
at height `dimHeight |L|` is exhibited.  No hash premise.

That the walk recomputes `root()` stands for the outer hop, which authenticates the chain's root
inside the settlement-layer root and is not modelled (`LastLeafFaithful`, model boundary). -/
def Properties.DimAcceptedLastLeafAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (S : PushTree) (sibs : ℕ → UInt256)
    (k j : ℕ) (x r : UInt256),
    Run h ze L S → L ≠ [] → root S = some r →
    j < 2 ^ k → walkPure h sibs 0 k j x = r →
    (∀ l < k, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l) →
      (k = dimHeight L.length ∧ j + 1 = L.length ∧ L.getD j ze = x)
        ∨ LastLeafAnyLengthBreak h ze L sibs k (dimHeight L.length) j x

/-- **ITS PREMISES HOLD AT THE LAST LEAF, WITH THE ZERO CHECK EXERCISED.**  For every hash, zero
value and three leaves, the run over `[a, b, c]` reports `root() = h (h a b) (h c ze)`.  The honest
path of the last leaf, at length `k = 2 = dimHeight 3` and mask `2 < 2^2`, recomputes it and passes
the zero check, which fires at level 0 (index 2 is a left child there).  This is the first
outcome. -/
def Properties.DimAcceptedLastLeafThreeLeaves : Prop :=
  ∀ (h : Hash) (ze a b c : UInt256), ∃ S : PushTree,
    Run h ze [a, b, c] S ∧ root S = some (h (h a b) (h c ze)) ∧ 2 < 2 ^ 2
      ∧ walkPure h (honestSibs h ze [a, b, c] 2) 0 2 2 c = h (h a b) (h c ze)
      ∧ (∀ l < 2, (2 / 2 ^ l) % 2 = 0 → honestSibs h ze [a, b, c] 2 l = zeros h ze l)
      ∧ (2 / 2 ^ 0) % 2 = 0 ∧ dimHeight 3 = 2

/-- **THE WRONG-LENGTH OUTCOME OCCURS ON A DIM RUN, FOR EVERY HASH.**  For the run over three
leaves `[a, b, c]` (DIM height 2), the empty path (`k = 0`) at index 0 with any siblings, whose
claimed leaf is the stored root itself, is in bounds (`0 < 2^0`), recomputes `root()`, and passes the
zero check, which ranges over no level.  Its length is not the DIM height, and a `HeightBreak` is
located: the `wrongLength` outcome (the other four need `k = dimHeight 3`). -/
def Properties.DimWrongLengthOccurs : Prop :=
  ∀ (h : Hash) (ze a b c : UInt256) (sibs : ℕ → UInt256), ∃ S : PushTree,
    Run h ze [a, b, c] S ∧ root S = some (h (h a b) (h c ze)) ∧ 0 < 2 ^ 0
      ∧ walkPure h sibs 0 0 0 (h (h a b) (h c ze)) = h (h a b) (h c ze)
      ∧ (∀ l < 0, (0 / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l)
      ∧ 0 ≠ dimHeight 3
      ∧ HeightBreak h ze [a, b, c] sibs 0 (dimHeight 3) 0 (h (h a b) (h c ze))

/-- **THE PADDED-ENTRY OUTCOME OCCURS ON A DIM RUN, FOR EVERY HASH.**  For the run over five
leaves (DIM height 3), the honest path of the empty slot 6 with the zero value `ze` as the claimed
leaf, at length `k = 3` and mask `6 < 2^3`, recomputes `root()`.  It passes the zero check, which
fires at level 0 (index 6 is a left child there; its sibling, slot 7, is padding).  Slot 6 is past
the pushed leaves, so it is not the last leaf, and the outcome is `paddedEntry`. -/
def Properties.DimPaddedEntryOccurs : Prop :=
  ∀ (h : Hash) (ze a b c d e : UInt256), ∃ S : PushTree,
    Run h ze [a, b, c, d, e] S
      ∧ root S = some (h (h (h a b) (h c d)) (h (h e ze) (h ze ze))) ∧ 6 < 2 ^ 3
      ∧ walkPure h (honestSibs h ze [a, b, c, d, e] 6) 0 3 6 ze
          = h (h (h a b) (h c d)) (h (h e ze) (h ze ze))
      ∧ (∀ l < 3, (6 / 2 ^ l) % 2 = 0 → honestSibs h ze [a, b, c, d, e] 6 l = zeros h ze l)
      ∧ (6 / 2 ^ 0) % 2 = 0 ∧ dimHeight 5 = 3
      ∧ 6 + 1 ≠ ([a, b, c, d, e] : List UInt256).length
      ∧ LastLeafAnyLengthBreak h ze [a, b, c, d, e] (honestSibs h ze [a, b, c, d, e] 6) 3 3 6 ze

/-- **THE PINNED-BREAK OUTCOME OCCURS ON A DIM RUN, FOR EVERY HASH.**  Chain trees in which every
chain has pushed `[a, ze, ze]`: leaves 1 and 2 equal the zero value, which `EntriesNotEmpty`
excludes.  The honest path of leaf 0 meets every field of `LastBatchAccepted` (DIM height 2), with
the zero check firing at both levels, though leaf 0 is not the last leaf; the stored root is
`h (h a ze) (h ze ze)`.  There is a `PinnedBreak` at 0 (`entryIsEmpty`: leaf 1 is `ze`) and no
`PathCollision` on the path, so in `DimLastBatchProofIdentifiesLastBatchPinned` only the
`PinnedBreak` disjunct holds.  The same path passes `ZeroRightSide` at a non-last leaf
(`ContractPathZeroRightSideIsLastOrPinnedBreak`'s second disjunct), and at `k = 2` it is the
`pinned` outcome of `DimAcceptedLastLeafAnyLengthOrBreak`. -/
def Properties.DimPinnedBreakOccurs : Prop :=
  ∀ (h : Hash) (ze a : UInt256), ∃ T : ChainTrees h ze,
    ∀ (created : ℕ) (ch : Contracts.Atomicity.Chain),
      T.leaves ch = [a, ze, ze] ∧ (T.backing created).height ch = 2
        ∧ root (T.state ch) = some (h (h a ze) (h ze ze))
        ∧ LastBatchAccepted (T.backing created) ch 0 (honestSibs h ze [a, ze, ze] 0) a
        ∧ (0 / 2 ^ 0) % 2 = 0 ∧ (0 / 2 ^ 1) % 2 = 0
        ∧ ZeroRightSide h ze [a, ze, ze] 2 0
        ∧ 0 + 1 ≠ (T.leaves ch).length
        ∧ PinnedBreak h ze [a, ze, ze] 0
        ∧ ¬ PathCollision h ze [a, ze, ze] (honestSibs h ze [a, ze, ze] 0) 0 2 0 a
        ∧ LastLeafAnyLengthBreak h ze [a, ze, ze] (honestSibs h ze [a, ze, ze] 0) 2 2 0 a

/-- **THE PATH-COLLISION OUTCOME OCCURS ON A DIM RUN.**  Chain trees under the colliding
`demoHash` in which every chain's storage is `demoChainState`, the run over `[5, 7, 9]` from
`setup(0)`, whose `root()` is `41`.  The submission for index 0 with the zero cascade (`0`, then
`1`) as siblings and claimed leaf `37` walks `demoHash 37 0 = 38`, then `demoHash 38 1 = 41`: it
meets every field of `LastBatchAccepted` (DIM height 2; the zero check passes at both levels),
though index 0 is not the last leaf, and there is no `PinnedBreak` at 0.  The `PathCollision` is at
level 1: the verifier hashed `(38, 1)` where the tree has `(20, 10)`, and both hash to `41`.  So in
`DimLastBatchProofIdentifiesLastBatchPinned` only the `PathCollision` disjunct holds, and at
`k = 2` this is the `pathCollision` outcome of `DimAcceptedLastLeafAnyLengthOrBreak`. -/
def Properties.DimPathCollisionOccurs : Prop :=
  ∃ T : ChainTrees demoHash 0, ∀ (created : ℕ) (ch : Contracts.Atomicity.Chain),
    T.leaves ch = [5, 7, 9] ∧ T.state ch = demoChainState ∧ root demoChainState = some 41
      ∧ (T.backing created).height ch = 2
      ∧ LastBatchAccepted (T.backing created) ch 0 (zeros demoHash 0) 37
      ∧ 0 + 1 ≠ (T.leaves ch).length ∧ ¬ PinnedBreak demoHash 0 [5, 7, 9] 0
      ∧ walkPair demoHash (zeros demoHash 0) 0 0 37 1 = (38, 1)
      ∧ treePair demoHash 0 [5, 7, 9] 1 0 = (20, 10)
      ∧ PathCollision demoHash 0 [5, 7, 9] (zeros demoHash 0) 0 2 0 37
      ∧ LastLeafAnyLengthBreak demoHash 0 [5, 7, 9] (zeros demoHash 0) 2 2 0 37

/-! ## The check on the honest path -/

/-- **THE LAST LEAF PASSES THE CHECK.**  On storage representing a nonempty `L` at `H`, `root()`
is the fold, the honest path of the last leaf recomputes it, and that path passes the zero
check.  Only the first conjunct reads the storage; the other two hold for every nonempty `L` that
fits `H` (`honest_walk_root`, and the last leaf's left-turn siblings are padding). -/
def Properties.ContractPathLastHasZeroRightSide : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree),
    Represents h ze L H S → L ≠ [] →
      root S = some (rootOf h ze L H)
        ∧ walkPure h (honestSibs h ze L (L.length - 1)) 0 H (L.length - 1)
            (L.getD (L.length - 1) ze) = rootOf h ze L H
        ∧ ZeroRightSide h ze L H (L.length - 1)

/-- **A PASSING LEAF IS THE LAST, OR PINS A BREAK.**  No hash premise: for every `L` that fits `H`,
if the honest path of an occupied leaf `i` passes the zero check, then `i` is the last leaf or
there is a `PinnedBreak` on the subtree that starts at `i + 1`.  This is
`LastLeaf.last_leaf_or_pinned_break` on the honest sibling stream; it does not read storage.  Every
storage representing `L` at `H` meets the capacity premise (`Frontier.capacity`). -/
def Properties.ContractPathZeroRightSideIsLastOrPinnedBreak : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H i : ℕ),
    L.length ≤ 2 ^ H → i < L.length → ZeroRightSide h ze L H i →
      i + 1 = L.length ∨ PinnedBreak h ze L i

/-- **THE CHECK IS EXACTLY "LAST LEAF", UNDER A BOUNDED PREMISE.**  For every `L` that fits `H`,
with no collision among the tree's own pairs and its zero cascade (`TreePair`, a finite
instance-determined set) and no leaf equal to the zero value, the honest path of an occupied leaf
`i` passes the zero check iff `i` is the last leaf.  The forward direction is
`ContractPathZeroRightSideIsLastOrPinnedBreak` with `LastLeaf.no_pinned_break_on`; it does not
read storage.  Every storage representing `L` at `H` meets the capacity premise. -/
def Properties.ContractPathLastIff : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256) (H i : ℕ),
    L.length ≤ 2 ^ H → i < L.length → EntriesNotEmpty ze L →
    PairInjOn h (TreePair h ze L H) →
      (ZeroRightSide h ze L H i ↔ i + 1 = L.length)

/-- **ITS PREMISES ARE SATISFIABLE, AND BOTH SIDES OCCUR.**  `demoChainState` is the storage
`setup(0)` and pushes of `[5, 7, 9]` leave under the colliding `demoHash`.  It is a run, it
represents the leaves at height 2, and the premises hold (the leaves fit height 2, and the bounded
premises).  Leaf 0 fails the check (its level-0 sibling is `7`), and the last leaf 2 passes it,
with the check exercised at level 0. -/
def Properties.ContractPathLastIffSatisfiable : Prop :=
  Run demoHash 0 [5, 7, 9] demoChainState ∧ Represents demoHash 0 [5, 7, 9] 2 demoChainState
    ∧ ([5, 7, 9] : List UInt256).length ≤ 2 ^ 2
    ∧ EntriesNotEmpty 0 [5, 7, 9] ∧ PairInjOn demoHash (TreePair demoHash 0 [5, 7, 9] 2)
    ∧ ¬ ZeroRightSide demoHash 0 [5, 7, 9] 2 0 ∧ ZeroRightSide demoHash 0 [5, 7, 9] 2 2
    ∧ (2 / 2 ^ 0) % 2 = 0
    ∧ (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ demoHash a b = demoHash c d)

end Contracts.DynamicIncrementalMerkle
