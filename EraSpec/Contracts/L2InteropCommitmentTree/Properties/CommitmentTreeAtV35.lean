import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CommitmentTreeAtV35

/-!
# Properties: the v35 tree contract's transactions on its whole storage

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.CommitmentTreeAtV35`
(`draft/v0.35.0` `b17415d20`; the same tree code is on `main` `70096e2`).  Proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CommitmentTreeAtV35`.

No hash premise anywhere: the node hash `h`, the leaf hash `hl` and the padding constant `zE` are
arbitrary.  Gas and the leaf hook are not modelled (see the spec), so a run below is a run of the
code's checks and storage writes.

## What holds along every run from the predeploy's storage

* **Setup.**  On the predeploy's storage, `initL2()` succeeds exactly when the upgrader sends it.
  It does not revert inside `FullMerkle`, writes the list state `setup`, and leaves the storage
  caching the one leaf hash `hashLeaf({0,0,0})`, padded with `zE`.  No `insert` succeeds there
  (`CInitL2AtV35OnPredeploy`).  With `zE = hashLeaf({0,0,0})` the call is the pin's `cSetup`
  (`CInitL2AtV35AtPinPaddingIsCSetup`).
* **Shape.**  A run stays on the predeploy's storage, with no successful transaction, until the
  upgrader's `initL2()`, if there is one.  That is the run's only successful `initL2()`, and from
  there on the run is a `CachedRoot.CRun`: each step is idle or a guarded `cInsert`
  (`CTxRunAtV35Shape`).  With the pin's padding constant it is a `CRun` from `cSetup`
  (`CTxRunAtV35AtPinPaddingIsCRunFromCSetup`), so `CachedRoot.CRunRootIsPublished` applies to it.
* **Inserts.**  Every successful `insert(v, hint)` was sent by the appender, and its walk exits at
  the index where `InsertGuard` holds.  It writes there, moves `(_leafNumber, _height)` as
  `hInsert` does, and returns the root that `root()` reads afterwards
  (`CTxRunAtV35InsertIsGuardedCInsert`).
* **The stored root (headline).**  At every step the storage is the predeploy's, or the list state
  is reached from `setup` and `Valid`, the two copies of `_leafNumber` agree, `_height` is the
  source's `fmHeight`, the storage caches the leaf hashes padded with `zE`, and `root()` is the fold
  over them at `_height` (`CTxRunAtV35StoredRootIsPublished`).
* **The contract's own proofs against it.**  `CachedRoot.ContractProofsAtStoredRoot`, with padding
  `zE`, at every initialized step (`CTxRunAtV35ContractProofsAtStoredRoot`).
* **Empty slots.**  A path accepted against `root()` that presents a leaf at an index at or beyond
  the leaf count locates the equation `hashLeaf(ℓ) = zE`, a node-hash collision on the path, or a
  wrong length (`CTxRunAtV35EmptySlotLocatesPadding`).

## Witnesses

`StaleHintCRunWitnessAtV35`: for every hash and padding constant, a run from the predeploy's
storage with `initL2()` and seven inserts, the last one from a hint six hops below its exit index,
which the pin's five-hop search refuses.  It meets the run premises of every statement above.
`PaddingForgeryAtV35Witness`: on that run, with the pin's padding constant as `zE`, the sentinel
`{0,0,0}` at the empty slot 7 is an accepted non-inclusion proof for the key `1`, which the
contract's own `merklePath(1)` proves included.  So the inclusion and non-inclusion premises of
clause 3 of `CTxRunAtV35ContractProofsAtStoredRoot` and the premises of
`CTxRunAtV35EmptySlotLocatesPadding` hold together, and the located break is exactly `paddingHit`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## Setup -/

/-- **`initL2()` ON THE PREDEPLOY'S STORAGE.**  For every node hash, leaf hash and padding
constant `zE`: `IndexedMerkleTree.setup`'s calls on the predeploy's storage do not revert, and
give the sentinel list state `setup` with the dimensions `hSetup`, on storage that caches the one
leaf hash `hashLeaf({0,0,0})` padded with `zE`.  For any roles, a transaction `initL2()` from `c`
on that storage succeeds exactly when `c` is the upgrader, and then leaves that storage.  No
`insert(v, hint)` succeeds there, whoever sends it. -/
def Properties.CInitL2AtV35OnPredeploy : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256),
    (∃ S : CState, cInitL2AtV35 h hl zE cPredeployAtV35 = some S ∧ S.tree = setup
      ∧ S.toH = hSetup ∧ FullMerkle.Represents h zE [hl ⟨0, 0, 0⟩] S.fm)
    ∧ (∀ (K : Roles) (c : Caller) (S' : CState),
        CTxStepAtV35 h hl zE K cPredeployAtV35 c .initL2 S'
          ↔ c = K.upgrader ∧ cInitL2AtV35 h hl zE cPredeployAtV35 = some S')
    ∧ ∀ (K : Roles) (c : Caller) (v : UInt256) (hint : ℕ) (S' : CState),
        ¬ CTxStepAtV35 h hl zE K cPredeployAtV35 c (.insert v hint) S'

/-- **AT THE PIN'S PADDING CONSTANT, v35's SETUP IS THE PIN'S.**  On the predeploy's storage,
`cInitL2AtV35` with `zE = hashLeaf({0,0,0})` is `CachedRoot.cSetup`, the pin's
`IndexedMerkleTree.setup` on fresh storage.  So the two setups differ only in the constant passed
to `FullMerkle.setup`. -/
def Properties.CInitL2AtV35AtPinPaddingIsCSetup : Prop :=
  ∀ (h : Hash) (hl : LeafHash), cInitL2AtV35 h hl (zeroLeafHash hl) cPredeployAtV35 = cSetup h hl

/-! ## The shape of a run -/

/-- **THE SHAPE OF A RUN FROM THE PREDEPLOY'S STORAGE.**  For every node hash, leaf hash, padding
constant and roles, a run from `cPredeployAtV35` either never has a successful transaction and
stays there, or there is a step `k` such that the storage is the predeploy's up to `k`, no
transaction succeeds before `k`, the transaction at `k` is the upgrader's `initL2()`, the storage
after it is what `cInitL2AtV35` writes on the predeploy's storage, no later transaction is a
successful `initL2()`, and the run from `k + 1` on is a `CachedRoot.CRun`: each step is idle or a
guarded insert (`InsertGuard`) through `cInsert` that does not revert. -/
def Properties.CTxRunAtV35Shape : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    (∀ n : ℕ, R n = cPredeployAtV35 ∧ tx n = none)
    ∨ ∃ k : ℕ, (∀ n ≤ k, R n = cPredeployAtV35) ∧ (∀ n < k, tx n = none)
        ∧ tx k = some (K.upgrader, .initL2)
        ∧ cInitL2AtV35 h hl zE cPredeployAtV35 = some (R (k + 1))
        ∧ (∀ n : ℕ, k < n → ∀ c : Caller, tx n ≠ some (c, .initL2))
        ∧ CRun h hl (fun n => R (k + 1 + n))

/-- **WITH THE PIN'S PADDING CONSTANT, A v35 RUN IS A `CachedRoot` RUN FROM `cSetup`.**  For every
node hash, leaf hash and roles, in a run of the v35 machine with `zE = hashLeaf({0,0,0})` from the
predeploy's storage, if the transaction at step `k` is the upgrader's `initL2()`, then the state
after it is `cSetup`'s, and the run from `k + 1` on is a `CRun`.  So `CRunRootIsPublished` holds
for the run from `k + 1` on, whatever hints its inserts carry. -/
def Properties.CTxRunAtV35AtPinPaddingIsCRunFromCSetup : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl (zeroLeafHash hl) K R tx → R 0 = cPredeployAtV35 →
    ∀ k : ℕ, tx k = some (K.upgrader, .initL2) →
      cSetup h hl = some (R (k + 1)) ∧ CRun h hl (fun n => R (k + 1 + n))

/-- **EVERY SUCCESSFUL INSERT IS THE GUARDED INSERT AT ITS EXIT INDEX, AND RETURNS THE STORED
ROOT.**  For every node hash, leaf hash, padding constant and roles, in every run from the
predeploy's storage, if the transaction at step `n` is `insert(v, hint)` from `c`, then `c` is the
appender, and for some exit index `low` and returned `newRoot` `r`: the walk from `hint` exits at
`low`; `InsertGuard` holds there (`low` is occupied, its value is below `v` and its `nextValue` is
`0` or at least `v`, and `v` is nonzero and unregistered); the storage after the step is `cInsert`
at `low`, which returns `r`; the dimensions move as `hInsert` moves them; `root()` afterwards
returns `r`; and `r` is the fold over the new leaf hashes at the new `_height`, padded with
`zE`. -/
def Properties.CTxRunAtV35InsertIsGuardedCInsert : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    ∀ (n : ℕ) (c : Caller) (v : UInt256) (hint : ℕ), tx n = some (c, .insert v hint) →
      c = K.appender
        ∧ ∃ (low : ℕ) (r : UInt256), WalkExitsAtV35 (R n).tree v hint low
          ∧ InsertGuard (R n).tree v low
          ∧ cInsert h hl (R n) v low = some (R (n + 1), r)
          ∧ (R (n + 1)).toH = hInsert (R n).toH v low
          ∧ (R (n + 1)).root = some r
          ∧ r = (hInsert (R n).toH v low).root h zE hl

/-! ## The stored root -/

/-- **HEADLINE: ALONG EVERY RUN FROM GENESIS STORAGE, `root()` IS THE FOLD OVER THE LEAF HASHES,
PADDED WITH `zE`.**  For every node hash, leaf hash, padding constant and roles, at every step `n`
of every run from the predeploy's storage, either the storage is still the predeploy's, or all of:

* the list state is reached from `setup` by guarded inserts and is `Valid`;
* with `(_leafNumber, _height)` it is reached from `hSetup`;
* the two copies of `_leafNumber` agree, and `_height` is `fmHeight` of the leaf count;
* the `FullMerkle` storage caches the leaf hashes of the list state, padded with `zE`;
* `root()` returns `HState.root` of the state with padding `zE`, the fold over the leaf hashes at
  `_height`.

So each `RunHeight` result about a state reached from `hSetup`, taken with padding `zE`, is about
the root this storage holds. -/
def Properties.CTxRunAtV35StoredRootIsPublished : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    ∀ n : ℕ, R n = cPredeployAtV35
      ∨ (Reaches setup (R n).tree ∧ Valid (R n).tree ∧ HReaches hSetup (R n).toH
          ∧ (R n).fm.leafNumber = (R n).tree.leafCount
          ∧ (R n).fm.height = fmHeight (R n).tree.leafCount
          ∧ FullMerkle.Represents h zE (leafHashes hl (R n).tree) (R n).fm
          ∧ (R n).root = some ((R n).toH.root h zE hl))

/-- **THE CONTRACT'S OWN PROOFS AGAINST THE STORED ROOT, ALONG EVERY RUN FROM GENESIS STORAGE.**
For every node hash, leaf hash, padding constant and roles, at every initialized step of every
run from the predeploy's storage, `root()` returns some `Rt`, and:

1. every value the tree holds sits at an occupied index `i` whose `merklePath(i)` is a path of
   length `_height` that is accepted as an inclusion proof against `Rt`, with no located break;
2. every nonzero value the tree does not hold has an occupied low leaf `i` whose `merklePath(i)`
   is accepted as a non-inclusion proof against `Rt`, with no located break;
3. if a value has both an accepted inclusion proof and an accepted non-inclusion proof against
   `Rt`, one of the two submitted paths carries a located `TreeRootBreak` at padding `zE`, whose
   `paddingHit` case is the equation `hashLeaf(ℓ) = zE`.

This is `CachedRoot.ContractProofsAtStoredRoot` with padding `zE`, for runs of the v35 machine. -/
def Properties.CTxRunAtV35ContractProofsAtStoredRoot : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    ∀ n : ℕ, Initialized (R n).tree →
    ∃ Rt : UInt256, (R n).root = some Rt
      ∧ (∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
          ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
            ∧ ∃ p : List UInt256, (R n).merklePath i = some p ∧ p.length = (R n).fm.height
              ∧ InclusionAccepted h hl Rt v ((R n).tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h zE hl (R n).tree (R n).fm.height (FullMerkle.pathSibs p)
                  p.length i ((R n).tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
          ∃ i < (R n).tree.leafCount,
            ∃ p : List UInt256, (R n).merklePath i = some p ∧ p.length = (R n).fm.height
              ∧ NonInclusionAccepted h hl Rt v ((R n).tree.leaf i) i (FullMerkle.pathSibs p)
                  p.length
              ∧ ¬ TreeRootBreak h zE hl (R n).tree (R n).fm.height (FullMerkle.pathSibs p)
                  p.length i ((R n).tree.leaf i))
      ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
          InclusionAccepted h hl Rt v ℓ₁ i₁ s₁ k₁ → NonInclusionAccepted h hl Rt v ℓ₂ i₂ s₂ k₂ →
            TreeRootBreak h zE hl (R n).tree (R n).fm.height s₁ k₁ i₁ ℓ₁
              ∨ TreeRootBreak h zE hl (R n).tree (R n).fm.height s₂ k₂ i₂ ℓ₂)

/-- **AN EMPTY SLOT'S PATH LOCATES THE PADDING EQUATION, A COLLISION, OR A WRONG LENGTH.**  For
every node hash, leaf hash, padding constant and roles, at every step of every run from the
predeploy's storage where `root()` returns `Rt`: if a path `s` of length `k` presenting
`hashLeaf(ℓ)` at an index `j` at or beyond the leaf count is accepted against `Rt` (`PathAccepts`,
the root check that both verifiers make), then

* `hashLeaf(ℓ)` is the padding constant `zE`; or
* `k` is `_height`, and the path carries a node-hash collision at a named step (`PathCollision`
  against the tree's own pairs); or
* `k` is not `_height`, located by `HeightBreak`.

At the pin the padding constant was `hashLeaf({0,0,0})`, so the first case held for `ℓ = {0,0,0}`
with no collision (`History.CThreeLeafWitness`); here `zE` is a parameter, and at v35 the first case is the
keccak equation of the spec's model boundary.  `PaddingForgeryAtV35Witness` meets the premises on
a run of this machine; it exhibits only the first case, at the pin's padding.  The
`PathCollision` and `HeightBreak` break cases fire on the base model at an occupied index
(`Contracts.InteropCommitmentTree.Properties.TreeRootBreakEveryCaseFires`); no empty-slot instance
of them is exhibited. -/
def Properties.CTxRunAtV35EmptySlotLocatesPadding : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    ∀ (n : ℕ) (Rt : UInt256) (ℓ : Leaf) (j k : ℕ) (s : ℕ → UInt256),
      (R n).root = some Rt → (R n).tree.leafCount ≤ j → PathAccepts h Rt s k j (hl ℓ) →
      hl ℓ = zE
        ∨ (k = (R n).fm.height
            ∧ PathCollision h zE (leafHashes hl (R n).tree) s 0 k j (hl ℓ))
        ∨ HeightBreak h zE (leafHashes hl (R n).tree) s k (R n).fm.height j (hl ℓ)

/-! ## Witnesses -/

/-- **A RUN FROM GENESIS STORAGE WITH A STALE HINT, FOR EVERY HASH AND PADDING.**  For every node
hash, leaf hash, padding constant and roles, `staleHintCRunAtV35` with trace `staleHintTxV35 K` is
a run of the v35 machine from the predeploy's storage, and its list states are `staleHintRunV35`.
Its transactions (`staleHintTxV35`) are the upgrader's `initL2()` at step 0, six honest inserts,
and at step 7 the appender's `insert(7, 0)` on `chainTree 6`.  That walk exits at index 6 after six
hops, while the pin's five-hop search from `0` runs out, so the pin's `InsertChecks` hold for no
exit index: the pin's `TxStep` has no step for it.  The state at step 7 is initialized, holds the
key `1` and not the key `8`, and has `_height` 3; after step 7 the list state is `chainTree 7`, at
`_height` 3, and `root()` returns the fold over its leaf hashes, padded with `zE`.

So the run premises of every statement above hold on this run, for every padding constant, in
particular for the pin's (`CTxRunAtV35AtPinPaddingIsCRunFromCSetup`, with `k = 0`).  An insert
premise holds at step 7, and an initialized state with a key and a non-key is at step 7.
`PaddingForgeryAtV35Witness` meets the remaining premises. -/
def Properties.StaleHintCRunWitnessAtV35 : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles),
    CTxRunAtV35 h hl zE K (staleHintCRunAtV35 h hl zE) (staleHintTxV35 K)
      ∧ staleHintCRunAtV35 h hl zE 0 = cPredeployAtV35
      ∧ (∀ n : ℕ, (staleHintCRunAtV35 h hl zE n).tree = staleHintRunV35 n)
      ∧ staleHintTxV35 K 0 = some (K.upgrader, .initL2)
      ∧ staleHintTxV35 K 7 = some (K.appender, .insert 7 0)
      ∧ staleHintRunV35 7 = chainTree 6 ∧ staleHintRunV35 8 = chainTree 7
      ∧ WalkExitsAtV35 (chainTree 6) 7 0 6 ∧ lowSearch (chainTree 6) 7 6 0 = some 6
      ∧ lowSearch (chainTree 6) 7 maxLowIndexSearchAttempts 0 = none
      ∧ (∀ low : ℕ, ¬ InsertChecks (chainTree 6) 7 0 low)
      ∧ Initialized (staleHintCRunAtV35 h hl zE 7).tree
      ∧ (1 : UInt256) ∈ keys (toAbs (staleHintCRunAtV35 h hl zE 7).tree)
      ∧ (8 : UInt256) ∉ keys (toAbs (staleHintCRunAtV35 h hl zE 7).tree)
      ∧ (staleHintCRunAtV35 h hl zE 7).fm.height = 3
      ∧ (staleHintCRunAtV35 h hl zE 8).fm.height = 3
      ∧ (staleHintCRunAtV35 h hl zE 8).root = some (root h zE hl (chainTree 7) 3)

/-- **THE PADDING FORGERY ON THE v35 MACHINE, AT THE PIN'S PADDING CONSTANT.**  For every node hash
and leaf hash, on `staleHintCRunAtV35` with `zE = hashLeaf({0,0,0})`, at step 7 (`chainTree 6`:
seven leaves at `_height` 3, slot 7 empty), against the root `Rt` that `root()` returns:

* the contract's own `merklePath(1)` is an accepted inclusion proof for the key `1`;
* the contract refuses `merklePath(7)`;
* yet the sentinel `{0,0,0}` at index 7, with the tree's own siblings of slot 7, is an accepted
  non-inclusion proof for `1`, and its located break is exactly `paddingHit`.

So with the pin's constant the v35 machine's stored root accepts the pin's forgery: the premises
of clause 3 of `CTxRunAtV35ContractProofsAtStoredRoot` and of
`CTxRunAtV35EmptySlotLocatesPadding` hold on a run of this machine.  The first case of the latter
holds and, by `TreeRootBreakExactly`, the other two do not. -/
def Properties.PaddingForgeryAtV35Witness : Prop :=
  ∀ (h : Hash) (hl : LeafHash),
    (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).root
        = some (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3)
      ∧ (∃ p : List UInt256, (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).merklePath 1 = some p
          ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1
              ((chainTree 6).leaf 1) 1 (FullMerkle.pathSibs p) p.length)
      ∧ (staleHintCRunAtV35 h hl (hl ⟨0, 0, 0⟩) 7).merklePath 7 = none
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3) 1 ⟨0, 0, 0⟩ 7
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (chainTree 6)) 7) 3 7 ⟨0, 0, 0⟩ .paddingHit

/-! ## The list-state projection, and what follows from it

`HintSearchAtHead` states the v35 contract's transactions on the list state alone
(`TxStepAtHead`, with the same `InsertChecksAtV35`).  The canonical machine `CTxStepAtV35` projects
onto it, so the head results hold of the canonical machine's list state. -/

/-- **THE CANONICAL MACHINE PROJECTS TO THE LIST-STATE MACHINE.**  For every node hash, leaf hash
and padding constant, every run of `CTxRunAtV35` (any start state) is, on its list state, a run of
`HintSearchAtHead`'s `TxRunAtHead` with the same trace. -/
def Properties.CTxRunAtV35ProjectsToTxRunAtHead : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → TxRunAtHead K (fun n => (R n).tree) tx

/-- **RECLAIMABLE EXACTLY WHEN ABSENT, ON THE CANONICAL MACHINE.**  For every node hash, leaf hash
and padding constant, at every initialized step of every run from the predeploy's storage, a
nonzero value is straddled by a leaf of the tree (a leaf `W` with `W.key < v` and `v` below
`W.nextKey`, or `W.nextKey = 0`) exactly when it is not a key.  The straddling leaf is a genuine
leaf of the list state; what the deployed `verifyNonInclusion` accepts against `root()` is
`CTxRunAtV35ContractProofsAtStoredRoot`'s statement, not this one. -/
def Properties.CTxRunAtV35ReclaimableIffAbsent : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx → R 0 = cPredeployAtV35 →
    ∀ (n : ℕ) (v : UInt256), Initialized (R n).tree → v ≠ 0 →
      ((∃ W ∈ toAbs (R n).tree, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (toAbs (R n).tree))

/-- **THE KEY SET NEVER SHRINKS, ON THE CANONICAL MACHINE.**  For every node hash, leaf hash and
padding constant, along every run from any start state, a key of the list state at step `m` is a
key at every later step. -/
def Properties.CTxRunAtV35KeysMono : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx →
    ∀ m n : ℕ, m ≤ n → keys (toAbs (R m).tree)
      ⊆ keys (toAbs (R n).tree)

/-- **AT MOST ONE `initL2()` SUCCEEDS, ON THE CANONICAL MACHINE.**  For every node hash, leaf hash
and padding constant, along every run from any start state, two successful `initL2()` calls are
the same step. -/
def Properties.CTxRunAtV35InitL2AtMostOnce : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) (R : ℕ → CState) (tx : Trace),
    CTxRunAtV35 h hl zE K R tx →
    ∀ (m n : ℕ) (cm cn : Caller), tx m = some (cm, .initL2) → tx n = some (cn, .initL2) → m = n

end Contracts.InteropCommitmentTree
