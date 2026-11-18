import EraSpec.Contracts.ChainBatchRootTree.Specs.GenesisSeed

/-!
# Properties: genesis seeding stores one root in both places, once, and never after a real batch

Proofs: `../Proofs/GenesisSeed.lean`. No property assumes anything about `keccak`;
`GenesisImtLeavesOpenSetupRoot` takes the documented value of `EMPTY_IMT_ROOT`.

* `CreateNewChainSeedsGenesisRoot`: a successful `createNewChain` leaves `chainBatchRoots[c][0]`
  and the diamond's `l2LogsRootHashes[0]` both equal to `compute(0, 0, EMPTY_IMT_ROOT,
  EMPTY_IMT_ROOT)`, with `c` registered at batch 0. `CreateNewChainSucceedsIffGenesisNonzero`: from
  unregistered, uncreated storage it succeeds exactly when that root is nonzero.
* `GenesisRootStable`: on every run from fresh storage, once `c` has a chain contract both slots
  hold the genesis root, which is nonzero.
* `SeedAtMostOnce`: on every successful run, from any storage, `seedGenesisRoot` succeeds at most
  once (inside `createNewChain` or as a direct call).
* `NoSeedAfterRealBatch`: on every successful run, from any storage, no `seedGenesisRoot` succeeds
  after a batch root has been recorded.
* `FirstRealBatchIsOne`: right after `createNewChain` the next recorded batch is batch 1.
* `GenesisImtLeavesOpenSetupRoot`: the IMT-root hop at leaf 2 or 3 of the genesis root opens the
  root of the freshly set-up commitment tree, or locates a collision. `GenesisImtLeavesWitness`:
  its premises hold on the honest proofs, which locate no collision.
* `GenesisSeedRunWitness`: a concrete run creates the chain, executes a batch, and then both seed
  paths revert.
-/

namespace Contracts.ChainBatchRootTree

/-- **`createNewChain` SEEDS ONE ROOT IN BOTH PLACES.** After a successful `createNewChain` for
`c`, the chain contract's `l2LogsRootHashes[0]` and the message root's `chainBatchRoots[c][0]`
both equal `genesisChainBatchRoot = compute(0, 0, EMPTY_IMT_ROOT, EMPTY_IMT_ROOT)`,
`currentChainBatchNumber[c] = 0`, and `c` is registered. -/
def Properties.CreateNewChainSeedsGenesisRoot : Prop :=
  ∀ (keccak : Keccak) (s s' : SeedSystem),
    seedStep keccak s .createNewChain = some s' →
      (∃ d, s'.diamond = some d ∧ d.logsRoots 0 = genesisChainBatchRoot keccak)
        ∧ s'.mr.roots 0 = genesisChainBatchRoot keccak
        ∧ s'.mr.current = 0 ∧ s'.mr.registered = true

/-- **WHEN `createNewChain` SUCCEEDS.** From a state with no chain contract for `c`, `c`
unregistered and `chainBatchRoots[c][0] = 0`, `createNewChain` succeeds exactly when the genesis
root is nonzero (`require(genesisChainBatchRoot != bytes32(0))`, `MessageRootBase.sol:303`). Off
chain, `cast keccak` gives `0x1d57…7885`; Lean does not evaluate keccak. -/
def Properties.CreateNewChainSucceedsIffGenesisNonzero : Prop :=
  ∀ (keccak : Keccak) (s : SeedSystem),
    s.diamond = none → s.mr.registered = false → s.mr.roots 0 = 0 →
      ((seedStep keccak s .createNewChain).isSome ↔ genesisChainBatchRoot keccak ≠ 0)

/-- **GENESIS CONSISTENCY, ON EVERY RUN.** On every successful run from fresh storage, in the final
state, if `c` has a chain contract then its `l2LogsRootHashes[0]` and `chainBatchRoots[c][0]` both
equal `genesisChainBatchRoot`, that root is nonzero, and `c` is registered. -/
def Properties.GenesisRootStable : Prop :=
  ∀ (keccak : Keccak) (ls : List SeedLabel) (s : SeedSystem),
    seedRun keccak seedFresh ls = some s →
      ∀ d, s.diamond = some d →
        d.logsRoots 0 = genesisChainBatchRoot keccak
          ∧ s.mr.roots 0 = genesisChainBatchRoot keccak
          ∧ genesisChainBatchRoot keccak ≠ 0 ∧ s.mr.registered = true

/-- **`seedGenesisRoot` SUCCEEDS AT MOST ONCE.** On every successful run, from any storage, at most
one step runs `seedGenesisRoot` (`createNewChain` or a direct call). -/
def Properties.SeedAtMostOnce : Prop :=
  ∀ (keccak : Keccak) (s₀ : SeedSystem) (ls : List SeedLabel) (s : SeedSystem),
    seedRun keccak s₀ ls = some s → seedCount ls ≤ 1

/-- **NO `seedGenesisRoot` AFTER A REAL BATCH.** On every successful run, from any storage, no step
after one that records a batch root (`execute`, or a direct `addChainBatchRoot`) runs
`seedGenesisRoot`. -/
def Properties.NoSeedAfterRealBatch : Prop :=
  ∀ (keccak : Keccak) (s₀ : SeedSystem) (ls₁ : List SeedLabel) (ℓ : SeedLabel)
    (ls₂ : List SeedLabel) (s : SeedSystem),
    seedRun keccak s₀ (ls₁ ++ ℓ :: ls₂) = some s → ℓ.IsRealBatch → ∀ ℓ' ∈ ls₂, ¬ ℓ'.IsSeed

/-- **THE FIRST REAL BATCH IS BATCH 1.** Right after a successful `createNewChain`,
`addChainBatchRoot(c, n, r)` succeeds only for `n = 1` (`currentChainBatchNumber` stays 0,
`MessageRootBase.sol:312`). -/
def Properties.FirstRealBatchIsOne : Prop :=
  ∀ (keccak : Keccak) (s s' : SeedSystem) (read0 : Option UInt256) (n : ℕ) (r : UInt256),
    seedStep keccak s .createNewChain = some s' →
      seedExec s'.mr read0 (.addChainBatchRoot n r) ≠ none → n = 1

/-- **THE GENESIS IMT LEAVES ARE THE FRESHLY SET-UP COMMITMENT TREE'S ROOT.** Under the documented
value of `EMPTY_IMT_ROOT` (keccak of 96 zero bytes), the atomic-interop IMT-root hop at leaf 2 or 3
of the genesis root opens the root of `Contracts.InteropCommitmentTree.setup` (the `{0,0,0}`
sentinel alone) at height 0, for any padding `z0`, or locates an `OpeningCollision`. This is the
batch-0 tree `Contracts.InteropOperational.BatchLog.genesis` takes. -/
def Properties.GenesisImtLeavesOpenSetupRoot : Prop :=
  ∀ (keccak : Keccak) (z0 : UInt256) (sibs : ℕ → UInt256) (len m : ℕ) (x : UInt256),
    EmptyImtRootDocumented keccak →
    (m = IMT_BEGIN_ROOT_LEAF_INDEX ∨ m = IMT_END_ROOT_LEAF_INDEX) →
    ImtRootHopAccepted keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs len m x →
      x = Contracts.InteropCommitmentTree.root (node keccak) z0 (imtHashLeaf keccak)
            Contracts.InteropCommitmentTree.setup 0
        ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs m x

/-- **WITNESS.** On a concrete keccak with a nonzero genesis root: from fresh storage,
`createNewChain` then one executed batch with root `r ≠ 0` succeed; afterwards
`chainBatchRoots[c][0]` is the genesis root, `chainBatchRoots[c][1] = r`, the current batch is 1,
exactly one step seeded, and both seed paths revert. -/
def Properties.GenesisSeedRunWitness : Prop :=
  ∃ (keccak : Keccak) (r : UInt256) (s : SeedSystem),
    genesisChainBatchRoot keccak ≠ 0 ∧ r ≠ 0
      ∧ seedRun keccak seedFresh [.createNewChain, .execute r] = some s
      ∧ s.mr.roots 0 = genesisChainBatchRoot keccak ∧ s.mr.roots 1 = r ∧ s.mr.current = 1
      ∧ seedCount [.createNewChain, .execute r] = 1
      ∧ seedStep keccak s (.mrCall .seedGenesisRoot) = none
      ∧ seedStep keccak s .createNewChain = none

/-- **WITNESS FOR THE GENESIS IMT LEAVES.** Some keccak meets the documented value of
`EMPTY_IMT_ROOT`, and under it the honest proofs of leaves 2 and 3 of the genesis root meet
`ImtRootHopAccepted` with claimed root `EMPTY_IMT_ROOT`, locate no `OpeningCollision`, and that
root is the set-up tree's root. -/
def Properties.GenesisImtLeavesWitness : Prop :=
  ∃ keccak : Keccak, EmptyImtRootDocumented keccak
    ∧ ∀ (z0 : UInt256) (m : ℕ), (m = IMT_BEGIN_ROOT_LEAF_INDEX ∨ m = IMT_END_ROOT_LEAF_INDEX) →
        ImtRootHopAccepted keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT
            (openingSibs keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT m) TREE_DEPTH m EMPTY_IMT_ROOT
          ∧ ¬ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT
              (openingSibs keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT m) m EMPTY_IMT_ROOT
          ∧ EMPTY_IMT_ROOT = Contracts.InteropCommitmentTree.root (node keccak) z0
              (imtHashLeaf keccak) Contracts.InteropCommitmentTree.setup 0

end Contracts.ChainBatchRootTree
